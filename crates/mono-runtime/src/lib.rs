//! `mono::Program` をそのまま読む oracle runtime。
//!
//! この crate は control VM の前に `specialize -> mono` 契約を検証するための実行器である。
//! 最適化や軽量 control 表現への lowering は `control-vm` 側で扱う。

#![forbid(unsafe_code)]

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use mono::{
    Block, CaseArm, CatchArm, DefId, Expr, ExprKind, FunctionAdapterHygiene, InstanceId, Lit, Pat,
    RecordField, RecordSpread, Root, SelectResolution, Stmt, Type,
};
use num_bigint::BigInt;

pub fn run_program(program: &mono::Program) -> Result<Vec<Value>, RuntimeError> {
    Runtime::new(program).run()
}

type RuntimeResult<'a> = Result<EvalResult<'a>, RuntimeError>;
type Continuation<'a> = Rc<dyn Fn(&mut Runtime<'a>, Value) -> RuntimeResult<'a> + 'a>;

enum EvalResult<'a> {
    Value(Value),
    Request(Request<'a>),
}

#[derive(Clone)]
struct Request<'a> {
    path: Vec<String>,
    payload: Value,
    resume: Continuation<'a>,
}

pub struct Runtime<'a> {
    program: &'a mono::Program,
    instances: HashMap<InstanceId, Value>,
    evaluating_instances: HashSet<InstanceId>,
    continuations: HashMap<ContinuationId, Continuation<'a>>,
    next_continuation_id: u32,
}

impl<'a> Runtime<'a> {
    pub fn new(program: &'a mono::Program) -> Self {
        Self {
            program,
            instances: HashMap::new(),
            evaluating_instances: HashSet::new(),
            continuations: HashMap::new(),
            next_continuation_id: 0,
        }
    }

    pub fn run(&mut self) -> Result<Vec<Value>, RuntimeError> {
        let mut results = Vec::with_capacity(self.program.roots.len());
        let mut env = CapturedEnv::default();
        for root in &self.program.roots {
            let result = match root {
                Root::Instance(instance) => EvalResult::Value(self.eval_instance(*instance)?),
                Root::Expr(expr) => self.eval_expr(expr, &mut env)?,
            };
            match result {
                EvalResult::Value(value) => results.push(value),
                EvalResult::Request(request) => {
                    return Err(RuntimeError::UnhandledEffect { path: request.path });
                }
            }
        }
        Ok(results)
    }

    fn eval_instance(&mut self, instance: InstanceId) -> Result<Value, RuntimeError> {
        if let Some(value) = self.instances.get(&instance) {
            return Ok(value.clone());
        }
        if !self.evaluating_instances.insert(instance) {
            return Err(RuntimeError::RecursiveInstance { instance });
        }
        let mono_instance = self
            .program
            .instances
            .get(instance.0 as usize)
            .ok_or(RuntimeError::MissingInstance { instance })?;
        if mono_instance.id != instance {
            self.evaluating_instances.remove(&instance);
            return Err(RuntimeError::MismatchedInstanceSlot {
                requested: instance,
                actual: mono_instance.id,
            });
        }

        let mut env = CapturedEnv::default();
        let value = self.eval_expr(&mono_instance.body, &mut env);
        self.evaluating_instances.remove(&instance);
        let value = expect_eval_value(value?)?;
        self.instances.insert(instance, value.clone());
        Ok(value)
    }

    fn eval_expr(&mut self, expr: &Expr, env: &mut CapturedEnv) -> RuntimeResult<'a> {
        match &expr.kind {
            ExprKind::Lit(lit) => value_result(Value::from(lit)),
            ExprKind::PrimitiveOp(name) => Err(RuntimeError::UnsupportedExpr {
                feature: format!("primitive op {name}"),
            }),
            ExprKind::EffectOp { path } => value_result(Value::EffectOp { path: path.clone() }),
            ExprKind::Local(def) => value_result(
                env.locals
                    .get(def)
                    .cloned()
                    .ok_or(RuntimeError::UnboundLocal { def: *def })?,
            ),
            ExprKind::InstanceRef(instance) => value_result(self.eval_instance(*instance)?),
            ExprKind::Coerce {
                source,
                target,
                expr,
            } => {
                let source = source.clone();
                let target = target.clone();
                let result = self.eval_expr(expr, env)?;
                self.continue_with(result, move |runtime, value| {
                    runtime.adapt_value(value, &source, &target)
                })
            }
            ExprKind::MakeThunk { body, .. } => value_result(Value::Thunk(Thunk::Expr {
                body: body.as_ref().clone(),
                env: env.clone(),
            })),
            ExprKind::ForceThunk { thunk, .. } => {
                let result = self.eval_expr(thunk, env)?;
                self.continue_with(result, |runtime, thunk| runtime.force_thunk(thunk))
            }
            ExprKind::FunctionAdapter {
                source,
                target,
                function,
                hygiene,
            } => {
                let function = self.eval_expr(function, env)?;
                let source = source.clone();
                let target = target.clone();
                let hygiene = hygiene.clone();
                self.continue_with(function, move |_, function| {
                    value_result(Value::FunctionAdapter(FunctionAdapter {
                        source: source.clone(),
                        target: target.clone(),
                        function: Box::new(function),
                        hygiene: hygiene.clone(),
                    }))
                })
            }
            ExprKind::Apply(callee, arg) => {
                let arg = arg.as_ref().clone();
                let env_for_arg = env.clone();
                let callee = self.eval_expr(callee, env)?;
                self.continue_with(callee, move |runtime, callee| {
                    let mut env = env_for_arg.clone();
                    let arg_result = runtime.eval_expr(&arg, &mut env)?;
                    runtime.continue_with(arg_result, move |runtime, arg| {
                        runtime.apply_value(callee.clone(), arg)
                    })
                })
            }
            ExprKind::RefSet(_, _) => Err(RuntimeError::UnsupportedExpr {
                feature: "ref set".to_string(),
            }),
            ExprKind::Lambda(param, body) => value_result(Value::Closure(Closure {
                param: param.clone(),
                body: body.as_ref().clone(),
                env: env.clone(),
            })),
            ExprKind::Tuple(items) => self.eval_tuple(items.clone(), env.clone()),
            ExprKind::Record { fields, spread } => {
                self.eval_record(fields.clone(), spread.clone(), env.clone())
            }
            ExprKind::PolyVariant { tag, payloads } => {
                self.eval_poly_variant(tag.clone(), payloads.clone(), env.clone())
            }
            ExprKind::Select {
                base,
                name,
                resolution,
            } => self.eval_select(base, name, *resolution, env),
            ExprKind::Case { scrutinee, arms } => {
                let scrutinee = self.eval_expr(scrutinee, env)?;
                let arms = arms.clone();
                let env = env.clone();
                self.continue_with(scrutinee, move |runtime, scrutinee| {
                    runtime.eval_case(scrutinee, arms.clone(), env.clone())
                })
            }
            ExprKind::Catch { body, arms } => self.eval_catch(body, arms, env),
            ExprKind::Block(block) => self.eval_block(block, env),
        }
    }

    fn eval_record(
        &mut self,
        fields: Vec<RecordField>,
        spread: RecordSpread<Box<Expr>>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        match spread {
            RecordSpread::None => self.eval_record_fields(fields, env, Vec::new(), 0),
            RecordSpread::Head(expr) => {
                let mut spread_env = env.clone();
                let spread = self.eval_expr(&expr, &mut spread_env)?;
                self.continue_with(spread, move |runtime, spread| {
                    let spread_fields = runtime.expect_record(spread)?;
                    runtime.eval_record_fields(fields.clone(), env.clone(), spread_fields, 0)
                })
            }
            RecordSpread::Tail(expr) => {
                let fields_result = self.eval_record_fields(fields, env.clone(), Vec::new(), 0)?;
                self.continue_with(fields_result, move |runtime, fields| {
                    let fields = runtime.expect_record(fields)?;
                    let mut spread_env = env.clone();
                    let spread = runtime.eval_expr(&expr, &mut spread_env)?;
                    runtime.continue_with(spread, move |runtime, spread| {
                        let mut fields = fields.clone();
                        fields.extend(runtime.expect_record(spread)?);
                        value_result(Value::Record(fields))
                    })
                })
            }
        }
    }

    fn eval_tuple(&mut self, items: Vec<Expr>, env: CapturedEnv) -> RuntimeResult<'a> {
        self.eval_tuple_items(items, env, Vec::new(), 0)
    }

    fn eval_tuple_items(
        &mut self,
        items: Vec<Expr>,
        env: CapturedEnv,
        values: Vec<Value>,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index >= items.len() {
            return value_result(Value::Tuple(values));
        }

        let item = items[index].clone();
        let mut item_env = env.clone();
        let result = self.eval_expr(&item, &mut item_env)?;
        self.continue_with(result, move |runtime, value| {
            let mut values = values.clone();
            values.push(value);
            runtime.eval_tuple_items(items.clone(), env.clone(), values, index + 1)
        })
    }

    fn eval_poly_variant(
        &mut self,
        tag: String,
        payloads: Vec<Expr>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.eval_poly_variant_payloads(tag, payloads, env, Vec::new(), 0)
    }

    fn eval_poly_variant_payloads(
        &mut self,
        tag: String,
        payloads: Vec<Expr>,
        env: CapturedEnv,
        values: Vec<Value>,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index >= payloads.len() {
            return value_result(Value::PolyVariant {
                tag,
                payloads: values,
            });
        }

        let payload = payloads[index].clone();
        let mut payload_env = env.clone();
        let result = self.eval_expr(&payload, &mut payload_env)?;
        self.continue_with(result, move |runtime, value| {
            let mut values = values.clone();
            values.push(value);
            runtime.eval_poly_variant_payloads(
                tag.clone(),
                payloads.clone(),
                env.clone(),
                values,
                index + 1,
            )
        })
    }

    fn eval_record_fields(
        &mut self,
        fields: Vec<RecordField>,
        env: CapturedEnv,
        values: Vec<ValueField>,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index >= fields.len() {
            return value_result(Value::Record(values));
        }

        let field = fields[index].clone();
        let mut field_env = env.clone();
        let result = self.eval_expr(&field.value, &mut field_env)?;
        self.continue_with(result, move |runtime, value| {
            let mut values = values.clone();
            values.push(ValueField {
                name: field.name.clone(),
                value,
            });
            runtime.eval_record_fields(fields.clone(), env.clone(), values, index + 1)
        })
    }

    fn eval_select(
        &mut self,
        base: &Expr,
        name: &str,
        resolution: Option<SelectResolution>,
        env: &mut CapturedEnv,
    ) -> RuntimeResult<'a> {
        let result = self.eval_expr(base, env)?;
        let name = name.to_string();
        self.continue_with(result, move |runtime, base| match resolution {
            Some(SelectResolution::RecordField) => {
                value_result(runtime.project_record_field(base, &name)?)
            }
            Some(SelectResolution::Method { instance }) => {
                let method = runtime.eval_instance(instance)?;
                runtime.apply_value(method, base)
            }
            Some(SelectResolution::TypeclassMethod { member }) => {
                Err(RuntimeError::UnsupportedExpr {
                    feature: format!("typeclass method d{}", member.0),
                })
            }
            None => Err(RuntimeError::UnresolvedSelect { name: name.clone() }),
        })
    }

    fn eval_case(
        &mut self,
        scrutinee: Value,
        arms: Vec<CaseArm>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.eval_case_arm(scrutinee, arms, env, 0)
    }

    fn eval_case_arm(
        &mut self,
        scrutinee: Value,
        arms: Vec<CaseArm>,
        env: CapturedEnv,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index >= arms.len() {
            return Err(RuntimeError::NoMatchingCase);
        }

        let arm = arms[index].clone();
        let mut arm_env = env.clone();
        if !self.bind_pat(&arm.pat, &scrutinee, &mut arm_env)? {
            return self.eval_case_arm(scrutinee, arms, env, index + 1);
        }
        let Some(guard) = arm.guard else {
            return self.eval_expr(&arm.body, &mut arm_env);
        };

        let guard_result = self.eval_expr(&guard, &mut arm_env)?;
        self.continue_with(guard_result, move |runtime, guard| match guard {
            Value::Bool(true) => runtime.eval_expr(&arm.body, &mut arm_env.clone()),
            Value::Bool(false) => {
                runtime.eval_case_arm(scrutinee.clone(), arms.clone(), env.clone(), index + 1)
            }
            value => Err(RuntimeError::NonBoolGuard { value }),
        })
    }

    fn eval_catch(
        &mut self,
        body: &Expr,
        arms: &[CatchArm],
        env: &mut CapturedEnv,
    ) -> RuntimeResult<'a> {
        let arms = arms.to_vec();
        let catch_env = env.clone();
        let result = self.eval_expr(body, env)?;
        self.handle_catch_result(result, arms, catch_env)
    }

    fn handle_catch_result(
        &mut self,
        result: EvalResult<'a>,
        arms: Vec<CatchArm>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        match result {
            EvalResult::Value(value) => self.handle_catch_value(value, &arms, &env),
            EvalResult::Request(request) => self.handle_catch_request(request, arms, env),
        }
    }

    fn handle_catch_value(
        &mut self,
        value: Value,
        arms: &[CatchArm],
        env: &CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.handle_catch_value_arm(value, arms.to_vec(), env.clone(), 0)
    }

    fn handle_catch_value_arm(
        &mut self,
        value: Value,
        arms: Vec<CatchArm>,
        env: CapturedEnv,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index >= arms.len() {
            return value_result(value);
        }

        let arm = arms[index].clone();
        if arm.operation_path.is_some() {
            return self.handle_catch_value_arm(value, arms, env, index + 1);
        }

        let mut arm_env = env.clone();
        if !self.bind_pat(&arm.pat, &value, &mut arm_env)? {
            return self.handle_catch_value_arm(value, arms, env, index + 1);
        }
        let Some(guard) = arm.guard else {
            return self.eval_expr(&arm.body, &mut arm_env);
        };

        let guard_result = self.eval_expr(&guard, &mut arm_env)?;
        self.continue_with(guard_result, move |runtime, guard| match guard {
            Value::Bool(true) => runtime.eval_expr(&arm.body, &mut arm_env.clone()),
            Value::Bool(false) => {
                runtime.handle_catch_value_arm(value.clone(), arms.clone(), env.clone(), index + 1)
            }
            value => Err(RuntimeError::NonBoolGuard { value }),
        })
    }

    fn handle_catch_request(
        &mut self,
        request: Request<'a>,
        arms: Vec<CatchArm>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.handle_catch_request_arm(request, arms, env, 0)
    }

    fn handle_catch_request_arm(
        &mut self,
        request: Request<'a>,
        arms: Vec<CatchArm>,
        env: CapturedEnv,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index < arms.len() {
            let arm = arms[index].clone();
            if arm.operation_path.as_ref() != Some(&request.path) {
                return self.handle_catch_request_arm(request, arms, env, index + 1);
            }

            let mut arm_env = env.clone();
            if !self.bind_pat(&arm.pat, &request.payload, &mut arm_env)? {
                return self.handle_catch_request_arm(request, arms, env, index + 1);
            }
            if let Some(continuation) = &arm.continuation {
                let id = self.store_continuation(request.resume.clone());
                if !self.bind_pat(continuation, &Value::Continuation(id), &mut arm_env)? {
                    return self.handle_catch_request_arm(request, arms, env, index + 1);
                }
            }
            let Some(guard) = arm.guard else {
                return self.eval_expr(&arm.body, &mut arm_env);
            };

            let guard_result = self.eval_expr(&guard, &mut arm_env)?;
            return self.continue_with(guard_result, move |runtime, guard| match guard {
                Value::Bool(true) => runtime.eval_expr(&arm.body, &mut arm_env.clone()),
                Value::Bool(false) => runtime.handle_catch_request_arm(
                    request.clone(),
                    arms.clone(),
                    env.clone(),
                    index + 1,
                ),
                value => Err(RuntimeError::NonBoolGuard { value }),
            });
        }

        let arms_for_resume = arms.clone();
        let env_for_resume = env.clone();
        let resume = request.resume.clone();
        Ok(EvalResult::Request(Request {
            path: request.path,
            payload: request.payload,
            resume: Rc::new(move |runtime, value| {
                let resumed = resume(runtime, value)?;
                runtime.handle_catch_result(
                    resumed,
                    arms_for_resume.clone(),
                    env_for_resume.clone(),
                )
            }),
        }))
    }

    fn eval_block(&mut self, block: &Block, env: &mut CapturedEnv) -> RuntimeResult<'a> {
        self.eval_block_parts(
            block.stmts.clone(),
            block.tail.as_deref().cloned(),
            env.clone(),
        )
    }

    fn eval_block_parts(
        &mut self,
        stmts: Vec<Stmt>,
        tail: Option<Expr>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.eval_block_step(stmts, tail, env, 0, Value::Unit)
    }

    fn eval_block_step(
        &mut self,
        stmts: Vec<Stmt>,
        tail: Option<Expr>,
        mut env: CapturedEnv,
        index: usize,
        last: Value,
    ) -> RuntimeResult<'a> {
        if index >= stmts.len() {
            if let Some(tail) = tail {
                return self.eval_expr(&tail, &mut env);
            }
            return value_result(last);
        }

        match stmts[index].clone() {
            Stmt::Let(_, pat, expr) => {
                let result = self.eval_expr(&expr, &mut env)?;
                self.continue_with(result, move |runtime, value| {
                    let mut next_env = env.clone();
                    if !runtime.bind_pat(&pat, &value, &mut next_env)? {
                        return Err(RuntimeError::PatternMismatch);
                    }
                    runtime.eval_block_step(stmts.clone(), tail.clone(), next_env, index + 1, value)
                })
            }
            Stmt::Expr(expr) => {
                let result = self.eval_expr(&expr, &mut env)?;
                self.continue_with(result, move |runtime, value| {
                    runtime.eval_block_step(
                        stmts.clone(),
                        tail.clone(),
                        env.clone(),
                        index + 1,
                        value,
                    )
                })
            }
            Stmt::Module(_, module_stmts) => {
                let result = self.eval_block_parts(module_stmts, None, env.clone())?;
                self.continue_with(result, move |runtime, value| {
                    runtime.eval_block_step(
                        stmts.clone(),
                        tail.clone(),
                        env.clone(),
                        index + 1,
                        value,
                    )
                })
            }
        }
    }

    fn apply_value(&mut self, callee: Value, arg: Value) -> RuntimeResult<'a> {
        match callee {
            Value::Closure(closure) => self.apply_closure(closure, arg),
            Value::FunctionAdapter(adapter) => self.apply_adapter(adapter, arg),
            Value::EffectOp { path } => Ok(EvalResult::Request(Request {
                path,
                payload: arg,
                resume: Rc::new(|_, value| value_result(value)),
            })),
            Value::Continuation(id) => {
                let resume = self
                    .continuations
                    .get(&id)
                    .cloned()
                    .ok_or(RuntimeError::MissingContinuation { id })?;
                resume(self, arg)
            }
            value => Err(RuntimeError::NotFunction { value }),
        }
    }

    fn apply_closure(&mut self, closure: Closure, arg: Value) -> RuntimeResult<'a> {
        let mut env = closure.env;
        if !self.bind_pat(&closure.param, &arg, &mut env)? {
            return Err(RuntimeError::PatternMismatch);
        }
        self.eval_expr(&closure.body, &mut env)
    }

    fn apply_adapter(&mut self, adapter: FunctionAdapter, arg: Value) -> RuntimeResult<'a> {
        if !adapter.hygiene.markers.is_empty() {
            return Err(RuntimeError::UnsupportedBoundary {
                feature: "function adapter hygiene".to_string(),
            });
        }
        let (source_arg, source_ret) =
            function_parts(&adapter.source).ok_or(RuntimeError::ExpectedFunctionType)?;
        let (target_arg, target_ret) =
            function_parts(&adapter.target).ok_or(RuntimeError::ExpectedFunctionType)?;
        let source_arg = source_arg.clone();
        let source_ret = source_ret.clone();
        let target_arg = target_arg.clone();
        let target_ret = target_ret.clone();
        let function = *adapter.function;
        let arg = self.adapt_value(arg, &target_arg, &source_arg)?;
        self.continue_with(arg, move |runtime, arg| {
            let result = runtime.apply_value(function.clone(), arg)?;
            let source_ret = source_ret.clone();
            let target_ret = target_ret.clone();
            runtime.continue_with(result, move |runtime, result| {
                runtime.adapt_value(result, &source_ret, &target_ret)
            })
        })
    }

    fn bind_pat(
        &mut self,
        pat: &Pat,
        value: &Value,
        env: &mut CapturedEnv,
    ) -> Result<bool, RuntimeError> {
        match pat {
            Pat::Wild => Ok(true),
            Pat::Lit(lit) => Ok(value == &Value::from(lit)),
            Pat::Tuple(items) => {
                let Value::Tuple(values) = value else {
                    return Ok(false);
                };
                if items.len() != values.len() {
                    return Ok(false);
                }
                for (pat, value) in items.iter().zip(values) {
                    if !self.bind_pat(pat, value, env)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pat::List { .. } => Err(RuntimeError::UnsupportedPattern {
                feature: "list pattern".to_string(),
            }),
            Pat::Record { fields, spread } => {
                let Value::Record(record_fields) = value else {
                    return Ok(false);
                };
                let mut consumed = HashSet::new();
                for (name, pat) in fields {
                    let Some((index, field)) = record_field_with_index(record_fields, name) else {
                        return Ok(false);
                    };
                    consumed.insert(index);
                    if !self.bind_pat(pat, &field.value, env)? {
                        return Ok(false);
                    }
                }
                if let Some(def) = record_spread_def(spread) {
                    let captured = record_fields
                        .iter()
                        .enumerate()
                        .filter(|(index, _)| !consumed.contains(index))
                        .map(|(_, field)| field.clone())
                        .collect();
                    env.locals.insert(def, Value::Record(captured));
                }
                Ok(true)
            }
            Pat::PolyVariant(tag, payload_pats) => {
                let Value::PolyVariant {
                    tag: value_tag,
                    payloads,
                } = value
                else {
                    return Ok(false);
                };
                if tag != value_tag || payload_pats.len() != payloads.len() {
                    return Ok(false);
                }
                for (pat, value) in payload_pats.iter().zip(payloads) {
                    if !self.bind_pat(pat, value, env)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pat::Con(_, _) => Err(RuntimeError::UnsupportedPattern {
                feature: "constructor pattern".to_string(),
            }),
            Pat::Ref(instance) => {
                let expected = self.eval_instance(*instance)?;
                Ok(value == &expected)
            }
            Pat::Var(def) => {
                env.locals.insert(*def, value.clone());
                Ok(true)
            }
            Pat::Or(left, right) => {
                let mut left_env = env.clone();
                if self.bind_pat(left, value, &mut left_env)? {
                    *env = left_env;
                    return Ok(true);
                }
                self.bind_pat(right, value, env)
            }
            Pat::As(pat, def) => {
                if !self.bind_pat(pat, value, env)? {
                    return Ok(false);
                }
                env.locals.insert(*def, value.clone());
                Ok(true)
            }
        }
    }

    fn adapt_value(&mut self, value: Value, source: &Type, target: &Type) -> RuntimeResult<'a> {
        if equivalent_runtime_types(source, target) || matches!(target, Type::Any) {
            return value_result(value);
        }
        match (source, target) {
            (Type::Thunk { .. }, target) => {
                let source_value = thunk_value_type(source).unwrap_or(source).clone();
                let target = target.clone();
                let value = self.force_thunk(value)?;
                self.continue_with(value, move |runtime, value| {
                    runtime.adapt_value(value, &source_value, &target)
                })
            }
            (source, Type::Thunk { .. }) => {
                let target_value = thunk_value_type(target).unwrap_or(target).clone();
                let source = source.clone();
                let value = self.adapt_value(value, &source, &target_value)?;
                self.continue_with(value, |_, value| {
                    value_result(Value::Thunk(Thunk::Value(Box::new(value))))
                })
            }
            _ => Err(RuntimeError::UnsupportedBoundary {
                feature: format!(
                    "coerce {} => {}",
                    mono::dump::dump_type(source),
                    mono::dump::dump_type(target)
                ),
            }),
        }
    }

    fn force_thunk(&mut self, thunk: Value) -> RuntimeResult<'a> {
        match thunk {
            Value::Thunk(Thunk::Expr { body, mut env }) => self.eval_expr(&body, &mut env),
            Value::Thunk(Thunk::Value(value)) => value_result(*value),
            value => Err(RuntimeError::NotThunk { value }),
        }
    }

    fn continue_with(
        &mut self,
        result: EvalResult<'a>,
        continuation: impl Fn(&mut Runtime<'a>, Value) -> RuntimeResult<'a> + 'a,
    ) -> RuntimeResult<'a> {
        self.continue_with_rc(result, Rc::new(continuation))
    }

    fn continue_with_rc(
        &mut self,
        result: EvalResult<'a>,
        continuation: Continuation<'a>,
    ) -> RuntimeResult<'a> {
        match result {
            EvalResult::Value(value) => continuation(self, value),
            EvalResult::Request(request) => {
                let request_resume = request.resume.clone();
                Ok(EvalResult::Request(Request {
                    path: request.path,
                    payload: request.payload,
                    resume: Rc::new(move |runtime, value| {
                        let resumed = request_resume(runtime, value)?;
                        runtime.continue_with_rc(resumed, continuation.clone())
                    }),
                }))
            }
        }
    }

    fn store_continuation(&mut self, continuation: Continuation<'a>) -> ContinuationId {
        let id = ContinuationId(self.next_continuation_id);
        self.next_continuation_id += 1;
        self.continuations.insert(id, continuation);
        id
    }

    fn expect_record(&self, value: Value) -> Result<Vec<ValueField>, RuntimeError> {
        match value {
            Value::Record(fields) => Ok(fields),
            value => Err(RuntimeError::ExpectedRecord { value }),
        }
    }

    fn project_record_field(&self, value: Value, name: &str) -> Result<Value, RuntimeError> {
        match value {
            Value::Record(fields) => fields
                .iter()
                .rev()
                .find(|field| field.name == name)
                .map(|field| field.value.clone())
                .ok_or_else(|| RuntimeError::MissingRecordField {
                    name: name.to_string(),
                }),
            value => Err(RuntimeError::ExpectedRecord { value }),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    BigInt(BigInt),
    Float(f64),
    Str(String),
    Bool(bool),
    Unit,
    Tuple(Vec<Value>),
    Record(Vec<ValueField>),
    PolyVariant { tag: String, payloads: Vec<Value> },
    Closure(Closure),
    Thunk(Thunk),
    FunctionAdapter(FunctionAdapter),
    EffectOp { path: Vec<String> },
    Continuation(ContinuationId),
}

impl From<&Lit> for Value {
    fn from(lit: &Lit) -> Self {
        match lit {
            Lit::Int(value) => Self::Int(*value),
            Lit::BigInt(value) => Self::BigInt(value.clone()),
            Lit::Float(value) => Self::Float(*value),
            Lit::Str(value) => Self::Str(value.clone()),
            Lit::Bool(value) => Self::Bool(*value),
            Lit::Unit => Self::Unit,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ValueField {
    pub name: String,
    pub value: Value,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    pub param: Pat,
    pub body: Expr,
    env: CapturedEnv,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Thunk {
    Expr { body: Expr, env: CapturedEnv },
    Value(Box<Value>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionAdapter {
    pub source: Type,
    pub target: Type,
    pub function: Box<Value>,
    pub hygiene: FunctionAdapterHygiene,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct CapturedEnv {
    locals: HashMap<DefId, Value>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ContinuationId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub enum RuntimeError {
    MissingInstance {
        instance: InstanceId,
    },
    MismatchedInstanceSlot {
        requested: InstanceId,
        actual: InstanceId,
    },
    RecursiveInstance {
        instance: InstanceId,
    },
    UnboundLocal {
        def: DefId,
    },
    MissingContinuation {
        id: ContinuationId,
    },
    UnresolvedSelect {
        name: String,
    },
    MissingRecordField {
        name: String,
    },
    NotFunction {
        value: Value,
    },
    NotThunk {
        value: Value,
    },
    ExpectedRecord {
        value: Value,
    },
    ExpectedFunctionType,
    PatternMismatch,
    NoMatchingCase,
    NonBoolGuard {
        value: Value,
    },
    UnsupportedExpr {
        feature: String,
    },
    UnsupportedPattern {
        feature: String,
    },
    UnsupportedBoundary {
        feature: String,
    },
    UnhandledEffect {
        path: Vec<String>,
    },
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingInstance { instance } => write!(f, "missing instance m{}", instance.0),
            Self::MismatchedInstanceSlot { requested, actual } => write!(
                f,
                "mismatched instance slot: requested m{}, found m{}",
                requested.0, actual.0
            ),
            Self::RecursiveInstance { instance } => {
                write!(f, "recursive instance evaluation m{}", instance.0)
            }
            Self::UnboundLocal { def } => write!(f, "unbound local d{}", def.0),
            Self::MissingContinuation { id } => write!(f, "missing continuation k{}", id.0),
            Self::UnresolvedSelect { name } => write!(f, "unresolved select .{name}"),
            Self::MissingRecordField { name } => write!(f, "missing record field {name}"),
            Self::NotFunction { value } => write!(f, "value is not a function: {value:?}"),
            Self::NotThunk { value } => write!(f, "value is not a thunk: {value:?}"),
            Self::ExpectedRecord { value } => write!(f, "expected record, got {value:?}"),
            Self::ExpectedFunctionType => write!(f, "expected function type"),
            Self::PatternMismatch => write!(f, "pattern mismatch"),
            Self::NoMatchingCase => write!(f, "no matching case arm"),
            Self::NonBoolGuard { value } => write!(f, "case guard returned non-bool {value:?}"),
            Self::UnsupportedExpr { feature } => write!(f, "unsupported expression: {feature}"),
            Self::UnsupportedPattern { feature } => write!(f, "unsupported pattern: {feature}"),
            Self::UnsupportedBoundary { feature } => write!(f, "unsupported boundary: {feature}"),
            Self::UnhandledEffect { path } => write!(f, "unhandled effect {}", path.join("::")),
        }
    }
}

impl std::error::Error for RuntimeError {}

fn function_parts(ty: &Type) -> Option<(&Type, &Type)> {
    let Type::Fun { arg, ret, .. } = ty else {
        return None;
    };
    Some((arg, ret))
}

fn thunk_value_type(ty: &Type) -> Option<&Type> {
    let Type::Thunk { value, .. } = ty else {
        return None;
    };
    Some(value)
}

fn equivalent_runtime_types(source: &Type, target: &Type) -> bool {
    source == target || source.is_pure_effect() && target.is_pure_effect()
}

fn record_spread_def(spread: &RecordSpread<DefId>) -> Option<DefId> {
    match spread {
        RecordSpread::Head(def) | RecordSpread::Tail(def) => Some(*def),
        RecordSpread::None => None,
    }
}

fn record_field_with_index<'a>(
    fields: &'a [ValueField],
    name: &str,
) -> Option<(usize, &'a ValueField)> {
    fields
        .iter()
        .enumerate()
        .rev()
        .find(|(_, field)| field.name == name)
}

fn value_result<'a>(value: Value) -> RuntimeResult<'a> {
    Ok(EvalResult::Value(value))
}

fn expect_eval_value(result: EvalResult<'_>) -> Result<Value, RuntimeError> {
    match result {
        EvalResult::Value(value) => Ok(value),
        EvalResult::Request(request) => Err(RuntimeError::UnhandledEffect { path: request.path }),
    }
}

#[cfg(test)]
mod tests {
    use mono::{
        Block, CatchArm, Expr, ExprKind, Instance, InstanceId, InstanceSource, Lit, Pat, Program,
        Root, Signature, Stmt, Type, Vis,
    };

    use super::{Value, run_program};

    #[test]
    fn runs_literal_root() {
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Lit(Lit::Int(1))))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(1)]));
    }

    #[test]
    fn stores_root_instance_for_later_instance_ref() {
        let program = Program {
            roots: vec![
                Root::Instance(InstanceId(0)),
                Root::Expr(Expr::new(ExprKind::InstanceRef(InstanceId(0)))),
            ],
            instances: vec![Instance {
                id: InstanceId(0),
                source: InstanceSource::Def(mono::DefId(0)),
                signature: Signature { ty: int_type() },
                body: Expr::new(ExprKind::Lit(Lit::Int(1))),
            }],
        };

        assert_eq!(
            run_program(&program),
            Ok(vec![Value::Int(1), Value::Int(1)])
        );
    }

    #[test]
    fn runs_lambda_application() {
        let param = mono::DefId(10);
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Apply(
                Box::new(Expr::new(ExprKind::Lambda(
                    Pat::Var(param),
                    Box::new(Expr::new(ExprKind::Local(param))),
                ))),
                Box::new(Expr::new(ExprKind::Lit(Lit::Int(7)))),
            )))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(7)]));
    }

    #[test]
    fn runs_block_let_and_tail() {
        let local = mono::DefId(2);
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Block(Block {
                stmts: vec![Stmt::Let(
                    Vis::My,
                    Pat::Var(local),
                    Expr::new(ExprKind::Lit(Lit::Int(3))),
                )],
                tail: Some(Box::new(Expr::new(ExprKind::Local(local)))),
            })))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(3)]));
    }

    #[test]
    fn forces_thunk_only_at_force_node() {
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::ForceThunk {
                source: mono::EffectiveThunkType {
                    effect: Type::pure_effect(),
                    value: int_type(),
                },
                target: mono::ComputationType {
                    effect: Type::pure_effect(),
                    value: int_type(),
                },
                thunk: Box::new(Expr::new(ExprKind::MakeThunk {
                    source: mono::ComputationType {
                        effect: Type::pure_effect(),
                        value: int_type(),
                    },
                    target: mono::EffectiveThunkType {
                        effect: Type::pure_effect(),
                        value: int_type(),
                    },
                    body: Box::new(Expr::new(ExprKind::Lit(Lit::Int(9)))),
                })),
            }))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(9)]));
    }

    #[test]
    fn catches_matching_effect_request() {
        let payload = mono::DefId(1);
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
                body: Box::new(effect_call(
                    path(&["out", "say"]),
                    ExprKind::Lit(Lit::Int(1)),
                )),
                arms: vec![CatchArm {
                    operation_path: Some(path(&["out", "say"])),
                    pat: Pat::Var(payload),
                    continuation: Some(Pat::Wild),
                    guard: None,
                    body: Expr::new(ExprKind::Local(payload)),
                }],
            }))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(1)]));
    }

    #[test]
    fn handler_continuation_resumes_block_after_request() {
        let payload = mono::DefId(1);
        let continuation = mono::DefId(2);
        let local = mono::DefId(3);
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
                body: Box::new(Expr::new(ExprKind::Block(Block {
                    stmts: vec![Stmt::Let(
                        Vis::My,
                        Pat::Var(local),
                        effect_call(path(&["ask", "value"]), ExprKind::Lit(Lit::Unit)),
                    )],
                    tail: Some(Box::new(Expr::new(ExprKind::Local(local)))),
                }))),
                arms: vec![CatchArm {
                    operation_path: Some(path(&["ask", "value"])),
                    pat: Pat::Var(payload),
                    continuation: Some(Pat::Var(continuation)),
                    guard: None,
                    body: Expr::new(ExprKind::Apply(
                        Box::new(Expr::new(ExprKind::Local(continuation))),
                        Box::new(Expr::new(ExprKind::Lit(Lit::Int(7)))),
                    )),
                }],
            }))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(7)]));
    }

    #[test]
    fn shallow_handler_searches_past_unhandled_request_until_matching_one() {
        let skip_continuation = mono::DefId(1);
        let target_payload = mono::DefId(2);
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
                body: Box::new(Expr::new(ExprKind::Catch {
                    body: Box::new(Expr::new(ExprKind::Block(Block {
                        stmts: vec![Stmt::Expr(effect_call(
                            path(&["skip", "go"]),
                            ExprKind::Lit(Lit::Unit),
                        ))],
                        tail: Some(Box::new(effect_call(
                            path(&["target", "hit"]),
                            ExprKind::Lit(Lit::Int(1)),
                        ))),
                    }))),
                    arms: vec![CatchArm {
                        operation_path: Some(path(&["target", "hit"])),
                        pat: Pat::Var(target_payload),
                        continuation: Some(Pat::Wild),
                        guard: None,
                        body: Expr::new(ExprKind::Local(target_payload)),
                    }],
                })),
                arms: vec![CatchArm {
                    operation_path: Some(path(&["skip", "go"])),
                    pat: Pat::Wild,
                    continuation: Some(Pat::Var(skip_continuation)),
                    guard: None,
                    body: Expr::new(ExprKind::Apply(
                        Box::new(Expr::new(ExprKind::Local(skip_continuation))),
                        Box::new(Expr::new(ExprKind::Lit(Lit::Unit))),
                    )),
                }],
            }))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(1)]));
    }

    #[test]
    fn resumes_tuple_construction_after_effect_request() {
        let payload = mono::DefId(1);
        let continuation = mono::DefId(2);
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
                body: Box::new(Expr::new(ExprKind::Tuple(vec![
                    Expr::new(ExprKind::Lit(Lit::Int(1))),
                    effect_call(path(&["ask", "tuple"]), ExprKind::Lit(Lit::Unit)),
                    Expr::new(ExprKind::Lit(Lit::Int(3))),
                ]))),
                arms: vec![CatchArm {
                    operation_path: Some(path(&["ask", "tuple"])),
                    pat: Pat::Var(payload),
                    continuation: Some(Pat::Var(continuation)),
                    guard: None,
                    body: Expr::new(ExprKind::Apply(
                        Box::new(Expr::new(ExprKind::Local(continuation))),
                        Box::new(Expr::new(ExprKind::Lit(Lit::Int(2)))),
                    )),
                }],
            }))],
            instances: Vec::new(),
        };

        assert_eq!(
            run_program(&program),
            Ok(vec![Value::Tuple(vec![
                Value::Int(1),
                Value::Int(2),
                Value::Int(3)
            ])])
        );
    }

    #[test]
    fn resumes_record_construction_after_effect_request() {
        let continuation = mono::DefId(2);
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
                body: Box::new(Expr::new(ExprKind::Record {
                    fields: vec![
                        mono::RecordField {
                            name: "a".to_string(),
                            value: Expr::new(ExprKind::Lit(Lit::Int(1))),
                        },
                        mono::RecordField {
                            name: "b".to_string(),
                            value: effect_call(path(&["ask", "record"]), ExprKind::Lit(Lit::Unit)),
                        },
                    ],
                    spread: mono::RecordSpread::None,
                })),
                arms: vec![CatchArm {
                    operation_path: Some(path(&["ask", "record"])),
                    pat: Pat::Wild,
                    continuation: Some(Pat::Var(continuation)),
                    guard: None,
                    body: Expr::new(ExprKind::Apply(
                        Box::new(Expr::new(ExprKind::Local(continuation))),
                        Box::new(Expr::new(ExprKind::Lit(Lit::Int(2)))),
                    )),
                }],
            }))],
            instances: Vec::new(),
        };

        assert_eq!(
            run_program(&program),
            Ok(vec![Value::Record(vec![
                super::ValueField {
                    name: "a".to_string(),
                    value: Value::Int(1),
                },
                super::ValueField {
                    name: "b".to_string(),
                    value: Value::Int(2),
                },
            ])])
        );
    }

    #[test]
    fn resumes_poly_variant_construction_after_effect_request() {
        let continuation = mono::DefId(2);
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
                body: Box::new(Expr::new(ExprKind::PolyVariant {
                    tag: "some".to_string(),
                    payloads: vec![effect_call(
                        path(&["ask", "variant"]),
                        ExprKind::Lit(Lit::Unit),
                    )],
                })),
                arms: vec![CatchArm {
                    operation_path: Some(path(&["ask", "variant"])),
                    pat: Pat::Wild,
                    continuation: Some(Pat::Var(continuation)),
                    guard: None,
                    body: Expr::new(ExprKind::Apply(
                        Box::new(Expr::new(ExprKind::Local(continuation))),
                        Box::new(Expr::new(ExprKind::Lit(Lit::Int(4)))),
                    )),
                }],
            }))],
            instances: Vec::new(),
        };

        assert_eq!(
            run_program(&program),
            Ok(vec![Value::PolyVariant {
                tag: "some".to_string(),
                payloads: vec![Value::Int(4)],
            }])
        );
    }

    #[test]
    fn resumes_case_guard_after_effect_request() {
        let continuation = mono::DefId(1);
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
                body: Box::new(Expr::new(ExprKind::Case {
                    scrutinee: Box::new(Expr::new(ExprKind::Lit(Lit::Unit))),
                    arms: vec![
                        mono::CaseArm {
                            pat: Pat::Wild,
                            guard: Some(effect_call(
                                path(&["ask", "guard"]),
                                ExprKind::Lit(Lit::Unit),
                            )),
                            body: Expr::new(ExprKind::Lit(Lit::Int(1))),
                        },
                        mono::CaseArm {
                            pat: Pat::Wild,
                            guard: None,
                            body: Expr::new(ExprKind::Lit(Lit::Int(2))),
                        },
                    ],
                })),
                arms: vec![CatchArm {
                    operation_path: Some(path(&["ask", "guard"])),
                    pat: Pat::Wild,
                    continuation: Some(Pat::Var(continuation)),
                    guard: None,
                    body: Expr::new(ExprKind::Apply(
                        Box::new(Expr::new(ExprKind::Local(continuation))),
                        Box::new(Expr::new(ExprKind::Lit(Lit::Bool(true)))),
                    )),
                }],
            }))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(1)]));
    }

    #[test]
    fn resumes_catch_request_guard_after_effect_request() {
        let guard_continuation = mono::DefId(1);
        let target_payload = mono::DefId(2);
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
                body: Box::new(Expr::new(ExprKind::Catch {
                    body: Box::new(effect_call(
                        path(&["target", "hit"]),
                        ExprKind::Lit(Lit::Int(1)),
                    )),
                    arms: vec![CatchArm {
                        operation_path: Some(path(&["target", "hit"])),
                        pat: Pat::Var(target_payload),
                        continuation: Some(Pat::Wild),
                        guard: Some(effect_call(
                            path(&["ask", "guard"]),
                            ExprKind::Lit(Lit::Unit),
                        )),
                        body: Expr::new(ExprKind::Local(target_payload)),
                    }],
                })),
                arms: vec![CatchArm {
                    operation_path: Some(path(&["ask", "guard"])),
                    pat: Pat::Wild,
                    continuation: Some(Pat::Var(guard_continuation)),
                    guard: None,
                    body: Expr::new(ExprKind::Apply(
                        Box::new(Expr::new(ExprKind::Local(guard_continuation))),
                        Box::new(Expr::new(ExprKind::Lit(Lit::Bool(true)))),
                    )),
                }],
            }))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(1)]));
    }

    #[test]
    fn runs_specialized_string_input_generic_call() {
        let lowering = lower_source("my id x = x\nid(1)\n");
        let program = specialize::specialize(&lowering.session.poly)
            .expect("source should specialize to mono program");

        assert_eq!(run_program(&program), Ok(vec![Value::Int(1)]));
    }

    fn lower_source(source: &str) -> infer::lowering::BodyLowering {
        let files = sources::load(vec![sources::SourceFile {
            module_path: sources::Path::default(),
            source: source.to_string(),
        }]);
        let output = infer::dump::dump_loaded_files(&files).expect("source should lower");
        assert!(
            output.lowering.errors.is_empty(),
            "body lowering errors: {:?}",
            output.lowering.errors
        );
        output.lowering
    }

    fn int_type() -> Type {
        Type::Con {
            path: vec!["int".to_string()],
            args: Vec::new(),
        }
    }

    fn path(parts: &[&str]) -> Vec<String> {
        parts.iter().map(|part| part.to_string()).collect()
    }

    fn effect_call(path: Vec<String>, payload: ExprKind) -> Expr {
        Expr::new(ExprKind::Apply(
            Box::new(Expr::new(ExprKind::EffectOp { path })),
            Box::new(Expr::new(payload)),
        ))
    }
}
