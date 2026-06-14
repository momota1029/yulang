//! `mono::Program` をそのまま読む oracle runtime。
//!
//! この crate は control VM の前に `specialize -> mono` 契約を検証するための実行器である。
//! 最適化や軽量 control 表現への lowering は `control-vm` 側で扱う。

#![forbid(unsafe_code)]

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use list_tree::{ListTree, ListView};
use mono::{
    Block, CaseArm, CatchArm, DefId, Expr, ExprKind, FunctionAdapterHygiene, InstanceId, Lit, Pat,
    PrimitiveContext, PrimitiveOp, RecordField, RecordSpread, Root, SelectResolution, Stmt, Type,
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
    guard_ids: Vec<GuardId>,
    payload: Value,
    resume: Continuation<'a>,
}

pub struct Runtime<'a> {
    program: &'a mono::Program,
    instances: HashMap<InstanceId, Value>,
    evaluating_instances: HashSet<InstanceId>,
    continuations: HashMap<ContinuationId, Continuation<'a>>,
    next_continuation_id: u32,
    guard_ids: Vec<GuardId>,
    active_markers: Vec<ValueMarker>,
    next_guard_id: u32,
}

impl<'a> Runtime<'a> {
    pub fn new(program: &'a mono::Program) -> Self {
        Self {
            program,
            instances: HashMap::new(),
            evaluating_instances: HashSet::new(),
            continuations: HashMap::new(),
            next_continuation_id: 0,
            guard_ids: Vec::new(),
            active_markers: Vec::new(),
            next_guard_id: 0,
        }
    }

    pub fn run(&mut self) -> Result<Vec<Value>, RuntimeError> {
        let mut results = Vec::new();
        let mut env = CapturedEnv::default();
        for root in &self.program.roots {
            let result = match root {
                Root::Instance(instance) => EvalResult::Value(self.eval_instance(*instance)?),
                Root::EvalInstance(instance) => EvalResult::Value(self.eval_instance(*instance)?),
                Root::Expr(expr) => self.eval_expr(expr, &mut env)?,
            };
            match result {
                EvalResult::Value(value) => {
                    if !matches!(root, Root::EvalInstance(_)) {
                        results.push(value);
                    }
                }
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
            ExprKind::PrimitiveOp { op, context } => self.eval_primitive_op(*op, context.clone()),
            ExprKind::Constructor { def, arity } => {
                value_result(constructor_value(*def, *arity, Vec::new()))
            }
            ExprKind::EffectOp { path } => value_result(Value::EffectOp { path: path.clone() }),
            ExprKind::Local(def) => value_result(
                self.mark_active_value(
                    env.locals
                        .get(def)
                        .cloned()
                        .ok_or(RuntimeError::UnboundLocal { def: *def })?,
                ),
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
            ExprKind::MakeThunk { body, .. } => {
                value_result(self.mark_active_value(Value::Thunk(Thunk::Expr {
                    body: body.as_ref().clone(),
                    env: env.clone(),
                })))
            }
            ExprKind::ForceThunk { target, thunk, .. } => {
                let target_value = target.value.clone();
                let result = self.eval_expr(thunk, env)?;
                self.continue_with(result, move |runtime, thunk| {
                    let result = runtime.force_thunk(thunk)?;
                    if matches!(target_value, Type::Thunk { .. }) {
                        return Ok(result);
                    }
                    runtime
                        .continue_with(result, |runtime, value| runtime.force_value_if_thunk(value))
                })
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
                self.continue_with(function, move |runtime, function| {
                    value_result(runtime.mark_active_value(Value::FunctionAdapter(
                        FunctionAdapter {
                            source: source.clone(),
                            target: target.clone(),
                            function: Box::new(function),
                            hygiene: hygiene.clone(),
                        },
                    )))
                })
            }
            ExprKind::MarkerFrame { path, body } => {
                let body = body.as_ref().clone();
                let mut frame_env = env.clone();
                let marker = ValueMarker {
                    id: self.fresh_guard_id(),
                    path: path.clone(),
                    depth: 1,
                    skip_own_path: false,
                };
                self.with_marker_frame(vec![marker], move |runtime| {
                    runtime.eval_expr(&body, &mut frame_env)
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
            ExprKind::Lambda(param, body) => {
                value_result(self.mark_active_value(Value::Closure(Closure {
                    param: param.clone(),
                    body: body.as_ref().clone(),
                    env: env.clone(),
                })))
            }
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
            if arm.operation_path.as_ref() != Some(&request.path)
                || self.request_intersects_guard_stack(&request)
            {
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
            guard_ids: request.guard_ids,
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
            Value::Marked { value, markers } => {
                let markers = markers_for_function_call(markers);
                self.with_marker_frame(markers, move |runtime| runtime.apply_value(*value, arg))
            }
            Value::PrimitiveOp(primitive) => self.apply_primitive_op(primitive, arg),
            Value::ConstructorFunction(constructor) => {
                value_result(apply_constructor(constructor, arg))
            }
            Value::Closure(closure) => self.apply_closure(closure, arg),
            Value::FunctionAdapter(adapter) => self.apply_adapter(adapter, arg),
            Value::EffectOp { path } => value_result(Value::Thunk(Thunk::Effect {
                path,
                payload: Box::new(arg),
            })),
            Value::Continuation(id) => value_result(Value::Thunk(Thunk::Continuation {
                id,
                arg: Box::new(arg),
            })),
            value => Err(RuntimeError::NotFunction { value }),
        }
    }

    fn eval_primitive_op(
        &mut self,
        op: PrimitiveOp,
        context: PrimitiveContext,
    ) -> RuntimeResult<'a> {
        if op.arity() == 0 {
            return value_result(apply_primitive(op, &context, &[])?);
        }
        value_result(Value::PrimitiveOp(PrimitiveValue {
            op,
            context,
            args: Vec::new(),
        }))
    }

    fn apply_primitive_op(
        &mut self,
        mut primitive: PrimitiveValue,
        arg: Value,
    ) -> RuntimeResult<'a> {
        primitive.args.push(arg);
        if primitive.args.len() < primitive.op.arity() {
            return value_result(Value::PrimitiveOp(primitive));
        }
        value_result(apply_primitive(
            primitive.op,
            &primitive.context,
            &primitive.args,
        )?)
    }

    fn apply_closure(&mut self, closure: Closure, arg: Value) -> RuntimeResult<'a> {
        let mut env = closure.env;
        if !self.bind_pat(&closure.param, &arg, &mut env)? {
            return Err(RuntimeError::PatternMismatch);
        }
        self.eval_expr(&closure.body, &mut env)
    }

    fn apply_adapter(&mut self, adapter: FunctionAdapter, arg: Value) -> RuntimeResult<'a> {
        let (source_arg, source_ret) =
            function_parts(&adapter.source).ok_or(RuntimeError::ExpectedFunctionType)?;
        let (target_arg, target_ret) =
            function_parts(&adapter.target).ok_or(RuntimeError::ExpectedFunctionType)?;
        let source_arg = source_arg.clone();
        let source_ret = source_ret.clone();
        let target_arg = target_arg.clone();
        let target_ret = target_ret.clone();
        let function = *adapter.function;
        let markers = self.instantiate_hygiene(&adapter.hygiene);
        self.with_marker_frame(markers.clone(), move |runtime| {
            let arg = mark_value(arg.clone(), &markers);
            let arg = runtime.adapt_value(arg, &target_arg, &source_arg)?;
            runtime.continue_with(arg, move |runtime, arg| {
                let arg = mark_value(arg, &markers);
                let result = runtime.apply_value(function.clone(), arg)?;
                let source_ret = source_ret.clone();
                let target_ret = target_ret.clone();
                let markers = markers.clone();
                runtime.continue_with(result, move |runtime, result| {
                    let result = mark_value(result, &markers);
                    runtime.adapt_value(result, &source_ret, &target_ret)
                })
            })
        })
    }

    fn emit_effect_request(&self, path: Vec<String>, payload: Value) -> RuntimeResult<'a> {
        let mut request = Request {
            path,
            guard_ids: Vec::new(),
            payload,
            resume: Rc::new(|_, value| value_result(value)),
        };
        self.mark_request_with_active_markers(&mut request);
        Ok(EvalResult::Request(request))
    }

    fn mark_request_with_active_markers(&self, request: &mut Request<'a>) {
        for marker in &self.active_markers {
            if marker.depth != 0 || request_matches_marker_path(request, marker) {
                continue;
            }
            if !request.guard_ids.contains(&marker.id) {
                request.guard_ids.push(marker.id);
            }
        }
    }

    fn mark_active_value(&mut self, value: Value) -> Value {
        // Handler marker propagation follows the innermost active handler. Carrying outer
        // markers into a nested handler would make the outer handler skip the same request.
        let Some(marker) = self.active_markers.last().cloned() else {
            return value;
        };
        let marker = ValueMarker {
            id: self.fresh_guard_id(),
            path: marker.path,
            depth: marker.depth,
            skip_own_path: marker.skip_own_path,
        };
        mark_value(value, std::slice::from_ref(&marker))
    }

    fn request_intersects_guard_stack(&self, request: &Request<'_>) -> bool {
        request
            .guard_ids
            .iter()
            .any(|guard_id| self.guard_ids.contains(guard_id))
    }

    fn instantiate_hygiene(&mut self, hygiene: &FunctionAdapterHygiene) -> Vec<ValueMarker> {
        hygiene
            .markers
            .iter()
            .map(|marker| ValueMarker {
                id: self.fresh_guard_id(),
                path: marker.path.clone(),
                depth: marker.depth,
                skip_own_path: true,
            })
            .collect()
    }

    fn fresh_guard_id(&mut self) -> GuardId {
        let id = GuardId(self.next_guard_id);
        self.next_guard_id += 1;
        id
    }

    fn with_marker_frame(
        &mut self,
        markers: Vec<ValueMarker>,
        run: impl FnOnce(&mut Runtime<'a>) -> RuntimeResult<'a> + 'a,
    ) -> RuntimeResult<'a> {
        if markers.is_empty() {
            return run(self);
        }

        let guard_len = self.guard_ids.len();
        let active_len = self.active_markers.len();
        self.push_marker_frame(&markers);
        let result = run(self);
        self.pop_marker_frame(guard_len, active_len);

        self.close_marker_frame_result(result?, markers)
    }

    fn push_marker_frame(&mut self, markers: &[ValueMarker]) {
        self.guard_ids
            .extend(markers.iter().map(|marker| marker.id));
        self.active_markers.extend(markers.iter().cloned());
    }

    fn pop_marker_frame(&mut self, guard_len: usize, active_len: usize) {
        self.guard_ids.truncate(guard_len);
        self.active_markers.truncate(active_len);
    }

    fn close_marker_frame_result(
        &mut self,
        result: EvalResult<'a>,
        markers: Vec<ValueMarker>,
    ) -> RuntimeResult<'a> {
        match result {
            EvalResult::Value(value) => value_result(mark_value(value, &markers)),
            EvalResult::Request(request) => {
                let resume = request.resume.clone();
                Ok(EvalResult::Request(Request {
                    path: request.path,
                    guard_ids: request.guard_ids,
                    payload: request.payload,
                    resume: Rc::new(move |runtime, value| {
                        let resume = resume.clone();
                        runtime.with_marker_frame(markers.clone(), move |runtime| {
                            resume(runtime, value)
                        })
                    }),
                }))
            }
        }
    }

    fn bind_pat(
        &mut self,
        pat: &Pat,
        value: &Value,
        env: &mut CapturedEnv,
    ) -> Result<bool, RuntimeError> {
        let (view, markers) = value_view(value);
        match pat {
            Pat::Wild => Ok(true),
            Pat::Lit(lit) => Ok(value_equivalent(value, &Value::from(lit))),
            Pat::Tuple(items) => {
                let Value::Tuple(values) = view else {
                    return Ok(false);
                };
                if items.len() != values.len() {
                    return Ok(false);
                }
                for (pat, value) in items.iter().zip(values) {
                    let value = mark_value(value.clone(), &markers);
                    if !self.bind_pat(pat, &value, env)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pat::List {
                prefix,
                spread,
                suffix,
            } => self.bind_list_pat(prefix, spread.as_deref(), suffix, view, &markers, env),
            Pat::Record { fields, spread } => {
                let Value::Record(record_fields) = view else {
                    return Ok(false);
                };
                let mut consumed = HashSet::new();
                for (name, pat) in fields {
                    let Some((index, field)) = record_field_with_index(record_fields, name) else {
                        return Ok(false);
                    };
                    consumed.insert(index);
                    let value = mark_value(field.value.clone(), &markers);
                    if !self.bind_pat(pat, &value, env)? {
                        return Ok(false);
                    }
                }
                if let Some(def) = record_spread_def(spread) {
                    let captured = record_fields
                        .iter()
                        .enumerate()
                        .filter(|(index, _)| !consumed.contains(index))
                        .map(|(_, field)| ValueField {
                            name: field.name.clone(),
                            value: mark_value(field.value.clone(), &markers),
                        })
                        .collect();
                    env.locals.insert(def, Value::Record(captured));
                }
                Ok(true)
            }
            Pat::PolyVariant(tag, payload_pats) => {
                let Value::PolyVariant {
                    tag: value_tag,
                    payloads,
                } = view
                else {
                    return Ok(false);
                };
                if tag != value_tag || payload_pats.len() != payloads.len() {
                    return Ok(false);
                }
                for (pat, value) in payload_pats.iter().zip(payloads) {
                    let value = mark_value(value.clone(), &markers);
                    if !self.bind_pat(pat, &value, env)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pat::Con(def, payload_pats) => {
                let Value::DataConstructor {
                    def: value_def,
                    payloads,
                } = view
                else {
                    return Ok(false);
                };
                if def != value_def || payload_pats.len() != payloads.len() {
                    return Ok(false);
                }
                for (pat, value) in payload_pats.iter().zip(payloads) {
                    let value = mark_value(value.clone(), &markers);
                    if !self.bind_pat(pat, &value, env)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pat::Ref(instance) => {
                let expected = self.eval_instance(*instance)?;
                Ok(value_equivalent(value, &expected))
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

    fn bind_list_pat(
        &mut self,
        prefix: &[Pat],
        spread: Option<&Pat>,
        suffix: &[Pat],
        value: &Value,
        markers: &[ValueMarker],
        env: &mut CapturedEnv,
    ) -> Result<bool, RuntimeError> {
        let Value::List(items) = value else {
            return Ok(false);
        };
        let min_len = prefix.len() + suffix.len();
        if items.len() < min_len || spread.is_none() && items.len() != min_len {
            return Ok(false);
        }

        for (index, pat) in prefix.iter().enumerate() {
            let Some(item) = items.index(index) else {
                return Ok(false);
            };
            let item = mark_value((*item).clone(), markers);
            if !self.bind_pat(pat, &item, env)? {
                return Ok(false);
            }
        }

        let suffix_start = items.len() - suffix.len();
        for (offset, pat) in suffix.iter().enumerate() {
            let Some(item) = items.index(suffix_start + offset) else {
                return Ok(false);
            };
            let item = mark_value((*item).clone(), markers);
            if !self.bind_pat(pat, &item, env)? {
                return Ok(false);
            }
        }

        if let Some(spread) = spread {
            let Some(slice) = items.index_range(prefix.len(), suffix_start) else {
                return Ok(false);
            };
            let slice = mark_value(Value::List(slice), markers);
            if !self.bind_pat(spread, &slice, env)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn adapt_value(&mut self, value: Value, source: &Type, target: &Type) -> RuntimeResult<'a> {
        if equivalent_runtime_types(source, target) || matches!(target, Type::Any) {
            return value_result(value);
        }
        if matches!(source, Type::Never) {
            return value_result(value);
        }
        match (source, target) {
            (
                Type::Thunk {
                    value: source_value,
                    ..
                },
                Type::Thunk {
                    value: target_value,
                    ..
                },
            ) => value_result(Value::Thunk(Thunk::Adapter {
                source: source_value.as_ref().clone(),
                target: target_value.as_ref().clone(),
                thunk: Box::new(value),
            })),
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
            Value::Marked { value, markers } => {
                self.with_marker_frame(markers, move |runtime| runtime.force_thunk(*value))
            }
            Value::Thunk(Thunk::Expr { body, mut env }) => self.eval_expr(&body, &mut env),
            Value::Thunk(Thunk::Value(value)) => value_result(*value),
            Value::Thunk(Thunk::Effect { path, payload }) => {
                self.emit_effect_request(path, *payload)
            }
            Value::Thunk(Thunk::Continuation { id, arg }) => {
                let resume = self
                    .continuations
                    .get(&id)
                    .cloned()
                    .ok_or(RuntimeError::MissingContinuation { id })?;
                let result = resume(self, *arg)?;
                self.continue_with(result, |runtime, value| runtime.force_value_if_thunk(value))
            }
            Value::Thunk(Thunk::Adapter {
                source,
                target,
                thunk,
            }) => {
                let value = self.force_thunk(*thunk)?;
                self.continue_with(value, move |runtime, value| {
                    runtime.adapt_value(value, &source, &target)
                })
            }
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
                    guard_ids: request.guard_ids,
                    payload: request.payload,
                    resume: Rc::new(move |runtime, value| {
                        let resumed = request_resume(runtime, value)?;
                        runtime.continue_with_rc(resumed, continuation.clone())
                    }),
                }))
            }
        }
    }

    fn force_value_if_thunk(&mut self, value: Value) -> RuntimeResult<'a> {
        if value_is_thunk_like(&value) {
            return self.force_thunk(value);
        }
        value_result(value)
    }

    fn store_continuation(&mut self, continuation: Continuation<'a>) -> ContinuationId {
        let id = ContinuationId(self.next_continuation_id);
        self.next_continuation_id += 1;
        self.continuations.insert(id, continuation);
        id
    }

    fn expect_record(&self, value: Value) -> Result<Vec<ValueField>, RuntimeError> {
        let (value, markers) = into_value_markers(value);
        match value {
            Value::Record(fields) => Ok(fields
                .into_iter()
                .map(|field| ValueField {
                    name: field.name,
                    value: mark_value(field.value, &markers),
                })
                .collect()),
            value => Err(RuntimeError::ExpectedRecord { value }),
        }
    }

    fn project_record_field(&self, value: Value, name: &str) -> Result<Value, RuntimeError> {
        let (value, markers) = into_value_markers(value);
        match value {
            Value::Record(fields) => fields
                .iter()
                .rev()
                .find(|field| field.name == name)
                .map(|field| mark_value(field.value.clone(), &markers))
                .ok_or_else(|| RuntimeError::MissingRecordField {
                    name: name.to_string(),
                }),
            Value::DataConstructor { payloads, .. } if payloads.len() == 1 => {
                self.project_record_field(mark_value(payloads[0].clone(), &markers), name)
            }
            value => Err(RuntimeError::ExpectedRecord { value }),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GuardId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ValueMarker {
    pub id: GuardId,
    pub path: Vec<String>,
    pub depth: u32,
    pub skip_own_path: bool,
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
    List(ListTree<Rc<Value>>),
    Record(Vec<ValueField>),
    PolyVariant {
        tag: String,
        payloads: Vec<Value>,
    },
    DataConstructor {
        def: DefId,
        payloads: Vec<Value>,
    },
    ConstructorFunction(ConstructorFunction),
    PrimitiveOp(PrimitiveValue),
    Closure(Closure),
    Thunk(Thunk),
    FunctionAdapter(FunctionAdapter),
    EffectOp {
        path: Vec<String>,
    },
    Continuation(ContinuationId),
    Marked {
        value: Box<Value>,
        markers: Vec<ValueMarker>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConstructorFunction {
    pub def: DefId,
    pub arity: usize,
    pub args: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct PrimitiveValue {
    pub op: PrimitiveOp,
    pub context: PrimitiveContext,
    pub args: Vec<Value>,
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
    Expr {
        body: Expr,
        env: CapturedEnv,
    },
    Effect {
        path: Vec<String>,
        payload: Box<Value>,
    },
    Continuation {
        id: ContinuationId,
        arg: Box<Value>,
    },
    Value(Box<Value>),
    Adapter {
        source: Type,
        target: Type,
        thunk: Box<Value>,
    },
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
    ExpectedInt {
        value: Value,
    },
    ExpectedFloat {
        value: Value,
    },
    ExpectedBool {
        value: Value,
    },
    ExpectedRecord {
        value: Value,
    },
    ExpectedList {
        value: Value,
    },
    MissingPrimitiveContext {
        op: PrimitiveOp,
    },
    UnsupportedPrimitive {
        op: PrimitiveOp,
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
            Self::ExpectedInt { value } => write!(f, "expected int, got {value:?}"),
            Self::ExpectedFloat { value } => write!(f, "expected float, got {value:?}"),
            Self::ExpectedBool { value } => write!(f, "expected bool, got {value:?}"),
            Self::ExpectedRecord { value } => write!(f, "expected record, got {value:?}"),
            Self::ExpectedList { value } => write!(f, "expected list, got {value:?}"),
            Self::MissingPrimitiveContext { op } => {
                write!(f, "missing runtime context for primitive {op:?}")
            }
            Self::UnsupportedPrimitive { op } => write!(f, "unsupported primitive {op:?}"),
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

fn markers_for_function_call(markers: Vec<ValueMarker>) -> Vec<ValueMarker> {
    markers
        .into_iter()
        .map(|marker| ValueMarker {
            depth: marker.depth.saturating_sub(1),
            ..marker
        })
        .collect()
}

fn mark_value(value: Value, markers: &[ValueMarker]) -> Value {
    if markers.is_empty() {
        return value;
    }

    let (value, mut value_markers) = into_value_markers(value);
    extend_marker_list(&mut value_markers, markers);
    if value_markers.is_empty() || is_scalar_value(&value) {
        return value;
    }
    Value::Marked {
        value: Box::new(value),
        markers: value_markers,
    }
}

fn value_view(value: &Value) -> (&Value, Vec<ValueMarker>) {
    let mut value = value;
    let mut markers = Vec::new();
    while let Value::Marked {
        value: inner,
        markers: value_markers,
    } = value
    {
        extend_marker_list(&mut markers, value_markers);
        value = inner;
    }
    (value, markers)
}

fn value_is_thunk_like(value: &Value) -> bool {
    match value {
        Value::Thunk(_) => true,
        Value::Marked { value, .. } => value_is_thunk_like(value),
        _ => false,
    }
}

fn request_matches_marker_path(request: &Request<'_>, marker: &ValueMarker) -> bool {
    marker.skip_own_path && path_has_prefix(&request.path, &marker.path)
}

fn path_has_prefix(path: &[String], prefix: &[String]) -> bool {
    prefix.len() <= path.len()
        && path
            .iter()
            .zip(prefix)
            .all(|(segment, prefix)| segment == prefix)
}

fn into_value_markers(value: Value) -> (Value, Vec<ValueMarker>) {
    let mut value = value;
    let mut markers = Vec::new();
    while let Value::Marked {
        value: inner,
        markers: value_markers,
    } = value
    {
        extend_marker_list(&mut markers, &value_markers);
        value = *inner;
    }
    (value, markers)
}

fn extend_marker_list(markers: &mut Vec<ValueMarker>, new_markers: &[ValueMarker]) {
    for marker in new_markers {
        if !markers.iter().any(|existing| existing == marker) {
            markers.push(marker.clone());
        }
    }
}

fn is_scalar_value(value: &Value) -> bool {
    matches!(
        value,
        Value::Int(_)
            | Value::BigInt(_)
            | Value::Float(_)
            | Value::Str(_)
            | Value::Bool(_)
            | Value::Unit
    )
}

fn value_equivalent(left: &Value, right: &Value) -> bool {
    let (left, _) = value_view(left);
    let (right, _) = value_view(right);
    left == right
}

fn constructor_value(def: DefId, arity: usize, args: Vec<Value>) -> Value {
    if args.len() >= arity {
        return Value::DataConstructor {
            def,
            payloads: args,
        };
    }
    Value::ConstructorFunction(ConstructorFunction { def, arity, args })
}

fn apply_constructor(mut constructor: ConstructorFunction, arg: Value) -> Value {
    constructor.args.push(arg);
    constructor_value(constructor.def, constructor.arity, constructor.args)
}

fn apply_primitive(
    op: PrimitiveOp,
    context: &PrimitiveContext,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    match op {
        PrimitiveOp::YadaYada => Err(RuntimeError::UnsupportedPrimitive { op }),
        PrimitiveOp::BoolNot => Ok(Value::Bool(!expect_bool(&args[0])?)),
        PrimitiveOp::BoolEq => Ok(Value::Bool(
            expect_bool(&args[0])? == expect_bool(&args[1])?,
        )),
        PrimitiveOp::IntAdd => Ok(Value::Int(expect_int(&args[0])? + expect_int(&args[1])?)),
        PrimitiveOp::IntSub => Ok(Value::Int(expect_int(&args[0])? - expect_int(&args[1])?)),
        PrimitiveOp::IntMul => Ok(Value::Int(expect_int(&args[0])? * expect_int(&args[1])?)),
        PrimitiveOp::IntDiv => Ok(Value::Int(expect_int(&args[0])? / expect_int(&args[1])?)),
        PrimitiveOp::IntMod => Ok(Value::Int(expect_int(&args[0])? % expect_int(&args[1])?)),
        PrimitiveOp::IntEq => Ok(Value::Bool(expect_int(&args[0])? == expect_int(&args[1])?)),
        PrimitiveOp::IntLt => Ok(Value::Bool(expect_int(&args[0])? < expect_int(&args[1])?)),
        PrimitiveOp::IntLe => Ok(Value::Bool(expect_int(&args[0])? <= expect_int(&args[1])?)),
        PrimitiveOp::IntGt => Ok(Value::Bool(expect_int(&args[0])? > expect_int(&args[1])?)),
        PrimitiveOp::IntGe => Ok(Value::Bool(expect_int(&args[0])? >= expect_int(&args[1])?)),
        PrimitiveOp::FloatAdd => Ok(Value::Float(
            expect_float(&args[0])? + expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatSub => Ok(Value::Float(
            expect_float(&args[0])? - expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatMul => Ok(Value::Float(
            expect_float(&args[0])? * expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatDiv => Ok(Value::Float(
            expect_float(&args[0])? / expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatEq => Ok(Value::Bool(
            expect_float(&args[0])? == expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatLt => Ok(Value::Bool(
            expect_float(&args[0])? < expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatLe => Ok(Value::Bool(
            expect_float(&args[0])? <= expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatGt => Ok(Value::Bool(
            expect_float(&args[0])? > expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatGe => Ok(Value::Bool(
            expect_float(&args[0])? >= expect_float(&args[1])?,
        )),
        PrimitiveOp::StringEq => Ok(Value::Bool(expect_str(&args[0])? == expect_str(&args[1])?)),
        PrimitiveOp::StringConcat => Ok(Value::Str(format!(
            "{}{}",
            expect_str(&args[0])?,
            expect_str(&args[1])?
        ))),
        PrimitiveOp::StringLen => Ok(Value::Int(expect_str(&args[0])?.chars().count() as i64)),
        PrimitiveOp::StringIndex => {
            let text = expect_str(&args[0])?;
            let index =
                usize::try_from(expect_int(&args[1])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[1].clone(),
                })?;
            text.chars()
                .nth(index)
                .map(|ch| Value::Str(ch.to_string()))
                .ok_or_else(|| RuntimeError::UnsupportedPrimitive { op })
        }
        PrimitiveOp::StringIndexRangeRaw => {
            let text = expect_str(&args[0])?;
            let start =
                usize::try_from(expect_int(&args[1])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[1].clone(),
                })?;
            let end =
                usize::try_from(expect_int(&args[2])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[2].clone(),
                })?;
            Ok(Value::Str(
                text.chars().skip(start).take(end - start).collect(),
            ))
        }
        PrimitiveOp::StringSpliceRaw => {
            let text = expect_str(&args[0])?;
            let start =
                usize::try_from(expect_int(&args[1])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[1].clone(),
                })?;
            let end =
                usize::try_from(expect_int(&args[2])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[2].clone(),
                })?;
            let insert = expect_str(&args[3])?;
            let prefix = text.chars().take(start).collect::<String>();
            let suffix = text.chars().skip(end).collect::<String>();
            Ok(Value::Str(format!("{prefix}{insert}{suffix}")))
        }
        PrimitiveOp::IntToString => Ok(Value::Str(expect_int(&args[0])?.to_string())),
        PrimitiveOp::IntToHex => Ok(Value::Str(format!("{:x}", expect_int(&args[0])?))),
        PrimitiveOp::IntToUpperHex => Ok(Value::Str(format!("{:X}", expect_int(&args[0])?))),
        PrimitiveOp::FloatToString => Ok(Value::Str(format_float(expect_float(&args[0])?))),
        PrimitiveOp::BoolToString => Ok(Value::Str(expect_bool(&args[0])?.to_string())),
        PrimitiveOp::ListEmpty => Ok(Value::List(ListTree::empty())),
        PrimitiveOp::ListSingleton => {
            Ok(Value::List(ListTree::singleton(Rc::new(args[0].clone()))))
        }
        PrimitiveOp::ListLen => Ok(Value::Int(expect_list(&args[0])?.len() as i64)),
        PrimitiveOp::ListMerge => Ok(Value::List(ListTree::concat(
            expect_list(&args[0])?.clone(),
            expect_list(&args[1])?.clone(),
        ))),
        PrimitiveOp::ListIndex => {
            let index =
                usize::try_from(expect_int(&args[1])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[1].clone(),
                })?;
            expect_list(&args[0])?
                .index(index)
                .map(|value| (*value).clone())
                .ok_or_else(|| RuntimeError::ExpectedList {
                    value: args[0].clone(),
                })
        }
        PrimitiveOp::ListIndexRangeRaw => {
            let start =
                usize::try_from(expect_int(&args[1])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[1].clone(),
                })?;
            let end =
                usize::try_from(expect_int(&args[2])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[2].clone(),
                })?;
            expect_list(&args[0])?
                .index_range(start, end)
                .map(Value::List)
                .ok_or_else(|| RuntimeError::ExpectedList {
                    value: args[0].clone(),
                })
        }
        PrimitiveOp::ListSpliceRaw => {
            let start =
                usize::try_from(expect_int(&args[1])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[1].clone(),
                })?;
            let end =
                usize::try_from(expect_int(&args[2])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[2].clone(),
                })?;
            let insert = expect_list(&args[3])?;
            expect_list(&args[0])?
                .splice(start, end, insert.clone())
                .map(Value::List)
                .ok_or_else(|| RuntimeError::ExpectedList {
                    value: args[0].clone(),
                })
        }
        PrimitiveOp::ListViewRaw => apply_list_view_raw(context, &args[0]),
        PrimitiveOp::CharEq => Ok(Value::Bool(expect_str(&args[0])? == expect_str(&args[1])?)),
        PrimitiveOp::CharToString => Ok(Value::Str(expect_str(&args[0])?.to_string())),
        PrimitiveOp::CharIsWhitespace => Ok(Value::Bool(expect_str(&args[0])?.trim().is_empty())),
        PrimitiveOp::CharIsPunctuation => Ok(Value::Bool(
            expect_str(&args[0])?
                .chars()
                .all(|ch| ch.is_ascii_punctuation()),
        )),
        PrimitiveOp::CharIsWord => Ok(Value::Bool(
            expect_str(&args[0])?
                .chars()
                .all(|ch| ch == '_' || ch.is_alphanumeric()),
        )),
        PrimitiveOp::ListIndexRange
        | PrimitiveOp::ListSplice
        | PrimitiveOp::StringIndexRange
        | PrimitiveOp::StringSplice
        | PrimitiveOp::StringLineCount
        | PrimitiveOp::StringLineRange
        | PrimitiveOp::StringToBytes
        | PrimitiveOp::BytesLen
        | PrimitiveOp::BytesEq
        | PrimitiveOp::BytesConcat
        | PrimitiveOp::BytesIndex
        | PrimitiveOp::BytesIndexRange
        | PrimitiveOp::BytesToUtf8Raw
        | PrimitiveOp::BytesToPath
        | PrimitiveOp::PathToBytes => Err(RuntimeError::UnsupportedPrimitive { op }),
    }
}

fn apply_list_view_raw(context: &PrimitiveContext, value: &Value) -> Result<Value, RuntimeError> {
    let constructors = context
        .list_view
        .ok_or(RuntimeError::MissingPrimitiveContext {
            op: PrimitiveOp::ListViewRaw,
        })?;
    match expect_list(value)?.view() {
        ListView::Empty => Ok(Value::DataConstructor {
            def: constructors.empty,
            payloads: Vec::new(),
        }),
        ListView::Leaf(value) => Ok(Value::DataConstructor {
            def: constructors.leaf,
            payloads: vec![(*value).clone()],
        }),
        ListView::Node { left, right, .. } => Ok(Value::DataConstructor {
            def: constructors.node,
            payloads: vec![Value::List(left), Value::List(right)],
        }),
    }
}

fn expect_int(value: &Value) -> Result<i64, RuntimeError> {
    let (value, _) = value_view(value);
    match value {
        Value::Int(value) => Ok(*value),
        Value::BigInt(value) => value
            .to_string()
            .parse()
            .map_err(|_| RuntimeError::ExpectedInt {
                value: Value::BigInt(value.clone()),
            }),
        value => Err(RuntimeError::ExpectedInt {
            value: value.clone(),
        }),
    }
}

fn expect_float(value: &Value) -> Result<f64, RuntimeError> {
    let (value, _) = value_view(value);
    match value {
        Value::Float(value) => Ok(*value),
        Value::Int(value) => Ok(*value as f64),
        value => Err(RuntimeError::ExpectedFloat {
            value: value.clone(),
        }),
    }
}

fn expect_bool(value: &Value) -> Result<bool, RuntimeError> {
    let (value, _) = value_view(value);
    match value {
        Value::Bool(value) => Ok(*value),
        value => Err(RuntimeError::ExpectedBool {
            value: value.clone(),
        }),
    }
}

fn expect_str(value: &Value) -> Result<&str, RuntimeError> {
    let (value, _) = value_view(value);
    match value {
        Value::Str(value) => Ok(value),
        value => Err(RuntimeError::UnsupportedBoundary {
            feature: format!("expected str, got {value:?}"),
        }),
    }
}

fn expect_list(value: &Value) -> Result<&ListTree<Rc<Value>>, RuntimeError> {
    let (value, _) = value_view(value);
    match value {
        Value::List(value) => Ok(value),
        value => Err(RuntimeError::ExpectedList {
            value: value.clone(),
        }),
    }
}

fn format_float(value: f64) -> String {
    let text = value.to_string();
    if text.contains('.') || text.contains('e') || text.contains('E') {
        text
    } else {
        format!("{text}.0")
    }
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
        Block, CatchArm, Expr, ExprKind, FunctionAdapterHygiene, GuardMarker, Instance, InstanceId,
        InstanceSource, Lit, Pat, Program, Root, SelectResolution, Signature, Stmt, Type, Vis,
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
    fn force_thunk_reaches_nested_computation_when_target_value_is_plain() {
        let inner = make_thunk_expr(
            Type::pure_effect(),
            unit_type(),
            Expr::new(ExprKind::Lit(Lit::Unit)),
        );
        let outer_value = thunk_type(Type::pure_effect(), unit_type());
        let outer = make_thunk_expr(Type::pure_effect(), outer_value, inner);

        let program = Program {
            roots: vec![Root::Expr(force_thunk_expr(
                outer,
                Type::pure_effect(),
                unit_type(),
            ))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Unit]));
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
                    body: continuation_call(continuation, ExprKind::Lit(Lit::Int(7))),
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
                    body: continuation_call(skip_continuation, ExprKind::Lit(Lit::Unit)),
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
                    body: continuation_call(continuation, ExprKind::Lit(Lit::Int(2))),
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
                    body: continuation_call(continuation, ExprKind::Lit(Lit::Int(2))),
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
                    body: continuation_call(continuation, ExprKind::Lit(Lit::Int(4))),
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
                    body: continuation_call(continuation, ExprKind::Lit(Lit::Bool(true))),
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
                    body: continuation_call(guard_continuation, ExprKind::Lit(Lit::Bool(true))),
                }],
            }))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(1)]));
    }

    #[test]
    fn hygiene_blocks_inner_handler_for_foreign_thunk_argument() {
        let thunk_arg = mono::DefId(10);
        let outer_payload = mono::DefId(11);
        let blocked = path(&["blocked", "fire"]);
        let allowed = path(&["allowed", "run"]);
        let thunk_effect = effect_row(&["blocked", "fire"]);
        let thunk_arg_type = thunk_type(thunk_effect.clone(), int_type());
        let source = pure_function_type(thunk_arg_type.clone(), int_type());
        let target = pure_function_type(thunk_arg_type.clone(), int_type());
        let function = Expr::new(ExprKind::Lambda(
            Pat::Var(thunk_arg),
            Box::new(Expr::new(ExprKind::Catch {
                body: Box::new(force_thunk_expr(
                    Expr::new(ExprKind::Local(thunk_arg)),
                    thunk_effect.clone(),
                    int_type(),
                )),
                arms: vec![CatchArm {
                    operation_path: Some(blocked.clone()),
                    pat: Pat::Wild,
                    continuation: Some(Pat::Wild),
                    guard: None,
                    body: Expr::new(ExprKind::Lit(Lit::Int(99))),
                }],
            })),
        ));
        let adapter = function_adapter(function, source, target, allowed, 0);
        let arg = make_thunk_expr(
            thunk_effect,
            int_type(),
            effect_call(blocked.clone(), ExprKind::Lit(Lit::Int(7))),
        );
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
                body: Box::new(Expr::new(ExprKind::Apply(Box::new(adapter), Box::new(arg)))),
                arms: vec![CatchArm {
                    operation_path: Some(blocked),
                    pat: Pat::Var(outer_payload),
                    continuation: Some(Pat::Wild),
                    guard: None,
                    body: Expr::new(ExprKind::Local(outer_payload)),
                }],
            }))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(7)]));
    }

    #[test]
    fn hygiene_keeps_allowed_path_readable_inside_marker_frame() {
        let thunk_arg = mono::DefId(20);
        let allowed = path(&["allowed", "run"]);
        let thunk_effect = effect_row(&["allowed", "run"]);
        let thunk_arg_type = thunk_type(thunk_effect.clone(), int_type());
        let source = pure_function_type(thunk_arg_type.clone(), int_type());
        let target = pure_function_type(thunk_arg_type.clone(), int_type());
        let function = Expr::new(ExprKind::Lambda(
            Pat::Var(thunk_arg),
            Box::new(Expr::new(ExprKind::Catch {
                body: Box::new(force_thunk_expr(
                    Expr::new(ExprKind::Local(thunk_arg)),
                    thunk_effect.clone(),
                    int_type(),
                )),
                arms: vec![CatchArm {
                    operation_path: Some(allowed.clone()),
                    pat: Pat::Wild,
                    continuation: Some(Pat::Wild),
                    guard: None,
                    body: Expr::new(ExprKind::Lit(Lit::Int(99))),
                }],
            })),
        ));
        let adapter = function_adapter(function, source, target, allowed.clone(), 0);
        let arg = make_thunk_expr(
            thunk_effect,
            int_type(),
            effect_call(allowed, ExprKind::Lit(Lit::Int(7))),
        );
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Apply(
                Box::new(adapter),
                Box::new(arg),
            )))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(99)]));
    }

    #[test]
    fn hygiene_depth_one_blocks_inner_handler_when_marked_function_runs() {
        let callback = mono::DefId(30);
        let outer_payload = mono::DefId(31);
        let blocked = path(&["blocked", "fire"]);
        let allowed = path(&["allowed", "run"]);
        let callback_type = pure_function_type(unit_type(), int_type());
        let source = pure_function_type(callback_type.clone(), int_type());
        let target = pure_function_type(callback_type.clone(), int_type());
        let function = Expr::new(ExprKind::Lambda(
            Pat::Var(callback),
            Box::new(Expr::new(ExprKind::Catch {
                body: Box::new(Expr::new(ExprKind::Apply(
                    Box::new(Expr::new(ExprKind::Local(callback))),
                    Box::new(Expr::new(ExprKind::Lit(Lit::Unit))),
                ))),
                arms: vec![CatchArm {
                    operation_path: Some(blocked.clone()),
                    pat: Pat::Wild,
                    continuation: Some(Pat::Wild),
                    guard: None,
                    body: Expr::new(ExprKind::Lit(Lit::Int(99))),
                }],
            })),
        ));
        let callback_arg = Expr::new(ExprKind::Lambda(
            Pat::Wild,
            Box::new(effect_call(blocked.clone(), ExprKind::Lit(Lit::Int(7)))),
        ));
        let adapter = function_adapter(function, source, target, allowed, 1);
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
                body: Box::new(Expr::new(ExprKind::Apply(
                    Box::new(adapter),
                    Box::new(callback_arg),
                ))),
                arms: vec![CatchArm {
                    operation_path: Some(blocked),
                    pat: Pat::Var(outer_payload),
                    continuation: Some(Pat::Wild),
                    guard: None,
                    body: Expr::new(ExprKind::Local(outer_payload)),
                }],
            }))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(7)]));
    }

    #[test]
    fn hygiene_marker_propagates_through_record_projection_to_returned_thunk() {
        let outer_payload = mono::DefId(41);
        let blocked = path(&["blocked", "fire"]);
        let allowed = path(&["allowed", "run"]);
        let thunk_effect = effect_row(&["blocked", "fire"]);
        let thunk_value = int_type();
        let thunk = thunk_type(thunk_effect.clone(), thunk_value.clone());
        let record = Type::Record(vec![mono::TypeField {
            name: "run".to_string(),
            value: thunk.clone(),
            optional: false,
        }]);
        let source = pure_function_type(unit_type(), record.clone());
        let target = pure_function_type(unit_type(), record);
        let function = Expr::new(ExprKind::Lambda(
            Pat::Wild,
            Box::new(Expr::new(ExprKind::Record {
                fields: vec![mono::RecordField {
                    name: "run".to_string(),
                    value: make_thunk_expr(
                        thunk_effect.clone(),
                        thunk_value.clone(),
                        Expr::new(ExprKind::Catch {
                            body: Box::new(effect_call(
                                blocked.clone(),
                                ExprKind::Lit(Lit::Int(7)),
                            )),
                            arms: vec![CatchArm {
                                operation_path: Some(blocked.clone()),
                                pat: Pat::Wild,
                                continuation: Some(Pat::Wild),
                                guard: None,
                                body: Expr::new(ExprKind::Lit(Lit::Int(99))),
                            }],
                        }),
                    ),
                }],
                spread: mono::RecordSpread::None,
            })),
        ));
        let adapter = function_adapter(function, source, target, allowed, 0);
        let selected = Expr::new(ExprKind::Select {
            base: Box::new(Expr::new(ExprKind::Apply(
                Box::new(adapter),
                Box::new(Expr::new(ExprKind::Lit(Lit::Unit))),
            ))),
            name: "run".to_string(),
            resolution: Some(SelectResolution::RecordField),
        });
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
                body: Box::new(force_thunk_expr(selected, thunk_effect, thunk_value)),
                arms: vec![CatchArm {
                    operation_path: Some(blocked),
                    pat: Pat::Var(outer_payload),
                    continuation: Some(Pat::Wild),
                    guard: None,
                    body: Expr::new(ExprKind::Local(outer_payload)),
                }],
            }))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(7)]));
    }

    #[test]
    fn hygiene_marker_frame_is_restored_when_outer_handler_resumes() {
        let resume_continuation = mono::DefId(50);
        let second_payload = mono::DefId(51);
        let first = path(&["blocked", "first"]);
        let second = path(&["blocked", "second"]);
        let allowed = path(&["allowed", "run"]);
        let source = pure_function_type(unit_type(), int_type());
        let target = pure_function_type(unit_type(), int_type());
        let function = Expr::new(ExprKind::Lambda(
            Pat::Wild,
            Box::new(Expr::new(ExprKind::Block(Block {
                stmts: vec![Stmt::Expr(effect_call(
                    first.clone(),
                    ExprKind::Lit(Lit::Unit),
                ))],
                tail: Some(Box::new(Expr::new(ExprKind::Catch {
                    body: Box::new(effect_call(second.clone(), ExprKind::Lit(Lit::Int(2)))),
                    arms: vec![CatchArm {
                        operation_path: Some(second.clone()),
                        pat: Pat::Wild,
                        continuation: Some(Pat::Wild),
                        guard: None,
                        body: Expr::new(ExprKind::Lit(Lit::Int(99))),
                    }],
                }))),
            }))),
        ));
        let adapter = function_adapter(function, source, target, allowed, 0);
        let program = Program {
            roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
                body: Box::new(Expr::new(ExprKind::Catch {
                    body: Box::new(Expr::new(ExprKind::Apply(
                        Box::new(adapter),
                        Box::new(Expr::new(ExprKind::Lit(Lit::Unit))),
                    ))),
                    arms: vec![CatchArm {
                        operation_path: Some(first),
                        pat: Pat::Wild,
                        continuation: Some(Pat::Var(resume_continuation)),
                        guard: None,
                        body: continuation_call(resume_continuation, ExprKind::Lit(Lit::Unit)),
                    }],
                })),
                arms: vec![CatchArm {
                    operation_path: Some(second),
                    pat: Pat::Var(second_payload),
                    continuation: Some(Pat::Wild),
                    guard: None,
                    body: Expr::new(ExprKind::Local(second_payload)),
                }],
            }))],
            instances: Vec::new(),
        };

        assert_eq!(run_program(&program), Ok(vec![Value::Int(2)]));
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

    fn unit_type() -> Type {
        Type::unit()
    }

    fn effect_row(parts: &[&str]) -> Type {
        Type::EffectRow(vec![effect_type(parts)])
    }

    fn effect_type(parts: &[&str]) -> Type {
        Type::Con {
            path: path(parts),
            args: Vec::new(),
        }
    }

    fn thunk_type(effect: Type, value: Type) -> Type {
        Type::Thunk {
            effect: Box::new(effect),
            value: Box::new(value),
        }
    }

    fn pure_function_type(arg: Type, ret: Type) -> Type {
        Type::Fun {
            arg: Box::new(arg),
            arg_effect: Box::new(Type::pure_effect()),
            ret_effect: Box::new(Type::pure_effect()),
            ret: Box::new(ret),
        }
    }

    fn function_adapter(
        function: Expr,
        source: Type,
        target: Type,
        path: Vec<String>,
        depth: u32,
    ) -> Expr {
        Expr::new(ExprKind::FunctionAdapter {
            source,
            target,
            function: Box::new(function),
            hygiene: FunctionAdapterHygiene {
                markers: vec![GuardMarker { path, depth }],
            },
        })
    }

    fn make_thunk_expr(effect: Type, value: Type, body: Expr) -> Expr {
        Expr::new(ExprKind::MakeThunk {
            source: mono::ComputationType {
                effect: effect.clone(),
                value: value.clone(),
            },
            target: mono::EffectiveThunkType { effect, value },
            body: Box::new(body),
        })
    }

    fn force_thunk_expr(thunk: Expr, effect: Type, value: Type) -> Expr {
        Expr::new(ExprKind::ForceThunk {
            source: mono::EffectiveThunkType {
                effect: effect.clone(),
                value: value.clone(),
            },
            target: mono::ComputationType { effect, value },
            thunk: Box::new(thunk),
        })
    }

    fn path(parts: &[&str]) -> Vec<String> {
        parts.iter().map(|part| part.to_string()).collect()
    }

    fn effect_call(path: Vec<String>, payload: ExprKind) -> Expr {
        let effect = Type::EffectRow(vec![Type::Con {
            path: path.clone(),
            args: Vec::new(),
        }]);
        force_thunk_expr(
            Expr::new(ExprKind::Apply(
                Box::new(Expr::new(ExprKind::EffectOp { path })),
                Box::new(Expr::new(payload)),
            )),
            effect,
            Type::Any,
        )
    }

    fn continuation_call(continuation: mono::DefId, arg: ExprKind) -> Expr {
        force_thunk_expr(
            Expr::new(ExprKind::Apply(
                Box::new(Expr::new(ExprKind::Local(continuation))),
                Box::new(Expr::new(arg)),
            )),
            Type::Any,
            Type::Any,
        )
    }
}
