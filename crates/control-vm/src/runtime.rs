//! Runtime for the lowered control IR.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use mono::{FunctionAdapterHygiene, Lit, Type};
use num_bigint::BigInt;

use crate::boundary::{equivalent_runtime_types, function_parts, thunk_value_type};
use crate::ir::{
    Block, CaseArm, CatchArm, DefId, Expr, ExprId, InstanceId, Pat, Program, RecordField,
    RecordSpread, Root, SelectResolution, Stmt,
};
use crate::lower::{LowerError, lower};
use crate::validate::{ValidateError, validate};

pub fn run_mono_program(program: &mono::Program) -> Result<Vec<Value>, RunError> {
    let program = lower(program).map_err(RunError::Lower)?;
    run_program(&program)
}

pub fn run_program(program: &Program) -> Result<Vec<Value>, RunError> {
    validate(program).map_err(RunError::Validate)?;
    Runtime::new(program).run().map_err(RunError::Runtime)
}

#[derive(Debug, Clone, PartialEq)]
pub enum RunError {
    Lower(LowerError),
    Validate(ValidateError),
    Runtime(RuntimeError),
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lower(error) => write!(f, "{error}"),
            Self::Validate(error) => write!(f, "{error}"),
            Self::Runtime(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for RunError {}

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
    PolyVariant {
        tag: String,
        payloads: Vec<Value>,
    },
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
    pub body: ExprId,
    env: CapturedEnv,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Thunk {
    Expr {
        body: ExprId,
        env: CapturedEnv,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GuardId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ValueMarker {
    pub id: GuardId,
    pub path: Vec<String>,
    pub depth: u32,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct CapturedEnv {
    locals: HashMap<DefId, Value>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ContinuationId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub enum RuntimeError {
    MissingExpr {
        expr: ExprId,
    },
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
            Self::MissingExpr { expr } => write!(f, "missing control expression e{}", expr.0),
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

struct Runtime<'a> {
    program: &'a Program,
    instances: HashMap<InstanceId, Value>,
    evaluating_instances: HashSet<InstanceId>,
    continuations: HashMap<ContinuationId, Continuation<'a>>,
    next_continuation_id: u32,
    guard_ids: Vec<GuardId>,
    active_markers: Vec<ValueMarker>,
    next_guard_id: u32,
}

impl<'a> Runtime<'a> {
    fn new(program: &'a Program) -> Self {
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

    fn run(&mut self) -> Result<Vec<Value>, RuntimeError> {
        let mut results = Vec::with_capacity(self.program.roots.len());
        let mut env = CapturedEnv::default();
        for root in &self.program.roots {
            let result = match root {
                Root::Instance(instance) => EvalResult::Value(self.eval_instance(*instance)?),
                Root::Expr(expr) => self.eval_expr(*expr, &mut env)?,
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
        let control_instance = self
            .program
            .instances
            .get(instance.0 as usize)
            .ok_or(RuntimeError::MissingInstance { instance })?;
        if control_instance.id != instance {
            self.evaluating_instances.remove(&instance);
            return Err(RuntimeError::MismatchedInstanceSlot {
                requested: instance,
                actual: control_instance.id,
            });
        }

        let mut env = CapturedEnv::default();
        let value = self.eval_expr(control_instance.entry, &mut env);
        self.evaluating_instances.remove(&instance);
        let value = expect_eval_value(value?)?;
        self.instances.insert(instance, value.clone());
        Ok(value)
    }

    fn eval_expr(&mut self, expr: ExprId, env: &mut CapturedEnv) -> RuntimeResult<'a> {
        let expr = self
            .program
            .exprs
            .get(expr.0 as usize)
            .cloned()
            .ok_or(RuntimeError::MissingExpr { expr })?;
        match expr {
            Expr::Lit(lit) => value_result(Value::from(&lit)),
            Expr::PrimitiveOp(name) => Err(RuntimeError::UnsupportedExpr {
                feature: format!("primitive op {name}"),
            }),
            Expr::EffectOp { path } => value_result(Value::EffectOp { path }),
            Expr::Local(def) => value_result(
                self.mark_active_value(
                    env.locals
                        .get(&def)
                        .cloned()
                        .ok_or(RuntimeError::UnboundLocal { def })?,
                ),
            ),
            Expr::InstanceRef(instance) => value_result(self.eval_instance(instance)?),
            Expr::Coerce {
                source,
                target,
                expr,
            } => {
                let result = self.eval_expr(expr, env)?;
                self.continue_with(result, move |runtime, value| {
                    runtime.adapt_value(value, &source, &target)
                })
            }
            Expr::MakeThunk { body, .. } => value_result(Value::Thunk(Thunk::Expr {
                body,
                env: env.clone(),
            })),
            Expr::ForceThunk { thunk, .. } => {
                let result = self.eval_expr(thunk, env)?;
                self.continue_with(result, |runtime, thunk| runtime.force_thunk(thunk))
            }
            Expr::FunctionAdapter {
                source,
                target,
                function,
                hygiene,
            } => {
                let function = self.eval_expr(function, env)?;
                self.continue_with(function, move |_, function| {
                    value_result(Value::FunctionAdapter(FunctionAdapter {
                        source: source.clone(),
                        target: target.clone(),
                        function: Box::new(function),
                        hygiene: hygiene.clone(),
                    }))
                })
            }
            Expr::MarkerFrame { path, body } => {
                let mut frame_env = env.clone();
                let marker = ValueMarker {
                    id: self.fresh_guard_id(),
                    path,
                    depth: 1,
                };
                self.with_marker_frame(vec![marker], move |runtime| {
                    runtime.eval_expr(body, &mut frame_env)
                })
            }
            Expr::Apply { callee, arg } => {
                let env_for_arg = env.clone();
                let callee = self.eval_expr(callee, env)?;
                self.continue_with(callee, move |runtime, callee| {
                    let mut env = env_for_arg.clone();
                    let arg_result = runtime.eval_expr(arg, &mut env)?;
                    runtime.continue_with(arg_result, move |runtime, arg| {
                        runtime.apply_value(callee.clone(), arg)
                    })
                })
            }
            Expr::RefSet { .. } => Err(RuntimeError::UnsupportedExpr {
                feature: "ref set".to_string(),
            }),
            Expr::Lambda { param, body } => value_result(Value::Closure(Closure {
                param,
                body,
                env: env.clone(),
            })),
            Expr::Tuple(items) => self.eval_tuple(items, env.clone()),
            Expr::Record { fields, spread } => self.eval_record(fields, spread, env.clone()),
            Expr::PolyVariant { tag, payloads } => {
                self.eval_poly_variant(tag, payloads, env.clone())
            }
            Expr::Select {
                base,
                name,
                resolution,
            } => self.eval_select(base, name, resolution, env),
            Expr::Case { scrutinee, arms } => {
                let scrutinee = self.eval_expr(scrutinee, env)?;
                let env = env.clone();
                self.continue_with(scrutinee, move |runtime, scrutinee| {
                    runtime.eval_case(scrutinee, arms.clone(), env.clone())
                })
            }
            Expr::Catch { body, arms } => self.eval_catch(body, arms, env),
            Expr::Block(block) => self.eval_block(block, env),
        }
    }

    fn eval_record(
        &mut self,
        fields: Vec<RecordField>,
        spread: RecordSpread<ExprId>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        match spread {
            RecordSpread::None => self.eval_record_fields(fields, env, Vec::new(), 0),
            RecordSpread::Head(expr) => {
                let mut spread_env = env.clone();
                let spread = self.eval_expr(expr, &mut spread_env)?;
                self.continue_with(spread, move |runtime, spread| {
                    let spread_fields = runtime.expect_record(spread)?;
                    runtime.eval_record_fields(fields.clone(), env.clone(), spread_fields, 0)
                })
            }
            RecordSpread::Tail(expr) => {
                let fields_result =
                    self.eval_record_fields(fields.clone(), env.clone(), Vec::new(), 0)?;
                self.continue_with(fields_result, move |runtime, fields| {
                    let fields = runtime.expect_record(fields)?;
                    let mut spread_env = env.clone();
                    let spread = runtime.eval_expr(expr, &mut spread_env)?;
                    runtime.continue_with(spread, move |runtime, spread| {
                        let mut combined = fields.clone();
                        combined.extend(runtime.expect_record(spread)?);
                        value_result(Value::Record(combined))
                    })
                })
            }
        }
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
        let result = self.eval_expr(field.value, &mut field_env)?;
        self.continue_with(result, move |runtime, value| {
            let mut values = values.clone();
            values.push(ValueField {
                name: field.name.clone(),
                value,
            });
            runtime.eval_record_fields(fields.clone(), env.clone(), values, index + 1)
        })
    }

    fn eval_tuple(&mut self, items: Vec<ExprId>, env: CapturedEnv) -> RuntimeResult<'a> {
        self.eval_tuple_items(items, env, Vec::new(), 0)
    }

    fn eval_tuple_items(
        &mut self,
        items: Vec<ExprId>,
        env: CapturedEnv,
        values: Vec<Value>,
        index: usize,
    ) -> RuntimeResult<'a> {
        if index >= items.len() {
            return value_result(Value::Tuple(values));
        }
        let mut item_env = env.clone();
        let result = self.eval_expr(items[index], &mut item_env)?;
        self.continue_with(result, move |runtime, value| {
            let mut values = values.clone();
            values.push(value);
            runtime.eval_tuple_items(items.clone(), env.clone(), values, index + 1)
        })
    }

    fn eval_poly_variant(
        &mut self,
        tag: String,
        payloads: Vec<ExprId>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.eval_poly_variant_payloads(tag, payloads, env, Vec::new(), 0)
    }

    fn eval_poly_variant_payloads(
        &mut self,
        tag: String,
        payloads: Vec<ExprId>,
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
        let mut payload_env = env.clone();
        let result = self.eval_expr(payloads[index], &mut payload_env)?;
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

    fn eval_select(
        &mut self,
        base: ExprId,
        name: String,
        resolution: Option<SelectResolution>,
        env: &mut CapturedEnv,
    ) -> RuntimeResult<'a> {
        let result = self.eval_expr(base, env)?;
        self.continue_with(result, move |runtime, base| match resolution {
            Some(SelectResolution::RecordField) => {
                value_result(runtime.project_record_field(base, &name)?)
            }
            Some(SelectResolution::Method { instance }) => {
                let method = runtime.eval_instance(instance)?;
                runtime.apply_value(method, base)
            }
            Some(SelectResolution::TypeclassMethod { .. }) => Err(RuntimeError::UnsupportedExpr {
                feature: format!("typeclass method select .{name}"),
            }),
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
            return self.eval_expr(arm.body, &mut arm_env);
        };

        let guard_result = self.eval_expr(guard, &mut arm_env)?;
        self.continue_with(guard_result, move |runtime, guard| match guard {
            Value::Bool(true) => runtime.eval_expr(arm.body, &mut arm_env.clone()),
            Value::Bool(false) => {
                runtime.eval_case_arm(scrutinee.clone(), arms.clone(), env.clone(), index + 1)
            }
            value => Err(RuntimeError::NonBoolGuard { value }),
        })
    }

    fn eval_catch(
        &mut self,
        body: ExprId,
        arms: Vec<CatchArm>,
        env: &mut CapturedEnv,
    ) -> RuntimeResult<'a> {
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
            return self.eval_expr(arm.body, &mut arm_env);
        };

        let guard_result = self.eval_expr(guard, &mut arm_env)?;
        self.continue_with(guard_result, move |runtime, guard| match guard {
            Value::Bool(true) => runtime.eval_expr(arm.body, &mut arm_env.clone()),
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
                return self.eval_expr(arm.body, &mut arm_env);
            };

            let guard_result = self.eval_expr(guard, &mut arm_env)?;
            return self.continue_with(guard_result, move |runtime, guard| match guard {
                Value::Bool(true) => runtime.eval_expr(arm.body, &mut arm_env.clone()),
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

    fn eval_block(&mut self, block: Block, env: &mut CapturedEnv) -> RuntimeResult<'a> {
        self.eval_block_parts(block.stmts, block.tail, env.clone())
    }

    fn eval_block_parts(
        &mut self,
        stmts: Vec<Stmt>,
        tail: Option<ExprId>,
        env: CapturedEnv,
    ) -> RuntimeResult<'a> {
        self.eval_block_step(stmts, tail, env, 0, Value::Unit)
    }

    fn eval_block_step(
        &mut self,
        stmts: Vec<Stmt>,
        tail: Option<ExprId>,
        env: CapturedEnv,
        index: usize,
        last: Value,
    ) -> RuntimeResult<'a> {
        if index >= stmts.len() {
            if let Some(tail) = tail {
                let mut env = env;
                return self.eval_expr(tail, &mut env);
            }
            return value_result(last);
        }

        match stmts[index].clone() {
            Stmt::Let(_, pat, value) => {
                let mut value_env = env.clone();
                let result = self.eval_expr(value, &mut value_env)?;
                self.continue_with(result, move |runtime, value| {
                    let mut next_env = env.clone();
                    if !runtime.bind_pat(&pat, &value, &mut next_env)? {
                        return Err(RuntimeError::PatternMismatch);
                    }
                    runtime.eval_block_step(stmts.clone(), tail, next_env, index + 1, value)
                })
            }
            Stmt::Expr(expr) => {
                let mut expr_env = env.clone();
                let result = self.eval_expr(expr, &mut expr_env)?;
                self.continue_with(result, move |runtime, value| {
                    runtime.eval_block_step(stmts.clone(), tail, env.clone(), index + 1, value)
                })
            }
            Stmt::Module(_, module_stmts) => {
                let result = self.eval_block_parts(module_stmts, None, env.clone())?;
                self.continue_with(result, move |runtime, value| {
                    runtime.eval_block_step(stmts.clone(), tail, env.clone(), index + 1, value)
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
            Value::Closure(closure) => self.apply_closure(closure, arg),
            Value::FunctionAdapter(adapter) => self.apply_adapter(adapter, arg),
            Value::EffectOp { path } => self.emit_effect_request(path, arg),
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
        self.eval_expr(closure.body, &mut env)
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
            if marker.depth != 0
                || request.path == marker.path
                || self.request_intersects_guard_stack(request)
            {
                continue;
            }
            if !request.guard_ids.contains(&marker.id) {
                request.guard_ids.push(marker.id);
            }
        }
    }

    fn mark_active_value(&self, value: Value) -> Value {
        // Handler marker propagation follows the innermost active handler. Carrying outer
        // markers into a nested handler would make the outer handler skip the same request.
        let Some(marker) = self.active_markers.last() else {
            return value;
        };
        mark_value(value, std::slice::from_ref(marker))
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
            Pat::Tuple(pats) => {
                let Value::Tuple(values) = view else {
                    return Ok(false);
                };
                if pats.len() != values.len() {
                    return Ok(false);
                }
                for (pat, value) in pats.iter().zip(values) {
                    let value = mark_value(value.clone(), &markers);
                    if !self.bind_pat(pat, &value, env)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pat::List { .. } => Err(RuntimeError::UnsupportedPattern {
                feature: "list pattern".to_string(),
            }),
            Pat::Record { fields, spread } => {
                let Value::Record(record_fields) = view else {
                    return Ok(false);
                };
                let mut used = HashSet::new();
                for (name, pat) in fields {
                    let Some((index, field)) = find_record_field(record_fields, name) else {
                        return Ok(false);
                    };
                    used.insert(index);
                    let value = mark_value(field.value.clone(), &markers);
                    if !self.bind_pat(pat, &value, env)? {
                        return Ok(false);
                    }
                }
                match spread {
                    RecordSpread::None => Ok(true),
                    RecordSpread::Head(def) | RecordSpread::Tail(def) => {
                        let captured = record_fields
                            .iter()
                            .enumerate()
                            .filter(|(index, _)| !used.contains(index))
                            .map(|(_, field)| ValueField {
                                name: field.name.clone(),
                                value: mark_value(field.value.clone(), &markers),
                            })
                            .collect();
                        env.locals.insert(*def, Value::Record(captured));
                        Ok(true)
                    }
                }
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
            Pat::Con(_, _) => Err(RuntimeError::UnsupportedPattern {
                feature: "constructor pattern".to_string(),
            }),
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
            Value::Thunk(Thunk::Expr { body, mut env }) => self.eval_expr(body, &mut env),
            Value::Thunk(Thunk::Value(value)) => value_result(*value),
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
            value => Err(RuntimeError::ExpectedRecord { value }),
        }
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

fn value_equivalent(left: &Value, right: &Value) -> bool {
    let (left, _) = value_view(left);
    let (right, _) = value_view(right);
    match (left, right) {
        (Value::Int(left), Value::Int(right)) => left == right,
        (Value::BigInt(left), Value::BigInt(right)) => left == right,
        (Value::Float(left), Value::Float(right)) => left == right,
        (Value::Str(left), Value::Str(right)) => left == right,
        (Value::Bool(left), Value::Bool(right)) => left == right,
        (Value::Unit, Value::Unit) => true,
        (Value::Tuple(left), Value::Tuple(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| value_equivalent(left, right))
        }
        (
            Value::PolyVariant {
                tag: left_tag,
                payloads: left_payloads,
            },
            Value::PolyVariant {
                tag: right_tag,
                payloads: right_payloads,
            },
        ) => {
            left_tag == right_tag
                && left_payloads.len() == right_payloads.len()
                && left_payloads
                    .iter()
                    .zip(right_payloads)
                    .all(|(left, right)| value_equivalent(left, right))
        }
        (Value::Record(left), Value::Record(right)) => {
            left.len() == right.len()
                && left.iter().zip(right).all(|(left, right)| {
                    left.name == right.name && value_equivalent(&left.value, &right.value)
                })
        }
        _ => false,
    }
}

fn find_record_field<'a>(fields: &'a [ValueField], name: &str) -> Option<(usize, &'a ValueField)> {
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
