use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use control_vm::{
    Block, ControlEffectEvidence, ControlEffectUseKind, ControlEvidenceProgram,
    ControlEvidenceRoute, DefId, Expr, ExprId, InstanceId, Pat, Program, RecordSpread, Root,
    SelectResolution, Stmt,
};
use specialize::mono::{Lit, PrimitiveContext, PrimitiveOp};

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct RuntimeEvidenceRunOutput {
    values: Vec<RuntimeEvidenceValue>,
    pub(crate) evidence_stats: RuntimeEvidenceRunStats,
}

impl RuntimeEvidenceRunOutput {
    pub(crate) fn roots_text(&self) -> String {
        format!("run roots {}\n", format_values(&self.values))
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct RuntimeEvidenceRunStats {
    pub effect_calls: usize,
    pub direct_effect_calls: usize,
}

#[derive(Debug, Clone, PartialEq)]
enum RuntimeEvidenceValue {
    Int(i64),
    BigInt(String),
    Float(f64),
    Str(String),
    Bool(bool),
    Unit,
    Tuple(Vec<SharedValue>),
    Record(Vec<RuntimeEvidenceValueField>),
    PolyVariant {
        tag: String,
        payloads: Vec<SharedValue>,
    },
    DataConstructor {
        def: DefId,
        payloads: Vec<SharedValue>,
    },
    ConstructorFunction {
        def: DefId,
        arity: usize,
        args: Vec<SharedValue>,
    },
    PrimitiveOp {
        op: PrimitiveOp,
        context: PrimitiveContext,
        args: Vec<SharedValue>,
    },
    Closure(Rc<RuntimeEvidenceClosure>),
    EffectOp {
        expr: ExprId,
        path: Vec<String>,
    },
    Continuation(EvidenceContinuation),
    Thunk(Rc<RuntimeEvidenceThunk>),
}

#[derive(Debug, Clone, PartialEq)]
struct RuntimeEvidenceValueField {
    name: String,
    value: SharedValue,
}

#[derive(Debug, Clone, PartialEq)]
struct RuntimeEvidenceClosure {
    param: Pat,
    body: ExprId,
    env: Env,
}

#[derive(Debug, Clone, PartialEq)]
enum RuntimeEvidenceThunk {
    Expr {
        body: ExprId,
        env: Env,
    },
    Effect {
        path: Vec<String>,
        payload: SharedValue,
        route: EvidenceEffectRoute,
    },
    Value(SharedValue),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceContinuation {
    Identity,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceEffectRoute {
    Direct { handler: ExprId, resumptive: bool },
    Unhandled,
}

#[derive(Debug, Clone, PartialEq)]
struct EvidenceRequest {
    path: Vec<String>,
    payload: SharedValue,
    route: EvidenceEffectRoute,
    continuation: EvidenceContinuation,
}

#[derive(Debug, Clone, PartialEq)]
enum EvidenceEvalResult {
    Value(SharedValue),
    Request(EvidenceRequest),
}

type SharedValue = Rc<RuntimeEvidenceValue>;
type Env = HashMap<DefId, SharedValue>;

#[derive(Debug, Clone, Default)]
struct ControlEvidenceIndex {
    effect_calls: HashMap<(ExprId, ExprId), EvidenceEffectRoute>,
    stats: RuntimeEvidenceRunStats,
}

impl ControlEvidenceIndex {
    fn new(program: &Program) -> Self {
        let evidence = ControlEvidenceProgram::from_program(program);
        let mut effect_calls = HashMap::new();
        for effect in &evidence.effects {
            if let Some((apply, callee, route)) = effect_call_route(effect) {
                effect_calls.insert((apply, callee), route);
            }
        }
        let direct_effect_calls = effect_calls
            .values()
            .filter(|route| matches!(route, EvidenceEffectRoute::Direct { .. }))
            .count();
        Self {
            stats: RuntimeEvidenceRunStats {
                effect_calls: effect_calls.len(),
                direct_effect_calls,
            },
            effect_calls,
        }
    }

    fn effect_call_route(&self, apply: ExprId, callee: ExprId) -> Option<EvidenceEffectRoute> {
        self.effect_calls.get(&(apply, callee)).copied()
    }

    fn stats(&self) -> RuntimeEvidenceRunStats {
        self.stats
    }
}

fn effect_call_route(
    effect: &ControlEffectEvidence,
) -> Option<(ExprId, ExprId, EvidenceEffectRoute)> {
    let ControlEffectUseKind::OperationCall { apply, callee } = effect.kind else {
        return None;
    };
    let route = match &effect.route {
        ControlEvidenceRoute::Direct {
            handler,
            resumptive,
        } => EvidenceEffectRoute::Direct {
            handler: *handler,
            resumptive: *resumptive,
        },
        ControlEvidenceRoute::Blocked { .. } | ControlEvidenceRoute::Unhandled => {
            EvidenceEffectRoute::Unhandled
        }
    };
    Some((apply, callee, route))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RuntimeEvidenceRunError {
    MissingExpr(ExprId),
    MissingInstance(InstanceId),
    MismatchedInstanceSlot {
        requested: InstanceId,
        actual: InstanceId,
    },
    RecursiveInstance(InstanceId),
    UnboundLocal(DefId),
    UnsupportedExpr(&'static str),
    UnsupportedPattern(&'static str),
    UnsupportedPrimitive(PrimitiveOp),
    EscapedEffect(Vec<String>),
    NotFunction(String),
    NotThunk(String),
    NotRecord(String),
    MissingRecordField(String),
    PatternMismatch,
    DivideByZero,
}

impl fmt::Display for RuntimeEvidenceRunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingExpr(expr) => write!(f, "runtime-evidence-run missing expr e{}", expr.0),
            Self::MissingInstance(instance) => {
                write!(f, "runtime-evidence-run missing instance i{}", instance.0)
            }
            Self::MismatchedInstanceSlot { requested, actual } => write!(
                f,
                "runtime-evidence-run mismatched instance slot i{} != i{}",
                requested.0, actual.0
            ),
            Self::RecursiveInstance(instance) => {
                write!(f, "runtime-evidence-run recursive instance i{}", instance.0)
            }
            Self::UnboundLocal(def) => write!(f, "runtime-evidence-run unbound local d{}", def.0),
            Self::UnsupportedExpr(kind) => {
                write!(f, "runtime-evidence-run unsupported expr: {kind}")
            }
            Self::UnsupportedPattern(kind) => {
                write!(f, "runtime-evidence-run unsupported pattern: {kind}")
            }
            Self::UnsupportedPrimitive(op) => {
                write!(f, "runtime-evidence-run unsupported primitive: {op:?}")
            }
            Self::EscapedEffect(path) => write!(
                f,
                "runtime-evidence-run escaped effect request: {}",
                path.join("::")
            ),
            Self::NotFunction(value) => write!(f, "runtime-evidence-run not a function: {value}"),
            Self::NotThunk(value) => write!(f, "runtime-evidence-run not a thunk: {value}"),
            Self::NotRecord(value) => write!(f, "runtime-evidence-run not a record: {value}"),
            Self::MissingRecordField(name) => {
                write!(f, "runtime-evidence-run missing record field: {name}")
            }
            Self::PatternMismatch => write!(f, "runtime-evidence-run pattern mismatch"),
            Self::DivideByZero => write!(f, "runtime-evidence-run division by zero"),
        }
    }
}

pub(crate) fn run_program(
    program: &Program,
) -> Result<RuntimeEvidenceRunOutput, RuntimeEvidenceRunError> {
    RuntimeEvidenceRunner::new(program).run()
}

struct RuntimeEvidenceRunner<'a> {
    program: &'a Program,
    evidence: ControlEvidenceIndex,
    instances: HashMap<InstanceId, SharedValue>,
    evaluating_instances: HashSet<InstanceId>,
}

impl<'a> RuntimeEvidenceRunner<'a> {
    fn new(program: &'a Program) -> Self {
        Self {
            program,
            evidence: ControlEvidenceIndex::new(program),
            instances: HashMap::new(),
            evaluating_instances: HashSet::new(),
        }
    }

    fn run(&mut self) -> Result<RuntimeEvidenceRunOutput, RuntimeEvidenceRunError> {
        let mut values = Vec::new();
        let mut env = Env::new();
        for root in &self.program.roots {
            match root {
                Root::Instance(instance) => values.push(self.eval_instance(*instance)?),
                Root::EvalInstance(instance) => {
                    let _ = self.eval_instance(*instance)?;
                }
                Root::Expr(expr) => values.push(self.eval_expr(*expr, &mut env)?),
            }
        }
        let evidence_stats = self.evidence.stats();
        Ok(RuntimeEvidenceRunOutput {
            values: values
                .into_iter()
                .map(|value| value.as_ref().clone())
                .collect(),
            evidence_stats,
        })
    }

    fn eval_instance(
        &mut self,
        instance: InstanceId,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        if let Some(value) = self.instances.get(&instance) {
            return Ok(value.clone());
        }
        if !self.evaluating_instances.insert(instance) {
            return Err(RuntimeEvidenceRunError::RecursiveInstance(instance));
        }
        let Some(control_instance) = self.program.instances.get(instance.0 as usize) else {
            self.evaluating_instances.remove(&instance);
            return Err(RuntimeEvidenceRunError::MissingInstance(instance));
        };
        if control_instance.id != instance {
            self.evaluating_instances.remove(&instance);
            return Err(RuntimeEvidenceRunError::MismatchedInstanceSlot {
                requested: instance,
                actual: control_instance.id,
            });
        }

        let mut env = Env::new();
        let value = self.eval_expr(control_instance.entry, &mut env);
        self.evaluating_instances.remove(&instance);
        let value = value?;
        self.instances.insert(instance, value.clone());
        Ok(value)
    }

    fn eval_expr(
        &mut self,
        expr: ExprId,
        env: &mut Env,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        match self.eval_expr_result(expr, env)? {
            EvidenceEvalResult::Value(value) => Ok(value),
            EvidenceEvalResult::Request(request) => {
                Err(RuntimeEvidenceRunError::EscapedEffect(request.path))
            }
        }
    }

    fn eval_expr_result(
        &mut self,
        expr: ExprId,
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let expr_id = expr;
        let Some(expr) = self.program.exprs.get(expr_id.0 as usize) else {
            return Err(RuntimeEvidenceRunError::MissingExpr(expr));
        };
        let value = match expr {
            Expr::Lit(lit) => return Ok(value_result(value_from_lit(lit))),
            Expr::PrimitiveOp { op, context } => {
                return Ok(EvidenceEvalResult::Value(
                    self.eval_primitive_op(*op, context.clone())?,
                ));
            }
            Expr::Constructor { def, arity } => RuntimeEvidenceValue::ConstructorFunction {
                def: *def,
                arity: *arity,
                args: Vec::new(),
            },
            Expr::EffectOp { path } => RuntimeEvidenceValue::EffectOp {
                expr: expr_id,
                path: path.clone(),
            },
            Expr::Local(def) => {
                return Ok(EvidenceEvalResult::Value(
                    env.get(def)
                        .cloned()
                        .ok_or(RuntimeEvidenceRunError::UnboundLocal(*def))?,
                ));
            }
            Expr::InstanceRef(instance) => {
                return Ok(EvidenceEvalResult::Value(self.eval_instance(*instance)?));
            }
            Expr::Coerce { expr, .. } => return self.eval_expr_result(*expr, env),
            Expr::MakeThunk { body, .. } => {
                RuntimeEvidenceValue::Thunk(Rc::new(RuntimeEvidenceThunk::Expr {
                    body: *body,
                    env: env.clone(),
                }))
            }
            Expr::ForceThunk { thunk, .. } => {
                let thunk = self.eval_expr(*thunk, env)?;
                return self.force_thunk_result(thunk);
            }
            Expr::FunctionAdapter { function, .. } => return self.eval_expr_result(*function, env),
            Expr::MarkerFrame { body, .. } => return self.eval_expr_result(*body, env),
            Expr::Apply { callee, arg } => {
                let callee = self.eval_expr(*callee, env)?;
                let mut arg_env = env.clone();
                let arg = self.eval_expr(*arg, &mut arg_env)?;
                return Ok(EvidenceEvalResult::Value(self.apply_value(
                    Some(expr_id),
                    callee,
                    arg,
                )?));
            }
            Expr::RefSet { .. } => {
                return Err(RuntimeEvidenceRunError::UnsupportedExpr("ref-set"));
            }
            Expr::Lambda { param, body } => {
                RuntimeEvidenceValue::Closure(Rc::new(RuntimeEvidenceClosure {
                    param: param.clone(),
                    body: *body,
                    env: env.clone(),
                }))
            }
            Expr::Tuple(items) => {
                let mut values = Vec::with_capacity(items.len());
                for item in items {
                    values.push(self.eval_expr(*item, env)?);
                }
                RuntimeEvidenceValue::Tuple(values)
            }
            Expr::Record { fields, spread } => {
                let mut values = match spread {
                    RecordSpread::None => Vec::new(),
                    RecordSpread::Head(expr) => {
                        let spread = self.eval_expr(*expr, env)?;
                        record_fields(spread.as_ref())?
                    }
                    RecordSpread::Tail(_) => {
                        return Err(RuntimeEvidenceRunError::UnsupportedExpr(
                            "tail record spread",
                        ));
                    }
                };
                for field in fields {
                    values.push(RuntimeEvidenceValueField {
                        name: field.name.clone(),
                        value: self.eval_expr(field.value, env)?,
                    });
                }
                RuntimeEvidenceValue::Record(values)
            }
            Expr::PolyVariant { tag, payloads } => {
                let mut values = Vec::with_capacity(payloads.len());
                for payload in payloads {
                    values.push(self.eval_expr(*payload, env)?);
                }
                RuntimeEvidenceValue::PolyVariant {
                    tag: tag.clone(),
                    payloads: values,
                }
            }
            Expr::Select {
                base,
                name,
                resolution,
            } => {
                return Ok(EvidenceEvalResult::Value(
                    self.eval_select(*base, name, resolution, env)?,
                ));
            }
            Expr::Case { scrutinee, arms } => {
                let scrutinee = self.eval_expr(*scrutinee, env)?;
                return Ok(EvidenceEvalResult::Value(
                    self.eval_case(scrutinee, arms, env)?,
                ));
            }
            Expr::Catch { body, arms } => return self.eval_catch(expr_id, *body, arms, env),
            Expr::Block(block) => {
                return Ok(EvidenceEvalResult::Value(self.eval_block(block, env)?));
            }
        };
        Ok(value_result(value))
    }

    fn eval_primitive_op(
        &mut self,
        op: PrimitiveOp,
        context: PrimitiveContext,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        if op.arity() == 0 {
            return self.apply_primitive(op, &[]);
        }
        Ok(shared(RuntimeEvidenceValue::PrimitiveOp {
            op,
            context,
            args: Vec::new(),
        }))
    }

    fn apply_value(
        &mut self,
        site: Option<ExprId>,
        callee: SharedValue,
        arg: SharedValue,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        match callee.as_ref() {
            RuntimeEvidenceValue::PrimitiveOp { op, context, args } => {
                let mut args = args.clone();
                args.push(arg);
                if args.len() < op.arity() {
                    return Ok(shared(RuntimeEvidenceValue::PrimitiveOp {
                        op: *op,
                        context: context.clone(),
                        args,
                    }));
                }
                self.apply_primitive(*op, &args)
            }
            RuntimeEvidenceValue::ConstructorFunction { def, arity, args } => {
                let mut args = args.clone();
                args.push(arg);
                if args.len() < *arity {
                    return Ok(shared(RuntimeEvidenceValue::ConstructorFunction {
                        def: *def,
                        arity: *arity,
                        args,
                    }));
                }
                Ok(shared(RuntimeEvidenceValue::DataConstructor {
                    def: *def,
                    payloads: args,
                }))
            }
            RuntimeEvidenceValue::Closure(closure) => {
                let mut env = closure.env.clone();
                bind_pat(&closure.param, arg, &mut env)?;
                self.eval_expr(closure.body, &mut env)
            }
            RuntimeEvidenceValue::Continuation(EvidenceContinuation::Identity) => Ok(shared(
                RuntimeEvidenceValue::Thunk(Rc::new(RuntimeEvidenceThunk::Value(arg))),
            )),
            RuntimeEvidenceValue::Thunk(_) => {
                let callee = self.force_thunk(callee)?;
                self.apply_value(site, callee, arg)
            }
            RuntimeEvidenceValue::EffectOp { expr, path } => {
                let route = site
                    .and_then(|site| self.evidence.effect_call_route(site, *expr))
                    .unwrap_or(EvidenceEffectRoute::Unhandled);
                Ok(shared(RuntimeEvidenceValue::Thunk(Rc::new(
                    RuntimeEvidenceThunk::Effect {
                        path: path.clone(),
                        payload: arg,
                        route,
                    },
                ))))
            }
            value => Err(RuntimeEvidenceRunError::NotFunction(format_value(value))),
        }
    }

    fn force_thunk(&mut self, thunk: SharedValue) -> Result<SharedValue, RuntimeEvidenceRunError> {
        match self.force_thunk_result(thunk)? {
            EvidenceEvalResult::Value(value) => Ok(value),
            EvidenceEvalResult::Request(request) => {
                Err(RuntimeEvidenceRunError::EscapedEffect(request.path))
            }
        }
    }

    fn force_thunk_result(
        &mut self,
        thunk: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match thunk.as_ref() {
            RuntimeEvidenceValue::Thunk(thunk) => match thunk.as_ref() {
                RuntimeEvidenceThunk::Expr { body, env } => {
                    let mut env = env.clone();
                    self.eval_expr_result(*body, &mut env)
                }
                RuntimeEvidenceThunk::Effect {
                    path,
                    payload,
                    route,
                } => Ok(EvidenceEvalResult::Request(EvidenceRequest {
                    path: path.clone(),
                    payload: payload.clone(),
                    route: *route,
                    continuation: EvidenceContinuation::Identity,
                })),
                RuntimeEvidenceThunk::Value(value) => Ok(EvidenceEvalResult::Value(value.clone())),
            },
            value => Err(RuntimeEvidenceRunError::NotThunk(format_value(value))),
        }
    }

    fn eval_select(
        &mut self,
        base: ExprId,
        name: &str,
        resolution: &Option<SelectResolution>,
        env: &mut Env,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        match resolution {
            Some(SelectResolution::RecordField) | None => {
                let base = self.eval_expr(base, env)?;
                record_field(base.as_ref(), name)
            }
            Some(SelectResolution::Method { instance }) => {
                let base = self.eval_expr(base, env)?;
                let method = self.eval_instance(*instance)?;
                self.apply_value(None, method, base)
            }
            Some(SelectResolution::TypeclassMethod { .. }) => Err(
                RuntimeEvidenceRunError::UnsupportedExpr("typeclass method select"),
            ),
        }
    }

    fn eval_catch(
        &mut self,
        catch_expr: ExprId,
        body: ExprId,
        arms: &[control_vm::CatchArm],
        env: &Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let mut body_env = env.clone();
        match self.eval_expr_result(body, &mut body_env)? {
            EvidenceEvalResult::Value(value) => self.eval_value_arm(value, arms, env),
            EvidenceEvalResult::Request(request) => match request.route {
                EvidenceEffectRoute::Direct {
                    handler,
                    resumptive,
                } if handler == catch_expr => {
                    self.eval_operation_arm(request, resumptive, arms, env)
                }
                EvidenceEffectRoute::Direct { .. } | EvidenceEffectRoute::Unhandled => {
                    Ok(EvidenceEvalResult::Request(request))
                }
            },
        }
    }

    fn eval_value_arm(
        &mut self,
        value: SharedValue,
        arms: &[control_vm::CatchArm],
        env: &Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let Some(arm) = arms.iter().find(|arm| arm.operation_path.is_none()) else {
            return Ok(EvidenceEvalResult::Value(value));
        };
        let mut arm_env = env.clone();
        bind_pat(&arm.pat, value, &mut arm_env)?;
        if let Some(guard) = arm.guard {
            let guard = self.eval_expr(guard, &mut arm_env)?;
            if !matches!(guard.as_ref(), RuntimeEvidenceValue::Bool(true)) {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            }
        }
        self.eval_handler_body_result(arm.body, &mut arm_env)
    }

    fn eval_operation_arm(
        &mut self,
        request: EvidenceRequest,
        resumptive: bool,
        arms: &[control_vm::CatchArm],
        env: &Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let Some(arm) = arms
            .iter()
            .find(|arm| arm.operation_path.as_ref() == Some(&request.path))
        else {
            return Ok(EvidenceEvalResult::Request(request));
        };
        let mut arm_env = env.clone();
        bind_pat(&arm.pat, request.payload, &mut arm_env)?;
        if let Some(continuation_pat) = &arm.continuation {
            if !resumptive {
                return Err(RuntimeEvidenceRunError::UnsupportedExpr(
                    "abortive continuation binding",
                ));
            }
            bind_pat(
                continuation_pat,
                shared(RuntimeEvidenceValue::Continuation(request.continuation)),
                &mut arm_env,
            )?;
        }
        if let Some(guard) = arm.guard {
            let guard = self.eval_expr(guard, &mut arm_env)?;
            if !matches!(guard.as_ref(), RuntimeEvidenceValue::Bool(true)) {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            }
        }
        self.eval_handler_body_result(arm.body, &mut arm_env)
    }

    fn eval_handler_body_result(
        &mut self,
        body: ExprId,
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match self.eval_expr_result(body, env)? {
            EvidenceEvalResult::Value(value) => self.force_value_if_thunk_result(value),
            EvidenceEvalResult::Request(request) => Ok(EvidenceEvalResult::Request(request)),
        }
    }

    fn force_value_if_thunk_result(
        &mut self,
        value: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if matches!(value.as_ref(), RuntimeEvidenceValue::Thunk(_)) {
            self.force_thunk_result(value)
        } else {
            Ok(EvidenceEvalResult::Value(value))
        }
    }

    fn eval_case(
        &mut self,
        scrutinee: SharedValue,
        arms: &[control_vm::CaseArm],
        env: &Env,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        for arm in arms {
            let mut arm_env = env.clone();
            if bind_pat(&arm.pat, scrutinee.clone(), &mut arm_env).is_err() {
                continue;
            }
            if let Some(guard) = arm.guard {
                let guard = self.eval_expr(guard, &mut arm_env)?;
                if !matches!(guard.as_ref(), RuntimeEvidenceValue::Bool(true)) {
                    continue;
                }
            }
            return self.eval_expr(arm.body, &mut arm_env);
        }
        Err(RuntimeEvidenceRunError::PatternMismatch)
    }

    fn eval_block(
        &mut self,
        block: &Block,
        env: &mut Env,
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        let mut last = shared(RuntimeEvidenceValue::Unit);
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let(_, pat, expr) => {
                    let value = self.eval_expr(*expr, env)?;
                    bind_pat(pat, value, env)?;
                }
                Stmt::Expr(expr) => {
                    last = self.eval_expr(*expr, env)?;
                }
                Stmt::Module(_, stmts) => {
                    last = self.eval_block(
                        &Block {
                            stmts: stmts.clone(),
                            tail: None,
                        },
                        env,
                    )?;
                }
            }
        }
        if let Some(tail) = block.tail {
            self.eval_expr(tail, env)
        } else {
            Ok(last)
        }
    }

    fn apply_primitive(
        &mut self,
        op: PrimitiveOp,
        args: &[SharedValue],
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        use PrimitiveOp::*;
        let value = match op {
            BoolNot => RuntimeEvidenceValue::Bool(!expect_bool(&args[0])?),
            BoolEq => RuntimeEvidenceValue::Bool(expect_bool(&args[0])? == expect_bool(&args[1])?),
            IntAdd => RuntimeEvidenceValue::Int(expect_int(&args[0])? + expect_int(&args[1])?),
            IntSub => RuntimeEvidenceValue::Int(expect_int(&args[0])? - expect_int(&args[1])?),
            IntMul => RuntimeEvidenceValue::Int(expect_int(&args[0])? * expect_int(&args[1])?),
            IntDiv => {
                let right = expect_int(&args[1])?;
                if right == 0 {
                    return Err(RuntimeEvidenceRunError::DivideByZero);
                }
                RuntimeEvidenceValue::Int(expect_int(&args[0])? / right)
            }
            IntMod => {
                let right = expect_int(&args[1])?;
                if right == 0 {
                    return Err(RuntimeEvidenceRunError::DivideByZero);
                }
                RuntimeEvidenceValue::Int(expect_int(&args[0])? % right)
            }
            IntEq => RuntimeEvidenceValue::Bool(expect_int(&args[0])? == expect_int(&args[1])?),
            IntLt => RuntimeEvidenceValue::Bool(expect_int(&args[0])? < expect_int(&args[1])?),
            IntLe => RuntimeEvidenceValue::Bool(expect_int(&args[0])? <= expect_int(&args[1])?),
            IntGt => RuntimeEvidenceValue::Bool(expect_int(&args[0])? > expect_int(&args[1])?),
            IntGe => RuntimeEvidenceValue::Bool(expect_int(&args[0])? >= expect_int(&args[1])?),
            FloatAdd => {
                RuntimeEvidenceValue::Float(expect_float(&args[0])? + expect_float(&args[1])?)
            }
            FloatSub => {
                RuntimeEvidenceValue::Float(expect_float(&args[0])? - expect_float(&args[1])?)
            }
            FloatMul => {
                RuntimeEvidenceValue::Float(expect_float(&args[0])? * expect_float(&args[1])?)
            }
            FloatDiv => {
                RuntimeEvidenceValue::Float(expect_float(&args[0])? / expect_float(&args[1])?)
            }
            FloatEq => {
                RuntimeEvidenceValue::Bool(expect_float(&args[0])? == expect_float(&args[1])?)
            }
            FloatLt => {
                RuntimeEvidenceValue::Bool(expect_float(&args[0])? < expect_float(&args[1])?)
            }
            FloatLe => {
                RuntimeEvidenceValue::Bool(expect_float(&args[0])? <= expect_float(&args[1])?)
            }
            FloatGt => {
                RuntimeEvidenceValue::Bool(expect_float(&args[0])? > expect_float(&args[1])?)
            }
            FloatGe => {
                RuntimeEvidenceValue::Bool(expect_float(&args[0])? >= expect_float(&args[1])?)
            }
            StringEq => RuntimeEvidenceValue::Bool(expect_str(&args[0])? == expect_str(&args[1])?),
            StringConcat => RuntimeEvidenceValue::Str(format!(
                "{}{}",
                expect_str(&args[0])?,
                expect_str(&args[1])?
            )),
            IntToString => RuntimeEvidenceValue::Str(expect_int(&args[0])?.to_string()),
            FloatToString => RuntimeEvidenceValue::Str(expect_float(&args[0])?.to_string()),
            BoolToString => RuntimeEvidenceValue::Str(expect_bool(&args[0])?.to_string()),
            _ => return Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op)),
        };
        Ok(shared(value))
    }
}

fn bind_pat(pat: &Pat, value: SharedValue, env: &mut Env) -> Result<(), RuntimeEvidenceRunError> {
    match pat {
        Pat::Wild => Ok(()),
        Pat::Var(def) => {
            env.insert(*def, value);
            Ok(())
        }
        Pat::Lit(lit) if lit_matches(lit, value.as_ref()) => Ok(()),
        Pat::Lit(_) => Err(RuntimeEvidenceRunError::PatternMismatch),
        Pat::Tuple(items) => {
            let RuntimeEvidenceValue::Tuple(values) = value.as_ref() else {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            };
            if items.len() != values.len() {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            }
            for (pat, value) in items.iter().zip(values) {
                bind_pat(pat, value.clone(), env)?;
            }
            Ok(())
        }
        Pat::PolyVariant(tag, payload_pats) => {
            let RuntimeEvidenceValue::PolyVariant {
                tag: value_tag,
                payloads,
            } = value.as_ref()
            else {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            };
            if tag != value_tag || payload_pats.len() != payloads.len() {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            }
            for (pat, value) in payload_pats.iter().zip(payloads) {
                bind_pat(pat, value.clone(), env)?;
            }
            Ok(())
        }
        Pat::Con(def, payload_pats) => {
            let RuntimeEvidenceValue::DataConstructor {
                def: value_def,
                payloads,
            } = value.as_ref()
            else {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            };
            if def != value_def || payload_pats.len() != payloads.len() {
                return Err(RuntimeEvidenceRunError::PatternMismatch);
            }
            for (pat, value) in payload_pats.iter().zip(payloads) {
                bind_pat(pat, value.clone(), env)?;
            }
            Ok(())
        }
        Pat::As(inner, def) => {
            bind_pat(inner, value.clone(), env)?;
            env.insert(*def, value);
            Ok(())
        }
        Pat::Or(left, right) => {
            let mut left_env = env.clone();
            if bind_pat(left, value.clone(), &mut left_env).is_ok() {
                *env = left_env;
                return Ok(());
            }
            bind_pat(right, value, env)
        }
        Pat::List { .. } => Err(RuntimeEvidenceRunError::UnsupportedPattern("list")),
        Pat::Record { .. } => Err(RuntimeEvidenceRunError::UnsupportedPattern("record")),
        Pat::Ref(_) => Err(RuntimeEvidenceRunError::UnsupportedPattern("ref")),
    }
}

fn value_from_lit(lit: &Lit) -> RuntimeEvidenceValue {
    match lit {
        Lit::Int(value) => RuntimeEvidenceValue::Int(*value),
        Lit::BigInt(value) => RuntimeEvidenceValue::BigInt(value.to_string()),
        Lit::Float(value) => RuntimeEvidenceValue::Float(*value),
        Lit::Str(value) => RuntimeEvidenceValue::Str(value.clone()),
        Lit::Bool(value) => RuntimeEvidenceValue::Bool(*value),
        Lit::Unit => RuntimeEvidenceValue::Unit,
    }
}

fn lit_matches(lit: &Lit, value: &RuntimeEvidenceValue) -> bool {
    match (lit, value) {
        (Lit::Int(left), RuntimeEvidenceValue::Int(right)) => left == right,
        (Lit::BigInt(left), RuntimeEvidenceValue::BigInt(right)) => left.to_string() == *right,
        (Lit::Float(left), RuntimeEvidenceValue::Float(right)) => left == right,
        (Lit::Str(left), RuntimeEvidenceValue::Str(right)) => left == right,
        (Lit::Bool(left), RuntimeEvidenceValue::Bool(right)) => left == right,
        (Lit::Unit, RuntimeEvidenceValue::Unit) => true,
        _ => false,
    }
}

fn expect_int(value: &SharedValue) -> Result<i64, RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Int(value) => Ok(*value),
        value => Err(RuntimeEvidenceRunError::UnsupportedExpr(match value {
            RuntimeEvidenceValue::BigInt(_) => "bigint primitive argument",
            RuntimeEvidenceValue::Float(_) => "float where int expected",
            RuntimeEvidenceValue::Str(_) => "string where int expected",
            RuntimeEvidenceValue::Bool(_) => "bool where int expected",
            _ => "non-int primitive argument",
        })),
    }
}

fn expect_float(value: &SharedValue) -> Result<f64, RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Float(value) => Ok(*value),
        value => Err(RuntimeEvidenceRunError::UnsupportedExpr(match value {
            RuntimeEvidenceValue::Int(_) => "int where float expected",
            _ => "non-float primitive argument",
        })),
    }
}

fn expect_bool(value: &SharedValue) -> Result<bool, RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Bool(value) => Ok(*value),
        _ => Err(RuntimeEvidenceRunError::UnsupportedExpr(
            "non-bool primitive argument",
        )),
    }
}

fn expect_str(value: &SharedValue) -> Result<&str, RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Str(value) => Ok(value),
        _ => Err(RuntimeEvidenceRunError::UnsupportedExpr(
            "non-string primitive argument",
        )),
    }
}

fn record_fields(
    value: &RuntimeEvidenceValue,
) -> Result<Vec<RuntimeEvidenceValueField>, RuntimeEvidenceRunError> {
    match value {
        RuntimeEvidenceValue::Record(fields) => Ok(fields.clone()),
        value => Err(RuntimeEvidenceRunError::NotRecord(format_value(value))),
    }
}

fn record_field(
    value: &RuntimeEvidenceValue,
    name: &str,
) -> Result<SharedValue, RuntimeEvidenceRunError> {
    let fields = record_fields(value)?;
    fields
        .into_iter()
        .find(|field| field.name == name)
        .map(|field| field.value)
        .ok_or_else(|| RuntimeEvidenceRunError::MissingRecordField(name.to_string()))
}

fn shared(value: RuntimeEvidenceValue) -> SharedValue {
    Rc::new(value)
}

fn format_values(values: &[RuntimeEvidenceValue]) -> String {
    let values = values.iter().map(format_value).collect::<Vec<_>>();
    format!("[{}]", values.join(", "))
}

fn format_value(value: &RuntimeEvidenceValue) -> String {
    match value {
        RuntimeEvidenceValue::Int(value) => value.to_string(),
        RuntimeEvidenceValue::BigInt(value) => value.clone(),
        RuntimeEvidenceValue::Float(value) => value.to_string(),
        RuntimeEvidenceValue::Str(value) => format!("{value:?}"),
        RuntimeEvidenceValue::Bool(value) => value.to_string(),
        RuntimeEvidenceValue::Unit => "()".to_string(),
        RuntimeEvidenceValue::Tuple(values) => format_delimited("(", ")", values),
        RuntimeEvidenceValue::Record(fields) => {
            let fields = fields
                .iter()
                .map(|field| format!("{}: {}", field.name, format_value(&field.value)))
                .collect::<Vec<_>>();
            format!("{{{}}}", fields.join(", "))
        }
        RuntimeEvidenceValue::PolyVariant { tag, payloads } => {
            if payloads.is_empty() {
                tag.clone()
            } else {
                format!("{tag}({})", format_shared_values(payloads))
            }
        }
        RuntimeEvidenceValue::DataConstructor { def, payloads } => {
            if payloads.is_empty() {
                format!("<ctor d{}>", def.0)
            } else {
                format!("<ctor d{}>({})", def.0, format_shared_values(payloads))
            }
        }
        RuntimeEvidenceValue::ConstructorFunction { def, .. } => format!("<ctor-fn d{}>", def.0),
        RuntimeEvidenceValue::PrimitiveOp { op, .. } => format!("<primitive {op:?}>"),
        RuntimeEvidenceValue::Closure(_) => "<function>".to_string(),
        RuntimeEvidenceValue::EffectOp { path, .. } => {
            format!("<effect-op {}>", path.join("::"))
        }
        RuntimeEvidenceValue::Continuation(_) => "<continuation>".to_string(),
        RuntimeEvidenceValue::Thunk(_) => "<thunk>".to_string(),
    }
}

fn value_result(value: RuntimeEvidenceValue) -> EvidenceEvalResult {
    EvidenceEvalResult::Value(shared(value))
}

fn format_delimited(open: &str, close: &str, values: &[SharedValue]) -> String {
    let mut out = String::new();
    out.push_str(open);
    out.push_str(&format_shared_values(values));
    if values.len() == 1 && open == "(" {
        out.push(',');
    }
    out.push_str(close);
    out
}

fn format_shared_values(values: &[SharedValue]) -> String {
    values
        .iter()
        .map(|value| format_value(value.as_ref()))
        .collect::<Vec<_>>()
        .join(", ")
}
