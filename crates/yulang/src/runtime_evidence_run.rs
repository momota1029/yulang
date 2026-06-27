use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use control_vm::{
    Block, ControlEffectEvidence, ControlEffectUseKind, ControlEvidenceProgram,
    ControlEvidenceRoute, DefId, Expr, ExprId, InstanceId, Pat, Program, RecordSpread, Root,
    SelectResolution, Stmt,
};
use specialize::mono::{FunctionAdapterHygiene, Lit, PrimitiveContext, PrimitiveOp, Type};

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
    List(Vec<SharedValue>),
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
    FunctionAdapter {
        source: Type,
        target: Type,
        function: SharedValue,
    },
    Closure(Rc<RuntimeEvidenceClosure>),
    RecursiveClosure {
        def: DefId,
        closure: Rc<RuntimeEvidenceClosure>,
    },
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
    Continuation {
        continuation: EvidenceContinuation,
        arg: SharedValue,
    },
    Value(SharedValue),
    Adapter {
        source: Type,
        target: Type,
        thunk: SharedValue,
    },
}

#[derive(Debug, Clone, PartialEq)]
struct EvidenceContinuation(Rc<EvidenceContinuationFrame>);

#[derive(Debug, Clone, PartialEq)]
enum EvidenceContinuationFrame {
    Identity,
    ForceThunk {
        target_value_is_thunk: bool,
        next: EvidenceContinuation,
    },
    ForceValueIfThunk {
        next: EvidenceContinuation,
    },
    ApplyCallee {
        site: Option<ExprId>,
        arg: ExprId,
        env: Env,
        next: EvidenceContinuation,
    },
    ApplyArg {
        site: Option<ExprId>,
        callee: SharedValue,
        next: EvidenceContinuation,
    },
    ApplyForcedCallee {
        site: Option<ExprId>,
        arg: SharedValue,
        next: EvidenceContinuation,
    },
    AdaptValue {
        source: Type,
        target: Type,
        next: EvidenceContinuation,
    },
    WrapThunkValue {
        next: EvidenceContinuation,
    },
    ApplyAdapterArg {
        function: SharedValue,
        source_ret: Type,
        target_ret: Type,
        next: EvidenceContinuation,
    },
    ApplyAdapterResult {
        source_ret: Type,
        target_ret: Type,
        next: EvidenceContinuation,
    },
    CaseScrutinee {
        arms: Vec<control_vm::CaseArm>,
        env: Env,
        next: EvidenceContinuation,
    },
    CatchBody {
        catch_expr: ExprId,
        arms: Vec<control_vm::CatchArm>,
        env: Env,
        next: EvidenceContinuation,
    },
    MarkerFrame {
        path: Vec<String>,
        next: EvidenceContinuation,
    },
    TupleItems {
        values: Vec<SharedValue>,
        rest: Vec<ExprId>,
        env: Env,
        next: EvidenceContinuation,
    },
    RecordSpread {
        fields: Vec<control_vm::RecordField>,
        env: Env,
        next: EvidenceContinuation,
    },
    RecordFields {
        values: Vec<RuntimeEvidenceValueField>,
        rest: Vec<control_vm::RecordField>,
        env: Env,
        next: EvidenceContinuation,
    },
    PolyVariantPayloads {
        tag: String,
        values: Vec<SharedValue>,
        rest: Vec<ExprId>,
        env: Env,
        next: EvidenceContinuation,
    },
    SelectBase {
        name: String,
        resolution: Option<SelectResolution>,
        next: EvidenceContinuation,
    },
    BlockStmt {
        resume: EvidenceBlockResume,
        rest: Vec<Stmt>,
        tail: Option<ExprId>,
        env: Env,
        last: SharedValue,
        next: EvidenceContinuation,
    },
}

#[derive(Debug, Clone, PartialEq)]
enum EvidenceBlockResume {
    Let(Pat),
    Expr,
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
    visible_markers: Vec<Vec<String>>,
    continuation: EvidenceContinuation,
}

#[derive(Debug, Clone, PartialEq)]
enum EvidenceEvalResult {
    Value(SharedValue),
    Request(EvidenceRequest),
}

type SharedValue = Rc<RuntimeEvidenceValue>;
type Env = HashMap<DefId, SharedValue>;

impl EvidenceContinuation {
    fn identity() -> Self {
        Self(Rc::new(EvidenceContinuationFrame::Identity))
    }

    fn force_thunk(target_value_is_thunk: bool, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::ForceThunk {
            target_value_is_thunk,
            next,
        }))
    }

    fn force_value_if_thunk(next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::ForceValueIfThunk {
            next,
        }))
    }

    fn apply_callee(site: Option<ExprId>, arg: ExprId, env: Env, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::ApplyCallee {
            site,
            arg,
            env,
            next,
        }))
    }

    fn apply_arg(site: Option<ExprId>, callee: SharedValue, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::ApplyArg {
            site,
            callee,
            next,
        }))
    }

    fn apply_forced_callee(site: Option<ExprId>, arg: SharedValue, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::ApplyForcedCallee {
            site,
            arg,
            next,
        }))
    }

    fn adapt_value(source: Type, target: Type, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::AdaptValue {
            source,
            target,
            next,
        }))
    }

    fn wrap_thunk_value(next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::WrapThunkValue { next }))
    }

    fn apply_adapter_arg(
        function: SharedValue,
        source_ret: Type,
        target_ret: Type,
        next: Self,
    ) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::ApplyAdapterArg {
            function,
            source_ret,
            target_ret,
            next,
        }))
    }

    fn apply_adapter_result(source_ret: Type, target_ret: Type, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::ApplyAdapterResult {
            source_ret,
            target_ret,
            next,
        }))
    }

    fn case_scrutinee(arms: Vec<control_vm::CaseArm>, env: Env, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::CaseScrutinee {
            arms,
            env,
            next,
        }))
    }

    fn catch_body(
        catch_expr: ExprId,
        arms: Vec<control_vm::CatchArm>,
        env: Env,
        next: Self,
    ) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::CatchBody {
            catch_expr,
            arms,
            env,
            next,
        }))
    }

    fn marker_frame(path: Vec<String>, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::MarkerFrame {
            path,
            next,
        }))
    }

    fn tuple_items(values: Vec<SharedValue>, rest: Vec<ExprId>, env: Env, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::TupleItems {
            values,
            rest,
            env,
            next,
        }))
    }

    fn record_spread(fields: Vec<control_vm::RecordField>, env: Env, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::RecordSpread {
            fields,
            env,
            next,
        }))
    }

    fn record_fields(
        values: Vec<RuntimeEvidenceValueField>,
        rest: Vec<control_vm::RecordField>,
        env: Env,
        next: Self,
    ) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::RecordFields {
            values,
            rest,
            env,
            next,
        }))
    }

    fn poly_variant_payloads(
        tag: String,
        values: Vec<SharedValue>,
        rest: Vec<ExprId>,
        env: Env,
        next: Self,
    ) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::PolyVariantPayloads {
            tag,
            values,
            rest,
            env,
            next,
        }))
    }

    fn select_base(name: String, resolution: Option<SelectResolution>, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::SelectBase {
            name,
            resolution,
            next,
        }))
    }

    fn block_stmt(
        resume: EvidenceBlockResume,
        rest: Vec<Stmt>,
        tail: Option<ExprId>,
        env: Env,
        last: SharedValue,
        next: Self,
    ) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::BlockStmt {
            resume,
            rest,
            tail,
            env,
            last,
            next,
        }))
    }

    fn is_identity(&self) -> bool {
        matches!(self.0.as_ref(), EvidenceContinuationFrame::Identity)
    }

    fn then(self, tail: Self) -> Self {
        if tail.is_identity() {
            return self;
        }
        match self.0.as_ref() {
            EvidenceContinuationFrame::Identity => tail,
            EvidenceContinuationFrame::ForceThunk {
                target_value_is_thunk,
                next,
            } => Self::force_thunk(*target_value_is_thunk, next.clone().then(tail)),
            EvidenceContinuationFrame::ForceValueIfThunk { next } => {
                Self::force_value_if_thunk(next.clone().then(tail))
            }
            EvidenceContinuationFrame::ApplyCallee {
                site,
                arg,
                env,
                next,
            } => Self::apply_callee(*site, *arg, env.clone(), next.clone().then(tail)),
            EvidenceContinuationFrame::ApplyArg { site, callee, next } => {
                Self::apply_arg(*site, callee.clone(), next.clone().then(tail))
            }
            EvidenceContinuationFrame::ApplyForcedCallee { site, arg, next } => {
                Self::apply_forced_callee(*site, arg.clone(), next.clone().then(tail))
            }
            EvidenceContinuationFrame::AdaptValue {
                source,
                target,
                next,
            } => Self::adapt_value(source.clone(), target.clone(), next.clone().then(tail)),
            EvidenceContinuationFrame::WrapThunkValue { next } => {
                Self::wrap_thunk_value(next.clone().then(tail))
            }
            EvidenceContinuationFrame::ApplyAdapterArg {
                function,
                source_ret,
                target_ret,
                next,
            } => Self::apply_adapter_arg(
                function.clone(),
                source_ret.clone(),
                target_ret.clone(),
                next.clone().then(tail),
            ),
            EvidenceContinuationFrame::ApplyAdapterResult {
                source_ret,
                target_ret,
                next,
            } => Self::apply_adapter_result(
                source_ret.clone(),
                target_ret.clone(),
                next.clone().then(tail),
            ),
            EvidenceContinuationFrame::CaseScrutinee { arms, env, next } => {
                Self::case_scrutinee(arms.clone(), env.clone(), next.clone().then(tail))
            }
            EvidenceContinuationFrame::CatchBody {
                catch_expr,
                arms,
                env,
                next,
            } => Self::catch_body(
                *catch_expr,
                arms.clone(),
                env.clone(),
                next.clone().then(tail),
            ),
            EvidenceContinuationFrame::MarkerFrame { path, next } => {
                Self::marker_frame(path.clone(), next.clone().then(tail))
            }
            EvidenceContinuationFrame::TupleItems {
                values,
                rest,
                env,
                next,
            } => Self::tuple_items(
                values.clone(),
                rest.clone(),
                env.clone(),
                next.clone().then(tail),
            ),
            EvidenceContinuationFrame::RecordSpread { fields, env, next } => {
                Self::record_spread(fields.clone(), env.clone(), next.clone().then(tail))
            }
            EvidenceContinuationFrame::RecordFields {
                values,
                rest,
                env,
                next,
            } => Self::record_fields(
                values.clone(),
                rest.clone(),
                env.clone(),
                next.clone().then(tail),
            ),
            EvidenceContinuationFrame::PolyVariantPayloads {
                tag,
                values,
                rest,
                env,
                next,
            } => Self::poly_variant_payloads(
                tag.clone(),
                values.clone(),
                rest.clone(),
                env.clone(),
                next.clone().then(tail),
            ),
            EvidenceContinuationFrame::SelectBase {
                name,
                resolution,
                next,
            } => Self::select_base(name.clone(), resolution.clone(), next.clone().then(tail)),
            EvidenceContinuationFrame::BlockStmt {
                resume,
                rest,
                tail: block_tail,
                env,
                last,
                next,
            } => Self::block_stmt(
                resume.clone(),
                rest.clone(),
                *block_tail,
                env.clone(),
                last.clone(),
                next.clone().then(tail),
            ),
        }
    }
}

impl EvidenceRequest {
    fn map_continuation(
        mut self,
        f: impl FnOnce(EvidenceContinuation) -> EvidenceContinuation,
    ) -> Self {
        self.continuation = f(self.continuation);
        self
    }

    fn append_continuation(mut self, tail: EvidenceContinuation) -> Self {
        self.continuation = self.continuation.then(tail);
        self
    }

    fn add_visible_marker(&mut self, marker: &[String]) {
        if path_is_prefix(marker, &self.path)
            && !self
                .visible_markers
                .iter()
                .any(|existing| existing == marker)
        {
            self.visible_markers.push(marker.to_vec());
        }
    }

    fn with_visible_marker(mut self, marker: &[String]) -> Self {
        self.add_visible_marker(marker);
        self
    }

    fn is_visible_to(&self, operation_path: &[String]) -> bool {
        operation_path == self.path
            && self
                .visible_markers
                .iter()
                .any(|marker| path_is_prefix(marker, operation_path))
    }
}

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
            Expr::ForceThunk { target, thunk, .. } => {
                let target_value_is_thunk = matches!(target.value, Type::Thunk { .. });
                return match self.eval_expr_result(*thunk, env)? {
                    EvidenceEvalResult::Value(thunk) => {
                        let result = self.force_thunk_result(thunk)?;
                        self.finish_force_thunk_result(result, target_value_is_thunk)
                    }
                    EvidenceEvalResult::Request(request) => Ok(EvidenceEvalResult::Request(
                        request.append_continuation(EvidenceContinuation::force_thunk(
                            target_value_is_thunk,
                            EvidenceContinuation::identity(),
                        )),
                    )),
                };
            }
            Expr::FunctionAdapter {
                source,
                target,
                function,
                hygiene,
            } => {
                if !function_adapter_hygiene_is_empty(hygiene) {
                    return Err(RuntimeEvidenceRunError::UnsupportedExpr(
                        "function adapter hygiene",
                    ));
                }
                return match self.eval_expr_result(*function, env)? {
                    EvidenceEvalResult::Value(function) => Ok(EvidenceEvalResult::Value(shared(
                        RuntimeEvidenceValue::FunctionAdapter {
                            source: source.clone(),
                            target: target.clone(),
                            function,
                        },
                    ))),
                    EvidenceEvalResult::Request(request) => Ok(EvidenceEvalResult::Request(
                        request.append_continuation(EvidenceContinuation::adapt_value(
                            source.clone(),
                            target.clone(),
                            EvidenceContinuation::identity(),
                        )),
                    )),
                };
            }
            Expr::MarkerFrame { path, body } => {
                return match self.eval_expr_result(*body, env)? {
                    EvidenceEvalResult::Value(value) => Ok(EvidenceEvalResult::Value(value)),
                    EvidenceEvalResult::Request(request) => {
                        let marker = EvidenceContinuation::marker_frame(
                            path.clone(),
                            EvidenceContinuation::identity(),
                        );
                        Ok(EvidenceEvalResult::Request(
                            request
                                .with_visible_marker(path)
                                .map_continuation(|continuation| continuation.then(marker)),
                        ))
                    }
                };
            }
            Expr::Apply { callee, arg } => {
                return self.eval_apply_result(Some(expr_id), *callee, *arg, env);
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
                return self.eval_tuple_items_result(Vec::with_capacity(items.len()), items, env);
            }
            Expr::Record { fields, spread } => {
                return self.eval_record_result(fields, spread, env);
            }
            Expr::PolyVariant { tag, payloads } => {
                return self.eval_poly_variant_payloads_result(
                    tag.clone(),
                    Vec::with_capacity(payloads.len()),
                    payloads,
                    env,
                );
            }
            Expr::Select {
                base,
                name,
                resolution,
            } => {
                return self.eval_select_result(*base, name, resolution, env);
            }
            Expr::Case { scrutinee, arms } => {
                return match self.eval_expr_result(*scrutinee, env)? {
                    EvidenceEvalResult::Value(scrutinee) => {
                        self.eval_case_scrutinee_result(scrutinee, arms, env)
                    }
                    EvidenceEvalResult::Request(request) => Ok(EvidenceEvalResult::Request(
                        request.append_continuation(EvidenceContinuation::case_scrutinee(
                            arms.clone(),
                            env.clone(),
                            EvidenceContinuation::identity(),
                        )),
                    )),
                };
            }
            Expr::Catch { body, arms } => return self.eval_catch(expr_id, *body, arms, env),
            Expr::Block(block) => {
                return self.eval_block_result(block, env);
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
            return self.apply_primitive(op, &context, &[]);
        }
        Ok(shared(RuntimeEvidenceValue::PrimitiveOp {
            op,
            context,
            args: Vec::new(),
        }))
    }

    fn eval_apply_result(
        &mut self,
        site: Option<ExprId>,
        callee_expr: ExprId,
        arg_expr: ExprId,
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match self.eval_expr_result(callee_expr, env)? {
            EvidenceEvalResult::Value(callee) => {
                self.eval_apply_arg_result(site, callee, arg_expr, env)
            }
            EvidenceEvalResult::Request(request) => Ok(EvidenceEvalResult::Request(
                request.append_continuation(EvidenceContinuation::apply_callee(
                    site,
                    arg_expr,
                    env.clone(),
                    EvidenceContinuation::identity(),
                )),
            )),
        }
    }

    fn eval_apply_arg_result(
        &mut self,
        site: Option<ExprId>,
        callee: SharedValue,
        arg_expr: ExprId,
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let mut arg_env = env.clone();
        match self.eval_expr_result(arg_expr, &mut arg_env)? {
            EvidenceEvalResult::Value(arg) => self.apply_value_result(site, callee, arg),
            EvidenceEvalResult::Request(request) => {
                Ok(EvidenceEvalResult::Request(request.append_continuation(
                    EvidenceContinuation::apply_arg(site, callee, EvidenceContinuation::identity()),
                )))
            }
        }
    }

    fn eval_tuple_items_result(
        &mut self,
        mut values: Vec<SharedValue>,
        items: &[ExprId],
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        for (index, item) in items.iter().enumerate() {
            match self.eval_expr_result(*item, env)? {
                EvidenceEvalResult::Value(value) => values.push(value),
                EvidenceEvalResult::Request(request) => {
                    let rest = items[index + 1..].to_vec();
                    return Ok(EvidenceEvalResult::Request(request.append_continuation(
                        EvidenceContinuation::tuple_items(
                            values,
                            rest,
                            env.clone(),
                            EvidenceContinuation::identity(),
                        ),
                    )));
                }
            }
        }
        Ok(EvidenceEvalResult::Value(shared(
            RuntimeEvidenceValue::Tuple(values),
        )))
    }

    fn eval_record_result(
        &mut self,
        fields: &[control_vm::RecordField],
        spread: &RecordSpread<ExprId>,
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let values = match spread {
            RecordSpread::None => Vec::new(),
            RecordSpread::Head(expr) => match self.eval_expr_result(*expr, env)? {
                EvidenceEvalResult::Value(spread) => record_fields(spread.as_ref())?,
                EvidenceEvalResult::Request(request) => {
                    return Ok(EvidenceEvalResult::Request(request.append_continuation(
                        EvidenceContinuation::record_spread(
                            fields.to_vec(),
                            env.clone(),
                            EvidenceContinuation::identity(),
                        ),
                    )));
                }
            },
            RecordSpread::Tail(_) => {
                return Err(RuntimeEvidenceRunError::UnsupportedExpr(
                    "tail record spread",
                ));
            }
        };
        self.eval_record_fields_result(values, fields, env)
    }

    fn eval_record_fields_result(
        &mut self,
        mut values: Vec<RuntimeEvidenceValueField>,
        fields: &[control_vm::RecordField],
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        for (index, field) in fields.iter().enumerate() {
            match self.eval_expr_result(field.value, env)? {
                EvidenceEvalResult::Value(value) => values.push(RuntimeEvidenceValueField {
                    name: field.name.clone(),
                    value,
                }),
                EvidenceEvalResult::Request(request) => {
                    let rest = fields[index..].to_vec();
                    return Ok(EvidenceEvalResult::Request(request.append_continuation(
                        EvidenceContinuation::record_fields(
                            values,
                            rest,
                            env.clone(),
                            EvidenceContinuation::identity(),
                        ),
                    )));
                }
            }
        }
        Ok(EvidenceEvalResult::Value(shared(
            RuntimeEvidenceValue::Record(values),
        )))
    }

    fn eval_poly_variant_payloads_result(
        &mut self,
        tag: String,
        mut values: Vec<SharedValue>,
        payloads: &[ExprId],
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        for (index, payload) in payloads.iter().enumerate() {
            match self.eval_expr_result(*payload, env)? {
                EvidenceEvalResult::Value(value) => values.push(value),
                EvidenceEvalResult::Request(request) => {
                    let rest = payloads[index + 1..].to_vec();
                    return Ok(EvidenceEvalResult::Request(request.append_continuation(
                        EvidenceContinuation::poly_variant_payloads(
                            tag,
                            values,
                            rest,
                            env.clone(),
                            EvidenceContinuation::identity(),
                        ),
                    )));
                }
            }
        }
        Ok(EvidenceEvalResult::Value(shared(
            RuntimeEvidenceValue::PolyVariant {
                tag,
                payloads: values,
            },
        )))
    }

    fn eval_select_result(
        &mut self,
        base: ExprId,
        name: &str,
        resolution: &Option<SelectResolution>,
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match self.eval_expr_result(base, env)? {
            EvidenceEvalResult::Value(base) => {
                self.apply_select_base_result(base, name, resolution)
            }
            EvidenceEvalResult::Request(request) => Ok(EvidenceEvalResult::Request(
                request.append_continuation(EvidenceContinuation::select_base(
                    name.to_string(),
                    resolution.clone(),
                    EvidenceContinuation::identity(),
                )),
            )),
        }
    }

    fn apply_select_base_result(
        &mut self,
        base: SharedValue,
        name: &str,
        resolution: &Option<SelectResolution>,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match resolution {
            Some(SelectResolution::RecordField) | None => {
                record_field(base.as_ref(), name).map(EvidenceEvalResult::Value)
            }
            Some(SelectResolution::Method { instance }) => {
                let method = self.eval_instance(*instance)?;
                self.apply_value_result(None, method, base)
            }
            Some(SelectResolution::TypeclassMethod { .. }) => Err(
                RuntimeEvidenceRunError::UnsupportedExpr("typeclass method select"),
            ),
        }
    }

    fn apply_value_result(
        &mut self,
        site: Option<ExprId>,
        callee: SharedValue,
        arg: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match callee.as_ref() {
            RuntimeEvidenceValue::PrimitiveOp { op, context, args } => {
                let mut args = args.clone();
                args.push(arg);
                if args.len() < op.arity() {
                    return Ok(EvidenceEvalResult::Value(shared(
                        RuntimeEvidenceValue::PrimitiveOp {
                            op: *op,
                            context: context.clone(),
                            args,
                        },
                    )));
                }
                self.apply_primitive(*op, context, &args)
                    .map(EvidenceEvalResult::Value)
            }
            RuntimeEvidenceValue::FunctionAdapter {
                source,
                target,
                function,
            } => self.apply_adapter_result(source, target, function.clone(), arg),
            RuntimeEvidenceValue::ConstructorFunction { def, arity, args } => {
                let mut args = args.clone();
                args.push(arg);
                if args.len() < *arity {
                    return Ok(EvidenceEvalResult::Value(shared(
                        RuntimeEvidenceValue::ConstructorFunction {
                            def: *def,
                            arity: *arity,
                            args,
                        },
                    )));
                }
                Ok(EvidenceEvalResult::Value(shared(
                    RuntimeEvidenceValue::DataConstructor {
                        def: *def,
                        payloads: args,
                    },
                )))
            }
            RuntimeEvidenceValue::Closure(closure) => {
                let mut env = closure.env.clone();
                bind_pat(&closure.param, arg, &mut env)?;
                self.eval_expr_result(closure.body, &mut env)
            }
            RuntimeEvidenceValue::RecursiveClosure { def, closure } => {
                let mut env = closure.env.clone();
                env.insert(
                    *def,
                    shared(RuntimeEvidenceValue::RecursiveClosure {
                        def: *def,
                        closure: closure.clone(),
                    }),
                );
                bind_pat(&closure.param, arg, &mut env)?;
                self.eval_expr_result(closure.body, &mut env)
            }
            RuntimeEvidenceValue::Continuation(continuation) => {
                Ok(EvidenceEvalResult::Value(shared(
                    RuntimeEvidenceValue::Thunk(Rc::new(RuntimeEvidenceThunk::Continuation {
                        continuation: continuation.clone(),
                        arg,
                    })),
                )))
            }
            RuntimeEvidenceValue::Thunk(_) => match self.force_thunk_result(callee)? {
                EvidenceEvalResult::Value(callee) => self.apply_value_result(site, callee, arg),
                EvidenceEvalResult::Request(request) => Ok(EvidenceEvalResult::Request(
                    request.append_continuation(EvidenceContinuation::apply_forced_callee(
                        site,
                        arg,
                        EvidenceContinuation::identity(),
                    )),
                )),
            },
            RuntimeEvidenceValue::EffectOp { expr, path } => {
                let route = site
                    .and_then(|site| self.evidence.effect_call_route(site, *expr))
                    .unwrap_or(EvidenceEffectRoute::Unhandled);
                Ok(EvidenceEvalResult::Value(shared(
                    RuntimeEvidenceValue::Thunk(Rc::new(RuntimeEvidenceThunk::Effect {
                        path: path.clone(),
                        payload: arg,
                        route,
                    })),
                )))
            }
            value => Err(RuntimeEvidenceRunError::NotFunction(format_value(value))),
        }
    }

    fn apply_adapter_result(
        &mut self,
        source: &Type,
        target: &Type,
        function: SharedValue,
        arg: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let (source_arg, source_ret) = function_parts(source).ok_or(
            RuntimeEvidenceRunError::UnsupportedExpr("function adapter source type"),
        )?;
        let (target_arg, target_ret) = function_parts(target).ok_or(
            RuntimeEvidenceRunError::UnsupportedExpr("function adapter target type"),
        )?;
        let source_arg = source_arg.clone();
        let source_ret = source_ret.clone();
        let target_arg = target_arg.clone();
        let target_ret = target_ret.clone();
        let result = self.adapt_value_result(arg, &target_arg, &source_arg)?;
        self.continue_result(
            result,
            EvidenceContinuation::apply_adapter_arg(
                function,
                source_ret,
                target_ret,
                EvidenceContinuation::identity(),
            ),
        )
    }

    fn adapt_value_result(
        &mut self,
        value: SharedValue,
        source: &Type,
        target: &Type,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if equivalent_runtime_types(source, target) || matches!(target, Type::Any) {
            return Ok(EvidenceEvalResult::Value(value));
        }
        if matches!(source, Type::Never) {
            return Ok(EvidenceEvalResult::Value(value));
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
            ) => Ok(EvidenceEvalResult::Value(shared(
                RuntimeEvidenceValue::Thunk(Rc::new(RuntimeEvidenceThunk::Adapter {
                    source: source_value.as_ref().clone(),
                    target: target_value.as_ref().clone(),
                    thunk: value,
                })),
            ))),
            (
                Type::Thunk {
                    value: source_value,
                    ..
                },
                target,
            ) => {
                let result = self.force_thunk_result(value)?;
                self.continue_result(
                    result,
                    EvidenceContinuation::adapt_value(
                        source_value.as_ref().clone(),
                        target.clone(),
                        EvidenceContinuation::identity(),
                    ),
                )
            }
            (
                source,
                Type::Thunk {
                    value: target_value,
                    ..
                },
            ) => {
                let result = self.adapt_value_result(value, source, target_value)?;
                self.continue_result(
                    result,
                    EvidenceContinuation::wrap_thunk_value(EvidenceContinuation::identity()),
                )
            }
            (Type::Fun { .. }, Type::Fun { .. }) => Ok(EvidenceEvalResult::Value(shared(
                RuntimeEvidenceValue::FunctionAdapter {
                    source: source.clone(),
                    target: target.clone(),
                    function: value,
                },
            ))),
            (Type::Record(_), Type::Record(_)) if value_boundary_supported(source, target) => {
                Ok(EvidenceEvalResult::Value(value))
            }
            _ => Err(RuntimeEvidenceRunError::UnsupportedExpr("runtime boundary")),
        }
    }

    fn resume_continuation(
        &mut self,
        continuation: EvidenceContinuation,
        value: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match continuation.0.as_ref() {
            EvidenceContinuationFrame::Identity => Ok(EvidenceEvalResult::Value(value)),
            EvidenceContinuationFrame::ForceThunk {
                target_value_is_thunk,
                next,
            } => {
                let result = self.force_thunk_result(value)?;
                if *target_value_is_thunk {
                    self.continue_result(result, next.clone())
                } else {
                    self.continue_result(
                        result,
                        EvidenceContinuation::force_value_if_thunk(next.clone()),
                    )
                }
            }
            EvidenceContinuationFrame::ForceValueIfThunk { next } => {
                let result = self.force_value_if_thunk_result(value)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::ApplyCallee {
                site,
                arg,
                env,
                next,
            } => {
                let mut env = env.clone();
                let result = self.eval_apply_arg_result(*site, value, *arg, &mut env)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::ApplyArg { site, callee, next } => {
                let result = self.apply_value_result(*site, callee.clone(), value)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::ApplyForcedCallee { site, arg, next } => {
                let result = self.apply_value_result(*site, value, arg.clone())?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::AdaptValue {
                source,
                target,
                next,
            } => {
                let result = self.adapt_value_result(value, source, target)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::WrapThunkValue { next } => self.continue_result(
                EvidenceEvalResult::Value(shared(RuntimeEvidenceValue::Thunk(Rc::new(
                    RuntimeEvidenceThunk::Value(value),
                )))),
                next.clone(),
            ),
            EvidenceContinuationFrame::ApplyAdapterArg {
                function,
                source_ret,
                target_ret,
                next,
            } => {
                let result = self.apply_value_result(None, function.clone(), value)?;
                self.continue_result(
                    result,
                    EvidenceContinuation::apply_adapter_result(
                        source_ret.clone(),
                        target_ret.clone(),
                        next.clone(),
                    ),
                )
            }
            EvidenceContinuationFrame::ApplyAdapterResult {
                source_ret,
                target_ret,
                next,
            } => {
                let result = self.adapt_value_result(value, source_ret, target_ret)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::CaseScrutinee { arms, env, next } => {
                let result = self.eval_case_scrutinee_result(value, arms, env)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::CatchBody {
                catch_expr,
                arms,
                env,
                next,
            } => {
                let result = self.continue_catch_body_result(
                    *catch_expr,
                    arms,
                    env,
                    EvidenceEvalResult::Value(value),
                )?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::MarkerFrame { next, .. } => {
                self.continue_result(EvidenceEvalResult::Value(value), next.clone())
            }
            EvidenceContinuationFrame::TupleItems {
                values,
                rest,
                env,
                next,
            } => {
                let mut values = values.clone();
                values.push(value);
                let mut env = env.clone();
                let result = self.eval_tuple_items_result(values, rest, &mut env)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::RecordSpread { fields, env, next } => {
                let values = record_fields(value.as_ref())?;
                let mut env = env.clone();
                let result = self.eval_record_fields_result(values, fields, &mut env)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::RecordFields {
                values,
                rest,
                env,
                next,
            } => {
                let mut values = values.clone();
                let Some((field, remaining)) = rest.split_first() else {
                    return Err(RuntimeEvidenceRunError::UnsupportedExpr(
                        "empty record field continuation",
                    ));
                };
                values.push(RuntimeEvidenceValueField {
                    name: field.name.clone(),
                    value,
                });
                let mut env = env.clone();
                let result = self.eval_record_fields_result(values, remaining, &mut env)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::PolyVariantPayloads {
                tag,
                values,
                rest,
                env,
                next,
            } => {
                let mut values = values.clone();
                values.push(value);
                let mut env = env.clone();
                let result =
                    self.eval_poly_variant_payloads_result(tag.clone(), values, rest, &mut env)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::SelectBase {
                name,
                resolution,
                next,
            } => {
                let result = self.apply_select_base_result(value, name, resolution)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::BlockStmt {
                resume,
                rest,
                tail,
                env,
                last,
                next,
            } => {
                let mut env = env.clone();
                let last = match resume {
                    EvidenceBlockResume::Let(pat) => {
                        let value = recursive_let_value(pat, value);
                        bind_pat(pat, value, &mut env)?;
                        last.clone()
                    }
                    EvidenceBlockResume::Expr => value,
                };
                let result = self.eval_block_parts_result(rest, *tail, &mut env, last)?;
                self.continue_result(result, next.clone())
            }
        }
    }

    fn continue_result(
        &mut self,
        result: EvidenceEvalResult,
        continuation: EvidenceContinuation,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match result {
            EvidenceEvalResult::Value(value) => self.resume_continuation(continuation, value),
            EvidenceEvalResult::Request(request) => {
                self.continue_request_with_continuation(request, continuation)
            }
        }
    }

    fn continue_request_with_continuation(
        &mut self,
        request: EvidenceRequest,
        continuation: EvidenceContinuation,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let (request, next) = match continuation.0.as_ref() {
            EvidenceContinuationFrame::Identity => {
                return Ok(EvidenceEvalResult::Request(request));
            }
            EvidenceContinuationFrame::ForceThunk {
                target_value_is_thunk,
                next,
            } => (
                request.append_continuation(EvidenceContinuation::force_thunk(
                    *target_value_is_thunk,
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::ForceValueIfThunk { next } => (
                request.append_continuation(EvidenceContinuation::force_value_if_thunk(
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::ApplyCallee {
                site,
                arg,
                env,
                next,
            } => (
                request.append_continuation(EvidenceContinuation::apply_callee(
                    *site,
                    *arg,
                    env.clone(),
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::ApplyArg { site, callee, next } => (
                request.append_continuation(EvidenceContinuation::apply_arg(
                    *site,
                    callee.clone(),
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::ApplyForcedCallee { site, arg, next } => (
                request.append_continuation(EvidenceContinuation::apply_forced_callee(
                    *site,
                    arg.clone(),
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::AdaptValue {
                source,
                target,
                next,
            } => (
                request.append_continuation(EvidenceContinuation::adapt_value(
                    source.clone(),
                    target.clone(),
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::WrapThunkValue { next } => (
                request.append_continuation(EvidenceContinuation::wrap_thunk_value(
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::ApplyAdapterArg {
                function,
                source_ret,
                target_ret,
                next,
            } => (
                request.append_continuation(EvidenceContinuation::apply_adapter_arg(
                    function.clone(),
                    source_ret.clone(),
                    target_ret.clone(),
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::ApplyAdapterResult {
                source_ret,
                target_ret,
                next,
            } => (
                request.append_continuation(EvidenceContinuation::apply_adapter_result(
                    source_ret.clone(),
                    target_ret.clone(),
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::CaseScrutinee { arms, env, next } => (
                request.append_continuation(EvidenceContinuation::case_scrutinee(
                    arms.clone(),
                    env.clone(),
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::CatchBody {
                catch_expr,
                arms,
                env,
                next,
            } => {
                let result = self.continue_catch_body_result(
                    *catch_expr,
                    arms,
                    env,
                    EvidenceEvalResult::Request(request),
                )?;
                return self.continue_result(result, next.clone());
            }
            EvidenceContinuationFrame::MarkerFrame { path, next } => (
                request.with_visible_marker(path).append_continuation(
                    EvidenceContinuation::marker_frame(
                        path.clone(),
                        EvidenceContinuation::identity(),
                    ),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::TupleItems {
                values,
                rest,
                env,
                next,
            } => (
                request.append_continuation(EvidenceContinuation::tuple_items(
                    values.clone(),
                    rest.clone(),
                    env.clone(),
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::RecordSpread { fields, env, next } => (
                request.append_continuation(EvidenceContinuation::record_spread(
                    fields.clone(),
                    env.clone(),
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::RecordFields {
                values,
                rest,
                env,
                next,
            } => (
                request.append_continuation(EvidenceContinuation::record_fields(
                    values.clone(),
                    rest.clone(),
                    env.clone(),
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::PolyVariantPayloads {
                tag,
                values,
                rest,
                env,
                next,
            } => (
                request.append_continuation(EvidenceContinuation::poly_variant_payloads(
                    tag.clone(),
                    values.clone(),
                    rest.clone(),
                    env.clone(),
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::SelectBase {
                name,
                resolution,
                next,
            } => (
                request.append_continuation(EvidenceContinuation::select_base(
                    name.clone(),
                    resolution.clone(),
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
            EvidenceContinuationFrame::BlockStmt {
                resume,
                rest,
                tail,
                env,
                last,
                next,
            } => (
                request.append_continuation(EvidenceContinuation::block_stmt(
                    resume.clone(),
                    rest.clone(),
                    *tail,
                    env.clone(),
                    last.clone(),
                    EvidenceContinuation::identity(),
                )),
                next.clone(),
            ),
        };
        self.continue_request_with_continuation(request, next)
    }

    fn finish_force_thunk_result(
        &mut self,
        result: EvidenceEvalResult,
        target_value_is_thunk: bool,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if target_value_is_thunk {
            Ok(result)
        } else {
            self.continue_result(
                result,
                EvidenceContinuation::force_value_if_thunk(EvidenceContinuation::identity()),
            )
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
                    visible_markers: Vec::new(),
                    continuation: EvidenceContinuation::identity(),
                })),
                RuntimeEvidenceThunk::Continuation { continuation, arg } => {
                    let result = self.resume_continuation(continuation.clone(), arg.clone())?;
                    self.continue_result(
                        result,
                        EvidenceContinuation::force_value_if_thunk(EvidenceContinuation::identity()),
                    )
                }
                RuntimeEvidenceThunk::Value(value) => Ok(EvidenceEvalResult::Value(value.clone())),
                RuntimeEvidenceThunk::Adapter {
                    source,
                    target,
                    thunk,
                } => {
                    let result = self.force_thunk_result(thunk.clone())?;
                    self.continue_result(
                        result,
                        EvidenceContinuation::adapt_value(
                            source.clone(),
                            target.clone(),
                            EvidenceContinuation::identity(),
                        ),
                    )
                }
            },
            value => Err(RuntimeEvidenceRunError::NotThunk(format_value(value))),
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
        let result = self.eval_expr_result(body, &mut body_env)?;
        self.continue_catch_body_result(catch_expr, arms, env, result)
    }

    fn continue_catch_body_result(
        &mut self,
        catch_expr: ExprId,
        arms: &[control_vm::CatchArm],
        env: &Env,
        result: EvidenceEvalResult,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match result {
            EvidenceEvalResult::Value(value) => self.eval_value_arm(value, arms, env),
            EvidenceEvalResult::Request(request) => match request.route {
                EvidenceEffectRoute::Direct {
                    handler,
                    resumptive,
                } if handler == catch_expr => {
                    self.eval_operation_arm(request, resumptive, arms, env)
                }
                EvidenceEffectRoute::Direct { .. } => Ok(EvidenceEvalResult::Request(
                    self.defer_catch_body(catch_expr, arms, env, request),
                )),
                EvidenceEffectRoute::Unhandled => {
                    if let Some(resumptive) = visible_operation_resumptive(&request, arms) {
                        self.eval_operation_arm(request, resumptive, arms, env)
                    } else {
                        Ok(EvidenceEvalResult::Request(
                            self.defer_catch_body(catch_expr, arms, env, request),
                        ))
                    }
                }
            },
        }
    }

    fn defer_catch_body(
        &mut self,
        catch_expr: ExprId,
        arms: &[control_vm::CatchArm],
        env: &Env,
        request: EvidenceRequest,
    ) -> EvidenceRequest {
        request.append_continuation(EvidenceContinuation::catch_body(
            catch_expr,
            arms.to_vec(),
            env.clone(),
            EvidenceContinuation::identity(),
        ))
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
        self.eval_expr_result(arm.body, &mut arm_env)
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

    fn eval_case_result(
        &mut self,
        scrutinee: SharedValue,
        arms: &[control_vm::CaseArm],
        env: &Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
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
            return self.eval_expr_result(arm.body, &mut arm_env);
        }
        Err(RuntimeEvidenceRunError::PatternMismatch)
    }

    fn eval_case_scrutinee_result(
        &mut self,
        scrutinee: SharedValue,
        arms: &[control_vm::CaseArm],
        env: &Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match self.force_value_if_thunk_result(scrutinee)? {
            EvidenceEvalResult::Value(scrutinee) => self.eval_case_result(scrutinee, arms, env),
            EvidenceEvalResult::Request(request) => Ok(EvidenceEvalResult::Request(
                request.append_continuation(EvidenceContinuation::case_scrutinee(
                    arms.to_vec(),
                    env.clone(),
                    EvidenceContinuation::identity(),
                )),
            )),
        }
    }

    fn eval_block_result(
        &mut self,
        block: &Block,
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        self.eval_block_parts_result(
            &block.stmts,
            block.tail,
            env,
            shared(RuntimeEvidenceValue::Unit),
        )
    }

    fn eval_block_parts_result(
        &mut self,
        stmts: &[Stmt],
        tail: Option<ExprId>,
        env: &mut Env,
        mut last: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        for (index, stmt) in stmts.iter().enumerate() {
            let rest = &stmts[index + 1..];
            match stmt {
                Stmt::Let(_, pat, expr) => match self.eval_expr_result(*expr, env)? {
                    EvidenceEvalResult::Value(value) => {
                        let value = recursive_let_value(pat, value);
                        bind_pat(pat, value, env)?;
                    }
                    EvidenceEvalResult::Request(request) => {
                        return Ok(EvidenceEvalResult::Request(request.append_continuation(
                            EvidenceContinuation::block_stmt(
                                EvidenceBlockResume::Let(pat.clone()),
                                rest.to_vec(),
                                tail,
                                env.clone(),
                                last,
                                EvidenceContinuation::identity(),
                            ),
                        )));
                    }
                },
                Stmt::Expr(expr) => match self.eval_expr_result(*expr, env)? {
                    EvidenceEvalResult::Value(value) => last = value,
                    EvidenceEvalResult::Request(request) => {
                        return Ok(EvidenceEvalResult::Request(request.append_continuation(
                            EvidenceContinuation::block_stmt(
                                EvidenceBlockResume::Expr,
                                rest.to_vec(),
                                tail,
                                env.clone(),
                                last,
                                EvidenceContinuation::identity(),
                            ),
                        )));
                    }
                },
                Stmt::Module(_, module_stmts) => {
                    let module_block = Block {
                        stmts: module_stmts.clone(),
                        tail: None,
                    };
                    match self.eval_block_result(&module_block, env)? {
                        EvidenceEvalResult::Value(value) => last = value,
                        EvidenceEvalResult::Request(request) => {
                            return Ok(EvidenceEvalResult::Request(request.append_continuation(
                                EvidenceContinuation::block_stmt(
                                    EvidenceBlockResume::Expr,
                                    rest.to_vec(),
                                    tail,
                                    env.clone(),
                                    last,
                                    EvidenceContinuation::identity(),
                                ),
                            )));
                        }
                    }
                }
            }
        }
        if let Some(tail) = tail {
            self.eval_expr_result(tail, env)
        } else {
            Ok(EvidenceEvalResult::Value(last))
        }
    }

    fn apply_primitive(
        &mut self,
        op: PrimitiveOp,
        context: &PrimitiveContext,
        args: &[SharedValue],
    ) -> Result<SharedValue, RuntimeEvidenceRunError> {
        use PrimitiveOp::*;
        let value = match op {
            BoolNot => RuntimeEvidenceValue::Bool(!expect_bool(&args[0])?),
            BoolEq => RuntimeEvidenceValue::Bool(expect_bool(&args[0])? == expect_bool(&args[1])?),
            ListEmpty => RuntimeEvidenceValue::List(Vec::new()),
            ListSingleton => RuntimeEvidenceValue::List(vec![args[0].clone()]),
            ListLen => RuntimeEvidenceValue::Int(expect_list(&args[0])?.len() as i64),
            ListMerge => {
                let mut values = expect_list(&args[0])?.to_vec();
                values.extend(expect_list(&args[1])?.iter().cloned());
                RuntimeEvidenceValue::List(values)
            }
            ListViewRaw => apply_list_view_raw(context, &args[0])?,
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

fn recursive_let_value(pat: &Pat, value: SharedValue) -> SharedValue {
    match (pat, value.as_ref()) {
        (Pat::Var(def), RuntimeEvidenceValue::Closure(closure)) => {
            shared(RuntimeEvidenceValue::RecursiveClosure {
                def: *def,
                closure: closure.clone(),
            })
        }
        _ => value,
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

fn expect_list(value: &SharedValue) -> Result<&[SharedValue], RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::List(values) => Ok(values),
        _ => Err(RuntimeEvidenceRunError::UnsupportedExpr(
            "non-list primitive argument",
        )),
    }
}

fn apply_list_view_raw(
    context: &PrimitiveContext,
    value: &SharedValue,
) -> Result<RuntimeEvidenceValue, RuntimeEvidenceRunError> {
    let constructors = context
        .list_view
        .ok_or(RuntimeEvidenceRunError::UnsupportedExpr(
            "missing list_view primitive context",
        ))?;
    let values = expect_list(value)?;
    match values {
        [] => Ok(RuntimeEvidenceValue::DataConstructor {
            def: DefId(constructors.empty.0),
            payloads: Vec::new(),
        }),
        [value] => Ok(RuntimeEvidenceValue::DataConstructor {
            def: DefId(constructors.leaf.0),
            payloads: vec![value.clone()],
        }),
        values => {
            let split = values.len() / 2;
            let left = shared(RuntimeEvidenceValue::List(values[..split].to_vec()));
            let right = shared(RuntimeEvidenceValue::List(values[split..].to_vec()));
            Ok(RuntimeEvidenceValue::DataConstructor {
                def: DefId(constructors.node.0),
                payloads: vec![left, right],
            })
        }
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
        RuntimeEvidenceValue::DataConstructor { payloads, .. } if payloads.len() == 1 => {
            record_fields(payloads[0].as_ref())
        }
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

fn visible_operation_resumptive(
    request: &EvidenceRequest,
    arms: &[control_vm::CatchArm],
) -> Option<bool> {
    arms.iter().find_map(|arm| {
        let operation_path = arm.operation_path.as_ref()?;
        request
            .is_visible_to(operation_path)
            .then_some(arm.continuation.is_some())
    })
}

fn function_adapter_hygiene_is_empty(hygiene: &FunctionAdapterHygiene) -> bool {
    hygiene.markers.is_empty() && hygiene.arg_markers.is_empty() && hygiene.ret_markers.is_empty()
}

fn function_parts(ty: &Type) -> Option<(&Type, &Type)> {
    let Type::Fun { arg, ret, .. } = ty else {
        return None;
    };
    Some((arg, ret))
}

fn equivalent_runtime_types(source: &Type, target: &Type) -> bool {
    if source == target || source.is_pure_effect() && target.is_pure_effect() {
        return true;
    }
    match (source, target) {
        (Type::EffectRow(items), target) if items.len() == 1 => {
            equivalent_runtime_types(&items[0], target)
        }
        (source, Type::EffectRow(items)) if items.len() == 1 => {
            equivalent_runtime_types(source, &items[0])
        }
        (source, Type::Thunk { effect, value }) if effect.is_pure_effect() => {
            equivalent_runtime_types(source, value)
        }
        (Type::Thunk { effect, value }, target) if effect.is_pure_effect() => {
            equivalent_runtime_types(value, target)
        }
        (Type::Record(source_fields), Type::Record(target_fields)) => {
            target_fields.iter().all(|target| {
                record_field_type(source_fields, &target.name).map_or(target.optional, |source| {
                    equivalent_runtime_types(&source.value, &target.value)
                })
            })
        }
        (Type::EffectRow(source_items), Type::EffectRow(target_items)) => {
            equivalent_effect_rows(source_items, target_items)
        }
        (Type::PolyVariant(source_variants), Type::PolyVariant(target_variants)) => {
            source_variants.iter().all(|source| {
                target_variants
                    .iter()
                    .find(|target| {
                        target.name == source.name && target.payloads.len() == source.payloads.len()
                    })
                    .is_some_and(|target| {
                        source
                            .payloads
                            .iter()
                            .zip(&target.payloads)
                            .all(|(source, target)| equivalent_runtime_types(source, target))
                    })
            })
        }
        (source, Type::Union(left, right)) => {
            equivalent_runtime_types(source, left) || equivalent_runtime_types(source, right)
        }
        (Type::Union(left, right), target) => {
            equivalent_runtime_types(left, target) && equivalent_runtime_types(right, target)
        }
        (source, Type::Intersection(left, right)) => {
            equivalent_runtime_types(source, left) && equivalent_runtime_types(source, right)
        }
        (Type::Intersection(left, right), target) => {
            equivalent_runtime_types(left, target) || equivalent_runtime_types(right, target)
        }
        _ => false,
    }
}

fn equivalent_effect_rows(source_items: &[Type], target_items: &[Type]) -> bool {
    if source_items.len() != target_items.len() {
        return false;
    }
    let mut used = vec![false; target_items.len()];
    source_items.iter().all(|source| {
        let Some(index) = target_items.iter().enumerate().find_map(|(index, target)| {
            (!used[index] && equivalent_effect_items(source, target)).then_some(index)
        }) else {
            return false;
        };
        used[index] = true;
        true
    })
}

fn equivalent_effect_items(source: &Type, target: &Type) -> bool {
    match (source, target) {
        (
            Type::Con {
                path: source_path,
                args: source_args,
            },
            Type::Con {
                path: target_path,
                args: target_args,
            },
        ) if source_path == target_path && source_args.len() == target_args.len() => source_args
            .iter()
            .zip(target_args)
            .all(|(source, target)| equivalent_runtime_types(source, target)),
        _ => equivalent_runtime_types(source, target),
    }
}

fn record_field_type<'a>(
    fields: &'a [specialize::mono::TypeField],
    name: &str,
) -> Option<&'a specialize::mono::TypeField> {
    fields.iter().find(|field| field.name == name)
}

fn value_boundary_supported(source: &Type, target: &Type) -> bool {
    if equivalent_runtime_types(source, target) || matches!(target, Type::Any) {
        return true;
    }
    if matches!(source, Type::Never) {
        return true;
    }
    match (source, target) {
        (Type::Fun { .. }, Type::Fun { .. }) => function_boundary_supported(source, target),
        (Type::Thunk { value: source, .. }, Type::Thunk { value: target, .. }) => {
            value_boundary_supported(source, target)
        }
        (Type::Thunk { value: source, .. }, target) => value_boundary_supported(source, target),
        (source, Type::Thunk { value: target, .. }) => value_boundary_supported(source, target),
        (Type::Record(source_fields), Type::Record(target_fields)) => {
            record_value_boundary_supported(source_fields, target_fields)
        }
        _ => false,
    }
}

fn function_boundary_supported(source: &Type, target: &Type) -> bool {
    let Some((source_arg, source_ret)) = function_parts(source) else {
        return false;
    };
    let Some((target_arg, target_ret)) = function_parts(target) else {
        return false;
    };
    value_boundary_supported(target_arg, source_arg)
        && value_boundary_supported(source_ret, target_ret)
}

fn record_value_boundary_supported(
    source_fields: &[specialize::mono::TypeField],
    target_fields: &[specialize::mono::TypeField],
) -> bool {
    target_fields.iter().all(|target| {
        record_field_type(source_fields, &target.name)
            .map(|source| value_boundary_supported(&source.value, &target.value))
            .unwrap_or(target.optional)
    })
}

fn path_is_prefix(prefix: &[String], path: &[String]) -> bool {
    prefix.len() <= path.len() && prefix.iter().zip(path).all(|(left, right)| left == right)
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
        RuntimeEvidenceValue::List(values) => format_delimited("[", "]", values),
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
        RuntimeEvidenceValue::FunctionAdapter { .. } => "<function-adapter>".to_string(),
        RuntimeEvidenceValue::Closure(_) | RuntimeEvidenceValue::RecursiveClosure { .. } => {
            "<function>".to_string()
        }
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
