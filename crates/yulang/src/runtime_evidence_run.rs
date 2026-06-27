use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use control_vm::{
    Block, ControlEffectEvidence, ControlEffectUseKind, ControlEvidenceProgram,
    ControlEvidenceRoute, DefId, Expr, ExprId, InstanceId, Pat, Program, RecordSpread, Root,
    SelectResolution, Stmt,
};
use specialize::mono::{Lit, PrimitiveContext, PrimitiveOp, Type};

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
    Continuation {
        continuation: EvidenceContinuation,
        arg: SharedValue,
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
    CaseScrutinee {
        arms: Vec<control_vm::CaseArm>,
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

    fn case_scrutinee(arms: Vec<control_vm::CaseArm>, env: Env, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::CaseScrutinee {
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
            EvidenceContinuationFrame::CaseScrutinee { arms, env, next } => {
                Self::case_scrutinee(arms.clone(), env.clone(), next.clone().then(tail))
            }
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

    fn attach_to_request(self, request: EvidenceRequest) -> EvidenceRequest {
        let request = self.mark_visible_request(request);
        request.map_continuation(|inner| inner.then(self))
    }

    fn mark_visible_request(&self, mut request: EvidenceRequest) -> EvidenceRequest {
        self.mark_visible_request_in_place(&mut request);
        request
    }

    fn mark_visible_request_in_place(&self, request: &mut EvidenceRequest) {
        match self.0.as_ref() {
            EvidenceContinuationFrame::Identity => {}
            EvidenceContinuationFrame::ForceThunk { next, .. }
            | EvidenceContinuationFrame::ForceValueIfThunk { next }
            | EvidenceContinuationFrame::ApplyCallee { next, .. }
            | EvidenceContinuationFrame::ApplyArg { next, .. }
            | EvidenceContinuationFrame::ApplyForcedCallee { next, .. }
            | EvidenceContinuationFrame::CaseScrutinee { next, .. }
            | EvidenceContinuationFrame::TupleItems { next, .. }
            | EvidenceContinuationFrame::RecordSpread { next, .. }
            | EvidenceContinuationFrame::RecordFields { next, .. }
            | EvidenceContinuationFrame::PolyVariantPayloads { next, .. }
            | EvidenceContinuationFrame::SelectBase { next, .. }
            | EvidenceContinuationFrame::BlockStmt { next, .. } => {
                next.mark_visible_request_in_place(request);
            }
            EvidenceContinuationFrame::MarkerFrame { path, next } => {
                request.add_visible_marker(path);
                next.mark_visible_request_in_place(request);
            }
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
                        request.map_continuation(|continuation| {
                            EvidenceContinuation::force_thunk(target_value_is_thunk, continuation)
                        }),
                    )),
                };
            }
            Expr::FunctionAdapter { function, .. } => return self.eval_expr_result(*function, env),
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
                        request.map_continuation(|continuation| {
                            EvidenceContinuation::case_scrutinee(
                                arms.clone(),
                                env.clone(),
                                continuation,
                            )
                        }),
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
            return self.apply_primitive(op, &[]);
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
                request.map_continuation(|continuation| {
                    EvidenceContinuation::apply_callee(site, arg_expr, env.clone(), continuation)
                }),
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
                Ok(EvidenceEvalResult::Request(request.map_continuation(
                    |continuation| EvidenceContinuation::apply_arg(site, callee, continuation),
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
                    return Ok(EvidenceEvalResult::Request(request.map_continuation(
                        |continuation| {
                            EvidenceContinuation::tuple_items(
                                values,
                                rest,
                                env.clone(),
                                continuation,
                            )
                        },
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
                    return Ok(EvidenceEvalResult::Request(request.map_continuation(
                        |continuation| {
                            EvidenceContinuation::record_spread(
                                fields.to_vec(),
                                env.clone(),
                                continuation,
                            )
                        },
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
                    return Ok(EvidenceEvalResult::Request(request.map_continuation(
                        |continuation| {
                            EvidenceContinuation::record_fields(
                                values,
                                rest,
                                env.clone(),
                                continuation,
                            )
                        },
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
                    return Ok(EvidenceEvalResult::Request(request.map_continuation(
                        |continuation| {
                            EvidenceContinuation::poly_variant_payloads(
                                tag,
                                values,
                                rest,
                                env.clone(),
                                continuation,
                            )
                        },
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
                request.map_continuation(|continuation| {
                    EvidenceContinuation::select_base(
                        name.to_string(),
                        resolution.clone(),
                        continuation,
                    )
                }),
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
                self.apply_primitive(*op, &args)
                    .map(EvidenceEvalResult::Value)
            }
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
                    request.map_continuation(|continuation| {
                        EvidenceContinuation::apply_forced_callee(site, arg, continuation)
                    }),
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
            EvidenceContinuationFrame::CaseScrutinee { arms, env, next } => {
                let result = self.eval_case_scrutinee_result(value, arms, env)?;
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
            EvidenceEvalResult::Request(request) => Ok(EvidenceEvalResult::Request(
                continuation.attach_to_request(request),
            )),
        }
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
        match self.eval_expr_result(body, &mut body_env)? {
            EvidenceEvalResult::Value(value) => self.eval_value_arm(value, arms, env),
            EvidenceEvalResult::Request(request) => match request.route {
                EvidenceEffectRoute::Direct {
                    handler,
                    resumptive,
                } if handler == catch_expr => {
                    self.eval_operation_arm(request, resumptive, arms, env)
                }
                EvidenceEffectRoute::Direct { .. } => Ok(EvidenceEvalResult::Request(request)),
                EvidenceEffectRoute::Unhandled => {
                    if let Some(resumptive) = visible_operation_resumptive(&request, arms) {
                        self.eval_operation_arm(request, resumptive, arms, env)
                    } else {
                        Ok(EvidenceEvalResult::Request(request))
                    }
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
                request.map_continuation(|continuation| {
                    EvidenceContinuation::case_scrutinee(arms.to_vec(), env.clone(), continuation)
                }),
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
                    EvidenceEvalResult::Value(value) => bind_pat(pat, value, env)?,
                    EvidenceEvalResult::Request(request) => {
                        return Ok(EvidenceEvalResult::Request(request.map_continuation(
                            |continuation| {
                                EvidenceContinuation::block_stmt(
                                    EvidenceBlockResume::Let(pat.clone()),
                                    rest.to_vec(),
                                    tail,
                                    env.clone(),
                                    last,
                                    continuation,
                                )
                            },
                        )));
                    }
                },
                Stmt::Expr(expr) => match self.eval_expr_result(*expr, env)? {
                    EvidenceEvalResult::Value(value) => last = value,
                    EvidenceEvalResult::Request(request) => {
                        return Ok(EvidenceEvalResult::Request(request.map_continuation(
                            |continuation| {
                                EvidenceContinuation::block_stmt(
                                    EvidenceBlockResume::Expr,
                                    rest.to_vec(),
                                    tail,
                                    env.clone(),
                                    last,
                                    continuation,
                                )
                            },
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
                            return Ok(EvidenceEvalResult::Request(request.map_continuation(
                                |continuation| {
                                    EvidenceContinuation::block_stmt(
                                        EvidenceBlockResume::Expr,
                                        rest.to_vec(),
                                        tail,
                                        env.clone(),
                                        last,
                                        continuation,
                                    )
                                },
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

fn expect_list(value: &SharedValue) -> Result<&[SharedValue], RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::List(values) => Ok(values),
        _ => Err(RuntimeEvidenceRunError::UnsupportedExpr(
            "non-list primitive argument",
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
