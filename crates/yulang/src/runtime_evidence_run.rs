use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use control_vm::{
    Block, ControlEffectEvidence, ControlEffectUseKind, ControlEvidenceProgram,
    ControlEvidenceRoute, DefId, Expr, ExprId, InstanceId, Pat, Program, RecordSpread, Root,
    SelectResolution, Stmt,
};
use specialize::mono::{
    FunctionAdapterHygiene, GuardMarker, Lit, PrimitiveContext, PrimitiveOp, RangeConstructors,
    Type,
};
use unicode_segmentation::UnicodeSegmentation;

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
    pub expr_evals: usize,
    pub env_clones: usize,
    pub env_entries_cloned: usize,
    pub apply_value_calls: usize,
    pub apply_adapter_calls: usize,
    pub adapt_value_calls: usize,
    pub primitive_apply_calls: usize,
    pub thunk_forces: usize,
    pub thunk_force_expr: usize,
    pub thunk_force_effect: usize,
    pub thunk_force_continuation: usize,
    pub thunk_force_value: usize,
    pub thunk_force_adapter: usize,
    pub continuation_appends: usize,
    pub continuation_append_steps: usize,
    pub continuation_resume_steps: usize,
    pub request_continuation_steps: usize,
    pub catch_body_checks: usize,
    pub list_merge_calls: usize,
    pub list_view_raw_calls: usize,
    pub list_values_copied: usize,
}

#[derive(Debug, Clone, PartialEq)]
enum RuntimeEvidenceValue {
    Int(i64),
    BigInt(String),
    Float(f64),
    Str(String),
    Bytes(Vec<u8>),
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
        hygiene: FunctionAdapterHygiene,
    },
    Marked {
        value: SharedValue,
        markers: Vec<Vec<String>>,
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
    Then {
        first: EvidenceContinuation,
        second: EvidenceContinuation,
    },
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
        ret_markers: Vec<Vec<String>>,
        source_ret: Type,
        target_ret: Type,
        next: EvidenceContinuation,
    },
    ApplyAdapterResult {
        ret_markers: Vec<Vec<String>>,
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
    RefSetReference {
        value: ExprId,
        env: Env,
        next: EvidenceContinuation,
    },
    RefSetForcedReference {
        value: ExprId,
        env: Env,
        next: EvidenceContinuation,
    },
    RefSetValue {
        reference: SharedValue,
        next: EvidenceContinuation,
    },
    RefSetForcedValue {
        reference: SharedValue,
        next: EvidenceContinuation,
    },
    RefSetResolvedUnit {
        next: EvidenceContinuation,
    },
    RefSetHandleResult {
        assigned: SharedValue,
        next: EvidenceContinuation,
    },
    RefSetHandleValueResult {
        assigned: SharedValue,
        next: EvidenceContinuation,
    },
    RefSetEmitResolvedRequest {
        request: EvidenceRequest,
        assigned: SharedValue,
        mode: EvidenceRefSetResumeMode,
        next: EvidenceContinuation,
    },
    ResolveRefSetValues {
        values: Vec<SharedValue>,
        assigned: SharedValue,
        out: Vec<SharedValue>,
        index: usize,
        finish: EvidenceRefSetFinish,
        next: EvidenceContinuation,
    },
    ResolveRefSetFields {
        fields: Vec<RuntimeEvidenceValueField>,
        assigned: SharedValue,
        out: Vec<RuntimeEvidenceValueField>,
        index: usize,
        next: EvidenceContinuation,
    },
}

#[derive(Debug, Clone, PartialEq)]
enum EvidenceBlockResume {
    Let(Pat),
    Expr,
}

#[derive(Debug, Clone, PartialEq)]
enum EvidenceRefSetFinish {
    Tuple,
    List,
    PolyVariant { tag: String },
    DataConstructor { def: DefId },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceRefSetResumeMode {
    Result,
    ValueResult,
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

fn clone_env_for_stats(env: &Env, stats: &mut RuntimeEvidenceRunStats) -> Env {
    stats.env_clones += 1;
    stats.env_entries_cloned += env.len();
    env.clone()
}

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
        ret_markers: Vec<Vec<String>>,
        source_ret: Type,
        target_ret: Type,
        next: Self,
    ) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::ApplyAdapterArg {
            function,
            ret_markers,
            source_ret,
            target_ret,
            next,
        }))
    }

    fn apply_adapter_result(
        ret_markers: Vec<Vec<String>>,
        source_ret: Type,
        target_ret: Type,
        next: Self,
    ) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::ApplyAdapterResult {
            ret_markers,
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

    fn ref_set_reference(value: ExprId, env: Env, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::RefSetReference {
            value,
            env,
            next,
        }))
    }

    fn ref_set_forced_reference(value: ExprId, env: Env, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::RefSetForcedReference {
            value,
            env,
            next,
        }))
    }

    fn ref_set_value(reference: SharedValue, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::RefSetValue {
            reference,
            next,
        }))
    }

    fn ref_set_forced_value(reference: SharedValue, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::RefSetForcedValue {
            reference,
            next,
        }))
    }

    fn ref_set_resolved_unit(next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::RefSetResolvedUnit {
            next,
        }))
    }

    fn ref_set_handle_result(assigned: SharedValue, next: Self) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::RefSetHandleResult {
            assigned,
            next,
        }))
    }

    fn ref_set_handle_value_result(assigned: SharedValue, next: Self) -> Self {
        Self(Rc::new(
            EvidenceContinuationFrame::RefSetHandleValueResult { assigned, next },
        ))
    }

    fn ref_set_emit_resolved_request(
        request: EvidenceRequest,
        assigned: SharedValue,
        mode: EvidenceRefSetResumeMode,
        next: Self,
    ) -> Self {
        Self(Rc::new(
            EvidenceContinuationFrame::RefSetEmitResolvedRequest {
                request,
                assigned,
                mode,
                next,
            },
        ))
    }

    fn resolve_ref_set_values(
        values: Vec<SharedValue>,
        assigned: SharedValue,
        out: Vec<SharedValue>,
        index: usize,
        finish: EvidenceRefSetFinish,
        next: Self,
    ) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::ResolveRefSetValues {
            values,
            assigned,
            out,
            index,
            finish,
            next,
        }))
    }

    fn resolve_ref_set_fields(
        fields: Vec<RuntimeEvidenceValueField>,
        assigned: SharedValue,
        out: Vec<RuntimeEvidenceValueField>,
        index: usize,
        next: Self,
    ) -> Self {
        Self(Rc::new(EvidenceContinuationFrame::ResolveRefSetFields {
            fields,
            assigned,
            out,
            index,
            next,
        }))
    }

    fn is_identity(&self) -> bool {
        matches!(self.0.as_ref(), EvidenceContinuationFrame::Identity)
    }

    fn then_counted(self, tail: Self, stats: &mut RuntimeEvidenceRunStats) -> Self {
        if tail.is_identity() {
            return self;
        }
        if self.is_identity() {
            return tail;
        }
        stats.continuation_append_steps += 1;
        Self(Rc::new(EvidenceContinuationFrame::Then {
            first: self,
            second: tail,
        }))
    }
}

impl EvidenceRequest {
    fn append_continuation(
        mut self,
        tail: EvidenceContinuation,
        stats: &mut RuntimeEvidenceRunStats,
    ) -> Self {
        stats.continuation_appends += 1;
        self.continuation = self.continuation.then_counted(tail, stats);
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

    fn with_visible_markers(mut self, markers: &[Vec<String>]) -> Self {
        for marker in markers {
            self.add_visible_marker(marker);
        }
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
                ..RuntimeEvidenceRunStats::default()
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
    stats: RuntimeEvidenceRunStats,
}

impl<'a> RuntimeEvidenceRunner<'a> {
    fn new(program: &'a Program) -> Self {
        let evidence = ControlEvidenceIndex::new(program);
        let stats = evidence.stats();
        Self {
            program,
            evidence,
            instances: HashMap::new(),
            evaluating_instances: HashSet::new(),
            stats,
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
        Ok(RuntimeEvidenceRunOutput {
            values: values
                .into_iter()
                .map(|value| value.as_ref().clone())
                .collect(),
            evidence_stats: self.stats,
        })
    }

    fn clone_env(&mut self, env: &Env) -> Env {
        clone_env_for_stats(env, &mut self.stats)
    }

    fn append_request_continuation(
        &mut self,
        request: EvidenceRequest,
        tail: EvidenceContinuation,
    ) -> EvidenceRequest {
        request.append_continuation(tail, &mut self.stats)
    }

    fn close_marked_result(
        &mut self,
        result: EvidenceEvalResult,
        markers: &[Vec<String>],
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if markers.is_empty() {
            return Ok(result);
        }
        match result {
            EvidenceEvalResult::Value(value) => Ok(EvidenceEvalResult::Value(mark_runtime_value(
                value, markers,
            ))),
            EvidenceEvalResult::Request(request) => {
                let mut request = request.with_visible_markers(markers);
                for marker in markers.iter().rev() {
                    request = self.append_request_continuation(
                        request,
                        EvidenceContinuation::marker_frame(
                            marker.clone(),
                            EvidenceContinuation::identity(),
                        ),
                    );
                }
                Ok(EvidenceEvalResult::Request(request))
            }
        }
    }

    fn close_marked_result_for_type(
        &mut self,
        result: EvidenceEvalResult,
        markers: &[Vec<String>],
        ty: &Type,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if markers.is_empty() || !type_may_need_hygiene_mark(ty) {
            return Ok(result);
        }
        match result {
            EvidenceEvalResult::Value(value) => Ok(EvidenceEvalResult::Value(
                mark_runtime_value_unchecked(value, markers),
            )),
            EvidenceEvalResult::Request(request) => {
                self.close_marked_result(EvidenceEvalResult::Request(request), markers)
            }
        }
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
        self.stats.expr_evals += 1;
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
                    env: self.clone_env(env),
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
                        self.append_request_continuation(
                            request,
                            EvidenceContinuation::force_thunk(
                                target_value_is_thunk,
                                EvidenceContinuation::identity(),
                            ),
                        ),
                    )),
                };
            }
            Expr::FunctionAdapter {
                source,
                target,
                function,
                hygiene,
            } => {
                return match self.eval_expr_result(*function, env)? {
                    EvidenceEvalResult::Value(function) => Ok(EvidenceEvalResult::Value(shared(
                        RuntimeEvidenceValue::FunctionAdapter {
                            source: source.clone(),
                            target: target.clone(),
                            function,
                            hygiene: hygiene.clone(),
                        },
                    ))),
                    EvidenceEvalResult::Request(request) => Ok(EvidenceEvalResult::Request(
                        self.append_request_continuation(
                            request,
                            EvidenceContinuation::adapt_value(
                                source.clone(),
                                target.clone(),
                                EvidenceContinuation::identity(),
                            ),
                        ),
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
                            self.append_request_continuation(
                                request.with_visible_marker(path),
                                marker,
                            ),
                        ))
                    }
                };
            }
            Expr::Apply { callee, arg } => {
                return self.eval_apply_result(Some(expr_id), *callee, *arg, env);
            }
            Expr::RefSet { reference, value } => {
                return self.eval_ref_set_result(*reference, *value, env);
            }
            Expr::Lambda { param, body } => {
                RuntimeEvidenceValue::Closure(Rc::new(RuntimeEvidenceClosure {
                    param: param.clone(),
                    body: *body,
                    env: self.clone_env(env),
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
                    EvidenceEvalResult::Request(request) => {
                        let env = self.clone_env(env);
                        Ok(EvidenceEvalResult::Request(
                            self.append_request_continuation(
                                request,
                                EvidenceContinuation::case_scrutinee(
                                    arms.clone(),
                                    env,
                                    EvidenceContinuation::identity(),
                                ),
                            ),
                        ))
                    }
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
            EvidenceEvalResult::Request(request) => {
                let env = self.clone_env(env);
                Ok(EvidenceEvalResult::Request(
                    self.append_request_continuation(
                        request,
                        EvidenceContinuation::apply_callee(
                            site,
                            arg_expr,
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                ))
            }
        }
    }

    fn eval_apply_arg_result(
        &mut self,
        site: Option<ExprId>,
        callee: SharedValue,
        arg_expr: ExprId,
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let mut arg_env = self.clone_env(env);
        match self.eval_expr_result(arg_expr, &mut arg_env)? {
            EvidenceEvalResult::Value(arg) => self.apply_value_result(site, callee, arg),
            EvidenceEvalResult::Request(request) => Ok(EvidenceEvalResult::Request(
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::apply_arg(site, callee, EvidenceContinuation::identity()),
                ),
            )),
        }
    }

    fn eval_ref_set_result(
        &mut self,
        reference: ExprId,
        value: ExprId,
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let mut reference_env = self.clone_env(env);
        let result = self.eval_expr_result(reference, &mut reference_env)?;
        let env = self.clone_env(env);
        self.continue_result(
            result,
            EvidenceContinuation::ref_set_reference(value, env, EvidenceContinuation::identity()),
        )
    }

    fn handle_ref_set_result(
        &mut self,
        result: EvidenceEvalResult,
        assigned: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match result {
            EvidenceEvalResult::Value(value) => {
                let resolved = self.resolve_ref_set_value(value, assigned)?;
                self.continue_result(
                    resolved,
                    EvidenceContinuation::ref_set_resolved_unit(EvidenceContinuation::identity()),
                )
            }
            EvidenceEvalResult::Request(request) if request_is_ref_update(&request) => {
                let resumed = self.resume_continuation(request.continuation, assigned.clone())?;
                self.handle_ref_set_result(resumed, assigned)
            }
            EvidenceEvalResult::Request(request) => {
                let payload = request.payload.clone();
                let resolved_payload = self.resolve_ref_set_value(payload, assigned.clone())?;
                self.continue_result(
                    resolved_payload,
                    EvidenceContinuation::ref_set_emit_resolved_request(
                        request,
                        assigned,
                        EvidenceRefSetResumeMode::Result,
                        EvidenceContinuation::identity(),
                    ),
                )
            }
        }
    }

    fn handle_ref_set_value_result(
        &mut self,
        result: EvidenceEvalResult,
        assigned: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match result {
            EvidenceEvalResult::Value(value) => self.resolve_ref_set_value(value, assigned),
            EvidenceEvalResult::Request(request) if request_is_ref_update(&request) => {
                let resumed = self.resume_continuation(request.continuation, assigned.clone())?;
                self.handle_ref_set_value_result(resumed, assigned)
            }
            EvidenceEvalResult::Request(request) => {
                let payload = request.payload.clone();
                let resolved_payload = self.resolve_ref_set_value(payload, assigned.clone())?;
                self.continue_result(
                    resolved_payload,
                    EvidenceContinuation::ref_set_emit_resolved_request(
                        request,
                        assigned,
                        EvidenceRefSetResumeMode::ValueResult,
                        EvidenceContinuation::identity(),
                    ),
                )
            }
        }
    }

    fn resolve_ref_set_value(
        &mut self,
        value: SharedValue,
        assigned: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match value.as_ref() {
            RuntimeEvidenceValue::Tuple(values) => self.resolve_ref_set_values(
                values.clone(),
                assigned,
                Vec::new(),
                0,
                EvidenceRefSetFinish::Tuple,
            ),
            RuntimeEvidenceValue::List(values) => self.resolve_ref_set_values(
                values.clone(),
                assigned,
                Vec::new(),
                0,
                EvidenceRefSetFinish::List,
            ),
            RuntimeEvidenceValue::Record(fields) => {
                self.resolve_ref_set_fields(fields.clone(), assigned, Vec::new(), 0)
            }
            RuntimeEvidenceValue::PolyVariant { tag, payloads } => self.resolve_ref_set_values(
                payloads.clone(),
                assigned,
                Vec::new(),
                0,
                EvidenceRefSetFinish::PolyVariant { tag: tag.clone() },
            ),
            RuntimeEvidenceValue::DataConstructor { def, payloads } => self.resolve_ref_set_values(
                payloads.clone(),
                assigned,
                Vec::new(),
                0,
                EvidenceRefSetFinish::DataConstructor { def: *def },
            ),
            RuntimeEvidenceValue::Thunk(_) => {
                let result = self.force_thunk_result(value)?;
                self.handle_ref_set_value_result(result, assigned)
            }
            _ => Ok(EvidenceEvalResult::Value(value)),
        }
    }

    fn resolve_ref_set_values(
        &mut self,
        values: Vec<SharedValue>,
        assigned: SharedValue,
        out: Vec<SharedValue>,
        index: usize,
        finish: EvidenceRefSetFinish,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if index >= values.len() {
            return Ok(EvidenceEvalResult::Value(finish_ref_set_values(
                finish, out,
            )));
        }
        let resolved = self.resolve_ref_set_value(values[index].clone(), assigned.clone())?;
        self.continue_result(
            resolved,
            EvidenceContinuation::resolve_ref_set_values(
                values,
                assigned,
                out,
                index,
                finish,
                EvidenceContinuation::identity(),
            ),
        )
    }

    fn resolve_ref_set_fields(
        &mut self,
        fields: Vec<RuntimeEvidenceValueField>,
        assigned: SharedValue,
        out: Vec<RuntimeEvidenceValueField>,
        index: usize,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if index >= fields.len() {
            return Ok(EvidenceEvalResult::Value(shared(
                RuntimeEvidenceValue::Record(out),
            )));
        }
        let resolved = self.resolve_ref_set_value(fields[index].value.clone(), assigned.clone())?;
        self.continue_result(
            resolved,
            EvidenceContinuation::resolve_ref_set_fields(
                fields,
                assigned,
                out,
                index,
                EvidenceContinuation::identity(),
            ),
        )
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
                    let env = self.clone_env(env);
                    return Ok(EvidenceEvalResult::Request(
                        self.append_request_continuation(
                            request,
                            EvidenceContinuation::tuple_items(
                                values,
                                rest,
                                env,
                                EvidenceContinuation::identity(),
                            ),
                        ),
                    ));
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
                    let env = self.clone_env(env);
                    return Ok(EvidenceEvalResult::Request(
                        self.append_request_continuation(
                            request,
                            EvidenceContinuation::record_spread(
                                fields.to_vec(),
                                env,
                                EvidenceContinuation::identity(),
                            ),
                        ),
                    ));
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
                    let env = self.clone_env(env);
                    return Ok(EvidenceEvalResult::Request(
                        self.append_request_continuation(
                            request,
                            EvidenceContinuation::record_fields(
                                values,
                                rest,
                                env,
                                EvidenceContinuation::identity(),
                            ),
                        ),
                    ));
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
                    let env = self.clone_env(env);
                    return Ok(EvidenceEvalResult::Request(
                        self.append_request_continuation(
                            request,
                            EvidenceContinuation::poly_variant_payloads(
                                tag,
                                values,
                                rest,
                                env,
                                EvidenceContinuation::identity(),
                            ),
                        ),
                    ));
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
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::select_base(
                        name.to_string(),
                        resolution.clone(),
                        EvidenceContinuation::identity(),
                    ),
                ),
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
        self.stats.apply_value_calls += 1;
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
                hygiene,
            } => self.apply_adapter_result(source, target, function.clone(), hygiene, arg),
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
                let mut env = self.clone_env(&closure.env);
                self.bind_pat(&closure.param, arg, &mut env)?;
                self.eval_expr_result(closure.body, &mut env)
            }
            RuntimeEvidenceValue::RecursiveClosure { def, closure } => {
                let mut env = self.clone_env(&closure.env);
                env.insert(
                    *def,
                    shared(RuntimeEvidenceValue::RecursiveClosure {
                        def: *def,
                        closure: closure.clone(),
                    }),
                );
                self.bind_pat(&closure.param, arg, &mut env)?;
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
                    self.append_request_continuation(
                        request,
                        EvidenceContinuation::apply_forced_callee(
                            site,
                            arg,
                            EvidenceContinuation::identity(),
                        ),
                    ),
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
            RuntimeEvidenceValue::Marked { value, markers } => {
                let result = self.apply_value_result(site, value.clone(), arg)?;
                self.close_marked_result(result, markers)
            }
            value => Err(RuntimeEvidenceRunError::NotFunction(format_value(value))),
        }
    }

    fn apply_adapter_result(
        &mut self,
        source: &Type,
        target: &Type,
        function: SharedValue,
        hygiene: &FunctionAdapterHygiene,
        arg: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        self.stats.apply_adapter_calls += 1;
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
        let body_markers = marker_paths(&hygiene.markers);
        let arg_markers = combined_markers(&body_markers, &marker_paths(&hygiene.arg_markers));
        let ret_markers = combined_markers(&body_markers, &marker_paths(&hygiene.ret_markers));
        let function = mark_runtime_value_unchecked(function, &body_markers);
        let arg = mark_runtime_value_for_type(arg, &arg_markers, &target_arg);
        let result = self.adapt_value_result(arg, &target_arg, &source_arg)?;
        self.continue_result(
            result,
            EvidenceContinuation::apply_adapter_arg(
                function,
                ret_markers,
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
        self.stats.adapt_value_calls += 1;
        if let RuntimeEvidenceValue::Marked { value, markers } = value.as_ref() {
            let result = self.adapt_value_result(value.clone(), source, target)?;
            return self.close_marked_result(result, markers);
        }
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
                    hygiene: FunctionAdapterHygiene::default(),
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
        self.stats.continuation_resume_steps += 1;
        match continuation.0.as_ref() {
            EvidenceContinuationFrame::Identity => Ok(EvidenceEvalResult::Value(value)),
            EvidenceContinuationFrame::Then { first, second } => {
                let result = self.resume_continuation(first.clone(), value)?;
                self.continue_result(result, second.clone())
            }
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
                let mut env = self.clone_env(env);
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
                ret_markers,
                source_ret,
                target_ret,
                next,
            } => {
                let result = self.apply_value_result(None, function.clone(), value)?;
                self.continue_result(
                    result,
                    EvidenceContinuation::apply_adapter_result(
                        ret_markers.clone(),
                        source_ret.clone(),
                        target_ret.clone(),
                        next.clone(),
                    ),
                )
            }
            EvidenceContinuationFrame::ApplyAdapterResult {
                ret_markers,
                source_ret,
                target_ret,
                next,
            } => {
                let result = self.adapt_value_result(value, source_ret, target_ret)?;
                let result = self.close_marked_result_for_type(result, ret_markers, target_ret)?;
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
                let mut env = self.clone_env(env);
                let result = self.eval_tuple_items_result(values, rest, &mut env)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::RecordSpread { fields, env, next } => {
                let values = record_fields(value.as_ref())?;
                let mut env = self.clone_env(env);
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
                let mut env = self.clone_env(env);
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
                let mut env = self.clone_env(env);
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
                let mut env = self.clone_env(env);
                let last = match resume {
                    EvidenceBlockResume::Let(pat) => {
                        let value = recursive_let_value(pat, value);
                        self.bind_pat(pat, value, &mut env)?;
                        last.clone()
                    }
                    EvidenceBlockResume::Expr => value,
                };
                let result = self.eval_block_parts_result(rest, *tail, &mut env, last)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::RefSetReference {
                value: expr,
                env,
                next,
            } => {
                let result = self.force_value_if_thunk_result(value)?;
                let env = self.clone_env(env);
                self.continue_result(
                    result,
                    EvidenceContinuation::ref_set_forced_reference(*expr, env, next.clone()),
                )
            }
            EvidenceContinuationFrame::RefSetForcedReference {
                value: expr,
                env,
                next,
            } => {
                let mut env = self.clone_env(env);
                let result = self.eval_expr_result(*expr, &mut env)?;
                self.continue_result(
                    result,
                    EvidenceContinuation::ref_set_value(value, next.clone()),
                )
            }
            EvidenceContinuationFrame::RefSetValue { reference, next } => {
                let result = self.force_value_if_thunk_result(value)?;
                self.continue_result(
                    result,
                    EvidenceContinuation::ref_set_forced_value(reference.clone(), next.clone()),
                )
            }
            EvidenceContinuationFrame::RefSetForcedValue { reference, next } => {
                let update_effect = record_field(reference.as_ref(), "update_effect")?;
                let result = self.apply_value_result(
                    None,
                    update_effect,
                    shared(RuntimeEvidenceValue::Unit),
                )?;
                let result = self.handle_ref_set_result(result, value)?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::RefSetResolvedUnit { next } => self.continue_result(
                EvidenceEvalResult::Value(shared(RuntimeEvidenceValue::Unit)),
                next.clone(),
            ),
            EvidenceContinuationFrame::RefSetHandleResult { assigned, next } => {
                let result =
                    self.handle_ref_set_result(EvidenceEvalResult::Value(value), assigned.clone())?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::RefSetHandleValueResult { assigned, next } => {
                let result = self.handle_ref_set_value_result(
                    EvidenceEvalResult::Value(value),
                    assigned.clone(),
                )?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::RefSetEmitResolvedRequest {
                request,
                assigned,
                mode,
                next,
            } => {
                let mut request = request.clone();
                request.payload = value;
                let frame = match mode {
                    EvidenceRefSetResumeMode::Result => {
                        EvidenceContinuation::ref_set_handle_result(assigned.clone(), next.clone())
                    }
                    EvidenceRefSetResumeMode::ValueResult => {
                        EvidenceContinuation::ref_set_handle_value_result(
                            assigned.clone(),
                            next.clone(),
                        )
                    }
                };
                Ok(EvidenceEvalResult::Request(
                    self.append_request_continuation(request, frame),
                ))
            }
            EvidenceContinuationFrame::ResolveRefSetValues {
                values,
                assigned,
                out,
                index,
                finish,
                next,
            } => {
                let mut out = out.clone();
                out.push(value);
                let result = self.resolve_ref_set_values(
                    values.clone(),
                    assigned.clone(),
                    out,
                    index + 1,
                    finish.clone(),
                )?;
                self.continue_result(result, next.clone())
            }
            EvidenceContinuationFrame::ResolveRefSetFields {
                fields,
                assigned,
                out,
                index,
                next,
            } => {
                let mut out = out.clone();
                out.push(RuntimeEvidenceValueField {
                    name: fields[*index].name.clone(),
                    value,
                });
                let result =
                    self.resolve_ref_set_fields(fields.clone(), assigned.clone(), out, index + 1)?;
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
        self.stats.request_continuation_steps += 1;
        let (request, next) = match continuation.0.as_ref() {
            EvidenceContinuationFrame::Identity => {
                return Ok(EvidenceEvalResult::Request(request));
            }
            EvidenceContinuationFrame::Then { first, second } => {
                let result = self.continue_request_with_continuation(request, first.clone())?;
                return self.continue_result(result, second.clone());
            }
            EvidenceContinuationFrame::ForceThunk {
                target_value_is_thunk,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::force_thunk(
                        *target_value_is_thunk,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::ForceValueIfThunk { next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::force_value_if_thunk(EvidenceContinuation::identity()),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::ApplyCallee {
                site,
                arg,
                env,
                next,
            } => {
                let env = self.clone_env(env);
                (
                    self.append_request_continuation(
                        request,
                        EvidenceContinuation::apply_callee(
                            *site,
                            *arg,
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                    next.clone(),
                )
            }
            EvidenceContinuationFrame::ApplyArg { site, callee, next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::apply_arg(
                        *site,
                        callee.clone(),
                        EvidenceContinuation::identity(),
                    ),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::ApplyForcedCallee { site, arg, next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::apply_forced_callee(
                        *site,
                        arg.clone(),
                        EvidenceContinuation::identity(),
                    ),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::AdaptValue {
                source,
                target,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::adapt_value(
                        source.clone(),
                        target.clone(),
                        EvidenceContinuation::identity(),
                    ),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::WrapThunkValue { next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::wrap_thunk_value(EvidenceContinuation::identity()),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::ApplyAdapterArg {
                function,
                ret_markers,
                source_ret,
                target_ret,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::apply_adapter_arg(
                        function.clone(),
                        ret_markers.clone(),
                        source_ret.clone(),
                        target_ret.clone(),
                        EvidenceContinuation::identity(),
                    ),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::ApplyAdapterResult {
                ret_markers,
                source_ret,
                target_ret,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::apply_adapter_result(
                        ret_markers.clone(),
                        source_ret.clone(),
                        target_ret.clone(),
                        EvidenceContinuation::identity(),
                    ),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::CaseScrutinee { arms, env, next } => {
                let env = self.clone_env(env);
                (
                    self.append_request_continuation(
                        request,
                        EvidenceContinuation::case_scrutinee(
                            arms.clone(),
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                    next.clone(),
                )
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
                    EvidenceEvalResult::Request(request),
                )?;
                return self.continue_result(result, next.clone());
            }
            EvidenceContinuationFrame::MarkerFrame { path, next } => (
                self.append_request_continuation(
                    request.with_visible_marker(path),
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
            } => {
                let env = self.clone_env(env);
                (
                    self.append_request_continuation(
                        request,
                        EvidenceContinuation::tuple_items(
                            values.clone(),
                            rest.clone(),
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                    next.clone(),
                )
            }
            EvidenceContinuationFrame::RecordSpread { fields, env, next } => {
                let env = self.clone_env(env);
                (
                    self.append_request_continuation(
                        request,
                        EvidenceContinuation::record_spread(
                            fields.clone(),
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                    next.clone(),
                )
            }
            EvidenceContinuationFrame::RecordFields {
                values,
                rest,
                env,
                next,
            } => {
                let env = self.clone_env(env);
                (
                    self.append_request_continuation(
                        request,
                        EvidenceContinuation::record_fields(
                            values.clone(),
                            rest.clone(),
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                    next.clone(),
                )
            }
            EvidenceContinuationFrame::PolyVariantPayloads {
                tag,
                values,
                rest,
                env,
                next,
            } => {
                let env = self.clone_env(env);
                (
                    self.append_request_continuation(
                        request,
                        EvidenceContinuation::poly_variant_payloads(
                            tag.clone(),
                            values.clone(),
                            rest.clone(),
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                    next.clone(),
                )
            }
            EvidenceContinuationFrame::SelectBase {
                name,
                resolution,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::select_base(
                        name.clone(),
                        resolution.clone(),
                        EvidenceContinuation::identity(),
                    ),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::BlockStmt {
                resume,
                rest,
                tail,
                env,
                last,
                next,
            } => {
                let env = self.clone_env(env);
                (
                    self.append_request_continuation(
                        request,
                        EvidenceContinuation::block_stmt(
                            resume.clone(),
                            rest.clone(),
                            *tail,
                            env,
                            last.clone(),
                            EvidenceContinuation::identity(),
                        ),
                    ),
                    next.clone(),
                )
            }
            EvidenceContinuationFrame::RefSetReference { value, env, next } => {
                let env = self.clone_env(env);
                (
                    self.append_request_continuation(
                        request,
                        EvidenceContinuation::ref_set_reference(
                            *value,
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                    next.clone(),
                )
            }
            EvidenceContinuationFrame::RefSetForcedReference { value, env, next } => {
                let env = self.clone_env(env);
                (
                    self.append_request_continuation(
                        request,
                        EvidenceContinuation::ref_set_forced_reference(
                            *value,
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                    next.clone(),
                )
            }
            EvidenceContinuationFrame::RefSetValue { reference, next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::ref_set_value(
                        reference.clone(),
                        EvidenceContinuation::identity(),
                    ),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::RefSetForcedValue { reference, next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::ref_set_forced_value(
                        reference.clone(),
                        EvidenceContinuation::identity(),
                    ),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::RefSetResolvedUnit { next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::ref_set_resolved_unit(EvidenceContinuation::identity()),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::RefSetHandleResult { assigned, next } => {
                let result = self.handle_ref_set_result(
                    EvidenceEvalResult::Request(request),
                    assigned.clone(),
                )?;
                return self.continue_result(result, next.clone());
            }
            EvidenceContinuationFrame::RefSetHandleValueResult { assigned, next } => {
                let result = self.handle_ref_set_value_result(
                    EvidenceEvalResult::Request(request),
                    assigned.clone(),
                )?;
                return self.continue_result(result, next.clone());
            }
            EvidenceContinuationFrame::RefSetEmitResolvedRequest {
                request: pending,
                assigned,
                mode,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::ref_set_emit_resolved_request(
                        pending.clone(),
                        assigned.clone(),
                        *mode,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::ResolveRefSetValues {
                values,
                assigned,
                out,
                index,
                finish,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::resolve_ref_set_values(
                        values.clone(),
                        assigned.clone(),
                        out.clone(),
                        *index,
                        finish.clone(),
                        EvidenceContinuation::identity(),
                    ),
                ),
                next.clone(),
            ),
            EvidenceContinuationFrame::ResolveRefSetFields {
                fields,
                assigned,
                out,
                index,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::resolve_ref_set_fields(
                        fields.clone(),
                        assigned.clone(),
                        out.clone(),
                        *index,
                        EvidenceContinuation::identity(),
                    ),
                ),
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
        self.stats.thunk_forces += 1;
        match thunk.as_ref() {
            RuntimeEvidenceValue::Thunk(thunk) => match thunk.as_ref() {
                RuntimeEvidenceThunk::Expr { body, env } => {
                    self.stats.thunk_force_expr += 1;
                    let mut env = self.clone_env(env);
                    self.eval_expr_result(*body, &mut env)
                }
                RuntimeEvidenceThunk::Effect {
                    path,
                    payload,
                    route,
                } => {
                    self.stats.thunk_force_effect += 1;
                    Ok(EvidenceEvalResult::Request(EvidenceRequest {
                        path: path.clone(),
                        payload: payload.clone(),
                        route: *route,
                        visible_markers: Vec::new(),
                        continuation: EvidenceContinuation::identity(),
                    }))
                }
                RuntimeEvidenceThunk::Continuation { continuation, arg } => {
                    self.stats.thunk_force_continuation += 1;
                    let result = self.resume_continuation(continuation.clone(), arg.clone())?;
                    self.continue_result(
                        result,
                        EvidenceContinuation::force_value_if_thunk(EvidenceContinuation::identity()),
                    )
                }
                RuntimeEvidenceThunk::Value(value) => {
                    self.stats.thunk_force_value += 1;
                    Ok(EvidenceEvalResult::Value(value.clone()))
                }
                RuntimeEvidenceThunk::Adapter {
                    source,
                    target,
                    thunk,
                } => {
                    self.stats.thunk_force_adapter += 1;
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
            RuntimeEvidenceValue::Marked { value, markers } => {
                let result = self.force_thunk_result(value.clone())?;
                self.close_marked_result(result, markers)
            }
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
        let mut body_env = self.clone_env(env);
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
        self.stats.catch_body_checks += 1;
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
        let env = self.clone_env(env);
        self.append_request_continuation(
            request,
            EvidenceContinuation::catch_body(
                catch_expr,
                arms.to_vec(),
                env,
                EvidenceContinuation::identity(),
            ),
        )
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
        let mut arm_env = self.clone_env(env);
        self.bind_pat(&arm.pat, value, &mut arm_env)?;
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
        let mut arm_env = self.clone_env(env);
        self.bind_pat(&arm.pat, request.payload, &mut arm_env)?;
        if let Some(continuation_pat) = &arm.continuation {
            if !resumptive {
                return Err(RuntimeEvidenceRunError::UnsupportedExpr(
                    "abortive continuation binding",
                ));
            }
            self.bind_pat(
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
            let mut arm_env = self.clone_env(env);
            if self
                .bind_pat(&arm.pat, scrutinee.clone(), &mut arm_env)
                .is_err()
            {
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
            EvidenceEvalResult::Request(request) => {
                let env = self.clone_env(env);
                Ok(EvidenceEvalResult::Request(
                    self.append_request_continuation(
                        request,
                        EvidenceContinuation::case_scrutinee(
                            arms.to_vec(),
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                ))
            }
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
                        self.bind_pat(pat, value, env)?;
                    }
                    EvidenceEvalResult::Request(request) => {
                        let env = self.clone_env(env);
                        return Ok(EvidenceEvalResult::Request(
                            self.append_request_continuation(
                                request,
                                EvidenceContinuation::block_stmt(
                                    EvidenceBlockResume::Let(pat.clone()),
                                    rest.to_vec(),
                                    tail,
                                    env,
                                    last,
                                    EvidenceContinuation::identity(),
                                ),
                            ),
                        ));
                    }
                },
                Stmt::Expr(expr) => match self.eval_expr_result(*expr, env)? {
                    EvidenceEvalResult::Value(value) => last = value,
                    EvidenceEvalResult::Request(request) => {
                        let env = self.clone_env(env);
                        return Ok(EvidenceEvalResult::Request(
                            self.append_request_continuation(
                                request,
                                EvidenceContinuation::block_stmt(
                                    EvidenceBlockResume::Expr,
                                    rest.to_vec(),
                                    tail,
                                    env,
                                    last,
                                    EvidenceContinuation::identity(),
                                ),
                            ),
                        ));
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
                            let env = self.clone_env(env);
                            return Ok(EvidenceEvalResult::Request(
                                self.append_request_continuation(
                                    request,
                                    EvidenceContinuation::block_stmt(
                                        EvidenceBlockResume::Expr,
                                        rest.to_vec(),
                                        tail,
                                        env,
                                        last,
                                        EvidenceContinuation::identity(),
                                    ),
                                ),
                            ));
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
        self.stats.primitive_apply_calls += 1;
        use PrimitiveOp::*;
        let value = match op {
            BoolNot => RuntimeEvidenceValue::Bool(!expect_bool(&args[0])?),
            BoolEq => RuntimeEvidenceValue::Bool(expect_bool(&args[0])? == expect_bool(&args[1])?),
            ListEmpty => RuntimeEvidenceValue::List(Vec::new()),
            ListSingleton => RuntimeEvidenceValue::List(vec![args[0].clone()]),
            ListLen => RuntimeEvidenceValue::Int(expect_list(&args[0])?.len() as i64),
            ListIndex => expect_list(&args[0])?
                .get(value_index(&args[1])?)
                .map(|value| value.as_ref().clone())
                .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))?,
            ListIndexRange => {
                let values = expect_list(&args[0])?;
                let (start, end) = normalized_range_value(context, op, &args[1], values.len())?;
                self.stats.list_values_copied += end - start;
                RuntimeEvidenceValue::List(values[start..end].to_vec())
            }
            ListIndexRangeRaw => {
                let values = expect_list(&args[0])?;
                let start = value_index(&args[1])?;
                let end = value_index(&args[2])?;
                if start > end || end > values.len() {
                    return Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op));
                }
                self.stats.list_values_copied += end - start;
                RuntimeEvidenceValue::List(values[start..end].to_vec())
            }
            ListMerge => {
                self.stats.list_merge_calls += 1;
                let left = expect_list(&args[0])?;
                let right = expect_list(&args[1])?;
                self.stats.list_values_copied += left.len() + right.len();
                let mut values = left.to_vec();
                values.extend(right.iter().cloned());
                RuntimeEvidenceValue::List(values)
            }
            ListSplice => {
                let values = expect_list(&args[0])?;
                let (start, end) = normalized_range_value(context, op, &args[1], values.len())?;
                let insert = expect_list(&args[2])?;
                self.stats.list_values_copied += values.len() - (end - start) + insert.len();
                RuntimeEvidenceValue::List(splice_shared_slice(values, start, end, insert)?)
            }
            ListSpliceRaw => {
                let values = expect_list(&args[0])?;
                let start = value_index(&args[1])?;
                let end = value_index(&args[2])?;
                let insert = expect_list(&args[3])?;
                if start > end || end > values.len() {
                    return Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op));
                }
                self.stats.list_values_copied += values.len() - (end - start) + insert.len();
                RuntimeEvidenceValue::List(splice_shared_slice(values, start, end, insert)?)
            }
            ListViewRaw => apply_list_view_raw(context, &args[0], &mut self.stats)?,
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
            StringLen => RuntimeEvidenceValue::Int(grapheme_len(expect_str(&args[0])?) as i64),
            StringLineCount => {
                RuntimeEvidenceValue::Int(string_line_count(expect_str(&args[0])?) as i64)
            }
            StringLineRange => {
                let index = value_index(&args[1])?;
                let (start, end) = string_line_range(expect_str(&args[0])?, index)
                    .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))?;
                range_value(context, op, start, end)?
            }
            StringIndex => RuntimeEvidenceValue::Str(
                string_index(expect_str(&args[0])?, value_index(&args[1])?)
                    .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))?,
            ),
            StringIndexRange => {
                let text = expect_str(&args[0])?;
                let (start, end) =
                    normalized_range_value(context, op, &args[1], grapheme_len(text))?;
                RuntimeEvidenceValue::Str(
                    string_index_range(text, start, end)
                        .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))?,
                )
            }
            StringIndexRangeRaw => {
                let text = expect_str(&args[0])?;
                RuntimeEvidenceValue::Str(
                    string_index_range(text, value_index(&args[1])?, value_index(&args[2])?)
                        .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))?,
                )
            }
            StringSplice => {
                let text = expect_str(&args[0])?;
                let (start, end) =
                    normalized_range_value(context, op, &args[1], grapheme_len(text))?;
                RuntimeEvidenceValue::Str(
                    string_splice(text, start, end, expect_str(&args[2])?)
                        .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))?,
                )
            }
            StringSpliceRaw => RuntimeEvidenceValue::Str(
                string_splice(
                    expect_str(&args[0])?,
                    value_index(&args[1])?,
                    value_index(&args[2])?,
                    expect_str(&args[3])?,
                )
                .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))?,
            ),
            StringToBytes => RuntimeEvidenceValue::Bytes(expect_str(&args[0])?.as_bytes().to_vec()),
            CharEq => RuntimeEvidenceValue::Bool(expect_str(&args[0])? == expect_str(&args[1])?),
            CharToString => RuntimeEvidenceValue::Str(expect_str(&args[0])?.to_string()),
            CharIsWhitespace => RuntimeEvidenceValue::Bool(expect_str(&args[0])?.trim().is_empty()),
            CharIsPunctuation => RuntimeEvidenceValue::Bool(
                expect_str(&args[0])?
                    .chars()
                    .all(|ch| ch.is_ascii_punctuation()),
            ),
            CharIsWord => RuntimeEvidenceValue::Bool(
                expect_str(&args[0])?
                    .chars()
                    .all(|ch| ch == '_' || ch.is_alphanumeric()),
            ),
            BytesLen => RuntimeEvidenceValue::Int(expect_bytes(&args[0])?.len() as i64),
            BytesEq => {
                RuntimeEvidenceValue::Bool(expect_bytes(&args[0])? == expect_bytes(&args[1])?)
            }
            BytesConcat => {
                let left = expect_bytes(&args[0])?;
                let right = expect_bytes(&args[1])?;
                let mut bytes = Vec::with_capacity(left.len() + right.len());
                bytes.extend_from_slice(left);
                bytes.extend_from_slice(right);
                RuntimeEvidenceValue::Bytes(bytes)
            }
            BytesIndex => RuntimeEvidenceValue::Int(
                *expect_bytes(&args[0])?
                    .get(value_index(&args[1])?)
                    .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))?
                    as i64,
            ),
            BytesIndexRange => {
                let bytes = expect_bytes(&args[0])?;
                let (start, end) = normalized_range_value(context, op, &args[1], bytes.len())?;
                RuntimeEvidenceValue::Bytes(bytes[start..end].to_vec())
            }
            BytesToUtf8Raw => {
                let bytes = expect_bytes(&args[0])?;
                let (text, valid) = match std::str::from_utf8(bytes) {
                    Ok(text) => (text, bytes.len()),
                    Err(error) => {
                        let valid = error.valid_up_to();
                        (std::str::from_utf8(&bytes[..valid]).unwrap_or(""), valid)
                    }
                };
                RuntimeEvidenceValue::Tuple(vec![
                    shared(RuntimeEvidenceValue::Str(text.to_string())),
                    shared(RuntimeEvidenceValue::Int(valid as i64)),
                ])
            }
            IntToString => RuntimeEvidenceValue::Str(expect_int(&args[0])?.to_string()),
            IntToHex => RuntimeEvidenceValue::Str(format!("{:x}", expect_int(&args[0])?)),
            IntToUpperHex => RuntimeEvidenceValue::Str(format!("{:X}", expect_int(&args[0])?)),
            IntToFloat => RuntimeEvidenceValue::Float(expect_int(&args[0])? as f64),
            FloatToString => RuntimeEvidenceValue::Str(format_float(expect_float(&args[0])?)),
            BoolToString => RuntimeEvidenceValue::Str(expect_bool(&args[0])?.to_string()),
            _ => return Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op)),
        };
        Ok(shared(value))
    }
}

impl<'a> RuntimeEvidenceRunner<'a> {
    fn bind_pat(
        &mut self,
        pat: &Pat,
        value: SharedValue,
        env: &mut Env,
    ) -> Result<(), RuntimeEvidenceRunError> {
        let (view, markers) = runtime_value_view(value.as_ref());
        match pat {
            Pat::Wild => Ok(()),
            Pat::Var(def) => {
                env.insert(*def, value);
                Ok(())
            }
            Pat::Lit(lit) if lit_matches(lit, view) => Ok(()),
            Pat::Lit(_) => Err(RuntimeEvidenceRunError::PatternMismatch),
            Pat::Tuple(items) => {
                let RuntimeEvidenceValue::Tuple(values) = view else {
                    return Err(RuntimeEvidenceRunError::PatternMismatch);
                };
                if items.len() != values.len() {
                    return Err(RuntimeEvidenceRunError::PatternMismatch);
                }
                for (pat, value) in items.iter().zip(values) {
                    self.bind_pat(pat, mark_runtime_value(value.clone(), &markers), env)?;
                }
                Ok(())
            }
            Pat::List {
                prefix,
                spread,
                suffix,
            } => self.bind_list_pat(prefix, spread.as_deref(), suffix, value, env),
            Pat::Record { fields, spread } => {
                let RuntimeEvidenceValue::Record(record_fields) = view else {
                    return Err(RuntimeEvidenceRunError::PatternMismatch);
                };
                let mut used = HashSet::new();
                for field in fields {
                    if let Some((index, value)) = record_fields
                        .iter()
                        .enumerate()
                        .find(|(_, value)| value.name == field.name)
                    {
                        used.insert(index);
                        self.bind_pat(
                            &field.pat,
                            mark_runtime_value(value.value.clone(), &markers),
                            env,
                        )?;
                        continue;
                    }

                    let Some(default) = field.default else {
                        return Err(RuntimeEvidenceRunError::PatternMismatch);
                    };
                    let value = self.eval_expr(default, env)?;
                    self.bind_pat(&field.pat, value, env)?;
                }

                let def = match spread {
                    RecordSpread::None => return Ok(()),
                    RecordSpread::Head(def) | RecordSpread::Tail(def) => *def,
                };
                let captured = record_fields
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| !used.contains(index))
                    .map(|(_, field)| RuntimeEvidenceValueField {
                        name: field.name.clone(),
                        value: mark_runtime_value(field.value.clone(), &markers),
                    })
                    .collect();
                env.insert(def, shared(RuntimeEvidenceValue::Record(captured)));
                Ok(())
            }
            Pat::PolyVariant(tag, payload_pats) => {
                let RuntimeEvidenceValue::PolyVariant {
                    tag: value_tag,
                    payloads,
                } = view
                else {
                    return Err(RuntimeEvidenceRunError::PatternMismatch);
                };
                if tag != value_tag || payload_pats.len() != payloads.len() {
                    return Err(RuntimeEvidenceRunError::PatternMismatch);
                }
                for (pat, value) in payload_pats.iter().zip(payloads) {
                    self.bind_pat(pat, mark_runtime_value(value.clone(), &markers), env)?;
                }
                Ok(())
            }
            Pat::Con(def, payload_pats) => {
                let RuntimeEvidenceValue::DataConstructor {
                    def: value_def,
                    payloads,
                } = view
                else {
                    return Err(RuntimeEvidenceRunError::PatternMismatch);
                };
                if def != value_def || payload_pats.len() != payloads.len() {
                    return Err(RuntimeEvidenceRunError::PatternMismatch);
                }
                for (pat, value) in payload_pats.iter().zip(payloads) {
                    self.bind_pat(pat, mark_runtime_value(value.clone(), &markers), env)?;
                }
                Ok(())
            }
            Pat::Ref(instance) => {
                let expected = self.eval_instance(*instance)?;
                if runtime_values_equivalent(view, expected.as_ref()) {
                    Ok(())
                } else {
                    Err(RuntimeEvidenceRunError::PatternMismatch)
                }
            }
            Pat::As(inner, def) => {
                self.bind_pat(inner, value.clone(), env)?;
                env.insert(*def, value);
                Ok(())
            }
            Pat::Or(left, right) => {
                let mut left_env = env.clone();
                if self.bind_pat(left, value.clone(), &mut left_env).is_ok() {
                    *env = left_env;
                    return Ok(());
                }
                self.bind_pat(right, value, env)
            }
        }
    }

    fn bind_list_pat(
        &mut self,
        prefix: &[Pat],
        spread: Option<&Pat>,
        suffix: &[Pat],
        value: SharedValue,
        env: &mut Env,
    ) -> Result<(), RuntimeEvidenceRunError> {
        let (view, markers) = runtime_value_view(value.as_ref());
        let RuntimeEvidenceValue::List(values) = view else {
            return Err(RuntimeEvidenceRunError::PatternMismatch);
        };
        let min_len = prefix.len() + suffix.len();
        if values.len() < min_len || spread.is_none() && values.len() != min_len {
            return Err(RuntimeEvidenceRunError::PatternMismatch);
        }

        for (pat, value) in prefix.iter().zip(values.iter()) {
            self.bind_pat(pat, mark_runtime_value(value.clone(), &markers), env)?;
        }

        let suffix_start = values.len() - suffix.len();
        for (offset, pat) in suffix.iter().enumerate() {
            self.bind_pat(
                pat,
                mark_runtime_value(values[suffix_start + offset].clone(), &markers),
                env,
            )?;
        }

        if let Some(spread) = spread {
            let slice = values[prefix.len()..suffix_start].to_vec();
            self.bind_pat(
                spread,
                mark_runtime_value(shared(RuntimeEvidenceValue::List(slice)), &markers),
                env,
            )?;
        }
        Ok(())
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

fn finish_ref_set_values(finish: EvidenceRefSetFinish, values: Vec<SharedValue>) -> SharedValue {
    shared(match finish {
        EvidenceRefSetFinish::Tuple => RuntimeEvidenceValue::Tuple(values),
        EvidenceRefSetFinish::List => RuntimeEvidenceValue::List(values),
        EvidenceRefSetFinish::PolyVariant { tag } => RuntimeEvidenceValue::PolyVariant {
            tag,
            payloads: values,
        },
        EvidenceRefSetFinish::DataConstructor { def } => RuntimeEvidenceValue::DataConstructor {
            def,
            payloads: values,
        },
    })
}

fn request_is_ref_update(request: &EvidenceRequest) -> bool {
    request
        .path
        .iter()
        .map(String::as_str)
        .eq(["std", "control", "var", "ref_update", "update"])
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

fn runtime_values_equivalent(left: &RuntimeEvidenceValue, right: &RuntimeEvidenceValue) -> bool {
    match (left, right) {
        (RuntimeEvidenceValue::Marked { value, .. }, right) => {
            runtime_values_equivalent(value.as_ref(), right)
        }
        (left, RuntimeEvidenceValue::Marked { value, .. }) => {
            runtime_values_equivalent(left, value.as_ref())
        }
        (RuntimeEvidenceValue::Int(left), RuntimeEvidenceValue::Int(right)) => left == right,
        (RuntimeEvidenceValue::BigInt(left), RuntimeEvidenceValue::BigInt(right)) => left == right,
        (RuntimeEvidenceValue::Float(left), RuntimeEvidenceValue::Float(right)) => left == right,
        (RuntimeEvidenceValue::Str(left), RuntimeEvidenceValue::Str(right)) => left == right,
        (RuntimeEvidenceValue::Bytes(left), RuntimeEvidenceValue::Bytes(right)) => left == right,
        (RuntimeEvidenceValue::Bool(left), RuntimeEvidenceValue::Bool(right)) => left == right,
        (RuntimeEvidenceValue::Unit, RuntimeEvidenceValue::Unit) => true,
        (RuntimeEvidenceValue::Tuple(left), RuntimeEvidenceValue::Tuple(right))
        | (RuntimeEvidenceValue::List(left), RuntimeEvidenceValue::List(right)) => {
            runtime_value_slices_equivalent(left, right)
        }
        (RuntimeEvidenceValue::Record(left), RuntimeEvidenceValue::Record(right)) => {
            left.len() == right.len()
                && left.iter().all(|left_field| {
                    right.iter().any(|right_field| {
                        left_field.name == right_field.name
                            && runtime_values_equivalent(
                                left_field.value.as_ref(),
                                right_field.value.as_ref(),
                            )
                    })
                })
        }
        (
            RuntimeEvidenceValue::PolyVariant {
                tag: left_tag,
                payloads: left_payloads,
            },
            RuntimeEvidenceValue::PolyVariant {
                tag: right_tag,
                payloads: right_payloads,
            },
        ) => {
            left_tag == right_tag && runtime_value_slices_equivalent(left_payloads, right_payloads)
        }
        (
            RuntimeEvidenceValue::DataConstructor {
                def: left_def,
                payloads: left_payloads,
            },
            RuntimeEvidenceValue::DataConstructor {
                def: right_def,
                payloads: right_payloads,
            },
        ) => {
            left_def == right_def && runtime_value_slices_equivalent(left_payloads, right_payloads)
        }
        _ => false,
    }
}

fn runtime_value_slices_equivalent(left: &[SharedValue], right: &[SharedValue]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| runtime_values_equivalent(left.as_ref(), right.as_ref()))
}

fn runtime_value_view(value: &RuntimeEvidenceValue) -> (&RuntimeEvidenceValue, Vec<Vec<String>>) {
    let mut value = value;
    let mut markers = Vec::new();
    while let RuntimeEvidenceValue::Marked {
        value: inner,
        markers: value_markers,
    } = value
    {
        markers = combined_markers(&markers, value_markers);
        value = inner.as_ref();
    }
    (value, markers)
}

fn expect_int(value: &SharedValue) -> Result<i64, RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Marked { value, .. } => expect_int(value),
        RuntimeEvidenceValue::Int(value) => Ok(*value),
        RuntimeEvidenceValue::BigInt(value) => value
            .parse()
            .map_err(|_| RuntimeEvidenceRunError::UnsupportedExpr("bigint outside int range")),
        value => Err(RuntimeEvidenceRunError::UnsupportedExpr(match value {
            RuntimeEvidenceValue::Float(_) => "float where int expected",
            RuntimeEvidenceValue::Str(_) => "string where int expected",
            RuntimeEvidenceValue::Bytes(_) => "bytes where int expected",
            RuntimeEvidenceValue::Bool(_) => "bool where int expected",
            _ => "non-int primitive argument",
        })),
    }
}

fn expect_float(value: &SharedValue) -> Result<f64, RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Marked { value, .. } => expect_float(value),
        RuntimeEvidenceValue::Float(value) => Ok(*value),
        RuntimeEvidenceValue::Int(value) => Ok(*value as f64),
        value => Err(RuntimeEvidenceRunError::UnsupportedExpr(match value {
            RuntimeEvidenceValue::Bytes(_) => "bytes where float expected",
            _ => "non-float primitive argument",
        })),
    }
}

fn expect_bool(value: &SharedValue) -> Result<bool, RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Marked { value, .. } => expect_bool(value),
        RuntimeEvidenceValue::Bool(value) => Ok(*value),
        _ => Err(RuntimeEvidenceRunError::UnsupportedExpr(
            "non-bool primitive argument",
        )),
    }
}

fn expect_list(value: &SharedValue) -> Result<&[SharedValue], RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Marked { value, .. } => expect_list(value),
        RuntimeEvidenceValue::List(values) => Ok(values),
        _ => Err(RuntimeEvidenceRunError::UnsupportedExpr(
            "non-list primitive argument",
        )),
    }
}

fn expect_bytes(value: &SharedValue) -> Result<&[u8], RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Marked { value, .. } => expect_bytes(value),
        RuntimeEvidenceValue::Bytes(bytes) => Ok(bytes),
        _ => Err(RuntimeEvidenceRunError::UnsupportedExpr(
            "non-bytes primitive argument",
        )),
    }
}

fn value_index(value: &SharedValue) -> Result<usize, RuntimeEvidenceRunError> {
    usize::try_from(expect_int(value)?)
        .map_err(|_| RuntimeEvidenceRunError::UnsupportedExpr("negative index"))
}

fn index_to_int(index: usize) -> Result<i64, RuntimeEvidenceRunError> {
    i64::try_from(index).map_err(|_| RuntimeEvidenceRunError::UnsupportedExpr("index too large"))
}

fn splice_shared_slice(
    values: &[SharedValue],
    start: usize,
    end: usize,
    insert: &[SharedValue],
) -> Result<Vec<SharedValue>, RuntimeEvidenceRunError> {
    if start > end || end > values.len() {
        return Err(RuntimeEvidenceRunError::UnsupportedExpr(
            "list splice range out of bounds",
        ));
    }
    let mut out = Vec::with_capacity(values.len() - (end - start) + insert.len());
    out.extend_from_slice(&values[..start]);
    out.extend_from_slice(insert);
    out.extend_from_slice(&values[end..]);
    Ok(out)
}

fn apply_list_view_raw(
    context: &PrimitiveContext,
    value: &SharedValue,
    stats: &mut RuntimeEvidenceRunStats,
) -> Result<RuntimeEvidenceValue, RuntimeEvidenceRunError> {
    stats.list_view_raw_calls += 1;
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
            stats.list_values_copied += values.len();
            let left = shared(RuntimeEvidenceValue::List(values[..split].to_vec()));
            let right = shared(RuntimeEvidenceValue::List(values[split..].to_vec()));
            Ok(RuntimeEvidenceValue::DataConstructor {
                def: DefId(constructors.node.0),
                payloads: vec![left, right],
            })
        }
    }
}

fn range_constructors(
    context: &PrimitiveContext,
    op: PrimitiveOp,
) -> Result<RangeConstructors, RuntimeEvidenceRunError> {
    context
        .range
        .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))
}

fn range_value(
    context: &PrimitiveContext,
    op: PrimitiveOp,
    start: usize,
    end: usize,
) -> Result<RuntimeEvidenceValue, RuntimeEvidenceRunError> {
    let constructors = range_constructors(context, op)?;
    let start = RuntimeEvidenceValue::DataConstructor {
        def: DefId(constructors.included.0),
        payloads: vec![shared(RuntimeEvidenceValue::Int(index_to_int(start)?))],
    };
    let end = RuntimeEvidenceValue::DataConstructor {
        def: DefId(constructors.excluded.0),
        payloads: vec![shared(RuntimeEvidenceValue::Int(index_to_int(end)?))],
    };
    Ok(RuntimeEvidenceValue::DataConstructor {
        def: DefId(constructors.within.0),
        payloads: vec![shared(start), shared(end)],
    })
}

fn normalized_range_value(
    context: &PrimitiveContext,
    op: PrimitiveOp,
    value: &SharedValue,
    len: usize,
) -> Result<(usize, usize), RuntimeEvidenceRunError> {
    let constructors = range_constructors(context, op)?;
    let RuntimeEvidenceValue::DataConstructor { def, payloads } = value.as_ref() else {
        return Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op));
    };
    if *def != DefId(constructors.within.0) {
        return Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op));
    }
    let Some((start_bound, end_bound)) = range_bound_pair(payloads) else {
        return Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op));
    };
    let start = range_start_bound(&constructors, start_bound, op)?;
    let end = range_end_bound(&constructors, end_bound, len, op)?;
    if start <= end && end <= len {
        return Ok((start, end));
    }
    Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op))
}

fn range_bound_pair(payloads: &[SharedValue]) -> Option<(&SharedValue, &SharedValue)> {
    match payloads {
        [start, end] => Some((start, end)),
        [payload] => {
            let RuntimeEvidenceValue::Tuple(bounds) = payload.as_ref() else {
                return None;
            };
            match bounds.as_slice() {
                [start, end] => Some((start, end)),
                _ => None,
            }
        }
        _ => None,
    }
}

fn range_start_bound(
    constructors: &RangeConstructors,
    value: &SharedValue,
    op: PrimitiveOp,
) -> Result<usize, RuntimeEvidenceRunError> {
    let RuntimeEvidenceValue::DataConstructor { def, payloads } = value.as_ref() else {
        return Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op));
    };
    if *def == DefId(constructors.unbounded.0) {
        return Ok(0);
    }
    if *def == DefId(constructors.included.0) {
        return single_index_payload(payloads, op);
    }
    if *def == DefId(constructors.excluded.0) {
        return single_index_payload(payloads, op)?
            .checked_add(1)
            .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op));
    }
    Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op))
}

fn range_end_bound(
    constructors: &RangeConstructors,
    value: &SharedValue,
    len: usize,
    op: PrimitiveOp,
) -> Result<usize, RuntimeEvidenceRunError> {
    let RuntimeEvidenceValue::DataConstructor { def, payloads } = value.as_ref() else {
        return Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op));
    };
    if *def == DefId(constructors.unbounded.0) {
        return Ok(len);
    }
    if *def == DefId(constructors.included.0) {
        return single_index_payload(payloads, op)?
            .checked_add(1)
            .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op));
    }
    if *def == DefId(constructors.excluded.0) {
        return single_index_payload(payloads, op);
    }
    Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op))
}

fn single_index_payload(
    payloads: &[SharedValue],
    op: PrimitiveOp,
) -> Result<usize, RuntimeEvidenceRunError> {
    match payloads {
        [payload] => value_index(payload),
        _ => Err(RuntimeEvidenceRunError::UnsupportedPrimitive(op)),
    }
}

fn grapheme_len(text: &str) -> usize {
    UnicodeSegmentation::graphemes(text, true).count()
}

fn string_index(text: &str, index: usize) -> Option<String> {
    UnicodeSegmentation::graphemes(text, true)
        .nth(index)
        .map(str::to_string)
}

fn string_index_range(text: &str, start: usize, end: usize) -> Option<String> {
    if start > end {
        return None;
    }
    let len = grapheme_len(text);
    if end > len {
        return None;
    }
    Some(
        UnicodeSegmentation::graphemes(text, true)
            .skip(start)
            .take(end - start)
            .collect(),
    )
}

fn string_splice(text: &str, start: usize, end: usize, insert: &str) -> Option<String> {
    let prefix = string_index_range(text, 0, start)?;
    let suffix = string_index_range(text, end, grapheme_len(text))?;
    Some(format!("{prefix}{insert}{suffix}"))
}

fn string_line_count(text: &str) -> usize {
    text.chars().filter(|ch| *ch == '\n').count() + 1
}

fn string_line_range(text: &str, line: usize) -> Option<(usize, usize)> {
    if line >= string_line_count(text) {
        return None;
    }
    let mut starts = vec![0usize];
    for (index, grapheme) in UnicodeSegmentation::graphemes(text, true).enumerate() {
        if grapheme.contains('\n') {
            starts.push(index + 1);
        }
    }
    let start = *starts.get(line)?;
    let end = starts
        .get(line + 1)
        .copied()
        .unwrap_or_else(|| grapheme_len(text));
    Some((start, end))
}

fn expect_str(value: &SharedValue) -> Result<&str, RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Marked { value, .. } => expect_str(value),
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
        RuntimeEvidenceValue::Marked { value, markers } => {
            let mut fields = record_fields(value.as_ref())?;
            for field in &mut fields {
                field.value = mark_runtime_value(field.value.clone(), markers);
            }
            Ok(fields)
        }
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

fn marker_paths(markers: &[GuardMarker]) -> Vec<Vec<String>> {
    markers.iter().map(|marker| marker.path.clone()).collect()
}

fn combined_markers(left: &[Vec<String>], right: &[Vec<String>]) -> Vec<Vec<String>> {
    let mut markers = Vec::with_capacity(left.len() + right.len());
    for marker in left.iter().chain(right) {
        if !markers.iter().any(|existing| existing == marker) {
            markers.push(marker.clone());
        }
    }
    markers
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

fn mark_runtime_value(value: SharedValue, markers: &[Vec<String>]) -> SharedValue {
    if markers.is_empty() || !runtime_value_needs_hygiene_mark(value.as_ref()) {
        return value;
    }
    mark_runtime_value_unchecked(value, markers)
}

fn mark_runtime_value_for_type(
    value: SharedValue,
    markers: &[Vec<String>],
    ty: &Type,
) -> SharedValue {
    if markers.is_empty() || !type_may_need_hygiene_mark(ty) {
        return value;
    }
    mark_runtime_value_unchecked(value, markers)
}

fn mark_runtime_value_unchecked(value: SharedValue, markers: &[Vec<String>]) -> SharedValue {
    if markers.is_empty() {
        return value;
    }
    match value.as_ref() {
        RuntimeEvidenceValue::Marked {
            value,
            markers: existing,
        } => shared(RuntimeEvidenceValue::Marked {
            value: value.clone(),
            markers: combined_markers(existing, markers),
        }),
        _ => shared(RuntimeEvidenceValue::Marked {
            value,
            markers: markers.to_vec(),
        }),
    }
}

fn runtime_value_needs_hygiene_mark(value: &RuntimeEvidenceValue) -> bool {
    match value {
        RuntimeEvidenceValue::Closure(_)
        | RuntimeEvidenceValue::RecursiveClosure { .. }
        | RuntimeEvidenceValue::EffectOp { .. }
        | RuntimeEvidenceValue::Continuation(_)
        | RuntimeEvidenceValue::Thunk(_)
        | RuntimeEvidenceValue::FunctionAdapter { .. } => true,
        RuntimeEvidenceValue::Marked { value, .. } => runtime_value_needs_hygiene_mark(value),
        RuntimeEvidenceValue::ConstructorFunction { args, .. }
        | RuntimeEvidenceValue::PrimitiveOp { args, .. } => args
            .iter()
            .any(|value| runtime_value_needs_hygiene_mark(value.as_ref())),
        RuntimeEvidenceValue::Tuple(_)
        | RuntimeEvidenceValue::List(_)
        | RuntimeEvidenceValue::Record(_)
        | RuntimeEvidenceValue::PolyVariant { .. }
        | RuntimeEvidenceValue::DataConstructor { .. } => false,
        RuntimeEvidenceValue::Int(_)
        | RuntimeEvidenceValue::BigInt(_)
        | RuntimeEvidenceValue::Float(_)
        | RuntimeEvidenceValue::Str(_)
        | RuntimeEvidenceValue::Bytes(_)
        | RuntimeEvidenceValue::Bool(_)
        | RuntimeEvidenceValue::Unit => false,
    }
}

fn type_may_need_hygiene_mark(ty: &Type) -> bool {
    match ty {
        Type::Fun { .. } | Type::Thunk { .. } => true,
        Type::Con { args, .. } | Type::Tuple(args) | Type::EffectRow(args) => {
            args.iter().any(type_may_need_hygiene_mark)
        }
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_may_need_hygiene_mark(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .any(|variant| variant.payloads.iter().any(type_may_need_hygiene_mark)),
        Type::Stack { inner, .. } => type_may_need_hygiene_mark(inner),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_may_need_hygiene_mark(left) || type_may_need_hygiene_mark(right)
        }
        Type::Any | Type::Never | Type::OpenVar(_) => false,
    }
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
        RuntimeEvidenceValue::Bytes(value) => format!("<bytes len={}>", value.len()),
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
        RuntimeEvidenceValue::Marked { value, .. } => format_value(value),
        RuntimeEvidenceValue::Closure(_) | RuntimeEvidenceValue::RecursiveClosure { .. } => {
            "<closure>".to_string()
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

fn format_float(value: f64) -> String {
    let text = value.to_string();
    if text.contains('.') || text.contains('e') || text.contains('E') {
        text
    } else {
        format!("{text}.0")
    }
}
