use std::cell::OnceCell;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::mem;
use std::rc::Rc;

use control_vm::{
    Block, ControlEffectEvidence, ControlEffectUseKind, ControlEvidenceProgram,
    ControlEvidenceRoute, DefId, Expr, ExprId, InstanceId, Pat, Program, RecordSpread, Root,
    SelectResolution, Stmt,
};
use list_tree::{ListTree, ListView};
use specialize::mono::{
    EffectiveThunkType, FunctionAdapterHygiene, GuardMarker, Lit, PrimitiveContext, PrimitiveOp,
    RangeConstructors, Type,
};

mod format;
mod plan;
mod text;
use crate::{EvidenceVmOperationExecutionPlan, EvidenceVmPlan};
use format::{format_float, format_value, format_values_with_labels};
use plan::RuntimeEvidenceProviderGrantPermission;
use plan::{
    RuntimeEvidenceOperationVisibility, RuntimeEvidenceProviderEnv, RuntimeEvidenceRunContext,
};
use text::{
    grapheme_len, string_index, string_index_range, string_line_count, string_line_range,
    string_splice,
};

#[derive(Debug, Clone, PartialEq)]
pub struct RuntimeEvidenceRunOutput {
    values: Vec<RuntimeEvidenceValue>,
    pub stdout: String,
    pub evidence_stats: RuntimeEvidenceRunStats,
}

impl RuntimeEvidenceRunOutput {
    pub fn roots_text_with_labels(&self, labels: Option<&poly::dump::DumpLabels>) -> String {
        format!(
            "run roots {}\n",
            format_values_with_labels(&self.values, labels)
        )
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RuntimeEvidenceRunStats {
    pub effect_calls: usize,
    pub direct_effect_calls: usize,
    pub plan_provider_slots: usize,
    pub plan_provider_candidates: usize,
    pub plan_env_provider_slots: usize,
    pub plan_env_provider_candidates: usize,
    pub plan_direct_candidates: usize,
    pub plan_effect_routes: usize,
    pub plan_direct_effect_routes: usize,
    pub plan_direct_abortive_effect_routes: usize,
    pub plan_direct_tail_resumptive_effect_routes: usize,
    pub runtime_provider_env_values: usize,
    pub runtime_provider_env_slots: usize,
    pub runtime_provider_env_candidates: usize,
    pub runtime_provider_env_reads: usize,
    pub runtime_provider_env_read_slots: usize,
    pub runtime_provider_env_read_candidates: usize,
    pub runtime_provider_env_route_lookups: usize,
    pub runtime_provider_env_route_hits: usize,
    pub runtime_provider_env_route_hit_direct_abortive: usize,
    pub runtime_provider_env_route_hit_direct_tail_resumptive: usize,
    pub runtime_provider_env_route_hit_yield_fallback: usize,
    pub runtime_provider_env_route_hit_blocked_fallback: usize,
    pub runtime_provider_env_route_hit_generic_fallback: usize,
    pub runtime_provider_env_route_hit_unhandled: usize,
    pub direct_tail_gate_fail_no_grant: usize,
    pub direct_tail_gate_fail_missing_grant: usize,
    pub direct_tail_gate_fail_scope_missing: usize,
    pub direct_tail_gate_fail_add_id_shadowed: usize,
    pub direct_tail_gate_fail_add_id_all_path: usize,
    pub direct_tail_gate_fail_add_id_own_path: usize,
    pub direct_tail_gate_fail_add_id_foreign_path: usize,
    pub direct_tail_gate_fail_handler_shadowed: usize,
    pub direct_tail_guarded_add_id_shadowed: usize,
    pub direct_tail_guarded_add_id_all_path: usize,
    pub direct_tail_guarded_add_id_own_path: usize,
    pub direct_tail_guarded_add_id_foreign_path: usize,
    pub permission_visibility_signals: usize,
    pub permission_visibility_identity: usize,
    pub permission_visibility_legacy_bridge: usize,
    pub permission_visibility_guard_mask: usize,
    pub permission_visibility_resume_delta: usize,
    pub permission_visibility_handler_boundary_mask: usize,
    pub permission_visibility_guard_and_boundary_mask: usize,
    pub permission_visibility_guard_without_boundary: usize,
    pub permission_visibility_boundary_without_guard: usize,
    pub permission_shadow_provider_boundary_pair: usize,
    pub permission_shadow_provider_boundary_pair_legacy_visible: usize,
    pub permission_shadow_provider_boundary_pair_permission_visible: usize,
    pub permission_shadow_provider_boundary_pair_match: usize,
    pub permission_shadow_provider_boundary_pair_mismatch: usize,
    pub permission_shadow_provider_boundary_pair_no_allowed_handler: usize,
    pub permission_provider_boundary_pair_fast_paths: usize,
    pub permission_provider_boundary_pair_fast_path_visible: usize,
    pub permission_provider_boundary_pair_fast_path_invisible: usize,
    pub permission_provider_boundary_pair_fast_path_no_allowed_handler: usize,
    pub permission_provider_boundary_pair_native_shadow: usize,
    pub permission_provider_boundary_pair_native_shadow_legacy_visible: usize,
    pub permission_provider_boundary_pair_native_shadow_native_visible: usize,
    pub permission_provider_boundary_pair_native_shadow_match: usize,
    pub permission_provider_boundary_pair_native_shadow_mismatch: usize,
    pub permission_provider_boundary_pair_native_shadow_no_allowed_handler: usize,
    pub provider_add_id_shortcut_attempts: usize,
    pub provider_add_id_shortcut_used: usize,
    pub provider_add_id_shortcut_fallback_carry_after_frame: usize,
    pub provider_add_id_shortcut_fallback_no_provider_permission: usize,
    pub provider_add_id_shortcut_full_scan_guard_visible_match: usize,
    pub provider_add_id_shortcut_full_scan_guard_visible_mismatch: usize,
    pub provider_add_id_shortcut_full_scan_extra_guards: usize,
    pub provider_add_id_shortcut_full_scan_extra_carried_guards: usize,
    pub expr_evals: usize,
    pub env_clones: usize,
    pub env_entries_cloned: usize,
    pub apply_value_calls: usize,
    pub apply_adapter_calls: usize,
    pub adapt_value_calls: usize,
    pub primitive_apply_calls: usize,
    pub forced_effect_call_fusions: usize,
    pub thunk_forces: usize,
    pub thunk_force_expr: usize,
    pub thunk_force_effect: usize,
    pub thunk_force_continuation: usize,
    pub thunk_force_value: usize,
    pub thunk_force_adapter: usize,
    pub continuation_appends: usize,
    pub continuation_owned_tail_appends: usize,
    pub continuation_append_steps: usize,
    pub request_continuation_appends: usize,
    pub request_continuation_owned_tail_appends: usize,
    pub request_continuation_then_appends: usize,
    pub direct_tail_continuation_appends: usize,
    pub direct_tail_continuation_owned_tail_appends: usize,
    pub direct_tail_continuation_then_appends: usize,
    pub continuation_append_blocked_by_marker_frame: usize,
    pub continuation_append_blocked_by_provider_env: usize,
    pub continuation_append_blocked_by_rc_shared: usize,
    pub request_continuation_append_blocked_by_marker_frame: usize,
    pub request_continuation_append_blocked_by_provider_env: usize,
    pub request_continuation_append_blocked_by_rc_shared: usize,
    pub direct_tail_continuation_append_blocked_by_marker_frame: usize,
    pub direct_tail_continuation_append_blocked_by_provider_env: usize,
    pub direct_tail_continuation_append_blocked_by_rc_shared: usize,
    pub continuation_resume_steps: usize,
    pub continuation_resume_then_steps: usize,
    pub continuation_resume_then_first_marker_frame: usize,
    pub continuation_resume_then_first_provider_env: usize,
    pub continuation_resume_then_first_other: usize,
    pub continuation_resume_then_second_marker_frame: usize,
    pub continuation_resume_then_second_provider_env: usize,
    pub continuation_resume_then_second_other: usize,
    pub continuation_resume_then_plain: usize,
    pub continuation_resume_force_steps: usize,
    pub continuation_resume_apply_steps: usize,
    pub continuation_resume_adapter_steps: usize,
    pub continuation_resume_case_steps: usize,
    pub continuation_resume_catch_steps: usize,
    pub continuation_resume_marker_steps: usize,
    pub continuation_resume_marker_identity_fast_paths: usize,
    pub continuation_resume_marker_empty_markers: usize,
    pub continuation_resume_marker_with_active_add_id: usize,
    pub continuation_resume_marker_with_handler_path: usize,
    pub continuation_resume_marker_result_value: usize,
    pub continuation_resume_marker_result_direct_tail: usize,
    pub continuation_resume_marker_result_direct_tail_provider_permission: usize,
    pub continuation_resume_marker_result_direct_tail_provider_boundary_pair: usize,
    pub continuation_resume_marker_result_legacy_signal: usize,
    pub continuation_resume_marker_result_error: usize,
    pub continuation_resume_provider_steps: usize,
    pub continuation_resume_aggregate_steps: usize,
    pub continuation_resume_select_steps: usize,
    pub continuation_resume_block_steps: usize,
    pub continuation_resume_ref_set_steps: usize,
    pub request_whole_continuation_appends: usize,
    pub request_continuation_steps: usize,
    pub catch_body_checks: usize,
    pub marker_frame_entries: usize,
    pub marker_frame_markers: usize,
    pub marker_frame_add_id_markers: usize,
    pub marker_frame_active_add_id_markers: usize,
    pub marker_frame_frame_only_entries: usize,
    pub marker_frame_no_active_add_id_no_handler_entries: usize,
    pub marker_frame_expr_entries: usize,
    pub marker_frame_scoped_apply_entries: usize,
    pub marker_frame_marked_apply_entries: usize,
    pub marker_frame_adapter_entries: usize,
    pub marker_frame_continuation_resume_entries: usize,
    pub marker_frame_marked_force_entries: usize,
    pub marked_force_value_fast_paths: usize,
    pub marked_force_fallback_expr_thunks: usize,
    pub marked_force_fallback_effect_thunks: usize,
    pub marked_force_fallback_continuation_thunks: usize,
    pub marked_force_fallback_adapter_thunks: usize,
    pub marked_force_fallback_other: usize,
    pub marked_force_active_add_id_markers: usize,
    pub marked_force_carry_after_frame_markers: usize,
    pub active_marker_plan_pushes: usize,
    pub active_marker_plan_dedupes: usize,
    pub active_add_id_scans: usize,
    pub active_add_id_path_candidates: usize,
    pub active_add_id_path_rejects: usize,
    pub active_add_id_entry_except_rejects: usize,
    pub active_add_id_already_carried_rejects: usize,
    pub active_add_id_hits: usize,
    pub function_call_marker_plans: usize,
    pub function_call_marker_inputs: usize,
    pub function_call_marker_outputs: usize,
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
    List(ListTree<SharedValue>),
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
        provider_env: RuntimeEvidenceProviderEnv,
    },
    Marked {
        value: SharedValue,
        markers: Rc<[EvidenceValueMarker]>,
    },
    Closure(Rc<RuntimeEvidenceClosure>),
    RecursiveClosure {
        def: DefId,
        closure: Rc<RuntimeEvidenceClosure>,
    },
    EffectOp {
        expr: ExprId,
        path: Rc<[String]>,
    },
    Continuation(EvidenceContinuation),
    Thunk(Rc<RuntimeEvidenceThunk>),
}

#[derive(Debug, Clone, PartialEq)]
enum RuntimeEvidenceExpr {
    Value(SharedValue),
    NullaryPrimitive {
        op: PrimitiveOp,
        context: PrimitiveContext,
    },
    Local {
        slot: EnvSlot,
        def: DefId,
    },
    Instance(InstanceId),
    Alias(ExprId),
    MakeThunk {
        body: ExprId,
        provider_expr: ExprId,
        needs_hygiene_mark: bool,
    },
    Lambda {
        param: Rc<Pat>,
        body: ExprId,
        provider_expr: ExprId,
    },
    FunctionAdapter {
        source: Type,
        target: Type,
        function: ExprId,
        hygiene: FunctionAdapterHygiene,
        provider_expr: ExprId,
    },
    ForceThunk {
        target_value_is_thunk: bool,
        thunk: ExprId,
    },
    ForceEffectCall {
        target_value_is_thunk: bool,
        site: ExprId,
        effect: ExprId,
        path: Rc<[String]>,
        arg: ExprId,
    },
    MarkerFrame {
        path: Rc<[String]>,
        body: ExprId,
    },
    Apply {
        site: ExprId,
        callee: ExprId,
        arg: ExprId,
    },
    RefSet {
        reference: ExprId,
        value: ExprId,
    },
    Tuple(Rc<[ExprId]>),
    Record {
        fields: Rc<[control_vm::RecordField]>,
        spread: RecordSpread<ExprId>,
    },
    PolyVariant {
        tag: String,
        payloads: Rc<[ExprId]>,
    },
    Select {
        base: ExprId,
        name: String,
        resolution: Option<SelectResolution>,
    },
    Case {
        expr: ExprId,
        scrutinee: ExprId,
    },
    Catch {
        expr: ExprId,
        body: ExprId,
    },
    Block {
        stmts: Rc<[Stmt]>,
        tail: Option<ExprId>,
    },
}

#[derive(Debug, Clone, PartialEq)]
struct RuntimeEvidenceValueField {
    name: String,
    value: SharedValue,
}

#[derive(Debug, Clone, PartialEq)]
struct RuntimeEvidenceClosure {
    param: Rc<Pat>,
    body: ExprId,
    env: Env,
    provider_env: RuntimeEvidenceProviderEnv,
}

#[derive(Debug, Clone, PartialEq)]
enum RuntimeEvidenceThunk {
    Expr {
        body: ExprId,
        env: Env,
        provider_env: RuntimeEvidenceProviderEnv,
        needs_hygiene_mark: bool,
    },
    Effect {
        path: Rc<[String]>,
        payload: SharedValue,
        route: EvidenceEffectRoute,
        evidence: EffectThunkEvidence,
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
enum EvidenceContinuation {
    Identity,
    Frame(Rc<EvidenceContinuationFrame>),
}

#[derive(Debug, Clone, PartialEq)]
enum EvidenceContinuationFrame {
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
        ret_markers: Vec<EvidenceValueMarker>,
        source_ret: Type,
        target_ret: Type,
        next: EvidenceContinuation,
    },
    ApplyAdapterResult {
        ret_markers: Vec<EvidenceValueMarker>,
        source_ret: Type,
        target_ret: Type,
        next: EvidenceContinuation,
    },
    CaseScrutinee {
        arms: Rc<[control_vm::CaseArm]>,
        env: Env,
        next: EvidenceContinuation,
    },
    CatchBody {
        catch_expr: ExprId,
        arms: Rc<[control_vm::CatchArm]>,
        env: Env,
        next: EvidenceContinuation,
    },
    MarkerFrame {
        markers: Rc<[EvidenceValueMarker]>,
        activate_add_ids: bool,
        handler_path: Option<Vec<String>>,
        next: EvidenceContinuation,
    },
    ProviderEnv {
        provider_env: RuntimeEvidenceProviderEnv,
        next: EvidenceContinuation,
    },
    TupleItems {
        values: Vec<SharedValue>,
        rest: Rc<[ExprId]>,
        env: Env,
        next: EvidenceContinuation,
    },
    RecordSpread {
        fields: Rc<[control_vm::RecordField]>,
        env: Env,
        next: EvidenceContinuation,
    },
    RecordFields {
        values: Vec<RuntimeEvidenceValueField>,
        rest: Rc<[control_vm::RecordField]>,
        env: Env,
        next: EvidenceContinuation,
    },
    PolyVariantPayloads {
        tag: String,
        values: Vec<SharedValue>,
        rest: Rc<[ExprId]>,
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
        rest: Rc<[Stmt]>,
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
enum EvidenceResolvedRouteOrigin {
    StaticDirect,
    ProviderGrant(EvidenceProviderGrant),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceRouteCert {
    None,
    StaticDirect,
    ProviderGrant(EvidenceProviderGrantId),
}

impl EvidenceRouteCert {
    fn provider_grant_id(self) -> Option<EvidenceProviderGrantId> {
        match self {
            Self::ProviderGrant(id) => Some(id),
            Self::None | Self::StaticDirect => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EvidenceProviderScopeId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EvidenceProviderGrantId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EvidenceProviderHygieneBaseline {
    marker_plan_len: usize,
    active_add_id_len: usize,
    active_handler_frame_len: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EvidenceProviderGrant {
    demand_slot_id: u32,
    provider_slot_id: u32,
    handler_id: u32,
    scope_id: EvidenceProviderScopeId,
    hygiene_baseline: EvidenceProviderHygieneBaseline,
}

impl EvidenceProviderGrant {
    fn gate(&self) -> EvidenceProviderGrantGate {
        EvidenceProviderGrantGate {
            scope_id: self.scope_id,
            hygiene_baseline: self.hygiene_baseline,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EvidenceProviderGrantGate {
    scope_id: EvidenceProviderScopeId,
    hygiene_baseline: EvidenceProviderHygieneBaseline,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EffectThunkEvidence {
    route_cert: EvidenceRouteCert,
    visibility: Option<RuntimeEvidenceOperationVisibility>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ProviderGrantPathGateFail {
    NoGrant,
    MissingGrant,
    ScopeMissing,
    AddIdShadowed(EvidenceProviderShadowedAddId),
    HandlerShadowed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ActiveAddIdMatchKind {
    AllPath,
    OwnPath,
    ForeignPath,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EvidenceProviderShadowedAddId {
    marker: EvidenceActiveAddIdMarker,
    kind: ActiveAddIdMatchKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EvidenceResolvedEffectRoute {
    route: EvidenceEffectRoute,
    origin: Option<EvidenceResolvedRouteOrigin>,
    visibility: Option<RuntimeEvidenceOperationVisibility>,
}

fn merge_operation_visibility(
    static_visibility: Option<RuntimeEvidenceOperationVisibility>,
    provider_visibility: Option<RuntimeEvidenceOperationVisibility>,
) -> Option<RuntimeEvidenceOperationVisibility> {
    // Provider grants are runtime evidence selected from the active provider env, so they are
    // more specific than the static operation visibility attached to the operation object.
    provider_visibility.or(static_visibility)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceEffectRoute {
    Direct {
        handler: ExprId,
        resumptive: bool,
        execution: EvidenceVmOperationExecutionPlan,
        // Provider-env routes still need the generic request path: returned effect thunks rely on
        // that boundary to keep call evidence and handler visibility aligned.
        request_free_yield: bool,
    },
    Unhandled,
}

impl EvidenceEffectRoute {
    fn is_direct(self) -> bool {
        matches!(self, Self::Direct { .. })
    }

    fn is_direct_abortive(self) -> bool {
        matches!(
            self,
            Self::Direct {
                execution: EvidenceVmOperationExecutionPlan::DirectAbortive,
                ..
            }
        )
    }

    fn is_direct_tail_resumptive(self) -> bool {
        matches!(
            self,
            Self::Direct {
                execution: EvidenceVmOperationExecutionPlan::DirectTailResumptive,
                ..
            }
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct EvidenceGuardId(u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum EvidenceValueMarker {
    Frame { id: EvidenceGuardId },
    AddId(Rc<EvidenceAddIdMarker>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceMarkerFrameSource {
    Expr,
    ScopedApply,
    MarkedApply,
    Adapter,
    ContinuationResume,
    MarkedForce,
}

// Function-call markers are not an implementation detail of apply/force.
// They are the hygiene boundary that must be closed on every result shape.
#[derive(Debug, Clone, PartialEq, Eq)]
struct EvidenceCallBoundary {
    source: EvidenceMarkerFrameSource,
    markers: Rc<[EvidenceValueMarker]>,
    activate_add_ids: bool,
    handler_path: Option<Vec<String>>,
}

impl EvidenceCallBoundary {
    fn new(
        source: EvidenceMarkerFrameSource,
        markers: Rc<[EvidenceValueMarker]>,
        activate_add_ids: bool,
        handler_path: Option<Vec<String>>,
    ) -> Self {
        Self {
            source,
            markers,
            activate_add_ids,
            handler_path,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceCallBoundaryBypassCert {
    NoActiveMarkerPlan,
    NoFunctionCallMarkers,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceContinuationAppendSource {
    Request,
    DirectTail,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceContinuationAppendBlocker {
    MarkerFrame,
    ProviderEnv,
    RcShared,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceContinuationBoundaryKind {
    Identity,
    MarkerFrame,
    ProviderEnv,
    Other,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct EvidenceAddIdMarker {
    id: EvidenceGuardId,
    path: Rc<[String]>,
    depth: u32,
    guard_own_path: bool,
    guard_foreign_path: bool,
    carry_after_frame: bool,
    preserve_own_on_resume: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EvidenceActiveFrame {
    id: EvidenceGuardId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EvidenceActiveHandlerFrame {
    frame_index: usize,
    id: EvidenceGuardId,
    path: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EvidenceActiveAddIdMarker {
    marker: Rc<EvidenceAddIdMarker>,
    entry_frame_len: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeEvidenceProviderFrame {
    scope_id: EvidenceProviderScopeId,
    provider_env: RuntimeEvidenceProviderEnv,
    hygiene_baseline: EvidenceProviderHygieneBaseline,
}

impl RuntimeEvidenceProviderFrame {
    fn new(
        scope_id: EvidenceProviderScopeId,
        provider_env: RuntimeEvidenceProviderEnv,
        marker_plan_len_at_entry: usize,
        active_add_id_len_at_entry: usize,
        active_handler_frame_len_at_entry: usize,
    ) -> Self {
        Self {
            scope_id,
            provider_env,
            hygiene_baseline: EvidenceProviderHygieneBaseline {
                marker_plan_len: marker_plan_len_at_entry,
                active_add_id_len: active_add_id_len_at_entry,
                active_handler_frame_len: active_handler_frame_len_at_entry,
            },
        }
    }

    fn is_unshadowed(
        &self,
        marker_plan_len: usize,
        active_add_id_len: usize,
        active_handler_frame_len: usize,
    ) -> bool {
        self.hygiene_baseline.marker_plan_len == marker_plan_len
            && self.hygiene_baseline.active_add_id_len == active_add_id_len
            && self.hygiene_baseline.active_handler_frame_len == active_handler_frame_len
    }

    fn matches_gate(&self, gate: EvidenceProviderGrantGate) -> bool {
        self.scope_id == gate.scope_id && self.hygiene_baseline == gate.hygiene_baseline
    }

    fn gate_is_unshadowed(
        &self,
        gate: EvidenceProviderGrantGate,
        marker_plan_len: usize,
        active_add_id_len: usize,
        active_handler_frame_len: usize,
    ) -> bool {
        self.matches_gate(gate)
            && self.is_unshadowed(marker_plan_len, active_add_id_len, active_handler_frame_len)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeEvidenceProviderView<'a> {
    scope_id: EvidenceProviderScopeId,
    provider_env: &'a RuntimeEvidenceProviderEnv,
    hygiene_baseline: EvidenceProviderHygieneBaseline,
}

struct EvidenceActiveMarkerPlan {
    markers: Rc<[EvidenceValueMarker]>,
    function_call_markers: OnceCell<Rc<[EvidenceValueMarker]>>,
}

impl EvidenceActiveMarkerPlan {
    fn new(markers: Rc<[EvidenceValueMarker]>) -> Self {
        Self {
            markers,
            function_call_markers: OnceCell::new(),
        }
    }

    fn function_call_markers(&self) -> Rc<[EvidenceValueMarker]> {
        self.function_call_markers
            .get_or_init(|| markers_for_function_call_shared(&self.markers))
            .clone()
    }
}

#[cfg(debug_assertions)]
#[derive(Debug, Clone, Default)]
struct ActiveAddIdIndex {
    entries: Vec<ActiveAddIdIndexEntry>,
    all_path: Vec<usize>,
    own_by_path: HashMap<Vec<String>, Vec<usize>>,
    foreign_all: Vec<usize>,
    foreign_excluded_by_path: HashMap<Vec<String>, Vec<usize>>,
}

#[cfg(debug_assertions)]
#[derive(Debug, Clone)]
enum ActiveAddIdIndexEntry {
    AllPath,
    OwnPath(Vec<String>),
    ForeignPath(Vec<String>),
    Never,
}

#[cfg(debug_assertions)]
impl ActiveAddIdIndex {
    fn push(&mut self, index: usize, marker: &EvidenceActiveAddIdMarker) {
        match (
            marker.marker.guard_own_path,
            marker.marker.guard_foreign_path,
        ) {
            (true, true) => {
                self.entries.push(ActiveAddIdIndexEntry::AllPath);
                self.all_path.push(index);
            }
            (true, false) => {
                let path = marker.marker.path.to_vec();
                self.entries
                    .push(ActiveAddIdIndexEntry::OwnPath(path.clone()));
                self.own_by_path.entry(path).or_default().push(index);
            }
            (false, true) => {
                let path = marker.marker.path.to_vec();
                self.entries
                    .push(ActiveAddIdIndexEntry::ForeignPath(path.clone()));
                self.foreign_all.push(index);
                self.foreign_excluded_by_path
                    .entry(path)
                    .or_default()
                    .push(index);
            }
            (false, false) => self.entries.push(ActiveAddIdIndexEntry::Never),
        }
    }

    fn truncate(&mut self, len: usize) {
        while self.entries.len() > len {
            let index = self.entries.len() - 1;
            match self.entries.pop().expect("active add-id index entry") {
                ActiveAddIdIndexEntry::AllPath => {
                    let popped = self.all_path.pop();
                    debug_assert_eq!(popped, Some(index));
                }
                ActiveAddIdIndexEntry::OwnPath(path) => {
                    pop_index_map_entry(&mut self.own_by_path, &path, index);
                }
                ActiveAddIdIndexEntry::ForeignPath(path) => {
                    let popped = self.foreign_all.pop();
                    debug_assert_eq!(popped, Some(index));
                    pop_index_map_entry(&mut self.foreign_excluded_by_path, &path, index);
                }
                ActiveAddIdIndexEntry::Never => {}
            }
        }
    }

    fn candidates_for(&self, request_path: &[String]) -> Vec<usize> {
        let mut candidates = self.all_path.clone();
        for prefix_len in 0..=request_path.len() {
            let prefix = &request_path[..prefix_len];
            if let Some(indices) = self.own_by_path.get(prefix) {
                candidates.extend_from_slice(indices);
            }
        }

        let mut excluded_foreign = Vec::new();
        for prefix_len in 0..=request_path.len() {
            let prefix = &request_path[..prefix_len];
            if let Some(indices) = self.foreign_excluded_by_path.get(prefix) {
                excluded_foreign.extend_from_slice(indices);
            }
        }
        excluded_foreign.sort_unstable();
        excluded_foreign.dedup();
        candidates.extend(
            self.foreign_all
                .iter()
                .copied()
                .filter(|index| excluded_foreign.binary_search(index).is_err()),
        );

        candidates.sort_unstable();
        candidates.dedup();
        candidates
    }
}

#[cfg(debug_assertions)]
fn pop_index_map_entry(map: &mut HashMap<Vec<String>, Vec<usize>>, path: &[String], index: usize) {
    let Some(indices) = map.get_mut(path) else {
        debug_assert!(false, "missing active add-id index bucket");
        return;
    };
    let popped = indices.pop();
    debug_assert_eq!(popped, Some(index));
    if indices.is_empty() {
        map.remove(path);
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EvidenceCarriedGuard {
    id: EvidenceGuardId,
    entry_frame_len: usize,
    exposed_guard_ids: Vec<EvidenceGuardId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct EvidenceSignalHygiene {
    guard_ids: Vec<EvidenceGuardId>,
    carried_guards: Vec<EvidenceCarriedGuard>,
    handler_boundary: Option<EvidenceHandlerBoundary>,
    permission_visibility: EvidenceSignalPermissionVisibility,
}

impl EvidenceSignalHygiene {
    fn new() -> Self {
        Self::default()
    }

    fn from_request(request: &mut EvidenceRequest) -> Self {
        mem::take(&mut request.hygiene)
    }

    fn apply_to_request(self, request: &mut EvidenceRequest) {
        request.hygiene = self;
    }

    fn push_guard_id(&mut self, id: EvidenceGuardId) -> bool {
        let pushed = push_unique_guard(&mut self.guard_ids, id);
        if pushed {
            self.permission_visibility.record_guard_mask();
        }
        pushed
    }

    fn set_handler_boundary(&mut self, handler_boundary: EvidenceHandlerBoundary) {
        self.permission_visibility.record_handler_boundary_mask();
        self.handler_boundary = Some(handler_boundary);
    }

    fn with_operation_visibility(
        mut self,
        visibility: Option<RuntimeEvidenceOperationVisibility>,
    ) -> Self {
        self.permission_visibility.set_base(visibility);
        self
    }

    fn push_carried_guard(&mut self, guard: EvidenceCarriedGuard) {
        self.permission_visibility.record_resume_delta();
        self.carried_guards.push(guard);
    }

    fn permission_shadow_kind(&self) -> Option<EvidencePermissionShadowKind> {
        self.permission_visibility.shadow_kind()
    }

    fn provider_grant_permission(&self) -> Option<RuntimeEvidenceProviderGrantPermission> {
        self.permission_visibility.base?.provider_grant_permission()
    }

    #[cfg(debug_assertions)]
    fn operation_visibility(&self) -> Option<RuntimeEvidenceOperationVisibility> {
        self.permission_visibility.base
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct EvidenceSignalPermissionVisibility {
    base: Option<RuntimeEvidenceOperationVisibility>,
    transform: EvidenceSignalPermissionTransform,
}

impl EvidenceSignalPermissionVisibility {
    fn set_base(&mut self, base: Option<RuntimeEvidenceOperationVisibility>) {
        self.base = base;
    }

    fn record_guard_mask(&mut self) {
        self.transform.guard_mask = true;
    }

    fn record_resume_delta(&mut self) {
        self.transform.resume_delta = true;
    }

    fn record_handler_boundary_mask(&mut self) {
        self.transform.handler_boundary_mask = true;
    }

    fn shadow_kind(&self) -> Option<EvidencePermissionShadowKind> {
        let visibility = self.base?;
        if visibility.legacy_guard_bridge() {
            return None;
        }
        if self.transform.is_identity() {
            return Some(EvidencePermissionShadowKind::Direct);
        }
        if self.transform.is_guard_boundary_pair()
            && let Some(permission) = visibility.provider_grant_permission()
        {
            return Some(EvidencePermissionShadowKind::ProviderGrantBoundaryPair(
                permission,
            ));
        }
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidencePermissionShadowKind {
    Direct,
    ProviderGrantBoundaryPair(RuntimeEvidenceProviderGrantPermission),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidencePermissionVisibleResult {
    NoAllowedHandler,
    Visible(Option<bool>),
}

impl EvidencePermissionVisibleResult {
    fn visible(self) -> Option<bool> {
        match self {
            Self::NoAllowedHandler => None,
            Self::Visible(visible) => visible,
        }
    }

    fn no_allowed_handler(self) -> bool {
        matches!(self, Self::NoAllowedHandler)
    }
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidencePermissionVisibleDecision {
    NotApplicable,
    Handled(EvidencePermissionVisibleResult),
}

#[derive(Debug, Clone, Copy)]
struct EvidenceGuardBoundaryExposure<'a> {
    handler_boundary: Option<&'a EvidenceHandlerBoundary>,
    guard_ids: &'a [EvidenceGuardId],
    carried_guards: &'a [EvidenceCarriedGuard],
}

impl<'a> EvidenceGuardBoundaryExposure<'a> {
    fn from_hygiene(hygiene: &'a EvidenceSignalHygiene) -> Self {
        Self {
            handler_boundary: hygiene.handler_boundary.as_ref(),
            guard_ids: &hygiene.guard_ids,
            carried_guards: &hygiene.carried_guards,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct EvidenceSignalPermissionTransform {
    guard_mask: bool,
    resume_delta: bool,
    handler_boundary_mask: bool,
}

impl EvidenceSignalPermissionTransform {
    fn is_identity(self) -> bool {
        !self.guard_mask && !self.resume_delta && !self.handler_boundary_mask
    }

    fn is_guard_boundary_pair(self) -> bool {
        self.guard_mask && self.handler_boundary_mask && !self.resume_delta
    }

    fn is_guard_only(self) -> bool {
        self.guard_mask && !self.handler_boundary_mask && !self.resume_delta
    }

    fn is_boundary_only(self) -> bool {
        !self.guard_mask && self.handler_boundary_mask && !self.resume_delta
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EvidenceHandlerBoundary {
    id: EvidenceGuardId,
    path: Vec<String>,
    blocked: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EvidenceResumeMarkerPlan {
    markers: Rc<[EvidenceValueMarker]>,
    activate_add_ids: bool,
    handler_path: Option<Vec<String>>,
}

impl EvidenceResumeMarkerPlan {
    fn attach(self, continuation: EvidenceContinuation) -> EvidenceContinuation {
        EvidenceContinuation::marker_frame(
            self.markers,
            self.activate_add_ids,
            self.handler_path,
            continuation,
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceGuardSkip {
    Preserve(EvidenceGuardId),
}

#[derive(Debug, Clone, PartialEq)]
struct EvidenceRequest {
    path: Rc<[String]>,
    payload: SharedValue,
    route: EvidenceEffectRoute,
    hygiene: EvidenceSignalHygiene,
    continuation: EvidenceContinuation,
}

#[derive(Debug, Clone, PartialEq)]
enum EvidenceEffectSignal {
    GenericRequest(EvidenceRequest),
    DirectAbortive(EvidenceDirectAbortive),
    DirectTailResumptive(EvidenceDirectTailResumptive),
    RoutedYield(EvidenceRoutedYield),
}

impl EvidenceEffectSignal {
    fn from_request(request: EvidenceRequest) -> Self {
        Self::GenericRequest(request)
    }
}

#[derive(Debug, Clone, PartialEq)]
struct EvidenceDirectAbortive {
    handler: ExprId,
    path: Rc<[String]>,
    payload: SharedValue,
    close_cert: EvidenceDirectAbortiveCloseCert,
}

impl EvidenceDirectAbortive {
    fn static_handler(handler: ExprId, path: Rc<[String]>, payload: SharedValue) -> Self {
        Self {
            handler,
            path,
            payload,
            close_cert: EvidenceDirectAbortiveCloseCert::StaticAbortiveHandler,
        }
    }

    fn close_cert(&self) -> EvidenceDirectAbortiveCloseCert {
        self.close_cert
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceDirectAbortiveCloseCert {
    StaticAbortiveHandler,
}

#[derive(Debug, Clone, PartialEq)]
struct EvidenceDirectTailResumptive {
    handler: ExprId,
    path: Rc<[String]>,
    payload: SharedValue,
    hygiene: EvidenceSignalHygiene,
    continuation: EvidenceContinuation,
}

impl EvidenceDirectTailResumptive {
    fn with_hygiene(
        handler: ExprId,
        path: Rc<[String]>,
        payload: SharedValue,
        hygiene: EvidenceSignalHygiene,
    ) -> Self {
        Self {
            handler,
            path,
            payload,
            hygiene,
            continuation: EvidenceContinuation::identity(),
        }
    }

    fn with_handler_boundary(mut self, handler_boundary: EvidenceHandlerBoundary) -> Self {
        self.hygiene.set_handler_boundary(handler_boundary);
        self
    }

    fn close_provider_env(mut self, provider_env: RuntimeEvidenceProviderEnv) -> Self {
        self.continuation = EvidenceContinuation::provider_env(provider_env, self.continuation);
        self
    }

    fn close_marker_frame(
        mut self,
        markers: Rc<[EvidenceValueMarker]>,
        resume_plan: Option<EvidenceResumeMarkerPlan>,
    ) -> Self {
        self.payload = mark_runtime_value_shared(self.payload, markers);
        if let Some(plan) = resume_plan {
            self.continuation = plan.attach(self.continuation);
        }
        self
    }

    fn into_request(self, route: EvidenceEffectRoute) -> EvidenceRequest {
        EvidenceRequest {
            path: self.path,
            payload: self.payload,
            route,
            hygiene: self.hygiene,
            continuation: self.continuation,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct EvidenceRoutedYield {
    handler: ExprId,
    request: EvidenceRequest,
}

impl EvidenceRoutedYield {
    fn from_request(handler: ExprId, request: EvidenceRequest) -> Self {
        Self { handler, request }
    }

    fn request(&self) -> &EvidenceRequest {
        &self.request
    }

    fn with_handler_boundary(mut self, handler_boundary: EvidenceHandlerBoundary) -> Self {
        self.request.hygiene.set_handler_boundary(handler_boundary);
        self
    }

    fn close_provider_env(mut self, provider_env: RuntimeEvidenceProviderEnv) -> Self {
        self.request.continuation =
            EvidenceContinuation::provider_env(provider_env, self.request.continuation);
        self
    }

    fn close_marker_frame(
        mut self,
        markers: Rc<[EvidenceValueMarker]>,
        resume_plan: Option<EvidenceResumeMarkerPlan>,
    ) -> Self {
        self.request.payload = mark_runtime_value_shared(self.request.payload, markers);
        if let Some(plan) = resume_plan {
            self.request.continuation = plan.attach(self.request.continuation);
        }
        self
    }

    fn append_continuation(
        mut self,
        tail: EvidenceContinuation,
        stats: &mut RuntimeEvidenceRunStats,
    ) -> Self {
        self.request = self.request.append_continuation(tail, stats);
        self
    }

    fn into_request(self) -> EvidenceRequest {
        self.request
    }
}

#[derive(Debug, Clone, PartialEq)]
enum EvidenceEvalResult {
    Value(SharedValue),
    Effect(EvidenceEffectSignal),
}

impl EvidenceEvalResult {
    fn request(request: EvidenceRequest) -> Self {
        Self::Effect(EvidenceEffectSignal::from_request(request))
    }

    fn direct_abortive(call: EvidenceDirectAbortive) -> Self {
        Self::Effect(EvidenceEffectSignal::DirectAbortive(call))
    }

    fn direct_tail_resumptive(call: EvidenceDirectTailResumptive) -> Self {
        Self::Effect(EvidenceEffectSignal::DirectTailResumptive(call))
    }

    fn routed_yield(call: EvidenceRoutedYield) -> Self {
        Self::Effect(EvidenceEffectSignal::RoutedYield(call))
    }
}

type SharedValue = Rc<RuntimeEvidenceValue>;

#[cfg(debug_assertions)]
const PROVIDER_ADD_ID_SHORTCUT_FULL_SCAN_VERIFY_LIMIT: usize = 1024;

#[derive(Debug, Clone, Default, PartialEq)]
struct Env {
    head: Option<Rc<EnvEntry>>,
    depth: usize,
}

#[derive(Debug, Clone, PartialEq)]
struct EnvEntry {
    slot: EnvSlot,
    value: SharedValue,
    parent: Option<Rc<EnvEntry>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EnvSlot(usize);

impl From<DefId> for EnvSlot {
    fn from(def: DefId) -> Self {
        Self(def.0 as usize)
    }
}

impl Env {
    fn new() -> Self {
        Self::default()
    }

    fn get_slot(&self, slot: EnvSlot) -> Option<SharedValue> {
        let mut entry = self.head.as_deref();
        while let Some(current) = entry {
            if current.slot == slot {
                return Some(current.value.clone());
            }
            entry = current.parent.as_deref();
        }
        None
    }

    fn insert_slot(&mut self, slot: EnvSlot, value: SharedValue) {
        self.head = Some(Rc::new(EnvEntry {
            slot,
            value,
            parent: self.head.clone(),
        }));
        self.depth += 1;
    }

    fn len(&self) -> usize {
        self.depth
    }
}

fn clone_env_for_stats(env: &Env, stats: &mut RuntimeEvidenceRunStats) -> Env {
    stats.env_clones += 1;
    stats.env_entries_cloned += env.len();
    env.clone()
}

impl EvidenceContinuation {
    fn identity() -> Self {
        Self::Identity
    }

    fn frame(&self) -> Option<&EvidenceContinuationFrame> {
        match self {
            Self::Identity => None,
            Self::Frame(frame) => Some(frame.as_ref()),
        }
    }

    fn into_frame(self) -> Option<EvidenceContinuationFrame> {
        match self {
            Self::Identity => None,
            Self::Frame(frame) => Some(match Rc::try_unwrap(frame) {
                Ok(frame) => frame,
                Err(frame) => frame.as_ref().clone(),
            }),
        }
    }

    fn force_thunk(target_value_is_thunk: bool, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::ForceThunk {
            target_value_is_thunk,
            next,
        }))
    }

    fn force_value_if_thunk(next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::ForceValueIfThunk {
            next,
        }))
    }

    fn apply_callee(site: Option<ExprId>, arg: ExprId, env: Env, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::ApplyCallee {
            site,
            arg,
            env,
            next,
        }))
    }

    fn apply_arg(site: Option<ExprId>, callee: SharedValue, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::ApplyArg {
            site,
            callee,
            next,
        }))
    }

    fn apply_forced_callee(site: Option<ExprId>, arg: SharedValue, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::ApplyForcedCallee {
            site,
            arg,
            next,
        }))
    }

    fn adapt_value(source: Type, target: Type, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::AdaptValue {
            source,
            target,
            next,
        }))
    }

    fn wrap_thunk_value(next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::WrapThunkValue { next }))
    }

    fn apply_adapter_arg(
        function: SharedValue,
        ret_markers: Vec<EvidenceValueMarker>,
        source_ret: Type,
        target_ret: Type,
        next: Self,
    ) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::ApplyAdapterArg {
            function,
            ret_markers,
            source_ret,
            target_ret,
            next,
        }))
    }

    fn apply_adapter_result(
        ret_markers: Vec<EvidenceValueMarker>,
        source_ret: Type,
        target_ret: Type,
        next: Self,
    ) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::ApplyAdapterResult {
            ret_markers,
            source_ret,
            target_ret,
            next,
        }))
    }

    fn case_scrutinee(arms: Rc<[control_vm::CaseArm]>, env: Env, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::CaseScrutinee {
            arms,
            env,
            next,
        }))
    }

    fn catch_body(
        catch_expr: ExprId,
        arms: Rc<[control_vm::CatchArm]>,
        env: Env,
        next: Self,
    ) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::CatchBody {
            catch_expr,
            arms,
            env,
            next,
        }))
    }

    fn marker_frame(
        markers: Rc<[EvidenceValueMarker]>,
        activate_add_ids: bool,
        handler_path: Option<Vec<String>>,
        next: Self,
    ) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::MarkerFrame {
            markers,
            activate_add_ids,
            handler_path,
            next,
        }))
    }

    fn provider_env(provider_env: RuntimeEvidenceProviderEnv, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::ProviderEnv {
            provider_env,
            next,
        }))
    }

    fn tuple_items(values: Vec<SharedValue>, rest: Rc<[ExprId]>, env: Env, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::TupleItems {
            values,
            rest,
            env,
            next,
        }))
    }

    fn record_spread(fields: Rc<[control_vm::RecordField]>, env: Env, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::RecordSpread {
            fields,
            env,
            next,
        }))
    }

    fn record_fields(
        values: Vec<RuntimeEvidenceValueField>,
        rest: Rc<[control_vm::RecordField]>,
        env: Env,
        next: Self,
    ) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::RecordFields {
            values,
            rest,
            env,
            next,
        }))
    }

    fn poly_variant_payloads(
        tag: String,
        values: Vec<SharedValue>,
        rest: Rc<[ExprId]>,
        env: Env,
        next: Self,
    ) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::PolyVariantPayloads {
            tag,
            values,
            rest,
            env,
            next,
        }))
    }

    fn select_base(name: String, resolution: Option<SelectResolution>, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::SelectBase {
            name,
            resolution,
            next,
        }))
    }

    fn block_stmt(
        resume: EvidenceBlockResume,
        rest: Rc<[Stmt]>,
        tail: Option<ExprId>,
        env: Env,
        last: SharedValue,
        next: Self,
    ) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::BlockStmt {
            resume,
            rest,
            tail,
            env,
            last,
            next,
        }))
    }

    fn ref_set_reference(value: ExprId, env: Env, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::RefSetReference {
            value,
            env,
            next,
        }))
    }

    fn ref_set_forced_reference(value: ExprId, env: Env, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::RefSetForcedReference {
            value,
            env,
            next,
        }))
    }

    fn ref_set_value(reference: SharedValue, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::RefSetValue {
            reference,
            next,
        }))
    }

    fn ref_set_forced_value(reference: SharedValue, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::RefSetForcedValue {
            reference,
            next,
        }))
    }

    fn ref_set_resolved_unit(next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::RefSetResolvedUnit {
            next,
        }))
    }

    fn ref_set_handle_result(assigned: SharedValue, next: Self) -> Self {
        Self::Frame(Rc::new(EvidenceContinuationFrame::RefSetHandleResult {
            assigned,
            next,
        }))
    }

    fn ref_set_handle_value_result(assigned: SharedValue, next: Self) -> Self {
        Self::Frame(Rc::new(
            EvidenceContinuationFrame::RefSetHandleValueResult { assigned, next },
        ))
    }

    fn ref_set_emit_resolved_request(
        request: EvidenceRequest,
        assigned: SharedValue,
        mode: EvidenceRefSetResumeMode,
        next: Self,
    ) -> Self {
        Self::Frame(Rc::new(
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
        Self::Frame(Rc::new(EvidenceContinuationFrame::ResolveRefSetValues {
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
        Self::Frame(Rc::new(EvidenceContinuationFrame::ResolveRefSetFields {
            fields,
            assigned,
            out,
            index,
            next,
        }))
    }

    fn is_identity(&self) -> bool {
        matches!(self, Self::Identity)
    }

    fn then_counted(
        self,
        tail: Self,
        stats: &mut RuntimeEvidenceRunStats,
        source: EvidenceContinuationAppendSource,
    ) -> Self {
        if tail.is_identity() {
            return self;
        }
        if self.is_identity() {
            return tail;
        }
        let mut head = self;
        match head.try_append_owned_tail_counted(tail, stats, source) {
            Ok(()) => {
                stats.continuation_owned_tail_appends += 1;
                record_continuation_append_owned_tail(stats, source);
                return head;
            }
            Err(tail) => {
                stats.continuation_append_steps += 1;
                record_continuation_append_then(stats, source);
                return Self::Frame(Rc::new(EvidenceContinuationFrame::Then {
                    first: head,
                    second: tail,
                }));
            }
        }
    }

    fn try_append_owned_tail_counted(
        &mut self,
        tail: Self,
        stats: &mut RuntimeEvidenceRunStats,
        source: EvidenceContinuationAppendSource,
    ) -> Result<(), Self> {
        if tail.is_identity() {
            return Ok(());
        }
        match self {
            Self::Identity => {
                *self = tail;
                Ok(())
            }
            Self::Frame(frame) => {
                let Some(frame) = Rc::get_mut(frame) else {
                    record_continuation_append_blocker(
                        stats,
                        source,
                        EvidenceContinuationAppendBlocker::RcShared,
                    );
                    return Err(tail);
                };
                frame.try_append_owned_tail_counted(tail, stats, source)
            }
        }
    }

    fn boundary_kind(&self) -> EvidenceContinuationBoundaryKind {
        match self {
            Self::Identity => EvidenceContinuationBoundaryKind::Identity,
            Self::Frame(frame) => frame.boundary_kind(),
        }
    }

    fn has_request_boundary(&self, routed_yield_handler: Option<ExprId>) -> bool {
        let Some(frame) = self.frame() else {
            return false;
        };
        frame.has_request_boundary(routed_yield_handler)
    }
}

impl EvidenceContinuationFrame {
    fn has_request_boundary(&self, routed_yield_handler: Option<ExprId>) -> bool {
        match self {
            EvidenceContinuationFrame::Then { first, second } => {
                first.has_request_boundary(routed_yield_handler)
                    || second.has_request_boundary(routed_yield_handler)
            }
            EvidenceContinuationFrame::CatchBody {
                catch_expr, next, ..
            } => match routed_yield_handler {
                None => true,
                Some(handler) if handler == *catch_expr => true,
                Some(_) => next.has_request_boundary(routed_yield_handler),
            },
            EvidenceContinuationFrame::RefSetHandleResult { .. }
            | EvidenceContinuationFrame::RefSetHandleValueResult { .. } => true,
            EvidenceContinuationFrame::MarkerFrame { .. }
            | EvidenceContinuationFrame::ProviderEnv { .. } => false,
            EvidenceContinuationFrame::ForceThunk { next, .. }
            | EvidenceContinuationFrame::ForceValueIfThunk { next }
            | EvidenceContinuationFrame::ApplyCallee { next, .. }
            | EvidenceContinuationFrame::ApplyArg { next, .. }
            | EvidenceContinuationFrame::ApplyForcedCallee { next, .. }
            | EvidenceContinuationFrame::AdaptValue { next, .. }
            | EvidenceContinuationFrame::WrapThunkValue { next }
            | EvidenceContinuationFrame::ApplyAdapterArg { next, .. }
            | EvidenceContinuationFrame::ApplyAdapterResult { next, .. }
            | EvidenceContinuationFrame::CaseScrutinee { next, .. }
            | EvidenceContinuationFrame::TupleItems { next, .. }
            | EvidenceContinuationFrame::RecordSpread { next, .. }
            | EvidenceContinuationFrame::RecordFields { next, .. }
            | EvidenceContinuationFrame::PolyVariantPayloads { next, .. }
            | EvidenceContinuationFrame::SelectBase { next, .. }
            | EvidenceContinuationFrame::BlockStmt { next, .. }
            | EvidenceContinuationFrame::RefSetReference { next, .. }
            | EvidenceContinuationFrame::RefSetForcedReference { next, .. }
            | EvidenceContinuationFrame::RefSetValue { next, .. }
            | EvidenceContinuationFrame::RefSetForcedValue { next, .. }
            | EvidenceContinuationFrame::RefSetResolvedUnit { next }
            | EvidenceContinuationFrame::RefSetEmitResolvedRequest { next, .. }
            | EvidenceContinuationFrame::ResolveRefSetValues { next, .. }
            | EvidenceContinuationFrame::ResolveRefSetFields { next, .. } => {
                next.has_request_boundary(routed_yield_handler)
            }
        }
    }

    fn try_append_owned_tail_counted(
        &mut self,
        tail: EvidenceContinuation,
        stats: &mut RuntimeEvidenceRunStats,
        source: EvidenceContinuationAppendSource,
    ) -> Result<(), EvidenceContinuation> {
        let blocker = self.append_scope_blocker();
        let Some(tail_slot) = self.tail_mut() else {
            if let Some(blocker) = blocker {
                record_continuation_append_blocker(stats, source, blocker);
            }
            return Err(tail);
        };
        tail_slot.try_append_owned_tail_counted(tail, stats, source)
    }

    fn boundary_kind(&self) -> EvidenceContinuationBoundaryKind {
        match self {
            Self::MarkerFrame { .. } => EvidenceContinuationBoundaryKind::MarkerFrame,
            Self::ProviderEnv { .. } => EvidenceContinuationBoundaryKind::ProviderEnv,
            _ => EvidenceContinuationBoundaryKind::Other,
        }
    }

    fn append_scope_blocker(&self) -> Option<EvidenceContinuationAppendBlocker> {
        match self {
            Self::MarkerFrame { .. } => Some(EvidenceContinuationAppendBlocker::MarkerFrame),
            Self::ProviderEnv { .. } => Some(EvidenceContinuationAppendBlocker::ProviderEnv),
            _ => None,
        }
    }

    fn tail_mut(&mut self) -> Option<&mut EvidenceContinuation> {
        match self {
            EvidenceContinuationFrame::Then { second, .. } => Some(second),
            // Appending into these frames would move the appended continuation under the dynamic
            // marker/provider scope. Keep the old Then boundary for scope-preserving composition.
            EvidenceContinuationFrame::MarkerFrame { .. }
            | EvidenceContinuationFrame::ProviderEnv { .. } => None,
            EvidenceContinuationFrame::ForceThunk { next, .. }
            | EvidenceContinuationFrame::ForceValueIfThunk { next }
            | EvidenceContinuationFrame::ApplyCallee { next, .. }
            | EvidenceContinuationFrame::ApplyArg { next, .. }
            | EvidenceContinuationFrame::ApplyForcedCallee { next, .. }
            | EvidenceContinuationFrame::AdaptValue { next, .. }
            | EvidenceContinuationFrame::WrapThunkValue { next }
            | EvidenceContinuationFrame::ApplyAdapterArg { next, .. }
            | EvidenceContinuationFrame::ApplyAdapterResult { next, .. }
            | EvidenceContinuationFrame::CaseScrutinee { next, .. }
            | EvidenceContinuationFrame::CatchBody { next, .. }
            | EvidenceContinuationFrame::TupleItems { next, .. }
            | EvidenceContinuationFrame::RecordSpread { next, .. }
            | EvidenceContinuationFrame::RecordFields { next, .. }
            | EvidenceContinuationFrame::PolyVariantPayloads { next, .. }
            | EvidenceContinuationFrame::SelectBase { next, .. }
            | EvidenceContinuationFrame::BlockStmt { next, .. }
            | EvidenceContinuationFrame::RefSetReference { next, .. }
            | EvidenceContinuationFrame::RefSetForcedReference { next, .. }
            | EvidenceContinuationFrame::RefSetValue { next, .. }
            | EvidenceContinuationFrame::RefSetForcedValue { next, .. }
            | EvidenceContinuationFrame::RefSetResolvedUnit { next }
            | EvidenceContinuationFrame::RefSetHandleResult { next, .. }
            | EvidenceContinuationFrame::RefSetHandleValueResult { next, .. }
            | EvidenceContinuationFrame::RefSetEmitResolvedRequest { next, .. }
            | EvidenceContinuationFrame::ResolveRefSetValues { next, .. }
            | EvidenceContinuationFrame::ResolveRefSetFields { next, .. } => Some(next),
        }
    }
}

fn record_continuation_append(
    stats: &mut RuntimeEvidenceRunStats,
    source: EvidenceContinuationAppendSource,
) {
    stats.continuation_appends += 1;
    match source {
        EvidenceContinuationAppendSource::Request => {
            stats.request_continuation_appends += 1;
        }
        EvidenceContinuationAppendSource::DirectTail => {
            stats.direct_tail_continuation_appends += 1;
        }
    }
}

fn record_continuation_append_owned_tail(
    stats: &mut RuntimeEvidenceRunStats,
    source: EvidenceContinuationAppendSource,
) {
    match source {
        EvidenceContinuationAppendSource::Request => {
            stats.request_continuation_owned_tail_appends += 1;
        }
        EvidenceContinuationAppendSource::DirectTail => {
            stats.direct_tail_continuation_owned_tail_appends += 1;
        }
    }
}

fn record_continuation_append_then(
    stats: &mut RuntimeEvidenceRunStats,
    source: EvidenceContinuationAppendSource,
) {
    match source {
        EvidenceContinuationAppendSource::Request => {
            stats.request_continuation_then_appends += 1;
        }
        EvidenceContinuationAppendSource::DirectTail => {
            stats.direct_tail_continuation_then_appends += 1;
        }
    }
}

fn record_continuation_append_blocker(
    stats: &mut RuntimeEvidenceRunStats,
    source: EvidenceContinuationAppendSource,
    blocker: EvidenceContinuationAppendBlocker,
) {
    match blocker {
        EvidenceContinuationAppendBlocker::MarkerFrame => {
            stats.continuation_append_blocked_by_marker_frame += 1;
        }
        EvidenceContinuationAppendBlocker::ProviderEnv => {
            stats.continuation_append_blocked_by_provider_env += 1;
        }
        EvidenceContinuationAppendBlocker::RcShared => {
            stats.continuation_append_blocked_by_rc_shared += 1;
        }
    }
    match (source, blocker) {
        (
            EvidenceContinuationAppendSource::Request,
            EvidenceContinuationAppendBlocker::MarkerFrame,
        ) => {
            stats.request_continuation_append_blocked_by_marker_frame += 1;
        }
        (
            EvidenceContinuationAppendSource::Request,
            EvidenceContinuationAppendBlocker::ProviderEnv,
        ) => {
            stats.request_continuation_append_blocked_by_provider_env += 1;
        }
        (
            EvidenceContinuationAppendSource::Request,
            EvidenceContinuationAppendBlocker::RcShared,
        ) => {
            stats.request_continuation_append_blocked_by_rc_shared += 1;
        }
        (
            EvidenceContinuationAppendSource::DirectTail,
            EvidenceContinuationAppendBlocker::MarkerFrame,
        ) => {
            stats.direct_tail_continuation_append_blocked_by_marker_frame += 1;
        }
        (
            EvidenceContinuationAppendSource::DirectTail,
            EvidenceContinuationAppendBlocker::ProviderEnv,
        ) => {
            stats.direct_tail_continuation_append_blocked_by_provider_env += 1;
        }
        (
            EvidenceContinuationAppendSource::DirectTail,
            EvidenceContinuationAppendBlocker::RcShared,
        ) => {
            stats.direct_tail_continuation_append_blocked_by_rc_shared += 1;
        }
    }
}

impl EvidenceRequest {
    fn append_continuation(
        mut self,
        tail: EvidenceContinuation,
        stats: &mut RuntimeEvidenceRunStats,
    ) -> Self {
        record_continuation_append(stats, EvidenceContinuationAppendSource::Request);
        self.continuation =
            self.continuation
                .then_counted(tail, stats, EvidenceContinuationAppendSource::Request);
        self
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
            .filter(|route| route.is_direct())
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

    fn replace_effect_calls(
        &mut self,
        effect_calls: HashMap<(ExprId, ExprId), EvidenceEffectRoute>,
    ) {
        let direct_effect_calls = effect_calls
            .values()
            .filter(|route| route.is_direct())
            .count();
        self.stats.effect_calls = effect_calls.len();
        self.stats.direct_effect_calls = direct_effect_calls;
        self.effect_calls = effect_calls;
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
            execution: EvidenceVmOperationExecutionPlan::YieldFallback,
            request_free_yield: true,
        },
        ControlEvidenceRoute::Blocked { .. } | ControlEvidenceRoute::Unhandled => {
            EvidenceEffectRoute::Unhandled
        }
    };
    Some((apply, callee, route))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeEvidenceRunError {
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

pub fn run_program(program: &Program) -> Result<RuntimeEvidenceRunOutput, RuntimeEvidenceRunError> {
    RuntimeEvidenceRunner::new(program, RuntimeEvidenceRunContext::default()).run()
}

pub fn run_program_with_plan(
    program: &Program,
    plan: &EvidenceVmPlan,
) -> Result<RuntimeEvidenceRunOutput, RuntimeEvidenceRunError> {
    RuntimeEvidenceRunner::new(program, RuntimeEvidenceRunContext::from_plan(plan)).run()
}

fn runtime_expr_cache(program: &Program) -> Vec<RuntimeEvidenceExpr> {
    program
        .exprs
        .iter()
        .enumerate()
        .map(|(index, expr)| match expr {
            Expr::Lit(lit) => RuntimeEvidenceExpr::Value(shared(value_from_lit(lit))),
            Expr::Constructor { def, arity } => {
                RuntimeEvidenceExpr::Value(shared(constructor_value(*def, *arity, Vec::new())))
            }
            Expr::EffectOp { path } => {
                RuntimeEvidenceExpr::Value(shared(RuntimeEvidenceValue::EffectOp {
                    expr: ExprId(index as u32),
                    path: shared_path(path),
                }))
            }
            Expr::PrimitiveOp { op, context } if op.arity() > 0 => {
                RuntimeEvidenceExpr::Value(shared(RuntimeEvidenceValue::PrimitiveOp {
                    op: *op,
                    context: context.clone(),
                    args: Vec::new(),
                }))
            }
            Expr::PrimitiveOp { op, context } => RuntimeEvidenceExpr::NullaryPrimitive {
                op: *op,
                context: context.clone(),
            },
            Expr::Local(def) => RuntimeEvidenceExpr::Local {
                slot: EnvSlot::from(*def),
                def: *def,
            },
            Expr::InstanceRef(instance) => RuntimeEvidenceExpr::Instance(*instance),
            Expr::Coerce { expr, .. } => RuntimeEvidenceExpr::Alias(*expr),
            Expr::MakeThunk { target, body, .. } => RuntimeEvidenceExpr::MakeThunk {
                body: *body,
                provider_expr: ExprId(index as u32),
                needs_hygiene_mark: effective_thunk_type_may_need_hygiene_mark(target),
            },
            Expr::Lambda { param, body } => RuntimeEvidenceExpr::Lambda {
                param: shared_pat(param),
                body: *body,
                provider_expr: ExprId(index as u32),
            },
            Expr::FunctionAdapter {
                source,
                target,
                function,
                hygiene,
            } => RuntimeEvidenceExpr::FunctionAdapter {
                source: source.clone(),
                target: target.clone(),
                function: *function,
                hygiene: hygiene.clone(),
                provider_expr: ExprId(index as u32),
            },
            Expr::ForceThunk { target, thunk, .. } => {
                let target_value_is_thunk = matches!(target.value, Type::Thunk { .. });
                if let Some((site, effect, path, arg)) = forced_effect_call_parts(program, *thunk) {
                    RuntimeEvidenceExpr::ForceEffectCall {
                        target_value_is_thunk,
                        site,
                        effect,
                        path: shared_path(path),
                        arg,
                    }
                } else {
                    RuntimeEvidenceExpr::ForceThunk {
                        target_value_is_thunk,
                        thunk: *thunk,
                    }
                }
            }
            Expr::MarkerFrame { path, body } => RuntimeEvidenceExpr::MarkerFrame {
                path: Rc::from(path.clone().into_boxed_slice()),
                body: *body,
            },
            Expr::Apply { callee, arg } => RuntimeEvidenceExpr::Apply {
                site: ExprId(index as u32),
                callee: *callee,
                arg: *arg,
            },
            Expr::RefSet { reference, value } => RuntimeEvidenceExpr::RefSet {
                reference: *reference,
                value: *value,
            },
            Expr::Tuple(items) => RuntimeEvidenceExpr::Tuple(shared_expr_ids(items)),
            Expr::Record { fields, spread } => RuntimeEvidenceExpr::Record {
                fields: shared_record_fields(fields),
                spread: spread.clone(),
            },
            Expr::PolyVariant { tag, payloads } => RuntimeEvidenceExpr::PolyVariant {
                tag: tag.clone(),
                payloads: shared_expr_ids(payloads),
            },
            Expr::Select {
                base,
                name,
                resolution,
            } => RuntimeEvidenceExpr::Select {
                base: *base,
                name: name.clone(),
                resolution: resolution.clone(),
            },
            Expr::Case { scrutinee, .. } => RuntimeEvidenceExpr::Case {
                expr: ExprId(index as u32),
                scrutinee: *scrutinee,
            },
            Expr::Catch { body, .. } => RuntimeEvidenceExpr::Catch {
                expr: ExprId(index as u32),
                body: *body,
            },
            Expr::Block(block) => RuntimeEvidenceExpr::Block {
                stmts: shared_stmts(&block.stmts),
                tail: block.tail,
            },
        })
        .collect()
}

fn forced_effect_call_parts(
    program: &Program,
    thunk: ExprId,
) -> Option<(ExprId, ExprId, &[String], ExprId)> {
    let site = thunk;
    let Expr::Apply { callee, arg } = program.exprs.get(thunk.0 as usize)? else {
        return None;
    };
    let Expr::EffectOp { path } = program.exprs.get(callee.0 as usize)? else {
        return None;
    };
    Some((site, *callee, path, *arg))
}

fn static_arm_caches(
    program: &Program,
) -> (
    Vec<Option<Rc<[control_vm::CaseArm]>>>,
    Vec<Option<Rc<[control_vm::CatchArm]>>>,
) {
    let mut case_arms = Vec::with_capacity(program.exprs.len());
    let mut catch_arms = Vec::with_capacity(program.exprs.len());
    for expr in &program.exprs {
        match expr {
            Expr::Case { arms, .. } => {
                case_arms.push(Some(shared_case_arms(arms)));
                catch_arms.push(None);
            }
            Expr::Catch { arms, .. } => {
                case_arms.push(None);
                catch_arms.push(Some(shared_catch_arms(arms)));
            }
            _ => {
                case_arms.push(None);
                catch_arms.push(None);
            }
        }
    }
    (case_arms, catch_arms)
}

struct RuntimeEvidenceRunner<'a> {
    program: &'a Program,
    evidence: ControlEvidenceIndex,
    runtime_exprs: Vec<RuntimeEvidenceExpr>,
    case_arms: Vec<Option<Rc<[control_vm::CaseArm]>>>,
    catch_arms: Vec<Option<Rc<[control_vm::CatchArm]>>>,
    instances: HashMap<InstanceId, SharedValue>,
    evaluating_instances: HashSet<InstanceId>,
    next_guard_id: u32,
    next_provider_scope_id: u32,
    provider_grants: Vec<EvidenceProviderGrant>,
    active_frames: Vec<EvidenceActiveFrame>,
    active_handler_frames: Vec<EvidenceActiveHandlerFrame>,
    active_add_ids: Vec<EvidenceActiveAddIdMarker>,
    #[cfg(debug_assertions)]
    active_add_id_index: ActiveAddIdIndex,
    active_marker_plans: Vec<EvidenceActiveMarkerPlan>,
    active_provider_envs: Vec<RuntimeEvidenceProviderFrame>,
    active_provider_handlers: Vec<u32>,
    stdout: String,
    context: RuntimeEvidenceRunContext,
    stats: RuntimeEvidenceRunStats,
}

impl<'a> RuntimeEvidenceRunner<'a> {
    fn new(program: &'a Program, mut context: RuntimeEvidenceRunContext) -> Self {
        let mut evidence = ControlEvidenceIndex::new(program);
        context.apply_to_evidence(&mut evidence);
        let runtime_exprs = runtime_expr_cache(program);
        let (case_arms, catch_arms) = static_arm_caches(program);
        let mut stats = evidence.stats();
        context.apply_to_stats(&mut stats);
        Self {
            program,
            evidence,
            runtime_exprs,
            case_arms,
            catch_arms,
            instances: HashMap::new(),
            evaluating_instances: HashSet::new(),
            next_guard_id: 0,
            next_provider_scope_id: 0,
            provider_grants: Vec::new(),
            active_frames: Vec::new(),
            active_handler_frames: Vec::new(),
            active_add_ids: Vec::new(),
            #[cfg(debug_assertions)]
            active_add_id_index: ActiveAddIdIndex::default(),
            active_marker_plans: Vec::new(),
            active_provider_envs: Vec::new(),
            active_provider_handlers: Vec::new(),
            stdout: String::new(),
            context,
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
            stdout: self.stdout.clone(),
            evidence_stats: self.stats,
        })
    }

    fn static_case_arms(&self, expr: ExprId) -> Rc<[control_vm::CaseArm]> {
        self.case_arms
            .get(expr.0 as usize)
            .and_then(|arms| arms.as_ref())
            .cloned()
            .expect("case expression must have cached case arms")
    }

    fn static_catch_arms(&self, expr: ExprId) -> Rc<[control_vm::CatchArm]> {
        self.catch_arms
            .get(expr.0 as usize)
            .and_then(|arms| arms.as_ref())
            .cloned()
            .expect("catch expression must have cached catch arms")
    }

    fn clone_env(&mut self, env: &Env) -> Env {
        clone_env_for_stats(env, &mut self.stats)
    }

    fn provider_env_for_value(&mut self, expr: ExprId) -> RuntimeEvidenceProviderEnv {
        let active_provider_envs = self.active_provider_env_refs();
        let provider_env = self.context.provider_env_for_value(
            expr,
            &self.active_provider_handlers,
            &active_provider_envs,
        );
        if !provider_env.is_empty() {
            self.stats.runtime_provider_env_values += 1;
            self.stats.runtime_provider_env_slots += provider_env.provider_count();
            self.stats.runtime_provider_env_candidates += provider_env.candidate_count();
        }
        provider_env
    }

    fn observe_provider_env(&mut self, provider_env: &RuntimeEvidenceProviderEnv) {
        if provider_env.is_empty() {
            return;
        }
        self.stats.runtime_provider_env_reads += 1;
        self.stats.runtime_provider_env_read_slots += provider_env.provider_count();
        self.stats.runtime_provider_env_read_candidates += provider_env.candidate_count();
    }

    fn with_provider_env(
        &mut self,
        provider_env: RuntimeEvidenceProviderEnv,
        run: impl FnOnce(&mut Self) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError>,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if provider_env.is_empty() {
            return run(self);
        }
        let len = self.active_provider_envs.len();
        let frame = self.provider_frame(provider_env.clone());
        self.active_provider_envs.push(frame);
        let result = run(self);
        self.active_provider_envs.truncate(len);
        self.close_provider_env_result(result?, provider_env)
    }

    fn provider_frame(
        &mut self,
        provider_env: RuntimeEvidenceProviderEnv,
    ) -> RuntimeEvidenceProviderFrame {
        let scope_id = EvidenceProviderScopeId(self.next_provider_scope_id);
        self.next_provider_scope_id += 1;
        RuntimeEvidenceProviderFrame::new(
            scope_id,
            provider_env,
            self.active_marker_plans.len(),
            self.active_add_ids.len(),
            self.active_handler_frames.len(),
        )
    }

    fn close_provider_env_result(
        &mut self,
        result: EvidenceEvalResult,
        provider_env: RuntimeEvidenceProviderEnv,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if provider_env.is_empty() {
            return Ok(result);
        }
        match result {
            EvidenceEvalResult::Value(value) => Ok(EvidenceEvalResult::Value(value)),
            EvidenceEvalResult::Effect(signal) => {
                self.close_provider_env_signal(signal, provider_env)
            }
        }
    }

    fn close_provider_env_signal(
        &mut self,
        signal: EvidenceEffectSignal,
        provider_env: RuntimeEvidenceProviderEnv,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match signal {
            EvidenceEffectSignal::DirectAbortive(call) => {
                Ok(EvidenceEvalResult::direct_abortive(call))
            }
            EvidenceEffectSignal::DirectTailResumptive(call) => {
                Ok(EvidenceEvalResult::direct_tail_resumptive(
                    self.close_provider_direct_tail(call, provider_env),
                ))
            }
            EvidenceEffectSignal::RoutedYield(call) => Ok(EvidenceEvalResult::routed_yield(
                self.close_provider_routed_yield(call, provider_env),
            )),
            EvidenceEffectSignal::GenericRequest(mut request) => {
                if !request.route.is_direct_abortive() {
                    request.continuation =
                        EvidenceContinuation::provider_env(provider_env, request.continuation);
                }
                Ok(EvidenceEvalResult::request(request))
            }
        }
    }

    fn close_provider_direct_tail(
        &mut self,
        call: EvidenceDirectTailResumptive,
        provider_env: RuntimeEvidenceProviderEnv,
    ) -> EvidenceDirectTailResumptive {
        if provider_env.is_empty() {
            return call;
        }
        call.close_provider_env(provider_env)
    }

    fn close_provider_routed_yield(
        &mut self,
        call: EvidenceRoutedYield,
        provider_env: RuntimeEvidenceProviderEnv,
    ) -> EvidenceRoutedYield {
        if provider_env.is_empty() {
            return call;
        }
        call.close_provider_env(provider_env)
    }

    fn active_provider_env_refs(&self) -> Vec<&RuntimeEvidenceProviderEnv> {
        self.active_provider_envs
            .iter()
            .filter(|frame| {
                frame.is_unshadowed(
                    self.active_marker_plans.len(),
                    self.active_add_ids.len(),
                    self.active_handler_frames.len(),
                )
            })
            .map(|frame| &frame.provider_env)
            .collect()
    }

    fn active_provider_env_views(&self) -> Vec<RuntimeEvidenceProviderView<'_>> {
        self.active_provider_envs
            .iter()
            .filter(|frame| {
                frame.is_unshadowed(
                    self.active_marker_plans.len(),
                    self.active_add_ids.len(),
                    self.active_handler_frames.len(),
                )
            })
            .map(|frame| RuntimeEvidenceProviderView {
                scope_id: frame.scope_id,
                provider_env: &frame.provider_env,
                hygiene_baseline: frame.hygiene_baseline,
            })
            .collect()
    }

    fn effect_route_for_operation_call(
        &mut self,
        site: Option<ExprId>,
        callee: ExprId,
    ) -> EvidenceResolvedEffectRoute {
        let Some(site) = site else {
            return EvidenceResolvedEffectRoute {
                route: EvidenceEffectRoute::Unhandled,
                origin: None,
                visibility: None,
            };
        };
        let visibility = self.context.operation_visibility_for_call(site, callee);
        let route = self
            .evidence
            .effect_call_route(site, callee)
            .unwrap_or(EvidenceEffectRoute::Unhandled);
        let resolved = EvidenceResolvedEffectRoute {
            route,
            origin: route
                .is_direct()
                .then_some(EvidenceResolvedRouteOrigin::StaticDirect),
            visibility,
        };
        if route.is_direct() {
            return resolved;
        }
        if self.active_provider_envs.is_empty() {
            return resolved;
        }
        if !self.context.has_provider_lookup_for_call(site, callee) {
            return resolved;
        }
        let provider_route = {
            let provider_envs = self.active_provider_env_views();
            if provider_envs.is_empty() {
                return resolved;
            }
            self.context
                .provider_route_for_call(site, callee, &provider_envs)
        };
        self.stats.runtime_provider_env_route_lookups += 1;
        let Some(provider_route) = provider_route else {
            return resolved;
        };
        self.stats.runtime_provider_env_route_hits += 1;
        self.record_provider_env_route_hit(provider_route.route);
        EvidenceResolvedEffectRoute {
            route: provider_route.route,
            origin: provider_route.origin,
            visibility: merge_operation_visibility(visibility, provider_route.visibility),
        }
    }

    fn record_provider_env_route_hit(&mut self, route: EvidenceEffectRoute) {
        match route {
            EvidenceEffectRoute::Direct { execution, .. } => match execution {
                EvidenceVmOperationExecutionPlan::DirectAbortive => {
                    self.stats.runtime_provider_env_route_hit_direct_abortive += 1;
                }
                EvidenceVmOperationExecutionPlan::DirectTailResumptive => {
                    self.stats
                        .runtime_provider_env_route_hit_direct_tail_resumptive += 1;
                }
                EvidenceVmOperationExecutionPlan::YieldFallback => {
                    self.stats.runtime_provider_env_route_hit_yield_fallback += 1;
                }
                EvidenceVmOperationExecutionPlan::BlockedFallback => {
                    self.stats.runtime_provider_env_route_hit_blocked_fallback += 1;
                }
                EvidenceVmOperationExecutionPlan::GenericFallback => {
                    self.stats.runtime_provider_env_route_hit_generic_fallback += 1;
                }
            },
            EvidenceEffectRoute::Unhandled => {
                self.stats.runtime_provider_env_route_hit_unhandled += 1;
            }
        }
    }

    fn effect_route_cert(
        &mut self,
        origin: Option<EvidenceResolvedRouteOrigin>,
    ) -> EvidenceRouteCert {
        match origin {
            Some(EvidenceResolvedRouteOrigin::StaticDirect) => EvidenceRouteCert::StaticDirect,
            Some(EvidenceResolvedRouteOrigin::ProviderGrant(grant)) => {
                EvidenceRouteCert::ProviderGrant(self.record_provider_grant(grant))
            }
            None => EvidenceRouteCert::None,
        }
    }

    fn record_provider_grant(&mut self, grant: EvidenceProviderGrant) -> EvidenceProviderGrantId {
        let id = EvidenceProviderGrantId(self.provider_grants.len() as u32);
        self.provider_grants.push(grant);
        id
    }

    #[allow(dead_code)]
    fn provider_grant_gate_passes(&self, cert: EvidenceRouteCert) -> bool {
        let Some(id) = cert.provider_grant_id() else {
            return false;
        };
        let Some(grant) = self.provider_grants.get(id.0 as usize) else {
            return false;
        };
        let gate = grant.gate();
        self.active_provider_envs.iter().any(|frame| {
            frame.gate_is_unshadowed(
                gate,
                self.active_marker_plans.len(),
                self.active_add_ids.len(),
                self.active_handler_frames.len(),
            )
        })
    }

    fn route_allows_routed_yield(
        &self,
        request_free_yield: bool,
        evidence: EffectThunkEvidence,
    ) -> bool {
        request_free_yield || self.provider_grant_gate_passes(evidence.route_cert)
    }

    fn direct_tail_gate_failure(
        &self,
        request_free_yield: bool,
        evidence: EffectThunkEvidence,
        path: &[String],
    ) -> Option<ProviderGrantPathGateFail> {
        if request_free_yield {
            return None;
        }
        self.provider_grant_path_gate_failure(evidence.route_cert, path)
    }

    fn provider_grant_path_gate_failure(
        &self,
        cert: EvidenceRouteCert,
        path: &[String],
    ) -> Option<ProviderGrantPathGateFail> {
        let Some(id) = cert.provider_grant_id() else {
            return Some(ProviderGrantPathGateFail::NoGrant);
        };
        let Some(grant) = self.provider_grants.get(id.0 as usize) else {
            return Some(ProviderGrantPathGateFail::MissingGrant);
        };
        let gate = grant.gate();
        if !self
            .active_provider_envs
            .iter()
            .any(|frame| frame.matches_gate(gate))
        {
            return Some(ProviderGrantPathGateFail::ScopeMissing);
        }
        if self.provider_grant_handler_shadowed(gate, path) {
            return Some(ProviderGrantPathGateFail::HandlerShadowed);
        }
        if let Some(shadowed) = self.provider_grant_add_id_shadow(gate, path) {
            return Some(ProviderGrantPathGateFail::AddIdShadowed(shadowed));
        }
        None
    }

    fn provider_grant_add_id_shadow(
        &self,
        gate: EvidenceProviderGrantGate,
        path: &[String],
    ) -> Option<EvidenceProviderShadowedAddId> {
        self.active_add_ids[gate.hygiene_baseline.active_add_id_len..]
            .iter()
            .find_map(|marker| {
                let kind = active_add_id_match_kind(&marker.marker, path)?;
                Some(EvidenceProviderShadowedAddId {
                    marker: marker.clone(),
                    kind,
                })
            })
    }

    fn provider_grant_handler_shadowed(
        &self,
        gate: EvidenceProviderGrantGate,
        path: &[String],
    ) -> bool {
        self.active_handler_frames[gate.hygiene_baseline.active_handler_frame_len..]
            .iter()
            .any(|frame| path_is_prefix(&frame.path, path))
    }

    fn record_direct_tail_gate_fail(&mut self, fail: ProviderGrantPathGateFail) {
        match fail {
            ProviderGrantPathGateFail::NoGrant => {
                self.stats.direct_tail_gate_fail_no_grant += 1;
            }
            ProviderGrantPathGateFail::MissingGrant => {
                self.stats.direct_tail_gate_fail_missing_grant += 1;
            }
            ProviderGrantPathGateFail::ScopeMissing => {
                self.stats.direct_tail_gate_fail_scope_missing += 1;
            }
            ProviderGrantPathGateFail::AddIdShadowed(shadowed) => {
                self.stats.direct_tail_gate_fail_add_id_shadowed += 1;
                match shadowed.kind {
                    ActiveAddIdMatchKind::AllPath => {
                        self.stats.direct_tail_gate_fail_add_id_all_path += 1;
                    }
                    ActiveAddIdMatchKind::OwnPath => {
                        self.stats.direct_tail_gate_fail_add_id_own_path += 1;
                    }
                    ActiveAddIdMatchKind::ForeignPath => {
                        self.stats.direct_tail_gate_fail_add_id_foreign_path += 1;
                    }
                }
            }
            ProviderGrantPathGateFail::HandlerShadowed => {
                self.stats.direct_tail_gate_fail_handler_shadowed += 1;
            }
        }
    }

    fn record_direct_tail_guarded_add_id(&mut self, kind: ActiveAddIdMatchKind) {
        self.stats.direct_tail_guarded_add_id_shadowed += 1;
        match kind {
            ActiveAddIdMatchKind::AllPath => {
                self.stats.direct_tail_guarded_add_id_all_path += 1;
            }
            ActiveAddIdMatchKind::OwnPath => {
                self.stats.direct_tail_guarded_add_id_own_path += 1;
            }
            ActiveAddIdMatchKind::ForeignPath => {
                self.stats.direct_tail_guarded_add_id_foreign_path += 1;
            }
        }
    }

    fn direct_tail_resumptive(
        &self,
        handler: ExprId,
        path: Rc<[String]>,
        payload: SharedValue,
        evidence: EffectThunkEvidence,
    ) -> EvidenceDirectTailResumptive {
        EvidenceDirectTailResumptive {
            handler,
            path,
            payload,
            hygiene: EvidenceSignalHygiene::new().with_operation_visibility(evidence.visibility),
            continuation: EvidenceContinuation::identity(),
        }
    }

    fn guarded_direct_tail_resumptive(
        &mut self,
        handler: ExprId,
        path: Rc<[String]>,
        payload: SharedValue,
        evidence: EffectThunkEvidence,
    ) -> EvidenceDirectTailResumptive {
        let hygiene = self
            .signal_hygiene_with_active_markers(&path)
            .with_operation_visibility(evidence.visibility);
        EvidenceDirectTailResumptive::with_hygiene(handler, path, payload, hygiene)
    }

    fn provider_permission_guarded_direct_tail_resumptive(
        &mut self,
        handler: ExprId,
        path: Rc<[String]>,
        payload: SharedValue,
        evidence: EffectThunkEvidence,
        shadowed: EvidenceProviderShadowedAddId,
    ) -> EvidenceDirectTailResumptive {
        self.stats.provider_add_id_shortcut_attempts += 1;
        let Some(visibility) = evidence.visibility else {
            self.stats
                .provider_add_id_shortcut_fallback_no_provider_permission += 1;
            return self.guarded_direct_tail_resumptive(handler, path, payload, evidence);
        };
        if visibility.provider_grant_permission().is_none() {
            self.stats
                .provider_add_id_shortcut_fallback_no_provider_permission += 1;
            return self.guarded_direct_tail_resumptive(handler, path, payload, evidence);
        }
        if shadowed.marker.marker.carry_after_frame {
            self.stats
                .provider_add_id_shortcut_fallback_carry_after_frame += 1;
            return self.guarded_direct_tail_resumptive(handler, path, payload, evidence);
        }
        let mut hygiene = EvidenceSignalHygiene::new().with_operation_visibility(Some(visibility));
        hygiene.push_guard_id(shadowed.marker.marker.id);
        self.stats.provider_add_id_shortcut_used += 1;
        #[cfg(debug_assertions)]
        if self.stats.provider_add_id_shortcut_used
            <= PROVIDER_ADD_ID_SHORTCUT_FULL_SCAN_VERIFY_LIMIT
        {
            let full_scan_hygiene = self
                .signal_hygiene_with_active_markers(&path)
                .with_operation_visibility(evidence.visibility);
            self.record_provider_add_id_shortcut_full_scan_guard_visible(
                &hygiene,
                &full_scan_hygiene,
                &path,
            );
        }
        EvidenceDirectTailResumptive::with_hygiene(handler, path, payload, hygiene)
    }

    fn provider_env_for_call(&mut self, site: Option<ExprId>) -> RuntimeEvidenceProviderEnv {
        let Some(site) = site else {
            return RuntimeEvidenceProviderEnv::default();
        };
        if self.active_provider_handlers.is_empty() && self.active_provider_envs.is_empty() {
            return RuntimeEvidenceProviderEnv::default();
        }
        if !self.context.has_provider_env_for_call(site) {
            return RuntimeEvidenceProviderEnv::default();
        }
        let active_provider_envs = self.active_provider_env_refs();
        let provider_env = self.context.provider_env_for_call(
            site,
            &self.active_provider_handlers,
            &active_provider_envs,
        );
        if !provider_env.is_empty() {
            self.stats.runtime_provider_env_values += 1;
            self.stats.runtime_provider_env_slots += provider_env.provider_count();
            self.stats.runtime_provider_env_candidates += provider_env.candidate_count();
        }
        provider_env
    }

    fn with_call_provider_env(
        &mut self,
        site: Option<ExprId>,
        run: impl FnOnce(&mut Self) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError>,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let provider_env = self.provider_env_for_call(site);
        self.with_provider_env(provider_env, run)
    }

    fn append_request_continuation(
        &mut self,
        request: EvidenceRequest,
        tail: EvidenceContinuation,
    ) -> EvidenceRequest {
        if request.route.is_direct_abortive() {
            return request;
        }
        request.append_continuation(tail, &mut self.stats)
    }

    fn append_direct_tail_continuation(
        &mut self,
        mut call: EvidenceDirectTailResumptive,
        tail: EvidenceContinuation,
    ) -> EvidenceDirectTailResumptive {
        record_continuation_append(
            &mut self.stats,
            EvidenceContinuationAppendSource::DirectTail,
        );
        call.continuation = call.continuation.then_counted(
            tail,
            &mut self.stats,
            EvidenceContinuationAppendSource::DirectTail,
        );
        call
    }

    fn fresh_guard_id(&mut self) -> EvidenceGuardId {
        let id = EvidenceGuardId(self.next_guard_id);
        self.next_guard_id += 1;
        id
    }

    fn instantiate_hygiene_markers(&mut self, markers: &[GuardMarker]) -> Vec<EvidenceValueMarker> {
        let mut value_markers = Vec::with_capacity(markers.len() * 2);
        for marker in markers {
            let id = self.fresh_guard_id();
            value_markers.push(EvidenceValueMarker::Frame { id });
            value_markers.push(EvidenceValueMarker::AddId(Rc::new(EvidenceAddIdMarker {
                id,
                path: shared_path(&marker.path),
                depth: marker.depth,
                guard_own_path: marker.guard_own_path,
                guard_foreign_path: marker.guard_foreign_path,
                carry_after_frame: marker.guard_own_path,
                preserve_own_on_resume: marker.preserve_own_on_resume,
            })));
        }
        value_markers
    }

    fn active_function_call_boundary(
        &mut self,
        source: EvidenceMarkerFrameSource,
    ) -> Result<EvidenceCallBoundary, EvidenceCallBoundaryBypassCert> {
        let Some(active_plan) = self.active_marker_plans.last() else {
            return Err(EvidenceCallBoundaryBypassCert::NoActiveMarkerPlan);
        };
        self.stats.function_call_marker_plans += 1;
        self.stats.function_call_marker_inputs += active_plan.markers.len();
        let markers = active_plan.function_call_markers();
        self.stats.function_call_marker_outputs += markers.len();
        if markers.is_empty() {
            return Err(EvidenceCallBoundaryBypassCert::NoFunctionCallMarkers);
        }
        Ok(EvidenceCallBoundary::new(source, markers, true, None))
    }

    fn with_call_boundary(
        &mut self,
        boundary: EvidenceCallBoundary,
        run: impl FnOnce(&mut Self) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError>,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        self.with_marker_frame(
            boundary.source,
            boundary.markers,
            boundary.activate_add_ids,
            boundary.handler_path,
            run,
        )
    }

    fn close_call_boundary_without_frame(
        &mut self,
        result: EvidenceEvalResult,
        boundary: &EvidenceCallBoundary,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        self.close_marked_result(result, boundary.markers.as_ref())
    }

    fn with_marker_frame(
        &mut self,
        source: EvidenceMarkerFrameSource,
        markers: Rc<[EvidenceValueMarker]>,
        activate_add_ids: bool,
        handler_path: Option<Vec<String>>,
        run: impl FnOnce(&mut Self) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError>,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if markers.is_empty() {
            return run(self);
        }
        self.record_marker_frame_entry(source, &markers, activate_add_ids, handler_path.is_some());

        let frame_len = self.active_frames.len();
        let handler_frame_len = self.active_handler_frames.len();
        let add_id_len = self.active_add_ids.len();
        let plan_len = self.active_marker_plans.len();
        self.push_marker_frame(&markers, activate_add_ids, handler_path.clone());
        self.push_active_marker_plan(markers.clone());
        let result = run(self);
        let handler_boundary = match &result {
            Ok(EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request))) => {
                self.handler_boundary_for_request(request, handler_path.as_deref(), frame_len)
            }
            Ok(EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call))) => self
                .handler_boundary_for_request(call.request(), handler_path.as_deref(), frame_len),
            Ok(EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call))) => {
                self.handler_boundary_for_direct_tail(call, handler_path.as_deref(), frame_len)
            }
            Ok(EvidenceEvalResult::Value(_))
            | Ok(EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(_)))
            | Err(_) => None,
        };
        self.pop_marker_frame(frame_len, handler_frame_len, add_id_len, plan_len);

        self.close_marker_frame_result(
            result?,
            markers,
            activate_add_ids,
            handler_path,
            handler_boundary,
        )
    }

    fn resume_marker_frame(
        &mut self,
        markers: Rc<[EvidenceValueMarker]>,
        activate_add_ids: bool,
        handler_path: Option<Vec<String>>,
        next: EvidenceContinuation,
        value: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        self.record_continuation_resume_marker_boundary(
            &markers,
            activate_add_ids,
            handler_path.is_some(),
        );
        if markers.is_empty() {
            return self.resume_continuation(next, value);
        }
        if next.is_identity() {
            self.stats.continuation_resume_marker_identity_fast_paths += 1;
            self.stats.continuation_resume_marker_result_value += 1;
            return Ok(EvidenceEvalResult::Value(mark_runtime_value_shared(
                value, markers,
            )));
        }
        self.record_marker_frame_entry(
            EvidenceMarkerFrameSource::ContinuationResume,
            &markers,
            activate_add_ids,
            handler_path.is_some(),
        );

        let frame_len = self.active_frames.len();
        let handler_frame_len = self.active_handler_frames.len();
        let add_id_len = self.active_add_ids.len();
        let plan_len = self.active_marker_plans.len();
        self.push_marker_frame(&markers, activate_add_ids, handler_path.clone());
        self.push_active_marker_plan(markers.clone());
        let result = self.resume_continuation(next, value);
        self.record_continuation_resume_marker_result(&result);
        let handler_boundary = match &result {
            Ok(EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request))) => {
                self.handler_boundary_for_request(request, handler_path.as_deref(), frame_len)
            }
            Ok(EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call))) => self
                .handler_boundary_for_request(call.request(), handler_path.as_deref(), frame_len),
            Ok(EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call))) => {
                self.handler_boundary_for_direct_tail(call, handler_path.as_deref(), frame_len)
            }
            Ok(EvidenceEvalResult::Value(_))
            | Ok(EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(_)))
            | Err(_) => None,
        };
        self.pop_marker_frame(frame_len, handler_frame_len, add_id_len, plan_len);

        self.close_marker_frame_result(
            result?,
            markers,
            activate_add_ids,
            handler_path,
            handler_boundary,
        )
    }

    fn record_continuation_resume_marker_boundary(
        &mut self,
        markers: &[EvidenceValueMarker],
        activate_add_ids: bool,
        has_handler_path: bool,
    ) {
        if markers.is_empty() {
            self.stats.continuation_resume_marker_empty_markers += 1;
            return;
        }
        if markers.iter().any(|marker| {
            matches!(
                marker,
                EvidenceValueMarker::AddId(marker) if activate_add_ids && marker.depth == 0
            )
        }) {
            self.stats.continuation_resume_marker_with_active_add_id += 1;
        }
        if has_handler_path {
            self.stats.continuation_resume_marker_with_handler_path += 1;
        }
    }

    fn record_continuation_resume_marker_result(
        &mut self,
        result: &Result<EvidenceEvalResult, RuntimeEvidenceRunError>,
    ) {
        match result {
            Ok(EvidenceEvalResult::Value(_)) => {
                self.stats.continuation_resume_marker_result_value += 1;
            }
            Ok(EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call))) => {
                self.stats.continuation_resume_marker_result_direct_tail += 1;
                if call.hygiene.provider_grant_permission().is_some() {
                    self.stats
                        .continuation_resume_marker_result_direct_tail_provider_permission += 1;
                }
                if self
                    .provider_guard_boundary_permission(&call.hygiene)
                    .is_some()
                {
                    self.stats
                        .continuation_resume_marker_result_direct_tail_provider_boundary_pair += 1;
                }
            }
            Ok(EvidenceEvalResult::Effect(_)) => {
                self.stats.continuation_resume_marker_result_legacy_signal += 1;
            }
            Err(_) => {
                self.stats.continuation_resume_marker_result_error += 1;
            }
        }
    }

    fn record_marker_frame_entry(
        &mut self,
        source: EvidenceMarkerFrameSource,
        markers: &[EvidenceValueMarker],
        activate_add_ids: bool,
        has_handler_path: bool,
    ) {
        self.stats.marker_frame_entries += 1;
        self.stats.marker_frame_markers += markers.len();
        let mut add_id_markers = 0;
        let mut active_add_id_markers = 0;
        for marker in markers {
            let EvidenceValueMarker::AddId(marker) = marker else {
                continue;
            };
            add_id_markers += 1;
            if activate_add_ids && marker.depth == 0 {
                active_add_id_markers += 1;
            }
        }
        self.stats.marker_frame_add_id_markers += add_id_markers;
        self.stats.marker_frame_active_add_id_markers += active_add_id_markers;
        if add_id_markers == 0 {
            self.stats.marker_frame_frame_only_entries += 1;
        }
        if active_add_id_markers == 0 && !has_handler_path {
            self.stats.marker_frame_no_active_add_id_no_handler_entries += 1;
        }
        match source {
            EvidenceMarkerFrameSource::Expr => {
                self.stats.marker_frame_expr_entries += 1;
            }
            EvidenceMarkerFrameSource::ScopedApply => {
                self.stats.marker_frame_scoped_apply_entries += 1;
            }
            EvidenceMarkerFrameSource::MarkedApply => {
                self.stats.marker_frame_marked_apply_entries += 1;
            }
            EvidenceMarkerFrameSource::Adapter => {
                self.stats.marker_frame_adapter_entries += 1;
            }
            EvidenceMarkerFrameSource::ContinuationResume => {
                self.stats.marker_frame_continuation_resume_entries += 1;
            }
            EvidenceMarkerFrameSource::MarkedForce => {
                self.stats.marker_frame_marked_force_entries += 1;
            }
        }
    }

    fn push_marker_frame(
        &mut self,
        markers: &[EvidenceValueMarker],
        activate_add_ids: bool,
        handler_path: Option<Vec<String>>,
    ) {
        let mut last_local_frame_entry = None;
        for marker in markers {
            match marker {
                EvidenceValueMarker::Frame { id } => {
                    let entry_frame_len = self.active_frames.len();
                    let frame_index = entry_frame_len;
                    self.active_frames.push(EvidenceActiveFrame { id: *id });
                    last_local_frame_entry = Some((*id, entry_frame_len));
                    if let Some(path) = &handler_path {
                        self.active_handler_frames.push(EvidenceActiveHandlerFrame {
                            frame_index,
                            id: *id,
                            path: path.clone(),
                        });
                    }
                }
                EvidenceValueMarker::AddId(marker) if activate_add_ids && marker.depth == 0 => {
                    let active_marker = EvidenceActiveAddIdMarker {
                        marker: marker.clone(),
                        entry_frame_len: last_local_frame_entry
                            .and_then(|(id, entry)| (id == marker.id).then_some(entry))
                            .unwrap_or_else(|| self.entry_frame_len_for_marker(marker.id)),
                    };
                    #[cfg(debug_assertions)]
                    self.active_add_id_index
                        .push(self.active_add_ids.len(), &active_marker);
                    self.active_add_ids.push(active_marker);
                }
                EvidenceValueMarker::AddId(_) => {}
            }
        }
    }

    fn pop_marker_frame(
        &mut self,
        frame_len: usize,
        handler_frame_len: usize,
        add_id_len: usize,
        plan_len: usize,
    ) {
        self.active_frames.truncate(frame_len);
        self.active_handler_frames.truncate(handler_frame_len);
        self.active_add_ids.truncate(add_id_len);
        #[cfg(debug_assertions)]
        self.active_add_id_index.truncate(add_id_len);
        self.active_marker_plans.truncate(plan_len);
    }

    fn push_active_marker_plan(&mut self, markers: Rc<[EvidenceValueMarker]>) {
        if self
            .active_marker_plans
            .last()
            .is_some_and(|current| current.markers.as_ref() == markers.as_ref())
        {
            self.stats.active_marker_plan_dedupes += 1;
            return;
        }
        self.stats.active_marker_plan_pushes += 1;
        self.active_marker_plans
            .push(EvidenceActiveMarkerPlan::new(markers));
    }

    fn entry_frame_len_for_marker(&self, id: EvidenceGuardId) -> usize {
        self.active_frames
            .iter()
            .rposition(|frame| frame.id == id)
            .unwrap_or(self.active_frames.len())
    }

    fn close_marker_frame_result(
        &mut self,
        result: EvidenceEvalResult,
        markers: Rc<[EvidenceValueMarker]>,
        activate_add_ids: bool,
        handler_path: Option<Vec<String>>,
        handler_boundary: Option<EvidenceHandlerBoundary>,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match result {
            EvidenceEvalResult::Value(value) => Ok(EvidenceEvalResult::Value(
                mark_runtime_value_shared(value, markers.clone()),
            )),
            EvidenceEvalResult::Effect(signal) => self.close_marker_frame_signal(
                signal,
                markers,
                activate_add_ids,
                handler_path,
                handler_boundary,
            ),
        }
    }

    fn close_marker_frame_signal(
        &mut self,
        signal: EvidenceEffectSignal,
        markers: Rc<[EvidenceValueMarker]>,
        activate_add_ids: bool,
        handler_path: Option<Vec<String>>,
        handler_boundary: Option<EvidenceHandlerBoundary>,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match signal {
            EvidenceEffectSignal::DirectAbortive(call) => self.close_direct_abortive(call),
            EvidenceEffectSignal::DirectTailResumptive(call) => {
                let resume_plan = self.resume_marker_plan(&markers, activate_add_ids, handler_path);
                self.close_marker_direct_tail(call, markers, resume_plan, handler_boundary)
            }
            EvidenceEffectSignal::RoutedYield(mut call) => {
                if let Some(handler_boundary) = handler_boundary {
                    call = call.with_handler_boundary(handler_boundary);
                }
                let resume_plan = self.resume_marker_plan(&markers, activate_add_ids, handler_path);
                self.close_marker_routed_yield(call, markers, resume_plan)
            }
            EvidenceEffectSignal::GenericRequest(mut request) => {
                if let Some(handler_boundary) = handler_boundary {
                    request.hygiene.set_handler_boundary(handler_boundary);
                }
                request.payload = mark_runtime_value_shared(request.payload, markers.clone());
                self.close_marker_request(
                    request,
                    self.resume_marker_plan(&markers, activate_add_ids, handler_path),
                )
            }
        }
    }

    fn resume_marker_plan(
        &self,
        markers: &Rc<[EvidenceValueMarker]>,
        activate_add_ids: bool,
        handler_path: Option<Vec<String>>,
    ) -> Option<EvidenceResumeMarkerPlan> {
        let markers = markers_for_continuation_resume_shared(markers);
        if markers.is_empty() {
            return None;
        }
        Some(EvidenceResumeMarkerPlan {
            markers,
            activate_add_ids,
            handler_path,
        })
    }

    fn resume_marker_plan_for_slice(
        &self,
        markers: &[EvidenceValueMarker],
        activate_add_ids: bool,
        handler_path: Option<Vec<String>>,
    ) -> Option<EvidenceResumeMarkerPlan> {
        let markers = markers_for_continuation_resume(markers);
        if markers.is_empty() {
            return None;
        }
        Some(EvidenceResumeMarkerPlan {
            markers: share_marker_vec(markers),
            activate_add_ids,
            handler_path,
        })
    }

    fn close_marker_request(
        &mut self,
        mut request: EvidenceRequest,
        resume_plan: Option<EvidenceResumeMarkerPlan>,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if request.route.is_direct_abortive() {
            return Ok(EvidenceEvalResult::request(request));
        }
        if let Some(plan) = resume_plan {
            request.continuation = plan.attach(request.continuation);
        }
        Ok(EvidenceEvalResult::request(request))
    }

    fn close_marker_direct_tail(
        &mut self,
        call: EvidenceDirectTailResumptive,
        markers: Rc<[EvidenceValueMarker]>,
        resume_plan: Option<EvidenceResumeMarkerPlan>,
        handler_boundary: Option<EvidenceHandlerBoundary>,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let call = match handler_boundary {
            Some(handler_boundary) => call.with_handler_boundary(handler_boundary),
            None => call,
        };
        Ok(EvidenceEvalResult::direct_tail_resumptive(
            call.close_marker_frame(markers, resume_plan),
        ))
    }

    fn close_marker_routed_yield(
        &mut self,
        call: EvidenceRoutedYield,
        markers: Rc<[EvidenceValueMarker]>,
        resume_plan: Option<EvidenceResumeMarkerPlan>,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        Ok(EvidenceEvalResult::routed_yield(
            call.close_marker_frame(markers, resume_plan),
        ))
    }

    fn mark_request_with_active_markers(&mut self, request: &mut EvidenceRequest) {
        let mut hygiene = EvidenceSignalHygiene::from_request(request);
        self.mark_signal_hygiene_with_active_markers(&request.path, &mut hygiene);
        hygiene.apply_to_request(request);
    }

    fn signal_hygiene_with_active_markers(&mut self, path: &[String]) -> EvidenceSignalHygiene {
        let mut hygiene = EvidenceSignalHygiene::new();
        self.mark_signal_hygiene_with_active_markers(path, &mut hygiene);
        hygiene
    }

    fn mark_signal_hygiene_with_active_markers(
        &mut self,
        path: &[String],
        hygiene: &mut EvidenceSignalHygiene,
    ) {
        #[cfg(debug_assertions)]
        {
            let path_candidate_indices = self.active_add_id_index.candidates_for(path);
            debug_assert_eq!(
                path_candidate_indices,
                active_add_id_path_candidate_indices_by_scan(&self.active_add_ids, path)
            );
        }
        let mut entry_except_index =
            EvidenceRequestEntryExceptIndex::new(&self.active_frames, &hygiene.guard_ids);
        let mut scans = 0;
        let mut path_candidates = 0;
        let mut path_rejects = 0;
        let mut entry_except_rejects = 0;
        let mut already_carried_rejects = 0;
        let mut hits = 0;
        for active_marker in &self.active_add_ids {
            scans += 1;
            let marker = &active_marker.marker;
            if !active_add_id_matches_request_path(marker, path) {
                path_rejects += 1;
                continue;
            }
            path_candidates += 1;

            if !marker.carry_after_frame
                && signal_excepted_at_marker_entry(&entry_except_index, active_marker)
            {
                entry_except_rejects += 1;
                continue;
            }

            if marker.carry_after_frame {
                if hygiene
                    .carried_guards
                    .iter()
                    .any(|guard| guard.id == marker.id)
                {
                    already_carried_rejects += 1;
                    continue;
                }
                let entry_guard_ids = signal_guard_ids_at_marker_entry(
                    &self.active_frames,
                    &hygiene.guard_ids,
                    active_marker,
                );
                let exposed_guard_ids = self.carried_exposed_guard_ids_at_marker_entry(
                    path,
                    active_marker,
                    entry_guard_ids,
                );
                if hygiene.push_guard_id(marker.id) {
                    entry_except_index.push_guard_id(&self.active_frames, marker.id);
                }
                hygiene.push_carried_guard(EvidenceCarriedGuard {
                    id: marker.id,
                    entry_frame_len: active_marker.entry_frame_len,
                    exposed_guard_ids,
                });
                hits += 1;
            } else {
                if hygiene.push_guard_id(marker.id) {
                    entry_except_index.push_guard_id(&self.active_frames, marker.id);
                }
                hits += 1;
            }
        }
        self.stats.active_add_id_scans += scans;
        self.stats.active_add_id_path_candidates += path_candidates;
        self.stats.active_add_id_path_rejects += path_rejects;
        self.stats.active_add_id_entry_except_rejects += entry_except_rejects;
        self.stats.active_add_id_already_carried_rejects += already_carried_rejects;
        self.stats.active_add_id_hits += hits;
    }

    fn carried_exposed_guard_ids_at_marker_entry(
        &self,
        path: &[String],
        marker: &EvidenceActiveAddIdMarker,
        mut ids: Vec<EvidenceGuardId>,
    ) -> Vec<EvidenceGuardId> {
        if marker.marker.preserve_own_on_resume {
            self.push_contract_matching_handler_ids_at_marker_entry(
                path,
                marker.entry_frame_len,
                &mut ids,
            );
        }
        if self.exposes_matching_handler_alias(path, marker.entry_frame_len, &ids)
            && let Some(handler_id) = self.outermost_matching_handler_id(path)
        {
            push_unique_guard(&mut ids, handler_id);
        }
        ids
    }

    fn push_contract_matching_handler_ids_at_marker_entry(
        &self,
        path: &[String],
        entry_frame_len: usize,
        ids: &mut Vec<EvidenceGuardId>,
    ) {
        for frame in &self.active_handler_frames {
            if frame.frame_index < entry_frame_len && path_is_prefix(&frame.path, path) {
                push_unique_guard(ids, frame.id);
            }
        }
    }

    fn exposes_matching_handler_alias(
        &self,
        path: &[String],
        entry_frame_len: usize,
        ids: &[EvidenceGuardId],
    ) -> bool {
        ids.iter().any(|id| {
            self.active_handler_frames.iter().any(|frame| {
                frame.frame_index < entry_frame_len
                    && frame.id == *id
                    && path_is_prefix(&frame.path, path)
            })
        })
    }

    fn outermost_matching_handler_id(&self, request_path: &[String]) -> Option<EvidenceGuardId> {
        self.active_handler_frames
            .iter()
            .find(|frame| path_is_prefix(&frame.path, request_path))
            .map(|frame| frame.id)
    }

    fn request_guard_for_path_parts(
        &self,
        guard_ids: &[EvidenceGuardId],
        carried_guards: &[EvidenceCarriedGuard],
        operation_path: &[String],
    ) -> Option<EvidenceGuardSkip> {
        let matching_handler = self.find_matching_handler_frame(operation_path);
        let Some(matching_handler) = matching_handler else {
            if !self.active_handler_frames.is_empty() {
                return None;
            }
            return self
                .active_frames
                .iter()
                .find(|frame| guard_ids.contains(&frame.id))
                .map(|frame| EvidenceGuardSkip::Preserve(frame.id))
                .or_else(|| {
                    carried_guards
                        .first()
                        .map(|guard| EvidenceGuardSkip::Preserve(guard.id))
                });
        };
        self.carried_guard_for_matching_handler_parts(carried_guards, matching_handler)
            .or_else(|| {
                let handler_id = self.active_frames.get(matching_handler)?.id;
                self.active_frames[matching_handler + 1..]
                    .iter()
                    .find(|frame| {
                        self.guard_blocks_handler_parts(
                            guard_ids,
                            carried_guards,
                            frame.id,
                            handler_id,
                        )
                    })
                    .map(|frame| EvidenceGuardSkip::Preserve(frame.id))
            })
            .or_else(|| {
                self.current_handler_guard_parts(guard_ids, carried_guards, matching_handler)
            })
            .or_else(|| {
                if self.active_frames.is_empty() {
                    carried_guards
                        .first()
                        .map(|guard| EvidenceGuardSkip::Preserve(guard.id))
                } else {
                    None
                }
            })
    }

    fn carried_guard_for_matching_handler_parts(
        &self,
        carried_guards: &[EvidenceCarriedGuard],
        matching_handler: usize,
    ) -> Option<EvidenceGuardSkip> {
        let handler_id = self
            .active_frames
            .get(matching_handler)
            .map(|frame| frame.id)?;
        carried_guards
            .iter()
            .find(|guard| {
                matching_handler < guard.entry_frame_len
                    && !guard.exposed_guard_ids.contains(&handler_id)
            })
            .map(|guard| EvidenceGuardSkip::Preserve(guard.id))
    }

    fn guard_blocks_handler_parts(
        &self,
        guard_ids: &[EvidenceGuardId],
        carried_guards: &[EvidenceCarriedGuard],
        guard_id: EvidenceGuardId,
        handler_id: EvidenceGuardId,
    ) -> bool {
        guard_ids.contains(&guard_id)
            && !carried_guards.iter().any(|guard| {
                guard.exposed_guard_ids.contains(&handler_id)
                    && (guard.id == guard_id || guard.exposed_guard_ids.contains(&guard_id))
            })
    }

    fn current_handler_guard_parts(
        &self,
        guard_ids: &[EvidenceGuardId],
        carried_guards: &[EvidenceCarriedGuard],
        matching_handler: usize,
    ) -> Option<EvidenceGuardSkip> {
        for frame in &self.active_handler_frames {
            if frame.frame_index == matching_handler
                && self.guard_blocks_handler_parts(guard_ids, carried_guards, frame.id, frame.id)
            {
                return Some(EvidenceGuardSkip::Preserve(frame.id));
            }
        }
        None
    }

    fn find_matching_handler_frame(&self, operation_path: &[String]) -> Option<usize> {
        self.active_handler_frames
            .iter()
            .rev()
            .find(|frame| path_is_prefix(&frame.path, operation_path))
            .map(|frame| frame.frame_index)
    }

    fn handler_boundary_for_request(
        &self,
        request: &EvidenceRequest,
        handler_path: Option<&[String]>,
        frame_len_before_marker: usize,
    ) -> Option<EvidenceHandlerBoundary> {
        self.handler_boundary_for_request_parts(
            &request.hygiene.guard_ids,
            &request.hygiene.carried_guards,
            handler_path,
            frame_len_before_marker,
        )
    }

    fn handler_boundary_for_request_parts(
        &self,
        guard_ids: &[EvidenceGuardId],
        carried_guards: &[EvidenceCarriedGuard],
        handler_path: Option<&[String]>,
        frame_len_before_marker: usize,
    ) -> Option<EvidenceHandlerBoundary> {
        let handler_path = handler_path?;
        let handler = self.active_handler_frames.iter().rev().find(|frame| {
            frame.frame_index >= frame_len_before_marker && frame.path == handler_path
        })?;
        let blocked = self.handler_boundary_blocked_parts(
            guard_ids,
            carried_guards,
            handler.frame_index,
            handler.id,
            handler_path,
        );
        Some(EvidenceHandlerBoundary {
            id: handler.id,
            path: handler.path.clone(),
            blocked,
        })
    }

    fn handler_boundary_blocked_parts(
        &self,
        guard_ids: &[EvidenceGuardId],
        carried_guards: &[EvidenceCarriedGuard],
        handler_frame_index: usize,
        handler_id: EvidenceGuardId,
        handler_path: &[String],
    ) -> bool {
        self.carried_guard_for_matching_handler_parts(carried_guards, handler_frame_index)
            .is_some()
            || self.active_frames.iter().enumerate().any(|(index, frame)| {
                frame.id != handler_id
                    && self.guard_blocks_handler_parts(
                        guard_ids,
                        carried_guards,
                        frame.id,
                        handler_id,
                    )
                    && (index > handler_frame_index
                        || self.guard_frame_matches_handler(frame.id, handler_path))
            })
    }

    fn guard_frame_matches_handler(
        &self,
        guard_id: EvidenceGuardId,
        handler_path: &[String],
    ) -> bool {
        self.active_handler_frames
            .iter()
            .any(|frame| frame.id == guard_id && frame.path == handler_path)
    }

    fn close_marked_result(
        &mut self,
        result: EvidenceEvalResult,
        markers: &[EvidenceValueMarker],
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match result {
            EvidenceEvalResult::Value(value) => Ok(EvidenceEvalResult::Value(mark_runtime_value(
                value, markers,
            ))),
            EvidenceEvalResult::Effect(signal) => self.close_marked_signal(signal, markers),
        }
    }

    fn close_direct_abortive(
        &mut self,
        call: EvidenceDirectAbortive,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match call.close_cert() {
            EvidenceDirectAbortiveCloseCert::StaticAbortiveHandler => {
                Ok(EvidenceEvalResult::direct_abortive(call))
            }
        }
    }

    fn close_marked_signal(
        &mut self,
        signal: EvidenceEffectSignal,
        markers: &[EvidenceValueMarker],
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match signal {
            EvidenceEffectSignal::DirectAbortive(call) => self.close_direct_abortive(call),
            EvidenceEffectSignal::DirectTailResumptive(call) => {
                let markers = share_marker_vec(markers.to_vec());
                let resume_plan = self.resume_marker_plan(&markers, true, None);
                self.close_marker_direct_tail(call, markers, resume_plan, None)
            }
            EvidenceEffectSignal::RoutedYield(call) => {
                let markers = share_marker_vec(markers.to_vec());
                let resume_plan = self.resume_marker_plan(&markers, true, None);
                self.close_marker_routed_yield(call, markers, resume_plan)
            }
            EvidenceEffectSignal::GenericRequest(request) => self.close_marker_request(
                request,
                self.resume_marker_plan_for_slice(markers, true, None),
            ),
        }
    }

    fn close_marked_result_for_type(
        &mut self,
        result: EvidenceEvalResult,
        markers: &[EvidenceValueMarker],
        ty: &Type,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if markers.is_empty() || !type_may_need_hygiene_mark(ty) {
            return Ok(result);
        }
        match result {
            EvidenceEvalResult::Value(value) => Ok(EvidenceEvalResult::Value(
                mark_runtime_value_unchecked(value, markers),
            )),
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                self.close_direct_abortive(call)
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => {
                let markers = share_marker_vec(markers.to_vec());
                let resume_plan = self.resume_marker_plan(&markers, true, None);
                self.close_marker_direct_tail(call, markers, resume_plan, None)
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => {
                let markers = share_marker_vec(markers.to_vec());
                let resume_plan = self.resume_marker_plan(&markers, true, None);
                self.close_marker_routed_yield(call, markers, resume_plan)
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                self.close_marked_result(EvidenceEvalResult::request(request), markers)
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
        let mut result = self.eval_expr_result(expr, env)?;
        loop {
            match result {
                EvidenceEvalResult::Value(value) => return Ok(value),
                EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                    result = self.handle_escaped_request(request)?;
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                    return Err(RuntimeEvidenceRunError::EscapedEffect(call.path.to_vec()));
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => {
                    return Err(RuntimeEvidenceRunError::EscapedEffect(call.path.to_vec()));
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => {
                    return Err(RuntimeEvidenceRunError::EscapedEffect(
                        call.request().path.to_vec(),
                    ));
                }
            }
        }
    }

    fn handle_escaped_request(
        &mut self,
        request: EvidenceRequest,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if request.path.as_ref() == ["std", "io", "console", "out", "write"] {
            push_runtime_host_string_payload(request.payload.as_ref(), &mut self.stdout)
                .ok_or_else(|| RuntimeEvidenceRunError::EscapedEffect(request.path.to_vec()))?;
            return self
                .resume_continuation(request.continuation, shared(RuntimeEvidenceValue::Unit));
        }
        Err(RuntimeEvidenceRunError::EscapedEffect(
            request.path.to_vec(),
        ))
    }

    fn eval_expr_result(
        &mut self,
        expr: ExprId,
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        self.stats.expr_evals += 1;
        let expr_id = expr;
        match self
            .runtime_exprs
            .get(expr_id.0 as usize)
            .ok_or(RuntimeEvidenceRunError::MissingExpr(expr))?
        {
            RuntimeEvidenceExpr::Value(value) => {
                return Ok(EvidenceEvalResult::Value(value.clone()));
            }
            RuntimeEvidenceExpr::NullaryPrimitive { op, context } => {
                return Ok(EvidenceEvalResult::Value(
                    self.eval_primitive_op(*op, context.clone())?,
                ));
            }
            RuntimeEvidenceExpr::Local { slot, def } => {
                return Ok(EvidenceEvalResult::Value(
                    env.get_slot(*slot)
                        .ok_or(RuntimeEvidenceRunError::UnboundLocal(*def))?,
                ));
            }
            RuntimeEvidenceExpr::Instance(instance) => {
                return Ok(EvidenceEvalResult::Value(self.eval_instance(*instance)?));
            }
            RuntimeEvidenceExpr::Alias(expr) => return self.eval_expr_result(*expr, env),
            RuntimeEvidenceExpr::MakeThunk {
                body,
                provider_expr,
                needs_hygiene_mark,
            } => {
                let body = *body;
                let provider_expr = *provider_expr;
                let needs_hygiene_mark = *needs_hygiene_mark;
                let provider_env = self.provider_env_for_value(provider_expr);
                let env = self.clone_env(env);
                return Ok(EvidenceEvalResult::Value(shared(
                    RuntimeEvidenceValue::Thunk(Rc::new(RuntimeEvidenceThunk::Expr {
                        body,
                        env,
                        provider_env,
                        needs_hygiene_mark,
                    })),
                )));
            }
            RuntimeEvidenceExpr::Lambda {
                param,
                body,
                provider_expr,
            } => {
                let param = param.clone();
                let body = *body;
                let provider_expr = *provider_expr;
                let provider_env = self.provider_env_for_value(provider_expr);
                let env = self.clone_env(env);
                return Ok(EvidenceEvalResult::Value(shared(
                    RuntimeEvidenceValue::Closure(Rc::new(RuntimeEvidenceClosure {
                        param,
                        body,
                        env,
                        provider_env,
                    })),
                )));
            }
            RuntimeEvidenceExpr::FunctionAdapter {
                source,
                target,
                function,
                hygiene,
                provider_expr,
            } => {
                let source = source.clone();
                let target = target.clone();
                let function = *function;
                let hygiene = hygiene.clone();
                let provider_expr = *provider_expr;
                return match self.eval_expr_result(function, env)? {
                    EvidenceEvalResult::Value(function) => {
                        let provider_env = self.provider_env_for_value(provider_expr);
                        Ok(EvidenceEvalResult::Value(shared(
                            RuntimeEvidenceValue::FunctionAdapter {
                                source,
                                target,
                                function,
                                hygiene,
                                provider_env,
                            },
                        )))
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                        Ok(EvidenceEvalResult::request(
                            self.append_request_continuation(
                                request,
                                EvidenceContinuation::adapt_value(
                                    source,
                                    target,
                                    EvidenceContinuation::identity(),
                                ),
                            ),
                        ))
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                        Ok(EvidenceEvalResult::direct_abortive(call))
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(
                        call,
                    )) => self.continue_result(
                        EvidenceEvalResult::direct_tail_resumptive(call),
                        EvidenceContinuation::adapt_value(
                            source,
                            target,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => self
                        .continue_result(
                            EvidenceEvalResult::routed_yield(call),
                            EvidenceContinuation::adapt_value(
                                source,
                                target,
                                EvidenceContinuation::identity(),
                            ),
                        ),
                };
            }
            RuntimeEvidenceExpr::ForceThunk {
                target_value_is_thunk,
                thunk,
            } => {
                let target_value_is_thunk = *target_value_is_thunk;
                let thunk = *thunk;
                return match self.eval_expr_result(thunk, env)? {
                    EvidenceEvalResult::Value(thunk) => {
                        let result = self.force_thunk_result(thunk)?;
                        self.finish_force_thunk_result(result, target_value_is_thunk)
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                        Ok(EvidenceEvalResult::request(
                            self.append_request_continuation(
                                request,
                                EvidenceContinuation::force_thunk(
                                    target_value_is_thunk,
                                    EvidenceContinuation::identity(),
                                ),
                            ),
                        ))
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                        Ok(EvidenceEvalResult::direct_abortive(call))
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(
                        call,
                    )) => self.continue_result(
                        EvidenceEvalResult::direct_tail_resumptive(call),
                        EvidenceContinuation::force_thunk(
                            target_value_is_thunk,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => self
                        .continue_result(
                            EvidenceEvalResult::routed_yield(call),
                            EvidenceContinuation::force_thunk(
                                target_value_is_thunk,
                                EvidenceContinuation::identity(),
                            ),
                        ),
                };
            }
            RuntimeEvidenceExpr::ForceEffectCall {
                target_value_is_thunk,
                site,
                effect,
                path,
                arg,
            } => {
                let target_value_is_thunk = *target_value_is_thunk;
                let site = *site;
                let effect = *effect;
                let path = path.clone();
                let arg = *arg;
                return self.eval_force_effect_call_result(
                    target_value_is_thunk,
                    site,
                    effect,
                    &path,
                    arg,
                    env,
                );
            }
            RuntimeEvidenceExpr::MarkerFrame { path, body } => {
                let path = path.clone();
                let body = *body;
                let id = self.fresh_guard_id();
                let markers = stack_handler_markers(id, &path);
                return self.with_marker_frame(
                    EvidenceMarkerFrameSource::Expr,
                    share_marker_vec(markers),
                    true,
                    Some(path.to_vec()),
                    |runner| runner.eval_expr_result(body, env),
                );
            }
            RuntimeEvidenceExpr::Apply { site, callee, arg } => {
                return self.eval_apply_result(Some(*site), *callee, *arg, env);
            }
            RuntimeEvidenceExpr::RefSet { reference, value } => {
                return self.eval_ref_set_result(*reference, *value, env);
            }
            RuntimeEvidenceExpr::Tuple(items) => {
                let items = items.clone();
                return self.eval_tuple_items_result(Vec::with_capacity(items.len()), &items, env);
            }
            RuntimeEvidenceExpr::Record { fields, spread } => {
                let fields = fields.clone();
                let spread = spread.clone();
                return self.eval_record_result(&fields, &spread, env);
            }
            RuntimeEvidenceExpr::PolyVariant { tag, payloads } => {
                let tag = tag.clone();
                let payloads = payloads.clone();
                return self.eval_poly_variant_payloads_result(
                    tag,
                    Vec::with_capacity(payloads.len()),
                    &payloads,
                    env,
                );
            }
            RuntimeEvidenceExpr::Select {
                base,
                name,
                resolution,
            } => {
                let name = name.clone();
                let resolution = resolution.clone();
                return self.eval_select_result(*base, &name, &resolution, env);
            }
            RuntimeEvidenceExpr::Case { expr, scrutinee } => {
                let arms = self.static_case_arms(*expr);
                return match self.eval_expr_result(*scrutinee, env)? {
                    EvidenceEvalResult::Value(scrutinee) => {
                        self.eval_case_scrutinee_result(scrutinee, arms, env)
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                        let env = self.clone_env(env);
                        Ok(EvidenceEvalResult::request(
                            self.append_request_continuation(
                                request,
                                EvidenceContinuation::case_scrutinee(
                                    arms,
                                    env,
                                    EvidenceContinuation::identity(),
                                ),
                            ),
                        ))
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                        Ok(EvidenceEvalResult::direct_abortive(call))
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(
                        call,
                    )) => {
                        let env = self.clone_env(env);
                        self.continue_result(
                            EvidenceEvalResult::direct_tail_resumptive(call),
                            EvidenceContinuation::case_scrutinee(
                                arms,
                                env,
                                EvidenceContinuation::identity(),
                            ),
                        )
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => {
                        let env = self.clone_env(env);
                        self.continue_result(
                            EvidenceEvalResult::routed_yield(call),
                            EvidenceContinuation::case_scrutinee(
                                arms,
                                env,
                                EvidenceContinuation::identity(),
                            ),
                        )
                    }
                };
            }
            RuntimeEvidenceExpr::Catch { expr, body } => return self.eval_catch(*expr, *body, env),
            RuntimeEvidenceExpr::Block { stmts, tail } => {
                let stmts = stmts.clone();
                let tail = *tail;
                self.eval_block_parts_result(&stmts, tail, env, shared(RuntimeEvidenceValue::Unit))
            }
        }
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
            EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                let env = self.clone_env(env);
                Ok(EvidenceEvalResult::request(
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
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                Ok(EvidenceEvalResult::direct_abortive(call))
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => {
                let env = self.clone_env(env);
                self.continue_result(
                    EvidenceEvalResult::direct_tail_resumptive(call),
                    EvidenceContinuation::apply_callee(
                        site,
                        arg_expr,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                )
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => {
                let env = self.clone_env(env);
                self.continue_result(
                    EvidenceEvalResult::routed_yield(call),
                    EvidenceContinuation::apply_callee(
                        site,
                        arg_expr,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                )
            }
        }
    }

    fn eval_force_effect_call_result(
        &mut self,
        target_value_is_thunk: bool,
        site: ExprId,
        effect: ExprId,
        path: &[String],
        arg_expr: ExprId,
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let mut arg_env = self.clone_env(env);
        match self.eval_expr_result(arg_expr, &mut arg_env)? {
            EvidenceEvalResult::Value(arg) => {
                let resolved_route = self.effect_route_for_operation_call(Some(site), effect);
                let route_cert = self.effect_route_cert(resolved_route.origin);
                let evidence = EffectThunkEvidence {
                    route_cert,
                    visibility: resolved_route.visibility,
                };
                self.force_effect_call_scoped_result(
                    target_value_is_thunk,
                    path,
                    arg,
                    resolved_route.route,
                    evidence,
                )
            }
            result => {
                let callee = shared(RuntimeEvidenceValue::EffectOp {
                    expr: effect,
                    path: shared_path(path),
                });
                self.continue_result(
                    result,
                    EvidenceContinuation::apply_arg(
                        Some(site),
                        callee,
                        EvidenceContinuation::force_thunk(
                            target_value_is_thunk,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                )
            }
        }
    }

    fn force_effect_call_scoped_result(
        &mut self,
        target_value_is_thunk: bool,
        path: &[String],
        arg: SharedValue,
        route: EvidenceEffectRoute,
        evidence: EffectThunkEvidence,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let boundary = self.active_function_call_boundary(EvidenceMarkerFrameSource::MarkedForce);
        match boundary {
            Err(
                EvidenceCallBoundaryBypassCert::NoActiveMarkerPlan
                | EvidenceCallBoundaryBypassCert::NoFunctionCallMarkers,
            ) => self.force_effect_call_payload_result(
                target_value_is_thunk,
                path,
                arg,
                route,
                evidence,
            ),
            Ok(boundary) => self.with_call_boundary(boundary, |runner| {
                runner.force_effect_call_payload_result(
                    target_value_is_thunk,
                    path,
                    arg,
                    route,
                    evidence,
                )
            }),
        }
    }

    fn force_effect_call_payload_result(
        &mut self,
        target_value_is_thunk: bool,
        path: &[String],
        arg: SharedValue,
        route: EvidenceEffectRoute,
        evidence: EffectThunkEvidence,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        self.stats.forced_effect_call_fusions += 1;
        let result = self.force_effect_result(path, arg, route, evidence)?;
        self.finish_force_thunk_result(result, target_value_is_thunk)
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
            EvidenceEvalResult::Value(arg) => self.apply_scoped_value_result(site, callee, arg),
            EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => Ok(
                EvidenceEvalResult::request(self.append_request_continuation(
                    request,
                    EvidenceContinuation::apply_arg(site, callee, EvidenceContinuation::identity()),
                )),
            ),
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                Ok(EvidenceEvalResult::direct_abortive(call))
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => self
                .continue_result(
                    EvidenceEvalResult::direct_tail_resumptive(call),
                    EvidenceContinuation::apply_arg(site, callee, EvidenceContinuation::identity()),
                ),
            EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => self
                .continue_result(
                    EvidenceEvalResult::routed_yield(call),
                    EvidenceContinuation::apply_arg(site, callee, EvidenceContinuation::identity()),
                ),
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
            EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request))
                if request_is_ref_update(&request) =>
            {
                let resumed = self.resume_continuation(request.continuation, assigned.clone())?;
                self.handle_ref_set_result(resumed, assigned)
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
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
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                Ok(EvidenceEvalResult::direct_abortive(call))
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => self
                .continue_result(
                    EvidenceEvalResult::direct_tail_resumptive(call),
                    EvidenceContinuation::ref_set_handle_result(
                        assigned,
                        EvidenceContinuation::identity(),
                    ),
                ),
            EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => self
                .continue_result(
                    EvidenceEvalResult::routed_yield(call),
                    EvidenceContinuation::ref_set_handle_result(
                        assigned,
                        EvidenceContinuation::identity(),
                    ),
                ),
        }
    }

    fn handle_ref_set_value_result(
        &mut self,
        result: EvidenceEvalResult,
        assigned: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match result {
            EvidenceEvalResult::Value(value) => self.resolve_ref_set_value(value, assigned),
            EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request))
                if request_is_ref_update(&request) =>
            {
                let resumed = self.resume_continuation(request.continuation, assigned.clone())?;
                self.handle_ref_set_value_result(resumed, assigned)
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
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
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                Ok(EvidenceEvalResult::direct_abortive(call))
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => self
                .continue_result(
                    EvidenceEvalResult::direct_tail_resumptive(call),
                    EvidenceContinuation::ref_set_handle_value_result(
                        assigned,
                        EvidenceContinuation::identity(),
                    ),
                ),
            EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => self
                .continue_result(
                    EvidenceEvalResult::routed_yield(call),
                    EvidenceContinuation::ref_set_handle_value_result(
                        assigned,
                        EvidenceContinuation::identity(),
                    ),
                ),
        }
    }

    fn resolve_ref_set_value(
        &mut self,
        value: SharedValue,
        assigned: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match value.as_ref() {
            RuntimeEvidenceValue::Marked { value, markers } => {
                let result = self.resolve_ref_set_value(value.clone(), assigned)?;
                self.close_marked_result(result, markers)
            }
            RuntimeEvidenceValue::Tuple(values) => self.resolve_ref_set_values(
                values.clone(),
                assigned,
                Vec::new(),
                0,
                EvidenceRefSetFinish::Tuple,
            ),
            RuntimeEvidenceValue::List(values) => self.resolve_ref_set_values(
                values.to_vec(),
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
                EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                    let rest = shared_expr_ids(&items[index + 1..]);
                    let env = self.clone_env(env);
                    return Ok(EvidenceEvalResult::request(
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
                EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                    return Ok(EvidenceEvalResult::direct_abortive(call));
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => {
                    let rest = shared_expr_ids(&items[index + 1..]);
                    let env = self.clone_env(env);
                    return self.continue_result(
                        EvidenceEvalResult::direct_tail_resumptive(call),
                        EvidenceContinuation::tuple_items(
                            values,
                            rest,
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    );
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => {
                    let rest = shared_expr_ids(&items[index + 1..]);
                    let env = self.clone_env(env);
                    return self.continue_result(
                        EvidenceEvalResult::routed_yield(call),
                        EvidenceContinuation::tuple_items(
                            values,
                            rest,
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    );
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
                EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                    let env = self.clone_env(env);
                    return Ok(EvidenceEvalResult::request(
                        self.append_request_continuation(
                            request,
                            EvidenceContinuation::record_spread(
                                shared_record_fields(fields),
                                env,
                                EvidenceContinuation::identity(),
                            ),
                        ),
                    ));
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                    return Ok(EvidenceEvalResult::direct_abortive(call));
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => {
                    let env = self.clone_env(env);
                    return self.continue_result(
                        EvidenceEvalResult::direct_tail_resumptive(call),
                        EvidenceContinuation::record_spread(
                            shared_record_fields(fields),
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    );
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => {
                    let env = self.clone_env(env);
                    return self.continue_result(
                        EvidenceEvalResult::routed_yield(call),
                        EvidenceContinuation::record_spread(
                            shared_record_fields(fields),
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    );
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
                EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                    let rest = shared_record_fields(&fields[index..]);
                    let env = self.clone_env(env);
                    return Ok(EvidenceEvalResult::request(
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
                EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                    return Ok(EvidenceEvalResult::direct_abortive(call));
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => {
                    let rest = shared_record_fields(&fields[index..]);
                    let env = self.clone_env(env);
                    return self.continue_result(
                        EvidenceEvalResult::direct_tail_resumptive(call),
                        EvidenceContinuation::record_fields(
                            values,
                            rest,
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    );
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => {
                    let rest = shared_record_fields(&fields[index..]);
                    let env = self.clone_env(env);
                    return self.continue_result(
                        EvidenceEvalResult::routed_yield(call),
                        EvidenceContinuation::record_fields(
                            values,
                            rest,
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    );
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
                EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                    let rest = shared_expr_ids(&payloads[index + 1..]);
                    let env = self.clone_env(env);
                    return Ok(EvidenceEvalResult::request(
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
                EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                    return Ok(EvidenceEvalResult::direct_abortive(call));
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => {
                    let rest = shared_expr_ids(&payloads[index + 1..]);
                    let env = self.clone_env(env);
                    return self.continue_result(
                        EvidenceEvalResult::direct_tail_resumptive(call),
                        EvidenceContinuation::poly_variant_payloads(
                            tag,
                            values,
                            rest,
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    );
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => {
                    let rest = shared_expr_ids(&payloads[index + 1..]);
                    let env = self.clone_env(env);
                    return self.continue_result(
                        EvidenceEvalResult::routed_yield(call),
                        EvidenceContinuation::poly_variant_payloads(
                            tag,
                            values,
                            rest,
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    );
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
            EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => Ok(
                EvidenceEvalResult::request(self.append_request_continuation(
                    request,
                    EvidenceContinuation::select_base(
                        name.to_string(),
                        resolution.clone(),
                        EvidenceContinuation::identity(),
                    ),
                )),
            ),
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                Ok(EvidenceEvalResult::direct_abortive(call))
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => self
                .continue_result(
                    EvidenceEvalResult::direct_tail_resumptive(call),
                    EvidenceContinuation::select_base(
                        name.to_string(),
                        resolution.clone(),
                        EvidenceContinuation::identity(),
                    ),
                ),
            EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => self
                .continue_result(
                    EvidenceEvalResult::routed_yield(call),
                    EvidenceContinuation::select_base(
                        name.to_string(),
                        resolution.clone(),
                        EvidenceContinuation::identity(),
                    ),
                ),
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

    fn apply_scoped_value_result(
        &mut self,
        site: Option<ExprId>,
        callee: SharedValue,
        arg: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let boundary = self.active_function_call_boundary(EvidenceMarkerFrameSource::ScopedApply);
        match boundary {
            Err(
                EvidenceCallBoundaryBypassCert::NoActiveMarkerPlan
                | EvidenceCallBoundaryBypassCert::NoFunctionCallMarkers,
            ) => self.apply_value_result(site, callee, arg),
            Ok(boundary) => match callee.as_ref() {
                RuntimeEvidenceValue::Marked { .. } => {
                    let callee =
                        mark_runtime_value_unchecked_shared(callee, boundary.markers.clone());
                    self.apply_value_result(site, callee, arg)
                }
                callee_value if callee_apply_closes_without_frame(callee_value) => {
                    let result = self.apply_value_result(site, callee, arg)?;
                    self.close_call_boundary_without_frame(result, &boundary)
                }
                _ => self.with_call_boundary(boundary, |runner| {
                    runner.apply_value_result(site, callee, arg)
                }),
            },
        }
    }

    fn apply_value_result(
        &mut self,
        site: Option<ExprId>,
        callee: SharedValue,
        arg: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        self.with_call_provider_env(site, |runner| {
            runner.apply_value_result_inner(site, callee, arg)
        })
    }

    fn apply_value_result_inner(
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
                provider_env,
            } => {
                let provider_env = provider_env.clone();
                self.observe_provider_env(&provider_env);
                self.with_provider_env(provider_env, |runner| {
                    runner.apply_adapter_result(source, target, function.clone(), hygiene, arg)
                })
            }
            RuntimeEvidenceValue::ConstructorFunction { def, arity, args } => {
                let mut args = args.clone();
                args.push(arg);
                Ok(EvidenceEvalResult::Value(shared(constructor_value(
                    *def, *arity, args,
                ))))
            }
            RuntimeEvidenceValue::Closure(closure) => {
                let closure = closure.clone();
                let provider_env = closure.provider_env.clone();
                self.observe_provider_env(&provider_env);
                self.with_provider_env(provider_env, |runner| {
                    let mut env = runner.clone_env(&closure.env);
                    runner.bind_pat(&closure.param, arg, &mut env)?;
                    runner.eval_expr_result(closure.body, &mut env)
                })
            }
            RuntimeEvidenceValue::RecursiveClosure { def, closure } => {
                let def = *def;
                let closure = closure.clone();
                let provider_env = closure.provider_env.clone();
                self.observe_provider_env(&provider_env);
                self.with_provider_env(provider_env, |runner| {
                    let mut env = runner.clone_env(&closure.env);
                    env.insert_slot(
                        EnvSlot::from(def),
                        shared(RuntimeEvidenceValue::RecursiveClosure {
                            def,
                            closure: closure.clone(),
                        }),
                    );
                    runner.bind_pat(&closure.param, arg, &mut env)?;
                    runner.eval_expr_result(closure.body, &mut env)
                })
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
                EvidenceEvalResult::Value(callee) => {
                    self.apply_value_result_inner(site, callee, arg)
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => Ok(
                    EvidenceEvalResult::request(self.append_request_continuation(
                        request,
                        EvidenceContinuation::apply_forced_callee(
                            site,
                            arg,
                            EvidenceContinuation::identity(),
                        ),
                    )),
                ),
                EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                    Ok(EvidenceEvalResult::direct_abortive(call))
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => {
                    self.continue_result(
                        EvidenceEvalResult::direct_tail_resumptive(call),
                        EvidenceContinuation::apply_forced_callee(
                            site,
                            arg,
                            EvidenceContinuation::identity(),
                        ),
                    )
                }
                EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => self
                    .continue_result(
                        EvidenceEvalResult::routed_yield(call),
                        EvidenceContinuation::apply_forced_callee(
                            site,
                            arg,
                            EvidenceContinuation::identity(),
                        ),
                    ),
            },
            RuntimeEvidenceValue::EffectOp { expr, path } => {
                let resolved_route = self.effect_route_for_operation_call(site, *expr);
                let route_cert = self.effect_route_cert(resolved_route.origin);
                let evidence = EffectThunkEvidence {
                    route_cert,
                    visibility: resolved_route.visibility,
                };
                Ok(EvidenceEvalResult::Value(shared(
                    RuntimeEvidenceValue::Thunk(Rc::new(RuntimeEvidenceThunk::Effect {
                        path: path.clone(),
                        payload: arg,
                        route: resolved_route.route,
                        evidence,
                    })),
                )))
            }
            RuntimeEvidenceValue::Marked { value, markers } => {
                let markers = if matches!(value.as_ref(), RuntimeEvidenceValue::Continuation(_)) {
                    markers_for_continuation_call_shared(markers)
                } else {
                    markers_for_function_call_shared(markers)
                };
                self.with_marker_frame(
                    EvidenceMarkerFrameSource::MarkedApply,
                    markers,
                    true,
                    None,
                    |runner| runner.apply_value_result_inner(site, value.clone(), arg),
                )
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
        let body_markers = self.instantiate_hygiene_markers(&hygiene.markers);
        let arg_markers = combined_markers(
            &body_markers,
            &self.instantiate_hygiene_markers(&hygiene.arg_markers),
        );
        let ret_markers = combined_markers(
            &body_markers,
            &self.instantiate_hygiene_markers(&hygiene.ret_markers),
        );
        self.with_marker_frame(
            EvidenceMarkerFrameSource::Adapter,
            share_marker_vec(body_markers.clone()),
            true,
            None,
            |runner| {
                let function = mark_runtime_value_unchecked(function, &body_markers);
                let arg = mark_runtime_value_for_type(arg, &arg_markers, &target_arg);
                let result = runner.adapt_value_result(arg, &target_arg, &source_arg)?;
                runner.continue_result(
                    result,
                    EvidenceContinuation::apply_adapter_arg(
                        function,
                        ret_markers,
                        source_ret,
                        target_ret,
                        EvidenceContinuation::identity(),
                    ),
                )
            },
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
                    provider_env: RuntimeEvidenceProviderEnv::default(),
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
        if continuation.is_identity() {
            return Ok(EvidenceEvalResult::Value(value));
        }
        self.stats.continuation_resume_steps += 1;
        let frame = continuation
            .into_frame()
            .expect("non-identity continuation must have a frame");
        self.record_continuation_resume_frame(&frame);
        match frame {
            EvidenceContinuationFrame::Then { first, second } => {
                self.record_continuation_resume_then_boundary(&first, &second);
                let result = self.resume_continuation(first, value)?;
                self.continue_result(result, second)
            }
            EvidenceContinuationFrame::ForceThunk {
                target_value_is_thunk,
                next,
            } => {
                let result = self.force_thunk_result(value)?;
                if target_value_is_thunk {
                    self.continue_result(result, next)
                } else {
                    self.continue_result(result, EvidenceContinuation::force_value_if_thunk(next))
                }
            }
            EvidenceContinuationFrame::ForceValueIfThunk { next } => {
                let result = self.force_value_if_thunk_result(value)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::ApplyCallee {
                site,
                arg,
                env,
                next,
            } => {
                let mut env = self.clone_env(&env);
                let result = self.eval_apply_arg_result(site, value, arg, &mut env)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::ApplyArg { site, callee, next } => {
                let result = self.apply_scoped_value_result(site, callee, value)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::ApplyForcedCallee { site, arg, next } => {
                let result = self.apply_scoped_value_result(site, value, arg)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::AdaptValue {
                source,
                target,
                next,
            } => {
                let result = self.adapt_value_result(value, &source, &target)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::WrapThunkValue { next } => self.continue_result(
                EvidenceEvalResult::Value(shared(RuntimeEvidenceValue::Thunk(Rc::new(
                    RuntimeEvidenceThunk::Value(value),
                )))),
                next,
            ),
            EvidenceContinuationFrame::ApplyAdapterArg {
                function,
                ret_markers,
                source_ret,
                target_ret,
                next,
            } => {
                let result = self.apply_value_result(None, function, value)?;
                self.continue_result(
                    result,
                    EvidenceContinuation::apply_adapter_result(
                        ret_markers,
                        source_ret,
                        target_ret,
                        next,
                    ),
                )
            }
            EvidenceContinuationFrame::ApplyAdapterResult {
                ret_markers,
                source_ret,
                target_ret,
                next,
            } => {
                let result = self.adapt_value_result(value, &source_ret, &target_ret)?;
                let result =
                    self.close_marked_result_for_type(result, &ret_markers, &target_ret)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::CaseScrutinee { arms, env, next } => {
                let result = self.eval_case_scrutinee_result(value, arms, &env)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::CatchBody {
                catch_expr,
                arms,
                env,
                next,
            } => {
                let result = self.continue_catch_body_result(
                    catch_expr,
                    arms,
                    &env,
                    EvidenceEvalResult::Value(value),
                )?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::MarkerFrame {
                markers,
                activate_add_ids,
                handler_path,
                next,
            } => self.resume_marker_frame(markers, activate_add_ids, handler_path, next, value),
            EvidenceContinuationFrame::ProviderEnv { provider_env, next } => self
                .with_provider_env(provider_env, |runner| {
                    runner.resume_continuation(next, value)
                }),
            EvidenceContinuationFrame::TupleItems {
                values,
                rest,
                env,
                next,
            } => {
                let mut values = values;
                values.push(value);
                let mut env = self.clone_env(&env);
                let result = self.eval_tuple_items_result(values, &rest, &mut env)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::RecordSpread { fields, env, next } => {
                let values = record_fields(value.as_ref())?;
                let mut env = self.clone_env(&env);
                let result = self.eval_record_fields_result(values, &fields, &mut env)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::RecordFields {
                values,
                rest,
                env,
                next,
            } => {
                let mut values = values;
                let Some((field, remaining)) = rest.split_first() else {
                    return Err(RuntimeEvidenceRunError::UnsupportedExpr(
                        "empty record field continuation",
                    ));
                };
                values.push(RuntimeEvidenceValueField {
                    name: field.name.clone(),
                    value,
                });
                let mut env = self.clone_env(&env);
                let result = self.eval_record_fields_result(values, remaining, &mut env)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::PolyVariantPayloads {
                tag,
                values,
                rest,
                env,
                next,
            } => {
                let mut values = values;
                values.push(value);
                let mut env = self.clone_env(&env);
                let result =
                    self.eval_poly_variant_payloads_result(tag, values, &rest, &mut env)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::SelectBase {
                name,
                resolution,
                next,
            } => {
                let result = self.apply_select_base_result(value, &name, &resolution)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::BlockStmt {
                resume,
                rest,
                tail,
                env,
                last,
                next,
            } => {
                let mut env = self.clone_env(&env);
                let last = match resume {
                    EvidenceBlockResume::Let(pat) => {
                        let value = recursive_let_value(&pat, value);
                        self.bind_pat(&pat, value, &mut env)?;
                        last.clone()
                    }
                    EvidenceBlockResume::Expr => value,
                };
                let result = self.eval_block_parts_result(&rest, tail, &mut env, last)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::RefSetReference {
                value: expr,
                env,
                next,
            } => {
                let result = self.force_value_if_thunk_result(value)?;
                let env = self.clone_env(&env);
                self.continue_result(
                    result,
                    EvidenceContinuation::ref_set_forced_reference(expr, env, next),
                )
            }
            EvidenceContinuationFrame::RefSetForcedReference {
                value: expr,
                env,
                next,
            } => {
                let mut env = self.clone_env(&env);
                let result = self.eval_expr_result(expr, &mut env)?;
                self.continue_result(result, EvidenceContinuation::ref_set_value(value, next))
            }
            EvidenceContinuationFrame::RefSetValue { reference, next } => {
                let result = self.force_value_if_thunk_result(value)?;
                self.continue_result(
                    result,
                    EvidenceContinuation::ref_set_forced_value(reference, next),
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
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::RefSetResolvedUnit { next } => self.continue_result(
                EvidenceEvalResult::Value(shared(RuntimeEvidenceValue::Unit)),
                next,
            ),
            EvidenceContinuationFrame::RefSetHandleResult { assigned, next } => {
                let result =
                    self.handle_ref_set_result(EvidenceEvalResult::Value(value), assigned)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::RefSetHandleValueResult { assigned, next } => {
                let result =
                    self.handle_ref_set_value_result(EvidenceEvalResult::Value(value), assigned)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::RefSetEmitResolvedRequest {
                mut request,
                assigned,
                mode,
                next,
            } => {
                request.payload = value;
                let frame = match mode {
                    EvidenceRefSetResumeMode::Result => {
                        EvidenceContinuation::ref_set_handle_result(assigned, next)
                    }
                    EvidenceRefSetResumeMode::ValueResult => {
                        EvidenceContinuation::ref_set_handle_value_result(assigned, next)
                    }
                };
                Ok(EvidenceEvalResult::request(
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
                let mut out = out;
                out.push(value);
                let result =
                    self.resolve_ref_set_values(values, assigned, out, index + 1, finish)?;
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::ResolveRefSetFields {
                fields,
                assigned,
                out,
                index,
                next,
            } => {
                let mut out = out;
                out.push(RuntimeEvidenceValueField {
                    name: fields[index].name.clone(),
                    value,
                });
                let result = self.resolve_ref_set_fields(fields, assigned, out, index + 1)?;
                self.continue_result(result, next)
            }
        }
    }

    fn record_continuation_resume_frame(&mut self, frame: &EvidenceContinuationFrame) {
        match frame {
            EvidenceContinuationFrame::Then { .. } => {
                self.stats.continuation_resume_then_steps += 1;
            }
            EvidenceContinuationFrame::ForceThunk { .. }
            | EvidenceContinuationFrame::ForceValueIfThunk { .. } => {
                self.stats.continuation_resume_force_steps += 1;
            }
            EvidenceContinuationFrame::ApplyCallee { .. }
            | EvidenceContinuationFrame::ApplyArg { .. }
            | EvidenceContinuationFrame::ApplyForcedCallee { .. } => {
                self.stats.continuation_resume_apply_steps += 1;
            }
            EvidenceContinuationFrame::AdaptValue { .. }
            | EvidenceContinuationFrame::WrapThunkValue { .. }
            | EvidenceContinuationFrame::ApplyAdapterArg { .. }
            | EvidenceContinuationFrame::ApplyAdapterResult { .. } => {
                self.stats.continuation_resume_adapter_steps += 1;
            }
            EvidenceContinuationFrame::CaseScrutinee { .. } => {
                self.stats.continuation_resume_case_steps += 1;
            }
            EvidenceContinuationFrame::CatchBody { .. } => {
                self.stats.continuation_resume_catch_steps += 1;
            }
            EvidenceContinuationFrame::MarkerFrame { .. } => {
                self.stats.continuation_resume_marker_steps += 1;
            }
            EvidenceContinuationFrame::ProviderEnv { .. } => {
                self.stats.continuation_resume_provider_steps += 1;
            }
            EvidenceContinuationFrame::TupleItems { .. }
            | EvidenceContinuationFrame::RecordSpread { .. }
            | EvidenceContinuationFrame::RecordFields { .. }
            | EvidenceContinuationFrame::PolyVariantPayloads { .. } => {
                self.stats.continuation_resume_aggregate_steps += 1;
            }
            EvidenceContinuationFrame::SelectBase { .. } => {
                self.stats.continuation_resume_select_steps += 1;
            }
            EvidenceContinuationFrame::BlockStmt { .. } => {
                self.stats.continuation_resume_block_steps += 1;
            }
            EvidenceContinuationFrame::RefSetReference { .. }
            | EvidenceContinuationFrame::RefSetForcedReference { .. }
            | EvidenceContinuationFrame::RefSetValue { .. }
            | EvidenceContinuationFrame::RefSetForcedValue { .. }
            | EvidenceContinuationFrame::RefSetResolvedUnit { .. }
            | EvidenceContinuationFrame::RefSetHandleResult { .. }
            | EvidenceContinuationFrame::RefSetHandleValueResult { .. }
            | EvidenceContinuationFrame::RefSetEmitResolvedRequest { .. }
            | EvidenceContinuationFrame::ResolveRefSetValues { .. }
            | EvidenceContinuationFrame::ResolveRefSetFields { .. } => {
                self.stats.continuation_resume_ref_set_steps += 1;
            }
        }
    }

    fn record_continuation_resume_then_boundary(
        &mut self,
        first: &EvidenceContinuation,
        second: &EvidenceContinuation,
    ) {
        let first_kind = first.boundary_kind();
        let second_kind = second.boundary_kind();
        match first_kind {
            EvidenceContinuationBoundaryKind::MarkerFrame => {
                self.stats.continuation_resume_then_first_marker_frame += 1;
            }
            EvidenceContinuationBoundaryKind::ProviderEnv => {
                self.stats.continuation_resume_then_first_provider_env += 1;
            }
            EvidenceContinuationBoundaryKind::Identity
            | EvidenceContinuationBoundaryKind::Other => {
                self.stats.continuation_resume_then_first_other += 1;
            }
        }
        match second_kind {
            EvidenceContinuationBoundaryKind::MarkerFrame => {
                self.stats.continuation_resume_then_second_marker_frame += 1;
            }
            EvidenceContinuationBoundaryKind::ProviderEnv => {
                self.stats.continuation_resume_then_second_provider_env += 1;
            }
            EvidenceContinuationBoundaryKind::Identity
            | EvidenceContinuationBoundaryKind::Other => {
                self.stats.continuation_resume_then_second_other += 1;
            }
        }
        if !matches!(
            first_kind,
            EvidenceContinuationBoundaryKind::MarkerFrame
                | EvidenceContinuationBoundaryKind::ProviderEnv
        ) && !matches!(
            second_kind,
            EvidenceContinuationBoundaryKind::MarkerFrame
                | EvidenceContinuationBoundaryKind::ProviderEnv
        ) {
            self.stats.continuation_resume_then_plain += 1;
        }
    }

    fn continue_result(
        &mut self,
        result: EvidenceEvalResult,
        continuation: EvidenceContinuation,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if continuation.is_identity() {
            return Ok(result);
        }
        match result {
            EvidenceEvalResult::Value(value) => self.resume_continuation(continuation, value),
            EvidenceEvalResult::Effect(signal) => self.continue_signal(signal, continuation),
        }
    }

    fn continue_signal(
        &mut self,
        signal: EvidenceEffectSignal,
        continuation: EvidenceContinuation,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match signal {
            EvidenceEffectSignal::GenericRequest(request) => {
                self.continue_request_with_continuation(request, continuation)
            }
            EvidenceEffectSignal::DirectAbortive(call) => {
                self.continue_direct_abortive_with_continuation(call, continuation)
            }
            EvidenceEffectSignal::DirectTailResumptive(call) => {
                self.continue_direct_tail_resumptive_with_continuation(call, continuation)
            }
            EvidenceEffectSignal::RoutedYield(call) => {
                self.continue_routed_yield_with_continuation(call, continuation)
            }
        }
    }

    fn continue_direct_abortive_with_continuation(
        &mut self,
        call: EvidenceDirectAbortive,
        continuation: EvidenceContinuation,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if continuation.is_identity() {
            return Ok(EvidenceEvalResult::direct_abortive(call));
        }
        let frame = continuation
            .into_frame()
            .expect("non-identity continuation must have a frame");
        match frame {
            EvidenceContinuationFrame::Then { first, second } => {
                let result = self.continue_direct_abortive_with_continuation(call, first)?;
                self.continue_result(result, second)
            }
            EvidenceContinuationFrame::CatchBody {
                catch_expr,
                arms,
                env,
                next,
            } => {
                let result = if call.handler == catch_expr {
                    self.eval_direct_abortive_arm(call, &arms, &env)?
                } else {
                    EvidenceEvalResult::direct_abortive(call)
                };
                self.continue_result(result, next)
            }
            EvidenceContinuationFrame::ForceThunk { next, .. }
            | EvidenceContinuationFrame::ForceValueIfThunk { next }
            | EvidenceContinuationFrame::ApplyArg { next, .. }
            | EvidenceContinuationFrame::ApplyForcedCallee { next, .. }
            | EvidenceContinuationFrame::AdaptValue { next, .. }
            | EvidenceContinuationFrame::WrapThunkValue { next }
            | EvidenceContinuationFrame::ApplyAdapterArg { next, .. }
            | EvidenceContinuationFrame::ApplyAdapterResult { next, .. }
            | EvidenceContinuationFrame::MarkerFrame { next, .. }
            | EvidenceContinuationFrame::ProviderEnv { next, .. }
            | EvidenceContinuationFrame::SelectBase { next, .. }
            | EvidenceContinuationFrame::RefSetValue { next, .. }
            | EvidenceContinuationFrame::RefSetForcedValue { next, .. }
            | EvidenceContinuationFrame::RefSetResolvedUnit { next }
            | EvidenceContinuationFrame::RefSetHandleResult { next, .. }
            | EvidenceContinuationFrame::RefSetHandleValueResult { next, .. }
            | EvidenceContinuationFrame::RefSetEmitResolvedRequest { next, .. }
            | EvidenceContinuationFrame::ResolveRefSetValues { next, .. }
            | EvidenceContinuationFrame::ResolveRefSetFields { next, .. } => {
                self.continue_direct_abortive_with_continuation(call, next)
            }
            EvidenceContinuationFrame::ApplyCallee { next, .. }
            | EvidenceContinuationFrame::CaseScrutinee { next, .. }
            | EvidenceContinuationFrame::TupleItems { next, .. }
            | EvidenceContinuationFrame::RecordSpread { next, .. }
            | EvidenceContinuationFrame::RecordFields { next, .. }
            | EvidenceContinuationFrame::PolyVariantPayloads { next, .. }
            | EvidenceContinuationFrame::BlockStmt { next, .. }
            | EvidenceContinuationFrame::RefSetReference { next, .. }
            | EvidenceContinuationFrame::RefSetForcedReference { next, .. } => {
                self.continue_direct_abortive_with_continuation(call, next)
            }
        }
    }

    fn continue_direct_tail_resumptive_with_continuation(
        &mut self,
        call: EvidenceDirectTailResumptive,
        continuation: EvidenceContinuation,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if continuation.is_identity() {
            return Ok(EvidenceEvalResult::direct_tail_resumptive(call));
        }
        if !continuation.has_request_boundary(Some(call.handler)) {
            let call = self.append_direct_tail_continuation(call, continuation);
            return Ok(EvidenceEvalResult::direct_tail_resumptive(call));
        }
        let frame = continuation
            .into_frame()
            .expect("non-identity continuation must have a frame");
        let (call, next) = match frame {
            EvidenceContinuationFrame::Then { first, second } => {
                let result = self.continue_direct_tail_resumptive_with_continuation(call, first)?;
                return self.continue_result(result, second);
            }
            EvidenceContinuationFrame::ForceThunk {
                target_value_is_thunk,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::force_thunk(
                        target_value_is_thunk,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::ForceValueIfThunk { next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::force_value_if_thunk(EvidenceContinuation::identity()),
                ),
                next,
            ),
            EvidenceContinuationFrame::ApplyCallee {
                site,
                arg,
                env,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::apply_callee(
                        site,
                        arg,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::ApplyArg { site, callee, next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::apply_arg(site, callee, EvidenceContinuation::identity()),
                ),
                next,
            ),
            EvidenceContinuationFrame::ApplyForcedCallee { site, arg, next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::apply_forced_callee(
                        site,
                        arg,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::AdaptValue {
                source,
                target,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::adapt_value(
                        source,
                        target,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::WrapThunkValue { next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::wrap_thunk_value(EvidenceContinuation::identity()),
                ),
                next,
            ),
            EvidenceContinuationFrame::ApplyAdapterArg {
                function,
                ret_markers,
                source_ret,
                target_ret,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::apply_adapter_arg(
                        function,
                        ret_markers,
                        source_ret,
                        target_ret,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::ApplyAdapterResult {
                ret_markers,
                source_ret,
                target_ret,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::apply_adapter_result(
                        ret_markers,
                        source_ret,
                        target_ret,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::CaseScrutinee { arms, env, next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::case_scrutinee(
                        arms,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::CatchBody {
                catch_expr,
                arms,
                env,
                next,
            } => {
                if call.handler == catch_expr {
                    let result = if self
                        .visible_direct_tail_resumptive(catch_expr, &call, &arms)
                        .is_some()
                    {
                        self.eval_direct_tail_resumptive_arm(call, &arms, &env)?
                    } else {
                        let request = call.into_request(EvidenceEffectRoute::Unhandled);
                        EvidenceEvalResult::request(
                            self.defer_catch_body(catch_expr, arms, &env, request),
                        )
                    };
                    return self.continue_result(result, next);
                }
                (
                    self.append_direct_tail_continuation(
                        call,
                        EvidenceContinuation::catch_body(
                            catch_expr,
                            arms,
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                    next,
                )
            }
            EvidenceContinuationFrame::MarkerFrame {
                markers,
                activate_add_ids,
                handler_path,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::marker_frame(
                        markers,
                        activate_add_ids,
                        handler_path,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::ProviderEnv { provider_env, next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::provider_env(
                        provider_env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::TupleItems {
                values,
                rest,
                env,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::tuple_items(
                        values,
                        rest,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RecordSpread { fields, env, next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::record_spread(
                        fields,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RecordFields {
                values,
                rest,
                env,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::record_fields(
                        values,
                        rest,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::PolyVariantPayloads {
                tag,
                values,
                rest,
                env,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::poly_variant_payloads(
                        tag,
                        values,
                        rest,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::SelectBase {
                name,
                resolution,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::select_base(
                        name,
                        resolution,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::BlockStmt {
                resume,
                rest,
                tail,
                env,
                last,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::block_stmt(
                        resume,
                        rest,
                        tail,
                        env,
                        last,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetReference { value, env, next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::ref_set_reference(
                        value,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetForcedReference { value, env, next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::ref_set_forced_reference(
                        value,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetValue { reference, next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::ref_set_value(
                        reference,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetForcedValue { reference, next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::ref_set_forced_value(
                        reference,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetResolvedUnit { next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::ref_set_resolved_unit(EvidenceContinuation::identity()),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetHandleResult { assigned, next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::ref_set_handle_result(
                        assigned,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetHandleValueResult { assigned, next } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::ref_set_handle_value_result(
                        assigned,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetEmitResolvedRequest {
                request,
                assigned,
                mode,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::ref_set_emit_resolved_request(
                        request,
                        assigned,
                        mode,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::ResolveRefSetValues {
                values,
                assigned,
                out,
                index,
                finish,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::resolve_ref_set_values(
                        values,
                        assigned,
                        out,
                        index,
                        finish,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::ResolveRefSetFields {
                fields,
                assigned,
                out,
                index,
                next,
            } => (
                self.append_direct_tail_continuation(
                    call,
                    EvidenceContinuation::resolve_ref_set_fields(
                        fields,
                        assigned,
                        out,
                        index,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
        };
        self.continue_direct_tail_resumptive_with_continuation(call, next)
    }

    fn continue_routed_yield_with_continuation(
        &mut self,
        call: EvidenceRoutedYield,
        continuation: EvidenceContinuation,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if continuation.is_identity() {
            return Ok(EvidenceEvalResult::routed_yield(call));
        }
        if !continuation.has_request_boundary(Some(call.handler)) {
            self.stats.request_whole_continuation_appends += 1;
            let call = call.append_continuation(continuation, &mut self.stats);
            return Ok(EvidenceEvalResult::routed_yield(call));
        }
        self.continue_routed_request_with_continuation(
            Some(call.handler),
            call.into_request(),
            continuation,
        )
    }

    fn continue_request_with_continuation(
        &mut self,
        request: EvidenceRequest,
        continuation: EvidenceContinuation,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        self.continue_routed_request_with_continuation(None, request, continuation)
    }

    fn continue_routed_request_with_continuation(
        &mut self,
        routed_yield_handler: Option<ExprId>,
        request: EvidenceRequest,
        continuation: EvidenceContinuation,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if continuation.is_identity() {
            return Ok(self.routed_request_result(routed_yield_handler, request));
        }
        if !continuation.has_request_boundary(routed_yield_handler) {
            self.stats.request_whole_continuation_appends += 1;
            let request = self.append_request_continuation(request, continuation);
            return Ok(self.routed_request_result(routed_yield_handler, request));
        }
        if routed_yield_handler.is_none() {
            self.stats.request_continuation_steps += 1;
        }
        let frame = continuation
            .into_frame()
            .expect("non-identity continuation must have a frame");
        let (request, next) = match frame {
            EvidenceContinuationFrame::Then { first, second } => {
                let result = self.continue_routed_request_with_continuation(
                    routed_yield_handler,
                    request,
                    first,
                )?;
                return self.continue_result(result, second);
            }
            EvidenceContinuationFrame::ForceThunk {
                target_value_is_thunk,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::force_thunk(
                        target_value_is_thunk,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::ForceValueIfThunk { next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::force_value_if_thunk(EvidenceContinuation::identity()),
                ),
                next,
            ),
            EvidenceContinuationFrame::ApplyCallee {
                site,
                arg,
                env,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::apply_callee(
                        site,
                        arg,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::ApplyArg { site, callee, next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::apply_arg(site, callee, EvidenceContinuation::identity()),
                ),
                next,
            ),
            EvidenceContinuationFrame::ApplyForcedCallee { site, arg, next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::apply_forced_callee(
                        site,
                        arg,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::AdaptValue {
                source,
                target,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::adapt_value(
                        source,
                        target,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::WrapThunkValue { next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::wrap_thunk_value(EvidenceContinuation::identity()),
                ),
                next,
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
                        function,
                        ret_markers,
                        source_ret,
                        target_ret,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
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
                        ret_markers,
                        source_ret,
                        target_ret,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::CaseScrutinee { arms, env, next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::case_scrutinee(
                        arms,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::CatchBody {
                catch_expr,
                arms,
                env,
                next,
            } => {
                let result = if let Some(handler) = routed_yield_handler {
                    if handler == catch_expr {
                        self.eval_routed_yield_arm(
                            EvidenceRoutedYield::from_request(handler, request),
                            catch_expr,
                            arms,
                            &env,
                        )?
                    } else {
                        let request = self.append_request_continuation(
                            request,
                            EvidenceContinuation::catch_body(
                                catch_expr,
                                arms,
                                env,
                                EvidenceContinuation::identity(),
                            ),
                        );
                        return self.continue_routed_request_with_continuation(
                            routed_yield_handler,
                            request,
                            next,
                        );
                    }
                } else {
                    self.continue_catch_body_result(
                        catch_expr,
                        arms,
                        &env,
                        EvidenceEvalResult::request(request),
                    )?
                };
                return self.continue_result(result, next);
            }
            EvidenceContinuationFrame::MarkerFrame {
                markers,
                activate_add_ids,
                handler_path,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::marker_frame(
                        markers,
                        activate_add_ids,
                        handler_path,
                        next,
                    ),
                ),
                EvidenceContinuation::identity(),
            ),
            EvidenceContinuationFrame::ProviderEnv { provider_env, next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::provider_env(provider_env, next),
                ),
                EvidenceContinuation::identity(),
            ),
            EvidenceContinuationFrame::TupleItems {
                values,
                rest,
                env,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::tuple_items(
                        values,
                        rest,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RecordSpread { fields, env, next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::record_spread(
                        fields,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RecordFields {
                values,
                rest,
                env,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::record_fields(
                        values,
                        rest,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::PolyVariantPayloads {
                tag,
                values,
                rest,
                env,
                next,
            } => (
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
                next,
            ),
            EvidenceContinuationFrame::SelectBase {
                name,
                resolution,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::select_base(
                        name,
                        resolution,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::BlockStmt {
                resume,
                rest,
                tail,
                env,
                last,
                next,
            } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::block_stmt(
                        resume,
                        rest,
                        tail,
                        env,
                        last,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetReference { value, env, next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::ref_set_reference(
                        value,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetForcedReference { value, env, next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::ref_set_forced_reference(
                        value,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetValue { reference, next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::ref_set_value(
                        reference,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetForcedValue { reference, next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::ref_set_forced_value(
                        reference,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetResolvedUnit { next } => (
                self.append_request_continuation(
                    request,
                    EvidenceContinuation::ref_set_resolved_unit(EvidenceContinuation::identity()),
                ),
                next,
            ),
            EvidenceContinuationFrame::RefSetHandleResult { assigned, next } => {
                let result = self.handle_ref_set_result(
                    self.routed_request_result(routed_yield_handler, request),
                    assigned,
                )?;
                return self.continue_result(result, next);
            }
            EvidenceContinuationFrame::RefSetHandleValueResult { assigned, next } => {
                let result = self.handle_ref_set_value_result(
                    self.routed_request_result(routed_yield_handler, request),
                    assigned,
                )?;
                return self.continue_result(result, next);
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
                        pending,
                        assigned,
                        mode,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
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
                        values,
                        assigned,
                        out,
                        index,
                        finish,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
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
                        fields,
                        assigned,
                        out,
                        index,
                        EvidenceContinuation::identity(),
                    ),
                ),
                next,
            ),
        };
        self.continue_routed_request_with_continuation(routed_yield_handler, request, next)
    }

    fn routed_request_result(
        &self,
        routed_yield_handler: Option<ExprId>,
        request: EvidenceRequest,
    ) -> EvidenceEvalResult {
        match routed_yield_handler {
            Some(handler) => EvidenceEvalResult::routed_yield(EvidenceRoutedYield::from_request(
                handler, request,
            )),
            None => EvidenceEvalResult::request(request),
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

    fn force_effect_result(
        &mut self,
        path: &[String],
        payload: SharedValue,
        route: EvidenceEffectRoute,
        evidence: EffectThunkEvidence,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let path = shared_path(path);
        if let EvidenceEffectRoute::Direct {
            handler,
            execution: EvidenceVmOperationExecutionPlan::DirectAbortive,
            ..
        } = route
        {
            return Ok(EvidenceEvalResult::direct_abortive(
                EvidenceDirectAbortive::static_handler(handler, path.clone(), payload),
            ));
        }
        if let EvidenceEffectRoute::Direct {
            handler,
            execution: EvidenceVmOperationExecutionPlan::DirectTailResumptive,
            request_free_yield,
            ..
        } = route
        {
            if let Some(fail) = self.direct_tail_gate_failure(request_free_yield, evidence, &path) {
                if let ProviderGrantPathGateFail::AddIdShadowed(shadowed) = fail {
                    self.record_direct_tail_guarded_add_id(shadowed.kind);
                    return Ok(EvidenceEvalResult::direct_tail_resumptive(
                        self.provider_permission_guarded_direct_tail_resumptive(
                            handler,
                            path.clone(),
                            payload,
                            evidence,
                            shadowed,
                        ),
                    ));
                } else {
                    self.record_direct_tail_gate_fail(fail);
                }
            } else {
                return Ok(EvidenceEvalResult::direct_tail_resumptive(
                    self.direct_tail_resumptive(handler, path.clone(), payload, evidence),
                ));
            }
        }
        if let EvidenceEffectRoute::Direct {
            handler,
            execution: EvidenceVmOperationExecutionPlan::YieldFallback,
            request_free_yield,
            ..
        } = route
            && self.route_allows_routed_yield(request_free_yield, evidence)
        {
            let mut request = EvidenceRequest {
                path: path.clone(),
                payload,
                route,
                hygiene: EvidenceSignalHygiene::new()
                    .with_operation_visibility(evidence.visibility),
                continuation: EvidenceContinuation::identity(),
            };
            self.mark_request_with_active_markers(&mut request);
            return Ok(EvidenceEvalResult::routed_yield(
                EvidenceRoutedYield::from_request(handler, request),
            ));
        }
        let mut request = EvidenceRequest {
            path,
            payload,
            route,
            hygiene: EvidenceSignalHygiene::new().with_operation_visibility(evidence.visibility),
            continuation: EvidenceContinuation::identity(),
        };
        if !request.route.is_direct_abortive() {
            self.mark_request_with_active_markers(&mut request);
        }
        Ok(EvidenceEvalResult::request(request))
    }

    fn force_thunk_result(
        &mut self,
        thunk: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        self.stats.thunk_forces += 1;
        match thunk.as_ref() {
            RuntimeEvidenceValue::Thunk(thunk) => match thunk.as_ref() {
                RuntimeEvidenceThunk::Expr {
                    body,
                    env,
                    provider_env,
                    ..
                } => {
                    self.stats.thunk_force_expr += 1;
                    let provider_env = provider_env.clone();
                    self.observe_provider_env(&provider_env);
                    self.with_provider_env(provider_env, |runner| {
                        let mut env = runner.clone_env(env);
                        runner.eval_expr_result(*body, &mut env)
                    })
                }
                RuntimeEvidenceThunk::Effect {
                    path,
                    payload,
                    route,
                    evidence,
                } => {
                    self.stats.thunk_force_effect += 1;
                    self.force_effect_result(path, payload.clone(), *route, *evidence)
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
                if let Some((value, markers)) =
                    marked_force_value_thunk(value.as_ref(), markers.clone())
                {
                    self.stats.marked_force_value_fast_paths += 1;
                    return Ok(EvidenceEvalResult::Value(mark_runtime_value_shared(
                        value, markers,
                    )));
                }
                let marker_summary = marked_force_marker_summary(&markers);
                self.stats.marked_force_active_add_id_markers += marker_summary.active_add_ids;
                self.stats.marked_force_carry_after_frame_markers +=
                    marker_summary.carry_after_frame;
                self.record_marked_force_fallback(value.as_ref());
                self.with_marker_frame(
                    EvidenceMarkerFrameSource::MarkedForce,
                    markers.clone(),
                    true,
                    None,
                    |runner| runner.force_thunk_result(value.clone()),
                )
            }
            value => Err(RuntimeEvidenceRunError::NotThunk(format_value(value))),
        }
    }

    fn record_marked_force_fallback(&mut self, value: &RuntimeEvidenceValue) {
        match marked_force_thunk_kind(value) {
            Some(RuntimeEvidenceThunkKind::Expr) => {
                self.stats.marked_force_fallback_expr_thunks += 1;
            }
            Some(RuntimeEvidenceThunkKind::Effect) => {
                self.stats.marked_force_fallback_effect_thunks += 1;
            }
            Some(RuntimeEvidenceThunkKind::Continuation) => {
                self.stats.marked_force_fallback_continuation_thunks += 1;
            }
            Some(RuntimeEvidenceThunkKind::Adapter) => {
                self.stats.marked_force_fallback_adapter_thunks += 1;
            }
            Some(RuntimeEvidenceThunkKind::Value) | None => {
                self.stats.marked_force_fallback_other += 1;
            }
        }
    }

    fn eval_catch(
        &mut self,
        catch_expr: ExprId,
        body: ExprId,
        env: &Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let arms = self.static_catch_arms(catch_expr);
        let mut body_env = self.clone_env(env);
        let provider_len = self.active_provider_handlers.len();
        self.active_provider_handlers
            .extend_from_slice(self.context.handler_ids_for_catch(catch_expr));
        let result = self.eval_expr_result(body, &mut body_env);
        self.active_provider_handlers.truncate(provider_len);
        let result = result?;
        self.continue_catch_body_result(catch_expr, arms, env, result)
    }

    fn continue_catch_body_result(
        &mut self,
        catch_expr: ExprId,
        arms: Rc<[control_vm::CatchArm]>,
        env: &Env,
        result: EvidenceEvalResult,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        self.stats.catch_body_checks += 1;
        match result {
            EvidenceEvalResult::Value(value) => self.eval_value_arm(value, &arms, env),
            EvidenceEvalResult::Effect(signal) => {
                self.continue_catch_body_signal(catch_expr, arms, env, signal)
            }
        }
    }

    fn continue_catch_body_signal(
        &mut self,
        catch_expr: ExprId,
        arms: Rc<[control_vm::CatchArm]>,
        env: &Env,
        signal: EvidenceEffectSignal,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match signal {
            EvidenceEffectSignal::DirectAbortive(call) => {
                if call.handler == catch_expr {
                    self.eval_direct_abortive_arm(call, &arms, env)
                } else {
                    Ok(EvidenceEvalResult::direct_abortive(call))
                }
            }
            EvidenceEffectSignal::DirectTailResumptive(call) => {
                if call.handler == catch_expr {
                    if self
                        .visible_direct_tail_resumptive(catch_expr, &call, &arms)
                        .is_some()
                    {
                        self.eval_direct_tail_resumptive_arm(call, &arms, env)
                    } else {
                        let request = call.into_request(EvidenceEffectRoute::Unhandled);
                        Ok(EvidenceEvalResult::request(
                            self.defer_catch_body(catch_expr, arms, env, request),
                        ))
                    }
                } else {
                    let env = self.clone_env(env);
                    Ok(EvidenceEvalResult::direct_tail_resumptive(
                        self.append_direct_tail_continuation(
                            call,
                            EvidenceContinuation::catch_body(
                                catch_expr,
                                arms,
                                env,
                                EvidenceContinuation::identity(),
                            ),
                        ),
                    ))
                }
            }
            EvidenceEffectSignal::RoutedYield(call) => {
                if call.handler == catch_expr {
                    self.eval_routed_yield_arm(call, catch_expr, arms, env)
                } else {
                    Ok(EvidenceEvalResult::routed_yield(call))
                }
            }
            EvidenceEffectSignal::GenericRequest(request) => match request.route {
                EvidenceEffectRoute::Direct {
                    handler,
                    resumptive,
                    ..
                } if handler == catch_expr => {
                    match self.visible_operation_resumptive(catch_expr, &request, &arms) {
                        Some(_) => self.eval_operation_arm(request, resumptive, &arms, env),
                        None => {
                            let mut request = request;
                            request.route = EvidenceEffectRoute::Unhandled;
                            Ok(EvidenceEvalResult::request(
                                self.defer_catch_body(catch_expr, arms, env, request),
                            ))
                        }
                    }
                }
                EvidenceEffectRoute::Direct { .. } => Ok(EvidenceEvalResult::request(
                    self.defer_catch_body(catch_expr, arms, env, request),
                )),
                EvidenceEffectRoute::Unhandled => {
                    if let Some(resumptive) =
                        self.visible_operation_resumptive(catch_expr, &request, &arms)
                    {
                        self.eval_operation_arm(request, resumptive, &arms, env)
                    } else {
                        Ok(EvidenceEvalResult::request(
                            self.defer_catch_body(catch_expr, arms, env, request),
                        ))
                    }
                }
            },
        }
    }

    fn visible_operation_resumptive(
        &mut self,
        catch_expr: ExprId,
        request: &EvidenceRequest,
        arms: &[control_vm::CatchArm],
    ) -> Option<bool> {
        let exposure = EvidenceGuardBoundaryExposure::from_hygiene(&request.hygiene);
        self.record_permission_visibility_stats(&request.hygiene);
        let visible = self.visible_operation_resumptive_parts(&request.path, exposure, arms);
        self.record_permission_visibility_shadow(
            catch_expr,
            &request.path,
            &request.hygiene,
            arms,
            visible,
        );
        visible
    }

    fn operation_arm_visible(
        &self,
        request_path: &[String],
        arms: &[control_vm::CatchArm],
    ) -> Option<bool> {
        arms.iter().find_map(|arm| {
            let operation_path = arm.operation_path.as_ref()?;
            (operation_path.as_slice() == request_path).then_some(arm.continuation.is_some())
        })
    }

    fn visible_operation_resumptive_parts(
        &self,
        request_path: &[String],
        exposure: EvidenceGuardBoundaryExposure<'_>,
        arms: &[control_vm::CatchArm],
    ) -> Option<bool> {
        arms.iter().find_map(|arm| {
            let operation_path = arm.operation_path.as_ref()?;
            if operation_path.as_slice() != request_path {
                return None;
            }
            let skipped_guard = match exposure.handler_boundary {
                Some(boundary) if path_is_prefix(&boundary.path, request_path) => boundary
                    .blocked
                    .then_some(EvidenceGuardSkip::Preserve(boundary.id)),
                Some(boundary) => Some(EvidenceGuardSkip::Preserve(boundary.id)),
                None => self.request_guard_for_path_parts(
                    exposure.guard_ids,
                    exposure.carried_guards,
                    operation_path,
                ),
            };
            skipped_guard
                .is_none()
                .then_some(arm.continuation.is_some())
        })
    }

    fn visible_direct_tail_resumptive(
        &mut self,
        catch_expr: ExprId,
        call: &EvidenceDirectTailResumptive,
        arms: &[control_vm::CatchArm],
    ) -> Option<bool> {
        self.record_permission_visibility_stats(&call.hygiene);
        if let Some(permission) = self.provider_guard_boundary_permission(&call.hygiene) {
            let native_result = self.permission_visible_guard_boundary_pair_native(
                catch_expr, &call.path, permission, arms,
            );
            let native_visible = native_result.visible();
            if self.should_verify_permission_visibility() {
                let permission_result = self.permission_visible_guard_boundary_pair_bridge(
                    catch_expr,
                    &call.path,
                    &call.hygiene,
                    permission,
                    arms,
                );
                let bridge_visible = permission_result.visible();
                let exposure = EvidenceGuardBoundaryExposure::from_hygiene(&call.hygiene);
                let legacy_visible =
                    self.visible_operation_resumptive_parts(&call.path, exposure, arms);
                self.record_provider_boundary_pair_shadow(legacy_visible, permission_result);
                self.record_provider_boundary_pair_native_shadow(legacy_visible, native_result);
                debug_assert_eq!(
                    bridge_visible,
                    legacy_visible,
                    "bridge provider permission visibility diverged from legacy hygiene for {}",
                    call.path.join("::")
                );
                debug_assert_eq!(
                    native_visible,
                    legacy_visible,
                    "native provider permission visibility diverged from legacy hygiene for {}",
                    call.path.join("::")
                );
            }
            self.record_provider_boundary_pair_fast_path(native_result);
            return native_visible;
        }

        let exposure = EvidenceGuardBoundaryExposure::from_hygiene(&call.hygiene);
        let visible = self.visible_operation_resumptive_parts(&call.path, exposure, arms);
        self.record_permission_visibility_shadow(
            catch_expr,
            &call.path,
            &call.hygiene,
            arms,
            visible,
        );
        visible
    }

    fn provider_guard_boundary_permission(
        &self,
        hygiene: &EvidenceSignalHygiene,
    ) -> Option<RuntimeEvidenceProviderGrantPermission> {
        let EvidencePermissionShadowKind::ProviderGrantBoundaryPair(permission) =
            hygiene.permission_shadow_kind()?
        else {
            return None;
        };
        Some(permission)
    }

    fn should_verify_permission_visibility(&self) -> bool {
        cfg!(debug_assertions)
    }

    fn record_permission_visibility_shadow(
        &mut self,
        catch_expr: ExprId,
        request_path: &[String],
        hygiene: &EvidenceSignalHygiene,
        arms: &[control_vm::CatchArm],
        legacy_visible: Option<bool>,
    ) {
        let Some(shadow_kind) = hygiene.permission_shadow_kind() else {
            return;
        };
        match shadow_kind {
            EvidencePermissionShadowKind::Direct => {
                #[cfg(debug_assertions)]
                {
                    let Some(visibility) = hygiene.operation_visibility() else {
                        return;
                    };
                    let permission_visible = self.permission_visible_operation_resumptive(
                        catch_expr,
                        request_path,
                        visibility,
                        arms,
                    );
                    debug_assert_eq!(
                        permission_visible,
                        legacy_visible,
                        "permission visibility ({shadow_kind:?}) diverged from legacy hygiene for {}",
                        request_path.join("::")
                    );
                }
            }
            EvidencePermissionShadowKind::ProviderGrantBoundaryPair(permission) => {
                let permission_result = self.permission_visible_guard_boundary_pair_bridge(
                    catch_expr,
                    request_path,
                    hygiene,
                    permission,
                    arms,
                );
                let permission_visible = permission_result.visible();
                self.record_provider_boundary_pair_shadow(legacy_visible, permission_result);
                debug_assert_eq!(
                    permission_visible,
                    legacy_visible,
                    "permission visibility ({shadow_kind:?}) diverged from legacy hygiene for {}",
                    request_path.join("::")
                );
            }
        }
    }

    #[cfg(test)]
    fn provider_guard_boundary_permission_decision(
        &self,
        catch_expr: ExprId,
        request_path: &[String],
        hygiene: &EvidenceSignalHygiene,
        arms: &[control_vm::CatchArm],
    ) -> EvidencePermissionVisibleDecision {
        let Some(EvidencePermissionShadowKind::ProviderGrantBoundaryPair(permission)) =
            hygiene.permission_shadow_kind()
        else {
            return EvidencePermissionVisibleDecision::NotApplicable;
        };
        EvidencePermissionVisibleDecision::Handled(
            self.permission_visible_guard_boundary_pair_bridge(
                catch_expr,
                request_path,
                hygiene,
                permission,
                arms,
            ),
        )
    }

    #[cfg(debug_assertions)]
    fn permission_visible_operation_resumptive(
        &self,
        catch_expr: ExprId,
        request_path: &[String],
        visibility: RuntimeEvidenceOperationVisibility,
        arms: &[control_vm::CatchArm],
    ) -> Option<bool> {
        let arm_resumptive = arms.iter().find_map(|arm| {
            let operation_path = arm.operation_path.as_ref()?;
            (operation_path.as_slice() == request_path).then_some(arm.continuation.is_some())
        })?;
        self.context
            .catch_has_allowed_handler(catch_expr, request_path, visibility)
            .then_some(arm_resumptive)
    }

    fn permission_visible_guard_boundary_pair_bridge(
        &self,
        catch_expr: ExprId,
        request_path: &[String],
        hygiene: &EvidenceSignalHygiene,
        permission: RuntimeEvidenceProviderGrantPermission,
        arms: &[control_vm::CatchArm],
    ) -> EvidencePermissionVisibleResult {
        if !self
            .context
            .catch_has_provider_grant_permission(catch_expr, request_path, permission)
        {
            return EvidencePermissionVisibleResult::NoAllowedHandler;
        }
        let exposure = EvidenceGuardBoundaryExposure::from_hygiene(hygiene);
        EvidencePermissionVisibleResult::Visible(self.visible_operation_resumptive_parts(
            request_path,
            exposure,
            arms,
        ))
    }

    fn permission_visible_guard_boundary_pair_native(
        &self,
        catch_expr: ExprId,
        request_path: &[String],
        permission: RuntimeEvidenceProviderGrantPermission,
        arms: &[control_vm::CatchArm],
    ) -> EvidencePermissionVisibleResult {
        if !self
            .context
            .catch_has_provider_grant_permission(catch_expr, request_path, permission)
        {
            return EvidencePermissionVisibleResult::NoAllowedHandler;
        }
        EvidencePermissionVisibleResult::Visible(self.operation_arm_visible(request_path, arms))
    }

    fn record_provider_boundary_pair_shadow(
        &mut self,
        legacy_visible: Option<bool>,
        permission_result: EvidencePermissionVisibleResult,
    ) {
        self.stats.permission_shadow_provider_boundary_pair += 1;
        if legacy_visible.is_some() {
            self.stats
                .permission_shadow_provider_boundary_pair_legacy_visible += 1;
        }
        let permission_visible = permission_result.visible();
        if permission_visible.is_some() {
            self.stats
                .permission_shadow_provider_boundary_pair_permission_visible += 1;
        }
        if permission_result.no_allowed_handler() {
            self.stats
                .permission_shadow_provider_boundary_pair_no_allowed_handler += 1;
        }
        if legacy_visible == permission_visible {
            self.stats.permission_shadow_provider_boundary_pair_match += 1;
        } else {
            self.stats.permission_shadow_provider_boundary_pair_mismatch += 1;
        }
    }

    fn record_provider_boundary_pair_fast_path(
        &mut self,
        permission_result: EvidencePermissionVisibleResult,
    ) {
        self.stats.permission_provider_boundary_pair_fast_paths += 1;
        if permission_result.visible().is_some() {
            self.stats
                .permission_provider_boundary_pair_fast_path_visible += 1;
        } else {
            self.stats
                .permission_provider_boundary_pair_fast_path_invisible += 1;
        }
        if permission_result.no_allowed_handler() {
            self.stats
                .permission_provider_boundary_pair_fast_path_no_allowed_handler += 1;
        }
    }

    fn record_provider_boundary_pair_native_shadow(
        &mut self,
        legacy_visible: Option<bool>,
        native_result: EvidencePermissionVisibleResult,
    ) {
        self.stats.permission_provider_boundary_pair_native_shadow += 1;
        if legacy_visible.is_some() {
            self.stats
                .permission_provider_boundary_pair_native_shadow_legacy_visible += 1;
        }
        let native_visible = native_result.visible();
        if native_visible.is_some() {
            self.stats
                .permission_provider_boundary_pair_native_shadow_native_visible += 1;
        }
        if native_result.no_allowed_handler() {
            self.stats
                .permission_provider_boundary_pair_native_shadow_no_allowed_handler += 1;
        }
        if legacy_visible == native_visible {
            self.stats
                .permission_provider_boundary_pair_native_shadow_match += 1;
        } else {
            self.stats
                .permission_provider_boundary_pair_native_shadow_mismatch += 1;
        }
    }

    #[cfg(debug_assertions)]
    fn record_provider_add_id_shortcut_full_scan_guard_visible(
        &mut self,
        shortcut_hygiene: &EvidenceSignalHygiene,
        full_scan_hygiene: &EvidenceSignalHygiene,
        request_path: &[String],
    ) {
        let shortcut_visible = self
            .request_guard_for_path_parts(
                &shortcut_hygiene.guard_ids,
                &shortcut_hygiene.carried_guards,
                request_path,
            )
            .is_none();
        let full_scan_visible = self
            .request_guard_for_path_parts(
                &full_scan_hygiene.guard_ids,
                &full_scan_hygiene.carried_guards,
                request_path,
            )
            .is_none();
        if shortcut_visible == full_scan_visible {
            self.stats
                .provider_add_id_shortcut_full_scan_guard_visible_match += 1;
        } else {
            self.stats
                .provider_add_id_shortcut_full_scan_guard_visible_mismatch += 1;
        }
        self.stats.provider_add_id_shortcut_full_scan_extra_guards += full_scan_hygiene
            .guard_ids
            .iter()
            .filter(|id| !shortcut_hygiene.guard_ids.contains(id))
            .count();
        self.stats
            .provider_add_id_shortcut_full_scan_extra_carried_guards += full_scan_hygiene
            .carried_guards
            .iter()
            .filter(|guard| {
                !shortcut_hygiene
                    .carried_guards
                    .iter()
                    .any(|shortcut| shortcut.id == guard.id)
            })
            .count();
    }

    fn record_permission_visibility_stats(&mut self, hygiene: &EvidenceSignalHygiene) {
        let Some(visibility) = hygiene.permission_visibility.base else {
            return;
        };
        self.stats.permission_visibility_signals += 1;
        if visibility.legacy_guard_bridge() {
            self.stats.permission_visibility_legacy_bridge += 1;
            return;
        }
        let transform = hygiene.permission_visibility.transform;
        if transform.is_identity() {
            self.stats.permission_visibility_identity += 1;
            return;
        }
        if transform.guard_mask {
            self.stats.permission_visibility_guard_mask += 1;
        }
        if transform.resume_delta {
            self.stats.permission_visibility_resume_delta += 1;
        }
        if transform.handler_boundary_mask {
            self.stats.permission_visibility_handler_boundary_mask += 1;
        }
        if transform.is_guard_boundary_pair() {
            self.stats.permission_visibility_guard_and_boundary_mask += 1;
        } else if transform.is_guard_only() {
            self.stats.permission_visibility_guard_without_boundary += 1;
        } else if transform.is_boundary_only() {
            self.stats.permission_visibility_boundary_without_guard += 1;
        }
    }

    fn handler_boundary_for_direct_tail(
        &self,
        call: &EvidenceDirectTailResumptive,
        handler_path: Option<&[String]>,
        frame_len_before_marker: usize,
    ) -> Option<EvidenceHandlerBoundary> {
        self.handler_boundary_for_request_parts(
            &call.hygiene.guard_ids,
            &call.hygiene.carried_guards,
            handler_path,
            frame_len_before_marker,
        )
    }

    fn defer_catch_body(
        &mut self,
        catch_expr: ExprId,
        arms: Rc<[control_vm::CatchArm]>,
        env: &Env,
        request: EvidenceRequest,
    ) -> EvidenceRequest {
        let env = self.clone_env(env);
        self.append_request_continuation(
            request,
            EvidenceContinuation::catch_body(
                catch_expr,
                arms,
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
        for arm in arms {
            if arm.operation_path.is_some() {
                continue;
            }
            let mut arm_env = self.clone_env(env);
            if !self.bind_pat_matches(&arm.pat, value.clone(), &mut arm_env)? {
                continue;
            }
            if !self.arm_guard_matches(arm.guard, &mut arm_env)? {
                continue;
            }
            return self.eval_expr_result(arm.body, &mut arm_env);
        }
        Ok(EvidenceEvalResult::Value(value))
    }

    fn eval_operation_arm(
        &mut self,
        request: EvidenceRequest,
        resumptive: bool,
        arms: &[control_vm::CatchArm],
        env: &Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        for arm in arms {
            if arm.operation_path.as_deref() != Some(request.path.as_ref()) {
                continue;
            }
            let mut arm_env = self.clone_env(env);
            if !self.bind_pat_matches(&arm.pat, request.payload.clone(), &mut arm_env)? {
                continue;
            }
            if let Some(continuation_pat) = &arm.continuation {
                if !resumptive {
                    return Err(RuntimeEvidenceRunError::UnsupportedExpr(
                        "abortive continuation binding",
                    ));
                }
                if !self.bind_pat_matches(
                    continuation_pat,
                    shared(RuntimeEvidenceValue::Continuation(
                        request.continuation.clone(),
                    )),
                    &mut arm_env,
                )? {
                    continue;
                }
            }
            if !self.arm_guard_matches(arm.guard, &mut arm_env)? {
                continue;
            }
            return self.eval_handler_body_result(arm.body, &mut arm_env);
        }
        Ok(EvidenceEvalResult::request(request))
    }

    fn eval_direct_abortive_arm(
        &mut self,
        call: EvidenceDirectAbortive,
        arms: &[control_vm::CatchArm],
        env: &Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        for arm in arms {
            if arm.operation_path.as_deref() != Some(call.path.as_ref()) {
                continue;
            }
            let mut arm_env = self.clone_env(env);
            if !self.bind_pat_matches(&arm.pat, call.payload.clone(), &mut arm_env)? {
                continue;
            }
            if arm
                .continuation
                .as_ref()
                .is_some_and(|pat| !matches!(pat, Pat::Wild))
            {
                return Err(RuntimeEvidenceRunError::UnsupportedExpr(
                    "direct abortive continuation binding",
                ));
            }
            if !self.arm_guard_matches(arm.guard, &mut arm_env)? {
                continue;
            }
            return self.eval_handler_body_result(arm.body, &mut arm_env);
        }
        Ok(EvidenceEvalResult::direct_abortive(call))
    }

    fn eval_direct_tail_resumptive_arm(
        &mut self,
        call: EvidenceDirectTailResumptive,
        arms: &[control_vm::CatchArm],
        env: &Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        for arm in arms {
            if arm.operation_path.as_deref() != Some(call.path.as_ref()) {
                continue;
            }
            let mut arm_env = self.clone_env(env);
            if !self.bind_pat_matches(&arm.pat, call.payload.clone(), &mut arm_env)? {
                continue;
            }
            if let Some(continuation_pat) = &arm.continuation
                && !self.bind_pat_matches(
                    continuation_pat,
                    shared(RuntimeEvidenceValue::Continuation(
                        call.continuation.clone(),
                    )),
                    &mut arm_env,
                )?
            {
                continue;
            }
            if !self.arm_guard_matches(arm.guard, &mut arm_env)? {
                continue;
            }
            return self.eval_handler_body_result(arm.body, &mut arm_env);
        }
        Ok(EvidenceEvalResult::direct_tail_resumptive(call))
    }

    fn eval_routed_yield_arm(
        &mut self,
        call: EvidenceRoutedYield,
        catch_expr: ExprId,
        arms: Rc<[control_vm::CatchArm]>,
        env: &Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        let mut request = call.into_request();
        let resumptive = match request.route {
            EvidenceEffectRoute::Direct { resumptive, .. } => resumptive,
            EvidenceEffectRoute::Unhandled => {
                return Ok(EvidenceEvalResult::request(
                    self.defer_catch_body(catch_expr, arms, env, request),
                ));
            }
        };
        if self
            .visible_operation_resumptive(catch_expr, &request, &arms)
            .is_some()
        {
            return self.eval_operation_arm(request, resumptive, &arms, env);
        }
        request.route = EvidenceEffectRoute::Unhandled;
        Ok(EvidenceEvalResult::request(
            self.defer_catch_body(catch_expr, arms, env, request),
        ))
    }

    fn bind_pat_matches(
        &mut self,
        pat: &Pat,
        value: SharedValue,
        env: &mut Env,
    ) -> Result<bool, RuntimeEvidenceRunError> {
        match self.bind_pat(pat, value, env) {
            Ok(()) => Ok(true),
            Err(RuntimeEvidenceRunError::PatternMismatch) => Ok(false),
            Err(err) => Err(err),
        }
    }

    fn arm_guard_matches(
        &mut self,
        guard: Option<ExprId>,
        env: &mut Env,
    ) -> Result<bool, RuntimeEvidenceRunError> {
        let Some(guard) = guard else {
            return Ok(true);
        };
        let guard = self.eval_expr(guard, env)?;
        match guard.as_ref() {
            RuntimeEvidenceValue::Bool(true) => Ok(true),
            RuntimeEvidenceValue::Bool(false) => Ok(false),
            _ => Err(RuntimeEvidenceRunError::PatternMismatch),
        }
    }

    fn eval_handler_body_result(
        &mut self,
        body: ExprId,
        env: &mut Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match self.eval_expr_result(body, env)? {
            EvidenceEvalResult::Value(value) => self.force_value_if_thunk_result(value),
            EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                Ok(EvidenceEvalResult::request(request))
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                Ok(EvidenceEvalResult::direct_abortive(call))
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => {
                Ok(EvidenceEvalResult::direct_tail_resumptive(call))
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => {
                Ok(EvidenceEvalResult::routed_yield(call))
            }
        }
    }

    fn force_value_if_thunk_result(
        &mut self,
        value: SharedValue,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        if runtime_value_is_thunk_like(value.as_ref()) {
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
            if !self.bind_pat_matches(&arm.pat, scrutinee.clone(), &mut arm_env)? {
                continue;
            }
            if !self.arm_guard_matches(arm.guard, &mut arm_env)? {
                continue;
            }
            return self.eval_expr_result(arm.body, &mut arm_env);
        }
        Err(RuntimeEvidenceRunError::PatternMismatch)
    }

    fn eval_case_scrutinee_result(
        &mut self,
        scrutinee: SharedValue,
        arms: Rc<[control_vm::CaseArm]>,
        env: &Env,
    ) -> Result<EvidenceEvalResult, RuntimeEvidenceRunError> {
        match self.force_value_if_thunk_result(scrutinee)? {
            EvidenceEvalResult::Value(scrutinee) => self.eval_case_result(scrutinee, &arms, env),
            EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                let env = self.clone_env(env);
                Ok(EvidenceEvalResult::request(
                    self.append_request_continuation(
                        request,
                        EvidenceContinuation::case_scrutinee(
                            arms,
                            env,
                            EvidenceContinuation::identity(),
                        ),
                    ),
                ))
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                Ok(EvidenceEvalResult::direct_abortive(call))
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(call)) => {
                let env = self.clone_env(env);
                self.continue_result(
                    EvidenceEvalResult::direct_tail_resumptive(call),
                    EvidenceContinuation::case_scrutinee(
                        arms,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                )
            }
            EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => {
                let env = self.clone_env(env);
                self.continue_result(
                    EvidenceEvalResult::routed_yield(call),
                    EvidenceContinuation::case_scrutinee(
                        arms,
                        env,
                        EvidenceContinuation::identity(),
                    ),
                )
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
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                        let env = self.clone_env(env);
                        return Ok(EvidenceEvalResult::request(
                            self.append_request_continuation(
                                request,
                                EvidenceContinuation::block_stmt(
                                    EvidenceBlockResume::Let(pat.clone()),
                                    shared_stmts(rest),
                                    tail,
                                    env,
                                    last,
                                    EvidenceContinuation::identity(),
                                ),
                            ),
                        ));
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                        return Ok(EvidenceEvalResult::direct_abortive(call));
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(
                        call,
                    )) => {
                        let env = self.clone_env(env);
                        return self.continue_result(
                            EvidenceEvalResult::direct_tail_resumptive(call),
                            EvidenceContinuation::block_stmt(
                                EvidenceBlockResume::Let(pat.clone()),
                                shared_stmts(rest),
                                tail,
                                env,
                                last,
                                EvidenceContinuation::identity(),
                            ),
                        );
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => {
                        let env = self.clone_env(env);
                        return self.continue_result(
                            EvidenceEvalResult::routed_yield(call),
                            EvidenceContinuation::block_stmt(
                                EvidenceBlockResume::Let(pat.clone()),
                                shared_stmts(rest),
                                tail,
                                env,
                                last,
                                EvidenceContinuation::identity(),
                            ),
                        );
                    }
                },
                Stmt::Expr(expr) => match self.eval_expr_result(*expr, env)? {
                    EvidenceEvalResult::Value(value) => last = value,
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) => {
                        let env = self.clone_env(env);
                        return Ok(EvidenceEvalResult::request(
                            self.append_request_continuation(
                                request,
                                EvidenceContinuation::block_stmt(
                                    EvidenceBlockResume::Expr,
                                    shared_stmts(rest),
                                    tail,
                                    env,
                                    last,
                                    EvidenceContinuation::identity(),
                                ),
                            ),
                        ));
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                        return Ok(EvidenceEvalResult::direct_abortive(call));
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(
                        call,
                    )) => {
                        let env = self.clone_env(env);
                        return self.continue_result(
                            EvidenceEvalResult::direct_tail_resumptive(call),
                            EvidenceContinuation::block_stmt(
                                EvidenceBlockResume::Expr,
                                shared_stmts(rest),
                                tail,
                                env,
                                last,
                                EvidenceContinuation::identity(),
                            ),
                        );
                    }
                    EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => {
                        let env = self.clone_env(env);
                        return self.continue_result(
                            EvidenceEvalResult::routed_yield(call),
                            EvidenceContinuation::block_stmt(
                                EvidenceBlockResume::Expr,
                                shared_stmts(rest),
                                tail,
                                env,
                                last,
                                EvidenceContinuation::identity(),
                            ),
                        );
                    }
                },
                Stmt::Module(_, module_stmts) => {
                    let module_block = Block {
                        stmts: module_stmts.clone(),
                        tail: None,
                    };
                    match self.eval_block_result(&module_block, env)? {
                        EvidenceEvalResult::Value(value) => last = value,
                        EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(
                            request,
                        )) => {
                            let env = self.clone_env(env);
                            return Ok(EvidenceEvalResult::request(
                                self.append_request_continuation(
                                    request,
                                    EvidenceContinuation::block_stmt(
                                        EvidenceBlockResume::Expr,
                                        shared_stmts(rest),
                                        tail,
                                        env,
                                        last,
                                        EvidenceContinuation::identity(),
                                    ),
                                ),
                            ));
                        }
                        EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectAbortive(call)) => {
                            return Ok(EvidenceEvalResult::direct_abortive(call));
                        }
                        EvidenceEvalResult::Effect(EvidenceEffectSignal::DirectTailResumptive(
                            call,
                        )) => {
                            let env = self.clone_env(env);
                            return self.continue_result(
                                EvidenceEvalResult::direct_tail_resumptive(call),
                                EvidenceContinuation::block_stmt(
                                    EvidenceBlockResume::Expr,
                                    shared_stmts(rest),
                                    tail,
                                    env,
                                    last,
                                    EvidenceContinuation::identity(),
                                ),
                            );
                        }
                        EvidenceEvalResult::Effect(EvidenceEffectSignal::RoutedYield(call)) => {
                            let env = self.clone_env(env);
                            return self.continue_result(
                                EvidenceEvalResult::routed_yield(call),
                                EvidenceContinuation::block_stmt(
                                    EvidenceBlockResume::Expr,
                                    shared_stmts(rest),
                                    tail,
                                    env,
                                    last,
                                    EvidenceContinuation::identity(),
                                ),
                            );
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
            ListEmpty => RuntimeEvidenceValue::List(ListTree::empty()),
            ListSingleton => RuntimeEvidenceValue::List(ListTree::singleton(args[0].clone())),
            ListLen => RuntimeEvidenceValue::Int(expect_list(&args[0])?.len() as i64),
            ListIndex => expect_list(&args[0])?
                .index(value_index(&args[1])?)
                .map(|value| value.as_ref().clone())
                .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))?,
            ListIndexRange => {
                let values = expect_list(&args[0])?;
                let (start, end) = normalized_range_value(context, op, &args[1], values.len())?;
                RuntimeEvidenceValue::List(
                    values
                        .index_range(start, end)
                        .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))?,
                )
            }
            ListIndexRangeRaw => {
                let values = expect_list(&args[0])?;
                let start = value_index(&args[1])?;
                let end = value_index(&args[2])?;
                RuntimeEvidenceValue::List(
                    values
                        .index_range(start, end)
                        .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))?,
                )
            }
            ListMerge => {
                self.stats.list_merge_calls += 1;
                let left = expect_list(&args[0])?;
                let right = expect_list(&args[1])?;
                RuntimeEvidenceValue::List(ListTree::concat(left.clone(), right.clone()))
            }
            ListSplice => {
                let values = expect_list(&args[0])?;
                let (start, end) = normalized_range_value(context, op, &args[1], values.len())?;
                let insert = expect_list(&args[2])?;
                RuntimeEvidenceValue::List(
                    values
                        .splice(start, end, insert.clone())
                        .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))?,
                )
            }
            ListSpliceRaw => {
                let values = expect_list(&args[0])?;
                let start = value_index(&args[1])?;
                let end = value_index(&args[2])?;
                let insert = expect_list(&args[3])?;
                RuntimeEvidenceValue::List(
                    values
                        .splice(start, end, insert.clone())
                        .ok_or(RuntimeEvidenceRunError::UnsupportedPrimitive(op))?,
                )
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
                env.insert_slot(EnvSlot::from(*def), value);
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
                env.insert_slot(
                    EnvSlot::from(def),
                    shared(RuntimeEvidenceValue::Record(captured)),
                );
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
                env.insert_slot(EnvSlot::from(*def), value);
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
        let values = values.to_vec();

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
            let slice = ListTree::from_items(values[prefix.len()..suffix_start].iter().cloned());
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

fn constructor_value(def: DefId, arity: usize, args: Vec<SharedValue>) -> RuntimeEvidenceValue {
    if args.len() >= arity {
        return RuntimeEvidenceValue::DataConstructor {
            def,
            payloads: args,
        };
    }
    RuntimeEvidenceValue::ConstructorFunction { def, arity, args }
}

fn finish_ref_set_values(finish: EvidenceRefSetFinish, values: Vec<SharedValue>) -> SharedValue {
    shared(match finish {
        EvidenceRefSetFinish::Tuple => RuntimeEvidenceValue::Tuple(values),
        EvidenceRefSetFinish::List => RuntimeEvidenceValue::List(ListTree::from_items(values)),
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
        (RuntimeEvidenceValue::Tuple(left), RuntimeEvidenceValue::Tuple(right)) => {
            runtime_value_slices_equivalent(left, right)
        }
        (RuntimeEvidenceValue::List(left), RuntimeEvidenceValue::List(right)) => {
            runtime_value_lists_equivalent(left, right)
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

fn runtime_value_lists_equivalent(
    left: &ListTree<SharedValue>,
    right: &ListTree<SharedValue>,
) -> bool {
    if left.len() != right.len() {
        return false;
    }
    left.to_vec()
        .iter()
        .zip(right.to_vec().iter())
        .all(|(left, right)| runtime_values_equivalent(left.as_ref(), right.as_ref()))
}

fn runtime_value_view(
    value: &RuntimeEvidenceValue,
) -> (&RuntimeEvidenceValue, Vec<EvidenceValueMarker>) {
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

fn expect_list(value: &SharedValue) -> Result<&ListTree<SharedValue>, RuntimeEvidenceRunError> {
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
    match values.view() {
        ListView::Empty => Ok(RuntimeEvidenceValue::DataConstructor {
            def: DefId(constructors.empty.0),
            payloads: Vec::new(),
        }),
        ListView::Leaf(value) => Ok(RuntimeEvidenceValue::DataConstructor {
            def: DefId(constructors.leaf.0),
            payloads: vec![value],
        }),
        ListView::Node { left, right, .. } => Ok(RuntimeEvidenceValue::DataConstructor {
            def: DefId(constructors.node.0),
            payloads: vec![
                shared(RuntimeEvidenceValue::List(left)),
                shared(RuntimeEvidenceValue::List(right)),
            ],
        }),
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

fn expect_str(value: &SharedValue) -> Result<&str, RuntimeEvidenceRunError> {
    match value.as_ref() {
        RuntimeEvidenceValue::Marked { value, .. } => expect_str(value),
        RuntimeEvidenceValue::Str(value) => Ok(value),
        _ => Err(RuntimeEvidenceRunError::UnsupportedExpr(
            "non-string primitive argument",
        )),
    }
}

fn push_runtime_host_string_payload(value: &RuntimeEvidenceValue, out: &mut String) -> Option<()> {
    match value {
        RuntimeEvidenceValue::Marked { value, .. } => {
            push_runtime_host_string_payload(value.as_ref(), out)
        }
        RuntimeEvidenceValue::Str(value) => {
            out.push_str(value);
            Some(())
        }
        _ => None,
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

fn combined_markers(
    left: &[EvidenceValueMarker],
    right: &[EvidenceValueMarker],
) -> Vec<EvidenceValueMarker> {
    let mut markers = Vec::with_capacity(left.len() + right.len());
    for marker in left.iter().chain(right) {
        if !markers.iter().any(|existing| existing == marker) {
            markers.push(marker.clone());
        }
    }
    markers
}

fn markers_for_function_call_shared(
    markers: &Rc<[EvidenceValueMarker]>,
) -> Rc<[EvidenceValueMarker]> {
    transformed_markers_shared(markers, function_call_marker)
}

fn markers_for_continuation_call_shared(
    markers: &Rc<[EvidenceValueMarker]>,
) -> Rc<[EvidenceValueMarker]> {
    transformed_markers_shared(markers, continuation_call_marker)
}

fn markers_for_continuation_resume(markers: &[EvidenceValueMarker]) -> Vec<EvidenceValueMarker> {
    let mut out = Vec::with_capacity(markers.len());
    for marker in markers {
        let marker = continuation_resume_marker(marker);
        push_marker_if_absent(&mut out, marker);
    }
    out
}

fn markers_for_continuation_resume_shared(
    markers: &Rc<[EvidenceValueMarker]>,
) -> Rc<[EvidenceValueMarker]> {
    transformed_markers_shared(markers, continuation_resume_marker)
}

fn transformed_markers_shared(
    markers: &Rc<[EvidenceValueMarker]>,
    transform: fn(&EvidenceValueMarker) -> EvidenceValueMarker,
) -> Rc<[EvidenceValueMarker]> {
    let mut out = None::<Vec<EvidenceValueMarker>>;
    for (index, marker) in markers.iter().enumerate() {
        let transformed = transform(marker);
        let duplicate = match &out {
            Some(out) => out.iter().any(|existing| existing == &transformed),
            None => markers[..index]
                .iter()
                .any(|existing| existing == &transformed),
        };
        if let Some(out) = &mut out {
            if !duplicate {
                out.push(transformed);
            }
            continue;
        }
        if duplicate || &transformed != marker {
            let mut next = Vec::with_capacity(markers.len());
            next.extend_from_slice(&markers[..index]);
            if !duplicate {
                next.push(transformed);
            }
            out = Some(next);
        }
    }
    match out {
        Some(out) => share_marker_vec(out),
        None => markers.clone(),
    }
}

fn function_call_marker(marker: &EvidenceValueMarker) -> EvidenceValueMarker {
    match marker {
        EvidenceValueMarker::Frame { id } => EvidenceValueMarker::Frame { id: *id },
        EvidenceValueMarker::AddId(marker) => function_call_add_id_marker(marker),
    }
}

fn continuation_call_marker(marker: &EvidenceValueMarker) -> EvidenceValueMarker {
    match marker {
        EvidenceValueMarker::Frame { id } => EvidenceValueMarker::Frame { id: *id },
        EvidenceValueMarker::AddId(marker) => continuation_call_add_id_marker(marker),
    }
}

fn continuation_resume_marker(marker: &EvidenceValueMarker) -> EvidenceValueMarker {
    match marker {
        EvidenceValueMarker::AddId(marker) => continuation_resume_add_id_marker(marker),
        marker => marker.clone(),
    }
}

fn function_call_add_id_marker(marker: &Rc<EvidenceAddIdMarker>) -> EvidenceValueMarker {
    let depth = marker.depth.saturating_sub(1);
    if depth == marker.depth {
        return EvidenceValueMarker::AddId(marker.clone());
    }
    let mut out = marker.as_ref().clone();
    out.depth = depth;
    EvidenceValueMarker::AddId(Rc::new(out))
}

fn continuation_call_add_id_marker(marker: &Rc<EvidenceAddIdMarker>) -> EvidenceValueMarker {
    let depth = marker.depth.saturating_sub(1);
    let guard_own_path = marker.guard_own_path && marker.preserve_own_on_resume;
    if depth == marker.depth && guard_own_path == marker.guard_own_path && marker.guard_foreign_path
    {
        return EvidenceValueMarker::AddId(marker.clone());
    }
    let mut out = marker.as_ref().clone();
    out.depth = depth;
    out.guard_own_path = guard_own_path;
    out.guard_foreign_path = true;
    EvidenceValueMarker::AddId(Rc::new(out))
}

fn continuation_resume_add_id_marker(marker: &Rc<EvidenceAddIdMarker>) -> EvidenceValueMarker {
    let guard_own_path = marker.guard_own_path && marker.preserve_own_on_resume;
    if guard_own_path == marker.guard_own_path && marker.guard_foreign_path {
        return EvidenceValueMarker::AddId(marker.clone());
    }
    let mut out = marker.as_ref().clone();
    out.guard_own_path = guard_own_path;
    out.guard_foreign_path = true;
    EvidenceValueMarker::AddId(Rc::new(out))
}

fn stack_handler_markers(id: EvidenceGuardId, path: &[String]) -> Vec<EvidenceValueMarker> {
    vec![
        EvidenceValueMarker::Frame { id },
        EvidenceValueMarker::AddId(Rc::new(EvidenceAddIdMarker {
            id,
            path: shared_path(path),
            depth: 0,
            guard_own_path: false,
            guard_foreign_path: true,
            carry_after_frame: false,
            preserve_own_on_resume: false,
        })),
        EvidenceValueMarker::AddId(Rc::new(EvidenceAddIdMarker {
            id,
            path: shared_path(path),
            depth: 1,
            guard_own_path: true,
            guard_foreign_path: true,
            carry_after_frame: false,
            preserve_own_on_resume: false,
        })),
    ]
}

fn push_marker_if_absent(markers: &mut Vec<EvidenceValueMarker>, marker: EvidenceValueMarker) {
    if !markers.iter().any(|existing| existing == &marker) {
        markers.push(marker);
    }
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

#[cfg(debug_assertions)]
fn active_add_id_path_candidate_indices_by_scan(
    markers: &[EvidenceActiveAddIdMarker],
    request_path: &[String],
) -> Vec<usize> {
    markers
        .iter()
        .enumerate()
        .filter_map(|(index, marker)| {
            active_add_id_matches_request_path(&marker.marker, request_path).then_some(index)
        })
        .collect()
}

fn active_add_id_matches_request_path(
    marker: &EvidenceAddIdMarker,
    request_path: &[String],
) -> bool {
    active_add_id_match_kind(marker, request_path).is_some()
}

fn active_add_id_match_kind(
    marker: &EvidenceAddIdMarker,
    request_path: &[String],
) -> Option<ActiveAddIdMatchKind> {
    match (marker.guard_own_path, marker.guard_foreign_path) {
        (true, true) => Some(ActiveAddIdMatchKind::AllPath),
        (true, false) => {
            path_is_prefix(&marker.path, request_path).then_some(ActiveAddIdMatchKind::OwnPath)
        }
        (false, true) => (!path_is_prefix(&marker.path, request_path))
            .then_some(ActiveAddIdMatchKind::ForeignPath),
        (false, false) => None,
    }
}

fn shared_case_arms(arms: &[control_vm::CaseArm]) -> Rc<[control_vm::CaseArm]> {
    Rc::from(arms.to_vec().into_boxed_slice())
}

fn shared_catch_arms(arms: &[control_vm::CatchArm]) -> Rc<[control_vm::CatchArm]> {
    Rc::from(arms.to_vec().into_boxed_slice())
}

fn shared_expr_ids(exprs: &[ExprId]) -> Rc<[ExprId]> {
    Rc::from(exprs.to_vec().into_boxed_slice())
}

fn shared_path(path: &[String]) -> Rc<[String]> {
    Rc::from(path.to_vec().into_boxed_slice())
}

fn shared_record_fields(fields: &[control_vm::RecordField]) -> Rc<[control_vm::RecordField]> {
    Rc::from(fields.to_vec().into_boxed_slice())
}

fn shared_stmts(stmts: &[Stmt]) -> Rc<[Stmt]> {
    Rc::from(stmts.to_vec().into_boxed_slice())
}

fn shared_pat(pat: &Pat) -> Rc<Pat> {
    Rc::new(pat.clone())
}

fn shared_markers(markers: &[EvidenceValueMarker]) -> Rc<[EvidenceValueMarker]> {
    Rc::from(markers.to_vec().into_boxed_slice())
}

fn share_marker_vec(markers: Vec<EvidenceValueMarker>) -> Rc<[EvidenceValueMarker]> {
    Rc::from(markers.into_boxed_slice())
}

fn push_unique_guard(ids: &mut Vec<EvidenceGuardId>, id: EvidenceGuardId) -> bool {
    if ids.contains(&id) {
        return false;
    }
    ids.push(id);
    true
}

fn signal_excepted_at_marker_entry(
    entry_except_index: &EvidenceRequestEntryExceptIndex,
    marker: &EvidenceActiveAddIdMarker,
) -> bool {
    entry_except_index.excepted_before(marker.entry_frame_len)
}

#[derive(Debug, Clone, Copy, Default)]
struct EvidenceRequestEntryExceptIndex {
    min_guard_position: Option<usize>,
}

impl EvidenceRequestEntryExceptIndex {
    fn new(active_frames: &[EvidenceActiveFrame], guard_ids: &[EvidenceGuardId]) -> Self {
        let min_guard_position = if guard_ids.is_empty() {
            None
        } else {
            active_frames
                .iter()
                .enumerate()
                .find_map(|(position, frame)| guard_ids.contains(&frame.id).then_some(position))
        };
        Self { min_guard_position }
    }

    fn excepted_before(&self, entry_frame_len: usize) -> bool {
        self.min_guard_position
            .is_some_and(|position| position < entry_frame_len)
    }

    fn push_guard_id(&mut self, active_frames: &[EvidenceActiveFrame], id: EvidenceGuardId) {
        if let Some(position) = active_frames.iter().position(|frame| frame.id == id) {
            self.min_guard_position = Some(
                self.min_guard_position
                    .map_or(position, |current| current.min(position)),
            );
        }
    }
}

fn signal_guard_ids_at_marker_entry(
    active_frames: &[EvidenceActiveFrame],
    guard_ids: &[EvidenceGuardId],
    marker: &EvidenceActiveAddIdMarker,
) -> Vec<EvidenceGuardId> {
    let mut ids = Vec::new();
    for frame in active_frames.iter().take(marker.entry_frame_len) {
        if guard_ids.contains(&frame.id) {
            push_unique_guard(&mut ids, frame.id);
        }
    }
    ids
}

fn shared(value: RuntimeEvidenceValue) -> SharedValue {
    Rc::new(value)
}

fn mark_runtime_value(value: SharedValue, markers: &[EvidenceValueMarker]) -> SharedValue {
    if markers.is_empty() || !runtime_value_needs_hygiene_mark(value.as_ref()) {
        return value;
    }
    mark_runtime_value_unchecked(value, markers)
}

fn mark_runtime_value_shared(
    value: SharedValue,
    markers: Rc<[EvidenceValueMarker]>,
) -> SharedValue {
    if markers.is_empty() || !runtime_value_needs_hygiene_mark(value.as_ref()) {
        return value;
    }
    mark_runtime_value_unchecked_shared(value, markers)
}

fn mark_runtime_value_for_type(
    value: SharedValue,
    markers: &[EvidenceValueMarker],
    ty: &Type,
) -> SharedValue {
    if markers.is_empty() || !type_may_need_hygiene_mark(ty) {
        return value;
    }
    mark_runtime_value_unchecked(value, markers)
}

fn mark_runtime_value_unchecked(
    value: SharedValue,
    markers: &[EvidenceValueMarker],
) -> SharedValue {
    if markers.is_empty() {
        return value;
    }
    match value.as_ref() {
        RuntimeEvidenceValue::Marked {
            value,
            markers: existing,
        } => shared(RuntimeEvidenceValue::Marked {
            value: value.clone(),
            markers: share_marker_vec(combined_markers(existing, markers)),
        }),
        _ => shared(RuntimeEvidenceValue::Marked {
            value,
            markers: shared_markers(markers),
        }),
    }
}

fn mark_runtime_value_unchecked_shared(
    value: SharedValue,
    markers: Rc<[EvidenceValueMarker]>,
) -> SharedValue {
    if markers.is_empty() {
        return value;
    }
    match value.as_ref() {
        RuntimeEvidenceValue::Marked {
            value,
            markers: existing,
        } => shared(RuntimeEvidenceValue::Marked {
            value: value.clone(),
            markers: share_marker_vec(combined_markers(existing, &markers)),
        }),
        _ => shared(RuntimeEvidenceValue::Marked { value, markers }),
    }
}

fn runtime_value_needs_hygiene_mark(value: &RuntimeEvidenceValue) -> bool {
    match value {
        RuntimeEvidenceValue::Closure(_)
        | RuntimeEvidenceValue::RecursiveClosure { .. }
        | RuntimeEvidenceValue::EffectOp { .. }
        | RuntimeEvidenceValue::Continuation(_)
        | RuntimeEvidenceValue::FunctionAdapter { .. } => true,
        RuntimeEvidenceValue::Thunk(thunk) => runtime_thunk_needs_hygiene_mark(thunk),
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

fn runtime_thunk_needs_hygiene_mark(thunk: &RuntimeEvidenceThunk) -> bool {
    match thunk {
        RuntimeEvidenceThunk::Expr {
            needs_hygiene_mark, ..
        } => *needs_hygiene_mark,
        RuntimeEvidenceThunk::Effect { .. }
        | RuntimeEvidenceThunk::Continuation { .. }
        | RuntimeEvidenceThunk::Adapter { .. } => true,
        RuntimeEvidenceThunk::Value(value) => runtime_value_needs_hygiene_mark(value.as_ref()),
    }
}

fn runtime_value_is_thunk_like(value: &RuntimeEvidenceValue) -> bool {
    match value {
        RuntimeEvidenceValue::Thunk(_) => true,
        RuntimeEvidenceValue::Marked { value, .. } => runtime_value_is_thunk_like(value),
        _ => false,
    }
}

fn marked_force_value_thunk(
    value: &RuntimeEvidenceValue,
    markers: Rc<[EvidenceValueMarker]>,
) -> Option<(SharedValue, Rc<[EvidenceValueMarker]>)> {
    match value {
        RuntimeEvidenceValue::Thunk(thunk) => match thunk.as_ref() {
            RuntimeEvidenceThunk::Value(value) => Some((value.clone(), markers)),
            _ => None,
        },
        RuntimeEvidenceValue::Marked {
            value,
            markers: nested,
        } => marked_force_value_thunk(
            value.as_ref(),
            share_marker_vec(combined_markers(&markers, nested)),
        ),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct MarkedForceMarkerSummary {
    active_add_ids: usize,
    carry_after_frame: usize,
}

fn marked_force_marker_summary(markers: &[EvidenceValueMarker]) -> MarkedForceMarkerSummary {
    let mut summary = MarkedForceMarkerSummary::default();
    for marker in markers {
        let EvidenceValueMarker::AddId(marker) = marker else {
            continue;
        };
        if marker.depth != 0 {
            continue;
        }
        summary.active_add_ids += 1;
        if marker.carry_after_frame {
            summary.carry_after_frame += 1;
        }
    }
    summary
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RuntimeEvidenceThunkKind {
    Expr,
    Effect,
    Continuation,
    Value,
    Adapter,
}

fn marked_force_thunk_kind(value: &RuntimeEvidenceValue) -> Option<RuntimeEvidenceThunkKind> {
    match value {
        RuntimeEvidenceValue::Thunk(thunk) => Some(match thunk.as_ref() {
            RuntimeEvidenceThunk::Expr { .. } => RuntimeEvidenceThunkKind::Expr,
            RuntimeEvidenceThunk::Effect { .. } => RuntimeEvidenceThunkKind::Effect,
            RuntimeEvidenceThunk::Continuation { .. } => RuntimeEvidenceThunkKind::Continuation,
            RuntimeEvidenceThunk::Value(_) => RuntimeEvidenceThunkKind::Value,
            RuntimeEvidenceThunk::Adapter { .. } => RuntimeEvidenceThunkKind::Adapter,
        }),
        RuntimeEvidenceValue::Marked { value, .. } => marked_force_thunk_kind(value),
        _ => None,
    }
}

fn callee_apply_closes_without_frame(value: &RuntimeEvidenceValue) -> bool {
    matches!(
        value,
        RuntimeEvidenceValue::PrimitiveOp { .. }
            | RuntimeEvidenceValue::ConstructorFunction { .. }
            | RuntimeEvidenceValue::EffectOp { .. }
            | RuntimeEvidenceValue::Continuation(_)
    )
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

fn effective_thunk_type_may_need_hygiene_mark(ty: &EffectiveThunkType) -> bool {
    !ty.effect.is_pure_effect() || type_may_need_hygiene_mark(&ty.value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        EvidenceVmAllowedSetKind, EvidenceVmAllowedSetPlan, EvidenceVmEnvProviderPlan,
        EvidenceVmObjectPlan, EvidenceVmOperationKind, EvidenceVmOperationLowering,
        EvidenceVmOperationObjectPlan, EvidenceVmOperationPlan, EvidenceVmOperationVisibilityPlan,
        EvidenceVmSlotKey, EvidenceVmSlotRouteKey, EvidenceVmSummary, EvidenceVmValueEnvKind,
        EvidenceVmValueObjectPlan,
    };

    #[test]
    fn provider_env_close_wraps_escaped_request_continuation() {
        let provider_env = provider_env_fixture();
        let program = Program::default();
        let mut runner = RuntimeEvidenceRunner::new(&program, RuntimeEvidenceRunContext::default());
        let request = EvidenceRequest {
            path: shared_path(&["out".to_string(), "say".to_string()]),
            payload: shared(RuntimeEvidenceValue::Unit),
            route: EvidenceEffectRoute::Unhandled,
            hygiene: EvidenceSignalHygiene::new(),
            continuation: EvidenceContinuation::identity(),
        };

        let result = runner
            .with_provider_env(provider_env.clone(), move |_| {
                Ok(EvidenceEvalResult::request(request))
            })
            .expect("provider env close must succeed");

        let EvidenceEvalResult::Effect(EvidenceEffectSignal::GenericRequest(request)) = result
        else {
            panic!("provider env close should keep escaped request");
        };
        let Some(EvidenceContinuationFrame::ProviderEnv {
            provider_env: captured,
            next,
        }) = request.continuation.frame()
        else {
            panic!("escaped request continuation should be wrapped in provider env");
        };
        assert_eq!(captured, &provider_env);
        assert!(next.is_identity());
    }

    #[test]
    fn pure_expr_thunk_does_not_need_hygiene_mark() {
        let pure = RuntimeEvidenceValue::Thunk(Rc::new(RuntimeEvidenceThunk::Expr {
            body: ExprId(0),
            env: Env::new(),
            provider_env: RuntimeEvidenceProviderEnv::default(),
            needs_hygiene_mark: false,
        }));
        let effectful = RuntimeEvidenceValue::Thunk(Rc::new(RuntimeEvidenceThunk::Expr {
            body: ExprId(0),
            env: Env::new(),
            provider_env: RuntimeEvidenceProviderEnv::default(),
            needs_hygiene_mark: true,
        }));
        let continuation =
            RuntimeEvidenceValue::Thunk(Rc::new(RuntimeEvidenceThunk::Continuation {
                continuation: EvidenceContinuation::identity(),
                arg: shared(RuntimeEvidenceValue::Unit),
            }));

        assert!(!runtime_value_needs_hygiene_mark(&pure));
        assert!(runtime_value_needs_hygiene_mark(&effectful));
        assert!(runtime_value_needs_hygiene_mark(&continuation));
    }

    #[test]
    fn permission_visibility_shadow_check_allows_identity_and_provider_pair() {
        let visibility = RuntimeEvidenceOperationVisibility::plan_allowed_set(
            crate::EvidenceVmAllowedSetId(0),
            Some(7),
            false,
        );
        let clean = EvidenceSignalHygiene::new().with_operation_visibility(Some(visibility));
        assert_eq!(
            clean.permission_shadow_kind(),
            Some(EvidencePermissionShadowKind::Direct)
        );

        let mut guarded = clean.clone();
        assert!(guarded.push_guard_id(EvidenceGuardId(1)));
        assert_eq!(guarded.permission_shadow_kind(), None);

        let mut resumed = clean.clone();
        resumed.push_carried_guard(EvidenceCarriedGuard {
            id: EvidenceGuardId(2),
            entry_frame_len: 0,
            exposed_guard_ids: Vec::new(),
        });
        assert_eq!(resumed.permission_shadow_kind(), None);

        let mut bounded = clean.clone();
        bounded.set_handler_boundary(EvidenceHandlerBoundary {
            id: EvidenceGuardId(3),
            path: vec!["flip".to_string(), "coin".to_string()],
            blocked: false,
        });
        assert_eq!(bounded.permission_shadow_kind(), None);

        let provider_visibility = RuntimeEvidenceOperationVisibility::provider_grant(7);
        let provider_clean =
            EvidenceSignalHygiene::new().with_operation_visibility(Some(provider_visibility));
        assert_eq!(
            provider_clean.permission_shadow_kind(),
            Some(EvidencePermissionShadowKind::Direct)
        );

        let mut provider_pair = provider_clean.clone();
        assert!(provider_pair.push_guard_id(EvidenceGuardId(4)));
        provider_pair.set_handler_boundary(EvidenceHandlerBoundary {
            id: EvidenceGuardId(4),
            path: vec!["flip".to_string(), "coin".to_string()],
            blocked: false,
        });
        let provider_permission = provider_visibility.provider_grant_permission().unwrap();
        assert_eq!(
            provider_pair.permission_shadow_kind(),
            Some(EvidencePermissionShadowKind::ProviderGrantBoundaryPair(
                provider_permission
            ))
        );

        let mut provider_guarded = provider_clean.clone();
        assert!(provider_guarded.push_guard_id(EvidenceGuardId(5)));
        assert_eq!(provider_guarded.permission_shadow_kind(), None);

        let mut provider_bounded = provider_clean.clone();
        provider_bounded.set_handler_boundary(EvidenceHandlerBoundary {
            id: EvidenceGuardId(6),
            path: vec!["flip".to_string(), "coin".to_string()],
            blocked: false,
        });
        assert_eq!(provider_bounded.permission_shadow_kind(), None);

        let legacy_bridge = EvidenceSignalHygiene::new().with_operation_visibility(Some(
            RuntimeEvidenceOperationVisibility::plan_allowed_set(
                crate::EvidenceVmAllowedSetId(1),
                None,
                true,
            ),
        ));
        assert_eq!(legacy_bridge.permission_shadow_kind(), None);
    }

    #[test]
    fn provider_pair_permission_decision_preserves_no_allowed_handler() {
        let program = Program::default();
        let runner = RuntimeEvidenceRunner::new(&program, RuntimeEvidenceRunContext::default());
        let request_path = permission_test_path();
        let visibility = RuntimeEvidenceOperationVisibility::provider_grant(7);
        let hygiene = permission_pair_hygiene(visibility, EvidenceGuardId(4));
        let arms = vec![permission_test_arm(true)];

        let decision = runner.provider_guard_boundary_permission_decision(
            ExprId(99),
            &request_path,
            &hygiene,
            &arms,
        );

        assert_eq!(
            decision,
            EvidencePermissionVisibleDecision::Handled(
                EvidencePermissionVisibleResult::NoAllowedHandler
            )
        );
        let EvidencePermissionVisibleDecision::Handled(result) = decision else {
            panic!("provider pair must be handled, not treated as not applicable");
        };
        assert_eq!(result.visible(), None);
        assert!(result.no_allowed_handler());
    }

    #[test]
    fn non_provider_pair_permission_decision_is_not_applicable() {
        let program = Program::default();
        let runner = RuntimeEvidenceRunner::new(&program, RuntimeEvidenceRunContext::default());
        let request_path = permission_test_path();
        let arms = vec![permission_test_arm(true)];

        let plan_visibility = RuntimeEvidenceOperationVisibility::plan_allowed_set(
            crate::EvidenceVmAllowedSetId(0),
            Some(7),
            false,
        );
        let plan_pair = permission_pair_hygiene(plan_visibility, EvidenceGuardId(4));
        assert_eq!(
            runner.provider_guard_boundary_permission_decision(
                ExprId(99),
                &request_path,
                &plan_pair,
                &arms
            ),
            EvidencePermissionVisibleDecision::NotApplicable
        );

        let provider_visibility = RuntimeEvidenceOperationVisibility::provider_grant(7);
        let mut provider_guard_only =
            EvidenceSignalHygiene::new().with_operation_visibility(Some(provider_visibility));
        assert!(provider_guard_only.push_guard_id(EvidenceGuardId(5)));
        assert_eq!(
            runner.provider_guard_boundary_permission_decision(
                ExprId(99),
                &request_path,
                &provider_guard_only,
                &arms
            ),
            EvidencePermissionVisibleDecision::NotApplicable
        );

        let mut provider_boundary_only =
            EvidenceSignalHygiene::new().with_operation_visibility(Some(provider_visibility));
        provider_boundary_only.set_handler_boundary(EvidenceHandlerBoundary {
            id: EvidenceGuardId(6),
            path: permission_test_path(),
            blocked: false,
        });
        assert_eq!(
            runner.provider_guard_boundary_permission_decision(
                ExprId(99),
                &request_path,
                &provider_boundary_only,
                &arms
            ),
            EvidencePermissionVisibleDecision::NotApplicable
        );
    }

    #[test]
    fn provider_env_frame_is_shadowed_by_later_marker_scope() {
        let provider_env = provider_env_fixture();
        let program = Program::default();
        let mut runner = RuntimeEvidenceRunner::new(&program, RuntimeEvidenceRunContext::default());
        let frame = runner.provider_frame(provider_env.clone());
        runner.active_provider_envs.push(frame);

        assert_eq!(runner.active_provider_env_refs(), vec![&provider_env]);

        let markers: Rc<[EvidenceValueMarker]> = Vec::new().into();
        runner
            .active_marker_plans
            .push(EvidenceActiveMarkerPlan::new(markers));

        assert!(runner.active_provider_env_refs().is_empty());
    }

    #[test]
    fn provider_grant_gate_requires_active_scope_and_baseline() {
        let provider_env = provider_env_fixture();
        let program = Program::default();
        let mut runner = RuntimeEvidenceRunner::new(&program, RuntimeEvidenceRunContext::default());
        let frame = runner.provider_frame(provider_env);
        let grant = EvidenceProviderGrant {
            demand_slot_id: 7,
            provider_slot_id: 7,
            handler_id: 3,
            scope_id: frame.scope_id,
            hygiene_baseline: frame.hygiene_baseline,
        };
        runner.active_provider_envs.push(frame);
        let grant_id = runner.record_provider_grant(grant);
        let evidence = EffectThunkEvidence {
            route_cert: EvidenceRouteCert::ProviderGrant(grant_id),
            visibility: None,
        };

        assert!(runner.provider_grant_gate_passes(EvidenceRouteCert::ProviderGrant(grant_id)));
        assert!(runner.route_allows_routed_yield(false, evidence));
        assert!(runner.route_allows_routed_yield(
            true,
            EffectThunkEvidence {
                route_cert: EvidenceRouteCert::None,
                visibility: None
            }
        ));

        let markers: Rc<[EvidenceValueMarker]> = Vec::new().into();
        runner
            .active_marker_plans
            .push(EvidenceActiveMarkerPlan::new(markers));

        assert!(!runner.provider_grant_gate_passes(EvidenceRouteCert::ProviderGrant(grant_id)));
        assert!(!runner.route_allows_routed_yield(false, evidence));
    }

    fn permission_pair_hygiene(
        visibility: RuntimeEvidenceOperationVisibility,
        guard_id: EvidenceGuardId,
    ) -> EvidenceSignalHygiene {
        let mut hygiene = EvidenceSignalHygiene::new().with_operation_visibility(Some(visibility));
        assert!(hygiene.push_guard_id(guard_id));
        hygiene.set_handler_boundary(EvidenceHandlerBoundary {
            id: guard_id,
            path: permission_test_path(),
            blocked: false,
        });
        hygiene
    }

    fn permission_test_arm(resumptive: bool) -> control_vm::CatchArm {
        control_vm::CatchArm {
            operation_path: Some(permission_test_path()),
            pat: Pat::Wild,
            continuation: resumptive.then_some(Pat::Wild),
            guard: None,
            body: ExprId(1),
        }
    }

    fn permission_test_path() -> Vec<String> {
        vec!["flip".to_string(), "coin".to_string()]
    }

    fn provider_env_fixture() -> RuntimeEvidenceProviderEnv {
        let apply = ExprId(10);
        let callee = ExprId(11);
        let handler = ExprId(20);
        let value = ExprId(30);
        let slot_id = 7;
        let handler_id = 3;
        let plan = EvidenceVmPlan {
            summary: EvidenceVmSummary::default(),
            handlers: Vec::new(),
            operations: vec![EvidenceVmOperationPlan {
                expr: callee,
                path: vec!["out".to_string(), "say".to_string()],
                slot: EvidenceVmSlotKey {
                    family: vec!["out".to_string(), "say".to_string()],
                    route: EvidenceVmSlotRouteKey::UnknownFallback,
                },
                kind: EvidenceVmOperationKind::Call { apply, callee },
                lowering: EvidenceVmOperationLowering::LexicalHandlerCandidate {
                    handler,
                    resumptive: true,
                    delayed_boundary: false,
                },
                runtime_nodes: Vec::new(),
                runtime_evidence_refs: 0,
            }],
            functions: Vec::new(),
            values: Vec::new(),
            objects: EvidenceVmObjectPlan {
                operations: vec![EvidenceVmOperationObjectPlan {
                    expr: callee,
                    slot_id,
                    candidate_handler: Some(handler_id),
                    execution: EvidenceVmOperationExecutionPlan::DirectTailResumptive,
                    visibility: EvidenceVmOperationVisibilityPlan {
                        allowed_set_id: crate::EvidenceVmAllowedSetId(0),
                        legacy_guard_bridge: true,
                    },
                }],
                values: vec![EvidenceVmValueObjectPlan {
                    id: 0,
                    expr: value,
                    kind: EvidenceVmValueEnvKind::Lambda { body: ExprId(31) },
                    captures: vec![slot_id],
                    env_providers: vec![EvidenceVmEnvProviderPlan {
                        slot_id,
                        handler_ids: vec![handler_id],
                    }],
                }],
                allowed_sets: vec![EvidenceVmAllowedSetPlan {
                    id: crate::EvidenceVmAllowedSetId(0),
                    kind: EvidenceVmAllowedSetKind::LegacyGuardBridge,
                }],
                ..EvidenceVmObjectPlan::default()
            },
        };
        RuntimeEvidenceRunContext::from_plan(&plan).provider_env_for_value(value, &[], &[])
    }
}
