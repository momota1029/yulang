use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;

use control_vm::{
    Block, ControlEffectUseKind, ControlEvidenceProgram, ControlEvidenceRoute, DefId, Expr, ExprId,
    Pat, Program, RecordSpread, Root, SelectResolution, Stmt,
};
use specialize::{
    RuntimeEvidenceNode, RuntimeEvidenceNodeKind, RuntimeEvidenceSurface, RuntimeEvidenceTaskOwner,
};

mod runtime;
pub use runtime::{
    RuntimeEvidenceDisplayContext, RuntimeEvidenceRunError, RuntimeEvidenceRunOutput,
    RuntimeEvidenceRunStats, run_program, run_program_with_plan,
    run_program_with_plan_deep_profile, run_program_with_plan_without_native_host_operations,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvidenceVmPlan {
    pub(crate) summary: EvidenceVmSummary,
    pub(crate) handlers: Vec<EvidenceVmHandlerPlan>,
    pub(crate) operations: Vec<EvidenceVmOperationPlan>,
    pub(crate) functions: Vec<EvidenceVmFunctionPlan>,
    pub(crate) values: Vec<EvidenceVmValueEnvPlan>,
    pub(crate) objects: EvidenceVmObjectPlan,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct EvidenceVmSummary {
    pub(crate) handlers: usize,
    pub(crate) handler_continuation_direct_calls: usize,
    pub(crate) handler_continuation_delayed_calls: usize,
    pub(crate) handler_continuation_escape_arms: usize,
    pub(crate) handler_tail_resume_arms: usize,
    pub(crate) operations: usize,
    pub(crate) direct_operations: usize,
    pub(crate) direct_abortive_operations: usize,
    pub(crate) direct_resumptive_operations: usize,
    pub(crate) lexical_candidate_operations: usize,
    pub(crate) delayed_lexical_candidate_operations: usize,
    pub(crate) blocked_operations: usize,
    pub(crate) unhandled_operations: usize,
    pub(crate) adapter_boundaries: usize,
    pub(crate) delayed_boundaries: usize,
    pub(crate) generic_fallbacks: usize,
    pub(crate) evidence_param_functions: usize,
    pub(crate) evidence_params: usize,
    pub(crate) evidence_arg_calls: usize,
    pub(crate) evidence_slot_keys: usize,
    pub(crate) evidence_object_slots: usize,
    pub(crate) evidence_function_objects: usize,
    pub(crate) evidence_value_objects: usize,
    pub(crate) evidence_call_objects: usize,
    pub(crate) evidence_handler_objects: usize,
    pub(crate) evidence_operation_objects: usize,
    pub(crate) evidence_known_handler_objects: usize,
    pub(crate) evidence_known_state_handler_objects: usize,
    pub(crate) evidence_known_state_handler_compiler_certificates: usize,
    pub(crate) plan_known_operation_calls: usize,
    pub(crate) plan_known_operation_state_get_candidates: usize,
    pub(crate) plan_known_operation_state_set_candidates: usize,
    pub(crate) plan_known_operation_state_direct_gets: usize,
    pub(crate) plan_known_operation_state_direct_sets: usize,
    pub(crate) plan_known_state_operation_route_proofs: usize,
    pub(crate) plan_known_operation_reject_no_operation_object: usize,
    pub(crate) plan_known_operation_reject_not_call: usize,
    pub(crate) plan_known_operation_reject_no_visibility: usize,
    pub(crate) plan_known_operation_reject_no_candidate_handler: usize,
    pub(crate) plan_known_operation_reject_no_known_state_access_proof: usize,
    pub(crate) plan_known_operation_reject_known_state_access_handler_mismatch: usize,
    pub(crate) plan_known_operation_reject_known_state_access_boundary_unsafe: usize,
    pub(crate) plan_known_operation_reject_direct_execution_disabled: usize,
    pub(crate) plan_known_operation_reject_no_known_handler: usize,
    pub(crate) plan_known_operation_reject_wrong_handler: usize,
    pub(crate) plan_known_operation_reject_wrong_operation: usize,
    pub(crate) plan_known_operation_reject_blocked: usize,
    pub(crate) plan_known_operation_reject_delayed: usize,
    pub(crate) plan_known_operation_reject_provider_dirty: usize,
    pub(crate) static_route_sites_total: usize,
    pub(crate) static_route_static_handler: usize,
    pub(crate) static_route_static_tail_resumptive: usize,
    pub(crate) static_route_static_abortive: usize,
    pub(crate) static_route_static_other_arm: usize,
    pub(crate) static_route_dynamic_open_row: usize,
    pub(crate) static_route_dynamic_multiple_candidates: usize,
    pub(crate) static_route_dynamic_hygiene_barrier: usize,
    pub(crate) static_route_dynamic_provider_env: usize,
    pub(crate) static_route_dynamic_delayed_boundary: usize,
    pub(crate) static_route_dynamic_host_escape: usize,
    pub(crate) static_route_dynamic_unclassified: usize,
    pub(crate) evidence_handler_capabilities: usize,
    pub(crate) evidence_allowed_sets: usize,
    pub(crate) evidence_provider_slots: usize,
    pub(crate) evidence_provider_candidates: usize,
    pub(crate) evidence_env_provider_slots: usize,
    pub(crate) evidence_env_provider_candidates: usize,
    pub(crate) evidence_direct_candidates: usize,
    pub(crate) evidence_env_values: usize,
    pub(crate) evidence_env_captures: usize,
    pub(crate) runtime_tasks: usize,
    pub(crate) runtime_nodes: usize,
    pub(crate) runtime_evidence_refs: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmHandlerPlan {
    pub(crate) expr: ExprId,
    pub(crate) body: ExprId,
    pub(crate) arms: Vec<EvidenceVmHandlerArmPlan>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmHandlerArmPlan {
    pub(crate) path: Option<Vec<String>>,
    pub(crate) resumptive: bool,
    pub(crate) guarded: bool,
    pub(crate) classification: EvidenceVmHandlerArmClass,
    pub(crate) continuation_use: EvidenceVmContinuationUsePlan,
    pub(crate) body: ExprId,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct EvidenceVmContinuationUsePlan {
    pub(crate) direct_calls: usize,
    pub(crate) delayed_calls: usize,
    pub(crate) escapes: bool,
    pub(crate) tail_arg: Option<ExprId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvidenceVmHandlerArmClass {
    Value,
    Abortive,
    TailResumptive,
    OneShotYield,
    MultiShotYield,
    MayEscapeYield,
    Fallback,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmOperationPlan {
    pub(crate) expr: ExprId,
    pub(crate) operation_def: Option<DefId>,
    pub(crate) path: Vec<String>,
    pub(crate) slot: EvidenceVmSlotKey,
    pub(crate) kind: EvidenceVmOperationKind,
    pub(crate) lowering: EvidenceVmOperationLowering,
    pub(crate) runtime_nodes: Vec<u32>,
    pub(crate) runtime_evidence_refs: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvidenceVmOperationKind {
    Value,
    Call { apply: ExprId, callee: ExprId },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EvidenceVmOperationLowering {
    DirectHandlerCall {
        handler: ExprId,
        resumptive: bool,
        handler_known: bool,
    },
    LexicalHandlerCandidate {
        handler: ExprId,
        resumptive: bool,
        delayed_boundary: bool,
    },
    HygieneFallback {
        handler: ExprId,
        resumptive: bool,
        callback_boundary: bool,
        delayed_boundary: bool,
    },
    GenericFallback,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmFunctionPlan {
    pub(crate) owner: RuntimeEvidenceTaskOwner,
    pub(crate) signature: EvidenceVmFunctionSignature,
    pub(crate) node_count: usize,
    pub(crate) evidence_ref_count: usize,
    pub(crate) required_evidence: Vec<EvidenceVmEvidenceRequirement>,
    pub(crate) provided_evidence_paths: Vec<Vec<String>>,
    pub(crate) calls_needing_evidence: Vec<EvidenceVmCallPlan>,
    pub(crate) operation_exprs: Vec<u32>,
    pub(crate) handler_exprs: Vec<u32>,
    pub(crate) fallback_exprs: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmEvidenceRequirement {
    pub(crate) slot: EvidenceVmSlotKey,
    pub(crate) operation_exprs: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmCallPlan {
    pub(crate) apply: ExprId,
    pub(crate) callee_instance: u32,
    pub(crate) required_evidence_slots: Vec<EvidenceVmSlotKey>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmValueEnvPlan {
    pub(crate) expr: ExprId,
    pub(crate) kind: EvidenceVmValueEnvKind,
    pub(crate) signature: EvidenceVmValueEnvSignature,
    pub(crate) captured_evidence: Vec<EvidenceVmEvidenceRequirement>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmFunctionSignature {
    pub(crate) params: Vec<EvidenceVmSlotKey>,
    pub(crate) provides: Vec<EvidenceVmSlotKey>,
    pub(crate) value_env: Vec<EvidenceVmSlotKey>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmValueEnvSignature {
    pub(crate) captures: Vec<EvidenceVmSlotKey>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct EvidenceVmSlotKey {
    pub(crate) family: Vec<String>,
    pub(crate) route: EvidenceVmSlotRouteKey,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum EvidenceVmSlotRouteKey {
    Positive,
    Blocked,
    UnknownFallback,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct EvidenceVmHandlerCapId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct EvidenceVmAllowedSetId(pub(crate) u32);

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct EvidenceVmObjectPlan {
    pub(crate) slots: Vec<EvidenceVmSlotPlan>,
    pub(crate) functions: Vec<EvidenceVmFunctionObjectPlan>,
    pub(crate) values: Vec<EvidenceVmValueObjectPlan>,
    pub(crate) calls: Vec<EvidenceVmCallObjectPlan>,
    pub(crate) handlers: Vec<EvidenceVmHandlerObjectPlan>,
    pub(crate) operations: Vec<EvidenceVmOperationObjectPlan>,
    pub(crate) known_handlers: Vec<EvidenceVmKnownHandlerPlan>,
    pub(crate) known_operations: Vec<EvidenceVmKnownOperationPlan>,
    pub(crate) known_state_operation_route_proofs: Vec<EvidenceVmKnownStateOperationRouteProof>,
    pub(crate) handler_capabilities: Vec<EvidenceVmHandlerCapabilityPlan>,
    pub(crate) allowed_sets: Vec<EvidenceVmAllowedSetPlan>,
    pub(crate) providers: Vec<EvidenceVmProviderPlan>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmSlotPlan {
    pub(crate) id: u32,
    pub(crate) key: EvidenceVmSlotKey,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmFunctionObjectPlan {
    pub(crate) id: u32,
    pub(crate) owner: RuntimeEvidenceTaskOwner,
    pub(crate) params: Vec<u32>,
    pub(crate) provides: Vec<u32>,
    pub(crate) value_env: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmValueObjectPlan {
    pub(crate) id: u32,
    pub(crate) expr: ExprId,
    pub(crate) kind: EvidenceVmValueEnvKind,
    pub(crate) captures: Vec<u32>,
    pub(crate) env_providers: Vec<EvidenceVmEnvProviderPlan>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmCallObjectPlan {
    pub(crate) apply: ExprId,
    pub(crate) callee_instance: u32,
    pub(crate) required_slots: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmHandlerObjectPlan {
    pub(crate) id: u32,
    pub(crate) capability_id: EvidenceVmHandlerCapId,
    pub(crate) handler: ExprId,
    pub(crate) slot_id: u32,
    pub(crate) path: Vec<String>,
    pub(crate) arm_body: ExprId,
    pub(crate) arm_class: EvidenceVmHandlerArmClass,
    pub(crate) continuation_use: EvidenceVmContinuationUsePlan,
    pub(crate) definition_env: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmOperationObjectPlan {
    pub(crate) expr: ExprId,
    pub(crate) slot_id: u32,
    pub(crate) candidate_handler: Option<u32>,
    pub(crate) execution: EvidenceVmOperationExecutionPlan,
    pub(crate) visibility: EvidenceVmOperationVisibilityPlan,
    pub(crate) static_route: EvidenceVmStaticRouteResolution,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvidenceVmStaticRouteResolution {
    StaticHandler {
        arm_class: EvidenceVmHandlerArmClass,
    },
    Dynamic(EvidenceVmStaticRouteDynamicReason),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) enum EvidenceVmStaticRouteDynamicReason {
    OpenRow,
    MultipleCandidates,
    HygieneBarrier,
    ProviderEnvDependent,
    DelayedBoundary,
    HostEscape,
    Unclassified,
}

#[derive(Debug, Clone, PartialEq, Eq)]
// The certificate surface lands before the compiler-generated local-var producer.
#[allow(dead_code)]
pub(crate) enum EvidenceVmKnownHandlerPlan {
    State(EvidenceVmKnownStateHandlerPlan),
}

impl EvidenceVmKnownHandlerPlan {
    fn is_state(&self) -> bool {
        matches!(self, Self::State(_))
    }

    fn is_compiler_state_certificate(&self) -> bool {
        match self {
            Self::State(plan) => plan.source == EvidenceVmKnownStateHandlerSource::CompilerLocalVar,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmKnownStateHandlerPlan {
    pub(crate) id: EvidenceVmKnownHandlerPlanId,
    pub(crate) synthetic_var: u32,
    pub(crate) handler: ExprId,
    pub(crate) state: DefId,
    pub(crate) family: Vec<String>,
    pub(crate) get_handler_id: u32,
    pub(crate) set_handler_id: u32,
    pub(crate) source: EvidenceVmKnownStateHandlerSource,
    pub(crate) continuation: EvidenceVmKnownStateContinuationSemantics,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct EvidenceVmKnownHandlerPlanId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvidenceVmKnownStateHandlerSource {
    CompilerLocalVar,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
// Snapshot/fork is the semantic contract even before direct state execution exists.
#[allow(dead_code)]
pub(crate) enum EvidenceVmKnownStateContinuationSemantics {
    SnapshotFork,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum EvidenceVmKnownOperationRole {
    StateGet,
    StateSet,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) enum EvidenceVmKnownOperationReject {
    NoOperationObject,
    NotCall,
    NoVisibility,
    NoCandidateHandler,
    NoKnownStateAccessProof,
    KnownStateAccessHandlerMismatch,
    KnownStateAccessBoundaryUnsafe,
    DirectExecutionDisabled,
    NoKnownHandler,
    WrongHandler,
    WrongOperation,
    Blocked,
    Delayed,
    ProviderDirty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmKnownOperationPlan {
    pub(crate) expr: ExprId,
    pub(crate) apply: ExprId,
    pub(crate) callee: ExprId,
    pub(crate) known_handler: EvidenceVmKnownHandlerPlanId,
    pub(crate) handler_id: u32,
    pub(crate) role: EvidenceVmKnownOperationRole,
    pub(crate) direct_ready: bool,
    pub(crate) reject: Option<EvidenceVmKnownOperationReject>,
    pub(crate) visibility: EvidenceVmAllowedSetId,
    pub(crate) route_proof: Option<EvidenceVmKnownStateOperationRouteProofId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct EvidenceVmKnownStateOperationRouteProofId(pub(crate) u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmKnownStateOperationRouteProof {
    pub(crate) id: EvidenceVmKnownStateOperationRouteProofId,
    pub(crate) operation_expr: ExprId,
    pub(crate) apply: ExprId,
    pub(crate) callee: ExprId,
    pub(crate) access_operation_def: u32,
    pub(crate) synthetic_var: u32,
    pub(crate) plan_id: EvidenceVmKnownHandlerPlanId,
    pub(crate) catch_expr: ExprId,
    pub(crate) handler_id: u32,
    pub(crate) role: EvidenceVmKnownOperationRole,
    pub(crate) source: EvidenceVmKnownStateOperationRouteProofSource,
    pub(crate) visibility: EvidenceVmKnownStateOperationVisibilityProof,
    pub(crate) payload: EvidenceVmKnownStateOperationPayloadProof,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvidenceVmKnownStateOperationRouteProofSource {
    CompilerLocalVar { synthetic_var: u32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvidenceVmKnownStateOperationVisibilityProof {
    CleanKnownStateCatch {
        catch_expr: ExprId,
        plan_id: EvidenceVmKnownHandlerPlanId,
        handler_id: u32,
        no_delayed_boundary: bool,
        no_callback_boundary: bool,
        no_blocking_marker: bool,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvidenceVmKnownStateOperationPayloadProof {
    UnitPayloadForGet,
    SingleValuePayloadForSet,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmHandlerCapabilityPlan {
    pub(crate) id: EvidenceVmHandlerCapId,
    pub(crate) handler_id: u32,
    pub(crate) slot_id: u32,
    pub(crate) family: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmAllowedSetPlan {
    pub(crate) id: EvidenceVmAllowedSetId,
    pub(crate) kind: EvidenceVmAllowedSetKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum EvidenceVmAllowedSetKind {
    HandlerCapability(EvidenceVmHandlerCapId),
    LegacyGuardBridge,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmOperationVisibilityPlan {
    pub(crate) allowed_set_id: EvidenceVmAllowedSetId,
    pub(crate) legacy_guard_bridge: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmEnvProviderPlan {
    pub(crate) slot_id: u32,
    pub(crate) handler_ids: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EvidenceVmProviderPlan {
    pub(crate) slot_id: u32,
    pub(crate) route: EvidenceVmProviderRoute,
    pub(crate) handler_candidates: Vec<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvidenceVmProviderRoute {
    DirectPositive,
    NeedsEvidenceEnv,
    BlockedByHygiene,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvidenceVmOperationExecutionPlan {
    DirectAbortive,
    DirectTailResumptive,
    YieldFallback,
    BlockedFallback,
    GenericFallback,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EvidenceVmValueEnvKind {
    Lambda {
        body: ExprId,
    },
    Thunk {
        body: ExprId,
    },
    FunctionAdapter {
        function: ExprId,
        creates_callback_boundary: bool,
        body_marker_count: usize,
        arg_marker_count: usize,
        ret_marker_count: usize,
    },
}

pub fn build_plan(program: &Program, surface: &RuntimeEvidenceSurface) -> EvidenceVmPlan {
    let control = ControlEvidenceProgram::from_program(program);
    build_plan_from_evidence(program, &control, surface)
}

fn build_plan_from_evidence(
    program: &Program,
    control: &ControlEvidenceProgram,
    surface: &RuntimeEvidenceSurface,
) -> EvidenceVmPlan {
    let runtime_nodes = RuntimeNodeIndex::new(surface);
    let lexical_handlers = LexicalHandlerIndex::new(program, control);
    let handler_exprs = control
        .handlers
        .iter()
        .map(|handler| handler.expr)
        .collect::<HashSet<_>>();

    let handlers = control
        .handlers
        .iter()
        .map(|handler| EvidenceVmHandlerPlan {
            expr: handler.expr,
            body: handler.body,
            arms: handler
                .arms
                .iter()
                .enumerate()
                .map(|(index, arm)| {
                    let analysis = analyze_handler_arm(program, handler.expr, index, arm);
                    EvidenceVmHandlerArmPlan {
                        path: arm.operation_path.clone(),
                        resumptive: arm.resumptive,
                        guarded: arm.guarded,
                        classification: analysis.classification,
                        continuation_use: analysis.continuation_use,
                        body: arm.body,
                    }
                })
                .collect(),
        })
        .collect::<Vec<_>>();

    let operations = control
        .effects
        .iter()
        .map(|effect| {
            let nodes = runtime_nodes.nodes_for_expr(effect.expr.0);
            let lowering = operation_lowering(
                effect.expr,
                &effect.route,
                &handler_exprs,
                &lexical_handlers,
            );
            EvidenceVmOperationPlan {
                expr: effect.expr,
                operation_def: effect.def,
                path: effect.path.clone(),
                slot: slot_for_operation_lowering(&effect.path, &lowering),
                kind: operation_kind(effect.kind),
                lowering,
                runtime_evidence_refs: nodes
                    .iter()
                    .map(|node| node.evidence_refs.len())
                    .sum::<usize>(),
                runtime_nodes: nodes.iter().map(|node| node.id).collect(),
            }
        })
        .collect::<Vec<_>>();

    let mut functions = surface
        .tasks
        .iter()
        .map(|task| function_plan(control, task))
        .collect::<Vec<_>>();
    attach_evidence_call_plans(program, &mut functions);
    let values = collect_value_env_plans(program, control);
    let objects = build_object_plan(
        program,
        surface,
        &handlers,
        &operations,
        &functions,
        &values,
    );

    let summary = summarize_plan(
        control,
        surface,
        &handlers,
        &operations,
        &functions,
        &values,
        &objects,
    );
    EvidenceVmPlan {
        summary,
        handlers,
        operations,
        functions,
        values,
        objects,
    }
}

pub fn format_plan(plan: &EvidenceVmPlan) -> String {
    let mut out = String::new();
    let summary = plan.summary;
    writeln!(&mut out, "evidence vm plan:").unwrap();
    writeln!(&mut out, "  handlers: {}", summary.handlers).unwrap();
    writeln!(
        &mut out,
        "  handler_continuations: direct_calls {} delayed_calls {} escape_arms {} tail_arms {}",
        summary.handler_continuation_direct_calls,
        summary.handler_continuation_delayed_calls,
        summary.handler_continuation_escape_arms,
        summary.handler_tail_resume_arms
    )
    .unwrap();
    writeln!(&mut out, "  operations: {}", summary.operations).unwrap();
    writeln!(
        &mut out,
        "  direct_operations: {} abortive {} resumptive {}",
        summary.direct_operations,
        summary.direct_abortive_operations,
        summary.direct_resumptive_operations
    )
    .unwrap();
    writeln!(
        &mut out,
        "  lexical_candidate_operations: {} delayed {}",
        summary.lexical_candidate_operations, summary.delayed_lexical_candidate_operations
    )
    .unwrap();
    writeln!(
        &mut out,
        "  blocked_operations: {} unhandled_operations: {}",
        summary.blocked_operations, summary.unhandled_operations
    )
    .unwrap();
    writeln!(
        &mut out,
        "  adapter_boundaries: {} delayed_boundaries: {} generic_fallbacks: {}",
        summary.adapter_boundaries, summary.delayed_boundaries, summary.generic_fallbacks
    )
    .unwrap();
    writeln!(
        &mut out,
        "  evidence_param_functions: {} evidence_params: {} evidence_arg_calls: {}",
        summary.evidence_param_functions, summary.evidence_params, summary.evidence_arg_calls
    )
    .unwrap();
    writeln!(
        &mut out,
        "  evidence_slot_keys: {}",
        summary.evidence_slot_keys
    )
    .unwrap();
    writeln!(
        &mut out,
        "  evidence_object_slots: {} function_objects: {} value_objects: {} call_objects: {} handler_objects: {} operation_objects: {} handler_caps: {} allowed_sets: {} provider_slots: {} provider_candidates: {} env_provider_slots: {} env_provider_candidates: {} direct_candidates: {}",
        summary.evidence_object_slots,
        summary.evidence_function_objects,
        summary.evidence_value_objects,
        summary.evidence_call_objects,
        summary.evidence_handler_objects,
        summary.evidence_operation_objects,
        summary.evidence_handler_capabilities,
        summary.evidence_allowed_sets,
        summary.evidence_provider_slots,
        summary.evidence_provider_candidates,
        summary.evidence_env_provider_slots,
        summary.evidence_env_provider_candidates,
        summary.evidence_direct_candidates
    )
    .unwrap();
    writeln!(
        &mut out,
        "  known_handler_objects: {} state {} compiler_state_certificates {}",
        summary.evidence_known_handler_objects,
        summary.evidence_known_state_handler_objects,
        summary.evidence_known_state_handler_compiler_certificates
    )
    .unwrap();
    writeln!(
        &mut out,
        "  known_operation_calls: {} state_get_candidates {} state_set_candidates {} direct_gets {} direct_sets {} route_proofs {}",
        summary.plan_known_operation_calls,
        summary.plan_known_operation_state_get_candidates,
        summary.plan_known_operation_state_set_candidates,
        summary.plan_known_operation_state_direct_gets,
        summary.plan_known_operation_state_direct_sets,
        summary.plan_known_state_operation_route_proofs
    )
    .unwrap();
    writeln!(
        &mut out,
        "  known_operation_rejects: no_operation_object {} not_call {} no_visibility {} no_candidate_handler {} no_known_state_access_proof {} known_state_access_handler_mismatch {} known_state_access_boundary_unsafe {} direct_execution_disabled {} no_known_handler {} wrong_handler {} wrong_operation {} blocked {} delayed {} provider_dirty {}",
        summary.plan_known_operation_reject_no_operation_object,
        summary.plan_known_operation_reject_not_call,
        summary.plan_known_operation_reject_no_visibility,
        summary.plan_known_operation_reject_no_candidate_handler,
        summary.plan_known_operation_reject_no_known_state_access_proof,
        summary.plan_known_operation_reject_known_state_access_handler_mismatch,
        summary.plan_known_operation_reject_known_state_access_boundary_unsafe,
        summary.plan_known_operation_reject_direct_execution_disabled,
        summary.plan_known_operation_reject_no_known_handler,
        summary.plan_known_operation_reject_wrong_handler,
        summary.plan_known_operation_reject_wrong_operation,
        summary.plan_known_operation_reject_blocked,
        summary.plan_known_operation_reject_delayed,
        summary.plan_known_operation_reject_provider_dirty
    )
    .unwrap();
    writeln!(
        &mut out,
        "  static_route_sites: total {} static_handler {} tail_resumptive {} abortive {} other_arm {}",
        summary.static_route_sites_total,
        summary.static_route_static_handler,
        summary.static_route_static_tail_resumptive,
        summary.static_route_static_abortive,
        summary.static_route_static_other_arm
    )
    .unwrap();
    writeln!(
        &mut out,
        "  static_route_dynamic: open_row {} multiple_candidates {} hygiene_barrier {} provider_env {} delayed_boundary {} host_escape {} unclassified {}",
        summary.static_route_dynamic_open_row,
        summary.static_route_dynamic_multiple_candidates,
        summary.static_route_dynamic_hygiene_barrier,
        summary.static_route_dynamic_provider_env,
        summary.static_route_dynamic_delayed_boundary,
        summary.static_route_dynamic_host_escape,
        summary.static_route_dynamic_unclassified
    )
    .unwrap();
    writeln!(
        &mut out,
        "  evidence_env_values: {} evidence_env_captures: {}",
        summary.evidence_env_values, summary.evidence_env_captures
    )
    .unwrap();
    writeln!(
        &mut out,
        "  runtime_tasks: {} runtime_nodes: {} runtime_evidence_refs: {}",
        summary.runtime_tasks, summary.runtime_nodes, summary.runtime_evidence_refs
    )
    .unwrap();
    format_handlers(&mut out, &plan.handlers);
    format_operations(&mut out, &plan.operations);
    format_functions(&mut out, &plan.functions);
    format_value_envs(&mut out, &plan.values);
    format_object_plan(&mut out, &plan.objects);
    out
}

fn summarize_plan(
    control: &ControlEvidenceProgram,
    surface: &RuntimeEvidenceSurface,
    handlers: &[EvidenceVmHandlerPlan],
    operations: &[EvidenceVmOperationPlan],
    functions: &[EvidenceVmFunctionPlan],
    values: &[EvidenceVmValueEnvPlan],
    objects: &EvidenceVmObjectPlan,
) -> EvidenceVmSummary {
    let known_operation_counts = known_operation_counts(operations, objects);
    let static_route_counts = static_route_counts(operations, objects);
    let mut summary = EvidenceVmSummary {
        handlers: control.handlers.len(),
        handler_continuation_direct_calls: handlers
            .iter()
            .flat_map(|handler| handler.arms.iter())
            .map(|arm| arm.continuation_use.direct_calls)
            .sum(),
        handler_continuation_delayed_calls: handlers
            .iter()
            .flat_map(|handler| handler.arms.iter())
            .map(|arm| arm.continuation_use.delayed_calls)
            .sum(),
        handler_continuation_escape_arms: handlers
            .iter()
            .flat_map(|handler| handler.arms.iter())
            .filter(|arm| arm.continuation_use.escapes)
            .count(),
        handler_tail_resume_arms: handlers
            .iter()
            .flat_map(|handler| handler.arms.iter())
            .filter(|arm| arm.continuation_use.tail_arg.is_some())
            .count(),
        operations: operations.len(),
        adapter_boundaries: control
            .adapters
            .iter()
            .filter(|adapter| adapter.creates_callback_boundary)
            .count(),
        delayed_boundaries: control.delayed_boundaries.len(),
        generic_fallbacks: control.fallbacks.len(),
        evidence_param_functions: functions
            .iter()
            .filter(|function| !function.required_evidence.is_empty())
            .count(),
        evidence_params: functions
            .iter()
            .map(|function| function.required_evidence.len())
            .sum(),
        evidence_arg_calls: functions
            .iter()
            .map(|function| function.calls_needing_evidence.len())
            .sum(),
        evidence_slot_keys: objects.slots.len(),
        evidence_object_slots: objects.slots.len(),
        evidence_function_objects: objects.functions.len(),
        evidence_value_objects: objects.values.len(),
        evidence_call_objects: objects.calls.len(),
        evidence_handler_objects: objects.handlers.len(),
        evidence_operation_objects: objects.operations.len(),
        evidence_known_handler_objects: objects.known_handlers.len(),
        evidence_known_state_handler_objects: objects
            .known_handlers
            .iter()
            .filter(|handler| handler.is_state())
            .count(),
        evidence_known_state_handler_compiler_certificates: objects
            .known_handlers
            .iter()
            .filter(|handler| handler.is_compiler_state_certificate())
            .count(),
        plan_known_operation_calls: known_operation_counts.calls,
        plan_known_operation_state_get_candidates: known_operation_counts.state_get_candidates,
        plan_known_operation_state_set_candidates: known_operation_counts.state_set_candidates,
        plan_known_operation_state_direct_gets: known_operation_counts.state_direct_gets,
        plan_known_operation_state_direct_sets: known_operation_counts.state_direct_sets,
        plan_known_state_operation_route_proofs: known_operation_counts.route_proofs,
        plan_known_operation_reject_no_operation_object: known_operation_counts
            .reject_no_operation_object,
        plan_known_operation_reject_not_call: known_operation_counts.reject_not_call,
        plan_known_operation_reject_no_visibility: known_operation_counts.reject_no_visibility,
        plan_known_operation_reject_no_candidate_handler: known_operation_counts
            .reject_no_candidate_handler,
        plan_known_operation_reject_no_known_state_access_proof: known_operation_counts
            .reject_no_known_state_access_proof,
        plan_known_operation_reject_known_state_access_handler_mismatch: known_operation_counts
            .reject_known_state_access_handler_mismatch,
        plan_known_operation_reject_known_state_access_boundary_unsafe: known_operation_counts
            .reject_known_state_access_boundary_unsafe,
        plan_known_operation_reject_direct_execution_disabled: known_operation_counts
            .reject_direct_execution_disabled,
        plan_known_operation_reject_no_known_handler: known_operation_counts
            .reject_no_known_handler,
        plan_known_operation_reject_wrong_handler: known_operation_counts.reject_wrong_handler,
        plan_known_operation_reject_wrong_operation: known_operation_counts.reject_wrong_operation,
        plan_known_operation_reject_blocked: known_operation_counts.reject_blocked,
        plan_known_operation_reject_delayed: known_operation_counts.reject_delayed,
        plan_known_operation_reject_provider_dirty: known_operation_counts.reject_provider_dirty,
        static_route_sites_total: static_route_counts.sites_total,
        static_route_static_handler: static_route_counts.static_handler,
        static_route_static_tail_resumptive: static_route_counts.static_tail_resumptive,
        static_route_static_abortive: static_route_counts.static_abortive,
        static_route_static_other_arm: static_route_counts.static_other_arm,
        static_route_dynamic_open_row: static_route_counts.dynamic_open_row,
        static_route_dynamic_multiple_candidates: static_route_counts.dynamic_multiple_candidates,
        static_route_dynamic_hygiene_barrier: static_route_counts.dynamic_hygiene_barrier,
        static_route_dynamic_provider_env: static_route_counts.dynamic_provider_env,
        static_route_dynamic_delayed_boundary: static_route_counts.dynamic_delayed_boundary,
        static_route_dynamic_host_escape: static_route_counts.dynamic_host_escape,
        static_route_dynamic_unclassified: static_route_counts.dynamic_unclassified,
        evidence_handler_capabilities: objects.handler_capabilities.len(),
        evidence_allowed_sets: objects.allowed_sets.len(),
        evidence_provider_slots: objects.providers.len(),
        evidence_provider_candidates: objects
            .providers
            .iter()
            .map(|provider| provider.handler_candidates.len())
            .sum(),
        evidence_env_provider_slots: env_provider_slot_count(objects),
        evidence_env_provider_candidates: env_provider_candidate_count(objects),
        evidence_direct_candidates: objects
            .operations
            .iter()
            .filter(|operation| operation.candidate_handler.is_some())
            .count(),
        evidence_env_values: values.len(),
        evidence_env_captures: values
            .iter()
            .map(|value| value.captured_evidence.len())
            .sum(),
        runtime_tasks: surface.tasks.len(),
        runtime_nodes: surface.tasks.iter().map(|task| task.nodes.len()).sum(),
        runtime_evidence_refs: surface
            .tasks
            .iter()
            .flat_map(|task| &task.nodes)
            .map(|node| node.evidence_refs.len())
            .sum(),
        ..EvidenceVmSummary::default()
    };
    for operation in operations {
        match operation.lowering {
            EvidenceVmOperationLowering::DirectHandlerCall {
                resumptive: false, ..
            } => {
                summary.direct_operations += 1;
                summary.direct_abortive_operations += 1;
            }
            EvidenceVmOperationLowering::DirectHandlerCall {
                resumptive: true, ..
            } => {
                summary.direct_operations += 1;
                summary.direct_resumptive_operations += 1;
            }
            EvidenceVmOperationLowering::LexicalHandlerCandidate {
                delayed_boundary, ..
            } => {
                summary.lexical_candidate_operations += 1;
                if delayed_boundary {
                    summary.delayed_lexical_candidate_operations += 1;
                }
            }
            EvidenceVmOperationLowering::HygieneFallback { .. } => {
                summary.blocked_operations += 1;
            }
            EvidenceVmOperationLowering::GenericFallback => {
                summary.unhandled_operations += 1;
            }
        }
    }
    summary
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct EvidenceVmStaticRouteCounts {
    sites_total: usize,
    static_handler: usize,
    static_tail_resumptive: usize,
    static_abortive: usize,
    static_other_arm: usize,
    dynamic_open_row: usize,
    dynamic_multiple_candidates: usize,
    dynamic_hygiene_barrier: usize,
    dynamic_provider_env: usize,
    dynamic_delayed_boundary: usize,
    dynamic_host_escape: usize,
    dynamic_unclassified: usize,
}

fn static_route_counts(
    operations: &[EvidenceVmOperationPlan],
    objects: &EvidenceVmObjectPlan,
) -> EvidenceVmStaticRouteCounts {
    let operation_objects = operation_objects_by_expr_from_slice(&objects.operations);
    let mut counts = EvidenceVmStaticRouteCounts::default();
    for operation in operations {
        if !matches!(operation.kind, EvidenceVmOperationKind::Call { .. }) {
            continue;
        }
        counts.sites_total += 1;
        let resolution = operation_objects
            .get(&operation.expr)
            .map(|object| object.static_route)
            .unwrap_or(EvidenceVmStaticRouteResolution::Dynamic(
                EvidenceVmStaticRouteDynamicReason::Unclassified,
            ));
        counts.record(resolution);
    }
    counts
}

fn operation_objects_by_expr_from_slice(
    objects: &[EvidenceVmOperationObjectPlan],
) -> HashMap<ExprId, &EvidenceVmOperationObjectPlan> {
    objects
        .iter()
        .map(|object| (object.expr, object))
        .collect::<HashMap<_, _>>()
}

impl EvidenceVmStaticRouteCounts {
    fn record(&mut self, resolution: EvidenceVmStaticRouteResolution) {
        match resolution {
            EvidenceVmStaticRouteResolution::StaticHandler { arm_class } => {
                self.static_handler += 1;
                match arm_class {
                    EvidenceVmHandlerArmClass::TailResumptive => {
                        self.static_tail_resumptive += 1;
                    }
                    EvidenceVmHandlerArmClass::Abortive => {
                        self.static_abortive += 1;
                    }
                    EvidenceVmHandlerArmClass::Value
                    | EvidenceVmHandlerArmClass::OneShotYield
                    | EvidenceVmHandlerArmClass::MultiShotYield
                    | EvidenceVmHandlerArmClass::MayEscapeYield
                    | EvidenceVmHandlerArmClass::Fallback => {
                        self.static_other_arm += 1;
                    }
                }
            }
            EvidenceVmStaticRouteResolution::Dynamic(reason) => match reason {
                EvidenceVmStaticRouteDynamicReason::OpenRow => {
                    self.dynamic_open_row += 1;
                }
                EvidenceVmStaticRouteDynamicReason::MultipleCandidates => {
                    self.dynamic_multiple_candidates += 1;
                }
                EvidenceVmStaticRouteDynamicReason::HygieneBarrier => {
                    self.dynamic_hygiene_barrier += 1;
                }
                EvidenceVmStaticRouteDynamicReason::ProviderEnvDependent => {
                    self.dynamic_provider_env += 1;
                }
                EvidenceVmStaticRouteDynamicReason::DelayedBoundary => {
                    self.dynamic_delayed_boundary += 1;
                }
                EvidenceVmStaticRouteDynamicReason::HostEscape => {
                    self.dynamic_host_escape += 1;
                }
                EvidenceVmStaticRouteDynamicReason::Unclassified => {
                    self.dynamic_unclassified += 1;
                }
            },
        }
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct EvidenceVmKnownOperationCounts {
    calls: usize,
    state_get_candidates: usize,
    state_set_candidates: usize,
    state_direct_gets: usize,
    state_direct_sets: usize,
    route_proofs: usize,
    reject_no_operation_object: usize,
    reject_not_call: usize,
    reject_no_visibility: usize,
    reject_no_candidate_handler: usize,
    reject_no_known_state_access_proof: usize,
    reject_known_state_access_handler_mismatch: usize,
    reject_known_state_access_boundary_unsafe: usize,
    reject_direct_execution_disabled: usize,
    reject_no_known_handler: usize,
    reject_wrong_handler: usize,
    reject_wrong_operation: usize,
    reject_blocked: usize,
    reject_delayed: usize,
    reject_provider_dirty: usize,
}

fn known_operation_counts(
    operations: &[EvidenceVmOperationPlan],
    objects: &EvidenceVmObjectPlan,
) -> EvidenceVmKnownOperationCounts {
    let targets = known_state_operation_targets_by_path(&objects.known_handlers);
    let known_call_sites = operations
        .iter()
        .filter(|operation| {
            targets.contains_key(&operation.path)
                && matches!(operation.kind, EvidenceVmOperationKind::Call { .. })
        })
        .count();
    let mut counts = EvidenceVmKnownOperationCounts {
        calls: objects.known_operations.len(),
        route_proofs: objects.known_state_operation_route_proofs.len(),
        reject_no_operation_object: known_call_sites.saturating_sub(objects.known_operations.len()),
        reject_not_call: operations
            .iter()
            .filter(|operation| {
                targets.contains_key(&operation.path)
                    && !matches!(operation.kind, EvidenceVmOperationKind::Call { .. })
            })
            .count(),
        ..EvidenceVmKnownOperationCounts::default()
    };
    for operation in &objects.known_operations {
        match operation.role {
            EvidenceVmKnownOperationRole::StateGet => {
                counts.state_get_candidates += 1;
                if operation.direct_ready {
                    counts.state_direct_gets += 1;
                }
            }
            EvidenceVmKnownOperationRole::StateSet => {
                counts.state_set_candidates += 1;
                if operation.direct_ready {
                    counts.state_direct_sets += 1;
                }
            }
        }
        if let Some(reject) = operation.reject {
            counts.record_reject(reject);
        }
    }
    counts
}

impl EvidenceVmKnownOperationCounts {
    fn record_reject(&mut self, reject: EvidenceVmKnownOperationReject) {
        match reject {
            EvidenceVmKnownOperationReject::NoOperationObject => {
                self.reject_no_operation_object += 1;
            }
            EvidenceVmKnownOperationReject::NotCall => {
                self.reject_not_call += 1;
            }
            EvidenceVmKnownOperationReject::NoVisibility => {
                self.reject_no_visibility += 1;
            }
            EvidenceVmKnownOperationReject::NoCandidateHandler => {
                self.reject_no_candidate_handler += 1;
            }
            EvidenceVmKnownOperationReject::NoKnownStateAccessProof => {
                self.reject_no_known_state_access_proof += 1;
            }
            EvidenceVmKnownOperationReject::KnownStateAccessHandlerMismatch => {
                self.reject_known_state_access_handler_mismatch += 1;
            }
            EvidenceVmKnownOperationReject::KnownStateAccessBoundaryUnsafe => {
                self.reject_known_state_access_boundary_unsafe += 1;
            }
            EvidenceVmKnownOperationReject::DirectExecutionDisabled => {
                self.reject_direct_execution_disabled += 1;
            }
            EvidenceVmKnownOperationReject::NoKnownHandler => {
                self.reject_no_known_handler += 1;
            }
            EvidenceVmKnownOperationReject::WrongHandler => {
                self.reject_wrong_handler += 1;
            }
            EvidenceVmKnownOperationReject::WrongOperation => {
                self.reject_wrong_operation += 1;
            }
            EvidenceVmKnownOperationReject::Blocked => {
                self.reject_blocked += 1;
            }
            EvidenceVmKnownOperationReject::Delayed => {
                self.reject_delayed += 1;
            }
            EvidenceVmKnownOperationReject::ProviderDirty => {
                self.reject_provider_dirty += 1;
            }
        }
    }
}

fn env_provider_slot_count(objects: &EvidenceVmObjectPlan) -> usize {
    objects
        .values
        .iter()
        .map(|value| value.env_providers.len())
        .sum::<usize>()
}

fn env_provider_candidate_count(objects: &EvidenceVmObjectPlan) -> usize {
    objects
        .values
        .iter()
        .flat_map(|value| &value.env_providers)
        .map(|provider| provider.handler_ids.len())
        .sum::<usize>()
}

fn function_plan(
    control: &ControlEvidenceProgram,
    task: &specialize::RuntimeEvidenceTask,
) -> EvidenceVmFunctionPlan {
    let provided_evidence_paths = provided_paths_for_nodes(&task.nodes);
    let required_evidence = required_evidence_for_nodes(&task.nodes, &provided_evidence_paths);
    let signature = EvidenceVmFunctionSignature {
        params: requirement_slots(&required_evidence),
        provides: provided_evidence_paths
            .iter()
            .map(|path| positive_slot(path.clone()))
            .collect(),
        value_env: Vec::new(),
    };
    EvidenceVmFunctionPlan {
        owner: task.owner,
        signature,
        node_count: task.nodes.len(),
        evidence_ref_count: task
            .nodes
            .iter()
            .map(|node| node.evidence_refs.len())
            .sum::<usize>(),
        required_evidence,
        provided_evidence_paths,
        calls_needing_evidence: Vec::new(),
        operation_exprs: task
            .nodes
            .iter()
            .filter_map(|node| {
                matches!(node.kind, RuntimeEvidenceNodeKind::OperationCall { .. })
                    .then_some(node.expr)
            })
            .collect(),
        handler_exprs: task
            .nodes
            .iter()
            .filter_map(|node| {
                matches!(node.kind, RuntimeEvidenceNodeKind::Handler { .. }).then_some(node.expr)
            })
            .collect(),
        fallback_exprs: generic_fallback_exprs(control, task.nodes.iter().map(|node| node.expr)),
    }
}

fn attach_evidence_call_plans(program: &Program, functions: &mut [EvidenceVmFunctionPlan]) {
    let requirements_by_instance = functions
        .iter()
        .filter_map(|function| {
            let RuntimeEvidenceTaskOwner::InstanceBody { instance, .. } = function.owner else {
                return None;
            };
            (!function.required_evidence.is_empty())
                .then(|| (instance, function.signature.params.clone()))
        })
        .collect::<HashMap<_, _>>();
    if requirements_by_instance.is_empty() {
        return;
    }
    for function in functions {
        let Some(body) = function_body(function.owner) else {
            continue;
        };
        let mut visited = HashSet::new();
        collect_evidence_arg_calls(
            program,
            ExprId(body),
            &requirements_by_instance,
            &mut visited,
            &mut function.calls_needing_evidence,
        );
    }
}

fn function_body(owner: RuntimeEvidenceTaskOwner) -> Option<u32> {
    match owner {
        RuntimeEvidenceTaskOwner::RootExpr { expr, .. } => Some(expr),
        RuntimeEvidenceTaskOwner::InstanceBody { body, .. } => Some(body),
    }
}

fn collect_evidence_arg_calls(
    program: &Program,
    expr: ExprId,
    requirements_by_instance: &HashMap<u32, Vec<EvidenceVmSlotKey>>,
    visited: &mut HashSet<ExprId>,
    out: &mut Vec<EvidenceVmCallPlan>,
) {
    if !visited.insert(expr) {
        return;
    }
    let Some(node) = control_expr(program, expr) else {
        return;
    };
    match node {
        Expr::Apply { callee, arg } => {
            if let Some(instance) = instance_ref(program, *callee)
                && let Some(required_evidence_slots) = requirements_by_instance.get(&instance.0)
            {
                out.push(EvidenceVmCallPlan {
                    apply: expr,
                    callee_instance: instance.0,
                    required_evidence_slots: required_evidence_slots.clone(),
                });
            }
            collect_evidence_arg_calls(program, *callee, requirements_by_instance, visited, out);
            collect_evidence_arg_calls(program, *arg, requirements_by_instance, visited, out);
        }
        Expr::Coerce { expr, .. }
        | Expr::ForceThunk { thunk: expr, .. }
        | Expr::FunctionAdapter { function: expr, .. }
        | Expr::MarkerFrame { body: expr, .. }
        | Expr::MakeThunk { body: expr, .. }
        | Expr::Lambda { body: expr, .. } => {
            collect_evidence_arg_calls(program, *expr, requirements_by_instance, visited, out);
        }
        Expr::Select {
            base, resolution, ..
        } => {
            if let Some(SelectResolution::Method { instance }) = resolution
                && let Some(required_evidence_slots) = requirements_by_instance.get(&instance.0)
            {
                out.push(EvidenceVmCallPlan {
                    apply: expr,
                    callee_instance: instance.0,
                    required_evidence_slots: required_evidence_slots.clone(),
                });
            }
            collect_evidence_arg_calls(program, *base, requirements_by_instance, visited, out);
        }
        Expr::RefSet { reference, value } => {
            collect_evidence_arg_calls(program, *reference, requirements_by_instance, visited, out);
            collect_evidence_arg_calls(program, *value, requirements_by_instance, visited, out);
        }
        Expr::Tuple(items) => {
            for item in items {
                collect_evidence_arg_calls(program, *item, requirements_by_instance, visited, out);
            }
        }
        Expr::Record { fields, spread } => {
            for field in fields {
                collect_evidence_arg_calls(
                    program,
                    field.value,
                    requirements_by_instance,
                    visited,
                    out,
                );
            }
            match spread {
                RecordSpread::None => {}
                RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                    collect_evidence_arg_calls(
                        program,
                        *expr,
                        requirements_by_instance,
                        visited,
                        out,
                    );
                }
            }
        }
        Expr::PolyVariant { payloads, .. } => {
            for payload in payloads {
                collect_evidence_arg_calls(
                    program,
                    *payload,
                    requirements_by_instance,
                    visited,
                    out,
                );
            }
        }
        Expr::Case { scrutinee, arms } => {
            collect_evidence_arg_calls(program, *scrutinee, requirements_by_instance, visited, out);
            for arm in arms {
                if let Some(guard) = arm.guard {
                    collect_evidence_arg_calls(
                        program,
                        guard,
                        requirements_by_instance,
                        visited,
                        out,
                    );
                }
                collect_evidence_arg_calls(
                    program,
                    arm.body,
                    requirements_by_instance,
                    visited,
                    out,
                );
            }
        }
        Expr::Catch { body, arms } => {
            collect_evidence_arg_calls(program, *body, requirements_by_instance, visited, out);
            for arm in arms {
                if let Some(guard) = arm.guard {
                    collect_evidence_arg_calls(
                        program,
                        guard,
                        requirements_by_instance,
                        visited,
                        out,
                    );
                }
                collect_evidence_arg_calls(
                    program,
                    arm.body,
                    requirements_by_instance,
                    visited,
                    out,
                );
            }
        }
        Expr::Block(block) => {
            collect_block_evidence_arg_calls(
                program,
                block,
                requirements_by_instance,
                visited,
                out,
            );
        }
        Expr::Lit(_)
        | Expr::PrimitiveOp { .. }
        | Expr::Constructor { .. }
        | Expr::EffectOp { .. }
        | Expr::Local(_)
        | Expr::InstanceRef(_) => {}
    }
}

fn collect_block_evidence_arg_calls(
    program: &Program,
    block: &Block,
    requirements_by_instance: &HashMap<u32, Vec<EvidenceVmSlotKey>>,
    visited: &mut HashSet<ExprId>,
    out: &mut Vec<EvidenceVmCallPlan>,
) {
    for stmt in &block.stmts {
        collect_stmt_evidence_arg_calls(program, stmt, requirements_by_instance, visited, out);
    }
    if let Some(tail) = block.tail {
        collect_evidence_arg_calls(program, tail, requirements_by_instance, visited, out);
    }
}

fn collect_stmt_evidence_arg_calls(
    program: &Program,
    stmt: &Stmt,
    requirements_by_instance: &HashMap<u32, Vec<EvidenceVmSlotKey>>,
    visited: &mut HashSet<ExprId>,
    out: &mut Vec<EvidenceVmCallPlan>,
) {
    match stmt {
        Stmt::Let(_, _, expr) | Stmt::Expr(expr) => {
            collect_evidence_arg_calls(program, *expr, requirements_by_instance, visited, out);
        }
        Stmt::Module(_, stmts) => {
            for stmt in stmts {
                collect_stmt_evidence_arg_calls(
                    program,
                    stmt,
                    requirements_by_instance,
                    visited,
                    out,
                );
            }
        }
    }
}

fn collect_value_env_plans(
    program: &Program,
    control: &ControlEvidenceProgram,
) -> Vec<EvidenceVmValueEnvPlan> {
    let adapters = control
        .adapters
        .iter()
        .map(|adapter| (adapter.expr, adapter))
        .collect::<HashMap<_, _>>();
    let mut values = Vec::new();
    for (index, expr) in program.exprs.iter().enumerate() {
        let id = ExprId(index as u32);
        match expr {
            Expr::Lambda { body, .. } => {
                let captured_evidence = requirements_in_expr(program, *body);
                if captured_evidence.is_empty() {
                    continue;
                }
                values.push(EvidenceVmValueEnvPlan {
                    expr: id,
                    kind: EvidenceVmValueEnvKind::Lambda { body: *body },
                    signature: value_env_signature(&captured_evidence),
                    captured_evidence,
                });
            }
            Expr::MakeThunk { body, .. } => {
                let captured_evidence = requirements_in_expr(program, *body);
                if captured_evidence.is_empty() {
                    continue;
                }
                values.push(EvidenceVmValueEnvPlan {
                    expr: id,
                    kind: EvidenceVmValueEnvKind::Thunk { body: *body },
                    signature: value_env_signature(&captured_evidence),
                    captured_evidence,
                });
            }
            Expr::FunctionAdapter { function, .. } => {
                let adapter = adapters.get(&id).copied();
                let captured_evidence = requirements_for_value_expr(program, *function);
                let kind = EvidenceVmValueEnvKind::FunctionAdapter {
                    function: *function,
                    creates_callback_boundary: adapter
                        .is_some_and(|adapter| adapter.creates_callback_boundary),
                    body_marker_count: adapter.map_or(0, |adapter| adapter.body_markers.len()),
                    arg_marker_count: adapter.map_or(0, |adapter| adapter.arg_markers.len()),
                    ret_marker_count: adapter.map_or(0, |adapter| adapter.ret_markers.len()),
                };
                if captured_evidence.is_empty() && !value_env_kind_has_boundary(&kind) {
                    continue;
                }
                values.push(EvidenceVmValueEnvPlan {
                    expr: id,
                    kind,
                    signature: value_env_signature(&captured_evidence),
                    captured_evidence,
                });
            }
            _ => {}
        }
    }
    values
}

fn value_env_kind_has_boundary(kind: &EvidenceVmValueEnvKind) -> bool {
    match kind {
        EvidenceVmValueEnvKind::Lambda { .. } | EvidenceVmValueEnvKind::Thunk { .. } => false,
        EvidenceVmValueEnvKind::FunctionAdapter {
            creates_callback_boundary,
            body_marker_count,
            arg_marker_count,
            ret_marker_count,
            ..
        } => {
            *creates_callback_boundary
                || *body_marker_count > 0
                || *arg_marker_count > 0
                || *ret_marker_count > 0
        }
    }
}

fn requirements_for_value_expr(
    program: &Program,
    expr: ExprId,
) -> Vec<EvidenceVmEvidenceRequirement> {
    let mut active = HashSet::new();
    requirements_for_value_expr_inner(program, expr, &mut active)
}

fn requirements_for_value_expr_inner(
    program: &Program,
    expr: ExprId,
    active: &mut HashSet<ExprId>,
) -> Vec<EvidenceVmEvidenceRequirement> {
    if !active.insert(expr) {
        return Vec::new();
    }
    let requirements = match control_expr(program, expr) {
        Some(Expr::Lambda { body, .. }) | Some(Expr::MakeThunk { body, .. }) => {
            requirements_in_expr(program, *body)
        }
        Some(Expr::FunctionAdapter { function, .. }) => {
            requirements_for_value_expr_inner(program, *function, active)
        }
        Some(Expr::Coerce { expr, .. })
        | Some(Expr::MarkerFrame { body: expr, .. })
        | Some(Expr::Select { base: expr, .. }) => {
            requirements_for_value_expr_inner(program, *expr, active)
        }
        Some(_) | None => requirements_in_expr(program, expr),
    };
    active.remove(&expr);
    requirements
}

fn requirements_in_expr(program: &Program, root: ExprId) -> Vec<EvidenceVmEvidenceRequirement> {
    let mut collector = RequirementCollector::default();
    let mut context = RequirementContext::default();
    let mut active = HashSet::new();
    collector.visit_expr(program, root, &mut context, &mut active);
    collector.finish()
}

#[derive(Default)]
struct RequirementCollector {
    by_slot: BTreeMap<EvidenceVmSlotKey, BTreeSet<u32>>,
}

impl RequirementCollector {
    fn record(&mut self, path: &[String], operation_expr: ExprId) {
        self.by_slot
            .entry(fallback_slot(path.to_vec()))
            .or_default()
            .insert(operation_expr.0);
    }

    fn finish(self) -> Vec<EvidenceVmEvidenceRequirement> {
        self.by_slot
            .into_iter()
            .map(|(slot, operation_exprs)| EvidenceVmEvidenceRequirement {
                slot,
                operation_exprs: operation_exprs.into_iter().collect(),
            })
            .collect()
    }

    fn visit_expr(
        &mut self,
        program: &Program,
        id: ExprId,
        context: &mut RequirementContext,
        active: &mut HashSet<ExprId>,
    ) {
        if !active.insert(id) {
            return;
        }
        let Some(expr) = control_expr(program, id) else {
            active.remove(&id);
            return;
        };
        match expr {
            Expr::Apply { callee, arg } => {
                if let Some(path) = effect_op_path(program, *callee)
                    && !context.handles(path)
                {
                    self.record(path, id);
                }
                self.visit_expr(program, *callee, context, active);
                self.visit_expr(program, *arg, context, active);
            }
            Expr::Catch { body, arms } => {
                let handled_paths = arms
                    .iter()
                    .filter_map(|arm| arm.operation_path.clone())
                    .collect::<Vec<_>>();
                context.with_handled_paths(&handled_paths, |context| {
                    self.visit_expr(program, *body, context, active);
                });
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.visit_expr(program, guard, context, active);
                    }
                    self.visit_expr(program, arm.body, context, active);
                }
            }
            Expr::Coerce { expr, .. }
            | Expr::ForceThunk { thunk: expr, .. }
            | Expr::MarkerFrame { body: expr, .. }
            | Expr::Select { base: expr, .. } => {
                self.visit_expr(program, *expr, context, active);
            }
            Expr::RefSet { reference, value } => {
                self.visit_expr(program, *reference, context, active);
                self.visit_expr(program, *value, context, active);
            }
            Expr::Tuple(items) => {
                for item in items {
                    self.visit_expr(program, *item, context, active);
                }
            }
            Expr::Record { fields, spread } => {
                for field in fields {
                    self.visit_expr(program, field.value, context, active);
                }
                self.visit_spread(program, spread, context, active);
            }
            Expr::PolyVariant { payloads, .. } => {
                for payload in payloads {
                    self.visit_expr(program, *payload, context, active);
                }
            }
            Expr::Case { scrutinee, arms } => {
                self.visit_expr(program, *scrutinee, context, active);
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.visit_expr(program, guard, context, active);
                    }
                    self.visit_expr(program, arm.body, context, active);
                }
            }
            Expr::Block(block) => self.visit_block(program, block, context, active),
            Expr::Lambda { .. } | Expr::MakeThunk { .. } | Expr::FunctionAdapter { .. } => {}
            Expr::Lit(_)
            | Expr::PrimitiveOp { .. }
            | Expr::Constructor { .. }
            | Expr::EffectOp { .. }
            | Expr::Local(_)
            | Expr::InstanceRef(_) => {}
        }
        active.remove(&id);
    }

    fn visit_spread(
        &mut self,
        program: &Program,
        spread: &RecordSpread<ExprId>,
        context: &mut RequirementContext,
        active: &mut HashSet<ExprId>,
    ) {
        match spread {
            RecordSpread::None => {}
            RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                self.visit_expr(program, *expr, context, active);
            }
        }
    }

    fn visit_block(
        &mut self,
        program: &Program,
        block: &Block,
        context: &mut RequirementContext,
        active: &mut HashSet<ExprId>,
    ) {
        for stmt in &block.stmts {
            self.visit_stmt(program, stmt, context, active);
        }
        if let Some(tail) = block.tail {
            self.visit_expr(program, tail, context, active);
        }
    }

    fn visit_stmt(
        &mut self,
        program: &Program,
        stmt: &Stmt,
        context: &mut RequirementContext,
        active: &mut HashSet<ExprId>,
    ) {
        match stmt {
            Stmt::Let(_, _, expr) | Stmt::Expr(expr) => {
                self.visit_expr(program, *expr, context, active);
            }
            Stmt::Module(_, stmts) => {
                for stmt in stmts {
                    self.visit_stmt(program, stmt, context, active);
                }
            }
        }
    }
}

#[derive(Debug, Default)]
struct RequirementContext {
    handled_paths: Vec<Vec<String>>,
}

impl RequirementContext {
    fn handles(&self, path: &[String]) -> bool {
        self.handled_paths
            .iter()
            .rev()
            .any(|handled_path| handled_path == path)
    }

    fn with_handled_paths(&mut self, paths: &[Vec<String>], f: impl FnOnce(&mut Self)) {
        let start = self.handled_paths.len();
        self.handled_paths.extend(paths.iter().cloned());
        f(self);
        self.handled_paths.truncate(start);
    }
}

fn effect_op_path(program: &Program, expr: ExprId) -> Option<&[String]> {
    match control_expr(program, expr)? {
        Expr::EffectOp { path, .. } => Some(path),
        _ => None,
    }
}

fn instance_ref(program: &Program, expr: ExprId) -> Option<control_vm::InstanceId> {
    match control_expr(program, expr)? {
        Expr::InstanceRef(instance) => Some(*instance),
        _ => None,
    }
}

fn provided_paths_for_nodes(nodes: &[RuntimeEvidenceNode]) -> Vec<Vec<String>> {
    let mut paths = BTreeSet::new();
    for node in nodes {
        if let RuntimeEvidenceNodeKind::Handler { handled_paths, .. } = &node.kind {
            for path in handled_paths {
                paths.insert(path.clone());
            }
        }
    }
    paths.into_iter().collect()
}

fn required_evidence_for_nodes(
    nodes: &[RuntimeEvidenceNode],
    provided_paths: &[Vec<String>],
) -> Vec<EvidenceVmEvidenceRequirement> {
    let provided = provided_paths.iter().collect::<BTreeSet<_>>();
    let mut by_slot = BTreeMap::<EvidenceVmSlotKey, Vec<u32>>::new();
    for node in nodes {
        if let RuntimeEvidenceNodeKind::OperationCall { path, .. } = &node.kind
            && !provided.contains(path)
        {
            by_slot
                .entry(fallback_slot(path.clone()))
                .or_default()
                .push(node.expr);
        }
    }
    by_slot
        .into_iter()
        .map(|(slot, operation_exprs)| EvidenceVmEvidenceRequirement {
            slot,
            operation_exprs,
        })
        .collect()
}

fn positive_slot(family: Vec<String>) -> EvidenceVmSlotKey {
    EvidenceVmSlotKey {
        family,
        route: EvidenceVmSlotRouteKey::Positive,
    }
}

fn blocked_slot(family: Vec<String>) -> EvidenceVmSlotKey {
    EvidenceVmSlotKey {
        family,
        route: EvidenceVmSlotRouteKey::Blocked,
    }
}

fn fallback_slot(family: Vec<String>) -> EvidenceVmSlotKey {
    EvidenceVmSlotKey {
        family,
        route: EvidenceVmSlotRouteKey::UnknownFallback,
    }
}

fn slot_for_operation_lowering(
    path: &[String],
    lowering: &EvidenceVmOperationLowering,
) -> EvidenceVmSlotKey {
    match lowering {
        EvidenceVmOperationLowering::DirectHandlerCall { .. } => positive_slot(path.to_vec()),
        EvidenceVmOperationLowering::HygieneFallback { .. } => blocked_slot(path.to_vec()),
        EvidenceVmOperationLowering::LexicalHandlerCandidate { .. }
        | EvidenceVmOperationLowering::GenericFallback => fallback_slot(path.to_vec()),
    }
}

fn requirement_slots(requirements: &[EvidenceVmEvidenceRequirement]) -> Vec<EvidenceVmSlotKey> {
    requirements
        .iter()
        .map(|requirement| requirement.slot.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn value_env_signature(captures: &[EvidenceVmEvidenceRequirement]) -> EvidenceVmValueEnvSignature {
    EvidenceVmValueEnvSignature {
        captures: requirement_slots(captures),
    }
}

fn build_object_plan(
    program: &Program,
    surface: &RuntimeEvidenceSurface,
    handlers: &[EvidenceVmHandlerPlan],
    operations: &[EvidenceVmOperationPlan],
    functions: &[EvidenceVmFunctionPlan],
    values: &[EvidenceVmValueEnvPlan],
) -> EvidenceVmObjectPlan {
    let slots = collect_object_slots(handlers, operations, functions, values);
    let slot_ids = slots
        .iter()
        .enumerate()
        .map(|(index, key)| (key.clone(), index as u32))
        .collect::<BTreeMap<_, _>>();
    let slot_plans = slots
        .into_iter()
        .enumerate()
        .map(|(index, key)| EvidenceVmSlotPlan {
            id: index as u32,
            key,
        })
        .collect::<Vec<_>>();

    let mut handlers = build_handler_objects(handlers, &slot_ids);
    let handler_capabilities = build_handler_capabilities(&handlers);
    let known_handlers = build_known_handler_plans(program, &handlers, surface);
    let function_objects = build_function_objects(functions, &slot_ids);
    let lexical_envs = build_lexical_handler_envs(program, values, &slot_plans, &handlers);
    attach_handler_definition_envs(&lexical_envs.handler_definition_envs, &mut handlers);
    let value_objects = build_value_objects(values, &slot_ids, &lexical_envs.value_provider_envs);
    let call_objects = build_call_objects(functions, &slot_ids);
    let handler_index = handlers
        .iter()
        .map(|handler| ((handler.handler, handler.slot_id), handler.id))
        .collect::<HashMap<_, _>>();
    let (operation_objects, allowed_sets) =
        build_operation_objects(operations, &slot_ids, &handler_index, &handlers);
    let (known_operations, known_state_operation_route_proofs) =
        build_known_operation_plans(operations, &operation_objects, &known_handlers, surface);
    let providers = build_provider_index(&slot_plans, &handlers);

    EvidenceVmObjectPlan {
        slots: slot_plans,
        functions: function_objects,
        values: value_objects,
        calls: call_objects,
        handlers,
        operations: operation_objects,
        known_handlers,
        known_operations,
        known_state_operation_route_proofs,
        handler_capabilities,
        allowed_sets,
        providers,
    }
}

fn build_known_handler_plans(
    program: &Program,
    handlers: &[EvidenceVmHandlerObjectPlan],
    surface: &RuntimeEvidenceSurface,
) -> Vec<EvidenceVmKnownHandlerPlan> {
    let mut plans = Vec::new();
    for certificate in &surface.known_state_handlers {
        for pair in state_handler_pairs_for_family(handlers, &certificate.effect_path) {
            let Some(state) = compiler_state_param_for_handler(program, pair.handler) else {
                continue;
            };
            plans.push(EvidenceVmKnownHandlerPlan::State(
                EvidenceVmKnownStateHandlerPlan {
                    id: EvidenceVmKnownHandlerPlanId(plans.len() as u32),
                    synthetic_var: certificate.synthetic_var,
                    handler: pair.handler,
                    state,
                    family: certificate.effect_path.clone(),
                    get_handler_id: pair.get_handler_id,
                    set_handler_id: pair.set_handler_id,
                    source: known_state_source(certificate.source),
                    continuation: known_state_continuation(certificate.continuation),
                },
            ));
        }
    }
    plans
}

fn build_known_operation_plans(
    operations: &[EvidenceVmOperationPlan],
    operation_objects: &[EvidenceVmOperationObjectPlan],
    known_handlers: &[EvidenceVmKnownHandlerPlan],
    surface: &RuntimeEvidenceSurface,
) -> (
    Vec<EvidenceVmKnownOperationPlan>,
    Vec<EvidenceVmKnownStateOperationRouteProof>,
) {
    debug_assert_eq!(
        operations.len(),
        operation_objects.len(),
        "operation objects are built in operation plan order"
    );
    let targets = known_state_operation_targets_by_path(known_handlers);
    if targets.is_empty() {
        return (Vec::new(), Vec::new());
    }
    let accesses = known_state_access_targets(surface);
    let mut proofs = Vec::new();
    let operations = operations
        .iter()
        .zip(operation_objects.iter())
        .filter_map(|(operation, object)| {
            let target = targets.get(&operation.path)?;
            let EvidenceVmOperationKind::Call { apply, callee } = operation.kind else {
                return None;
            };
            let operation_def = operation.operation_def.map(|def| def.0);
            let proof = build_known_state_operation_route_proof(
                operation,
                target,
                apply,
                callee,
                operation_def.and_then(|operation_def| {
                    accesses.get(&EvidenceVmKnownStateAccessKey {
                        synthetic_var: target.synthetic_var,
                        role: target.role,
                        operation_def,
                    })
                }),
                &mut proofs,
            );
            let reject = known_operation_direct_ready(operation, object, target, proof.is_some());
            Some(EvidenceVmKnownOperationPlan {
                expr: operation.expr,
                apply,
                callee,
                known_handler: target.known_handler,
                handler_id: target.handler_id,
                role: target.role,
                direct_ready: reject.is_none(),
                reject,
                visibility: object.visibility.allowed_set_id,
                route_proof: proof,
            })
        })
        .collect();
    (operations, proofs)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EvidenceVmKnownOperationTarget {
    synthetic_var: u32,
    catch_expr: ExprId,
    known_handler: EvidenceVmKnownHandlerPlanId,
    handler_id: u32,
    role: EvidenceVmKnownOperationRole,
}

fn known_state_operation_targets_by_path(
    known_handlers: &[EvidenceVmKnownHandlerPlan],
) -> BTreeMap<Vec<String>, EvidenceVmKnownOperationTarget> {
    let mut targets = BTreeMap::new();
    for known in known_handlers {
        let EvidenceVmKnownHandlerPlan::State(state) = known;
        targets.insert(
            state_operation_path(&state.family, EvidenceVmKnownStateOperation::Get),
            EvidenceVmKnownOperationTarget {
                synthetic_var: state.synthetic_var,
                catch_expr: state.handler,
                known_handler: state.id,
                handler_id: state.get_handler_id,
                role: EvidenceVmKnownOperationRole::StateGet,
            },
        );
        targets.insert(
            state_operation_path(&state.family, EvidenceVmKnownStateOperation::Set),
            EvidenceVmKnownOperationTarget {
                synthetic_var: state.synthetic_var,
                catch_expr: state.handler,
                known_handler: state.id,
                handler_id: state.set_handler_id,
                role: EvidenceVmKnownOperationRole::StateSet,
            },
        );
    }
    targets
}

#[derive(Debug, Clone, Copy)]
struct EvidenceVmKnownStateAccessTarget {
    operation_def: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct EvidenceVmKnownStateAccessKey {
    synthetic_var: u32,
    role: EvidenceVmKnownOperationRole,
    operation_def: u32,
}

fn known_state_access_targets(
    surface: &RuntimeEvidenceSurface,
) -> BTreeMap<EvidenceVmKnownStateAccessKey, EvidenceVmKnownStateAccessTarget> {
    let mut targets = BTreeMap::new();
    for access in &surface.known_state_accesses {
        targets
            .entry(EvidenceVmKnownStateAccessKey {
                synthetic_var: access.synthetic_var,
                role: known_state_access_role(access.role),
                operation_def: access.operation_def,
            })
            .or_insert(EvidenceVmKnownStateAccessTarget {
                operation_def: access.operation_def,
            });
    }
    targets
}

fn known_state_access_role(
    role: specialize::RuntimeEvidenceKnownStateAccessRole,
) -> EvidenceVmKnownOperationRole {
    match role {
        specialize::RuntimeEvidenceKnownStateAccessRole::StateGet => {
            EvidenceVmKnownOperationRole::StateGet
        }
        specialize::RuntimeEvidenceKnownStateAccessRole::StateSet => {
            EvidenceVmKnownOperationRole::StateSet
        }
    }
}

fn build_known_state_operation_route_proof(
    operation: &EvidenceVmOperationPlan,
    target: &EvidenceVmKnownOperationTarget,
    apply: ExprId,
    callee: ExprId,
    access: Option<&EvidenceVmKnownStateAccessTarget>,
    proofs: &mut Vec<EvidenceVmKnownStateOperationRouteProof>,
) -> Option<EvidenceVmKnownStateOperationRouteProofId> {
    let access = access?;
    let id = EvidenceVmKnownStateOperationRouteProofId(proofs.len() as u32);
    proofs.push(EvidenceVmKnownStateOperationRouteProof {
        id,
        operation_expr: operation.expr,
        apply,
        callee,
        access_operation_def: access.operation_def,
        synthetic_var: target.synthetic_var,
        plan_id: target.known_handler,
        catch_expr: target.catch_expr,
        handler_id: target.handler_id,
        role: target.role,
        source: EvidenceVmKnownStateOperationRouteProofSource::CompilerLocalVar {
            synthetic_var: target.synthetic_var,
        },
        visibility: clean_known_state_visibility_proof(operation, target),
        payload: known_state_operation_payload_proof(target.role),
    });
    Some(id)
}

fn clean_known_state_visibility_proof(
    operation: &EvidenceVmOperationPlan,
    target: &EvidenceVmKnownOperationTarget,
) -> EvidenceVmKnownStateOperationVisibilityProof {
    EvidenceVmKnownStateOperationVisibilityProof::CleanKnownStateCatch {
        catch_expr: target.catch_expr,
        plan_id: target.known_handler,
        handler_id: target.handler_id,
        no_delayed_boundary: !matches!(
            operation.lowering,
            EvidenceVmOperationLowering::LexicalHandlerCandidate {
                delayed_boundary: true,
                ..
            }
        ),
        no_callback_boundary: !matches!(
            operation.lowering,
            EvidenceVmOperationLowering::HygieneFallback {
                callback_boundary: true,
                ..
            }
        ),
        no_blocking_marker: !matches!(
            operation.lowering,
            EvidenceVmOperationLowering::HygieneFallback { .. }
        ),
    }
}

fn known_state_operation_payload_proof(
    role: EvidenceVmKnownOperationRole,
) -> EvidenceVmKnownStateOperationPayloadProof {
    match role {
        EvidenceVmKnownOperationRole::StateGet => {
            EvidenceVmKnownStateOperationPayloadProof::UnitPayloadForGet
        }
        EvidenceVmKnownOperationRole::StateSet => {
            EvidenceVmKnownStateOperationPayloadProof::SingleValuePayloadForSet
        }
    }
}

fn known_operation_direct_ready(
    operation: &EvidenceVmOperationPlan,
    _object: &EvidenceVmOperationObjectPlan,
    target: &EvidenceVmKnownOperationTarget,
    has_route_proof: bool,
) -> Option<EvidenceVmKnownOperationReject> {
    match operation.lowering {
        EvidenceVmOperationLowering::HygieneFallback { .. } => {
            return Some(EvidenceVmKnownOperationReject::KnownStateAccessBoundaryUnsafe);
        }
        EvidenceVmOperationLowering::LexicalHandlerCandidate {
            delayed_boundary: true,
            ..
        } => return Some(EvidenceVmKnownOperationReject::KnownStateAccessBoundaryUnsafe),
        EvidenceVmOperationLowering::GenericFallback => {}
        EvidenceVmOperationLowering::DirectHandlerCall { .. }
        | EvidenceVmOperationLowering::LexicalHandlerCandidate {
            delayed_boundary: false,
            ..
        } => {}
    }
    if !has_route_proof {
        return Some(EvidenceVmKnownOperationReject::NoKnownStateAccessProof);
    }
    match target.role {
        EvidenceVmKnownOperationRole::StateGet | EvidenceVmKnownOperationRole::StateSet => None,
    }
}

fn compiler_state_param_for_handler(program: &Program, handler: ExprId) -> Option<DefId> {
    let mut found = None;
    for expr in &program.exprs {
        let Expr::Lambda {
            param: Pat::Var(state),
            body,
        } = expr
        else {
            continue;
        };
        let Some(Expr::Lambda {
            param: Pat::Var(_),
            body: inner,
        }) = program.exprs.get(body.0 as usize)
        else {
            continue;
        };
        if *inner != handler {
            continue;
        }
        match found {
            Some(existing) if existing != *state => return None,
            Some(_) => {}
            None => found = Some(*state),
        }
    }
    found
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EvidenceVmKnownStateHandlerPair {
    handler: ExprId,
    get_handler_id: u32,
    set_handler_id: u32,
}

fn state_handler_pairs_for_family(
    handlers: &[EvidenceVmHandlerObjectPlan],
    family: &[String],
) -> Vec<EvidenceVmKnownStateHandlerPair> {
    let get_path = state_operation_path(family, EvidenceVmKnownStateOperation::Get);
    let set_path = state_operation_path(family, EvidenceVmKnownStateOperation::Set);
    let mut by_handler = BTreeMap::<u32, (ExprId, Vec<&EvidenceVmHandlerObjectPlan>)>::new();
    for handler in handlers {
        by_handler
            .entry(handler.handler.0)
            .or_insert_with(|| (handler.handler, Vec::new()))
            .1
            .push(handler);
    }
    by_handler
        .into_iter()
        .filter_map(|(_, (handler, arms))| {
            if arms.len() != 2 {
                return None;
            }
            let get = arms.iter().find(|arm| arm.path == get_path)?;
            let set = arms.iter().find(|arm| arm.path == set_path)?;
            Some(EvidenceVmKnownStateHandlerPair {
                handler,
                get_handler_id: get.id,
                set_handler_id: set.id,
            })
        })
        .collect()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceVmKnownStateOperation {
    Get,
    Set,
}

fn state_operation_path(
    family: &[String],
    operation: EvidenceVmKnownStateOperation,
) -> Vec<String> {
    let mut path = family.to_vec();
    path.push(
        match operation {
            EvidenceVmKnownStateOperation::Get => "get",
            EvidenceVmKnownStateOperation::Set => "set",
        }
        .to_string(),
    );
    path
}

fn known_state_source(
    source: specialize::RuntimeEvidenceKnownStateHandlerSource,
) -> EvidenceVmKnownStateHandlerSource {
    match source {
        specialize::RuntimeEvidenceKnownStateHandlerSource::CompilerLocalVar => {
            EvidenceVmKnownStateHandlerSource::CompilerLocalVar
        }
    }
}

fn known_state_continuation(
    continuation: specialize::RuntimeEvidenceKnownStateContinuationSemantics,
) -> EvidenceVmKnownStateContinuationSemantics {
    match continuation {
        specialize::RuntimeEvidenceKnownStateContinuationSemantics::SnapshotFork => {
            EvidenceVmKnownStateContinuationSemantics::SnapshotFork
        }
    }
}

fn collect_object_slots(
    handlers: &[EvidenceVmHandlerPlan],
    operations: &[EvidenceVmOperationPlan],
    functions: &[EvidenceVmFunctionPlan],
    values: &[EvidenceVmValueEnvPlan],
) -> Vec<EvidenceVmSlotKey> {
    let mut slots = BTreeSet::new();
    for handler in handlers {
        for arm in &handler.arms {
            if let Some(path) = &arm.path {
                slots.insert(positive_slot(path.clone()));
            }
        }
    }
    for operation in operations {
        slots.insert(operation.slot.clone());
    }
    for function in functions {
        slots.extend(function.signature.params.iter().cloned());
        slots.extend(function.signature.provides.iter().cloned());
        slots.extend(function.signature.value_env.iter().cloned());
    }
    for value in values {
        slots.extend(value.signature.captures.iter().cloned());
    }
    slots.into_iter().collect()
}

fn build_function_objects(
    functions: &[EvidenceVmFunctionPlan],
    slot_ids: &BTreeMap<EvidenceVmSlotKey, u32>,
) -> Vec<EvidenceVmFunctionObjectPlan> {
    functions
        .iter()
        .enumerate()
        .map(|(index, function)| EvidenceVmFunctionObjectPlan {
            id: index as u32,
            owner: function.owner,
            params: slot_ids_for_keys(&function.signature.params, slot_ids),
            provides: slot_ids_for_keys(&function.signature.provides, slot_ids),
            value_env: slot_ids_for_keys(&function.signature.value_env, slot_ids),
        })
        .collect()
}

fn build_value_objects(
    values: &[EvidenceVmValueEnvPlan],
    slot_ids: &BTreeMap<EvidenceVmSlotKey, u32>,
    value_provider_envs: &HashMap<ExprId, Vec<EvidenceVmEnvProviderPlan>>,
) -> Vec<EvidenceVmValueObjectPlan> {
    values
        .iter()
        .enumerate()
        .map(|(index, value)| EvidenceVmValueObjectPlan {
            id: index as u32,
            expr: value.expr,
            kind: value.kind.clone(),
            captures: slot_ids_for_keys(&value.signature.captures, slot_ids),
            env_providers: value_provider_envs
                .get(&value.expr)
                .cloned()
                .unwrap_or_default(),
        })
        .collect()
}

#[derive(Debug, Default)]
struct EvidenceVmLexicalHandlerEnvPlan {
    value_provider_envs: HashMap<ExprId, Vec<EvidenceVmEnvProviderPlan>>,
    handler_definition_envs: HashMap<u32, Vec<u32>>,
}

fn build_lexical_handler_envs(
    program: &Program,
    values: &[EvidenceVmValueEnvPlan],
    slots: &[EvidenceVmSlotPlan],
    handlers: &[EvidenceVmHandlerObjectPlan],
) -> EvidenceVmLexicalHandlerEnvPlan {
    let capture_slots = values
        .iter()
        .map(|value| (value.expr, value.signature.captures.clone()))
        .collect::<HashMap<_, _>>();
    if capture_slots.is_empty() && handlers.is_empty() {
        return EvidenceVmLexicalHandlerEnvPlan::default();
    }
    let slot_ids = slots
        .iter()
        .map(|slot| (slot.key.clone(), slot.id))
        .collect::<BTreeMap<_, _>>();
    let handlers_by_expr = handlers.iter().fold(
        HashMap::<ExprId, Vec<u32>>::new(),
        |mut by_expr, handler| {
            by_expr.entry(handler.handler).or_default().push(handler.id);
            by_expr
        },
    );
    let handlers_by_id = handlers
        .iter()
        .map(|handler| (handler.id, handler))
        .collect::<HashMap<_, _>>();
    let mut collector = LexicalHandlerEnvCollector {
        capture_slots,
        slot_ids,
        handlers_by_expr,
        handlers_by_id,
        value_providers: HashMap::new(),
        handler_definition_envs: HashMap::new(),
    };
    collector.collect_program(program);
    collector.finish()
}

struct LexicalHandlerEnvCollector<'a> {
    capture_slots: HashMap<ExprId, Vec<EvidenceVmSlotKey>>,
    slot_ids: BTreeMap<EvidenceVmSlotKey, u32>,
    handlers_by_expr: HashMap<ExprId, Vec<u32>>,
    handlers_by_id: HashMap<u32, &'a EvidenceVmHandlerObjectPlan>,
    value_providers: HashMap<ExprId, BTreeMap<u32, BTreeSet<u32>>>,
    handler_definition_envs: HashMap<u32, Vec<u32>>,
}

impl LexicalHandlerEnvCollector<'_> {
    fn collect_program(&mut self, program: &Program) {
        let mut active_handlers = Vec::new();
        for instance in &program.instances {
            self.visit_expr(program, instance.entry, &mut active_handlers);
        }
        for root in &program.roots {
            match root {
                Root::Instance(instance) | Root::EvalInstance(instance) => {
                    if let Some(instance) = program.instances.get(instance.0 as usize) {
                        self.visit_expr(program, instance.entry, &mut active_handlers);
                    }
                }
                Root::Expr(expr) => self.visit_expr(program, *expr, &mut active_handlers),
            }
        }
    }

    fn finish(self) -> EvidenceVmLexicalHandlerEnvPlan {
        let value_provider_envs = self
            .value_providers
            .into_iter()
            .map(|(expr, by_slot)| {
                let providers = by_slot
                    .into_iter()
                    .filter_map(|(slot_id, handler_ids)| {
                        let handler_ids = handler_ids.into_iter().collect::<Vec<_>>();
                        (!handler_ids.is_empty()).then_some(EvidenceVmEnvProviderPlan {
                            slot_id,
                            handler_ids,
                        })
                    })
                    .collect::<Vec<_>>();
                (expr, providers)
            })
            .collect();
        EvidenceVmLexicalHandlerEnvPlan {
            value_provider_envs,
            handler_definition_envs: self.handler_definition_envs,
        }
    }

    fn visit_expr(&mut self, program: &Program, id: ExprId, active_handlers: &mut Vec<u32>) {
        self.record_value_env(id, active_handlers);
        let Some(expr) = control_expr(program, id) else {
            return;
        };
        match expr {
            Expr::Catch { body, arms } => {
                let handler_ids = self.handlers_by_expr.get(&id).cloned().unwrap_or_default();
                for handler_id in &handler_ids {
                    self.handler_definition_envs
                        .entry(*handler_id)
                        .or_insert_with(|| active_handlers.clone());
                }

                let start = active_handlers.len();
                active_handlers.extend(handler_ids);
                self.visit_expr(program, *body, active_handlers);
                active_handlers.truncate(start);
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.visit_expr(program, guard, active_handlers);
                    }
                    self.visit_expr(program, arm.body, active_handlers);
                }
            }
            Expr::Apply { callee, arg } => {
                self.visit_expr(program, *callee, active_handlers);
                self.visit_expr(program, *arg, active_handlers);
            }
            Expr::Coerce { expr, .. }
            | Expr::ForceThunk { thunk: expr, .. }
            | Expr::FunctionAdapter { function: expr, .. }
            | Expr::MakeThunk { body: expr, .. }
            | Expr::Lambda { body: expr, .. }
            | Expr::MarkerFrame { body: expr, .. }
            | Expr::Select { base: expr, .. } => {
                self.visit_expr(program, *expr, active_handlers);
            }
            Expr::RefSet { reference, value } => {
                self.visit_expr(program, *reference, active_handlers);
                self.visit_expr(program, *value, active_handlers);
            }
            Expr::Tuple(items) => {
                for item in items {
                    self.visit_expr(program, *item, active_handlers);
                }
            }
            Expr::Record { fields, spread } => {
                for field in fields {
                    self.visit_expr(program, field.value, active_handlers);
                }
                self.visit_spread(program, spread, active_handlers);
            }
            Expr::PolyVariant { payloads, .. } => {
                for payload in payloads {
                    self.visit_expr(program, *payload, active_handlers);
                }
            }
            Expr::Case { scrutinee, arms } => {
                self.visit_expr(program, *scrutinee, active_handlers);
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.visit_expr(program, guard, active_handlers);
                    }
                    self.visit_expr(program, arm.body, active_handlers);
                }
            }
            Expr::Block(block) => self.visit_block(program, block, active_handlers),
            Expr::Lit(_)
            | Expr::PrimitiveOp { .. }
            | Expr::Constructor { .. }
            | Expr::EffectOp { .. }
            | Expr::Local(_)
            | Expr::InstanceRef(_) => {}
        }
    }

    fn record_value_env(&mut self, id: ExprId, active_handlers: &[u32]) {
        let Some(captures) = self.capture_slots.get(&id) else {
            return;
        };
        for capture in captures {
            let Some(slot_id) = self.slot_ids.get(capture).copied() else {
                continue;
            };
            if matches!(capture.route, EvidenceVmSlotRouteKey::Blocked) {
                continue;
            }
            let handler_ids = active_handlers
                .iter()
                .filter_map(|handler_id| {
                    let handler = self.handlers_by_id.get(handler_id)?;
                    (handler.path == capture.family).then_some(*handler_id)
                })
                .collect::<Vec<_>>();
            if handler_ids.is_empty() {
                continue;
            }
            self.value_providers
                .entry(id)
                .or_default()
                .entry(slot_id)
                .or_default()
                .extend(handler_ids);
        }
    }

    fn visit_spread(
        &mut self,
        program: &Program,
        spread: &RecordSpread<ExprId>,
        active_handlers: &mut Vec<u32>,
    ) {
        match spread {
            RecordSpread::None => {}
            RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                self.visit_expr(program, *expr, active_handlers);
            }
        }
    }

    fn visit_block(&mut self, program: &Program, block: &Block, active_handlers: &mut Vec<u32>) {
        for stmt in &block.stmts {
            self.visit_stmt(program, stmt, active_handlers);
        }
        if let Some(tail) = block.tail {
            self.visit_expr(program, tail, active_handlers);
        }
    }

    fn visit_stmt(&mut self, program: &Program, stmt: &Stmt, active_handlers: &mut Vec<u32>) {
        match stmt {
            Stmt::Let(_, _, expr) | Stmt::Expr(expr) => {
                self.visit_expr(program, *expr, active_handlers);
            }
            Stmt::Module(_, stmts) => {
                for stmt in stmts {
                    self.visit_stmt(program, stmt, active_handlers);
                }
            }
        }
    }
}

fn build_call_objects(
    functions: &[EvidenceVmFunctionPlan],
    slot_ids: &BTreeMap<EvidenceVmSlotKey, u32>,
) -> Vec<EvidenceVmCallObjectPlan> {
    functions
        .iter()
        .flat_map(|function| function.calls_needing_evidence.iter())
        .map(|call| EvidenceVmCallObjectPlan {
            apply: call.apply,
            callee_instance: call.callee_instance,
            required_slots: slot_ids_for_keys(&call.required_evidence_slots, slot_ids),
        })
        .collect()
}

fn slot_ids_for_keys(
    keys: &[EvidenceVmSlotKey],
    slot_ids: &BTreeMap<EvidenceVmSlotKey, u32>,
) -> Vec<u32> {
    keys.iter()
        .filter_map(|key| slot_ids.get(key).copied())
        .collect()
}

fn build_handler_objects(
    handlers: &[EvidenceVmHandlerPlan],
    slot_ids: &BTreeMap<EvidenceVmSlotKey, u32>,
) -> Vec<EvidenceVmHandlerObjectPlan> {
    let mut objects = Vec::new();
    for handler in handlers {
        for arm in &handler.arms {
            let Some(path) = &arm.path else {
                continue;
            };
            let slot = positive_slot(path.clone());
            let Some(slot_id) = slot_ids.get(&slot).copied() else {
                continue;
            };
            objects.push(EvidenceVmHandlerObjectPlan {
                id: objects.len() as u32,
                capability_id: EvidenceVmHandlerCapId(objects.len() as u32),
                handler: handler.expr,
                slot_id,
                path: path.clone(),
                arm_body: arm.body,
                arm_class: arm.classification,
                continuation_use: arm.continuation_use,
                definition_env: Vec::new(),
            });
        }
    }
    objects
}

fn build_handler_capabilities(
    handlers: &[EvidenceVmHandlerObjectPlan],
) -> Vec<EvidenceVmHandlerCapabilityPlan> {
    handlers
        .iter()
        .map(|handler| EvidenceVmHandlerCapabilityPlan {
            id: handler.capability_id,
            handler_id: handler.id,
            slot_id: handler.slot_id,
            family: handler.path.clone(),
        })
        .collect()
}

fn attach_handler_definition_envs(
    definition_envs: &HashMap<u32, Vec<u32>>,
    handlers: &mut [EvidenceVmHandlerObjectPlan],
) {
    for handler in handlers {
        handler.definition_env = definition_envs
            .get(&handler.id)
            .cloned()
            .unwrap_or_default();
    }
}

fn build_operation_objects(
    operations: &[EvidenceVmOperationPlan],
    slot_ids: &BTreeMap<EvidenceVmSlotKey, u32>,
    handler_index: &HashMap<(ExprId, u32), u32>,
    handlers: &[EvidenceVmHandlerObjectPlan],
) -> (
    Vec<EvidenceVmOperationObjectPlan>,
    Vec<EvidenceVmAllowedSetPlan>,
) {
    let handler_by_id = handlers
        .iter()
        .map(|handler| (handler.id, handler))
        .collect::<HashMap<_, _>>();
    let mut allowed_sets = EvidenceVmAllowedSetInterner::new();
    let objects = operations
        .iter()
        .filter_map(|operation| {
            let slot_id = slot_ids.get(&operation.slot).copied()?;
            let candidate_handler = operation_candidate_handler(operation).and_then(|handler| {
                let positive_slot_id = slot_ids
                    .get(&positive_slot(operation.path.clone()))
                    .copied()?;
                handler_index.get(&(handler, positive_slot_id)).copied()
            });
            let execution = operation_execution_plan(operation, candidate_handler, &handler_by_id);
            let visibility =
                operation_visibility_plan(candidate_handler, &handler_by_id, &mut allowed_sets);
            let static_route =
                operation_static_route_resolution(operation, candidate_handler, &handler_by_id);
            Some(EvidenceVmOperationObjectPlan {
                expr: operation.expr,
                slot_id,
                candidate_handler,
                execution,
                visibility,
                static_route,
            })
        })
        .collect::<Vec<_>>();
    (objects, allowed_sets.finish())
}

fn operation_static_route_resolution(
    operation: &EvidenceVmOperationPlan,
    candidate_handler: Option<u32>,
    handler_by_id: &HashMap<u32, &EvidenceVmHandlerObjectPlan>,
) -> EvidenceVmStaticRouteResolution {
    match operation.lowering {
        EvidenceVmOperationLowering::DirectHandlerCall { .. } => candidate_handler
            .and_then(|handler_id| handler_by_id.get(&handler_id))
            .map(|handler| EvidenceVmStaticRouteResolution::StaticHandler {
                arm_class: handler.arm_class,
            })
            .unwrap_or(EvidenceVmStaticRouteResolution::Dynamic(
                EvidenceVmStaticRouteDynamicReason::Unclassified,
            )),
        EvidenceVmOperationLowering::LexicalHandlerCandidate {
            delayed_boundary: true,
            ..
        } => EvidenceVmStaticRouteResolution::Dynamic(
            EvidenceVmStaticRouteDynamicReason::DelayedBoundary,
        ),
        EvidenceVmOperationLowering::LexicalHandlerCandidate {
            delayed_boundary: false,
            ..
        } => EvidenceVmStaticRouteResolution::Dynamic(
            EvidenceVmStaticRouteDynamicReason::ProviderEnvDependent,
        ),
        EvidenceVmOperationLowering::HygieneFallback { .. } => {
            EvidenceVmStaticRouteResolution::Dynamic(
                EvidenceVmStaticRouteDynamicReason::HygieneBarrier,
            )
        }
        EvidenceVmOperationLowering::GenericFallback => {
            let matching_handlers = matching_handler_count(handler_by_id, &operation.path);
            let reason = if runtime::runtime_host_manifest_has_known_act(&operation.path) {
                EvidenceVmStaticRouteDynamicReason::HostEscape
            } else if matching_handlers > 1 {
                EvidenceVmStaticRouteDynamicReason::MultipleCandidates
            } else if matching_handlers == 1 {
                EvidenceVmStaticRouteDynamicReason::ProviderEnvDependent
            } else {
                EvidenceVmStaticRouteDynamicReason::Unclassified
            };
            EvidenceVmStaticRouteResolution::Dynamic(reason)
        }
    }
}

fn matching_handler_count(
    handler_by_id: &HashMap<u32, &EvidenceVmHandlerObjectPlan>,
    operation_path: &[String],
) -> usize {
    handler_by_id
        .values()
        .filter(|handler| handler.path == operation_path)
        .count()
}

#[derive(Default)]
struct EvidenceVmAllowedSetInterner {
    ids: BTreeMap<EvidenceVmAllowedSetKind, EvidenceVmAllowedSetId>,
    plans: Vec<EvidenceVmAllowedSetPlan>,
}

impl EvidenceVmAllowedSetInterner {
    fn new() -> Self {
        Self::default()
    }

    fn intern(&mut self, kind: EvidenceVmAllowedSetKind) -> EvidenceVmAllowedSetId {
        if let Some(id) = self.ids.get(&kind) {
            return *id;
        }
        let id = EvidenceVmAllowedSetId(self.plans.len() as u32);
        self.ids.insert(kind, id);
        self.plans.push(EvidenceVmAllowedSetPlan { id, kind });
        id
    }

    fn finish(self) -> Vec<EvidenceVmAllowedSetPlan> {
        self.plans
    }
}

fn operation_visibility_plan(
    candidate_handler: Option<u32>,
    handler_by_id: &HashMap<u32, &EvidenceVmHandlerObjectPlan>,
    allowed_sets: &mut EvidenceVmAllowedSetInterner,
) -> EvidenceVmOperationVisibilityPlan {
    let kind = candidate_handler
        .and_then(|handler_id| handler_by_id.get(&handler_id))
        .map(|handler| EvidenceVmAllowedSetKind::HandlerCapability(handler.capability_id))
        .unwrap_or(EvidenceVmAllowedSetKind::LegacyGuardBridge);
    EvidenceVmOperationVisibilityPlan {
        allowed_set_id: allowed_sets.intern(kind),
        legacy_guard_bridge: matches!(kind, EvidenceVmAllowedSetKind::LegacyGuardBridge),
    }
}

fn build_provider_index(
    slots: &[EvidenceVmSlotPlan],
    handlers: &[EvidenceVmHandlerObjectPlan],
) -> Vec<EvidenceVmProviderPlan> {
    slots
        .iter()
        .filter_map(|slot| {
            let handler_candidates = handlers
                .iter()
                .filter(|handler| handler.path == slot.key.family)
                .map(|handler| handler.id)
                .collect::<Vec<_>>();
            if handler_candidates.is_empty() {
                return None;
            }
            Some(EvidenceVmProviderPlan {
                slot_id: slot.id,
                route: provider_route_for_slot(slot.key.route),
                handler_candidates,
            })
        })
        .collect()
}

fn provider_route_for_slot(route: EvidenceVmSlotRouteKey) -> EvidenceVmProviderRoute {
    match route {
        EvidenceVmSlotRouteKey::Positive => EvidenceVmProviderRoute::DirectPositive,
        EvidenceVmSlotRouteKey::Blocked => EvidenceVmProviderRoute::BlockedByHygiene,
        EvidenceVmSlotRouteKey::UnknownFallback => EvidenceVmProviderRoute::NeedsEvidenceEnv,
    }
}

fn operation_candidate_handler(operation: &EvidenceVmOperationPlan) -> Option<ExprId> {
    match operation.lowering {
        EvidenceVmOperationLowering::DirectHandlerCall { handler, .. } => Some(handler),
        EvidenceVmOperationLowering::LexicalHandlerCandidate {
            handler,
            delayed_boundary: false,
            ..
        } => Some(handler),
        EvidenceVmOperationLowering::LexicalHandlerCandidate {
            delayed_boundary: true,
            ..
        }
        | EvidenceVmOperationLowering::HygieneFallback { .. }
        | EvidenceVmOperationLowering::GenericFallback => None,
    }
}

fn operation_execution_plan(
    operation: &EvidenceVmOperationPlan,
    candidate_handler: Option<u32>,
    handler_by_id: &HashMap<u32, &EvidenceVmHandlerObjectPlan>,
) -> EvidenceVmOperationExecutionPlan {
    match operation.lowering {
        EvidenceVmOperationLowering::HygieneFallback { .. } => {
            return EvidenceVmOperationExecutionPlan::BlockedFallback;
        }
        EvidenceVmOperationLowering::GenericFallback => {
            return EvidenceVmOperationExecutionPlan::GenericFallback;
        }
        EvidenceVmOperationLowering::LexicalHandlerCandidate {
            delayed_boundary: true,
            ..
        } => return EvidenceVmOperationExecutionPlan::YieldFallback,
        EvidenceVmOperationLowering::DirectHandlerCall { .. }
        | EvidenceVmOperationLowering::LexicalHandlerCandidate {
            delayed_boundary: false,
            ..
        } => {}
    }
    let Some(handler) = candidate_handler.and_then(|id| handler_by_id.get(&id)) else {
        return EvidenceVmOperationExecutionPlan::GenericFallback;
    };
    match handler.arm_class {
        EvidenceVmHandlerArmClass::Abortive => EvidenceVmOperationExecutionPlan::DirectAbortive,
        EvidenceVmHandlerArmClass::TailResumptive => {
            EvidenceVmOperationExecutionPlan::DirectTailResumptive
        }
        EvidenceVmHandlerArmClass::MayEscapeYield => {
            EvidenceVmOperationExecutionPlan::DirectTailResumptive
        }
        EvidenceVmHandlerArmClass::OneShotYield
        | EvidenceVmHandlerArmClass::MultiShotYield
        | EvidenceVmHandlerArmClass::Fallback
        | EvidenceVmHandlerArmClass::Value => EvidenceVmOperationExecutionPlan::YieldFallback,
    }
}

fn operation_kind(kind: ControlEffectUseKind) -> EvidenceVmOperationKind {
    match kind {
        ControlEffectUseKind::OperationValue => EvidenceVmOperationKind::Value,
        ControlEffectUseKind::OperationCall { apply, callee } => {
            EvidenceVmOperationKind::Call { apply, callee }
        }
    }
}

fn operation_lowering(
    expr: ExprId,
    route: &ControlEvidenceRoute,
    handler_exprs: &HashSet<ExprId>,
    lexical_handlers: &LexicalHandlerIndex,
) -> EvidenceVmOperationLowering {
    match route {
        ControlEvidenceRoute::Direct {
            handler,
            resumptive,
        } => EvidenceVmOperationLowering::DirectHandlerCall {
            handler: *handler,
            resumptive: *resumptive,
            handler_known: handler_exprs.contains(handler),
        },
        ControlEvidenceRoute::Blocked {
            handler,
            resumptive,
            callback_boundary,
            delayed_boundary,
        } => EvidenceVmOperationLowering::HygieneFallback {
            handler: *handler,
            resumptive: *resumptive,
            callback_boundary: *callback_boundary,
            delayed_boundary: *delayed_boundary,
        },
        ControlEvidenceRoute::Unhandled => lexical_handlers
            .candidate_for(expr)
            .map(
                |candidate| EvidenceVmOperationLowering::LexicalHandlerCandidate {
                    handler: candidate.handler,
                    resumptive: candidate.resumptive,
                    delayed_boundary: candidate.delayed_boundary,
                },
            )
            .unwrap_or(EvidenceVmOperationLowering::GenericFallback),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct HandlerArmAnalysis {
    classification: EvidenceVmHandlerArmClass,
    continuation_use: EvidenceVmContinuationUsePlan,
}

impl HandlerArmAnalysis {
    fn new(classification: EvidenceVmHandlerArmClass) -> Self {
        Self {
            classification,
            continuation_use: EvidenceVmContinuationUsePlan::default(),
        }
    }
}

fn analyze_handler_arm(
    program: &Program,
    handler_expr: ExprId,
    arm_index: usize,
    arm: &control_vm::ControlHandlerArmEvidence,
) -> HandlerArmAnalysis {
    if arm.operation_path.is_none() {
        return HandlerArmAnalysis::new(EvidenceVmHandlerArmClass::Value);
    }
    if !arm.resumptive {
        return HandlerArmAnalysis::new(EvidenceVmHandlerArmClass::Abortive);
    }
    if arm.guarded {
        return HandlerArmAnalysis::new(EvidenceVmHandlerArmClass::Fallback);
    }
    let Some(continuation_pat) = source_handler_arm(program, handler_expr, arm_index)
        .and_then(|source_arm| source_arm.continuation.as_ref())
    else {
        return HandlerArmAnalysis::new(EvidenceVmHandlerArmClass::MayEscapeYield);
    };
    let Some(continuation) = continuation_def(continuation_pat) else {
        return if matches!(continuation_pat, control_vm::Pat::Wild) {
            HandlerArmAnalysis::new(EvidenceVmHandlerArmClass::Abortive)
        } else {
            HandlerArmAnalysis::new(EvidenceVmHandlerArmClass::MayEscapeYield)
        };
    };
    if !expr_contains_local(program, arm.body, continuation) {
        return HandlerArmAnalysis::new(EvidenceVmHandlerArmClass::Abortive);
    }
    let continuation_use = handler_arm_continuation_use(program, arm.body, continuation);
    let classification = if continuation_use.tail_arg.is_some() {
        EvidenceVmHandlerArmClass::TailResumptive
    } else {
        if continuation_use.escapes {
            EvidenceVmHandlerArmClass::MayEscapeYield
        } else if continuation_use.direct_calls <= 1 {
            EvidenceVmHandlerArmClass::OneShotYield
        } else {
            EvidenceVmHandlerArmClass::MultiShotYield
        }
    };
    HandlerArmAnalysis {
        classification,
        continuation_use,
    }
}

fn source_handler_arm(
    program: &Program,
    handler_expr: ExprId,
    arm_index: usize,
) -> Option<&control_vm::CatchArm> {
    let Expr::Catch { arms, .. } = control_expr(program, handler_expr)? else {
        return None;
    };
    arms.get(arm_index)
}

fn continuation_def(pat: &control_vm::Pat) -> Option<DefId> {
    match pat {
        control_vm::Pat::Var(def) | control_vm::Pat::As(_, def) => Some(*def),
        _ => None,
    }
}

fn handler_arm_continuation_use(
    program: &Program,
    body: ExprId,
    continuation: DefId,
) -> EvidenceVmContinuationUsePlan {
    let summary = summarize_continuation_uses(program, body, continuation);
    let tail_arg = tail_resume_arg(program, body, continuation)
        .filter(|arg| !expr_contains_local(program, *arg, continuation));
    EvidenceVmContinuationUsePlan {
        direct_calls: summary.direct_calls,
        delayed_calls: summary.delayed_calls,
        escapes: summary.escapes,
        tail_arg,
    }
}

fn tail_resume_arg(program: &Program, expr: ExprId, continuation: DefId) -> Option<ExprId> {
    match control_expr(program, expr)? {
        Expr::Apply { callee, arg } if expr_is_local(program, *callee, continuation) => Some(*arg),
        Expr::Coerce { expr, .. }
        | Expr::MarkerFrame { body: expr, .. }
        | Expr::Select { base: expr, .. } => tail_resume_arg(program, *expr, continuation),
        Expr::Block(block) => {
            if block
                .stmts
                .iter()
                .any(|stmt| stmt_contains_local(program, stmt, continuation))
            {
                return None;
            }
            tail_resume_arg(program, block.tail?, continuation)
        }
        _ => None,
    }
}

#[derive(Debug, Default)]
struct ContinuationUseSummary {
    direct_calls: usize,
    delayed_calls: usize,
    escapes: bool,
}

impl ContinuationUseSummary {
    fn add(&mut self, other: ContinuationUseSummary) {
        self.direct_calls += other.direct_calls;
        self.delayed_calls += other.delayed_calls;
        self.escapes |= other.escapes;
    }

    fn delay(mut self) -> Self {
        self.delayed_calls += self.direct_calls;
        self.direct_calls = 0;
        self
    }
}

fn summarize_continuation_uses(
    program: &Program,
    expr: ExprId,
    continuation: DefId,
) -> ContinuationUseSummary {
    let mut visited = HashSet::new();
    summarize_continuation_uses_inner(program, expr, continuation, &mut visited)
}

fn summarize_continuation_uses_inner(
    program: &Program,
    expr: ExprId,
    continuation: DefId,
    visited: &mut HashSet<ExprId>,
) -> ContinuationUseSummary {
    if !visited.insert(expr) {
        return ContinuationUseSummary::default();
    }
    let Some(node) = control_expr(program, expr) else {
        return ContinuationUseSummary::default();
    };
    match node {
        Expr::Local(local) => ContinuationUseSummary {
            direct_calls: 0,
            delayed_calls: 0,
            escapes: *local == continuation,
        },
        Expr::Apply { callee, arg } if expr_is_local(program, *callee, continuation) => {
            let mut summary =
                summarize_continuation_uses_inner(program, *arg, continuation, visited);
            summary.direct_calls += 1;
            summary
        }
        Expr::Coerce { expr, .. }
        | Expr::ForceThunk { thunk: expr, .. }
        | Expr::MarkerFrame { body: expr, .. }
        | Expr::Select { base: expr, .. } => {
            summarize_continuation_uses_inner(program, *expr, continuation, visited)
        }
        Expr::MakeThunk { body: expr, .. } => {
            let mut summary =
                summarize_continuation_uses_inner(program, *expr, continuation, visited).delay();
            summary.escapes |= expr_contains_local(program, *expr, continuation);
            summary
        }
        Expr::FunctionAdapter { function: expr, .. } | Expr::Lambda { body: expr, .. } => {
            let contains = expr_contains_local(program, *expr, continuation);
            ContinuationUseSummary {
                direct_calls: 0,
                delayed_calls: 0,
                escapes: contains,
            }
        }
        Expr::Apply { callee, arg }
        | Expr::RefSet {
            reference: callee,
            value: arg,
        } => {
            let mut summary =
                summarize_continuation_uses_inner(program, *callee, continuation, visited);
            summary.add(summarize_continuation_uses_inner(
                program,
                *arg,
                continuation,
                visited,
            ));
            summary
        }
        Expr::Tuple(items) => {
            summarize_expr_list_continuation_uses(program, items, continuation, visited)
        }
        Expr::Record { fields, spread } => {
            let mut summary =
                fields
                    .iter()
                    .fold(ContinuationUseSummary::default(), |mut summary, field| {
                        summary.add(summarize_continuation_uses_inner(
                            program,
                            field.value,
                            continuation,
                            visited,
                        ));
                        summary
                    });
            summary.add(summarize_spread_continuation_uses(
                program,
                spread,
                continuation,
                visited,
            ));
            summary
        }
        Expr::PolyVariant { payloads, .. } => {
            summarize_expr_list_continuation_uses(program, payloads, continuation, visited)
        }
        Expr::Case { scrutinee, arms } => {
            let mut summary =
                summarize_continuation_uses_inner(program, *scrutinee, continuation, visited);
            for arm in arms {
                if let Some(guard) = arm.guard {
                    summary.add(summarize_continuation_uses_inner(
                        program,
                        guard,
                        continuation,
                        visited,
                    ));
                }
                summary.add(summarize_continuation_uses_inner(
                    program,
                    arm.body,
                    continuation,
                    visited,
                ));
            }
            summary
        }
        Expr::Catch { body, arms } => {
            let mut summary =
                summarize_continuation_uses_inner(program, *body, continuation, visited);
            for arm in arms {
                if let Some(guard) = arm.guard {
                    summary.add(summarize_continuation_uses_inner(
                        program,
                        guard,
                        continuation,
                        visited,
                    ));
                }
                summary.add(summarize_continuation_uses_inner(
                    program,
                    arm.body,
                    continuation,
                    visited,
                ));
            }
            summary
        }
        Expr::Block(block) => {
            let mut summary = ContinuationUseSummary::default();
            for stmt in &block.stmts {
                summary.add(summarize_stmt_continuation_uses(
                    program,
                    stmt,
                    continuation,
                    visited,
                ));
            }
            if let Some(tail) = block.tail {
                summary.add(summarize_continuation_uses_inner(
                    program,
                    tail,
                    continuation,
                    visited,
                ));
            }
            summary
        }
        Expr::Lit(_)
        | Expr::PrimitiveOp { .. }
        | Expr::Constructor { .. }
        | Expr::EffectOp { .. }
        | Expr::InstanceRef(_) => ContinuationUseSummary::default(),
    }
}

fn summarize_expr_list_continuation_uses(
    program: &Program,
    exprs: &[ExprId],
    continuation: DefId,
    visited: &mut HashSet<ExprId>,
) -> ContinuationUseSummary {
    exprs
        .iter()
        .fold(ContinuationUseSummary::default(), |mut summary, expr| {
            summary.add(summarize_continuation_uses_inner(
                program,
                *expr,
                continuation,
                visited,
            ));
            summary
        })
}

fn summarize_spread_continuation_uses(
    program: &Program,
    spread: &RecordSpread<ExprId>,
    continuation: DefId,
    visited: &mut HashSet<ExprId>,
) -> ContinuationUseSummary {
    match spread {
        RecordSpread::None => ContinuationUseSummary::default(),
        RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
            summarize_continuation_uses_inner(program, *expr, continuation, visited)
        }
    }
}

fn summarize_stmt_continuation_uses(
    program: &Program,
    stmt: &Stmt,
    continuation: DefId,
    visited: &mut HashSet<ExprId>,
) -> ContinuationUseSummary {
    match stmt {
        Stmt::Let(_, _, expr) | Stmt::Expr(expr) => {
            summarize_continuation_uses_inner(program, *expr, continuation, visited)
        }
        Stmt::Module(_, stmts) => {
            stmts
                .iter()
                .fold(ContinuationUseSummary::default(), |mut summary, stmt| {
                    summary.add(summarize_stmt_continuation_uses(
                        program,
                        stmt,
                        continuation,
                        visited,
                    ));
                    summary
                })
        }
    }
}

fn expr_is_local(program: &Program, expr: ExprId, def: DefId) -> bool {
    matches!(control_expr(program, expr), Some(Expr::Local(local)) if *local == def)
}

fn expr_contains_local(program: &Program, expr: ExprId, def: DefId) -> bool {
    let mut visited = HashSet::new();
    expr_contains_local_inner(program, expr, def, &mut visited)
}

fn expr_contains_local_inner(
    program: &Program,
    expr: ExprId,
    def: DefId,
    visited: &mut HashSet<ExprId>,
) -> bool {
    if !visited.insert(expr) {
        return false;
    }
    let Some(node) = control_expr(program, expr) else {
        return false;
    };
    match node {
        Expr::Local(local) => *local == def,
        Expr::Coerce { expr, .. }
        | Expr::ForceThunk { thunk: expr, .. }
        | Expr::FunctionAdapter { function: expr, .. }
        | Expr::MarkerFrame { body: expr, .. }
        | Expr::MakeThunk { body: expr, .. }
        | Expr::Lambda { body: expr, .. }
        | Expr::Select { base: expr, .. } => {
            expr_contains_local_inner(program, *expr, def, visited)
        }
        Expr::Apply { callee, arg }
        | Expr::RefSet {
            reference: callee,
            value: arg,
        } => {
            expr_contains_local_inner(program, *callee, def, visited)
                || expr_contains_local_inner(program, *arg, def, visited)
        }
        Expr::Tuple(items) => items
            .iter()
            .any(|item| expr_contains_local_inner(program, *item, def, visited)),
        Expr::Record { fields, spread } => {
            fields
                .iter()
                .any(|field| expr_contains_local_inner(program, field.value, def, visited))
                || spread_contains_local(program, spread, def, visited)
        }
        Expr::PolyVariant { payloads, .. } => payloads
            .iter()
            .any(|payload| expr_contains_local_inner(program, *payload, def, visited)),
        Expr::Case { scrutinee, arms } => {
            expr_contains_local_inner(program, *scrutinee, def, visited)
                || arms.iter().any(|arm| {
                    arm.guard.is_some_and(|guard| {
                        expr_contains_local_inner(program, guard, def, visited)
                    }) || expr_contains_local_inner(program, arm.body, def, visited)
                })
        }
        Expr::Catch { body, arms } => {
            expr_contains_local_inner(program, *body, def, visited)
                || arms.iter().any(|arm| {
                    arm.guard.is_some_and(|guard| {
                        expr_contains_local_inner(program, guard, def, visited)
                    }) || expr_contains_local_inner(program, arm.body, def, visited)
                })
        }
        Expr::Block(block) => {
            block
                .stmts
                .iter()
                .any(|stmt| stmt_contains_local(program, stmt, def))
                || block
                    .tail
                    .is_some_and(|tail| expr_contains_local_inner(program, tail, def, visited))
        }
        Expr::Lit(_)
        | Expr::PrimitiveOp { .. }
        | Expr::Constructor { .. }
        | Expr::EffectOp { .. }
        | Expr::InstanceRef(_) => false,
    }
}

fn spread_contains_local(
    program: &Program,
    spread: &RecordSpread<ExprId>,
    def: DefId,
    visited: &mut HashSet<ExprId>,
) -> bool {
    match spread {
        RecordSpread::None => false,
        RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
            expr_contains_local_inner(program, *expr, def, visited)
        }
    }
}

fn stmt_contains_local(program: &Program, stmt: &Stmt, def: DefId) -> bool {
    match stmt {
        Stmt::Let(_, _, expr) | Stmt::Expr(expr) => expr_contains_local(program, *expr, def),
        Stmt::Module(_, stmts) => stmts
            .iter()
            .any(|stmt| stmt_contains_local(program, stmt, def)),
    }
}

fn generic_fallback_exprs(
    control: &ControlEvidenceProgram,
    exprs: impl Iterator<Item = u32>,
) -> Vec<u32> {
    let exprs = exprs.collect::<BTreeSet<_>>();
    control
        .fallbacks
        .iter()
        .filter_map(|fallback| exprs.contains(&fallback.expr.0).then_some(fallback.expr.0))
        .collect()
}

fn format_handlers(out: &mut String, handlers: &[EvidenceVmHandlerPlan]) {
    if handlers.is_empty() {
        return;
    }
    writeln!(out, "handlers:").unwrap();
    for handler in handlers {
        writeln!(
            out,
            "  e{} handler body e{} arms {}",
            handler.expr.0,
            handler.body.0,
            handler.arms.len()
        )
        .unwrap();
        for arm in &handler.arms {
            let path = arm
                .path
                .as_deref()
                .map(format_path)
                .unwrap_or_else(|| "value".to_string());
            let mode = if arm.resumptive {
                "resumptive"
            } else {
                "abortive"
            };
            let guarded = if arm.guarded { " guarded" } else { "" };
            writeln!(
                out,
                "    {path} {mode}{guarded} class {} body e{} {}",
                format_handler_arm_class(arm.classification),
                arm.body.0,
                format_continuation_use(arm.continuation_use)
            )
            .unwrap();
        }
    }
}

fn format_operations(out: &mut String, operations: &[EvidenceVmOperationPlan]) {
    if operations.is_empty() {
        return;
    }
    writeln!(out, "operations:").unwrap();
    for operation in operations {
        let def = operation
            .operation_def
            .map(|def| format!(" d{}", def.0))
            .unwrap_or_default();
        writeln!(
            out,
            "  e{}{} {} {} slot {} {} runtime_nodes [{}] evidence_refs {}",
            operation.expr.0,
            def,
            format_operation_kind(operation.kind),
            format_path(&operation.path),
            format_slot_key(&operation.slot),
            format_operation_lowering(&operation.lowering),
            operation
                .runtime_nodes
                .iter()
                .map(u32::to_string)
                .collect::<Vec<_>>()
                .join(", "),
            operation.runtime_evidence_refs
        )
        .unwrap();
    }
}

fn format_functions(out: &mut String, functions: &[EvidenceVmFunctionPlan]) {
    if functions.is_empty() {
        return;
    }
    writeln!(out, "functions:").unwrap();
    for function in functions {
        writeln!(
            out,
            "  {} nodes {} evidence_refs {} signature params [{}] provides [{}] value_env [{}] requires [{}] evidence_calls [{}] operations [{}] handlers [{}] fallbacks [{}]",
            format_task_owner(function.owner),
            function.node_count,
            function.evidence_ref_count,
            format_slot_keys(&function.signature.params),
            format_slot_keys(&function.signature.provides),
            format_slot_keys(&function.signature.value_env),
            format_requirements(&function.required_evidence),
            format_call_plans(&function.calls_needing_evidence),
            format_u32_list(&function.operation_exprs),
            format_u32_list(&function.handler_exprs),
            format_u32_list(&function.fallback_exprs)
        )
        .unwrap();
    }
}

fn format_value_envs(out: &mut String, values: &[EvidenceVmValueEnvPlan]) {
    if values.is_empty() {
        return;
    }
    writeln!(out, "values:").unwrap();
    for value in values {
        writeln!(
            out,
            "  e{} {} signature captures [{}] captures [{}]",
            value.expr.0,
            format_value_env_kind(&value.kind),
            format_slot_keys(&value.signature.captures),
            format_requirements(&value.captured_evidence)
        )
        .unwrap();
    }
}

fn format_object_plan(out: &mut String, objects: &EvidenceVmObjectPlan) {
    if objects.slots.is_empty()
        && objects.functions.is_empty()
        && objects.values.is_empty()
        && objects.calls.is_empty()
        && objects.handlers.is_empty()
        && objects.operations.is_empty()
        && objects.known_handlers.is_empty()
        && objects.known_operations.is_empty()
        && objects.handler_capabilities.is_empty()
        && objects.allowed_sets.is_empty()
        && objects.providers.is_empty()
    {
        return;
    }
    writeln!(out, "evidence object graph:").unwrap();
    if !objects.slots.is_empty() {
        writeln!(out, "  slots:").unwrap();
        for slot in &objects.slots {
            writeln!(out, "    s{} {}", slot.id, format_slot_key(&slot.key)).unwrap();
        }
    }
    if !objects.functions.is_empty() {
        writeln!(out, "  function-objects:").unwrap();
        for function in &objects.functions {
            writeln!(
                out,
                "    f{} {} params [{}] provides [{}] value_env [{}]",
                function.id,
                format_task_owner(function.owner),
                format_u32_list_with_prefix("s", &function.params),
                format_u32_list_with_prefix("s", &function.provides),
                format_u32_list_with_prefix("s", &function.value_env)
            )
            .unwrap();
        }
    }
    if !objects.values.is_empty() {
        writeln!(out, "  value-objects:").unwrap();
        for value in &objects.values {
            writeln!(
                out,
                "    v{} e{} {} captures [{}] env_providers [{}]",
                value.id,
                value.expr.0,
                format_value_env_kind(&value.kind),
                format_u32_list_with_prefix("s", &value.captures),
                format_env_providers(&value.env_providers)
            )
            .unwrap();
        }
    }
    if !objects.calls.is_empty() {
        writeln!(out, "  call-objects:").unwrap();
        for call in &objects.calls {
            writeln!(
                out,
                "    e{} -> i{} evidence [{}]",
                call.apply.0,
                call.callee_instance,
                format_u32_list_with_prefix("s", &call.required_slots)
            )
            .unwrap();
        }
    }
    if !objects.handlers.is_empty() {
        writeln!(out, "  handler-objects:").unwrap();
        for handler in &objects.handlers {
            writeln!(
                out,
                "    h{} cap c{} handler e{} slot s{} {} arm e{} class {} {} def_env [{}]",
                handler.id,
                handler.capability_id.0,
                handler.handler.0,
                handler.slot_id,
                format_path(&handler.path),
                handler.arm_body.0,
                format_handler_arm_class(handler.arm_class),
                format_continuation_use(handler.continuation_use),
                format_u32_list_with_prefix("h", &handler.definition_env)
            )
            .unwrap();
        }
    }
    if !objects.handler_capabilities.is_empty() {
        writeln!(out, "  handler-capabilities:").unwrap();
        for capability in &objects.handler_capabilities {
            writeln!(
                out,
                "    c{} handler h{} slot s{} {}",
                capability.id.0,
                capability.handler_id,
                capability.slot_id,
                format_path(&capability.family)
            )
            .unwrap();
        }
    }
    if !objects.known_handlers.is_empty() {
        writeln!(out, "  known-handlers:").unwrap();
        for known in &objects.known_handlers {
            writeln!(out, "    {}", format_known_handler_plan(known)).unwrap();
        }
    }
    if !objects.known_operations.is_empty() {
        writeln!(out, "  known-operation-calls:").unwrap();
        for operation in &objects.known_operations {
            let reject = operation
                .reject
                .map(format_known_operation_reject)
                .unwrap_or("-");
            let proof = operation
                .route_proof
                .map(|id| format!("p{}", id.0))
                .unwrap_or_else(|| "-".to_string());
            writeln!(
                out,
                "    e{} apply e{} callee e{} k{} {} handler h{} visibility a{} proof {} direct_ready={} reject {}",
                operation.expr.0,
                operation.apply.0,
                operation.callee.0,
                operation.known_handler.0,
                format_known_operation_role(operation.role),
                operation.handler_id,
                operation.visibility.0,
                proof,
                operation.direct_ready,
                reject
            )
            .unwrap();
        }
    }
    if !objects.known_state_operation_route_proofs.is_empty() {
        writeln!(out, "  known-state-operation-route-proofs:").unwrap();
        for proof in &objects.known_state_operation_route_proofs {
            writeln!(
                out,
                "    {}",
                format_known_state_operation_route_proof(proof)
            )
            .unwrap();
        }
    }
    if !objects.allowed_sets.is_empty() {
        writeln!(out, "  allowed-sets:").unwrap();
        for allowed in &objects.allowed_sets {
            writeln!(
                out,
                "    a{} {}",
                allowed.id.0,
                format_allowed_set_kind(allowed.kind)
            )
            .unwrap();
        }
    }
    if !objects.providers.is_empty() {
        writeln!(out, "  provider-index:").unwrap();
        for provider in &objects.providers {
            writeln!(
                out,
                "    s{} {} candidates [{}]",
                provider.slot_id,
                format_provider_route(provider.route),
                format_u32_list_with_prefix("h", &provider.handler_candidates)
            )
            .unwrap();
        }
    }
    if !objects.operations.is_empty() {
        writeln!(out, "  operation-objects:").unwrap();
        for operation in &objects.operations {
            let handler = operation
                .candidate_handler
                .map(|id| format!("h{id}"))
                .unwrap_or_else(|| "none".to_string());
            writeln!(
                out,
                "    e{} slot s{} handler {} exec {} visibility a{} legacy_bridge={}",
                operation.expr.0,
                operation.slot_id,
                handler,
                format_operation_execution_plan(operation.execution),
                operation.visibility.allowed_set_id.0,
                operation.visibility.legacy_guard_bridge
            )
            .unwrap();
        }
    }
}

fn format_known_handler_plan(plan: &EvidenceVmKnownHandlerPlan) -> String {
    match plan {
        EvidenceVmKnownHandlerPlan::State(state) => format!(
            "k{} state sv{} handler e{} state d{} family {} get h{} set h{} source {} continuation {}",
            state.id.0,
            state.synthetic_var,
            state.handler.0,
            state.state.0,
            format_path(&state.family),
            state.get_handler_id,
            state.set_handler_id,
            format_known_state_handler_source(state.source),
            format_known_state_continuation(state.continuation)
        ),
    }
}

fn format_known_state_operation_route_proof(
    proof: &EvidenceVmKnownStateOperationRouteProof,
) -> String {
    format!(
        "p{} e{} apply e{} callee e{} def d{} sv{} k{} catch e{} handler h{} {} source {} visibility {} payload {}",
        proof.id.0,
        proof.operation_expr.0,
        proof.apply.0,
        proof.callee.0,
        proof.access_operation_def,
        proof.synthetic_var,
        proof.plan_id.0,
        proof.catch_expr.0,
        proof.handler_id,
        format_known_operation_role(proof.role),
        format_known_state_route_proof_source(proof.source),
        format_known_state_visibility_proof(proof.visibility),
        format_known_state_payload_proof(proof.payload)
    )
}

fn format_known_state_route_proof_source(
    source: EvidenceVmKnownStateOperationRouteProofSource,
) -> String {
    match source {
        EvidenceVmKnownStateOperationRouteProofSource::CompilerLocalVar { synthetic_var } => {
            format!("compiler-local-var sv{synthetic_var}")
        }
    }
}

fn format_known_state_visibility_proof(
    visibility: EvidenceVmKnownStateOperationVisibilityProof,
) -> String {
    match visibility {
        EvidenceVmKnownStateOperationVisibilityProof::CleanKnownStateCatch {
            catch_expr,
            plan_id,
            handler_id,
            no_delayed_boundary,
            no_callback_boundary,
            no_blocking_marker,
        } => format!(
            "clean-known-state-catch e{} k{} h{} delayed={} callback={} blocking={}",
            catch_expr.0,
            plan_id.0,
            handler_id,
            !no_delayed_boundary,
            !no_callback_boundary,
            !no_blocking_marker
        ),
    }
}

fn format_known_state_payload_proof(
    payload: EvidenceVmKnownStateOperationPayloadProof,
) -> &'static str {
    match payload {
        EvidenceVmKnownStateOperationPayloadProof::UnitPayloadForGet => "unit-payload-for-get",
        EvidenceVmKnownStateOperationPayloadProof::SingleValuePayloadForSet => {
            "single-value-payload-for-set"
        }
    }
}

fn format_known_state_handler_source(source: EvidenceVmKnownStateHandlerSource) -> &'static str {
    match source {
        EvidenceVmKnownStateHandlerSource::CompilerLocalVar => "compiler-local-var",
    }
}

fn format_known_state_continuation(
    continuation: EvidenceVmKnownStateContinuationSemantics,
) -> &'static str {
    match continuation {
        EvidenceVmKnownStateContinuationSemantics::SnapshotFork => "snapshot-fork",
    }
}

fn format_known_operation_role(role: EvidenceVmKnownOperationRole) -> &'static str {
    match role {
        EvidenceVmKnownOperationRole::StateGet => "state-get",
        EvidenceVmKnownOperationRole::StateSet => "state-set",
    }
}

fn format_known_operation_reject(reject: EvidenceVmKnownOperationReject) -> &'static str {
    match reject {
        EvidenceVmKnownOperationReject::NoOperationObject => "no-operation-object",
        EvidenceVmKnownOperationReject::NotCall => "not-call",
        EvidenceVmKnownOperationReject::NoVisibility => "no-visibility",
        EvidenceVmKnownOperationReject::NoCandidateHandler => "no-candidate-handler",
        EvidenceVmKnownOperationReject::NoKnownStateAccessProof => "no-known-state-access-proof",
        EvidenceVmKnownOperationReject::KnownStateAccessHandlerMismatch => {
            "known-state-access-handler-mismatch"
        }
        EvidenceVmKnownOperationReject::KnownStateAccessBoundaryUnsafe => {
            "known-state-access-boundary-unsafe"
        }
        EvidenceVmKnownOperationReject::DirectExecutionDisabled => "direct-execution-disabled",
        EvidenceVmKnownOperationReject::NoKnownHandler => "no-known-handler",
        EvidenceVmKnownOperationReject::WrongHandler => "wrong-handler",
        EvidenceVmKnownOperationReject::WrongOperation => "wrong-operation",
        EvidenceVmKnownOperationReject::Blocked => "blocked",
        EvidenceVmKnownOperationReject::Delayed => "delayed",
        EvidenceVmKnownOperationReject::ProviderDirty => "provider-dirty",
    }
}

fn format_allowed_set_kind(kind: EvidenceVmAllowedSetKind) -> String {
    match kind {
        EvidenceVmAllowedSetKind::HandlerCapability(capability) => {
            format!("handler-cap c{}", capability.0)
        }
        EvidenceVmAllowedSetKind::LegacyGuardBridge => "legacy-guard-bridge".to_string(),
    }
}

fn format_value_env_kind(kind: &EvidenceVmValueEnvKind) -> String {
    match kind {
        EvidenceVmValueEnvKind::Lambda { body } => format!("lambda body e{}", body.0),
        EvidenceVmValueEnvKind::Thunk { body } => format!("thunk body e{}", body.0),
        EvidenceVmValueEnvKind::FunctionAdapter {
            function,
            creates_callback_boundary,
            body_marker_count,
            arg_marker_count,
            ret_marker_count,
        } => format!(
            "adapter function e{} callback_boundary={} markers body:{} arg:{} ret:{}",
            function.0,
            creates_callback_boundary,
            body_marker_count,
            arg_marker_count,
            ret_marker_count
        ),
    }
}

fn format_handler_arm_class(classification: EvidenceVmHandlerArmClass) -> &'static str {
    match classification {
        EvidenceVmHandlerArmClass::Value => "value",
        EvidenceVmHandlerArmClass::Abortive => "abortive",
        EvidenceVmHandlerArmClass::TailResumptive => "tail-resumptive",
        EvidenceVmHandlerArmClass::OneShotYield => "one-shot-yield",
        EvidenceVmHandlerArmClass::MultiShotYield => "multi-shot-yield",
        EvidenceVmHandlerArmClass::MayEscapeYield => "may-escape-yield",
        EvidenceVmHandlerArmClass::Fallback => "fallback",
    }
}

fn format_continuation_use(use_plan: EvidenceVmContinuationUsePlan) -> String {
    let tail = use_plan
        .tail_arg
        .map(|arg| format!("e{}", arg.0))
        .unwrap_or_else(|| "-".to_string());
    format!(
        "cont calls {} delayed {} escapes {} tail {}",
        use_plan.direct_calls, use_plan.delayed_calls, use_plan.escapes, tail
    )
}

fn format_operation_execution_plan(plan: EvidenceVmOperationExecutionPlan) -> &'static str {
    match plan {
        EvidenceVmOperationExecutionPlan::DirectAbortive => "direct-abortive",
        EvidenceVmOperationExecutionPlan::DirectTailResumptive => "direct-tail-resumptive",
        EvidenceVmOperationExecutionPlan::YieldFallback => "yield-fallback",
        EvidenceVmOperationExecutionPlan::BlockedFallback => "blocked-fallback",
        EvidenceVmOperationExecutionPlan::GenericFallback => "generic-fallback",
    }
}

fn format_provider_route(route: EvidenceVmProviderRoute) -> &'static str {
    match route {
        EvidenceVmProviderRoute::DirectPositive => "direct-positive",
        EvidenceVmProviderRoute::NeedsEvidenceEnv => "needs-evidence-env",
        EvidenceVmProviderRoute::BlockedByHygiene => "blocked-by-hygiene",
    }
}

fn format_operation_kind(kind: EvidenceVmOperationKind) -> String {
    match kind {
        EvidenceVmOperationKind::Value => "op-value".to_string(),
        EvidenceVmOperationKind::Call { apply, callee } => {
            format!("op-call apply e{} callee e{}", apply.0, callee.0)
        }
    }
}

fn format_operation_lowering(lowering: &EvidenceVmOperationLowering) -> String {
    match lowering {
        EvidenceVmOperationLowering::DirectHandlerCall {
            handler,
            resumptive,
            handler_known,
        } => {
            let mode = if *resumptive {
                "resumptive"
            } else {
                "abortive"
            };
            format!("direct-handler e{} {mode} known={handler_known}", handler.0)
        }
        EvidenceVmOperationLowering::LexicalHandlerCandidate {
            handler,
            resumptive,
            delayed_boundary,
        } => {
            let mode = if *resumptive {
                "resumptive"
            } else {
                "abortive"
            };
            format!(
                "lexical-handler-candidate e{} {mode} delayed_boundary={delayed_boundary}",
                handler.0
            )
        }
        EvidenceVmOperationLowering::HygieneFallback {
            handler,
            resumptive,
            callback_boundary,
            delayed_boundary,
        } => {
            let mode = if *resumptive {
                "resumptive"
            } else {
                "abortive"
            };
            format!(
                "hygiene-fallback e{} {mode} callback_boundary={} delayed_boundary={}",
                handler.0, callback_boundary, delayed_boundary
            )
        }
        EvidenceVmOperationLowering::GenericFallback => "generic-fallback".to_string(),
    }
}

fn format_task_owner(owner: RuntimeEvidenceTaskOwner) -> String {
    match owner {
        RuntimeEvidenceTaskOwner::RootExpr { root_index, expr } => {
            format!("root#{root_index} e{expr}")
        }
        RuntimeEvidenceTaskOwner::InstanceBody {
            instance,
            def,
            body,
        } => format!("instance i{instance} d{def} e{body}"),
    }
}

fn format_path(path: &[String]) -> String {
    path.join("::")
}

fn format_slot_key(slot: &EvidenceVmSlotKey) -> String {
    format!(
        "{}:{}",
        format_slot_route_key(slot.route),
        format_path(&slot.family)
    )
}

fn format_slot_route_key(route: EvidenceVmSlotRouteKey) -> &'static str {
    match route {
        EvidenceVmSlotRouteKey::Positive => "positive",
        EvidenceVmSlotRouteKey::Blocked => "blocked",
        EvidenceVmSlotRouteKey::UnknownFallback => "fallback",
    }
}

fn format_slot_keys(slots: &[EvidenceVmSlotKey]) -> String {
    slots
        .iter()
        .map(format_slot_key)
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_requirements(requirements: &[EvidenceVmEvidenceRequirement]) -> String {
    requirements
        .iter()
        .map(|requirement| {
            format!(
                "{}@e{}",
                format_slot_key(&requirement.slot),
                format_u32_list(&requirement.operation_exprs)
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_call_plans(calls: &[EvidenceVmCallPlan]) -> String {
    calls
        .iter()
        .map(|call| {
            format!(
                "e{}->i{}({})",
                call.apply.0,
                call.callee_instance,
                format_slot_keys(&call.required_evidence_slots)
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_env_providers(providers: &[EvidenceVmEnvProviderPlan]) -> String {
    providers
        .iter()
        .map(|provider| {
            format!(
                "s{}=[{}]",
                provider.slot_id,
                format_u32_list_with_prefix("h", &provider.handler_ids)
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_u32_list(values: &[u32]) -> String {
    values
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_u32_list_with_prefix(prefix: &str, values: &[u32]) -> String {
    values
        .iter()
        .map(|value| format!("{prefix}{value}"))
        .collect::<Vec<_>>()
        .join(", ")
}

#[derive(Debug, Clone, Copy)]
struct LexicalHandlerCandidate {
    handler: ExprId,
    resumptive: bool,
    delayed_boundary: bool,
}

struct LexicalHandlerIndex {
    by_operation_expr: HashMap<ExprId, LexicalHandlerCandidate>,
}

impl LexicalHandlerIndex {
    fn new(program: &Program, control: &ControlEvidenceProgram) -> Self {
        let handler_arms = control
            .handlers
            .iter()
            .map(|handler| {
                let arms = handler
                    .arms
                    .iter()
                    .filter_map(|arm| {
                        let path = arm.operation_path.clone()?;
                        Some((path, arm.resumptive))
                    })
                    .collect::<Vec<_>>();
                (handler.expr, arms)
            })
            .collect::<HashMap<_, _>>();
        let mut index = Self {
            by_operation_expr: HashMap::new(),
        };
        let mut context = LexicalHandlerContext::default();
        for root in &program.roots {
            match root {
                Root::Instance(_) | Root::EvalInstance(_) => {}
                Root::Expr(expr) => index.visit_expr(*expr, program, &handler_arms, &mut context),
            }
        }
        for instance in &program.instances {
            index.visit_expr(instance.entry, program, &handler_arms, &mut context);
        }
        index
    }

    fn candidate_for(&self, expr: ExprId) -> Option<LexicalHandlerCandidate> {
        self.by_operation_expr.get(&expr).copied()
    }

    fn visit_expr(
        &mut self,
        id: ExprId,
        program: &Program,
        handler_arms: &HashMap<ExprId, Vec<(Vec<String>, bool)>>,
        context: &mut LexicalHandlerContext,
    ) {
        let Some(expr) = control_expr(program, id) else {
            return;
        };
        match expr {
            Expr::EffectOp { path, .. } => {
                if let Some(candidate) = context.candidate_for(path) {
                    self.by_operation_expr.entry(id).or_insert(candidate);
                }
            }
            Expr::Coerce { expr, .. }
            | Expr::ForceThunk { thunk: expr, .. }
            | Expr::FunctionAdapter { function: expr, .. }
            | Expr::MarkerFrame { body: expr, .. }
            | Expr::Select { base: expr, .. } => {
                self.visit_expr(*expr, program, handler_arms, context);
            }
            Expr::MakeThunk { body, .. } => {
                context.with_delayed_boundary(true, |context| {
                    self.visit_expr(*body, program, handler_arms, context);
                });
            }
            Expr::Apply { callee, arg }
            | Expr::RefSet {
                reference: callee,
                value: arg,
            } => {
                self.visit_expr(*callee, program, handler_arms, context);
                self.visit_expr(*arg, program, handler_arms, context);
            }
            Expr::Lambda { body, .. } => {
                context.with_delayed_boundary(true, |context| {
                    self.visit_expr(*body, program, handler_arms, context);
                });
            }
            Expr::Tuple(items) => {
                for item in items {
                    self.visit_expr(*item, program, handler_arms, context);
                }
            }
            Expr::Record { fields, spread } => {
                for field in fields {
                    self.visit_expr(field.value, program, handler_arms, context);
                }
                match spread {
                    RecordSpread::None => {}
                    RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                        self.visit_expr(*expr, program, handler_arms, context);
                    }
                }
            }
            Expr::PolyVariant { payloads, .. } => {
                for payload in payloads {
                    self.visit_expr(*payload, program, handler_arms, context);
                }
            }
            Expr::Case { scrutinee, arms } => {
                self.visit_expr(*scrutinee, program, handler_arms, context);
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.visit_expr(guard, program, handler_arms, context);
                    }
                    self.visit_expr(arm.body, program, handler_arms, context);
                }
            }
            Expr::Catch { body, arms } => {
                let pushed = handler_arms.get(&id).and_then(|arms| {
                    (!arms.is_empty()).then(|| LexicalHandlerFrame {
                        handler: id,
                        arms: arms.clone(),
                    })
                });
                if let Some(frame) = pushed {
                    context.handlers.push(frame);
                    self.visit_expr(*body, program, handler_arms, context);
                    context.handlers.pop();
                } else {
                    self.visit_expr(*body, program, handler_arms, context);
                }
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.visit_expr(guard, program, handler_arms, context);
                    }
                    self.visit_expr(arm.body, program, handler_arms, context);
                }
            }
            Expr::Block(block) => self.visit_block(block, program, handler_arms, context),
            Expr::Lit(_)
            | Expr::PrimitiveOp { .. }
            | Expr::Constructor { .. }
            | Expr::Local(_)
            | Expr::InstanceRef(_) => {}
        }
    }

    fn visit_block(
        &mut self,
        block: &Block,
        program: &Program,
        handler_arms: &HashMap<ExprId, Vec<(Vec<String>, bool)>>,
        context: &mut LexicalHandlerContext,
    ) {
        for stmt in &block.stmts {
            self.visit_stmt(stmt, program, handler_arms, context);
        }
        if let Some(tail) = block.tail {
            self.visit_expr(tail, program, handler_arms, context);
        }
    }

    fn visit_stmt(
        &mut self,
        stmt: &Stmt,
        program: &Program,
        handler_arms: &HashMap<ExprId, Vec<(Vec<String>, bool)>>,
        context: &mut LexicalHandlerContext,
    ) {
        match stmt {
            Stmt::Let(_, _, expr) | Stmt::Expr(expr) => {
                self.visit_expr(*expr, program, handler_arms, context);
            }
            Stmt::Module(_, stmts) => {
                for stmt in stmts {
                    self.visit_stmt(stmt, program, handler_arms, context);
                }
            }
        }
    }
}

#[derive(Debug, Default)]
struct LexicalHandlerContext {
    handlers: Vec<LexicalHandlerFrame>,
    delayed_boundary_depth: usize,
}

impl LexicalHandlerContext {
    fn candidate_for(&self, path: &[String]) -> Option<LexicalHandlerCandidate> {
        self.handlers.iter().rev().find_map(|handler| {
            handler
                .arms
                .iter()
                .find(|(handled_path, _)| handled_path == path)
                .map(|(_, resumptive)| LexicalHandlerCandidate {
                    handler: handler.handler,
                    resumptive: *resumptive,
                    delayed_boundary: self.delayed_boundary_depth > 0,
                })
        })
    }

    fn with_delayed_boundary(&mut self, enabled: bool, f: impl FnOnce(&mut Self)) {
        if enabled {
            self.delayed_boundary_depth += 1;
        }
        f(self);
        if enabled {
            self.delayed_boundary_depth -= 1;
        }
    }
}

#[derive(Debug)]
struct LexicalHandlerFrame {
    handler: ExprId,
    arms: Vec<(Vec<String>, bool)>,
}

fn control_expr(program: &Program, id: ExprId) -> Option<&Expr> {
    program.exprs.get(id.0 as usize)
}

struct RuntimeNodeIndex<'a> {
    by_expr: BTreeMap<u32, Vec<&'a RuntimeEvidenceNode>>,
}

impl<'a> RuntimeNodeIndex<'a> {
    fn new(surface: &'a RuntimeEvidenceSurface) -> Self {
        let mut by_expr: BTreeMap<u32, Vec<&'a RuntimeEvidenceNode>> = BTreeMap::new();
        for task in &surface.tasks {
            for node in &task.nodes {
                by_expr.entry(node.expr).or_default().push(node);
            }
        }
        Self { by_expr }
    }

    fn nodes_for_expr(&self, expr: u32) -> Vec<&'a RuntimeEvidenceNode> {
        self.by_expr.get(&expr).cloned().unwrap_or_default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn object_plan_names_handler_capability_and_operation_visibility() {
        let path = vec!["flip".to_string(), "coin".to_string()];
        let handler_expr = ExprId(1);
        let operation_expr = ExprId(3);
        let handler = EvidenceVmHandlerPlan {
            expr: handler_expr,
            body: ExprId(2),
            arms: vec![EvidenceVmHandlerArmPlan {
                path: Some(path.clone()),
                resumptive: true,
                guarded: false,
                classification: EvidenceVmHandlerArmClass::TailResumptive,
                continuation_use: EvidenceVmContinuationUsePlan::default(),
                body: ExprId(4),
            }],
        };
        let operation = EvidenceVmOperationPlan {
            expr: operation_expr,
            operation_def: None,
            path: path.clone(),
            slot: positive_slot(path),
            kind: EvidenceVmOperationKind::Value,
            lowering: EvidenceVmOperationLowering::DirectHandlerCall {
                handler: handler_expr,
                resumptive: true,
                handler_known: true,
            },
            runtime_nodes: Vec::new(),
            runtime_evidence_refs: 0,
        };

        let objects = build_object_plan(
            &Program::default(),
            &RuntimeEvidenceSurface::default(),
            &[handler],
            &[operation],
            &[],
            &[],
        );

        assert_eq!(objects.handlers.len(), 1);
        assert_eq!(objects.handler_capabilities.len(), 1);
        assert_eq!(
            objects.handler_capabilities[0].id,
            objects.handlers[0].capability_id
        );
        assert_eq!(objects.allowed_sets.len(), 1);
        assert_eq!(
            objects.allowed_sets[0].kind,
            EvidenceVmAllowedSetKind::HandlerCapability(objects.handlers[0].capability_id)
        );
        assert_eq!(
            objects.operations[0].visibility.allowed_set_id,
            objects.allowed_sets[0].id
        );
        assert!(!objects.operations[0].visibility.legacy_guard_bridge);
        assert!(objects.known_handlers.is_empty());
    }

    #[test]
    fn static_route_classifies_only_known_host_generic_fallbacks_as_host_escape() {
        let host_path = vec![
            "std".to_string(),
            "io".to_string(),
            "file".to_string(),
            "file".to_string(),
            "read_at".to_string(),
        ];
        let user_path = vec!["flip".to_string(), "coin".to_string()];
        let handlers = HashMap::new();

        assert_eq!(
            operation_static_route_resolution(
                &generic_fallback_operation(ExprId(10), host_path),
                None,
                &handlers
            ),
            EvidenceVmStaticRouteResolution::Dynamic(
                EvidenceVmStaticRouteDynamicReason::HostEscape
            )
        );
        assert_eq!(
            operation_static_route_resolution(
                &generic_fallback_operation(ExprId(20), user_path),
                None,
                &handlers
            ),
            EvidenceVmStaticRouteResolution::Dynamic(
                EvidenceVmStaticRouteDynamicReason::Unclassified
            )
        );
    }

    #[test]
    fn static_route_classifies_non_lexical_handler_candidates() {
        let path = vec!["flip".to_string(), "coin".to_string()];
        let operation = generic_fallback_operation(ExprId(10), path.clone());
        let first_handler = handler_object(0, path.clone());
        let second_handler = handler_object(1, path);
        let mut one_handler = HashMap::new();
        one_handler.insert(0, &first_handler);
        let mut two_handlers = one_handler.clone();
        two_handlers.insert(1, &second_handler);

        assert_eq!(
            operation_static_route_resolution(&operation, None, &one_handler),
            EvidenceVmStaticRouteResolution::Dynamic(
                EvidenceVmStaticRouteDynamicReason::ProviderEnvDependent
            )
        );
        assert_eq!(
            operation_static_route_resolution(&operation, None, &two_handlers),
            EvidenceVmStaticRouteResolution::Dynamic(
                EvidenceVmStaticRouteDynamicReason::MultipleCandidates
            )
        );
    }

    #[test]
    fn object_plan_marks_compiler_known_state_handler_from_certificate() {
        let family = vec!["local".to_string(), "var".to_string()];
        let handler_expr = ExprId(2);
        let state_def = DefId(10);
        let body_def = DefId(11);
        let program = Program {
            exprs: vec![
                Expr::Lambda {
                    param: Pat::Var(state_def),
                    body: ExprId(1),
                },
                Expr::Lambda {
                    param: Pat::Var(body_def),
                    body: handler_expr,
                },
                Expr::Catch {
                    body: ExprId(3),
                    arms: Vec::new(),
                },
                Expr::Local(body_def),
            ],
            ..Program::default()
        };
        let handler = EvidenceVmHandlerPlan {
            expr: handler_expr,
            body: ExprId(2),
            arms: vec![
                EvidenceVmHandlerArmPlan {
                    path: Some(state_operation_path(
                        &family,
                        EvidenceVmKnownStateOperation::Get,
                    )),
                    resumptive: true,
                    guarded: false,
                    classification: EvidenceVmHandlerArmClass::MayEscapeYield,
                    continuation_use: EvidenceVmContinuationUsePlan {
                        delayed_calls: 1,
                        escapes: true,
                        ..EvidenceVmContinuationUsePlan::default()
                    },
                    body: ExprId(3),
                },
                EvidenceVmHandlerArmPlan {
                    path: Some(state_operation_path(
                        &family,
                        EvidenceVmKnownStateOperation::Set,
                    )),
                    resumptive: true,
                    guarded: false,
                    classification: EvidenceVmHandlerArmClass::MayEscapeYield,
                    continuation_use: EvidenceVmContinuationUsePlan {
                        delayed_calls: 1,
                        escapes: true,
                        ..EvidenceVmContinuationUsePlan::default()
                    },
                    body: ExprId(4),
                },
            ],
        };
        let surface = RuntimeEvidenceSurface {
            known_state_handlers: vec![specialize::RuntimeEvidenceKnownStateHandler {
                synthetic_var: 0,
                effect_path: family.clone(),
                source: specialize::RuntimeEvidenceKnownStateHandlerSource::CompilerLocalVar,
                continuation:
                    specialize::RuntimeEvidenceKnownStateContinuationSemantics::SnapshotFork,
            }],
            ..RuntimeEvidenceSurface::default()
        };

        let objects = build_object_plan(&program, &surface, &[handler], &[], &[], &[]);

        let [EvidenceVmKnownHandlerPlan::State(state)] = objects.known_handlers.as_slice() else {
            panic!(
                "expected one known state handler: {:?}",
                objects.known_handlers
            );
        };
        assert_eq!(state.handler, handler_expr);
        assert_eq!(state.synthetic_var, 0);
        assert_eq!(state.state, state_def);
        assert_eq!(state.family, family);
        assert_eq!(state.get_handler_id, 0);
        assert_eq!(state.set_handler_id, 1);
        assert_eq!(
            state.source,
            EvidenceVmKnownStateHandlerSource::CompilerLocalVar
        );
        assert_eq!(
            state.continuation,
            EvidenceVmKnownStateContinuationSemantics::SnapshotFork
        );
    }

    fn generic_fallback_operation(expr: ExprId, path: Vec<String>) -> EvidenceVmOperationPlan {
        EvidenceVmOperationPlan {
            expr,
            operation_def: None,
            path: path.clone(),
            slot: fallback_slot(path),
            kind: EvidenceVmOperationKind::Call {
                apply: expr,
                callee: expr,
            },
            lowering: EvidenceVmOperationLowering::GenericFallback,
            runtime_nodes: Vec::new(),
            runtime_evidence_refs: 0,
        }
    }

    fn handler_object(id: u32, path: Vec<String>) -> EvidenceVmHandlerObjectPlan {
        EvidenceVmHandlerObjectPlan {
            id,
            capability_id: EvidenceVmHandlerCapId(id),
            handler: ExprId(100 + id),
            slot_id: id,
            path,
            arm_body: ExprId(200 + id),
            arm_class: EvidenceVmHandlerArmClass::TailResumptive,
            continuation_use: EvidenceVmContinuationUsePlan::default(),
            definition_env: Vec::new(),
        }
    }
}
