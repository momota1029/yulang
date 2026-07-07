use std::collections::HashMap;

use control_ir::{DefId, ExprId};
use smallvec::{SmallVec, smallvec};

use super::{
    ControlEvidenceIndex, EvidenceEffectRoute, EvidenceProviderGrant, EvidenceResolvedEffectRoute,
    EvidenceResolvedRouteOrigin, RuntimeEvidenceHostConstructors, RuntimeEvidenceProviderView,
    RuntimeEvidenceRunStats,
};
use crate::{
    EvidenceVmAllowedSetId, EvidenceVmAllowedSetKind, EvidenceVmHandlerArmClass,
    EvidenceVmHandlerObjectPlan, EvidenceVmKnownHandlerPlan, EvidenceVmKnownHandlerPlanId,
    EvidenceVmKnownOperationReject, EvidenceVmKnownOperationRole,
    EvidenceVmKnownStateOperationPayloadProof, EvidenceVmKnownStateOperationRouteProofId,
    EvidenceVmOperationExecutionPlan, EvidenceVmOperationKind, EvidenceVmOperationLowering,
    EvidenceVmOperationObjectPlan, EvidenceVmOperationPlan, EvidenceVmPlan,
    EvidenceVmStaticRouteDynamicReason, EvidenceVmStaticRouteResolution,
};

pub(super) const DEFAULT_PRINT_NTH_LABEL: &str = "Out";

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct RuntimeEvidenceRunContext {
    deep_profile: bool,
    native_host_operations_disabled: bool,
    in_process_server_host_enabled: bool,
    flush_stdout_on_external_wait: bool,
    print_nth: bool,
    print_nth_label: Option<String>,
    provider_slots: usize,
    provider_candidates: usize,
    env_provider_slots: usize,
    env_provider_candidates: usize,
    direct_candidates: usize,
    effect_route_count: usize,
    direct_effect_route_count: usize,
    direct_abortive_effect_route_count: usize,
    direct_tail_resumptive_effect_route_count: usize,
    known_handler_count: usize,
    known_state_handler_count: usize,
    known_state_handler_compiler_certificate_count: usize,
    known_operation_call_count: usize,
    known_operation_state_get_candidate_count: usize,
    known_operation_state_set_candidate_count: usize,
    known_operation_state_direct_get_count: usize,
    known_operation_state_direct_set_count: usize,
    known_state_operation_route_proof_count: usize,
    known_operation_reject_no_operation_object_count: usize,
    known_operation_reject_not_call_count: usize,
    known_operation_reject_no_visibility_count: usize,
    known_operation_reject_no_candidate_handler_count: usize,
    known_operation_reject_no_known_state_access_proof_count: usize,
    known_operation_reject_known_state_access_handler_mismatch_count: usize,
    known_operation_reject_known_state_access_boundary_unsafe_count: usize,
    known_operation_reject_direct_execution_disabled_count: usize,
    known_operation_reject_no_known_handler_count: usize,
    known_operation_reject_wrong_handler_count: usize,
    known_operation_reject_wrong_operation_count: usize,
    known_operation_reject_blocked_count: usize,
    known_operation_reject_delayed_count: usize,
    known_operation_reject_provider_dirty_count: usize,
    static_route_sites_total: usize,
    static_route_static_handler: usize,
    static_route_static_tail_resumptive: usize,
    static_route_static_abortive: usize,
    static_route_static_other_arm: usize,
    static_route_dynamic_open_row: usize,
    static_route_dynamic_multiple_candidates: usize,
    static_route_dynamic_hygiene_barrier: usize,
    static_route_dynamic_provider_env: usize,
    static_route_dynamic_delayed_boundary: usize,
    static_route_dynamic_host_escape: usize,
    static_route_dynamic_unclassified: usize,
    static_route_mono_join_failures: usize,
    effect_routes: Option<HashMap<(ExprId, ExprId), EvidenceEffectRoute>>,
    value_provider_envs: Vec<Option<RuntimeEvidenceProviderEnv>>,
    value_capture_slots: Vec<Option<SmallVec<[u32; 2]>>>,
    call_required_slots: Vec<Option<SmallVec<[u32; 2]>>>,
    provider_candidates_by_slot: HashMap<u32, SmallVec<[u32; 2]>>,
    handlers_by_catch: Vec<Option<SmallVec<[u32; 2]>>>,
    known_state_handlers_by_catch: Vec<Option<RuntimeEvidenceKnownStateHandler>>,
    handler_families_by_id: Vec<Option<Vec<String>>>,
    known_operations_by_call: Vec<Option<(ExprId, RuntimeEvidenceKnownOperationCall)>>,
    known_state_route_proofs: Vec<Option<RuntimeEvidenceKnownStateRouteProof>>,
    operation_visibilities: Vec<Option<(ExprId, RuntimeEvidenceOperationVisibility)>>,
    operation_provider_lookups: Vec<Option<(ExprId, RuntimeEvidenceOperationProviderLookup)>>,
    static_routes_by_call: Vec<Option<(ExprId, RuntimeEvidenceStaticRouteResolution)>>,
    host_manifest: Option<poly::host_manifest::HostActManifest>,
    host_constructors: RuntimeEvidenceHostConstructors,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeEvidenceKnownOperationCall {
    pub(super) plan_id: EvidenceVmKnownHandlerPlanId,
    #[allow(dead_code)]
    pub(super) handler_id: u32,
    pub(super) role: EvidenceVmKnownOperationRole,
    pub(super) direct_ready: bool,
    pub(super) reject: Option<EvidenceVmKnownOperationReject>,
    pub(super) route_proof: Option<EvidenceVmKnownStateOperationRouteProofId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeEvidenceKnownStateRouteProof {
    pub(super) plan_id: EvidenceVmKnownHandlerPlanId,
    pub(super) catch_expr: ExprId,
    pub(super) handler_id: u32,
    pub(super) role: EvidenceVmKnownOperationRole,
    pub(super) payload: EvidenceVmKnownStateOperationPayloadProof,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeEvidenceStaticRouteResolution {
    StaticTail,
    StaticOther,
    Dynamic(RuntimeEvidenceStaticRouteDynamicReason),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeEvidenceStaticRouteDynamicReason {
    OpenRow,
    MultipleCandidates,
    HygieneBarrier,
    ProviderEnvDependent,
    DelayedBoundary,
    HostEscape,
    Unclassified,
}

impl RuntimeEvidenceRunContext {
    pub(super) fn from_plan(plan: &EvidenceVmPlan) -> Self {
        let effect_routes = effect_routes_from_plan(plan);
        let effect_route_count = effect_routes.len();
        let direct_effect_route_count = effect_routes
            .values()
            .filter(|route| route.is_direct())
            .count();
        let direct_abortive_effect_route_count = effect_routes
            .values()
            .filter(|route| route.is_direct_abortive())
            .count();
        let direct_tail_resumptive_effect_route_count = effect_routes
            .values()
            .filter(|route| route.is_direct_tail_resumptive())
            .count();
        let known_handler_count = plan.objects.known_handlers.len();
        let known_state_handler_count = plan
            .objects
            .known_handlers
            .iter()
            .filter(|handler| matches!(handler, EvidenceVmKnownHandlerPlan::State(_)))
            .count();
        let known_state_handler_compiler_certificate_count = plan
            .objects
            .known_handlers
            .iter()
            .filter(|handler| match handler {
                EvidenceVmKnownHandlerPlan::State(plan) => {
                    matches!(
                        plan.source,
                        crate::EvidenceVmKnownStateHandlerSource::CompilerLocalVar
                    )
                }
            })
            .count();
        let known_operation_call_count = plan.summary.plan_known_operation_calls;
        let known_operation_state_get_candidate_count =
            plan.summary.plan_known_operation_state_get_candidates;
        let known_operation_state_set_candidate_count =
            plan.summary.plan_known_operation_state_set_candidates;
        let known_operation_state_direct_get_count =
            plan.summary.plan_known_operation_state_direct_gets;
        let known_operation_state_direct_set_count =
            plan.summary.plan_known_operation_state_direct_sets;
        let known_state_operation_route_proof_count =
            plan.summary.plan_known_state_operation_route_proofs;
        let known_operation_reject_no_operation_object_count =
            plan.summary.plan_known_operation_reject_no_operation_object;
        let known_operation_reject_not_call_count =
            plan.summary.plan_known_operation_reject_not_call;
        let known_operation_reject_no_visibility_count =
            plan.summary.plan_known_operation_reject_no_visibility;
        let known_operation_reject_no_candidate_handler_count = plan
            .summary
            .plan_known_operation_reject_no_candidate_handler;
        let known_operation_reject_no_known_state_access_proof_count = plan
            .summary
            .plan_known_operation_reject_no_known_state_access_proof;
        let known_operation_reject_known_state_access_handler_mismatch_count = plan
            .summary
            .plan_known_operation_reject_known_state_access_handler_mismatch;
        let known_operation_reject_known_state_access_boundary_unsafe_count = plan
            .summary
            .plan_known_operation_reject_known_state_access_boundary_unsafe;
        let known_operation_reject_direct_execution_disabled_count = plan
            .summary
            .plan_known_operation_reject_direct_execution_disabled;
        let known_operation_reject_no_known_handler_count =
            plan.summary.plan_known_operation_reject_no_known_handler;
        let known_operation_reject_wrong_handler_count =
            plan.summary.plan_known_operation_reject_wrong_handler;
        let known_operation_reject_wrong_operation_count =
            plan.summary.plan_known_operation_reject_wrong_operation;
        let known_operation_reject_blocked_count = plan.summary.plan_known_operation_reject_blocked;
        let known_operation_reject_delayed_count = plan.summary.plan_known_operation_reject_delayed;
        let known_operation_reject_provider_dirty_count =
            plan.summary.plan_known_operation_reject_provider_dirty;
        let static_route_sites_total = plan.summary.static_route_sites_total;
        let static_route_static_handler = plan.summary.static_route_static_handler;
        let static_route_static_tail_resumptive = plan.summary.static_route_static_tail_resumptive;
        let static_route_static_abortive = plan.summary.static_route_static_abortive;
        let static_route_static_other_arm = plan.summary.static_route_static_other_arm;
        let static_route_dynamic_open_row = plan.summary.static_route_dynamic_open_row;
        let static_route_dynamic_multiple_candidates =
            plan.summary.static_route_dynamic_multiple_candidates;
        let static_route_dynamic_hygiene_barrier =
            plan.summary.static_route_dynamic_hygiene_barrier;
        let static_route_dynamic_provider_env = plan.summary.static_route_dynamic_provider_env;
        let static_route_dynamic_delayed_boundary =
            plan.summary.static_route_dynamic_delayed_boundary;
        let static_route_dynamic_host_escape = plan.summary.static_route_dynamic_host_escape;
        let static_route_dynamic_unclassified = plan.summary.static_route_dynamic_unclassified;
        let static_route_mono_join_failures = plan.summary.static_route_mono_join_failures;
        let expr_table_len = evidence_context_expr_table_len(plan);
        let value_provider_envs = value_provider_envs_from_plan(plan, expr_table_len);
        let value_capture_slots = value_capture_slots_from_plan(plan, expr_table_len);
        let call_required_slots = call_required_slots_from_plan(plan, expr_table_len);
        let provider_candidates_by_slot = provider_candidates_by_slot(plan);
        let handlers_by_catch = handlers_by_catch_from_plan(plan, expr_table_len);
        let known_state_handlers_by_catch =
            known_state_handlers_by_catch_from_plan(plan, expr_table_len);
        let handler_families_by_id = handler_families_by_id_from_plan(plan);
        let known_operations_by_call = known_operations_by_call_from_plan(plan, expr_table_len);
        let known_state_route_proofs = known_state_route_proofs_from_plan(plan);
        let operation_visibilities = operation_visibilities_from_plan(plan, expr_table_len);
        let operation_provider_lookups = operation_provider_lookups_from_plan(plan, expr_table_len);
        let static_routes_by_call = static_routes_by_call_from_plan(plan, expr_table_len);
        Self {
            deep_profile: false,
            native_host_operations_disabled: false,
            in_process_server_host_enabled: false,
            flush_stdout_on_external_wait: false,
            print_nth: false,
            print_nth_label: None,
            provider_slots: plan.objects.providers.len(),
            provider_candidates: plan
                .objects
                .providers
                .iter()
                .map(|provider| provider.handler_candidates.len())
                .sum(),
            env_provider_slots: plan
                .objects
                .values
                .iter()
                .map(|value| value.env_providers.len())
                .sum(),
            env_provider_candidates: plan
                .objects
                .values
                .iter()
                .flat_map(|value| &value.env_providers)
                .map(|provider| provider.handler_ids.len())
                .sum(),
            direct_candidates: plan
                .objects
                .operations
                .iter()
                .filter(|operation| operation.candidate_handler.is_some())
                .count(),
            effect_route_count,
            direct_effect_route_count,
            direct_abortive_effect_route_count,
            direct_tail_resumptive_effect_route_count,
            known_handler_count,
            known_state_handler_count,
            known_state_handler_compiler_certificate_count,
            known_operation_call_count,
            known_operation_state_get_candidate_count,
            known_operation_state_set_candidate_count,
            known_operation_state_direct_get_count,
            known_operation_state_direct_set_count,
            known_state_operation_route_proof_count,
            known_operation_reject_no_operation_object_count,
            known_operation_reject_not_call_count,
            known_operation_reject_no_visibility_count,
            known_operation_reject_no_candidate_handler_count,
            known_operation_reject_no_known_state_access_proof_count,
            known_operation_reject_known_state_access_handler_mismatch_count,
            known_operation_reject_known_state_access_boundary_unsafe_count,
            known_operation_reject_direct_execution_disabled_count,
            known_operation_reject_no_known_handler_count,
            known_operation_reject_wrong_handler_count,
            known_operation_reject_wrong_operation_count,
            known_operation_reject_blocked_count,
            known_operation_reject_delayed_count,
            known_operation_reject_provider_dirty_count,
            static_route_sites_total,
            static_route_static_handler,
            static_route_static_tail_resumptive,
            static_route_static_abortive,
            static_route_static_other_arm,
            static_route_dynamic_open_row,
            static_route_dynamic_multiple_candidates,
            static_route_dynamic_hygiene_barrier,
            static_route_dynamic_provider_env,
            static_route_dynamic_delayed_boundary,
            static_route_dynamic_host_escape,
            static_route_dynamic_unclassified,
            static_route_mono_join_failures,
            effect_routes: Some(effect_routes),
            value_provider_envs,
            value_capture_slots,
            call_required_slots,
            provider_candidates_by_slot,
            handlers_by_catch,
            known_state_handlers_by_catch,
            handler_families_by_id,
            known_operations_by_call,
            known_state_route_proofs,
            operation_visibilities,
            operation_provider_lookups,
            static_routes_by_call,
            host_manifest: plan.host_manifest.clone(),
            host_constructors: RuntimeEvidenceHostConstructors::default(),
        }
    }

    pub(super) fn with_deep_profile(mut self, enabled: bool) -> Self {
        self.deep_profile = enabled;
        self
    }

    pub(super) fn deep_profile_enabled(&self) -> bool {
        self.deep_profile
    }

    pub(super) fn without_native_host_operations(mut self) -> Self {
        self.native_host_operations_disabled = true;
        self
    }

    pub(super) fn with_in_process_server_host(mut self) -> Self {
        self.in_process_server_host_enabled = true;
        self
    }

    pub(super) fn in_process_server_host_enabled(&self) -> bool {
        self.in_process_server_host_enabled
    }

    pub(super) fn with_stdout_flush_on_external_wait(mut self) -> Self {
        self.flush_stdout_on_external_wait = true;
        self
    }

    pub(super) fn flush_stdout_on_external_wait(&self) -> bool {
        self.flush_stdout_on_external_wait
    }

    pub(super) fn with_print_nth(mut self) -> Self {
        self.print_nth = true;
        self
    }

    pub(super) fn with_print_nth_label(mut self, label: impl Into<String>) -> Self {
        self.print_nth = true;
        self.print_nth_label = Some(label.into());
        self
    }

    pub(super) fn print_nth(&self) -> bool {
        self.print_nth
    }

    pub(super) fn print_nth_label(&self) -> &str {
        self.print_nth_label
            .as_deref()
            .unwrap_or(DEFAULT_PRINT_NTH_LABEL)
    }

    pub(super) fn with_host_constructors(
        mut self,
        host_constructors: RuntimeEvidenceHostConstructors,
    ) -> Self {
        self.host_constructors = host_constructors;
        self
    }

    pub(super) fn host_constructors(&self) -> &RuntimeEvidenceHostConstructors {
        &self.host_constructors
    }

    pub(super) fn native_host_operations_enabled(&self) -> bool {
        !self.native_host_operations_disabled
    }

    pub(super) fn host_manifest(&self) -> Option<&poly::host_manifest::HostActManifest> {
        self.host_manifest.as_ref()
    }

    pub(super) fn apply_to_evidence(&mut self, evidence: &mut ControlEvidenceIndex) {
        if let Some(effect_routes) = self.effect_routes.take() {
            evidence.replace_effect_calls(effect_routes);
        }
    }

    pub(super) fn apply_to_stats(&self, stats: &mut RuntimeEvidenceRunStats) {
        stats.plan_provider_slots = self.provider_slots;
        stats.plan_provider_candidates = self.provider_candidates;
        stats.plan_env_provider_slots = self.env_provider_slots;
        stats.plan_env_provider_candidates = self.env_provider_candidates;
        stats.plan_direct_candidates = self.direct_candidates;
        stats.plan_effect_routes = self.effect_route_count;
        stats.plan_direct_effect_routes = self.direct_effect_route_count;
        stats.plan_direct_abortive_effect_routes = self.direct_abortive_effect_route_count;
        stats.plan_direct_tail_resumptive_effect_routes =
            self.direct_tail_resumptive_effect_route_count;
        stats.plan_known_handlers = self.known_handler_count;
        stats.plan_known_state_handlers = self.known_state_handler_count;
        stats.plan_known_state_handler_compiler_certificates =
            self.known_state_handler_compiler_certificate_count;
        stats.plan_known_operation_calls = self.known_operation_call_count;
        stats.plan_known_operation_state_get_candidates =
            self.known_operation_state_get_candidate_count;
        stats.plan_known_operation_state_set_candidates =
            self.known_operation_state_set_candidate_count;
        stats.plan_known_operation_state_direct_gets = self.known_operation_state_direct_get_count;
        stats.plan_known_operation_state_direct_sets = self.known_operation_state_direct_set_count;
        stats.plan_known_state_operation_route_proofs =
            self.known_state_operation_route_proof_count;
        stats.plan_known_operation_reject_no_operation_object =
            self.known_operation_reject_no_operation_object_count;
        stats.plan_known_operation_reject_not_call = self.known_operation_reject_not_call_count;
        stats.plan_known_operation_reject_no_visibility =
            self.known_operation_reject_no_visibility_count;
        stats.plan_known_operation_reject_no_candidate_handler =
            self.known_operation_reject_no_candidate_handler_count;
        stats.plan_known_operation_reject_no_known_state_access_proof =
            self.known_operation_reject_no_known_state_access_proof_count;
        stats.plan_known_operation_reject_known_state_access_handler_mismatch =
            self.known_operation_reject_known_state_access_handler_mismatch_count;
        stats.plan_known_operation_reject_known_state_access_boundary_unsafe =
            self.known_operation_reject_known_state_access_boundary_unsafe_count;
        stats.plan_known_operation_reject_direct_execution_disabled =
            self.known_operation_reject_direct_execution_disabled_count;
        stats.plan_known_operation_reject_no_known_handler =
            self.known_operation_reject_no_known_handler_count;
        stats.plan_known_operation_reject_wrong_handler =
            self.known_operation_reject_wrong_handler_count;
        stats.plan_known_operation_reject_wrong_operation =
            self.known_operation_reject_wrong_operation_count;
        stats.plan_known_operation_reject_blocked = self.known_operation_reject_blocked_count;
        stats.plan_known_operation_reject_delayed = self.known_operation_reject_delayed_count;
        stats.plan_known_operation_reject_provider_dirty =
            self.known_operation_reject_provider_dirty_count;
        stats.static_route_sites_total = self.static_route_sites_total;
        stats.static_route_static_handler = self.static_route_static_handler;
        stats.static_route_static_tail_resumptive = self.static_route_static_tail_resumptive;
        stats.static_route_static_abortive = self.static_route_static_abortive;
        stats.static_route_static_other_arm = self.static_route_static_other_arm;
        stats.static_route_dynamic_open_row = self.static_route_dynamic_open_row;
        stats.static_route_dynamic_multiple_candidates =
            self.static_route_dynamic_multiple_candidates;
        stats.static_route_dynamic_hygiene_barrier = self.static_route_dynamic_hygiene_barrier;
        stats.static_route_dynamic_provider_env = self.static_route_dynamic_provider_env;
        stats.static_route_dynamic_delayed_boundary = self.static_route_dynamic_delayed_boundary;
        stats.static_route_dynamic_host_escape = self.static_route_dynamic_host_escape;
        stats.static_route_dynamic_unclassified = self.static_route_dynamic_unclassified;
        stats.static_route_mono_join_failures = self.static_route_mono_join_failures;
    }

    pub(super) fn provider_env_for_value(
        &self,
        expr: ExprId,
        active_handlers: &[u32],
        active_envs: &[&RuntimeEvidenceProviderEnv],
    ) -> RuntimeEvidenceProviderEnv {
        let mut provider_env = self
            .value_provider_envs
            .get(expr.0 as usize)
            .and_then(Option::as_ref)
            .cloned()
            .unwrap_or_default();
        if let Some(capture_slots) = self
            .value_capture_slots
            .get(expr.0 as usize)
            .and_then(Option::as_ref)
        {
            provider_env.extend_missing(capture_slots.iter().filter_map(|slot_id| {
                self.provider_for_slot(*slot_id, active_handlers, active_envs)
            }));
        }
        provider_env
    }

    pub(super) fn handler_ids_for_catch(&self, expr: ExprId) -> &[u32] {
        self.handlers_by_catch
            .get(expr.0 as usize)
            .and_then(Option::as_ref)
            .map(SmallVec::as_slice)
            .unwrap_or_default()
    }

    pub(super) fn known_state_frame_for_catch(
        &self,
        catch_expr: ExprId,
    ) -> Option<RuntimeEvidenceKnownStateFramePlan> {
        let handler = self
            .known_state_handlers_by_catch
            .get(catch_expr.0 as usize)
            .and_then(Option::as_ref)?;
        Some(RuntimeEvidenceKnownStateFramePlan {
            plan_id: handler.plan_id,
            state: handler.state,
        })
    }

    pub(super) fn known_state_operation_for_request(
        &self,
        catch_expr: ExprId,
        request_path: &[String],
    ) -> Option<RuntimeEvidenceKnownStateOperation> {
        let handler = self
            .known_state_handlers_by_catch
            .get(catch_expr.0 as usize)
            .and_then(Option::as_ref)?;
        let operation = if request_path == handler.get_path.as_slice() {
            RuntimeEvidenceKnownStateOperationKind::Get
        } else if request_path == handler.set_path.as_slice() {
            RuntimeEvidenceKnownStateOperationKind::Set
        } else {
            return None;
        };
        Some(RuntimeEvidenceKnownStateOperation {
            plan_id: handler.plan_id,
            state: handler.state,
            kind: operation,
        })
    }

    pub(super) fn operation_visibility_for_call(
        &self,
        apply: ExprId,
        callee: ExprId,
    ) -> Option<RuntimeEvidenceOperationVisibility> {
        self.operation_visibilities
            .get(apply.0 as usize)
            .and_then(Option::as_ref)
            .and_then(|(expected_callee, visibility)| {
                (*expected_callee == callee).then_some(*visibility)
            })
    }

    pub(super) fn known_operation_for_call(
        &self,
        apply: ExprId,
        callee: ExprId,
    ) -> Option<RuntimeEvidenceKnownOperationCall> {
        self.known_operations_by_call
            .get(apply.0 as usize)
            .and_then(Option::as_ref)
            .and_then(|(expected_callee, operation)| {
                (*expected_callee == callee).then_some(*operation)
            })
    }

    pub(super) fn static_route_for_call(
        &self,
        apply: ExprId,
        callee: ExprId,
    ) -> Option<RuntimeEvidenceStaticRouteResolution> {
        self.static_routes_by_call
            .get(apply.0 as usize)
            .and_then(Option::as_ref)
            .and_then(|(expected_callee, resolution)| {
                (*expected_callee == callee).then_some(*resolution)
            })
    }

    pub(super) fn known_state_route_proof(
        &self,
        proof_id: EvidenceVmKnownStateOperationRouteProofId,
    ) -> Option<RuntimeEvidenceKnownStateRouteProof> {
        self.known_state_route_proofs
            .get(proof_id.0 as usize)
            .and_then(|proof| *proof)
    }

    #[cfg(debug_assertions)]
    pub(super) fn catch_has_allowed_handler(
        &self,
        catch_expr: ExprId,
        request_path: &[String],
        visibility: RuntimeEvidenceOperationVisibility,
    ) -> bool {
        let Some(allowed_handler_id) = visibility.allowed_handler_id() else {
            return false;
        };
        self.catch_has_allowed_handler_id(catch_expr, request_path, allowed_handler_id)
    }

    pub(super) fn catch_has_provider_grant_permission(
        &self,
        catch_expr: ExprId,
        request_path: &[String],
        permission: RuntimeEvidenceProviderGrantPermission,
    ) -> bool {
        self.catch_has_allowed_handler_id(catch_expr, request_path, permission.handler_id())
    }

    fn catch_has_allowed_handler_id(
        &self,
        catch_expr: ExprId,
        request_path: &[String],
        allowed_handler_id: u32,
    ) -> bool {
        let Some(family) = self
            .handler_families_by_id
            .get(allowed_handler_id as usize)
            .and_then(Option::as_ref)
        else {
            return false;
        };
        if family.as_slice() != request_path {
            return false;
        }
        self.handler_ids_for_catch(catch_expr)
            .contains(&allowed_handler_id)
    }

    pub(super) fn provider_grant_permission_family(
        &self,
        permission: RuntimeEvidenceProviderGrantPermission,
    ) -> Option<&[String]> {
        self.handler_families_by_id
            .get(permission.handler_id() as usize)
            .and_then(Option::as_ref)
            .map(Vec::as_slice)
    }

    pub(super) fn provider_env_for_call(
        &self,
        apply: ExprId,
        active_handlers: &[u32],
        active_envs: &[&RuntimeEvidenceProviderEnv],
    ) -> RuntimeEvidenceProviderEnv {
        let Some(required_slots) = self
            .call_required_slots
            .get(apply.0 as usize)
            .and_then(Option::as_ref)
        else {
            return RuntimeEvidenceProviderEnv::default();
        };
        let providers = required_slots
            .iter()
            .filter_map(|slot_id| self.provider_for_slot(*slot_id, active_handlers, active_envs))
            .collect::<SmallVec<_>>();
        RuntimeEvidenceProviderEnv { providers }
    }

    pub(super) fn has_provider_env_for_call(&self, apply: ExprId) -> bool {
        self.call_required_slots
            .get(apply.0 as usize)
            .is_some_and(Option::is_some)
    }

    pub(super) fn has_provider_lookup_for_call(&self, apply: ExprId, callee: ExprId) -> bool {
        self.operation_provider_lookups
            .get(apply.0 as usize)
            .and_then(Option::as_ref)
            .is_some_and(|(expected_callee, _)| *expected_callee == callee)
    }

    pub(super) fn provider_route_for_call(
        &self,
        apply: ExprId,
        callee: ExprId,
        envs: &[RuntimeEvidenceProviderView<'_>],
    ) -> Option<EvidenceResolvedEffectRoute> {
        let (expected_callee, lookup) = self
            .operation_provider_lookups
            .get(apply.0 as usize)
            .and_then(Option::as_ref)?;
        if *expected_callee != callee {
            return None;
        }
        for env in envs.iter().rev() {
            for candidate in &lookup.candidates {
                if env
                    .provider_env
                    .provides(lookup.slot_id, candidate.handler_id)
                {
                    return Some(EvidenceResolvedEffectRoute {
                        route: candidate.route,
                        origin: Some(EvidenceResolvedRouteOrigin::ProviderGrant(
                            candidate.grant(env.scope_id, env.hygiene_baseline),
                        )),
                        visibility: Some(RuntimeEvidenceOperationVisibility::provider_grant(
                            candidate.handler_id,
                        )),
                    });
                }
            }
        }
        None
    }

    fn provider_for_slot(
        &self,
        slot_id: u32,
        active_handlers: &[u32],
        active_envs: &[&RuntimeEvidenceProviderEnv],
    ) -> Option<RuntimeEvidenceEnvProvider> {
        let candidates = self.provider_candidates_by_slot.get(&slot_id)?;
        let handler_id = active_handlers
            .iter()
            .rev()
            .find(|handler_id| candidates.contains(handler_id))
            .copied()
            .or_else(|| {
                active_envs
                    .iter()
                    .rev()
                    .find_map(|env| env.handler_for_slot(slot_id, candidates))
            })?;
        Some(RuntimeEvidenceEnvProvider {
            slot_id,
            handler_ids: smallvec![handler_id],
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeEvidenceKnownStateHandler {
    plan_id: EvidenceVmKnownHandlerPlanId,
    state: DefId,
    get_path: Vec<String>,
    set_path: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeEvidenceKnownStateFramePlan {
    pub(super) plan_id: EvidenceVmKnownHandlerPlanId,
    pub(super) state: DefId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeEvidenceKnownStateOperation {
    pub(super) plan_id: EvidenceVmKnownHandlerPlanId,
    pub(super) state: DefId,
    pub(super) kind: RuntimeEvidenceKnownStateOperationKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeEvidenceKnownStateOperationKind {
    Get,
    Set,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeEvidenceOperationVisibility {
    PlanAllowedSet {
        allowed_set_id: EvidenceVmAllowedSetId,
        allowed_handler_id: Option<u32>,
        legacy_guard_bridge: bool,
    },
    ProviderGrant(RuntimeEvidenceProviderGrantPermission),
}

impl RuntimeEvidenceOperationVisibility {
    pub(super) fn plan_allowed_set(
        allowed_set_id: EvidenceVmAllowedSetId,
        allowed_handler_id: Option<u32>,
        legacy_guard_bridge: bool,
    ) -> Self {
        Self::PlanAllowedSet {
            allowed_set_id,
            allowed_handler_id,
            legacy_guard_bridge,
        }
    }

    pub(super) fn provider_grant(handler_id: u32) -> Self {
        Self::ProviderGrant(RuntimeEvidenceProviderGrantPermission { handler_id })
    }

    #[cfg(debug_assertions)]
    pub(super) fn allowed_handler_id(self) -> Option<u32> {
        match self {
            Self::PlanAllowedSet {
                allowed_handler_id, ..
            } => allowed_handler_id,
            Self::ProviderGrant(permission) => Some(permission.handler_id()),
        }
    }

    pub(super) fn legacy_guard_bridge(self) -> bool {
        match self {
            Self::PlanAllowedSet {
                legacy_guard_bridge,
                ..
            } => legacy_guard_bridge,
            Self::ProviderGrant(_) => false,
        }
    }

    pub(super) fn provider_grant_permission(
        self,
    ) -> Option<RuntimeEvidenceProviderGrantPermission> {
        match self {
            Self::ProviderGrant(permission) => Some(permission),
            Self::PlanAllowedSet { .. } => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeEvidenceProviderGrantPermission {
    handler_id: u32,
}

impl RuntimeEvidenceProviderGrantPermission {
    pub(super) fn handler_id(self) -> u32 {
        self.handler_id
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub(super) struct RuntimeEvidenceProviderEnv {
    providers: SmallVec<[RuntimeEvidenceEnvProvider; 2]>,
}

impl RuntimeEvidenceProviderEnv {
    pub(super) fn is_empty(&self) -> bool {
        self.providers.is_empty()
    }

    pub(super) fn provider_count(&self) -> usize {
        self.providers.len()
    }

    pub(super) fn candidate_count(&self) -> usize {
        self.providers
            .iter()
            .map(|provider| provider.handler_ids.len())
            .sum()
    }

    fn extend_missing(&mut self, providers: impl IntoIterator<Item = RuntimeEvidenceEnvProvider>) {
        for provider in providers {
            if self
                .providers
                .iter()
                .any(|current| current.slot_id == provider.slot_id)
            {
                continue;
            }
            self.providers.push(provider);
        }
    }

    fn provides(&self, slot_id: u32, handler_id: u32) -> bool {
        self.providers.iter().any(|provider| {
            provider.slot_id == slot_id && provider.handler_ids.contains(&handler_id)
        })
    }

    pub(super) fn contains_handler(&self, handler_id: u32) -> bool {
        self.providers
            .iter()
            .any(|provider| provider.handler_ids.contains(&handler_id))
    }

    fn handler_for_slot(&self, slot_id: u32, candidates: &[u32]) -> Option<u32> {
        self.providers.iter().find_map(|provider| {
            if provider.slot_id != slot_id {
                return None;
            }
            provider
                .handler_ids
                .iter()
                .find(|handler_id| candidates.contains(handler_id))
                .copied()
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RuntimeEvidenceEnvProvider {
    slot_id: u32,
    handler_ids: SmallVec<[u32; 2]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeEvidenceOperationProviderLookup {
    slot_id: u32,
    candidates: SmallVec<[RuntimeEvidenceOperationProviderCandidate; 2]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RuntimeEvidenceOperationProviderCandidate {
    handler_id: u32,
    route: EvidenceEffectRoute,
    demand_slot_id: u32,
    provider_slot_id: u32,
}

impl RuntimeEvidenceOperationProviderCandidate {
    fn grant(
        &self,
        scope_id: super::EvidenceProviderScopeId,
        hygiene_baseline: super::EvidenceProviderHygieneBaseline,
    ) -> EvidenceProviderGrant {
        EvidenceProviderGrant {
            demand_slot_id: self.demand_slot_id,
            provider_slot_id: self.provider_slot_id,
            handler_id: self.handler_id,
            scope_id,
            hygiene_baseline,
        }
    }
}

fn effect_routes_from_plan(
    plan: &EvidenceVmPlan,
) -> HashMap<(ExprId, ExprId), EvidenceEffectRoute> {
    let operation_objects = operation_objects_by_expr(plan);
    plan.operations
        .iter()
        .filter_map(|operation| effect_route_from_operation_plan(operation, &operation_objects))
        .collect()
}

fn effect_route_from_operation_plan(
    operation: &EvidenceVmOperationPlan,
    operation_objects: &HashMap<ExprId, &EvidenceVmOperationObjectPlan>,
) -> Option<((ExprId, ExprId), EvidenceEffectRoute)> {
    let EvidenceVmOperationKind::Call { apply, callee } = operation.kind else {
        return None;
    };
    let execution = operation_execution_for_route(operation, operation_objects);
    let route = match operation.lowering {
        EvidenceVmOperationLowering::DirectHandlerCall {
            handler,
            resumptive,
            ..
        } => EvidenceEffectRoute::Direct {
            handler,
            resumptive,
            execution,
            request_free_yield: true,
        },
        EvidenceVmOperationLowering::LexicalHandlerCandidate { .. }
        | EvidenceVmOperationLowering::HygieneFallback { .. }
        | EvidenceVmOperationLowering::GenericFallback => EvidenceEffectRoute::Unhandled,
    };
    Some(((apply, callee), route))
}

fn value_provider_envs_from_plan(
    plan: &EvidenceVmPlan,
    len: usize,
) -> Vec<Option<RuntimeEvidenceProviderEnv>> {
    let mut table = empty_expr_table(len);
    for value in &plan.objects.values {
        let providers = value
            .env_providers
            .iter()
            .filter(|provider| !provider.handler_ids.is_empty())
            .map(|provider| RuntimeEvidenceEnvProvider {
                slot_id: provider.slot_id,
                handler_ids: provider.handler_ids.iter().copied().collect(),
            })
            .collect::<SmallVec<_>>();
        if !providers.is_empty() {
            table[value.expr.0 as usize] = Some(RuntimeEvidenceProviderEnv { providers });
        }
    }
    table
}

fn call_required_slots_from_plan(
    plan: &EvidenceVmPlan,
    len: usize,
) -> Vec<Option<SmallVec<[u32; 2]>>> {
    let mut table = empty_expr_table(len);
    for call in &plan.objects.calls {
        if !call.required_slots.is_empty() {
            table[call.apply.0 as usize] = Some(call.required_slots.iter().copied().collect());
        }
    }
    table
}

fn value_capture_slots_from_plan(
    plan: &EvidenceVmPlan,
    len: usize,
) -> Vec<Option<SmallVec<[u32; 2]>>> {
    let mut table = empty_expr_table(len);
    for value in &plan.objects.values {
        if !value.captures.is_empty() {
            table[value.expr.0 as usize] = Some(value.captures.iter().copied().collect());
        }
    }
    table
}

fn empty_expr_table<T>(len: usize) -> Vec<Option<T>> {
    let mut table = Vec::with_capacity(len);
    table.resize_with(len, || None);
    table
}

fn evidence_context_expr_table_len(plan: &EvidenceVmPlan) -> usize {
    plan.objects
        .values
        .iter()
        .map(|value| value.expr)
        .chain(plan.objects.handlers.iter().map(|handler| handler.handler))
        .chain(plan.objects.calls.iter().map(|call| call.apply))
        .chain(plan.operations.iter().flat_map(|operation| {
            let mut exprs = SmallVec::<[ExprId; 3]>::new();
            exprs.push(operation.expr);
            if let EvidenceVmOperationKind::Call { apply, callee } = operation.kind {
                exprs.push(apply);
                exprs.push(callee);
            }
            exprs
        }))
        .map(|expr| expr.0 as usize + 1)
        .max()
        .unwrap_or(0)
}

fn handlers_by_catch_from_plan(
    plan: &EvidenceVmPlan,
    len: usize,
) -> Vec<Option<SmallVec<[u32; 2]>>> {
    let mut table = empty_expr_table(len);
    for handler in &plan.objects.handlers {
        table[handler.handler.0 as usize]
            .get_or_insert_with(SmallVec::new)
            .push(handler.id);
    }
    table
}

fn known_state_handlers_by_catch_from_plan(
    plan: &EvidenceVmPlan,
    len: usize,
) -> Vec<Option<RuntimeEvidenceKnownStateHandler>> {
    let mut table = empty_expr_table(len);
    for known in &plan.objects.known_handlers {
        let EvidenceVmKnownHandlerPlan::State(state) = known;
        table[state.handler.0 as usize] = Some(RuntimeEvidenceKnownStateHandler {
            plan_id: state.id,
            state: state.state,
            get_path: state_operation_path(&state.family, "get"),
            set_path: state_operation_path(&state.family, "set"),
        });
    }
    table
}

fn state_operation_path(family: &[String], operation: &str) -> Vec<String> {
    let mut path = family.to_vec();
    path.push(operation.to_string());
    path
}

fn handler_families_by_id_from_plan(plan: &EvidenceVmPlan) -> Vec<Option<Vec<String>>> {
    let len = plan
        .objects
        .handlers
        .iter()
        .map(|handler| handler.id as usize + 1)
        .max()
        .unwrap_or(0);
    let mut table = Vec::with_capacity(len);
    table.resize_with(len, || None);
    for handler in &plan.objects.handlers {
        table[handler.id as usize] = Some(handler.path.clone());
    }
    table
}

fn known_operations_by_call_from_plan(
    plan: &EvidenceVmPlan,
    len: usize,
) -> Vec<Option<(ExprId, RuntimeEvidenceKnownOperationCall)>> {
    let mut table = empty_expr_table(len);
    for operation in &plan.objects.known_operations {
        table[operation.apply.0 as usize] = Some((
            operation.callee,
            RuntimeEvidenceKnownOperationCall {
                plan_id: operation.known_handler,
                handler_id: operation.handler_id,
                role: operation.role,
                direct_ready: operation.direct_ready,
                reject: operation.reject,
                route_proof: operation.route_proof,
            },
        ));
    }
    table
}

fn known_state_route_proofs_from_plan(
    plan: &EvidenceVmPlan,
) -> Vec<Option<RuntimeEvidenceKnownStateRouteProof>> {
    let len = plan
        .objects
        .known_state_operation_route_proofs
        .iter()
        .map(|proof| proof.id.0 as usize + 1)
        .max()
        .unwrap_or(0);
    let mut table = Vec::with_capacity(len);
    table.resize_with(len, || None);
    for proof in &plan.objects.known_state_operation_route_proofs {
        table[proof.id.0 as usize] = Some(RuntimeEvidenceKnownStateRouteProof {
            plan_id: proof.plan_id,
            catch_expr: proof.catch_expr,
            handler_id: proof.handler_id,
            role: proof.role,
            payload: proof.payload,
        });
    }
    table
}

fn operation_visibilities_from_plan(
    plan: &EvidenceVmPlan,
    len: usize,
) -> Vec<Option<(ExprId, RuntimeEvidenceOperationVisibility)>> {
    let cap_handlers = plan
        .objects
        .handler_capabilities
        .iter()
        .map(|capability| (capability.id, capability.handler_id))
        .collect::<HashMap<_, _>>();
    let allowed_sets = plan
        .objects
        .allowed_sets
        .iter()
        .map(|allowed| {
            let allowed_handler_id = match allowed.kind {
                EvidenceVmAllowedSetKind::HandlerCapability(capability_id) => {
                    cap_handlers.get(&capability_id).copied()
                }
                EvidenceVmAllowedSetKind::LegacyGuardBridge => None,
            };
            let legacy_guard_bridge =
                matches!(allowed.kind, EvidenceVmAllowedSetKind::LegacyGuardBridge);
            (
                allowed.id,
                RuntimeEvidenceOperationVisibility::plan_allowed_set(
                    allowed.id,
                    allowed_handler_id,
                    legacy_guard_bridge,
                ),
            )
        })
        .collect::<HashMap<_, _>>();
    let operation_objects = operation_objects_by_expr(plan);
    let mut table = empty_expr_table(len);
    for operation in &plan.operations {
        let Some((apply, callee, visibility)) = (|| {
            let EvidenceVmOperationKind::Call { apply, callee } = operation.kind else {
                return None;
            };
            let object = operation_objects.get(&operation.expr)?;
            let visibility = allowed_sets
                .get(&object.visibility.allowed_set_id)
                .copied()?;
            Some((apply, callee, visibility))
        })() else {
            continue;
        };
        table[apply.0 as usize] = Some((callee, visibility));
    }
    table
}

fn static_routes_by_call_from_plan(
    plan: &EvidenceVmPlan,
    len: usize,
) -> Vec<Option<(ExprId, RuntimeEvidenceStaticRouteResolution)>> {
    let operation_objects = operation_objects_by_expr(plan);
    let mut table = empty_expr_table(len);
    for operation in &plan.operations {
        let EvidenceVmOperationKind::Call { apply, callee } = operation.kind else {
            continue;
        };
        let Some(object) = operation_objects.get(&operation.expr) else {
            table[apply.0 as usize] = Some((
                callee,
                RuntimeEvidenceStaticRouteResolution::Dynamic(
                    RuntimeEvidenceStaticRouteDynamicReason::Unclassified,
                ),
            ));
            continue;
        };
        table[apply.0 as usize] = Some((callee, static_route_resolution(object.static_route)));
    }
    table
}

fn static_route_resolution(
    resolution: EvidenceVmStaticRouteResolution,
) -> RuntimeEvidenceStaticRouteResolution {
    match resolution {
        EvidenceVmStaticRouteResolution::StaticHandler { arm_class } => {
            if arm_class == EvidenceVmHandlerArmClass::TailResumptive {
                RuntimeEvidenceStaticRouteResolution::StaticTail
            } else {
                RuntimeEvidenceStaticRouteResolution::StaticOther
            }
        }
        EvidenceVmStaticRouteResolution::Dynamic(reason) => {
            RuntimeEvidenceStaticRouteResolution::Dynamic(static_route_dynamic_reason(reason))
        }
    }
}

fn static_route_dynamic_reason(
    reason: EvidenceVmStaticRouteDynamicReason,
) -> RuntimeEvidenceStaticRouteDynamicReason {
    match reason {
        EvidenceVmStaticRouteDynamicReason::OpenRow => {
            RuntimeEvidenceStaticRouteDynamicReason::OpenRow
        }
        EvidenceVmStaticRouteDynamicReason::MultipleCandidates => {
            RuntimeEvidenceStaticRouteDynamicReason::MultipleCandidates
        }
        EvidenceVmStaticRouteDynamicReason::HygieneBarrier => {
            RuntimeEvidenceStaticRouteDynamicReason::HygieneBarrier
        }
        EvidenceVmStaticRouteDynamicReason::ProviderEnvDependent => {
            RuntimeEvidenceStaticRouteDynamicReason::ProviderEnvDependent
        }
        EvidenceVmStaticRouteDynamicReason::DelayedBoundary => {
            RuntimeEvidenceStaticRouteDynamicReason::DelayedBoundary
        }
        EvidenceVmStaticRouteDynamicReason::HostEscape => {
            RuntimeEvidenceStaticRouteDynamicReason::HostEscape
        }
        EvidenceVmStaticRouteDynamicReason::Unclassified => {
            RuntimeEvidenceStaticRouteDynamicReason::Unclassified
        }
    }
}

fn operation_provider_lookups_from_plan(
    plan: &EvidenceVmPlan,
    len: usize,
) -> Vec<Option<(ExprId, RuntimeEvidenceOperationProviderLookup)>> {
    let operation_objects = operation_objects_by_expr(plan);
    let provider_candidates = provider_candidates_by_slot(plan);
    let handlers = handler_objects_by_id(plan);
    let mut table = empty_expr_table(len);
    for operation in &plan.operations {
        let Some((apply, callee, lookup)) = (|| {
            let EvidenceVmOperationKind::Call { apply, callee } = operation.kind else {
                return None;
            };
            if matches!(
                operation.lowering,
                EvidenceVmOperationLowering::DirectHandlerCall { .. }
            ) {
                return None;
            }
            let object = operation_objects.get(&operation.expr)?;
            if let EvidenceVmOperationLowering::LexicalHandlerCandidate {
                handler,
                resumptive,
                delayed_boundary: false,
            } = operation.lowering
                && let Some(handler_id) = object.candidate_handler
            {
                return Some((
                    apply,
                    callee,
                    RuntimeEvidenceOperationProviderLookup {
                        slot_id: object.slot_id,
                        candidates: smallvec![RuntimeEvidenceOperationProviderCandidate {
                            handler_id,
                            route: EvidenceEffectRoute::Direct {
                                handler,
                                resumptive,
                                execution: object.execution,
                                request_free_yield: false,
                            },
                            demand_slot_id: object.slot_id,
                            provider_slot_id: object.slot_id,
                        }],
                    },
                ));
            }
            let candidates = provider_candidates.get(&object.slot_id)?;
            let candidates = candidates
                .iter()
                .filter_map(|handler_id| {
                    let handler = handlers.get(handler_id)?;
                    Some(RuntimeEvidenceOperationProviderCandidate {
                        handler_id: *handler_id,
                        route: route_for_provider_handler(handler),
                        demand_slot_id: object.slot_id,
                        provider_slot_id: handler.slot_id,
                    })
                })
                .collect::<SmallVec<_>>();
            if candidates.is_empty() {
                return None;
            }
            Some((
                apply,
                callee,
                RuntimeEvidenceOperationProviderLookup {
                    slot_id: object.slot_id,
                    candidates,
                },
            ))
        })() else {
            continue;
        };
        table[apply.0 as usize] = Some((callee, lookup));
    }
    table
}

fn operation_objects_by_expr(
    plan: &EvidenceVmPlan,
) -> HashMap<ExprId, &EvidenceVmOperationObjectPlan> {
    plan.objects
        .operations
        .iter()
        .map(|operation| (operation.expr, operation))
        .collect()
}

fn operation_execution_for_route(
    operation: &EvidenceVmOperationPlan,
    operation_objects: &HashMap<ExprId, &EvidenceVmOperationObjectPlan>,
) -> EvidenceVmOperationExecutionPlan {
    operation_objects
        .get(&operation.expr)
        .map(|object| object.execution)
        .unwrap_or(EvidenceVmOperationExecutionPlan::GenericFallback)
}

fn provider_candidates_by_slot(plan: &EvidenceVmPlan) -> HashMap<u32, SmallVec<[u32; 2]>> {
    plan.objects
        .providers
        .iter()
        .map(|provider| {
            (
                provider.slot_id,
                provider.handler_candidates.iter().copied().collect(),
            )
        })
        .collect()
}

fn handler_objects_by_id(plan: &EvidenceVmPlan) -> HashMap<u32, &EvidenceVmHandlerObjectPlan> {
    plan.objects
        .handlers
        .iter()
        .map(|handler| (handler.id, handler))
        .collect()
}

fn route_for_provider_handler(handler: &EvidenceVmHandlerObjectPlan) -> EvidenceEffectRoute {
    EvidenceEffectRoute::Direct {
        handler: handler.handler,
        resumptive: handler.arm_class != EvidenceVmHandlerArmClass::Abortive,
        execution: execution_for_handler_arm_class(handler.arm_class),
        request_free_yield: false,
    }
}

fn execution_for_handler_arm_class(
    class: EvidenceVmHandlerArmClass,
) -> EvidenceVmOperationExecutionPlan {
    match class {
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

#[cfg(test)]
mod tests {
    use super::super::{EvidenceProviderHygieneBaseline, EvidenceProviderScopeId};
    use super::*;
    use crate::{
        EvidenceVmAllowedSetKind, EvidenceVmAllowedSetPlan, EvidenceVmObjectPlan,
        EvidenceVmOperationExecutionPlan, EvidenceVmOperationObjectPlan,
        EvidenceVmOperationVisibilityPlan, EvidenceVmSlotRouteKey, EvidenceVmSummary,
        EvidenceVmValueEnvKind, EvidenceVmValueObjectPlan,
    };

    #[test]
    fn provider_env_can_route_lexical_candidate_operation() {
        let apply = ExprId(10);
        let callee = ExprId(11);
        let handler = ExprId(20);
        let value = ExprId(30);
        let slot_id = 7;
        let handler_id = 3;
        let plan = EvidenceVmPlan {
            host_manifest: None,
            summary: EvidenceVmSummary::default(),
            handlers: Vec::new(),
            operations: vec![crate::EvidenceVmOperationPlan {
                expr: callee,
                operation_def: None,
                path: vec!["out".to_string(), "say".to_string()],
                slot: crate::EvidenceVmSlotKey {
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
                    static_route: EvidenceVmStaticRouteResolution::Dynamic(
                        EvidenceVmStaticRouteDynamicReason::ProviderEnvDependent,
                    ),
                }],
                values: vec![EvidenceVmValueObjectPlan {
                    id: 0,
                    expr: value,
                    kind: EvidenceVmValueEnvKind::Lambda { body: ExprId(31) },
                    captures: vec![slot_id],
                    env_providers: vec![crate::EvidenceVmEnvProviderPlan {
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
        let context = RuntimeEvidenceRunContext::from_plan(&plan);
        let env = context.provider_env_for_value(value, &[], &[]);
        let scope_id = EvidenceProviderScopeId(0);
        let hygiene_baseline = EvidenceProviderHygieneBaseline {
            marker_plan_len: 0,
            active_add_id_len: 0,
            active_handler_frame_len: 0,
        };
        let view = RuntimeEvidenceProviderView {
            scope_id,
            provider_env: &env,
            hygiene_baseline,
        };

        assert_eq!(context.provider_route_for_call(apply, callee, &[]), None);
        assert_eq!(
            context.provider_route_for_call(apply, callee, &[view]),
            Some(EvidenceResolvedEffectRoute {
                route: EvidenceEffectRoute::Direct {
                    handler,
                    resumptive: true,
                    execution: EvidenceVmOperationExecutionPlan::DirectTailResumptive,
                    request_free_yield: false,
                },
                origin: Some(EvidenceResolvedRouteOrigin::ProviderGrant(
                    EvidenceProviderGrant {
                        demand_slot_id: slot_id,
                        provider_slot_id: slot_id,
                        handler_id,
                        scope_id,
                        hygiene_baseline,
                    }
                )),
                visibility: Some(RuntimeEvidenceOperationVisibility::provider_grant(
                    handler_id
                )),
            })
        );
    }
}
