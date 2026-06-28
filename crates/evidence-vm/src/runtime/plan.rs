use std::collections::HashMap;

use control_vm::ExprId;

use super::{
    ControlEvidenceIndex, EvidenceEffectRoute, EvidenceProviderGrant, EvidenceResolvedEffectRoute,
    EvidenceResolvedRouteOrigin, RuntimeEvidenceProviderView, RuntimeEvidenceRunStats,
};
use crate::{
    EvidenceVmAllowedSetId, EvidenceVmAllowedSetKind, EvidenceVmHandlerArmClass,
    EvidenceVmHandlerObjectPlan, EvidenceVmOperationExecutionPlan, EvidenceVmOperationKind,
    EvidenceVmOperationLowering, EvidenceVmOperationObjectPlan, EvidenceVmOperationPlan,
    EvidenceVmPlan,
};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct RuntimeEvidenceRunContext {
    provider_slots: usize,
    provider_candidates: usize,
    env_provider_slots: usize,
    env_provider_candidates: usize,
    direct_candidates: usize,
    effect_route_count: usize,
    direct_effect_route_count: usize,
    direct_abortive_effect_route_count: usize,
    direct_tail_resumptive_effect_route_count: usize,
    effect_routes: Option<HashMap<(ExprId, ExprId), EvidenceEffectRoute>>,
    value_provider_envs: HashMap<ExprId, RuntimeEvidenceProviderEnv>,
    value_capture_slots: HashMap<ExprId, Vec<u32>>,
    call_required_slots: HashMap<ExprId, Vec<u32>>,
    provider_candidates_by_slot: HashMap<u32, Vec<u32>>,
    handlers_by_catch: HashMap<ExprId, Vec<u32>>,
    handler_families_by_id: HashMap<u32, Vec<String>>,
    operation_visibilities: HashMap<(ExprId, ExprId), RuntimeEvidenceOperationVisibility>,
    operation_provider_lookups: HashMap<(ExprId, ExprId), RuntimeEvidenceOperationProviderLookup>,
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
        let value_provider_envs = value_provider_envs_from_plan(plan);
        let value_capture_slots = value_capture_slots_from_plan(plan);
        let call_required_slots = call_required_slots_from_plan(plan);
        let provider_candidates_by_slot = provider_candidates_by_slot(plan);
        let handlers_by_catch = handlers_by_catch_from_plan(plan);
        let handler_families_by_id = handler_families_by_id_from_plan(plan);
        let operation_visibilities = operation_visibilities_from_plan(plan);
        let operation_provider_lookups = operation_provider_lookups_from_plan(plan);
        Self {
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
            effect_routes: Some(effect_routes),
            value_provider_envs,
            value_capture_slots,
            call_required_slots,
            provider_candidates_by_slot,
            handlers_by_catch,
            handler_families_by_id,
            operation_visibilities,
            operation_provider_lookups,
        }
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
    }

    pub(super) fn provider_env_for_value(
        &self,
        expr: ExprId,
        active_handlers: &[u32],
        active_envs: &[&RuntimeEvidenceProviderEnv],
    ) -> RuntimeEvidenceProviderEnv {
        let mut provider_env = self
            .value_provider_envs
            .get(&expr)
            .cloned()
            .unwrap_or_default();
        if let Some(capture_slots) = self.value_capture_slots.get(&expr) {
            provider_env.extend_missing(capture_slots.iter().filter_map(|slot_id| {
                self.provider_for_slot(*slot_id, active_handlers, active_envs)
            }));
        }
        provider_env
    }

    pub(super) fn handler_ids_for_catch(&self, expr: ExprId) -> &[u32] {
        self.handlers_by_catch
            .get(&expr)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub(super) fn operation_visibility_for_call(
        &self,
        apply: ExprId,
        callee: ExprId,
    ) -> Option<RuntimeEvidenceOperationVisibility> {
        self.operation_visibilities.get(&(apply, callee)).copied()
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

    #[cfg(debug_assertions)]
    pub(super) fn catch_has_provider_grant_permission(
        &self,
        catch_expr: ExprId,
        request_path: &[String],
        permission: RuntimeEvidenceProviderGrantPermission,
    ) -> bool {
        self.catch_has_allowed_handler_id(catch_expr, request_path, permission.handler_id())
    }

    #[cfg(debug_assertions)]
    fn catch_has_allowed_handler_id(
        &self,
        catch_expr: ExprId,
        request_path: &[String],
        allowed_handler_id: u32,
    ) -> bool {
        self.handlers_by_catch
            .get(&catch_expr)
            .into_iter()
            .flatten()
            .any(|handler_id| {
                *handler_id == allowed_handler_id
                    && self
                        .handler_families_by_id
                        .get(handler_id)
                        .is_some_and(|family| family.as_slice() == request_path)
            })
    }

    pub(super) fn provider_env_for_call(
        &self,
        apply: ExprId,
        active_handlers: &[u32],
        active_envs: &[&RuntimeEvidenceProviderEnv],
    ) -> RuntimeEvidenceProviderEnv {
        let Some(required_slots) = self.call_required_slots.get(&apply) else {
            return RuntimeEvidenceProviderEnv::default();
        };
        let providers = required_slots
            .iter()
            .filter_map(|slot_id| self.provider_for_slot(*slot_id, active_handlers, active_envs))
            .collect::<Vec<_>>();
        RuntimeEvidenceProviderEnv { providers }
    }

    pub(super) fn has_provider_env_for_call(&self, apply: ExprId) -> bool {
        self.call_required_slots.contains_key(&apply)
    }

    pub(super) fn has_provider_lookup_for_call(&self, apply: ExprId, callee: ExprId) -> bool {
        self.operation_provider_lookups
            .contains_key(&(apply, callee))
    }

    pub(super) fn provider_route_for_call(
        &self,
        apply: ExprId,
        callee: ExprId,
        envs: &[RuntimeEvidenceProviderView<'_>],
    ) -> Option<EvidenceResolvedEffectRoute> {
        let lookup = self.operation_provider_lookups.get(&(apply, callee))?;
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
            handler_ids: vec![handler_id],
        })
    }
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

    #[cfg(debug_assertions)]
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
    #[cfg(debug_assertions)]
    pub(super) fn handler_id(self) -> u32 {
        self.handler_id
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct RuntimeEvidenceProviderEnv {
    providers: Vec<RuntimeEvidenceEnvProvider>,
}

impl RuntimeEvidenceProviderEnv {
    pub(super) fn is_empty(&self) -> bool {
        self.providers.is_empty()
    }

    pub(super) fn provider_count(&self) -> usize {
        self.providers
            .iter()
            .map(|provider| {
                let _slot_id = provider.slot_id;
                1usize
            })
            .sum()
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeEvidenceEnvProvider {
    slot_id: u32,
    handler_ids: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeEvidenceOperationProviderLookup {
    slot_id: u32,
    candidates: Vec<RuntimeEvidenceOperationProviderCandidate>,
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
) -> HashMap<ExprId, RuntimeEvidenceProviderEnv> {
    plan.objects
        .values
        .iter()
        .filter_map(|value| {
            let providers = value
                .env_providers
                .iter()
                .filter(|provider| !provider.handler_ids.is_empty())
                .map(|provider| RuntimeEvidenceEnvProvider {
                    slot_id: provider.slot_id,
                    handler_ids: provider.handler_ids.clone(),
                })
                .collect::<Vec<_>>();
            (!providers.is_empty())
                .then_some((value.expr, RuntimeEvidenceProviderEnv { providers }))
        })
        .collect()
}

fn call_required_slots_from_plan(plan: &EvidenceVmPlan) -> HashMap<ExprId, Vec<u32>> {
    plan.objects
        .calls
        .iter()
        .filter_map(|call| {
            (!call.required_slots.is_empty()).then_some((call.apply, call.required_slots.clone()))
        })
        .collect()
}

fn value_capture_slots_from_plan(plan: &EvidenceVmPlan) -> HashMap<ExprId, Vec<u32>> {
    plan.objects
        .values
        .iter()
        .filter_map(|value| {
            (!value.captures.is_empty()).then_some((value.expr, value.captures.clone()))
        })
        .collect()
}

fn handlers_by_catch_from_plan(plan: &EvidenceVmPlan) -> HashMap<ExprId, Vec<u32>> {
    plan.objects.handlers.iter().fold(
        HashMap::<ExprId, Vec<u32>>::new(),
        |mut by_catch, handler| {
            by_catch
                .entry(handler.handler)
                .or_default()
                .push(handler.id);
            by_catch
        },
    )
}

fn handler_families_by_id_from_plan(plan: &EvidenceVmPlan) -> HashMap<u32, Vec<String>> {
    plan.objects
        .handlers
        .iter()
        .map(|handler| (handler.id, handler.path.clone()))
        .collect()
}

fn operation_visibilities_from_plan(
    plan: &EvidenceVmPlan,
) -> HashMap<(ExprId, ExprId), RuntimeEvidenceOperationVisibility> {
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
    plan.operations
        .iter()
        .filter_map(|operation| {
            let EvidenceVmOperationKind::Call { apply, callee } = operation.kind else {
                return None;
            };
            let object = operation_objects.get(&operation.expr)?;
            let visibility = allowed_sets
                .get(&object.visibility.allowed_set_id)
                .copied()?;
            Some(((apply, callee), visibility))
        })
        .collect()
}

fn operation_provider_lookups_from_plan(
    plan: &EvidenceVmPlan,
) -> HashMap<(ExprId, ExprId), RuntimeEvidenceOperationProviderLookup> {
    let operation_objects = operation_objects_by_expr(plan);
    let provider_candidates = provider_candidates_by_slot(plan);
    let handlers = handler_objects_by_id(plan);
    plan.operations
        .iter()
        .filter_map(|operation| {
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
                    (apply, callee),
                    RuntimeEvidenceOperationProviderLookup {
                        slot_id: object.slot_id,
                        candidates: vec![RuntimeEvidenceOperationProviderCandidate {
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
                .collect::<Vec<_>>();
            if candidates.is_empty() {
                return None;
            }
            Some((
                (apply, callee),
                RuntimeEvidenceOperationProviderLookup {
                    slot_id: object.slot_id,
                    candidates,
                },
            ))
        })
        .collect()
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

fn provider_candidates_by_slot(plan: &EvidenceVmPlan) -> HashMap<u32, Vec<u32>> {
    plan.objects
        .providers
        .iter()
        .map(|provider| (provider.slot_id, provider.handler_candidates.clone()))
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
            summary: EvidenceVmSummary::default(),
            handlers: Vec::new(),
            operations: vec![crate::EvidenceVmOperationPlan {
                expr: callee,
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
