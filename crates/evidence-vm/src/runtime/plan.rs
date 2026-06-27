use std::collections::HashMap;

use control_vm::ExprId;

use super::{ControlEvidenceIndex, EvidenceEffectRoute, RuntimeEvidenceRunStats};
use crate::{
    EvidenceVmOperationKind, EvidenceVmOperationLowering, EvidenceVmOperationPlan, EvidenceVmPlan,
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
    effect_routes: Option<HashMap<(ExprId, ExprId), EvidenceEffectRoute>>,
    value_provider_envs: HashMap<ExprId, RuntimeEvidenceProviderEnv>,
    operation_provider_lookups: HashMap<(ExprId, ExprId), RuntimeEvidenceOperationProviderLookup>,
}

impl RuntimeEvidenceRunContext {
    pub(super) fn from_plan(plan: &EvidenceVmPlan) -> Self {
        let effect_routes = effect_routes_from_plan(plan);
        let effect_route_count = effect_routes.len();
        let direct_effect_route_count = effect_routes
            .values()
            .filter(|route| matches!(route, EvidenceEffectRoute::Direct { .. }))
            .count();
        let value_provider_envs = value_provider_envs_from_plan(plan);
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
            effect_routes: Some(effect_routes),
            value_provider_envs,
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
    }

    pub(super) fn provider_env_for_value(&self, expr: ExprId) -> RuntimeEvidenceProviderEnv {
        self.value_provider_envs
            .get(&expr)
            .cloned()
            .unwrap_or_default()
    }

    pub(super) fn has_provider_lookup_for_call(&self, apply: ExprId, callee: ExprId) -> bool {
        self.operation_provider_lookups
            .contains_key(&(apply, callee))
    }

    pub(super) fn provider_route_for_call(
        &self,
        apply: ExprId,
        callee: ExprId,
        envs: &[RuntimeEvidenceProviderEnv],
    ) -> Option<EvidenceEffectRoute> {
        let lookup = self.operation_provider_lookups.get(&(apply, callee))?;
        envs.iter()
            .rev()
            .any(|env| env.provides(lookup.slot_id, lookup.handler_id))
            .then_some(lookup.route)
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

    fn provides(&self, slot_id: u32, handler_id: u32) -> bool {
        self.providers.iter().any(|provider| {
            provider.slot_id == slot_id && provider.handler_ids.contains(&handler_id)
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeEvidenceEnvProvider {
    slot_id: u32,
    handler_ids: Vec<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RuntimeEvidenceOperationProviderLookup {
    slot_id: u32,
    handler_id: u32,
    route: EvidenceEffectRoute,
}

fn effect_routes_from_plan(
    plan: &EvidenceVmPlan,
) -> HashMap<(ExprId, ExprId), EvidenceEffectRoute> {
    plan.operations
        .iter()
        .filter_map(effect_route_from_operation_plan)
        .collect()
}

fn effect_route_from_operation_plan(
    operation: &EvidenceVmOperationPlan,
) -> Option<((ExprId, ExprId), EvidenceEffectRoute)> {
    let EvidenceVmOperationKind::Call { apply, callee } = operation.kind else {
        return None;
    };
    let route = match operation.lowering {
        EvidenceVmOperationLowering::DirectHandlerCall {
            handler,
            resumptive,
            ..
        } => EvidenceEffectRoute::Direct {
            handler,
            resumptive,
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

fn operation_provider_lookups_from_plan(
    plan: &EvidenceVmPlan,
) -> HashMap<(ExprId, ExprId), RuntimeEvidenceOperationProviderLookup> {
    let operation_objects = plan
        .objects
        .operations
        .iter()
        .map(|operation| (operation.expr, operation))
        .collect::<HashMap<_, _>>();
    plan.operations
        .iter()
        .filter_map(|operation| {
            let EvidenceVmOperationKind::Call { apply, callee } = operation.kind else {
                return None;
            };
            let EvidenceVmOperationLowering::LexicalHandlerCandidate {
                handler,
                resumptive,
                delayed_boundary: false,
            } = operation.lowering
            else {
                return None;
            };
            let object = operation_objects.get(&operation.expr)?;
            let handler_id = object.candidate_handler?;
            Some((
                (apply, callee),
                RuntimeEvidenceOperationProviderLookup {
                    slot_id: object.slot_id,
                    handler_id,
                    route: EvidenceEffectRoute::Direct {
                        handler,
                        resumptive,
                    },
                },
            ))
        })
        .collect()
}
