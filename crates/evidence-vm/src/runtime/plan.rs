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
}

impl RuntimeEvidenceRunContext {
    pub(super) fn from_plan(plan: &EvidenceVmPlan) -> Self {
        let effect_routes = effect_routes_from_plan(plan);
        let effect_route_count = effect_routes.len();
        let direct_effect_route_count = effect_routes
            .values()
            .filter(|route| matches!(route, EvidenceEffectRoute::Direct { .. }))
            .count();
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
