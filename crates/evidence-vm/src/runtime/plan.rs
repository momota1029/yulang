use std::collections::HashMap;

use control_vm::ExprId;

use super::{ControlEvidenceIndex, EvidenceEffectRoute, RuntimeEvidenceRunStats};
use crate::{
    EvidenceVmOperationExecutionPlan, EvidenceVmOperationKind, EvidenceVmOperationLowering,
    EvidenceVmOperationObjectPlan, EvidenceVmOperationPlan, EvidenceVmPlan,
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
    let operation_objects = operation_objects_by_expr(plan);
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
                        execution: object.execution,
                    },
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        EvidenceVmObjectPlan, EvidenceVmOperationExecutionPlan, EvidenceVmOperationObjectPlan,
        EvidenceVmSlotRouteKey, EvidenceVmSummary, EvidenceVmValueEnvKind,
        EvidenceVmValueObjectPlan,
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
                ..EvidenceVmObjectPlan::default()
            },
        };
        let context = RuntimeEvidenceRunContext::from_plan(&plan);
        let env = context.provider_env_for_value(value);

        assert_eq!(context.provider_route_for_call(apply, callee, &[]), None);
        assert_eq!(
            context.provider_route_for_call(apply, callee, &[env]),
            Some(EvidenceEffectRoute::Direct {
                handler,
                resumptive: true,
                execution: EvidenceVmOperationExecutionPlan::DirectTailResumptive,
            })
        );
    }
}
