//! Read-only algebraic-effect region analysis for CPS representation ABI.
//!
//! This module deliberately classifies effect handling by `Perform`, handler
//! arm, `Resume`, clone, and nested-effect structure. It does not inspect std
//! paths or treat any operation name as syntax.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::cps_ir::{
    CpsContinuationId, CpsHandlerId, CpsShotKind, CpsStmt, CpsTerminator, CpsValueId,
};
use crate::cps_repr::CpsReprAbiLane;
use crate::cps_repr_abi::{CpsReprAbiContinuation, CpsReprAbiFunction, CpsReprAbiModule};
use yulang_typed_ir as typed_ir;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectHandlerRegionClass {
    Opaque,
    SingleResume,
    FiniteMultiResume,
    EscapingResumption,
    NestedEffectful,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectHandlerRegion {
    pub handler: CpsHandlerId,
    pub effect: typed_ir::Path,
    pub perform: CpsContinuationId,
    pub resume: CpsContinuationId,
    pub resume_shot_kind: Option<CpsShotKind>,
    pub arm_entry: Option<CpsContinuationId>,
    pub class: EffectHandlerRegionClass,
    pub resume_uses: usize,
    pub resume_with_handler_uses: usize,
    pub clone_uses: usize,
    pub nested_performs: usize,
    pub direct_call_uses: usize,
    pub apply_closure_uses: usize,
    pub effectful_terminators: usize,
    pub local_thunk_entries: usize,
    pub resumption_lane_values: usize,
    pub resumption_operand_uses: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectBoundaryKind {
    EffectfulCall,
    EffectfulApply,
    EffectfulForce,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DynamicEffectHandlerCandidate {
    pub caller: String,
    pub boundary: CpsContinuationId,
    pub boundary_kind: EffectBoundaryKind,
    pub boundary_target: Option<String>,
    pub handler: CpsHandlerId,
    pub effect: typed_ir::Path,
    pub arm_entry: CpsContinuationId,
    pub arm_class: EffectHandlerRegionClass,
    pub perform_function: String,
    pub perform: CpsContinuationId,
    pub resume: CpsContinuationId,
    pub resume_shot_kind: Option<CpsShotKind>,
    pub resume_uses: usize,
    pub resume_with_handler_uses: usize,
    pub clone_uses: usize,
    pub nested_performs: usize,
    pub local_thunk_entries: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectResumeActionKind {
    Resume,
    ResumeWithHandler,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectResumeAction {
    pub continuation: CpsContinuationId,
    pub stmt_index: usize,
    pub kind: EffectResumeActionKind,
    pub result: CpsValueId,
    pub resumption: CpsValueId,
    pub arg: CpsValueId,
    pub local_thunk_entry: Option<CpsContinuationId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DynamicEffectRegionPlanClass {
    Opaque,
    FiniteResumeSchedule,
    EscapingResumption,
    NestedEffectful,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DynamicEffectRegionPlan {
    pub caller: String,
    pub boundary: CpsContinuationId,
    pub boundary_kind: EffectBoundaryKind,
    pub boundary_target: Option<String>,
    pub boundary_force_thunk: Option<CpsValueId>,
    pub handler: CpsHandlerId,
    pub effect: typed_ir::Path,
    pub arm_entry: CpsContinuationId,
    pub perform_function: String,
    pub perform: CpsContinuationId,
    pub resume: CpsContinuationId,
    pub resume_shot_kind: Option<CpsShotKind>,
    pub class: DynamicEffectRegionPlanClass,
    pub resume_actions: Vec<EffectResumeAction>,
    pub local_thunk_entries: Vec<CpsContinuationId>,
    pub clone_uses: usize,
    pub nested_performs: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DynamicEffectThunkArgumentPlan {
    pub caller: String,
    pub call_continuation: CpsContinuationId,
    pub call_stmt_index: usize,
    pub callee: String,
    pub callee_boundary: CpsContinuationId,
    pub callee_force_param_index: usize,
    pub thunk: CpsValueId,
    pub thunk_entry: CpsContinuationId,
    pub post_call_force_chain_len: usize,
    pub effect: typed_ir::Path,
    pub region_class: DynamicEffectRegionPlanClass,
    pub resume_actions: Vec<EffectResumeAction>,
    pub clone_uses: usize,
    pub nested_performs: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DynamicEffectThunkSpecializationClass {
    ReadyFinite,
    Blocked,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DynamicEffectThunkSpecializationSeed {
    pub caller: String,
    pub call_continuation: CpsContinuationId,
    pub call_stmt_index: usize,
    pub callee: String,
    pub thunk: CpsValueId,
    pub thunk_entry: CpsContinuationId,
    pub post_call_force_chain_len: usize,
    pub class: DynamicEffectThunkSpecializationClass,
    pub finite_effects: Vec<typed_ir::Path>,
    pub no_resume_effects: Vec<typed_ir::Path>,
    pub blocked_effects: Vec<typed_ir::Path>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DynamicEffectThunkRewriteStrategy {
    DefunctionalizeFiniteHandler,
    CalleeBodyClone,
    Blocked,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DynamicEffectThunkBodyCloneBlocker {
    RecursiveCallee,
    PostCallForceChain,
    CalleeHasHandlers,
    CalleeHasEffectBoundary,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DynamicEffectThunkRewritePlan {
    pub caller: String,
    pub call_continuation: CpsContinuationId,
    pub call_stmt_index: usize,
    pub callee: String,
    pub thunk: CpsValueId,
    pub thunk_entry: CpsContinuationId,
    pub post_call_force_chain_len: usize,
    pub seed_class: DynamicEffectThunkSpecializationClass,
    pub strategy: DynamicEffectThunkRewriteStrategy,
    pub body_clone_blockers: Vec<DynamicEffectThunkBodyCloneBlocker>,
    pub finite_effects: Vec<typed_ir::Path>,
    pub no_resume_effects: Vec<typed_ir::Path>,
    pub blocked_effects: Vec<typed_ir::Path>,
}

pub fn analyze_effect_handler_regions(function: &CpsReprAbiFunction) -> Vec<EffectHandlerRegion> {
    let continuations = function
        .continuations
        .iter()
        .map(|continuation| (continuation.id, continuation))
        .collect::<HashMap<_, _>>();
    let value_lanes = value_lanes(function);
    let handler_arms = function
        .handlers
        .iter()
        .flat_map(|handler| {
            handler
                .arms
                .iter()
                .map(|arm| ((handler.id, arm.effect.clone()), arm.entry))
        })
        .collect::<Vec<_>>();

    let mut regions = Vec::new();
    for continuation in &function.continuations {
        let CpsTerminator::Perform {
            effect,
            resume,
            handler,
            ..
        } = &continuation.terminator
        else {
            continue;
        };
        let arm_entry = handler_arms
            .iter()
            .find(|((arm_handler, arm_effect), _)| {
                arm_handler == handler && effect_matches(arm_effect, effect)
            })
            .map(|(_, entry)| *entry);
        let resume_shot_kind = continuations.get(resume).map(|resume| resume.shot_kind);
        let arm_summary = arm_entry
            .and_then(|entry| summarize_arm_region(entry, &continuations, &value_lanes))
            .unwrap_or_default();
        regions.push(EffectHandlerRegion {
            handler: *handler,
            effect: effect.clone(),
            perform: continuation.id,
            resume: *resume,
            resume_shot_kind,
            arm_entry,
            class: classify_region(arm_entry, resume_shot_kind, &arm_summary),
            resume_uses: arm_summary.resume_uses,
            resume_with_handler_uses: arm_summary.resume_with_handler_uses,
            clone_uses: arm_summary.clone_uses,
            nested_performs: arm_summary.nested_performs,
            direct_call_uses: arm_summary.direct_call_uses,
            apply_closure_uses: arm_summary.apply_closure_uses,
            effectful_terminators: arm_summary.effectful_terminators,
            local_thunk_entries: arm_summary.local_thunk_entries.len(),
            resumption_lane_values: arm_summary.resumption_lane_values,
            resumption_operand_uses: arm_summary.resumption_operand_uses,
        });
    }
    regions
}

pub fn analyze_dynamic_effect_handler_candidates(
    module: &CpsReprAbiModule,
) -> Vec<DynamicEffectHandlerCandidate> {
    let dynamic_performs = dynamic_perform_sites(module);
    if dynamic_performs.is_empty() {
        return Vec::new();
    }
    let all_dynamic_performs = dynamic_performs.iter().collect::<Vec<_>>();
    let dynamic_performs_by_function = dynamic_performs.iter().fold(
        HashMap::<String, Vec<&DynamicPerformSite>>::new(),
        |mut map, site| {
            map.entry(site.function.clone()).or_default().push(site);
            map
        },
    );

    let mut candidates = Vec::new();
    for function in module.functions.iter().chain(&module.roots) {
        let continuations = continuation_table(function);
        let value_lanes = value_lanes(function);
        let handler_arms = function
            .handlers
            .iter()
            .map(|handler| {
                let arms = handler
                    .arms
                    .iter()
                    .map(|arm| {
                        let summary = summarize_arm_region(arm.entry, &continuations, &value_lanes)
                            .unwrap_or_default();
                        HandlerArmSummary {
                            effect: arm.effect.clone(),
                            entry: arm.entry,
                            class: classify_arm_summary(&summary),
                            summary,
                        }
                    })
                    .collect::<Vec<_>>();
                (handler.id, arms)
            })
            .collect::<HashMap<_, _>>();

        for boundary in active_effect_boundaries(function) {
            for handler in &boundary.active_handlers {
                let Some(arms) = handler_arms.get(handler) else {
                    continue;
                };
                for arm in arms {
                    let possible_performs = boundary
                        .target
                        .as_ref()
                        .and_then(|target| dynamic_performs_by_function.get(target))
                        .map(Vec::as_slice)
                        .unwrap_or(all_dynamic_performs.as_slice());
                    for perform in possible_performs
                        .iter()
                        .copied()
                        .filter(|perform| effect_matches(&arm.effect, &perform.effect))
                    {
                        candidates.push(DynamicEffectHandlerCandidate {
                            caller: function.name.clone(),
                            boundary: boundary.continuation,
                            boundary_kind: boundary.kind,
                            boundary_target: boundary.target.clone(),
                            handler: *handler,
                            effect: arm.effect.clone(),
                            arm_entry: arm.entry,
                            arm_class: arm.class,
                            perform_function: perform.function.clone(),
                            perform: perform.perform,
                            resume: perform.resume,
                            resume_shot_kind: perform.resume_shot_kind,
                            resume_uses: arm.summary.resume_uses,
                            resume_with_handler_uses: arm.summary.resume_with_handler_uses,
                            clone_uses: arm.summary.clone_uses,
                            nested_performs: arm.summary.nested_performs,
                            local_thunk_entries: arm.summary.local_thunk_entries.len(),
                        });
                    }
                }
            }
        }
    }
    candidates
}

pub fn analyze_dynamic_effect_region_plans(
    module: &CpsReprAbiModule,
) -> Vec<DynamicEffectRegionPlan> {
    let dynamic_performs = dynamic_perform_sites(module);
    if dynamic_performs.is_empty() {
        return Vec::new();
    }
    let all_dynamic_performs = dynamic_performs.iter().collect::<Vec<_>>();
    let dynamic_performs_by_function = dynamic_performs.iter().fold(
        HashMap::<String, Vec<&DynamicPerformSite>>::new(),
        |mut map, site| {
            map.entry(site.function.clone()).or_default().push(site);
            map
        },
    );

    let mut plans = Vec::new();
    for function in module.functions.iter().chain(&module.roots) {
        let continuations = continuation_table(function);
        let value_lanes = value_lanes(function);
        let handler_arms = function
            .handlers
            .iter()
            .map(|handler| {
                let arms = handler
                    .arms
                    .iter()
                    .map(|arm| {
                        let summary = summarize_arm_region(arm.entry, &continuations, &value_lanes)
                            .unwrap_or_default();
                        HandlerArmSummary {
                            effect: arm.effect.clone(),
                            entry: arm.entry,
                            class: classify_arm_summary(&summary),
                            summary,
                        }
                    })
                    .collect::<Vec<_>>();
                (handler.id, arms)
            })
            .collect::<HashMap<_, _>>();

        for boundary in active_effect_boundaries(function) {
            for handler in &boundary.active_handlers {
                let Some(arms) = handler_arms.get(handler) else {
                    continue;
                };
                for arm in arms {
                    let possible_performs = boundary
                        .target
                        .as_ref()
                        .and_then(|target| dynamic_performs_by_function.get(target))
                        .map(Vec::as_slice)
                        .unwrap_or(all_dynamic_performs.as_slice());
                    for perform in possible_performs
                        .iter()
                        .copied()
                        .filter(|perform| effect_matches(&arm.effect, &perform.effect))
                    {
                        plans.push(DynamicEffectRegionPlan {
                            caller: function.name.clone(),
                            boundary: boundary.continuation,
                            boundary_kind: boundary.kind,
                            boundary_target: boundary.target.clone(),
                            boundary_force_thunk: boundary.force_thunk,
                            handler: *handler,
                            effect: arm.effect.clone(),
                            arm_entry: arm.entry,
                            perform_function: perform.function.clone(),
                            perform: perform.perform,
                            resume: perform.resume,
                            resume_shot_kind: perform.resume_shot_kind,
                            class: classify_dynamic_plan(&arm.summary),
                            resume_actions: arm.summary.resume_actions.clone(),
                            local_thunk_entries: arm.summary.local_thunk_entries.clone(),
                            clone_uses: arm.summary.clone_uses,
                            nested_performs: arm.summary.nested_performs,
                        });
                    }
                }
            }
        }
    }
    plans
}

pub fn analyze_dynamic_effect_thunk_argument_plans(
    module: &CpsReprAbiModule,
) -> Vec<DynamicEffectThunkArgumentPlan> {
    let region_plans = analyze_dynamic_effect_region_plans(module);
    if region_plans.is_empty() {
        return Vec::new();
    }
    let functions = module
        .functions
        .iter()
        .chain(&module.roots)
        .map(|function| (function.name.as_str(), function))
        .collect::<HashMap<_, _>>();
    let region_plans_by_callee = region_plans.iter().fold(
        HashMap::<&str, Vec<&DynamicEffectRegionPlan>>::new(),
        |mut map, plan| {
            map.entry(plan.caller.as_str()).or_default().push(plan);
            map
        },
    );

    let mut thunk_plans = Vec::new();
    for function in module.functions.iter().chain(&module.roots) {
        for continuation in &function.continuations {
            let local_thunks = local_thunk_entries_by_dest(continuation);
            for (stmt_index, stmt) in continuation.stmts.iter().enumerate() {
                let CpsStmt::DirectCall { dest, target, args } = stmt else {
                    continue;
                };
                let Some(callee_region_plans) = region_plans_by_callee.get(target.as_str()) else {
                    continue;
                };
                let Some(callee) = functions.get(target.as_str()) else {
                    continue;
                };
                for region_plan in callee_region_plans {
                    if region_plan.boundary_kind != EffectBoundaryKind::EffectfulForce {
                        continue;
                    }
                    let Some(force_param_index) = force_thunk_param_index(
                        callee,
                        region_plan.boundary,
                        region_plan.boundary_force_thunk,
                    ) else {
                        continue;
                    };
                    let Some(thunk) = args.get(force_param_index).copied() else {
                        continue;
                    };
                    let Some(thunk_entry) = local_thunks.get(&thunk).copied() else {
                        continue;
                    };
                    thunk_plans.push(DynamicEffectThunkArgumentPlan {
                        caller: function.name.clone(),
                        call_continuation: continuation.id,
                        call_stmt_index: stmt_index,
                        callee: target.clone(),
                        callee_boundary: region_plan.boundary,
                        callee_force_param_index: force_param_index,
                        thunk,
                        thunk_entry,
                        post_call_force_chain_len: immediate_force_chain_len(
                            &continuation.stmts,
                            stmt_index + 1,
                            *dest,
                        ),
                        effect: region_plan.effect.clone(),
                        region_class: region_plan.class,
                        resume_actions: region_plan.resume_actions.clone(),
                        clone_uses: region_plan.clone_uses,
                        nested_performs: region_plan.nested_performs,
                    });
                }
            }
        }
    }
    thunk_plans
}

pub fn analyze_dynamic_effect_thunk_specialization_seeds(
    module: &CpsReprAbiModule,
) -> Vec<DynamicEffectThunkSpecializationSeed> {
    let mut groups = HashMap::<ThunkSpecializationKey, Vec<DynamicEffectThunkArgumentPlan>>::new();
    for plan in analyze_dynamic_effect_thunk_argument_plans(module) {
        groups
            .entry(ThunkSpecializationKey::from(&plan))
            .or_default()
            .push(plan);
    }

    let mut seeds = groups
        .into_iter()
        .map(|(key, plans)| {
            let mut finite_effects = Vec::new();
            let mut no_resume_effects = Vec::new();
            let mut blocked_effects = Vec::new();
            for plan in plans {
                if plan.region_class == DynamicEffectRegionPlanClass::FiniteResumeSchedule {
                    finite_effects.push(plan.effect);
                } else if plan.region_class == DynamicEffectRegionPlanClass::Opaque
                    && plan.resume_actions.is_empty()
                    && plan.clone_uses == 0
                    && plan.nested_performs == 0
                {
                    no_resume_effects.push(plan.effect);
                } else {
                    blocked_effects.push(plan.effect);
                }
            }
            let class = if !finite_effects.is_empty() && blocked_effects.is_empty() {
                DynamicEffectThunkSpecializationClass::ReadyFinite
            } else {
                DynamicEffectThunkSpecializationClass::Blocked
            };
            DynamicEffectThunkSpecializationSeed {
                caller: key.caller,
                call_continuation: key.call_continuation,
                call_stmt_index: key.call_stmt_index,
                callee: key.callee,
                thunk: key.thunk,
                thunk_entry: key.thunk_entry,
                post_call_force_chain_len: key.post_call_force_chain_len,
                class,
                finite_effects,
                no_resume_effects,
                blocked_effects,
            }
        })
        .collect::<Vec<_>>();
    seeds.sort_by(|left, right| {
        left.caller
            .cmp(&right.caller)
            .then(left.call_continuation.0.cmp(&right.call_continuation.0))
            .then(left.call_stmt_index.cmp(&right.call_stmt_index))
    });
    seeds
}

pub fn analyze_dynamic_effect_thunk_rewrite_plans(
    module: &CpsReprAbiModule,
) -> Vec<DynamicEffectThunkRewritePlan> {
    let functions = module
        .functions
        .iter()
        .chain(&module.roots)
        .map(|function| (function.name.as_str(), function))
        .collect::<HashMap<_, _>>();
    analyze_dynamic_effect_thunk_specialization_seeds(module)
        .into_iter()
        .map(|seed| {
            let body_clone_blockers =
                body_clone_blockers_for_dynamic_effect_thunk_seed(&seed, &functions);
            let strategy =
                classify_dynamic_effect_thunk_rewrite_strategy(&seed, &body_clone_blockers);
            DynamicEffectThunkRewritePlan {
                caller: seed.caller,
                call_continuation: seed.call_continuation,
                call_stmt_index: seed.call_stmt_index,
                callee: seed.callee,
                thunk: seed.thunk,
                thunk_entry: seed.thunk_entry,
                post_call_force_chain_len: seed.post_call_force_chain_len,
                seed_class: seed.class,
                strategy,
                body_clone_blockers,
                finite_effects: seed.finite_effects,
                no_resume_effects: seed.no_resume_effects,
                blocked_effects: seed.blocked_effects,
            }
        })
        .collect()
}

pub fn maybe_trace_effect_handler_regions(
    function: &CpsReprAbiFunction,
    regions: &[EffectHandlerRegion],
) {
    let Some(level) = std::env::var_os("YULANG_CPS_EFFECT_REGION_TRACE") else {
        return;
    };
    let dump_continuations = level == "2";
    let continuations = function
        .continuations
        .iter()
        .map(|continuation| (continuation.id, continuation))
        .collect::<HashMap<_, _>>();
    for region in regions {
        eprintln!(
            "[CPS-EFFECT-REGION] function={} handler={:?} effect={} perform={:?} resume={:?} resume_shot={:?} arm={:?} class={:?} resume={} resume_with_handler={} clone={} nested={} direct_call={} apply_closure={} effectful_terms={} local_thunks={} resumption_lane_values={} resumption_operand_uses={}",
            function.name,
            region.handler,
            format_path(&region.effect),
            region.perform,
            region.resume,
            region.resume_shot_kind,
            region.arm_entry,
            region.class,
            region.resume_uses,
            region.resume_with_handler_uses,
            region.clone_uses,
            region.nested_performs,
            region.direct_call_uses,
            region.apply_closure_uses,
            region.effectful_terminators,
            region.local_thunk_entries,
            region.resumption_lane_values,
            region.resumption_operand_uses,
        );
        if dump_continuations {
            trace_reachable_arm_continuations(region.arm_entry, &continuations);
        }
    }
}

pub fn maybe_trace_dynamic_effect_handler_candidates(candidates: &[DynamicEffectHandlerCandidate]) {
    if std::env::var_os("YULANG_CPS_EFFECT_REGION_TRACE").is_none() {
        return;
    }
    for candidate in candidates {
        eprintln!(
            "[CPS-DYNAMIC-EFFECT-CANDIDATE] caller={} boundary={:?} boundary_kind={:?} boundary_target={:?} handler={:?} effect={} arm={:?} arm_class={:?} perform_function={} perform={:?} resume={:?} resume_shot={:?} resume={} resume_with_handler={} clone={} nested={} local_thunks={}",
            candidate.caller,
            candidate.boundary,
            candidate.boundary_kind,
            candidate.boundary_target,
            candidate.handler,
            format_path(&candidate.effect),
            candidate.arm_entry,
            candidate.arm_class,
            candidate.perform_function,
            candidate.perform,
            candidate.resume,
            candidate.resume_shot_kind,
            candidate.resume_uses,
            candidate.resume_with_handler_uses,
            candidate.clone_uses,
            candidate.nested_performs,
            candidate.local_thunk_entries,
        );
    }
}

pub fn maybe_trace_dynamic_effect_region_plans(plans: &[DynamicEffectRegionPlan]) {
    if std::env::var_os("YULANG_CPS_EFFECT_REGION_TRACE").is_none() {
        return;
    }
    for plan in plans {
        eprintln!(
            "[CPS-DYNAMIC-EFFECT-PLAN] caller={} boundary={:?} boundary_kind={:?} boundary_target={:?} boundary_force_thunk={:?} handler={:?} effect={} arm={:?} perform_function={} perform={:?} resume={:?} resume_shot={:?} class={:?} actions={} local_thunks={} clone={} nested={}",
            plan.caller,
            plan.boundary,
            plan.boundary_kind,
            plan.boundary_target,
            plan.boundary_force_thunk,
            plan.handler,
            format_path(&plan.effect),
            plan.arm_entry,
            plan.perform_function,
            plan.perform,
            plan.resume,
            plan.resume_shot_kind,
            plan.class,
            plan.resume_actions.len(),
            plan.local_thunk_entries.len(),
            plan.clone_uses,
            plan.nested_performs,
        );
        for action in &plan.resume_actions {
            eprintln!(
                "[CPS-DYNAMIC-EFFECT-PLAN-ACTION] continuation={:?} stmt_index={} kind={:?} result={:?} resumption={:?} arg={:?} local_thunk={:?}",
                action.continuation,
                action.stmt_index,
                action.kind,
                action.result,
                action.resumption,
                action.arg,
                action.local_thunk_entry,
            );
        }
    }
}

pub fn maybe_trace_dynamic_effect_thunk_argument_plans(plans: &[DynamicEffectThunkArgumentPlan]) {
    if std::env::var_os("YULANG_CPS_EFFECT_REGION_TRACE").is_none() {
        return;
    }
    for plan in plans {
        eprintln!(
            "[CPS-DYNAMIC-EFFECT-THUNK-ARG] caller={} call={:?} stmt_index={} callee={} callee_boundary={:?} force_param={} thunk={:?} thunk_entry={:?} post_call_force_chain={} effect={} region_class={:?} actions={}",
            plan.caller,
            plan.call_continuation,
            plan.call_stmt_index,
            plan.callee,
            plan.callee_boundary,
            plan.callee_force_param_index,
            plan.thunk,
            plan.thunk_entry,
            plan.post_call_force_chain_len,
            format_path(&plan.effect),
            plan.region_class,
            plan.resume_actions.len(),
        );
    }
}

pub fn maybe_trace_dynamic_effect_thunk_specialization_seeds(
    seeds: &[DynamicEffectThunkSpecializationSeed],
) {
    if std::env::var_os("YULANG_CPS_EFFECT_REGION_TRACE").is_none() {
        return;
    }
    for seed in seeds {
        eprintln!(
            "[CPS-DYNAMIC-EFFECT-THUNK-SEED] caller={} call={:?} stmt_index={} callee={} thunk={:?} thunk_entry={:?} post_call_force_chain={} class={:?} finite_effects={} no_resume_effects={} blocked_effects={}",
            seed.caller,
            seed.call_continuation,
            seed.call_stmt_index,
            seed.callee,
            seed.thunk,
            seed.thunk_entry,
            seed.post_call_force_chain_len,
            seed.class,
            format_paths(&seed.finite_effects),
            format_paths(&seed.no_resume_effects),
            format_paths(&seed.blocked_effects),
        );
    }
}

pub fn maybe_trace_dynamic_effect_thunk_rewrite_plans(plans: &[DynamicEffectThunkRewritePlan]) {
    if std::env::var_os("YULANG_CPS_EFFECT_REGION_TRACE").is_none() {
        return;
    }
    for plan in plans {
        eprintln!(
            "[CPS-DYNAMIC-EFFECT-THUNK-REWRITE] caller={} call={:?} stmt_index={} callee={} thunk={:?} thunk_entry={:?} post_call_force_chain={} seed_class={:?} strategy={:?} body_clone_blockers={} finite_effects={} no_resume_effects={} blocked_effects={}",
            plan.caller,
            plan.call_continuation,
            plan.call_stmt_index,
            plan.callee,
            plan.thunk,
            plan.thunk_entry,
            plan.post_call_force_chain_len,
            plan.seed_class,
            plan.strategy,
            format_body_clone_blockers(&plan.body_clone_blockers),
            format_paths(&plan.finite_effects),
            format_paths(&plan.no_resume_effects),
            format_paths(&plan.blocked_effects),
        );
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ThunkSpecializationKey {
    caller: String,
    call_continuation: CpsContinuationId,
    call_stmt_index: usize,
    callee: String,
    thunk: CpsValueId,
    thunk_entry: CpsContinuationId,
    post_call_force_chain_len: usize,
}

impl From<&DynamicEffectThunkArgumentPlan> for ThunkSpecializationKey {
    fn from(plan: &DynamicEffectThunkArgumentPlan) -> Self {
        Self {
            caller: plan.caller.clone(),
            call_continuation: plan.call_continuation,
            call_stmt_index: plan.call_stmt_index,
            callee: plan.callee.clone(),
            thunk: plan.thunk,
            thunk_entry: plan.thunk_entry,
            post_call_force_chain_len: plan.post_call_force_chain_len,
        }
    }
}

#[derive(Debug, Clone, Default)]
struct ArmRegionSummary {
    resume_uses: usize,
    resume_with_handler_uses: usize,
    clone_uses: usize,
    nested_performs: usize,
    direct_call_uses: usize,
    apply_closure_uses: usize,
    effectful_terminators: usize,
    local_thunk_entries: Vec<CpsContinuationId>,
    resume_actions: Vec<EffectResumeAction>,
    resumption_lane_values: usize,
    resumption_operand_uses: usize,
}

#[derive(Debug, Clone)]
struct HandlerArmSummary {
    effect: typed_ir::Path,
    entry: CpsContinuationId,
    class: EffectHandlerRegionClass,
    summary: ArmRegionSummary,
}

#[derive(Debug, Clone)]
struct DynamicPerformSite {
    function: String,
    effect: typed_ir::Path,
    perform: CpsContinuationId,
    resume: CpsContinuationId,
    resume_shot_kind: Option<CpsShotKind>,
}

#[derive(Debug, Clone)]
struct ActiveEffectBoundary {
    continuation: CpsContinuationId,
    kind: EffectBoundaryKind,
    target: Option<String>,
    force_thunk: Option<CpsValueId>,
    active_handlers: Vec<CpsHandlerId>,
}

fn dynamic_perform_sites(module: &CpsReprAbiModule) -> Vec<DynamicPerformSite> {
    let mut sites = Vec::new();
    for function in module.functions.iter().chain(&module.roots) {
        let continuations = continuation_table(function);
        for continuation in &function.continuations {
            let CpsTerminator::Perform {
                effect,
                resume,
                handler,
                ..
            } = &continuation.terminator
            else {
                continue;
            };
            if !is_dynamic_handler(*handler) {
                continue;
            }
            sites.push(DynamicPerformSite {
                function: function.name.clone(),
                effect: effect.clone(),
                perform: continuation.id,
                resume: *resume,
                resume_shot_kind: continuations.get(resume).map(|resume| resume.shot_kind),
            });
        }
    }
    sites
}

fn active_effect_boundaries(function: &CpsReprAbiFunction) -> Vec<ActiveEffectBoundary> {
    let continuations = continuation_table(function);
    let mut boundaries = Vec::new();
    let mut active_by_continuation = HashMap::<CpsContinuationId, Vec<CpsHandlerId>>::new();
    let mut queue = VecDeque::from([(function.entry, Vec::new())]);
    while let Some((id, incoming_active)) = queue.pop_front() {
        let Some(continuation) = continuations.get(&id) else {
            continue;
        };
        let changed = merge_active_handlers(
            active_by_continuation.entry(id).or_default(),
            &incoming_active,
        );
        if !changed && !incoming_active.is_empty() {
            continue;
        }

        let mut active = active_by_continuation.get(&id).cloned().unwrap_or_default();
        for stmt in &continuation.stmts {
            match stmt {
                CpsStmt::InstallHandler { handler, .. } => push_handler(&mut active, *handler),
                CpsStmt::UninstallHandler { handler } => {
                    active.retain(|active_handler| active_handler != handler);
                }
                _ => {}
            }
        }
        match &continuation.terminator {
            CpsTerminator::Continue { target, .. } => {
                queue.push_back((*target, active));
            }
            CpsTerminator::Branch {
                then_cont,
                else_cont,
                ..
            } => {
                queue.push_back((*then_cont, active.clone()));
                queue.push_back((*else_cont, active));
            }
            CpsTerminator::EffectfulCall { target, .. } => {
                if !active.is_empty() {
                    boundaries.push(ActiveEffectBoundary {
                        continuation: id,
                        kind: EffectBoundaryKind::EffectfulCall,
                        target: Some(target.clone()),
                        force_thunk: None,
                        active_handlers: active,
                    });
                }
            }
            CpsTerminator::EffectfulApply { .. } => {
                if !active.is_empty() {
                    boundaries.push(ActiveEffectBoundary {
                        continuation: id,
                        kind: EffectBoundaryKind::EffectfulApply,
                        target: None,
                        force_thunk: None,
                        active_handlers: active,
                    });
                }
            }
            CpsTerminator::EffectfulForce { thunk, .. } => {
                if !active.is_empty() {
                    boundaries.push(ActiveEffectBoundary {
                        continuation: id,
                        kind: EffectBoundaryKind::EffectfulForce,
                        target: None,
                        force_thunk: Some(*thunk),
                        active_handlers: active,
                    });
                }
            }
            CpsTerminator::Return(_) | CpsTerminator::Perform { .. } => {}
        }
    }
    boundaries
}

fn continuation_table(
    function: &CpsReprAbiFunction,
) -> HashMap<CpsContinuationId, &CpsReprAbiContinuation> {
    function
        .continuations
        .iter()
        .map(|continuation| (continuation.id, continuation))
        .collect()
}

fn local_thunk_entries_by_dest(
    continuation: &CpsReprAbiContinuation,
) -> HashMap<CpsValueId, CpsContinuationId> {
    continuation
        .stmts
        .iter()
        .filter_map(|stmt| match stmt {
            CpsStmt::MakeThunk { dest, entry } => Some((*dest, *entry)),
            _ => None,
        })
        .collect()
}

fn immediate_force_chain_len(stmts: &[CpsStmt], start: usize, value: CpsValueId) -> usize {
    let mut len = 0;
    let mut current = value;
    for stmt in &stmts[start..] {
        let CpsStmt::ForceThunk { dest, thunk } = stmt else {
            break;
        };
        if *thunk != current {
            break;
        }
        current = *dest;
        len += 1;
    }
    len
}

fn force_thunk_param_index(
    function: &CpsReprAbiFunction,
    boundary: CpsContinuationId,
    force_thunk: Option<CpsValueId>,
) -> Option<usize> {
    let force_thunk = force_thunk?;
    let continuations = continuation_table(function);
    let boundary = continuations.get(&boundary)?;
    let mut source = force_thunk;
    for stmt in boundary.stmts.iter().rev() {
        let CpsStmt::AddThunkBoundary { dest, thunk, .. } = stmt else {
            continue;
        };
        if *dest == source {
            source = *thunk;
        }
    }
    function
        .params
        .iter()
        .position(|param| param.value == source)
}

fn summarize_arm_region(
    entry: CpsContinuationId,
    continuations: &HashMap<CpsContinuationId, &CpsReprAbiContinuation>,
    value_lanes: &HashMap<crate::cps_ir::CpsValueId, CpsReprAbiLane>,
) -> Option<ArmRegionSummary> {
    let mut summary = ArmRegionSummary::default();
    let mut seen = HashSet::new();
    let mut queue = VecDeque::from([(entry, None)]);
    while let Some((id, local_thunk_entry)) = queue.pop_front() {
        if !seen.insert(id) {
            continue;
        }
        let continuation = continuations.get(&id)?;
        summary.resumption_lane_values += continuation
            .params
            .iter()
            .filter(|value| value.lane == CpsReprAbiLane::ResumptionPtr)
            .count();
        summary.resumption_lane_values += continuation
            .environment
            .iter()
            .filter(|slot| slot.lane == CpsReprAbiLane::ResumptionPtr)
            .count();
        for (stmt_index, stmt) in continuation.stmts.iter().enumerate() {
            match stmt {
                CpsStmt::Resume {
                    dest,
                    resumption,
                    arg,
                } => {
                    summary.resume_uses += 1;
                    summary.resume_actions.push(EffectResumeAction {
                        continuation: id,
                        stmt_index,
                        kind: EffectResumeActionKind::Resume,
                        result: *dest,
                        resumption: *resumption,
                        arg: *arg,
                        local_thunk_entry,
                    });
                }
                CpsStmt::ResumeWithHandler {
                    dest,
                    resumption,
                    arg,
                    ..
                } => {
                    summary.resume_with_handler_uses += 1;
                    summary.resume_actions.push(EffectResumeAction {
                        continuation: id,
                        stmt_index,
                        kind: EffectResumeActionKind::ResumeWithHandler,
                        result: *dest,
                        resumption: *resumption,
                        arg: *arg,
                        local_thunk_entry,
                    });
                }
                CpsStmt::CloneContinuation { .. } => summary.clone_uses += 1,
                CpsStmt::DirectCall { .. } => summary.direct_call_uses += 1,
                CpsStmt::ApplyClosure { .. } => summary.apply_closure_uses += 1,
                CpsStmt::MakeThunk { entry, .. } => {
                    summary.local_thunk_entries.push(*entry);
                    queue.push_back((*entry, Some(*entry)));
                }
                _ => {}
            }
            summary.resumption_operand_uses += stmt_operands(stmt)
                .into_iter()
                .filter(|value| {
                    value_lanes
                        .get(value)
                        .is_some_and(|lane| *lane == CpsReprAbiLane::ResumptionPtr)
                })
                .count();
        }
        match &continuation.terminator {
            CpsTerminator::Continue { target, .. } => queue.push_back((*target, local_thunk_entry)),
            CpsTerminator::Branch {
                then_cont,
                else_cont,
                ..
            } => {
                queue.push_back((*then_cont, local_thunk_entry));
                queue.push_back((*else_cont, local_thunk_entry));
            }
            CpsTerminator::Perform { .. }
            | CpsTerminator::EffectfulCall { .. }
            | CpsTerminator::EffectfulApply { .. }
            | CpsTerminator::EffectfulForce { .. } => {
                summary.nested_performs += 1;
                summary.effectful_terminators += 1;
            }
            CpsTerminator::Return(_) => {}
        }
    }
    Some(summary)
}

fn merge_active_handlers(active: &mut Vec<CpsHandlerId>, incoming: &[CpsHandlerId]) -> bool {
    let before = active.len();
    for handler in incoming {
        push_handler(active, *handler);
    }
    active.len() != before
}

fn push_handler(active: &mut Vec<CpsHandlerId>, handler: CpsHandlerId) {
    if !active.contains(&handler) {
        active.push(handler);
    }
}

fn is_dynamic_handler(handler: CpsHandlerId) -> bool {
    handler.0 == usize::MAX
}

fn value_lanes(
    function: &CpsReprAbiFunction,
) -> HashMap<crate::cps_ir::CpsValueId, CpsReprAbiLane> {
    let mut lanes = HashMap::new();
    for value in &function.params {
        lanes.insert(value.value, value.lane);
    }
    for continuation in &function.continuations {
        for value in &continuation.params {
            lanes.insert(value.value, value.lane);
        }
        for slot in &continuation.environment {
            lanes.insert(slot.value, slot.lane);
        }
    }
    lanes
}

fn trace_reachable_arm_continuations(
    entry: Option<CpsContinuationId>,
    continuations: &HashMap<CpsContinuationId, &CpsReprAbiContinuation>,
) {
    let Some(entry) = entry else {
        return;
    };
    let mut seen = HashSet::new();
    let mut queue = VecDeque::from([entry]);
    while let Some(id) = queue.pop_front() {
        if !seen.insert(id) {
            continue;
        }
        let Some(continuation) = continuations.get(&id) else {
            continue;
        };
        eprintln!(
            "[CPS-EFFECT-REGION-CONT] id={:?} params={:?} env={:?} shot={:?} stmts={:?} term={:?}",
            continuation.id,
            continuation.params,
            continuation.environment,
            continuation.shot_kind,
            continuation.stmts,
            continuation.terminator,
        );
        match &continuation.terminator {
            CpsTerminator::Continue { target, .. } => queue.push_back(*target),
            CpsTerminator::Branch {
                then_cont,
                else_cont,
                ..
            } => {
                queue.push_back(*then_cont);
                queue.push_back(*else_cont);
            }
            _ => {}
        }
    }
}

fn stmt_operands(stmt: &CpsStmt) -> Vec<crate::cps_ir::CpsValueId> {
    match stmt {
        CpsStmt::Literal { .. } | CpsStmt::FreshGuard { .. } => Vec::new(),
        CpsStmt::PeekGuard { .. } => Vec::new(),
        CpsStmt::FindGuard { guard, .. } => vec![*guard],
        CpsStmt::MakeThunk { .. }
        | CpsStmt::MakeClosure { .. }
        | CpsStmt::MakeRecursiveClosure { .. } => Vec::new(),
        CpsStmt::AddThunkBoundary { thunk, guard, .. } => vec![*thunk, *guard],
        CpsStmt::ForceThunk { thunk, .. } => vec![*thunk],
        CpsStmt::Tuple { items, .. } => items.clone(),
        CpsStmt::Record { base, fields, .. } => base
            .iter()
            .copied()
            .chain(fields.iter().map(|field| field.value))
            .collect(),
        CpsStmt::RecordWithoutFields { base, .. } => vec![*base],
        CpsStmt::Variant { value, .. } => value.iter().copied().collect(),
        CpsStmt::Select { base, .. }
        | CpsStmt::RecordHasField { base, .. }
        | CpsStmt::VariantTagEq { variant: base, .. }
        | CpsStmt::VariantPayload { variant: base, .. } => vec![*base],
        CpsStmt::SelectWithDefault { base, default, .. } => vec![*base, *default],
        CpsStmt::TupleGet { tuple, .. } => vec![*tuple],
        CpsStmt::Primitive { args, .. } | CpsStmt::DirectCall { args, .. } => args.clone(),
        CpsStmt::ApplyClosure { closure, arg, .. } => vec![*closure, *arg],
        CpsStmt::CloneContinuation { source, .. } => vec![*source],
        CpsStmt::Resume {
            resumption, arg, ..
        } => vec![*resumption, *arg],
        CpsStmt::ResumeWithHandler {
            resumption,
            arg,
            envs,
            ..
        } => std::iter::once(*resumption)
            .chain(std::iter::once(*arg))
            .chain(
                envs.iter()
                    .flat_map(|env| env.values.iter().chain(&env.targets))
                    .copied(),
            )
            .collect(),
        CpsStmt::InstallHandler { envs, .. } => envs
            .iter()
            .flat_map(|env| env.values.iter().chain(&env.targets))
            .copied()
            .collect(),
        CpsStmt::UninstallHandler { .. } => Vec::new(),
    }
}

fn body_clone_blockers_for_dynamic_effect_thunk_seed(
    seed: &DynamicEffectThunkSpecializationSeed,
    functions: &HashMap<&str, &CpsReprAbiFunction>,
) -> Vec<DynamicEffectThunkBodyCloneBlocker> {
    let mut blockers = Vec::new();
    if seed.caller == seed.callee {
        blockers.push(DynamicEffectThunkBodyCloneBlocker::RecursiveCallee);
    }
    if seed.post_call_force_chain_len > 0 {
        blockers.push(DynamicEffectThunkBodyCloneBlocker::PostCallForceChain);
    }
    if let Some(callee) = functions.get(seed.callee.as_str()) {
        if !callee.handlers.is_empty() {
            blockers.push(DynamicEffectThunkBodyCloneBlocker::CalleeHasHandlers);
        }
        if function_has_effect_boundary(callee) {
            blockers.push(DynamicEffectThunkBodyCloneBlocker::CalleeHasEffectBoundary);
        }
    }
    blockers
}

fn classify_dynamic_effect_thunk_rewrite_strategy(
    seed: &DynamicEffectThunkSpecializationSeed,
    body_clone_blockers: &[DynamicEffectThunkBodyCloneBlocker],
) -> DynamicEffectThunkRewriteStrategy {
    if seed.class != DynamicEffectThunkSpecializationClass::ReadyFinite {
        return DynamicEffectThunkRewriteStrategy::Blocked;
    }
    if seed.finite_effects.is_empty() {
        return DynamicEffectThunkRewriteStrategy::Blocked;
    }
    if body_clone_blockers.is_empty() {
        return DynamicEffectThunkRewriteStrategy::CalleeBodyClone;
    }
    DynamicEffectThunkRewriteStrategy::DefunctionalizeFiniteHandler
}

fn function_has_effect_boundary(function: &CpsReprAbiFunction) -> bool {
    function.continuations.iter().any(|continuation| {
        matches!(
            continuation.terminator,
            CpsTerminator::EffectfulCall { .. }
                | CpsTerminator::EffectfulApply { .. }
                | CpsTerminator::EffectfulForce { .. }
        )
    })
}

fn format_body_clone_blockers(blockers: &[DynamicEffectThunkBodyCloneBlocker]) -> String {
    blockers
        .iter()
        .map(|blocker| match blocker {
            DynamicEffectThunkBodyCloneBlocker::RecursiveCallee => "recursive_callee",
            DynamicEffectThunkBodyCloneBlocker::PostCallForceChain => "post_call_force_chain",
            DynamicEffectThunkBodyCloneBlocker::CalleeHasHandlers => "callee_has_handlers",
            DynamicEffectThunkBodyCloneBlocker::CalleeHasEffectBoundary => {
                "callee_has_effect_boundary"
            }
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn format_path(path: &typed_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn format_paths(paths: &[typed_ir::Path]) -> String {
    paths.iter().map(format_path).collect::<Vec<_>>().join(",")
}

fn effect_matches(allowed: &typed_ir::Path, effect: &typed_ir::Path) -> bool {
    if effect.segments.starts_with(&allowed.segments) {
        return true;
    }
    if allowed.segments.len() > 1
        && effect.segments.len() == allowed.segments.len()
        && effect.segments[..effect.segments.len() - 1]
            == allowed.segments[..allowed.segments.len() - 1]
        && effect_segment_matches(
            &allowed.segments[allowed.segments.len() - 1],
            &effect.segments[effect.segments.len() - 1],
        )
    {
        return true;
    }
    effect
        .segments
        .iter()
        .enumerate()
        .skip(1)
        .any(|(index, _)| effect.segments[index..].starts_with(&allowed.segments))
}

fn effect_segment_matches(allowed: &typed_ir::Name, effect: &typed_ir::Name) -> bool {
    allowed == effect
        || effect
            .0
            .strip_suffix("#effect")
            .is_some_and(|base| base == allowed.0)
}

fn classify_region(
    arm_entry: Option<CpsContinuationId>,
    resume_shot_kind: Option<CpsShotKind>,
    summary: &ArmRegionSummary,
) -> EffectHandlerRegionClass {
    if arm_entry.is_none() || resume_shot_kind.is_none() {
        return EffectHandlerRegionClass::Opaque;
    }
    if summary.clone_uses > 0 {
        return EffectHandlerRegionClass::EscapingResumption;
    }
    if summary.nested_performs > 0 {
        return EffectHandlerRegionClass::NestedEffectful;
    }
    let resume_uses = summary.resume_uses + summary.resume_with_handler_uses;
    match resume_uses {
        1 => EffectHandlerRegionClass::SingleResume,
        2.. => EffectHandlerRegionClass::FiniteMultiResume,
        0 => EffectHandlerRegionClass::Opaque,
    }
}

fn classify_arm_summary(summary: &ArmRegionSummary) -> EffectHandlerRegionClass {
    if summary.clone_uses > 0 {
        return EffectHandlerRegionClass::EscapingResumption;
    }
    if summary.nested_performs > 0 {
        return EffectHandlerRegionClass::NestedEffectful;
    }
    match summary.resume_uses + summary.resume_with_handler_uses {
        1 => EffectHandlerRegionClass::SingleResume,
        2.. => EffectHandlerRegionClass::FiniteMultiResume,
        0 => EffectHandlerRegionClass::Opaque,
    }
}

fn classify_dynamic_plan(summary: &ArmRegionSummary) -> DynamicEffectRegionPlanClass {
    if summary.clone_uses > 0 {
        return DynamicEffectRegionPlanClass::EscapingResumption;
    }
    if summary.nested_performs > 0 {
        return DynamicEffectRegionPlanClass::NestedEffectful;
    }
    if summary.resume_actions.is_empty() {
        return DynamicEffectRegionPlanClass::Opaque;
    }
    DynamicEffectRegionPlanClass::FiniteResumeSchedule
}

#[cfg(test)]
mod tests {
    use crate::cps_ir::{CpsLiteral, CpsValueId};
    use crate::cps_repr::CpsReprAbiLane;
    use crate::cps_repr_abi::{CpsReprAbiHandler, CpsReprAbiHandlerArm, CpsReprAbiValue};

    use super::*;

    #[test]
    fn classifies_structural_finite_multi_resume_region() {
        let effect = path("op");
        let function = function_with_arm_stmts(
            effect.clone(),
            vec![
                CpsStmt::Resume {
                    dest: CpsValueId(10),
                    resumption: CpsValueId(2),
                    arg: CpsValueId(0),
                },
                CpsStmt::Resume {
                    dest: CpsValueId(11),
                    resumption: CpsValueId(2),
                    arg: CpsValueId(1),
                },
            ],
            CpsTerminator::Return(CpsValueId(11)),
        );

        let regions = analyze_effect_handler_regions(&function);

        assert_eq!(regions.len(), 1);
        assert_eq!(regions[0].effect, effect);
        assert_eq!(
            regions[0].class,
            EffectHandlerRegionClass::FiniteMultiResume
        );
        assert_eq!(regions[0].resume_uses, 2);
    }

    #[test]
    fn classifies_cloned_resumption_as_escaping() {
        let function = function_with_arm_stmts(
            path("op"),
            vec![CpsStmt::CloneContinuation {
                dest: CpsValueId(12),
                source: CpsValueId(2),
            }],
            CpsTerminator::Return(CpsValueId(12)),
        );

        let regions = analyze_effect_handler_regions(&function);

        assert_eq!(
            regions[0].class,
            EffectHandlerRegionClass::EscapingResumption
        );
        assert_eq!(regions[0].clone_uses, 1);
    }

    #[test]
    fn classifies_nested_effectful_arm_as_nested_effectful() {
        let function = function_with_arm_stmts(
            path("op"),
            Vec::new(),
            CpsTerminator::EffectfulCall {
                target: "effectful".to_string(),
                args: Vec::new(),
                resume: CpsContinuationId(3),
            },
        );

        let regions = analyze_effect_handler_regions(&function);

        assert_eq!(regions[0].class, EffectHandlerRegionClass::NestedEffectful);
        assert_eq!(regions[0].nested_performs, 1);
    }

    #[test]
    fn links_dynamic_perform_to_installed_effectful_call_handler() {
        let effect = path("op");
        let absolute_effect = path_segments(&["std", "effect", "op"]);
        let module = CpsReprAbiModule {
            functions: vec![callee_with_dynamic_perform("callee", absolute_effect)],
            roots: vec![caller_with_effectful_call_handler(
                "root",
                "callee",
                effect.clone(),
            )],
        };

        let candidates = analyze_dynamic_effect_handler_candidates(&module);

        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].caller, "root");
        assert_eq!(
            candidates[0].boundary_kind,
            EffectBoundaryKind::EffectfulCall
        );
        assert_eq!(candidates[0].boundary_target, Some("callee".to_string()));
        assert_eq!(candidates[0].effect, effect);
        assert_eq!(candidates[0].perform_function, "callee");
        assert_eq!(
            candidates[0].arm_class,
            EffectHandlerRegionClass::SingleResume
        );
    }

    #[test]
    fn ignores_dynamic_perform_with_unmatched_effect() {
        let module = CpsReprAbiModule {
            functions: vec![callee_with_dynamic_perform("callee", path("other"))],
            roots: vec![caller_with_effectful_call_handler(
                "root",
                "callee",
                path("op"),
            )],
        };

        let candidates = analyze_dynamic_effect_handler_candidates(&module);

        assert!(candidates.is_empty());
    }

    #[test]
    fn follows_local_thunk_entries_in_handler_arm_summary() {
        let function = function_with_arm_thunk_resumes(path("op"));

        let regions = analyze_effect_handler_regions(&function);

        assert_eq!(
            regions[0].class,
            EffectHandlerRegionClass::FiniteMultiResume
        );
        assert_eq!(regions[0].resume_uses, 2);
        assert_eq!(regions[0].local_thunk_entries, 2);
    }

    #[test]
    fn builds_dynamic_finite_resume_schedule_plan() {
        let module = CpsReprAbiModule {
            functions: vec![callee_with_dynamic_perform(
                "callee",
                path_segments(&["std", "effect", "op"]),
            )],
            roots: vec![caller_with_effectful_call_handler_thunk_resumes(
                "root",
                "callee",
                path("op"),
            )],
        };

        let plans = analyze_dynamic_effect_region_plans(&module);

        assert_eq!(plans.len(), 1);
        assert_eq!(
            plans[0].class,
            DynamicEffectRegionPlanClass::FiniteResumeSchedule
        );
        assert_eq!(
            plans[0]
                .resume_actions
                .iter()
                .map(|action| action.local_thunk_entry)
                .collect::<Vec<_>>(),
            vec![Some(CpsContinuationId(3)), Some(CpsContinuationId(4))]
        );
        assert_eq!(
            plans[0].local_thunk_entries,
            vec![CpsContinuationId(3), CpsContinuationId(4)]
        );
    }

    #[test]
    fn links_direct_call_thunk_argument_to_dynamic_region_plan() {
        let module = CpsReprAbiModule {
            functions: vec![
                callee_with_dynamic_perform("producer", path_segments(&["std", "effect", "op"])),
                collector_with_effectful_force_handler_thunk_resumes("collector", path("op")),
            ],
            roots: vec![root_direct_calls_collector_with_local_thunk(
                "root",
                "collector",
            )],
        };

        let plans = analyze_dynamic_effect_thunk_argument_plans(&module);

        assert_eq!(plans.len(), 1);
        assert_eq!(plans[0].caller, "root");
        assert_eq!(plans[0].callee, "collector");
        assert_eq!(plans[0].callee_force_param_index, 0);
        assert_eq!(plans[0].thunk, CpsValueId(40));
        assert_eq!(plans[0].thunk_entry, CpsContinuationId(1));
        assert_eq!(plans[0].post_call_force_chain_len, 2);
        assert_eq!(
            plans[0].region_class,
            DynamicEffectRegionPlanClass::FiniteResumeSchedule
        );
    }

    #[test]
    fn groups_ready_dynamic_thunk_specialization_seed() {
        let module = CpsReprAbiModule {
            functions: vec![
                callee_with_dynamic_perform("producer", path_segments(&["std", "effect", "op"])),
                collector_with_effectful_force_handler_thunk_resumes("collector", path("op")),
            ],
            roots: vec![root_direct_calls_collector_with_local_thunk(
                "root",
                "collector",
            )],
        };

        let seeds = analyze_dynamic_effect_thunk_specialization_seeds(&module);

        assert_eq!(seeds.len(), 1);
        assert_eq!(
            seeds[0].class,
            DynamicEffectThunkSpecializationClass::ReadyFinite
        );
        assert_eq!(seeds[0].finite_effects, vec![path("op")]);
        assert_eq!(seeds[0].post_call_force_chain_len, 2);
        assert!(seeds[0].blocked_effects.is_empty());
    }

    #[test]
    fn plans_ready_finite_seed_as_defunctionalized_when_body_clone_is_blocked() {
        let module = CpsReprAbiModule {
            functions: vec![
                callee_with_dynamic_perform("producer", path_segments(&["std", "effect", "op"])),
                collector_with_effectful_force_handler_thunk_resumes("collector", path("op")),
            ],
            roots: vec![root_direct_calls_collector_with_local_thunk(
                "root",
                "collector",
            )],
        };

        let plans = analyze_dynamic_effect_thunk_rewrite_plans(&module);

        assert_eq!(plans.len(), 1);
        assert_eq!(
            plans[0].strategy,
            DynamicEffectThunkRewriteStrategy::DefunctionalizeFiniteHandler
        );
        assert_eq!(
            plans[0].body_clone_blockers,
            vec![
                DynamicEffectThunkBodyCloneBlocker::PostCallForceChain,
                DynamicEffectThunkBodyCloneBlocker::CalleeHasHandlers,
                DynamicEffectThunkBodyCloneBlocker::CalleeHasEffectBoundary,
            ]
        );
    }

    fn function_with_arm_stmts(
        effect: typed_ir::Path,
        arm_stmts: Vec<CpsStmt>,
        arm_terminator: CpsTerminator,
    ) -> CpsReprAbiFunction {
        CpsReprAbiFunction {
            name: "root".to_string(),
            params: Vec::new(),
            entry: CpsContinuationId(0),
            handlers: vec![CpsReprAbiHandler {
                id: CpsHandlerId(0),
                arms: vec![CpsReprAbiHandlerArm {
                    effect: effect.clone(),
                    entry: CpsContinuationId(2),
                }],
            }],
            continuations: vec![
                continuation(
                    CpsContinuationId(0),
                    CpsShotKind::OneShot,
                    Vec::new(),
                    CpsTerminator::Perform {
                        effect,
                        payload: CpsValueId(0),
                        resume: CpsContinuationId(1),
                        handler: CpsHandlerId(0),
                        blocked: None,
                    },
                ),
                continuation(
                    CpsContinuationId(1),
                    CpsShotKind::MultiShot,
                    Vec::new(),
                    CpsTerminator::Return(CpsValueId(20)),
                ),
                continuation(
                    CpsContinuationId(2),
                    CpsShotKind::MultiShot,
                    arm_stmts,
                    arm_terminator,
                ),
                continuation(
                    CpsContinuationId(3),
                    CpsShotKind::OneShot,
                    Vec::new(),
                    CpsTerminator::Return(CpsValueId(30)),
                ),
            ],
        }
    }

    fn continuation(
        id: CpsContinuationId,
        shot_kind: CpsShotKind,
        stmts: Vec<CpsStmt>,
        terminator: CpsTerminator,
    ) -> CpsReprAbiContinuation {
        CpsReprAbiContinuation {
            id,
            params: vec![CpsReprAbiValue {
                value: CpsValueId(0),
                lane: CpsReprAbiLane::ScalarI64,
            }],
            environment: Vec::new(),
            shot_kind,
            return_lane: CpsReprAbiLane::ScalarI64,
            stmts,
            terminator,
        }
    }

    fn caller_with_effectful_call_handler(
        name: &str,
        target: &str,
        effect: typed_ir::Path,
    ) -> CpsReprAbiFunction {
        CpsReprAbiFunction {
            name: name.to_string(),
            params: Vec::new(),
            entry: CpsContinuationId(0),
            handlers: vec![CpsReprAbiHandler {
                id: CpsHandlerId(0),
                arms: vec![CpsReprAbiHandlerArm {
                    effect,
                    entry: CpsContinuationId(1),
                }],
            }],
            continuations: vec![
                continuation(
                    CpsContinuationId(0),
                    CpsShotKind::OneShot,
                    vec![CpsStmt::InstallHandler {
                        handler: CpsHandlerId(0),
                        envs: Vec::new(),
                        value: CpsContinuationId(2),
                        escape: CpsContinuationId(2),
                    }],
                    CpsTerminator::EffectfulCall {
                        target: target.to_string(),
                        args: Vec::new(),
                        resume: CpsContinuationId(2),
                    },
                ),
                continuation(
                    CpsContinuationId(1),
                    CpsShotKind::MultiShot,
                    vec![CpsStmt::Resume {
                        dest: CpsValueId(10),
                        resumption: CpsValueId(2),
                        arg: CpsValueId(0),
                    }],
                    CpsTerminator::Return(CpsValueId(10)),
                ),
                continuation(
                    CpsContinuationId(2),
                    CpsShotKind::OneShot,
                    Vec::new(),
                    CpsTerminator::Return(CpsValueId(20)),
                ),
            ],
        }
    }

    fn callee_with_dynamic_perform(name: &str, effect: typed_ir::Path) -> CpsReprAbiFunction {
        CpsReprAbiFunction {
            name: name.to_string(),
            params: Vec::new(),
            entry: CpsContinuationId(0),
            handlers: Vec::new(),
            continuations: vec![
                continuation(
                    CpsContinuationId(0),
                    CpsShotKind::OneShot,
                    Vec::new(),
                    CpsTerminator::Perform {
                        effect,
                        payload: CpsValueId(0),
                        resume: CpsContinuationId(1),
                        handler: CpsHandlerId(usize::MAX),
                        blocked: None,
                    },
                ),
                continuation(
                    CpsContinuationId(1),
                    CpsShotKind::MultiShot,
                    Vec::new(),
                    CpsTerminator::Return(CpsValueId(20)),
                ),
            ],
        }
    }

    fn caller_with_effectful_call_handler_thunk_resumes(
        name: &str,
        target: &str,
        effect: typed_ir::Path,
    ) -> CpsReprAbiFunction {
        let mut function = function_with_arm_thunk_resumes(effect);
        function.name = name.to_string();
        function.continuations[0].stmts = vec![CpsStmt::InstallHandler {
            handler: CpsHandlerId(0),
            envs: Vec::new(),
            value: CpsContinuationId(1),
            escape: CpsContinuationId(1),
        }];
        function.continuations[0].terminator = CpsTerminator::EffectfulCall {
            target: target.to_string(),
            args: Vec::new(),
            resume: CpsContinuationId(1),
        };
        function
    }

    fn collector_with_effectful_force_handler_thunk_resumes(
        name: &str,
        effect: typed_ir::Path,
    ) -> CpsReprAbiFunction {
        let mut function = function_with_arm_thunk_resumes(effect);
        function.name = name.to_string();
        function.params = vec![CpsReprAbiValue {
            value: CpsValueId(0),
            lane: CpsReprAbiLane::ScalarI64,
        }];
        function.continuations[0].stmts = vec![
            CpsStmt::InstallHandler {
                handler: CpsHandlerId(0),
                envs: Vec::new(),
                value: CpsContinuationId(1),
                escape: CpsContinuationId(1),
            },
            CpsStmt::AddThunkBoundary {
                dest: CpsValueId(34),
                thunk: CpsValueId(0),
                guard: CpsValueId(35),
                allowed: typed_ir::Type::Any,
                active: true,
            },
        ];
        function.continuations[0].terminator = CpsTerminator::EffectfulForce {
            thunk: CpsValueId(34),
            resume: CpsContinuationId(1),
        };
        function
    }

    fn root_direct_calls_collector_with_local_thunk(
        name: &str,
        collector: &str,
    ) -> CpsReprAbiFunction {
        CpsReprAbiFunction {
            name: name.to_string(),
            params: Vec::new(),
            entry: CpsContinuationId(0),
            handlers: Vec::new(),
            continuations: vec![
                continuation(
                    CpsContinuationId(0),
                    CpsShotKind::OneShot,
                    vec![
                        CpsStmt::MakeThunk {
                            dest: CpsValueId(40),
                            entry: CpsContinuationId(1),
                        },
                        CpsStmt::DirectCall {
                            dest: CpsValueId(41),
                            target: collector.to_string(),
                            args: vec![CpsValueId(40)],
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(42),
                            thunk: CpsValueId(41),
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(43),
                            thunk: CpsValueId(42),
                        },
                    ],
                    CpsTerminator::Return(CpsValueId(43)),
                ),
                continuation(
                    CpsContinuationId(1),
                    CpsShotKind::OneShot,
                    Vec::new(),
                    CpsTerminator::Return(CpsValueId(42)),
                ),
            ],
        }
    }

    fn function_with_arm_thunk_resumes(effect: typed_ir::Path) -> CpsReprAbiFunction {
        CpsReprAbiFunction {
            name: "root".to_string(),
            params: Vec::new(),
            entry: CpsContinuationId(0),
            handlers: vec![CpsReprAbiHandler {
                id: CpsHandlerId(0),
                arms: vec![CpsReprAbiHandlerArm {
                    effect: effect.clone(),
                    entry: CpsContinuationId(2),
                }],
            }],
            continuations: vec![
                continuation(
                    CpsContinuationId(0),
                    CpsShotKind::OneShot,
                    Vec::new(),
                    CpsTerminator::Perform {
                        effect,
                        payload: CpsValueId(0),
                        resume: CpsContinuationId(1),
                        handler: CpsHandlerId(0),
                        blocked: None,
                    },
                ),
                continuation(
                    CpsContinuationId(1),
                    CpsShotKind::MultiShot,
                    Vec::new(),
                    CpsTerminator::Return(CpsValueId(20)),
                ),
                continuation(
                    CpsContinuationId(2),
                    CpsShotKind::MultiShot,
                    vec![
                        CpsStmt::MakeThunk {
                            dest: CpsValueId(30),
                            entry: CpsContinuationId(3),
                        },
                        CpsStmt::MakeThunk {
                            dest: CpsValueId(31),
                            entry: CpsContinuationId(4),
                        },
                    ],
                    CpsTerminator::Return(CpsValueId(31)),
                ),
                continuation(
                    CpsContinuationId(3),
                    CpsShotKind::OneShot,
                    vec![CpsStmt::Resume {
                        dest: CpsValueId(32),
                        resumption: CpsValueId(2),
                        arg: CpsValueId(0),
                    }],
                    CpsTerminator::Return(CpsValueId(32)),
                ),
                continuation(
                    CpsContinuationId(4),
                    CpsShotKind::OneShot,
                    vec![CpsStmt::Resume {
                        dest: CpsValueId(33),
                        resumption: CpsValueId(2),
                        arg: CpsValueId(1),
                    }],
                    CpsTerminator::Return(CpsValueId(33)),
                ),
            ],
        }
    }

    fn path(name: &str) -> typed_ir::Path {
        typed_ir::Path::from_name(typed_ir::Name(name.to_string()))
    }

    fn path_segments(names: &[&str]) -> typed_ir::Path {
        typed_ir::Path {
            segments: names
                .iter()
                .map(|name| typed_ir::Name((*name).to_string()))
                .collect(),
        }
    }

    #[allow(dead_code)]
    fn literal_int(dest: CpsValueId, value: &str) -> CpsStmt {
        CpsStmt::Literal {
            dest,
            literal: CpsLiteral::Int(value.to_string()),
        }
    }
}
