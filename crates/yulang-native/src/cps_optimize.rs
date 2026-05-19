//! Optimization entrypoint for backend-facing CPS representation ABI.
//!
//! This module is intentionally placed between CPS repr ABI lowering and
//! Cranelift codegen so JIT and object generation share one transformation
//! path.  Early passes are deliberately conservative: they rewrite explicit
//! continuation call sites, but leave closure entries, thunk entries, and
//! handler arm entries alone unless their call protocol is represented at the
//! call site.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::cps_effect_regions::{
    DynamicEffectRegionPlanClass, DynamicEffectThunkRewritePlan, DynamicEffectThunkRewriteStrategy,
    DynamicEffectThunkSpecializationClass, DynamicEffectThunkSpecializationSeed,
    EffectHandlerRegionClass, analyze_dynamic_effect_handler_candidates,
    analyze_dynamic_effect_region_plans, analyze_dynamic_effect_thunk_argument_plans,
    analyze_dynamic_effect_thunk_rewrite_plans, analyze_dynamic_effect_thunk_specialization_seeds,
    analyze_effect_handler_regions, maybe_trace_dynamic_effect_handler_candidates,
    maybe_trace_dynamic_effect_region_plans, maybe_trace_dynamic_effect_thunk_argument_plans,
    maybe_trace_dynamic_effect_thunk_rewrite_plans,
    maybe_trace_dynamic_effect_thunk_specialization_seeds, maybe_trace_effect_handler_regions,
};
use crate::cps_ir::{
    CpsContinuationId, CpsHandlerEnv, CpsRecordField, CpsShotKind, CpsStmt, CpsTerminator,
    CpsValueId,
};
use crate::cps_repr_abi::{
    CpsReprAbiContinuation, CpsReprAbiEnvironmentSlot, CpsReprAbiFunction, CpsReprAbiHandler,
    CpsReprAbiHandlerArm, CpsReprAbiModule, CpsReprAbiValue,
};
use yulang_typed_ir as typed_ir;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsOptimizationOutput {
    pub module: CpsReprAbiModule,
    pub profile: CpsOptimizationProfile,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CpsOptimizationProfile {
    pub functions: usize,
    pub roots: usize,
    pub continuations: usize,
    pub handlers: usize,
    pub statements: usize,
    pub optimized_continuations: usize,
    pub optimized_statements: usize,
    pub passes_run: usize,
    pub forwarded_continuation_calls: usize,
    pub returned_continuation_calls: usize,
    pub folded_constant_branches: usize,
    pub rewritten_pure_effectful_calls: usize,
    pub inlined_local_thunk_forces: usize,
    pub collapsed_force_thunk_chains: usize,
    pub removed_redundant_non_thunk_forces: usize,
    pub reified_primitive_calls: usize,
    pub reified_partial_closure_calls: usize,
    pub reified_known_closure_parameter_calls: usize,
    pub removed_unused_continuation_params: usize,
    pub removed_unused_environment_slots: usize,
    pub folded_structural_projections: usize,
    pub inlined_pure_direct_calls: usize,
    pub inlined_ready_finite_thunk_calls: usize,
    pub defunctionalized_finite_handler_thunk_calls: usize,
    pub inlined_continuation_calls: usize,
    pub removed_unreachable_continuations: usize,
    pub removed_dead_pure_statements: usize,
    pub direct_style_islands: usize,
    pub direct_style_continuations: usize,
    pub effect_regions: usize,
    pub single_resume_regions: usize,
    pub finite_multi_resume_regions: usize,
    pub escaping_resumption_regions: usize,
    pub nested_effectful_regions: usize,
    pub opaque_effect_regions: usize,
    pub dynamic_effect_handler_candidates: usize,
    pub dynamic_effect_region_plans: usize,
    pub finite_dynamic_effect_region_plans: usize,
    pub dynamic_effect_thunk_argument_plans: usize,
    pub dynamic_effect_thunk_specialization_seeds: usize,
    pub ready_dynamic_effect_thunk_specialization_seeds: usize,
    pub dynamic_effect_thunk_rewrite_plans: usize,
    pub defunctionalized_dynamic_effect_thunk_rewrite_plans: usize,
    pub body_clone_dynamic_effect_thunk_rewrite_plans: usize,
    pub changed: bool,
}

pub fn optimize_cps_repr_abi_module(module: &CpsReprAbiModule) -> CpsOptimizationOutput {
    let mut output = CpsOptimizationOutput {
        module: module.clone(),
        profile: CpsOptimizationProfile::measure(module),
    };

    for _ in 0..4 {
        if !run_simplification_round(&mut output) {
            break;
        }
    }
    output.profile.record_optimized_size(&output.module);
    analyze_direct_style_islands(&mut output);
    analyze_effect_regions(&mut output);
    maybe_trace_profile(&output.profile);
    output
}

fn run_simplification_round(output: &mut CpsOptimizationOutput) -> bool {
    let before = output.profile;
    rewrite_forwarding_continuation_calls(output);
    rewrite_returning_continuation_calls(output);
    fold_constant_branches(output);
    rewrite_pure_effectful_calls(output);
    inline_local_thunk_forces(output);
    collapse_force_thunk_chains(output);
    remove_redundant_non_thunk_forces(output);
    reify_direct_primitive_calls(output);
    reify_local_partial_closure_calls(output);
    reify_known_closure_parameter_calls(output);
    remove_unused_continuation_params(output);
    remove_unused_environment_slots(output);
    fold_structural_projections(output);
    inline_pure_direct_calls(output);
    inline_ready_finite_thunk_calls(output);
    defunctionalize_finite_handler_thunk_calls(output);
    inline_single_use_continuation_calls(output);
    reify_local_partial_closure_calls(output);
    reify_known_closure_parameter_calls(output);
    remove_unused_continuation_params(output);
    remove_unused_environment_slots(output);
    prune_unreachable_continuations(output);
    eliminate_dead_pure_statements(output);
    prune_unreachable_continuations(output);
    output.profile.has_more_changes_than(before)
}

fn rewrite_forwarding_continuation_calls(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        let forwarders = forwarding_continuations(function);
        if forwarders.is_empty() {
            continue;
        }
        for continuation in &mut function.continuations {
            output.profile.forwarded_continuation_calls +=
                rewrite_terminator_forwarders(&mut continuation.terminator, &forwarders);
        }
    }
    output.profile.changed = output.profile.forwarded_continuation_calls > 0;
}

fn rewrite_returning_continuation_calls(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        let returners = returning_continuations(function);
        if returners.is_empty() {
            continue;
        }
        for continuation in &mut function.continuations {
            output.profile.returned_continuation_calls +=
                rewrite_terminator_returners(&mut continuation.terminator, &returners);
        }
    }
    output.profile.changed |= output.profile.returned_continuation_calls > 0;
}

fn fold_constant_branches(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        let empty_param_continuations = function
            .continuations
            .iter()
            .filter(|continuation| continuation.params.is_empty())
            .map(|continuation| continuation.id)
            .collect::<HashSet<_>>();
        for continuation in &mut function.continuations {
            output.profile.folded_constant_branches +=
                fold_constant_branch_in_continuation(continuation, &empty_param_continuations);
        }
    }
    output.profile.changed |= output.profile.folded_constant_branches > 0;
}

fn rewrite_pure_effectful_calls(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    let pure_functions = pure_callable_functions(&output.module);
    if pure_functions.is_empty() {
        return;
    }
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        output.profile.rewritten_pure_effectful_calls +=
            rewrite_pure_effectful_calls_in_function(function, &pure_functions);
    }
    output.profile.changed |= output.profile.rewritten_pure_effectful_calls > 0;
}

fn inline_local_thunk_forces(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        output.profile.inlined_local_thunk_forces +=
            inline_local_thunk_forces_in_function(function);
    }
    output.profile.changed |= output.profile.inlined_local_thunk_forces > 0;
}

fn collapse_force_thunk_chains(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    if std::env::var("YULANG_CPS_DISABLE_FORCE_CHAIN_COLLAPSE")
        .map(|value| value == "1")
        .unwrap_or(false)
    {
        return;
    }
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        output.profile.collapsed_force_thunk_chains +=
            collapse_force_thunk_chains_in_function(function);
    }
    output.profile.changed |= output.profile.collapsed_force_thunk_chains > 0;
}

fn remove_redundant_non_thunk_forces(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    let direct_non_thunk_returns = direct_non_thunk_return_functions(&output.module);
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        output.profile.removed_redundant_non_thunk_forces +=
            remove_redundant_non_thunk_forces_in_function(function, &direct_non_thunk_returns);
    }
    output.profile.changed |= output.profile.removed_redundant_non_thunk_forces > 0;
}

fn reify_direct_primitive_calls(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    let primitives = primitive_wrappers(&output.module);
    if primitives.is_empty() {
        return;
    }
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        for continuation in &mut function.continuations {
            for stmt in &mut continuation.stmts {
                output.profile.reified_primitive_calls +=
                    reify_direct_primitive_stmt(stmt, &primitives);
            }
        }
    }
    output.profile.changed |= output.profile.reified_primitive_calls > 0;
}

fn reify_local_partial_closure_calls(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        let wrappers = partial_closure_wrappers(function);
        let direct_style = direct_style_closure_inline_candidates(function);
        let resumable = scalar_resume_continuations(function);
        let mut next_value = next_function_value_id(function);
        if !wrappers.is_empty() {
            for continuation in &mut function.continuations {
                output.profile.reified_partial_closure_calls +=
                    reify_local_partial_closure_calls_in_continuation(
                        continuation,
                        &wrappers,
                        &resumable,
                        &mut next_value,
                    );
            }
        }
        if !direct_style.is_empty() {
            output.profile.inlined_continuation_calls +=
                inline_local_direct_style_closure_calls_in_function(
                    function,
                    &direct_style,
                    &mut next_value,
                );
        }
    }
    output.profile.changed |= output.profile.reified_partial_closure_calls > 0
        || output.profile.inlined_continuation_calls > 0;
}

fn reify_known_closure_parameter_calls(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        let wrappers = partial_closure_wrappers(function);
        if wrappers.is_empty() {
            continue;
        }
        output.profile.reified_known_closure_parameter_calls +=
            reify_known_closure_parameter_calls_in_function(function, &wrappers);
    }
    output.profile.changed |= output.profile.reified_known_closure_parameter_calls > 0;
}

fn remove_unused_continuation_params(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        output.profile.removed_unused_continuation_params +=
            remove_unused_continuation_params_in_function(function);
    }
    output.profile.changed |= output.profile.removed_unused_continuation_params > 0;
}

fn remove_unused_environment_slots(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        output.profile.removed_unused_environment_slots +=
            remove_unused_environment_slots_in_function(function);
    }
    output.profile.changed |= output.profile.removed_unused_environment_slots > 0;
}

fn fold_structural_projections(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        for continuation in &mut function.continuations {
            output.profile.folded_structural_projections +=
                fold_structural_projections_in_continuation(continuation);
        }
    }
    output.profile.changed |= output.profile.folded_structural_projections > 0;
}

fn inline_pure_direct_calls(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    let candidates = pure_direct_inline_candidates(&output.module);
    if candidates.is_empty() {
        return;
    }
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        output.profile.inlined_pure_direct_calls +=
            inline_pure_direct_calls_in_function(function, &candidates);
    }
    output.profile.changed |= output.profile.inlined_pure_direct_calls > 0;
}

fn inline_ready_finite_thunk_calls(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    if std::env::var("YULANG_CPS_ENABLE_READY_FINITE_INLINE")
        .map(|value| value != "1")
        .unwrap_or(true)
    {
        return;
    }
    let seeds = analyze_dynamic_effect_thunk_rewrite_plans(&output.module)
        .into_iter()
        .filter(|plan| plan.strategy == DynamicEffectThunkRewriteStrategy::CalleeBodyClone)
        .map(|plan| DynamicEffectThunkSpecializationSeed {
            caller: plan.caller,
            call_continuation: plan.call_continuation,
            call_stmt_index: plan.call_stmt_index,
            callee: plan.callee,
            thunk: plan.thunk,
            thunk_entry: plan.thunk_entry,
            post_call_force_chain_len: plan.post_call_force_chain_len,
            class: plan.seed_class,
            finite_effects: plan.finite_effects,
            finite_callee_boundaries: plan.finite_callee_boundaries,
            finite_arm_entries: plan.finite_arm_entries,
            finite_performs: plan.finite_performs,
            finite_resumes: plan.finite_resumes,
            finite_resume_actions: plan.finite_resume_actions,
            no_resume_effects: plan.no_resume_effects,
            blocked_effects: plan.blocked_effects,
        })
        .collect::<Vec<_>>();
    if seeds.is_empty() {
        return;
    }
    let callees = output
        .module
        .functions
        .iter()
        .chain(&output.module.roots)
        .map(|function| (function.name.clone(), function.clone()))
        .collect::<HashMap<_, _>>();
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        output.profile.inlined_ready_finite_thunk_calls +=
            inline_ready_finite_thunk_calls_in_function(function, &seeds, &callees);
    }
    output.profile.changed |= output.profile.inlined_ready_finite_thunk_calls > 0;
}

fn defunctionalize_finite_handler_thunk_calls(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    if std::env::var("YULANG_CPS_ENABLE_FINITE_HANDLER_DEFUN")
        .map(|value| value != "1")
        .unwrap_or(true)
    {
        return;
    }
    let plans = analyze_dynamic_effect_thunk_rewrite_plans(&output.module)
        .into_iter()
        .filter(|plan| {
            plan.strategy == DynamicEffectThunkRewriteStrategy::DefunctionalizeFiniteHandler
        })
        .collect::<Vec<_>>();
    if plans.is_empty() {
        return;
    }
    let callees = output
        .module
        .functions
        .iter()
        .chain(&output.module.roots)
        .map(|function| (function.name.clone(), function.clone()))
        .collect::<HashMap<_, _>>();
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        output.profile.defunctionalized_finite_handler_thunk_calls +=
            defunctionalize_finite_handler_thunk_calls_in_function(function, &plans, &callees);
    }
    output.profile.changed |= output.profile.defunctionalized_finite_handler_thunk_calls > 0;
}

fn remove_unused_continuation_params_in_function(function: &mut CpsReprAbiFunction) -> usize {
    let unused_slots = unused_continuation_param_slots(function);
    if unused_slots.is_empty() {
        return 0;
    }

    let mut removed = 0;
    for continuation in &mut function.continuations {
        if let Some(slots) = unused_slots.get(&continuation.id) {
            removed += remove_indexed_items(&mut continuation.params, slots);
        }
        if let CpsTerminator::Continue { target, args } = &mut continuation.terminator {
            if let Some(slots) = unused_slots.get(target) {
                remove_indexed_items(args, slots);
            }
        }
    }
    removed
}

fn unused_continuation_param_slots(
    function: &CpsReprAbiFunction,
) -> HashMap<CpsContinuationId, HashSet<usize>> {
    let references = continuation_references(function);
    let protected = protected_continuations(function);
    let used_values = function_used_values(function);

    function
        .continuations
        .iter()
        .filter(|continuation| !protected.contains(&continuation.id))
        .filter(|continuation| {
            references
                .get(&continuation.id)
                .is_some_and(|reference| reference.total == reference.continue_calls)
        })
        .filter_map(|continuation| {
            let slots = continuation
                .params
                .iter()
                .enumerate()
                .filter_map(|(index, param)| (!used_values.contains(&param.value)).then_some(index))
                .collect::<HashSet<_>>();
            (!slots.is_empty()).then_some((continuation.id, slots))
        })
        .collect()
}

fn inline_local_thunk_forces_in_function(function: &mut CpsReprAbiFunction) -> usize {
    let continuations = function
        .continuations
        .iter()
        .map(|continuation| (continuation.id, continuation.clone()))
        .collect::<HashMap<_, _>>();
    let value_uses = value_use_counts(function);
    let mut inlined = 0;

    for continuation in &mut function.continuations {
        inlined +=
            inline_local_thunk_force_in_continuation(continuation, &continuations, &value_uses);
    }

    inlined
}

fn inline_local_thunk_force_in_continuation(
    continuation: &mut CpsReprAbiContinuation,
    continuations: &HashMap<CpsContinuationId, CpsReprAbiContinuation>,
    value_uses: &HashMap<CpsValueId, usize>,
) -> usize {
    let CpsTerminator::EffectfulForce { thunk, resume } = continuation.terminator.clone() else {
        return 0;
    };
    if value_uses.get(&thunk).copied().unwrap_or(0) != 1 {
        return 0;
    }

    let Some((thunk_stmt_index, entry)) = local_make_thunk_entry(continuation, thunk) else {
        return 0;
    };
    if !continuation.stmts[thunk_stmt_index + 1..]
        .iter()
        .all(direct_style_stmt)
    {
        return 0;
    }

    let Some(entry_continuation) = continuations.get(&entry) else {
        return 0;
    };
    if !local_thunk_force_entry_is_inlineable(entry_continuation) {
        return 0;
    }
    let CpsTerminator::Return(result) = entry_continuation.terminator else {
        return 0;
    };

    continuation.stmts.remove(thunk_stmt_index);
    continuation
        .stmts
        .extend(entry_continuation.stmts.iter().cloned());
    continuation.terminator = CpsTerminator::Continue {
        target: resume,
        args: vec![result],
    };
    1
}

fn collapse_force_thunk_chains_in_function(function: &mut CpsReprAbiFunction) -> usize {
    let value_uses = value_use_counts(function);
    function
        .continuations
        .iter_mut()
        .map(|continuation| collapse_force_thunk_chains_in_continuation(continuation, &value_uses))
        .sum()
}

fn collapse_force_thunk_chains_in_continuation(
    continuation: &mut CpsReprAbiContinuation,
    value_uses: &HashMap<CpsValueId, usize>,
) -> usize {
    let mut collapsed = 0;
    let mut index = 0;
    while index + 1 < continuation.stmts.len() {
        let Some((first_dest, first_thunk)) = force_thunk_stmt_values(&continuation.stmts[index])
        else {
            index += 1;
            continue;
        };
        let Some((second_dest, second_thunk)) =
            force_thunk_stmt_values(&continuation.stmts[index + 1])
        else {
            index += 1;
            continue;
        };
        if second_thunk != first_dest || value_uses.get(&first_dest).copied().unwrap_or(0) != 1 {
            index += 1;
            continue;
        }

        continuation.stmts[index] = CpsStmt::ForceThunk {
            dest: second_dest,
            thunk: first_thunk,
        };
        continuation.stmts.remove(index + 1);
        collapsed += 1;
    }
    collapsed
}

fn force_thunk_stmt_values(stmt: &CpsStmt) -> Option<(CpsValueId, CpsValueId)> {
    match stmt {
        CpsStmt::ForceThunk { dest, thunk } => Some((*dest, *thunk)),
        _ => None,
    }
}

fn remove_redundant_non_thunk_forces_in_function(
    function: &mut CpsReprAbiFunction,
    direct_non_thunk_returns: &HashSet<String>,
) -> usize {
    let value_uses = value_use_counts(function);
    function
        .continuations
        .iter_mut()
        .map(|continuation| {
            remove_redundant_non_thunk_forces_in_continuation(
                continuation,
                &value_uses,
                direct_non_thunk_returns,
            )
        })
        .sum()
}

fn remove_redundant_non_thunk_forces_in_continuation(
    continuation: &mut CpsReprAbiContinuation,
    value_uses: &HashMap<CpsValueId, usize>,
    direct_non_thunk_returns: &HashSet<String>,
) -> usize {
    let mut known_non_thunks = HashSet::new();
    let mut removed = 0;
    let mut index = 0;
    while index < continuation.stmts.len() {
        if let CpsStmt::ForceThunk { dest, thunk } = continuation.stmts[index] {
            if known_non_thunks.contains(&thunk)
                && value_uses.get(&dest).copied().unwrap_or(0)
                    == count_tail_value_uses(continuation, index + 1, dest)
            {
                substitute_continuation_tail_value(continuation, index + 1, dest, thunk);
                continuation.stmts.remove(index);
                removed += 1;
                continue;
            }
        }

        if let Some(dest) = stmt_dest(&continuation.stmts[index]) {
            if stmt_result_is_definitely_non_thunk(
                &continuation.stmts[index],
                direct_non_thunk_returns,
            ) {
                known_non_thunks.insert(dest);
            }
        }
        index += 1;
    }
    removed
}

fn count_tail_value_uses(
    continuation: &CpsReprAbiContinuation,
    start: usize,
    value: CpsValueId,
) -> usize {
    continuation.stmts[start..]
        .iter()
        .flat_map(stmt_operands)
        .chain(terminator_values(&continuation.terminator))
        .filter(|used| *used == value)
        .count()
}

fn substitute_continuation_tail_value(
    continuation: &mut CpsReprAbiContinuation,
    start: usize,
    from: CpsValueId,
    to: CpsValueId,
) {
    let substitution = HashMap::from([(from, to)]);
    for stmt in &mut continuation.stmts[start..] {
        *stmt = substitute_stmt_values(stmt.clone(), &substitution);
    }
    continuation.terminator =
        substitute_terminator_values(continuation.terminator.clone(), &substitution);
}

fn direct_non_thunk_return_functions(module: &CpsReprAbiModule) -> HashSet<String> {
    let mut known = HashSet::new();
    loop {
        let before = known.len();
        for function in module.functions.iter().chain(&module.roots) {
            if function_returns_definitely_non_thunk(function, &known) {
                known.insert(function.name.clone());
            }
        }
        if known.len() == before {
            return known;
        }
    }
}

fn function_returns_definitely_non_thunk(
    function: &CpsReprAbiFunction,
    direct_non_thunk_returns: &HashSet<String>,
) -> bool {
    let direct_return_continuations = direct_return_continuations(function);
    let mut has_return = false;
    for continuation in &function.continuations {
        if !direct_return_continuations.contains(&continuation.id) {
            continue;
        }
        let mut known_non_thunks = HashSet::new();
        for stmt in &continuation.stmts {
            if let Some(dest) = stmt_dest(stmt) {
                if stmt_result_is_definitely_non_thunk(stmt, direct_non_thunk_returns) {
                    known_non_thunks.insert(dest);
                }
            }
        }
        if let CpsTerminator::Return(value) = continuation.terminator {
            has_return = true;
            if !known_non_thunks.contains(&value) {
                return false;
            }
        }
    }
    has_return
}

fn direct_return_continuations(function: &CpsReprAbiFunction) -> HashSet<CpsContinuationId> {
    let continuations = function
        .continuations
        .iter()
        .map(|continuation| (continuation.id, continuation))
        .collect::<HashMap<_, _>>();
    let mut reachable = HashSet::new();
    let mut work = VecDeque::from([function.entry]);
    for handler in &function.handlers {
        for arm in &handler.arms {
            work.push_back(arm.entry);
        }
    }

    while let Some(id) = work.pop_front() {
        if !reachable.insert(id) {
            continue;
        }
        let Some(continuation) = continuations.get(&id) else {
            continue;
        };
        for stmt in &continuation.stmts {
            if let CpsStmt::InstallHandler { value, escape, .. } = stmt {
                work.push_back(*value);
                work.push_back(*escape);
            }
        }
        match &continuation.terminator {
            CpsTerminator::Continue { target, .. } => work.push_back(*target),
            CpsTerminator::Branch {
                then_cont,
                else_cont,
                ..
            } => {
                work.push_back(*then_cont);
                work.push_back(*else_cont);
            }
            CpsTerminator::EffectfulCall { resume, .. }
            | CpsTerminator::EffectfulApply { resume, .. }
            | CpsTerminator::EffectfulForce { resume, .. }
            | CpsTerminator::Perform { resume, .. } => work.push_back(*resume),
            CpsTerminator::Return(_) => {}
        }
    }
    reachable
}

fn stmt_result_is_definitely_non_thunk(
    stmt: &CpsStmt,
    direct_non_thunk_returns: &HashSet<String>,
) -> bool {
    match stmt {
        CpsStmt::Primitive { op, .. } => primitive_result_is_definitely_non_thunk(*op),
        CpsStmt::DirectCall { target, .. } => direct_non_thunk_returns.contains(target),
        stmt => matches!(
            stmt,
            CpsStmt::Literal { .. }
                | CpsStmt::FreshGuard { .. }
                | CpsStmt::PeekGuard { .. }
                | CpsStmt::FindGuard { .. }
                | CpsStmt::MakeClosure { .. }
                | CpsStmt::MakeRecursiveClosure { .. }
                | CpsStmt::ForceThunk { .. }
                | CpsStmt::Tuple { .. }
                | CpsStmt::Record { .. }
                | CpsStmt::RecordWithoutFields { .. }
                | CpsStmt::Variant { .. }
                | CpsStmt::RecordHasField { .. }
                | CpsStmt::VariantTagEq { .. }
                | CpsStmt::CloneContinuation { .. }
        ),
    }
}

fn primitive_result_is_definitely_non_thunk(op: typed_ir::PrimitiveOp) -> bool {
    // A primitive result is safe here when the result object/scalar is produced
    // by the primitive itself. Element projection is different: ListIndex may
    // surface an existing thunk handle stored in a list and still needs force.
    matches!(
        op,
        typed_ir::PrimitiveOp::BoolNot
            | typed_ir::PrimitiveOp::BoolEq
            | typed_ir::PrimitiveOp::ListEmpty
            | typed_ir::PrimitiveOp::ListSingleton
            | typed_ir::PrimitiveOp::ListLen
            | typed_ir::PrimitiveOp::ListMerge
            | typed_ir::PrimitiveOp::ListIndexRange
            | typed_ir::PrimitiveOp::ListSplice
            | typed_ir::PrimitiveOp::ListIndexRangeRaw
            | typed_ir::PrimitiveOp::ListSpliceRaw
            | typed_ir::PrimitiveOp::ListViewRaw
            | typed_ir::PrimitiveOp::StringLen
            | typed_ir::PrimitiveOp::StringIndex
            | typed_ir::PrimitiveOp::StringIndexRange
            | typed_ir::PrimitiveOp::StringSplice
            | typed_ir::PrimitiveOp::StringIndexRangeRaw
            | typed_ir::PrimitiveOp::StringSpliceRaw
            | typed_ir::PrimitiveOp::IntAdd
            | typed_ir::PrimitiveOp::IntSub
            | typed_ir::PrimitiveOp::IntMul
            | typed_ir::PrimitiveOp::IntDiv
            | typed_ir::PrimitiveOp::IntEq
            | typed_ir::PrimitiveOp::IntLt
            | typed_ir::PrimitiveOp::IntLe
            | typed_ir::PrimitiveOp::IntGt
            | typed_ir::PrimitiveOp::IntGe
            | typed_ir::PrimitiveOp::IntToString
            | typed_ir::PrimitiveOp::IntToHex
            | typed_ir::PrimitiveOp::IntToUpperHex
            | typed_ir::PrimitiveOp::FloatAdd
            | typed_ir::PrimitiveOp::FloatSub
            | typed_ir::PrimitiveOp::FloatMul
            | typed_ir::PrimitiveOp::FloatDiv
            | typed_ir::PrimitiveOp::FloatEq
            | typed_ir::PrimitiveOp::FloatLt
            | typed_ir::PrimitiveOp::FloatLe
            | typed_ir::PrimitiveOp::FloatGt
            | typed_ir::PrimitiveOp::FloatGe
            | typed_ir::PrimitiveOp::FloatToString
            | typed_ir::PrimitiveOp::BoolToString
            | typed_ir::PrimitiveOp::StringConcat
            | typed_ir::PrimitiveOp::StringEq
            | typed_ir::PrimitiveOp::StringToBytes
            | typed_ir::PrimitiveOp::CharEq
            | typed_ir::PrimitiveOp::CharToString
            | typed_ir::PrimitiveOp::CharIsWhitespace
            | typed_ir::PrimitiveOp::CharIsPunctuation
            | typed_ir::PrimitiveOp::CharIsWord
            | typed_ir::PrimitiveOp::BytesLen
            | typed_ir::PrimitiveOp::BytesEq
            | typed_ir::PrimitiveOp::BytesConcat
            | typed_ir::PrimitiveOp::BytesIndex
            | typed_ir::PrimitiveOp::BytesIndexRange
            | typed_ir::PrimitiveOp::BytesToUtf8Raw
            | typed_ir::PrimitiveOp::BytesToPath
            | typed_ir::PrimitiveOp::PathToBytes
    )
}

fn local_make_thunk_entry(
    continuation: &CpsReprAbiContinuation,
    thunk: CpsValueId,
) -> Option<(usize, CpsContinuationId)> {
    continuation
        .stmts
        .iter()
        .enumerate()
        .find_map(|(index, stmt)| match stmt {
            CpsStmt::MakeThunk { dest, entry } if *dest == thunk => Some((index, *entry)),
            _ => None,
        })
}

fn local_thunk_force_entry_is_inlineable(continuation: &CpsReprAbiContinuation) -> bool {
    if continuation.shot_kind != CpsShotKind::OneShot
        || !continuation.params.is_empty()
        || continuation.stmts.len() > 12
    {
        return false;
    }
    let CpsTerminator::Return(result) = continuation.terminator else {
        return false;
    };
    continuation.stmts.iter().all(local_thunk_force_stmt)
        && continuation
            .stmts
            .iter()
            .any(|stmt| stmt_dest(stmt) == Some(result) && local_thunk_force_return_stmt(stmt))
}

fn local_thunk_force_stmt(stmt: &CpsStmt) -> bool {
    matches!(
        stmt,
        CpsStmt::Literal { .. }
            | CpsStmt::Tuple { .. }
            | CpsStmt::Record { .. }
            | CpsStmt::RecordWithoutFields { .. }
            | CpsStmt::Variant { .. }
            | CpsStmt::Select { .. }
            | CpsStmt::SelectWithDefault { .. }
            | CpsStmt::RecordHasField { .. }
            | CpsStmt::TupleGet { .. }
            | CpsStmt::VariantTagEq { .. }
            | CpsStmt::VariantPayload { .. }
            | CpsStmt::Primitive {
                op: typed_ir::PrimitiveOp::BoolNot
                    | typed_ir::PrimitiveOp::BoolEq
                    | typed_ir::PrimitiveOp::IntAdd
                    | typed_ir::PrimitiveOp::IntSub
                    | typed_ir::PrimitiveOp::IntMul
                    | typed_ir::PrimitiveOp::IntEq
                    | typed_ir::PrimitiveOp::IntLt
                    | typed_ir::PrimitiveOp::IntLe
                    | typed_ir::PrimitiveOp::IntGt
                    | typed_ir::PrimitiveOp::IntGe
                    | typed_ir::PrimitiveOp::IntToString
                    | typed_ir::PrimitiveOp::IntToHex
                    | typed_ir::PrimitiveOp::IntToUpperHex
                    | typed_ir::PrimitiveOp::FloatAdd
                    | typed_ir::PrimitiveOp::FloatSub
                    | typed_ir::PrimitiveOp::FloatMul
                    | typed_ir::PrimitiveOp::FloatEq
                    | typed_ir::PrimitiveOp::FloatLt
                    | typed_ir::PrimitiveOp::FloatLe
                    | typed_ir::PrimitiveOp::FloatGt
                    | typed_ir::PrimitiveOp::FloatGe
                    | typed_ir::PrimitiveOp::FloatToString
                    | typed_ir::PrimitiveOp::BoolToString
                    | typed_ir::PrimitiveOp::StringConcat
                    | typed_ir::PrimitiveOp::StringLen
                    | typed_ir::PrimitiveOp::StringEq,
                ..
            }
    )
}

fn local_thunk_force_return_stmt(stmt: &CpsStmt) -> bool {
    matches!(
        stmt,
        CpsStmt::Literal { .. }
            | CpsStmt::Tuple { .. }
            | CpsStmt::Record { .. }
            | CpsStmt::RecordWithoutFields { .. }
            | CpsStmt::Variant { .. }
            | CpsStmt::RecordHasField { .. }
            | CpsStmt::VariantTagEq { .. }
            | CpsStmt::Primitive { .. }
    )
}

fn value_use_counts(function: &CpsReprAbiFunction) -> HashMap<CpsValueId, usize> {
    let mut uses = HashMap::new();
    for continuation in &function.continuations {
        for slot in &continuation.environment {
            count_value_use(slot.value, &mut uses);
        }
        for stmt in &continuation.stmts {
            for value in stmt_operands(stmt) {
                count_value_use(value, &mut uses);
            }
        }
        for value in terminator_values(&continuation.terminator) {
            count_value_use(value, &mut uses);
        }
    }
    uses
}

fn count_value_use(value: CpsValueId, uses: &mut HashMap<CpsValueId, usize>) {
    *uses.entry(value).or_insert(0) += 1;
}

fn remove_unused_environment_slots_in_function(function: &mut CpsReprAbiFunction) -> usize {
    let required_values = required_environment_values_by_continuation(function);
    let mut removed = 0;
    for continuation in &mut function.continuations {
        let Some(required) = required_values.get(&continuation.id) else {
            continue;
        };
        let before = continuation.environment.len();
        continuation
            .environment
            .retain(|slot| required.contains(&slot.value));
        if before != continuation.environment.len() {
            for (index, slot) in continuation.environment.iter_mut().enumerate() {
                slot.index = index;
            }
            removed += before - continuation.environment.len();
        }
    }
    removed
}

fn required_environment_values_by_continuation(
    function: &CpsReprAbiFunction,
) -> HashMap<CpsContinuationId, HashSet<CpsValueId>> {
    let environment_values = function
        .continuations
        .iter()
        .map(|continuation| {
            (
                continuation.id,
                continuation
                    .environment
                    .iter()
                    .map(|slot| slot.value)
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<HashMap<_, _>>();

    function
        .continuations
        .iter()
        .map(|continuation| {
            let mut required = HashSet::new();
            for stmt in &continuation.stmts {
                required.extend(stmt_operands(stmt));
                required.extend(referenced_environment_values_in_stmt(
                    stmt,
                    &environment_values,
                ));
            }
            required.extend(terminator_values(&continuation.terminator));
            required.extend(referenced_environment_values_in_terminator(
                &continuation.terminator,
                &environment_values,
            ));
            (continuation.id, required)
        })
        .collect()
}

fn referenced_environment_values_in_stmt(
    stmt: &CpsStmt,
    environment_values: &HashMap<CpsContinuationId, Vec<CpsValueId>>,
) -> Vec<CpsValueId> {
    match stmt {
        CpsStmt::MakeThunk { entry, .. }
        | CpsStmt::MakeClosure { entry, .. }
        | CpsStmt::MakeRecursiveClosure { entry, .. } => environment_values
            .get(entry)
            .into_iter()
            .flatten()
            .copied()
            .collect(),
        CpsStmt::InstallHandler {
            value,
            escape,
            envs,
            ..
        } => std::iter::once(value)
            .chain(std::iter::once(escape))
            .chain(envs.iter().map(|env| &env.entry))
            .filter_map(|entry| environment_values.get(entry))
            .flatten()
            .copied()
            .collect(),
        CpsStmt::ResumeWithHandler { envs, .. } => envs
            .iter()
            .filter_map(|env| environment_values.get(&env.entry))
            .flatten()
            .copied()
            .collect(),
        _ => Vec::new(),
    }
}

fn referenced_environment_values_in_terminator(
    terminator: &CpsTerminator,
    environment_values: &HashMap<CpsContinuationId, Vec<CpsValueId>>,
) -> Vec<CpsValueId> {
    match terminator {
        CpsTerminator::Continue { target, .. } => environment_values
            .get(target)
            .into_iter()
            .flatten()
            .copied()
            .collect(),
        CpsTerminator::Branch {
            then_cont,
            else_cont,
            ..
        } => [then_cont, else_cont]
            .into_iter()
            .filter_map(|target| environment_values.get(target))
            .flatten()
            .copied()
            .collect(),
        CpsTerminator::Perform { resume, .. }
        | CpsTerminator::EffectfulCall { resume, .. }
        | CpsTerminator::EffectfulApply { resume, .. }
        | CpsTerminator::EffectfulForce { resume, .. } => environment_values
            .get(resume)
            .into_iter()
            .flatten()
            .copied()
            .collect(),
        CpsTerminator::Return(_) => Vec::new(),
    }
}

fn function_used_values(function: &CpsReprAbiFunction) -> HashSet<CpsValueId> {
    let mut used = HashSet::new();
    for continuation in &function.continuations {
        used.extend(continuation.environment.iter().map(|slot| slot.value));
        for stmt in &continuation.stmts {
            used.extend(stmt_operands(stmt));
        }
        used.extend(terminator_values(&continuation.terminator));
    }
    used
}

fn remove_indexed_items<T>(items: &mut Vec<T>, slots: &HashSet<usize>) -> usize {
    let before = items.len();
    let mut index = 0;
    items.retain(|_| {
        let keep = !slots.contains(&index);
        index += 1;
        keep
    });
    before - items.len()
}

fn inline_single_use_continuation_calls(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        let candidates = inline_candidates(function);
        if candidates.is_empty() {
            continue;
        }
        for index in 0..function.continuations.len() {
            output.profile.inlined_continuation_calls +=
                inline_continuation_call_at(function, index, &candidates);
        }
    }
    output.profile.changed |= output.profile.inlined_continuation_calls > 0;
}

fn prune_unreachable_continuations(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        let reachable = reachable_continuations(function);
        let before = function.continuations.len();
        function
            .continuations
            .retain(|continuation| reachable.contains(&continuation.id));
        output.profile.removed_unreachable_continuations += before - function.continuations.len();
    }
    output.profile.changed |= output.profile.removed_unreachable_continuations > 0;
}

fn eliminate_dead_pure_statements(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
    for function in output
        .module
        .functions
        .iter_mut()
        .chain(&mut output.module.roots)
    {
        let captured_values = function_captured_values(function);
        for continuation in &mut function.continuations {
            output.profile.removed_dead_pure_statements +=
                eliminate_dead_pure_statements_in_continuation(continuation, &captured_values);
        }
    }
    output.profile.changed |= output.profile.removed_dead_pure_statements > 0;
}

fn analyze_direct_style_islands(output: &mut CpsOptimizationOutput) {
    output.profile.direct_style_islands = 0;
    output.profile.direct_style_continuations = 0;
    for function in output.module.functions.iter().chain(&output.module.roots) {
        let islands = direct_style_islands(function);
        output.profile.direct_style_islands += islands.len();
        output.profile.direct_style_continuations += islands
            .iter()
            .map(|island| island.continuations.len())
            .sum::<usize>();
    }
}

fn analyze_effect_regions(output: &mut CpsOptimizationOutput) {
    output.profile.effect_regions = 0;
    output.profile.single_resume_regions = 0;
    output.profile.finite_multi_resume_regions = 0;
    output.profile.escaping_resumption_regions = 0;
    output.profile.nested_effectful_regions = 0;
    output.profile.opaque_effect_regions = 0;
    output.profile.dynamic_effect_handler_candidates = 0;
    output.profile.dynamic_effect_region_plans = 0;
    output.profile.finite_dynamic_effect_region_plans = 0;
    output.profile.dynamic_effect_thunk_argument_plans = 0;
    output.profile.dynamic_effect_thunk_specialization_seeds = 0;
    output
        .profile
        .ready_dynamic_effect_thunk_specialization_seeds = 0;
    output.profile.dynamic_effect_thunk_rewrite_plans = 0;
    output
        .profile
        .defunctionalized_dynamic_effect_thunk_rewrite_plans = 0;
    output.profile.body_clone_dynamic_effect_thunk_rewrite_plans = 0;
    for function in output.module.functions.iter().chain(&output.module.roots) {
        let regions = analyze_effect_handler_regions(function);
        maybe_trace_effect_handler_regions(function, &regions);
        for region in regions {
            output.profile.effect_regions += 1;
            match region.class {
                EffectHandlerRegionClass::Opaque => output.profile.opaque_effect_regions += 1,
                EffectHandlerRegionClass::SingleResume => output.profile.single_resume_regions += 1,
                EffectHandlerRegionClass::FiniteMultiResume => {
                    output.profile.finite_multi_resume_regions += 1
                }
                EffectHandlerRegionClass::EscapingResumption => {
                    output.profile.escaping_resumption_regions += 1
                }
                EffectHandlerRegionClass::NestedEffectful => {
                    output.profile.nested_effectful_regions += 1
                }
            }
        }
    }
    let dynamic_candidates = analyze_dynamic_effect_handler_candidates(&output.module);
    maybe_trace_dynamic_effect_handler_candidates(&dynamic_candidates);
    output.profile.dynamic_effect_handler_candidates = dynamic_candidates.len();
    let dynamic_plans = analyze_dynamic_effect_region_plans(&output.module);
    maybe_trace_dynamic_effect_region_plans(&dynamic_plans);
    output.profile.dynamic_effect_region_plans = dynamic_plans.len();
    output.profile.finite_dynamic_effect_region_plans = dynamic_plans
        .iter()
        .filter(|plan| plan.class == DynamicEffectRegionPlanClass::FiniteResumeSchedule)
        .count();
    let thunk_argument_plans = analyze_dynamic_effect_thunk_argument_plans(&output.module);
    maybe_trace_dynamic_effect_thunk_argument_plans(&thunk_argument_plans);
    output.profile.dynamic_effect_thunk_argument_plans = thunk_argument_plans.len();
    let thunk_seeds = analyze_dynamic_effect_thunk_specialization_seeds(&output.module);
    maybe_trace_dynamic_effect_thunk_specialization_seeds(&thunk_seeds);
    output.profile.dynamic_effect_thunk_specialization_seeds = thunk_seeds.len();
    output
        .profile
        .ready_dynamic_effect_thunk_specialization_seeds = thunk_seeds
        .iter()
        .filter(|seed| seed.class == DynamicEffectThunkSpecializationClass::ReadyFinite)
        .count();
    let rewrite_plans = analyze_dynamic_effect_thunk_rewrite_plans(&output.module);
    maybe_trace_dynamic_effect_thunk_rewrite_plans(&rewrite_plans);
    output.profile.dynamic_effect_thunk_rewrite_plans = rewrite_plans.len();
    output
        .profile
        .defunctionalized_dynamic_effect_thunk_rewrite_plans = rewrite_plans
        .iter()
        .filter(|plan| {
            plan.strategy == DynamicEffectThunkRewriteStrategy::DefunctionalizeFiniteHandler
        })
        .count();
    output.profile.body_clone_dynamic_effect_thunk_rewrite_plans = rewrite_plans
        .iter()
        .filter(|plan| plan.strategy == DynamicEffectThunkRewriteStrategy::CalleeBodyClone)
        .count();
}

fn maybe_trace_profile(profile: &CpsOptimizationProfile) {
    if std::env::var_os("YULANG_CPS_OPT_TRACE").is_none() {
        return;
    }
    eprintln!(
        "[CPS-OPT] functions={} roots={} continuations={} optimized_continuations={} handlers={} statements={} optimized_statements={} passes={} forwarded_continuation_calls={} returned_continuation_calls={} folded_constant_branches={} rewritten_pure_effectful_calls={} inlined_local_thunk_forces={} collapsed_force_thunk_chains={} removed_redundant_non_thunk_forces={} reified_primitive_calls={} reified_partial_closure_calls={} reified_known_closure_parameter_calls={} removed_unused_continuation_params={} removed_unused_environment_slots={} folded_structural_projections={} inlined_pure_direct_calls={} inlined_ready_finite_thunk_calls={} defunctionalized_finite_handler_thunk_calls={} inlined_continuation_calls={} removed_unreachable_continuations={} removed_dead_pure_statements={} direct_style_islands={} direct_style_continuations={} effect_regions={} single_resume_regions={} finite_multi_resume_regions={} escaping_resumption_regions={} nested_effectful_regions={} opaque_effect_regions={} dynamic_effect_handler_candidates={} dynamic_effect_region_plans={} finite_dynamic_effect_region_plans={} dynamic_effect_thunk_argument_plans={} dynamic_effect_thunk_specialization_seeds={} ready_dynamic_effect_thunk_specialization_seeds={} dynamic_effect_thunk_rewrite_plans={} defunctionalized_dynamic_effect_thunk_rewrite_plans={} body_clone_dynamic_effect_thunk_rewrite_plans={} changed={}",
        profile.functions,
        profile.roots,
        profile.continuations,
        profile.optimized_continuations,
        profile.handlers,
        profile.statements,
        profile.optimized_statements,
        profile.passes_run,
        profile.forwarded_continuation_calls,
        profile.returned_continuation_calls,
        profile.folded_constant_branches,
        profile.rewritten_pure_effectful_calls,
        profile.inlined_local_thunk_forces,
        profile.collapsed_force_thunk_chains,
        profile.removed_redundant_non_thunk_forces,
        profile.reified_primitive_calls,
        profile.reified_partial_closure_calls,
        profile.reified_known_closure_parameter_calls,
        profile.removed_unused_continuation_params,
        profile.removed_unused_environment_slots,
        profile.folded_structural_projections,
        profile.inlined_pure_direct_calls,
        profile.inlined_ready_finite_thunk_calls,
        profile.defunctionalized_finite_handler_thunk_calls,
        profile.inlined_continuation_calls,
        profile.removed_unreachable_continuations,
        profile.removed_dead_pure_statements,
        profile.direct_style_islands,
        profile.direct_style_continuations,
        profile.effect_regions,
        profile.single_resume_regions,
        profile.finite_multi_resume_regions,
        profile.escaping_resumption_regions,
        profile.nested_effectful_regions,
        profile.opaque_effect_regions,
        profile.dynamic_effect_handler_candidates,
        profile.dynamic_effect_region_plans,
        profile.finite_dynamic_effect_region_plans,
        profile.dynamic_effect_thunk_argument_plans,
        profile.dynamic_effect_thunk_specialization_seeds,
        profile.ready_dynamic_effect_thunk_specialization_seeds,
        profile.dynamic_effect_thunk_rewrite_plans,
        profile.defunctionalized_dynamic_effect_thunk_rewrite_plans,
        profile.body_clone_dynamic_effect_thunk_rewrite_plans,
        profile.changed
    );
}

fn primitive_wrappers(module: &CpsReprAbiModule) -> HashMap<String, PrimitiveWrapper> {
    module
        .functions
        .iter()
        .chain(&module.roots)
        .filter_map(primitive_wrapper)
        .collect()
}

fn primitive_wrapper(function: &CpsReprAbiFunction) -> Option<(String, PrimitiveWrapper)> {
    if !function.handlers.is_empty() {
        return None;
    }
    let continuation = function
        .continuations
        .iter()
        .find(|continuation| continuation.id == function.entry)?;
    if !continuation.environment.is_empty() || continuation.stmts.len() != 1 {
        return None;
    }
    let [CpsStmt::Primitive { dest, op, args }] = continuation.stmts.as_slice() else {
        return None;
    };
    if !matches!(continuation.terminator, CpsTerminator::Return(value) if value == *dest) {
        return None;
    }
    let params = continuation
        .params
        .iter()
        .map(|param| param.value)
        .collect::<Vec<_>>();
    if function
        .params
        .iter()
        .map(|param| param.value)
        .collect::<Vec<_>>()
        != params
    {
        return None;
    }
    if *args != params {
        return None;
    }
    Some((
        function.name.clone(),
        PrimitiveWrapper {
            op: *op,
            arity: params.len(),
        },
    ))
}

fn reify_direct_primitive_stmt(
    stmt: &mut CpsStmt,
    primitives: &HashMap<String, PrimitiveWrapper>,
) -> usize {
    let CpsStmt::DirectCall { dest, target, args } = stmt else {
        return 0;
    };
    let Some(primitive) = primitives.get(target) else {
        return 0;
    };
    if primitive.arity != args.len() {
        return 0;
    }
    *stmt = CpsStmt::Primitive {
        dest: *dest,
        op: primitive.op,
        args: args.clone(),
    };
    1
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PrimitiveWrapper {
    op: typed_ir::PrimitiveOp,
    arity: usize,
}

fn pure_callable_functions(module: &CpsReprAbiModule) -> HashSet<String> {
    module
        .functions
        .iter()
        .filter(|function| function_is_pure_callable(function))
        .map(|function| function.name.clone())
        .collect()
}

fn function_is_pure_callable(function: &CpsReprAbiFunction) -> bool {
    function.handlers.is_empty()
        && function
            .continuations
            .iter()
            .all(|continuation| continuation.environment.is_empty())
        && function
            .continuations
            .iter()
            .flat_map(|continuation| &continuation.stmts)
            .all(stmt_is_direct_call_safe)
        && function
            .continuations
            .iter()
            .all(|continuation| terminator_is_direct_call_safe(&continuation.terminator))
}

fn stmt_is_direct_call_safe(stmt: &CpsStmt) -> bool {
    matches!(
        stmt,
        CpsStmt::Literal { .. }
            | CpsStmt::Tuple { .. }
            | CpsStmt::Record { .. }
            | CpsStmt::RecordWithoutFields { .. }
            | CpsStmt::Variant { .. }
            | CpsStmt::Select { .. }
            | CpsStmt::SelectWithDefault { .. }
            | CpsStmt::RecordHasField { .. }
            | CpsStmt::TupleGet { .. }
            | CpsStmt::VariantTagEq { .. }
            | CpsStmt::VariantPayload { .. }
            | CpsStmt::Primitive { .. }
            | CpsStmt::DirectCall { .. }
    )
}

fn terminator_is_direct_call_safe(terminator: &CpsTerminator) -> bool {
    matches!(
        terminator,
        CpsTerminator::Return(_) | CpsTerminator::Continue { .. } | CpsTerminator::Branch { .. }
    )
}

fn rewrite_pure_effectful_calls_in_function(
    function: &mut CpsReprAbiFunction,
    pure_functions: &HashSet<String>,
) -> usize {
    let resumable = scalar_resume_continuations(function);
    let mut next_value = next_function_value_id(function);
    let mut count = 0;

    for continuation in &mut function.continuations {
        let CpsTerminator::EffectfulCall {
            target,
            args,
            resume,
        } = &continuation.terminator
        else {
            continue;
        };
        if !pure_functions.contains(target) || !resumable.contains(resume) {
            continue;
        }
        let dest = next_value;
        next_value.0 += 1;
        continuation.stmts.push(CpsStmt::DirectCall {
            dest,
            target: target.clone(),
            args: args.clone(),
        });
        continuation.terminator = CpsTerminator::Continue {
            target: *resume,
            args: vec![dest],
        };
        count += 1;
    }

    count
}

fn fold_constant_branch_in_continuation(
    continuation: &mut CpsReprAbiContinuation,
    empty_param_continuations: &HashSet<CpsContinuationId>,
) -> usize {
    let (cond, then_cont, else_cont) = match &continuation.terminator {
        CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        } => (*cond, *then_cont, *else_cont),
        _ => return 0,
    };
    let Some(value) = local_bool_literal(continuation, cond) else {
        return 0;
    };
    let target = if value { then_cont } else { else_cont };
    if !empty_param_continuations.contains(&target) {
        return 0;
    }
    continuation.terminator = CpsTerminator::Continue {
        target,
        args: Vec::new(),
    };
    1
}

fn local_bool_literal(continuation: &CpsReprAbiContinuation, value: CpsValueId) -> Option<bool> {
    continuation.stmts.iter().find_map(|stmt| match stmt {
        CpsStmt::Literal {
            dest,
            literal: crate::cps_ir::CpsLiteral::Bool(bool_value),
        } if *dest == value => Some(*bool_value),
        _ => None,
    })
}

fn scalar_resume_continuations(function: &CpsReprAbiFunction) -> HashSet<CpsContinuationId> {
    function
        .continuations
        .iter()
        .filter(|continuation| {
            continuation.environment.is_empty() && continuation.params.len() == 1
        })
        .map(|continuation| continuation.id)
        .collect()
}

fn partial_closure_wrappers(
    function: &CpsReprAbiFunction,
) -> HashMap<CpsContinuationId, PartialClosureWrapper> {
    function
        .continuations
        .iter()
        .filter_map(partial_closure_wrapper)
        .collect()
}

fn partial_closure_wrapper(
    continuation: &CpsReprAbiContinuation,
) -> Option<(CpsContinuationId, PartialClosureWrapper)> {
    if continuation.params.len() != 1 || continuation.stmts.len() != 1 {
        return None;
    }
    let [stmt] = continuation.stmts.as_slice() else {
        return None;
    };
    let Some((dest, call, args)) = partial_closure_call_shape(stmt) else {
        return None;
    };
    if !matches!(continuation.terminator, CpsTerminator::Return(value) if value == dest) {
        return None;
    }
    let captured = continuation
        .environment
        .iter()
        .map(|slot| slot.value)
        .collect::<Vec<_>>();
    let param = continuation.params[0].value;
    if args.len() != captured.len() + 1 {
        return None;
    }
    if args[..captured.len()] != captured {
        return None;
    }
    if args[captured.len()] != param {
        return None;
    }
    Some((continuation.id, PartialClosureWrapper { call, captured }))
}

fn partial_closure_call_shape(
    stmt: &CpsStmt,
) -> Option<(CpsValueId, PartialClosureCall, &[CpsValueId])> {
    match stmt {
        CpsStmt::DirectCall { dest, target, args } => Some((
            *dest,
            PartialClosureCall::Direct {
                target: target.clone(),
            },
            args,
        )),
        CpsStmt::Primitive { dest, op, args } => {
            Some((*dest, PartialClosureCall::Primitive { op: *op }, args))
        }
        _ => None,
    }
}

fn reify_local_partial_closure_calls_in_continuation(
    continuation: &mut CpsReprAbiContinuation,
    wrappers: &HashMap<CpsContinuationId, PartialClosureWrapper>,
    resumable: &HashSet<CpsContinuationId>,
    next_value: &mut CpsValueId,
) -> usize {
    reify_partial_closure_calls_in_continuation(
        continuation,
        wrappers,
        &HashMap::new(),
        resumable,
        next_value,
    )
}

fn reify_known_closure_parameter_calls_in_function(
    function: &mut CpsReprAbiFunction,
    wrappers: &HashMap<CpsContinuationId, PartialClosureWrapper>,
) -> usize {
    let closure_values = local_closure_values(function, wrappers);
    if closure_values.is_empty() {
        return 0;
    }
    let parameter_wrappers = known_closure_parameter_wrappers(function, &closure_values);
    if parameter_wrappers.is_empty() {
        return 0;
    }

    let resumable = scalar_resume_continuations(function);
    let mut next_value = next_function_value_id(function);
    let mut count = 0;
    for continuation in &mut function.continuations {
        let Some(initial_closures) = parameter_wrappers.get(&continuation.id) else {
            continue;
        };
        count += reify_partial_closure_calls_in_continuation(
            continuation,
            wrappers,
            initial_closures,
            &resumable,
            &mut next_value,
        );
    }
    count
}

fn direct_style_closure_inline_candidates(
    function: &CpsReprAbiFunction,
) -> HashMap<CpsContinuationId, DirectStyleClosureInline> {
    function
        .continuations
        .iter()
        .filter_map(direct_style_closure_inline_candidate)
        .collect()
}

fn direct_style_closure_inline_candidate(
    continuation: &CpsReprAbiContinuation,
) -> Option<(CpsContinuationId, DirectStyleClosureInline)> {
    if continuation.params.len() != 1 || continuation.stmts.len() > 12 {
        return None;
    }
    if !continuation.stmts.iter().all(direct_style_stmt) {
        return None;
    }
    let CpsTerminator::Return(result) = continuation.terminator else {
        return None;
    };
    if !continuation
        .stmts
        .iter()
        .any(|stmt| stmt_dest(stmt) == Some(result))
    {
        return None;
    }
    Some((
        continuation.id,
        DirectStyleClosureInline {
            param: continuation.params[0].value,
            stmts: continuation.stmts.clone(),
            result,
        },
    ))
}

fn inline_local_direct_style_closure_calls_in_function(
    function: &mut CpsReprAbiFunction,
    candidates: &HashMap<CpsContinuationId, DirectStyleClosureInline>,
    next_value: &mut CpsValueId,
) -> usize {
    let mut count = 0;
    for continuation in &mut function.continuations {
        let mut closures = HashMap::<CpsValueId, DirectStyleClosureInline>::new();
        let mut stmts = Vec::with_capacity(continuation.stmts.len());
        for stmt in continuation.stmts.drain(..) {
            match stmt {
                CpsStmt::MakeClosure { dest, entry } => {
                    if let Some(candidate) = candidates.get(&entry) {
                        closures.insert(dest, candidate.clone());
                    }
                    stmts.push(CpsStmt::MakeClosure { dest, entry });
                }
                CpsStmt::MakeRecursiveClosure { dest, entry } => {
                    closures.remove(&dest);
                    stmts.push(CpsStmt::MakeRecursiveClosure { dest, entry });
                }
                CpsStmt::ApplyClosure { dest, closure, arg } => {
                    let Some(candidate) = closures.get(&closure) else {
                        stmts.push(CpsStmt::ApplyClosure { dest, closure, arg });
                        continue;
                    };
                    stmts.extend(candidate.inline_stmts(dest, arg, next_value));
                    count += 1;
                }
                stmt => {
                    if let Some(dest) = stmt_dest(&stmt) {
                        closures.remove(&dest);
                    }
                    stmts.push(stmt);
                }
            }
        }
        continuation.stmts = stmts;
    }
    count
}

fn reify_partial_closure_calls_in_continuation(
    continuation: &mut CpsReprAbiContinuation,
    wrappers: &HashMap<CpsContinuationId, PartialClosureWrapper>,
    initial_closures: &HashMap<CpsValueId, PartialClosureWrapper>,
    resumable: &HashSet<CpsContinuationId>,
    next_value: &mut CpsValueId,
) -> usize {
    let mut closures = initial_closures.clone();
    let mut count = 0;
    for stmt in &mut continuation.stmts {
        match stmt {
            CpsStmt::MakeClosure { dest, entry } => {
                if let Some(wrapper) = wrappers.get(entry) {
                    closures.insert(*dest, wrapper.clone());
                }
            }
            CpsStmt::MakeRecursiveClosure { dest, .. } => {
                closures.remove(dest);
            }
            CpsStmt::ApplyClosure { dest, closure, arg } => {
                let Some(wrapper) = closures.get(closure) else {
                    continue;
                };
                let mut args = wrapper.captured.clone();
                args.push(*arg);
                *stmt = wrapper.call.to_stmt(*dest, args);
                count += 1;
            }
            _ => {}
        }
    }
    count += reify_partial_closure_terminator(
        &mut continuation.stmts,
        &mut continuation.terminator,
        &closures,
        resumable,
        next_value,
    );
    count
}

fn reify_partial_closure_terminator(
    stmts: &mut Vec<CpsStmt>,
    terminator: &mut CpsTerminator,
    closures: &HashMap<CpsValueId, PartialClosureWrapper>,
    resumable: &HashSet<CpsContinuationId>,
    next_value: &mut CpsValueId,
) -> usize {
    let (closure, arg, resume) = match terminator {
        CpsTerminator::EffectfulApply {
            closure,
            arg,
            resume,
        } => (*closure, *arg, *resume),
        _ => return 0,
    };
    let Some(wrapper) = closures.get(&closure) else {
        return 0;
    };
    let mut args = wrapper.captured.clone();
    args.push(arg);
    match &wrapper.call {
        PartialClosureCall::Direct { target } => {
            *terminator = CpsTerminator::EffectfulCall {
                target: target.clone(),
                args,
                resume,
            };
            1
        }
        PartialClosureCall::Primitive { op } if resumable.contains(&resume) => {
            let dest = *next_value;
            next_value.0 += 1;
            stmts.push(CpsStmt::Primitive {
                dest,
                op: *op,
                args,
            });
            *terminator = CpsTerminator::Continue {
                target: resume,
                args: vec![dest],
            };
            1
        }
        PartialClosureCall::Primitive { .. } => 0,
    }
}

fn local_closure_values(
    function: &CpsReprAbiFunction,
    wrappers: &HashMap<CpsContinuationId, PartialClosureWrapper>,
) -> HashMap<CpsValueId, PartialClosureWrapper> {
    let mut closures = HashMap::new();
    for continuation in &function.continuations {
        for stmt in &continuation.stmts {
            match stmt {
                CpsStmt::MakeClosure { dest, entry } => {
                    let Some(wrapper) = wrappers.get(entry) else {
                        continue;
                    };
                    closures.insert(*dest, wrapper.clone());
                }
                CpsStmt::MakeRecursiveClosure { dest, .. } => {
                    closures.remove(dest);
                }
                _ => {}
            }
        }
    }
    closures
}

fn known_closure_parameter_wrappers(
    function: &CpsReprAbiFunction,
    closure_values: &HashMap<CpsValueId, PartialClosureWrapper>,
) -> HashMap<CpsContinuationId, HashMap<CpsValueId, PartialClosureWrapper>> {
    let continuations = function
        .continuations
        .iter()
        .map(|continuation| (continuation.id, continuation))
        .collect::<HashMap<_, _>>();
    let references = continuation_references(function);
    let protected = protected_continuations(function);
    let mut candidates: HashMap<CpsContinuationId, Vec<KnownClosureParameterCandidate>> =
        HashMap::new();
    let mut blocked = HashSet::new();

    for continuation in &function.continuations {
        let CpsTerminator::Continue { target, args } = &continuation.terminator else {
            continue;
        };
        if protected.contains(target) {
            continue;
        }
        let Some(target_continuation) = continuations.get(target) else {
            continue;
        };
        let Some(reference) = references.get(target) else {
            continue;
        };
        if reference.total != reference.continue_calls
            || args.len() != target_continuation.params.len()
        {
            blocked.insert(*target);
            continue;
        }

        let slots = candidates.entry(*target).or_insert_with(|| {
            vec![KnownClosureParameterCandidate::Unseen; target_continuation.params.len()]
        });
        for (index, arg) in args.iter().enumerate() {
            let adapted = closure_values
                .get(arg)
                .and_then(|wrapper| wrapper.rebase_for_continue(args, &target_continuation.params));
            slots[index].merge(adapted);
        }
    }

    blocked.into_iter().for_each(|target| {
        candidates.remove(&target);
    });

    candidates
        .into_iter()
        .filter_map(|(target, slots)| {
            let continuation = continuations.get(&target)?;
            let known = continuation
                .params
                .iter()
                .zip(slots)
                .filter_map(|(param, slot)| match slot {
                    KnownClosureParameterCandidate::Known(wrapper) => Some((param.value, wrapper)),
                    KnownClosureParameterCandidate::Unseen
                    | KnownClosureParameterCandidate::Conflict => None,
                })
                .collect::<HashMap<_, _>>();
            (!known.is_empty()).then_some((target, known))
        })
        .collect()
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum KnownClosureParameterCandidate {
    Unseen,
    Known(PartialClosureWrapper),
    Conflict,
}

impl KnownClosureParameterCandidate {
    fn merge(&mut self, wrapper: Option<PartialClosureWrapper>) {
        let Some(wrapper) = wrapper else {
            *self = Self::Conflict;
            return;
        };
        match self {
            Self::Unseen => *self = Self::Known(wrapper),
            Self::Known(current) if *current == wrapper => {}
            Self::Known(_) | Self::Conflict => *self = Self::Conflict,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PartialClosureWrapper {
    call: PartialClosureCall,
    captured: Vec<CpsValueId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DirectStyleClosureInline {
    param: CpsValueId,
    stmts: Vec<CpsStmt>,
    result: CpsValueId,
}

impl DirectStyleClosureInline {
    fn inline_stmts(
        &self,
        dest: CpsValueId,
        arg: CpsValueId,
        next_value: &mut CpsValueId,
    ) -> Vec<CpsStmt> {
        let mut substitution = HashMap::from([(self.param, arg), (self.result, dest)]);
        for stmt in &self.stmts {
            if let Some(value) = stmt_dest(stmt) {
                substitution.entry(value).or_insert_with(|| {
                    let fresh = *next_value;
                    next_value.0 += 1;
                    fresh
                });
            }
        }
        self.stmts
            .iter()
            .cloned()
            .map(|stmt| substitute_pure_inline_stmt_values(stmt, &substitution))
            .collect()
    }
}

impl PartialClosureWrapper {
    fn rebase_for_continue(
        &self,
        supplied_args: &[CpsValueId],
        target_params: &[CpsReprAbiValue],
    ) -> Option<Self> {
        if supplied_args.len() != target_params.len() {
            return None;
        }
        let captured = self
            .captured
            .iter()
            .map(|captured| {
                supplied_args
                    .iter()
                    .position(|arg| arg == captured)
                    .map(|index| target_params[index].value)
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Self {
            call: self.call.clone(),
            captured,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum PartialClosureCall {
    Direct { target: String },
    Primitive { op: typed_ir::PrimitiveOp },
}

impl PartialClosureCall {
    fn to_stmt(&self, dest: CpsValueId, args: Vec<CpsValueId>) -> CpsStmt {
        match self {
            PartialClosureCall::Direct { target } => CpsStmt::DirectCall {
                dest,
                target: target.clone(),
                args,
            },
            PartialClosureCall::Primitive { op } => CpsStmt::Primitive {
                dest,
                op: *op,
                args,
            },
        }
    }
}

fn pure_direct_inline_candidates(module: &CpsReprAbiModule) -> HashMap<String, PureDirectInline> {
    module
        .functions
        .iter()
        .filter_map(pure_direct_inline_candidate)
        .collect()
}

fn pure_direct_inline_candidate(
    function: &CpsReprAbiFunction,
) -> Option<(String, PureDirectInline)> {
    if !function.handlers.is_empty() || function.continuations.len() != 1 {
        return None;
    }
    let continuation = function
        .continuations
        .iter()
        .find(|continuation| continuation.id == function.entry)?;
    if !continuation.environment.is_empty() || continuation.stmts.len() > 16 {
        return None;
    }
    if continuation.params.len() != function.params.len() {
        return None;
    }
    if continuation
        .params
        .iter()
        .map(|param| param.value)
        .ne(function.params.iter().map(|param| param.value))
    {
        return None;
    }
    if !continuation.stmts.iter().all(pure_direct_inline_stmt) {
        return None;
    }
    let CpsTerminator::Return(result) = continuation.terminator else {
        return None;
    };
    if !continuation
        .stmts
        .iter()
        .any(|stmt| stmt_dest(stmt) == Some(result))
    {
        return None;
    }
    Some((
        function.name.clone(),
        PureDirectInline {
            params: continuation
                .params
                .iter()
                .map(|param| param.value)
                .collect(),
            stmts: continuation.stmts.clone(),
            result,
        },
    ))
}

fn pure_direct_inline_stmt(stmt: &CpsStmt) -> bool {
    matches!(
        stmt,
        CpsStmt::Literal { .. }
            | CpsStmt::Tuple { .. }
            | CpsStmt::Record { .. }
            | CpsStmt::RecordWithoutFields { .. }
            | CpsStmt::Variant { .. }
            | CpsStmt::Select { .. }
            | CpsStmt::SelectWithDefault { .. }
            | CpsStmt::RecordHasField { .. }
            | CpsStmt::TupleGet { .. }
            | CpsStmt::VariantTagEq { .. }
            | CpsStmt::VariantPayload { .. }
            | CpsStmt::Primitive { .. }
    )
}

fn inline_pure_direct_calls_in_function(
    function: &mut CpsReprAbiFunction,
    candidates: &HashMap<String, PureDirectInline>,
) -> usize {
    let mut next_value = next_function_value_id(function);
    let mut count = 0;
    for continuation in &mut function.continuations {
        let mut stmts = Vec::with_capacity(continuation.stmts.len());
        for stmt in continuation.stmts.drain(..) {
            let CpsStmt::DirectCall { dest, target, args } = &stmt else {
                stmts.push(stmt);
                continue;
            };
            let Some(candidate) = candidates.get(target) else {
                stmts.push(stmt);
                continue;
            };
            if candidate.params.len() != args.len() {
                stmts.push(stmt);
                continue;
            }
            let mut substitution = candidate
                .params
                .iter()
                .copied()
                .zip(args.iter().copied())
                .collect::<HashMap<_, _>>();
            for stmt in &candidate.stmts {
                if let Some(value) = stmt_dest(stmt) {
                    substitution.entry(value).or_insert_with(|| {
                        let fresh = next_value;
                        next_value.0 += 1;
                        fresh
                    });
                }
            }
            substitution.insert(candidate.result, *dest);
            stmts.extend(
                candidate
                    .stmts
                    .iter()
                    .cloned()
                    .map(|stmt| substitute_pure_inline_stmt_values(stmt, &substitution)),
            );
            count += 1;
        }
        continuation.stmts = stmts;
    }
    count
}

fn inline_ready_finite_thunk_calls_in_function(
    function: &mut CpsReprAbiFunction,
    seeds: &[DynamicEffectThunkSpecializationSeed],
    callees: &HashMap<String, CpsReprAbiFunction>,
) -> usize {
    let seeds_by_call = seeds
        .iter()
        .filter(|seed| seed.caller == function.name)
        .filter(|seed| seed.callee != function.name)
        .filter(|seed| seed.call_continuation == function.entry)
        .map(|seed| ((seed.call_continuation, seed.call_stmt_index), seed))
        .collect::<HashMap<_, _>>();
    if seeds_by_call.is_empty() {
        return 0;
    }

    let original_len = function.continuations.len();
    let mut inlined = 0;
    for index in 0..original_len {
        let continuation_id = function.continuations[index].id;
        let stmt_len = function.continuations[index].stmts.len();
        for stmt_index in 0..stmt_len {
            let Some(seed) = seeds_by_call.get(&(continuation_id, stmt_index)) else {
                continue;
            };
            let Some(callee) = callees.get(&seed.callee) else {
                continue;
            };
            inlined += inline_ready_finite_thunk_call_at(function, index, stmt_index, seed, callee);
            break;
        }
    }
    inlined
}

fn inline_ready_finite_thunk_call_at(
    function: &mut CpsReprAbiFunction,
    continuation_index: usize,
    stmt_index: usize,
    seed: &DynamicEffectThunkSpecializationSeed,
    callee: &CpsReprAbiFunction,
) -> usize {
    if callee.handlers.is_empty() || callee.continuations.is_empty() {
        return 0;
    }
    let Some(callee_entry) = callee
        .continuations
        .iter()
        .find(|continuation| continuation.id == callee.entry)
    else {
        return 0;
    };
    let continuation = &function.continuations[continuation_index];
    let Some(CpsStmt::DirectCall { dest, target, args }) = continuation.stmts.get(stmt_index)
    else {
        return 0;
    };
    if target != &seed.callee || args.len() != callee.params.len() {
        return 0;
    }
    let dest = *dest;
    let args = args.clone();
    let return_lane = continuation.return_lane;
    let rest_environment = continuation.environment.clone();
    let (rest_param, rest_stmts) =
        rest_after_inlined_thunk_return(&continuation.stmts, stmt_index + 1, dest);
    let rest_terminator = continuation.terminator.clone();

    let rest_id = next_function_continuation_id(function);
    let mut next_continuation = CpsContinuationId(rest_id.0 + 1);
    let mut next_value = next_function_value_id(function);
    let mut next_handler = next_function_handler_id(function);
    let continuation_map = callee
        .continuations
        .iter()
        .map(|continuation| {
            let fresh = next_continuation;
            next_continuation.0 += 1;
            (continuation.id, fresh)
        })
        .collect::<HashMap<_, _>>();
    let handler_map = callee
        .handlers
        .iter()
        .map(|handler| {
            let fresh = next_handler;
            next_handler.0 += 1;
            (handler.id, fresh)
        })
        .collect::<HashMap<_, _>>();
    let value_map = callee
        .value_ids()
        .into_iter()
        .map(|value| {
            let fresh = next_value;
            next_value.0 += 1;
            (value, fresh)
        })
        .collect::<HashMap<_, _>>();
    let Some(cloned_entry) = continuation_map.get(&callee.entry).copied() else {
        return 0;
    };

    let rest_continuation = CpsReprAbiContinuation {
        id: rest_id,
        params: vec![CpsReprAbiValue {
            value: rest_param,
            lane: callee_entry.return_lane,
        }],
        environment: rest_environment,
        shot_kind: CpsShotKind::OneShot,
        return_lane,
        stmts: rest_stmts,
        terminator: rest_terminator,
    };
    let cloned_handlers = callee
        .handlers
        .iter()
        .cloned()
        .map(|handler| remap_handler(handler, &continuation_map, &handler_map))
        .collect::<Vec<_>>();
    let cloned_continuations = callee
        .continuations
        .iter()
        .cloned()
        .map(|continuation| {
            remap_inlined_continuation(
                continuation,
                rest_id,
                &continuation_map,
                &handler_map,
                &value_map,
            )
        })
        .collect::<Vec<_>>();

    let continuation = &mut function.continuations[continuation_index];
    continuation.stmts.truncate(stmt_index);
    continuation.terminator = CpsTerminator::Continue {
        target: cloned_entry,
        args,
    };
    function.continuations.push(rest_continuation);
    function.continuations.extend(cloned_continuations);
    function.handlers.extend(cloned_handlers);
    1
}

fn defunctionalize_finite_handler_thunk_calls_in_function(
    function: &mut CpsReprAbiFunction,
    plans: &[DynamicEffectThunkRewritePlan],
    callees: &HashMap<String, CpsReprAbiFunction>,
) -> usize {
    let plans_by_call = plans
        .iter()
        .filter(|plan| plan.caller == function.name)
        .filter(|plan| plan.callee != function.name)
        .filter(|plan| plan.call_continuation == function.entry)
        .map(|plan| ((plan.call_continuation, plan.call_stmt_index), plan))
        .collect::<HashMap<_, _>>();
    if plans_by_call.is_empty() {
        return 0;
    }

    let original_len = function.continuations.len();
    let mut rewritten = 0;
    for index in 0..original_len {
        let continuation_id = function.continuations[index].id;
        let stmt_len = function.continuations[index].stmts.len();
        for stmt_index in 0..stmt_len {
            let Some(plan) = plans_by_call.get(&(continuation_id, stmt_index)) else {
                continue;
            };
            let Some(callee) = callees.get(&plan.callee) else {
                continue;
            };
            rewritten += defunctionalize_finite_handler_thunk_call_at(
                function, index, stmt_index, plan, callee,
            );
            break;
        }
    }
    rewritten
}

fn defunctionalize_finite_handler_thunk_call_at(
    function: &mut CpsReprAbiFunction,
    continuation_index: usize,
    stmt_index: usize,
    plan: &DynamicEffectThunkRewritePlan,
    callee: &CpsReprAbiFunction,
) -> usize {
    if plan.finite_callee_boundaries.len() != 1 || callee.continuations.is_empty() {
        return 0;
    }
    let boundary = plan.finite_callee_boundaries[0];
    let Some(callee_entry) = callee
        .continuations
        .iter()
        .find(|continuation| continuation.id == callee.entry)
    else {
        return 0;
    };
    let Some(callee_boundary) = callee
        .continuations
        .iter()
        .find(|continuation| continuation.id == boundary)
    else {
        return 0;
    };
    let CpsTerminator::EffectfulForce {
        resume: boundary_resume,
        ..
    } = callee_boundary.terminator
    else {
        return 0;
    };

    let Some(thunk_region) = continuation_region(function, plan.thunk_entry) else {
        return 0;
    };
    if thunk_region_has_unsupported_control(function, &thunk_region) {
        return 0;
    }
    if region_has_effectful_terminator(function, &thunk_region) {
        return 0;
    }

    let continuation = &function.continuations[continuation_index];
    let Some(CpsStmt::DirectCall { dest, target, args }) = continuation.stmts.get(stmt_index)
    else {
        return 0;
    };
    if target != &plan.callee || args.len() != callee.params.len() {
        return 0;
    }

    let dest = *dest;
    let args = args.clone();
    let return_lane = continuation.return_lane;
    let rest_environment = continuation.environment.clone();
    let (rest_param, rest_stmts) =
        rest_after_inlined_thunk_return(&continuation.stmts, stmt_index + 1, dest);
    let rest_terminator = continuation.terminator.clone();

    let rest_id = next_function_continuation_id(function);
    let mut next_continuation = CpsContinuationId(rest_id.0 + 1);
    let mut next_value = next_function_value_id(function);
    let mut next_handler = next_function_handler_id(function);

    let continuation_map = callee
        .continuations
        .iter()
        .map(|continuation| {
            let fresh = next_continuation;
            next_continuation.0 += 1;
            (continuation.id, fresh)
        })
        .collect::<HashMap<_, _>>();
    let handler_map = callee
        .handlers
        .iter()
        .map(|handler| {
            let fresh = next_handler;
            next_handler.0 += 1;
            (handler.id, fresh)
        })
        .collect::<HashMap<_, _>>();
    let value_map = callee
        .value_ids()
        .into_iter()
        .map(|value| {
            let fresh = next_value;
            next_value.0 += 1;
            (value, fresh)
        })
        .collect::<HashMap<_, _>>();
    let thunk_continuation_map = thunk_region
        .iter()
        .map(|id| {
            let fresh = next_continuation;
            next_continuation.0 += 1;
            (*id, fresh)
        })
        .collect::<HashMap<_, _>>();
    let thunk_value_map = local_value_defs_for_continuations(function, &thunk_region)
        .into_iter()
        .map(|value| {
            let fresh = next_value;
            next_value.0 += 1;
            (value, fresh)
        })
        .collect::<HashMap<_, _>>();

    let Some(cloned_entry) = continuation_map.get(&callee.entry).copied() else {
        return 0;
    };
    let Some(cloned_boundary) = continuation_map.get(&boundary).copied() else {
        return 0;
    };
    let Some(cloned_boundary_resume) = continuation_map.get(&boundary_resume).copied() else {
        return 0;
    };
    let Some(cloned_thunk_entry) = thunk_continuation_map.get(&plan.thunk_entry).copied() else {
        return 0;
    };

    let rest_continuation = CpsReprAbiContinuation {
        id: rest_id,
        params: vec![CpsReprAbiValue {
            value: rest_param,
            lane: callee_entry.return_lane,
        }],
        environment: rest_environment,
        shot_kind: CpsShotKind::OneShot,
        return_lane,
        stmts: rest_stmts,
        terminator: rest_terminator,
    };
    let cloned_handlers = callee
        .handlers
        .iter()
        .cloned()
        .map(|handler| remap_handler(handler, &continuation_map, &handler_map))
        .collect::<Vec<_>>();
    let mut cloned_continuations = callee
        .continuations
        .iter()
        .cloned()
        .map(|continuation| {
            remap_inlined_continuation(
                continuation,
                rest_id,
                &continuation_map,
                &handler_map,
                &value_map,
            )
        })
        .collect::<Vec<_>>();
    if let Some(cloned_force_boundary) = cloned_continuations
        .iter_mut()
        .find(|continuation| continuation.id == cloned_boundary)
    {
        cloned_force_boundary.terminator = CpsTerminator::Continue {
            target: cloned_thunk_entry,
            args: Vec::new(),
        };
    } else {
        return 0;
    }

    let continuation_by_id = function
        .continuations
        .iter()
        .map(|continuation| (continuation.id, continuation.clone()))
        .collect::<HashMap<_, _>>();
    let cloned_thunk_continuations = thunk_region
        .iter()
        .filter_map(|id| continuation_by_id.get(id).cloned())
        .map(|continuation| {
            remap_inlined_continuation(
                continuation,
                cloned_boundary_resume,
                &thunk_continuation_map,
                &HashMap::new(),
                &thunk_value_map,
            )
        })
        .collect::<Vec<_>>();

    let continuation = &mut function.continuations[continuation_index];
    continuation.stmts.truncate(stmt_index);
    continuation.terminator = CpsTerminator::Continue {
        target: cloned_entry,
        args,
    };
    function.continuations.push(rest_continuation);
    function.continuations.extend(cloned_continuations);
    function.continuations.extend(cloned_thunk_continuations);
    function.handlers.extend(cloned_handlers);
    1
}

fn rest_after_inlined_thunk_return(
    stmts: &[CpsStmt],
    start: usize,
    call_dest: CpsValueId,
) -> (CpsValueId, Vec<CpsStmt>) {
    let mut next = start;
    let mut value = call_dest;
    while let Some(CpsStmt::ForceThunk { dest, thunk }) = stmts.get(next) {
        if *thunk != value {
            break;
        }
        value = *dest;
        next += 1;
    }
    (value, stmts[next..].to_vec())
}

fn continuation_region(
    function: &CpsReprAbiFunction,
    entry: CpsContinuationId,
) -> Option<Vec<CpsContinuationId>> {
    let continuations = function
        .continuations
        .iter()
        .map(|continuation| (continuation.id, continuation))
        .collect::<HashMap<_, _>>();
    let mut visited = HashSet::new();
    let mut order = Vec::new();
    let mut queue = VecDeque::from([entry]);
    while let Some(id) = queue.pop_front() {
        if !visited.insert(id) {
            continue;
        }
        let continuation = continuations.get(&id)?;
        order.push(id);
        for successor in continuation_all_successors(&continuation.terminator) {
            queue.push_back(successor);
        }
    }
    Some(order)
}

fn continuation_all_successors(terminator: &CpsTerminator) -> Vec<CpsContinuationId> {
    match terminator {
        CpsTerminator::Continue { target, .. } => vec![*target],
        CpsTerminator::Branch {
            then_cont,
            else_cont,
            ..
        } => vec![*then_cont, *else_cont],
        CpsTerminator::Perform { resume, .. }
        | CpsTerminator::EffectfulCall { resume, .. }
        | CpsTerminator::EffectfulApply { resume, .. }
        | CpsTerminator::EffectfulForce { resume, .. } => vec![*resume],
        CpsTerminator::Return(_) => Vec::new(),
    }
}

fn thunk_region_has_unsupported_control(
    function: &CpsReprAbiFunction,
    region: &[CpsContinuationId],
) -> bool {
    let region = region.iter().copied().collect::<HashSet<_>>();
    function
        .continuations
        .iter()
        .filter(|continuation| region.contains(&continuation.id))
        .any(|continuation| {
            continuation.stmts.iter().any(|stmt| {
                matches!(
                    stmt,
                    CpsStmt::InstallHandler { .. }
                        | CpsStmt::UninstallHandler { .. }
                        | CpsStmt::ResumeWithHandler { .. }
                )
            })
        })
}

fn region_has_effectful_terminator(
    function: &CpsReprAbiFunction,
    region: &[CpsContinuationId],
) -> bool {
    let region = region.iter().copied().collect::<HashSet<_>>();
    function
        .continuations
        .iter()
        .filter(|continuation| region.contains(&continuation.id))
        .any(|continuation| {
            matches!(
                continuation.terminator,
                CpsTerminator::Perform { .. }
                    | CpsTerminator::EffectfulCall { .. }
                    | CpsTerminator::EffectfulApply { .. }
                    | CpsTerminator::EffectfulForce { .. }
            )
        })
}

fn local_value_defs_for_continuations(
    function: &CpsReprAbiFunction,
    region: &[CpsContinuationId],
) -> HashSet<CpsValueId> {
    let region = region.iter().copied().collect::<HashSet<_>>();
    function
        .continuations
        .iter()
        .filter(|continuation| region.contains(&continuation.id))
        .flat_map(|continuation| {
            continuation
                .params
                .iter()
                .map(|param| param.value)
                .chain(continuation.stmts.iter().filter_map(stmt_dest))
        })
        .collect()
}

trait CpsReprAbiFunctionValueIds {
    fn value_ids(&self) -> HashSet<CpsValueId>;
}

impl CpsReprAbiFunctionValueIds for CpsReprAbiFunction {
    fn value_ids(&self) -> HashSet<CpsValueId> {
        self.params
            .iter()
            .map(|value| value.value)
            .chain(
                self.continuations
                    .iter()
                    .flat_map(continuation_all_value_ids),
            )
            .collect()
    }
}

fn continuation_all_value_ids(
    continuation: &CpsReprAbiContinuation,
) -> impl Iterator<Item = CpsValueId> + '_ {
    continuation
        .params
        .iter()
        .map(|value| value.value)
        .chain(continuation.environment.iter().map(|slot| slot.value))
        .chain(continuation.stmts.iter().flat_map(stmt_all_values))
        .chain(terminator_values(&continuation.terminator))
}

fn stmt_all_values(stmt: &CpsStmt) -> Vec<CpsValueId> {
    stmt_dest(stmt)
        .into_iter()
        .chain(stmt_operands(stmt))
        .collect()
}

fn remap_handler(
    handler: CpsReprAbiHandler,
    continuations: &HashMap<CpsContinuationId, CpsContinuationId>,
    handlers: &HashMap<crate::cps_ir::CpsHandlerId, crate::cps_ir::CpsHandlerId>,
) -> CpsReprAbiHandler {
    CpsReprAbiHandler {
        id: remap_handler_id(handler.id, handlers),
        arms: handler
            .arms
            .into_iter()
            .map(|arm| CpsReprAbiHandlerArm {
                effect: arm.effect,
                entry: remap_continuation_id(arm.entry, continuations),
            })
            .collect(),
    }
}

fn remap_inlined_continuation(
    continuation: CpsReprAbiContinuation,
    rest_id: CpsContinuationId,
    continuations: &HashMap<CpsContinuationId, CpsContinuationId>,
    handlers: &HashMap<crate::cps_ir::CpsHandlerId, crate::cps_ir::CpsHandlerId>,
    values: &HashMap<CpsValueId, CpsValueId>,
) -> CpsReprAbiContinuation {
    CpsReprAbiContinuation {
        id: remap_continuation_id(continuation.id, continuations),
        params: continuation
            .params
            .into_iter()
            .map(|value| remap_abi_value(value, values))
            .collect(),
        environment: continuation
            .environment
            .into_iter()
            .map(|slot| remap_environment_slot(slot, values))
            .collect(),
        shot_kind: continuation.shot_kind,
        return_lane: continuation.return_lane,
        stmts: continuation
            .stmts
            .into_iter()
            .map(|stmt| remap_stmt(stmt, continuations, handlers, values))
            .collect(),
        terminator: match continuation.terminator {
            CpsTerminator::Return(value) => CpsTerminator::Continue {
                target: rest_id,
                args: vec![subst_value(value, values)],
            },
            terminator => remap_terminator(terminator, continuations, handlers, values),
        },
    }
}

fn remap_abi_value(
    value: CpsReprAbiValue,
    values: &HashMap<CpsValueId, CpsValueId>,
) -> CpsReprAbiValue {
    CpsReprAbiValue {
        value: subst_value(value.value, values),
        lane: value.lane,
    }
}

fn remap_environment_slot(
    slot: CpsReprAbiEnvironmentSlot,
    values: &HashMap<CpsValueId, CpsValueId>,
) -> CpsReprAbiEnvironmentSlot {
    CpsReprAbiEnvironmentSlot {
        index: slot.index,
        value: subst_value(slot.value, values),
        lane: slot.lane,
    }
}

fn remap_stmt(
    stmt: CpsStmt,
    continuations: &HashMap<CpsContinuationId, CpsContinuationId>,
    handlers: &HashMap<crate::cps_ir::CpsHandlerId, crate::cps_ir::CpsHandlerId>,
    values: &HashMap<CpsValueId, CpsValueId>,
) -> CpsStmt {
    let stmt = remap_stmt_values(stmt, values);
    match stmt {
        CpsStmt::MakeThunk { dest, entry } => CpsStmt::MakeThunk {
            dest,
            entry: remap_continuation_id(entry, continuations),
        },
        CpsStmt::MakeClosure { dest, entry } => CpsStmt::MakeClosure {
            dest,
            entry: remap_continuation_id(entry, continuations),
        },
        CpsStmt::MakeRecursiveClosure { dest, entry } => CpsStmt::MakeRecursiveClosure {
            dest,
            entry: remap_continuation_id(entry, continuations),
        },
        CpsStmt::ResumeWithHandler {
            dest,
            resumption,
            arg,
            handler,
            envs,
        } => CpsStmt::ResumeWithHandler {
            dest,
            resumption,
            arg,
            handler: remap_handler_id(handler, handlers),
            envs: remap_handler_envs(envs, continuations, values),
        },
        CpsStmt::InstallHandler {
            handler,
            envs,
            value,
            escape,
        } => CpsStmt::InstallHandler {
            handler: remap_handler_id(handler, handlers),
            envs: remap_handler_envs(envs, continuations, values),
            value: remap_continuation_id(value, continuations),
            escape: remap_continuation_id(escape, continuations),
        },
        CpsStmt::UninstallHandler { handler } => CpsStmt::UninstallHandler {
            handler: remap_handler_id(handler, handlers),
        },
        stmt => stmt,
    }
}

fn remap_stmt_values(stmt: CpsStmt, substitution: &HashMap<CpsValueId, CpsValueId>) -> CpsStmt {
    match stmt {
        CpsStmt::Literal { dest, literal } => CpsStmt::Literal {
            dest: subst_value(dest, substitution),
            literal,
        },
        CpsStmt::FreshGuard { dest, var } => CpsStmt::FreshGuard {
            dest: subst_value(dest, substitution),
            var,
        },
        CpsStmt::PeekGuard { dest } => CpsStmt::PeekGuard {
            dest: subst_value(dest, substitution),
        },
        CpsStmt::FindGuard { dest, guard } => CpsStmt::FindGuard {
            dest: subst_value(dest, substitution),
            guard: subst_value(guard, substitution),
        },
        CpsStmt::MakeThunk { dest, entry } => CpsStmt::MakeThunk {
            dest: subst_value(dest, substitution),
            entry,
        },
        CpsStmt::AddThunkBoundary {
            dest,
            thunk,
            guard,
            allowed,
            active,
        } => CpsStmt::AddThunkBoundary {
            dest: subst_value(dest, substitution),
            thunk: subst_value(thunk, substitution),
            guard: subst_value(guard, substitution),
            allowed,
            active,
        },
        CpsStmt::MakeClosure { dest, entry } => CpsStmt::MakeClosure {
            dest: subst_value(dest, substitution),
            entry,
        },
        CpsStmt::MakeRecursiveClosure { dest, entry } => CpsStmt::MakeRecursiveClosure {
            dest: subst_value(dest, substitution),
            entry,
        },
        CpsStmt::ForceThunk { dest, thunk } => CpsStmt::ForceThunk {
            dest: subst_value(dest, substitution),
            thunk: subst_value(thunk, substitution),
        },
        CpsStmt::Tuple { dest, items } => CpsStmt::Tuple {
            dest: subst_value(dest, substitution),
            items: subst_values(items, substitution),
        },
        CpsStmt::Record { dest, base, fields } => CpsStmt::Record {
            dest: subst_value(dest, substitution),
            base: base.map(|value| subst_value(value, substitution)),
            fields: fields
                .into_iter()
                .map(|field| CpsRecordField {
                    name: field.name,
                    value: subst_value(field.value, substitution),
                })
                .collect(),
        },
        CpsStmt::RecordWithoutFields { dest, base, fields } => CpsStmt::RecordWithoutFields {
            dest: subst_value(dest, substitution),
            base: subst_value(base, substitution),
            fields,
        },
        CpsStmt::Variant { dest, tag, value } => CpsStmt::Variant {
            dest: subst_value(dest, substitution),
            tag,
            value: value.map(|value| subst_value(value, substitution)),
        },
        CpsStmt::Select { dest, base, field } => CpsStmt::Select {
            dest: subst_value(dest, substitution),
            base: subst_value(base, substitution),
            field,
        },
        CpsStmt::SelectWithDefault {
            dest,
            base,
            field,
            default,
        } => CpsStmt::SelectWithDefault {
            dest: subst_value(dest, substitution),
            base: subst_value(base, substitution),
            field,
            default: subst_value(default, substitution),
        },
        CpsStmt::RecordHasField { dest, base, field } => CpsStmt::RecordHasField {
            dest: subst_value(dest, substitution),
            base: subst_value(base, substitution),
            field,
        },
        CpsStmt::TupleGet { dest, tuple, index } => CpsStmt::TupleGet {
            dest: subst_value(dest, substitution),
            tuple: subst_value(tuple, substitution),
            index,
        },
        CpsStmt::VariantTagEq { dest, variant, tag } => CpsStmt::VariantTagEq {
            dest: subst_value(dest, substitution),
            variant: subst_value(variant, substitution),
            tag,
        },
        CpsStmt::VariantPayload { dest, variant } => CpsStmt::VariantPayload {
            dest: subst_value(dest, substitution),
            variant: subst_value(variant, substitution),
        },
        CpsStmt::Primitive { dest, op, args } => CpsStmt::Primitive {
            dest: subst_value(dest, substitution),
            op,
            args: subst_values(args, substitution),
        },
        CpsStmt::DirectCall { dest, target, args } => CpsStmt::DirectCall {
            dest: subst_value(dest, substitution),
            target,
            args: subst_values(args, substitution),
        },
        CpsStmt::ApplyClosure { dest, closure, arg } => CpsStmt::ApplyClosure {
            dest: subst_value(dest, substitution),
            closure: subst_value(closure, substitution),
            arg: subst_value(arg, substitution),
        },
        CpsStmt::CloneContinuation { dest, source } => CpsStmt::CloneContinuation {
            dest: subst_value(dest, substitution),
            source: subst_value(source, substitution),
        },
        CpsStmt::Resume {
            dest,
            resumption,
            arg,
        } => CpsStmt::Resume {
            dest: subst_value(dest, substitution),
            resumption: subst_value(resumption, substitution),
            arg: subst_value(arg, substitution),
        },
        CpsStmt::ResumeWithHandler {
            dest,
            resumption,
            arg,
            handler,
            envs,
        } => CpsStmt::ResumeWithHandler {
            dest: subst_value(dest, substitution),
            resumption: subst_value(resumption, substitution),
            arg: subst_value(arg, substitution),
            handler,
            envs: subst_handler_envs(envs, substitution),
        },
        CpsStmt::InstallHandler {
            handler,
            envs,
            value,
            escape,
        } => CpsStmt::InstallHandler {
            handler,
            envs: subst_handler_envs(envs, substitution),
            value,
            escape,
        },
        CpsStmt::UninstallHandler { handler } => CpsStmt::UninstallHandler { handler },
    }
}

fn remap_terminator(
    terminator: CpsTerminator,
    continuations: &HashMap<CpsContinuationId, CpsContinuationId>,
    handlers: &HashMap<crate::cps_ir::CpsHandlerId, crate::cps_ir::CpsHandlerId>,
    values: &HashMap<CpsValueId, CpsValueId>,
) -> CpsTerminator {
    let terminator = substitute_terminator_values(terminator, values);
    match terminator {
        CpsTerminator::Continue { target, args } => CpsTerminator::Continue {
            target: remap_continuation_id(target, continuations),
            args,
        },
        CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        } => CpsTerminator::Branch {
            cond,
            then_cont: remap_continuation_id(then_cont, continuations),
            else_cont: remap_continuation_id(else_cont, continuations),
        },
        CpsTerminator::Perform {
            effect,
            payload,
            resume,
            handler,
            blocked,
        } => CpsTerminator::Perform {
            effect,
            payload,
            resume: remap_continuation_id(resume, continuations),
            handler: remap_handler_id(handler, handlers),
            blocked,
        },
        CpsTerminator::EffectfulCall {
            target,
            args,
            resume,
        } => CpsTerminator::EffectfulCall {
            target,
            args,
            resume: remap_continuation_id(resume, continuations),
        },
        CpsTerminator::EffectfulApply {
            closure,
            arg,
            resume,
        } => CpsTerminator::EffectfulApply {
            closure,
            arg,
            resume: remap_continuation_id(resume, continuations),
        },
        CpsTerminator::EffectfulForce { thunk, resume } => CpsTerminator::EffectfulForce {
            thunk,
            resume: remap_continuation_id(resume, continuations),
        },
        CpsTerminator::Return(value) => CpsTerminator::Return(value),
    }
}

fn remap_handler_envs(
    envs: Vec<CpsHandlerEnv>,
    continuations: &HashMap<CpsContinuationId, CpsContinuationId>,
    values: &HashMap<CpsValueId, CpsValueId>,
) -> Vec<CpsHandlerEnv> {
    envs.into_iter()
        .map(|env| CpsHandlerEnv {
            entry: remap_continuation_id(env.entry, continuations),
            values: subst_values(env.values, values),
            targets: subst_values(env.targets, values),
        })
        .collect()
}

fn remap_continuation_id(
    id: CpsContinuationId,
    continuations: &HashMap<CpsContinuationId, CpsContinuationId>,
) -> CpsContinuationId {
    continuations.get(&id).copied().unwrap_or(id)
}

fn remap_handler_id(
    id: crate::cps_ir::CpsHandlerId,
    handlers: &HashMap<crate::cps_ir::CpsHandlerId, crate::cps_ir::CpsHandlerId>,
) -> crate::cps_ir::CpsHandlerId {
    handlers.get(&id).copied().unwrap_or(id)
}

fn substitute_pure_inline_stmt_values(
    stmt: CpsStmt,
    substitution: &HashMap<CpsValueId, CpsValueId>,
) -> CpsStmt {
    match stmt {
        CpsStmt::Literal { dest, literal } => CpsStmt::Literal {
            dest: subst_value(dest, substitution),
            literal,
        },
        CpsStmt::Tuple { dest, items } => CpsStmt::Tuple {
            dest: subst_value(dest, substitution),
            items: subst_values(items, substitution),
        },
        CpsStmt::Record { dest, base, fields } => CpsStmt::Record {
            dest: subst_value(dest, substitution),
            base: base.map(|value| subst_value(value, substitution)),
            fields: fields
                .into_iter()
                .map(|field| CpsRecordField {
                    name: field.name,
                    value: subst_value(field.value, substitution),
                })
                .collect(),
        },
        CpsStmt::RecordWithoutFields { dest, base, fields } => CpsStmt::RecordWithoutFields {
            dest: subst_value(dest, substitution),
            base: subst_value(base, substitution),
            fields,
        },
        CpsStmt::Variant { dest, tag, value } => CpsStmt::Variant {
            dest: subst_value(dest, substitution),
            tag,
            value: value.map(|value| subst_value(value, substitution)),
        },
        CpsStmt::Select { dest, base, field } => CpsStmt::Select {
            dest: subst_value(dest, substitution),
            base: subst_value(base, substitution),
            field,
        },
        CpsStmt::SelectWithDefault {
            dest,
            base,
            field,
            default,
        } => CpsStmt::SelectWithDefault {
            dest: subst_value(dest, substitution),
            base: subst_value(base, substitution),
            field,
            default: subst_value(default, substitution),
        },
        CpsStmt::RecordHasField { dest, base, field } => CpsStmt::RecordHasField {
            dest: subst_value(dest, substitution),
            base: subst_value(base, substitution),
            field,
        },
        CpsStmt::TupleGet { dest, tuple, index } => CpsStmt::TupleGet {
            dest: subst_value(dest, substitution),
            tuple: subst_value(tuple, substitution),
            index,
        },
        CpsStmt::VariantTagEq { dest, variant, tag } => CpsStmt::VariantTagEq {
            dest: subst_value(dest, substitution),
            variant: subst_value(variant, substitution),
            tag,
        },
        CpsStmt::VariantPayload { dest, variant } => CpsStmt::VariantPayload {
            dest: subst_value(dest, substitution),
            variant: subst_value(variant, substitution),
        },
        CpsStmt::Primitive { dest, op, args } => CpsStmt::Primitive {
            dest: subst_value(dest, substitution),
            op,
            args: subst_values(args, substitution),
        },
        CpsStmt::DirectCall { dest, target, args } => CpsStmt::DirectCall {
            dest: subst_value(dest, substitution),
            target,
            args: subst_values(args, substitution),
        },
        stmt => stmt,
    }
}

fn next_function_value_id(function: &CpsReprAbiFunction) -> CpsValueId {
    let max_value = function
        .params
        .iter()
        .map(|value| value.value)
        .chain(
            function
                .continuations
                .iter()
                .flat_map(continuation_value_ids),
        )
        .map(|value| value.0)
        .max()
        .unwrap_or(0);
    CpsValueId(max_value + 1)
}

fn next_function_continuation_id(function: &CpsReprAbiFunction) -> CpsContinuationId {
    let max_id = function
        .continuations
        .iter()
        .map(|continuation| continuation.id.0)
        .max()
        .unwrap_or(0);
    CpsContinuationId(max_id + 1)
}

fn next_function_handler_id(function: &CpsReprAbiFunction) -> crate::cps_ir::CpsHandlerId {
    let max_id = function
        .handlers
        .iter()
        .map(|handler| handler.id.0)
        .max()
        .unwrap_or(0);
    crate::cps_ir::CpsHandlerId(max_id + 1)
}

fn continuation_value_ids(
    continuation: &CpsReprAbiContinuation,
) -> impl Iterator<Item = CpsValueId> + '_ {
    continuation
        .params
        .iter()
        .map(|value| value.value)
        .chain(continuation.environment.iter().map(|slot| slot.value))
        .chain(continuation.stmts.iter().filter_map(stmt_dest))
}

fn fold_structural_projections_in_continuation(continuation: &mut CpsReprAbiContinuation) -> usize {
    let mut aliases = HashMap::<CpsValueId, CpsValueId>::new();
    let mut tuples = HashMap::<CpsValueId, Vec<CpsValueId>>::new();
    let mut scalar_values = HashSet::<CpsValueId>::new();
    let mut stmts = Vec::with_capacity(continuation.stmts.len());
    let mut count = 0;

    for stmt in continuation.stmts.drain(..) {
        let stmt = substitute_stmt_values(stmt, &aliases);
        match stmt {
            CpsStmt::Tuple { dest, items } => {
                tuples.insert(dest, items.clone());
                stmts.push(CpsStmt::Tuple { dest, items });
            }
            CpsStmt::TupleGet { dest, tuple, index } => {
                if let Some(items) = tuples.get(&tuple) {
                    if let Some(value) = items.get(index).copied() {
                        let value = resolve_alias(value, &aliases);
                        if scalar_values.contains(&value) {
                            aliases.insert(dest, value);
                            scalar_values.insert(dest);
                            count += 1;
                            continue;
                        }
                    }
                }
                tuples.remove(&dest);
                stmts.push(CpsStmt::TupleGet { dest, tuple, index });
            }
            stmt => {
                if let Some(dest) = stmt_dest(&stmt) {
                    tuples.remove(&dest);
                    if stmt_produces_scalar_value(&stmt) {
                        scalar_values.insert(dest);
                    }
                }
                stmts.push(stmt);
            }
        }
    }

    continuation.terminator =
        substitute_terminator_values(continuation.terminator.clone(), &aliases);
    continuation.stmts = stmts;
    count
}

fn stmt_produces_scalar_value(stmt: &CpsStmt) -> bool {
    matches!(
        stmt,
        CpsStmt::Literal { .. }
            | CpsStmt::RecordHasField { .. }
            | CpsStmt::VariantTagEq { .. }
            | CpsStmt::Primitive {
                op: typed_ir::PrimitiveOp::BoolNot
                    | typed_ir::PrimitiveOp::BoolEq
                    | typed_ir::PrimitiveOp::IntAdd
                    | typed_ir::PrimitiveOp::IntSub
                    | typed_ir::PrimitiveOp::IntMul
                    | typed_ir::PrimitiveOp::IntEq
                    | typed_ir::PrimitiveOp::IntLt
                    | typed_ir::PrimitiveOp::IntLe
                    | typed_ir::PrimitiveOp::IntGt
                    | typed_ir::PrimitiveOp::IntGe
                    | typed_ir::PrimitiveOp::FloatAdd
                    | typed_ir::PrimitiveOp::FloatSub
                    | typed_ir::PrimitiveOp::FloatMul
                    | typed_ir::PrimitiveOp::FloatEq
                    | typed_ir::PrimitiveOp::FloatLt
                    | typed_ir::PrimitiveOp::FloatLe
                    | typed_ir::PrimitiveOp::FloatGt
                    | typed_ir::PrimitiveOp::FloatGe,
                ..
            }
    )
}

fn resolve_alias(mut value: CpsValueId, aliases: &HashMap<CpsValueId, CpsValueId>) -> CpsValueId {
    let mut seen = HashSet::new();
    while let Some(next) = aliases.get(&value).copied() {
        if !seen.insert(value) {
            break;
        }
        value = next;
    }
    value
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PureDirectInline {
    params: Vec<CpsValueId>,
    stmts: Vec<CpsStmt>,
    result: CpsValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DirectStyleIsland {
    continuations: Vec<CpsContinuationId>,
}

fn direct_style_islands(function: &CpsReprAbiFunction) -> Vec<DirectStyleIsland> {
    let candidates = function
        .continuations
        .iter()
        .filter(|continuation| direct_style_candidate(continuation))
        .map(|continuation| continuation.id)
        .collect::<HashSet<_>>();
    if candidates.is_empty() {
        return Vec::new();
    }

    let continuations = function
        .continuations
        .iter()
        .map(|continuation| (continuation.id, continuation))
        .collect::<HashMap<_, _>>();
    let mut visited = HashSet::new();
    let mut islands = Vec::new();

    for start in candidates.iter().copied() {
        if visited.contains(&start) {
            continue;
        }
        let mut queue = VecDeque::from([start]);
        let mut island = Vec::new();
        visited.insert(start);

        while let Some(id) = queue.pop_front() {
            island.push(id);
            let Some(continuation) = continuations.get(&id) else {
                continue;
            };
            for successor in direct_style_successors(&continuation.terminator) {
                if candidates.contains(&successor) && visited.insert(successor) {
                    queue.push_back(successor);
                }
            }
        }

        island.sort();
        islands.push(DirectStyleIsland {
            continuations: island,
        });
    }

    islands.sort_by_key(|island| island.continuations.first().copied());
    islands
}

fn direct_style_candidate(continuation: &CpsReprAbiContinuation) -> bool {
    if !continuation.environment.is_empty() {
        return false;
    }
    continuation.stmts.iter().all(direct_style_stmt)
        && matches!(
            continuation.terminator,
            CpsTerminator::Return(_)
                | CpsTerminator::Continue { .. }
                | CpsTerminator::Branch { .. }
        )
}

fn direct_style_stmt(stmt: &CpsStmt) -> bool {
    matches!(
        stmt,
        CpsStmt::Literal { .. }
            | CpsStmt::Tuple { .. }
            | CpsStmt::Record { .. }
            | CpsStmt::RecordWithoutFields { .. }
            | CpsStmt::Variant { .. }
            | CpsStmt::Select { .. }
            | CpsStmt::SelectWithDefault { .. }
            | CpsStmt::RecordHasField { .. }
            | CpsStmt::TupleGet { .. }
            | CpsStmt::VariantTagEq { .. }
            | CpsStmt::VariantPayload { .. }
            | CpsStmt::Primitive { .. }
            | CpsStmt::DirectCall { .. }
    )
}

fn direct_style_successors(terminator: &CpsTerminator) -> Vec<CpsContinuationId> {
    match terminator {
        CpsTerminator::Continue { target, .. } => vec![*target],
        CpsTerminator::Branch {
            then_cont,
            else_cont,
            ..
        } => vec![*then_cont, *else_cont],
        CpsTerminator::Return(_)
        | CpsTerminator::Perform { .. }
        | CpsTerminator::EffectfulCall { .. }
        | CpsTerminator::EffectfulApply { .. }
        | CpsTerminator::EffectfulForce { .. } => Vec::new(),
    }
}

fn eliminate_dead_pure_statements_in_continuation(
    continuation: &mut CpsReprAbiContinuation,
    captured_values: &HashSet<CpsValueId>,
) -> usize {
    let mut live = terminator_values(&continuation.terminator)
        .into_iter()
        .collect::<HashSet<_>>();
    live.extend(captured_values.iter().copied());
    let mut kept = Vec::with_capacity(continuation.stmts.len());
    let mut removed = 0;

    for stmt in continuation.stmts.iter().rev() {
        let dest = stmt_dest(stmt);
        if dest.is_some_and(|dest| !live.contains(&dest)) && stmt_is_pure(stmt) {
            removed += 1;
            continue;
        }

        if let Some(dest) = dest {
            live.remove(&dest);
        }
        live.extend(stmt_operands(stmt));
        kept.push(stmt.clone());
    }

    kept.reverse();
    continuation.stmts = kept;
    removed
}

fn function_captured_values(function: &CpsReprAbiFunction) -> HashSet<CpsValueId> {
    function
        .continuations
        .iter()
        .flat_map(|continuation| continuation.environment.iter().map(|slot| slot.value))
        .collect()
}

fn inline_candidates(
    function: &CpsReprAbiFunction,
) -> HashMap<CpsContinuationId, CpsReprAbiContinuation> {
    let references = continuation_references(function);
    let protected = protected_continuations(function);
    function
        .continuations
        .iter()
        .filter(|continuation| {
            if continuation.shot_kind != CpsShotKind::OneShot {
                return false;
            }
            if !continuation.environment.is_empty() {
                return false;
            }
            if continuation.stmts.len() > 12 {
                return false;
            }
            references
                .get(&continuation.id)
                .is_some_and(|reference| reference.total == 1 && reference.continue_calls == 1)
        })
        .filter(|continuation| !protected.contains(&continuation.id))
        .map(|continuation| (continuation.id, continuation.clone()))
        .collect()
}

fn inline_continuation_call_at(
    function: &mut CpsReprAbiFunction,
    index: usize,
    candidates: &HashMap<CpsContinuationId, CpsReprAbiContinuation>,
) -> usize {
    let continuation = &mut function.continuations[index];
    let CpsTerminator::Continue { target, args } = &continuation.terminator else {
        return 0;
    };
    let Some(target_continuation) = candidates.get(target) else {
        return 0;
    };
    if target_continuation.id == continuation.id {
        return 0;
    }
    if target_continuation.params.len() != args.len() {
        return 0;
    }

    let substitution = target_continuation
        .params
        .iter()
        .zip(args.iter().copied())
        .map(|(param, arg)| (param.value, arg))
        .collect::<HashMap<_, _>>();
    continuation.stmts.extend(
        target_continuation
            .stmts
            .iter()
            .cloned()
            .map(|stmt| substitute_stmt_values(stmt, &substitution)),
    );
    continuation.terminator =
        substitute_terminator_values(target_continuation.terminator.clone(), &substitution);
    1
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct ContinuationReferenceCount {
    total: usize,
    continue_calls: usize,
}

fn continuation_references(
    function: &CpsReprAbiFunction,
) -> HashMap<CpsContinuationId, ContinuationReferenceCount> {
    let mut references = HashMap::new();
    for continuation in &function.continuations {
        for stmt in &continuation.stmts {
            collect_stmt_reference_counts(stmt, &mut references);
        }
        collect_terminator_reference_counts(&continuation.terminator, &mut references);
    }
    references
}

fn protected_continuations(function: &CpsReprAbiFunction) -> HashSet<CpsContinuationId> {
    let mut protected = HashSet::new();
    protected.insert(function.entry);
    for handler in &function.handlers {
        for arm in &handler.arms {
            protected.insert(arm.entry);
        }
    }
    for continuation in &function.continuations {
        for stmt in &continuation.stmts {
            collect_protected_stmt_continuations(stmt, &mut protected);
        }
    }
    protected
}

fn collect_stmt_reference_counts(
    stmt: &CpsStmt,
    references: &mut HashMap<CpsContinuationId, ContinuationReferenceCount>,
) {
    match stmt {
        CpsStmt::MakeThunk { entry, .. }
        | CpsStmt::MakeClosure { entry, .. }
        | CpsStmt::MakeRecursiveClosure { entry, .. } => {
            count_reference(*entry, references, false);
        }
        CpsStmt::InstallHandler {
            value,
            escape,
            envs,
            ..
        } => {
            count_reference(*value, references, false);
            count_reference(*escape, references, false);
            for env in envs {
                count_reference(env.entry, references, false);
            }
        }
        CpsStmt::ResumeWithHandler { envs, .. } => {
            for env in envs {
                count_reference(env.entry, references, false);
            }
        }
        CpsStmt::Literal { .. }
        | CpsStmt::FreshGuard { .. }
        | CpsStmt::PeekGuard { .. }
        | CpsStmt::FindGuard { .. }
        | CpsStmt::AddThunkBoundary { .. }
        | CpsStmt::ForceThunk { .. }
        | CpsStmt::Tuple { .. }
        | CpsStmt::Record { .. }
        | CpsStmt::RecordWithoutFields { .. }
        | CpsStmt::Variant { .. }
        | CpsStmt::Select { .. }
        | CpsStmt::SelectWithDefault { .. }
        | CpsStmt::RecordHasField { .. }
        | CpsStmt::TupleGet { .. }
        | CpsStmt::VariantTagEq { .. }
        | CpsStmt::VariantPayload { .. }
        | CpsStmt::Primitive { .. }
        | CpsStmt::DirectCall { .. }
        | CpsStmt::ApplyClosure { .. }
        | CpsStmt::CloneContinuation { .. }
        | CpsStmt::Resume { .. }
        | CpsStmt::UninstallHandler { .. } => {}
    }
}

fn collect_terminator_reference_counts(
    terminator: &CpsTerminator,
    references: &mut HashMap<CpsContinuationId, ContinuationReferenceCount>,
) {
    match terminator {
        CpsTerminator::Continue { target, .. } => count_reference(*target, references, true),
        CpsTerminator::Branch {
            then_cont,
            else_cont,
            ..
        } => {
            count_reference(*then_cont, references, false);
            count_reference(*else_cont, references, false);
        }
        CpsTerminator::Perform { resume, .. }
        | CpsTerminator::EffectfulCall { resume, .. }
        | CpsTerminator::EffectfulApply { resume, .. }
        | CpsTerminator::EffectfulForce { resume, .. } => {
            count_reference(*resume, references, false)
        }
        CpsTerminator::Return(_) => {}
    }
}

fn collect_protected_stmt_continuations(
    stmt: &CpsStmt,
    protected: &mut HashSet<CpsContinuationId>,
) {
    match stmt {
        CpsStmt::MakeThunk { entry, .. }
        | CpsStmt::MakeClosure { entry, .. }
        | CpsStmt::MakeRecursiveClosure { entry, .. } => {
            protected.insert(*entry);
        }
        CpsStmt::InstallHandler {
            value,
            escape,
            envs,
            ..
        } => {
            protected.insert(*value);
            protected.insert(*escape);
            for env in envs {
                protected.insert(env.entry);
            }
        }
        CpsStmt::ResumeWithHandler { envs, .. } => {
            for env in envs {
                protected.insert(env.entry);
            }
        }
        CpsStmt::Literal { .. }
        | CpsStmt::FreshGuard { .. }
        | CpsStmt::PeekGuard { .. }
        | CpsStmt::FindGuard { .. }
        | CpsStmt::AddThunkBoundary { .. }
        | CpsStmt::ForceThunk { .. }
        | CpsStmt::Tuple { .. }
        | CpsStmt::Record { .. }
        | CpsStmt::RecordWithoutFields { .. }
        | CpsStmt::Variant { .. }
        | CpsStmt::Select { .. }
        | CpsStmt::SelectWithDefault { .. }
        | CpsStmt::RecordHasField { .. }
        | CpsStmt::TupleGet { .. }
        | CpsStmt::VariantTagEq { .. }
        | CpsStmt::VariantPayload { .. }
        | CpsStmt::Primitive { .. }
        | CpsStmt::DirectCall { .. }
        | CpsStmt::ApplyClosure { .. }
        | CpsStmt::CloneContinuation { .. }
        | CpsStmt::Resume { .. }
        | CpsStmt::UninstallHandler { .. } => {}
    }
}

fn count_reference(
    id: CpsContinuationId,
    references: &mut HashMap<CpsContinuationId, ContinuationReferenceCount>,
    is_continue_call: bool,
) {
    let reference = references.entry(id).or_default();
    reference.total += 1;
    if is_continue_call {
        reference.continue_calls += 1;
    }
}

fn stmt_is_pure(stmt: &CpsStmt) -> bool {
    matches!(
        stmt,
        CpsStmt::Literal { .. }
            | CpsStmt::MakeThunk { .. }
            | CpsStmt::AddThunkBoundary { .. }
            | CpsStmt::MakeClosure { .. }
            | CpsStmt::MakeRecursiveClosure { .. }
            | CpsStmt::Tuple { .. }
            | CpsStmt::Record { .. }
            | CpsStmt::RecordWithoutFields { .. }
            | CpsStmt::Variant { .. }
            | CpsStmt::Select { .. }
            | CpsStmt::SelectWithDefault { .. }
            | CpsStmt::RecordHasField { .. }
            | CpsStmt::TupleGet { .. }
            | CpsStmt::VariantTagEq { .. }
            | CpsStmt::Primitive {
                op: typed_ir::PrimitiveOp::BoolNot
                    | typed_ir::PrimitiveOp::BoolEq
                    | typed_ir::PrimitiveOp::IntAdd
                    | typed_ir::PrimitiveOp::IntSub
                    | typed_ir::PrimitiveOp::IntMul
                    | typed_ir::PrimitiveOp::IntEq
                    | typed_ir::PrimitiveOp::IntLt
                    | typed_ir::PrimitiveOp::IntLe
                    | typed_ir::PrimitiveOp::IntGt
                    | typed_ir::PrimitiveOp::IntGe
                    | typed_ir::PrimitiveOp::IntToString
                    | typed_ir::PrimitiveOp::IntToHex
                    | typed_ir::PrimitiveOp::IntToUpperHex
                    | typed_ir::PrimitiveOp::FloatAdd
                    | typed_ir::PrimitiveOp::FloatSub
                    | typed_ir::PrimitiveOp::FloatMul
                    | typed_ir::PrimitiveOp::FloatEq
                    | typed_ir::PrimitiveOp::FloatLt
                    | typed_ir::PrimitiveOp::FloatLe
                    | typed_ir::PrimitiveOp::FloatGt
                    | typed_ir::PrimitiveOp::FloatGe
                    | typed_ir::PrimitiveOp::FloatToString
                    | typed_ir::PrimitiveOp::BoolToString
                    | typed_ir::PrimitiveOp::StringConcat
                    | typed_ir::PrimitiveOp::StringLen
                    | typed_ir::PrimitiveOp::StringEq,
                ..
            }
    )
}

fn stmt_dest(stmt: &CpsStmt) -> Option<CpsValueId> {
    match stmt {
        CpsStmt::Literal { dest, .. }
        | CpsStmt::FreshGuard { dest, .. }
        | CpsStmt::PeekGuard { dest }
        | CpsStmt::FindGuard { dest, .. }
        | CpsStmt::MakeThunk { dest, .. }
        | CpsStmt::AddThunkBoundary { dest, .. }
        | CpsStmt::MakeClosure { dest, .. }
        | CpsStmt::MakeRecursiveClosure { dest, .. }
        | CpsStmt::ForceThunk { dest, .. }
        | CpsStmt::Tuple { dest, .. }
        | CpsStmt::Record { dest, .. }
        | CpsStmt::RecordWithoutFields { dest, .. }
        | CpsStmt::Variant { dest, .. }
        | CpsStmt::Select { dest, .. }
        | CpsStmt::SelectWithDefault { dest, .. }
        | CpsStmt::RecordHasField { dest, .. }
        | CpsStmt::TupleGet { dest, .. }
        | CpsStmt::VariantTagEq { dest, .. }
        | CpsStmt::VariantPayload { dest, .. }
        | CpsStmt::Primitive { dest, .. }
        | CpsStmt::DirectCall { dest, .. }
        | CpsStmt::ApplyClosure { dest, .. }
        | CpsStmt::CloneContinuation { dest, .. }
        | CpsStmt::Resume { dest, .. }
        | CpsStmt::ResumeWithHandler { dest, .. } => Some(*dest),
        CpsStmt::InstallHandler { .. } | CpsStmt::UninstallHandler { .. } => None,
    }
}

fn stmt_operands(stmt: &CpsStmt) -> Vec<CpsValueId> {
    match stmt {
        CpsStmt::FindGuard { guard, .. } => vec![*guard],
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
        CpsStmt::Select { base, .. } | CpsStmt::RecordHasField { base, .. } => vec![*base],
        CpsStmt::SelectWithDefault { base, default, .. } => vec![*base, *default],
        CpsStmt::TupleGet { tuple, .. } => vec![*tuple],
        CpsStmt::VariantTagEq { variant, .. } | CpsStmt::VariantPayload { variant, .. } => {
            vec![*variant]
        }
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
            .chain(envs.iter().flat_map(|env| env.values.iter().copied()))
            .collect(),
        CpsStmt::InstallHandler { envs, .. } => envs
            .iter()
            .flat_map(|env| env.values.iter().copied())
            .collect(),
        CpsStmt::Literal { .. }
        | CpsStmt::FreshGuard { .. }
        | CpsStmt::PeekGuard { .. }
        | CpsStmt::MakeThunk { .. }
        | CpsStmt::MakeClosure { .. }
        | CpsStmt::MakeRecursiveClosure { .. }
        | CpsStmt::UninstallHandler { .. } => Vec::new(),
    }
}

fn terminator_values(terminator: &CpsTerminator) -> Vec<CpsValueId> {
    match terminator {
        CpsTerminator::Return(value) => vec![*value],
        CpsTerminator::Continue { args, .. } => args.clone(),
        CpsTerminator::Branch { cond, .. } => vec![*cond],
        CpsTerminator::Perform {
            payload, blocked, ..
        } => std::iter::once(*payload)
            .chain(blocked.iter().copied())
            .collect(),
        CpsTerminator::EffectfulCall { args, .. } => args.clone(),
        CpsTerminator::EffectfulApply { closure, arg, .. } => vec![*closure, *arg],
        CpsTerminator::EffectfulForce { thunk, .. } => vec![*thunk],
    }
}

fn reachable_continuations(function: &CpsReprAbiFunction) -> HashSet<CpsContinuationId> {
    let continuations = function
        .continuations
        .iter()
        .map(|continuation| (continuation.id, continuation))
        .collect::<HashMap<_, _>>();
    let mut reachable = HashSet::new();
    let mut work = VecDeque::new();

    push_reachable(function.entry, &mut reachable, &mut work);
    for handler in &function.handlers {
        for arm in &handler.arms {
            push_reachable(arm.entry, &mut reachable, &mut work);
        }
    }

    while let Some(id) = work.pop_front() {
        let Some(continuation) = continuations.get(&id) else {
            continue;
        };
        for stmt in &continuation.stmts {
            collect_stmt_continuations(stmt, &mut reachable, &mut work);
        }
        collect_terminator_continuations(&continuation.terminator, &mut reachable, &mut work);
    }

    reachable
}

fn push_reachable(
    id: CpsContinuationId,
    reachable: &mut HashSet<CpsContinuationId>,
    work: &mut VecDeque<CpsContinuationId>,
) {
    if reachable.insert(id) {
        work.push_back(id);
    }
}

fn collect_stmt_continuations(
    stmt: &CpsStmt,
    reachable: &mut HashSet<CpsContinuationId>,
    work: &mut VecDeque<CpsContinuationId>,
) {
    match stmt {
        CpsStmt::MakeThunk { entry, .. }
        | CpsStmt::MakeClosure { entry, .. }
        | CpsStmt::MakeRecursiveClosure { entry, .. } => {
            push_reachable(*entry, reachable, work);
        }
        CpsStmt::InstallHandler {
            value,
            escape,
            envs,
            ..
        } => {
            push_reachable(*value, reachable, work);
            push_reachable(*escape, reachable, work);
            for env in envs {
                push_reachable(env.entry, reachable, work);
            }
        }
        CpsStmt::ResumeWithHandler { envs, .. } => {
            for env in envs {
                push_reachable(env.entry, reachable, work);
            }
        }
        CpsStmt::Literal { .. }
        | CpsStmt::FreshGuard { .. }
        | CpsStmt::PeekGuard { .. }
        | CpsStmt::FindGuard { .. }
        | CpsStmt::AddThunkBoundary { .. }
        | CpsStmt::ForceThunk { .. }
        | CpsStmt::Tuple { .. }
        | CpsStmt::Record { .. }
        | CpsStmt::RecordWithoutFields { .. }
        | CpsStmt::Variant { .. }
        | CpsStmt::Select { .. }
        | CpsStmt::SelectWithDefault { .. }
        | CpsStmt::RecordHasField { .. }
        | CpsStmt::TupleGet { .. }
        | CpsStmt::VariantTagEq { .. }
        | CpsStmt::VariantPayload { .. }
        | CpsStmt::Primitive { .. }
        | CpsStmt::DirectCall { .. }
        | CpsStmt::ApplyClosure { .. }
        | CpsStmt::CloneContinuation { .. }
        | CpsStmt::Resume { .. }
        | CpsStmt::UninstallHandler { .. } => {}
    }
}

fn collect_terminator_continuations(
    terminator: &CpsTerminator,
    reachable: &mut HashSet<CpsContinuationId>,
    work: &mut VecDeque<CpsContinuationId>,
) {
    match terminator {
        CpsTerminator::Continue { target, .. } => push_reachable(*target, reachable, work),
        CpsTerminator::Branch {
            then_cont,
            else_cont,
            ..
        } => {
            push_reachable(*then_cont, reachable, work);
            push_reachable(*else_cont, reachable, work);
        }
        CpsTerminator::Perform { resume, .. }
        | CpsTerminator::EffectfulCall { resume, .. }
        | CpsTerminator::EffectfulApply { resume, .. }
        | CpsTerminator::EffectfulForce { resume, .. } => push_reachable(*resume, reachable, work),
        CpsTerminator::Return(_) => {}
    }
}

fn forwarding_continuations(
    function: &CpsReprAbiFunction,
) -> HashMap<CpsContinuationId, ForwardingContinuation> {
    let mut forwarders = HashMap::new();
    for continuation in &function.continuations {
        if !continuation.stmts.is_empty() || !continuation.environment.is_empty() {
            continue;
        }
        let CpsTerminator::Continue { target, args } = &continuation.terminator else {
            continue;
        };
        if *target == continuation.id {
            continue;
        }
        if args
            .iter()
            .all(|arg| continuation.params.iter().any(|param| param.value == *arg))
        {
            forwarders.insert(
                continuation.id,
                ForwardingContinuation {
                    params: continuation
                        .params
                        .iter()
                        .map(|param| param.value)
                        .collect(),
                    target: *target,
                    args: args.clone(),
                },
            );
        }
    }
    forwarders
}

fn returning_continuations(
    function: &CpsReprAbiFunction,
) -> HashMap<CpsContinuationId, ReturningContinuation> {
    let mut returners = HashMap::new();
    for continuation in &function.continuations {
        if !continuation.stmts.is_empty() || !continuation.environment.is_empty() {
            continue;
        }
        let CpsTerminator::Return(value) = continuation.terminator else {
            continue;
        };
        if let Some(param_index) = continuation
            .params
            .iter()
            .position(|param| param.value == value)
        {
            returners.insert(continuation.id, ReturningContinuation { param_index });
        }
    }
    returners
}

fn rewrite_terminator_forwarders(
    terminator: &mut CpsTerminator,
    forwarders: &HashMap<CpsContinuationId, ForwardingContinuation>,
) -> usize {
    match terminator {
        CpsTerminator::Continue { target, args } => {
            rewrite_continuation_call(target, args, forwarders)
        }
        CpsTerminator::Perform { resume, .. }
        | CpsTerminator::EffectfulCall { resume, .. }
        | CpsTerminator::EffectfulApply { resume, .. }
        | CpsTerminator::EffectfulForce { resume, .. } => {
            let mut args = Vec::new();
            rewrite_resume_target(resume, &mut args, forwarders)
        }
        CpsTerminator::Branch {
            then_cont,
            else_cont,
            ..
        } => {
            let mut count = 0;
            let mut args = Vec::new();
            count += rewrite_resume_target(then_cont, &mut args, forwarders);
            count += rewrite_resume_target(else_cont, &mut args, forwarders);
            count
        }
        CpsTerminator::Return(_) => 0,
    }
}

fn rewrite_terminator_returners(
    terminator: &mut CpsTerminator,
    returners: &HashMap<CpsContinuationId, ReturningContinuation>,
) -> usize {
    let CpsTerminator::Continue { target, args } = terminator else {
        return 0;
    };
    let Some(returner) = returners.get(target) else {
        return 0;
    };
    let Some(value) = args.get(returner.param_index).copied() else {
        return 0;
    };
    *terminator = CpsTerminator::Return(value);
    1
}

fn rewrite_continuation_call(
    target: &mut CpsContinuationId,
    args: &mut Vec<CpsValueId>,
    forwarders: &HashMap<CpsContinuationId, ForwardingContinuation>,
) -> usize {
    let mut count = 0;
    while let Some(forwarder) = forwarders.get(target) {
        let Some(remapped) = forwarder.remap_args(args) else {
            break;
        };
        *target = forwarder.target;
        *args = remapped;
        count += 1;
    }
    count
}

fn rewrite_resume_target(
    target: &mut CpsContinuationId,
    args: &mut Vec<CpsValueId>,
    forwarders: &HashMap<CpsContinuationId, ForwardingContinuation>,
) -> usize {
    let mut count = 0;
    while let Some(forwarder) = forwarders.get(target) {
        if !forwarder.params.is_empty() {
            break;
        }
        if !forwarder.args.is_empty() {
            break;
        }
        *target = forwarder.target;
        args.clear();
        count += 1;
    }
    count
}

fn substitute_stmt_values(
    stmt: CpsStmt,
    substitution: &HashMap<CpsValueId, CpsValueId>,
) -> CpsStmt {
    match stmt {
        CpsStmt::Literal { dest, literal } => CpsStmt::Literal { dest, literal },
        CpsStmt::FreshGuard { dest, var } => CpsStmt::FreshGuard { dest, var },
        CpsStmt::PeekGuard { dest } => CpsStmt::PeekGuard { dest },
        CpsStmt::FindGuard { dest, guard } => CpsStmt::FindGuard {
            dest,
            guard: subst_value(guard, substitution),
        },
        CpsStmt::MakeThunk { dest, entry } => CpsStmt::MakeThunk { dest, entry },
        CpsStmt::AddThunkBoundary {
            dest,
            thunk,
            guard,
            allowed,
            active,
        } => CpsStmt::AddThunkBoundary {
            dest,
            thunk: subst_value(thunk, substitution),
            guard: subst_value(guard, substitution),
            allowed,
            active,
        },
        CpsStmt::MakeClosure { dest, entry } => CpsStmt::MakeClosure { dest, entry },
        CpsStmt::MakeRecursiveClosure { dest, entry } => {
            CpsStmt::MakeRecursiveClosure { dest, entry }
        }
        CpsStmt::ForceThunk { dest, thunk } => CpsStmt::ForceThunk {
            dest,
            thunk: subst_value(thunk, substitution),
        },
        CpsStmt::Tuple { dest, items } => CpsStmt::Tuple {
            dest,
            items: subst_values(items, substitution),
        },
        CpsStmt::Record { dest, base, fields } => CpsStmt::Record {
            dest,
            base: base.map(|value| subst_value(value, substitution)),
            fields: fields
                .into_iter()
                .map(|field| CpsRecordField {
                    name: field.name,
                    value: subst_value(field.value, substitution),
                })
                .collect(),
        },
        CpsStmt::RecordWithoutFields { dest, base, fields } => CpsStmt::RecordWithoutFields {
            dest,
            base: subst_value(base, substitution),
            fields,
        },
        CpsStmt::Variant { dest, tag, value } => CpsStmt::Variant {
            dest,
            tag,
            value: value.map(|value| subst_value(value, substitution)),
        },
        CpsStmt::Select { dest, base, field } => CpsStmt::Select {
            dest,
            base: subst_value(base, substitution),
            field,
        },
        CpsStmt::SelectWithDefault {
            dest,
            base,
            field,
            default,
        } => CpsStmt::SelectWithDefault {
            dest,
            base: subst_value(base, substitution),
            field,
            default: subst_value(default, substitution),
        },
        CpsStmt::RecordHasField { dest, base, field } => CpsStmt::RecordHasField {
            dest,
            base: subst_value(base, substitution),
            field,
        },
        CpsStmt::TupleGet { dest, tuple, index } => CpsStmt::TupleGet {
            dest,
            tuple: subst_value(tuple, substitution),
            index,
        },
        CpsStmt::VariantTagEq { dest, variant, tag } => CpsStmt::VariantTagEq {
            dest,
            variant: subst_value(variant, substitution),
            tag,
        },
        CpsStmt::VariantPayload { dest, variant } => CpsStmt::VariantPayload {
            dest,
            variant: subst_value(variant, substitution),
        },
        CpsStmt::Primitive { dest, op, args } => CpsStmt::Primitive {
            dest,
            op,
            args: subst_values(args, substitution),
        },
        CpsStmt::DirectCall { dest, target, args } => CpsStmt::DirectCall {
            dest,
            target,
            args: subst_values(args, substitution),
        },
        CpsStmt::ApplyClosure { dest, closure, arg } => CpsStmt::ApplyClosure {
            dest,
            closure: subst_value(closure, substitution),
            arg: subst_value(arg, substitution),
        },
        CpsStmt::CloneContinuation { dest, source } => CpsStmt::CloneContinuation {
            dest,
            source: subst_value(source, substitution),
        },
        CpsStmt::Resume {
            dest,
            resumption,
            arg,
        } => CpsStmt::Resume {
            dest,
            resumption: subst_value(resumption, substitution),
            arg: subst_value(arg, substitution),
        },
        CpsStmt::ResumeWithHandler {
            dest,
            resumption,
            arg,
            handler,
            envs,
        } => CpsStmt::ResumeWithHandler {
            dest,
            resumption: subst_value(resumption, substitution),
            arg: subst_value(arg, substitution),
            handler,
            envs: subst_handler_envs(envs, substitution),
        },
        CpsStmt::InstallHandler {
            handler,
            envs,
            value,
            escape,
        } => CpsStmt::InstallHandler {
            handler,
            envs: subst_handler_envs(envs, substitution),
            value,
            escape,
        },
        CpsStmt::UninstallHandler { handler } => CpsStmt::UninstallHandler { handler },
    }
}

fn substitute_terminator_values(
    terminator: CpsTerminator,
    substitution: &HashMap<CpsValueId, CpsValueId>,
) -> CpsTerminator {
    match terminator {
        CpsTerminator::Return(value) => CpsTerminator::Return(subst_value(value, substitution)),
        CpsTerminator::Continue { target, args } => CpsTerminator::Continue {
            target,
            args: subst_values(args, substitution),
        },
        CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        } => CpsTerminator::Branch {
            cond: subst_value(cond, substitution),
            then_cont,
            else_cont,
        },
        CpsTerminator::Perform {
            effect,
            payload,
            resume,
            handler,
            blocked,
        } => CpsTerminator::Perform {
            effect,
            payload: subst_value(payload, substitution),
            resume,
            handler,
            blocked: blocked.map(|value| subst_value(value, substitution)),
        },
        CpsTerminator::EffectfulCall {
            target,
            args,
            resume,
        } => CpsTerminator::EffectfulCall {
            target,
            args: subst_values(args, substitution),
            resume,
        },
        CpsTerminator::EffectfulApply {
            closure,
            arg,
            resume,
        } => CpsTerminator::EffectfulApply {
            closure: subst_value(closure, substitution),
            arg: subst_value(arg, substitution),
            resume,
        },
        CpsTerminator::EffectfulForce { thunk, resume } => CpsTerminator::EffectfulForce {
            thunk: subst_value(thunk, substitution),
            resume,
        },
    }
}

fn subst_handler_envs(
    envs: Vec<CpsHandlerEnv>,
    substitution: &HashMap<CpsValueId, CpsValueId>,
) -> Vec<CpsHandlerEnv> {
    envs.into_iter()
        .map(|env| CpsHandlerEnv {
            entry: env.entry,
            values: subst_values(env.values, substitution),
            targets: subst_values(env.targets, substitution),
        })
        .collect()
}

fn subst_values(
    values: Vec<CpsValueId>,
    substitution: &HashMap<CpsValueId, CpsValueId>,
) -> Vec<CpsValueId> {
    values
        .into_iter()
        .map(|value| subst_value(value, substitution))
        .collect()
}

fn subst_value(value: CpsValueId, substitution: &HashMap<CpsValueId, CpsValueId>) -> CpsValueId {
    substitution.get(&value).copied().unwrap_or(value)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ForwardingContinuation {
    params: Vec<CpsValueId>,
    target: CpsContinuationId,
    args: Vec<CpsValueId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ReturningContinuation {
    param_index: usize,
}

impl ForwardingContinuation {
    fn remap_args(&self, supplied_args: &[CpsValueId]) -> Option<Vec<CpsValueId>> {
        if supplied_args.len() != self.params.len() {
            return None;
        }
        self.args
            .iter()
            .map(|forwarded| {
                self.params
                    .iter()
                    .position(|param| param == forwarded)
                    .map(|index| supplied_args[index])
            })
            .collect()
    }
}

impl CpsOptimizationProfile {
    fn record_optimized_size(&mut self, module: &CpsReprAbiModule) {
        self.optimized_continuations = module
            .functions
            .iter()
            .chain(&module.roots)
            .map(|function| function.continuations.len())
            .sum();
        self.optimized_statements = module
            .functions
            .iter()
            .chain(&module.roots)
            .flat_map(|function| &function.continuations)
            .map(|continuation| continuation.stmts.len())
            .sum();
    }

    fn has_more_changes_than(self, before: Self) -> bool {
        self.forwarded_continuation_calls > before.forwarded_continuation_calls
            || self.returned_continuation_calls > before.returned_continuation_calls
            || self.folded_constant_branches > before.folded_constant_branches
            || self.rewritten_pure_effectful_calls > before.rewritten_pure_effectful_calls
            || self.inlined_local_thunk_forces > before.inlined_local_thunk_forces
            || self.collapsed_force_thunk_chains > before.collapsed_force_thunk_chains
            || self.removed_redundant_non_thunk_forces > before.removed_redundant_non_thunk_forces
            || self.reified_primitive_calls > before.reified_primitive_calls
            || self.reified_partial_closure_calls > before.reified_partial_closure_calls
            || self.reified_known_closure_parameter_calls
                > before.reified_known_closure_parameter_calls
            || self.removed_unused_continuation_params > before.removed_unused_continuation_params
            || self.removed_unused_environment_slots > before.removed_unused_environment_slots
            || self.folded_structural_projections > before.folded_structural_projections
            || self.inlined_pure_direct_calls > before.inlined_pure_direct_calls
            || self.inlined_ready_finite_thunk_calls > before.inlined_ready_finite_thunk_calls
            || self.defunctionalized_finite_handler_thunk_calls
                > before.defunctionalized_finite_handler_thunk_calls
            || self.inlined_continuation_calls > before.inlined_continuation_calls
            || self.removed_unreachable_continuations > before.removed_unreachable_continuations
            || self.removed_dead_pure_statements > before.removed_dead_pure_statements
    }

    pub fn measure(module: &CpsReprAbiModule) -> Self {
        let functions = module.functions.len();
        let roots = module.roots.len();
        let continuations = module
            .functions
            .iter()
            .chain(&module.roots)
            .map(|function| function.continuations.len())
            .sum();
        let handlers = module
            .functions
            .iter()
            .chain(&module.roots)
            .map(|function| function.handlers.len())
            .sum();
        let statements = module
            .functions
            .iter()
            .chain(&module.roots)
            .flat_map(|function| &function.continuations)
            .map(|continuation| continuation.stmts.len())
            .sum();

        Self {
            functions,
            roots,
            continuations,
            handlers,
            statements,
            optimized_continuations: continuations,
            optimized_statements: statements,
            passes_run: 0,
            forwarded_continuation_calls: 0,
            returned_continuation_calls: 0,
            folded_constant_branches: 0,
            rewritten_pure_effectful_calls: 0,
            inlined_local_thunk_forces: 0,
            collapsed_force_thunk_chains: 0,
            removed_redundant_non_thunk_forces: 0,
            reified_primitive_calls: 0,
            reified_partial_closure_calls: 0,
            reified_known_closure_parameter_calls: 0,
            removed_unused_continuation_params: 0,
            removed_unused_environment_slots: 0,
            folded_structural_projections: 0,
            inlined_pure_direct_calls: 0,
            inlined_ready_finite_thunk_calls: 0,
            defunctionalized_finite_handler_thunk_calls: 0,
            inlined_continuation_calls: 0,
            removed_unreachable_continuations: 0,
            removed_dead_pure_statements: 0,
            direct_style_islands: 0,
            direct_style_continuations: 0,
            effect_regions: 0,
            single_resume_regions: 0,
            finite_multi_resume_regions: 0,
            escaping_resumption_regions: 0,
            nested_effectful_regions: 0,
            opaque_effect_regions: 0,
            dynamic_effect_handler_candidates: 0,
            dynamic_effect_region_plans: 0,
            finite_dynamic_effect_region_plans: 0,
            dynamic_effect_thunk_argument_plans: 0,
            dynamic_effect_thunk_specialization_seeds: 0,
            ready_dynamic_effect_thunk_specialization_seeds: 0,
            dynamic_effect_thunk_rewrite_plans: 0,
            defunctionalized_dynamic_effect_thunk_rewrite_plans: 0,
            body_clone_dynamic_effect_thunk_rewrite_plans: 0,
            changed: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::cps_ir::{
        CpsContinuationId, CpsFunction, CpsHandlerId, CpsLiteral, CpsModule, CpsShotKind, CpsStmt,
        CpsTerminator, CpsValueId,
    };
    use crate::cps_repr::{CpsReprAbiLane, lower_cps_repr_module};
    use crate::cps_repr_abi::lower_cps_repr_abi_module;

    use super::*;

    #[test]
    fn optimization_boundary_keeps_non_forwarding_module() {
        let abi = sample_abi_module();
        let optimized = optimize_cps_repr_abi_module(&abi);

        assert_eq!(optimized.module, abi);
        assert_eq!(optimized.profile.roots, 1);
        assert_eq!(optimized.profile.continuations, 1);
        assert_eq!(optimized.profile.optimized_continuations, 1);
        assert_eq!(optimized.profile.statements, 1);
        assert_eq!(optimized.profile.optimized_statements, 1);
        assert_eq!(optimized.profile.passes_run, 24);
        assert_eq!(optimized.profile.forwarded_continuation_calls, 0);
        assert_eq!(optimized.profile.returned_continuation_calls, 0);
        assert_eq!(optimized.profile.folded_constant_branches, 0);
        assert_eq!(optimized.profile.rewritten_pure_effectful_calls, 0);
        assert_eq!(optimized.profile.inlined_local_thunk_forces, 0);
        assert_eq!(optimized.profile.collapsed_force_thunk_chains, 0);
        assert_eq!(optimized.profile.removed_redundant_non_thunk_forces, 0);
        assert_eq!(optimized.profile.inlined_ready_finite_thunk_calls, 0);
        assert_eq!(
            optimized
                .profile
                .defunctionalized_finite_handler_thunk_calls,
            0
        );
        assert_eq!(optimized.profile.reified_primitive_calls, 0);
        assert_eq!(optimized.profile.reified_partial_closure_calls, 0);
        assert_eq!(optimized.profile.reified_known_closure_parameter_calls, 0);
        assert_eq!(optimized.profile.removed_unused_continuation_params, 0);
        assert_eq!(optimized.profile.removed_unused_environment_slots, 0);
        assert_eq!(optimized.profile.folded_structural_projections, 0);
        assert_eq!(optimized.profile.inlined_pure_direct_calls, 0);
        assert_eq!(optimized.profile.inlined_continuation_calls, 0);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 0);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 0);
        assert_eq!(optimized.profile.direct_style_islands, 1);
        assert_eq!(optimized.profile.direct_style_continuations, 1);
        assert!(!optimized.profile.changed);
    }

    #[test]
    fn ready_finite_inline_consumes_immediate_force_chain() {
        let stmts = vec![
            CpsStmt::DirectCall {
                dest: CpsValueId(1),
                target: "collector".to_string(),
                args: Vec::new(),
            },
            CpsStmt::ForceThunk {
                dest: CpsValueId(2),
                thunk: CpsValueId(1),
            },
            CpsStmt::ForceThunk {
                dest: CpsValueId(3),
                thunk: CpsValueId(2),
            },
            CpsStmt::Tuple {
                dest: CpsValueId(4),
                items: vec![CpsValueId(3)],
            },
        ];

        let (rest_param, rest_stmts) = rest_after_inlined_thunk_return(&stmts, 1, CpsValueId(1));

        assert_eq!(rest_param, CpsValueId(3));
        assert_eq!(rest_stmts.len(), 1);
        assert!(matches!(rest_stmts[0], CpsStmt::Tuple { .. }));
    }

    #[test]
    fn collapses_consecutive_deep_force_thunk_chain() {
        let mut function = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(1),
                            thunk: CpsValueId(0),
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(2),
                            thunk: CpsValueId(1),
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(3),
                            thunk: CpsValueId(2),
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(3)),
                }],
            }],
        }))
        .roots
        .remove(0);

        let collapsed = collapse_force_thunk_chains_in_function(&mut function);

        assert_eq!(collapsed, 2);
        assert_eq!(
            function.continuations[0].stmts,
            vec![CpsStmt::ForceThunk {
                dest: CpsValueId(3),
                thunk: CpsValueId(0),
            }]
        );
    }

    #[test]
    fn keeps_intermediate_force_value_when_it_has_another_use() {
        let mut function = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(1),
                            thunk: CpsValueId(0),
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(2),
                            thunk: CpsValueId(1),
                        },
                    ],
                    terminator: CpsTerminator::Continue {
                        target: CpsContinuationId(1),
                        args: vec![CpsValueId(1), CpsValueId(2)],
                    },
                }],
            }],
        }))
        .roots
        .remove(0);

        let collapsed = collapse_force_thunk_chains_in_function(&mut function);

        assert_eq!(collapsed, 0);
        assert_eq!(function.continuations[0].stmts.len(), 2);
    }

    #[test]
    fn removes_force_of_known_non_thunk_value_when_uses_are_local() {
        let mut function = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("42".to_string()),
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(1),
                            thunk: CpsValueId(0),
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(1)),
                }],
            }],
        }))
        .roots
        .remove(0);

        let removed = remove_redundant_non_thunk_forces_in_function(&mut function, &HashSet::new());

        assert_eq!(removed, 1);
        assert_eq!(
            function.continuations[0].stmts,
            vec![CpsStmt::Literal {
                dest: CpsValueId(0),
                literal: CpsLiteral::Int("42".to_string()),
            }]
        );
        assert_eq!(
            function.continuations[0].terminator,
            CpsTerminator::Return(CpsValueId(0))
        );
    }

    #[test]
    fn keeps_known_non_thunk_force_when_result_escapes_tail_substitution() {
        let mut function = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(0),
                                literal: CpsLiteral::Int("42".to_string()),
                            },
                            CpsStmt::ForceThunk {
                                dest: CpsValueId(1),
                                thunk: CpsValueId(0),
                            },
                        ],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(1),
                            args: vec![CpsValueId(1)],
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(2)],
                        captures: vec![CpsValueId(1)],
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(2)),
                    },
                ],
            }],
        }))
        .roots
        .remove(0);

        let removed = remove_redundant_non_thunk_forces_in_function(&mut function, &HashSet::new());

        assert_eq!(removed, 0);
        assert_eq!(function.continuations[0].stmts.len(), 2);
    }

    #[test]
    fn removes_force_of_safe_scalar_primitive_result() {
        let mut function = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("20".to_string()),
                        },
                        CpsStmt::Literal {
                            dest: CpsValueId(1),
                            literal: CpsLiteral::Int("22".to_string()),
                        },
                        CpsStmt::Primitive {
                            dest: CpsValueId(2),
                            op: typed_ir::PrimitiveOp::IntAdd,
                            args: vec![CpsValueId(0), CpsValueId(1)],
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(3),
                            thunk: CpsValueId(2),
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(3)),
                }],
            }],
        }))
        .roots
        .remove(0);

        let removed = remove_redundant_non_thunk_forces_in_function(&mut function, &HashSet::new());

        assert_eq!(removed, 1);
        assert_eq!(
            function.continuations[0].terminator,
            CpsTerminator::Return(CpsValueId(2))
        );
    }

    #[test]
    fn removes_force_of_safe_list_primitive_result() {
        let mut function = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::Primitive {
                            dest: CpsValueId(2),
                            op: typed_ir::PrimitiveOp::ListMerge,
                            args: vec![CpsValueId(0), CpsValueId(1)],
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(3),
                            thunk: CpsValueId(2),
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(3)),
                }],
            }],
        }))
        .roots
        .remove(0);

        let removed = remove_redundant_non_thunk_forces_in_function(&mut function, &HashSet::new());

        assert_eq!(removed, 1);
        assert_eq!(
            function.continuations[0].terminator,
            CpsTerminator::Return(CpsValueId(2))
        );
    }

    #[test]
    fn keeps_force_of_list_index_primitive_result() {
        let mut function = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("0".to_string()),
                        },
                        CpsStmt::Primitive {
                            dest: CpsValueId(2),
                            op: typed_ir::PrimitiveOp::ListIndex,
                            args: vec![CpsValueId(1), CpsValueId(0)],
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(3),
                            thunk: CpsValueId(2),
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(3)),
                }],
            }],
        }))
        .roots
        .remove(0);

        let removed = remove_redundant_non_thunk_forces_in_function(&mut function, &HashSet::new());

        assert_eq!(removed, 0);
        assert!(matches!(
            function.continuations[0].stmts.last(),
            Some(CpsStmt::ForceThunk { .. })
        ));
    }

    #[test]
    fn removes_force_of_direct_call_with_known_non_thunk_return() {
        let module = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: vec![CpsFunction {
                name: "callee".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("42".to_string()),
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(1),
                            thunk: CpsValueId(0),
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(1)),
                }],
            }],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::DirectCall {
                            dest: CpsValueId(2),
                            target: "callee".to_string(),
                            args: Vec::new(),
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(3),
                            thunk: CpsValueId(2),
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(3)),
                }],
            }],
        }));
        let mut output = CpsOptimizationOutput {
            profile: CpsOptimizationProfile::measure(&module),
            module,
        };

        remove_redundant_non_thunk_forces(&mut output);

        assert_eq!(output.profile.removed_redundant_non_thunk_forces, 2);
        assert_eq!(
            output.module.roots[0].continuations[0].terminator,
            CpsTerminator::Return(CpsValueId(2))
        );
    }

    #[test]
    fn keeps_force_of_direct_call_with_unknown_return() {
        let module = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: vec![CpsFunction {
                name: "callee".to_string(),
                params: vec![CpsValueId(0)],
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: vec![CpsValueId(0)],
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: Vec::new(),
                    terminator: CpsTerminator::Return(CpsValueId(0)),
                }],
            }],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(1),
                            literal: CpsLiteral::Int("42".to_string()),
                        },
                        CpsStmt::DirectCall {
                            dest: CpsValueId(2),
                            target: "callee".to_string(),
                            args: vec![CpsValueId(1)],
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(3),
                            thunk: CpsValueId(2),
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(3)),
                }],
            }],
        }));
        let mut output = CpsOptimizationOutput {
            profile: CpsOptimizationProfile::measure(&module),
            module,
        };

        remove_redundant_non_thunk_forces(&mut output);

        assert_eq!(output.profile.removed_redundant_non_thunk_forces, 0);
        assert!(matches!(
            output.module.roots[0].continuations[0].stmts.last(),
            Some(CpsStmt::ForceThunk { .. })
        ));
    }

    #[test]
    fn direct_return_analysis_ignores_thunk_entry_returns() {
        let module = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: vec![CpsFunction {
                name: "callee".to_string(),
                params: vec![CpsValueId(0)],
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: vec![CpsValueId(0)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::MakeThunk {
                                dest: CpsValueId(1),
                                entry: CpsContinuationId(1),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("42".to_string()),
                            },
                            CpsStmt::ForceThunk {
                                dest: CpsValueId(3),
                                thunk: CpsValueId(2),
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: Vec::new(),
                        captures: vec![CpsValueId(0)],
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(0)),
                    },
                ],
            }],
            roots: Vec::new(),
        }));

        let non_thunk_returns = direct_non_thunk_return_functions(&module);

        assert!(non_thunk_returns.contains("callee"));
    }

    #[test]
    fn rewrites_empty_continue_forwarder_calls() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("42".to_string()),
                        }],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(1),
                            args: vec![CpsValueId(0)],
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(1)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(2),
                            args: vec![CpsValueId(1)],
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(2)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(2)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let entry = &optimized.module.roots[0].continuations[0];

        assert_eq!(entry.terminator, CpsTerminator::Return(CpsValueId(0)));
        assert_eq!(optimized.profile.forwarded_continuation_calls, 1);
        assert_eq!(optimized.profile.returned_continuation_calls, 2);
        assert_eq!(optimized.profile.reified_primitive_calls, 0);
        assert_eq!(optimized.profile.reified_partial_closure_calls, 0);
        assert_eq!(optimized.profile.inlined_pure_direct_calls, 0);
        assert_eq!(optimized.profile.inlined_continuation_calls, 0);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 2);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 0);
        assert_eq!(optimized.profile.direct_style_islands, 1);
        assert_eq!(optimized.profile.direct_style_continuations, 1);
        assert!(optimized.profile.changed);
    }

    #[test]
    fn rewrites_empty_returning_continuation_calls() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("42".to_string()),
                        }],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(1),
                            args: vec![CpsValueId(0)],
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(1)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(1)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let entry = &optimized.module.roots[0].continuations[0];

        assert_eq!(entry.terminator, CpsTerminator::Return(CpsValueId(0)));
        assert_eq!(optimized.profile.returned_continuation_calls, 1);
        assert_eq!(optimized.profile.reified_primitive_calls, 0);
        assert_eq!(optimized.profile.reified_partial_closure_calls, 0);
        assert_eq!(optimized.profile.inlined_pure_direct_calls, 0);
        assert_eq!(optimized.profile.inlined_continuation_calls, 0);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 1);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 0);
        assert_eq!(optimized.profile.direct_style_islands, 1);
        assert_eq!(optimized.profile.direct_style_continuations, 1);
        assert!(optimized.profile.changed);
    }

    #[test]
    fn inlines_single_use_one_shot_continuations() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("41".to_string()),
                        }],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(1),
                            args: vec![CpsValueId(0)],
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(1)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("1".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(3),
                                op: yulang_typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(1), CpsValueId(2)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let root = &optimized.module.roots[0];
        let entry = &root.continuations[0];

        assert_eq!(root.continuations.len(), 1);
        assert_eq!(entry.stmts.len(), 3);
        assert_eq!(
            entry.stmts[2],
            CpsStmt::Primitive {
                dest: CpsValueId(3),
                op: yulang_typed_ir::PrimitiveOp::IntAdd,
                args: vec![CpsValueId(0), CpsValueId(2)],
            }
        );
        assert_eq!(entry.terminator, CpsTerminator::Return(CpsValueId(3)));
        assert_eq!(optimized.profile.inlined_continuation_calls, 1);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 1);
        assert_eq!(optimized.profile.direct_style_islands, 1);
        assert_eq!(optimized.profile.direct_style_continuations, 1);
    }

    #[test]
    fn inlines_local_one_shot_thunk_force_to_resume_continue() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(0),
                                literal: CpsLiteral::Int("40".to_string()),
                            },
                            CpsStmt::MakeThunk {
                                dest: CpsValueId(1),
                                entry: CpsContinuationId(1),
                            },
                        ],
                        terminator: CpsTerminator::EffectfulForce {
                            thunk: CpsValueId(1),
                            resume: CpsContinuationId(2),
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: Vec::new(),
                        captures: vec![CpsValueId(0)],
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("2".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(3),
                                op: yulang_typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(0), CpsValueId(2)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(4)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(4)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let root = &optimized.module.roots[0];
        let entry = &root.continuations[0];

        assert_eq!(root.continuations.len(), 1);
        assert_eq!(optimized.profile.inlined_local_thunk_forces, 1);
        assert!(
            !entry
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, CpsStmt::MakeThunk { .. }))
        );
        assert!(matches!(
            entry.terminator,
            CpsTerminator::Return(CpsValueId(3))
        ));
    }

    #[test]
    fn reifies_direct_calls_to_primitive_wrappers() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: vec![CpsFunction {
                name: "add".to_string(),
                params: vec![CpsValueId(0), CpsValueId(1)],
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: vec![CpsValueId(0), CpsValueId(1)],
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::MultiShot,
                    stmts: vec![CpsStmt::Primitive {
                        dest: CpsValueId(2),
                        op: typed_ir::PrimitiveOp::IntAdd,
                        args: vec![CpsValueId(0), CpsValueId(1)],
                    }],
                    terminator: CpsTerminator::Return(CpsValueId(2)),
                }],
            }],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("1".to_string()),
                        },
                        CpsStmt::Literal {
                            dest: CpsValueId(1),
                            literal: CpsLiteral::Int("2".to_string()),
                        },
                        CpsStmt::DirectCall {
                            dest: CpsValueId(2),
                            target: "add".to_string(),
                            args: vec![CpsValueId(0), CpsValueId(1)],
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(2)),
                }],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let entry = &optimized.module.roots[0].continuations[0];

        assert_eq!(
            entry.stmts[2],
            CpsStmt::Primitive {
                dest: CpsValueId(2),
                op: typed_ir::PrimitiveOp::IntAdd,
                args: vec![CpsValueId(0), CpsValueId(1)],
            }
        );
        assert_eq!(optimized.profile.reified_primitive_calls, 1);
        assert_eq!(optimized.profile.direct_style_islands, 2);
        assert_eq!(optimized.profile.direct_style_continuations, 2);
    }

    #[test]
    fn inlines_small_pure_direct_calls() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: vec![CpsFunction {
                name: "plus_one".to_string(),
                params: vec![CpsValueId(0)],
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: vec![CpsValueId(0)],
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(1),
                            literal: CpsLiteral::Int("1".to_string()),
                        },
                        CpsStmt::Primitive {
                            dest: CpsValueId(2),
                            op: typed_ir::PrimitiveOp::IntAdd,
                            args: vec![CpsValueId(0), CpsValueId(1)],
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(2)),
                }],
            }],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("41".to_string()),
                        },
                        CpsStmt::DirectCall {
                            dest: CpsValueId(1),
                            target: "plus_one".to_string(),
                            args: vec![CpsValueId(0)],
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(1)),
                }],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let entry = &optimized.module.roots[0].continuations[0];

        assert_eq!(entry.stmts.len(), 3);
        assert_eq!(
            entry.stmts[1],
            CpsStmt::Literal {
                dest: CpsValueId(2),
                literal: CpsLiteral::Int("1".to_string()),
            }
        );
        assert_eq!(
            entry.stmts[2],
            CpsStmt::Primitive {
                dest: CpsValueId(1),
                op: typed_ir::PrimitiveOp::IntAdd,
                args: vec![CpsValueId(0), CpsValueId(2)],
            }
        );
        assert_eq!(optimized.profile.inlined_pure_direct_calls, 1);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 0);
    }

    #[test]
    fn inlines_small_structural_pure_direct_calls() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: vec![CpsFunction {
                name: "pair".to_string(),
                params: vec![CpsValueId(0), CpsValueId(1)],
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: vec![CpsValueId(0), CpsValueId(1)],
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![CpsStmt::Tuple {
                        dest: CpsValueId(2),
                        items: vec![CpsValueId(0), CpsValueId(1)],
                    }],
                    terminator: CpsTerminator::Return(CpsValueId(2)),
                }],
            }],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("1".to_string()),
                        },
                        CpsStmt::Literal {
                            dest: CpsValueId(1),
                            literal: CpsLiteral::Int("2".to_string()),
                        },
                        CpsStmt::DirectCall {
                            dest: CpsValueId(2),
                            target: "pair".to_string(),
                            args: vec![CpsValueId(0), CpsValueId(1)],
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(2)),
                }],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let entry = &optimized.module.roots[0].continuations[0];

        assert_eq!(
            entry.stmts[2],
            CpsStmt::Tuple {
                dest: CpsValueId(2),
                items: vec![CpsValueId(0), CpsValueId(1)],
            }
        );
        assert_eq!(optimized.profile.inlined_pure_direct_calls, 1);
    }

    #[test]
    fn rewrites_effectful_call_to_pure_callee() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: vec![CpsFunction {
                name: "plus_one".to_string(),
                params: vec![CpsValueId(0)],
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: vec![CpsValueId(0)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(1),
                                literal: CpsLiteral::Int("1".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(2),
                                op: typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(0), CpsValueId(1)],
                            },
                        ],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(1),
                            args: vec![CpsValueId(2)],
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(3)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                ],
            }],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("41".to_string()),
                        }],
                        terminator: CpsTerminator::EffectfulCall {
                            target: "plus_one".to_string(),
                            args: vec![CpsValueId(0)],
                            resume: CpsContinuationId(1),
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(1)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(1)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let entry = &optimized.module.roots[0].continuations[0];

        assert_eq!(
            entry.stmts[1],
            CpsStmt::Literal {
                dest: CpsValueId(3),
                literal: CpsLiteral::Int("1".to_string()),
            }
        );
        assert_eq!(
            entry.stmts[2],
            CpsStmt::Primitive {
                dest: CpsValueId(2),
                op: typed_ir::PrimitiveOp::IntAdd,
                args: vec![CpsValueId(0), CpsValueId(3)],
            }
        );
        assert_eq!(entry.terminator, CpsTerminator::Return(CpsValueId(2)));
        assert_eq!(optimized.profile.rewritten_pure_effectful_calls, 1);
        assert_eq!(optimized.profile.inlined_pure_direct_calls, 1);
        assert_eq!(optimized.profile.returned_continuation_calls, 1);
    }

    #[test]
    fn reifies_local_partial_closure_apply_to_direct_call() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: vec![CpsFunction {
                name: "add".to_string(),
                params: vec![CpsValueId(0), CpsValueId(1)],
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: vec![CpsValueId(0), CpsValueId(1)],
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::MultiShot,
                    stmts: vec![CpsStmt::Primitive {
                        dest: CpsValueId(2),
                        op: typed_ir::PrimitiveOp::IntAdd,
                        args: vec![CpsValueId(0), CpsValueId(1)],
                    }],
                    terminator: CpsTerminator::Return(CpsValueId(2)),
                }],
            }],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(0),
                                literal: CpsLiteral::Int("40".to_string()),
                            },
                            CpsStmt::MakeClosure {
                                dest: CpsValueId(1),
                                entry: CpsContinuationId(1),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("2".to_string()),
                            },
                            CpsStmt::ApplyClosure {
                                dest: CpsValueId(3),
                                closure: CpsValueId(1),
                                arg: CpsValueId(2),
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(4)],
                        captures: vec![CpsValueId(0)],
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::DirectCall {
                            dest: CpsValueId(5),
                            target: "add".to_string(),
                            args: vec![CpsValueId(0), CpsValueId(4)],
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(5)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let entry = &optimized.module.roots[0].continuations[0];

        assert_eq!(entry.stmts.len(), 3);
        assert_eq!(
            entry.stmts[2],
            CpsStmt::Primitive {
                dest: CpsValueId(3),
                op: typed_ir::PrimitiveOp::IntAdd,
                args: vec![CpsValueId(0), CpsValueId(2)],
            }
        );
        assert_eq!(optimized.profile.reified_partial_closure_calls, 1);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 1);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 1);
        assert_eq!(optimized.profile.direct_style_islands, 2);
        assert_eq!(optimized.profile.direct_style_continuations, 2);
    }

    #[test]
    fn inlines_local_direct_style_closure_apply() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(0),
                                literal: CpsLiteral::Int("40".to_string()),
                            },
                            CpsStmt::MakeClosure {
                                dest: CpsValueId(1),
                                entry: CpsContinuationId(1),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("2".to_string()),
                            },
                            CpsStmt::ApplyClosure {
                                dest: CpsValueId(3),
                                closure: CpsValueId(1),
                                arg: CpsValueId(2),
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(4)],
                        captures: vec![CpsValueId(0)],
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![
                            CpsStmt::Primitive {
                                dest: CpsValueId(5),
                                op: typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(0), CpsValueId(4)],
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(6),
                                op: typed_ir::PrimitiveOp::IntMul,
                                args: vec![CpsValueId(5), CpsValueId(4)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(6)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let root = &optimized.module.roots[0];
        let entry = &root.continuations[0];

        assert_eq!(root.continuations.len(), 1);
        assert!(entry.stmts.iter().all(|stmt| !matches!(
            stmt,
            CpsStmt::MakeClosure { .. } | CpsStmt::ApplyClosure { .. }
        )));
        assert!(entry.stmts.iter().any(|stmt| {
            matches!(
                stmt,
                CpsStmt::Primitive {
                    dest: CpsValueId(3),
                    op: typed_ir::PrimitiveOp::IntMul,
                    args,
                } if args == &vec![CpsValueId(7), CpsValueId(2)]
            )
        }));
        assert_eq!(entry.terminator, CpsTerminator::Return(CpsValueId(3)));
        assert_eq!(optimized.profile.reified_partial_closure_calls, 0);
        assert_eq!(optimized.profile.inlined_continuation_calls, 1);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 1);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 1);
    }

    #[test]
    fn reifies_partial_closure_apply_after_inline() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: vec![CpsFunction {
                name: "add".to_string(),
                params: vec![CpsValueId(0), CpsValueId(1)],
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: vec![CpsValueId(0), CpsValueId(1)],
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::MultiShot,
                    stmts: vec![CpsStmt::Primitive {
                        dest: CpsValueId(2),
                        op: typed_ir::PrimitiveOp::IntAdd,
                        args: vec![CpsValueId(0), CpsValueId(1)],
                    }],
                    terminator: CpsTerminator::Return(CpsValueId(2)),
                }],
            }],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(0),
                                literal: CpsLiteral::Int("40".to_string()),
                            },
                            CpsStmt::MakeClosure {
                                dest: CpsValueId(1),
                                entry: CpsContinuationId(1),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("2".to_string()),
                            },
                        ],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(2),
                            args: vec![CpsValueId(1), CpsValueId(2)],
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(4)],
                        captures: vec![CpsValueId(0)],
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::DirectCall {
                            dest: CpsValueId(5),
                            target: "add".to_string(),
                            args: vec![CpsValueId(0), CpsValueId(4)],
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(5)),
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(6), CpsValueId(7)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::ApplyClosure {
                            dest: CpsValueId(8),
                            closure: CpsValueId(6),
                            arg: CpsValueId(7),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(8)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let entry = &optimized.module.roots[0].continuations[0];

        assert_eq!(entry.stmts.len(), 3);
        assert_eq!(
            entry.stmts[2],
            CpsStmt::Primitive {
                dest: CpsValueId(8),
                op: typed_ir::PrimitiveOp::IntAdd,
                args: vec![CpsValueId(0), CpsValueId(2)],
            }
        );
        assert_eq!(entry.terminator, CpsTerminator::Return(CpsValueId(8)));
        assert_eq!(optimized.profile.inlined_continuation_calls, 1);
        assert_eq!(optimized.profile.reified_partial_closure_calls, 1);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 2);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 1);
        assert_eq!(optimized.profile.direct_style_islands, 2);
        assert_eq!(optimized.profile.direct_style_continuations, 2);
    }

    #[test]
    fn reifies_uncaptured_closure_apply_through_continuation_parameter() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::MakeClosure {
                                dest: CpsValueId(0),
                                entry: CpsContinuationId(1),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(1),
                                literal: CpsLiteral::Int("7".to_string()),
                            },
                        ],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(2),
                            args: vec![CpsValueId(0), CpsValueId(1)],
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(2)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Primitive {
                            dest: CpsValueId(3),
                            op: typed_ir::PrimitiveOp::IntToString,
                            args: vec![CpsValueId(2)],
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(4), CpsValueId(5)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::ApplyClosure {
                            dest: CpsValueId(6),
                            closure: CpsValueId(4),
                            arg: CpsValueId(5),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(6)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let root = &optimized.module.roots[0];
        let entry = root
            .continuations
            .iter()
            .find(|continuation| continuation.id == CpsContinuationId(0))
            .unwrap();

        assert!(root.continuations.iter().all(|continuation| {
            continuation
                .stmts
                .iter()
                .all(|stmt| !matches!(stmt, CpsStmt::ApplyClosure { .. }))
        }));
        assert!(entry.stmts.iter().any(|stmt| {
            matches!(
                stmt,
                CpsStmt::Primitive {
                    op: typed_ir::PrimitiveOp::IntToString,
                    args,
                    ..
                } if args == &vec![CpsValueId(1)]
            )
        }));
        assert_eq!(entry.terminator, CpsTerminator::Return(CpsValueId(6)));
        assert_eq!(optimized.profile.reified_partial_closure_calls, 0);
        assert_eq!(optimized.profile.reified_known_closure_parameter_calls, 1);
        assert_eq!(optimized.profile.inlined_continuation_calls, 1);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 2);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 1);
    }

    #[test]
    fn reifies_captured_closure_apply_when_captures_are_continuation_parameters() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: vec![CpsFunction {
                name: "add".to_string(),
                params: vec![CpsValueId(0), CpsValueId(1)],
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: vec![CpsValueId(0), CpsValueId(1)],
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::MultiShot,
                    stmts: vec![CpsStmt::Primitive {
                        dest: CpsValueId(2),
                        op: typed_ir::PrimitiveOp::IntAdd,
                        args: vec![CpsValueId(0), CpsValueId(1)],
                    }],
                    terminator: CpsTerminator::Return(CpsValueId(2)),
                }],
            }],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(0),
                                literal: CpsLiteral::Int("40".to_string()),
                            },
                            CpsStmt::MakeClosure {
                                dest: CpsValueId(1),
                                entry: CpsContinuationId(1),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("2".to_string()),
                            },
                        ],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(2),
                            args: vec![CpsValueId(1), CpsValueId(0), CpsValueId(2)],
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(4)],
                        captures: vec![CpsValueId(0)],
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::DirectCall {
                            dest: CpsValueId(5),
                            target: "add".to_string(),
                            args: vec![CpsValueId(0), CpsValueId(4)],
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(5)),
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(6), CpsValueId(7), CpsValueId(8)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::ApplyClosure {
                            dest: CpsValueId(9),
                            closure: CpsValueId(6),
                            arg: CpsValueId(8),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(9)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let root = &optimized.module.roots[0];
        let entry = root
            .continuations
            .iter()
            .find(|continuation| continuation.id == CpsContinuationId(0))
            .unwrap();

        assert!(root.continuations.iter().all(|continuation| {
            continuation
                .stmts
                .iter()
                .all(|stmt| !matches!(stmt, CpsStmt::ApplyClosure { .. }))
        }));
        assert!(entry.stmts.iter().any(|stmt| {
            matches!(
                stmt,
                CpsStmt::Primitive {
                    op: typed_ir::PrimitiveOp::IntAdd,
                    args,
                    ..
                } if args == &vec![CpsValueId(0), CpsValueId(2)]
            )
        }));
        assert_eq!(entry.terminator, CpsTerminator::Return(CpsValueId(9)));
        assert_eq!(optimized.profile.reified_partial_closure_calls, 0);
        assert_eq!(optimized.profile.reified_known_closure_parameter_calls, 1);
        assert_eq!(optimized.profile.inlined_continuation_calls, 1);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 2);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 1);
    }

    #[test]
    fn reifies_local_effectful_apply_to_known_primitive_closure() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::MakeClosure {
                                dest: CpsValueId(0),
                                entry: CpsContinuationId(1),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(1),
                                literal: CpsLiteral::Int("7".to_string()),
                            },
                        ],
                        terminator: CpsTerminator::EffectfulApply {
                            closure: CpsValueId(0),
                            arg: CpsValueId(1),
                            resume: CpsContinuationId(2),
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(2)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Primitive {
                            dest: CpsValueId(3),
                            op: typed_ir::PrimitiveOp::IntToString,
                            args: vec![CpsValueId(2)],
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(4)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(4)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let root = &optimized.module.roots[0];
        let entry = root
            .continuations
            .iter()
            .find(|continuation| continuation.id == CpsContinuationId(0))
            .unwrap();

        assert!(root.continuations.iter().all(|continuation| {
            !matches!(
                continuation.terminator,
                CpsTerminator::EffectfulApply { .. }
            )
        }));
        assert!(entry.stmts.iter().any(|stmt| {
            matches!(
                stmt,
                CpsStmt::Primitive {
                    op: typed_ir::PrimitiveOp::IntToString,
                    args,
                    ..
                } if args == &vec![CpsValueId(1)]
            )
        }));
        assert!(matches!(entry.terminator, CpsTerminator::Return(_)));
        assert_eq!(optimized.profile.reified_partial_closure_calls, 1);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 2);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 1);
    }

    #[test]
    fn removes_dead_pure_value_statements() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("1".to_string()),
                        },
                        CpsStmt::Literal {
                            dest: CpsValueId(1),
                            literal: CpsLiteral::Int("2".to_string()),
                        },
                        CpsStmt::Tuple {
                            dest: CpsValueId(2),
                            items: vec![CpsValueId(0), CpsValueId(1)],
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(0)),
                }],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let entry = &optimized.module.roots[0].continuations[0];

        assert_eq!(
            entry.stmts,
            vec![CpsStmt::Literal {
                dest: CpsValueId(0),
                literal: CpsLiteral::Int("1".to_string()),
            }]
        );
        assert_eq!(optimized.profile.removed_dead_pure_statements, 2);
    }

    #[test]
    fn removes_dead_total_primitives_and_structural_projections() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("1".to_string()),
                        },
                        CpsStmt::Literal {
                            dest: CpsValueId(1),
                            literal: CpsLiteral::Int("2".to_string()),
                        },
                        CpsStmt::Primitive {
                            dest: CpsValueId(2),
                            op: typed_ir::PrimitiveOp::IntAdd,
                            args: vec![CpsValueId(0), CpsValueId(1)],
                        },
                        CpsStmt::Tuple {
                            dest: CpsValueId(3),
                            items: vec![CpsValueId(0), CpsValueId(1)],
                        },
                        CpsStmt::TupleGet {
                            dest: CpsValueId(4),
                            tuple: CpsValueId(3),
                            index: 1,
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(0)),
                }],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let entry = &optimized.module.roots[0].continuations[0];

        assert_eq!(
            entry.stmts,
            vec![CpsStmt::Literal {
                dest: CpsValueId(0),
                literal: CpsLiteral::Int("1".to_string()),
            }]
        );
        assert_eq!(optimized.profile.folded_structural_projections, 1);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 3);
    }

    #[test]
    fn folds_tuple_get_from_local_tuple() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("1".to_string()),
                        },
                        CpsStmt::Literal {
                            dest: CpsValueId(1),
                            literal: CpsLiteral::Int("2".to_string()),
                        },
                        CpsStmt::Tuple {
                            dest: CpsValueId(2),
                            items: vec![CpsValueId(0), CpsValueId(1)],
                        },
                        CpsStmt::TupleGet {
                            dest: CpsValueId(3),
                            tuple: CpsValueId(2),
                            index: 1,
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(3)),
                }],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let entry = &optimized.module.roots[0].continuations[0];

        assert_eq!(
            entry.stmts,
            vec![CpsStmt::Literal {
                dest: CpsValueId(1),
                literal: CpsLiteral::Int("2".to_string()),
            }]
        );
        assert_eq!(entry.terminator, CpsTerminator::Return(CpsValueId(1)));
        assert_eq!(optimized.profile.folded_structural_projections, 1);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 2);
    }

    #[test]
    fn removes_unused_multi_use_continuation_parameters() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(0),
                                literal: CpsLiteral::Int("1".to_string()),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(8),
                                literal: CpsLiteral::Bool(false),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(9),
                                op: typed_ir::PrimitiveOp::BoolNot,
                                args: vec![CpsValueId(8)],
                            },
                        ],
                        terminator: CpsTerminator::Branch {
                            cond: CpsValueId(9),
                            then_cont: CpsContinuationId(1),
                            else_cont: CpsContinuationId(2),
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(2),
                            literal: CpsLiteral::Int("2".to_string()),
                        }],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(3),
                            args: vec![CpsValueId(0), CpsValueId(2)],
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(2),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(3),
                            literal: CpsLiteral::Int("3".to_string()),
                        }],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(3),
                            args: vec![CpsValueId(0), CpsValueId(3)],
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(3),
                        params: vec![CpsValueId(4), CpsValueId(5)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(6),
                                literal: CpsLiteral::Int("0".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(7),
                                op: typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(5), CpsValueId(6)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(7)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let root = &optimized.module.roots[0];
        let join = root
            .continuations
            .iter()
            .find(|continuation| continuation.id == CpsContinuationId(3))
            .unwrap();

        assert_eq!(
            join.params
                .iter()
                .map(|param| param.value)
                .collect::<Vec<_>>(),
            vec![CpsValueId(5)]
        );
        for source in [CpsContinuationId(1), CpsContinuationId(2)] {
            let continuation = root
                .continuations
                .iter()
                .find(|continuation| continuation.id == source)
                .unwrap();
            assert!(matches!(
                &continuation.terminator,
                CpsTerminator::Continue { args, .. } if args.len() == 1
            ));
        }
        assert_eq!(optimized.profile.removed_unused_continuation_params, 1);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 1);
    }

    #[test]
    fn removes_unused_closure_environment_slots_and_reindexes_remaining_slots() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(0),
                                literal: CpsLiteral::Int("1".to_string()),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(1),
                                literal: CpsLiteral::Int("2".to_string()),
                            },
                            CpsStmt::MakeClosure {
                                dest: CpsValueId(2),
                                entry: CpsContinuationId(1),
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(2)),
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(3)],
                        captures: vec![CpsValueId(0), CpsValueId(1)],
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Primitive {
                            dest: CpsValueId(4),
                            op: typed_ir::PrimitiveOp::IntAdd,
                            args: vec![CpsValueId(1), CpsValueId(3)],
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(4)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let root = &optimized.module.roots[0];
        let closure_entry = root
            .continuations
            .iter()
            .find(|continuation| continuation.id == CpsContinuationId(1))
            .unwrap();

        assert_eq!(closure_entry.environment.len(), 1);
        assert_eq!(closure_entry.environment[0].index, 0);
        assert_eq!(closure_entry.environment[0].value, CpsValueId(1));
        assert_eq!(optimized.profile.removed_unused_environment_slots, 1);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 1);
    }

    #[test]
    fn folds_constant_bool_branches_before_pruning() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Bool(true),
                        }],
                        terminator: CpsTerminator::Branch {
                            cond: CpsValueId(0),
                            then_cont: CpsContinuationId(1),
                            else_cont: CpsContinuationId(2),
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(1),
                            literal: CpsLiteral::Int("1".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(1)),
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(2),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(2),
                            literal: CpsLiteral::Int("2".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(2)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let entry = &optimized.module.roots[0].continuations[0];

        assert_eq!(
            entry.stmts,
            vec![CpsStmt::Literal {
                dest: CpsValueId(1),
                literal: CpsLiteral::Int("1".to_string()),
            }]
        );
        assert_eq!(entry.terminator, CpsTerminator::Return(CpsValueId(1)));
        assert_eq!(optimized.profile.folded_constant_branches, 1);
        assert_eq!(optimized.profile.inlined_continuation_calls, 1);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 2);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 1);
    }

    #[test]
    fn keeps_handler_arm_entries_when_pruning_unreachable_continuations() {
        let effect = yulang_typed_ir::Path::from_name(yulang_typed_ir::Name("ask".to_string()));
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![crate::cps_ir::CpsHandler {
                    id: crate::cps_ir::CpsHandlerId(0),
                    arms: vec![crate::cps_ir::CpsHandlerArm {
                        effect,
                        entry: CpsContinuationId(1),
                    }],
                }],
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("1".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(0)),
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(1), CpsValueId(2)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(1)),
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(2),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(0)),
                    },
                ],
            }],
        }));

        let optimized = optimize_cps_repr_abi_module(&abi);
        let ids = optimized.module.roots[0]
            .continuations
            .iter()
            .map(|continuation| continuation.id)
            .collect::<Vec<_>>();

        assert_eq!(ids, vec![CpsContinuationId(0), CpsContinuationId(1)]);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 1);
    }

    #[test]
    fn contifies_known_thunk_argument_into_cloned_effectful_force_boundary() {
        let mut root = CpsReprAbiFunction {
            name: "root".to_string(),
            params: Vec::new(),
            entry: CpsContinuationId(0),
            continuations: vec![
                abi_continuation(
                    CpsContinuationId(0),
                    Vec::new(),
                    vec![
                        CpsStmt::MakeThunk {
                            dest: CpsValueId(0),
                            entry: CpsContinuationId(1),
                        },
                        CpsStmt::DirectCall {
                            dest: CpsValueId(1),
                            target: "collector".to_string(),
                            args: vec![CpsValueId(0)],
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(2),
                            thunk: CpsValueId(1),
                        },
                    ],
                    CpsTerminator::Return(CpsValueId(2)),
                ),
                abi_continuation(
                    CpsContinuationId(1),
                    Vec::new(),
                    vec![CpsStmt::Literal {
                        dest: CpsValueId(3),
                        literal: CpsLiteral::Int("7".to_string()),
                    }],
                    CpsTerminator::Return(CpsValueId(3)),
                ),
            ],
            handlers: Vec::new(),
        };
        let collector = CpsReprAbiFunction {
            name: "collector".to_string(),
            params: vec![abi_value(CpsValueId(0))],
            entry: CpsContinuationId(0),
            continuations: vec![
                abi_continuation(
                    CpsContinuationId(0),
                    vec![CpsValueId(0)],
                    vec![
                        CpsStmt::InstallHandler {
                            handler: CpsHandlerId(0),
                            envs: Vec::new(),
                            value: CpsContinuationId(1),
                            escape: CpsContinuationId(1),
                        },
                        CpsStmt::AddThunkBoundary {
                            dest: CpsValueId(1),
                            thunk: CpsValueId(0),
                            guard: CpsValueId(9),
                            allowed: typed_ir::Type::Any,
                            active: true,
                        },
                    ],
                    CpsTerminator::EffectfulForce {
                        thunk: CpsValueId(1),
                        resume: CpsContinuationId(1),
                    },
                ),
                abi_continuation(
                    CpsContinuationId(1),
                    vec![CpsValueId(2)],
                    Vec::new(),
                    CpsTerminator::Return(CpsValueId(2)),
                ),
                abi_continuation(
                    CpsContinuationId(2),
                    vec![CpsValueId(3), CpsValueId(4)],
                    Vec::new(),
                    CpsTerminator::Return(CpsValueId(3)),
                ),
            ],
            handlers: vec![CpsReprAbiHandler {
                id: CpsHandlerId(0),
                arms: vec![CpsReprAbiHandlerArm {
                    effect: typed_ir::Path::from_name(typed_ir::Name("op".to_string())),
                    entry: CpsContinuationId(2),
                }],
            }],
        };
        let plan = DynamicEffectThunkRewritePlan {
            caller: "root".to_string(),
            call_continuation: CpsContinuationId(0),
            call_stmt_index: 1,
            callee: "collector".to_string(),
            thunk: CpsValueId(0),
            thunk_entry: CpsContinuationId(1),
            post_call_force_chain_len: 1,
            seed_class: DynamicEffectThunkSpecializationClass::ReadyFinite,
            strategy: DynamicEffectThunkRewriteStrategy::DefunctionalizeFiniteHandler,
            body_clone_blockers: Vec::new(),
            finite_effects: Vec::new(),
            finite_callee_boundaries: vec![CpsContinuationId(0)],
            finite_arm_entries: vec![CpsContinuationId(2)],
            finite_performs: Vec::new(),
            finite_resumes: Vec::new(),
            finite_resume_actions: Vec::new(),
            no_resume_effects: Vec::new(),
            blocked_effects: Vec::new(),
        };
        let callees = std::collections::HashMap::from([("collector".to_string(), collector)]);

        let rewritten =
            defunctionalize_finite_handler_thunk_calls_in_function(&mut root, &[plan], &callees);

        assert_eq!(rewritten, 1);
        assert!(matches!(
            root.continuations[0].terminator,
            CpsTerminator::Continue {
                target: CpsContinuationId(3),
                ..
            }
        ));
        let cloned_boundary = root
            .continuations
            .iter()
            .find(|continuation| continuation.id == CpsContinuationId(3))
            .unwrap();
        assert_eq!(
            cloned_boundary.terminator,
            CpsTerminator::Continue {
                target: CpsContinuationId(6),
                args: Vec::new(),
            }
        );
        let cloned_thunk = root
            .continuations
            .iter()
            .find(|continuation| continuation.id == CpsContinuationId(6))
            .unwrap();
        assert_eq!(
            cloned_thunk.terminator,
            CpsTerminator::Continue {
                target: CpsContinuationId(4),
                args: vec![CpsValueId(10)],
            }
        );
    }

    fn sample_abi_module() -> CpsReprAbiModule {
        lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![crate::cps_ir::CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![CpsStmt::Literal {
                        dest: CpsValueId(0),
                        literal: CpsLiteral::Int("42".to_string()),
                    }],
                    terminator: CpsTerminator::Return(CpsValueId(0)),
                }],
            }],
        }))
    }

    fn abi_continuation(
        id: CpsContinuationId,
        params: Vec<CpsValueId>,
        stmts: Vec<CpsStmt>,
        terminator: CpsTerminator,
    ) -> CpsReprAbiContinuation {
        CpsReprAbiContinuation {
            id,
            params: params.into_iter().map(abi_value).collect(),
            environment: Vec::new(),
            shot_kind: CpsShotKind::OneShot,
            return_lane: CpsReprAbiLane::ScalarI64,
            stmts,
            terminator,
        }
    }

    fn abi_value(value: CpsValueId) -> CpsReprAbiValue {
        CpsReprAbiValue {
            value,
            lane: CpsReprAbiLane::ScalarI64,
        }
    }
}
