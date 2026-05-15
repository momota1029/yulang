//! Optimization entrypoint for backend-facing CPS representation ABI.
//!
//! This module is intentionally placed between CPS repr ABI lowering and
//! Cranelift codegen so JIT and object generation share one transformation
//! path.  Early passes are deliberately conservative: they rewrite explicit
//! continuation call sites, but leave closure entries, thunk entries, and
//! handler arm entries alone unless their call protocol is represented at the
//! call site.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::cps_ir::{
    CpsContinuationId, CpsHandlerEnv, CpsRecordField, CpsShotKind, CpsStmt, CpsTerminator,
    CpsValueId,
};
use crate::cps_repr_abi::{CpsReprAbiContinuation, CpsReprAbiFunction, CpsReprAbiModule};

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
    pub passes_run: usize,
    pub forwarded_continuation_calls: usize,
    pub returned_continuation_calls: usize,
    pub inlined_continuation_calls: usize,
    pub removed_unreachable_continuations: usize,
    pub removed_dead_pure_statements: usize,
    pub changed: bool,
}

pub fn optimize_cps_repr_abi_module(module: &CpsReprAbiModule) -> CpsOptimizationOutput {
    let mut output = CpsOptimizationOutput {
        module: module.clone(),
        profile: CpsOptimizationProfile::measure(module),
    };

    rewrite_forwarding_continuation_calls(&mut output);
    rewrite_returning_continuation_calls(&mut output);
    inline_single_use_continuation_calls(&mut output);
    prune_unreachable_continuations(&mut output);
    eliminate_dead_pure_statements(&mut output);
    prune_unreachable_continuations(&mut output);
    maybe_trace_profile(&output.profile);
    output
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

fn maybe_trace_profile(profile: &CpsOptimizationProfile) {
    if std::env::var_os("YULANG_CPS_OPT_TRACE").is_none() {
        return;
    }
    eprintln!(
        "[CPS-OPT] functions={} roots={} continuations={} handlers={} statements={} passes={} forwarded_continuation_calls={} returned_continuation_calls={} inlined_continuation_calls={} removed_unreachable_continuations={} removed_dead_pure_statements={} changed={}",
        profile.functions,
        profile.roots,
        profile.continuations,
        profile.handlers,
        profile.statements,
        profile.passes_run,
        profile.forwarded_continuation_calls,
        profile.returned_continuation_calls,
        profile.inlined_continuation_calls,
        profile.removed_unreachable_continuations,
        profile.removed_dead_pure_statements,
        profile.changed
    );
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
        CpsStmt::InstallHandler { escape, envs, .. } => {
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
        CpsStmt::InstallHandler { escape, envs, .. } => {
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
            | CpsStmt::RecordHasField { .. }
            | CpsStmt::VariantTagEq { .. }
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
        CpsStmt::InstallHandler { escape, envs, .. } => {
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
            escape,
        } => CpsStmt::InstallHandler {
            handler,
            envs: subst_handler_envs(envs, substitution),
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
            passes_run: 0,
            forwarded_continuation_calls: 0,
            returned_continuation_calls: 0,
            inlined_continuation_calls: 0,
            removed_unreachable_continuations: 0,
            removed_dead_pure_statements: 0,
            changed: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::cps_ir::{
        CpsContinuationId, CpsFunction, CpsLiteral, CpsModule, CpsShotKind, CpsStmt, CpsTerminator,
        CpsValueId,
    };
    use crate::cps_repr::lower_cps_repr_module;
    use crate::cps_repr_abi::lower_cps_repr_abi_module;

    use super::*;

    #[test]
    fn optimization_boundary_keeps_non_forwarding_module() {
        let abi = sample_abi_module();
        let optimized = optimize_cps_repr_abi_module(&abi);

        assert_eq!(optimized.module, abi);
        assert_eq!(optimized.profile.roots, 1);
        assert_eq!(optimized.profile.continuations, 1);
        assert_eq!(optimized.profile.statements, 1);
        assert_eq!(optimized.profile.passes_run, 6);
        assert_eq!(optimized.profile.forwarded_continuation_calls, 0);
        assert_eq!(optimized.profile.returned_continuation_calls, 0);
        assert_eq!(optimized.profile.inlined_continuation_calls, 0);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 0);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 0);
        assert!(!optimized.profile.changed);
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
        assert_eq!(optimized.profile.inlined_continuation_calls, 0);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 2);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 0);
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
        assert_eq!(optimized.profile.inlined_continuation_calls, 0);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 1);
        assert_eq!(optimized.profile.removed_dead_pure_statements, 0);
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
}
