//! Optimization entrypoint for backend-facing CPS representation ABI.
//!
//! This module is intentionally placed between CPS repr ABI lowering and
//! Cranelift codegen so JIT and object generation share one transformation
//! path.  Early passes are deliberately conservative: they rewrite explicit
//! continuation call sites, but leave closure entries, thunk entries, and
//! handler arm entries alone unless their call protocol is represented at the
//! call site.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::cps_ir::{CpsContinuationId, CpsStmt, CpsTerminator, CpsValueId};
use crate::cps_repr_abi::{CpsReprAbiFunction, CpsReprAbiModule};

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
    pub removed_unreachable_continuations: usize,
    pub changed: bool,
}

pub fn optimize_cps_repr_abi_module(module: &CpsReprAbiModule) -> CpsOptimizationOutput {
    let mut output = CpsOptimizationOutput {
        module: module.clone(),
        profile: CpsOptimizationProfile::measure(module),
    };

    rewrite_forwarding_continuation_calls(&mut output);
    rewrite_returning_continuation_calls(&mut output);
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

fn maybe_trace_profile(profile: &CpsOptimizationProfile) {
    if std::env::var_os("YULANG_CPS_OPT_TRACE").is_none() {
        return;
    }
    eprintln!(
        "[CPS-OPT] functions={} roots={} continuations={} handlers={} statements={} passes={} forwarded_continuation_calls={} returned_continuation_calls={} removed_unreachable_continuations={} changed={}",
        profile.functions,
        profile.roots,
        profile.continuations,
        profile.handlers,
        profile.statements,
        profile.passes_run,
        profile.forwarded_continuation_calls,
        profile.returned_continuation_calls,
        profile.removed_unreachable_continuations,
        profile.changed
    );
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
            removed_unreachable_continuations: 0,
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
        assert_eq!(optimized.profile.passes_run, 3);
        assert_eq!(optimized.profile.forwarded_continuation_calls, 0);
        assert_eq!(optimized.profile.returned_continuation_calls, 0);
        assert_eq!(optimized.profile.removed_unreachable_continuations, 0);
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
        assert_eq!(optimized.profile.removed_unreachable_continuations, 2);
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
        assert_eq!(optimized.profile.removed_unreachable_continuations, 1);
        assert!(optimized.profile.changed);
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
