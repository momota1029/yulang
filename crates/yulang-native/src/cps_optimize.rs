//! Optimization entrypoint for backend-facing CPS representation ABI.
//!
//! This module is intentionally placed between CPS repr ABI lowering and
//! Cranelift codegen so JIT and object generation share one transformation
//! path.  Early passes are deliberately conservative: they rewrite explicit
//! continuation call sites, but leave closure entries, thunk entries, and
//! handler arm entries alone unless their call protocol is represented at the
//! call site.

use std::collections::HashMap;

use crate::cps_ir::{CpsContinuationId, CpsTerminator, CpsValueId};
use crate::cps_repr_abi::CpsReprAbiModule;

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
    pub changed: bool,
}

pub fn optimize_cps_repr_abi_module(module: &CpsReprAbiModule) -> CpsOptimizationOutput {
    let mut output = CpsOptimizationOutput {
        module: module.clone(),
        profile: CpsOptimizationProfile::measure(module),
    };

    rewrite_forwarding_continuation_calls(&mut output);
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

fn maybe_trace_profile(profile: &CpsOptimizationProfile) {
    if std::env::var_os("YULANG_CPS_OPT_TRACE").is_none() {
        return;
    }
    eprintln!(
        "[CPS-OPT] functions={} roots={} continuations={} handlers={} statements={} passes={} forwarded_continuation_calls={} changed={}",
        profile.functions,
        profile.roots,
        profile.continuations,
        profile.handlers,
        profile.statements,
        profile.passes_run,
        profile.forwarded_continuation_calls,
        profile.changed
    );
}

fn forwarding_continuations(
    function: &crate::cps_repr_abi::CpsReprAbiFunction,
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
        assert_eq!(optimized.profile.passes_run, 1);
        assert_eq!(optimized.profile.forwarded_continuation_calls, 0);
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

        assert_eq!(
            entry.terminator,
            CpsTerminator::Continue {
                target: CpsContinuationId(2),
                args: vec![CpsValueId(0)],
            }
        );
        assert_eq!(optimized.profile.forwarded_continuation_calls, 1);
        assert!(optimized.profile.changed);
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
