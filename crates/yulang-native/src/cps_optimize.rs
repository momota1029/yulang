//! Optimization entrypoint for backend-facing CPS representation ABI.
//!
//! This module is intentionally placed between CPS repr ABI lowering and
//! Cranelift codegen.  The first implementation preserves the module exactly,
//! but it gives JIT and object generation one shared optimization boundary for
//! later continuation, thunk, handler, and delimiter passes.

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
    pub changed: bool,
}

pub fn optimize_cps_repr_abi_module(module: &CpsReprAbiModule) -> CpsOptimizationOutput {
    let mut output = CpsOptimizationOutput {
        module: module.clone(),
        profile: CpsOptimizationProfile::measure(module),
    };

    run_identity_boundary_pass(&mut output);
    maybe_trace_profile(&output.profile);
    output
}

fn run_identity_boundary_pass(output: &mut CpsOptimizationOutput) {
    output.profile.passes_run += 1;
}

fn maybe_trace_profile(profile: &CpsOptimizationProfile) {
    if std::env::var_os("YULANG_CPS_OPT_TRACE").is_none() {
        return;
    }
    eprintln!(
        "[CPS-OPT] functions={} roots={} continuations={} handlers={} statements={} passes={} changed={}",
        profile.functions,
        profile.roots,
        profile.continuations,
        profile.handlers,
        profile.statements,
        profile.passes_run,
        profile.changed
    );
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
    fn optimization_boundary_preserves_abi_module() {
        let abi = sample_abi_module();
        let optimized = optimize_cps_repr_abi_module(&abi);

        assert_eq!(optimized.module, abi);
        assert_eq!(optimized.profile.roots, 1);
        assert_eq!(optimized.profile.continuations, 1);
        assert_eq!(optimized.profile.statements, 1);
        assert_eq!(optimized.profile.passes_run, 1);
        assert!(!optimized.profile.changed);
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
