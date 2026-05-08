use crate::cps_env::{CpsEnvironmentSlot, layout_cps_environments};
use crate::cps_ir::{CpsContinuationId, CpsModule, CpsShotKind, CpsValueId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsClosureModule {
    pub functions: Vec<CpsClosureFunction>,
    pub roots: Vec<CpsClosureFunction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsClosureFunction {
    pub name: String,
    pub continuations: Vec<CpsClosureContinuation>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsClosureContinuation {
    pub code: CpsContinuationId,
    pub params: Vec<CpsValueId>,
    pub environment: Vec<CpsEnvironmentSlot>,
    pub shot_kind: CpsShotKind,
}

pub fn closure_convert_cps_module(module: &CpsModule) -> CpsClosureModule {
    let layout = layout_cps_environments(module);
    CpsClosureModule {
        functions: module
            .functions
            .iter()
            .zip(layout.functions)
            .map(|(function, layout)| closure_convert_function(function, layout.continuations))
            .collect(),
        roots: module
            .roots
            .iter()
            .zip(layout.roots)
            .map(|(function, layout)| closure_convert_function(function, layout.continuations))
            .collect(),
    }
}

fn closure_convert_function(
    function: &crate::cps_ir::CpsFunction,
    layouts: Vec<crate::cps_env::CpsContinuationEnvironmentLayout>,
) -> CpsClosureFunction {
    CpsClosureFunction {
        name: function.name.clone(),
        continuations: function
            .continuations
            .iter()
            .zip(layouts)
            .map(|(continuation, layout)| CpsClosureContinuation {
                code: continuation.id,
                params: continuation.params.clone(),
                environment: layout.slots,
                shot_kind: continuation.shot_kind,
            })
            .collect(),
    }
}

#[cfg(test)]
mod tests {
    use crate::cps_ir::{
        CpsContinuation, CpsContinuationId, CpsFunction, CpsModule, CpsShotKind, CpsTerminator,
        CpsValueId,
    };

    use super::*;

    #[test]
    fn closure_conversion_preserves_code_params_and_environment_slots() {
        let module = CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                continuations: vec![CpsContinuation {
                    id: CpsContinuationId(7),
                    params: vec![CpsValueId(1)],
                    captures: vec![CpsValueId(4), CpsValueId(2)],
                    shot_kind: CpsShotKind::MultiShot,
                    stmts: Vec::new(),
                    terminator: CpsTerminator::Return(CpsValueId(1)),
                }],
                handlers: Vec::new(),
            }],
        };

        let converted = closure_convert_cps_module(&module);

        assert_eq!(
            converted.roots[0].continuations,
            vec![CpsClosureContinuation {
                code: CpsContinuationId(7),
                params: vec![CpsValueId(1)],
                environment: vec![
                    CpsEnvironmentSlot {
                        index: 0,
                        value: CpsValueId(4),
                    },
                    CpsEnvironmentSlot {
                        index: 1,
                        value: CpsValueId(2),
                    },
                ],
                shot_kind: CpsShotKind::MultiShot,
            }]
        );
    }
}
