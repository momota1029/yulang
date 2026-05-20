use crate::cps_ir::{CpsContinuationId, CpsModule, CpsValueId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsEnvironmentLayout {
    pub functions: Vec<CpsFunctionEnvironmentLayout>,
    pub roots: Vec<CpsFunctionEnvironmentLayout>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsFunctionEnvironmentLayout {
    pub name: String,
    pub continuations: Vec<CpsContinuationEnvironmentLayout>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsContinuationEnvironmentLayout {
    pub continuation: CpsContinuationId,
    pub slots: Vec<CpsEnvironmentSlot>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CpsEnvironmentSlot {
    pub index: usize,
    pub value: CpsValueId,
}

pub fn layout_cps_environments(module: &CpsModule) -> CpsEnvironmentLayout {
    CpsEnvironmentLayout {
        functions: module
            .functions
            .iter()
            .map(layout_function_environments)
            .collect(),
        roots: module
            .roots
            .iter()
            .map(layout_function_environments)
            .collect(),
    }
}

fn layout_function_environments(
    function: &crate::cps_ir::CpsFunction,
) -> CpsFunctionEnvironmentLayout {
    CpsFunctionEnvironmentLayout {
        name: function.name.clone(),
        continuations: function
            .continuations
            .iter()
            .map(|continuation| CpsContinuationEnvironmentLayout {
                continuation: continuation.id,
                slots: continuation
                    .captures
                    .iter()
                    .copied()
                    .enumerate()
                    .map(|(index, value)| CpsEnvironmentSlot { index, value })
                    .collect(),
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
    fn assigns_stable_slots_from_continuation_capture_order() {
        let module = CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                continuations: vec![CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: vec![CpsValueId(4), CpsValueId(2)],
                    shot_kind: CpsShotKind::MultiShot,
                    stmts: Vec::new(),
                    terminator: CpsTerminator::Return(CpsValueId(4)),
                }],
                handlers: Vec::new(),
            }],
        };

        assert_eq!(
            layout_cps_environments(&module).roots[0].continuations[0].slots,
            vec![
                CpsEnvironmentSlot {
                    index: 0,
                    value: CpsValueId(4),
                },
                CpsEnvironmentSlot {
                    index: 1,
                    value: CpsValueId(2),
                },
            ]
        );
    }
}
