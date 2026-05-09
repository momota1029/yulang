use std::collections::HashSet;

use crate::control_ir::{
    BlockId, NativeFunction, NativeModule, NativeStmt, NativeTerminator, ValueId,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeClosureModule {
    pub functions: Vec<NativeClosureFunction>,
    pub roots: Vec<NativeClosureFunction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeClosureFunction {
    pub name: String,
    pub params: Vec<ValueId>,
    pub environment: NativeClosureEnvironment,
    pub abi: NativeClosureAbi,
    pub blocks: Vec<NativeClosureBlock>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeClosureBlock {
    pub id: BlockId,
    pub params: Vec<ValueId>,
    pub stmts: Vec<NativeClosureStmt>,
    pub terminator: NativeTerminator,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeClosureStmt {
    LoadEnv {
        dest: ValueId,
        slot: usize,
    },
    MakeClosure {
        dest: ValueId,
        target: String,
        environment: Vec<NativeClosureCapture>,
    },
    ClosureCall {
        dest: ValueId,
        callee: ValueId,
        args: Vec<ValueId>,
    },
    Native(NativeStmt),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeClosureEnvironment {
    pub slots: Vec<NativeClosureSlot>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeClosureAbi {
    pub code: NativeClosureCodeRef,
    pub environment: NativeClosureEnvRef,
    pub params: Vec<ValueId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeClosureCodeRef {
    pub function: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeClosureEnvRef {
    pub slots: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeClosureSlot {
    pub index: usize,
    pub value: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeClosureCapture {
    pub slot: usize,
    pub value: ValueId,
}

pub fn closure_convert_module(module: &NativeModule) -> NativeClosureModule {
    NativeClosureModule {
        functions: module
            .functions
            .iter()
            .map(closure_convert_function)
            .collect(),
        roots: module.roots.iter().map(closure_convert_function).collect(),
    }
}

fn closure_convert_function(function: &NativeFunction) -> NativeClosureFunction {
    let environment_slots = closure_environment_slots(function);
    let capture_values = function.captures.iter().copied().collect::<HashSet<_>>();
    let params = function
        .params
        .iter()
        .copied()
        .filter(|param| !capture_values.contains(param))
        .collect();
    let blocks = closure_convert_blocks(function, &environment_slots, &capture_values);
    NativeClosureFunction {
        name: function.name.clone(),
        params,
        abi: NativeClosureAbi {
            code: NativeClosureCodeRef {
                function: function.name.clone(),
            },
            environment: NativeClosureEnvRef {
                slots: environment_slots.len(),
            },
            params: function
                .params
                .iter()
                .copied()
                .filter(|param| !capture_values.contains(param))
                .collect(),
        },
        environment: NativeClosureEnvironment {
            slots: environment_slots,
        },
        blocks,
    }
}

fn closure_environment_slots(function: &NativeFunction) -> Vec<NativeClosureSlot> {
    function
        .captures
        .iter()
        .copied()
        .enumerate()
        .map(|(index, value)| NativeClosureSlot { index, value })
        .collect()
}

fn closure_convert_blocks(
    function: &NativeFunction,
    environment_slots: &[NativeClosureSlot],
    capture_values: &HashSet<ValueId>,
) -> Vec<NativeClosureBlock> {
    let entry = function.blocks.first().map(|block| block.id);
    function
        .blocks
        .iter()
        .map(|block| {
            let mut stmts = Vec::new();
            if Some(block.id) == entry {
                stmts.extend(
                    environment_slots
                        .iter()
                        .map(|slot| NativeClosureStmt::LoadEnv {
                            dest: slot.value,
                            slot: slot.index,
                        }),
                );
            }
            stmts.extend(block.stmts.iter().cloned().map(closure_convert_stmt));
            NativeClosureBlock {
                id: block.id,
                params: block
                    .params
                    .iter()
                    .copied()
                    .filter(|param| !capture_values.contains(param))
                    .collect(),
                stmts,
                terminator: block.terminator.clone(),
            }
        })
        .collect()
}

fn closure_convert_stmt(stmt: NativeStmt) -> NativeClosureStmt {
    match stmt {
        NativeStmt::MakeClosure {
            dest,
            target,
            captures,
        } => NativeClosureStmt::MakeClosure {
            dest,
            target,
            environment: captures
                .into_iter()
                .enumerate()
                .map(|(slot, value)| NativeClosureCapture { slot, value })
                .collect(),
        },
        NativeStmt::ClosureCall { dest, callee, args } => {
            NativeClosureStmt::ClosureCall { dest, callee, args }
        }
        stmt => NativeClosureStmt::Native(stmt),
    }
}

#[cfg(test)]
mod tests {
    use crate::control_ir::{
        BlockId, NativeBlock, NativeFunction, NativeLiteral, NativeModule, NativeStmt,
        NativeTerminator, ValueId,
    };

    use super::*;

    #[test]
    fn converts_first_order_function_to_empty_environment_closure() {
        let function = NativeFunction {
            name: "root".to_string(),
            captures: Vec::new(),
            params: vec![ValueId(0)],
            blocks: vec![NativeBlock {
                id: BlockId(0),
                params: vec![ValueId(0)],
                stmts: vec![NativeStmt::Literal {
                    dest: ValueId(1),
                    literal: NativeLiteral::Int("1".to_string()),
                }],
                terminator: NativeTerminator::Return(ValueId(1)),
            }],
        };
        let module = NativeModule {
            functions: Vec::new(),
            roots: vec![function.clone()],
        };

        let converted = closure_convert_module(&module);

        assert_eq!(
            converted.roots,
            vec![NativeClosureFunction {
                name: "root".to_string(),
                params: vec![ValueId(0)],
                abi: NativeClosureAbi {
                    code: NativeClosureCodeRef {
                        function: "root".to_string(),
                    },
                    environment: NativeClosureEnvRef { slots: 0 },
                    params: vec![ValueId(0)],
                },
                environment: NativeClosureEnvironment { slots: Vec::new() },
                blocks: function
                    .blocks
                    .into_iter()
                    .map(|block| NativeClosureBlock {
                        id: block.id,
                        params: block.params,
                        stmts: block.stmts.into_iter().map(closure_convert_stmt).collect(),
                        terminator: block.terminator,
                    })
                    .collect(),
            }]
        );
    }

    #[test]
    fn separates_capture_params_into_environment_slots() {
        let function = NativeFunction {
            name: "root#lambda0".to_string(),
            captures: vec![ValueId(0)],
            params: vec![ValueId(0), ValueId(1)],
            blocks: vec![NativeBlock {
                id: BlockId(0),
                params: vec![ValueId(0), ValueId(1)],
                stmts: Vec::new(),
                terminator: NativeTerminator::Return(ValueId(1)),
            }],
        };
        let module = NativeModule {
            functions: vec![function.clone()],
            roots: Vec::new(),
        };

        let converted = closure_convert_module(&module);

        assert_eq!(converted.functions[0].params, vec![ValueId(1)]);
        assert_eq!(
            converted.functions[0].abi,
            NativeClosureAbi {
                code: NativeClosureCodeRef {
                    function: "root#lambda0".to_string(),
                },
                environment: NativeClosureEnvRef { slots: 1 },
                params: vec![ValueId(1)],
            }
        );
        assert_eq!(converted.functions[0].blocks[0].params, vec![ValueId(1)]);
        assert_eq!(
            converted.functions[0].environment,
            NativeClosureEnvironment {
                slots: vec![NativeClosureSlot {
                    index: 0,
                    value: ValueId(0),
                }]
            }
        );
        assert_eq!(
            converted.functions[0].blocks[0].stmts,
            vec![NativeClosureStmt::LoadEnv {
                dest: ValueId(0),
                slot: 0,
            }]
        );
        assert_eq!(
            converted.functions[0].blocks[0].terminator,
            NativeTerminator::Return(ValueId(1))
        );
    }

    #[test]
    fn converts_make_closure_to_environment_allocation() {
        let function = NativeFunction {
            name: "root".to_string(),
            captures: Vec::new(),
            params: Vec::new(),
            blocks: vec![NativeBlock {
                id: BlockId(0),
                params: Vec::new(),
                stmts: vec![NativeStmt::MakeClosure {
                    dest: ValueId(2),
                    target: "root#lambda0".to_string(),
                    captures: vec![ValueId(0), ValueId(1)],
                }],
                terminator: NativeTerminator::Return(ValueId(2)),
            }],
        };
        let module = NativeModule {
            functions: Vec::new(),
            roots: vec![function],
        };

        let converted = closure_convert_module(&module);

        assert_eq!(
            converted.roots[0].blocks[0].stmts,
            vec![NativeClosureStmt::MakeClosure {
                dest: ValueId(2),
                target: "root#lambda0".to_string(),
                environment: vec![
                    NativeClosureCapture {
                        slot: 0,
                        value: ValueId(0),
                    },
                    NativeClosureCapture {
                        slot: 1,
                        value: ValueId(1),
                    },
                ],
            }]
        );
    }
}
