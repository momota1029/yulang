//! Backend-neutral ABI lowering for native closure IR.
//!
//! This is the boundary Cranelift should consume later.  It keeps closure
//! allocation, environment loads, direct calls, and indirect closure calls
//! explicit without committing to a machine-level value representation yet.

use yulang_typed_ir as typed_ir;

use crate::closure::{
    NativeClosureBlock, NativeClosureFunction, NativeClosureModule, NativeClosureStmt,
};
use crate::control_ir::{
    BlockId, NativeLiteral, NativeRecordField, NativeStmt, NativeTerminator, ValueId,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeAbiModule {
    pub functions: Vec<NativeAbiFunction>,
    pub roots: Vec<NativeAbiFunction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeAbiFunction {
    pub name: String,
    pub params: Vec<ValueId>,
    pub environment_slots: usize,
    pub blocks: Vec<NativeAbiBlock>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeAbiBlock {
    pub id: BlockId,
    pub params: Vec<ValueId>,
    pub stmts: Vec<NativeAbiStmt>,
    pub terminator: NativeTerminator,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeAbiStmt {
    Literal {
        dest: ValueId,
        literal: NativeLiteral,
    },
    Primitive {
        dest: ValueId,
        op: typed_ir::PrimitiveOp,
        args: Vec<ValueId>,
    },
    DirectCall {
        dest: ValueId,
        target: String,
        args: Vec<ValueId>,
    },
    Tuple {
        dest: ValueId,
        items: Vec<ValueId>,
    },
    Record {
        dest: ValueId,
        fields: Vec<NativeRecordField>,
    },
    Variant {
        dest: ValueId,
        tag: typed_ir::Name,
        value: Option<ValueId>,
    },
    Select {
        dest: ValueId,
        base: ValueId,
        field: typed_ir::Name,
    },
    LoadEnv {
        dest: ValueId,
        slot: usize,
    },
    AllocateClosure {
        dest: ValueId,
        target: String,
        environment: Vec<ValueId>,
    },
    IndirectClosureCall {
        dest: ValueId,
        callee: ValueId,
        args: Vec<ValueId>,
    },
}

pub fn lower_closure_module_to_abi(module: &NativeClosureModule) -> NativeAbiModule {
    NativeAbiModule {
        functions: module.functions.iter().map(lower_function).collect(),
        roots: module.roots.iter().map(lower_function).collect(),
    }
}

fn lower_function(function: &NativeClosureFunction) -> NativeAbiFunction {
    NativeAbiFunction {
        name: function.name.clone(),
        params: function.abi.params.clone(),
        environment_slots: function.abi.environment.slots,
        blocks: function.blocks.iter().map(lower_block).collect(),
    }
}

fn lower_block(block: &NativeClosureBlock) -> NativeAbiBlock {
    NativeAbiBlock {
        id: block.id,
        params: block.params.clone(),
        stmts: block.stmts.iter().map(lower_stmt).collect(),
        terminator: block.terminator.clone(),
    }
}

fn lower_stmt(stmt: &NativeClosureStmt) -> NativeAbiStmt {
    match stmt {
        NativeClosureStmt::LoadEnv { dest, slot } => NativeAbiStmt::LoadEnv {
            dest: *dest,
            slot: *slot,
        },
        NativeClosureStmt::MakeClosure {
            dest,
            target,
            environment,
        } => NativeAbiStmt::AllocateClosure {
            dest: *dest,
            target: target.clone(),
            environment: environment.iter().map(|capture| capture.value).collect(),
        },
        NativeClosureStmt::ClosureCall { dest, callee, args } => {
            NativeAbiStmt::IndirectClosureCall {
                dest: *dest,
                callee: *callee,
                args: args.clone(),
            }
        }
        NativeClosureStmt::Native(stmt) => lower_native_stmt(stmt),
    }
}

fn lower_native_stmt(stmt: &NativeStmt) -> NativeAbiStmt {
    match stmt {
        NativeStmt::Literal { dest, literal } => NativeAbiStmt::Literal {
            dest: *dest,
            literal: literal.clone(),
        },
        NativeStmt::Primitive { dest, op, args } => NativeAbiStmt::Primitive {
            dest: *dest,
            op: *op,
            args: args.clone(),
        },
        NativeStmt::DirectCall { dest, target, args } => NativeAbiStmt::DirectCall {
            dest: *dest,
            target: target.clone(),
            args: args.clone(),
        },
        NativeStmt::Tuple { dest, items } => NativeAbiStmt::Tuple {
            dest: *dest,
            items: items.clone(),
        },
        NativeStmt::Record { dest, fields } => NativeAbiStmt::Record {
            dest: *dest,
            fields: fields.clone(),
        },
        NativeStmt::Variant { dest, tag, value } => NativeAbiStmt::Variant {
            dest: *dest,
            tag: tag.clone(),
            value: *value,
        },
        NativeStmt::Select { dest, base, field } => NativeAbiStmt::Select {
            dest: *dest,
            base: *base,
            field: field.clone(),
        },
        NativeStmt::MakeClosure {
            dest,
            target,
            captures,
        } => NativeAbiStmt::AllocateClosure {
            dest: *dest,
            target: target.clone(),
            environment: captures.clone(),
        },
        NativeStmt::ClosureCall { dest, callee, args } => NativeAbiStmt::IndirectClosureCall {
            dest: *dest,
            callee: *callee,
            args: args.clone(),
        },
    }
}

#[cfg(test)]
mod tests {
    use crate::closure::{NativeClosureCapture, closure_convert_module};
    use crate::control_ir::{NativeBlock, NativeFunction, NativeModule, NativeTerminator};

    use super::*;

    #[test]
    fn lowers_closure_function_abi_shape() {
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
            functions: vec![function],
            roots: Vec::new(),
        };
        let closure_module = closure_convert_module(&module);

        let abi = lower_closure_module_to_abi(&closure_module);

        assert_eq!(
            abi.functions,
            vec![NativeAbiFunction {
                name: "root#lambda0".to_string(),
                params: vec![ValueId(1)],
                environment_slots: 1,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: vec![ValueId(1)],
                    stmts: vec![NativeAbiStmt::LoadEnv {
                        dest: ValueId(0),
                        slot: 0,
                    }],
                    terminator: NativeTerminator::Return(ValueId(1)),
                }],
            }]
        );
    }

    #[test]
    fn lowers_closure_allocation_and_indirect_call() {
        let closure_module = NativeClosureModule {
            functions: Vec::new(),
            roots: vec![crate::closure::NativeClosureFunction {
                name: "root".to_string(),
                params: Vec::new(),
                abi: crate::closure::NativeClosureAbi {
                    code: crate::closure::NativeClosureCodeRef {
                        function: "root".to_string(),
                    },
                    environment: crate::closure::NativeClosureEnvRef { slots: 0 },
                    params: Vec::new(),
                },
                environment: crate::closure::NativeClosureEnvironment { slots: Vec::new() },
                blocks: vec![crate::closure::NativeClosureBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![
                        NativeClosureStmt::MakeClosure {
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
                        },
                        NativeClosureStmt::ClosureCall {
                            dest: ValueId(3),
                            callee: ValueId(2),
                            args: vec![ValueId(4)],
                        },
                    ],
                    terminator: NativeTerminator::Return(ValueId(3)),
                }],
            }],
        };

        let abi = lower_closure_module_to_abi(&closure_module);

        assert_eq!(
            abi.roots[0].blocks[0].stmts,
            vec![
                NativeAbiStmt::AllocateClosure {
                    dest: ValueId(2),
                    target: "root#lambda0".to_string(),
                    environment: vec![ValueId(0), ValueId(1)],
                },
                NativeAbiStmt::IndirectClosureCall {
                    dest: ValueId(3),
                    callee: ValueId(2),
                    args: vec![ValueId(4)],
                },
            ]
        );
    }
}
