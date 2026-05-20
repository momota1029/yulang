use std::fmt;

use yulang_typed_ir as typed_ir;

use crate::abi::{NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
use crate::control_ir::NativeLiteral;

pub type NativeAbiSubsetResult<T> = Result<T, NativeAbiSubsetError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeAbiSubsetError {
    UnsupportedLiteral {
        function: String,
        literal: NativeLiteral,
    },
    UnsupportedPrimitive {
        function: String,
        op: typed_ir::PrimitiveOp,
    },
}

impl fmt::Display for NativeAbiSubsetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeAbiSubsetError::UnsupportedLiteral { function, literal } => write!(
                f,
                "native Cranelift prototype does not support literal {literal:?} in `{function}`"
            ),
            NativeAbiSubsetError::UnsupportedPrimitive { function, op } => write!(
                f,
                "native Cranelift prototype does not support primitive {op:?} in `{function}`"
            ),
        }
    }
}

impl std::error::Error for NativeAbiSubsetError {}

pub fn validate_cranelift_prototype_subset(module: &NativeAbiModule) -> NativeAbiSubsetResult<()> {
    for function in module.functions.iter().chain(&module.roots) {
        validate_function(function)?;
    }
    Ok(())
}

fn validate_function(function: &NativeAbiFunction) -> NativeAbiSubsetResult<()> {
    for block in &function.blocks {
        validate_block(function, block)?;
    }
    Ok(())
}

fn validate_block(
    function: &NativeAbiFunction,
    block: &NativeAbiBlock,
) -> NativeAbiSubsetResult<()> {
    for stmt in &block.stmts {
        validate_stmt(function, stmt)?;
    }
    Ok(())
}

fn validate_stmt(function: &NativeAbiFunction, stmt: &NativeAbiStmt) -> NativeAbiSubsetResult<()> {
    match stmt {
        NativeAbiStmt::Literal { literal, .. } if supported_literal(literal) => Ok(()),
        NativeAbiStmt::Literal { literal, .. } => Err(NativeAbiSubsetError::UnsupportedLiteral {
            function: function.name.clone(),
            literal: literal.clone(),
        }),
        NativeAbiStmt::Primitive { op, .. } if supported_primitive(*op) => Ok(()),
        NativeAbiStmt::Primitive { op, .. } => Err(NativeAbiSubsetError::UnsupportedPrimitive {
            function: function.name.clone(),
            op: *op,
        }),
        NativeAbiStmt::DirectCall { .. } => Ok(()),
        NativeAbiStmt::Tuple { .. }
        | NativeAbiStmt::Record { .. }
        | NativeAbiStmt::RecordWithoutFields { .. }
        | NativeAbiStmt::Variant { .. }
        | NativeAbiStmt::Select { .. }
        | NativeAbiStmt::TupleGet { .. }
        | NativeAbiStmt::VariantTagEq { .. }
        | NativeAbiStmt::VariantPayload { .. }
        | NativeAbiStmt::ValueEq { .. }
        | NativeAbiStmt::BoolAnd { .. } => Ok(()),
        NativeAbiStmt::LoadEnv { .. }
        | NativeAbiStmt::AllocateClosure { .. }
        | NativeAbiStmt::IndirectClosureCall { .. } => Ok(()),
    }
}

fn supported_literal(literal: &NativeLiteral) -> bool {
    matches!(
        literal,
        NativeLiteral::Int(_)
            | NativeLiteral::Float(_)
            | NativeLiteral::Bool(_)
            | NativeLiteral::Unit
    )
}

fn supported_primitive(op: typed_ir::PrimitiveOp) -> bool {
    matches!(
        op,
        typed_ir::PrimitiveOp::BoolNot
            | typed_ir::PrimitiveOp::BoolEq
            | typed_ir::PrimitiveOp::IntAdd
            | typed_ir::PrimitiveOp::IntSub
            | typed_ir::PrimitiveOp::IntMul
            | typed_ir::PrimitiveOp::IntDiv
            | typed_ir::PrimitiveOp::IntMod
            | typed_ir::PrimitiveOp::IntEq
            | typed_ir::PrimitiveOp::IntLt
            | typed_ir::PrimitiveOp::IntLe
            | typed_ir::PrimitiveOp::IntGt
            | typed_ir::PrimitiveOp::IntGe
            | typed_ir::PrimitiveOp::FloatAdd
            | typed_ir::PrimitiveOp::FloatSub
            | typed_ir::PrimitiveOp::FloatMul
            | typed_ir::PrimitiveOp::FloatDiv
            | typed_ir::PrimitiveOp::FloatEq
            | typed_ir::PrimitiveOp::FloatLt
            | typed_ir::PrimitiveOp::FloatLe
            | typed_ir::PrimitiveOp::FloatGt
            | typed_ir::PrimitiveOp::FloatGe
    )
}

#[cfg(test)]
mod tests {
    use crate::abi::{NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
    use crate::control_ir::{BlockId, NativeTerminator, ValueId};

    use super::*;

    #[test]
    fn accepts_primitive_direct_call_subset() {
        let module = NativeAbiModule {
            functions: vec![NativeAbiFunction {
                name: "add".to_string(),
                params: vec![ValueId(0), ValueId(1)],
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![NativeAbiStmt::Primitive {
                        dest: ValueId(2),
                        op: typed_ir::PrimitiveOp::IntAdd,
                        args: vec![ValueId(0), ValueId(1)],
                    }],
                    terminator: NativeTerminator::Return(ValueId(2)),
                }],
            }],
            roots: vec![NativeAbiFunction {
                name: "root".to_string(),
                params: Vec::new(),
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![
                        NativeAbiStmt::Literal {
                            dest: ValueId(0),
                            literal: NativeLiteral::Int("1".to_string()),
                        },
                        NativeAbiStmt::Literal {
                            dest: ValueId(1),
                            literal: NativeLiteral::Int("2".to_string()),
                        },
                        NativeAbiStmt::DirectCall {
                            dest: ValueId(2),
                            target: "add".to_string(),
                            args: vec![ValueId(0), ValueId(1)],
                        },
                    ],
                    terminator: NativeTerminator::Return(ValueId(2)),
                }],
            }],
        };

        validate_cranelift_prototype_subset(&module).expect("subset");
    }

    #[test]
    fn rejects_string_literal_before_runtime_string_abi_exists() {
        let module = single_stmt_module(NativeAbiStmt::Literal {
            dest: ValueId(0),
            literal: NativeLiteral::String("hello".to_string()),
        });

        assert_eq!(
            validate_cranelift_prototype_subset(&module),
            Err(NativeAbiSubsetError::UnsupportedLiteral {
                function: "root".to_string(),
                literal: NativeLiteral::String("hello".to_string()),
            })
        );
    }

    #[test]
    fn accepts_closure_statements_for_hosted_closure_prototype() {
        let module = NativeAbiModule {
            functions: vec![NativeAbiFunction {
                name: "add_capture".to_string(),
                params: vec![ValueId(1)],
                environment_slots: 1,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![NativeAbiStmt::LoadEnv {
                        dest: ValueId(0),
                        slot: 0,
                    }],
                    terminator: NativeTerminator::Return(ValueId(0)),
                }],
            }],
            roots: vec![NativeAbiFunction {
                name: "root".to_string(),
                params: Vec::new(),
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![
                        NativeAbiStmt::Literal {
                            dest: ValueId(0),
                            literal: NativeLiteral::Int("1".to_string()),
                        },
                        NativeAbiStmt::AllocateClosure {
                            dest: ValueId(1),
                            target: "add_capture".to_string(),
                            environment: vec![ValueId(0)],
                        },
                        NativeAbiStmt::IndirectClosureCall {
                            dest: ValueId(2),
                            callee: ValueId(1),
                            args: vec![ValueId(0)],
                        },
                    ],
                    terminator: NativeTerminator::Return(ValueId(2)),
                }],
            }],
        };

        validate_cranelift_prototype_subset(&module).expect("subset");
    }

    #[test]
    fn rejects_list_primitive_before_heap_value_abi_exists() {
        let module = single_stmt_module(NativeAbiStmt::Primitive {
            dest: ValueId(0),
            op: typed_ir::PrimitiveOp::ListEmpty,
            args: Vec::new(),
        });

        assert_eq!(
            validate_cranelift_prototype_subset(&module),
            Err(NativeAbiSubsetError::UnsupportedPrimitive {
                function: "root".to_string(),
                op: typed_ir::PrimitiveOp::ListEmpty,
            })
        );
    }

    fn single_stmt_module(stmt: NativeAbiStmt) -> NativeAbiModule {
        NativeAbiModule {
            functions: Vec::new(),
            roots: vec![NativeAbiFunction {
                name: "root".to_string(),
                params: Vec::new(),
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![stmt],
                    terminator: NativeTerminator::Return(ValueId(0)),
                }],
            }],
        }
    }
}
