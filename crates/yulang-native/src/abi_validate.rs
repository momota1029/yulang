use std::collections::HashSet;
use std::fmt;

use crate::abi::{NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
use crate::control_ir::{BlockId, NativeTerminator, ValueId};

pub type NativeAbiValidateResult<T> = Result<T, NativeAbiValidateError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeAbiValidateError {
    DuplicateFunction {
        name: String,
    },
    DuplicateBlock {
        function: String,
        block: BlockId,
    },
    DuplicateBlockParam {
        function: String,
        block: BlockId,
        value: ValueId,
    },
    DuplicateValue {
        function: String,
        block: BlockId,
        value: ValueId,
    },
    UndefinedValue {
        function: String,
        block: BlockId,
        value: ValueId,
    },
    MissingBlock {
        function: String,
        block: BlockId,
    },
    EnvSlotOutOfRange {
        function: String,
        block: BlockId,
        slot: usize,
        slots: usize,
    },
}

impl fmt::Display for NativeAbiValidateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeAbiValidateError::DuplicateFunction { name } => {
                write!(f, "duplicate native ABI function `{name}`")
            }
            NativeAbiValidateError::DuplicateBlock { function, block } => {
                write!(f, "duplicate native ABI block {block:?} in `{function}`")
            }
            NativeAbiValidateError::DuplicateBlockParam {
                function,
                block,
                value,
            } => write!(
                f,
                "duplicate native ABI block param {value:?} in block {block:?} of `{function}`"
            ),
            NativeAbiValidateError::DuplicateValue {
                function,
                block,
                value,
            } => write!(
                f,
                "duplicate native ABI value {value:?} in block {block:?} of `{function}`"
            ),
            NativeAbiValidateError::UndefinedValue {
                function,
                block,
                value,
            } => write!(
                f,
                "undefined native ABI value {value:?} in block {block:?} of `{function}`"
            ),
            NativeAbiValidateError::MissingBlock { function, block } => {
                write!(f, "missing native ABI block {block:?} in `{function}`")
            }
            NativeAbiValidateError::EnvSlotOutOfRange {
                function,
                block,
                slot,
                slots,
            } => write!(
                f,
                "native ABI env slot {slot} is out of range for {slots} slots in block {block:?} of `{function}`"
            ),
        }
    }
}

impl std::error::Error for NativeAbiValidateError {}

pub fn validate_abi_module(module: &NativeAbiModule) -> NativeAbiValidateResult<()> {
    let mut functions = HashSet::new();
    for function in module.functions.iter().chain(&module.roots) {
        if !functions.insert(function.name.clone()) {
            return Err(NativeAbiValidateError::DuplicateFunction {
                name: function.name.clone(),
            });
        }
        validate_function(function)?;
    }
    Ok(())
}

fn validate_function(function: &NativeAbiFunction) -> NativeAbiValidateResult<()> {
    let mut blocks = HashSet::new();
    for block in &function.blocks {
        if !blocks.insert(block.id) {
            return Err(NativeAbiValidateError::DuplicateBlock {
                function: function.name.clone(),
                block: block.id,
            });
        }
    }
    let entry = function.blocks.first().map(|block| block.id);
    for block in &function.blocks {
        validate_block(function, block, &blocks, Some(block.id) == entry)?;
    }
    Ok(())
}

fn validate_block(
    function: &NativeAbiFunction,
    block: &NativeAbiBlock,
    blocks: &HashSet<BlockId>,
    is_entry: bool,
) -> NativeAbiValidateResult<()> {
    let mut values = HashSet::new();
    for param in &function.params {
        if !values.insert(*param) {
            return Err(NativeAbiValidateError::DuplicateBlockParam {
                function: function.name.clone(),
                block: block.id,
                value: *param,
            });
        }
    }
    let block_params = if is_entry && block.params.starts_with(&function.params) {
        &block.params[function.params.len()..]
    } else {
        block.params.as_slice()
    };
    for param in block_params {
        if !values.insert(*param) {
            return Err(NativeAbiValidateError::DuplicateBlockParam {
                function: function.name.clone(),
                block: block.id,
                value: *param,
            });
        }
    }
    for stmt in &block.stmts {
        validate_stmt_uses(function, block, stmt, &values)?;
        let dest = stmt_dest(stmt);
        if !values.insert(dest) {
            return Err(NativeAbiValidateError::DuplicateValue {
                function: function.name.clone(),
                block: block.id,
                value: dest,
            });
        }
    }
    validate_terminator(function, block, blocks, &values)
}

fn validate_stmt_uses(
    function: &NativeAbiFunction,
    block: &NativeAbiBlock,
    stmt: &NativeAbiStmt,
    values: &HashSet<ValueId>,
) -> NativeAbiValidateResult<()> {
    match stmt {
        NativeAbiStmt::Literal { .. } => Ok(()),
        NativeAbiStmt::Primitive { args, .. }
        | NativeAbiStmt::DirectCall { args, .. }
        | NativeAbiStmt::Tuple { items: args, .. }
        | NativeAbiStmt::IndirectClosureCall { args, .. } => {
            for arg in args {
                require_value(function, block, values, *arg)?;
            }
            if let NativeAbiStmt::IndirectClosureCall { callee, .. } = stmt {
                require_value(function, block, values, *callee)?;
            }
            Ok(())
        }
        NativeAbiStmt::Record { base, fields, .. } => {
            if let Some(base) = base {
                require_value(function, block, values, *base)?;
            }
            for field in fields {
                require_value(function, block, values, field.value)?;
            }
            Ok(())
        }
        NativeAbiStmt::Variant { value, .. } => {
            if let Some(value) = value {
                require_value(function, block, values, *value)?;
            }
            Ok(())
        }
        NativeAbiStmt::Select { base, .. } => require_value(function, block, values, *base),
        NativeAbiStmt::LoadEnv { slot, .. } => {
            if *slot >= function.environment_slots {
                return Err(NativeAbiValidateError::EnvSlotOutOfRange {
                    function: function.name.clone(),
                    block: block.id,
                    slot: *slot,
                    slots: function.environment_slots,
                });
            }
            Ok(())
        }
        NativeAbiStmt::AllocateClosure { environment, .. } => {
            for value in environment {
                require_value(function, block, values, *value)?;
            }
            Ok(())
        }
    }
}

fn validate_terminator(
    function: &NativeAbiFunction,
    block: &NativeAbiBlock,
    blocks: &HashSet<BlockId>,
    values: &HashSet<ValueId>,
) -> NativeAbiValidateResult<()> {
    match &block.terminator {
        NativeTerminator::Return(value) => require_value(function, block, values, *value),
        NativeTerminator::Jump { target, args } => {
            require_block(function, *target, blocks)?;
            for arg in args {
                require_value(function, block, values, *arg)?;
            }
            Ok(())
        }
        NativeTerminator::Branch {
            cond,
            then_block,
            else_block,
        } => {
            require_value(function, block, values, *cond)?;
            require_block(function, *then_block, blocks)?;
            require_block(function, *else_block, blocks)
        }
    }
}

fn stmt_dest(stmt: &NativeAbiStmt) -> ValueId {
    match stmt {
        NativeAbiStmt::Literal { dest, .. }
        | NativeAbiStmt::Primitive { dest, .. }
        | NativeAbiStmt::DirectCall { dest, .. }
        | NativeAbiStmt::Tuple { dest, .. }
        | NativeAbiStmt::Record { dest, .. }
        | NativeAbiStmt::Variant { dest, .. }
        | NativeAbiStmt::Select { dest, .. }
        | NativeAbiStmt::LoadEnv { dest, .. }
        | NativeAbiStmt::AllocateClosure { dest, .. }
        | NativeAbiStmt::IndirectClosureCall { dest, .. } => *dest,
    }
}

fn require_value(
    function: &NativeAbiFunction,
    block: &NativeAbiBlock,
    values: &HashSet<ValueId>,
    value: ValueId,
) -> NativeAbiValidateResult<()> {
    if values.contains(&value) {
        Ok(())
    } else {
        Err(NativeAbiValidateError::UndefinedValue {
            function: function.name.clone(),
            block: block.id,
            value,
        })
    }
}

fn require_block(
    function: &NativeAbiFunction,
    block: BlockId,
    blocks: &HashSet<BlockId>,
) -> NativeAbiValidateResult<()> {
    if blocks.contains(&block) {
        Ok(())
    } else {
        Err(NativeAbiValidateError::MissingBlock {
            function: function.name.clone(),
            block,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::abi::{NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
    use crate::control_ir::{BlockId, NativeLiteral, NativeTerminator, ValueId};

    use super::*;

    #[test]
    fn accepts_valid_abi_module() {
        let module = NativeAbiModule {
            functions: Vec::new(),
            roots: vec![NativeAbiFunction {
                name: "root".to_string(),
                params: Vec::new(),
                environment_slots: 1,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![
                        NativeAbiStmt::LoadEnv {
                            dest: ValueId(0),
                            slot: 0,
                        },
                        NativeAbiStmt::Literal {
                            dest: ValueId(1),
                            literal: NativeLiteral::Int("1".to_string()),
                        },
                        NativeAbiStmt::AllocateClosure {
                            dest: ValueId(2),
                            target: "root#lambda0".to_string(),
                            environment: vec![ValueId(0), ValueId(1)],
                        },
                    ],
                    terminator: NativeTerminator::Return(ValueId(2)),
                }],
            }],
        };

        validate_abi_module(&module).expect("valid abi");
    }

    #[test]
    fn rejects_out_of_range_env_slot() {
        let module = NativeAbiModule {
            functions: Vec::new(),
            roots: vec![NativeAbiFunction {
                name: "root".to_string(),
                params: Vec::new(),
                environment_slots: 0,
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
        };

        assert_eq!(
            validate_abi_module(&module),
            Err(NativeAbiValidateError::EnvSlotOutOfRange {
                function: "root".to_string(),
                block: BlockId(0),
                slot: 0,
                slots: 0,
            })
        );
    }

    #[test]
    fn rejects_undefined_call_argument() {
        let module = NativeAbiModule {
            functions: Vec::new(),
            roots: vec![NativeAbiFunction {
                name: "root".to_string(),
                params: Vec::new(),
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![NativeAbiStmt::DirectCall {
                        dest: ValueId(1),
                        target: "f".to_string(),
                        args: vec![ValueId(0)],
                    }],
                    terminator: NativeTerminator::Return(ValueId(1)),
                }],
            }],
        };

        assert_eq!(
            validate_abi_module(&module),
            Err(NativeAbiValidateError::UndefinedValue {
                function: "root".to_string(),
                block: BlockId(0),
                value: ValueId(0),
            })
        );
    }
}
