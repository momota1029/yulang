use std::collections::BTreeMap;
use std::fmt;

use yulang_runtime as runtime;
use yulang_typed_ir as typed_ir;

use crate::abi::{NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
use crate::control_ir::{BlockId, NativeLiteral, NativeTerminator, ValueId};
use crate::eval::NativeEvalError;

#[derive(Debug, Clone, PartialEq)]
pub enum NativeAbiEvalError {
    EmptyFunction {
        name: String,
    },
    MissingFunction {
        name: String,
    },
    MissingBlock {
        id: BlockId,
    },
    BlockArgumentMismatch {
        id: BlockId,
        expected: usize,
        actual: usize,
    },
    FunctionArgumentMismatch {
        function: String,
        expected: usize,
        actual: usize,
    },
    EnvArgumentMismatch {
        function: String,
        expected: usize,
        actual: usize,
    },
    MissingValue {
        id: ValueId,
    },
    MissingEnvSlot {
        function: String,
        slot: usize,
    },
    ExpectedPlainValue {
        id: ValueId,
    },
    ExpectedClosure {
        id: ValueId,
    },
    ExpectedRecord {
        value: runtime::VmValue,
    },
    NativeEval(NativeEvalError),
}

impl fmt::Display for NativeAbiEvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeAbiEvalError::EmptyFunction { name } => {
                write!(f, "native ABI function {name} has no entry block")
            }
            NativeAbiEvalError::MissingFunction { name } => {
                write!(f, "native ABI function {name} is missing")
            }
            NativeAbiEvalError::MissingBlock { id } => {
                write!(f, "native ABI block {id:?} is missing")
            }
            NativeAbiEvalError::BlockArgumentMismatch {
                id,
                expected,
                actual,
            } => write!(
                f,
                "native ABI block {id:?} expected {expected} arguments, got {actual}"
            ),
            NativeAbiEvalError::FunctionArgumentMismatch {
                function,
                expected,
                actual,
            } => write!(
                f,
                "native ABI function {function} expected {expected} arguments, got {actual}"
            ),
            NativeAbiEvalError::EnvArgumentMismatch {
                function,
                expected,
                actual,
            } => write!(
                f,
                "native ABI function {function} expected {expected} environment slots, got {actual}"
            ),
            NativeAbiEvalError::MissingValue { id } => {
                write!(f, "native ABI value {id:?} is missing")
            }
            NativeAbiEvalError::MissingEnvSlot { function, slot } => {
                write!(f, "native ABI env slot {slot} is missing in `{function}`")
            }
            NativeAbiEvalError::ExpectedPlainValue { id } => {
                write!(f, "native ABI expected plain value {id:?}")
            }
            NativeAbiEvalError::ExpectedClosure { id } => {
                write!(f, "native ABI expected closure value {id:?}")
            }
            NativeAbiEvalError::ExpectedRecord { value } => {
                write!(f, "native ABI expected record, got {value:?}")
            }
            NativeAbiEvalError::NativeEval(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for NativeAbiEvalError {}

impl From<NativeEvalError> for NativeAbiEvalError {
    fn from(error: NativeEvalError) -> Self {
        NativeAbiEvalError::NativeEval(error)
    }
}

pub type NativeAbiEvalResult<T> = Result<T, NativeAbiEvalError>;

pub fn eval_abi_module(module: &NativeAbiModule) -> NativeAbiEvalResult<Vec<runtime::VmValue>> {
    module
        .roots
        .iter()
        .map(|root| eval_function(module, root, Vec::new(), Vec::new()))
        .collect()
}

fn eval_function(
    module: &NativeAbiModule,
    function: &NativeAbiFunction,
    env: Vec<NativeAbiRuntimeValue>,
    args: Vec<NativeAbiRuntimeValue>,
) -> NativeAbiEvalResult<runtime::VmValue> {
    into_plain_value(
        ValueId(usize::MAX),
        eval_function_value(module, function, env, args)?,
    )
}

fn eval_function_value(
    module: &NativeAbiModule,
    function: &NativeAbiFunction,
    env: Vec<NativeAbiRuntimeValue>,
    args: Vec<NativeAbiRuntimeValue>,
) -> NativeAbiEvalResult<NativeAbiRuntimeValue> {
    if function.environment_slots != env.len() {
        return Err(NativeAbiEvalError::EnvArgumentMismatch {
            function: function.name.clone(),
            expected: function.environment_slots,
            actual: env.len(),
        });
    }
    if function.params.len() != args.len() {
        return Err(NativeAbiEvalError::FunctionArgumentMismatch {
            function: function.name.clone(),
            expected: function.params.len(),
            actual: args.len(),
        });
    }
    let entry = function
        .blocks
        .first()
        .ok_or_else(|| NativeAbiEvalError::EmptyFunction {
            name: function.name.clone(),
        })?;
    eval_blocks(module, function, &env, entry.id, args)
}

fn eval_blocks(
    module: &NativeAbiModule,
    function: &NativeAbiFunction,
    env: &[NativeAbiRuntimeValue],
    entry: BlockId,
    initial_args: Vec<NativeAbiRuntimeValue>,
) -> NativeAbiEvalResult<NativeAbiRuntimeValue> {
    let mut values = Vec::<Option<NativeAbiRuntimeValue>>::new();
    let mut current = entry;
    let mut args = initial_args;
    loop {
        let block = block_by_id(function, current)?;
        assign_block_args(&mut values, block, args)?;
        args = Vec::new();

        for stmt in &block.stmts {
            match stmt {
                NativeAbiStmt::Literal { dest, literal } => {
                    write_value(&mut values, *dest, plain(eval_literal(literal)));
                }
                NativeAbiStmt::Primitive { dest, op, args } => {
                    let args = args
                        .iter()
                        .map(|id| read_plain_value(&values, *id))
                        .collect::<NativeAbiEvalResult<Vec<_>>>()?;
                    write_value(
                        &mut values,
                        *dest,
                        plain(crate::eval::eval_primitive_for_abi(*op, &args)?),
                    );
                }
                NativeAbiStmt::DirectCall { dest, target, args } => {
                    let function = function_by_name(module, target)?;
                    let args = args
                        .iter()
                        .map(|id| read_value(&values, *id))
                        .collect::<NativeAbiEvalResult<Vec<_>>>()?;
                    write_value(
                        &mut values,
                        *dest,
                        eval_function_value(module, function, Vec::new(), args)?,
                    );
                }
                NativeAbiStmt::Tuple { dest, items } => {
                    let items = items
                        .iter()
                        .map(|id| read_plain_value(&values, *id))
                        .collect::<NativeAbiEvalResult<Vec<_>>>()?;
                    write_value(&mut values, *dest, plain(runtime::VmValue::Tuple(items)));
                }
                NativeAbiStmt::Record { dest, base, fields } => {
                    let mut record = match base {
                        Some(base) => match read_plain_value(&values, *base)? {
                            runtime::VmValue::Record(fields) => fields,
                            value => return Err(NativeAbiEvalError::ExpectedRecord { value }),
                        },
                        None => BTreeMap::new(),
                    };
                    for field in fields {
                        record.insert(field.name.clone(), read_plain_value(&values, field.value)?);
                    }
                    write_value(&mut values, *dest, plain(runtime::VmValue::Record(record)));
                }
                NativeAbiStmt::Variant { dest, tag, value } => {
                    let value = value
                        .map(|value| read_plain_value(&values, value).map(Box::new))
                        .transpose()?;
                    write_value(
                        &mut values,
                        *dest,
                        plain(runtime::VmValue::Variant {
                            tag: tag.clone(),
                            value,
                        }),
                    );
                }
                NativeAbiStmt::Select { dest, base, field } => {
                    let value = match read_plain_value(&values, *base)? {
                        runtime::VmValue::Record(fields) => fields.get(field).cloned(),
                        _ => None,
                    }
                    .ok_or(NativeAbiEvalError::ExpectedPlainValue { id: *base })?;
                    write_value(&mut values, *dest, plain(value));
                }
                NativeAbiStmt::LoadEnv { dest, slot } => {
                    let value = env.get(*slot).cloned().ok_or_else(|| {
                        NativeAbiEvalError::MissingEnvSlot {
                            function: function.name.clone(),
                            slot: *slot,
                        }
                    })?;
                    write_value(&mut values, *dest, value);
                }
                NativeAbiStmt::AllocateClosure {
                    dest,
                    target,
                    environment,
                } => {
                    let environment = environment
                        .iter()
                        .map(|id| read_value(&values, *id))
                        .collect::<NativeAbiEvalResult<Vec<_>>>()?;
                    write_value(
                        &mut values,
                        *dest,
                        NativeAbiRuntimeValue::Closure(NativeAbiClosureValue {
                            target: target.clone(),
                            environment,
                        }),
                    );
                }
                NativeAbiStmt::IndirectClosureCall { dest, callee, args } => {
                    let closure = read_closure(&values, *callee)?;
                    let function = function_by_name(module, &closure.target)?;
                    let args = args
                        .iter()
                        .map(|id| read_value(&values, *id))
                        .collect::<NativeAbiEvalResult<Vec<_>>>()?;
                    write_value(
                        &mut values,
                        *dest,
                        eval_function_value(module, function, closure.environment, args)?,
                    );
                }
            }
        }

        match &block.terminator {
            NativeTerminator::Return(value) => return read_value(&values, *value),
            NativeTerminator::Jump {
                target,
                args: jump_args,
            } => {
                args = jump_args
                    .iter()
                    .map(|id| read_value(&values, *id))
                    .collect::<NativeAbiEvalResult<Vec<_>>>()?;
                current = *target;
            }
            NativeTerminator::Branch {
                cond,
                then_block,
                else_block,
            } => {
                let cond = read_plain_value(&values, *cond)?;
                current = if bool_value(&cond)? {
                    *then_block
                } else {
                    *else_block
                };
            }
        }
    }
}

fn block_by_id(function: &NativeAbiFunction, id: BlockId) -> NativeAbiEvalResult<&NativeAbiBlock> {
    function
        .blocks
        .iter()
        .find(|block| block.id == id)
        .ok_or(NativeAbiEvalError::MissingBlock { id })
}

fn function_by_name<'a>(
    module: &'a NativeAbiModule,
    name: &str,
) -> NativeAbiEvalResult<&'a NativeAbiFunction> {
    module
        .functions
        .iter()
        .chain(&module.roots)
        .find(|function| function.name == name)
        .ok_or_else(|| NativeAbiEvalError::MissingFunction {
            name: name.to_string(),
        })
}

fn assign_block_args(
    values: &mut Vec<Option<NativeAbiRuntimeValue>>,
    block: &NativeAbiBlock,
    args: Vec<NativeAbiRuntimeValue>,
) -> NativeAbiEvalResult<()> {
    if block.params.len() != args.len() {
        return Err(NativeAbiEvalError::BlockArgumentMismatch {
            id: block.id,
            expected: block.params.len(),
            actual: args.len(),
        });
    }
    for (param, value) in block.params.iter().copied().zip(args) {
        write_value(values, param, value);
    }
    Ok(())
}

fn write_value(
    values: &mut Vec<Option<NativeAbiRuntimeValue>>,
    id: ValueId,
    value: NativeAbiRuntimeValue,
) {
    if values.len() <= id.0 {
        values.resize_with(id.0 + 1, || None);
    }
    values[id.0] = Some(value);
}

fn read_value(
    values: &[Option<NativeAbiRuntimeValue>],
    id: ValueId,
) -> NativeAbiEvalResult<NativeAbiRuntimeValue> {
    values
        .get(id.0)
        .and_then(Clone::clone)
        .ok_or(NativeAbiEvalError::MissingValue { id })
}

fn read_plain_value(
    values: &[Option<NativeAbiRuntimeValue>],
    id: ValueId,
) -> NativeAbiEvalResult<runtime::VmValue> {
    into_plain_value(id, read_value(values, id)?)
}

fn read_closure(
    values: &[Option<NativeAbiRuntimeValue>],
    id: ValueId,
) -> NativeAbiEvalResult<NativeAbiClosureValue> {
    match read_value(values, id)? {
        NativeAbiRuntimeValue::Closure(value) => Ok(value),
        NativeAbiRuntimeValue::Plain(_) => Err(NativeAbiEvalError::ExpectedClosure { id }),
    }
}

fn into_plain_value(
    id: ValueId,
    value: NativeAbiRuntimeValue,
) -> NativeAbiEvalResult<runtime::VmValue> {
    match value {
        NativeAbiRuntimeValue::Plain(value) => Ok(value),
        NativeAbiRuntimeValue::Closure(_) => Err(NativeAbiEvalError::ExpectedPlainValue { id }),
    }
}

fn plain(value: runtime::VmValue) -> NativeAbiRuntimeValue {
    NativeAbiRuntimeValue::Plain(value)
}

#[derive(Debug, Clone, PartialEq)]
enum NativeAbiRuntimeValue {
    Plain(runtime::VmValue),
    Closure(NativeAbiClosureValue),
}

#[derive(Debug, Clone, PartialEq)]
struct NativeAbiClosureValue {
    target: String,
    environment: Vec<NativeAbiRuntimeValue>,
}

fn eval_literal(lit: &NativeLiteral) -> runtime::VmValue {
    match lit {
        NativeLiteral::Int(value) => runtime::VmValue::Int(value.clone()),
        NativeLiteral::Float(value) => runtime::VmValue::Float(value.clone()),
        NativeLiteral::String(value) => {
            runtime::VmValue::String(runtime::runtime::string_tree::StringTree::from_str(value))
        }
        NativeLiteral::Bool(value) => runtime::VmValue::Bool(*value),
        NativeLiteral::Unit => runtime::VmValue::Unit,
    }
}

fn bool_value(value: &runtime::VmValue) -> NativeAbiEvalResult<bool> {
    match value {
        runtime::VmValue::Bool(value) => Ok(*value),
        value => Err(NativeAbiEvalError::NativeEval(
            NativeEvalError::PrimitiveTypeMismatch {
                op: typed_ir::PrimitiveOp::BoolNot,
                value: value.clone(),
            },
        )),
    }
}

#[cfg(test)]
mod tests {
    use yulang_typed_ir as typed_ir;

    use crate::abi::{
        NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt,
        lower_closure_module_to_abi,
    };
    use crate::closure::closure_convert_module;
    use crate::control_ir::{
        BlockId, NativeBlock, NativeFunction, NativeLiteral, NativeModule, NativeStmt,
        NativeTerminator, ValueId,
    };

    use super::*;

    #[test]
    fn evaluates_direct_call() {
        let module = NativeAbiModule {
            functions: vec![add_function()],
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
                            literal: NativeLiteral::Int("20".to_string()),
                        },
                        NativeAbiStmt::Literal {
                            dest: ValueId(1),
                            literal: NativeLiteral::Int("22".to_string()),
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

        assert_eq!(
            eval_abi_module(&module).expect("evaluated"),
            vec![runtime::VmValue::Int("42".to_string())]
        );
    }

    #[test]
    fn evaluates_closure_environment_and_indirect_call() {
        let module = NativeAbiModule {
            functions: vec![add_capture_function()],
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
                            literal: NativeLiteral::Int("10".to_string()),
                        },
                        NativeAbiStmt::Literal {
                            dest: ValueId(1),
                            literal: NativeLiteral::Int("32".to_string()),
                        },
                        NativeAbiStmt::AllocateClosure {
                            dest: ValueId(2),
                            target: "add_capture".to_string(),
                            environment: vec![ValueId(0)],
                        },
                        NativeAbiStmt::IndirectClosureCall {
                            dest: ValueId(3),
                            callee: ValueId(2),
                            args: vec![ValueId(1)],
                        },
                    ],
                    terminator: NativeTerminator::Return(ValueId(3)),
                }],
            }],
        };

        assert_eq!(
            eval_abi_module(&module).expect("evaluated"),
            vec![runtime::VmValue::Int("42".to_string())]
        );
    }

    #[test]
    fn evaluates_lowered_closure_call_abi() {
        let native = NativeModule {
            functions: vec![NativeFunction {
                name: "add_capture".to_string(),
                captures: vec![ValueId(0)],
                params: vec![ValueId(0), ValueId(1)],
                blocks: vec![NativeBlock {
                    id: BlockId(0),
                    params: vec![ValueId(0), ValueId(1)],
                    stmts: vec![NativeStmt::Primitive {
                        dest: ValueId(2),
                        op: typed_ir::PrimitiveOp::IntAdd,
                        args: vec![ValueId(0), ValueId(1)],
                    }],
                    terminator: NativeTerminator::Return(ValueId(2)),
                }],
            }],
            roots: vec![NativeFunction {
                name: "root".to_string(),
                captures: Vec::new(),
                params: Vec::new(),
                blocks: vec![NativeBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![
                        NativeStmt::Literal {
                            dest: ValueId(0),
                            literal: NativeLiteral::Int("10".to_string()),
                        },
                        NativeStmt::Literal {
                            dest: ValueId(1),
                            literal: NativeLiteral::Int("32".to_string()),
                        },
                        NativeStmt::MakeClosure {
                            dest: ValueId(2),
                            target: "add_capture".to_string(),
                            captures: vec![ValueId(0)],
                        },
                        NativeStmt::ClosureCall {
                            dest: ValueId(3),
                            callee: ValueId(2),
                            args: vec![ValueId(1)],
                        },
                    ],
                    terminator: NativeTerminator::Return(ValueId(3)),
                }],
            }],
        };
        let abi = lower_closure_module_to_abi(&closure_convert_module(&native));

        assert_eq!(
            eval_abi_module(&abi).expect("evaluated"),
            vec![runtime::VmValue::Int("42".to_string())]
        );
    }

    fn add_function() -> NativeAbiFunction {
        NativeAbiFunction {
            name: "add".to_string(),
            params: vec![ValueId(0), ValueId(1)],
            environment_slots: 0,
            blocks: vec![NativeAbiBlock {
                id: BlockId(0),
                params: vec![ValueId(0), ValueId(1)],
                stmts: vec![NativeAbiStmt::Primitive {
                    dest: ValueId(2),
                    op: typed_ir::PrimitiveOp::IntAdd,
                    args: vec![ValueId(0), ValueId(1)],
                }],
                terminator: NativeTerminator::Return(ValueId(2)),
            }],
        }
    }

    fn add_capture_function() -> NativeAbiFunction {
        NativeAbiFunction {
            name: "add_capture".to_string(),
            params: vec![ValueId(1)],
            environment_slots: 1,
            blocks: vec![NativeAbiBlock {
                id: BlockId(0),
                params: vec![ValueId(1)],
                stmts: vec![
                    NativeAbiStmt::LoadEnv {
                        dest: ValueId(0),
                        slot: 0,
                    },
                    NativeAbiStmt::Primitive {
                        dest: ValueId(2),
                        op: typed_ir::PrimitiveOp::IntAdd,
                        args: vec![ValueId(0), ValueId(1)],
                    },
                ],
                terminator: NativeTerminator::Return(ValueId(2)),
            }],
        }
    }
}
