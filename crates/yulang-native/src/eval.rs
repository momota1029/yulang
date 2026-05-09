use std::fmt;

use yulang_core_ir as core_ir;
use yulang_runtime as runtime;

use crate::control_ir::{
    BlockId, NativeBlock, NativeFunction, NativeLiteral, NativeModule, NativeStmt,
    NativeTerminator, ValueId,
};

pub type NativeEvalResult<T> = Result<T, NativeEvalError>;

#[derive(Debug, Clone, PartialEq)]
pub enum NativeEvalError {
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
    MissingValue {
        id: ValueId,
    },
    ExpectedPlainValue {
        id: ValueId,
    },
    ExpectedClosure {
        id: ValueId,
    },
    UnsupportedPrimitive {
        op: core_ir::PrimitiveOp,
    },
    PrimitiveTypeMismatch {
        op: core_ir::PrimitiveOp,
        value: runtime::VmValue,
    },
    InvalidPrimitiveArity {
        op: core_ir::PrimitiveOp,
        expected: usize,
        actual: usize,
    },
}

impl fmt::Display for NativeEvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeEvalError::EmptyFunction { name } => {
                write!(f, "native control function {name} has no entry block")
            }
            NativeEvalError::MissingFunction { name } => {
                write!(f, "native control function {name} is missing")
            }
            NativeEvalError::MissingBlock { id } => {
                write!(f, "native control block {id:?} is missing")
            }
            NativeEvalError::BlockArgumentMismatch {
                id,
                expected,
                actual,
            } => {
                write!(
                    f,
                    "native control block {id:?} expected {expected} arguments, got {actual}"
                )
            }
            NativeEvalError::MissingValue { id } => {
                write!(f, "native control value {id:?} is missing")
            }
            NativeEvalError::ExpectedPlainValue { id } => {
                write!(f, "native control expected plain value {id:?}")
            }
            NativeEvalError::ExpectedClosure { id } => {
                write!(f, "native control expected closure value {id:?}")
            }
            NativeEvalError::UnsupportedPrimitive { op } => {
                write!(
                    f,
                    "native control evaluator does not support primitive {op:?} yet"
                )
            }
            NativeEvalError::PrimitiveTypeMismatch { op, value } => {
                write!(f, "native primitive {op:?} cannot accept value {value:?}")
            }
            NativeEvalError::InvalidPrimitiveArity {
                op,
                expected,
                actual,
            } => write!(
                f,
                "native primitive {op:?} expected {expected} arguments, got {actual}"
            ),
        }
    }
}

impl std::error::Error for NativeEvalError {}

pub fn eval_module(module: &NativeModule) -> NativeEvalResult<Vec<runtime::VmValue>> {
    module
        .roots
        .iter()
        .map(|root| eval_function(module, root, Vec::new()))
        .collect()
}

fn eval_function(
    module: &NativeModule,
    function: &NativeFunction,
    args: Vec<runtime::VmValue>,
) -> NativeEvalResult<runtime::VmValue> {
    into_plain_value(
        ValueId(usize::MAX),
        eval_function_value(
            module,
            function,
            args.into_iter().map(NativeRuntimeValue::Plain).collect(),
        )?,
    )
}

fn eval_function_value(
    module: &NativeModule,
    function: &NativeFunction,
    args: Vec<NativeRuntimeValue>,
) -> NativeEvalResult<NativeRuntimeValue> {
    if function.params.len() != args.len() {
        return Err(NativeEvalError::BlockArgumentMismatch {
            id: BlockId(0),
            expected: function.params.len(),
            actual: args.len(),
        });
    }
    let entry = function
        .blocks
        .first()
        .ok_or_else(|| NativeEvalError::EmptyFunction {
            name: function.name.clone(),
        })?;
    eval_blocks(module, function, entry.id, args)
}

fn eval_blocks(
    module: &NativeModule,
    function: &NativeFunction,
    entry: BlockId,
    initial_args: Vec<NativeRuntimeValue>,
) -> NativeEvalResult<NativeRuntimeValue> {
    let mut values = Vec::<Option<NativeRuntimeValue>>::new();
    let mut current = entry;
    let mut args = initial_args;
    loop {
        let block = block_by_id(function, current)?;
        assign_block_args(&mut values, block, args)?;
        args = Vec::new();

        for stmt in &block.stmts {
            match stmt {
                NativeStmt::Literal { dest, literal } => {
                    write_value(
                        &mut values,
                        *dest,
                        NativeRuntimeValue::Plain(eval_literal(literal)),
                    );
                }
                NativeStmt::Primitive { dest, op, args } => {
                    let args = args
                        .iter()
                        .map(|id| read_plain_value(&values, *id))
                        .collect::<NativeEvalResult<Vec<_>>>()?;
                    write_value(
                        &mut values,
                        *dest,
                        NativeRuntimeValue::Plain(eval_primitive(*op, &args)?),
                    );
                }
                NativeStmt::DirectCall { dest, target, args } => {
                    let function = module
                        .functions
                        .iter()
                        .find(|function| &function.name == target)
                        .ok_or_else(|| NativeEvalError::MissingFunction {
                            name: target.clone(),
                        })?;
                    let args = args
                        .iter()
                        .map(|id| read_value(&values, *id))
                        .collect::<NativeEvalResult<Vec<_>>>()?;
                    write_value(
                        &mut values,
                        *dest,
                        eval_function_value(module, function, args)?,
                    );
                }
                NativeStmt::MakeClosure {
                    dest,
                    target,
                    captures,
                } => {
                    let captures = captures
                        .iter()
                        .map(|id| read_value(&values, *id))
                        .collect::<NativeEvalResult<Vec<_>>>()?;
                    write_value(
                        &mut values,
                        *dest,
                        NativeRuntimeValue::Closure(NativeClosureValue {
                            target: target.clone(),
                            captures,
                        }),
                    );
                }
                NativeStmt::ClosureCall { dest, callee, args } => {
                    let closure = read_closure(&values, *callee)?;
                    let mut call_args = closure.captures;
                    call_args.extend(
                        args.iter()
                            .map(|id| read_value(&values, *id))
                            .collect::<NativeEvalResult<Vec<_>>>()?,
                    );
                    let function = module
                        .functions
                        .iter()
                        .find(|function| function.name == closure.target)
                        .ok_or_else(|| NativeEvalError::MissingFunction {
                            name: closure.target,
                        })?;
                    write_value(
                        &mut values,
                        *dest,
                        eval_function_value(module, function, call_args)?,
                    );
                }
            }
        }
        match &block.terminator {
            NativeTerminator::Return(id) => return read_value(&values, *id),
            NativeTerminator::Jump {
                target,
                args: jump_args,
            } => {
                args = jump_args
                    .iter()
                    .map(|id| read_value(&values, *id))
                    .collect::<NativeEvalResult<Vec<_>>>()?;
                current = *target;
            }
            NativeTerminator::Branch {
                cond,
                then_block,
                else_block,
            } => {
                let cond = read_plain_value(&values, *cond)?;
                current = if bool_value(core_ir::PrimitiveOp::BoolNot, &cond)? {
                    *then_block
                } else {
                    *else_block
                };
            }
        }
    }
}

fn block_by_id(function: &NativeFunction, id: BlockId) -> NativeEvalResult<&NativeBlock> {
    function
        .blocks
        .iter()
        .find(|block| block.id == id)
        .ok_or(NativeEvalError::MissingBlock { id })
}

fn assign_block_args(
    values: &mut Vec<Option<NativeRuntimeValue>>,
    block: &NativeBlock,
    args: Vec<NativeRuntimeValue>,
) -> NativeEvalResult<()> {
    if block.params.len() != args.len() {
        return Err(NativeEvalError::BlockArgumentMismatch {
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
    values: &mut Vec<Option<NativeRuntimeValue>>,
    id: ValueId,
    value: NativeRuntimeValue,
) {
    if values.len() <= id.0 {
        values.resize_with(id.0 + 1, || None);
    }
    values[id.0] = Some(value);
}

fn read_value(
    values: &[Option<NativeRuntimeValue>],
    id: ValueId,
) -> NativeEvalResult<NativeRuntimeValue> {
    values
        .get(id.0)
        .and_then(Clone::clone)
        .ok_or(NativeEvalError::MissingValue { id })
}

fn read_plain_value(
    values: &[Option<NativeRuntimeValue>],
    id: ValueId,
) -> NativeEvalResult<runtime::VmValue> {
    into_plain_value(id, read_value(values, id)?)
}

fn read_closure(
    values: &[Option<NativeRuntimeValue>],
    id: ValueId,
) -> NativeEvalResult<NativeClosureValue> {
    match read_value(values, id)? {
        NativeRuntimeValue::Closure(value) => Ok(value),
        NativeRuntimeValue::Plain(_) => Err(NativeEvalError::ExpectedClosure { id }),
    }
}

fn into_plain_value(id: ValueId, value: NativeRuntimeValue) -> NativeEvalResult<runtime::VmValue> {
    match value {
        NativeRuntimeValue::Plain(value) => Ok(value),
        NativeRuntimeValue::Closure(_) => Err(NativeEvalError::ExpectedPlainValue { id }),
    }
}

#[derive(Debug, Clone, PartialEq)]
enum NativeRuntimeValue {
    Plain(runtime::VmValue),
    Closure(NativeClosureValue),
}

#[derive(Debug, Clone, PartialEq)]
struct NativeClosureValue {
    target: String,
    captures: Vec<NativeRuntimeValue>,
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

pub(crate) fn eval_primitive_for_abi(
    op: core_ir::PrimitiveOp,
    args: &[runtime::VmValue],
) -> NativeEvalResult<runtime::VmValue> {
    eval_primitive(op, args)
}

fn eval_primitive(
    op: core_ir::PrimitiveOp,
    args: &[runtime::VmValue],
) -> NativeEvalResult<runtime::VmValue> {
    use core_ir::PrimitiveOp;
    match op {
        PrimitiveOp::BoolNot => {
            expect_arity(op, args, 1)?;
            Ok(runtime::VmValue::Bool(!bool_value(op, &args[0])?))
        }
        PrimitiveOp::BoolEq => {
            expect_arity(op, args, 2)?;
            Ok(runtime::VmValue::Bool(
                bool_value(op, &args[0])? == bool_value(op, &args[1])?,
            ))
        }
        PrimitiveOp::IntAdd => int_bin_op(op, args, |left, right| left + right),
        PrimitiveOp::IntSub => int_bin_op(op, args, |left, right| left - right),
        PrimitiveOp::IntMul => int_bin_op(op, args, |left, right| left * right),
        PrimitiveOp::IntDiv => int_bin_op(op, args, |left, right| left / right),
        PrimitiveOp::IntEq => int_cmp_op(op, args, |left, right| left == right),
        PrimitiveOp::IntLt => int_cmp_op(op, args, |left, right| left < right),
        PrimitiveOp::IntLe => int_cmp_op(op, args, |left, right| left <= right),
        PrimitiveOp::IntGt => int_cmp_op(op, args, |left, right| left > right),
        PrimitiveOp::IntGe => int_cmp_op(op, args, |left, right| left >= right),
        PrimitiveOp::FloatAdd => float_bin_op(op, args, |left, right| left + right),
        PrimitiveOp::FloatSub => float_bin_op(op, args, |left, right| left - right),
        PrimitiveOp::FloatMul => float_bin_op(op, args, |left, right| left * right),
        PrimitiveOp::FloatDiv => float_bin_op(op, args, |left, right| left / right),
        PrimitiveOp::FloatEq => float_cmp_op(op, args, |left, right| left == right),
        PrimitiveOp::FloatLt => float_cmp_op(op, args, |left, right| left < right),
        PrimitiveOp::FloatLe => float_cmp_op(op, args, |left, right| left <= right),
        PrimitiveOp::FloatGt => float_cmp_op(op, args, |left, right| left > right),
        PrimitiveOp::FloatGe => float_cmp_op(op, args, |left, right| left >= right),
        PrimitiveOp::StringConcat => {
            expect_arity(op, args, 2)?;
            let left = string_value(op, &args[0])?;
            let right = string_value(op, &args[1])?;
            Ok(runtime::VmValue::String(
                runtime::runtime::string_tree::StringTree::concat(left.clone(), right.clone()),
            ))
        }
        PrimitiveOp::IntToString => {
            expect_arity(op, args, 1)?;
            Ok(value_from_string(&int_value(op, &args[0])?.to_string()))
        }
        PrimitiveOp::FloatToString => {
            expect_arity(op, args, 1)?;
            Ok(value_from_string(&format_float_value(float_value(
                op, &args[0],
            )?)))
        }
        PrimitiveOp::BoolToString => {
            expect_arity(op, args, 1)?;
            Ok(value_from_string(if bool_value(op, &args[0])? {
                "true"
            } else {
                "false"
            }))
        }
        _ => Err(NativeEvalError::UnsupportedPrimitive { op }),
    }
}

fn int_bin_op(
    op: core_ir::PrimitiveOp,
    args: &[runtime::VmValue],
    f: impl FnOnce(i64, i64) -> i64,
) -> NativeEvalResult<runtime::VmValue> {
    expect_arity(op, args, 2)?;
    Ok(runtime::VmValue::Int(
        f(int_value(op, &args[0])?, int_value(op, &args[1])?).to_string(),
    ))
}

fn int_cmp_op(
    op: core_ir::PrimitiveOp,
    args: &[runtime::VmValue],
    f: impl FnOnce(i64, i64) -> bool,
) -> NativeEvalResult<runtime::VmValue> {
    expect_arity(op, args, 2)?;
    Ok(runtime::VmValue::Bool(f(
        int_value(op, &args[0])?,
        int_value(op, &args[1])?,
    )))
}

fn float_bin_op(
    op: core_ir::PrimitiveOp,
    args: &[runtime::VmValue],
    f: impl FnOnce(f64, f64) -> f64,
) -> NativeEvalResult<runtime::VmValue> {
    expect_arity(op, args, 2)?;
    Ok(runtime::VmValue::Float(format_float_value(f(
        float_value(op, &args[0])?,
        float_value(op, &args[1])?,
    ))))
}

fn float_cmp_op(
    op: core_ir::PrimitiveOp,
    args: &[runtime::VmValue],
    f: impl FnOnce(f64, f64) -> bool,
) -> NativeEvalResult<runtime::VmValue> {
    expect_arity(op, args, 2)?;
    Ok(runtime::VmValue::Bool(f(
        float_value(op, &args[0])?,
        float_value(op, &args[1])?,
    )))
}

fn expect_arity(
    op: core_ir::PrimitiveOp,
    args: &[runtime::VmValue],
    expected: usize,
) -> NativeEvalResult<()> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(NativeEvalError::InvalidPrimitiveArity {
            op,
            expected,
            actual: args.len(),
        })
    }
}

fn int_value(op: core_ir::PrimitiveOp, value: &runtime::VmValue) -> NativeEvalResult<i64> {
    match value {
        runtime::VmValue::Int(value) => {
            value
                .parse()
                .map_err(|_| NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: value_from_string(value),
                })
        }
        value => Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: value.clone(),
        }),
    }
}

fn float_value(op: core_ir::PrimitiveOp, value: &runtime::VmValue) -> NativeEvalResult<f64> {
    match value {
        runtime::VmValue::Float(value) => {
            value
                .parse()
                .map_err(|_| NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: runtime::VmValue::Float(value.clone()),
                })
        }
        value => Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: value.clone(),
        }),
    }
}

fn bool_value(op: core_ir::PrimitiveOp, value: &runtime::VmValue) -> NativeEvalResult<bool> {
    match value {
        runtime::VmValue::Bool(value) => Ok(*value),
        value => Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: value.clone(),
        }),
    }
}

fn string_value(
    op: core_ir::PrimitiveOp,
    value: &runtime::VmValue,
) -> NativeEvalResult<&runtime::runtime::string_tree::StringTree> {
    match value {
        runtime::VmValue::String(value) => Ok(value),
        value => Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: value.clone(),
        }),
    }
}

fn format_float_value(value: f64) -> String {
    let mut rendered = value.to_string();
    if !rendered.contains('.') && !rendered.contains('e') && !rendered.contains('E') {
        rendered.push_str(".0");
    }
    rendered
}

fn value_from_string(value: &str) -> runtime::VmValue {
    runtime::VmValue::String(runtime::runtime::string_tree::StringTree::from_str(value))
}
