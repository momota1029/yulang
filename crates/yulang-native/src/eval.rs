use std::collections::BTreeMap;
use std::fmt;

use yulang_runtime as runtime;
use yulang_typed_ir as typed_ir;

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
    ExpectedRecord {
        value: runtime::VmValue,
    },
    ExpectedTuple {
        value: runtime::VmValue,
    },
    ExpectedVariant {
        value: runtime::VmValue,
    },
    UnsupportedPrimitive {
        op: typed_ir::PrimitiveOp,
    },
    PrimitiveTypeMismatch {
        op: typed_ir::PrimitiveOp,
        value: runtime::VmValue,
    },
    InvalidPrimitiveArity {
        op: typed_ir::PrimitiveOp,
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
            NativeEvalError::ExpectedRecord { value } => {
                write!(f, "native control expected record, got {value:?}")
            }
            NativeEvalError::ExpectedTuple { value } => {
                write!(f, "native control expected tuple, got {value:?}")
            }
            NativeEvalError::ExpectedVariant { value } => {
                write!(f, "native control expected variant, got {value:?}")
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
                NativeStmt::Tuple { dest, items } => {
                    let items = items
                        .iter()
                        .map(|id| read_plain_value(&values, *id))
                        .collect::<NativeEvalResult<Vec<_>>>()?;
                    write_value(
                        &mut values,
                        *dest,
                        NativeRuntimeValue::Plain(runtime::VmValue::Tuple(items)),
                    );
                }
                NativeStmt::Record { dest, base, fields } => {
                    let mut record = match base {
                        Some(base) => match read_plain_value(&values, *base)? {
                            runtime::VmValue::Record(fields) => fields,
                            value => return Err(NativeEvalError::ExpectedRecord { value }),
                        },
                        None => BTreeMap::new(),
                    };
                    for field in fields {
                        record.insert(field.name.clone(), read_plain_value(&values, field.value)?);
                    }
                    write_value(
                        &mut values,
                        *dest,
                        NativeRuntimeValue::Plain(runtime::VmValue::Record(record)),
                    );
                }
                NativeStmt::RecordWithoutFields { dest, base, fields } => {
                    let mut record = match read_plain_value(&values, *base)? {
                        runtime::VmValue::Record(fields) => fields,
                        value => return Err(NativeEvalError::ExpectedRecord { value }),
                    };
                    for field in fields {
                        record.remove(field);
                    }
                    write_value(
                        &mut values,
                        *dest,
                        NativeRuntimeValue::Plain(runtime::VmValue::Record(record)),
                    );
                }
                NativeStmt::Variant { dest, tag, value } => {
                    let value = value
                        .map(|value| read_plain_value(&values, value).map(Box::new))
                        .transpose()?;
                    write_value(
                        &mut values,
                        *dest,
                        NativeRuntimeValue::Plain(runtime::VmValue::Variant {
                            tag: tag.clone(),
                            value,
                        }),
                    );
                }
                NativeStmt::Select { dest, base, field } => {
                    let value = match read_plain_value(&values, *base)? {
                        runtime::VmValue::Record(fields) => fields.get(field).cloned(),
                        _ => None,
                    }
                    .ok_or(NativeEvalError::ExpectedPlainValue { id: *base })?;
                    write_value(&mut values, *dest, NativeRuntimeValue::Plain(value));
                }
                NativeStmt::TupleGet { dest, tuple, index } => {
                    let value = read_plain_value(&values, *tuple)?;
                    let runtime::VmValue::Tuple(items) = value else {
                        return Err(NativeEvalError::ExpectedTuple { value });
                    };
                    let value = items.get(*index).cloned().ok_or_else(|| {
                        NativeEvalError::ExpectedTuple {
                            value: runtime::VmValue::Tuple(items.clone()),
                        }
                    })?;
                    write_value(&mut values, *dest, NativeRuntimeValue::Plain(value));
                }
                NativeStmt::VariantTagEq { dest, variant, tag } => {
                    let value = read_plain_value(&values, *variant)?;
                    let runtime::VmValue::Variant {
                        tag: actual_tag, ..
                    } = value
                    else {
                        return Err(NativeEvalError::ExpectedVariant { value });
                    };
                    write_value(
                        &mut values,
                        *dest,
                        NativeRuntimeValue::Plain(runtime::VmValue::Bool(actual_tag == *tag)),
                    );
                }
                NativeStmt::VariantPayload { dest, variant } => {
                    let value = read_plain_value(&values, *variant)?;
                    let runtime::VmValue::Variant {
                        value: Some(payload),
                        ..
                    } = value
                    else {
                        return Err(NativeEvalError::ExpectedVariant { value });
                    };
                    write_value(&mut values, *dest, NativeRuntimeValue::Plain(*payload));
                }
                NativeStmt::ValueEq { dest, left, right } => {
                    let left = read_plain_value(&values, *left)?;
                    let right = read_plain_value(&values, *right)?;
                    write_value(
                        &mut values,
                        *dest,
                        NativeRuntimeValue::Plain(runtime::VmValue::Bool(left == right)),
                    );
                }
                NativeStmt::BoolAnd { dest, left, right } => {
                    let left = read_plain_value(&values, *left)?;
                    let right = read_plain_value(&values, *right)?;
                    write_value(
                        &mut values,
                        *dest,
                        NativeRuntimeValue::Plain(runtime::VmValue::Bool(
                            matches!(left, runtime::VmValue::Bool(true))
                                && matches!(right, runtime::VmValue::Bool(true)),
                        )),
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
                current = if bool_value(typed_ir::PrimitiveOp::BoolNot, &cond)? {
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
    op: typed_ir::PrimitiveOp,
    args: &[runtime::VmValue],
) -> NativeEvalResult<runtime::VmValue> {
    eval_primitive(op, args)
}

fn eval_primitive(
    op: typed_ir::PrimitiveOp,
    args: &[runtime::VmValue],
) -> NativeEvalResult<runtime::VmValue> {
    use typed_ir::PrimitiveOp;
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
        PrimitiveOp::ListEmpty => {
            expect_arity(op, args, 1)?;
            Ok(runtime::VmValue::List(
                runtime::runtime::list_tree::ListTree::empty(),
            ))
        }
        PrimitiveOp::ListSingleton => {
            expect_arity(op, args, 1)?;
            Ok(runtime::VmValue::List(
                runtime::runtime::list_tree::ListTree::singleton(std::rc::Rc::new(args[0].clone())),
            ))
        }
        PrimitiveOp::ListMerge => {
            expect_arity(op, args, 2)?;
            Ok(runtime::VmValue::List(
                runtime::runtime::list_tree::ListTree::concat(
                    list_value(op, &args[0])?.clone(),
                    list_value(op, &args[1])?.clone(),
                ),
            ))
        }
        PrimitiveOp::ListLen => {
            expect_arity(op, args, 1)?;
            Ok(runtime::VmValue::Int(
                list_value(op, &args[0])?.len().to_string(),
            ))
        }
        PrimitiveOp::ListIndex => {
            expect_arity(op, args, 2)?;
            let index = usize::try_from(int_value(op, &args[1])?).map_err(|_| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[1].clone(),
                }
            })?;
            let value = list_value(op, &args[0])?.index(index).ok_or_else(|| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[0].clone(),
                }
            })?;
            Ok(value.as_ref().clone())
        }
        PrimitiveOp::ListIndexRangeRaw => {
            expect_arity(op, args, 3)?;
            let start = usize::try_from(int_value(op, &args[1])?).map_err(|_| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[1].clone(),
                }
            })?;
            let end = usize::try_from(int_value(op, &args[2])?).map_err(|_| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[2].clone(),
                }
            })?;
            let value = list_value(op, &args[0])?
                .index_range(start, end)
                .ok_or_else(|| NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[0].clone(),
                })?;
            Ok(runtime::VmValue::List(value))
        }
        PrimitiveOp::ListIndexRange => {
            expect_arity(op, args, 2)?;
            let list = list_value(op, &args[0])?;
            let (start, end) = normalized_int_range_value(op, &args[1], list.len())?;
            let value = list.index_range(start, end).ok_or_else(|| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[0].clone(),
                }
            })?;
            Ok(runtime::VmValue::List(value))
        }
        PrimitiveOp::ListSplice => {
            expect_arity(op, args, 3)?;
            let list = list_value(op, &args[0])?;
            let (start, end) = normalized_int_range_value(op, &args[1], list.len())?;
            let insert = list_value(op, &args[2])?;
            let value = list.splice(start, end, insert.clone()).ok_or_else(|| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[0].clone(),
                }
            })?;
            Ok(runtime::VmValue::List(value))
        }
        PrimitiveOp::ListSpliceRaw => {
            expect_arity(op, args, 4)?;
            let start = usize::try_from(int_value(op, &args[1])?).map_err(|_| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[1].clone(),
                }
            })?;
            let end = usize::try_from(int_value(op, &args[2])?).map_err(|_| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[2].clone(),
                }
            })?;
            let list = list_value(op, &args[0])?;
            let insert = list_value(op, &args[3])?;
            let value = list.splice(start, end, insert.clone()).ok_or_else(|| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[0].clone(),
                }
            })?;
            Ok(runtime::VmValue::List(value))
        }
        PrimitiveOp::ListViewRaw => {
            expect_arity(op, args, 1)?;
            let value = match list_value(op, &args[0])?.view() {
                runtime::runtime::list_tree::ListView::Empty => runtime::VmValue::Variant {
                    tag: typed_ir::Name("empty".to_string()),
                    value: None,
                },
                runtime::runtime::list_tree::ListView::Leaf(single) => runtime::VmValue::Variant {
                    tag: typed_ir::Name("leaf".to_string()),
                    value: Some(Box::new((*single).clone())),
                },
                runtime::runtime::list_tree::ListView::Node { left, right, .. } => {
                    runtime::VmValue::Variant {
                        tag: typed_ir::Name("node".to_string()),
                        value: Some(Box::new(runtime::VmValue::Tuple(vec![
                            runtime::VmValue::List(left),
                            runtime::VmValue::List(right),
                        ]))),
                    }
                }
            };
            Ok(value)
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
        PrimitiveOp::StringEq => {
            expect_arity(op, args, 2)?;
            Ok(runtime::VmValue::Bool(
                string_value(op, &args[0])?.to_flat_string()
                    == string_value(op, &args[1])?.to_flat_string(),
            ))
        }
        PrimitiveOp::StringLen => {
            expect_arity(op, args, 1)?;
            Ok(runtime::VmValue::Int(
                string_value(op, &args[0])?.len().to_string(),
            ))
        }
        PrimitiveOp::StringIndex => {
            expect_arity(op, args, 2)?;
            let index = usize::try_from(int_value(op, &args[1])?).map_err(|_| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[1].clone(),
                }
            })?;
            let value = string_value(op, &args[0])?.index(index).ok_or_else(|| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[0].clone(),
                }
            })?;
            Ok(value_from_string(&value.to_string()))
        }
        PrimitiveOp::StringIndexRange => {
            expect_arity(op, args, 2)?;
            let text = string_value(op, &args[0])?;
            let (start, end) = normalized_int_range_value(op, &args[1], text.len())?;
            let value = text.index_range(start, end).ok_or_else(|| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[0].clone(),
                }
            })?;
            Ok(runtime::VmValue::String(value))
        }
        PrimitiveOp::StringSplice => {
            expect_arity(op, args, 3)?;
            let text = string_value(op, &args[0])?;
            let (start, end) = normalized_int_range_value(op, &args[1], text.len())?;
            let insert = string_value(op, &args[2])?;
            let value = text.splice(start, end, insert.clone()).ok_or_else(|| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[0].clone(),
                }
            })?;
            Ok(runtime::VmValue::String(value))
        }
        PrimitiveOp::StringIndexRangeRaw => {
            expect_arity(op, args, 3)?;
            let start = usize::try_from(int_value(op, &args[1])?).map_err(|_| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[1].clone(),
                }
            })?;
            let end = usize::try_from(int_value(op, &args[2])?).map_err(|_| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[2].clone(),
                }
            })?;
            let value = string_value(op, &args[0])?
                .index_range(start, end)
                .ok_or_else(|| NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[0].clone(),
                })?;
            Ok(runtime::VmValue::String(value))
        }
        PrimitiveOp::StringSpliceRaw => {
            expect_arity(op, args, 4)?;
            let start = usize::try_from(int_value(op, &args[1])?).map_err(|_| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[1].clone(),
                }
            })?;
            let end = usize::try_from(int_value(op, &args[2])?).map_err(|_| {
                NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[2].clone(),
                }
            })?;
            let insert = string_value(op, &args[3])?;
            let value = string_value(op, &args[0])?
                .splice(start, end, insert.clone())
                .ok_or_else(|| NativeEvalError::PrimitiveTypeMismatch {
                    op,
                    value: args[0].clone(),
                })?;
            Ok(runtime::VmValue::String(value))
        }
        PrimitiveOp::IntToString => {
            expect_arity(op, args, 1)?;
            Ok(value_from_string(&int_value(op, &args[0])?.to_string()))
        }
        PrimitiveOp::IntToHex => {
            expect_arity(op, args, 1)?;
            Ok(value_from_string(&format!(
                "{:x}",
                int_value(op, &args[0])?
            )))
        }
        PrimitiveOp::IntToUpperHex => {
            expect_arity(op, args, 1)?;
            Ok(value_from_string(&format!(
                "{:X}",
                int_value(op, &args[0])?
            )))
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
    }
}

fn int_bin_op(
    op: typed_ir::PrimitiveOp,
    args: &[runtime::VmValue],
    f: impl FnOnce(i64, i64) -> i64,
) -> NativeEvalResult<runtime::VmValue> {
    expect_arity(op, args, 2)?;
    Ok(runtime::VmValue::Int(
        f(int_value(op, &args[0])?, int_value(op, &args[1])?).to_string(),
    ))
}

fn int_cmp_op(
    op: typed_ir::PrimitiveOp,
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
    op: typed_ir::PrimitiveOp,
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
    op: typed_ir::PrimitiveOp,
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
    op: typed_ir::PrimitiveOp,
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

fn int_value(op: typed_ir::PrimitiveOp, value: &runtime::VmValue) -> NativeEvalResult<i64> {
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

fn float_value(op: typed_ir::PrimitiveOp, value: &runtime::VmValue) -> NativeEvalResult<f64> {
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

fn bool_value(op: typed_ir::PrimitiveOp, value: &runtime::VmValue) -> NativeEvalResult<bool> {
    match value {
        runtime::VmValue::Bool(value) => Ok(*value),
        value => Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: value.clone(),
        }),
    }
}

fn string_value(
    op: typed_ir::PrimitiveOp,
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

fn list_value(
    op: typed_ir::PrimitiveOp,
    value: &runtime::VmValue,
) -> NativeEvalResult<&runtime::runtime::list_tree::ListTree<std::rc::Rc<runtime::VmValue>>> {
    match value {
        runtime::VmValue::List(value) => Ok(value),
        value => Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: value.clone(),
        }),
    }
}

fn normalized_int_range_value(
    op: typed_ir::PrimitiveOp,
    value: &runtime::VmValue,
    len: usize,
) -> NativeEvalResult<(usize, usize)> {
    let original = value.clone();
    let runtime::VmValue::Variant { tag, value } = value else {
        return Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: original,
        });
    };
    if tag.0 != "within" {
        return Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: original,
        });
    }
    let Some(payload) = value.as_ref() else {
        return Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: runtime::VmValue::Variant {
                tag: tag.clone(),
                value: value.clone(),
            },
        });
    };
    let runtime::VmValue::Tuple(items) = payload.as_ref() else {
        return Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: payload.as_ref().clone(),
        });
    };
    let [start, end] = items.as_slice() else {
        return Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: runtime::VmValue::Tuple(items.clone()),
        });
    };
    let start = normalized_start_bound_value(op, start)?;
    let end = normalized_end_bound_value(op, end, len)?;
    if start <= end && end <= len {
        Ok((start, end))
    } else {
        Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: payload.as_ref().clone(),
        })
    }
}

fn normalized_start_bound_value(
    op: typed_ir::PrimitiveOp,
    value: &runtime::VmValue,
) -> NativeEvalResult<usize> {
    let original = value.clone();
    let runtime::VmValue::Variant { tag, value } = value else {
        return Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: original,
        });
    };
    match tag.0.as_str() {
        "unbounded" => Ok(0),
        "included" => {
            let value = int_variant_payload(op, value)?;
            usize::try_from(value).map_err(|_| NativeEvalError::PrimitiveTypeMismatch {
                op,
                value: value_from_string(&value.to_string()),
            })
        }
        "excluded" => {
            let value = int_variant_payload(op, value)?;
            usize::try_from(value + 1).map_err(|_| NativeEvalError::PrimitiveTypeMismatch {
                op,
                value: value_from_string(&value.to_string()),
            })
        }
        _ => Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: original,
        }),
    }
}

fn normalized_end_bound_value(
    op: typed_ir::PrimitiveOp,
    value: &runtime::VmValue,
    len: usize,
) -> NativeEvalResult<usize> {
    let original = value.clone();
    let runtime::VmValue::Variant { tag, value } = value else {
        return Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: original,
        });
    };
    match tag.0.as_str() {
        "unbounded" => Ok(len),
        "included" => {
            let value = int_variant_payload(op, value)?;
            usize::try_from(value + 1).map_err(|_| NativeEvalError::PrimitiveTypeMismatch {
                op,
                value: value_from_string(&value.to_string()),
            })
        }
        "excluded" => {
            let value = int_variant_payload(op, value)?;
            usize::try_from(value).map_err(|_| NativeEvalError::PrimitiveTypeMismatch {
                op,
                value: value_from_string(&value.to_string()),
            })
        }
        _ => Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: original,
        }),
    }
}

fn int_variant_payload(
    op: typed_ir::PrimitiveOp,
    value: &Option<Box<runtime::VmValue>>,
) -> NativeEvalResult<i64> {
    let Some(value) = value.as_ref() else {
        return Err(NativeEvalError::PrimitiveTypeMismatch {
            op,
            value: runtime::VmValue::Unit,
        });
    };
    int_value(op, value)
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
