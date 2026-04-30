use super::*;

pub(super) fn primitive_arity(op: core_ir::PrimitiveOp) -> usize {
    match op {
        core_ir::PrimitiveOp::BoolNot
        | core_ir::PrimitiveOp::ListEmpty
        | core_ir::PrimitiveOp::ListSingleton
        | core_ir::PrimitiveOp::ListLen
        | core_ir::PrimitiveOp::ListViewRaw
        | core_ir::PrimitiveOp::StringLen
        | core_ir::PrimitiveOp::IntToString
        | core_ir::PrimitiveOp::IntToHex
        | core_ir::PrimitiveOp::IntToUpperHex
        | core_ir::PrimitiveOp::FloatToString
        | core_ir::PrimitiveOp::BoolToString => 1,
        core_ir::PrimitiveOp::ListMerge
        | core_ir::PrimitiveOp::ListIndex
        | core_ir::PrimitiveOp::ListIndexRange
        | core_ir::PrimitiveOp::StringIndex
        | core_ir::PrimitiveOp::StringIndexRange
        | core_ir::PrimitiveOp::BoolEq
        | core_ir::PrimitiveOp::IntAdd
        | core_ir::PrimitiveOp::IntSub
        | core_ir::PrimitiveOp::IntMul
        | core_ir::PrimitiveOp::IntDiv
        | core_ir::PrimitiveOp::IntEq
        | core_ir::PrimitiveOp::IntLt
        | core_ir::PrimitiveOp::IntLe
        | core_ir::PrimitiveOp::IntGt
        | core_ir::PrimitiveOp::IntGe
        | core_ir::PrimitiveOp::FloatAdd
        | core_ir::PrimitiveOp::FloatSub
        | core_ir::PrimitiveOp::FloatMul
        | core_ir::PrimitiveOp::FloatDiv
        | core_ir::PrimitiveOp::FloatEq
        | core_ir::PrimitiveOp::FloatLt
        | core_ir::PrimitiveOp::FloatLe
        | core_ir::PrimitiveOp::FloatGt
        | core_ir::PrimitiveOp::FloatGe
        | core_ir::PrimitiveOp::StringConcat => 2,
        core_ir::PrimitiveOp::ListSplice
        | core_ir::PrimitiveOp::ListIndexRangeRaw
        | core_ir::PrimitiveOp::StringSplice
        | core_ir::PrimitiveOp::StringIndexRangeRaw => 3,
        core_ir::PrimitiveOp::ListSpliceRaw | core_ir::PrimitiveOp::StringSpliceRaw => 4,
    }
}

pub(super) fn apply_primitive(
    op: core_ir::PrimitiveOp,
    args: &[VmValue],
) -> Result<VmValue, VmError> {
    match op {
        core_ir::PrimitiveOp::BoolNot => Ok(VmValue::Bool(!bool_value(&args[0])?)),
        core_ir::PrimitiveOp::BoolEq => Ok(VmValue::Bool(
            bool_value(&args[0])? == bool_value(&args[1])?,
        )),
        core_ir::PrimitiveOp::IntAdd => Ok(VmValue::Int(
            (int_value(&args[0])? + int_value(&args[1])?).to_string(),
        )),
        core_ir::PrimitiveOp::IntSub => Ok(VmValue::Int(
            (int_value(&args[0])? - int_value(&args[1])?).to_string(),
        )),
        core_ir::PrimitiveOp::IntMul => Ok(VmValue::Int(
            (int_value(&args[0])? * int_value(&args[1])?).to_string(),
        )),
        core_ir::PrimitiveOp::IntDiv => Ok(VmValue::Int(
            (int_value(&args[0])? / int_value(&args[1])?).to_string(),
        )),
        core_ir::PrimitiveOp::IntEq => {
            Ok(VmValue::Bool(int_value(&args[0])? == int_value(&args[1])?))
        }
        core_ir::PrimitiveOp::IntLt => {
            Ok(VmValue::Bool(int_value(&args[0])? < int_value(&args[1])?))
        }
        core_ir::PrimitiveOp::IntLe => {
            Ok(VmValue::Bool(int_value(&args[0])? <= int_value(&args[1])?))
        }
        core_ir::PrimitiveOp::IntGt => {
            Ok(VmValue::Bool(int_value(&args[0])? > int_value(&args[1])?))
        }
        core_ir::PrimitiveOp::IntGe => {
            Ok(VmValue::Bool(int_value(&args[0])? >= int_value(&args[1])?))
        }
        core_ir::PrimitiveOp::FloatAdd => Ok(VmValue::Float(format_float_value(
            float_value(&args[0])? + float_value(&args[1])?,
        ))),
        core_ir::PrimitiveOp::FloatSub => Ok(VmValue::Float(format_float_value(
            float_value(&args[0])? - float_value(&args[1])?,
        ))),
        core_ir::PrimitiveOp::FloatMul => Ok(VmValue::Float(format_float_value(
            float_value(&args[0])? * float_value(&args[1])?,
        ))),
        core_ir::PrimitiveOp::FloatDiv => Ok(VmValue::Float(format_float_value(
            float_value(&args[0])? / float_value(&args[1])?,
        ))),
        core_ir::PrimitiveOp::FloatEq => Ok(VmValue::Bool(
            float_value(&args[0])? == float_value(&args[1])?,
        )),
        core_ir::PrimitiveOp::FloatLt => Ok(VmValue::Bool(
            float_value(&args[0])? < float_value(&args[1])?,
        )),
        core_ir::PrimitiveOp::FloatLe => Ok(VmValue::Bool(
            float_value(&args[0])? <= float_value(&args[1])?,
        )),
        core_ir::PrimitiveOp::FloatGt => Ok(VmValue::Bool(
            float_value(&args[0])? > float_value(&args[1])?,
        )),
        core_ir::PrimitiveOp::FloatGe => Ok(VmValue::Bool(
            float_value(&args[0])? >= float_value(&args[1])?,
        )),
        core_ir::PrimitiveOp::ListEmpty => Ok(VmValue::List(ListTree::empty())),
        core_ir::PrimitiveOp::ListSingleton => {
            Ok(VmValue::List(ListTree::singleton(args[0].clone())))
        }
        core_ir::PrimitiveOp::ListLen => Ok(VmValue::Int(list_value(&args[0])?.len().to_string())),
        core_ir::PrimitiveOp::ListMerge => {
            let left = list_value(&args[0])?;
            let right = list_value(&args[1])?;
            Ok(VmValue::List(ListTree::concat(left.clone(), right.clone())))
        }
        core_ir::PrimitiveOp::ListIndex => {
            let list = list_value(&args[0])?;
            let index = usize::try_from(int_value(&args[1])?)
                .map_err(|_| VmError::ExpectedInt(args[1].clone()))?;
            list.index(index)
                .map(|value| (*value).clone())
                .ok_or(VmError::ExpectedList(args[0].clone()))
        }
        core_ir::PrimitiveOp::ListIndexRange => {
            let list = list_value(&args[0])?;
            let (start, end) = normalized_int_range_value(&args[1], list.len())?;
            list.index_range(start, end)
                .map(VmValue::List)
                .ok_or(VmError::ExpectedList(args[0].clone()))
        }
        core_ir::PrimitiveOp::ListSplice => {
            let list = list_value(&args[0])?;
            let (start, end) = normalized_int_range_value(&args[1], list.len())?;
            let insert = list_value(&args[2])?;
            list.splice(start, end, insert.clone())
                .map(VmValue::List)
                .ok_or(VmError::ExpectedList(args[0].clone()))
        }
        core_ir::PrimitiveOp::ListIndexRangeRaw => {
            let list = list_value(&args[0])?;
            let start = usize::try_from(int_value(&args[1])?)
                .map_err(|_| VmError::ExpectedInt(args[1].clone()))?;
            let end = usize::try_from(int_value(&args[2])?)
                .map_err(|_| VmError::ExpectedInt(args[2].clone()))?;
            list.index_range(start, end)
                .map(VmValue::List)
                .ok_or(VmError::ExpectedList(args[0].clone()))
        }
        core_ir::PrimitiveOp::ListSpliceRaw => {
            let list = list_value(&args[0])?;
            let start = usize::try_from(int_value(&args[1])?)
                .map_err(|_| VmError::ExpectedInt(args[1].clone()))?;
            let end = usize::try_from(int_value(&args[2])?)
                .map_err(|_| VmError::ExpectedInt(args[2].clone()))?;
            let insert = list_value(&args[3])?;
            list.splice(start, end, insert.clone())
                .map(VmValue::List)
                .ok_or(VmError::ExpectedList(args[0].clone()))
        }
        core_ir::PrimitiveOp::ListViewRaw => match list_value(&args[0])?.view() {
            ListView::Empty => Ok(VmValue::Variant {
                tag: core_ir::Name("empty".to_string()),
                value: None,
            }),
            ListView::Leaf(single) => Ok(VmValue::Variant {
                tag: core_ir::Name("leaf".to_string()),
                value: Some(Box::new((*single).clone())),
            }),
            ListView::Node { left, right, .. } => Ok(VmValue::Variant {
                tag: core_ir::Name("node".to_string()),
                value: Some(Box::new(VmValue::Tuple(vec![
                    VmValue::List(left),
                    VmValue::List(right),
                ]))),
            }),
        },
        core_ir::PrimitiveOp::StringLen => {
            Ok(VmValue::Int(string_value(&args[0])?.len().to_string()))
        }
        core_ir::PrimitiveOp::StringIndex => {
            let text = string_value(&args[0])?;
            let index = usize::try_from(int_value(&args[1])?)
                .map_err(|_| VmError::ExpectedInt(args[1].clone()))?;
            text.index(index)
                .map(|ch| VmValue::String(StringTree::from(ch.to_string())))
                .ok_or(VmError::ExpectedString(args[0].clone()))
        }
        core_ir::PrimitiveOp::StringIndexRange => {
            let text = string_value(&args[0])?;
            let (start, end) = normalized_int_range_value(&args[1], text.len())?;
            text.index_range(start, end)
                .map(VmValue::String)
                .ok_or(VmError::ExpectedString(args[0].clone()))
        }
        core_ir::PrimitiveOp::StringSplice => {
            let text = string_value(&args[0])?;
            let (start, end) = normalized_int_range_value(&args[1], text.len())?;
            let insert = string_value(&args[2])?;
            text.splice(start, end, insert.clone())
                .map(VmValue::String)
                .ok_or(VmError::ExpectedString(args[0].clone()))
        }
        core_ir::PrimitiveOp::StringIndexRangeRaw => {
            let text = string_value(&args[0])?;
            let start = usize::try_from(int_value(&args[1])?)
                .map_err(|_| VmError::ExpectedInt(args[1].clone()))?;
            let end = usize::try_from(int_value(&args[2])?)
                .map_err(|_| VmError::ExpectedInt(args[2].clone()))?;
            text.index_range(start, end)
                .map(VmValue::String)
                .ok_or(VmError::ExpectedString(args[0].clone()))
        }
        core_ir::PrimitiveOp::StringSpliceRaw => {
            let text = string_value(&args[0])?;
            let start = usize::try_from(int_value(&args[1])?)
                .map_err(|_| VmError::ExpectedInt(args[1].clone()))?;
            let end = usize::try_from(int_value(&args[2])?)
                .map_err(|_| VmError::ExpectedInt(args[2].clone()))?;
            let insert = string_value(&args[3])?;
            text.splice(start, end, insert.clone())
                .map(VmValue::String)
                .ok_or(VmError::ExpectedString(args[0].clone()))
        }
        core_ir::PrimitiveOp::StringConcat => Ok(VmValue::String(StringTree::concat(
            string_value(&args[0])?.clone(),
            string_value(&args[1])?.clone(),
        ))),
        core_ir::PrimitiveOp::IntToString => Ok(VmValue::String(StringTree::from(
            int_value(&args[0])?.to_string(),
        ))),
        core_ir::PrimitiveOp::IntToHex => Ok(VmValue::String(StringTree::from(format!(
            "{:x}",
            int_value(&args[0])?
        )))),
        core_ir::PrimitiveOp::IntToUpperHex => Ok(VmValue::String(StringTree::from(format!(
            "{:X}",
            int_value(&args[0])?
        )))),
        core_ir::PrimitiveOp::FloatToString => Ok(VmValue::String(StringTree::from(
            format_float_value(float_value(&args[0])?),
        ))),
        core_ir::PrimitiveOp::BoolToString => Ok(VmValue::String(StringTree::from(
            bool_value(&args[0])?.to_string(),
        ))),
    }
}
