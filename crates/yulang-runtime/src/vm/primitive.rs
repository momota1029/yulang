use super::*;
use crate::runtime::char_class::{is_token_punctuation, is_token_whitespace, is_word_grapheme};

pub(super) fn primitive_arity(op: typed_ir::PrimitiveOp) -> usize {
    match op {
        typed_ir::PrimitiveOp::YadaYada => 0,
        typed_ir::PrimitiveOp::BoolNot
        | typed_ir::PrimitiveOp::ListEmpty
        | typed_ir::PrimitiveOp::ListSingleton
        | typed_ir::PrimitiveOp::ListLen
        | typed_ir::PrimitiveOp::ListViewRaw
        | typed_ir::PrimitiveOp::StringLen
        | typed_ir::PrimitiveOp::StringToBytes
        | typed_ir::PrimitiveOp::BytesLen
        | typed_ir::PrimitiveOp::BytesToUtf8Raw
        | typed_ir::PrimitiveOp::BytesToPath
        | typed_ir::PrimitiveOp::PathToBytes
        | typed_ir::PrimitiveOp::IntToString
        | typed_ir::PrimitiveOp::IntToHex
        | typed_ir::PrimitiveOp::IntToUpperHex
        | typed_ir::PrimitiveOp::FloatToString
        | typed_ir::PrimitiveOp::BoolToString
        | typed_ir::PrimitiveOp::CharToString
        | typed_ir::PrimitiveOp::CharIsWhitespace
        | typed_ir::PrimitiveOp::CharIsPunctuation
        | typed_ir::PrimitiveOp::CharIsWord => 1,
        typed_ir::PrimitiveOp::ListMerge
        | typed_ir::PrimitiveOp::ListIndex
        | typed_ir::PrimitiveOp::ListIndexRange
        | typed_ir::PrimitiveOp::StringIndex
        | typed_ir::PrimitiveOp::StringIndexRange
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
        | typed_ir::PrimitiveOp::StringEq
        | typed_ir::PrimitiveOp::StringConcat
        | typed_ir::PrimitiveOp::CharEq
        | typed_ir::PrimitiveOp::BytesEq
        | typed_ir::PrimitiveOp::BytesConcat
        | typed_ir::PrimitiveOp::BytesIndex
        | typed_ir::PrimitiveOp::BytesIndexRange => 2,
        typed_ir::PrimitiveOp::ListSplice
        | typed_ir::PrimitiveOp::ListIndexRangeRaw
        | typed_ir::PrimitiveOp::StringSplice
        | typed_ir::PrimitiveOp::StringIndexRangeRaw => 3,
        typed_ir::PrimitiveOp::ListSpliceRaw | typed_ir::PrimitiveOp::StringSpliceRaw => 4,
    }
}

pub fn apply_primitive(op: typed_ir::PrimitiveOp, args: &[VmValue]) -> Result<VmValue, VmError> {
    match op {
        typed_ir::PrimitiveOp::YadaYada => Err(VmError::YadaYada),
        typed_ir::PrimitiveOp::BoolNot => Ok(VmValue::Bool(!bool_value(&args[0])?)),
        typed_ir::PrimitiveOp::BoolEq => Ok(VmValue::Bool(
            bool_value(&args[0])? == bool_value(&args[1])?,
        )),
        typed_ir::PrimitiveOp::IntAdd => Ok(VmValue::Int(
            (int_value(&args[0])? + int_value(&args[1])?).to_string(),
        )),
        typed_ir::PrimitiveOp::IntSub => Ok(VmValue::Int(
            (int_value(&args[0])? - int_value(&args[1])?).to_string(),
        )),
        typed_ir::PrimitiveOp::IntMul => Ok(VmValue::Int(
            (int_value(&args[0])? * int_value(&args[1])?).to_string(),
        )),
        typed_ir::PrimitiveOp::IntDiv => Ok(VmValue::Int(
            (int_value(&args[0])? / int_value(&args[1])?).to_string(),
        )),
        typed_ir::PrimitiveOp::IntMod => Ok(VmValue::Int(
            (int_value(&args[0])? % int_value(&args[1])?).to_string(),
        )),
        typed_ir::PrimitiveOp::IntEq => {
            Ok(VmValue::Bool(int_value(&args[0])? == int_value(&args[1])?))
        }
        typed_ir::PrimitiveOp::IntLt => {
            Ok(VmValue::Bool(int_value(&args[0])? < int_value(&args[1])?))
        }
        typed_ir::PrimitiveOp::IntLe => {
            Ok(VmValue::Bool(int_value(&args[0])? <= int_value(&args[1])?))
        }
        typed_ir::PrimitiveOp::IntGt => {
            Ok(VmValue::Bool(int_value(&args[0])? > int_value(&args[1])?))
        }
        typed_ir::PrimitiveOp::IntGe => {
            Ok(VmValue::Bool(int_value(&args[0])? >= int_value(&args[1])?))
        }
        typed_ir::PrimitiveOp::FloatAdd => Ok(VmValue::Float(format_float_value(
            float_value(&args[0])? + float_value(&args[1])?,
        ))),
        typed_ir::PrimitiveOp::FloatSub => Ok(VmValue::Float(format_float_value(
            float_value(&args[0])? - float_value(&args[1])?,
        ))),
        typed_ir::PrimitiveOp::FloatMul => Ok(VmValue::Float(format_float_value(
            float_value(&args[0])? * float_value(&args[1])?,
        ))),
        typed_ir::PrimitiveOp::FloatDiv => Ok(VmValue::Float(format_float_value(
            float_value(&args[0])? / float_value(&args[1])?,
        ))),
        typed_ir::PrimitiveOp::FloatEq => Ok(VmValue::Bool(
            float_value(&args[0])? == float_value(&args[1])?,
        )),
        typed_ir::PrimitiveOp::FloatLt => Ok(VmValue::Bool(
            float_value(&args[0])? < float_value(&args[1])?,
        )),
        typed_ir::PrimitiveOp::FloatLe => Ok(VmValue::Bool(
            float_value(&args[0])? <= float_value(&args[1])?,
        )),
        typed_ir::PrimitiveOp::FloatGt => Ok(VmValue::Bool(
            float_value(&args[0])? > float_value(&args[1])?,
        )),
        typed_ir::PrimitiveOp::FloatGe => Ok(VmValue::Bool(
            float_value(&args[0])? >= float_value(&args[1])?,
        )),
        typed_ir::PrimitiveOp::StringEq => Ok(VmValue::Bool(
            string_value(&args[0])?.to_flat_string() == string_value(&args[1])?.to_flat_string(),
        )),
        typed_ir::PrimitiveOp::ListEmpty => Ok(VmValue::List(ListTree::empty())),
        typed_ir::PrimitiveOp::ListSingleton => {
            Ok(VmValue::List(ListTree::singleton(Rc::new(args[0].clone()))))
        }
        typed_ir::PrimitiveOp::ListLen => Ok(VmValue::Int(list_value(&args[0])?.len().to_string())),
        typed_ir::PrimitiveOp::ListMerge => {
            let left = list_value(&args[0])?;
            let right = list_value(&args[1])?;
            Ok(VmValue::List(ListTree::concat(left.clone(), right.clone())))
        }
        typed_ir::PrimitiveOp::ListIndex => {
            let list = list_value(&args[0])?;
            let index = usize::try_from(int_value(&args[1])?)
                .map_err(|_| VmError::ExpectedInt(args[1].clone()))?;
            list.index(index)
                .map(|value| (*value).clone())
                .ok_or(VmError::ExpectedList(args[0].clone()))
        }
        typed_ir::PrimitiveOp::ListIndexRange => {
            let list = list_value(&args[0])?;
            let (start, end) = normalized_int_range_value(&args[1], list.len())?;
            list.index_range(start, end)
                .map(VmValue::List)
                .ok_or(VmError::ExpectedList(args[0].clone()))
        }
        typed_ir::PrimitiveOp::ListSplice => {
            let list = list_value(&args[0])?;
            let (start, end) = normalized_int_range_value(&args[1], list.len())?;
            let insert = list_value(&args[2])?;
            list.splice(start, end, insert.clone())
                .map(VmValue::List)
                .ok_or(VmError::ExpectedList(args[0].clone()))
        }
        typed_ir::PrimitiveOp::ListIndexRangeRaw => {
            let list = list_value(&args[0])?;
            let start = usize::try_from(int_value(&args[1])?)
                .map_err(|_| VmError::ExpectedInt(args[1].clone()))?;
            let end = usize::try_from(int_value(&args[2])?)
                .map_err(|_| VmError::ExpectedInt(args[2].clone()))?;
            list.index_range(start, end)
                .map(VmValue::List)
                .ok_or(VmError::ExpectedList(args[0].clone()))
        }
        typed_ir::PrimitiveOp::ListSpliceRaw => {
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
        typed_ir::PrimitiveOp::ListViewRaw => match list_value(&args[0])?.view() {
            ListView::Empty => Ok(VmValue::Variant {
                tag: typed_ir::Name("empty".to_string()),
                value: None,
            }),
            ListView::Leaf(single) => Ok(VmValue::Variant {
                tag: typed_ir::Name("leaf".to_string()),
                value: Some(Box::new((*single).clone())),
            }),
            ListView::Node { left, right, .. } => Ok(VmValue::Variant {
                tag: typed_ir::Name("node".to_string()),
                value: Some(Box::new(VmValue::Tuple(vec![
                    VmValue::List(left),
                    VmValue::List(right),
                ]))),
            }),
        },
        typed_ir::PrimitiveOp::StringLen => {
            Ok(VmValue::Int(string_value(&args[0])?.len().to_string()))
        }
        typed_ir::PrimitiveOp::StringIndex => {
            let text = string_value(&args[0])?;
            let index = usize::try_from(int_value(&args[1])?)
                .map_err(|_| VmError::ExpectedInt(args[1].clone()))?;
            text.index(index)
                .map(|ch| VmValue::String(StringTree::from(ch)))
                .ok_or(VmError::ExpectedString(args[0].clone()))
        }
        typed_ir::PrimitiveOp::StringIndexRange => {
            let text = string_value(&args[0])?;
            let (start, end) = normalized_int_range_value(&args[1], text.len())?;
            text.index_range(start, end)
                .map(VmValue::String)
                .ok_or(VmError::ExpectedString(args[0].clone()))
        }
        typed_ir::PrimitiveOp::StringSplice => {
            let text = string_value(&args[0])?;
            let (start, end) = normalized_int_range_value(&args[1], text.len())?;
            let insert = string_value(&args[2])?;
            text.splice(start, end, insert.clone())
                .map(VmValue::String)
                .ok_or(VmError::ExpectedString(args[0].clone()))
        }
        typed_ir::PrimitiveOp::StringIndexRangeRaw => {
            let text = string_value(&args[0])?;
            let start = usize::try_from(int_value(&args[1])?)
                .map_err(|_| VmError::ExpectedInt(args[1].clone()))?;
            let end = usize::try_from(int_value(&args[2])?)
                .map_err(|_| VmError::ExpectedInt(args[2].clone()))?;
            text.index_range(start, end)
                .map(VmValue::String)
                .ok_or(VmError::ExpectedString(args[0].clone()))
        }
        typed_ir::PrimitiveOp::StringSpliceRaw => {
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
        typed_ir::PrimitiveOp::StringConcat => Ok(VmValue::String(StringTree::concat(
            string_value(&args[0])?.clone(),
            string_value(&args[1])?.clone(),
        ))),
        typed_ir::PrimitiveOp::StringToBytes => Ok(VmValue::Bytes(BytesTree::from_bytes(
            string_value(&args[0])?.to_flat_string().as_bytes(),
        ))),
        typed_ir::PrimitiveOp::CharEq => Ok(VmValue::Bool(
            grapheme_value(&args[0])? == grapheme_value(&args[1])?,
        )),
        typed_ir::PrimitiveOp::CharToString => {
            Ok(VmValue::String(StringTree::from(grapheme_value(&args[0])?)))
        }
        typed_ir::PrimitiveOp::CharIsWhitespace => Ok(VmValue::Bool(is_token_whitespace(
            &grapheme_value(&args[0])?,
        ))),
        typed_ir::PrimitiveOp::CharIsPunctuation => Ok(VmValue::Bool(is_token_punctuation(
            &grapheme_value(&args[0])?,
        ))),
        typed_ir::PrimitiveOp::CharIsWord => {
            Ok(VmValue::Bool(is_word_grapheme(&grapheme_value(&args[0])?)))
        }
        typed_ir::PrimitiveOp::BytesLen => {
            Ok(VmValue::Int(bytes_value(&args[0])?.len().to_string()))
        }
        typed_ir::PrimitiveOp::BytesEq => Ok(VmValue::Bool(
            bytes_value(&args[0])?.to_flat_vec() == bytes_value(&args[1])?.to_flat_vec(),
        )),
        typed_ir::PrimitiveOp::BytesConcat => Ok(VmValue::Bytes(BytesTree::concat(
            bytes_value(&args[0])?.clone(),
            bytes_value(&args[1])?.clone(),
        ))),
        typed_ir::PrimitiveOp::BytesIndex => {
            let value = bytes_value(&args[0])?;
            let index = usize::try_from(int_value(&args[1])?)
                .map_err(|_| VmError::ExpectedInt(args[1].clone()))?;
            value
                .index(index)
                .map(|byte| VmValue::Int((byte as i64).to_string()))
                .ok_or(VmError::ExpectedBytes(args[0].clone()))
        }
        typed_ir::PrimitiveOp::BytesIndexRange => {
            let value = bytes_value(&args[0])?;
            let (start, end) = normalized_int_range_value(&args[1], value.len())?;
            value
                .index_range(start, end)
                .map(VmValue::Bytes)
                .ok_or(VmError::ExpectedBytes(args[0].clone()))
        }
        typed_ir::PrimitiveOp::BytesToUtf8Raw => {
            let bytes = bytes_value(&args[0])?.to_flat_vec();
            let valid = match std::str::from_utf8(&bytes) {
                Ok(text) => {
                    return Ok(VmValue::Tuple(vec![
                        VmValue::String(StringTree::from(text.to_string())),
                        VmValue::Int(bytes.len().to_string()),
                    ]));
                }
                Err(error) => error.valid_up_to(),
            };
            let text = std::str::from_utf8(&bytes[..valid]).unwrap_or("");
            Ok(VmValue::Tuple(vec![
                VmValue::String(StringTree::from(text.to_string())),
                VmValue::Int(valid.to_string()),
            ]))
        }
        typed_ir::PrimitiveOp::BytesToPath => Ok(VmValue::Path(Rc::new(path_buf_from_bytes(
            &bytes_value(&args[0])?.to_flat_vec(),
        )))),
        typed_ir::PrimitiveOp::PathToBytes => Ok(VmValue::Bytes(BytesTree::from_bytes(
            &path_buf_bytes(path_value(&args[0])?.as_ref()),
        ))),
        typed_ir::PrimitiveOp::IntToString => Ok(VmValue::String(StringTree::from(
            int_value(&args[0])?.to_string(),
        ))),
        typed_ir::PrimitiveOp::IntToHex => Ok(VmValue::String(StringTree::from(format!(
            "{:x}",
            int_value(&args[0])?
        )))),
        typed_ir::PrimitiveOp::IntToUpperHex => Ok(VmValue::String(StringTree::from(format!(
            "{:X}",
            int_value(&args[0])?
        )))),
        typed_ir::PrimitiveOp::FloatToString => Ok(VmValue::String(StringTree::from(
            format_float_value(float_value(&args[0])?),
        ))),
        typed_ir::PrimitiveOp::BoolToString => Ok(VmValue::String(StringTree::from(
            bool_value(&args[0])?.to_string(),
        ))),
    }
}

#[cfg(unix)]
fn path_buf_from_bytes(bytes: &[u8]) -> PathBuf {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    PathBuf::from(OsString::from_vec(bytes.to_vec()))
}

#[cfg(not(unix))]
fn path_buf_from_bytes(bytes: &[u8]) -> PathBuf {
    PathBuf::from(String::from_utf8_lossy(bytes).into_owned())
}

#[cfg(unix)]
fn path_buf_bytes(path: &PathBuf) -> Vec<u8> {
    use std::os::unix::ffi::OsStrExt;

    path.as_os_str().as_bytes().to_vec()
}

#[cfg(not(unix))]
fn path_buf_bytes(path: &PathBuf) -> Vec<u8> {
    path.to_string_lossy().as_bytes().to_vec()
}
