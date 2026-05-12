use std::collections::HashMap;

use yulang_typed_ir as typed_ir;

use crate::abi::{NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
use crate::control_ir::{NativeLiteral, NativeTerminator, ValueId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeAbiRepr {
    Unit,
    Bool,
    Int,
    Float,
    List(Box<NativeAbiRepr>),
    Tuple(Vec<NativeAbiRepr>),
    Record(Vec<NativeAbiRecordFieldRepr>),
    Variant(Vec<NativeAbiVariantCaseRepr>),
    RuntimeValuePtr(NativeRuntimePtrKind),
    ClosurePtr,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeAbiRecordFieldRepr {
    pub name: typed_ir::Name,
    pub value: NativeAbiRepr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeAbiVariantCaseRepr {
    pub tag: typed_ir::Name,
    pub value: Option<NativeAbiRepr>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeRuntimePtrKind {
    String,
    RuntimeValue,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeAbiValueLane {
    ScalarI64,
    NativeFloat,
    RuntimeValuePtr,
    ClosurePtr,
    Unknown,
}

impl NativeAbiRepr {
    pub fn lane(&self) -> NativeAbiValueLane {
        match self {
            NativeAbiRepr::Unit | NativeAbiRepr::Bool | NativeAbiRepr::Int => {
                NativeAbiValueLane::ScalarI64
            }
            NativeAbiRepr::Float => NativeAbiValueLane::NativeFloat,
            NativeAbiRepr::List(_)
            | NativeAbiRepr::Tuple(_)
            | NativeAbiRepr::Record(_)
            | NativeAbiRepr::Variant(_)
            | NativeAbiRepr::RuntimeValuePtr(_) => NativeAbiValueLane::RuntimeValuePtr,
            NativeAbiRepr::ClosurePtr => NativeAbiValueLane::ClosurePtr,
            NativeAbiRepr::Unknown => NativeAbiValueLane::Unknown,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeAbiReprAnalysis {
    pub functions: HashMap<String, NativeAbiRepr>,
    pub values: HashMap<String, HashMap<ValueId, NativeAbiRepr>>,
}

impl NativeAbiReprAnalysis {
    pub fn function_repr(&self, name: &str) -> Option<&NativeAbiRepr> {
        self.functions.get(name)
    }

    pub fn function_lane(&self, name: &str) -> Option<NativeAbiValueLane> {
        self.function_repr(name).map(NativeAbiRepr::lane)
    }

    pub fn value_repr(&self, function: &str, value: ValueId) -> Option<&NativeAbiRepr> {
        self.values.get(function)?.get(&value)
    }
}

pub type NativeAbiLaneAnalysis = NativeAbiReprAnalysis;

pub fn analyze_abi_value_lanes(module: &NativeAbiModule) -> NativeAbiReprAnalysis {
    analyze_abi_reprs(module)
}

pub fn analyze_abi_reprs(module: &NativeAbiModule) -> NativeAbiReprAnalysis {
    let mut analysis = NativeAbiReprAnalysis {
        functions: module
            .functions
            .iter()
            .chain(&module.roots)
            .map(|function| (function.name.clone(), NativeAbiRepr::Unknown))
            .collect(),
        values: HashMap::new(),
    };
    loop {
        let mut changed = false;
        for function in module.functions.iter().chain(&module.roots) {
            let value_reprs = classify_values(function, &analysis);
            let return_repr = classify_function_return(function, &value_reprs);
            if analysis.values.get(&function.name) != Some(&value_reprs) {
                analysis.values.insert(function.name.clone(), value_reprs);
                changed = true;
            }
            if analysis.functions.get(&function.name) != Some(&return_repr) {
                analysis
                    .functions
                    .insert(function.name.clone(), return_repr);
                changed = true;
            }
        }
        if !changed {
            return analysis;
        }
    }
}

fn classify_values(
    function: &NativeAbiFunction,
    analysis: &NativeAbiReprAnalysis,
) -> HashMap<ValueId, NativeAbiRepr> {
    let mut values = HashMap::new();
    for param in &function.params {
        values.insert(*param, NativeAbiRepr::Unknown);
    }
    for block in &function.blocks {
        for param in &block.params {
            values.entry(*param).or_insert(NativeAbiRepr::Unknown);
        }
        for stmt in &block.stmts {
            classify_stmt(stmt, &mut values, analysis);
        }
    }
    values
}

fn classify_stmt(
    stmt: &NativeAbiStmt,
    values: &mut HashMap<ValueId, NativeAbiRepr>,
    analysis: &NativeAbiReprAnalysis,
) {
    match stmt {
        NativeAbiStmt::Literal { dest, literal } => {
            values.insert(*dest, literal_repr(literal));
        }
        NativeAbiStmt::Primitive { dest, op, args } => {
            values.insert(*dest, primitive_result_repr(*op, args, values));
        }
        NativeAbiStmt::DirectCall { dest, target, .. } => {
            values.insert(
                *dest,
                analysis
                    .function_repr(target)
                    .cloned()
                    .unwrap_or(NativeAbiRepr::Unknown),
            );
        }
        NativeAbiStmt::Tuple { dest, items } => {
            values.insert(
                *dest,
                NativeAbiRepr::Tuple(
                    items
                        .iter()
                        .map(|item| values.get(item).cloned().unwrap_or(NativeAbiRepr::Unknown))
                        .collect(),
                ),
            );
        }
        NativeAbiStmt::Record { dest, base, fields } => {
            let mut repr_fields = base
                .and_then(|base| values.get(&base).cloned())
                .and_then(|repr| match repr {
                    NativeAbiRepr::Record(fields) => Some(fields),
                    _ => None,
                })
                .unwrap_or_default();
            for field in fields {
                repr_fields.retain(|existing| existing.name != field.name);
                repr_fields.push(NativeAbiRecordFieldRepr {
                    name: field.name.clone(),
                    value: values
                        .get(&field.value)
                        .cloned()
                        .unwrap_or(NativeAbiRepr::Unknown),
                });
            }
            values.insert(*dest, NativeAbiRepr::Record(repr_fields));
        }
        NativeAbiStmt::Variant { dest, tag, value } => {
            values.insert(
                *dest,
                NativeAbiRepr::Variant(vec![NativeAbiVariantCaseRepr {
                    tag: tag.clone(),
                    value: value
                        .and_then(|value| values.get(&value).cloned())
                        .or_else(|| value.map(|_| NativeAbiRepr::Unknown)),
                }]),
            );
        }
        NativeAbiStmt::Select { dest, base, field } => {
            values.insert(
                *dest,
                record_field_repr(
                    values.get(base).cloned().unwrap_or(NativeAbiRepr::Unknown),
                    field,
                ),
            );
        }
        NativeAbiStmt::TupleGet { dest, tuple, index } => {
            values.insert(
                *dest,
                tuple_item_repr(
                    values.get(tuple).cloned().unwrap_or(NativeAbiRepr::Unknown),
                    *index,
                ),
            );
        }
        NativeAbiStmt::VariantTagEq { dest, .. } => {
            values.insert(*dest, NativeAbiRepr::Bool);
        }
        NativeAbiStmt::VariantPayload { dest, variant } => {
            values.insert(
                *dest,
                variant_payload_repr(
                    values
                        .get(variant)
                        .cloned()
                        .unwrap_or(NativeAbiRepr::Unknown),
                ),
            );
        }
        NativeAbiStmt::ValueEq { dest, .. } => {
            values.insert(*dest, NativeAbiRepr::Bool);
        }
        NativeAbiStmt::LoadEnv { dest, .. } => {
            values.insert(*dest, NativeAbiRepr::Unknown);
        }
        NativeAbiStmt::AllocateClosure { dest, .. } => {
            values.insert(*dest, NativeAbiRepr::ClosurePtr);
        }
        NativeAbiStmt::IndirectClosureCall { dest, .. } => {
            values.insert(*dest, NativeAbiRepr::Unknown);
        }
    }
}

fn record_field_repr(repr: NativeAbiRepr, field: &typed_ir::Name) -> NativeAbiRepr {
    match repr {
        NativeAbiRepr::Record(fields) => fields
            .into_iter()
            .find(|item| item.name == *field)
            .map(|item| item.value)
            .unwrap_or(NativeAbiRepr::Unknown),
        _ => NativeAbiRepr::Unknown,
    }
}

fn tuple_item_repr(repr: NativeAbiRepr, index: usize) -> NativeAbiRepr {
    match repr {
        NativeAbiRepr::Tuple(items) => items.get(index).cloned().unwrap_or(NativeAbiRepr::Unknown),
        _ => NativeAbiRepr::Unknown,
    }
}

fn variant_payload_repr(repr: NativeAbiRepr) -> NativeAbiRepr {
    match repr {
        NativeAbiRepr::Variant(cases) => cases
            .into_iter()
            .filter_map(|case| case.value)
            .reduce(merge_reprs)
            .unwrap_or(NativeAbiRepr::Unit),
        _ => NativeAbiRepr::Unknown,
    }
}

fn classify_function_return(
    function: &NativeAbiFunction,
    values: &HashMap<ValueId, NativeAbiRepr>,
) -> NativeAbiRepr {
    let mut return_repr = None;
    for block in &function.blocks {
        if let NativeTerminator::Return(value) = &block.terminator {
            let block_return = values.get(value).cloned().unwrap_or(NativeAbiRepr::Unknown);
            return_repr = Some(match return_repr {
                Some(current) => merge_reprs(current, block_return),
                None => block_return,
            });
        }
    }
    return_repr.unwrap_or(NativeAbiRepr::Unknown)
}

fn merge_reprs(left: NativeAbiRepr, right: NativeAbiRepr) -> NativeAbiRepr {
    if left == right {
        left
    } else {
        NativeAbiRepr::Unknown
    }
}

fn literal_repr(literal: &NativeLiteral) -> NativeAbiRepr {
    match literal {
        NativeLiteral::Int(_) => NativeAbiRepr::Int,
        NativeLiteral::Float(_) => NativeAbiRepr::Float,
        NativeLiteral::String(_) => NativeAbiRepr::RuntimeValuePtr(NativeRuntimePtrKind::String),
        NativeLiteral::Bool(_) => NativeAbiRepr::Bool,
        NativeLiteral::Unit => NativeAbiRepr::Unit,
    }
}

fn primitive_result_repr(
    op: typed_ir::PrimitiveOp,
    args: &[ValueId],
    values: &HashMap<ValueId, NativeAbiRepr>,
) -> NativeAbiRepr {
    use typed_ir::PrimitiveOp;
    match op {
        PrimitiveOp::BoolNot
        | PrimitiveOp::BoolEq
        | PrimitiveOp::IntEq
        | PrimitiveOp::IntLt
        | PrimitiveOp::IntLe
        | PrimitiveOp::IntGt
        | PrimitiveOp::IntGe
        | PrimitiveOp::FloatEq
        | PrimitiveOp::FloatLt
        | PrimitiveOp::FloatLe
        | PrimitiveOp::FloatGt
        | PrimitiveOp::FloatGe => NativeAbiRepr::Bool,
        PrimitiveOp::IntAdd | PrimitiveOp::IntSub | PrimitiveOp::IntMul | PrimitiveOp::IntDiv => {
            NativeAbiRepr::Int
        }
        PrimitiveOp::FloatAdd
        | PrimitiveOp::FloatSub
        | PrimitiveOp::FloatMul
        | PrimitiveOp::FloatDiv => NativeAbiRepr::Float,
        PrimitiveOp::ListLen => NativeAbiRepr::Int,
        PrimitiveOp::StringLen => NativeAbiRepr::Int,
        PrimitiveOp::ListEmpty => NativeAbiRepr::List(Box::new(NativeAbiRepr::Unknown)),
        PrimitiveOp::ListSingleton => NativeAbiRepr::List(Box::new(arg_repr(args, values, 0))),
        PrimitiveOp::ListMerge => list_with_merged_element_repr(args, values),
        PrimitiveOp::ListIndex => list_element_repr(arg_repr(args, values, 0)),
        PrimitiveOp::ListIndexRange
        | PrimitiveOp::ListSplice
        | PrimitiveOp::ListIndexRangeRaw
        | PrimitiveOp::ListSpliceRaw => list_with_element_repr(arg_repr(args, values, 0)),
        PrimitiveOp::ListViewRaw => NativeAbiRepr::Variant(vec![
            NativeAbiVariantCaseRepr {
                tag: typed_ir::Name("empty".to_string()),
                value: None,
            },
            NativeAbiVariantCaseRepr {
                tag: typed_ir::Name("leaf".to_string()),
                value: Some(list_element_repr(arg_repr(args, values, 0))),
            },
            NativeAbiVariantCaseRepr {
                tag: typed_ir::Name("node".to_string()),
                value: Some(NativeAbiRepr::Tuple(vec![
                    list_with_element_repr(arg_repr(args, values, 0)),
                    list_with_element_repr(arg_repr(args, values, 0)),
                ])),
            },
        ]),
        PrimitiveOp::StringIndex
        | PrimitiveOp::StringIndexRange
        | PrimitiveOp::StringSplice
        | PrimitiveOp::StringIndexRangeRaw
        | PrimitiveOp::StringSpliceRaw
        | PrimitiveOp::StringConcat
        | PrimitiveOp::IntToString
        | PrimitiveOp::IntToHex
        | PrimitiveOp::IntToUpperHex
        | PrimitiveOp::FloatToString
        | PrimitiveOp::BoolToString => NativeAbiRepr::RuntimeValuePtr(NativeRuntimePtrKind::String),
    }
}

fn arg_repr(
    args: &[ValueId],
    values: &HashMap<ValueId, NativeAbiRepr>,
    index: usize,
) -> NativeAbiRepr {
    args.get(index)
        .and_then(|value| values.get(value))
        .cloned()
        .unwrap_or(NativeAbiRepr::Unknown)
}

fn list_element_repr(repr: NativeAbiRepr) -> NativeAbiRepr {
    match repr {
        NativeAbiRepr::List(element) => *element,
        _ => NativeAbiRepr::Unknown,
    }
}

fn list_with_element_repr(repr: NativeAbiRepr) -> NativeAbiRepr {
    match repr {
        NativeAbiRepr::List(element) => NativeAbiRepr::List(element),
        _ => NativeAbiRepr::List(Box::new(NativeAbiRepr::Unknown)),
    }
}

fn list_with_merged_element_repr(
    args: &[ValueId],
    values: &HashMap<ValueId, NativeAbiRepr>,
) -> NativeAbiRepr {
    let left = list_element_repr(arg_repr(args, values, 0));
    let right = list_element_repr(arg_repr(args, values, 1));
    NativeAbiRepr::List(Box::new(merge_reprs(left, right)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::{NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
    use crate::control_ir::BlockId;

    #[test]
    fn classifies_scalar_function() {
        let module = NativeAbiModule {
            functions: Vec::new(),
            roots: vec![root_with_stmt(
                NativeAbiStmt::Literal {
                    dest: ValueId(0),
                    literal: NativeLiteral::Int("42".to_string()),
                },
                ValueId(0),
            )],
        };

        let analysis = analyze_abi_reprs(&module);

        assert_eq!(analysis.function_repr("root"), Some(&NativeAbiRepr::Int));
        assert_eq!(
            analysis.function_lane("root"),
            Some(NativeAbiValueLane::ScalarI64)
        );
    }

    #[test]
    fn classifies_float_as_native_float() {
        let module = NativeAbiModule {
            functions: Vec::new(),
            roots: vec![root_with_stmt(
                NativeAbiStmt::Literal {
                    dest: ValueId(0),
                    literal: NativeLiteral::Float("1.5".to_string()),
                },
                ValueId(0),
            )],
        };

        let analysis = analyze_abi_reprs(&module);

        assert_eq!(analysis.function_repr("root"), Some(&NativeAbiRepr::Float));
        assert_eq!(
            analysis.function_lane("root"),
            Some(NativeAbiValueLane::NativeFloat)
        );
    }

    #[test]
    fn classifies_string_literal_as_runtime_value() {
        let module = NativeAbiModule {
            functions: Vec::new(),
            roots: vec![root_with_stmt(
                NativeAbiStmt::Literal {
                    dest: ValueId(0),
                    literal: NativeLiteral::String("hello".to_string()),
                },
                ValueId(0),
            )],
        };

        let analysis = analyze_abi_reprs(&module);

        assert_eq!(
            analysis.function_repr("root"),
            Some(&NativeAbiRepr::RuntimeValuePtr(
                NativeRuntimePtrKind::String
            ))
        );
        assert_eq!(
            analysis.function_lane("root"),
            Some(NativeAbiValueLane::RuntimeValuePtr)
        );
    }

    #[test]
    fn propagates_runtime_value_repr_through_direct_call() {
        let module = NativeAbiModule {
            functions: vec![NativeAbiFunction {
                name: "make_text".to_string(),
                params: Vec::new(),
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![NativeAbiStmt::Literal {
                        dest: ValueId(0),
                        literal: NativeLiteral::String("hello".to_string()),
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
                    stmts: vec![NativeAbiStmt::DirectCall {
                        dest: ValueId(0),
                        target: "make_text".to_string(),
                        args: Vec::new(),
                    }],
                    terminator: NativeTerminator::Return(ValueId(0)),
                }],
            }],
        };

        let analysis = analyze_abi_reprs(&module);

        assert_eq!(
            analysis.function_repr("make_text"),
            Some(&NativeAbiRepr::RuntimeValuePtr(
                NativeRuntimePtrKind::String
            ))
        );
        assert_eq!(
            analysis.function_repr("root"),
            Some(&NativeAbiRepr::RuntimeValuePtr(
                NativeRuntimePtrKind::String
            ))
        );
    }

    #[test]
    fn classifies_list_primitive_as_list_pointer() {
        let module = NativeAbiModule {
            functions: Vec::new(),
            roots: vec![root_with_stmt(
                NativeAbiStmt::Primitive {
                    dest: ValueId(0),
                    op: typed_ir::PrimitiveOp::ListEmpty,
                    args: Vec::new(),
                },
                ValueId(0),
            )],
        };

        let analysis = analyze_abi_reprs(&module);

        assert_eq!(
            analysis.function_repr("root"),
            Some(&NativeAbiRepr::List(Box::new(NativeAbiRepr::Unknown)))
        );
        assert_eq!(
            analysis.function_lane("root"),
            Some(NativeAbiValueLane::RuntimeValuePtr)
        );
    }

    #[test]
    fn propagates_list_element_repr_from_singleton_and_index() {
        let module = NativeAbiModule {
            functions: Vec::new(),
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
                            literal: NativeLiteral::Int("42".to_string()),
                        },
                        NativeAbiStmt::Primitive {
                            dest: ValueId(1),
                            op: typed_ir::PrimitiveOp::ListSingleton,
                            args: vec![ValueId(0)],
                        },
                        NativeAbiStmt::Literal {
                            dest: ValueId(2),
                            literal: NativeLiteral::Int("0".to_string()),
                        },
                        NativeAbiStmt::Primitive {
                            dest: ValueId(3),
                            op: typed_ir::PrimitiveOp::ListIndex,
                            args: vec![ValueId(1), ValueId(2)],
                        },
                    ],
                    terminator: NativeTerminator::Return(ValueId(3)),
                }],
            }],
        };

        let analysis = analyze_abi_reprs(&module);

        assert_eq!(
            analysis.value_repr("root", ValueId(1)),
            Some(&NativeAbiRepr::List(Box::new(NativeAbiRepr::Int)))
        );
        assert_eq!(analysis.function_repr("root"), Some(&NativeAbiRepr::Int));
    }

    #[test]
    fn classifies_hosted_closure_call_as_unknown_result() {
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

        let analysis = analyze_abi_reprs(&module);

        assert_eq!(
            analysis.function_lane("add_capture"),
            Some(NativeAbiValueLane::Unknown)
        );
        assert_eq!(
            analysis.function_repr("root"),
            Some(&NativeAbiRepr::Unknown)
        );
        assert_eq!(
            analysis.value_repr("root", ValueId(1)),
            Some(&NativeAbiRepr::ClosurePtr)
        );
    }

    fn root_with_stmt(stmt: NativeAbiStmt, ret: ValueId) -> NativeAbiFunction {
        NativeAbiFunction {
            name: "root".to_string(),
            params: Vec::new(),
            environment_slots: 0,
            blocks: vec![NativeAbiBlock {
                id: BlockId(0),
                params: Vec::new(),
                stmts: vec![stmt],
                terminator: NativeTerminator::Return(ret),
            }],
        }
    }
}
