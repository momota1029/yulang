use std::collections::{HashMap, HashSet};

use yulang_core_ir as core_ir;

use crate::abi::{NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
use crate::control_ir::{NativeLiteral, NativeTerminator};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeAbiValueLane {
    ScalarI64,
    RuntimeValuePtr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeAbiLaneAnalysis {
    pub functions: HashMap<String, NativeAbiValueLane>,
}

impl NativeAbiLaneAnalysis {
    pub fn function_lane(&self, name: &str) -> Option<NativeAbiValueLane> {
        self.functions.get(name).copied()
    }
}

pub fn analyze_abi_value_lanes(module: &NativeAbiModule) -> NativeAbiLaneAnalysis {
    let functions = module
        .functions
        .iter()
        .chain(&module.roots)
        .map(|function| (function.name.clone(), NativeAbiValueLane::ScalarI64))
        .collect::<HashMap<_, _>>();
    let mut analysis = NativeAbiLaneAnalysis { functions };
    loop {
        let mut changed = false;
        for function in module.functions.iter().chain(&module.roots) {
            let lane = classify_function(function, &analysis);
            if analysis.functions.get(&function.name).copied() != Some(lane) {
                analysis.functions.insert(function.name.clone(), lane);
                changed = true;
            }
        }
        if !changed {
            return analysis;
        }
    }
}

fn classify_function(
    function: &NativeAbiFunction,
    analysis: &NativeAbiLaneAnalysis,
) -> NativeAbiValueLane {
    if function.environment_slots != 0 {
        return NativeAbiValueLane::RuntimeValuePtr;
    }
    for block in &function.blocks {
        for stmt in &block.stmts {
            if stmt_lane(stmt, analysis) == NativeAbiValueLane::RuntimeValuePtr {
                return NativeAbiValueLane::RuntimeValuePtr;
            }
        }
        if terminator_uses_runtime_value(&block.terminator, analysis, function) {
            return NativeAbiValueLane::RuntimeValuePtr;
        }
    }
    NativeAbiValueLane::ScalarI64
}

fn stmt_lane(stmt: &NativeAbiStmt, analysis: &NativeAbiLaneAnalysis) -> NativeAbiValueLane {
    match stmt {
        NativeAbiStmt::Literal { literal, .. } => literal_lane(literal),
        NativeAbiStmt::Primitive { op, .. } => primitive_lane(*op),
        NativeAbiStmt::DirectCall { target, .. } => analysis
            .function_lane(target)
            .unwrap_or(NativeAbiValueLane::RuntimeValuePtr),
        NativeAbiStmt::LoadEnv { .. }
        | NativeAbiStmt::AllocateClosure { .. }
        | NativeAbiStmt::IndirectClosureCall { .. } => NativeAbiValueLane::RuntimeValuePtr,
    }
}

fn literal_lane(literal: &NativeLiteral) -> NativeAbiValueLane {
    match literal {
        NativeLiteral::Int(_) | NativeLiteral::Bool(_) | NativeLiteral::Unit => {
            NativeAbiValueLane::ScalarI64
        }
        NativeLiteral::Float(_) | NativeLiteral::String(_) => NativeAbiValueLane::RuntimeValuePtr,
    }
}

fn primitive_lane(op: core_ir::PrimitiveOp) -> NativeAbiValueLane {
    use core_ir::PrimitiveOp;
    match op {
        PrimitiveOp::BoolNot
        | PrimitiveOp::BoolEq
        | PrimitiveOp::IntAdd
        | PrimitiveOp::IntSub
        | PrimitiveOp::IntMul
        | PrimitiveOp::IntDiv
        | PrimitiveOp::IntEq
        | PrimitiveOp::IntLt
        | PrimitiveOp::IntLe
        | PrimitiveOp::IntGt
        | PrimitiveOp::IntGe => NativeAbiValueLane::ScalarI64,
        PrimitiveOp::FloatAdd
        | PrimitiveOp::FloatSub
        | PrimitiveOp::FloatMul
        | PrimitiveOp::FloatDiv
        | PrimitiveOp::FloatEq
        | PrimitiveOp::FloatLt
        | PrimitiveOp::FloatLe
        | PrimitiveOp::FloatGt
        | PrimitiveOp::FloatGe
        | PrimitiveOp::ListEmpty
        | PrimitiveOp::ListSingleton
        | PrimitiveOp::ListLen
        | PrimitiveOp::ListMerge
        | PrimitiveOp::ListIndex
        | PrimitiveOp::ListIndexRange
        | PrimitiveOp::ListSplice
        | PrimitiveOp::ListIndexRangeRaw
        | PrimitiveOp::ListSpliceRaw
        | PrimitiveOp::ListViewRaw
        | PrimitiveOp::StringLen
        | PrimitiveOp::StringIndex
        | PrimitiveOp::StringIndexRange
        | PrimitiveOp::StringSplice
        | PrimitiveOp::StringIndexRangeRaw
        | PrimitiveOp::StringSpliceRaw
        | PrimitiveOp::StringConcat
        | PrimitiveOp::IntToString
        | PrimitiveOp::IntToHex
        | PrimitiveOp::IntToUpperHex
        | PrimitiveOp::FloatToString
        | PrimitiveOp::BoolToString => NativeAbiValueLane::RuntimeValuePtr,
    }
}

fn terminator_uses_runtime_value(
    terminator: &NativeTerminator,
    analysis: &NativeAbiLaneAnalysis,
    function: &NativeAbiFunction,
) -> bool {
    let value_defs = runtime_value_defs(function, analysis);
    terminator_values(terminator)
        .into_iter()
        .any(|value| value_defs.contains(&value))
}

fn runtime_value_defs(
    function: &NativeAbiFunction,
    analysis: &NativeAbiLaneAnalysis,
) -> HashSet<crate::control_ir::ValueId> {
    let mut values = HashSet::new();
    for block in &function.blocks {
        for stmt in &block.stmts {
            if stmt_lane(stmt, analysis) == NativeAbiValueLane::RuntimeValuePtr {
                match stmt {
                    NativeAbiStmt::Literal { dest, .. }
                    | NativeAbiStmt::Primitive { dest, .. }
                    | NativeAbiStmt::DirectCall { dest, .. }
                    | NativeAbiStmt::LoadEnv { dest, .. }
                    | NativeAbiStmt::AllocateClosure { dest, .. }
                    | NativeAbiStmt::IndirectClosureCall { dest, .. } => {
                        values.insert(*dest);
                    }
                }
            }
        }
    }
    values
}

fn terminator_values(terminator: &NativeTerminator) -> Vec<crate::control_ir::ValueId> {
    match terminator {
        NativeTerminator::Return(value) => vec![*value],
        NativeTerminator::Jump { args, .. } => args.clone(),
        NativeTerminator::Branch { cond, .. } => vec![*cond],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::{NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
    use crate::control_ir::{BlockId, ValueId};

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

        let lanes = analyze_abi_value_lanes(&module);

        assert_eq!(
            lanes.function_lane("root"),
            Some(NativeAbiValueLane::ScalarI64)
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

        let lanes = analyze_abi_value_lanes(&module);

        assert_eq!(
            lanes.function_lane("root"),
            Some(NativeAbiValueLane::RuntimeValuePtr)
        );
    }

    #[test]
    fn propagates_runtime_value_lane_through_direct_call() {
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

        let lanes = analyze_abi_value_lanes(&module);

        assert_eq!(
            lanes.function_lane("make_text"),
            Some(NativeAbiValueLane::RuntimeValuePtr)
        );
        assert_eq!(
            lanes.function_lane("root"),
            Some(NativeAbiValueLane::RuntimeValuePtr)
        );
    }

    #[test]
    fn classifies_list_primitive_as_runtime_value() {
        let module = NativeAbiModule {
            functions: Vec::new(),
            roots: vec![root_with_stmt(
                NativeAbiStmt::Primitive {
                    dest: ValueId(0),
                    op: core_ir::PrimitiveOp::ListEmpty,
                    args: Vec::new(),
                },
                ValueId(0),
            )],
        };

        let lanes = analyze_abi_value_lanes(&module);

        assert_eq!(
            lanes.function_lane("root"),
            Some(NativeAbiValueLane::RuntimeValuePtr)
        );
    }

    #[test]
    fn classifies_hosted_closure_call_as_runtime_value_lane() {
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

        let lanes = analyze_abi_value_lanes(&module);

        assert_eq!(
            lanes.function_lane("add_capture"),
            Some(NativeAbiValueLane::RuntimeValuePtr)
        );
        assert_eq!(
            lanes.function_lane("root"),
            Some(NativeAbiValueLane::RuntimeValuePtr)
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
