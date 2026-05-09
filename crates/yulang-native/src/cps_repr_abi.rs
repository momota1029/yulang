//! Backend-facing ABI shape for CPS representation IR.
//!
//! This layer does not choose a concrete machine layout yet. It attaches value
//! lanes to continuation parameters, captured environment slots, and returns so
//! the Cranelift lowering can distinguish plain values from resumption pointers.

use crate::cps_ir::{
    CpsContinuationId, CpsHandlerId, CpsShotKind, CpsStmt, CpsTerminator, CpsValueId,
};
use crate::cps_repr::{
    CpsReprAbiLane, CpsReprContinuation, CpsReprFunction, CpsReprHandler, CpsReprModule,
    analyze_cps_repr_abi_lanes,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprAbiModule {
    pub functions: Vec<CpsReprAbiFunction>,
    pub roots: Vec<CpsReprAbiFunction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprAbiFunction {
    pub name: String,
    pub params: Vec<CpsReprAbiValue>,
    pub entry: CpsContinuationId,
    pub continuations: Vec<CpsReprAbiContinuation>,
    pub handlers: Vec<CpsReprAbiHandler>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprAbiContinuation {
    pub id: CpsContinuationId,
    pub params: Vec<CpsReprAbiValue>,
    pub environment: Vec<CpsReprAbiEnvironmentSlot>,
    pub shot_kind: CpsShotKind,
    pub return_lane: CpsReprAbiLane,
    pub stmts: Vec<CpsStmt>,
    pub terminator: CpsTerminator,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CpsReprAbiValue {
    pub value: CpsValueId,
    pub lane: CpsReprAbiLane,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CpsReprAbiEnvironmentSlot {
    pub index: usize,
    pub value: CpsValueId,
    pub lane: CpsReprAbiLane,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprAbiHandler {
    pub id: CpsHandlerId,
    pub entry: CpsContinuationId,
}

pub fn lower_cps_repr_abi_module(module: &CpsReprModule) -> CpsReprAbiModule {
    let analysis = analyze_cps_repr_abi_lanes(module);
    CpsReprAbiModule {
        functions: module
            .functions
            .iter()
            .map(|function| lower_function(function, &analysis))
            .collect(),
        roots: module
            .roots
            .iter()
            .map(|function| lower_function(function, &analysis))
            .collect(),
    }
}

fn lower_function(
    function: &CpsReprFunction,
    analysis: &crate::cps_repr::CpsReprAbiAnalysis,
) -> CpsReprAbiFunction {
    CpsReprAbiFunction {
        name: function.name.clone(),
        params: function
            .params
            .iter()
            .copied()
            .map(|value| abi_value(function, analysis, value))
            .collect(),
        entry: function.entry,
        continuations: function
            .continuations
            .iter()
            .map(|continuation| lower_continuation(function, analysis, continuation))
            .collect(),
        handlers: function.handlers.iter().map(lower_handler).collect(),
    }
}

fn lower_continuation(
    function: &CpsReprFunction,
    analysis: &crate::cps_repr::CpsReprAbiAnalysis,
    continuation: &CpsReprContinuation,
) -> CpsReprAbiContinuation {
    CpsReprAbiContinuation {
        id: continuation.id,
        params: continuation
            .params
            .iter()
            .copied()
            .map(|value| abi_value(function, analysis, value))
            .collect(),
        environment: continuation
            .environment
            .iter()
            .map(|slot| CpsReprAbiEnvironmentSlot {
                index: slot.index,
                value: slot.value,
                lane: value_lane(function, analysis, slot.value),
            })
            .collect(),
        shot_kind: continuation.shot_kind,
        return_lane: analysis
            .continuation_return_lane(&function.name, continuation.id)
            .unwrap_or(CpsReprAbiLane::Unknown),
        stmts: continuation.stmts.clone(),
        terminator: continuation.terminator.clone(),
    }
}

fn lower_handler(handler: &CpsReprHandler) -> CpsReprAbiHandler {
    CpsReprAbiHandler {
        id: handler.id,
        entry: handler.entry,
    }
}

fn abi_value(
    function: &CpsReprFunction,
    analysis: &crate::cps_repr::CpsReprAbiAnalysis,
    value: CpsValueId,
) -> CpsReprAbiValue {
    CpsReprAbiValue {
        value,
        lane: value_lane(function, analysis, value),
    }
}

fn value_lane(
    function: &CpsReprFunction,
    analysis: &crate::cps_repr::CpsReprAbiAnalysis,
    value: CpsValueId,
) -> CpsReprAbiLane {
    analysis
        .value_lane(&function.name, value)
        .unwrap_or(CpsReprAbiLane::Unknown)
}

#[cfg(test)]
mod tests {
    use yulang_core_ir as core_ir;

    use crate::cps_ir::{CpsFunction, CpsHandler, CpsLiteral, CpsModule};
    use crate::cps_repr::lower_cps_repr_module;

    use super::*;

    #[test]
    fn lowers_resumption_parameter_to_pointer_lane() {
        let effect = core_ir::Path::from_name(core_ir::Name("choose".to_string()));
        let repr = lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![CpsHandler {
                    id: CpsHandlerId(0),
                    effect: effect.clone(),
                    entry: CpsContinuationId(2),
                }],
                continuations: vec![
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("1".to_string()),
                        }],
                        terminator: CpsTerminator::Perform {
                            effect,
                            payload: CpsValueId(0),
                            resume: CpsContinuationId(1),
                            handler: CpsHandlerId(0),
                        },
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(1)],
                        captures: vec![CpsValueId(0)],
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(5),
                                literal: CpsLiteral::Int("0".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(6),
                                op: core_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(1), CpsValueId(5)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(6)),
                    },
                    crate::cps_ir::CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(2), CpsValueId(3)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Resume {
                            dest: CpsValueId(4),
                            resumption: CpsValueId(3),
                            arg: CpsValueId(2),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(4)),
                    },
                ],
            }],
        });

        let abi = lower_cps_repr_abi_module(&repr);
        let handler_cont = abi.roots[0]
            .continuations
            .iter()
            .find(|continuation| continuation.id == CpsContinuationId(2))
            .expect("handler continuation");

        assert_eq!(
            handler_cont.params[1],
            CpsReprAbiValue {
                value: CpsValueId(3),
                lane: CpsReprAbiLane::ResumptionPtr,
            }
        );
        assert_eq!(handler_cont.return_lane, CpsReprAbiLane::ScalarI64);
    }
}
