//! Normalize effectful direct calls into explicit CPS call terminators.
//!
//! A `DirectCall` statement keeps the caller's post-call work on the host
//! stack. That is fine for pure calls, but effectful callees need the post-call
//! continuation to be represented as a CPS continuation so performs and
//! non-local handler returns can capture it in the return-frame protocol.

use std::collections::HashSet;

use crate::cps_ir::{
    CpsContinuation, CpsContinuationId, CpsFunction, CpsModule, CpsStmt, CpsTerminator,
};

pub fn reify_effectful_direct_calls(module: &mut CpsModule) -> usize {
    let effectful_functions = effectful_function_names(module);
    let mut rewritten = 0;
    for function in module.functions.iter_mut().chain(&mut module.roots) {
        rewritten += reify_effectful_direct_calls_in_function(function, &effectful_functions);
    }
    rewritten
}

fn reify_effectful_direct_calls_in_function(
    function: &mut CpsFunction,
    effectful_functions: &HashSet<String>,
) -> usize {
    let mut next_continuation = next_continuation_id(function);
    let mut rewritten = 0;
    let mut index = 0;

    while index < function.continuations.len() {
        let Some(split) =
            find_effectful_direct_call(&function.continuations[index], effectful_functions)
        else {
            index += 1;
            continue;
        };
        let suffix_id = next_continuation;
        next_continuation.0 += 1;
        let suffix = split_continuation_at_effectful_call(
            &mut function.continuations[index],
            split,
            suffix_id,
        );
        function.continuations.push(suffix);
        rewritten += 1;
        index += 1;
    }

    rewritten
}

fn split_continuation_at_effectful_call(
    continuation: &mut CpsContinuation,
    split: usize,
    suffix_id: CpsContinuationId,
) -> CpsContinuation {
    let CpsStmt::DirectCall {
        dest, target, args, ..
    } = continuation.stmts[split].clone()
    else {
        unreachable!("split index is selected from a DirectCall statement");
    };
    let suffix_stmts = continuation.stmts.split_off(split + 1);
    continuation.stmts.pop();
    let suffix_terminator = std::mem::replace(
        &mut continuation.terminator,
        CpsTerminator::EffectfulCall {
            target,
            args,
            resume: suffix_id,
        },
    );

    CpsContinuation {
        id: suffix_id,
        params: vec![dest],
        captures: Vec::new(),
        shot_kind: continuation.shot_kind,
        stmts: suffix_stmts,
        terminator: suffix_terminator,
    }
}

fn find_effectful_direct_call(
    continuation: &CpsContinuation,
    effectful_functions: &HashSet<String>,
) -> Option<usize> {
    continuation
        .stmts
        .iter()
        .enumerate()
        .position(|(index, stmt)| {
            matches!(stmt, CpsStmt::DirectCall { target, .. } if effectful_functions.contains(target))
                && !direct_call_result_is_already_forced_thunk(continuation, index)
        })
}

fn direct_call_result_is_already_forced_thunk(
    continuation: &CpsContinuation,
    index: usize,
) -> bool {
    let Some(CpsStmt::DirectCall { dest, .. }) = continuation.stmts.get(index) else {
        return false;
    };
    matches!(
        continuation.stmts.get(index + 1),
        Some(CpsStmt::ForceThunk { thunk, .. }) if thunk == dest
    ) || index + 1 == continuation.stmts.len()
        && matches!(
            continuation.terminator,
            CpsTerminator::EffectfulForce { thunk, .. } if thunk == *dest
        )
}

fn effectful_function_names(module: &CpsModule) -> HashSet<String> {
    let mut effectful = module
        .functions
        .iter()
        .chain(&module.roots)
        .filter(|function| function_has_local_effectful_flow(function))
        .map(|function| function.name.clone())
        .collect::<HashSet<_>>();

    loop {
        let before = effectful.len();
        for function in module.functions.iter().chain(&module.roots) {
            if effectful.contains(&function.name) {
                continue;
            }
            if function_calls_effectful_target(function, &effectful) {
                effectful.insert(function.name.clone());
            }
        }
        if effectful.len() == before {
            return effectful;
        }
    }
}

fn function_has_local_effectful_flow(function: &CpsFunction) -> bool {
    function.continuations.iter().any(|continuation| {
        continuation.stmts.iter().any(stmt_has_local_effectful_flow)
            || terminator_has_local_effectful_flow(&continuation.terminator)
    })
}

fn function_calls_effectful_target(function: &CpsFunction, effectful: &HashSet<String>) -> bool {
    function.continuations.iter().any(|continuation| {
        continuation.stmts.iter().any(
            |stmt| matches!(stmt, CpsStmt::DirectCall { target, .. } if effectful.contains(target)),
        )
    })
}

fn stmt_has_local_effectful_flow(stmt: &CpsStmt) -> bool {
    matches!(
        stmt,
        CpsStmt::ApplyClosure { .. }
            | CpsStmt::Resume { .. }
            | CpsStmt::ResumeWithHandler { .. }
            | CpsStmt::InstallHandler { .. }
            | CpsStmt::UninstallHandler { .. }
    )
}

fn terminator_has_local_effectful_flow(terminator: &CpsTerminator) -> bool {
    matches!(
        terminator,
        CpsTerminator::Perform { .. }
            | CpsTerminator::EffectfulCall { .. }
            | CpsTerminator::EffectfulApply { .. }
            | CpsTerminator::EffectfulForce { .. }
    )
}

fn next_continuation_id(function: &CpsFunction) -> CpsContinuationId {
    CpsContinuationId(
        function
            .continuations
            .iter()
            .map(|continuation| continuation.id.0)
            .max()
            .unwrap_or(0)
            + 1,
    )
}

#[cfg(test)]
mod tests {
    use yulang_typed_ir as typed_ir;

    use crate::cps_ir::{
        CpsContinuation, CpsContinuationId, CpsFunction, CpsHandler, CpsHandlerArm, CpsHandlerId,
        CpsLiteral, CpsModule, CpsShotKind, CpsStmt, CpsTerminator, CpsValueId,
    };

    use super::*;

    #[test]
    fn splits_post_call_work_after_effectful_direct_call() {
        let mut module = CpsModule {
            functions: vec![effectful_function("effectful")],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                continuations: vec![CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::MultiShot,
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("1".to_string()),
                        },
                        CpsStmt::DirectCall {
                            dest: CpsValueId(1),
                            target: "effectful".to_string(),
                            args: Vec::new(),
                            ownership: None,
                        },
                        CpsStmt::Primitive {
                            dest: CpsValueId(2),
                            op: typed_ir::PrimitiveOp::IntAdd,
                            args: vec![CpsValueId(1), CpsValueId(0)],
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(2)),
                }],
                handlers: Vec::new(),
            }],
        };

        assert_eq!(reify_effectful_direct_calls(&mut module), 1);
        let root = &module.roots[0];

        assert_eq!(root.continuations.len(), 2);
        assert!(matches!(
            root.continuations[0].terminator,
            CpsTerminator::EffectfulCall {
                ref target,
                resume: CpsContinuationId(1),
                ..
            } if target == "effectful"
        ));
        assert_eq!(root.continuations[1].params, vec![CpsValueId(1)]);
        assert!(matches!(
            root.continuations[1].stmts.as_slice(),
            [CpsStmt::Primitive {
                dest: CpsValueId(2),
                ..
            }]
        ));
        assert_eq!(
            root.continuations[1].terminator,
            CpsTerminator::Return(CpsValueId(2))
        );
    }

    #[test]
    fn propagates_effectfulness_through_direct_call_chain() {
        let mut module = CpsModule {
            functions: vec![
                effectful_function("leaf"),
                forwarding_function("middle", "leaf"),
            ],
            roots: vec![forwarding_function("root", "middle")],
        };

        assert_eq!(reify_effectful_direct_calls(&mut module), 2);
        assert!(matches!(
            module.functions[1].continuations[0].terminator,
            CpsTerminator::EffectfulCall { ref target, .. } if target == "leaf"
        ));
        assert!(matches!(
            module.roots[0].continuations[0].terminator,
            CpsTerminator::EffectfulCall { ref target, .. } if target == "middle"
        ));
    }

    #[test]
    fn keeps_direct_call_when_result_is_already_effectfully_forced() {
        let mut module = CpsModule {
            functions: vec![effectful_function("effectful")],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                continuations: vec![CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::MultiShot,
                    stmts: vec![CpsStmt::DirectCall {
                        dest: CpsValueId(0),
                        target: "effectful".to_string(),
                        args: Vec::new(),
                        ownership: None,
                    }],
                    terminator: CpsTerminator::EffectfulForce {
                        thunk: CpsValueId(0),
                        resume: CpsContinuationId(1),
                        ownership: None,
                    },
                }],
                handlers: Vec::new(),
            }],
        };

        assert_eq!(reify_effectful_direct_calls(&mut module), 0);
        assert!(matches!(
            module.roots[0].continuations[0].stmts.as_slice(),
            [CpsStmt::DirectCall { target, .. }] if target == "effectful"
        ));
        assert!(matches!(
            module.roots[0].continuations[0].terminator,
            CpsTerminator::EffectfulForce {
                thunk: CpsValueId(0),
                ..
            }
        ));
    }

    #[test]
    fn keeps_direct_call_when_result_is_immediately_forced_by_statement() {
        let mut module = CpsModule {
            functions: vec![effectful_function("effectful")],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                continuations: vec![CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::MultiShot,
                    stmts: vec![
                        CpsStmt::DirectCall {
                            dest: CpsValueId(0),
                            target: "effectful".to_string(),
                            args: Vec::new(),
                            ownership: None,
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(1),
                            thunk: CpsValueId(0),
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(1)),
                }],
                handlers: Vec::new(),
            }],
        };

        assert_eq!(reify_effectful_direct_calls(&mut module), 0);
        assert!(matches!(
            module.roots[0].continuations[0].stmts.as_slice(),
            [
                CpsStmt::DirectCall { target, .. },
                CpsStmt::ForceThunk {
                    thunk: CpsValueId(0),
                    ..
                }
            ] if target == "effectful"
        ));
    }

    fn effectful_function(name: &str) -> CpsFunction {
        let effect = typed_ir::Path::from_name(typed_ir::Name("op".to_string()));
        CpsFunction {
            name: name.to_string(),
            params: Vec::new(),
            entry: CpsContinuationId(0),
            continuations: vec![
                CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::MultiShot,
                    stmts: vec![CpsStmt::Literal {
                        dest: CpsValueId(0),
                        literal: CpsLiteral::Int("1".to_string()),
                    }],
                    terminator: CpsTerminator::Perform {
                        effect: effect.clone(),
                        payload: CpsValueId(0),
                        resume: CpsContinuationId(1),
                        handler: CpsHandlerId(0),
                        blocked: None,
                        ownership: None,
                    },
                },
                CpsContinuation {
                    id: CpsContinuationId(1),
                    params: vec![CpsValueId(1)],
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::MultiShot,
                    stmts: Vec::new(),
                    terminator: CpsTerminator::Return(CpsValueId(1)),
                },
                CpsContinuation {
                    id: CpsContinuationId(2),
                    params: vec![CpsValueId(2), CpsValueId(3)],
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::MultiShot,
                    stmts: Vec::new(),
                    terminator: CpsTerminator::Return(CpsValueId(2)),
                },
            ],
            handlers: vec![CpsHandler {
                id: CpsHandlerId(0),
                arms: vec![CpsHandlerArm {
                    effect,
                    entry: CpsContinuationId(2),
                }],
            }],
        }
    }

    fn forwarding_function(name: &str, target: &str) -> CpsFunction {
        CpsFunction {
            name: name.to_string(),
            params: Vec::new(),
            entry: CpsContinuationId(0),
            continuations: vec![CpsContinuation {
                id: CpsContinuationId(0),
                params: Vec::new(),
                captures: Vec::new(),
                shot_kind: CpsShotKind::MultiShot,
                stmts: vec![CpsStmt::DirectCall {
                    dest: CpsValueId(0),
                    target: target.to_string(),
                    args: Vec::new(),
                    ownership: None,
                }],
                terminator: CpsTerminator::Return(CpsValueId(0)),
            }],
            handlers: Vec::new(),
        }
    }
}
