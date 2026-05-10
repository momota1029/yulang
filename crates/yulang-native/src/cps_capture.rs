use std::collections::{BTreeSet, HashMap};

use crate::cps_ir::{CpsFunction, CpsHandlerEnv, CpsModule, CpsStmt, CpsTerminator, CpsValueId};

pub fn infer_cps_captures(module: &mut CpsModule) {
    for function in module.functions.iter_mut().chain(&mut module.roots) {
        infer_function_captures(function);
        fill_resume_handler_envs(function);
    }
}

fn infer_function_captures(function: &mut CpsFunction) {
    let handler_arm_entries = function
        .handlers
        .iter()
        .map(|handler| {
            (
                handler.id,
                handler.arms.iter().map(|arm| arm.entry).collect::<Vec<_>>(),
            )
        })
        .collect::<HashMap<_, _>>();
    loop {
        let current_captures = function
            .continuations
            .iter()
            .map(|continuation| (continuation.id, continuation.captures.clone()))
            .collect::<HashMap<_, _>>();
        let mut changed = false;
        for continuation in &mut function.continuations {
            let local_defs = continuation
                .params
                .iter()
                .copied()
                .chain(continuation_defs(continuation))
                .collect::<BTreeSet<_>>();
            let captures = continuation_uses(continuation, &current_captures, &handler_arm_entries)
                .into_iter()
                .filter(|value| !local_defs.contains(value))
                .collect::<Vec<_>>();
            if continuation.captures != captures {
                continuation.captures = captures;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

fn fill_resume_handler_envs(function: &mut CpsFunction) {
    let continuation_captures = function
        .continuations
        .iter()
        .map(|continuation| (continuation.id, continuation.captures.clone()))
        .collect::<HashMap<_, _>>();
    let handler_entries = function
        .handlers
        .iter()
        .map(|handler| {
            (
                handler.id,
                handler.arms.iter().map(|arm| arm.entry).collect::<Vec<_>>(),
            )
        })
        .collect::<HashMap<_, _>>();

    for continuation in &mut function.continuations {
        let mut available = continuation
            .params
            .iter()
            .copied()
            .chain(continuation.captures.iter().copied())
            .collect::<BTreeSet<_>>();
        for stmt in &mut continuation.stmts {
            match stmt {
                CpsStmt::ResumeWithHandler { handler, envs, .. }
                | CpsStmt::InstallHandler { handler, envs, .. }
                    if envs.is_empty() =>
                {
                    if let Some(entries) = handler_entries.get(handler) {
                        *envs = entries
                            .iter()
                            .filter_map(|entry| {
                                let captures = continuation_captures.get(entry)?;
                                captures
                                    .iter()
                                    .all(|value| available.contains(value))
                                    .then(|| CpsHandlerEnv {
                                        entry: *entry,
                                        values: captures.clone(),
                                    })
                            })
                            .collect();
                    }
                }
                _ => {}
            }
            available.extend(stmt_defs(stmt));
        }
    }
}

fn continuation_defs(continuation: &crate::cps_ir::CpsContinuation) -> Vec<CpsValueId> {
    continuation.stmts.iter().filter_map(stmt_def).collect()
}

fn stmt_defs(stmt: &CpsStmt) -> Option<CpsValueId> {
    stmt_def(stmt)
}

fn stmt_def(stmt: &CpsStmt) -> Option<CpsValueId> {
    match stmt {
        CpsStmt::Literal { dest, .. }
        | CpsStmt::FreshGuard { dest, .. }
        | CpsStmt::PeekGuard { dest }
        | CpsStmt::FindGuard { dest, .. }
        | CpsStmt::MakeThunk { dest, .. }
        | CpsStmt::MakeClosure { dest, .. }
        | CpsStmt::MakeRecursiveClosure { dest, .. }
        | CpsStmt::ForceThunk { dest, .. }
        | CpsStmt::Tuple { dest, .. }
        | CpsStmt::Record { dest, .. }
        | CpsStmt::Variant { dest, .. }
        | CpsStmt::Select { dest, .. }
        | CpsStmt::TupleGet { dest, .. }
        | CpsStmt::VariantTagEq { dest, .. }
        | CpsStmt::VariantPayload { dest, .. }
        | CpsStmt::Primitive { dest, .. }
        | CpsStmt::DirectCall { dest, .. }
        | CpsStmt::ApplyClosure { dest, .. }
        | CpsStmt::CloneContinuation { dest, .. }
        | CpsStmt::Resume { dest, .. }
        | CpsStmt::ResumeWithHandler { dest, .. } => Some(*dest),
        CpsStmt::InstallHandler { .. } | CpsStmt::UninstallHandler { .. } => None,
    }
}

fn continuation_uses(
    continuation: &crate::cps_ir::CpsContinuation,
    continuation_captures: &HashMap<crate::cps_ir::CpsContinuationId, Vec<CpsValueId>>,
    handler_arm_entries: &HashMap<crate::cps_ir::CpsHandlerId, Vec<crate::cps_ir::CpsContinuationId>>,
) -> Vec<CpsValueId> {
    let mut uses = BTreeSet::new();
    for stmt in &continuation.stmts {
        match stmt {
            CpsStmt::Literal { .. } | CpsStmt::FreshGuard { .. } | CpsStmt::PeekGuard { .. } => {}
            CpsStmt::FindGuard { guard, .. } => {
                uses.insert(*guard);
            }
            CpsStmt::MakeThunk { entry, .. } => {
                uses.extend(
                    continuation_captures
                        .get(entry)
                        .into_iter()
                        .flatten()
                        .copied(),
                );
            }
            CpsStmt::MakeClosure { entry, .. } => {
                uses.extend(
                    continuation_captures
                        .get(entry)
                        .into_iter()
                        .flatten()
                        .copied(),
                );
            }
            CpsStmt::MakeRecursiveClosure { dest, entry } => {
                uses.extend(
                    continuation_captures
                        .get(entry)
                        .into_iter()
                        .flatten()
                        .copied()
                        .filter(|value| value != dest),
                );
            }
            CpsStmt::ForceThunk { thunk, .. } => {
                uses.insert(*thunk);
            }
            CpsStmt::Tuple { items, .. } => {
                uses.extend(items.iter().copied());
            }
            CpsStmt::Record { fields, .. } => {
                uses.extend(fields.iter().map(|field| field.value));
            }
            CpsStmt::Variant { value, .. } => {
                uses.extend(value.iter().copied());
            }
            CpsStmt::Select { base, .. } => {
                uses.insert(*base);
            }
            CpsStmt::TupleGet { tuple, .. } => {
                uses.insert(*tuple);
            }
            CpsStmt::VariantTagEq { variant, .. } | CpsStmt::VariantPayload { variant, .. } => {
                uses.insert(*variant);
            }
            CpsStmt::Primitive { args, .. } | CpsStmt::DirectCall { args, .. } => {
                uses.extend(args.iter().copied());
            }
            CpsStmt::ApplyClosure { closure, arg, .. } => {
                uses.insert(*closure);
                uses.insert(*arg);
            }
            CpsStmt::CloneContinuation { source, .. } => {
                uses.insert(*source);
            }
            CpsStmt::Resume {
                resumption, arg, ..
            } => {
                uses.insert(*resumption);
                uses.insert(*arg);
            }
            CpsStmt::ResumeWithHandler {
                resumption,
                arg,
                envs,
                ..
            } => {
                uses.insert(*resumption);
                uses.insert(*arg);
                for env in envs {
                    uses.extend(env.values.iter().copied());
                }
            }
            CpsStmt::InstallHandler { handler, envs, .. } => {
                for env in envs {
                    uses.extend(env.values.iter().copied());
                }
                // The handler arm bodies may capture values that are live
                // *here* but referenced in arm continuations belonging to
                // this function. Propagate those captures so the env-fill
                // pass can package them into InstallHandler.envs.
                if let Some(entries) = handler_arm_entries.get(handler) {
                    for entry in entries {
                        uses.extend(
                            continuation_captures
                                .get(entry)
                                .into_iter()
                                .flatten()
                                .copied(),
                        );
                    }
                }
            }
            CpsStmt::UninstallHandler { .. } => {}
        }
    }
    match &continuation.terminator {
        CpsTerminator::Return(value) => {
            uses.insert(*value);
        }
        CpsTerminator::Continue { target, args } => {
            uses.extend(args.iter().copied());
            uses.extend(
                continuation_captures
                    .get(target)
                    .into_iter()
                    .flatten()
                    .copied(),
            );
        }
        CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        } => {
            uses.insert(*cond);
            uses.extend(
                continuation_captures
                    .get(then_cont)
                    .into_iter()
                    .flatten()
                    .copied(),
            );
            uses.extend(
                continuation_captures
                    .get(else_cont)
                    .into_iter()
                    .flatten()
                    .copied(),
            );
        }
        CpsTerminator::Perform {
            payload,
            resume,
            blocked,
            ..
        } => {
            uses.insert(*payload);
            uses.extend(blocked.iter().copied());
            uses.extend(
                continuation_captures
                    .get(resume)
                    .into_iter()
                    .flatten()
                    .copied(),
            );
        }
    }
    uses.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use yulang_core_ir as core_ir;

    use crate::cps_ir::{
        CpsContinuation, CpsContinuationId, CpsFunction, CpsLiteral, CpsModule, CpsShotKind,
        CpsStmt, CpsTerminator, CpsValueId,
    };
    use crate::cps_validate::validate_cps_module;

    use super::*;

    #[test]
    fn infers_values_captured_from_another_continuation() {
        let mut module = CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
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
                            literal: CpsLiteral::Int("10".to_string()),
                        }],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(1),
                            args: vec![CpsValueId(0)],
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(1)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Primitive {
                            dest: CpsValueId(2),
                            op: core_ir::PrimitiveOp::IntAdd,
                            args: vec![CpsValueId(0), CpsValueId(1)],
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(2)),
                    },
                ],
                handlers: Vec::new(),
            }],
        };

        infer_cps_captures(&mut module);

        assert_eq!(module.roots[0].continuations[0].captures, Vec::new());
        assert_eq!(
            module.roots[0].continuations[1].captures,
            vec![CpsValueId(0)]
        );
        validate_cps_module(&module).expect("valid CPS");
    }
}
