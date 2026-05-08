use std::collections::BTreeSet;

use crate::cps_ir::{CpsFunction, CpsModule, CpsStmt, CpsTerminator, CpsValueId};

pub fn infer_cps_captures(module: &mut CpsModule) {
    for function in module.functions.iter_mut().chain(&mut module.roots) {
        infer_function_captures(function);
    }
}

fn infer_function_captures(function: &mut CpsFunction) {
    for continuation in &mut function.continuations {
        let local_defs = continuation
            .params
            .iter()
            .copied()
            .chain(continuation_defs(continuation))
            .collect::<BTreeSet<_>>();
        let captures = continuation_uses(continuation)
            .into_iter()
            .filter(|value| !local_defs.contains(value))
            .collect::<Vec<_>>();
        continuation.captures = captures;
    }
}

fn continuation_defs(continuation: &crate::cps_ir::CpsContinuation) -> Vec<CpsValueId> {
    continuation
        .stmts
        .iter()
        .map(|stmt| match stmt {
            CpsStmt::Literal { dest, .. }
            | CpsStmt::Primitive { dest, .. }
            | CpsStmt::DirectCall { dest, .. }
            | CpsStmt::CloneContinuation { dest, .. }
            | CpsStmt::Resume { dest, .. } => *dest,
        })
        .collect()
}

fn continuation_uses(continuation: &crate::cps_ir::CpsContinuation) -> Vec<CpsValueId> {
    let mut uses = BTreeSet::new();
    for stmt in &continuation.stmts {
        match stmt {
            CpsStmt::Literal { .. } => {}
            CpsStmt::Primitive { args, .. } | CpsStmt::DirectCall { args, .. } => {
                uses.extend(args.iter().copied());
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
        }
    }
    match &continuation.terminator {
        CpsTerminator::Return(value) => {
            uses.insert(*value);
        }
        CpsTerminator::Continue { args, .. } => {
            uses.extend(args.iter().copied());
        }
        CpsTerminator::Branch { cond, .. } => {
            uses.insert(*cond);
        }
        CpsTerminator::Perform { payload, .. } => {
            uses.insert(*payload);
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
