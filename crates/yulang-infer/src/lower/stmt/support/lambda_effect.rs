use std::collections::HashSet;

use crate::ast::expr::{CatchArmKind, ExprKind, RecordSpread, TypedExpr, TypedStmt};
use crate::ids::{DefId, TypeVar};
use crate::lower::LowerState;
use crate::types::{Neg, Pos};

pub(crate) fn direct_param_source_eff_tv(body: &TypedExpr, param_def: DefId) -> Option<TypeVar> {
    match &body.kind {
        ExprKind::Lit(_) | ExprKind::PrimitiveOp(_) | ExprKind::Ref(_) => None,
        ExprKind::Coerce { expr, .. } => direct_param_source_eff_tv(expr, param_def),
        ExprKind::Tuple(items) => items
            .iter()
            .find_map(|item| direct_param_source_eff_tv(item, param_def)),
        ExprKind::Record { fields, spread } => fields
            .iter()
            .find_map(|(_, field)| direct_param_source_eff_tv(field, param_def))
            .or_else(|| {
                spread.as_ref().and_then(|spread| match spread {
                    RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                        direct_param_source_eff_tv(expr, param_def)
                    }
                })
            }),
        ExprKind::PolyVariant(_, items) => items
            .iter()
            .find_map(|item| direct_param_source_eff_tv(item, param_def)),
        ExprKind::Block(block) => block
            .stmts
            .iter()
            .find_map(|stmt| match stmt {
                TypedStmt::Let(_, expr) | TypedStmt::Expr(expr) => {
                    direct_param_source_eff_tv(expr, param_def)
                }
                TypedStmt::Module(_, block) => block
                    .tail
                    .as_deref()
                    .and_then(|tail| direct_param_source_eff_tv(tail, param_def)),
            })
            .or_else(|| {
                block
                    .tail
                    .as_deref()
                    .and_then(|tail| direct_param_source_eff_tv(tail, param_def))
            }),
        ExprKind::Match(scrutinee, arms) => direct_param_source_eff_tv(scrutinee, param_def)
            .or_else(|| {
                arms.iter().find_map(|arm| {
                    arm.guard
                        .as_ref()
                        .and_then(|guard| direct_param_source_eff_tv(guard, param_def))
                        .or_else(|| direct_param_source_eff_tv(&arm.body, param_def))
                })
            }),
        ExprKind::App { callee, arg, .. } => match &arg.kind {
            ExprKind::Var(def) if *def == param_def => Some(arg.eff),
            _ if matches!(&callee.kind, ExprKind::Var(def) if *def == param_def) => Some(body.eff),
            _ => direct_param_source_eff_tv(callee, param_def)
                .or_else(|| direct_param_source_eff_tv(arg, param_def)),
        },
        ExprKind::Select { recv, .. } => match &recv.kind {
            ExprKind::Var(def) if *def == param_def => Some(recv.eff),
            _ => direct_param_source_eff_tv(recv, param_def),
        },
        ExprKind::RefSet { reference, value } => direct_param_source_eff_tv(reference, param_def)
            .or_else(|| direct_param_source_eff_tv(value, param_def)),
        ExprKind::Catch(comp, _) if matches!(&comp.kind, ExprKind::Var(def) if *def == param_def) => {
            Some(comp.eff)
        }
        ExprKind::Catch(comp, arms) => direct_param_source_eff_tv(comp, param_def).or_else(|| {
            arms.iter().find_map(|arm| {
                arm.guard
                    .as_ref()
                    .and_then(|guard| direct_param_source_eff_tv(guard, param_def))
                    .or_else(|| match &arm.kind {
                        CatchArmKind::Value(_, body) | CatchArmKind::Effect { body, .. } => {
                            direct_param_source_eff_tv(body, param_def)
                        }
                    })
            })
        }),
        ExprKind::Lam(def, body) if *def != param_def => {
            direct_param_source_eff_tv(body, param_def)
        }
        ExprKind::Lam(_, _) | ExprKind::PackForall(_, _) => None,
        ExprKind::Var(def) if *def == param_def => Some(body.eff),
        ExprKind::Var(_) => None,
    }
}

pub(crate) fn lambda_expr_eff_tv(
    state: &mut LowerState,
    body: &TypedExpr,
    local_defs: &[DefId],
) -> TypeVar {
    let local_defs = local_defs.iter().copied().collect::<HashSet<_>>();
    let mut captured = HashSet::new();
    collect_lambda_capture_effs(state, body, &local_defs, &mut captured);
    if captured.is_empty() {
        return state.fresh_exact_pure_eff_tv();
    }
    let eff = state.fresh_tv();
    for captured_eff in captured {
        state.infer.constrain(Pos::Var(captured_eff), Neg::Var(eff));
    }
    eff
}

fn collect_lambda_capture_effs(
    state: &LowerState,
    expr: &TypedExpr,
    local_defs: &HashSet<DefId>,
    out: &mut HashSet<TypeVar>,
) {
    match &expr.kind {
        ExprKind::Lit(_) | ExprKind::PrimitiveOp(_) | ExprKind::Ref(_) => {}
        ExprKind::Var(def) => {
            if !local_defs.contains(def) {
                if let Some(&eff_tv) = state.def_eff_tvs.get(def) {
                    out.insert(eff_tv);
                }
            }
        }
        ExprKind::App { callee, arg, .. } => {
            collect_lambda_capture_effs(state, callee, local_defs, out);
            collect_lambda_capture_effs(state, arg, local_defs, out);
        }
        ExprKind::RefSet { reference, value } => {
            collect_lambda_capture_effs(state, reference, local_defs, out);
            collect_lambda_capture_effs(state, value, local_defs, out);
        }
        ExprKind::Lam(_, _) | ExprKind::PackForall(_, _) => {}
        ExprKind::Tuple(items) => {
            for item in items {
                collect_lambda_capture_effs(state, item, local_defs, out);
            }
        }
        ExprKind::Record { fields, spread } => {
            for (_, field) in fields {
                collect_lambda_capture_effs(state, field, local_defs, out);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                        collect_lambda_capture_effs(state, expr, local_defs, out);
                    }
                }
            }
        }
        ExprKind::PolyVariant(_, items) => {
            for item in items {
                collect_lambda_capture_effs(state, item, local_defs, out);
            }
        }
        ExprKind::Select { recv, .. } => {
            collect_lambda_capture_effs(state, recv, local_defs, out);
        }
        ExprKind::Match(scrutinee, arms) => {
            collect_lambda_capture_effs(state, scrutinee, local_defs, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_lambda_capture_effs(state, guard, local_defs, out);
                }
                collect_lambda_capture_effs(state, &arm.body, local_defs, out);
            }
        }
        ExprKind::Catch(comp, arms) => {
            collect_lambda_capture_effs(state, comp, local_defs, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_lambda_capture_effs(state, guard, local_defs, out);
                }
                match &arm.kind {
                    CatchArmKind::Value(_, body) | CatchArmKind::Effect { body, .. } => {
                        collect_lambda_capture_effs(state, body, local_defs, out);
                    }
                }
            }
        }
        ExprKind::Block(block) => {
            for stmt in &block.stmts {
                match stmt {
                    TypedStmt::Let(_, expr) | TypedStmt::Expr(expr) => {
                        collect_lambda_capture_effs(state, expr, local_defs, out);
                    }
                    TypedStmt::Module(_, block) => {
                        if let Some(tail) = &block.tail {
                            collect_lambda_capture_effs(state, tail, local_defs, out);
                        }
                    }
                }
            }
            if let Some(tail) = &block.tail {
                collect_lambda_capture_effs(state, tail, local_defs, out);
            }
        }
        ExprKind::Coerce { expr, .. } => {
            collect_lambda_capture_effs(state, expr, local_defs, out);
        }
    }
}
