//! Optional structural invariant checks for finalized runtime IR.
//!
//! These checks are gated by `YULANG_FINALIZE_DEBUG_INVARIANTS`; they are a
//! developer diagnostic pass, not part of normal monomorphization.

use yulang_runtime_ir::{
    FinalizedExpr as Expr, FinalizedExprKind as ExprKind, FinalizedModule as Module,
};

pub(crate) fn validate(module: &Module) {
    if std::env::var_os("YULANG_FINALIZE_DEBUG_INVARIANTS").is_none() {
        return;
    }
    for binding in &module.bindings {
        debug_expr_invariants(&binding.body, format!("binding {:?}", binding.name));
    }
    for (index, expr) in module.root_exprs.iter().enumerate() {
        debug_expr_invariants(expr, format!("root #{index}"));
    }
}

fn debug_expr_invariants(expr: &Expr, context: String) {
    match &expr.kind {
        ExprKind::Handle {
            body,
            handler,
            arms,
            ..
        } => {
            if !handler.consumes.is_empty()
                && !matches!(body.ty, yulang_runtime_ir::RuntimeType::Thunk { .. })
            {
                eprintln!(
                    "FINALIZE invariant: effectful handle body is not thunk at {context}: consumes={:?}, body_ty={:?}",
                    handler.consumes, body.ty
                );
            }
            debug_expr_invariants(body, format!("{context}/handle.body"));
            for (index, arm) in arms.iter().enumerate() {
                debug_expr_invariants(&arm.body, format!("{context}/handle.arm[{index}].body"));
                if let Some(guard) = &arm.guard {
                    debug_expr_invariants(guard, format!("{context}/handle.arm[{index}].guard"));
                }
            }
        }
        ExprKind::AddId { thunk, .. } => {
            if !matches!(thunk.ty, yulang_runtime_ir::RuntimeType::Thunk { .. }) {
                eprintln!(
                    "FINALIZE invariant: add_id input is not thunk at {context}: thunk_ty={:?}",
                    thunk.ty
                );
            }
            debug_expr_invariants(thunk, format!("{context}/add_id"));
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => {
            debug_expr_invariants(body, context);
        }
        ExprKind::Apply { callee, arg, .. } => {
            debug_expr_invariants(callee, format!("{context}/apply.callee"));
            debug_expr_invariants(arg, format!("{context}/apply.arg"));
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            debug_expr_invariants(cond, format!("{context}/if.cond"));
            debug_expr_invariants(then_branch, format!("{context}/if.then"));
            debug_expr_invariants(else_branch, format!("{context}/if.else"));
        }
        ExprKind::Tuple(items) => {
            for (index, item) in items.iter().enumerate() {
                debug_expr_invariants(item, format!("{context}/tuple[{index}]"));
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                debug_expr_invariants(&field.value, format!("{context}/record.{}", field.name.0));
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(expr)
                    | yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(expr) => {
                        debug_expr_invariants(expr, format!("{context}/record.spread"));
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                debug_expr_invariants(value, format!("{context}/variant"));
            }
        }
        ExprKind::Select { base, .. } => {
            debug_expr_invariants(base, format!("{context}/select.base"));
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            debug_expr_invariants(scrutinee, format!("{context}/match.scrutinee"));
            for (index, arm) in arms.iter().enumerate() {
                debug_expr_invariants(&arm.body, format!("{context}/match.arm[{index}].body"));
                if let Some(guard) = &arm.guard {
                    debug_expr_invariants(guard, format!("{context}/match.arm[{index}].guard"));
                }
            }
        }
        ExprKind::Block { stmts, tail } => {
            for (index, stmt) in stmts.iter().enumerate() {
                match stmt {
                    yulang_runtime_ir::FinalizedStmt::Let { value, .. } => {
                        debug_expr_invariants(value, format!("{context}/stmt[{index}].let"));
                    }
                    yulang_runtime_ir::FinalizedStmt::Expr(expr)
                    | yulang_runtime_ir::FinalizedStmt::Module { body: expr, .. } => {
                        debug_expr_invariants(expr, format!("{context}/stmt[{index}]"));
                    }
                }
            }
            if let Some(tail) = tail {
                debug_expr_invariants(tail, format!("{context}/tail"));
            }
        }
        ExprKind::Thunk { expr, .. } => {
            debug_expr_invariants(expr, format!("{context}/thunk"));
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}
