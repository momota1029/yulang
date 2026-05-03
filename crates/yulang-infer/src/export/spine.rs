use crate::ast::expr::{ExprKind, TypedExpr};

pub(super) fn collect_apply_spine<'a>(expr: &'a TypedExpr) -> (&'a TypedExpr, Vec<&'a TypedExpr>) {
    let mut args = Vec::new();
    let mut head = expr;
    loop {
        head = strip_transparent_wrappers(head);
        let ExprKind::App { callee, arg, .. } = &head.kind else {
            break;
        };
        args.push(arg.as_ref());
        head = callee;
    }
    args.reverse();
    (head, args)
}

pub(super) fn strip_transparent_wrappers<'a>(expr: &'a TypedExpr) -> &'a TypedExpr {
    match &expr.kind {
        ExprKind::Coerce { expr, .. } | ExprKind::PackForall(_, expr) => {
            strip_transparent_wrappers(expr)
        }
        ExprKind::Block(block) if block.stmts.is_empty() => block
            .tail
            .as_deref()
            .map(strip_transparent_wrappers)
            .unwrap_or(expr),
        _ => expr,
    }
}
