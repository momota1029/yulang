use super::*;

pub(crate) fn debug_expr_tree(
    arena: &poly_expr::Arena,
    expr: poly_expr::ExprId,
    depth: usize,
) -> String {
    if depth == 0 {
        return format!("{expr:?}:...");
    }
    match arena.expr(expr) {
        poly_expr::Expr::Lit(_) => format!("{expr:?}:lit"),
        poly_expr::Expr::PrimitiveOp(op) => format!("{expr:?}:primitive({op:?})"),
        poly_expr::Expr::Var(ref_id) => {
            let target = arena.ref_target(*ref_id);
            format!("{expr:?}:var(ref={ref_id:?}, target={target:?})")
        }
        poly_expr::Expr::App(callee, arg) => format!(
            "{expr:?}:app({}, {})",
            debug_expr_tree(arena, *callee, depth - 1),
            debug_expr_tree(arena, *arg, depth - 1)
        ),
        poly_expr::Expr::RefSet(reference, value) => format!(
            "{expr:?}:ref-set({}, {})",
            debug_expr_tree(arena, *reference, depth - 1),
            debug_expr_tree(arena, *value, depth - 1)
        ),
        poly_expr::Expr::Lambda(param, body) => {
            format!(
                "{expr:?}:lambda({param:?} -> {})",
                debug_expr_tree(arena, *body, depth - 1)
            )
        }
        poly_expr::Expr::Tuple(items) => format!(
            "{expr:?}:tuple({})",
            items
                .iter()
                .map(|item| debug_expr_tree(arena, *item, depth - 1))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        poly_expr::Expr::Record { fields, .. } => format!(
            "{expr:?}:record({})",
            fields
                .iter()
                .map(|(name, value)| format!(
                    "{name}:{}",
                    debug_expr_tree(arena, *value, depth - 1)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        poly_expr::Expr::PolyVariant(tag, payloads) => format!(
            "{expr:?}:variant({tag}, {})",
            payloads
                .iter()
                .map(|payload| debug_expr_tree(arena, *payload, depth - 1))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        poly_expr::Expr::Select(base, select) => {
            let select = arena.select(*select);
            format!(
                "{expr:?}:select({}, name={}, resolution={:?})",
                debug_expr_tree(arena, *base, depth - 1),
                select.name,
                select.resolution
            )
        }
        poly_expr::Expr::Case(scrutinee, arms) => format!(
            "{expr:?}:case({}, arms={})",
            debug_expr_tree(arena, *scrutinee, depth - 1),
            arms.len()
        ),
        poly_expr::Expr::Catch(body, arms) => format!(
            "{expr:?}:catch({}, arms={})",
            debug_expr_tree(arena, *body, depth - 1),
            arms.len()
        ),
        poly_expr::Expr::Block(stmts, tail) => format!(
            "{expr:?}:block(stmts={}, tail={})",
            stmts.len(),
            tail.map(|tail| debug_expr_tree(arena, tail, depth - 1))
                .unwrap_or_else(|| "none".to_string())
        ),
    }
}

pub(crate) fn def_body(def: &poly_expr::Def) -> Option<poly_expr::ExprId> {
    match def {
        poly_expr::Def::Let { body, .. } => *body,
        _ => None,
    }
}

pub(crate) fn expr_contains_expr(
    arena: &poly_expr::Arena,
    root: poly_expr::ExprId,
    needle: poly_expr::ExprId,
) -> bool {
    if root == needle {
        return true;
    }
    match arena.expr(root) {
        poly_expr::Expr::Lit(_) | poly_expr::Expr::PrimitiveOp(_) | poly_expr::Expr::Var(_) => {
            false
        }
        poly_expr::Expr::App(callee, arg) | poly_expr::Expr::RefSet(callee, arg) => {
            expr_contains_expr(arena, *callee, needle) || expr_contains_expr(arena, *arg, needle)
        }
        poly_expr::Expr::Lambda(_, body) => expr_contains_expr(arena, *body, needle),
        poly_expr::Expr::Tuple(items) => items
            .iter()
            .any(|item| expr_contains_expr(arena, *item, needle)),
        poly_expr::Expr::Record { fields, spread } => {
            fields
                .iter()
                .any(|(_, value)| expr_contains_expr(arena, *value, needle))
                || match spread {
                    poly_expr::RecordSpread::Head(expr) | poly_expr::RecordSpread::Tail(expr) => {
                        expr_contains_expr(arena, *expr, needle)
                    }
                    poly_expr::RecordSpread::None => false,
                }
        }
        poly_expr::Expr::PolyVariant(_, payloads) => payloads
            .iter()
            .any(|payload| expr_contains_expr(arena, *payload, needle)),
        poly_expr::Expr::Select(base, _) => expr_contains_expr(arena, *base, needle),
        poly_expr::Expr::Case(scrutinee, arms) => {
            expr_contains_expr(arena, *scrutinee, needle)
                || arms.iter().any(|arm| {
                    arm.guard
                        .is_some_and(|guard| expr_contains_expr(arena, guard, needle))
                        || expr_contains_expr(arena, arm.body, needle)
                })
        }
        poly_expr::Expr::Catch(body, arms) => {
            expr_contains_expr(arena, *body, needle)
                || arms.iter().any(|arm| {
                    arm.guard
                        .is_some_and(|guard| expr_contains_expr(arena, guard, needle))
                        || expr_contains_expr(arena, arm.body, needle)
                })
        }
        poly_expr::Expr::Block(stmts, tail) => {
            stmts.iter().any(|stmt| match stmt {
                poly_expr::Stmt::Let(_, _, value) | poly_expr::Stmt::Expr(value) => {
                    expr_contains_expr(arena, *value, needle)
                }
                poly_expr::Stmt::Module(_, body) => body.iter().any(|stmt| match stmt {
                    poly_expr::Stmt::Let(_, _, value) | poly_expr::Stmt::Expr(value) => {
                        expr_contains_expr(arena, *value, needle)
                    }
                    poly_expr::Stmt::Module(_, _) => false,
                }),
            }) || tail.is_some_and(|tail| expr_contains_expr(arena, tail, needle))
        }
    }
}
