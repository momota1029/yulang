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
