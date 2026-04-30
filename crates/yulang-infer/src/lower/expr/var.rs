use yulang_parser::lex::SyntaxKind;

use super::{lower_expr, make_app, make_const_lambda, resolve_path_expr, unit_expr};
use crate::ast::expr::{ExprKind, TypedExpr};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;

pub(super) fn lower_var_read_expr(state: &mut LowerState, sigil: &str) -> TypedExpr {
    let Some(raw) = sigil.strip_prefix('$') else {
        return unit_expr(state);
    };
    let reference_name = Name(format!("&{raw}"));
    if let Some(act_name) = state.ctx.resolve_var_ref_alias(&reference_name) {
        let get = resolve_path_expr(state, vec![act_name, Name("get".to_string())]);
        let unit = unit_expr(state);
        return make_app(state, get, unit);
    }
    if let Some(get) = state
        .ctx
        .resolve_value(&reference_name)
        .and_then(|def| state.var_ref_acts.get(&def).cloned())
        .map(|act_name| resolve_path_expr(state, vec![act_name, Name("get".to_string())]))
    {
        let unit = unit_expr(state);
        return make_app(state, get, unit);
    }
    lower_ref_get_read(state, reference_name)
}

fn lower_ref_get_read(state: &mut LowerState, reference_name: Name) -> TypedExpr {
    let get = resolve_path_expr(
        state,
        vec![
            Name("std".to_string()),
            Name("var".to_string()),
            Name("ref".to_string()),
            Name("get".to_string()),
        ],
    );
    let reference = resolve_path_expr(state, vec![reference_name]);
    let get_ref = make_app(state, get, reference);
    let unit = unit_expr(state);
    make_app(state, get_ref, unit)
}

pub(super) fn lower_var_assignment(
    state: &mut LowerState,
    reference: TypedExpr,
    suffix: &SyntaxNode,
) -> TypedExpr {
    let rhs = suffix
        .children()
        .filter(|c| {
            matches!(
                c.kind(),
                SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
            )
        })
        .last()
        .map(|node| lower_expr(state, &node))
        .unwrap_or_else(|| unit_expr(state));

    if let Some(set) = resolve_var_assignment_set(state, &reference) {
        return make_app(state, set, rhs);
    }

    let update = resolve_path_expr(
        state,
        vec![
            Name("std".to_string()),
            Name("var".to_string()),
            Name("ref".to_string()),
            Name("update".to_string()),
        ],
    );
    let update_ref = make_app(state, update, reference);
    let replacement = make_const_lambda(state, rhs);
    make_app(state, update_ref, replacement)
}

fn resolve_var_assignment_set(state: &mut LowerState, reference: &TypedExpr) -> Option<TypedExpr> {
    let act_name = match &reference.kind {
        ExprKind::Var(def) => state.var_ref_acts.get(def).cloned(),
        ExprKind::Ref(ref_id) => state
            .ctx
            .refs
            .get(*ref_id)
            .and_then(|def| state.var_ref_acts.get(&def).cloned())
            .or_else(|| {
                state
                    .ctx
                    .refs
                    .unresolved()
                    .iter()
                    .find(|(id, _)| id == ref_id)
                    .and_then(|(_, info)| match info.path.segments.as_slice() {
                        [name] => state.ctx.resolve_var_ref_alias(name),
                        _ => None,
                    })
            }),
        _ => None,
    }?;
    Some(resolve_path_expr(
        state,
        vec![act_name, Name("set".to_string())],
    ))
}
