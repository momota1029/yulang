use yulang_parser::lex::SyntaxKind;

use super::{lower_expr, make_app, neg_prim_type, prim_type, resolve_path_expr, unit_expr};
use crate::ast::expr::{ExprKind, TypedExpr};
use crate::diagnostic::{ConstraintCause, ConstraintReason, ExpectedEdgeKind};
use crate::ids::TypeVar;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};

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
    let rhs_node = suffix
        .children()
        .filter(|c| {
            matches!(
                c.kind(),
                SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
            )
        })
        .last();
    let rhs_span = rhs_node.as_ref().map(SyntaxNode::text_range);
    let rhs = rhs_node
        .map(|node| lower_expr(state, &node))
        .unwrap_or_else(|| unit_expr(state));

    if let Some(set) = resolve_var_assignment_set(state, &reference) {
        return make_app(state, set, rhs);
    }

    lower_ref_set_assignment(state, reference, rhs, rhs_span)
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

fn lower_ref_set_assignment(
    state: &mut LowerState,
    reference: TypedExpr,
    value: TypedExpr,
    value_span: Option<rowan::TextRange>,
) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    let ref_eff = state.fresh_tv();
    constrain_ref_set_assignment(state, tv, eff, ref_eff, &reference, &value, value_span);
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::RefSet {
            reference: Box::new(reference),
            value: Box::new(value),
        },
    }
}

fn constrain_ref_set_assignment(
    state: &mut LowerState,
    tv: TypeVar,
    eff: TypeVar,
    ref_eff: TypeVar,
    reference: &TypedExpr,
    value: &TypedExpr,
    value_span: Option<rowan::TextRange>,
) {
    let expected_value_tv = state.fresh_tv();
    state.infer.constrain(prim_type("unit"), Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_prim_type("unit"));
    state
        .infer
        .constrain(Pos::Var(reference.eff), Neg::Var(eff));
    state.infer.constrain(Pos::Var(value.eff), Neg::Var(eff));
    state.infer.constrain(Pos::Var(ref_eff), Neg::Var(eff));

    state.expect_value(
        value.tv,
        expected_value_tv,
        ExpectedEdgeKind::AssignmentValue,
        ConstraintCause {
            span: value_span,
            reason: ConstraintReason::AssignmentValue,
        },
    );

    let ref_args = invariant_ref_args(
        state,
        &[(ref_eff, ref_eff), (expected_value_tv, expected_value_tv)],
    );
    state.infer.constrain(
        Pos::Con(std_var_ref_path(), ref_args),
        Neg::Var(reference.tv),
    );
}

fn invariant_ref_args(
    state: &LowerState,
    tvs: &[(TypeVar, TypeVar)],
) -> Vec<(crate::ids::PosId, crate::ids::NegId)> {
    tvs.iter()
        .map(|&(lower, upper)| {
            (
                state.infer.alloc_pos(Pos::Var(lower)),
                state.infer.alloc_neg(Neg::Var(upper)),
            )
        })
        .collect()
}

fn std_var_ref_path() -> Path {
    Path {
        segments: vec![
            Name("std".to_string()),
            Name("var".to_string()),
            Name("ref".to_string()),
        ],
    }
}
