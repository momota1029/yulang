use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{ExprKind, Lit, TypedExpr, TypedMatchArm};
use crate::diagnostic::{TypeOrigin, TypeOriginKind};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;
use crate::types::{Neg, Pos};

pub(super) fn lower_short_circuit_infix(
    state: &mut LowerState,
    lhs: TypedExpr,
    node: &SyntaxNode,
) -> Option<TypedExpr> {
    let op = super::infix_op_name(node)?;
    let rhs_node = node.children().find(|c| c.kind() == SyntaxKind::Expr)?;
    let rhs = super::lower_expr(state, &rhs_node);
    match op.0.as_str() {
        "and" => {
            let false_expr = bool_expr(state, false);
            Some(lower_boolean_match(state, lhs, rhs, false_expr))
        }
        "or" => {
            let true_expr = bool_expr(state, true);
            Some(lower_boolean_match(state, lhs, true_expr, rhs))
        }
        _ => None,
    }
}

pub(super) fn lower_not_equal_infix(
    state: &mut LowerState,
    lhs: TypedExpr,
    rhs: TypedExpr,
    node: &SyntaxNode,
) -> Option<TypedExpr> {
    let op = super::infix_op_name(node)?;
    if op.0 != "!=" {
        return None;
    }
    let eq_ref = super::resolve_path_expr(
        state,
        vec![
            Name("std".to_string()),
            Name("prelude".to_string()),
            Name("Eq".to_string()),
            Name("eq".to_string()),
        ],
    );
    let not_ref = super::resolve_path_expr(state, vec![Name("not".to_string())]);
    let eq_app = super::make_app(state, eq_ref, lhs);
    let eq_result = super::make_app(state, eq_app, rhs);
    Some(super::make_app(state, not_ref, eq_result))
}

fn lower_boolean_match(
    state: &mut LowerState,
    scrutinee: TypedExpr,
    true_body: TypedExpr,
    false_body: TypedExpr,
) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    state
        .infer
        .constrain(Pos::Var(scrutinee.tv), super::neg_prim_type("bool"));
    state
        .infer
        .constrain(Pos::Var(scrutinee.eff), Neg::Var(eff));

    for body in [&true_body, &false_body] {
        state
            .infer
            .constrain(Pos::Var(body.tv), super::neg_prim_type("bool"));
        state.infer.constrain(Pos::Var(body.tv), Neg::Var(tv));
        state.infer.constrain(Pos::Var(body.eff), Neg::Var(eff));
    }

    let true_pat = super::control::bool_lit_pat(state, true);
    super::connect_pat_shape_and_locals(state, &true_pat, true_body.eff);
    state
        .infer
        .constrain(Pos::Var(scrutinee.tv), Neg::Var(true_pat.tv));

    let false_pat = super::control::bool_lit_pat(state, false);
    super::connect_pat_shape_and_locals(state, &false_pat, false_body.eff);
    state
        .infer
        .constrain(Pos::Var(scrutinee.tv), Neg::Var(false_pat.tv));

    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Match(
            Box::new(scrutinee),
            vec![
                TypedMatchArm {
                    pat: true_pat,
                    guard: None,
                    body: true_body,
                },
                TypedMatchArm {
                    pat: false_pat,
                    guard: None,
                    body: false_body,
                },
            ],
        ),
    }
}

fn bool_expr(state: &mut LowerState, value: bool) -> TypedExpr {
    let tv = state.fresh_tv_with_origin(TypeOrigin {
        span: None,
        kind: TypeOriginKind::Synthetic,
        label: Some("bool".to_string()),
    });
    let eff = state.fresh_exact_pure_eff_tv();
    state
        .infer
        .constrain(super::prim_type("bool"), Neg::Var(tv));
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Lit(Lit::Bool(value)),
    }
}
