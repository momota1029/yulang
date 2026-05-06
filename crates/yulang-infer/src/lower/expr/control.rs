use yulang_parser::lex::SyntaxKind;

use super::{
    LowerState, SyntaxNode, collect_child_arms, lower_expr, make_app_with_cause,
    neg_id_is_pure_row, neg_prim_type, pos_id_is_empty_row, prim_type, resolve_bound_def_expr,
    unit_expr,
};
use crate::ast::expr::{ExprKind, TypedExpr};
use crate::diagnostic::{ConstraintCause, ConstraintReason, ExpectedEdgeKind};
use crate::ids::TypeVar;
use crate::lower::stmt::{bind_pattern_locals, connect_pat_shape_and_locals};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};

// ── case (match) ─────────────────────────────────────────────────────────────

pub(super) fn lower_case(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();

    let scrutinee = node
        .children()
        .find(|c| c.kind() == SyntaxKind::Expr)
        .map(|c| lower_expr(state, &c))
        .unwrap_or_else(|| unit_expr(state));

    let arm_nodes: Vec<_> = node
        .children()
        .filter(|c| c.kind() == SyntaxKind::CaseBlock)
        .flat_map(|b| collect_child_arms(&b, SyntaxKind::CaseArm))
        .collect();
    let arms: Vec<crate::ast::expr::TypedMatchArm> = arm_nodes
        .into_iter()
        .filter_map(|arm| {
            let pat_node = arm.children().find(|c| {
                matches!(
                    c.kind(),
                    SyntaxKind::Pattern
                        | SyntaxKind::PatOr
                        | SyntaxKind::PatAs
                        | SyntaxKind::PatParenGroup
                )
            })?;
            state.ctx.push_local();
            bind_pattern_locals(state, &pat_node);
            let pat = crate::lower::stmt::lower_pat(state, &pat_node);
            let mut guard = lower_arm_guard(state, &arm);
            if let Some(guard_expr) = guard.take() {
                let cause = ConstraintCause {
                    span: Some(arm.text_range()),
                    reason: ConstraintReason::MatchGuard,
                };
                let expected_bool_tv = fresh_exact_bool_tv(state, &cause);
                guard = Some(
                    state
                        .implicit_cast_boundary_with_effects(
                            guard_expr,
                            expected_bool_tv,
                            eff,
                            ExpectedEdgeKind::MatchGuard,
                            cause,
                            false,
                        )
                        .0,
                );
            }
            let mut body = arm
                .children()
                .find(|c| {
                    matches!(
                        c.kind(),
                        SyntaxKind::Expr | SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
                    )
                })
                .map(|c| lower_expr(state, &c))
                .unwrap_or_else(|| unit_expr(state));
            connect_pat_shape_and_locals(state, &pat, body.eff);
            state
                .infer
                .constrain(Pos::Var(scrutinee.tv), Neg::Var(pat.tv));
            state
                .infer
                .constrain(Pos::Var(pat.tv), Neg::Var(scrutinee.tv));
            body = state
                .implicit_cast_boundary_with_effects(
                    body,
                    tv,
                    eff,
                    ExpectedEdgeKind::MatchBranch,
                    ConstraintCause {
                        span: Some(arm.text_range()),
                        reason: ConstraintReason::MatchBranch,
                    },
                    true,
                )
                .0;
            state.ctx.pop_local();
            Some(crate::ast::expr::TypedMatchArm { pat, guard, body })
        })
        .collect();

    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Match(Box::new(scrutinee), arms),
    }
}

// ── if ────────────────────────────────────────────────────────────────────────

pub(super) fn lower_if(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();

    let mut scrutinee = None;
    let mut arms = Vec::new();
    let mut has_else = false;

    for arm in node.children().filter(|c| c.kind() == SyntaxKind::IfArm) {
        let cond = arm
            .children()
            .find(|c| c.kind() == SyntaxKind::Cond)
            .and_then(|cond| cond.children().find(|c| c.kind() == SyntaxKind::Expr))
            .map(|expr| lower_expr(state, &expr))
            .unwrap_or_else(|| unit_expr(state));
        let cond = lower_junction_condition(state, cond);
        let condition_cause = ConstraintCause {
            span: Some(arm.text_range()),
            reason: ConstraintReason::IfCondition,
        };
        let expected_bool_tv = fresh_exact_bool_tv(state, &condition_cause);
        let cond = state
            .implicit_cast_boundary_with_effects(
                cond,
                expected_bool_tv,
                eff,
                ExpectedEdgeKind::IfCondition,
                condition_cause,
                false,
            )
            .0;

        let mut body = lower_if_arm_body(state, &arm);
        let branch_cause = ConstraintCause {
            span: Some(arm.text_range()),
            reason: ConstraintReason::IfBranch,
        };
        body = state
            .implicit_cast_boundary_with_effects(
                body,
                tv,
                eff,
                ExpectedEdgeKind::IfBranch,
                branch_cause,
                true,
            )
            .0;

        if scrutinee.is_none() {
            scrutinee = Some(cond);
        }
        let pat = bool_lit_pat(state, true);
        connect_pat_shape_and_locals(state, &pat, body.eff);
        state.infer.constrain(
            Pos::Var(scrutinee.as_ref().expect("if scrutinee").tv),
            Neg::Var(pat.tv),
        );
        arms.push(crate::ast::expr::TypedMatchArm {
            pat,
            guard: None,
            body,
        });
    }

    for arm in node.children().filter(|c| c.kind() == SyntaxKind::ElseArm) {
        has_else = true;
        let mut body = lower_if_arm_body(state, &arm);
        let branch_cause = ConstraintCause {
            span: Some(arm.text_range()),
            reason: ConstraintReason::IfBranch,
        };
        body = state
            .implicit_cast_boundary_with_effects(
                body,
                tv,
                eff,
                ExpectedEdgeKind::IfBranch,
                branch_cause,
                true,
            )
            .0;
        let pat = bool_lit_pat(state, false);
        connect_pat_shape_and_locals(state, &pat, body.eff);
        if let Some(scrutinee) = &scrutinee {
            state
                .infer
                .constrain(Pos::Var(scrutinee.tv), Neg::Var(pat.tv));
        }
        arms.push(crate::ast::expr::TypedMatchArm {
            pat,
            guard: None,
            body,
        });
    }

    if scrutinee.is_some() && !has_else {
        let mut body = unit_expr(state);
        let branch_cause = ConstraintCause {
            span: Some(node.text_range()),
            reason: ConstraintReason::IfBranch,
        };
        body = state
            .implicit_cast_boundary_with_effects(
                body,
                tv,
                eff,
                ExpectedEdgeKind::IfBranch,
                branch_cause,
                true,
            )
            .0;
        let pat = bool_lit_pat(state, false);
        connect_pat_shape_and_locals(state, &pat, body.eff);
        if let Some(scrutinee) = &scrutinee {
            state
                .infer
                .constrain(Pos::Var(scrutinee.tv), Neg::Var(pat.tv));
        }
        arms.push(crate::ast::expr::TypedMatchArm {
            pat,
            guard: None,
            body,
        });
    }

    let scrutinee = scrutinee.unwrap_or_else(|| unit_expr(state));
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Match(Box::new(scrutinee), arms),
    }
}

pub(super) fn bool_lit_pat(state: &mut LowerState, value: bool) -> crate::ast::expr::TypedPat {
    crate::ast::expr::TypedPat {
        tv: state.fresh_tv(),
        kind: crate::ast::expr::PatKind::Lit(crate::ast::expr::Lit::Bool(value)),
    }
}

fn lower_if_arm_body(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    node.children()
        .find(|c| {
            matches!(
                c.kind(),
                SyntaxKind::Expr | SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
            )
        })
        .map(|body| lower_expr(state, &body))
        .unwrap_or_else(|| unit_expr(state))
}

pub(in crate::lower::expr) fn lower_arm_guard(
    state: &mut LowerState,
    node: &SyntaxNode,
) -> Option<TypedExpr> {
    node.children()
        .find(|c| matches!(c.kind(), SyntaxKind::CaseGuard | SyntaxKind::CatchGuard))
        .and_then(|guard| guard.children().find(|c| c.kind() == SyntaxKind::Expr))
        .map(|expr| {
            let lowered = lower_expr(state, &expr);
            lower_junction_condition(state, lowered)
        })
}

fn lower_junction_condition(state: &mut LowerState, cond: TypedExpr) -> TypedExpr {
    if eff_tv_is_exact_pure_row(state, cond.eff) {
        return cond;
    }
    let junction_path = Path {
        segments: vec![Name("junction".to_string()), Name("junction".to_string())],
    };
    let Some(def) = state.ctx.resolve_path_value(&junction_path) else {
        return cond;
    };
    let junction = resolve_bound_def_expr(state, def);
    make_app_with_cause(
        state,
        junction,
        cond,
        ConstraintCause {
            span: None,
            reason: ConstraintReason::IfCondition,
        },
    )
}

fn fresh_exact_bool_tv(state: &mut LowerState, cause: &ConstraintCause) -> TypeVar {
    let tv = state.fresh_tv();
    state
        .infer
        .constrain_with_cause(prim_type("bool"), Neg::Var(tv), cause.clone());
    state
        .infer
        .constrain_with_cause(Pos::Var(tv), neg_prim_type("bool"), cause.clone());
    tv
}

fn eff_tv_is_exact_pure_row(state: &LowerState, tv: TypeVar) -> bool {
    let mut seen = std::collections::HashSet::new();
    seen.insert(tv);
    let lowers = state.infer.lower_refs_of(tv);
    let uppers = state.infer.upper_refs_of(tv);
    !lowers.is_empty()
        && lowers
            .iter()
            .all(|lower| pos_id_is_empty_row(state, *lower, &mut seen))
        && uppers
            .iter()
            .all(|upper| neg_id_is_pure_row(state, *upper, &mut seen))
}
