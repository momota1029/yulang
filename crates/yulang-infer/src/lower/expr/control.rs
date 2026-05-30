use yulang_parser::lex::SyntaxKind;

use super::{
    LowerState, SyntaxNode, collect_child_arms, lower_expr, make_app_with_cause,
    neg_id_is_pure_row, neg_prim_type, pos_id_is_empty_row, prim_type, resolve_bound_def_expr,
    unit_expr,
};
use crate::ast::expr::{ExprKind, PatKind, TypedBlock, TypedExpr, TypedPat, TypedStmt};
use crate::diagnostic::{ConstraintCause, ConstraintReason, ExpectedEdgeKind};
use crate::ids::TypeVar;
use crate::lower::stmt::{bind_pattern_locals, connect_pat_shape_and_locals};
use crate::lower::{CaseArmCheckSite, CaseArmPattern, CaseCheckSite};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};

// ── case (match) ─────────────────────────────────────────────────────────────

pub(super) fn lower_case(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let scrutinee = node
        .children()
        .find(|c| c.kind() == SyntaxKind::Expr)
        .map(|c| lower_expr(state, &c))
        .unwrap_or_else(|| unit_expr(state));
    if let Some(label) = case_like_label_name(node) {
        return lower_recursive_case_like(
            state,
            label,
            Some(scrutinee),
            "#case-receiver",
            |state, _receiver| state.fresh_exact_pure_eff_tv(),
            |state, receiver| {
                let scrutinee = resolve_bound_def_expr(state, receiver.def);
                lower_case_with_scrutinee(state, node, scrutinee)
            },
        );
    }
    lower_case_with_scrutinee(state, node, scrutinee)
}

pub(super) fn lower_case_lambda(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    if let Some(label) = case_like_label_name(node) {
        return lower_recursive_case_like(
            state,
            label,
            None,
            "#case-receiver",
            |state, _receiver| state.fresh_exact_pure_eff_tv(),
            |state, receiver| {
                let scrutinee = resolve_bound_def_expr(state, receiver.def);
                lower_case_with_scrutinee(state, node, scrutinee)
            },
        );
    }
    let receiver = fresh_case_like_lambda_receiver(state, "#case-receiver");
    let scrutinee = resolve_bound_def_expr(state, receiver.def);
    let body = lower_case_with_scrutinee(state, node, scrutinee);
    let arg_eff_tv = state.fresh_exact_pure_eff_tv();
    case_like_lambda_expr(state, receiver, body, arg_eff_tv)
}

#[derive(Clone, Copy)]
pub(in crate::lower::expr) struct CaseLikeLambdaReceiver {
    pub def: crate::ids::DefId,
    tv: TypeVar,
}

pub(in crate::lower::expr) fn fresh_case_like_lambda_receiver(
    state: &mut LowerState,
    name: &str,
) -> CaseLikeLambdaReceiver {
    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, Name(name.to_string()));
    if let Some(owner) = state.current_owner {
        state.register_def_owner(def, owner);
    }
    CaseLikeLambdaReceiver { def, tv }
}

pub(in crate::lower::expr) fn case_like_lambda_expr(
    state: &mut LowerState,
    receiver: CaseLikeLambdaReceiver,
    body: TypedExpr,
    arg_eff_tv: TypeVar,
) -> TypedExpr {
    let tv = state.fresh_tv();
    state.infer.constrain(
        state.pos_fun(
            Neg::Var(receiver.tv),
            Neg::Var(arg_eff_tv),
            Pos::Var(body.eff),
            Pos::Var(body.tv),
        ),
        Neg::Var(tv),
    );
    let eff = super::super::stmt::lambda_expr_eff_tv(state, &body, &[receiver.def]);
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Lam(receiver.def, Box::new(body)),
    }
}

pub(in crate::lower::expr) fn case_like_label_name(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::SigilIdent && token.text().starts_with('\''))
        .map(|token| Name(token.text().to_string()))
}

pub(in crate::lower::expr) fn lower_recursive_case_like<F, A>(
    state: &mut LowerState,
    label_name: Name,
    target: Option<TypedExpr>,
    receiver_name: &str,
    configure_receiver: A,
    lower_body: F,
) -> TypedExpr
where
    F: FnOnce(&mut LowerState, CaseLikeLambdaReceiver) -> TypedExpr,
    A: FnOnce(&mut LowerState, &CaseLikeLambdaReceiver) -> TypeVar,
{
    let self_def = state.fresh_def();
    let self_tv = state.fresh_tv();
    state.register_def_tv(self_def, self_tv);
    state.mark_let_bound_def(self_def);
    state.register_def_name(self_def, label_name.clone());
    if let Some(owner) = state.current_owner {
        state.register_def_owner(self_def, owner);
    }

    let receiver = fresh_case_like_lambda_receiver(state, receiver_name);
    state.register_def_owner(receiver.def, self_def);
    let arg_eff_tv = configure_receiver(state, &receiver);
    preconstrain_recursive_case_like_shape(state, self_def, receiver.tv, arg_eff_tv);

    state.ctx.push_local();
    state.ctx.bind_local(label_name, self_def);
    if let Some(&tv) = state.provisional_self_root_tvs.get(&self_def) {
        let eff_tv = state
            .def_eff_tvs
            .get(&self_def)
            .copied()
            .unwrap_or_else(|| state.fresh_exact_pure_eff_tv());
        state.activate_recursive_self_instance(
            self_def,
            crate::lower::ActiveRecursiveSelfInstance { tv, eff_tv },
        );
    }
    let body = state.with_owner(self_def, |state| lower_body(state, receiver));
    state.deactivate_recursive_self_instance(self_def);
    state.ctx.pop_local();

    let body_expr = case_like_lambda_expr(state, receiver, body, arg_eff_tv);
    state.insert_principal_body(self_def, body_expr.clone());
    let self_used = state.take_recursive_self_use(self_def);
    if self_used {
        state.mark_recursive_binding(self_def);
    }

    let bind_pat = recursive_case_like_bind_pat(state, self_def);
    super::super::stmt::connect_let_pattern(
        state,
        &bind_pat,
        body_expr.tv,
        body_expr.eff,
        None,
        self_used,
    );
    let self_expr = resolve_bound_def_expr(state, self_def);
    let tail = match target {
        Some(target) => super::make_app(state, self_expr, target),
        None => self_expr,
    };
    block_expr_from_parts(state, vec![TypedStmt::Let(bind_pat, body_expr)], tail)
}

fn preconstrain_recursive_case_like_shape(
    state: &mut LowerState,
    self_def: crate::ids::DefId,
    receiver_tv: TypeVar,
    arg_eff_tv: TypeVar,
) {
    let Some(&self_tv) = state.def_tvs.get(&self_def) else {
        return;
    };
    let ret_tv = state.fresh_tv();
    let ret_eff = state.fresh_tv();
    let fun_tv = state.fresh_tv();
    state.infer.constrain(
        state.pos_fun(
            Neg::Var(receiver_tv),
            Neg::Var(arg_eff_tv),
            Pos::Var(ret_eff),
            Pos::Var(ret_tv),
        ),
        Neg::Var(fun_tv),
    );
    state.infer.constrain(Pos::Var(self_tv), Neg::Var(fun_tv));
    state.infer.constrain(Pos::Var(fun_tv), Neg::Var(self_tv));
    state.provisional_self_root_tvs.insert(self_def, fun_tv);
    let non_generic_roots = [receiver_tv, arg_eff_tv]
        .into_iter()
        .collect::<std::collections::HashSet<_>>();
    let frozen =
        crate::scheme::freeze_type_var_with_non_generic(&state.infer, fun_tv, &non_generic_roots);
    state.provisional_self_schemes.insert(self_def, frozen);
}

fn recursive_case_like_bind_pat(
    state: &mut LowerState,
    self_def: crate::ids::DefId,
) -> crate::ast::expr::TypedPat {
    crate::ast::expr::TypedPat {
        tv: state.fresh_tv(),
        kind: crate::ast::expr::PatKind::As(
            Box::new(crate::ast::expr::TypedPat {
                tv: state.fresh_tv(),
                kind: crate::ast::expr::PatKind::Wild,
            }),
            self_def,
        ),
    }
}

fn block_expr_from_parts(
    state: &mut LowerState,
    stmts: Vec<TypedStmt>,
    tail: TypedExpr,
) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    for stmt in &stmts {
        match stmt {
            TypedStmt::Let(_, expr) | TypedStmt::Expr(expr) => {
                state.infer.constrain(Pos::Var(expr.eff), Neg::Var(eff));
            }
            TypedStmt::Module(..) => {}
        }
    }
    state.infer.constrain(Pos::Var(tail.tv), Neg::Var(tv));
    state.infer.constrain(Pos::Var(tail.eff), Neg::Var(eff));

    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Block(TypedBlock {
            tv,
            eff,
            stmts,
            tail: Some(Box::new(tail)),
        }),
    }
}

fn lower_case_with_scrutinee(
    state: &mut LowerState,
    node: &SyntaxNode,
    scrutinee: TypedExpr,
) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();

    let scrutinee_pattern = scrutinee_case_pattern(state, &scrutinee);
    state
        .infer
        .constrain(Pos::Var(scrutinee.eff), Neg::Var(eff));

    let arm_nodes = case_arm_nodes(node);
    let mut first_branch = true;
    let mut check_arms = Vec::new();
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
            let guarded = guard.is_some();
            check_arms.push(CaseArmCheckSite {
                span: arm.text_range(),
                file_span: state.current_source_span(arm.text_range()),
                guarded,
                patterns: case_arm_patterns(state, &pat),
            });
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
            if first_branch {
                state.infer.constrain(Pos::Var(tv), Neg::Var(body.tv));
                first_branch = false;
            }
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
    state.case_check_sites.push(CaseCheckSite {
        span: node.text_range(),
        file_span: state.current_source_span(node.text_range()),
        scrutinee: scrutinee_pattern,
        arms: check_arms,
    });

    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Match(Box::new(scrutinee), arms),
    }
}

fn scrutinee_case_pattern(state: &LowerState, expr: &TypedExpr) -> Option<CaseArmPattern> {
    let (head, _) = apply_spine_head_and_arg_count(expr);
    let ExprKind::Var(def) = &head.kind else {
        return None;
    };
    let shape = state.enum_variant_patterns.get(def)?;
    let variant = state.enum_variant_tags.get(def)?;
    Some(CaseArmPattern::EnumVariant {
        enum_path: shape.enum_path.clone(),
        variant: variant.clone(),
        payload_covers_all: true,
    })
}

fn apply_spine_head_and_arg_count(expr: &TypedExpr) -> (&TypedExpr, usize) {
    match &expr.kind {
        ExprKind::App { callee, .. } => {
            let (head, count) = apply_spine_head_and_arg_count(callee);
            (head, count + 1)
        }
        ExprKind::Coerce { expr, .. } => apply_spine_head_and_arg_count(expr),
        _ => (expr, 0),
    }
}

fn case_arm_nodes(node: &SyntaxNode) -> Vec<SyntaxNode> {
    node.children()
        .filter(|child| child.kind() == SyntaxKind::CaseBlock)
        .flat_map(|block| collect_child_arms(&block, SyntaxKind::CaseArm))
        .collect()
}

fn case_arm_patterns(state: &LowerState, pat: &TypedPat) -> Vec<CaseArmPattern> {
    let mut out = Vec::new();
    collect_case_arm_patterns(state, pat, &mut out);
    out
}

fn collect_case_arm_patterns(state: &LowerState, pat: &TypedPat, out: &mut Vec<CaseArmPattern>) {
    match &pat.kind {
        PatKind::Wild | PatKind::UnresolvedName(_) => out.push(CaseArmPattern::CoversAll),
        PatKind::As(inner, _) => collect_case_arm_patterns(state, inner, out),
        PatKind::Or(left, right) => {
            collect_case_arm_patterns(state, left, out);
            collect_case_arm_patterns(state, right, out);
        }
        PatKind::Con(ref_id, payload) => {
            let Some(resolved) = state.ctx.refs.resolved().get(ref_id) else {
                return;
            };
            let Some(shape) = state.enum_variant_patterns.get(&resolved.def_id) else {
                return;
            };
            let Some(variant) = state.enum_variant_tags.get(&resolved.def_id) else {
                return;
            };
            out.push(CaseArmPattern::EnumVariant {
                enum_path: shape.enum_path.clone(),
                variant: variant.clone(),
                payload_covers_all: payload
                    .as_deref()
                    .is_none_or(case_payload_pattern_covers_all),
            });
        }
        PatKind::Lit(_)
        | PatKind::Tuple(_)
        | PatKind::List { .. }
        | PatKind::Record { .. }
        | PatKind::PolyVariant(_, _) => {}
    }
}

fn case_payload_pattern_covers_all(pat: &TypedPat) -> bool {
    match &pat.kind {
        PatKind::Wild | PatKind::UnresolvedName(_) => true,
        PatKind::As(inner, _) => case_payload_pattern_covers_all(inner),
        PatKind::Or(left, right) => {
            case_payload_pattern_covers_all(left) || case_payload_pattern_covers_all(right)
        }
        PatKind::Tuple(items) => items.iter().all(case_payload_pattern_covers_all),
        PatKind::Lit(_)
        | PatKind::Con(_, _)
        | PatKind::List { .. }
        | PatKind::Record { .. }
        | PatKind::PolyVariant(_, _) => false,
    }
}

// ── if ────────────────────────────────────────────────────────────────────────

pub(super) fn lower_if(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();

    let mut scrutinee = None;
    let mut arms = Vec::new();
    let has_else = node.children().any(|c| c.kind() == SyntaxKind::ElseArm);
    if !has_else {
        state.infer.constrain(prim_type("unit"), Neg::Var(tv));
    }

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
        if !has_else {
            body = discard_if_branch_value(state, body);
        }
        let branch_cause = ConstraintCause {
            span: Some(arm.text_range()),
            reason: ConstraintReason::IfBranch,
        };
        if arms.is_empty() {
            state.infer.constrain(Pos::Var(tv), Neg::Var(body.tv));
        }
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
        let mut body = lower_if_arm_body(state, &arm);
        let branch_cause = ConstraintCause {
            span: Some(arm.text_range()),
            reason: ConstraintReason::IfBranch,
        };
        if arms.is_empty() {
            state.infer.constrain(Pos::Var(tv), Neg::Var(body.tv));
        }
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
        if arms.is_empty() {
            state.infer.constrain(Pos::Var(tv), Neg::Var(body.tv));
        }
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

fn discard_if_branch_value(state: &mut LowerState, expr: TypedExpr) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    let unit = unit_expr(state);
    state.infer.constrain(Pos::Var(expr.eff), Neg::Var(eff));
    state.infer.constrain(Pos::Var(unit.tv), Neg::Var(tv));
    state.infer.constrain(Pos::Var(unit.eff), Neg::Var(eff));

    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Block(TypedBlock {
            tv,
            eff,
            stmts: vec![TypedStmt::Expr(expr)],
            tail: Some(Box::new(unit)),
        }),
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
    let residual_eff = cond.eff;
    let junction = resolve_bound_def_expr(state, def);
    let handled = make_app_with_cause(
        state,
        junction,
        cond,
        ConstraintCause {
            span: None,
            reason: ConstraintReason::IfCondition,
        },
    );
    state
        .infer
        .constrain(Pos::Var(residual_eff), Neg::Var(handled.eff));
    handled
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
