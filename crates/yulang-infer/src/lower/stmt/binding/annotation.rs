use yulang_parser::lex::SyntaxKind;

use crate::diagnostic::{ConstraintCause, ConstraintReason, ExpectedEdgeKind};
use crate::ids::{NegId, PosId, TypeVar};
use crate::lower::{LowerState, SyntaxNode};
use crate::types::{Neg, Pos};

pub(crate) fn connect_binding_type_annotation(
    state: &mut LowerState,
    header: &SyntaxNode,
    body_tv: TypeVar,
) {
    let Some(pattern) = super::super::child_node(header, SyntaxKind::Pattern) else {
        return;
    };
    let Some(type_expr) = super::super::child_node(&pattern, SyntaxKind::TypeAnn)
        .and_then(|ann| super::super::child_node(&ann, SyntaxKind::TypeExpr))
    else {
        return;
    };
    let Some(sig) = crate::lower::signature::parse_sig_type_expr(&type_expr) else {
        return;
    };
    let mut vars = state.current_type_scope().cloned().unwrap_or_default();
    let pos_sig = crate::lower::signature::lower_pure_sig_pos_id(state, &sig, &mut vars);
    let mut neg_vars = vars.clone();
    let neg_sig = crate::lower::signature::lower_pure_sig_neg_id(state, &sig, &mut neg_vars);
    let cause = ConstraintCause {
        span: Some(type_expr.text_range()),
        reason: ConstraintReason::Annotation,
    };
    let ann_tv = fresh_annotation_tv(state, pos_sig, neg_sig, &cause);
    connect_annotated_target(state, body_tv, ann_tv, cause);
}

pub(crate) fn connect_pattern_sig_annotation(
    state: &mut LowerState,
    pat_node: &SyntaxNode,
    target_tv: TypeVar,
    _latent_eff_tv: Option<TypeVar>,
) -> Option<crate::lower::FunctionSigEffectHint> {
    let type_expr = super::super::child_node(pat_node, SyntaxKind::TypeAnn)
        .and_then(|ann| super::super::child_node(&ann, SyntaxKind::TypeExpr))?;
    let sig = crate::lower::signature::parse_sig_type_expr(&type_expr)?;
    let mut vars = state.current_type_scope().cloned().unwrap_or_default();
    let cause = ConstraintCause {
        span: Some(type_expr.text_range()),
        reason: ConstraintReason::Annotation,
    };

    if let Some(fun) = crate::lower::signature::lower_function_sig_shape(state, &sig, &mut vars) {
        let ann_tv = state.fresh_tv();
        state.infer.constrain_with_cause(
            Pos::Fun {
                arg: fun.arg_neg,
                arg_eff: state.infer.arena.empty_neg_row,
                ret_eff: fun.ret_eff_pos,
                ret: fun.ret_pos,
            },
            Neg::Var(ann_tv),
            cause.clone(),
        );
        state.infer.constrain_with_cause(
            Pos::Var(ann_tv),
            Neg::Fun {
                arg: fun.arg_pos,
                arg_eff: state.infer.arena.empty_pos_row,
                ret_eff: fun.ret_eff_neg,
                ret: fun.ret_neg,
            },
            cause.clone(),
        );
        state
            .infer
            .constrain_with_cause(Pos::Var(ann_tv), Neg::Var(target_tv), cause.clone());
        state.expect_value(
            target_tv,
            ann_tv,
            ExpectedEdgeKind::Annotation,
            cause.clone(),
        );
        return Some(if fun.effect_hint {
            crate::lower::FunctionSigEffectHint::Through
        } else if fun.ret_eff_pos == state.infer.arena.empty_pos_row
            && fun.ret_eff_neg == state.infer.arena.empty_neg_row
        {
            crate::lower::FunctionSigEffectHint::Pure
        } else {
            crate::lower::FunctionSigEffectHint::Bounds(fun.ret_eff_pos, fun.ret_eff_neg)
        });
    }

    let pos_sig = crate::lower::signature::lower_pure_sig_pos_id(state, &sig, &mut vars);
    let mut neg_vars = vars.clone();
    let neg_sig = crate::lower::signature::lower_pure_sig_neg_id(state, &sig, &mut neg_vars);
    let ann_tv = fresh_annotation_tv(state, pos_sig, neg_sig, &cause);
    connect_annotated_target(state, target_tv, ann_tv, cause);
    None
}

fn fresh_annotation_tv(
    state: &mut LowerState,
    lower: PosId,
    upper: NegId,
    cause: &ConstraintCause,
) -> TypeVar {
    let ann_tv = state.fresh_tv();
    state
        .infer
        .constrain_with_cause(lower, Neg::Var(ann_tv), cause.clone());
    state
        .infer
        .constrain_with_cause(Pos::Var(ann_tv), upper, cause.clone());
    ann_tv
}

fn connect_annotated_target(
    state: &mut LowerState,
    target_tv: TypeVar,
    ann_tv: TypeVar,
    cause: ConstraintCause,
) {
    state
        .infer
        .constrain_with_cause(Pos::Var(ann_tv), Neg::Var(target_tv), cause.clone());
    state.expect_value(target_tv, ann_tv, ExpectedEdgeKind::Annotation, cause);
}
