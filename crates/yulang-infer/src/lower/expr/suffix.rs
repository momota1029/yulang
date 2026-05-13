use crate::profile::ProfileClock as Instant;

use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{ExprKind, PolyVariantOrigin, TypedExpr};
use crate::diagnostic::{ConstraintCause, ConstraintReason};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;
use crate::types::{Neg, Pos};

use super::{
    infix_op_ref, lower_expr, lower_var_assignment, make_app_with_cause, neg_prim_type,
    prefix_op_ref, prim_type, resolve_path_expr_at, suffix_op_ref, unit_expr,
};

/// サフィックスノードを acc に適用して新しい TypedExpr を返す。
pub(super) fn apply_suffix(
    state: &mut LowerState,
    acc: TypedExpr,
    suffix: &SyntaxNode,
) -> TypedExpr {
    let start = Instant::now();
    let result = match suffix.kind() {
        SyntaxKind::Field => apply_field_suffix(state, acc, suffix),
        SyntaxKind::ApplyML => apply_ml_suffix(state, acc, suffix),
        SyntaxKind::ApplyC => apply_c_suffix(state, acc, suffix),
        SyntaxKind::ApplyColon => apply_colon_suffix(state, acc, suffix),
        SyntaxKind::Assign => lower_var_assignment(state, acc, suffix),
        SyntaxKind::InfixNode => apply_infix_suffix(state, acc, suffix),
        SyntaxKind::PrefixNode => {
            let op_ref = prefix_op_ref(state, suffix);
            let arg = lazy_operator_arg(state, &op_ref, acc);
            make_app_with_cause(state, op_ref, arg, apply_arg_cause(suffix))
        }
        SyntaxKind::SuffixNode => {
            let op_ref = suffix_op_ref(state, suffix);
            let arg = lazy_operator_arg(state, &op_ref, acc);
            make_app_with_cause(state, op_ref, arg, apply_arg_cause(suffix))
        }
        SyntaxKind::Index => apply_index_suffix(state, acc, suffix),
        _ => acc,
    };
    state.lower_detail.apply_suffix += start.elapsed();
    result
}

pub(super) fn apply_synthetic_field_selection(
    state: &mut LowerState,
    acc: TypedExpr,
    name: Name,
    node: &SyntaxNode,
) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    push_deferred_selection(state, acc, node, name, tv, eff, false, Some(node.text_range()))
}

fn apply_field_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    let field = suffix
        .children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| t.kind() == SyntaxKind::DotField)
        .map(|t| {
            let s = t.text().to_string();
            let field_like_source =
                s.starts_with('.') && suffix.to_string().trim_start().starts_with('.');
            (
                Name(s.trim_start_matches('.').to_string()),
                field_like_source,
                t.text_range(),
            )
        });
    if let Some((name, structural_record_allowed, selection_span)) = field {
        if let ExprKind::Var(def) = &acc.kind {
            if let Some(path) = state.ctx.resolve_field_alias(*def, &name) {
                return resolve_path_expr_at(state, path.segments, Some(suffix.text_range()));
            }
        }
        push_deferred_selection(
            state,
            acc,
            suffix,
            name,
            tv,
            eff,
            structural_record_allowed,
            Some(selection_span),
        )
    } else {
        acc
    }
}

fn apply_ml_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    if matches!(acc.kind, ExprKind::PolyVariant(_, _, _)) {
        return apply_variant_payload_suffix(state, acc, suffix);
    }
    let mut result = acc;
    for child in suffix.children().filter(|c| c.kind() == SyntaxKind::Expr) {
        let arg = lower_expr(state, &child);
        result = make_app_with_cause(
            state,
            result,
            arg,
            ConstraintCause {
                span: Some(suffix.text_range()),
                reason: ConstraintReason::ApplyArg,
            },
        );
    }
    result
}

fn apply_c_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    if matches!(acc.kind, ExprKind::PolyVariant(_, _, _)) {
        return apply_variant_payload_suffix(state, acc, suffix);
    }
    let args: Vec<_> = suffix
        .children()
        .filter(|c| c.kind() == SyntaxKind::Expr)
        .map(|c| lower_expr(state, &c))
        .collect();

    if args.is_empty() {
        let unit = unit_expr(state);
        make_app_with_cause(
            state,
            acc,
            unit,
            ConstraintCause {
                span: Some(suffix.text_range()),
                reason: ConstraintReason::ApplyArg,
            },
        )
    } else {
        let mut result = acc;
        for arg in args {
            result = make_app_with_cause(
                state,
                result,
                arg,
                ConstraintCause {
                    span: Some(suffix.text_range()),
                    reason: ConstraintReason::ApplyArg,
                },
            );
        }
        result
    }
}

fn apply_variant_payload_suffix(
    state: &mut LowerState,
    acc: TypedExpr,
    suffix: &SyntaxNode,
) -> TypedExpr {
    let ExprKind::PolyVariant(tag, mut payloads, origin) = acc.kind else {
        return acc;
    };
    payloads.extend(
        suffix
            .children()
            .filter(|child| child.kind() == SyntaxKind::Expr)
            .map(|child| lower_expr(state, &child)),
    );
    lower_poly_variant_expr(state, tag, payloads, origin)
}

pub(super) fn lower_poly_variant_expr(
    state: &mut LowerState,
    tag: Name,
    payloads: Vec<TypedExpr>,
    origin: PolyVariantOrigin,
) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_exact_pure_eff_tv();
    for payload in &payloads {
        state.infer.constrain(Pos::Var(payload.eff), Neg::Var(eff));
    }
    state.infer.constrain(
        state.pos_variant(vec![(
            tag.clone(),
            payloads
                .iter()
                .map(|payload| Pos::Var(payload.tv))
                .collect(),
        )]),
        Neg::Var(tv),
    );
    state.infer.constrain(
        Pos::Var(tv),
        Neg::PolyVariant(vec![(
            tag.clone(),
            payloads
                .iter()
                .map(|payload| state.infer.alloc_neg(Neg::Var(payload.tv)))
                .collect(),
        )]),
    );
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::PolyVariant(tag, payloads, origin),
    }
}

fn apply_colon_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    let mut result = acc;
    for arg_node in suffix.children().filter(|c| {
        matches!(
            c.kind(),
            SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        )
    }) {
        let arg = lower_expr(state, &arg_node);
        result = make_app_with_cause(
            state,
            result,
            arg,
            ConstraintCause {
                span: Some(suffix.text_range()),
                reason: ConstraintReason::ApplyArg,
            },
        );
    }
    result
}

fn apply_infix_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    let rhs_node = suffix.children().find(|c| c.kind() == SyntaxKind::Expr);
    if let Some(rhs_node) = rhs_node {
        let rhs = lower_expr(state, &rhs_node);
        let op_ref = infix_op_ref(state, suffix);
        let lazy = is_lazy_operator_expr(state, &op_ref);
        let lhs = if lazy {
            unit_thunk_expr(state, acc)
        } else {
            acc
        };
        let rhs = if lazy {
            unit_thunk_expr(state, rhs)
        } else {
            rhs
        };
        let app1 = make_app_with_cause(state, op_ref, lhs, apply_arg_cause(suffix));
        make_app_with_cause(state, app1, rhs, apply_arg_cause(suffix))
    } else {
        acc
    }
}

fn lazy_operator_arg(state: &mut LowerState, op_ref: &TypedExpr, arg: TypedExpr) -> TypedExpr {
    if is_lazy_operator_expr(state, op_ref) {
        unit_thunk_expr(state, arg)
    } else {
        arg
    }
}

fn is_lazy_operator_expr(state: &LowerState, op_ref: &TypedExpr) -> bool {
    matches!(&op_ref.kind, ExprKind::Var(def) if state.ctx.is_lazy_operator_def(*def))
}

fn unit_thunk_expr(state: &mut LowerState, body: TypedExpr) -> TypedExpr {
    let def = state.fresh_def();
    let param_tv = state.fresh_tv();
    let arg_eff_tv = state.fresh_exact_pure_eff_tv();
    let tv = state.fresh_tv();

    state.register_def_tv(def, param_tv);
    if let Some(owner) = state.current_owner {
        state.register_def_owner(def, owner);
    }
    state.infer.constrain(prim_type("unit"), Neg::Var(param_tv));
    state
        .infer
        .constrain(Pos::Var(param_tv), neg_prim_type("unit"));
    state.infer.constrain(
        state.pos_fun(
            Neg::Var(param_tv),
            Neg::Var(arg_eff_tv),
            Pos::Var(body.eff),
            Pos::Var(body.tv),
        ),
        Neg::Var(tv),
    );
    let eff = super::super::stmt::lambda_expr_eff_tv(state, &body, &[def]);
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Lam(def, Box::new(body)),
    }
}

fn apply_index_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    let idx_node = suffix
        .children()
        .find(|c| c.kind() == SyntaxKind::Expr)
        .or_else(|| {
            suffix
                .children()
                .find(|c| c.kind() == SyntaxKind::Bracket)
                .and_then(|bracket| bracket.children().find(|c| c.kind() == SyntaxKind::Expr))
        });
    let Some(idx_node) = idx_node else { return acc };
    let idx = lower_expr(state, &idx_node);
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    let select = push_deferred_selection(
        state,
        acc,
        suffix,
        Name("index".to_string()),
        tv,
        eff,
        false,
        None,
    );
    make_app_with_cause(state, select, idx, apply_arg_cause(suffix))
}

fn apply_arg_cause(suffix: &SyntaxNode) -> ConstraintCause {
    ConstraintCause {
        span: Some(suffix.text_range()),
        reason: ConstraintReason::ApplyArg,
    }
}

fn push_deferred_selection(
    state: &mut LowerState,
    acc: TypedExpr,
    suffix: &SyntaxNode,
    name: Name,
    tv: crate::ids::TypeVar,
    eff: crate::ids::TypeVar,
    structural_record_allowed: bool,
    source_span: Option<rowan::TextRange>,
) -> TypedExpr {
    let owner = state.current_owner;
    if let Some(owner) = owner {
        state.infer.increment_pending_selection(owner);
    }
    state
        .infer
        .deferred_selections
        .borrow_mut()
        .entry(acc.tv)
        .or_default()
        .push(crate::solve::DeferredSelection {
            name: name.clone(),
            module: state.ctx.current_module,
            recv_eff: acc.eff,
            result_tv: tv,
            result_eff: eff,
            owner,
            cause: ConstraintCause {
                span: Some(suffix.text_range()),
                reason: ConstraintReason::FieldSelection,
            },
            structural_record_allowed,
        });
    if let Some(span) = source_span {
        state.record_selection_span(span, tv);
    }
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Select {
            recv: Box::new(acc),
            name,
        },
    }
}
