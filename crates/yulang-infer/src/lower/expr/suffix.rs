use crate::profile::ProfileClock as Instant;

use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{ExprKind, TypedExpr};
use crate::diagnostic::{ConstraintCause, ConstraintReason};
use crate::lower::{LowerState, SyntaxNode};
use crate::solve::DeferredRoleMethodCall;
use crate::symbols::Name;

use super::{
    infix_op_ref, lower_expr, lower_not_equal_infix, lower_short_circuit_infix,
    lower_var_assignment, make_app_with_cause, prefix_op_ref, resolve_path_expr, suffix_op_ref,
    unit_expr,
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
            make_app_with_cause(state, op_ref, acc, apply_arg_cause(suffix))
        }
        SyntaxKind::SuffixNode => {
            let op_ref = suffix_op_ref(state, suffix);
            make_app_with_cause(state, op_ref, acc, apply_arg_cause(suffix))
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
    push_deferred_selection(state, acc, node, name, tv, eff)
}

fn apply_field_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    let name = suffix
        .children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| t.kind() == SyntaxKind::DotField)
        .map(|t| {
            let s = t.text().to_string();
            Name(s.trim_start_matches('.').to_string())
        });
    if let Some(name) = name {
        if let ExprKind::Var(def) = &acc.kind {
            if let Some(path) = state.ctx.resolve_field_alias(*def, &name) {
                return resolve_path_expr(state, path.segments);
            }
        }
        push_deferred_selection(state, acc, suffix, name, tv, eff)
    } else {
        acc
    }
}

fn apply_ml_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
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

fn apply_colon_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    if let Some(arg_node) = suffix.children().find(|c| {
        matches!(
            c.kind(),
            SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        )
    }) {
        let arg = lower_expr(state, &arg_node);
        make_app_with_cause(
            state,
            acc,
            arg,
            ConstraintCause {
                span: Some(suffix.text_range()),
                reason: ConstraintReason::ApplyArg,
            },
        )
    } else {
        acc
    }
}

fn apply_infix_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    if let Some(short_circuit) = lower_short_circuit_infix(state, acc.clone(), suffix) {
        return short_circuit;
    }
    let rhs_node = suffix.children().find(|c| c.kind() == SyntaxKind::Expr);
    if let Some(rhs_node) = rhs_node {
        let rhs = lower_expr(state, &rhs_node);
        if let Some(not_equal) = lower_not_equal_infix(state, acc.clone(), rhs.clone(), suffix) {
            return not_equal;
        }
        let op_ref = infix_op_ref(state, suffix);
        let app1 = make_app_with_cause(state, op_ref, acc, apply_arg_cause(suffix));
        make_app_with_cause(state, app1, rhs, apply_arg_cause(suffix))
    } else {
        acc
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
    let select = push_deferred_selection(state, acc, suffix, Name("index".to_string()), tv, eff);
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
        });
    state
        .infer
        .push_deferred_role_method_call(DeferredRoleMethodCall {
            name: name.clone(),
            recv_tv: acc.tv,
            arg_tvs: Vec::new(),
            result_tv: tv,
        });
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Select {
            recv: Box::new(acc),
            name,
        },
    }
}
