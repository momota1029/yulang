use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{ExprKind, TypedExpr};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;
use crate::types::{Neg, Pos};

/// `do` より前の通常 Binding を先行走査して DefId を確保・登録する。
pub(crate) fn preregister_items_until_do(state: &mut LowerState, items: &[SyntaxNode]) {
    for child in items {
        match child.kind() {
            SyntaxKind::Binding if binding_is_do_binding(child) => break,
            SyntaxKind::Expr if node_has_do_here(child) => break,
            SyntaxKind::Binding | SyntaxKind::OpDef => {
                super::super::preregister_binding(state, child);
            }
            _ => {}
        }
    }
}

pub(crate) fn lower_do_binding(
    state: &mut LowerState,
    binding: &SyntaxNode,
    suffix_items: &[SyntaxNode],
) -> Option<TypedExpr> {
    let param_name = do_binding_name(binding)?;
    let rhs = binding_direct_rhs_expr(binding)?;

    let def = state.fresh_def();
    let param_tv = state.fresh_tv();
    let arg_eff_tv = state.fresh_exact_pure_eff_tv();
    state.register_def_tv(def, param_tv);
    if let Some(owner) = state.current_owner {
        state.register_def_owner(def, owner);
    }
    state.register_def_name(def, param_name.clone());

    state.ctx.push_local();
    state.ctx.bind_local(param_name, def);
    let body = lower_block_expr_from_items(state, suffix_items);
    state.ctx.pop_local();

    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    super::super::configure_arg_effect_from_ann(state, arg_eff_tv, None);
    state.infer.constrain(
        state.pos_fun(
            Neg::Var(param_tv),
            Neg::Var(arg_eff_tv),
            Pos::Var(body.eff),
            Pos::Var(body.tv),
        ),
        Neg::Var(tv),
    );
    state
        .infer
        .constrain(state.infer.arena.empty_pos_row, Neg::Var(eff));
    let replacement = TypedExpr {
        tv,
        eff,
        kind: ExprKind::Lam(def, Box::new(body)),
    };

    let saved_do = state.do_replacement.replace(replacement);
    let lowered = crate::lower::expr::lower_expr(state, &rhs);
    state.do_replacement = saved_do;
    Some(lowered)
}

pub(crate) fn lower_do_expr(
    state: &mut LowerState,
    expr: &SyntaxNode,
    suffix_items: &[SyntaxNode],
) -> TypedExpr {
    let replacement = lower_block_expr_from_items(state, suffix_items);
    let saved_do = state.do_replacement.replace(replacement);
    let lowered = crate::lower::expr::lower_expr(state, expr);
    state.do_replacement = saved_do;
    lowered
}

pub(crate) fn lower_block_expr_from_items(
    state: &mut LowerState,
    items: &[SyntaxNode],
) -> TypedExpr {
    if items.is_empty() {
        return crate::lower::expr::unit_expr(state);
    }

    let block = super::lower_block_from_items(state, items);
    TypedExpr {
        tv: block.tv,
        eff: block.eff,
        kind: ExprKind::Block(block),
    }
}

pub(crate) fn lower_expr_with_synthetic_owner_if_top_level(
    state: &mut LowerState,
    node: &SyntaxNode,
) -> TypedExpr {
    if state.current_owner.is_some() || state.suppress_top_level_expr_owners() {
        return crate::lower::expr::lower_expr(state, node);
    }

    let owner = state.fresh_def();
    let owner_tv = state.fresh_tv();
    state.register_def_tv(owner, owner_tv);
    let expr = state.with_owner(owner, |state| crate::lower::expr::lower_expr(state, node));
    state.infer.constrain(
        crate::types::Pos::Var(expr.tv),
        crate::types::Neg::Var(owner_tv),
    );
    state.infer.constrain(
        crate::types::Pos::Var(owner_tv),
        crate::types::Neg::Var(expr.tv),
    );
    state.principal_bodies.insert(owner, expr.clone());
    state.record_top_level_expr_owner(owner);
    expr
}

pub(crate) fn binding_is_do_binding(binding: &SyntaxNode) -> bool {
    do_binding_name(binding).is_some()
        && binding_direct_rhs_expr(binding)
            .as_ref()
            .is_some_and(node_has_do_here)
}

fn do_binding_name(binding: &SyntaxNode) -> Option<Name> {
    let header = super::super::child_node(binding, SyntaxKind::BindingHeader)?;
    let pat = super::super::child_node(&header, SyntaxKind::Pattern)?;
    let has_args = pat.children().any(|child| {
        matches!(
            child.kind(),
            SyntaxKind::ApplyML | SyntaxKind::ApplyC | SyntaxKind::ApplyColon
        )
    });
    if has_args {
        return None;
    }
    super::super::ident_name(&pat)
}

fn binding_direct_rhs_expr(binding: &SyntaxNode) -> Option<SyntaxNode> {
    let body = super::super::child_node(binding, SyntaxKind::BindingBody)?;
    if super::super::child_node(&body, SyntaxKind::IndentBlock)
        .or_else(|| super::super::child_node(&body, SyntaxKind::BraceGroup))
        .is_some()
    {
        return None;
    }
    super::super::child_node(&body, SyntaxKind::Expr)
}

pub(crate) fn node_has_do_here(node: &SyntaxNode) -> bool {
    for item in node.children_with_tokens() {
        match item {
            rowan::NodeOrToken::Token(token) if token.kind() == SyntaxKind::Do => return true,
            rowan::NodeOrToken::Node(child) => {
                if matches!(
                    child.kind(),
                    SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
                ) {
                    continue;
                }
                if node_has_do_here(&child) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}
