use std::collections::{HashMap, HashSet};

use yulang_parser::lex::SyntaxKind;

use super::signature::{
    SigType, collect_all_sig_vars, lower_pure_sig_neg_id, lower_pure_sig_pos_id,
    parse_sig_type_expr, sig_type_head,
};
use super::stmt::child_nodes;
use super::{LowerState, SyntaxNode};
use crate::solve::{RoleConstraint, RoleConstraintArg};

pub(super) fn lower_where_clause(state: &mut LowerState, node: &SyntaxNode) {
    let Some(owner) = state.current_owner else {
        return;
    };
    let Some(scope) = state.current_type_scope().cloned() else {
        return;
    };
    for predicate in child_nodes(node, SyntaxKind::WherePredicate) {
        lower_where_predicate(state, owner, &scope, &predicate);
    }
}

fn lower_where_predicate(
    state: &mut LowerState,
    owner: crate::ids::DefId,
    scope: &HashMap<String, crate::ids::TypeVar>,
    predicate: &SyntaxNode,
) {
    let type_exprs = child_nodes(predicate, SyntaxKind::TypeExpr);
    match type_exprs.as_slice() {
        [direct] => lower_direct_where_predicate(state, owner, scope, direct),
        [lhs, rhs] => lower_colon_where_predicate(state, owner, scope, lhs, rhs),
        _ => {}
    }
}

fn lower_direct_where_predicate(
    state: &mut LowerState,
    owner: crate::ids::DefId,
    scope: &HashMap<String, crate::ids::TypeVar>,
    predicate: &SyntaxNode,
) {
    let Some(sig) = parse_sig_type_expr(predicate) else {
        return;
    };
    if !where_sig_vars_are_in_scope(&sig, scope) {
        return;
    }
    let Some((role, args)) = sig_type_head(&sig) else {
        return;
    };
    lower_role_constraint(state, owner, scope, role, args);
}

fn lower_colon_where_predicate(
    state: &mut LowerState,
    owner: crate::ids::DefId,
    scope: &HashMap<String, crate::ids::TypeVar>,
    lhs: &SyntaxNode,
    rhs: &SyntaxNode,
) {
    let Some(lhs_sig) = parse_sig_type_expr(lhs) else {
        return;
    };
    let Some(rhs_sig) = parse_sig_type_expr(rhs) else {
        return;
    };
    if !where_sig_vars_are_in_scope(&lhs_sig, scope)
        || !where_sig_vars_are_in_scope(&rhs_sig, scope)
    {
        return;
    }
    let Some((role, rhs_args)) = sig_type_head(&rhs_sig) else {
        return;
    };
    lower_role_constraint(
        state,
        owner,
        scope,
        role,
        std::iter::once(lhs_sig).chain(rhs_args).collect(),
    );
}

fn lower_role_constraint(
    state: &mut LowerState,
    owner: crate::ids::DefId,
    scope: &HashMap<String, crate::ids::TypeVar>,
    role: crate::symbols::Path,
    args: Vec<SigType>,
) {
    let role = state.ctx.canonical_current_type_path(&role);
    let mut pos_vars = scope.clone();
    let mut neg_vars = scope.clone();
    let args = args
        .into_iter()
        .map(|arg| RoleConstraintArg {
            pos: lower_pure_sig_pos_id(state, &arg, &mut pos_vars),
            neg: lower_pure_sig_neg_id(state, &arg, &mut neg_vars),
        })
        .collect();
    state
        .infer
        .add_role_constraint(owner, RoleConstraint { role, args });
}

fn where_sig_vars_are_in_scope(
    sig: &SigType,
    scope: &HashMap<String, crate::ids::TypeVar>,
) -> bool {
    let mut names = HashSet::new();
    collect_all_sig_vars(sig, &mut names);
    names.retain(|name| name != "_");
    names.into_iter().all(|name| scope.contains_key(&name))
}
