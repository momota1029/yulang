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
    for constraint in child_nodes(node, SyntaxKind::WhereConstraint) {
        let type_exprs = child_nodes(&constraint, SyntaxKind::TypeExpr);
        let [lhs, rhs] = type_exprs.as_slice() else {
            continue;
        };
        let Some(lhs_sig) = parse_sig_type_expr(lhs) else {
            continue;
        };
        let Some(rhs_sig) = parse_sig_type_expr(rhs) else {
            continue;
        };
        if !where_sig_vars_are_in_scope(&lhs_sig, &scope)
            || !where_sig_vars_are_in_scope(&rhs_sig, &scope)
        {
            continue;
        }
        let Some((role, rhs_args)) = sig_type_head(&rhs_sig) else {
            continue;
        };
        let role = state.ctx.canonical_current_type_path(&role);
        let mut pos_vars = scope.clone();
        let mut neg_vars = scope.clone();
        let mut args = vec![RoleConstraintArg {
            pos: lower_pure_sig_pos_id(state, &lhs_sig, &mut pos_vars),
            neg: lower_pure_sig_neg_id(state, &lhs_sig, &mut neg_vars),
        }];
        for arg in rhs_args {
            args.push(RoleConstraintArg {
                pos: lower_pure_sig_pos_id(state, &arg, &mut pos_vars),
                neg: lower_pure_sig_neg_id(state, &arg, &mut neg_vars),
            });
        }
        state
            .infer
            .add_role_constraint(owner, RoleConstraint { role, args });
    }
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
