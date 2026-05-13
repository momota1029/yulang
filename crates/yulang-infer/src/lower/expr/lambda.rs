use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::TypedExpr;
use crate::lower::{LowerState, SyntaxNode};

use super::{lower_expr, unit_expr};

pub(super) fn lower_lambda(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let pat_nodes: Vec<_> = node
        .children()
        .filter(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Pattern
                    | SyntaxKind::PatOr
                    | SyntaxKind::PatAs
                    | SyntaxKind::PatParenGroup
            )
        })
        .collect();

    let arg_pats = lambda_arg_pats(state, node, pat_nodes);
    if let Some(owner) = state.current_owner {
        for arg_pat in &arg_pats {
            state.register_def_owner(arg_pat.def, owner);
            for (_, def) in &arg_pat.local_bindings {
                state.register_def_owner(*def, owner);
            }
        }
    }

    state.ctx.push_local();
    for (name, def) in arg_pats
        .iter()
        .flat_map(|arg_pat| arg_pat.local_bindings.iter())
    {
        state.ctx.bind_local(name.clone(), *def);
    }

    let raw_body = node
        .children()
        .filter(|c| {
            matches!(
                c.kind(),
                SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
            )
        })
        .last()
        .map(|b| lower_expr(state, &b))
        .unwrap_or_else(|| unit_expr(state));
    state.ctx.pop_local();
    super::super::stmt::wrap_header_lambdas(state, raw_body, arg_pats)
}

fn lambda_arg_pats(
    state: &mut LowerState,
    node: &SyntaxNode,
    pat_nodes: Vec<SyntaxNode>,
) -> Vec<super::super::stmt::ArgPatInfo> {
    let args = if pat_nodes.is_empty() && lambda_has_unit_arg(node) {
        vec![super::super::stmt::HeaderArg::Unit]
    } else {
        pat_nodes
            .into_iter()
            .map(super::super::stmt::HeaderArg::Pattern)
            .collect()
    };

    args.into_iter()
        .map(|arg| super::super::stmt::make_arg_pat_info(state, arg))
        .collect()
}

fn lambda_has_unit_arg(node: &SyntaxNode) -> bool {
    node.children().any(|child| {
        child.kind() == SyntaxKind::ApplyC
            && !child.children().any(|grandchild| {
                matches!(
                    grandchild.kind(),
                    SyntaxKind::Pattern
                        | SyntaxKind::PatOr
                        | SyntaxKind::PatAs
                        | SyntaxKind::PatParenGroup
                )
            })
    })
}
