use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::ExprKind;
use crate::ast::expr::TypedExpr;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;
use crate::types::{Neg, Pos};

use super::{apply_suffix, lower_expr, resolve_bound_def_expr, unit_expr};

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

pub(super) fn lower_method_lambda(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let receiver_def = state.fresh_def();
    let receiver_tv = state.fresh_tv();
    state.register_def_tv(receiver_def, receiver_tv);
    state.register_def_name(receiver_def, Name("#method-receiver".to_string()));
    if let Some(owner) = state.current_owner {
        state.register_def_owner(receiver_def, owner);
    }

    let mut body = resolve_bound_def_expr(state, receiver_def);
    for suffix in node.children().filter(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Field
                | SyntaxKind::ApplyML
                | SyntaxKind::ApplyC
                | SyntaxKind::ApplyColon
                | SyntaxKind::Index
                | SyntaxKind::InfixNode
                | SyntaxKind::SuffixNode
                | SyntaxKind::PrefixNode
        )
    }) {
        body = apply_suffix(state, body, &suffix);
    }

    let tv = state.fresh_tv();
    let arg_eff_tv = state.fresh_exact_pure_eff_tv();
    state.infer.constrain(
        state.pos_fun(
            Neg::Var(receiver_tv),
            Neg::Var(arg_eff_tv),
            Pos::Var(body.eff),
            Pos::Var(body.tv),
        ),
        Neg::Var(tv),
    );
    let eff = super::super::stmt::lambda_expr_eff_tv(state, &body, &[receiver_def]);
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Lam(receiver_def, Box::new(body)),
    }
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
