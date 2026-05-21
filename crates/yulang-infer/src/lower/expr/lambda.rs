use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{ExprKind, PatKind, TypedBlock, TypedExpr, TypedPat, TypedStmt};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;
use crate::types::{Neg, Pos};

use super::{apply_suffix, lower_expr, resolve_bound_def_expr, unit_expr};

pub(super) fn lower_lambda(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let pat_nodes = lambda_pat_nodes(node);
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

pub(super) fn lower_recursive_lambda(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let Some(label_name) = recursive_lambda_label_name(node) else {
        return lower_lambda(state, node);
    };

    let self_def = state.fresh_def();
    let self_tv = state.fresh_tv();
    state.register_def_tv(self_def, self_tv);
    state.mark_let_bound_def(self_def);
    state.register_def_name(self_def, label_name.clone());
    if let Some(owner) = state.current_owner {
        state.register_def_owner(self_def, owner);
    }

    let arg_pats = lambda_arg_pats(state, node, lambda_pat_nodes(node));
    super::super::stmt::preconstrain_recursive_binding_header_shape(
        state, self_def, &arg_pats, None,
    );

    state.ctx.push_local();
    state.ctx.bind_local(label_name, self_def);
    for arg_pat in &arg_pats {
        for (name, def) in &arg_pat.local_bindings {
            state.ctx.bind_local(name.clone(), *def);
        }
    }
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
    for arg_pat in &arg_pats {
        state.register_def_owner(arg_pat.def, self_def);
        for (_, def) in &arg_pat.local_bindings {
            state.register_def_owner(*def, self_def);
        }
    }
    let raw_body = state.with_owner(self_def, |state| {
        node.children()
            .filter(|c| {
                matches!(
                    c.kind(),
                    SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
                )
            })
            .last()
            .map(|b| lower_expr(state, &b))
            .unwrap_or_else(|| unit_expr(state))
    });
    state.deactivate_recursive_self_instance(self_def);
    state.ctx.pop_local();

    let body_expr = super::super::stmt::wrap_header_lambdas(state, raw_body, arg_pats);
    state.insert_principal_body(self_def, body_expr.clone());
    let self_used = state.take_recursive_self_use(self_def);
    if self_used {
        state.mark_recursive_binding(self_def);
    }

    let bind_pat = recursive_lambda_bind_pat(state, self_def);
    super::super::stmt::connect_let_pattern(
        state,
        &bind_pat,
        body_expr.tv,
        body_expr.eff,
        Some(node.text_range()),
        self_used,
    );
    let tail = resolve_bound_def_expr(state, self_def);
    block_expr_from_parts(state, vec![TypedStmt::Let(bind_pat, body_expr)], tail)
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

fn lambda_pat_nodes(node: &SyntaxNode) -> Vec<SyntaxNode> {
    node.children()
        .filter(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Pattern
                    | SyntaxKind::PatOr
                    | SyntaxKind::PatAs
                    | SyntaxKind::PatParenGroup
            )
        })
        .collect()
}

fn recursive_lambda_label_name(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::SigilIdent && token.text().starts_with('\''))
        .map(|token| Name(token.text().to_string()))
}

fn recursive_lambda_bind_pat(state: &mut LowerState, self_def: crate::ids::DefId) -> TypedPat {
    TypedPat {
        tv: state.fresh_tv(),
        kind: PatKind::As(
            Box::new(TypedPat {
                tv: state.fresh_tv(),
                kind: PatKind::Wild,
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
