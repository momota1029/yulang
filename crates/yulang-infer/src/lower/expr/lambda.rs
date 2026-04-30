use yulang_parser::lex::SyntaxKind;

use super::super::ann::{
    LoweredEffAnn, configure_arg_effect_from_ann, fresh_arg_effect_tv, lower_pat_ann,
};
use crate::ast::expr::{ExprKind, TypedExpr};
use crate::diagnostic::{TypeOrigin, TypeOriginKind};
use crate::lower::stmt::{bind_pattern_locals, connect_pat_shape_and_locals, lower_pat};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;
use crate::types::{Neg, Pos};

use super::{lower_expr, neg_prim_type, prim_type, unit_expr};

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

    if pat_nodes.len() <= 1 {
        return lower_single_arg_lambda(state, node, pat_nodes.first().cloned());
    }

    let arg_pats: Vec<_> = pat_nodes
        .iter()
        .cloned()
        .map(|pat| {
            super::super::stmt::make_arg_pat_info(
                state,
                super::super::stmt::HeaderArg::Pattern(pat),
            )
        })
        .collect();
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

pub(super) fn make_const_lambda(state: &mut LowerState, body: TypedExpr) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_exact_pure_eff_tv();
    let def = state.fresh_def();
    let param_tv = state.fresh_tv();
    let arg_eff_tv = state.fresh_exact_pure_eff_tv();

    state.register_def_tv(def, param_tv);
    if let Some(owner) = state.current_owner {
        state.register_def_owner(def, owner);
    }

    state.infer.constrain(
        state.pos_fun(
            Neg::Var(param_tv),
            Neg::Var(arg_eff_tv),
            Pos::Var(body.eff),
            Pos::Var(body.tv),
        ),
        Neg::Var(tv),
    );
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Lam(def, Box::new(body)),
    }
}

fn lower_single_arg_lambda(
    state: &mut LowerState,
    node: &SyntaxNode,
    pat_node: Option<SyntaxNode>,
) -> TypedExpr {
    let tv = state.fresh_tv();
    let def = state.fresh_def();
    let has_unit_arg = node.children().any(|child| {
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
    });
    let param_tv = state.fresh_tv_with_origin(TypeOrigin {
        span: pat_node.as_ref().map(|pat| pat.text_range()),
        kind: TypeOriginKind::Param,
        label: None,
    });
    let pat_ann = pat_node.as_ref().and_then(|pat| lower_pat_ann(state, pat));
    let arg_eff_tv = fresh_arg_effect_tv(state, pat_ann.as_ref());
    state.register_def_tv(def, param_tv);
    if let Some(owner) = state.current_owner {
        state.register_def_owner(def, owner);
    }

    state.ctx.push_local();

    let read_eff_tv = pat_ann.as_ref().map(|ann| match ann.eff {
        Some(LoweredEffAnn::Row { .. }) | Some(LoweredEffAnn::Opaque) => state
            .fresh_tv_with_origin(TypeOrigin {
                span: Some(ann.span),
                kind: TypeOriginKind::Annotation,
                label: Some("argument read effect".to_string()),
            }),
        None => state.fresh_exact_pure_eff_tv(),
    });
    if let Some(read_eff_tv) = read_eff_tv {
        state.register_def_eff_tv(def, read_eff_tv);
    }
    if let Some(pat) = &pat_node {
        if let Some(name_tok) = pat
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|t| t.kind() == SyntaxKind::Ident)
        {
            let name = Name(name_tok.text().to_string());
            state.register_def_name(def, name.clone());
            state.ctx.bind_local(name, def);
        } else {
            bind_pattern_locals(state, pat);
        }
    }

    let body = node
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
    if has_unit_arg {
        state.infer.constrain(prim_type("unit"), Neg::Var(param_tv));
        state
            .infer
            .constrain(Pos::Var(param_tv), neg_prim_type("unit"));
    }
    configure_arg_effect_from_ann(state, arg_eff_tv, pat_ann.as_ref());
    if let Some(read_eff_tv) = read_eff_tv {
        if read_eff_tv != arg_eff_tv {
            if let Some(ann) = pat_ann.as_ref() {
                match ann.eff.clone() {
                    Some(LoweredEffAnn::Opaque) => {
                        state.infer.mark_through(read_eff_tv);
                    }
                    Some(LoweredEffAnn::Row { lower, .. }) => {
                        state.infer.constrain(lower, Neg::Var(read_eff_tv));
                    }
                    _ => {}
                }
            }
        }
    }
    if let Some(pat) = &pat_node {
        let pat = lower_pat(state, pat);
        state.infer.constrain(Pos::Var(param_tv), Neg::Var(pat.tv));
        state.infer.constrain(Pos::Var(pat.tv), Neg::Var(param_tv));
        connect_pat_shape_and_locals(state, &pat, body.eff);
    }
    state.ctx.pop_local();
    state.infer.constrain(
        state.pos_fun(
            Neg::Var(param_tv),
            Neg::Var(arg_eff_tv),
            Pos::Var(body.eff),
            Pos::Var(body.tv),
        ),
        Neg::Var(tv),
    );
    let local_defs = vec![def];
    let eff = super::super::stmt::lambda_expr_eff_tv(state, &body, &local_defs);
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Lam(def, Box::new(body)),
    }
}
