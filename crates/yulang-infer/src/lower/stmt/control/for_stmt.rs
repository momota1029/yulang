use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::TypedExpr;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path};

pub(crate) fn lower_for_stmt(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let iter = for_iter_expr(node)
        .map(|expr| crate::lower::expr::lower_expr(state, &expr))
        .unwrap_or_else(|| crate::lower::expr::unit_expr(state));

    let label_act = for_label(node).and_then(|label| prepare_for_label_act(state, &label));
    if let Some(spec) = &label_act {
        super::super::register_synthetic_act_identity(state, spec);
        super::super::materialize_synthetic_act(
            state,
            spec,
            &std_flow_label_loop_synthetic_act_source(),
        );
    }

    let body = lower_for_body_lambda(state, node);
    let for_in = if let Some(spec) = &label_act {
        crate::lower::expr::resolve_path_expr(
            state,
            vec![spec.name.clone(), Name("for_in".to_string())],
        )
    } else {
        crate::lower::expr::resolve_path_expr(
            state,
            ["std", "flow", "loop", "for_in"]
                .into_iter()
                .map(|segment| Name(segment.to_string()))
                .collect(),
        )
    };
    let applied_iter = crate::lower::expr::make_app(state, for_in, iter);
    crate::lower::expr::make_app(state, applied_iter, body)
}

fn lower_for_body_lambda(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let body_owner = state.current_owner.or_else(|| {
        let owner = state.fresh_def();
        let owner_tv = state.fresh_tv();
        state.register_def_tv(owner, owner_tv);
        Some(owner)
    });

    let mut arg_pats = Vec::new();
    if let Some(label_node) = for_label(node) {
        arg_pats.push(super::super::make_arg_pat_info(
            state,
            super::super::HeaderArg::Pattern(label_node),
        ));
    }
    let pat_node = for_pattern(node);
    if let Some(pat_node) = pat_node {
        arg_pats.push(super::super::make_arg_pat_info(
            state,
            super::super::HeaderArg::Pattern(pat_node),
        ));
    } else {
        arg_pats.push(super::super::make_arg_pat_info(
            state,
            super::super::HeaderArg::Unit,
        ));
    }
    if let Some(owner) = body_owner {
        for arg_pat in &arg_pats {
            state.register_def_owner(arg_pat.def, owner);
            for (_, def) in &arg_pat.local_bindings {
                state.register_def_owner(*def, owner);
            }
        }
    }

    state.ctx.push_local();
    for arg_pat in &arg_pats {
        for (name, def) in &arg_pat.local_bindings {
            state.ctx.bind_local(name.clone(), *def);
        }
    }
    let raw_body = for_body_block(node)
        .map(|body| {
            if let Some(owner) = body_owner {
                state.with_owner(owner, |state| crate::lower::expr::lower_expr(state, &body))
            } else {
                crate::lower::expr::lower_expr(state, &body)
            }
        })
        .unwrap_or_else(|| crate::lower::expr::unit_expr(state));
    state.ctx.pop_local();

    super::super::wrap_header_lambdas(state, raw_body, arg_pats)
}

fn for_label(node: &SyntaxNode) -> Option<SyntaxNode> {
    let header = super::super::child_node(node, SyntaxKind::ForHeader)?;
    super::super::child_node(&header, SyntaxKind::ForLabel)
}

fn prepare_for_label_act(
    state: &mut LowerState,
    label_node: &SyntaxNode,
) -> Option<super::super::SyntheticActSpec> {
    let label_name = for_label_name(label_node)?;
    let unique = state.fresh_synthetic_with_module_name();
    let raw_label = label_name.0.trim_start_matches('\'');
    let name = Name(format!("#loop_label:{}#{}", raw_label, unique.0));
    Some(super::super::nullary_synthetic_act_spec(name))
}

fn for_label_name(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::SigilIdent && token.text().starts_with('\''))
        .map(|token| Name(token.text().to_string()))
}

fn std_flow_label_loop_synthetic_act_source() -> super::super::SyntheticActSource {
    super::super::SyntheticActSource {
        source_module_path: std_flow_label_loop_path(),
        source_copy_path: Path {
            segments: vec![Name("label_loop".to_string())],
        },
        selected_values: ["last", "next", "redo", "control_label", "for_in"]
            .into_iter()
            .map(|segment| Name(segment.to_string()))
            .collect(),
        selected_template_items: vec![Name("label".to_string()), Name("LoopLabel".to_string())],
    }
}

fn std_flow_label_loop_path() -> Path {
    Path {
        segments: ["std", "flow", "label_loop"]
            .into_iter()
            .map(|segment| Name(segment.to_string()))
            .collect(),
    }
}

fn for_pattern(node: &SyntaxNode) -> Option<SyntaxNode> {
    let header = super::super::child_node(node, SyntaxKind::ForHeader)?;
    header.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Pattern | SyntaxKind::PatOr | SyntaxKind::PatAs | SyntaxKind::PatParenGroup
        )
    })
}

fn for_iter_expr(node: &SyntaxNode) -> Option<SyntaxNode> {
    let header = super::super::child_node(node, SyntaxKind::ForHeader)?;
    header
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)
}

fn for_body_block(node: &SyntaxNode) -> Option<SyntaxNode> {
    let body = super::super::child_node(node, SyntaxKind::ForBody)?;
    body.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup | SyntaxKind::Expr
        )
    })
}
