use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::TypedExpr;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};

pub(crate) fn lower_for_stmt(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let iter_node = for_iter_expr(node);
    let iter = iter_node
        .as_ref()
        .map(|expr| crate::lower::expr::lower_expr(state, &expr))
        .unwrap_or_else(|| crate::lower::expr::unit_expr(state));

    let label_act = for_label(node).and_then(|label| prepare_for_label_act(state, &label));
    if let Some(spec) = &label_act {
        super::super::register_synthetic_act_identity(state, spec);
        super::super::materialize_synthetic_act(
            state,
            spec,
            &standard_label_loop_synthetic_act_source(),
        );
    }

    let body = lower_for_body_lambda(state, node, iter_node.as_ref(), &iter, label_act.as_ref());
    let for_in = if let Some(spec) = &label_act {
        crate::lower::expr::resolve_path_expr(
            state,
            vec![spec.name.clone(), Name("for_in".to_string())],
        )
    } else {
        crate::lower::expr::resolve_path_expr(
            state,
            crate::std_flow_paths::standard_loop_for_in_path(),
        )
    };
    let applied_iter = crate::lower::expr::make_app(state, for_in, iter);
    crate::lower::expr::make_app(state, applied_iter, body)
}

fn lower_for_body_lambda(
    state: &mut LowerState,
    node: &SyntaxNode,
    iter_node: Option<&SyntaxNode>,
    iter: &TypedExpr,
    label_act: Option<&super::super::SyntheticActSpec>,
) -> TypedExpr {
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
    if iter_node.is_some_and(iter_expr_is_list_literal)
        && let Some(item_arg) = arg_pats.last()
        && !item_arg.unit_arg
    {
        constrain_iter_list_item(state, iter, item_arg.tv);
    }
    if iter_node.is_some_and(iter_expr_is_range)
        && let Some(item_arg) = arg_pats.last()
        && !item_arg.unit_arg
    {
        constrain_iter_range_item(state, iter, item_arg.tv);
    }
    if let Some(spec) = label_act
        && let Some(label_arg) = arg_pats.first()
        && !label_arg.unit_arg
    {
        constrain_for_label_arg(state, spec, label_arg.tv);
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

fn iter_expr_is_list_literal(node: &SyntaxNode) -> bool {
    node.kind() == SyntaxKind::Bracket
        || node
            .children()
            .any(|child| child.kind() == SyntaxKind::Bracket)
}

fn constrain_iter_list_item(
    state: &mut LowerState,
    iter: &TypedExpr,
    item_tv: crate::ids::TypeVar,
) {
    let list_path = state.builtin_source_type_path("list");
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    state.infer.constrain(
        state.pos_con(list_path.clone(), list_args.clone()),
        Neg::Var(iter.tv),
    );
    state
        .infer
        .constrain(Pos::Var(iter.tv), state.neg_con(list_path, list_args));
}

fn iter_expr_is_range(node: &SyntaxNode) -> bool {
    expr_contains_range_operator(node) || expr_starts_with_standard_range_constructor(node)
}

fn expr_contains_range_operator(node: &SyntaxNode) -> bool {
    node.children_with_tokens().any(|item| {
        item.into_token().is_some_and(|token| {
            matches!(
                token.kind(),
                SyntaxKind::Infix | SyntaxKind::Prefix | SyntaxKind::Suffix | SyntaxKind::Nullfix
            ) && token.text().contains("..")
        })
    }) || node
        .children()
        .any(|child| expr_contains_range_operator(&child))
}

fn expr_starts_with_standard_range_constructor(node: &SyntaxNode) -> bool {
    let mut segments = Vec::new();
    for item in node.children_with_tokens() {
        match item {
            rowan::NodeOrToken::Token(token) if token.kind() == SyntaxKind::Ident => {
                segments.push(token.text().to_string());
            }
            rowan::NodeOrToken::Node(child) if child.kind() == SyntaxKind::PathSep => {
                if let Some(segment) = child
                    .children_with_tokens()
                    .filter_map(|item| item.into_token())
                    .find(|token| token.kind() == SyntaxKind::Ident)
                {
                    segments.push(segment.text().to_string());
                }
            }
            rowan::NodeOrToken::Token(token)
                if matches!(token.kind(), SyntaxKind::Space | SyntaxKind::LineComment) => {}
            _ => break,
        }
    }

    matches!(
        segments.as_slice(),
        [std, range, constructor]
            if std == "std"
                && range == "range"
                && matches!(
                    constructor.as_str(),
                    "range"
                        | "inclusive"
                        | "exclusive"
                        | "from_exclusive_to_inclusive"
                        | "from_included"
                        | "from_excluded"
                        | "to_included"
                        | "to_excluded"
                        | "full"
                )
    )
}

fn constrain_iter_range_item(
    state: &mut LowerState,
    iter: &TypedExpr,
    item_tv: crate::ids::TypeVar,
) {
    let range_path = state.builtin_source_type_path("range");
    state
        .infer
        .constrain(state.pos_con(range_path.clone(), vec![]), Neg::Var(iter.tv));
    state
        .infer
        .constrain(Pos::Var(iter.tv), state.neg_con(range_path, vec![]));
    state
        .infer
        .constrain(super::super::prim_type("int"), Neg::Var(item_tv));
    state
        .infer
        .constrain(Pos::Var(item_tv), super::super::neg_prim_type("int"));
}

fn constrain_for_label_arg(
    state: &mut LowerState,
    spec: &super::super::SyntheticActSpec,
    label_tv: crate::ids::TypeVar,
) {
    let label_path = Path {
        segments: vec![spec.name.clone(), Name("label".to_string())],
    };
    state.infer.constrain(
        state.pos_con(label_path.clone(), vec![]),
        Neg::Var(label_tv),
    );
    state
        .infer
        .constrain(Pos::Var(label_tv), state.neg_con(label_path, vec![]));
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

fn standard_label_loop_synthetic_act_source() -> super::super::SyntheticActSource {
    super::super::SyntheticActSource {
        source_module_path: crate::std_flow_paths::standard_label_loop_path(),
        source_copy_path: Path {
            segments: vec![Name("label_loop".to_string())],
        },
        selected_values: ["last", "next", "redo", "control_label", "for_in"]
            .into_iter()
            .map(|segment| Name(segment.to_string()))
            .collect(),
        selected_template_items: ["last", "next", "redo", "label", "LoopLabel"]
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
