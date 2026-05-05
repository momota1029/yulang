use crate::profile::ProfileClock as Instant;

use rowan::NodeOrToken;
use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::TypedExpr;
use crate::diagnostic::{ConstraintCause, ConstraintReason};
use crate::lower::{LowerState, SyntaxNode, stmt};
use crate::symbols::{Name, OperatorFixity, Path};

use super::{
    apply_suffix, lower_expr, lower_expr_atom, lower_number_token, lower_var_read_expr,
    make_app_with_cause, resolve_operator_expr, resolve_path_expr, try_resolve_local_operator_expr,
    try_resolve_operator_expr, unit_expr,
};

// ── chain lowering ────────────────────────────────────────────────────────────

/// Expr ノード（ヘッド + サフィックス列）を左結合で畳む。
pub(super) fn lower_expr_chain(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let start = Instant::now();
    let result = if let Some(with_block) = node
        .children()
        .find(|child| child.kind() == SyntaxKind::WithBlock)
    {
        lower_with_expr_chain(state, node, &with_block, None)
    } else {
        lower_expr_chain_prefix(state, node, false)
    };
    state.lower_detail.lower_expr_chain += start.elapsed();
    result
}

fn lower_expr_chain_prefix(
    state: &mut LowerState,
    node: &SyntaxNode,
    stop_at_with: bool,
) -> TypedExpr {
    lower_expr_chain_prefix_with_pipe_arg(state, node, stop_at_with, None)
}

fn lower_expr_chain_prefix_with_pipe_arg(
    state: &mut LowerState,
    node: &SyntaxNode,
    stop_at_with: bool,
    pipe_arg: Option<PipeArg>,
) -> TypedExpr {
    (|| {
        use NodeOrToken::*;

        let mut items = node.children_with_tokens().peekable();
        let mut pipe_arg = pipe_arg;

        while matches!(
            items.peek(),
            Some(Token(t)) if matches!(t.kind(), SyntaxKind::Space | SyntaxKind::LineComment)
        ) {
            items.next();
        }

        let Some(head) = items.next() else {
            return unit_expr(state);
        };

        let mut path_segs: Vec<Name> = Vec::new();
        let mut head_expr: Option<TypedExpr> = None;
        let mut nullfix_head: Option<Name> = None;

        match &head {
            Token(t) if t.kind() == SyntaxKind::SigilIdent && t.text().starts_with('$') => {
                head_expr = Some(lower_var_read_expr(state, t.text()));
            }
            Token(t) if matches!(t.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent) => {
                path_segs.push(Name(t.text().to_string()));
            }
            Token(t) if t.kind() == SyntaxKind::Do => {
                let expr = state
                    .do_replacement
                    .clone()
                    .unwrap_or_else(|| unit_expr(state));
                head_expr = Some(expr);
            }
            Node(n) if n.kind() == SyntaxKind::Expr => {
                head_expr = Some(lower_expr(state, n));
            }
            Node(n) => {
                head_expr = Some(lower_expr_atom(state, n));
            }
            Token(t) if t.kind() == SyntaxKind::BraceL => {
                let Some(brace) = node.children().find(|c| c.kind() == SyntaxKind::BraceGroup)
                else {
                    return unit_expr(state);
                };
                head_expr = Some(lower_expr_atom(state, &brace));
            }
            Token(t) if t.kind() == SyntaxKind::Number => {
                let expr = lower_number_token(state, t.text(), Some(t.text_range()));
                head_expr = Some(expr);
            }
            Token(t) if t.kind() == SyntaxKind::Nullfix => {
                let name = Name(t.text().to_string());
                nullfix_head = Some(name.clone());
                head_expr = Some(resolve_nullfix_operator_expr(state, name, t.text_range()));
            }
            _ => return unit_expr(state),
        }

        while matches!(
            items.peek(),
            Some(Token(t)) if matches!(t.kind(), SyntaxKind::Space | SyntaxKind::LineComment)
        ) {
            items.next();
        }

        while let Some(item) = items.peek() {
            match item {
                Node(n) if n.kind() == SyntaxKind::PathSep => {
                    if let Some(seg) = path_sep_ident(n) {
                        path_segs.push(seg);
                    }
                    items.next();
                    while matches!(
                        items.peek(),
                        Some(Token(t))
                            if matches!(t.kind(), SyntaxKind::Space | SyntaxKind::LineComment)
                    ) {
                        items.next();
                    }
                }
                _ => break,
            }
        }

        let special_prefix_acc = if let Some(op_name) = nullfix_head
            .as_ref()
            .filter(|name| is_loop_control_op(name))
        {
            match items.peek() {
                Some(Node(n)) if n.kind() == SyntaxKind::ApplyML => {
                    let arg = label_arg_expr(n);
                    let node = n.clone();
                    arg.map(|arg| {
                        items.next();
                        let op_ref =
                            resolve_operator_expr(state, op_name.clone(), OperatorFixity::Prefix);
                        let arg = lower_expr(state, &arg);
                        make_app_with_cause(
                            state,
                            op_ref,
                            arg,
                            ConstraintCause {
                                span: Some(node.text_range()),
                                reason: ConstraintReason::ApplyArg,
                            },
                        )
                    })
                }
                _ => None,
            }
        } else {
            None
        };

        let mut acc = if let Some(expr) = special_prefix_acc {
            expr
        } else if head_expr.is_none() && path_segs.len() == 1 && path_segs[0].0 == "sub" {
            if let Some(expr) = lower_sub_syntax(state, &mut items) {
                expr
            } else {
                resolve_path_expr(state, path_segs)
            }
        } else if let Some(expr) = head_expr {
            expr
        } else {
            resolve_path_expr(state, path_segs)
        };
        if let Some(pipe_arg) = pipe_arg.take() {
            acc = make_app_with_cause(
                state,
                acc,
                pipe_arg.expr,
                ConstraintCause {
                    span: pipe_arg.span,
                    reason: ConstraintReason::ApplyArg,
                },
            );
        }

        while let Some(item) = items.next() {
            match item {
                Token(t) if matches!(t.kind(), SyntaxKind::Space | SyntaxKind::LineComment) => {
                    continue;
                }
                Node(n) if stop_at_with && n.kind() == SyntaxKind::WithBlock => break,
                Node(n) => {
                    if n.kind() == SyntaxKind::Field {
                        if let Some(path) = qualified_method_path_from_field(&n, &mut items) {
                            let callee = resolve_path_expr(state, path);
                            acc = make_app_with_cause(
                                state,
                                callee,
                                acc,
                                ConstraintCause {
                                    span: Some(n.text_range()),
                                    reason: ConstraintReason::ApplyArg,
                                },
                            );
                            continue;
                        }
                    }
                    acc = if n.kind() == SyntaxKind::PipeNode {
                        apply_pipe_node(state, acc, &n)
                    } else {
                        apply_suffix(state, acc, &n)
                    };
                }
                _ => {}
            }
        }

        acc
    })()
}

fn resolve_nullfix_operator_expr(
    state: &mut LowerState,
    name: Name,
    span: rowan::TextRange,
) -> TypedExpr {
    if let Some(expr) = try_resolve_local_operator_expr(state, &name, OperatorFixity::Nullfix) {
        return expr;
    }
    if let Some(prefix) = try_resolve_local_operator_expr(state, &name, OperatorFixity::Prefix) {
        return apply_prefix_operator_to_unit(state, prefix, span);
    }
    if let Some(expr) = try_resolve_operator_expr(state, &name, OperatorFixity::Nullfix) {
        return expr;
    }
    resolve_operator_expr(state, name, OperatorFixity::Nullfix)
}

fn apply_prefix_operator_to_unit(
    state: &mut LowerState,
    prefix: TypedExpr,
    span: rowan::TextRange,
) -> TypedExpr {
    let unit = unit_expr(state);
    make_app_with_cause(
        state,
        prefix,
        unit,
        ConstraintCause {
            span: Some(span),
            reason: ConstraintReason::ApplyArg,
        },
    )
}

fn lower_with_expr_chain(
    state: &mut LowerState,
    node: &SyntaxNode,
    with_block: &SyntaxNode,
    pipe_arg: Option<PipeArg>,
) -> TypedExpr {
    let mut items = Vec::new();
    for child in with_block.children() {
        match child.kind() {
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup => {
                stmt::collect_block_items(&child, &mut items);
            }
            _ => items.push(child),
        }
    }

    stmt::lower_scoped_with_block_expr_with_tail(state, &items, move |state| {
        lower_expr_chain_prefix_with_pipe_arg(state, node, true, pipe_arg)
    })
}

fn apply_pipe_node(state: &mut LowerState, acc: TypedExpr, node: &SyntaxNode) -> TypedExpr {
    let Some(rhs) = node
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)
    else {
        return acc;
    };
    let pipe_arg = PipeArg {
        expr: acc,
        span: Some(node.text_range()),
    };
    if let Some(with_block) = rhs
        .children()
        .find(|child| child.kind() == SyntaxKind::WithBlock)
    {
        return lower_with_expr_chain(state, &rhs, &with_block, Some(pipe_arg));
    }
    lower_expr_chain_prefix_with_pipe_arg(state, &rhs, false, Some(pipe_arg))
}

fn lower_sub_syntax(state: &mut LowerState, items: &mut ChainItems) -> Option<TypedExpr> {
    let mut probe = items.clone();
    skip_chain_trivia(&mut probe);
    let has_label = match probe.peek() {
        Some(NodeOrToken::Node(node)) if node.kind() == SyntaxKind::ApplyML => {
            label_arg_expr(node).is_some()
        }
        _ => false,
    };
    if has_label {
        probe.next();
        skip_chain_trivia(&mut probe);
    }
    let Some(NodeOrToken::Node(colon)) = probe.peek() else {
        return None;
    };
    if colon.kind() != SyntaxKind::ApplyColon {
        return None;
    }

    skip_chain_trivia(items);
    let label = match items.peek() {
        Some(NodeOrToken::Node(node)) if node.kind() == SyntaxKind::ApplyML => {
            label_arg_expr(node).map(|expr| (node.clone(), expr))
        }
        _ => None,
    };
    if label.is_some() {
        items.next();
        skip_chain_trivia(items);
    }
    let Some(NodeOrToken::Node(colon)) = items.peek() else {
        return None;
    };
    let colon = colon.clone();
    items.next();

    let body = colon.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        )
    })?;
    match label {
        None => {
            let sub = resolve_path_expr(state, std_flow_sub_path("sub"));
            state.ctx.push_local();
            bind_unlabeled_sub_operator_helpers(state);
            let body = lower_expr(state, &body);
            state.ctx.pop_local();
            Some(make_app_with_cause(
                state,
                sub,
                body,
                ConstraintCause {
                    span: Some(colon.text_range()),
                    reason: ConstraintReason::ApplyArg,
                },
            ))
        }
        Some((_label_apply, label_expr)) => {
            let Some(label_name) = label_sigil_name(&label_expr) else {
                return None;
            };
            let spec = prepare_sub_label_act(state, &label_name);
            stmt::register_synthetic_act_identity(state, &spec);
            materialize_sub_label_act_helpers(state, &spec);

            let label_arg = stmt::make_arg_pat_info(state, stmt::HeaderArg::Pattern(label_expr));
            if let Some(owner) = state.current_owner {
                state.register_def_owner(label_arg.def, owner);
                for (_, def) in &label_arg.local_bindings {
                    state.register_def_owner(*def, owner);
                }
            }
            state.ctx.push_local();
            bind_sub_label_operator_helpers(state, &spec);
            bind_sub_label_field_helpers(state, label_arg.def, &spec);
            for (name, def) in &label_arg.local_bindings {
                state.ctx.bind_local(name.clone(), *def);
                bind_sub_label_field_helpers(state, *def, &spec);
            }
            let raw_body = lower_expr(state, &body);
            state.ctx.pop_local();
            let lambda = stmt::wrap_header_lambdas(state, raw_body, vec![label_arg]);
            let control_label = resolve_path_expr(
                state,
                vec![spec.name.clone(), Name("control_label".to_string())],
            );
            let arg = make_app_with_cause(
                state,
                lambda,
                control_label,
                ConstraintCause {
                    span: Some(colon.text_range()),
                    reason: ConstraintReason::ApplyArg,
                },
            );
            let sub = resolve_path_expr(state, vec![spec.name, Name("sub".to_string())]);
            Some(make_app_with_cause(
                state,
                sub,
                arg,
                ConstraintCause {
                    span: Some(colon.text_range()),
                    reason: ConstraintReason::ApplyArg,
                },
            ))
        }
    }
}

fn std_flow_sub_path(name: &str) -> Vec<Name> {
    ["std", "flow", "sub", name]
        .into_iter()
        .map(|segment| Name(segment.to_string()))
        .collect()
}

fn label_sigil_name(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::SigilIdent && token.text().starts_with('\''))
        .map(|token| Name(token.text().to_string()))
}

fn prepare_sub_label_act(state: &mut LowerState, label_name: &Name) -> stmt::SyntheticActSpec {
    let unique = state.fresh_synthetic_with_module_name();
    let raw_label = label_name.0.trim_start_matches('\'');
    let name = Name(format!("#sub_label:{}#{}", raw_label, unique.0));
    stmt::unary_synthetic_act_spec(state, name)
}

fn materialize_sub_label_act_helpers(state: &mut LowerState, spec: &stmt::SyntheticActSpec) {
    stmt::materialize_synthetic_act(state, spec, &std_flow_sub_synthetic_act_source());
}

fn bind_sub_label_operator_helpers(state: &mut LowerState, spec: &stmt::SyntheticActSpec) {
    let member = sub_label_return_member_name();
    let path = Path {
        segments: vec![spec.name.clone(), member.clone()],
    };
    if let Some(def) = state.ctx.resolve_path_value(&path) {
        state
            .ctx
            .bind_local_operator(member, OperatorFixity::Prefix, def);
    }
}

fn bind_unlabeled_sub_operator_helpers(state: &mut LowerState) {
    let member = sub_label_return_member_name();
    let path = Path {
        segments: std_flow_sub_path_segments_with(member.clone()),
    };
    if let Some(def) = state.ctx.resolve_path_value(&path) {
        state
            .ctx
            .bind_local_operator(member, OperatorFixity::Prefix, def);
    }
}

fn bind_sub_label_field_helpers(
    state: &mut LowerState,
    label_def: crate::ids::DefId,
    spec: &stmt::SyntheticActSpec,
) {
    let member = sub_label_return_member_name();
    state.ctx.bind_field_alias(
        label_def,
        member.clone(),
        Path {
            segments: vec![spec.name.clone(), member],
        },
    );
}

fn std_flow_sub_effect_path() -> Path {
    Path {
        segments: std_flow_sub_path_segments(),
    }
}

fn std_flow_sub_path_segments() -> Vec<Name> {
    ["std", "flow", "sub"]
        .into_iter()
        .map(|segment| Name(segment.to_string()))
        .collect()
}

fn std_flow_sub_path_segments_with(member: Name) -> Vec<Name> {
    let mut segments = std_flow_sub_path_segments();
    segments.push(member);
    segments
}

fn selected_sub_label_helper_names() -> Vec<Name> {
    vec![
        sub_label_return_member_name(),
        Name("sub".to_string()),
        Name("control_label".to_string()),
    ]
}

fn sub_label_return_member_name() -> Name {
    Name("return".to_string())
}

fn std_flow_sub_synthetic_act_source() -> stmt::SyntheticActSource {
    stmt::SyntheticActSource {
        source_module_path: std_flow_sub_effect_path(),
        source_copy_path: Path {
            segments: vec![Name("sub".to_string())],
        },
        selected_values: selected_sub_label_helper_names(),
        selected_template_items: vec![Name("label".to_string())],
    }
}

/// PathSep ノードからパスセグメントを取り出す。
fn path_sep_ident(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| {
            matches!(
                t.kind(),
                SyntaxKind::Ident
                    | SyntaxKind::SigilIdent
                    | SyntaxKind::Prefix
                    | SyntaxKind::Infix
                    | SyntaxKind::Suffix
                    | SyntaxKind::Nullfix
            )
        })
        .map(|t| Name(t.text().to_string()))
}

fn qualified_method_path_from_field(
    field: &SyntaxNode,
    items: &mut ChainItems,
) -> Option<Vec<Name>> {
    let mut path = vec![field_suffix_ident(field)?];
    let mut has_path_sep = false;

    loop {
        skip_chain_trivia(items);
        let Some(NodeOrToken::Node(next)) = items.peek() else {
            break;
        };
        if next.kind() != SyntaxKind::PathSep {
            break;
        }
        let Some(seg) = path_sep_ident(next) else {
            break;
        };
        path.push(seg);
        has_path_sep = true;
        items.next();
    }

    has_path_sep.then_some(path)
}

fn field_suffix_ident(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| t.kind() == SyntaxKind::DotField)
        .map(|t| Name(t.text().trim_start_matches('.').to_string()))
}

fn is_loop_control_op(name: &Name) -> bool {
    matches!(name.0.as_str(), "last" | "next" | "redo")
}

fn label_arg_expr(node: &SyntaxNode) -> Option<SyntaxNode> {
    let expr = node
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)?;
    expr.children_with_tokens()
        .filter_map(|item| item.into_token())
        .any(|token| token.kind() == SyntaxKind::SigilIdent && token.text().starts_with('\''))
        .then_some(expr)
}

fn skip_chain_trivia(items: &mut ChainItems) {
    while matches!(
        items.peek(),
        Some(NodeOrToken::Token(t)) if matches!(t.kind(), SyntaxKind::Space | SyntaxKind::LineComment)
    ) {
        items.next();
    }
}

type ChainItems =
    std::iter::Peekable<rowan::SyntaxElementChildren<yulang_parser::sink::YulangLanguage>>;

struct PipeArg {
    expr: TypedExpr,
    span: Option<rowan::TextRange>,
}
