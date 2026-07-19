//! CST accessors and small token predicates used by expression lowering.

use super::*;
use crate::{node_source_range, token_source_range};
use num_bigint::BigInt;

pub(super) fn item_is_trivia(item: &NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>) -> bool {
    item.as_token()
        .is_some_and(|token| matches!(token.kind(), SyntaxKind::Space | SyntaxKind::LineComment))
}

pub(super) fn item_source_range(item: &CstItem) -> SourceRange {
    match item {
        NodeOrToken::Node(node) => node_source_range(node),
        NodeOrToken::Token(token) => token_source_range(token),
    }
}

pub(super) fn item_text_range(item: &CstItem) -> TextRange {
    match item {
        NodeOrToken::Node(node) => node.text_range(),
        NodeOrToken::Token(token) => token.text_range(),
    }
}

pub(super) fn item_slice_text_range(items: &[CstItem]) -> Option<TextRange> {
    let first = item_text_range(items.first()?);
    let last = item_text_range(items.last()?);
    Some(first.cover(last))
}

pub(super) fn item_slice_source_range(items: &[CstItem]) -> Option<SourceRange> {
    let first = item_source_range(items.first()?);
    let last = item_source_range(items.last()?);
    Some(SourceRange {
        start: first.start,
        end: last.end,
    })
}

pub(super) fn should_stop_expr_tail(
    kind: SyntaxKind,
    stop_at_with: bool,
    stop_kind: Option<SyntaxKind>,
) -> bool {
    (stop_at_with && kind == SyntaxKind::WithBlock) || stop_kind == Some(kind)
}

pub(super) fn expr_path_prefix(items: &[CstItem]) -> Option<(Vec<Name>, usize)> {
    let Some(NodeOrToken::Token(head)) = items.first() else {
        return None;
    };
    if head.kind() != SyntaxKind::Ident {
        return None;
    }

    let mut path = vec![Name(head.text().to_string())];
    let mut consumed = 1;
    for item in &items[1..] {
        let NodeOrToken::Node(path_sep) = item else {
            break;
        };
        if path_sep.kind() != SyntaxKind::PathSep {
            break;
        }
        let Some(segment) = path_sep_name(path_sep) else {
            break;
        };
        path.push(segment);
        consumed += 1;
    }
    (path.len() > 1).then_some((path, consumed))
}

pub(super) fn path_sep_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::Ident)
        .map(|token| Name(token.text().to_string()))
}

pub(super) fn path_label(path: &[Name]) -> String {
    path.iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

pub(super) fn builtin_op_from_path(path: &[Name]) -> Option<BuiltinOp> {
    match path {
        [namespace, name] if namespace.0 == "builtin_op" => resolve_builtin_op(&name.0),
        _ => None,
    }
}

pub(super) fn field_name(node: &Cst) -> Option<String> {
    let token = node
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::DotField)?;
    Some(token.text().trim_start_matches('.').to_string())
}

pub(super) fn brace_group_is_record_literal(node: &Cst) -> bool {
    let mut has_item = false;
    let mut saw_child = false;
    for child in node.children() {
        saw_child = true;
        match child.kind() {
            SyntaxKind::Expr => {
                if !is_inline_record_field_expr(&child) {
                    return false;
                }
                has_item = true;
            }
            SyntaxKind::ExprSpread => {
                if child
                    .children()
                    .all(|child| child.kind() != SyntaxKind::Expr)
                {
                    return false;
                }
                has_item = true;
            }
            SyntaxKind::Separator => {}
            _ => return false,
        }
    }
    has_item || !saw_child
}

fn is_inline_record_field_expr(node: &Cst) -> bool {
    record_field_name(node).is_some()
        && record_field_value(node).is_some()
        && node
            .children()
            .all(|child| child.kind() == SyntaxKind::ApplyColon)
}

pub(super) fn record_field_name(node: &Cst) -> Option<Name> {
    if node
        .children()
        .any(|child| child.kind() == SyntaxKind::PathSep)
    {
        return None;
    }
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| matches!(token.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent))
        .map(|token| Name(token.text().to_string()))
}

pub(super) fn record_field_value(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::ApplyColon)?
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)
}

pub(super) fn block_lowering_items(node: &Cst) -> Vec<Cst> {
    node.children()
        .filter(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Binding | SyntaxKind::Expr | SyntaxKind::ForStmt
            )
        })
        .collect()
}

pub(super) fn apply_argument_nodes(node: &Cst) -> Vec<Cst> {
    let mut args = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::Expr)
        .collect::<Vec<_>>();
    if !args.is_empty() || node.kind() != SyntaxKind::ApplyColon {
        return args;
    }
    args.extend(node.children().filter(|child| {
        child.kind() == SyntaxKind::IndentBlock
            || child.kind() == SyntaxKind::BraceGroup && !brace_group_is_record_literal(child)
    }));
    args
}

pub(super) fn with_block_lowering_items(node: &Cst) -> Vec<Cst> {
    let mut out = Vec::new();
    collect_with_block_lowering_items(node, &mut out);
    out
}

fn collect_with_block_lowering_items(node: &Cst, out: &mut Vec<Cst>) {
    for child in node.children() {
        match child.kind() {
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup | SyntaxKind::WithBlock => {
                collect_with_block_lowering_items(&child, out);
            }
            SyntaxKind::Binding | SyntaxKind::Expr | SyntaxKind::ForStmt => out.push(child),
            _ => {}
        }
    }
}

pub(super) fn with_public_binding_names(items: &[Cst]) -> Vec<Name> {
    let mut out = Vec::new();
    for item in items {
        if item.kind() != SyntaxKind::Binding || crate::binding_vis(item) == Vis::My {
            continue;
        }
        out.extend(crate::binding_value_names(item));
    }
    out
}

pub(super) fn index_expr(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::Expr)
        .or_else(|| {
            node.children()
                .find(|child| child.kind() == SyntaxKind::Bracket)
                .and_then(|bracket| {
                    bracket
                        .children()
                        .find(|child| child.kind() == SyntaxKind::Expr)
                })
        })
}

pub(super) fn assignment_value_expr(node: &Cst) -> Option<Cst> {
    node.children()
        .filter(|child| child.kind() == SyntaxKind::Expr)
        .last()
}

pub(super) fn for_label(node: &Cst) -> Option<Cst> {
    let header = node
        .children()
        .find(|child| child.kind() == SyntaxKind::ForHeader)?;
    header
        .children()
        .find(|child| child.kind() == SyntaxKind::ForLabel)
}

pub(super) fn for_label_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::SigilIdent)
        .map(|token| Name(token.text().to_string()))
}

pub(super) fn for_pattern(node: &Cst) -> Option<Cst> {
    let header = node
        .children()
        .find(|child| child.kind() == SyntaxKind::ForHeader)?;
    header.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Pattern | SyntaxKind::PatOr | SyntaxKind::PatAs | SyntaxKind::PatParenGroup
        )
    })
}

pub(super) fn for_iter_expr(node: &Cst) -> Option<Cst> {
    let header = node
        .children()
        .find(|child| child.kind() == SyntaxKind::ForHeader)?;
    header
        .children()
        .find(|child| child.kind() == SyntaxKind::Expr)
}

pub(super) fn for_body_expr(node: &Cst) -> Option<Cst> {
    let body = node
        .children()
        .find(|child| child.kind() == SyntaxKind::ForBody)?;
    body.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup | SyntaxKind::Expr
        )
    })
}

pub(super) fn var_read_reference_name(text: &str) -> Option<Name> {
    let raw = text.strip_prefix('$')?;
    (!raw.is_empty()).then(|| Name(format!("&{raw}")))
}

pub(super) fn local_var_binding_source(node: &Cst) -> Option<Name> {
    if !crate::binding_has_single_head_pattern(node) {
        return None;
    }
    let source = crate::binding_name(node)?;
    source.0.starts_with('$').then_some(source)
}

pub(super) fn local_var_pattern_binding_sources(node: &Cst) -> Vec<Name> {
    let Some(pattern) = crate::binding_pattern(node) else {
        return Vec::new();
    };
    let mut sources = Vec::new();
    crate::collect_pattern_var_binding_sources(&pattern, &mut sources);
    sources
}

pub(super) fn var_init_name(source: &Name) -> Option<Name> {
    let raw = source.0.strip_prefix('$')?;
    (!raw.is_empty()).then(|| Name(format!("#{raw}")))
}

pub(super) fn var_reference_name(source: &Name) -> Option<Name> {
    let raw = source.0.strip_prefix('$')?;
    (!raw.is_empty()).then(|| Name(format!("&{raw}")))
}

pub(super) fn direct_child(node: &Cst, kind: SyntaxKind) -> Option<Cst> {
    node.children().find(|child| child.kind() == kind)
}

fn integer_number_token(text: &str) -> bool {
    text.chars().all(|ch| ch.is_ascii_digit())
}

pub(super) fn parse_number_lit(text: &str) -> Result<(Lit, &'static str), LoweringError> {
    if integer_number_token(text) {
        if let Ok(parsed) = text.parse::<i64>() {
            return Ok((Lit::Int(parsed), "int"));
        }

        let parsed = text
            .parse::<BigInt>()
            .map_err(|_| LoweringError::InvalidNumber {
                text: text.to_string(),
            })?;
        Ok((Lit::BigInt(parsed), "int"))
    } else {
        let parsed = text
            .parse::<f64>()
            .map_err(|_| LoweringError::InvalidNumber {
                text: text.to_string(),
            })?;
        Ok((Lit::Float(parsed), "float"))
    }
}

pub(super) fn primitive_type(name: &str) -> Pos {
    Pos::Con(vec![name.into()], Vec::new())
}

pub(super) fn primitive_neg_type(name: &str) -> Neg {
    Neg::Con(vec![name.into()], Vec::new())
}

pub(super) fn expr_symbol_head_name(
    head: &NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>,
) -> Option<String> {
    let token = head.as_token()?;
    (token.kind() == SyntaxKind::Symbol).then(|| token.text().trim_start_matches(':').to_string())
}

pub(super) fn recursive_lambda_label_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::SigilIdent && token.text().starts_with('\''))
        .map(|token| Name(token.text().to_string()))
}

pub(super) fn binding_body_expr(binding: &Cst) -> Option<Cst> {
    crate::child_node(binding, SyntaxKind::BindingBody)?
        .children()
        .find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
            )
        })
}

pub(super) fn op_def_body_expr(node: &Cst) -> Option<Cst> {
    crate::child_node(node, SyntaxKind::OpDefBody)?
        .children()
        .find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
            )
        })
}

pub(super) fn binding_arg_patterns(binding: &Cst) -> Vec<Cst> {
    let Some(header) = crate::child_node(binding, SyntaxKind::BindingHeader) else {
        return Vec::new();
    };
    let Some(pattern) = crate::child_node(&header, SyntaxKind::Pattern) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    collect_binding_arg_patterns(&pattern, &mut out);
    out
}

pub(super) fn local_binding_call_return_effect(binding: &Cst) -> LocalCallReturnEffect {
    if binding_type_expr(binding).is_some() {
        LocalCallReturnEffect::Annotated
    } else {
        LocalCallReturnEffect::Unannotated
    }
}

fn collect_binding_arg_patterns(node: &Cst, out: &mut Vec<Cst>) {
    for child in node.children() {
        if !matches!(child.kind(), SyntaxKind::ApplyML | SyntaxKind::ApplyC) {
            continue;
        }
        collect_binding_arg_patterns(&child, out);
        let args = child
            .children()
            .filter(|item| item.kind() == SyntaxKind::Pattern)
            .collect::<Vec<_>>();
        if args.is_empty() && child.kind() == SyntaxKind::ApplyC {
            out.push(child);
        } else {
            out.extend(args);
        }
    }
}

pub(super) fn pattern_type_expr(pattern: &Cst) -> Option<Cst> {
    if let Some(type_expr) = crate::direct_pattern_type_expr(pattern) {
        return Some(type_expr);
    }
    if !matches!(
        pattern.kind(),
        SyntaxKind::Pattern | SyntaxKind::PatParenGroup
    ) {
        return None;
    }
    pattern
        .children()
        .find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Pattern | SyntaxKind::PatParenGroup
            )
        })
        .and_then(|child| pattern_type_expr(&child))
}

pub(super) fn module_body(module: &Cst) -> Option<Cst> {
    module.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
        )
    })
}
