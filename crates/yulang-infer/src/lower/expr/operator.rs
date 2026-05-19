use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::TypedExpr;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, OperatorFixity};

use super::{resolve_operator_expr_with_span, unit_expr};

pub(super) fn infix_op_ref(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let Some((name, span)) = infix_op_name_with_span(node) else {
        return unit_expr(state);
    };
    resolve_operator_expr_with_span(state, name, OperatorFixity::Infix, Some(span))
}

pub(super) fn prefix_op_ref(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let Some((name, span)) = prefix_op_name_with_span(node) else {
        return unit_expr(state);
    };
    resolve_operator_expr_with_span(state, name, OperatorFixity::Prefix, Some(span))
}

pub(super) fn suffix_op_ref(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let Some((name, span)) = suffix_op_name_with_span(node) else {
        return unit_expr(state);
    };
    resolve_operator_expr_with_span(state, name, OperatorFixity::Suffix, Some(span))
}

fn infix_op_name_with_span(node: &SyntaxNode) -> Option<(Name, rowan::TextRange)> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| matches!(t.kind(), SyntaxKind::Infix | SyntaxKind::OpName))
        .map(|t| (Name(t.text().to_string()), t.text_range()))
}

fn prefix_op_name_with_span(node: &SyntaxNode) -> Option<(Name, rowan::TextRange)> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| matches!(t.kind(), SyntaxKind::Prefix | SyntaxKind::OpName))
        .map(|t| (Name(t.text().to_string()), t.text_range()))
}

fn suffix_op_name_with_span(node: &SyntaxNode) -> Option<(Name, rowan::TextRange)> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| matches!(t.kind(), SyntaxKind::Suffix | SyntaxKind::OpName))
        .map(|t| (Name(t.text().to_string()), t.text_range()))
}
