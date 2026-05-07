use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::TypedExpr;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, OperatorFixity};

use super::{resolve_operator_expr, unit_expr};

pub(super) fn infix_op_ref(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let Some(name) = infix_op_name(node) else {
        return unit_expr(state);
    };
    resolve_operator_expr(state, name, OperatorFixity::Infix)
}

pub(super) fn prefix_op_ref(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let Some(name) = prefix_op_name(node) else {
        return unit_expr(state);
    };
    resolve_operator_expr(state, name, OperatorFixity::Prefix)
}

pub(super) fn suffix_op_ref(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let Some(name) = suffix_op_name(node) else {
        return unit_expr(state);
    };
    resolve_operator_expr(state, name, OperatorFixity::Suffix)
}

pub(super) fn infix_op_name(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| matches!(t.kind(), SyntaxKind::Infix | SyntaxKind::OpName))
        .map(|t| Name(t.text().to_string()))
}

fn prefix_op_name(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| matches!(t.kind(), SyntaxKind::Prefix | SyntaxKind::OpName))
        .map(|t| Name(t.text().to_string()))
}

fn suffix_op_name(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| matches!(t.kind(), SyntaxKind::Suffix | SyntaxKind::OpName))
        .map(|t| Name(t.text().to_string()))
}
