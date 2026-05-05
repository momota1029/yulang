use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::TypedExpr;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, OperatorFixity};

use super::{resolve_operator_expr, resolve_path_expr, unit_expr};

pub(super) fn infix_op_ref(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let Some(name) = infix_op_name(node) else {
        return unit_expr(state);
    };
    if let Some(path) = builtin_infix_role_target(&name) {
        resolve_path_expr(state, path)
    } else {
        resolve_operator_expr(state, builtin_infix_target(name), OperatorFixity::Infix)
    }
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

fn builtin_infix_target(name: Name) -> Name {
    match name.0.as_str() {
        "+" => Name("add".to_string()),
        "-" => Name("sub".to_string()),
        "*" => Name("mul".to_string()),
        "/" => Name("div".to_string()),
        _ => name,
    }
}

fn builtin_infix_role_target(name: &Name) -> Option<Vec<Name>> {
    let role = match name.0.as_str() {
        "+" => ("Add", "add"),
        "-" => ("Sub", "sub"),
        "*" => ("Mul", "mul"),
        "/" => ("Div", "div"),
        "==" => ("Eq", "eq"),
        "<" => ("Ord", "lt"),
        "<=" => ("Ord", "le"),
        ">" => ("Ord", "gt"),
        ">=" => ("Ord", "ge"),
        _ => return None,
    };
    Some(vec![
        Name("std".to_string()),
        Name("prelude".to_string()),
        Name(role.0.to_string()),
        Name(role.1.to_string()),
    ])
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
