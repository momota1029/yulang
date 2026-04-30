use yulang_parser::lex::SyntaxKind;

use crate::lower::SyntaxNode;
use crate::symbols::{Name, OperatorFixity, Visibility as ModuleVisibility};

pub(crate) fn header_module_visibility(header: &SyntaxNode) -> ModuleVisibility {
    if super::has_token(header, SyntaxKind::Pub) {
        ModuleVisibility::Pub
    } else if super::has_token(header, SyntaxKind::Our) {
        ModuleVisibility::Our
    } else {
        ModuleVisibility::My
    }
}

pub(crate) fn header_operator_fixity(header: &SyntaxNode) -> Option<OperatorFixity> {
    let kind = header
        .children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| {
            matches!(
                t.kind(),
                SyntaxKind::Prefix | SyntaxKind::Infix | SyntaxKind::Suffix | SyntaxKind::Nullfix
            )
        })?
        .kind();
    match kind {
        SyntaxKind::Prefix => Some(OperatorFixity::Prefix),
        SyntaxKind::Infix => Some(OperatorFixity::Infix),
        SyntaxKind::Suffix => Some(OperatorFixity::Suffix),
        SyntaxKind::Nullfix => Some(OperatorFixity::Nullfix),
        _ => None,
    }
}

pub(crate) fn header_value_name(header: &SyntaxNode) -> Option<Name> {
    if header.kind() == SyntaxKind::OpDefHeader {
        return op_name(header);
    }
    let pattern = super::child_node(header, SyntaxKind::Pattern)?;
    super::ident_name(&pattern).or_else(|| op_name(&pattern))
}

fn op_name(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| t.kind() == SyntaxKind::OpName)
        .map(|t| Name(t.text().to_string()))
}
