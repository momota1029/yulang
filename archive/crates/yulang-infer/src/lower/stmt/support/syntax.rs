use yulang_parser::lex::SyntaxKind;

use crate::lower::SyntaxNode;
use crate::symbols::Name;

/// node の直接の子から最初の kind トークンのテキストを返す。
pub(crate) fn first_token_text(node: &SyntaxNode, kind: SyntaxKind) -> Option<String> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| t.kind() == kind)
        .map(|t| t.text().to_string())
}

/// node の直接の子ノードから最初の kind を返す。
pub(crate) fn child_node(node: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxNode> {
    node.children().find(|c| c.kind() == kind)
}

/// node の直接の子ノードから kind のものを全て返す。
pub(crate) fn child_nodes(node: &SyntaxNode, kind: SyntaxKind) -> Vec<SyntaxNode> {
    node.children().filter(|c| c.kind() == kind).collect()
}

/// node の子孫から最初の kind ノードを返す。
pub(crate) fn descendant_node(node: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxNode> {
    for child in node.children() {
        if child.kind() == kind {
            return Some(child);
        }
        if let Some(found) = descendant_node(&child, kind) {
            return Some(found);
        }
    }
    None
}

/// node から最初の Ident トークンを Name として取り出す。
pub(crate) fn ident_name(node: &SyntaxNode) -> Option<Name> {
    first_token_text(node, SyntaxKind::Ident).map(Name)
}

pub(crate) fn ident_or_sigil_name(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| matches!(t.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent))
        .map(|t| Name(t.text().to_string()))
}

/// node に指定 kind のトークンが存在するか確認する。
pub(crate) fn has_token(node: &SyntaxNode, kind: SyntaxKind) -> bool {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .any(|t| t.kind() == kind)
}
