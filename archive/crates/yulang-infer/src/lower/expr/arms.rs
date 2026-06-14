use yulang_parser::lex::SyntaxKind;

use crate::lower::SyntaxNode;

pub(crate) fn collect_child_arms(node: &SyntaxNode, arm_kind: SyntaxKind) -> Vec<SyntaxNode> {
    let mut out = Vec::new();
    for child in node.children() {
        if child.kind() == arm_kind {
            out.push(child);
        } else if matches!(
            child.kind(),
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        ) {
            out.extend(collect_child_arms(&child, arm_kind));
        }
    }
    out
}
