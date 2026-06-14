use std::fmt::Write as _;

use parser::sink::YulangLanguage;
use rowan::SyntaxNode;

pub fn format_module_cst(source: &str) -> String {
    let green = parser::parse_module_to_green(source);
    let root = SyntaxNode::<YulangLanguage>::new_root(green);
    let mut out = String::new();
    format_cst_node(&mut out, &root, 0);
    out.push('\n');
    out
}

fn format_cst_node(out: &mut String, node: &SyntaxNode<YulangLanguage>, indent: usize) {
    let prefix = "  ".repeat(indent);
    let _ = write!(out, "{prefix}{:?}", node.kind());
    let text = node.text().to_string();
    if !text.contains('\n') && text.len() < 40 {
        let _ = writeln!(out, "  {:?}", text);
    } else {
        out.push('\n');
    }
    for child in node.children() {
        format_cst_node(out, &child, indent + 1);
    }
}
