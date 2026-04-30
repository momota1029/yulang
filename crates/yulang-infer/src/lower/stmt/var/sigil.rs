use yulang_parser::lex::SyntaxKind;

use crate::lower::SyntaxNode;
use crate::symbols::Name;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct VarBinding {
    pub source: Name,
    pub init: Name,
    pub reference: Name,
}

pub(crate) fn binding_var_sigils(binding: &SyntaxNode) -> Vec<VarBinding> {
    let Some(header) = super::super::child_node(binding, SyntaxKind::BindingHeader) else {
        return vec![];
    };
    let Some(pat) = super::super::child_node(&header, SyntaxKind::Pattern) else {
        return vec![];
    };
    let mut out = Vec::new();
    collect_var_sigils(&pat, &mut out);
    out
}

pub(crate) fn sigil_pattern_binding_name(text: &str) -> Option<Name> {
    text.strip_prefix('$')
        .map(internal_var_init_name)
        .or_else(|| Some(Name(text.to_string())))
}

fn collect_var_sigils(node: &SyntaxNode, out: &mut Vec<VarBinding>) {
    for token in node.children_with_tokens().filter_map(|it| it.into_token()) {
        if token.kind() != SyntaxKind::SigilIdent {
            continue;
        }
        let text = token.text();
        let Some(raw) = text.strip_prefix('$') else {
            continue;
        };
        let binding = VarBinding {
            source: Name(text.to_string()),
            init: internal_var_init_name(raw),
            reference: internal_var_ref_name(raw),
        };
        if !out.iter().any(|existing| existing == &binding) {
            out.push(binding);
        }
    }
    for child in node.children() {
        collect_var_sigils(&child, out);
    }
}

fn internal_var_init_name(raw: &str) -> Name {
    Name(format!("#{raw}"))
}

fn internal_var_ref_name(raw: &str) -> Name {
    Name(format!("&{raw}"))
}
