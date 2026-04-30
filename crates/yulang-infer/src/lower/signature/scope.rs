use std::collections::HashMap;

use crate::ids::TypeVar;
use crate::lower::{LowerState, SyntaxNode};

pub fn fresh_type_scope(state: &mut LowerState, names: &[String]) -> HashMap<String, TypeVar> {
    let mut out = HashMap::new();
    for name in names {
        out.entry(name.clone()).or_insert_with(|| state.fresh_tv());
    }
    out
}

pub fn ordered_type_vars(names: &[String], scope: &HashMap<String, TypeVar>) -> Vec<TypeVar> {
    names
        .iter()
        .filter_map(|name| scope.get(name).copied())
        .collect()
}

pub fn ordered_act_type_vars(node: &SyntaxNode, scope: &HashMap<String, TypeVar>) -> Vec<TypeVar> {
    ordered_type_vars(&act_type_param_names(node), scope)
}

pub fn act_type_param_names(node: &SyntaxNode) -> Vec<String> {
    let text = node.to_string();
    let before_body = text.split_once(':').map(|(head, _)| head).unwrap_or(&text);
    let head = before_body
        .split_once('=')
        .map(|(head, _)| head)
        .unwrap_or(before_body);
    let mut out = Vec::new();
    let mut chars = head.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch != '\'' {
            continue;
        }
        let mut name = String::new();
        while let Some(next) = chars.peek().copied() {
            if next.is_ascii_alphanumeric() || next == '_' {
                name.push(next);
                chars.next();
            } else {
                break;
            }
        }
        if !name.is_empty() && !out.contains(&name) {
            out.push(name);
        }
    }
    out
}
