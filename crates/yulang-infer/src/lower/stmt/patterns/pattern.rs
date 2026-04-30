use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{Lit, PatKind, RecordPatField, RecordPatSpread, TypedPat};
use crate::ids::DefId;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;

/// パターンノードを TypedPat に lower する。
pub fn lower_pat(state: &mut LowerState, node: &SyntaxNode) -> TypedPat {
    let tv = state.fresh_tv();
    let kind = lower_pat_kind(state, node);
    TypedPat { tv, kind }
}

pub(crate) fn pattern_binding_name(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find_map(|tok| match tok.kind() {
            SyntaxKind::Ident => Some(Name(tok.text().to_string())),
            SyntaxKind::SigilIdent => super::super::sigil_pattern_binding_name(tok.text()),
            _ => None,
        })
}

pub(crate) fn record_pat_spread_pat(spread: &RecordPatSpread) -> &TypedPat {
    match spread {
        RecordPatSpread::Head(pat) | RecordPatSpread::Tail(pat) => pat.as_ref(),
    }
}

fn record_pat_spread_alias_def(state: &LowerState, spread: &RecordPatSpread) -> Option<DefId> {
    let pat = record_pat_spread_pat(spread);
    let PatKind::UnresolvedName(name) = &pat.kind else {
        return None;
    };
    state.ctx.resolve_bound_value(name)
}

fn pattern_has_poly_variant_colon(node: &SyntaxNode) -> bool {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .any(|token| token.kind() == SyntaxKind::Colon)
}

fn pattern_payload_node(node: &SyntaxNode) -> Option<SyntaxNode> {
    node.children()
        .find(|c| matches!(c.kind(), SyntaxKind::ApplyML | SyntaxKind::ApplyC))
}

fn lower_ctor_or_name_pat(state: &mut LowerState, node: &SyntaxNode) -> PatKind {
    if let Some(lit) = literal_pat(node) {
        return PatKind::Lit(lit);
    }

    if let Some(path) = super::pattern_ctor_path(node) {
        let payload = pattern_payload_node(node);
        if pattern_has_poly_variant_colon(node) {
            return PatKind::PolyVariant(
                path.segments
                    .last()
                    .cloned()
                    .unwrap_or_else(|| Name(String::new())),
                payload
                    .into_iter()
                    .map(|inner_node| lower_pat(state, &inner_node))
                    .collect(),
            );
        }
        if let Some(def) = super::enum_variant_def_for_pattern(state, &path) {
            if state.enum_variant_tags.contains_key(&def) {
                let ref_id = super::resolve_pattern_constructor_ref(state, def);
                return PatKind::Con(
                    ref_id,
                    payload
                        .into_iter()
                        .map(|inner_node| Box::new(lower_pat(state, &inner_node)))
                        .next(),
                );
            }
        }
    }

    if let Some(name) = pattern_binding_name(node) {
        let ref_id = state.ctx.fresh_ref();
        if let Some(inner_node) = pattern_payload_node(node) {
            let inner_pat = lower_pat(state, &inner_node);
            PatKind::Con(ref_id, Some(Box::new(inner_pat)))
        } else {
            PatKind::UnresolvedName(name)
        }
    } else {
        PatKind::Wild
    }
}

fn literal_pat(node: &SyntaxNode) -> Option<Lit> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find_map(|token| match token.kind() {
            SyntaxKind::Ident if token.text() == "true" => Some(Lit::Bool(true)),
            SyntaxKind::Ident if token.text() == "false" => Some(Lit::Bool(false)),
            SyntaxKind::Number => number_lit(token.text()),
            _ => None,
        })
}

fn number_lit(text: &str) -> Option<Lit> {
    if let Ok(n) = text.parse::<i64>() {
        return Some(Lit::Int(n));
    }
    if let Ok(f) = text.parse::<f64>() {
        return Some(Lit::Float(f));
    }
    None
}

fn lower_pat_kind(state: &mut LowerState, node: &SyntaxNode) -> PatKind {
    match node.kind() {
        SyntaxKind::Pattern => {
            if let Some(inner) = node.children().next() {
                if matches!(
                    inner.kind(),
                    SyntaxKind::PatOr
                        | SyntaxKind::PatAs
                        | SyntaxKind::PatParenGroup
                        | SyntaxKind::PatList
                        | SyntaxKind::PatRecord
                ) {
                    return lower_pat_kind(state, &inner);
                }
            }
            lower_ctor_or_name_pat(state, node)
        }
        SyntaxKind::PatOr => {
            let children: Vec<_> = node.children().collect();
            if children.len() >= 2 {
                let lhs = lower_pat(state, &children[0]);
                let rhs = lower_pat(state, &children[1]);
                PatKind::Or(Box::new(lhs), Box::new(rhs))
            } else {
                PatKind::Wild
            }
        }
        SyntaxKind::PatAs => {
            let Some(pat_node) = node.children().next() else {
                return PatKind::Wild;
            };
            let inner = lower_pat(state, &pat_node);
            let def = state.fresh_def();
            let def_tv = state.fresh_tv();
            state.register_def_tv(def, def_tv);
            if let Some(alias_name) = super::super::ident_name(node) {
                if let Some(owner) = state.current_owner {
                    state.register_def_owner(def, owner);
                }
                state.ctx.bind_local(alias_name, def);
            }
            PatKind::As(Box::new(inner), def)
        }
        SyntaxKind::PatParenGroup => {
            let pats: Vec<_> = node
                .children()
                .filter(|c| {
                    matches!(
                        c.kind(),
                        SyntaxKind::Pattern | SyntaxKind::PatOr | SyntaxKind::PatAs
                    )
                })
                .map(|c| lower_pat(state, &c))
                .collect();
            if pats.is_empty() {
                PatKind::Lit(crate::ast::expr::Lit::Unit)
            } else if pats.len() == 1 {
                lower_pat_kind(state, &node.children().next().unwrap())
            } else {
                PatKind::Tuple(pats)
            }
        }
        SyntaxKind::ApplyML | SyntaxKind::ApplyC => {
            let pats: Vec<_> = node
                .children()
                .filter(|c| {
                    matches!(
                        c.kind(),
                        SyntaxKind::Pattern
                            | SyntaxKind::PatOr
                            | SyntaxKind::PatAs
                            | SyntaxKind::PatParenGroup
                            | SyntaxKind::PatList
                            | SyntaxKind::PatRecord
                    )
                })
                .map(|c| lower_pat(state, &c))
                .collect();
            if pats.is_empty() {
                PatKind::Wild
            } else if pats.len() == 1 {
                pats.into_iter().next().unwrap().kind
            } else {
                PatKind::Tuple(pats)
            }
        }
        SyntaxKind::PatList => lower_list_pat(state, node),
        SyntaxKind::PatRecord => lower_record_pat(state, node),
        _ => lower_ctor_or_name_pat(state, node),
    }
}

fn lower_list_pat(state: &mut LowerState, node: &SyntaxNode) -> PatKind {
    let mut prefix = Vec::new();
    let mut suffix = Vec::new();
    let mut spread = None;
    let mut after_spread = false;

    for item in node.children().filter(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Pattern
                | SyntaxKind::PatOr
                | SyntaxKind::PatAs
                | SyntaxKind::PatParenGroup
                | SyntaxKind::PatList
                | SyntaxKind::PatRecord
                | SyntaxKind::PatSpread
        )
    }) {
        if item.kind() == SyntaxKind::PatSpread {
            if spread.is_none() {
                spread = item
                    .children()
                    .find(is_pattern_node)
                    .map(|child| Box::new(lower_pat(state, &child)));
            }
            after_spread = true;
            continue;
        }
        let pat = lower_pat(state, &item);
        if after_spread {
            suffix.push(pat);
        } else {
            prefix.push(pat);
        }
    }

    PatKind::List {
        prefix,
        spread,
        suffix,
    }
}

fn is_pattern_node(node: &SyntaxNode) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::Pattern
            | SyntaxKind::PatOr
            | SyntaxKind::PatAs
            | SyntaxKind::PatParenGroup
            | SyntaxKind::PatList
            | SyntaxKind::PatRecord
    )
}

fn lower_record_pat(state: &mut LowerState, node: &SyntaxNode) -> PatKind {
    let mut fields = Vec::new();
    let mut spread = None;
    let items = node
        .children()
        .filter(|child| matches!(child.kind(), SyntaxKind::PatField | SyntaxKind::PatSpread))
        .collect::<Vec<_>>();
    for (index, item) in items.iter().enumerate() {
        match item.kind() {
            SyntaxKind::PatField => {
                let Some(fname) = super::super::ident_name(item) else {
                    continue;
                };
                let default = item
                    .children()
                    .find(|c| c.kind() == SyntaxKind::Expr)
                    .map(|c| crate::lower::expr::lower_expr(state, &c));
                let pat = item
                    .children()
                    .find(|c| {
                        matches!(
                            c.kind(),
                            SyntaxKind::Pattern
                                | SyntaxKind::PatOr
                                | SyntaxKind::PatAs
                                | SyntaxKind::PatList
                        )
                    })
                    .map(|c| lower_pat(state, &c))
                    .unwrap_or_else(|| {
                        let def = state.fresh_def();
                        let def_tv = state.fresh_tv();
                        state.register_def_tv(def, def_tv);
                        if let Some(owner) = state.current_owner {
                            state.register_def_owner(def, owner);
                        }
                        state.ctx.bind_local(fname.clone(), def);
                        TypedPat {
                            tv: def_tv,
                            kind: PatKind::UnresolvedName(fname.clone()),
                        }
                    });
                fields.push(RecordPatField {
                    name: fname,
                    pat,
                    default,
                });
            }
            SyntaxKind::PatSpread if spread.is_none() => {
                let pat = item
                    .children()
                    .find(|c| {
                        matches!(
                            c.kind(),
                            SyntaxKind::Pattern
                                | SyntaxKind::PatOr
                                | SyntaxKind::PatAs
                                | SyntaxKind::PatList
                        )
                    })
                    .map(|c| lower_pat(state, &c));
                if let Some(pat) = pat {
                    spread = Some(if index == 0 {
                        RecordPatSpread::Head(Box::new(pat))
                    } else {
                        RecordPatSpread::Tail(Box::new(pat))
                    });
                }
            }
            _ => {}
        }
    }
    if let Some(spread_pat) = spread {
        if let Some(def) = record_pat_spread_alias_def(state, &spread_pat) {
            return PatKind::As(
                Box::new(TypedPat {
                    tv: state.fresh_tv(),
                    kind: PatKind::Record {
                        spread: None,
                        fields,
                    },
                }),
                def,
            );
        }
        PatKind::Record {
            spread: Some(spread_pat),
            fields,
        }
    } else {
        PatKind::Record {
            spread: None,
            fields,
        }
    }
}
