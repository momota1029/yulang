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
            SyntaxKind::Ident if tok.text() != "_" => Some(Name(tok.text().to_string())),
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
        .any(|token| matches!(token.kind(), SyntaxKind::Colon | SyntaxKind::Symbol))
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
        if let Some(def) = super::struct_constructor_def_for_pattern(state, &path) {
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
    if let Some(lit) = node.children().find_map(string_lit_pat) {
        return Some(lit);
    }
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find_map(|token| match token.kind() {
            SyntaxKind::Ident if token.text() == "true" => Some(Lit::Bool(true)),
            SyntaxKind::Ident if token.text() == "false" => Some(Lit::Bool(false)),
            SyntaxKind::Number => number_lit(token.text()),
            _ => None,
        })
}

fn string_lit_pat(node: SyntaxNode) -> Option<Lit> {
    match node.kind() {
        SyntaxKind::StringLit => plain_string_lit_text(&node).map(Lit::Str),
        SyntaxKind::RuleLit => plain_rule_lit_text(&node).map(Lit::Str),
        _ => None,
    }
}

fn plain_string_lit_text(node: &SyntaxNode) -> Option<String> {
    if node
        .children()
        .any(|child| child.kind() == SyntaxKind::StringInterp)
    {
        return None;
    }

    let mut text = String::new();
    let mut tokens = node.children_with_tokens().peekable();
    while let Some(item) = tokens.next() {
        let Some(token) = item.into_token() else {
            continue;
        };
        match token.kind() {
            SyntaxKind::StringText => text.push_str(token.text()),
            SyntaxKind::StringEscapeLead => text.push_str(&collect_string_escape_text(&mut tokens)),
            SyntaxKind::StringStart | SyntaxKind::StringEnd => {}
            _ => {}
        }
    }
    Some(text)
}

fn plain_rule_lit_text(node: &SyntaxNode) -> Option<String> {
    let mut text = String::new();
    for token in node.descendants_with_tokens().filter_map(|item| item.into_token()) {
        match token.kind() {
            SyntaxKind::RuleLitText => text.push_str(token.text()),
            SyntaxKind::RuleLitStart
            | SyntaxKind::RuleLitEnd
            | SyntaxKind::StringStart
            | SyntaxKind::StringEnd => {}
            kind if is_trivia_kind(kind) => {}
            _ => return None,
        }
    }
    Some(text)
}

fn is_trivia_kind(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Space
            | SyntaxKind::LineComment
            | SyntaxKind::BlockCommentStart
            | SyntaxKind::BlockCommentText
            | SyntaxKind::BlockCommentEnd
            | SyntaxKind::QuotePrefix
            | SyntaxKind::DocComment
            | SyntaxKind::BlockComment
            | SyntaxKind::Trivia
    )
}

fn collect_string_escape_text(
    tokens: &mut std::iter::Peekable<
        rowan::SyntaxElementChildren<yulang_parser::sink::YulangLanguage>,
    >,
) -> String {
    let Some(next) = tokens.next().and_then(|item| item.into_token()) else {
        return String::new();
    };
    match next.kind() {
        SyntaxKind::StringEscapeSimple => simple_escape_text(next.text()),
        SyntaxKind::StringEscapeUnicodeStart => collect_unicode_escape_text(tokens),
        _ => next.text().to_string(),
    }
}

fn simple_escape_text(text: &str) -> String {
    match text {
        "n" => "\n".to_string(),
        "r" => "\r".to_string(),
        "t" => "\t".to_string(),
        "\\" => "\\".to_string(),
        "\"" => "\"".to_string(),
        "0" => "\0".to_string(),
        other => other.to_string(),
    }
}

fn collect_unicode_escape_text(
    tokens: &mut std::iter::Peekable<
        rowan::SyntaxElementChildren<yulang_parser::sink::YulangLanguage>,
    >,
) -> String {
    let Some(hex) = tokens.next().and_then(|item| item.into_token()) else {
        return String::new();
    };
    if hex.kind() != SyntaxKind::StringEscapeUnicodeHex {
        return hex.text().to_string();
    }
    let value = u32::from_str_radix(hex.text(), 16)
        .ok()
        .and_then(char::from_u32)
        .unwrap_or(char::REPLACEMENT_CHARACTER);
    if matches!(
        tokens
            .peek()
            .and_then(|item| item.as_token())
            .map(|token| token.kind()),
        Some(SyntaxKind::StringEscapeUnicodeEnd)
    ) {
        tokens.next();
    }
    value.to_string()
}

fn number_lit(text: &str) -> Option<Lit> {
    if text.chars().all(|ch| ch.is_ascii_digit()) {
        return Some(Lit::Int(text.to_string()));
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
                        let def = match state.ctx.resolve_bound_value(&fname) {
                            Some(def) => def,
                            None => {
                                let def = state.fresh_def();
                                let def_tv = state.fresh_tv();
                                state.register_def_tv(def, def_tv);
                                state.register_def_name(def, fname.clone());
                                if let Some(owner) = state.current_owner {
                                    state.register_def_owner(def, owner);
                                }
                                state.ctx.bind_local(fname.clone(), def);
                                def
                            }
                        };
                        let def_tv = state.def_tvs.get(&def).copied().unwrap_or_else(|| {
                            let tv = state.fresh_tv();
                            state.register_def_tv(def, tv);
                            tv
                        });
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
