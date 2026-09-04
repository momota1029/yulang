//! Raw successor evidence and lexical dynamic-operator selection.

use unicode_ident::{is_xid_continue, is_xid_start};

use crate::{
    operator::{OperatorFixities, OperatorFixity, OperatorTable},
    scan::operator::{OperatorSite, is_call_or_path_sensitive, judge_operator},
};

use super::{
    LexIn, Stops,
    item::{OperatorToken, OperatorUse},
};

pub(super) const STOP_COMMA: Stops = 1 << 0;
const STOP_SEMICOLON: Stops = 1 << 1;
const STOP_RPAREN: Stops = 1 << 2;
const STOP_RBRACKET: Stops = 1 << 3;
const STOP_RBRACE: Stops = 1 << 4;
pub(super) const STOP_RECORD_SPREAD: Stops = 1 << 5;
pub(super) const STOP_RECORD_SPREAD_AFTER_OPERATOR: Stops = 1 << 6;
pub(super) const STOP_COLON: Stops = 1 << 7;
pub(super) const STOP_LBRACE: Stops = 1 << 8;
pub(super) const STOP_ELSIF: Stops = 1 << 9;
pub(super) const STOP_ELSE: Stops = 1 << 10;

pub(super) fn stops_for(close: super::item::TokenKind) -> Stops {
    let close = match close {
        super::item::TokenKind::RParen => STOP_RPAREN,
        super::item::TokenKind::RBracket => STOP_RBRACKET,
        super::item::TokenKind::RBrace => STOP_RBRACE,
        _ => unreachable!("only a matching close owns a delimited stop set"),
    };
    STOP_COMMA | STOP_SEMICOLON | close
}

pub(super) fn scan_operator(
    mut i: LexIn,
    site: OperatorSite,
    has_leading_trivia: bool,
    baseline: usize,
    stops: Stops,
) -> Option<OperatorToken> {
    let table = i.recovery().operators();
    let source = i.remainder();
    let (use_, end) = table.longest_source_match_then(source, |last, entry, end| {
        operator_boundary(last, &source[end..])?;

        let (trailing, after_trivia) = raw_trivia_suffix(&source[end..]);
        let kinds = entry.fixities().kinds();
        if is_call_or_path_sensitive(kinds)
            && trailing == RawTrailing::None
            && matches!(after_trivia.chars().next(), Some('(' | ':'))
        {
            return None;
        }

        let post_whitespace = trailing != RawTrailing::None
            || after_trivia.is_empty()
            || active_stop(after_trivia, stops);
        let value_start = raw_value_start(table, trailing, after_trivia, baseline);
        let with_value = judge_operator(site, kinds, has_leading_trivia, post_whitespace, true);
        let without_value = judge_operator(site, kinds, has_leading_trivia, post_whitespace, false);
        let fixity = if is_call_or_path_sensitive(kinds) && post_whitespace && value_start {
            Some(OperatorFixity::Prefix)
        } else if with_value != without_value {
            if value_start {
                with_value
            } else {
                without_value
            }
        } else {
            with_value
        }?;
        selected_operator_use(entry.fixities(), fixity)
    })?;
    let character_count = source[..end].chars().count();
    let (accepted, text) = i.with_str(|mut operator| {
        for _ in 0..character_count {
            operator.next()?;
        }
        Some(())
    });
    accepted?;
    Some(OperatorToken {
        text: text.into(),
        use_,
    })
}

/// After ordinary role selection rejects a spelling for lack of a value,
/// recover one role only when the current site makes that role unambiguous.
///
/// This remains a source-only probe: no logical Item exists until the caller
/// accepts the returned token.  In particular, it keeps the ordinary trie
/// traversal's longer-to-shorter fallback and boundary check intact.
pub(super) fn scan_dangling_operator(
    mut i: LexIn,
    site: OperatorSite,
    baseline: usize,
    stops: Stops,
) -> Option<OperatorToken> {
    let table = i.recovery().operators();
    let source = i.remainder();
    let (use_, end) = table.longest_source_match_then(source, |last, entry, end| {
        operator_boundary(last, &source[end..])?;
        let fixities = entry.fixities();
        let fixity = match site {
            OperatorSite::Nud if fixities.prefix().is_some() && !fixities.is_nullfix() => {
                OperatorFixity::Prefix
            }
            OperatorSite::Led if fixities.infix().is_some() && fixities.suffix().is_none() => {
                OperatorFixity::Infix
            }
            _ => return None,
        };
        dangling_follower(&source[end..], baseline, stops)?;
        selected_operator_use(fixities, fixity)
    })?;
    let character_count = source[..end].chars().count();
    let (accepted, text) = i.with_str(|mut operator| {
        for _ in 0..character_count {
            operator.next()?;
        }
        Some(())
    });
    accepted?;
    Some(OperatorToken {
        text: text.into(),
        use_,
    })
}

/// A dangling role may be followed by a local boundary, EOF, or one invalid
/// region.  Structural starters stay for their future direct owners, and a
/// shallow newline stays with the outer statement owner.
fn dangling_follower(source: &str, baseline: usize, stops: Stops) -> Option<()> {
    let (trailing, after_trivia) = raw_trivia_suffix(source);
    if matches!(trailing, RawTrailing::Newline { indentation } if indentation <= baseline) {
        return None;
    }
    if after_trivia.is_empty() || active_stop(after_trivia, stops) {
        return Some(());
    }
    (!matches!(
        after_trivia.chars().next(),
        Some(':' | '=' | ',' | ';' | ')' | ']' | '}' | '{')
    ))
    .then_some(())
}

fn active_stop(source: &str, stops: Stops) -> bool {
    match source.chars().next() {
        Some(',') => stops & STOP_COMMA != 0,
        Some(';') => stops & STOP_SEMICOLON != 0,
        Some(')') => stops & STOP_RPAREN != 0,
        Some(']') => stops & STOP_RBRACKET != 0,
        Some('}') => stops & STOP_RBRACE != 0,
        Some(':') => stops & STOP_COLON != 0 && !source.starts_with("::"),
        Some('{') => stops & STOP_LBRACE != 0,
        _ => false,
    }
}

pub(super) fn active_stop_item(kind: super::item::TokenKind, stops: Stops) -> bool {
    match kind {
        super::item::TokenKind::Comma => stops & STOP_COMMA != 0,
        super::item::TokenKind::Semicolon => stops & STOP_SEMICOLON != 0,
        super::item::TokenKind::RParen => stops & STOP_RPAREN != 0,
        super::item::TokenKind::RBracket => stops & STOP_RBRACKET != 0,
        super::item::TokenKind::RBrace => stops & STOP_RBRACE != 0,
        super::item::TokenKind::Colon => stops & STOP_COLON != 0,
        super::item::TokenKind::LBrace => stops & STOP_LBRACE != 0,
        _ => false,
    }
}

/// Source-only reservation evidence for the second half of an exact `with:`
/// introducer. No logical item or parser state is completed by this probe.
pub(super) fn lone_colon_after_trivia(source: &str) -> bool {
    let (_, source) = raw_trivia_suffix(source);
    source.starts_with(':') && !source.starts_with("::")
}

/// Source-only layout evidence for a colon's mandatory RHS. The caller alone
/// compares it with its incoming baseline; no logical item is completed here.
pub(super) fn newline_indentation_after_trivia(source: &str) -> Option<usize> {
    let (trailing, source) = raw_trivia_suffix(source);
    match trailing {
        RawTrailing::Newline { indentation } => Some(indentation),
        RawTrailing::None | RawTrailing::Space | RawTrailing::Newline { .. } => None,
    }
}

fn operator_boundary(last: char, following: &str) -> Option<()> {
    (!is_xid_continue(last)
        || following
            .chars()
            .next()
            .is_none_or(|character| !is_xid_continue(character)))
    .then_some(())
}

fn raw_value_start(
    table: &OperatorTable,
    trailing: RawTrailing,
    source: &str,
    baseline: usize,
) -> bool {
    if matches!(trailing, RawTrailing::Newline { indentation } if indentation <= baseline) {
        return false;
    }

    match source.chars().next() {
        Some('"' | '(' | '[' | '{' | '$' | '\\' | '%' | '_' | '\'') => true,
        Some(character)
            if is_xid_start(character) || character.is_ascii_digit() || character == '.' =>
        {
            true
        }
        _ => table.value_start_source_len(source).is_some(),
    }
}

fn selected_operator_use(
    fixities: &OperatorFixities,
    fixity: OperatorFixity,
) -> Option<OperatorUse> {
    match fixity {
        OperatorFixity::Prefix => Some(OperatorUse::Prefix(
            fixities.prefix()?.right_binding_power().clone(),
        )),
        OperatorFixity::Infix => {
            let infix = fixities.infix()?;
            Some(OperatorUse::Infix {
                left: infix.left_binding_power().clone(),
                right: infix.right_binding_power().clone(),
            })
        }
        OperatorFixity::Suffix => Some(OperatorUse::Suffix(
            fixities.suffix()?.left_binding_power().clone(),
        )),
        OperatorFixity::Nullfix => fixities.is_nullfix().then_some(OperatorUse::Nullfix),
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RawTrailing {
    None,
    Space,
    Newline { indentation: usize },
}

fn raw_trivia_character(
    character: char,
    saw_newline: &mut bool,
    at_line_start: &mut bool,
    indentation: &mut usize,
) {
    match character {
        '\r' | '\n' => {
            *saw_newline = true;
            *at_line_start = true;
            *indentation = 0;
        }
        ' ' | '\t' if *at_line_start => *indentation += 1,
        _ => *at_line_start = false,
    }
}

fn raw_trivia_suffix(mut source: &str) -> (RawTrailing, &str) {
    let mut present = false;
    let mut saw_newline = false;
    let mut at_line_start = false;
    let mut indentation = 0usize;

    loop {
        let before = source;
        while let Some(character) = source.chars().next() {
            if !matches!(character, ' ' | '\t' | '\r' | '\n') {
                break;
            }
            present = true;
            raw_trivia_character(
                character,
                &mut saw_newline,
                &mut at_line_start,
                &mut indentation,
            );
            source = &source[character.len_utf8()..];
        }
        if source.starts_with("//") {
            present = true;
            source = &source[2..];
            raw_trivia_character('/', &mut saw_newline, &mut at_line_start, &mut indentation);
            raw_trivia_character('/', &mut saw_newline, &mut at_line_start, &mut indentation);
            while let Some(character) = source.chars().next() {
                if matches!(character, '\r' | '\n') {
                    break;
                }
                raw_trivia_character(
                    character,
                    &mut saw_newline,
                    &mut at_line_start,
                    &mut indentation,
                );
                source = &source[character.len_utf8()..];
            }
            continue;
        }
        if source.starts_with("/*") {
            present = true;
            let comment = source;
            source = raw_block_comment_suffix(source);
            let consumed = comment.len() - source.len();
            for character in comment[..consumed].chars() {
                raw_trivia_character(
                    character,
                    &mut saw_newline,
                    &mut at_line_start,
                    &mut indentation,
                );
            }
            continue;
        }
        if source.len() == before.len() {
            let trailing = if !present {
                RawTrailing::None
            } else if saw_newline {
                RawTrailing::Newline { indentation }
            } else {
                RawTrailing::Space
            };
            return (trailing, source);
        }
    }
}

fn raw_block_comment_suffix(mut source: &str) -> &str {
    debug_assert!(source.starts_with("/*"));
    source = &source[2..];
    let mut depth = 1usize;
    while !source.is_empty() {
        if source.starts_with("/*") {
            depth += 1;
            source = &source[2..];
            continue;
        }
        if source.starts_with("*/") {
            depth -= 1;
            source = &source[2..];
            if depth == 0 {
                return source;
            }
            continue;
        }
        let character = source
            .chars()
            .next()
            .expect("a non-empty UTF-8 suffix has one character");
        source = &source[character.len_utf8()..];
    }
    source
}
