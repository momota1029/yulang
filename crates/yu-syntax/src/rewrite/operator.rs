//! Raw successor evidence and lexical dynamic-operator selection.

use unicode_ident::{is_xid_continue, is_xid_start};

use crate::{
    operator::{OperatorFixities, OperatorFixity, OperatorTable},
    scan::operator::{OperatorSite, is_call_or_path_sensitive, judge_operator},
};

use super::{
    LexIn,
    item::{OperatorToken, OperatorUse},
};

const STOP_COMMA: u8 = 1 << 0;
const STOP_SEMICOLON: u8 = 1 << 1;
const STOP_RPAREN: u8 = 1 << 2;
const STOP_RBRACKET: u8 = 1 << 3;
const STOP_RBRACE: u8 = 1 << 4;
pub(super) const STOP_RECORD_SPREAD: u8 = 1 << 5;
pub(super) const STOP_RECORD_SPREAD_AFTER_OPERATOR: u8 = 1 << 6;

pub(super) fn stops_for(close: super::item::TokenKind) -> u8 {
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
    stops: u8,
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

fn active_stop(source: &str, stops: u8) -> bool {
    match source.chars().next() {
        Some(',') => stops & STOP_COMMA != 0,
        Some(';') => stops & STOP_SEMICOLON != 0,
        Some(')') => stops & STOP_RPAREN != 0,
        Some(']') => stops & STOP_RBRACKET != 0,
        Some('}') => stops & STOP_RBRACE != 0,
        _ => false,
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
