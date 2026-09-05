//! Raw successor evidence and lexical dynamic-operator selection.

use unicode_ident::{is_xid_continue, is_xid_start};

use crate::{
    operator::{OperatorFixities, OperatorFixity, OperatorTable},
    scan::operator::{OperatorSite, is_call_or_path_sensitive, judge_operator},
};

use super::{
    LexIn, Stops,
    current_item::LineEntry,
    item::{OperatorToken, OperatorUse},
    yumark::{FenceBoundary, FenceLineDecision, judge_fence_line},
};

pub(super) const STOP_COMMA: Stops = 1 << 0;
pub(super) const STOP_SEMICOLON: Stops = 1 << 1;
const STOP_RPAREN: Stops = 1 << 2;
const STOP_RBRACKET: Stops = 1 << 3;
const STOP_RBRACE: Stops = 1 << 4;
pub(super) const STOP_RECORD_SPREAD: Stops = 1 << 5;
pub(super) const STOP_RECORD_SPREAD_AFTER_OPERATOR: Stops = 1 << 6;
pub(super) const STOP_COLON: Stops = 1 << 7;
pub(super) const STOP_LBRACE: Stops = 1 << 8;
pub(super) const STOP_ELSIF: Stops = 1 << 9;
pub(super) const STOP_ELSE: Stops = 1 << 10;
pub(super) const STOP_ARROW: Stops = 1 << 11;
pub(super) const STOP_LINE_BREAK: Stops = 1 << 12;
pub(super) const STOP_WITH: Stops = 1 << 13;
pub(super) const STOP_IN: Stops = 1 << 14;

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
    i: LexIn,
    site: OperatorSite,
    has_leading_trivia: bool,
    baseline: usize,
    stops: Stops,
) -> Option<OperatorToken> {
    scan_operator_fenced(i, site, has_leading_trivia, baseline, stops, 0, None)
}

/// Selects one dynamic operator using only the visible suffix of its current
/// cell. The caller passes the immediate payload coordinate; nothing is
/// retained after this source-only lexical probe returns.
pub(super) fn scan_operator_fenced(
    mut i: LexIn,
    site: OperatorSite,
    has_leading_trivia: bool,
    baseline: usize,
    stops: Stops,
    payload_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<OperatorToken> {
    let table = i.recovery().operators();
    let source = i.remainder();
    let (use_, end) = table.longest_source_match_then(source, |last, entry, end| {
        operator_boundary(last, &source[end..])?;
        let kinds = entry.fixities().kinds();
        let observation = observe_fenced_trivia(
            &source[end..],
            payload_origin.checked_add(end)?,
            LineEntry::InLine,
            fence,
        );
        let (post_whitespace, value_start) = match observation {
            TriviaObservation::Boundary => (true, false),
            TriviaObservation::Visible(visible) => {
                if is_call_or_path_sensitive(kinds)
                    && !visible.present
                    && matches!(visible.source.chars().next(), Some('(' | ':'))
                {
                    return None;
                }
                let post_whitespace = visible.present
                    || visible.source.is_empty()
                    || active_stop(visible.source, stops);
                let value_start =
                    raw_value_start(table, visible.indentation, visible.source, baseline);
                (post_whitespace, value_start)
            }
        };
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
    i: LexIn,
    site: OperatorSite,
    baseline: usize,
    stops: Stops,
) -> Option<OperatorToken> {
    scan_dangling_operator_fenced(i, site, baseline, stops, 0, None)
}

/// Fence-aware counterpart of [`scan_dangling_operator`]. A fence boundary
/// is a local EOF fact for this one spelling; the pending boundary Item stays
/// for the next current-Item acquisition.
pub(super) fn scan_dangling_operator_fenced(
    mut i: LexIn,
    site: OperatorSite,
    baseline: usize,
    stops: Stops,
    payload_origin: usize,
    fence: Option<&FenceBoundary>,
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
        dangling_follower_fenced(
            &source[end..],
            payload_origin.checked_add(end)?,
            baseline,
            stops,
            fence,
        )?;
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
fn dangling_follower_fenced(
    source: &str,
    source_origin: usize,
    baseline: usize,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> Option<()> {
    match observe_fenced_trivia(source, source_origin, LineEntry::InLine, fence) {
        TriviaObservation::Boundary => Some(()),
        TriviaObservation::Visible(visible) => {
            if visible
                .indentation
                .is_some_and(|indentation| indentation <= baseline)
            {
                return None;
            }
            if visible.source.is_empty() || active_stop(visible.source, stops) {
                return Some(());
            }
            (!matches!(
                visible.source.chars().next(),
                Some(':' | '=' | ',' | ';' | ')' | ']' | '}' | '{')
            ))
            .then_some(())
        }
    }
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
        Some('-') => stops & STOP_ARROW != 0 && super::lexer::is_exact_arm_arrow(source),
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
        super::item::TokenKind::Arrow => stops & STOP_ARROW != 0,
        _ => false,
    }
}

/// Source-only reservation evidence for the second half of an exact `with:`
/// introducer. No logical item or parser state is completed by this probe.
pub(super) fn lone_colon_after_trivia(source: &str) -> bool {
    lone_colon_after_fenced_trivia(source, 0, LineEntry::InLine, None)
}

pub(super) fn lone_colon_after_fenced_trivia(
    source: &str,
    source_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> bool {
    matches!(
        observe_fenced_trivia(source, source_origin, line_entry, fence),
        TriviaObservation::Visible(VisibleTrivia { source, .. })
            if source.starts_with(':') && !source.starts_with("::")
    )
}

/// Source-only layout evidence for a colon's mandatory RHS. The caller alone
/// compares it with its incoming baseline; no logical item is completed here.
pub(super) fn newline_indentation_after_trivia(source: &str) -> Option<usize> {
    newline_indentation_after_fenced_trivia(source, 0, LineEntry::InLine, None)
}

pub(super) fn newline_indentation_after_fenced_trivia(
    source: &str,
    source_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<usize> {
    match observe_fenced_trivia(source, source_origin, line_entry, fence) {
        TriviaObservation::Visible(visible) => visible.indentation,
        TriviaObservation::Boundary => None,
    }
}

/// Return source-only facts about one maximal trivia run.  Statement-head
/// reservation uses the same lexical trivia boundary as operator and body
/// layout probes without completing an Item.
pub(super) fn source_after_trivia(source: &str) -> (&str, bool, Option<usize>) {
    let TriviaObservation::Visible(visible) =
        observe_fenced_trivia(source, 0, LineEntry::InLine, None)
    else {
        unreachable!("ordinary source observation has no fence boundary");
    };
    (visible.source, visible.present, visible.indentation)
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
    indentation: Option<usize>,
    source: &str,
    baseline: usize,
) -> bool {
    if indentation.is_some_and(|indentation| indentation <= baseline) {
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

pub(super) enum TriviaObservation<'source> {
    Visible(VisibleTrivia<'source>),
    Boundary,
}

pub(super) struct VisibleTrivia<'source> {
    pub(super) source: &'source str,
    pub(super) present: bool,
    pub(super) indentation: Option<usize>,
}

/// Reads one maximal trivia suffix without building Items or fence facts.
/// Under a fence it stops at the first close, transition, or physical EOF and
/// never reads the next outer line. Accepted quote prefixes are skipped as
/// foreign physical text, never reclassified as ordinary whitespace.
pub(super) fn observe_fenced_trivia<'source>(
    mut source: &'source str,
    mut source_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> TriviaObservation<'source> {
    if fence.is_none() {
        return observe_ordinary_trivia(source);
    }

    let mut present = false;
    let mut saw_newline = false;
    let mut at_line_start = false;
    let mut indentation = 0usize;

    if !observe_line(
        &mut source,
        &mut source_origin,
        &mut line_entry,
        fence,
        &mut at_line_start,
    ) {
        return TriviaObservation::Boundary;
    }

    loop {
        if source.starts_with([' ', '\t']) {
            present = true;
            let character = source
                .chars()
                .next()
                .expect("a nonempty source suffix has one character");
            raw_trivia_character(
                character,
                &mut saw_newline,
                &mut at_line_start,
                &mut indentation,
            );
            advance_source(&mut source, &mut source_origin, character.len_utf8());
            continue;
        }

        if source.starts_with("\r\n") {
            present = true;
            raw_trivia_character('\r', &mut saw_newline, &mut at_line_start, &mut indentation);
            raw_trivia_character('\n', &mut saw_newline, &mut at_line_start, &mut indentation);
            advance_source(&mut source, &mut source_origin, 2);
            line_entry = LineEntry::PhysicalStart;
            if !observe_line(
                &mut source,
                &mut source_origin,
                &mut line_entry,
                fence,
                &mut at_line_start,
            ) {
                return TriviaObservation::Boundary;
            }
            continue;
        }

        if source.starts_with('\n') {
            present = true;
            raw_trivia_character('\n', &mut saw_newline, &mut at_line_start, &mut indentation);
            advance_source(&mut source, &mut source_origin, 1);
            line_entry = LineEntry::PhysicalStart;
            if !observe_line(
                &mut source,
                &mut source_origin,
                &mut line_entry,
                fence,
                &mut at_line_start,
            ) {
                return TriviaObservation::Boundary;
            }
            continue;
        }

        if source.starts_with('\r') {
            present = true;
            raw_trivia_character('\r', &mut saw_newline, &mut at_line_start, &mut indentation);
            advance_source(&mut source, &mut source_origin, 1);
            line_entry = LineEntry::InLine;
            continue;
        }

        if source.starts_with("//") {
            present = true;
            raw_trivia_character('/', &mut saw_newline, &mut at_line_start, &mut indentation);
            raw_trivia_character('/', &mut saw_newline, &mut at_line_start, &mut indentation);
            advance_source(&mut source, &mut source_origin, 2);
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
                advance_source(&mut source, &mut source_origin, character.len_utf8());
            }
            continue;
        }

        if source.starts_with("/*") {
            present = true;
            if !observe_block_comment(
                &mut source,
                &mut source_origin,
                &mut line_entry,
                fence,
                &mut saw_newline,
                &mut at_line_start,
                &mut indentation,
            ) {
                return TriviaObservation::Boundary;
            }
            continue;
        }

        if source.is_empty() && fence.is_some() {
            return TriviaObservation::Boundary;
        }

        return TriviaObservation::Visible(VisibleTrivia {
            source,
            present,
            indentation: saw_newline.then_some(indentation),
        });
    }
}

/// The `None` mode is the retained ordinary raw scanner. It deliberately
/// avoids fence coordinates and line classification, preserving the ordinary
/// operator/follower path's work and result shape.
fn observe_ordinary_trivia<'source>(mut source: &'source str) -> TriviaObservation<'source> {
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
            source = ordinary_block_comment_suffix(source);
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
            return TriviaObservation::Visible(VisibleTrivia {
                source,
                present,
                indentation: saw_newline.then_some(indentation),
            });
        }
    }
}

fn ordinary_block_comment_suffix(mut source: &str) -> &str {
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
            .expect("a nonempty UTF-8 suffix has one character");
        source = &source[character.len_utf8()..];
    }
    source
}

fn observe_line(
    source: &mut &str,
    source_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
    at_line_start: &mut bool,
) -> bool {
    if *line_entry != LineEntry::PhysicalStart {
        return true;
    }
    let Some(fence) = fence else {
        return true;
    };
    match judge_fence_line(source, *source_origin, fence) {
        FenceLineDecision::Boundary(_) => false,
        FenceLineDecision::Body { prefix: None, .. } => {
            *line_entry = LineEntry::InLine;
            true
        }
        FenceLineDecision::Body {
            prefix: Some(_),
            content,
        } => {
            let length = content
                .checked_sub(*source_origin)
                .expect("a judged source prefix remains on its current line");
            advance_source(source, source_origin, length);
            *line_entry = LineEntry::InLine;
            *at_line_start = false;
            true
        }
    }
}

fn observe_block_comment(
    source: &mut &str,
    source_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
    saw_newline: &mut bool,
    at_line_start: &mut bool,
    indentation: &mut usize,
) -> bool {
    debug_assert!(source.starts_with("/*"));
    raw_trivia_character('/', saw_newline, at_line_start, indentation);
    raw_trivia_character('*', saw_newline, at_line_start, indentation);
    advance_source(source, source_origin, 2);
    let mut depth = 1usize;

    while !source.is_empty() {
        if source.starts_with("/*") {
            raw_trivia_character('/', saw_newline, at_line_start, indentation);
            raw_trivia_character('*', saw_newline, at_line_start, indentation);
            advance_source(source, source_origin, 2);
            depth = depth
                .checked_add(1)
                .expect("block-comment depth must fit usize");
            continue;
        }
        if source.starts_with("*/") {
            raw_trivia_character('*', saw_newline, at_line_start, indentation);
            raw_trivia_character('/', saw_newline, at_line_start, indentation);
            advance_source(source, source_origin, 2);
            depth -= 1;
            if depth == 0 {
                return true;
            }
            continue;
        }
        if source.starts_with("\r\n") {
            raw_trivia_character('\r', saw_newline, at_line_start, indentation);
            raw_trivia_character('\n', saw_newline, at_line_start, indentation);
            advance_source(source, source_origin, 2);
            *line_entry = LineEntry::PhysicalStart;
            if !observe_line(source, source_origin, line_entry, fence, at_line_start) {
                return false;
            }
            continue;
        }
        if source.starts_with('\n') {
            raw_trivia_character('\n', saw_newline, at_line_start, indentation);
            advance_source(source, source_origin, 1);
            *line_entry = LineEntry::PhysicalStart;
            if !observe_line(source, source_origin, line_entry, fence, at_line_start) {
                return false;
            }
            continue;
        }
        let character = source
            .chars()
            .next()
            .expect("a nonempty source suffix has one character");
        raw_trivia_character(character, saw_newline, at_line_start, indentation);
        advance_source(source, source_origin, character.len_utf8());
    }
    true
}

fn advance_source(source: &mut &str, source_origin: &mut usize, length: usize) {
    *source = &source[length..];
    *source_origin = source_origin
        .checked_add(length)
        .expect("a source-only probe coordinate must fit usize");
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
