//! Header-mode scanning for operator bodies that are not expression-parsed.
//!
//! This scanner makes comments, normal strings, heredocs, string interpolation,
//! rule literals, quoted/block Yumark, and Yumark code fences opaque to the
//! outer delimiter/layout scan.

use std::ops::Range;

use chasa::{
    ErrorSink,
    error::std::{Unexpected, UnexpectedEndOfInput},
    parser::SkipParserOnce as _,
    prelude::{In, any, from_fn, item},
};

use crate::{
    input::SourceInput,
    session::{EmbeddedLexicalMode, FenceKind, ParseLocal, YumarkMode},
};

use super::trivia::scan_trivia;

/// The exact source extent consumed while skipping one operator body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct OpaqueBodySpan<'source> {
    text: &'source str,
    start: usize,
    end: usize,
}

impl<'source> OpaqueBodySpan<'source> {
    pub(crate) fn text(self) -> &'source str {
        self.text
    }

    pub(crate) fn range(self) -> Range<usize> {
        self.start..self.end
    }
}

/// Consumes an operator body through its next depth-zero layout boundary.
///
/// The scanner starts immediately after the header's `=`. A boundary newline
/// and its indentation are included in the returned span, leaving the input at
/// the first character of the following declaration. Delimiter depth is local
/// because this opaque scan does not establish grammar-owned structural groups.
pub(crate) fn scan_opaque_body<'source, E>(
    mut input: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<OpaqueBodySpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = input.pos();
    let baseline = input
        .local
        .indentation_baseline()
        .map_or(input.local.line().line_indent, |baseline| baseline.column);
    let mut delimiter_depth = 0_usize;

    loop {
        if starts_comment(input.input.remainder()) {
            let trivia_start = input.pos();
            input.run(from_fn(scan_trivia))?;

            if input.input.remainder().is_empty()
                || (delimiter_depth == 0
                    && crossed_layout_boundary(trivia_start, baseline, input.local))
            {
                return Some(body_span(start, &input));
            }
            continue;
        }

        if input.input.remainder().starts_with("'[") || input.input.remainder().starts_with("'{") {
            if input.run(from_fn(scan_quoted_yumark_region))? == RegionEnd::Unterminated {
                return Some(body_span(start, &input));
            }
            continue;
        }

        if input.input.remainder().starts_with("~\"") {
            if input.run(from_fn(scan_rule_literal_region))? == RegionEnd::Unterminated {
                return Some(body_span(start, &input));
            }
            continue;
        }

        if input.input.remainder().starts_with('"') {
            if input.run(from_fn(scan_string_region))? == RegionEnd::Unterminated {
                return Some(body_span(start, &input));
            }
            continue;
        }

        let character_start = input.pos();
        let Some(character) = input.maybe(any)? else {
            return Some(body_span(start, &input));
        };

        let newline = if character == '\r' {
            input.skip(item('\n').or_not())?;
            update_newline(character_start, input.pos(), input.local);
            true
        } else if character == '\n' {
            update_newline(character_start, input.pos(), input.local);
            true
        } else {
            update_non_newline(character, input.local);
            false
        };

        match character {
            '(' | '[' | '{' => delimiter_depth += 1,
            ')' | ']' | '}' => delimiter_depth = delimiter_depth.saturating_sub(1),
            _ => {}
        }

        if newline && delimiter_depth == 0 {
            consume_indentation(&mut input)?;
            if input.local.line().line_indent <= baseline {
                return Some(body_span(start, &input));
            }
        }
    }
}

fn scan_string_region<E>(
    mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<RegionEnd>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    input.skip(item('"'))?;
    mark_non_trivia(input.local);

    let quote_count = if input.input.remainder().starts_with("\"\"") {
        input.skip(item('"'))?;
        input.skip(item('"'))?;
        let mut count = 3;
        while input.maybe(item('"'))?.is_some() {
            count += 1;
        }
        count
    } else {
        1
    };
    let mode = if quote_count == 1 {
        EmbeddedLexicalMode::NormalString
    } else {
        EmbeddedLexicalMode::Heredoc { quote_count }
    };
    input.local.push_lexical_mode(mode);

    loop {
        if starts_quote_sentinel(input.input.remainder(), quote_count) {
            for _ in 0..quote_count {
                input.skip(item('"'))?;
            }
            mark_non_trivia(input.local);
            debug_assert_eq!(input.local.pop_lexical_mode(), Some(mode));
            return Some(RegionEnd::Closed);
        }

        if input.input.remainder().starts_with('%') {
            if input.run(from_fn(scan_string_interpolation_region))? == RegionEnd::Unterminated {
                return Some(RegionEnd::Unterminated);
            }
            continue;
        }

        let character_start = input.pos();
        let Some(character) = input.maybe(any)? else {
            return Some(RegionEnd::Unterminated);
        };
        update_region_character(character, character_start, &mut input)?;

        if character == '\\' {
            let escaped_start = input.pos();
            let Some(escaped) = input.maybe(any)? else {
                return Some(RegionEnd::Unterminated);
            };
            update_region_character(escaped, escaped_start, &mut input)?;
        }
    }
}

/// Consumes one apostrophe-prefixed Yumark literal: `'[...]` or `'{...}`.
///
/// The literal's outer delimiter and all nested `[]`, `{}`, and `()` groups
/// are tracked locally. Yumark text is not Yulang string syntax, so quotes and
/// escapes remain ordinary text here.
fn scan_quoted_yumark_region<E>(
    mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<RegionEnd>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    input.skip(item('\''))?;
    mark_non_trivia(input.local);

    let (literal_mode, outer_close) = if input.input.remainder().starts_with('[') {
        input.skip(item('['))?;
        (YumarkMode::Inline, ']')
    } else {
        input.skip(item('{'))?;
        (YumarkMode::Block, '}')
    };
    mark_non_trivia(input.local);

    let mut mode = literal_mode;
    let mut quote_depth = 0_usize;
    let line_document_continuation = false;
    input.local.push_lexical_mode(EmbeddedLexicalMode::Yumark {
        mode,
        quote_depth,
        line_document_continuation,
    });

    let mut delimiters = vec![outer_close];
    let mut at_block_document_start = literal_mode == YumarkMode::Block;

    loop {
        if literal_mode == YumarkMode::Block && delimiters.len() == 1 && at_block_document_start {
            if input.local.line().at_line_start {
                consume_indentation(&mut input)?;
            }
            quote_depth = scan_yumark_quote_prefix(&mut input)?;
            mode = if quote_depth == 0 {
                YumarkMode::Block
            } else {
                YumarkMode::Quoted
            };
            replace_yumark_mode(&mut input, mode, quote_depth, line_document_continuation);

            if input.input.remainder().starts_with("```") {
                if input.run(from_fn(|input| {
                    scan_yumark_fence_region(input, quote_depth)
                }))? == RegionEnd::Unterminated
                {
                    return Some(RegionEnd::Unterminated);
                }
                quote_depth = 0;
                mode = YumarkMode::Block;
                replace_yumark_mode(&mut input, mode, quote_depth, line_document_continuation);
                at_block_document_start = false;
                continue;
            }
        }

        let character_start = input.pos();
        let Some(character) = input.maybe(any)? else {
            return Some(RegionEnd::Unterminated);
        };
        let newline = matches!(character, '\r' | '\n');
        update_region_character(character, character_start, &mut input)?;

        if delimiters.last().copied() == Some(character) {
            delimiters.pop();
            if delimiters.is_empty() {
                debug_assert_eq!(
                    input.local.pop_lexical_mode(),
                    Some(EmbeddedLexicalMode::Yumark {
                        mode,
                        quote_depth,
                        line_document_continuation,
                    })
                );
                return Some(RegionEnd::Closed);
            }
        } else if let Some(close) = matching_delimiter(character) {
            delimiters.push(close);
        }

        at_block_document_start = literal_mode == YumarkMode::Block && newline;
    }
}

/// Consumes a structural Yumark code fence, retaining its kind and logical
/// line-continuation state until the matching closing fence or EOF.
fn scan_yumark_fence_region<E>(
    mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
    quote_depth: usize,
) -> Option<RegionEnd>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    for _ in 0..3 {
        input.skip(item('`'))?;
    }
    mark_non_trivia(input.local);

    // The oracle tests this prefix immediately after the opening fence, not
    // after parsing or normalizing its info line.
    let kind = if input.input.remainder().starts_with("yulang") {
        FenceKind::Yulang
    } else {
        FenceKind::Raw
    };
    input.local.push_lexical_mode(EmbeddedLexicalMode::Fence {
        kind,
        continuation: false,
    });

    // Consume the entire info line. A fence without its separating newline is
    // incomplete, even if its info spelling happened to name Yulang.
    loop {
        let character_start = input.pos();
        let Some(character) = input.maybe(any)? else {
            return Some(RegionEnd::Unterminated);
        };
        let newline = matches!(character, '\r' | '\n');
        update_region_character(character, character_start, &mut input)?;
        if newline {
            break;
        }
    }
    replace_fence_mode(&mut input, kind, true);

    let end = match kind {
        FenceKind::Raw => scan_raw_yumark_fence_body(&mut input, quote_depth)?,
        FenceKind::Yulang => scan_yulang_fence_body(&mut input, quote_depth)?,
    };
    if end == RegionEnd::Unterminated {
        return Some(RegionEnd::Unterminated);
    }

    debug_assert_eq!(
        input.local.pop_lexical_mode(),
        Some(EmbeddedLexicalMode::Fence {
            kind,
            continuation: true,
        })
    );
    Some(RegionEnd::Closed)
}

/// Raw fences only inspect structural line starts. Everything else, including
/// braces and other lexical openers, is plain fence text.
fn scan_raw_yumark_fence_body<E>(
    mut input: &mut In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
    quote_depth: usize,
) -> Option<RegionEnd>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut continuation = true;
    loop {
        if continuation
            && consume_yumark_fence_line_prefix(&mut input, quote_depth)?
            && input.input.remainder().starts_with("```")
        {
            consume_fence_sigil(&mut input)?;
            return Some(RegionEnd::Closed);
        }

        let character_start = input.pos();
        let Some(character) = input.maybe(any)? else {
            return Some(RegionEnd::Unterminated);
        };
        continuation = matches!(character, '\r' | '\n');
        update_region_character(character, character_start, &mut input)?;
        replace_fence_mode(&mut input, FenceKind::Raw, continuation);
    }
}

/// Yulang fence bodies need lexical-region awareness so a triple backtick in a
/// string, comment, interpolation, rule literal, or nested Yumark literal is
/// not mistaken for the statement-level fence stop.
fn scan_yulang_fence_body<E>(
    mut input: &mut In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
    quote_depth: usize,
) -> Option<RegionEnd>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut continuation = true;
    loop {
        if continuation
            && consume_yumark_fence_line_prefix(&mut input, quote_depth)?
            && input.input.remainder().starts_with("```")
        {
            consume_fence_sigil(&mut input)?;
            return Some(RegionEnd::Closed);
        }

        if starts_comment(input.input.remainder()) {
            input.run(from_fn(scan_trivia))?;
            if input.input.remainder().is_empty() {
                return Some(RegionEnd::Unterminated);
            }
            continuation = input.local.line().at_line_start;
            replace_fence_mode(&mut input, FenceKind::Yulang, continuation);
            continue;
        }

        if input.input.remainder().starts_with("'[") || input.input.remainder().starts_with("'{") {
            if input.run(from_fn(scan_quoted_yumark_region))? == RegionEnd::Unterminated {
                return Some(RegionEnd::Unterminated);
            }
            continuation = input.local.line().at_line_start;
            replace_fence_mode(&mut input, FenceKind::Yulang, continuation);
            continue;
        }

        if input.input.remainder().starts_with("~\"") {
            if input.run(from_fn(scan_rule_literal_region))? == RegionEnd::Unterminated {
                return Some(RegionEnd::Unterminated);
            }
            continuation = input.local.line().at_line_start;
            replace_fence_mode(&mut input, FenceKind::Yulang, continuation);
            continue;
        }

        if input.input.remainder().starts_with('"') {
            if input.run(from_fn(scan_string_region))? == RegionEnd::Unterminated {
                return Some(RegionEnd::Unterminated);
            }
            continuation = input.local.line().at_line_start;
            replace_fence_mode(&mut input, FenceKind::Yulang, continuation);
            continue;
        }

        let character_start = input.pos();
        let Some(character) = input.maybe(any)? else {
            return Some(RegionEnd::Unterminated);
        };
        continuation = matches!(character, '\r' | '\n');
        update_region_character(character, character_start, &mut input)?;
        replace_fence_mode(&mut input, FenceKind::Yulang, continuation);
    }
}

fn consume_yumark_fence_line_prefix<E>(
    input: &mut In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
    quote_depth: usize,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    consume_indentation(input)?;
    let Some(prefix_len) = yumark_quote_prefix_len(input.input.remainder(), quote_depth) else {
        return Some(false);
    };
    for _ in 0..prefix_len {
        let character_start = input.pos();
        let Some(character) = input.maybe(any)? else {
            return Some(false);
        };
        update_region_character(character, character_start, input)?;
    }
    Some(true)
}

fn yumark_quote_prefix_len(remainder: &str, quote_depth: usize) -> Option<usize> {
    let mut index = 0_usize;
    for _ in 0..quote_depth {
        let rest = remainder.get(index..)?;
        if !rest.starts_with('>') {
            return None;
        }
        index += 1;
        if matches!(remainder.get(index..)?.chars().next(), Some(' ' | '\t')) {
            index += 1;
        }
    }
    Some(index)
}

fn consume_fence_sigil<E>(input: &mut In<'_, SourceInput<'_>, (), &mut ParseLocal, E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    for _ in 0..3 {
        input.skip(item('`'))?;
    }
    mark_non_trivia(input.local);
    Some(())
}

fn replace_fence_mode<E>(
    input: &mut In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
    kind: FenceKind,
    continuation: bool,
) where
    E: ErrorSink<usize>,
{
    input
        .local
        .replace_lexical_mode(EmbeddedLexicalMode::Fence { kind, continuation });
}

fn scan_yumark_quote_prefix<E>(
    input: &mut In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<usize>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut quote_depth = 0_usize;
    while input.input.remainder().starts_with('>') {
        input.skip(item('>'))?;
        mark_non_trivia(input.local);
        quote_depth += 1;

        if let Some(space) = input.maybe(item(' ').or(item('\t')))? {
            update_non_newline(space, input.local);
        }
    }
    Some(quote_depth)
}

fn replace_yumark_mode<E>(
    input: &mut In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
    mode: YumarkMode,
    quote_depth: usize,
    line_document_continuation: bool,
) where
    E: ErrorSink<usize>,
{
    input
        .local
        .replace_lexical_mode(EmbeddedLexicalMode::Yumark {
            mode,
            quote_depth,
            line_document_continuation,
        });
}

fn matching_delimiter(character: char) -> Option<char> {
    match character {
        '[' => Some(']'),
        '{' => Some('}'),
        '(' => Some(')'),
        _ => None,
    }
}

/// Consumes one oracle `~"..."` rule literal.
///
/// Unlike a normal string, a backslash has no effect on this literal's quote
/// terminator. Its only nested structure is `{...}` rule interpolation, whose
/// delimiters must remain opaque to the surrounding operator body.
fn scan_rule_literal_region<E>(
    mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<RegionEnd>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    input.skip(item('~'))?;
    input.skip(item('"'))?;
    mark_non_trivia(input.local);
    input
        .local
        .push_lexical_mode(EmbeddedLexicalMode::RuleLiteral);

    loop {
        if input.input.remainder().starts_with('"') {
            input.skip(item('"'))?;
            mark_non_trivia(input.local);
            debug_assert_eq!(
                input.local.pop_lexical_mode(),
                Some(EmbeddedLexicalMode::RuleLiteral)
            );
            return Some(RegionEnd::Closed);
        }

        if input.input.remainder().starts_with('{') {
            if input.run(from_fn(scan_rule_literal_interpolation))? == RegionEnd::Unterminated {
                return Some(RegionEnd::Unterminated);
            }
            continue;
        }

        let character_start = input.pos();
        let Some(character) = input.maybe(any)? else {
            return Some(RegionEnd::Unterminated);
        };
        update_region_character(character, character_start, &mut input)?;
    }
}

/// Consumes a `{...}` rule-literal interpolation without interpreting capture
/// syntax. Capture and lazy-capture spellings do not change the lexical
/// boundary; only nested delimiters, comments, and normal strings do.
fn scan_rule_literal_interpolation<E>(
    mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<RegionEnd>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    input.skip(item('{'))?;
    mark_non_trivia(input.local);
    let mut delimiter_depth = 1_usize;

    loop {
        if starts_comment(input.input.remainder()) {
            input.run(from_fn(scan_trivia))?;
            if input.input.remainder().is_empty() {
                return Some(RegionEnd::Unterminated);
            }
            continue;
        }

        if input.input.remainder().starts_with('"') {
            if input.run(from_fn(scan_string_region))? == RegionEnd::Unterminated {
                return Some(RegionEnd::Unterminated);
            }
            continue;
        }

        let character_start = input.pos();
        let Some(character) = input.maybe(any)? else {
            return Some(RegionEnd::Unterminated);
        };
        update_region_character(character, character_start, &mut input)?;

        match character {
            '(' | '[' | '{' => delimiter_depth += 1,
            ')' | ']' => delimiter_depth = delimiter_depth.saturating_sub(1).max(1),
            '}' if delimiter_depth == 1 => return Some(RegionEnd::Closed),
            '}' => delimiter_depth -= 1,
            _ => {}
        }
    }
}

/// Consumes one oracle string interpolation, from `%` through its matching
/// outer `}`. The text between `%` and `{` is format text, not string text: it
/// is deliberately scanned byte-for-byte so quotes, escapes, and newlines do
/// not terminate the enclosing string before the interpolation body begins.
fn scan_string_interpolation_region<E>(
    mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<RegionEnd>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    input.skip(item('%'))?;
    mark_non_trivia(input.local);
    input
        .local
        .push_lexical_mode(EmbeddedLexicalMode::Interpolation { delimiter_depth: 0 });

    loop {
        if input.input.remainder().starts_with('{') {
            input.skip(item('{'))?;
            mark_non_trivia(input.local);
            input
                .local
                .replace_lexical_mode(EmbeddedLexicalMode::Interpolation { delimiter_depth: 1 });
            break;
        }

        let character_start = input.pos();
        let Some(character) = input.maybe(any)? else {
            return Some(RegionEnd::Unterminated);
        };
        update_region_character(character, character_start, &mut input)?;
    }

    let mut delimiter_depth = 1_usize;
    loop {
        if starts_comment(input.input.remainder()) {
            input.run(from_fn(scan_trivia))?;
            if input.input.remainder().is_empty() {
                return Some(RegionEnd::Unterminated);
            }
            continue;
        }

        if input.input.remainder().starts_with('"') {
            if input.run(from_fn(scan_string_region))? == RegionEnd::Unterminated {
                return Some(RegionEnd::Unterminated);
            }
            continue;
        }

        let character_start = input.pos();
        let Some(character) = input.maybe(any)? else {
            return Some(RegionEnd::Unterminated);
        };
        update_region_character(character, character_start, &mut input)?;

        match character {
            '(' | '[' | '{' => delimiter_depth += 1,
            ')' | ']' => delimiter_depth = delimiter_depth.saturating_sub(1).max(1),
            '}' if delimiter_depth == 1 => {
                debug_assert_eq!(
                    input.local.pop_lexical_mode(),
                    Some(EmbeddedLexicalMode::Interpolation { delimiter_depth: 1 })
                );
                return Some(RegionEnd::Closed);
            }
            '}' => delimiter_depth -= 1,
            _ => {}
        }

        input
            .local
            .replace_lexical_mode(EmbeddedLexicalMode::Interpolation { delimiter_depth });
    }
}

fn update_region_character<E>(
    character: char,
    start: usize,
    input: &mut In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    if character == '\r' {
        input.skip(item('\n').or_not())?;
        update_newline(start, input.pos(), input.local);
    } else if character == '\n' {
        update_newline(start, input.pos(), input.local);
    } else {
        update_non_newline(character, input.local);
    }
    Some(())
}

fn consume_indentation<E>(input: &mut In<'_, SourceInput<'_>, (), &mut ParseLocal, E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    while let Some(character) = input.maybe(item(' ').or(item('\t')))? {
        update_non_newline(character, input.local);
    }
    Some(())
}

fn starts_comment(remainder: &str) -> bool {
    remainder.starts_with("//") || remainder.starts_with("/*")
}

fn starts_quote_sentinel(remainder: &str, quote_count: usize) -> bool {
    remainder
        .chars()
        .take(quote_count)
        .all(|character| character == '"')
        && remainder.chars().take(quote_count).count() == quote_count
}

fn crossed_layout_boundary(start: usize, baseline: usize, local: &ParseLocal) -> bool {
    let line = local.line();
    line.last_newline
        .is_some_and(|(newline_start, _)| newline_start >= start)
        && line.at_line_start
        && line.line_indent <= baseline
}

fn update_newline(start: usize, end: usize, local: &mut ParseLocal) {
    local.set_line(crate::session::LineState {
        last_newline: Some((start, end)),
        line_start: end,
        line_indent: 0,
        at_line_start: true,
    });
}

fn update_non_newline(character: char, local: &mut ParseLocal) {
    let mut line = local.line();
    if matches!(character, ' ' | '\t') && line.at_line_start {
        line.line_indent += 1;
    } else if !matches!(character, ' ' | '\t') {
        line.at_line_start = false;
    }
    local.set_line(line);
}

fn mark_non_trivia(local: &mut ParseLocal) {
    let mut line = local.line();
    line.at_line_start = false;
    local.set_line(line);
}

fn body_span<'source, E>(
    start: usize,
    input: &In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> OpaqueBodySpan<'source>
where
    E: ErrorSink<usize>,
{
    let end = input.pos();
    OpaqueBodySpan {
        text: &input.input.source()[start..end],
        start,
        end,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RegionEnd {
    Closed,
    Unterminated,
}

#[cfg(test)]
mod tests {
    use super::*;
    use chasa::input::IsCut;

    use crate::session::{Delimiter, IndentationBaseline, IndentationBaselineKind, LineState};

    #[test]
    fn balanced_delimiters_suspend_layout_boundaries() {
        let result = scan(" (a\n  + [b, {c}])\nnext");
        let expected = " (a\n  + [b, {c}])\n";

        assert_eq!(result.body, (0..expected.len(), expected));
        assert_eq!(result.remainder, "next");
    }

    #[test]
    fn string_brace_does_not_extend_the_opaque_body() {
        let result = scan(" \"{\"\nnext");
        let expected = " \"{\"\n";

        assert_eq!(result.body, (0..expected.len(), expected));
        assert_eq!(result.remainder, "next");
        assert_eq!(result.lexical_mode, None);
    }

    #[test]
    fn heredoc_newline_is_not_an_outer_layout_boundary() {
        let result = scan(" \"\"\"first\nnext\"\"\"\nheader");
        let expected = " \"\"\"first\nnext\"\"\"\n";

        assert_eq!(result.body, (0..expected.len(), expected));
        assert_eq!(result.remainder, "header");
        assert_eq!(result.lexical_mode, None);
    }

    #[test]
    fn interpolation_suspends_outer_layout_until_its_string_ends() {
        let simple = scan(" \"%{x}\"\nnext");
        let statement = scan(" \"%{my x = 41; x + 1}\"\nnext");
        let nested = scan(" \"%{ { my x = 41; x + 1 } }\"\nnext");

        for (result, expected) in [
            (simple, " \"%{x}\"\n"),
            (statement, " \"%{my x = 41; x + 1}\"\n"),
            (nested, " \"%{ { my x = 41; x + 1 } }\"\n"),
        ] {
            assert_eq!(result.body, (0..expected.len(), expected));
            assert_eq!(result.remainder, "next");
            assert_eq!(result.lexical_mode, None);
        }
    }

    #[test]
    fn interpolation_format_text_does_not_apply_string_termination_rules() {
        let result = scan(" \"%format \"text\"\n{ value }\"\nnext");
        let expected = " \"%format \"text\"\n{ value }\"\n";

        assert_eq!(result.body, (0..expected.len(), expected));
        assert_eq!(result.remainder, "next");
        assert_eq!(result.lexical_mode, None);
    }

    #[test]
    fn interpolation_body_reuses_string_heredoc_and_comment_regions() {
        let result = scan(" \"%{ \"}\" \"\"\"}\nvalue\"\"\" /* }\n*/ { value } }\"\nnext");
        let expected = " \"%{ \"}\" \"\"\"}\nvalue\"\"\" /* }\n*/ { value } }\"\n";

        assert_eq!(result.body, (0..expected.len(), expected));
        assert_eq!(result.remainder, "next");
        assert_eq!(result.lexical_mode, None);
    }

    #[test]
    fn rule_literals_suspend_outer_layout_until_the_closing_quote() {
        let simple = scan(" ~\"users/{id}\"\nnext");
        let capture = scan(" ~\"{id = ident}\"\nnext");
        let lazy_capture = scan(" ~\":name {rest = ..}\"\nnext");
        let grouped = scan(" ~\"{ (id [key]) }\"\nnext");
        let multiline = scan(" ~\"users/\n{id}\nend\"\nnext");

        for (result, expected) in [
            (simple, " ~\"users/{id}\"\n"),
            (capture, " ~\"{id = ident}\"\n"),
            (lazy_capture, " ~\":name {rest = ..}\"\n"),
            (grouped, " ~\"{ (id [key]) }\"\n"),
            (multiline, " ~\"users/\n{id}\nend\"\n"),
        ] {
            assert_eq!(result.body, (0..expected.len(), expected));
            assert_eq!(result.remainder, "next");
            assert_eq!(result.lexical_mode, None);
        }
    }

    #[test]
    fn rule_literal_interpolation_reuses_string_and_comment_regions() {
        let result = scan(" ~\"{ id = \"}\" /* } */ }\"\nnext");
        let expected = " ~\"{ id = \"}\" /* } */ }\"\n";

        assert_eq!(result.body, (0..expected.len(), expected));
        assert_eq!(result.remainder, "next");
        assert_eq!(result.lexical_mode, None);
    }

    #[test]
    fn rule_literal_backslash_does_not_escape_its_terminator() {
        let result = scan(" ~\"before\\\" suffix\nnext");
        let expected = " ~\"before\\\" suffix\n";

        assert_eq!(result.body, (0..expected.len(), expected));
        assert_eq!(result.remainder, "next");
        assert_eq!(result.lexical_mode, None);
    }

    #[test]
    fn quoted_yumark_literals_suspend_outer_layout_until_their_outer_delimiter() {
        let inline = scan(" '[hello world]\nnext");
        let block = scan(" '{# Title\n}\nnext");
        let nested = scan(" '{# Title\n[inline {command}]\n}\nnext");
        let quoted = scan(" '{> quoted { braces }\n}\nnext");

        for (result, expected) in [
            (inline, " '[hello world]\n"),
            (block, " '{# Title\n}\n"),
            (nested, " '{# Title\n[inline {command}]\n}\n"),
            (quoted, " '{> quoted { braces }\n}\n"),
        ] {
            assert_eq!(result.body, (0..expected.len(), expected));
            assert_eq!(result.remainder, "next");
            assert_eq!(result.lexical_mode, None);
        }
    }

    #[test]
    fn apostrophe_without_a_yumark_opener_remains_ordinary_source() {
        let result = scan(" 'not-a-yumark [text]\nnext");
        let expected = " 'not-a-yumark [text]\n";

        assert_eq!(result.body, (0..expected.len(), expected));
        assert_eq!(result.remainder, "next");
        assert_eq!(result.lexical_mode, None);
    }

    #[test]
    fn raw_yumark_fence_ignores_braces_and_mid_line_fence_text() {
        let result = scan(" '{```text\n}\n{ raw }\nbody ``` remains text\n```\n}\nnext");
        let expected = " '{```text\n}\n{ raw }\nbody ``` remains text\n```\n}\n";

        assert_eq!(result.body, (0..expected.len(), expected));
        assert_eq!(result.remainder, "next");
        assert_eq!(result.lexical_mode, None);
    }

    #[test]
    fn yulang_yumark_fence_reuses_nested_lexical_regions() {
        let result = scan(
            " '{```yulang\nmy data = \"%{ { value } }\"\n~\"users/{id}\"\n'[inline]\n// ``` remains comment text\nbody ``` remains mid-line text\n```\n}\nnext",
        );
        let expected = " '{```yulang\nmy data = \"%{ { value } }\"\n~\"users/{id}\"\n'[inline]\n// ``` remains comment text\nbody ``` remains mid-line text\n```\n}\n";

        assert_eq!(result.body, (0..expected.len(), expected));
        assert_eq!(result.remainder, "next");
        assert_eq!(result.lexical_mode, None);
    }

    #[test]
    fn raw_fence_accepts_indented_and_blockquote_continuation_lines() {
        let indented = scan(" '{\n  ```raw\n  }\n  ```\n}\nnext");
        let quoted = scan(" '{> ```rust\n> }\n> ```\n}\nnext");

        for (result, expected) in [
            (indented, " '{\n  ```raw\n  }\n  ```\n}\n"),
            (quoted, " '{> ```rust\n> }\n> ```\n}\n"),
        ] {
            assert_eq!(result.body, (0..expected.len(), expected));
            assert_eq!(result.remainder, "next");
            assert_eq!(result.lexical_mode, None);
        }
    }

    #[test]
    fn comment_delimiters_do_not_change_outer_depth() {
        let block = scan(" /* {[( */ value\nnext");
        let line = scan(" value // }])\nnext");
        let expected_block = " /* {[( */ value\n";
        let expected_line = " value // }])\n";

        assert_eq!(block.body, (0..expected_block.len(), expected_block));
        assert_eq!(block.remainder, "next");
        assert_eq!(line.body, (0..expected_line.len(), expected_line));
        assert_eq!(line.remainder, "next");
    }

    #[test]
    fn unterminated_strings_and_heredocs_end_at_eof() {
        let normal = scan(" \"open {");
        let heredoc = scan(" \"\"\"open\n{");
        let expected_normal = " \"open {";
        let expected_heredoc = " \"\"\"open\n{";

        assert_eq!(normal.body, (0..expected_normal.len(), expected_normal));
        assert_eq!(normal.remainder, "");
        assert_eq!(normal.lexical_mode, Some(EmbeddedLexicalMode::NormalString));
        assert_eq!(heredoc.body, (0..expected_heredoc.len(), expected_heredoc));
        assert_eq!(heredoc.remainder, "");
        assert_eq!(
            heredoc.lexical_mode,
            Some(EmbeddedLexicalMode::Heredoc { quote_count: 3 })
        );
    }

    #[test]
    fn unterminated_interpolation_keeps_its_local_depth_at_eof() {
        let result = scan(" \"%{ { open");
        let expected = " \"%{ { open";

        assert_eq!(result.body, (0..expected.len(), expected));
        assert_eq!(result.remainder, "");
        assert_eq!(
            result.lexical_mode,
            Some(EmbeddedLexicalMode::Interpolation { delimiter_depth: 2 })
        );
    }

    #[test]
    fn unterminated_rule_literal_keeps_its_lexical_mode_at_eof() {
        let result = scan(" ~\"users/{id}");
        let expected = " ~\"users/{id}";

        assert_eq!(result.body, (0..expected.len(), expected));
        assert_eq!(result.remainder, "");
        assert_eq!(result.lexical_mode, Some(EmbeddedLexicalMode::RuleLiteral));
    }

    #[test]
    fn unterminated_quoted_yumark_keeps_the_active_document_mode_at_eof() {
        let inline = scan(" '[hello");
        let quoted = scan(" '{> open");

        assert_eq!(inline.body, (0.." '[hello".len(), " '[hello"));
        assert_eq!(inline.remainder, "");
        assert_eq!(
            inline.lexical_mode,
            Some(EmbeddedLexicalMode::Yumark {
                mode: YumarkMode::Inline,
                quote_depth: 0,
                line_document_continuation: false,
            })
        );
        assert_eq!(quoted.body, (0.." '{> open".len(), " '{> open"));
        assert_eq!(quoted.remainder, "");
        assert_eq!(
            quoted.lexical_mode,
            Some(EmbeddedLexicalMode::Yumark {
                mode: YumarkMode::Quoted,
                quote_depth: 1,
                line_document_continuation: false,
            })
        );
    }

    #[test]
    fn unterminated_fences_keep_their_kind_and_continuation_state() {
        let raw = scan(" '{```text\nbody");
        let yulang = scan(" '{```yulang-extra\nmy value = 1");
        let raw_expected = " '{```text\nbody";
        let yulang_expected = " '{```yulang-extra\nmy value = 1";

        assert_eq!(raw.body, (0..raw_expected.len(), raw_expected));
        assert_eq!(raw.remainder, "");
        assert_eq!(
            raw.lexical_mode,
            Some(EmbeddedLexicalMode::Fence {
                kind: FenceKind::Raw,
                continuation: false,
            })
        );
        assert_eq!(yulang.body, (0..yulang_expected.len(), yulang_expected));
        assert_eq!(yulang.remainder, "");
        assert_eq!(
            yulang.lexical_mode,
            Some(EmbeddedLexicalMode::Fence {
                kind: FenceKind::Yulang,
                continuation: false,
            })
        );
    }

    struct ScanResult<'source> {
        body: (Range<usize>, &'source str),
        remainder: &'source str,
        lexical_mode: Option<EmbeddedLexicalMode>,
    }

    fn scan(source: &str) -> ScanResult<'_> {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: false,
            ..LineState::default()
        });
        local.push_indentation_baseline(IndentationBaseline {
            column: 0,
            kind: IndentationBaselineKind::Introducer,
        });
        local.push_delimiter(Delimiter::Brace);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut input = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let body = input
            .run(from_fn(scan_opaque_body))
            .expect("opaque body scanning is total");

        assert_eq!(input.local.delimiter(), Some(Delimiter::Brace));
        assert_eq!(
            input.local.indentation_baseline(),
            Some(IndentationBaseline {
                column: 0,
                kind: IndentationBaselineKind::Introducer,
            })
        );

        ScanResult {
            body: (body.range(), body.text()),
            remainder: input.input.remainder(),
            lexical_mode: input.local.lexical_mode(),
        }
    }
}
