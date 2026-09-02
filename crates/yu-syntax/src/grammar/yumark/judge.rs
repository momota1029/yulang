//! Sink-free source judges shared by the later Yumark grammar gates.

use std::ops::Range;

use chasa::{Back, ErrorSink, Input};
use unicode_ident::is_xid_start;

use crate::session::{SynIn, YumarkInlineClose};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DocumentMarkerKind {
    Line,
    BlockOpen,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DocumentMarker {
    pub(super) kind: DocumentMarkerKind,
    pub(super) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LineDocumentExtent {
    pub(super) prefix: Range<usize>,
    pub(super) body: Range<usize>,
    pub(super) end: Range<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ChunkContext {
    pub(super) at_line_start: bool,
    pub(super) indent_col: usize,
    pub(super) base_col: usize,
    pub(super) active_close: Option<ActiveClose>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ActiveClose {
    BlockDocument { after_opening_line: bool },
    RawFence,
    ExplicitQuote { depth: usize },
    Inline(YumarkInlineClose),
    BracedBody,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TerminatorKind {
    BlockDocument,
    RawFence,
    ExplicitQuote,
    Inline(YumarkInlineClose),
    BracedBody,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ChunkKind {
    Terminator(TerminatorKind),
    Eof,
    BlankLine,
    Newline,
    SectionClose { level: usize },
    Heading { level: usize },
    OrderedList,
    UnorderedList,
    RawFence,
    ExplicitQuote { depth: usize },
    PrefixQuote { depth: usize },
    Image,
    Strong,
    Backslash,
    InlineGroup,
    Emphasis,
    RawText,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Chunk {
    pub(super) kind: ChunkKind,
    pub(super) range: Range<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct QuoteMarkerFacts {
    pub(super) depth: usize,
    pub(super) marker_len: usize,
    pub(super) marker_end: usize,
    pub(super) explicit: bool,
}

pub(super) fn quote_marker_facts(
    source: &str,
    indent_col: usize,
    base_col: usize,
) -> Option<QuoteMarkerFacts> {
    let contiguous = source.bytes().take_while(|byte| *byte == b'>').count();
    if contiguous == 0 {
        return None;
    }
    if contiguous >= 3
        && indent_col == base_col
        && strict_horizontal_suffix(&source[contiguous..], true)
    {
        return Some(QuoteMarkerFacts {
            depth: contiguous,
            marker_len: contiguous,
            marker_end: contiguous,
            explicit: true,
        });
    }
    let (depth, marker_len, marker_end) = prefix_quote_marker(source);
    Some(QuoteMarkerFacts {
        depth,
        marker_len,
        marker_end,
        explicit: false,
    })
}

pub(super) fn judge_document_marker<E>(
    i: &mut SynIn<E>,
    at_line_start: bool,
) -> Option<DocumentMarker>
where
    E: ErrorSink<usize>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let remainder = i.input.remainder();
    let result = if let Some(suffix) = remainder.strip_prefix("---") {
        if at_line_start && strict_horizontal_suffix(suffix, false) {
            Some((DocumentMarkerKind::BlockOpen, 3))
        } else {
            None
        }
    } else if remainder.starts_with("--") {
        Some((DocumentMarkerKind::Line, 2))
    } else {
        None
    };

    let Some((kind, length)) = result else {
        i.rollback(checkpoint);
        return None;
    };
    consume_ascii(i, length);
    Some(DocumentMarker {
        kind,
        range: start..start + length,
    })
}

pub(super) fn judge_line_document_extent<E>(
    i: &mut SynIn<E>,
    prefix: Range<usize>,
) -> LineDocumentExtent
where
    E: ErrorSink<usize>,
{
    debug_assert_eq!(i.pos(), prefix.end);
    let body_start = i.pos();
    while !i.input.remainder().is_empty() && physical_newline_length(i.input.remainder()).is_none()
    {
        i.input
            .next()
            .expect("a nonempty source remainder has a next character");
    }
    let body_end = i.pos();
    LineDocumentExtent {
        prefix,
        body: body_start..body_end,
        end: body_end..body_end,
    }
}

pub(super) fn judge_block_close<E>(
    i: &mut SynIn<E>,
    after_opening_line: bool,
    at_line_start: bool,
    indent_col: usize,
    base_col: usize,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let remainder = i.input.remainder();
    let accepted = after_opening_line
        && at_line_start
        && indent_col == base_col
        && remainder
            .strip_prefix("---")
            .is_some_and(|suffix| strict_horizontal_suffix(suffix, true));
    if !accepted {
        i.rollback(checkpoint);
        return None;
    }
    consume_ascii(i, 3);
    Some(start..start + 3)
}

pub(super) fn judge_chunk<E>(i: &mut SynIn<E>, context: ChunkContext) -> Chunk
where
    E: ErrorSink<usize>,
{
    let start = i.pos();
    let remainder = i.input.remainder();

    if let Some((kind, length)) = active_terminator(remainder, context) {
        consume_ascii(i, length);
        return Chunk {
            kind: ChunkKind::Terminator(kind),
            range: start..start + length,
        };
    }
    if remainder.is_empty() {
        return Chunk {
            kind: ChunkKind::Eof,
            range: start..start,
        };
    }

    if context.at_line_start {
        if let Some(length) = blank_line_length(remainder) {
            consume_ascii(i, length);
            return Chunk {
                kind: ChunkKind::BlankLine,
                range: start..start + length,
            };
        }
    }
    if let Some(length) = physical_newline_length(remainder) {
        consume_ascii(i, length);
        return Chunk {
            kind: ChunkKind::Newline,
            range: start..start + length,
        };
    }

    if context.at_line_start {
        if let Some((kind, length)) = line_structure(remainder, context) {
            consume_ascii(i, length);
            return Chunk {
                kind,
                range: start..start + length,
            };
        }
    }

    for (spelling, kind) in [
        ("![", ChunkKind::Image),
        ("**", ChunkKind::Strong),
        ("[", ChunkKind::InlineGroup),
        ("*", ChunkKind::Emphasis),
    ] {
        if remainder.starts_with(spelling) {
            consume_ascii(i, spelling.len());
            return Chunk {
                kind,
                range: start..start + spelling.len(),
            };
        }
    }
    if remainder.starts_with('\\')
        && remainder[1..]
            .chars()
            .next()
            .is_some_and(is_identifier_start)
    {
        consume_ascii(i, 1);
        return Chunk {
            kind: ChunkKind::Backslash,
            range: start..start + 1,
        };
    }

    let length = consume_raw_text(i, context.active_close);
    Chunk {
        kind: ChunkKind::RawText,
        range: start..start + length,
    }
}

fn active_terminator(remainder: &str, context: ChunkContext) -> Option<(TerminatorKind, usize)> {
    let close = context.active_close?;
    match close {
        ActiveClose::BlockDocument { after_opening_line }
            if after_opening_line
                && context.at_line_start
                && context.indent_col == context.base_col
                && remainder
                    .strip_prefix("---")
                    .is_some_and(|suffix| strict_horizontal_suffix(suffix, true)) =>
        {
            Some((TerminatorKind::BlockDocument, 3))
        }
        ActiveClose::RawFence
            if context.at_line_start
                && context.indent_col == context.base_col
                && remainder
                    .strip_prefix("```")
                    .is_some_and(|suffix| strict_horizontal_suffix(suffix, true)) =>
        {
            Some((TerminatorKind::RawFence, 3))
        }
        ActiveClose::ExplicitQuote { depth }
            if context.at_line_start
                && quote_marker_facts(remainder, context.indent_col, context.base_col)
                    .is_some_and(|facts| facts.explicit && facts.depth == depth) =>
        {
            Some((TerminatorKind::ExplicitQuote, depth))
        }
        ActiveClose::Inline(YumarkInlineClose::RightBracket) if remainder.starts_with(']') => {
            Some((TerminatorKind::Inline(YumarkInlineClose::RightBracket), 1))
        }
        ActiveClose::Inline(YumarkInlineClose::Emphasis) if remainder.starts_with('*') => {
            Some((TerminatorKind::Inline(YumarkInlineClose::Emphasis), 1))
        }
        ActiveClose::Inline(YumarkInlineClose::Strong) if remainder.starts_with("**") => {
            Some((TerminatorKind::Inline(YumarkInlineClose::Strong), 2))
        }
        ActiveClose::BracedBody if remainder.starts_with('}') => {
            Some((TerminatorKind::BracedBody, 1))
        }
        _ => None,
    }
}

fn line_structure(remainder: &str, context: ChunkContext) -> Option<(ChunkKind, usize)> {
    if remainder.starts_with('#') {
        let level = remainder.bytes().take_while(|byte| *byte == b'#').count();
        let suffix = &remainder[level..];
        if suffix.starts_with('.') {
            return Some((ChunkKind::SectionClose { level }, level + 1));
        }
        if suffix.starts_with(' ') {
            return Some((ChunkKind::Heading { level }, level));
        }
    }

    let digits = remainder
        .bytes()
        .take_while(|byte| byte.is_ascii_digit())
        .count();
    if digits > 0 && remainder[digits..].starts_with(". ") {
        return Some((ChunkKind::OrderedList, digits + 2));
    }
    if remainder.starts_with("- ") {
        return Some((ChunkKind::UnorderedList, 2));
    }
    if remainder
        .strip_prefix("```")
        .is_some_and(raw_fence_opener_suffix)
    {
        return Some((ChunkKind::RawFence, 3));
    }
    if let Some(facts) = quote_marker_facts(remainder, context.indent_col, context.base_col) {
        return Some((
            if facts.explicit {
                ChunkKind::ExplicitQuote { depth: facts.depth }
            } else {
                ChunkKind::PrefixQuote { depth: facts.depth }
            },
            facts.marker_len,
        ));
    }
    None
}

fn strict_horizontal_suffix(mut suffix: &str, eof_allowed: bool) -> bool {
    while let Some(rest) = suffix.strip_prefix([' ', '\t']) {
        suffix = rest;
    }
    suffix.starts_with("\r\n") || suffix.starts_with('\n') || (eof_allowed && suffix.is_empty())
}

fn raw_fence_opener_suffix(suffix: &str) -> bool {
    suffix.contains('\n')
}

fn physical_newline_length(source: &str) -> Option<usize> {
    if source.starts_with("\r\n") {
        Some(2)
    } else if source.starts_with('\n') {
        Some(1)
    } else {
        None
    }
}

fn blank_line_length(source: &str) -> Option<usize> {
    let horizontal = source
        .bytes()
        .take_while(|byte| matches!(byte, b' ' | b'\t'))
        .count();
    physical_newline_length(&source[horizontal..]).map(|newline| horizontal + newline)
}

fn prefix_quote_marker(source: &str) -> (usize, usize, usize) {
    let bytes = source.as_bytes();
    let mut index = 0;
    let mut last_marker_end = 0;
    let mut depth = 0;
    while index < bytes.len() {
        if bytes[index] != b'>' {
            break;
        }
        index += 1;
        depth += 1;
        last_marker_end = index;
        while matches!(bytes.get(index), Some(b' ' | b'\t')) {
            index += 1;
        }
    }
    let length = if index > last_marker_end {
        index
    } else {
        last_marker_end
    };
    (depth, length, last_marker_end)
}

fn consume_raw_text<E>(i: &mut SynIn<E>, active_close: Option<ActiveClose>) -> usize
where
    E: ErrorSink<usize>,
{
    let start = i.pos();
    i.input
        .next()
        .expect("raw text is selected only for nonempty source");
    while !i.input.remainder().is_empty() && !inline_boundary(i.input.remainder(), active_close) {
        i.input
            .next()
            .expect("a nonempty source remainder has a next character");
    }
    i.pos() - start
}

fn inline_boundary(source: &str, active_close: Option<ActiveClose>) -> bool {
    physical_newline_length(source).is_some()
        || source.starts_with("![")
        || source.starts_with("**")
        || source.starts_with('[')
        || source.starts_with('*')
        || (source.starts_with('\\') && source[1..].chars().next().is_some_and(is_identifier_start))
        || matches!(active_close, Some(ActiveClose::BracedBody)) && source.starts_with('}')
        || matches!(
            active_close,
            Some(ActiveClose::Inline(YumarkInlineClose::RightBracket))
        ) && source.starts_with(']')
}

fn is_identifier_start(character: char) -> bool {
    character == '_' || is_xid_start(character)
}

fn consume_ascii<E>(i: &mut SynIn<E>, length: usize)
where
    E: ErrorSink<usize>,
{
    for _ in 0..length {
        let character = i.input.next();
        debug_assert!(character.is_some_and(|character| character.is_ascii()));
    }
}
