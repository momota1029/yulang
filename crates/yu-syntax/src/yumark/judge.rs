//! Sink-free source judges from doc-comment addendum §§2–4.
//!
//! These isolated Gate 2 judges return source ranges and structural facts only.
//! They emit no Rowan events or diagnostics and have no production dispatch.

use std::ops::Range;

use unicode_ident::is_xid_start;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum StatementPosition {
    CanonicalLineStart,
    CanonicalSameLine,
    NonStatement,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DocumentMarkerKind {
    Line,
    BlockOpen,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DocumentMarker {
    pub(crate) kind: DocumentMarkerKind,
    /// The complete and only committed marker bytes.
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LineDocumentExtent {
    pub(crate) prefix: Range<usize>,
    pub(crate) body: Range<usize>,
    /// The first unowned physical-newline byte or EOF position.
    pub(crate) end: Range<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct BlockCloseContext {
    pub(crate) after_opening_line: bool,
    pub(crate) at_physical_line_start: bool,
    pub(crate) indent_col: usize,
    pub(crate) base_col: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum BlockCloseDecision {
    /// The marker is the sole committed range; horizontal suffix/newline stay
    /// with the outer statement sequence.
    Close(Range<usize>),
    Text,
    MissingDocCommentClosingDelimiter {
        range: Range<usize>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ChunkContext {
    pub(crate) at_line_start: bool,
    pub(crate) indent_col: usize,
    pub(crate) base_col: usize,
    pub(crate) active_close: Option<ActiveClose>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ActiveClose {
    BlockDocument { after_opening_line: bool },
    RawFence,
    ExplicitQuote { depth: usize },
    Inline(InlineClose),
    BracedBody,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum InlineClose {
    RightBracket,
    Emphasis,
    Strong,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TerminatorKind {
    BlockDocument,
    RawFence,
    ExplicitQuote,
    Inline(InlineClose),
    BracedBody,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ChunkKind {
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
pub(crate) struct Chunk {
    pub(crate) kind: ChunkKind,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct QuoteMarkerFacts {
    depth: usize,
    marker_len: usize,
    explicit: bool,
}

/// Judges the doc-comment marker at one canonical Statement candidate.
///
/// The block spelling is tested first. Once three leading hyphens are seen, a
/// failed strict block opener never falls back to a two-byte line marker.
pub(crate) fn judge_document_marker(
    source: &str,
    origin: usize,
    position: StatementPosition,
) -> Option<DocumentMarker> {
    if position == StatementPosition::NonStatement {
        return None;
    }
    if let Some(suffix) = source.strip_prefix("---") {
        return (position == StatementPosition::CanonicalLineStart
            && strict_horizontal_suffix(suffix, false))
        .then(|| DocumentMarker {
            kind: DocumentMarkerKind::BlockOpen,
            range: origin..origin + 3,
        });
    }
    source.starts_with("--").then(|| DocumentMarker {
        kind: DocumentMarkerKind::Line,
        range: origin..origin + 2,
    })
}

/// Judges the complete line-document extent without owning its newline.
pub(crate) fn judge_line_document(source: &str, origin: usize) -> Option<LineDocumentExtent> {
    let marker = judge_document_marker(source, origin, StatementPosition::CanonicalLineStart)?;
    if marker.kind != DocumentMarkerKind::Line {
        return None;
    }

    let body_source = &source[2..];
    let body_length = physical_newline_offset(body_source).unwrap_or(body_source.len());
    let body_start = origin + 2;
    let body_end = body_start + body_length;
    Some(LineDocumentExtent {
        prefix: marker.range,
        body: body_start..body_end,
        end: body_end..body_end,
    })
}

/// Judges one active block-document close or its EOF recovery.
pub(crate) fn judge_block_close(
    source: &str,
    origin: usize,
    context: BlockCloseContext,
) -> BlockCloseDecision {
    if source.is_empty() && context.after_opening_line {
        return BlockCloseDecision::MissingDocCommentClosingDelimiter {
            range: origin..origin,
        };
    }
    let accepted = context.after_opening_line
        && context.at_physical_line_start
        && context.indent_col == context.base_col
        && source
            .strip_prefix("---")
            .is_some_and(|suffix| strict_horizontal_suffix(suffix, true));
    if accepted {
        BlockCloseDecision::Close(origin..origin + 3)
    } else {
        BlockCloseDecision::Text
    }
}

/// Returns the next maximal structural chunk in the authoritative precedence
/// order. The returned range is the only proposed commit.
pub(crate) fn judge_chunk(source: &str, origin: usize, context: ChunkContext) -> Chunk {
    if let Some((kind, length)) = active_terminator(source, context) {
        return chunk(origin, length, ChunkKind::Terminator(kind));
    }
    if source.is_empty() {
        return chunk(origin, 0, ChunkKind::Eof);
    }

    if context.at_line_start
        && let Some(length) = blank_line_length(source)
    {
        return chunk(origin, length, ChunkKind::BlankLine);
    }
    if let Some(length) = physical_newline_length(source) {
        return chunk(origin, length, ChunkKind::Newline);
    }

    if context.at_line_start
        && let Some((kind, length)) = line_structure(source, context)
    {
        return chunk(origin, length, kind);
    }

    for (spelling, kind) in [
        ("![", ChunkKind::Image),
        ("**", ChunkKind::Strong),
        ("[", ChunkKind::InlineGroup),
        ("*", ChunkKind::Emphasis),
    ] {
        if source.starts_with(spelling) {
            return chunk(origin, spelling.len(), kind);
        }
    }
    if source.starts_with('\\') && source[1..].chars().next().is_some_and(is_identifier_start) {
        return chunk(origin, 1, ChunkKind::Backslash);
    }

    chunk(
        origin,
        raw_text_length(source, context.active_close),
        ChunkKind::RawText,
    )
}

fn chunk(origin: usize, length: usize, kind: ChunkKind) -> Chunk {
    Chunk {
        kind,
        range: origin..origin + length,
    }
}

fn active_terminator(source: &str, context: ChunkContext) -> Option<(TerminatorKind, usize)> {
    match context.active_close? {
        ActiveClose::BlockDocument { after_opening_line }
            if after_opening_line
                && context.at_line_start
                && context.indent_col == context.base_col
                && source
                    .strip_prefix("---")
                    .is_some_and(|suffix| strict_horizontal_suffix(suffix, true)) =>
        {
            Some((TerminatorKind::BlockDocument, 3))
        }
        ActiveClose::RawFence
            if context.at_line_start
                && context.indent_col == context.base_col
                && source
                    .strip_prefix("```")
                    .is_some_and(|suffix| strict_horizontal_suffix(suffix, true)) =>
        {
            Some((TerminatorKind::RawFence, 3))
        }
        ActiveClose::ExplicitQuote { depth }
            if context.at_line_start
                && quote_marker_facts(source, context.indent_col, context.base_col)
                    .is_some_and(|facts| facts.explicit && facts.depth == depth) =>
        {
            Some((TerminatorKind::ExplicitQuote, depth))
        }
        ActiveClose::Inline(InlineClose::RightBracket) if source.starts_with(']') => {
            Some((TerminatorKind::Inline(InlineClose::RightBracket), 1))
        }
        ActiveClose::Inline(InlineClose::Emphasis) if source.starts_with('*') => {
            Some((TerminatorKind::Inline(InlineClose::Emphasis), 1))
        }
        ActiveClose::Inline(InlineClose::Strong) if source.starts_with("**") => {
            Some((TerminatorKind::Inline(InlineClose::Strong), 2))
        }
        ActiveClose::BracedBody if source.starts_with('}') => Some((TerminatorKind::BracedBody, 1)),
        _ => None,
    }
}

fn line_structure(source: &str, context: ChunkContext) -> Option<(ChunkKind, usize)> {
    if source.starts_with('#') {
        let level = source.bytes().take_while(|byte| *byte == b'#').count();
        let suffix = &source[level..];
        if suffix.starts_with('.') {
            return Some((ChunkKind::SectionClose { level }, level + 1));
        }
        if suffix.starts_with(' ') {
            return Some((ChunkKind::Heading { level }, level));
        }
    }

    let digits = source
        .bytes()
        .take_while(|byte| byte.is_ascii_digit())
        .count();
    if digits > 0 && source[digits..].starts_with(". ") {
        return Some((ChunkKind::OrderedList, digits + 2));
    }
    if source.starts_with("- ") {
        return Some((ChunkKind::UnorderedList, 2));
    }
    if source
        .strip_prefix("```")
        .is_some_and(raw_fence_opener_suffix)
    {
        return Some((ChunkKind::RawFence, 3));
    }
    if let Some(facts) = quote_marker_facts(source, context.indent_col, context.base_col) {
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

fn quote_marker_facts(
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
            explicit: true,
        });
    }
    let (depth, marker_len) = prefix_quote_marker(source);
    Some(QuoteMarkerFacts {
        depth,
        marker_len,
        explicit: false,
    })
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

fn physical_newline_offset(source: &str) -> Option<usize> {
    source.char_indices().find_map(|(index, character)| {
        (character == '\n').then_some(index.saturating_sub(usize::from(
            index > 0 && source.as_bytes()[index - 1] == b'\r',
        )))
    })
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

fn prefix_quote_marker(source: &str) -> (usize, usize) {
    let bytes = source.as_bytes();
    let mut index = 0;
    let mut marker_end = 0;
    let mut depth = 0;
    while bytes.get(index) == Some(&b'>') {
        index += 1;
        depth += 1;
        marker_end = index;
        while matches!(bytes.get(index), Some(b' ' | b'\t')) {
            index += 1;
        }
    }
    (depth, index.max(marker_end))
}

fn raw_text_length(source: &str, active_close: Option<ActiveClose>) -> usize {
    let first = source
        .chars()
        .next()
        .expect("raw text is selected only for nonempty source");
    let mut length = first.len_utf8();
    while length < source.len() && !inline_boundary(&source[length..], active_close) {
        length += source[length..]
            .chars()
            .next()
            .expect("a nonempty source remainder has a next character")
            .len_utf8();
    }
    length
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
            Some(ActiveClose::Inline(InlineClose::RightBracket))
        ) && source.starts_with(']')
}

fn is_identifier_start(character: char) -> bool {
    character == '_' || is_xid_start(character)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::yumark::frame::{EnvelopeStop, YumarkFrame, YumarkFrameStack};

    #[test]
    fn marker_judge_is_longest_first_strict_and_state_neutral() {
        let mut frames = YumarkFrameStack::new();
        frames.push(YumarkFrame::Document {
            base: 0,
            envelope_stop: EnvelopeStop::ParentFrame,
        });
        let before = frames.full_state_snapshot();

        for (source, position, expected) in [
            (
                "---\nnext",
                StatementPosition::CanonicalLineStart,
                Some(DocumentMarker {
                    kind: DocumentMarkerKind::BlockOpen,
                    range: 7..10,
                }),
            ),
            (
                "--- \t\r\nnext",
                StatementPosition::CanonicalLineStart,
                Some(DocumentMarker {
                    kind: DocumentMarkerKind::BlockOpen,
                    range: 7..10,
                }),
            ),
            (
                "--text",
                StatementPosition::CanonicalLineStart,
                Some(DocumentMarker {
                    kind: DocumentMarkerKind::Line,
                    range: 7..9,
                }),
            ),
            ("---", StatementPosition::CanonicalLineStart, None),
            ("----\n", StatementPosition::CanonicalLineStart, None),
            ("---x\n", StatementPosition::CanonicalLineStart, None),
            (" ---\n", StatementPosition::CanonicalLineStart, None),
            ("---\r", StatementPosition::CanonicalLineStart, None),
            ("---\n", StatementPosition::CanonicalSameLine, None),
            (
                "--text",
                StatementPosition::CanonicalSameLine,
                Some(DocumentMarker {
                    kind: DocumentMarkerKind::Line,
                    range: 7..9,
                }),
            ),
            ("--text", StatementPosition::NonStatement, None),
        ] {
            assert_eq!(
                judge_document_marker(source, 7, position),
                expected,
                "{source:?}"
            );
            assert_eq!(frames.full_state_snapshot(), before);
        }
    }

    #[test]
    fn line_document_owns_marker_and_content_but_not_physical_newline() {
        for (source, expected) in [
            (
                "--",
                Some(LineDocumentExtent {
                    prefix: 11..13,
                    body: 13..13,
                    end: 13..13,
                }),
            ),
            (
                "--body\n--next",
                Some(LineDocumentExtent {
                    prefix: 11..13,
                    body: 13..17,
                    end: 17..17,
                }),
            ),
            (
                "--a\rb\r\n--next",
                Some(LineDocumentExtent {
                    prefix: 11..13,
                    body: 13..16,
                    end: 16..16,
                }),
            ),
            (
                "--\ttext\r\n",
                Some(LineDocumentExtent {
                    prefix: 11..13,
                    body: 13..18,
                    end: 18..18,
                }),
            ),
            ("---\n", None),
            ("---x", None),
        ] {
            assert_eq!(judge_line_document(source, 11), expected, "{source:?}");
        }

        let first = judge_line_document("--one\n--two", 0).expect("first line doc");
        assert_eq!(first.body, 2..5);
        let second = judge_line_document(&"--one\n--two"[6..], 6).expect("second line doc");
        assert_eq!(second.prefix, 6..8);
        assert_eq!(second.body, 8..11);
    }

    #[test]
    fn strict_block_close_table_commits_only_marker_or_one_eof_missing() {
        let context =
            |after_opening_line, at_physical_line_start, indent_col, base_col| BlockCloseContext {
                after_opening_line,
                at_physical_line_start,
                indent_col,
                base_col,
            };
        for (source, facts, expected) in [
            (
                "---\nnext",
                context(true, true, 2, 2),
                BlockCloseDecision::Close(20..23),
            ),
            (
                "--- \t\r\nnext",
                context(true, true, 2, 2),
                BlockCloseDecision::Close(20..23),
            ),
            (
                "---",
                context(true, true, 2, 2),
                BlockCloseDecision::Close(20..23),
            ),
            (
                "",
                context(true, true, 2, 2),
                BlockCloseDecision::MissingDocCommentClosingDelimiter { range: 20..20 },
            ),
            ("---", context(false, true, 2, 2), BlockCloseDecision::Text),
            ("---", context(true, false, 2, 2), BlockCloseDecision::Text),
            ("---", context(true, true, 3, 2), BlockCloseDecision::Text),
            ("---", context(true, true, 1, 2), BlockCloseDecision::Text),
            ("---x", context(true, true, 2, 2), BlockCloseDecision::Text),
            ("----", context(true, true, 2, 2), BlockCloseDecision::Text),
            ("--- x", context(true, true, 2, 2), BlockCloseDecision::Text),
            ("---\r", context(true, true, 2, 2), BlockCloseDecision::Text),
            (
                " ---\n",
                context(true, true, 2, 2),
                BlockCloseDecision::Text,
            ),
        ] {
            assert_eq!(judge_block_close(source, 20, facts), expected, "{source:?}");
        }
    }

    fn context(at_line_start: bool) -> ChunkContext {
        ChunkContext {
            at_line_start,
            indent_col: 0,
            base_col: 0,
            active_close: None,
        }
    }

    #[test]
    fn chunk_judge_uses_authoritative_longest_first_order() {
        for (source, facts, kind, length) in [
            ("", context(true), ChunkKind::Eof, 0),
            (" \t\r\nx", context(true), ChunkKind::BlankLine, 4),
            ("\r\nx", context(false), ChunkKind::Newline, 2),
            (
                "###.tail",
                context(true),
                ChunkKind::SectionClose { level: 3 },
                4,
            ),
            (
                "## title",
                context(true),
                ChunkKind::Heading { level: 2 },
                2,
            ),
            ("##\ttitle", context(true), ChunkKind::RawText, 8),
            ("12. item", context(true), ChunkKind::OrderedList, 4),
            ("- item", context(true), ChunkKind::UnorderedList, 2),
            ("1.item", context(true), ChunkKind::RawText, 6),
            ("-item", context(true), ChunkKind::RawText, 5),
            ("```raw\nbody", context(true), ChunkKind::RawFence, 3),
            ("```", context(true), ChunkKind::RawText, 3),
            (
                ">>> \nbody",
                context(true),
                ChunkKind::ExplicitQuote { depth: 3 },
                3,
            ),
            (
                ">>> text",
                context(true),
                ChunkKind::PrefixQuote { depth: 3 },
                4,
            ),
            (
                "> > text",
                context(true),
                ChunkKind::PrefixQuote { depth: 2 },
                4,
            ),
            ("![doc]", context(false), ChunkKind::Image, 2),
            ("**bold", context(false), ChunkKind::Strong, 2),
            ("[doc]", context(false), ChunkKind::InlineGroup, 1),
            ("*em", context(false), ChunkKind::Emphasis, 1),
            ("\\name", context(false), ChunkKind::Backslash, 1),
            ("\\℘name", context(false), ChunkKind::Backslash, 1),
            ("\\", context(false), ChunkKind::RawText, 1),
            ("_", context(false), ChunkKind::RawText, 1),
            ("abc_[x", context(false), ChunkKind::RawText, 4),
        ] {
            let judged = judge_chunk(source, 5, facts);
            assert_eq!(judged.kind, kind, "{source:?}");
            assert_eq!(judged.range, 5..5 + length, "{source:?}");
        }
    }

    #[test]
    fn chunk_terminators_precede_starters_and_commit_only_the_marker() {
        for (source, facts, expected, length) in [
            (
                "--- \t\r\nnext",
                ChunkContext {
                    active_close: Some(ActiveClose::BlockDocument {
                        after_opening_line: true,
                    }),
                    ..context(true)
                },
                ChunkKind::Terminator(TerminatorKind::BlockDocument),
                3,
            ),
            (
                "```\nnext",
                ChunkContext {
                    active_close: Some(ActiveClose::RawFence),
                    ..context(true)
                },
                ChunkKind::Terminator(TerminatorKind::RawFence),
                3,
            ),
            (
                ">>>\nnext",
                ChunkContext {
                    active_close: Some(ActiveClose::ExplicitQuote { depth: 3 }),
                    ..context(true)
                },
                ChunkKind::Terminator(TerminatorKind::ExplicitQuote),
                3,
            ),
            (
                "]tail",
                ChunkContext {
                    active_close: Some(ActiveClose::Inline(InlineClose::RightBracket)),
                    ..context(false)
                },
                ChunkKind::Terminator(TerminatorKind::Inline(InlineClose::RightBracket)),
                1,
            ),
            (
                "**tail",
                ChunkContext {
                    active_close: Some(ActiveClose::Inline(InlineClose::Strong)),
                    ..context(false)
                },
                ChunkKind::Terminator(TerminatorKind::Inline(InlineClose::Strong)),
                2,
            ),
            (
                "}tail",
                ChunkContext {
                    active_close: Some(ActiveClose::BracedBody),
                    ..context(false)
                },
                ChunkKind::Terminator(TerminatorKind::BracedBody),
                1,
            ),
        ] {
            let judged = judge_chunk(source, 31, facts);
            assert_eq!(judged.kind, expected, "{source:?}");
            assert_eq!(judged.range, 31..31 + length, "{source:?}");
        }

        let text = judge_chunk(
            "---x",
            0,
            ChunkContext {
                active_close: Some(ActiveClose::BlockDocument {
                    after_opening_line: true,
                }),
                ..context(true)
            },
        );
        assert_eq!(text.kind, ChunkKind::RawText);
        assert_eq!(text.range, 0..4);
    }
}
