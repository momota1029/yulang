//! Lossless typed-range scanning for whitespace, newlines, and ordinary comments.

use std::ops::Range;

use chasa::{
    ErrorSink,
    error::std::{Unexpected, UnexpectedEndOfInput},
    parser::SkipParserOnce as _,
    prelude::{any, choice, from_fn, item, many_skip, none_of, one_of, tag},
};

use crate::{
    session::{EmbeddedLexicalMode, LineState, SynIn},
};

/// The typed, contiguous source range consumed by one maximal trivia scan.
///
/// Parts borrow no source text. A caller that commits this scanner result can
/// therefore emit every trivia token directly from its source range without a
/// second lexical pass.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TriviaRun {
    range: Range<usize>,
    parts: TriviaParts,
}

impl TriviaRun {
    fn new(range: Range<usize>, parts: TriviaParts) -> Self {
        debug_assert!(parts.cover(range.clone()));
        Self { range, parts }
    }

    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn parts(&self) -> &[TriviaPart] {
        self.parts.as_slice()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.parts.is_empty()
    }

    pub(crate) fn empty_at(at: usize) -> Self {
        Self::new(at..at, TriviaParts::default())
    }
}

/// Typed parts of one maximal trivia run.
///
/// This stays local to one scanner decision. The storage representation can
/// become inline-first later without changing the range contract.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct TriviaParts(Vec<TriviaPart>);

impl TriviaParts {
    fn push(&mut self, part: TriviaPart) {
        self.0.push(part);
    }

    fn extend(&mut self, parts: impl IntoIterator<Item = TriviaPart>) {
        self.0.extend(parts);
    }

    pub(crate) fn as_slice(&self) -> &[TriviaPart] {
        &self.0
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn cover(&self, range: Range<usize>) -> bool {
        let Some(first) = self.0.first() else {
            return range.start == range.end;
        };
        if first.range.start != range.start {
            return false;
        }

        let mut end = range.start;
        for part in &self.0 {
            if part.range.start != end || part.range.start == part.range.end {
                return false;
            }
            end = part.range.end;
        }
        end == range.end
    }
}

/// One source-backed trivia token in a [`TriviaRun`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TriviaPart {
    kind: TriviaPartKind,
    range: Range<usize>,
}

impl TriviaPart {
    fn new(kind: TriviaPartKind, range: Range<usize>) -> Self {
        Self { kind, range }
    }

    pub(crate) fn kind(&self) -> &TriviaPartKind {
        &self.kind
    }

    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

/// The lexical category of one trivia part.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TriviaPartKind {
    Whitespace,
    Newline,
    LineComment,
    BlockComment { termination: CommentTermination },
}

/// Whether a block comment reached its matching closing delimiter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CommentTermination {
    Closed,
    Unterminated { remaining_depth: usize },
}

/// Consumes the maximal ordinary-trivia run at the current byte position.
///
/// Yulang's `--` and `---` document markers are declaration-level tokens in
/// the oracle grammar. Document recognition therefore stays outside this
/// shared trivia scanner; only `//` is an ordinary line comment here.
pub(crate) fn scan_trivia<E>(
    mut i: SynIn<E>,
) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let mut parts = TriviaParts::default();

    loop {
        if let Some(whitespace) = i.maybe(from_fn(scan_whitespace))? {
            parts.extend(whitespace);
            continue;
        }
        if let Some(comment) = i.maybe(from_fn(scan_line_comment))? {
            parts.push(comment);
            continue;
        }
        if let Some(comment) = i.maybe(from_fn(scan_block_comment))? {
            parts.push(comment);
            continue;
        }
        break;
    }

    Some(TriviaRun::new(start..i.pos(), parts))
}

/// Consumes exactly one ordinary comment without absorbing adjacent whitespace.
///
/// Layout scanners that need to stop immediately before an outer newline use
/// this narrower entrypoint.  It deliberately keeps comment recognition in
/// the same lexical authority as [`scan_trivia`].
pub(crate) fn scan_comment<E>(i: SynIn<E>) -> Option<TriviaPart>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().starts_with("//") {
        scan_line_comment(i)
    } else if i.input.remainder().starts_with("/*") {
        scan_block_comment(i)
    } else {
        None
    }
}

fn scan_whitespace<E>(
    mut i: SynIn<E>,
) -> Option<Vec<TriviaPart>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut consumed = false;
    let mut parts = Vec::new();
    let mut whitespace_start = None;

    loop {
        let start = i.pos();
        let unit = choice((
            one_of(" \t").to(WhitespaceUnit::Horizontal),
            choice((tag("\r\n"), tag("\r"), tag("\n"))).to(WhitespaceUnit::Newline),
        ));
        let Some(unit) = i.maybe(unit)? else {
            break;
        };
        let end = i.pos();

        let mut line = i.local.line();
        if !consumed && line.at_line_start {
            // The oracle derives indentation from the final whitespace part
            // after the most recent newline, so a comment-separated part
            // replaces rather than extends the previous indentation part.
            line.line_indent = 0;
        }
        match unit {
            WhitespaceUnit::Horizontal if line.at_line_start => {
                line.line_indent += 1;
            }
            WhitespaceUnit::Horizontal => {}
            WhitespaceUnit::Newline => {
                line = LineState {
                    last_newline: Some((start, end)),
                    line_start: end,
                    line_indent: 0,
                    at_line_start: true,
                };
            }
        }
        i.local.set_line(line);

        match unit {
            WhitespaceUnit::Horizontal => {
                whitespace_start.get_or_insert(start);
            }
            WhitespaceUnit::Newline => {
                if let Some(whitespace_start) = whitespace_start.take() {
                    parts.push(TriviaPart::new(
                        TriviaPartKind::Whitespace,
                        whitespace_start..start,
                    ));
                }
                parts.push(TriviaPart::new(TriviaPartKind::Newline, start..end));
            }
        }
        consumed = true;
    }

    if let Some(whitespace_start) = whitespace_start {
        parts.push(TriviaPart::new(
            TriviaPartKind::Whitespace,
            whitespace_start..i.pos(),
        ));
    }

    consumed.then_some(parts)
}

fn scan_line_comment<E>(
    mut i: SynIn<E>,
) -> Option<TriviaPart>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = i.pos();
    i.skip(tag("//"))?;
    i
        .local
        .push_lexical_mode(EmbeddedLexicalMode::LineComment);
    i.skip(many_skip(none_of("\r\n")))?;
    debug_assert_eq!(
        i.local.pop_lexical_mode(),
        Some(EmbeddedLexicalMode::LineComment)
    );
    Some(TriviaPart::new(
        TriviaPartKind::LineComment,
        start..i.pos(),
    ))
}

fn scan_block_comment<E>(
    mut i: SynIn<E>,
) -> Option<TriviaPart>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    i.skip(tag("/*"))?;
    i
        .local
        .push_lexical_mode(EmbeddedLexicalMode::BlockComment { depth: 1 });

    loop {
        let comment_unit = choice((
            from_fn(scan_block_slash),
            from_fn(scan_block_star),
            from_fn(scan_whitespace).to(BlockCommentUnit::Whitespace),
            any.to(BlockCommentUnit::Text),
        ));
        let Some(unit) = i.maybe(comment_unit)? else {
            // The oracle accepts an unterminated block comment at EOF and
            // synthesizes its closing trivia token. Keep the lexical frame so
            // callers can still observe that the source ended in this mode.
            let Some(EmbeddedLexicalMode::BlockComment { depth }) = i.local.lexical_mode()
            else {
                unreachable!("block-comment scanner owns the top lexical frame");
            };
            return Some(TriviaPart::new(
                TriviaPartKind::BlockComment {
                    termination: CommentTermination::Unterminated {
                        remaining_depth: depth,
                    },
                },
                start..i.pos(),
            ));
        };

        match unit {
            BlockCommentUnit::Open => {
                let Some(EmbeddedLexicalMode::BlockComment { depth }) = i.local.lexical_mode()
                else {
                    unreachable!("block-comment scanner owns the top lexical frame");
                };
                i
                    .local
                    .replace_lexical_mode(EmbeddedLexicalMode::BlockComment { depth: depth + 1 });
            }
            BlockCommentUnit::Close => {
                let Some(EmbeddedLexicalMode::BlockComment { depth }) = i.local.lexical_mode()
                else {
                    unreachable!("block-comment scanner owns the top lexical frame");
                };
                if depth == 1 {
                    debug_assert_eq!(
                        i.local.pop_lexical_mode(),
                        Some(EmbeddedLexicalMode::BlockComment { depth: 1 })
                    );
                    return Some(TriviaPart::new(
                        TriviaPartKind::BlockComment {
                            termination: CommentTermination::Closed,
                        },
                        start..i.pos(),
                    ));
                }
                i
                    .local
                    .replace_lexical_mode(EmbeddedLexicalMode::BlockComment { depth: depth - 1 });
            }
            BlockCommentUnit::Whitespace | BlockCommentUnit::Text => {}
        }
    }
}

fn scan_block_slash<E>(
    mut i: SynIn<E>,
) -> Option<BlockCommentUnit>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    i.skip(item('/'))?;
    // Match the oracle's overlap rule: in `/*/`, the immediately overlapping
    // `*/` prevents the same bytes from opening a nested comment.
    i.skip(many_skip(tag("*/")))?;
    Some(
        i
            .maybe(item('*'))?
            .map_or(BlockCommentUnit::Text, |_| BlockCommentUnit::Open),
    )
}

fn scan_block_star<E>(
    mut i: SynIn<E>,
) -> Option<BlockCommentUnit>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    i.skip(item('*'))?;
    // Symmetrically skip an immediately overlapping `/*` before deciding
    // whether the final slash closes the current depth.
    i.skip(many_skip(tag("/*")))?;
    Some(
        i
            .maybe(item('/'))?
            .map_or(BlockCommentUnit::Text, |_| BlockCommentUnit::Close),
    )
}

#[derive(Clone, Copy)]
enum WhitespaceUnit {
    Horizontal,
    Newline,
}

#[derive(Clone, Copy)]
enum BlockCommentUnit {
    Open,
    Close,
    Whitespace,
    Text,
}

#[cfg(test)]
mod tests {
    use super::*;
    use chasa::{input::IsCut, prelude::{In, from_fn_once, item}};

    use crate::{input::SourceInput, session::ParseLocal};

    #[test]
    fn typed_parts_are_contiguous_and_cover_the_maximal_run() {
        let source = " \t\r\n// comment\n/* outer /* inner */ */name";
        let trivia_end = source.find("name").expect("test suffix must exist");
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let run = i
            .run(scan_trivia)
            .expect("trivia scanning is total");

        assert_eq!(run.range(), 0..trivia_end);
        assert_eq!(
            run.parts(),
            [
                TriviaPart::new(TriviaPartKind::Whitespace, 0..2),
                TriviaPart::new(TriviaPartKind::Newline, 2..4),
                TriviaPart::new(TriviaPartKind::LineComment, 4..14),
                TriviaPart::new(TriviaPartKind::Newline, 14..15),
                TriviaPart::new(
                    TriviaPartKind::BlockComment {
                        termination: CommentTermination::Closed,
                    },
                    15..trivia_end,
                ),
            ]
        );

        let mut end = run.range().start;
        for part in run.parts() {
            let range = part.range();
            assert_eq!(range.start, end);
            assert!(range.start < range.end);
            end = range.end;
        }
        assert_eq!(end, run.range().end);
    }

    #[test]
    fn empty_run_has_an_empty_range_and_no_parts() {
        let mut source_input = SourceInput::new("name");
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let run = i
            .run(scan_trivia)
            .expect("trivia scanning is total");

        assert_eq!(run.range(), 0..0);
        assert!(run.parts().is_empty());
        assert!(run.is_empty());
    }

    #[test]
    fn unterminated_nested_block_comment_records_its_remaining_depth() {
        let source = "/* outer /* nested";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let run = i
            .run(scan_trivia)
            .expect("trivia scanning is total");

        assert_eq!(run.range(), 0..source.len());
        assert_eq!(
            run.parts(),
            [TriviaPart::new(
                TriviaPartKind::BlockComment {
                    termination: CommentTermination::Unterminated { remaining_depth: 2 },
                },
                0..source.len(),
            )]
        );
        assert_eq!(
            i.local.lexical_mode(),
            Some(EmbeddedLexicalMode::BlockComment { depth: 2 })
        );
    }

    #[test]
    fn whitespace_and_newlines_update_physical_line_state() {
        let source = " \t\r\n  \n\t\tname";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let span = i
            .run(scan_trivia)
            .expect("trivia scanning is total");

        assert_eq!(span.range(), 0..9);
        assert_eq!(i.pos(), 9);
        assert_eq!(i.input.remainder(), "name");
        assert_eq!(
            i.local.line(),
            LineState {
                last_newline: Some((6, 7)),
                line_start: 7,
                line_indent: 2,
                at_line_start: true,
            }
        );

        let mut source_input = SourceInput::new(" \r\tname");
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let span = i
            .run(scan_trivia)
            .expect("trivia scanning is total");

        assert_eq!(span.range(), 0..3);
        assert_eq!(
            i.local.line(),
            LineState {
                last_newline: Some((1, 2)),
                line_start: 2,
                line_indent: 1,
                at_line_start: true,
            }
        );
    }

    #[test]
    fn nested_block_comment_balances_its_lexical_mode_depth() {
        let source = "/* outer /* inner */ outer */next";
        let trivia_end = source.find("next").expect("test suffix must exist");
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let span = i
            .run(scan_trivia)
            .expect("trivia scanning is total");

        assert_eq!(span.range(), 0..trivia_end);
        assert_eq!(i.input.remainder(), "next");
        assert_eq!(i.local.lexical_mode(), None);
    }

    #[test]
    fn line_comment_ends_before_newline_and_following_content() {
        let source = "// comment\r\n  next";
        let trivia_end = source.find("next").expect("test suffix must exist");
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let span = i
            .run(scan_trivia)
            .expect("trivia scanning is total");

        assert_eq!(span.range(), 0..trivia_end);
        assert_eq!(i.input.remainder(), "next");
        assert_eq!(i.local.lexical_mode(), None);
        assert_eq!(
            i.local.line(),
            LineState {
                last_newline: Some((10, 12)),
                line_start: 12,
                line_indent: 2,
                at_line_start: true,
            }
        );
    }

    #[test]
    fn document_markers_are_not_ordinary_trivia() {
        let mut source_input = SourceInput::new("-- document");
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let span = i
            .run(scan_trivia)
            .expect("trivia scanning is total");

        assert!(span.is_empty());
        assert_eq!(i.pos(), 0);
        assert_eq!(i.input.remainder(), "-- document");
    }

    #[test]
    fn failed_probe_rolls_back_input_line_and_unclosed_comment_mode_together() {
        let mut source_input = SourceInput::new("\n  /* outer /* nested");
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            last_newline: Some((20, 21)),
            line_start: 21,
            line_indent: 4,
            at_line_start: false,
        });
        let original_line = local.line();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let result = i
            .maybe(from_fn_once(|mut probe| {
                let span = probe.run(scan_trivia)?;
                assert_eq!(span.range(), 0..21);
                assert_eq!(
                    probe.local.lexical_mode(),
                    Some(EmbeddedLexicalMode::BlockComment { depth: 2 })
                );
                assert_eq!(probe.local.line().last_newline, Some((0, 1)));
                probe.skip(item('!'))
            }))
            .expect("the probe failure is uncut");

        assert_eq!(result, None);
        assert_eq!(i.pos(), 0);
        assert_eq!(i.input.remainder(), "\n  /* outer /* nested");
        assert_eq!(i.local.line(), original_line);
        assert_eq!(i.local.lexical_mode(), None);
    }
}
