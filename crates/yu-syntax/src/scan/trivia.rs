//! Lossless range scanning for whitespace, newlines, and ordinary comments.

use std::ops::Range;

use chasa::{
    ErrorSink,
    error::std::{Unexpected, UnexpectedEndOfInput},
    parser::SkipParserOnce as _,
    prelude::{In, any, choice, from_fn, item, many_skip, none_of, one_of, tag},
};

use crate::{
    input::SourceInput,
    session::{EmbeddedLexicalMode, LineState, ParseLocal},
};

/// The contiguous source range consumed by one maximal trivia scan.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TriviaSpan {
    start: usize,
    end: usize,
}

impl TriviaSpan {
    pub(crate) fn range(self) -> Range<usize> {
        self.start..self.end
    }

    pub(crate) fn is_empty(self) -> bool {
        self.start == self.end
    }
}

/// Consumes the maximal ordinary-trivia run at the current byte position.
///
/// Yulang's `--` and `---` document markers are declaration-level tokens in
/// the oracle grammar. Document recognition therefore stays outside this
/// shared trivia scanner; only `//` is an ordinary line comment here.
pub(crate) fn scan_trivia<E>(
    mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<TriviaSpan>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = input.pos();

    loop {
        let ordinary_trivia = choice((
            from_fn(scan_whitespace).to(()),
            from_fn(scan_line_comment).to(()),
            from_fn(scan_block_comment).to(()),
        ));
        if input.maybe(ordinary_trivia)?.is_none() {
            break;
        }
    }

    Some(TriviaSpan {
        start,
        end: input.pos(),
    })
}

fn scan_whitespace<E>(mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut consumed = false;

    loop {
        let start = input.pos();
        let unit = choice((
            one_of(" \t").to(WhitespaceUnit::Horizontal),
            choice((tag("\r\n"), tag("\r"), tag("\n"))).to(WhitespaceUnit::Newline),
        ));
        let Some(unit) = input.maybe(unit)? else {
            break;
        };
        let end = input.pos();

        let mut line = input.local.line();
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
        input.local.set_line(line);
        consumed = true;
    }

    consumed.then_some(())
}

fn scan_line_comment<E>(mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    input.skip(tag("//"))?;
    input
        .local
        .push_lexical_mode(EmbeddedLexicalMode::LineComment);
    input.skip(many_skip(none_of("\r\n")))?;
    debug_assert_eq!(
        input.local.pop_lexical_mode(),
        Some(EmbeddedLexicalMode::LineComment)
    );
    Some(())
}

fn scan_block_comment<E>(mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    input.skip(tag("/*"))?;
    input
        .local
        .push_lexical_mode(EmbeddedLexicalMode::BlockComment { depth: 1 });

    loop {
        let comment_unit = choice((
            from_fn(scan_block_slash),
            from_fn(scan_block_star),
            from_fn(scan_whitespace).to(BlockCommentUnit::Whitespace),
            any.to(BlockCommentUnit::Text),
        ));
        let Some(unit) = input.maybe(comment_unit)? else {
            // The oracle accepts an unterminated block comment at EOF and
            // synthesizes its closing trivia token. Keep the lexical frame so
            // callers can still observe that the source ended in this mode.
            return Some(());
        };

        match unit {
            BlockCommentUnit::Open => {
                let Some(EmbeddedLexicalMode::BlockComment { depth }) = input.local.lexical_mode()
                else {
                    unreachable!("block-comment scanner owns the top lexical frame");
                };
                input
                    .local
                    .replace_lexical_mode(EmbeddedLexicalMode::BlockComment { depth: depth + 1 });
            }
            BlockCommentUnit::Close => {
                let Some(EmbeddedLexicalMode::BlockComment { depth }) = input.local.lexical_mode()
                else {
                    unreachable!("block-comment scanner owns the top lexical frame");
                };
                if depth == 1 {
                    debug_assert_eq!(
                        input.local.pop_lexical_mode(),
                        Some(EmbeddedLexicalMode::BlockComment { depth: 1 })
                    );
                    return Some(());
                }
                input
                    .local
                    .replace_lexical_mode(EmbeddedLexicalMode::BlockComment { depth: depth - 1 });
            }
            BlockCommentUnit::Whitespace | BlockCommentUnit::Text => {}
        }
    }
}

fn scan_block_slash<E>(
    mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<BlockCommentUnit>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    input.skip(item('/'))?;
    // Match the oracle's overlap rule: in `/*/`, the immediately overlapping
    // `*/` prevents the same bytes from opening a nested comment.
    input.skip(many_skip(tag("*/")))?;
    Some(
        input
            .maybe(item('*'))?
            .map_or(BlockCommentUnit::Text, |_| BlockCommentUnit::Open),
    )
}

fn scan_block_star<E>(
    mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<BlockCommentUnit>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    input.skip(item('*'))?;
    // Symmetrically skip an immediately overlapping `/*` before deciding
    // whether the final slash closes the current depth.
    input.skip(many_skip(tag("/*")))?;
    Some(
        input
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
    use chasa::{input::IsCut, prelude::from_fn_once, prelude::item};

    #[test]
    fn whitespace_and_newlines_update_physical_line_state() {
        let source = " \t\r\n  \n\t\tname";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut input = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let span = input
            .run(from_fn(scan_trivia))
            .expect("trivia scanning is total");

        assert_eq!(span.range(), 0..9);
        assert_eq!(input.pos(), 9);
        assert_eq!(input.input.remainder(), "name");
        assert_eq!(
            input.local.line(),
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
        let mut input = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let span = input
            .run(from_fn(scan_trivia))
            .expect("trivia scanning is total");

        assert_eq!(span.range(), 0..3);
        assert_eq!(
            input.local.line(),
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
        let mut input = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let span = input
            .run(from_fn(scan_trivia))
            .expect("trivia scanning is total");

        assert_eq!(span.range(), 0..trivia_end);
        assert_eq!(input.input.remainder(), "next");
        assert_eq!(input.local.lexical_mode(), None);
    }

    #[test]
    fn line_comment_ends_before_newline_and_following_content() {
        let source = "// comment\r\n  next";
        let trivia_end = source.find("next").expect("test suffix must exist");
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut input = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let span = input
            .run(from_fn(scan_trivia))
            .expect("trivia scanning is total");

        assert_eq!(span.range(), 0..trivia_end);
        assert_eq!(input.input.remainder(), "next");
        assert_eq!(input.local.lexical_mode(), None);
        assert_eq!(
            input.local.line(),
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
        let mut input = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let span = input
            .run(from_fn(scan_trivia))
            .expect("trivia scanning is total");

        assert!(span.is_empty());
        assert_eq!(input.pos(), 0);
        assert_eq!(input.input.remainder(), "-- document");
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
        let mut input = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let result = input
            .maybe(from_fn_once(|mut probe| {
                let span = probe.run(from_fn(scan_trivia))?;
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
        assert_eq!(input.pos(), 0);
        assert_eq!(input.input.remainder(), "\n  /* outer /* nested");
        assert_eq!(input.local.line(), original_line);
        assert_eq!(input.local.lexical_mode(), None);
    }
}
