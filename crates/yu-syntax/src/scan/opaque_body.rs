//! Header-mode scanning for operator bodies that are not expression-parsed.
//!
//! This first slice makes comments, normal strings, and heredocs opaque to the
//! outer delimiter/layout scan. Interpolation, rule literals, quoted/block
//! Yumark, and raw/Yulang fences still need their own lexical-region handling
//! before this scanner can cover the complete language.

use std::ops::Range;

use chasa::{
    ErrorSink,
    error::std::{Unexpected, UnexpectedEndOfInput},
    parser::SkipParserOnce as _,
    prelude::{In, any, from_fn, item},
};

use crate::{
    input::SourceInput,
    session::{EmbeddedLexicalMode, ParseLocal},
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
