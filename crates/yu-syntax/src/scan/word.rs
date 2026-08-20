//! Lossless range scanning for identifier-shaped words.

use std::ops::Range;

use chasa::{
    ErrorSink,
    error::std::Unexpected,
    parser::SkipParserOnce as _,
    prelude::{In, many_skip, one_of},
};
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::{input::SourceInput, session::ParseLocal};

/// The source text and byte range consumed by one maximal word scan.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct WordSpan<'source> {
    text: &'source str,
    start: usize,
    end: usize,
}

impl<'source> WordSpan<'source> {
    pub(crate) fn text(self) -> &'source str {
        self.text
    }

    pub(crate) fn range(self) -> Range<usize> {
        self.start..self.end
    }
}

/// Consumes one maximal identifier-shaped word at the current byte position.
///
/// Keyword interpretation is deliberately absent: the oracle classifies the
/// same spelling differently by grammar position and active stop set.
pub(crate) fn scan_word<'source, E>(
    mut input: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = input.pos();
    input.maybe(one_of(is_word_start))??;
    input.skip(many_skip(one_of(is_xid_continue)))?;
    input.skip(one_of("?!").or_not())?;
    let end = input.pos();

    let mut line = input.local.line();
    line.at_line_start = false;
    input.local.set_line(line);

    Some(WordSpan {
        text: &input.input.source()[start..end],
        start,
        end,
    })
}

fn is_word_start(character: char) -> bool {
    character == '_' || is_xid_start(character)
}

#[cfg(test)]
mod tests {
    use super::*;
    use chasa::input::IsCut;

    use crate::session::LineState;

    #[test]
    fn scans_plain_ascii_identifier() {
        let (word, remainder, _) = scan("alpha_42 rest", LineState::default());

        assert_eq!(word, Some((0..8, "alpha_42")));
        assert_eq!(remainder, " rest");
    }

    #[test]
    fn scans_unicode_identifier_by_xid_rules() {
        let (word, remainder, _) = scan("日本語2 next", LineState::default());

        assert_eq!(word, Some((0..10, "日本語2")));
        assert_eq!(remainder, " next");
    }

    #[test]
    fn underscore_is_a_valid_word_start() {
        let (word, remainder, _) = scan("_private+", LineState::default());

        assert_eq!(word, Some((0..8, "_private")));
        assert_eq!(remainder, "+");
    }

    #[test]
    fn consumes_at_most_one_trailing_question_or_bang() {
        let (question, question_remainder, _) = scan("ready??", LineState::default());
        let (bang, bang_remainder, _) = scan("mutate!!", LineState::default());

        assert_eq!(question, Some((0..6, "ready?")));
        assert_eq!(question_remainder, "?");
        assert_eq!(bang, Some((0..7, "mutate!")));
        assert_eq!(bang_remainder, "!");
    }

    #[test]
    fn successful_word_leaves_the_physical_line_start() {
        let initial_line = LineState {
            last_newline: Some((4, 5)),
            line_start: 5,
            line_indent: 3,
            at_line_start: true,
        };

        let (_, _, line) = scan("name", initial_line);

        assert_eq!(
            line,
            LineState {
                at_line_start: false,
                ..initial_line
            }
        );
    }

    #[test]
    fn candidate_keyword_spelling_has_no_lexical_classification() {
        let (word, remainder, _) = scan("if(", LineState::default());

        assert_eq!(word, Some((0..2, "if")));
        assert_eq!(remainder, "(");
    }

    fn scan(source: &str, line: LineState) -> (Option<(Range<usize>, &str)>, &str, LineState) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(line);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut input = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let word = input
            .run(chasa::prelude::from_fn(scan_word))
            .map(|word| (word.range(), word.text()));

        (word, input.input.remainder(), input.local.line())
    }
}
