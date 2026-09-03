//! Lossless range scanning for identifier-shaped words.

use std::ops::Range;

use chasa::{
    Back as _, ErrorSink,
    error::std::Unexpected,
    parser::SkipParserOnce as _,
    prelude::{many_skip, one_of},
};
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::session::SynIn;

/// The source text and byte range consumed by one maximal word scan.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct WordSpan<'source> {
    text: &'source str,
    start: usize,
    end: usize,
}

impl<'source> WordSpan<'source> {
    pub(crate) fn from_root_range(root: &'source str, range: Range<usize>) -> Self {
        assert!(range.start < range.end);
        assert!(range.end <= root.len());
        assert!(root.is_char_boundary(range.start) && root.is_char_boundary(range.end));
        Self {
            text: &root[range.clone()],
            start: range.start,
            end: range.end,
        }
    }

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
pub(crate) fn scan_word<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = i.pos();
    i.maybe(one_of(is_word_start))??;
    i.skip(many_skip(one_of(is_xid_continue)))?;
    i.skip(one_of("?!").or_not())?;
    let end = i.pos();

    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);

    Some(WordSpan {
        text: &i.input.source()[start..end],
        start,
        end,
    })
}

/// Consumes a name accepted after a path separator.  Ordinary words and the
/// sigil-prefixed forms share the same lossless span representation.
pub(crate) fn scan_path_segment<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    if let Some(word) = i.run(scan_word) {
        return Some(word);
    }
    i.rollback(checkpoint);

    i.maybe(one_of("$&'"))??;
    i.run(scan_word)?;
    let end = i.pos();
    Some(WordSpan {
        text: &i.input.source()[start..end],
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
    use chasa::{input::IsCut, prelude::In};

    use crate::{
        input::SourceInput,
        session::{LineState, ParseLocal},
    };

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
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let word = i.run(scan_word).map(|word| (word.range(), word.text()));

        (word, i.input.remainder(), i.local.line())
    }
}
