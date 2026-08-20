//! Lossless range scanning for fixed, context-independent punctuation.

use std::ops::Range;

use chasa::{
    ErrorSink,
    error::std::Unexpected,
    parser::SkipParserOnce as _,
    prelude::{In, choice, from_fn, item, tag},
};

use crate::{
    input::SourceInput,
    session::{Delimiter, ParseLocal},
};

/// The scanner-layer kind and source extent of one fixed punctuation token.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct PunctuationSpan<'source> {
    kind: PunctuationKind,
    text: &'source str,
    start: usize,
    end: usize,
}

impl<'source> PunctuationSpan<'source> {
    pub(crate) fn kind(self) -> PunctuationKind {
        self.kind
    }

    pub(crate) fn text(self) -> &'source str {
        self.text
    }

    pub(crate) fn range(self) -> Range<usize> {
        self.start..self.end
    }
}

/// A fixed punctuation role before grammar-specific CST classification.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PunctuationKind {
    Open(Delimiter),
    Close(Delimiter),
    Backslash,
    Apostrophe,
    Comma,
    Semicolon,
    Dot,
    ColonColon,
    Colon,
}

/// Consumes one fixed punctuation token at the current byte position.
///
/// `=`, `..`, `...`, `->`, `|`, `*`, and `/` remain dynamic-operator
/// territory. Delimiter stack changes also remain grammar-owned: recognizing
/// an opening or closing spelling does not establish a structural group.
pub(crate) fn scan_punctuation<'source, E>(
    mut input: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<PunctuationSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = input.pos();
    let punctuation = choice((
        tag("::").to(PunctuationKind::ColonColon),
        item('(').to(PunctuationKind::Open(Delimiter::Parenthesis)),
        item(')').to(PunctuationKind::Close(Delimiter::Parenthesis)),
        item('[').to(PunctuationKind::Open(Delimiter::Bracket)),
        item(']').to(PunctuationKind::Close(Delimiter::Bracket)),
        item('{').to(PunctuationKind::Open(Delimiter::Brace)),
        item('}').to(PunctuationKind::Close(Delimiter::Brace)),
        item('\\').to(PunctuationKind::Backslash),
        item('\'').to(PunctuationKind::Apostrophe),
        item(',').to(PunctuationKind::Comma),
        item(';').to(PunctuationKind::Semicolon),
        item(':').to(PunctuationKind::Colon),
        from_fn(scan_dot),
    ));
    let kind = input.maybe(punctuation)??;
    let end = input.pos();

    let mut line = input.local.line();
    line.at_line_start = false;
    input.local.set_line(line);

    Some(PunctuationSpan {
        kind,
        text: &input.input.source()[start..end],
        start,
        end,
    })
}

fn scan_dot<E>(
    mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<PunctuationKind>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    input.skip(item('.'))?;
    input.not(item('.'))?;
    Some(PunctuationKind::Dot)
}

#[cfg(test)]
mod tests {
    use super::*;
    use chasa::input::IsCut;

    use crate::session::LineState;

    #[test]
    fn recognizes_the_complete_fixed_punctuation_set() {
        let cases = [
            ("(", PunctuationKind::Open(Delimiter::Parenthesis)),
            (")", PunctuationKind::Close(Delimiter::Parenthesis)),
            ("[", PunctuationKind::Open(Delimiter::Bracket)),
            ("]", PunctuationKind::Close(Delimiter::Bracket)),
            ("{", PunctuationKind::Open(Delimiter::Brace)),
            ("}", PunctuationKind::Close(Delimiter::Brace)),
            ("\\", PunctuationKind::Backslash),
            ("'", PunctuationKind::Apostrophe),
            (",", PunctuationKind::Comma),
            (";", PunctuationKind::Semicolon),
            (".", PunctuationKind::Dot),
            ("::", PunctuationKind::ColonColon),
            (":", PunctuationKind::Colon),
        ];

        for (text, expected_kind) in cases {
            let result = scan(text, ParseLocal::new());

            assert_eq!(
                result.punctuation,
                Some((expected_kind, 0..text.len(), text)),
                "fixed punctuation {text:?}",
            );
            assert_eq!(result.remainder, "");
        }
    }

    #[test]
    fn double_colon_wins_before_plain_colon() {
        let result = scan(":::tail", ParseLocal::new());

        assert_eq!(
            result.punctuation,
            Some((PunctuationKind::ColonColon, 0..2, "::"))
        );
        assert_eq!(result.remainder, ":tail");
    }

    #[test]
    fn dynamic_operator_spellings_are_not_fixed_punctuation() {
        for source in ["=", "..", "...", "->", "|", "*", "/"] {
            let result = scan(source, ParseLocal::new());

            assert_eq!(result.punctuation, None, "dynamic operator {source:?}");
            assert_eq!(result.remainder, source);
        }
    }

    #[test]
    fn scanning_delimiters_does_not_mutate_the_grammar_owned_stack() {
        let mut local = ParseLocal::new();
        local.push_delimiter(Delimiter::Brace);
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });

        let result = scan("(", local);

        assert_eq!(result.delimiter, Some(Delimiter::Brace));
        assert!(!result.line.at_line_start);
    }

    struct ScanResult<'source> {
        punctuation: Option<(PunctuationKind, Range<usize>, &'source str)>,
        remainder: &'source str,
        delimiter: Option<Delimiter>,
        line: LineState,
    }

    fn scan(source: &str, mut local: ParseLocal) -> ScanResult<'_> {
        let mut source_input = SourceInput::new(source);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut input = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let punctuation = input
            .run(chasa::prelude::from_fn(scan_punctuation))
            .map(|punctuation| (punctuation.kind(), punctuation.range(), punctuation.text()));

        ScanResult {
            punctuation,
            remainder: input.input.remainder(),
            delimiter: input.local.delimiter(),
            line: input.local.line(),
        }
    }
}
