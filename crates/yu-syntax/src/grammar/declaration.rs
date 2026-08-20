//! Shared grammar for source-leading declarations.

use std::ops::Range;

use chasa::{
    ErrorSink,
    error::std::{Unexpected, UnexpectedEndOfInput},
    prelude::{In, from_fn},
};

use crate::{
    input::SourceInput,
    scan::{
        punctuation::{PunctuationKind, scan_punctuation},
        trivia::scan_trivia,
        word::{WordSpan, scan_word},
    },
    session::ParseLocal,
};

/// One parsed source-leading declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Declaration<'source> {
    Use(UseDeclaration<'source>),
}

/// A `use path.component` declaration before syntax planning resolves it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UseDeclaration<'source> {
    range: Range<usize>,
    path: Vec<WordSpan<'source>>,
}

impl<'source> UseDeclaration<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn path(&self) -> &[WordSpan<'source>] {
        &self.path
    }
}

/// Parses one leading `use` declaration from the shared character stream.
pub(crate) fn parse_declaration<'source, E>(
    input: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<Declaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_use_declaration(input).map(Declaration::Use)
}

fn parse_use_declaration<'source, E>(
    mut input: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<UseDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = input.pos();
    let keyword = input.run(from_fn(scan_word))?;
    (keyword.text() == "use").then_some(())?;
    inline_trivia(&mut input)?;

    let mut path = vec![input.run(from_fn(scan_word))?];
    while let Some(punctuation) = input.maybe(from_fn(scan_punctuation))? {
        (punctuation.kind() == PunctuationKind::Dot).then_some(())?;
        path.push(input.run(from_fn(scan_word))?);
    }

    let end = path.last()?.range().end;
    Some(UseDeclaration {
        range: start..end,
        path,
    })
}

fn inline_trivia<E>(input: &mut In<'_, SourceInput<'_>, (), &mut ParseLocal, E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = input.run(from_fn(scan_trivia))?;
    let text = &input.input.source()[trivia.range()];
    (!text.is_empty() && !text.contains(['\r', '\n'])).then_some(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use chasa::input::IsCut;

    const LEADING_USE_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/leading-use-plain/main.yu"
    ));

    #[test]
    fn parses_leading_use_fixture_from_chasa_input() {
        let source = std::str::from_utf8(LEADING_USE_SOURCE).expect("fixture is UTF-8");
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

        let declaration = input
            .run(from_fn(parse_declaration))
            .expect("leading use declaration should parse");

        let Declaration::Use(declaration) = declaration;
        assert_eq!(declaration.range(), 0..12);
        assert_eq!(
            declaration
                .path()
                .iter()
                .map(|component| component.text())
                .collect::<Vec<_>>(),
            ["std", "data"]
        );
        assert_eq!(input.input.remainder(), "\nmy value = 1\n");
    }
}
