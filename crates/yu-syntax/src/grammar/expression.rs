//! Minimal expression grammar shared by declaration values and Pratt parsing.

use std::ops::Range;

use chasa::{
    ErrorSink,
    error::std::{Unexpected, UnexpectedEndOfInput},
    prelude::{In, from_fn, many_skip, one_of},
};

use crate::{input::SourceInput, scan::word::{WordSpan, scan_word}, session::ParseLocal};

/// One expression accepted before dynamic operators are enabled.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Expression<'source> {
    Identifier(WordSpan<'source>),
    Integer(IntegerLiteral<'source>),
}

impl Expression<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        match self {
            Self::Identifier(identifier) => identifier.range(),
            Self::Integer(integer) => integer.range(),
        }
    }
}

/// The source extent of one decimal integer literal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct IntegerLiteral<'source> {
    text: &'source str,
    start: usize,
    end: usize,
}

impl<'source> IntegerLiteral<'source> {
    pub(crate) fn range(self) -> Range<usize> {
        self.start..self.end
    }
}

/// Parses an identifier or decimal integer expression without operators.
pub(crate) fn parse_expression<'source, E>(
    mut input: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<Expression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    input.choice((
        from_fn(|input| parse_identifier(input).map(Expression::Identifier)),
        from_fn(|input| parse_integer(input).map(Expression::Integer)),
    ))
}

fn parse_identifier<'source, E>(
    mut input: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    input.run(from_fn(scan_word))
}

fn parse_integer<'source, E>(
    mut input: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<IntegerLiteral<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = input.pos();
    input.skip(one_of(|character: char| character.is_ascii_digit()))?;
    input.skip(many_skip(one_of(|character: char| character.is_ascii_digit())))?;
    let end = input.pos();

    Some(IntegerLiteral {
        text: &input.input.source()[start..end],
        start,
        end,
    })
}
