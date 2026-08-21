//! Minimal expression grammar shared by declaration values and Pratt parsing.

use std::ops::Range;

use chasa::{
    ErrorSink,
    error::std::{Unexpected, UnexpectedEndOfInput},
    parser::Parser,
    prelude::{In, from_fn, many_skip, one_of},
};

use crate::{
    input::SourceInput,
    operator::{BindingPower, OperatorTable},
    scan::{
        operator::{LeadingTrivia, OperatorSite, ScannedFixity, scan_operator},
        trivia::scan_trivia,
        word::{WordSpan, scan_word},
    },
    session::ParseLocal,
};

/// One expression accepted by the shared minimal and Pratt grammars.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Expression<'source> {
    Identifier(WordSpan<'source>),
    Integer(IntegerLiteral<'source>),
    PrefixApplication {
        operator: OperatorApplication<'source>,
        operand: Box<Expression<'source>>,
    },
    NullfixApplication {
        operator: OperatorApplication<'source>,
    },
    InfixApplication {
        left: Box<Expression<'source>>,
        operator: OperatorApplication<'source>,
        right: Box<Expression<'source>>,
    },
}

impl Expression<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        match self {
            Self::Identifier(identifier) => identifier.range(),
            Self::Integer(integer) => integer.range(),
            Self::PrefixApplication { operator, operand } => {
                operator.range.start..operand.range().end
            }
            Self::NullfixApplication { operator } => operator.range.clone(),
            Self::InfixApplication { left, right, .. } => left.range().start..right.range().end,
        }
    }
}

/// One site-aware operator use accepted by the immutable session table.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorApplication<'source> {
    text: &'source str,
    range: Range<usize>,
}

impl<'source> OperatorApplication<'source> {
    pub(crate) fn text(&self) -> &'source str {
        self.text
    }

    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
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
    pub(crate) fn text(self) -> &'source str {
        self.text
    }

    pub(crate) fn range(self) -> Range<usize> {
        self.start..self.end
    }
}

/// Parses an identifier or decimal integer expression without operators.
pub(crate) fn parse_expression<'source, E>(
    i: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<Expression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_atom(i)
}

/// Parses an expression with site-aware dynamic operator resolution.
pub(crate) fn parse_expression_with_operators<'source, E>(
    table: &OperatorTable,
    i: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<Expression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let minimum = BindingPower::scalar(i8::MIN);
    parse_expression_bp(table, &minimum, i)
}

fn parse_expression_bp<'source, E>(
    table: &OperatorTable,
    minimum: &BindingPower,
    mut i: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<Expression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = consume_trivia(&mut i)?;
    let mut left = i.choice((
        from_fn(|i| parse_prefix_or_nullfix(table, leading, i)),
        from_fn(parse_atom),
    ))?;

    while let Some(tail) = i.maybe(from_fn(|i| parse_infix_tail(table, minimum, i)))? {
        left = Expression::InfixApplication {
            left: Box::new(left),
            operator: tail.operator,
            right: Box::new(tail.right),
        };
    }

    Some(left)
}

fn parse_prefix_or_nullfix<'source, E>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    mut i: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<Expression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let scanned = i.run(from_fn(|i| {
        scan_operator(OperatorSite::Nud, leading, table, i)
    }))?;
    let operator = OperatorApplication {
        text: scanned.text(),
        range: scanned.range(),
    };

    match scanned.fixity().clone() {
        ScannedFixity::Prefix { right } => {
            i.cut();
            let operand = parse_expression_bp(table, &right, i)?;
            Some(Expression::PrefixApplication {
                operator,
                operand: Box::new(operand),
            })
        }
        ScannedFixity::Nullfix => Some(Expression::NullfixApplication { operator }),
        ScannedFixity::Infix { .. } | ScannedFixity::Suffix { .. } => None,
    }
}

fn parse_infix_tail<'source, E>(
    table: &OperatorTable,
    minimum: &BindingPower,
    mut i: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<InfixTail<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = consume_trivia(&mut i)?;
    let scanned = i.run(from_fn(|i| {
        scan_operator(OperatorSite::Led, leading, table, i)
    }))?;
    let ScannedFixity::Infix { left, right } = scanned.fixity().clone() else {
        return None;
    };
    (left >= *minimum).then_some(())?;
    i.cut();
    let operator = OperatorApplication {
        text: scanned.text(),
        range: scanned.range(),
    };
    let right = parse_expression_bp(table, &right, i)?;

    Some(InfixTail { operator, right })
}

fn consume_trivia<E>(
    i: &mut In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<LeadingTrivia>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = i.run(scan_trivia)?;
    if trivia.is_empty() {
        Some(LeadingTrivia::None)
    } else {
        Some(LeadingTrivia::Present)
    }
}

struct InfixTail<'source> {
    operator: OperatorApplication<'source>,
    right: Expression<'source>,
}

fn parse_atom<'source, E>(
    mut i: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<Expression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.choice((
        parse_identifier.map(Expression::Identifier),
        parse_integer_literal.map(Expression::Integer),
    ))
}

fn parse_identifier<'source, E>(
    mut i: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    i.run(scan_word)
}

pub(crate) fn parse_integer_literal<'source, E>(
    mut i: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<IntegerLiteral<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = i.pos();
    i.skip(one_of(|character: char| character.is_ascii_digit()))?;
    i.skip(many_skip(one_of(|character: char| {
        character.is_ascii_digit()
    })))?;
    let end = i.pos();

    Some(IntegerLiteral {
        text: &i.input.source()[start..end],
        start,
        end,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use chasa::input::IsCut;

    use crate::operator::{OperatorDeclaration, OperatorFixities};

    #[test]
    fn pratt_nud_splits_long_infix_into_prefix_nullfix_chain() {
        let table = canonical_operator_table();
        let expression = parse("+!a", &table);

        let Expression::PrefixApplication { operator, operand } = expression else {
            panic!("expected outer prefix application");
        };
        assert_eq!(operator.text(), "+");
        assert_eq!(operator.range(), 0..1);

        let Expression::PrefixApplication { operator, operand } = *operand else {
            panic!("expected nested prefix/nullfix-capable application");
        };
        assert_eq!(operator.text(), "!");
        assert_eq!(operator.range(), 1..2);

        let Expression::Identifier(identifier) = *operand else {
            panic!("expected identifier operand");
        };
        assert_eq!(identifier.text(), "a");
        assert_eq!(identifier.range(), 2..3);
    }

    #[test]
    fn pratt_led_keeps_long_infix_operator() {
        let table = canonical_operator_table();
        let expression = parse("a+!b", &table);

        let Expression::InfixApplication {
            left,
            operator,
            right,
        } = expression
        else {
            panic!("expected infix application");
        };
        assert_eq!(operator.text(), "+!");
        assert_eq!(operator.range(), 1..3);

        let Expression::Identifier(left) = *left else {
            panic!("expected left identifier");
        };
        let Expression::Identifier(right) = *right else {
            panic!("expected right identifier");
        };
        assert_eq!(left.text(), "a");
        assert_eq!(right.text(), "b");
    }

    #[test]
    fn pratt_binding_power_returns_a_weaker_tail_to_its_caller() {
        let table = canonical_operator_table();
        let expression = parse("a+!b+!c", &table);

        let Expression::InfixApplication {
            left,
            right: outer_right,
            ..
        } = expression
        else {
            panic!("expected outer infix application");
        };
        let Expression::InfixApplication { left, right, .. } = *left else {
            panic!("expected weaker trailing operator to associate outside the RHS");
        };
        let Expression::Identifier(left) = *left else {
            panic!("expected first identifier");
        };
        let Expression::Identifier(right) = *right else {
            panic!("expected second identifier");
        };
        let Expression::Identifier(rightmost) = *outer_right else {
            panic!("expected third identifier");
        };
        assert_eq!(
            (left.text(), right.text(), rightmost.text()),
            ("a", "b", "c")
        );
    }

    fn canonical_operator_table() -> OperatorTable {
        OperatorTable::from_declarations([
            OperatorDeclaration::new(
                "+!",
                OperatorFixities::new()
                    .with_infix(BindingPower::scalar(50), BindingPower::new(50, [1])),
            ),
            OperatorDeclaration::new(
                "+",
                OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            ),
            OperatorDeclaration::new(
                "!",
                OperatorFixities::new()
                    .with_prefix(BindingPower::scalar(80))
                    .with_nullfix(),
            ),
        ])
        .expect("canonical operators should be valid")
    }

    fn parse<'source>(source: &'source str, table: &OperatorTable) -> Expression<'source> {
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

        let expression = i
            .run(from_fn(|i| {
                parse_expression_with_operators(table, i)
            }))
            .expect("expression should parse");
        assert_eq!(i.input.remainder(), "");
        expression
    }
}
