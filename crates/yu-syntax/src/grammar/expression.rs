//! Minimal expression grammar shared by declaration values and Pratt parsing.

use std::ops::Range;

use chasa::{
    ErrorSink,
    error::std::{Unexpected, UnexpectedEndOfInput},
    parser::Parser,
    prelude::{from_fn, many_skip, one_of},
};

use crate::{
    operator::{BindingPower, OperatorTable},
    scan::{
        operator::{LeadingTrivia, OperatorSite, ScannedFixity, ScannedOperator, scan_operator},
        trivia::{TriviaRun, scan_trivia},
        word::{WordSpan, scan_word},
    },
    session::{CommitOutput, Committed, Probe, SynIn},
    syntax_kind::SyntaxKind,
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
    SuffixApplication {
        operand: Box<Expression<'source>>,
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
            Self::SuffixApplication { operand, operator } => {
                operand.range().start..operator.range().end
            }
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
    i: SynIn<'_, 'source, '_, E>,
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
    i: SynIn<'_, 'source, '_, E>,
) -> Option<Expression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let minimum = BindingPower::scalar(i8::MIN);
    parse_expression_bp(table, &minimum, i)
}

/// Minimal metadata retained by the direct Pratt continuation.
///
/// The checkpoint identifies the first emitted child of the expression, so an
/// accepted LED can wrap that complete left operand with `start_node_at`
/// without an event buffer or a second traversal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParsedExpression<C> {
    checkpoint: C,
    range: Range<usize>,
}

impl<C> ParsedExpression<C> {
    fn new(checkpoint: C, range: Range<usize>) -> Self {
        Self { checkpoint, range }
    }
}

/// Parses one expression into a committed direct-CST output.
///
/// The caller owns and has already emitted any trivia preceding the expression
/// start. `leading` preserves that trivia's effect on NUD operator judgement;
/// no leading trivia is scanned or emitted here.
pub(crate) fn parse_direct_expression_with_operators<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedExpression<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let minimum = BindingPower::scalar(i8::MIN);
    parse_direct_expression_bp(table, &minimum, leading, committed)
}

fn parse_expression_bp<'source, E>(
    table: &OperatorTable,
    minimum: &BindingPower,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Expression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = leading_trivia(&consume_trivia(&mut i)?);
    let nud = i.run(from_fn(|i| recognize_nud(table, leading, i)))?;
    let mut left = match nud {
        NudRecognition::Identifier(identifier) => Expression::Identifier(identifier),
        NudRecognition::Integer(integer) => Expression::Integer(integer),
        NudRecognition::Prefix(operator) => {
            i.cut();
            let operand = i.run(from_fn(|i| {
                parse_expression_bp(table, prefix_right_binding_power(&operator)?, i)
            }))?;
            Expression::PrefixApplication {
                operator: operator_application(&operator),
                operand: Box::new(operand),
            }
        }
        NudRecognition::Nullfix(operator) => Expression::NullfixApplication {
            operator: operator_application(&operator),
        },
    };

    while let Some(tail) = i.run(from_fn(|i| recognize_led(table, minimum, i)))? {
        match tail {
            LedRecognition::Infix {
                operator, right, ..
            } => {
                i.cut();
                let right = i.run(from_fn(|i| parse_expression_bp(table, &right, i)))?;
                left = Expression::InfixApplication {
                    left: Box::new(left),
                    operator: operator_application(&operator),
                    right: Box::new(right),
                };
            }
            LedRecognition::Suffix { operator, .. } => {
                left = Expression::SuffixApplication {
                    operand: Box::new(left),
                    operator: operator_application(&operator),
                };
            }
        }
    }

    Some(left)
}

/// Sink-free NUD result shared by AST tests and the direct continuation.
#[derive(Clone, Debug, Eq, PartialEq)]
enum NudRecognition<'source> {
    Identifier(WordSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Prefix(ScannedOperator<'source>),
    Nullfix(ScannedOperator<'source>),
}

/// Sink-free LED result shared by AST tests and the direct continuation.
#[derive(Clone, Debug, Eq, PartialEq)]
enum LedRecognition<'source> {
    Infix {
        leading: TriviaRun,
        operator: ScannedOperator<'source>,
        left: BindingPower,
        right: BindingPower,
    },
    Suffix {
        leading: TriviaRun,
        operator: ScannedOperator<'source>,
        left: BindingPower,
    },
}

fn recognize_nud<'source, E>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<NudRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.choice((
        from_fn(|i| {
            let scanned = scan_operator(OperatorSite::Nud, leading, table, i)?;
            match scanned.fixity() {
                ScannedFixity::Prefix { .. } => Some(NudRecognition::Prefix(scanned)),
                ScannedFixity::Nullfix => Some(NudRecognition::Nullfix(scanned)),
                ScannedFixity::Infix { .. } | ScannedFixity::Suffix { .. } => None,
            }
        }),
        parse_identifier.map(NudRecognition::Identifier),
        parse_integer_literal.map(NudRecognition::Integer),
    ))
}

fn recognize_led<'source, E>(
    table: &OperatorTable,
    minimum: &BindingPower,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Option<LedRecognition<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.maybe(from_fn(|i| scan_led(table, minimum, i)))
}

fn scan_led<'source, E>(
    table: &OperatorTable,
    minimum: &BindingPower,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<LedRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = consume_trivia(&mut i)?;
    let leading_presence = leading_trivia(&leading);
    let scanned = scan_operator(OperatorSite::Led, leading_presence, table, i)?;

    match scanned.fixity().clone() {
        ScannedFixity::Infix { left, right } if left >= *minimum => Some(LedRecognition::Infix {
            leading,
            operator: scanned,
            left,
            right,
        }),
        ScannedFixity::Suffix { left } if left >= *minimum => Some(LedRecognition::Suffix {
            leading,
            operator: scanned,
            left,
        }),
        ScannedFixity::Prefix { .. }
        | ScannedFixity::Infix { .. }
        | ScannedFixity::Suffix { .. }
        | ScannedFixity::Nullfix => None,
    }
}

fn consume_trivia<E>(i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.run(scan_trivia)
}

fn leading_trivia(trivia: &TriviaRun) -> LeadingTrivia {
    if trivia.is_empty() {
        LeadingTrivia::None
    } else {
        LeadingTrivia::Present
    }
}

fn operator_application<'source>(
    operator: &ScannedOperator<'source>,
) -> OperatorApplication<'source> {
    OperatorApplication {
        text: operator.text(),
        range: operator.range(),
    }
}

fn prefix_right_binding_power<'operator, 'source>(
    operator: &'operator ScannedOperator<'source>,
) -> Option<&'operator BindingPower> {
    let ScannedFixity::Prefix { right } = operator.fixity() else {
        return None;
    };
    Some(right)
}

fn parse_direct_expression_bp<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    minimum: &BindingPower,
    leading: LeadingTrivia,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedExpression<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let left_checkpoint = committed.checkpoint();
    let nud = committed.probe(|probe| probe_nud(table, leading, probe))?;
    if matches!(&nud, NudRecognition::Prefix(_)) {
        cut_after_acceptance(committed);
    }
    let mut left = commit_nud(table, nud, left_checkpoint, committed)?;

    while let Some(led) = committed.probe(|probe| probe_led(table, minimum, probe)) {
        cut_after_acceptance(committed);
        left = commit_led(table, led, left, committed)?;
    }

    Some(left)
}

/// Probes a NUD candidate without granting access to the output sink.
fn probe_nud<'parse, 'source, 'local, E>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> Option<NudRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    probe
        .input()
        .run(from_fn(|i| recognize_nud(table, leading, i)))
}

/// Probes a LED candidate and rolls back its trivia with every rejection.
fn probe_led<'parse, 'source, 'local, E>(
    table: &OperatorTable,
    minimum: &BindingPower,
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> Option<LedRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    probe
        .input()
        .run(from_fn(|i| recognize_led(table, minimum, i)))?
}

fn cut_after_acceptance<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| probe.input().cut());
}

fn commit_nud<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    accepted: NudRecognition<'source>,
    checkpoint: O::Checkpoint,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedExpression<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match accepted {
        NudRecognition::Identifier(identifier) => {
            let range = identifier.range();
            committed.start_node(SyntaxKind::IdentifierExpression);
            committed.token(SyntaxKind::Identifier, range.clone());
            committed.finish_node();
            Some(ParsedExpression::new(checkpoint, range))
        }
        NudRecognition::Integer(integer) => {
            let range = integer.range();
            committed.start_node(SyntaxKind::IntegerLiteral);
            committed.token(SyntaxKind::Integer, range.clone());
            committed.finish_node();
            Some(ParsedExpression::new(checkpoint, range))
        }
        NudRecognition::Prefix(operator) => {
            let range_start = operator.range().start;
            let right = prefix_right_binding_power(&operator)?;
            committed.start_node(SyntaxKind::PrefixExpression);
            committed.token(SyntaxKind::Operator, operator.range());
            committed.emit_trivia(operator.trailing_trivia());
            let operand = parse_direct_expression_bp(table, right, LeadingTrivia::None, committed)?;
            let range = range_start..operand.range.end;
            committed.finish_node();
            Some(ParsedExpression::new(checkpoint, range))
        }
        NudRecognition::Nullfix(operator) => {
            let range = operator.range();
            committed.start_node(SyntaxKind::NullfixExpression);
            committed.token(SyntaxKind::Operator, range.clone());
            committed.emit_trivia(operator.trailing_trivia());
            committed.finish_node();
            Some(ParsedExpression::new(checkpoint, range))
        }
    }
}

/// Emits one accepted LED after its probe has committed.
fn commit_led<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    accepted: LedRecognition<'source>,
    left: ParsedExpression<O::Checkpoint>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedExpression<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match accepted {
        LedRecognition::Infix {
            leading,
            operator,
            right,
            ..
        } => {
            let operator_range = operator.range();
            committed.start_node_at(left.checkpoint, SyntaxKind::InfixExpression);
            committed.emit_trivia(&leading);
            committed.token(SyntaxKind::Operator, operator_range.clone());
            committed.emit_trivia(operator.trailing_trivia());
            let right = parse_direct_expression_bp(table, &right, LeadingTrivia::None, committed)?;
            let range = left.range.start..right.range.end;
            committed.finish_node();
            Some(ParsedExpression::new(left.checkpoint, range))
        }
        LedRecognition::Suffix {
            leading, operator, ..
        } => {
            let operator_range = operator.range();
            let range = left.range.start..operator_range.end;
            committed.start_node_at(left.checkpoint, SyntaxKind::SuffixExpression);
            committed.emit_trivia(&leading);
            committed.token(SyntaxKind::Operator, operator_range);
            committed.emit_trivia(operator.trailing_trivia());
            committed.finish_node();
            Some(ParsedExpression::new(left.checkpoint, range))
        }
    }
}

fn parse_atom<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Expression<'source>>
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

fn parse_identifier<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    i.run(scan_word)
}

pub(crate) fn parse_integer_literal<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
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
    use chasa::{input::IsCut, prelude::In};

    use crate::{
        SyntaxKind, SyntaxNode,
        input::SourceInput,
        operator::{OperatorDeclaration, OperatorFixities},
        session::{FullCstOutput, ParseLocal, Probe},
    };

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

    #[test]
    fn direct_pratt_nud_emits_nested_prefix_nodes_after_candidate_fallback() {
        let root = parse_direct("+!a", &canonical_operator_table());
        let outer = only_child(&root, SyntaxKind::PrefixExpression);
        assert_eq!(direct_token_kinds(&outer), vec![SyntaxKind::Operator]);
        assert_eq!(outer.first_token().expect("prefix operator").text(), "+");

        let inner = only_child(&outer, SyntaxKind::PrefixExpression);
        assert_eq!(
            inner.first_token().expect("nested prefix operator").text(),
            "!"
        );
        let identifier = only_child(&inner, SyntaxKind::IdentifierExpression);
        assert_eq!(identifier.text().to_string(), "a");
        assert_eq!(root.to_string(), "+!a");
    }

    #[test]
    fn direct_pratt_led_wraps_the_left_operand_at_its_checkpoint() {
        let root = parse_direct("a+!b", &canonical_operator_table());
        let infix = only_child(&root, SyntaxKind::InfixExpression);
        let children = infix.children_with_tokens().collect::<Vec<_>>();

        assert_eq!(children[0].kind(), SyntaxKind::IdentifierExpression);
        assert_eq!(children[1].kind(), SyntaxKind::Operator);
        assert_eq!(children[2].kind(), SyntaxKind::IdentifierExpression);
        assert_eq!(children[1].as_token().expect("infix operator").text(), "+!");
        assert_eq!(infix.to_string(), "a+!b");
    }

    #[test]
    fn direct_pratt_returns_a_weaker_led_to_the_caller_without_emitting_it() {
        let root = parse_direct("a+!b+!c", &canonical_operator_table());
        let outer = only_child(&root, SyntaxKind::InfixExpression);
        let inner = outer
            .children()
            .next()
            .expect("outer infix has a left operand");

        assert_eq!(inner.kind(), SyntaxKind::InfixExpression);
        assert_eq!(inner.to_string(), "a+!b");
        assert_eq!(outer.to_string(), "a+!b+!c");
    }

    #[test]
    fn direct_pratt_assigns_accepted_led_trivia_to_the_application_once() {
        let root = parse_direct("a +! b", &canonical_operator_table());
        let infix = only_child(&root, SyntaxKind::InfixExpression);

        assert_eq!(
            infix
                .children_with_tokens()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            vec![
                SyntaxKind::IdentifierExpression,
                SyntaxKind::Whitespace,
                SyntaxKind::Operator,
                SyntaxKind::Whitespace,
                SyntaxKind::IdentifierExpression,
            ]
        );
        assert_eq!(root.to_string(), "a +! b");
    }

    #[test]
    fn direct_pratt_emits_suffix_and_nullfix_application_nodes() {
        let table = canonical_operator_table();

        let suffix_root = parse_direct("a++", &table);
        let suffix = only_child(&suffix_root, SyntaxKind::SuffixExpression);
        assert_eq!(suffix.to_string(), "a++");
        assert_eq!(
            suffix
                .children_with_tokens()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            vec![SyntaxKind::IdentifierExpression, SyntaxKind::Operator]
        );

        let nullfix_root = parse_direct("!", &table);
        let nullfix = only_child(&nullfix_root, SyntaxKind::NullfixExpression);
        assert_eq!(nullfix.to_string(), "!");
        assert_eq!(direct_token_kinds(&nullfix), vec![SyntaxKind::Operator]);
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
            OperatorDeclaration::new(
                "++",
                OperatorFixities::new().with_suffix(BindingPower::scalar(90)),
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
            .run(from_fn(|i| parse_expression_with_operators(table, i)))
            .expect("expression should parse");
        assert_eq!(i.input.remainder(), "");
        expression
    }

    fn parse_direct(source: &str, table: &OperatorTable) -> SyntaxNode {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let mut committed = Probe::new(i).commit(FullCstOutput::new(source));

        committed.start_node(SyntaxKind::Root);
        parse_direct_expression_with_operators(table, LeadingTrivia::None, &mut committed)
            .expect("expression should parse directly");
        assert_eq!(committed.probe(|probe| probe.input().input.remainder()), "");
        committed.finish_node();

        SyntaxNode::new_root(committed.into_output().finish_complete())
    }

    fn only_child(node: &SyntaxNode, expected: SyntaxKind) -> SyntaxNode {
        let children = node.children().collect::<Vec<_>>();
        assert_eq!(
            children.len(),
            1,
            "expected exactly one child of {expected:?}"
        );
        assert_eq!(children[0].kind(), expected);
        children.into_iter().next().expect("one child")
    }

    fn direct_token_kinds(node: &SyntaxNode) -> Vec<SyntaxKind> {
        node.children_with_tokens()
            .filter_map(|child| child.into_token())
            .map(|token| token.kind())
            .collect()
    }
}
