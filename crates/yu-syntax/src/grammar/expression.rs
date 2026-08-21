//! Minimal expression grammar shared by declaration values and Pratt parsing.

use std::{ops::Range, sync::Arc};

use chasa::{
    Back as _, ErrorSink, Input as _,
    error::std::{Unexpected, UnexpectedEndOfInput},
    parser::Parser,
    prelude::{from_fn, many_skip, one_of},
};

use crate::{
    operator::{BindingPower, OperatorTable},
    scan::{
        operator::{LeadingTrivia, OperatorSite, ScannedFixity, ScannedOperator, scan_operator},
        punctuation::{PunctuationKind, scan_punctuation},
        trivia::{TriviaRun, scan_trivia},
        word::{WordSpan, scan_word},
    },
    session::{
        CommitOutput, Committed, CommittedRecoveryRecord, ConstructRole, Delimiter,
        ExpectationSources, ExpectedSyntax, ExpressionRole, GrammarRole, Probe, RecoveryKind,
        RecoverySiteKey, StopKind, StopSet, SynIn, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

/// One expression accepted by the shared minimal and Pratt grammars.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Expression<'source> {
    Identifier(WordSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Grouped {
        inner: Box<Expression<'source>>,
        range: Range<usize>,
    },
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
            Self::Grouped { range, .. } => range.clone(),
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

    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
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
        NudRecognition::Group { open } => {
            i.cut();
            push_expression_group_scope(&mut i);
            let inner_minimum = BindingPower::scalar(i8::MIN);
            let inner = match i.run(from_fn(|i| parse_expression_bp(table, &inner_minimum, i))) {
                Some(inner) => inner,
                None => {
                    pop_expression_group_scope(&mut i);
                    return None;
                }
            };
            consume_trivia(&mut i).expect("trivia scanning is total");
            let close = match i.run(recognize_group_close) {
                Some(close) => close,
                None => {
                    pop_expression_group_scope(&mut i);
                    return None;
                }
            };
            pop_expression_group_scope(&mut i);
            Expression::Grouped {
                inner: Box::new(inner),
                range: open.start..close.end,
            }
        }
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
    Group { open: Range<usize> },
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
        recognize_group_open.map(|open| NudRecognition::Group { open }),
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

fn recognize_group_open<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    matches!(
        punctuation.kind(),
        PunctuationKind::Open(Delimiter::Parenthesis)
    )
    .then(|| punctuation.range())
}

fn recognize_group_close<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    let close = matches!(
        punctuation.kind(),
        PunctuationKind::Close(Delimiter::Parenthesis)
    )
    .then(|| punctuation.range());
    if close.is_none() {
        i.rollback(checkpoint);
    }
    close
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
    if matches!(
        &nud,
        NudRecognition::Prefix(_) | NudRecognition::Group { .. }
    ) {
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

/// Tests whether the current position can begin a direct expression without
/// granting a continuation access to its output sink. Declaration recovery
/// uses this to decide whether an invalid occupying byte can be skipped and
/// the same mandatory value slot retried.
pub(crate) fn direct_expression_nud_candidate<'parse, 'source, 'local, E>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let i = probe.input();
    let checkpoint = i.checkpoint();
    let candidate = i
        .run(from_fn(|i| recognize_nud(table, leading, i)))
        .is_some();
    i.rollback(checkpoint);
    candidate
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
        NudRecognition::Group { open } => commit_group_nud(table, open, checkpoint, committed),
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

/// Completes an accepted group without returning to the NUD choice.  The
/// group remains a Pratt operand even if its inner semantic value is absent:
/// the committed CST node and its recovery records own that source shape.
fn commit_group_nud<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    open: Range<usize>,
    checkpoint: O::Checkpoint,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedExpression<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node_at(checkpoint, SyntaxKind::GroupedExpression);
    committed.token(SyntaxKind::LParen, open.clone());
    push_direct_expression_group_scope(committed);

    let inner_leading = commit_group_trivia(committed).expect("trivia scanning is total");
    committed.emit_trivia(&inner_leading);
    let inner_minimum = BindingPower::scalar(i8::MIN);
    let inner = commit_group_inner(
        table,
        &inner_minimum,
        leading_trivia(&inner_leading),
        committed,
    );
    let inner_missing_at = inner.is_none().then(|| committed_position(committed));

    let inner_trailing = commit_group_trivia(committed).expect("trivia scanning is total");
    committed.emit_trivia(&inner_trailing);

    // A missing inner slot can collapse with a missing close only at the same
    // unconsumed owner boundary.  At any token that the closing continuation
    // will own, emit the inner absence before that later source child.
    let delay_inner_missing = inner_missing_at.is_some_and(|at| {
        at == committed_position(committed) && group_close_absent_boundary(committed)
    });
    if inner_missing_at.is_some() && !delay_inner_missing {
        emit_group_inner_missing(committed);
    }

    let close = commit_group_close(committed);
    match close {
        GroupClose::Matched(range) => {
            committed.token(SyntaxKind::RParen, range.clone());
            pop_direct_expression_group_scope(committed);
            committed.finish_node();
            Some(ParsedExpression::new(checkpoint, open.start..range.end))
        }
        GroupClose::Missing { at } => {
            if delay_inner_missing {
                emit_group_inner_and_close_missing(committed, at);
            } else {
                emit_group_close_missing(committed, at);
            }
            pop_direct_expression_group_scope(committed);
            committed.finish_node();
            Some(ParsedExpression::new(checkpoint, open.start..at))
        }
    }
}

fn commit_group_inner<'parse, 'source, 'local, E, O>(
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
    parse_direct_expression_bp(table, minimum, leading, committed).or_else(|| {
        group_inner_error_retry(table, committed).then(|| {
            parse_direct_expression_bp(table, minimum, LeadingTrivia::None, committed)
                .expect("a retried group inner slot must commit its shared NUD candidate")
        })
    })
}

/// The inner mandatory slot follows the atomic-value rule.  It owns invalid
/// bytes only until a shared NUD candidate or a group boundary; it never
/// hands those bytes back to an outer declaration body recovery.
fn group_inner_error_retry<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let boundary = {
                let i = probe.input();
                let Some(character) = i.input.remainder().chars().next() else {
                    return (start < end).then_some((start..end, false));
                };
                matches!(character, ')' | ']' | '}' | ';' | ',')
            };
            if boundary {
                return (start < end).then_some((start..end, false));
            }
            {
                let i = probe.input();
                i.input.next()?;
                end = i.pos();
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            if direct_expression_nud_candidate(table, LeadingTrivia::None, probe) {
                return Some((start..end, true));
            }
        }
    });
    let Some((range, retry)) = recovered else {
        return false;
    };
    emit_group_error(
        committed,
        GrammarRole::Expression(ExpressionRole::Nud),
        range,
    );
    retry
}

enum GroupClose {
    Matched(Range<usize>),
    Missing { at: usize },
}

/// The closing mandatory slot follows the closing-delimiter rule.  A wrong
/// close is emitted as its own non-empty episode, then the same close slot
/// keeps searching rather than returning failure to the NUD dispatcher.
fn commit_group_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> GroupClose
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    loop {
        if group_close_absent_boundary(committed) {
            return GroupClose::Missing {
                at: committed_position(committed),
            };
        }

        let punctuation = committed.probe(|probe| probe.input().run(scan_punctuation));
        if let Some(punctuation) = punctuation {
            match punctuation.kind() {
                PunctuationKind::Close(Delimiter::Parenthesis) => {
                    return GroupClose::Matched(punctuation.range());
                }
                PunctuationKind::Close(actual @ (Delimiter::Bracket | Delimiter::Brace)) => {
                    emit_group_close_error(committed, punctuation.range(), actual);
                }
                _ => emit_group_error(committed, group_close_role(), punctuation.range()),
            }
            continue;
        }

        let range = committed
            .probe(|probe| {
                let start = probe.input().pos();
                let mut end = start;
                loop {
                    let i = probe.input();
                    let Some(character) = i.input.remainder().chars().next() else {
                        return (start < end).then_some(start..end);
                    };
                    if matches!(character, ')' | ']' | '}' | ';' | ',') {
                        return (start < end).then_some(start..end);
                    }
                    i.input.next().expect("the scanned group-close byte exists");
                    end = i.pos();
                    let mut line = i.local.line();
                    line.at_line_start = false;
                    i.local.set_line(line);
                }
            })
            .expect("a non-boundary group-close position must consume invalid source");
        emit_group_error(committed, group_close_role(), range);
    }
}

fn commit_group_trivia<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| probe.input().run(scan_trivia))
}

fn group_close_absent_boundary<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| {
        probe.input().input.remainder().is_empty()
            || matches!(
                probe.input().input.remainder().chars().next(),
                Some(';' | ',')
            )
    })
}

fn group_close_role() -> GrammarRole {
    GrammarRole::ClosingDelimiter {
        owner: ConstructRole::ExpressionGroup,
        delimiter: Delimiter::Parenthesis,
    }
}

fn emit_group_inner_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Expression(ExpressionRole::Nud);
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Expression,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_group_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    at: usize,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let role = group_close_role();
    emit_group_missing(
        committed,
        role,
        at,
        Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                Delimiter::Parenthesis,
            )),
            range: at..at,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
    );
}

fn emit_group_inner_and_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    at: usize,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let close_role = group_close_role();
    let expression_role = GrammarRole::Expression(ExpressionRole::Nud);
    emit_group_missing(
        committed,
        close_role,
        at,
        Arc::from([
            SyntaxExpectation {
                role: close_role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    Delimiter::Parenthesis,
                )),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            },
            SyntaxExpectation {
                role: expression_role,
                expected: ExpectedSyntax::Expression,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            },
        ]),
    );
}

fn emit_group_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: GrammarRole,
    at: usize,
    expectations: Arc<[SyntaxExpectation]>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            expectations,
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_group_close_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
    actual: Delimiter,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let role = group_close_role();
    let record = committed.probe(|probe| {
        let i = probe.input();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::Punctuation(
                    crate::session::PunctuationEvidence::Close(actual),
                ),
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    Delimiter::Parenthesis,
                )),
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn emit_group_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: GrammarRole,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let expected = match role {
        GrammarRole::Expression(ExpressionRole::Nud) => ExpectedSyntax::Expression,
        GrammarRole::ClosingDelimiter { .. } => ExpectedSyntax::Punctuation(
            crate::session::PunctuationEvidence::Close(Delimiter::Parenthesis),
        ),
        _ => unreachable!("group recovery only emits inner or close roles"),
    };
    let record = committed.probe(|probe| {
        let i = probe.input();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn committed_position<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> usize
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| probe.input().pos())
}

fn push_expression_group_scope<E>(i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    i.local.push_delimiter(Delimiter::Parenthesis);
    i.local
        .push_stop_set(StopSet::default().with(StopKind::RightParenthesis));
}

fn pop_expression_group_scope<E>(i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    assert_eq!(
        i.local.pop_stop_set(),
        Some(StopSet::default().with(StopKind::RightParenthesis))
    );
}

fn push_direct_expression_group_scope<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| push_expression_group_scope(probe.input()));
}

fn pop_direct_expression_group_scope<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| pop_expression_group_scope(probe.input()));
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
    use std::{cell::Cell, rc::Rc};

    use super::*;
    use chasa::{input::IsCut, prelude::In};

    use crate::{
        SyntaxKind, SyntaxNode,
        input::SourceInput,
        operator::{OperatorDeclaration, OperatorFixities},
        session::{CommittedRecoveryRecord, FullCstOutput, ParseLocal, Probe},
    };

    #[test]
    fn pratt_ast_builds_a_grouped_expression_with_its_full_range() {
        let expression = parse("(a)", &canonical_operator_table());

        let Expression::Grouped { inner, range } = expression else {
            panic!("expected grouped expression");
        };
        assert_eq!(range, 0..3);
        let Expression::Identifier(inner) = *inner else {
            panic!("expected identifier inside group");
        };
        assert_eq!(inner.text(), "a");
        assert_eq!(inner.range(), 1..2);
    }

    #[test]
    fn pratt_ast_builds_nested_grouped_expressions() {
        let expression = parse("((a))", &canonical_operator_table());

        let Expression::Grouped { inner, range } = expression else {
            panic!("expected outer group");
        };
        assert_eq!(range, 0..5);
        let Expression::Grouped { inner, range } = *inner else {
            panic!("expected inner group");
        };
        assert_eq!(range, 1..4);
        assert!(matches!(*inner, Expression::Identifier(_)));
    }

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

    #[test]
    fn direct_pratt_emits_group_owned_trivia_and_nested_groups_losslessly() {
        let source = "(\n/* note */ ((a)) \n)";
        let root = parse_direct(source, &canonical_operator_table());
        let group = only_child(&root, SyntaxKind::GroupedExpression);

        assert_eq!(group.to_string(), source);
        assert_eq!(
            group
                .children_with_tokens()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            vec![
                SyntaxKind::LParen,
                SyntaxKind::Newline,
                SyntaxKind::BlockComment,
                SyntaxKind::Whitespace,
                SyntaxKind::GroupedExpression,
                SyntaxKind::Whitespace,
                SyntaxKind::Newline,
                SyntaxKind::RParen,
            ]
        );
        assert_eq!(
            group.children().next().expect("nested group").kind(),
            SyntaxKind::GroupedExpression
        );
    }

    #[test]
    fn group_resets_binding_power_and_returns_to_the_outer_led_loop() {
        let expression = parse("(a+!b)*c", &canonical_operator_table());

        let Expression::InfixApplication {
            left,
            operator,
            right,
        } = expression
        else {
            panic!("expected outer infix application");
        };
        assert_eq!(operator.text(), "*");
        let Expression::Grouped { inner, .. } = *left else {
            panic!("expected grouped left operand");
        };
        assert!(matches!(*inner, Expression::InfixApplication { .. }));
        assert!(matches!(*right, Expression::Identifier(_)));

        let root = parse_direct("(a+!b)*c", &canonical_operator_table());
        let outer = only_child(&root, SyntaxKind::InfixExpression);
        assert_eq!(
            outer.children().next().expect("left operand").kind(),
            SyntaxKind::GroupedExpression
        );
        assert_eq!(outer.to_string(), "(a+!b)*c");

        let suffix = parse_direct("(a)++", &canonical_operator_table());
        let suffix = only_child(&suffix, SyntaxKind::SuffixExpression);
        assert_eq!(
            suffix.children().next().expect("grouped operand").kind(),
            SyntaxKind::GroupedExpression
        );
        assert_eq!(suffix.to_string(), "(a)++");
    }

    #[test]
    fn direct_group_recovers_its_mandatory_slots_without_duplicate_absences() {
        let cases = [
            ("()", vec![(RecoveryKind::Missing, 1..1)]),
            ("(value", vec![(RecoveryKind::Missing, 6..6)]),
            (
                "(a]",
                vec![(RecoveryKind::Error, 2..3), (RecoveryKind::Missing, 3..3)],
            ),
            ("(", vec![(RecoveryKind::Missing, 1..1)]),
            ("(@a)", vec![(RecoveryKind::Error, 1..2)]),
            (
                "(@",
                vec![(RecoveryKind::Error, 1..2), (RecoveryKind::Missing, 2..2)],
            ),
        ];

        for (source, expected) in cases {
            let (root, recoveries) = parse_direct_recovered(source, &canonical_operator_table());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                recoveries
                    .iter()
                    .map(|recovery| (recovery.kind, recovery.site.range.clone()))
                    .collect::<Vec<_>>(),
                expected,
                "{source:?}"
            );
        }

        let (_, empty) = parse_direct_recovered("()", &canonical_operator_table());
        assert_eq!(
            empty[0].site.role,
            GrammarRole::Expression(ExpressionRole::Nud)
        );

        let (_, missing_close) = parse_direct_recovered("(value", &canonical_operator_table());
        assert_eq!(missing_close[0].site.role, group_close_role());

        let (_, mismatched) = parse_direct_recovered("(a]", &canonical_operator_table());
        assert_eq!(mismatched[0].site.role, group_close_role());
        assert_eq!(
            mismatched[0].unexpected,
            Arc::from([UnexpectedSyntax::Token {
                range: 2..3,
                category: UnexpectedCategory::Punctuation(
                    crate::session::PunctuationEvidence::Close(Delimiter::Bracket),
                ),
            }])
        );

        let (_, collapsed) = parse_direct_recovered("(", &canonical_operator_table());
        assert_eq!(collapsed[0].site.role, group_close_role());
        assert_eq!(collapsed[0].expectations.len(), 2);
        assert_eq!(collapsed[0].primary_expectation, 0);
        assert_eq!(
            collapsed[0].expectations[1].role,
            GrammarRole::Expression(ExpressionRole::Nud)
        );

        let (_, invalid_at_eof) = parse_direct_recovered("(@", &canonical_operator_table());
        assert_eq!(invalid_at_eof[1].site.role, group_close_role());
        assert_eq!(invalid_at_eof[1].expectations.len(), 2);
    }

    #[test]
    fn group_probe_is_sink_free_and_committed_group_preserves_lossless_invariants() {
        let source = "(a+!b)*c";
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
        let calls = Rc::new(Cell::new(0));
        let mut committed = Probe::new(i).commit(CountingOutput {
            calls: Rc::clone(&calls),
        });

        assert!(committed.probe(|probe| direct_expression_nud_candidate(
            &canonical_operator_table(),
            LeadingTrivia::None,
            probe,
        )));
        assert_eq!(calls.get(), 0, "a NUD probe must not call the sink");

        let root = parse_direct(source, &canonical_operator_table());
        let tokens = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.text().to_string())
            .collect::<String>();
        assert_eq!(tokens, source);
        assert_eq!(root.to_string(), source);
        assert_eq!(root.kind(), SyntaxKind::Root);
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
            OperatorDeclaration::new(
                "*",
                OperatorFixities::new()
                    .with_infix(BindingPower::scalar(60), BindingPower::scalar(60)),
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

    fn parse_direct_recovered(
        source: &str,
        table: &OperatorTable,
    ) -> (SyntaxNode, Vec<CommittedRecoveryRecord>) {
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
            .expect("an accepted group remains a direct Pratt operand after recovery");
        assert_eq!(committed.probe(|probe| probe.input().input.remainder()), "");
        committed.finish_node();

        let output = committed.into_output();
        let recoveries = output.committed_recoveries().to_vec();
        (SyntaxNode::new_root(output.finish_complete()), recoveries)
    }

    struct CountingOutput {
        calls: Rc<Cell<usize>>,
    }

    impl CountingOutput {
        fn record(&self) {
            self.calls.set(self.calls.get() + 1);
        }
    }

    impl CommitOutput<'_> for CountingOutput {
        type Checkpoint = ();

        fn checkpoint(&mut self) -> Self::Checkpoint {
            self.record();
        }

        fn start_node(&mut self, _: SyntaxKind) {
            self.record();
        }

        fn start_node_at(&mut self, _: Self::Checkpoint, _: SyntaxKind) {
            self.record();
        }

        fn token(&mut self, _: SyntaxKind, _: Range<usize>) {
            self.record();
        }

        fn emit_trivia(&mut self, _: &TriviaRun) {
            self.record();
        }

        fn finish_node(&mut self) {
            self.record();
        }

        fn commit_recovery(&mut self, _: CommittedRecoveryRecord) {
            self.record();
        }

        fn emit_missing(&mut self, _: CommittedRecoveryRecord) {
            self.record();
        }

        fn emit_error(&mut self, _: CommittedRecoveryRecord) {
            self.record();
        }
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
