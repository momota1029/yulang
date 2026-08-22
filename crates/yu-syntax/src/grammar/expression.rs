//! Minimal expression grammar shared by declaration values and Pratt parsing.

use std::{marker::PhantomData, ops::Range, sync::Arc};

use chasa::{
    Back as _, ErrorSink, Input as _,
    error::std::{Unexpected, UnexpectedEndOfInput},
    parser::Parser,
    prelude::{from_fn, many_skip, one_of},
};

use crate::{
    grammar::declaration::Recovered,
    operator::OperatorTable,
    scan::{
        operator::{LeadingTrivia, OperatorSite, ScannedFixity, ScannedOperator, scan_operator},
        punctuation::{PunctuationKind, scan_punctuation},
        trivia::{TriviaRun, scan_trivia},
        word::{WordSpan, scan_word},
    },
    session::{
        ColonApplicationRole, CommitOutput, Committed, CommittedRecoveryRecord, ConstructRole, Delimiter,
        ExpectationSources, ExpectedSyntax, ExpressionRole, GrammarRole, Probe, RecoveryKind,
        RecoverySiteKey, StopKind, StopSet, SynIn, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

/// A precedence-neutral source-order dynamic operator chain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorChain<'source> {
    items: Vec<OperatorChainItem<'source>>,
    range: Range<usize>,
}

impl<'source> OperatorChain<'source> {
    fn new(items: Vec<OperatorChainItem<'source>>, range: Range<usize>) -> Self {
        Self { items, range }
    }

    pub(crate) fn items(&self) -> &[OperatorChainItem<'source>] {
        &self.items
    }

    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum OperatorChainItem<'source> {
    PrefixUse(OperatorUse<'source>),
    Primary(PrimaryExpression<'source>),
    NullfixUse(OperatorUse<'source>),
    InfixUse(OperatorUse<'source>),
    SuffixUse(OperatorUse<'source>),
    TerminalOuter(TerminalOuterTail<'source>),
    MissingOperand { range: Range<usize> },
    Error { range: Range<usize> },
}

/// A terminal structural continuation that is associated only after the
/// preceding source-order dynamic operator segment has been reduced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TerminalOuterTail<'source> {
    ColonApplication(ColonApplicationTail<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ColonApplicationTail<'source> {
    colon: Range<usize>,
    rhs: Recovered<ColonApplicationRhs<'source>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ColonApplicationRhs<'source> {
    Inline {
        arguments: Vec<Recovered<OperatorChain<'source>>>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OperatorRole {
    Prefix,
    Infix,
    Suffix,
    Nullfix,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorUse<'source> {
    text: &'source str,
    range: Range<usize>,
    role: OperatorRole,
}

impl<'source> OperatorUse<'source> {
    pub(crate) fn text(&self) -> &'source str { self.text }
    pub(crate) fn range(&self) -> Range<usize> { self.range.clone() }
    pub(crate) fn role(&self) -> OperatorRole { self.role }
}

/// A primary expression; dynamic operator structure lives in [`OperatorChain`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum PrimaryExpression<'source> {
    Identifier(WordSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Parenthesized {
        elements: Vec<OperatorChain<'source>>,
        trailing_comma: Option<Range<usize>>,
        range: Range<usize>,
    },
}

pub(crate) type Expression<'source> = PrimaryExpression<'source>;

impl PrimaryExpression<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        match self {
            Self::Identifier(identifier) => identifier.range(),
            Self::Integer(integer) => integer.range(),
            Self::Parenthesized { range, .. } => range.clone(),
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
) -> Option<OperatorChain<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_operator_chain(table, i)
}

/// Minimal metadata retained by the direct flat-chain continuation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParsedExpression<C> {
    range: Range<usize>,
    marker: PhantomData<C>,
}

impl<C> ParsedExpression<C> {
    fn new(range: Range<usize>) -> Self {
        Self { range, marker: PhantomData }
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
    parse_direct_operator_chain(table, leading, committed)
}

fn parse_operator_chain<'source, E>(
    table: &OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<OperatorChain<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let mut items = Vec::new();
    let mut leading = leading_trivia(&consume_trivia(&mut i)?);
    loop {
        let nud = i.run(from_fn(|i| recognize_nud(table, leading, i)))?;
        match nud {
            NudRecognition::Prefix(operator) => {
                items.push(OperatorChainItem::PrefixUse(operator_use(&operator, OperatorRole::Prefix)));
                leading = LeadingTrivia::None;
            }
            NudRecognition::Parenthesized { open } => {
                i.cut();
                push_parenthesized_expression_scope(&mut i);
                consume_trivia(&mut i).expect("trivia scanning is total");
                let mut elements = Vec::new();
                let mut trailing_comma = None;
                let close = if let Some(close) = i.run(recognize_parenthesized_close) {
                    close
                } else {
                    loop {
                        elements.push(i.run(from_fn(|i| parse_operator_chain(table, i)))?);
                        consume_trivia(&mut i).expect("trivia scanning is total");
                        let Some(comma) = i.run(recognize_parenthesized_comma) else {
                            break i.run(recognize_parenthesized_close)?;
                        };
                        consume_trivia(&mut i).expect("trivia scanning is total");
                        if let Some(close) = i.run(recognize_parenthesized_close) {
                            trailing_comma = Some(comma);
                            break close;
                        }
                    }
                };
                pop_parenthesized_expression_scope(&mut i);
                items.push(OperatorChainItem::Primary(PrimaryExpression::Parenthesized {
                    elements, trailing_comma, range: open.start..close.end,
                }));
                break;
            }
            NudRecognition::Identifier(identifier) => {
                items.push(OperatorChainItem::Primary(PrimaryExpression::Identifier(identifier)));
                break;
            }
            NudRecognition::Integer(integer) => {
                items.push(OperatorChainItem::Primary(PrimaryExpression::Integer(integer)));
                break;
            }
            NudRecognition::Nullfix(operator) => {
                items.push(OperatorChainItem::NullfixUse(operator_use(&operator, OperatorRole::Nullfix)));
                break;
            }
        }
    }

    loop {
        if let Some(colon) = i.run(recognize_colon_application_tail) {
            i.cut();
            let colon_start = colon.colon.start;
            if trivia_has_physical_newline(&colon.post_colon) {
                items.push(OperatorChainItem::TerminalOuter(
                    TerminalOuterTail::ColonApplication(ColonApplicationTail {
                        colon: colon.colon.clone(),
                        rhs: Recovered::Incomplete,
                        range: colon_start..colon.colon.end,
                    }),
                ));
                break;
            }
            let outer_owns_comma = active_stop_set(&i).contains(StopKind::Comma);
            let arguments = if outer_owns_comma {
                vec![Recovered::Complete(i.run(from_fn(|i| parse_operator_chain(table, i)))?)]
            } else {
                let stop_set = active_stop_set(&i).with(StopKind::Comma);
                i.local.push_stop_set(stop_set);
                let arguments = parse_inline_colon_arguments(table, &mut i);
                assert_eq!(i.local.pop_stop_set(), Some(stop_set));
                arguments?
            };
            let end = arguments
                .last()
                .and_then(|argument| match argument {
                    Recovered::Complete(chain) => Some(chain.range.end),
                    Recovered::Incomplete => None,
                })
                .unwrap_or(colon.colon.end);
            items.push(OperatorChainItem::TerminalOuter(TerminalOuterTail::ColonApplication(
                ColonApplicationTail {
                    colon: colon.colon,
                    rhs: Recovered::Complete(ColonApplicationRhs::Inline { arguments }),
                    range: colon_start..end,
                },
            )));
            break;
        }

        let Some(tail) = i.run(from_fn(|i| recognize_led(table, i)))? else {
            break;
        };
        match tail {
            LedRecognition::Infix { operator, .. } => {
                i.cut();
                items.push(OperatorChainItem::InfixUse(operator_use(&operator, OperatorRole::Infix)));
                items.extend(i.run(from_fn(|i| parse_operator_chain_operand(table, i)))?);
            }
            LedRecognition::Suffix { operator, .. } => {
                items.push(OperatorChainItem::SuffixUse(operator_use(&operator, OperatorRole::Suffix)));
            }
        }
    }
    let end = items.last().map_or(start, operator_chain_item_end);
    Some(OperatorChain::new(items, start..end))
}

fn parse_operator_chain_operand<'source, E>(
    table: &OperatorTable,
    i: SynIn<'_, 'source, '_, E>,
) -> Option<Vec<OperatorChainItem<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    Some(parse_operator_chain(table, i)?.items)
}

fn operator_chain_item_end(item: &OperatorChainItem<'_>) -> usize {
    match item {
        OperatorChainItem::PrefixUse(operator) | OperatorChainItem::NullfixUse(operator)
        | OperatorChainItem::InfixUse(operator) | OperatorChainItem::SuffixUse(operator) => operator.range.end,
        OperatorChainItem::Primary(primary) => primary.range().end,
        OperatorChainItem::TerminalOuter(TerminalOuterTail::ColonApplication(tail)) => tail.range.end,
        OperatorChainItem::MissingOperand { range } | OperatorChainItem::Error { range } => range.end,
    }
}

fn operator_use<'source>(operator: &ScannedOperator<'source>, role: OperatorRole) -> OperatorUse<'source> {
    OperatorUse { text: operator.text(), range: operator.range(), role }
}

/// Sink-free NUD result shared by AST tests and the direct continuation.
#[derive(Clone, Debug, Eq, PartialEq)]
enum NudRecognition<'source> {
    Parenthesized { open: Range<usize> },
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
    },
    Suffix {
        leading: TriviaRun,
        operator: ScannedOperator<'source>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ColonApplicationRecognition {
    leading: TriviaRun,
    colon: Range<usize>,
    post_colon: TriviaRun,
}

fn parse_inline_colon_arguments<'source, E>(
    table: &OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Vec<Recovered<OperatorChain<'source>>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut arguments = vec![Recovered::Complete(i.run(from_fn(|i| parse_operator_chain(table, i)))?)];
    loop {
        let trivia = consume_trivia(i)?;
        let Some(_) = i.run(recognize_parenthesized_comma) else {
            return Some(arguments);
        };
        consume_trivia(i)?;
        arguments.push(Recovered::Complete(i.run(from_fn(|i| parse_operator_chain(table, i)))?));
        let _ = trivia;
    }
}

/// Recognizes the one terminal fixed-punctuation continuation. `scan_punctuation`
/// tries `::` before `:`, so a use-path separator can never be split here.
fn recognize_colon_application_tail<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ColonApplicationRecognition>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.local.ml_arg() || active_stop_set(&i).contains(StopKind::Colon) {
        return None;
    }

    let checkpoint = i.checkpoint();
    let leading = consume_trivia(&mut i)?;
    if !trivia_continues_chain(&leading, &i) {
        i.rollback(checkpoint);
        return None;
    }
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() != PunctuationKind::Colon {
        i.rollback(checkpoint);
        return None;
    }
    let post_colon = consume_trivia(&mut i)?;
    Some(ColonApplicationRecognition {
        leading,
        colon: punctuation.range(),
        post_colon,
    })
}

fn active_stop_set<E>(i: &SynIn<E>) -> StopSet
where
    E: ErrorSink<usize>,
{
    i.local.stop_set().unwrap_or_default()
}

fn trivia_continues_chain<E>(trivia: &TriviaRun, i: &SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
{
    !trivia_has_physical_newline(trivia)
        || i.local.line().line_indent
            > i.local
                .indentation_baseline()
                .map_or(0, |baseline| baseline.column)
}

fn trivia_has_physical_newline(trivia: &TriviaRun) -> bool {
    trivia
        .parts()
        .iter()
        .any(|part| matches!(part.kind(), crate::scan::trivia::TriviaPartKind::Newline))
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
        recognize_parenthesized_open.map(|open| NudRecognition::Parenthesized { open }),
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

fn recognize_parenthesized_open<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Range<usize>>
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

fn recognize_parenthesized_close<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Range<usize>>
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

fn recognize_parenthesized_comma<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    let comma = (punctuation.kind() == PunctuationKind::Comma).then(|| punctuation.range());
    if comma.is_none() {
        i.rollback(checkpoint);
    }
    comma
}

fn recognize_led<'source, E>(
    table: &OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Option<LedRecognition<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.maybe(from_fn(|i| scan_led(table, i)))
}

fn scan_led<'source, E>(
    table: &OperatorTable,
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

    match scanned.fixity() {
        ScannedFixity::Infix { .. } => Some(LedRecognition::Infix { leading, operator: scanned }),
        ScannedFixity::Suffix { .. } => Some(LedRecognition::Suffix { leading, operator: scanned }),
        ScannedFixity::Prefix { .. } | ScannedFixity::Nullfix => None,
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

fn parse_direct_operator_chain<'parse, 'source, 'local, E, O>(
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
    let start = committed_position(committed);
    let nud = committed.probe(|probe| probe_nud(table, leading, probe));
    if nud.is_none() {
        let (range, trailing) = committed.probe(|probe| {
            let checkpoint = probe.input().checkpoint();
            let recovered = probe_dangling_prefix(table, probe);
            if recovered.is_none() {
                probe.input().rollback(checkpoint);
            }
            recovered
        })?;
        cut_after_acceptance(committed);
        committed.start_node(SyntaxKind::OperatorChain);
        emit_operator_range(committed, SyntaxKind::PrefixOperatorUse, range);
        committed.emit_trivia(&trailing);
        emit_expression_missing(committed);
        committed.finish_node();
        return Some(ParsedExpression::new(start..committed_position(committed)));
    }
    committed.start_node(SyntaxKind::OperatorChain);
    commit_direct_operand_slot_from(table, nud.expect("checked above"), committed)?;
    loop {
        if let Some(colon) = committed.probe(|probe| {
            probe.input().run(recognize_colon_application_tail)
        }) {
            cut_after_acceptance(committed);
            commit_colon_application_tail(table, colon, committed);
            break;
        }

        let Some(led) = committed.probe(|probe| probe_led(table, probe)) else {
            break;
        };
        cut_after_acceptance(committed);
        match led {
            LedRecognition::Infix { leading, operator } => {
                committed.emit_trivia(&leading);
                emit_operator_use(committed, SyntaxKind::InfixOperatorUse, &operator);
                committed.emit_trivia(operator.trailing_trivia());
                if commit_direct_operand_slot(table, committed, LeadingTrivia::None).is_none() {
                    emit_expression_missing(committed);
                    break;
                }
            }
            LedRecognition::Suffix { leading, operator } => {
                committed.emit_trivia(&leading);
                emit_operator_use(committed, SyntaxKind::SuffixOperatorUse, &operator);
                committed.emit_trivia(operator.trailing_trivia());
            }
        }
    }
    if let Some((leading, range, trailing)) = committed.probe(|probe| {
        let checkpoint = probe.input().checkpoint();
        let recovered = probe_dangling_infix(table, probe);
        if recovered.is_none() {
            probe.input().rollback(checkpoint);
        }
        recovered
    }) {
        cut_after_acceptance(committed);
        committed.emit_trivia(&leading);
        emit_operator_range(committed, SyntaxKind::InfixOperatorUse, range);
        committed.emit_trivia(&trailing);
        emit_expression_missing(committed);
    }
    let end = committed_position(committed);
    committed.finish_node();
    Some(ParsedExpression::new(start..end))
}

/// Emits an accepted terminal colon tail. The target remains a sibling of this
/// node in the enclosing flat chain; only the colon and its RHS live here.
fn commit_colon_application_tail<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    colon: ColonApplicationRecognition,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.emit_trivia(&colon.leading);
    committed.start_node(SyntaxKind::ColonApplicationTail);
    committed.token(SyntaxKind::Colon, colon.colon);
    committed.emit_trivia(&colon.post_colon);

    if trivia_has_physical_newline(&colon.post_colon) {
        // `IndentedStatementBlock` is deliberately deferred. Until that
        // follow-up slice exists, newline-after-colon commits this tail but
        // recovers its mandatory inline RHS instead of opening a block.
        emit_colon_application_missing(committed, ColonApplicationRole::Rhs);
        committed.finish_node();
        return;
    }

    let outer_owns_comma = committed.probe(|probe| {
        active_stop_set(probe.input()).contains(StopKind::Comma)
    });
    if outer_owns_comma {
        commit_colon_inline_argument(
            table,
            leading_trivia(&colon.post_colon),
            ColonApplicationRole::Rhs,
            committed,
        );
    } else {
        let stop_set = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Comma));
        committed.probe(|probe| probe.input().local.push_stop_set(stop_set));
        commit_colon_inline_argument(
            table,
            leading_trivia(&colon.post_colon),
            ColonApplicationRole::Rhs,
            committed,
        );

        while let Some(comma) = commit_parenthesized_comma(committed) {
            committed.token(SyntaxKind::Comma, comma);
            let leading = commit_parenthesized_trivia(committed)
                .expect("trivia scanning is total");
            committed.emit_trivia(&leading);
            commit_colon_inline_argument(
                table,
                leading_trivia(&leading),
                ColonApplicationRole::InlineArgument,
                committed,
            );
        }
        committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stop_set)));
    }
    committed.finish_node();
}

/// A colon-owned comma makes every following position mandatory; unlike a
/// parenthesized list, a terminal comma has no valid trailing-comma marker.
fn commit_colon_inline_argument<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    role: ColonApplicationRole,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if parse_direct_operator_chain(table, leading, committed).is_some() {
        return;
    }
    if colon_inline_argument_error_retry(table, role, committed) {
        parse_direct_operator_chain(table, LeadingTrivia::None, committed)
            .expect("a retried colon argument must commit its shared NUD candidate");
    } else {
        emit_colon_application_missing(committed, role);
    }
}

fn colon_inline_argument_error_retry<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    role: ColonApplicationRole,
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
            let i = probe.input();
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < end).then_some((start..end, false));
            };
            if matches!(character, ')' | ']' | '}' | ';' | ',') {
                return (start < end).then_some((start..end, false));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            if direct_expression_nud_candidate(table, LeadingTrivia::None, probe) {
                return Some((start..end, true));
            }
        }
    });
    let Some((range, retry)) = recovered else {
        return false;
    };
    emit_colon_application_error(committed, role, range);
    retry
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
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> Option<LedRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    probe
        .input()
        .run(from_fn(|i| recognize_led(table, i)))?
}

fn cut_after_acceptance<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| probe.input().cut());
}

fn commit_direct_operand_slot<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    leading: LeadingTrivia,
) -> Option<()>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let accepted = committed.probe(|probe| probe_nud(table, leading, probe))?;
    commit_direct_operand_slot_from(table, accepted, committed)
}

fn commit_direct_operand_slot_from<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    mut accepted: NudRecognition<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<()>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    loop {
        match accepted {
        NudRecognition::Parenthesized { open } => {
            cut_after_acceptance(committed);
            commit_parenthesized_nud(table, open, committed)?;
            return Some(());
        }
        NudRecognition::Identifier(identifier) => {
            let range = identifier.range();
            committed.start_node(SyntaxKind::IdentifierExpression);
            committed.token(SyntaxKind::Identifier, range.clone());
            committed.finish_node();
            return Some(());
        }
        NudRecognition::Integer(integer) => {
            let range = integer.range();
            committed.start_node(SyntaxKind::IntegerLiteral);
            committed.token(SyntaxKind::Integer, range.clone());
            committed.finish_node();
            return Some(());
        }
            NudRecognition::Prefix(operator) => {
            cut_after_acceptance(committed);
            emit_operator_use(committed, SyntaxKind::PrefixOperatorUse, &operator);
            committed.emit_trivia(operator.trailing_trivia());
            accepted = committed.probe(|probe| probe_nud(table, LeadingTrivia::None, probe))?;
        }
        NudRecognition::Nullfix(operator) => {
            emit_operator_use(committed, SyntaxKind::NullfixOperatorUse, &operator);
            committed.emit_trivia(operator.trailing_trivia());
            return Some(());
        }
        }
    }
}

fn emit_operator_use<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    kind: SyntaxKind,
    operator: &ScannedOperator<'source>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.start_node(kind);
    committed.token(SyntaxKind::Operator, operator.range());
    committed.finish_node();
}

fn emit_operator_range<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    kind: SyntaxKind,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.start_node(kind);
    committed.token(SyntaxKind::Operator, range);
    committed.finish_node();
}

/// Recovery-only recognition preserves one unambiguous dangling infix use.
fn probe_dangling_infix<'parse, 'source, 'local, E>(
    table: &OperatorTable,
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> Option<(TriviaRun, Range<usize>, TriviaRun)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let i = probe.input();
    let leading = consume_trivia(i)?;
    let remainder = i.input.remainder();
    let entry = table
        .entries_with_sites()
        .map(|(entry, _)| entry)
        .filter(|entry| remainder.starts_with(entry.spelling()))
        .max_by_key(|entry| entry.spelling().len())?;
    let fixities = entry.fixities();
    (fixities.infix().is_some() && fixities.suffix().is_none()).then_some(())?;
    let start = i.pos();
    for _ in entry.spelling().chars() {
        i.input.next()?;
    }
    let end = i.pos();
    let trailing = consume_trivia(i)?;
    (i.input.remainder().is_empty() || i.input.remainder().starts_with(')')).then_some(())?;
    Some((leading, start..end, trailing))
}

fn probe_dangling_prefix<'parse, 'source, 'local, E>(
    table: &OperatorTable,
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> Option<(Range<usize>, TriviaRun)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let i = probe.input();
    let remainder = i.input.remainder();
    let entry = table
        .entries_with_sites()
        .map(|(entry, _)| entry)
        .filter(|entry| remainder.starts_with(entry.spelling()))
        .max_by_key(|entry| entry.spelling().len())?;
    let fixities = entry.fixities();
    (fixities.prefix().is_some() && !fixities.is_nullfix()).then_some(())?;
    let start = i.pos();
    for _ in entry.spelling().chars() {
        i.input.next()?;
    }
    let end = i.pos();
    let trailing = consume_trivia(i)?;
    (i.input.remainder().is_empty() || i.input.remainder().starts_with(')')).then_some(())?;
    Some((start..end, trailing))
}

/// Completes an accepted parenthesized expression without returning to the
/// NUD choice. The committed CST node owns the complete delimiter and list
/// shape, including recovery for a mandatory element after a comma.
fn commit_parenthesized_nud<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<()>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::ParenthesizedExpression);
    committed.token(SyntaxKind::LParen, open.clone());
    push_direct_parenthesized_expression_scope(committed);

    let leading = commit_parenthesized_trivia(committed).expect("trivia scanning is total");
    committed.emit_trivia(&leading);
    let mut delayed_initial_element_missing = None;

    if !parenthesized_close_pending(committed) && !parenthesized_close_absent_boundary(committed) {
        let element_start = committed_position(committed);
        let element =
            commit_parenthesized_element(table, leading_trivia(&leading), committed);
        if element.is_none() {
            let at = committed_position(committed);
            if element_start < at && parenthesized_close_absent_boundary(committed) {
                delayed_initial_element_missing = Some(at);
            } else {
                emit_expression_missing(committed);
            }
        }

        while let Some(comma) = commit_parenthesized_comma(committed) {
            committed.token(SyntaxKind::Comma, comma);
            let leading = commit_parenthesized_trivia(committed).expect("trivia scanning is total");
            committed.emit_trivia(&leading);
            if parenthesized_close_pending(committed) {
                break;
            }

            let element =
                commit_parenthesized_element(table, leading_trivia(&leading), committed);
            if element.is_none() {
                emit_expression_missing(committed);
            }
        }
    }

    let close = commit_parenthesized_close(committed);
    match close {
        ParenthesizedClose::Matched(range) => {
            committed.token(SyntaxKind::RParen, range.clone());
            pop_direct_parenthesized_expression_scope(committed);
            committed.finish_node();
            Some(())
        }
        ParenthesizedClose::Missing { at } => {
            if delayed_initial_element_missing == Some(at) {
                emit_parenthesized_element_and_close_missing(committed, at);
            } else {
                emit_parenthesized_close_missing(committed, at);
            }
            pop_direct_parenthesized_expression_scope(committed);
            committed.finish_node();
            Some(())
        }
    }
}

fn commit_parenthesized_element<'parse, 'source, 'local, E, O>(
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
    parse_direct_operator_chain(table, leading, committed).or_else(|| {
        parenthesized_element_error_retry(table, committed).then(|| {
            parse_direct_operator_chain(table, LeadingTrivia::None, committed)
                .expect("a retried parenthesized element must commit its shared NUD candidate")
        })
    })
}

/// A mandatory list element owns invalid bytes only until a shared NUD
/// candidate or a parenthesized-list boundary; it never hands them back to
/// an outer declaration body recovery.
fn parenthesized_element_error_retry<'parse, 'source, 'local, E, O>(
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
    emit_parenthesized_error(
        committed,
        GrammarRole::Expression(ExpressionRole::Nud),
        range,
    );
    retry
}

enum ParenthesizedClose {
    Matched(Range<usize>),
    Missing { at: usize },
}

/// The closing mandatory slot follows the closing-delimiter rule. A wrong
/// close is emitted as its own non-empty episode, then the same close slot
/// keeps searching rather than returning failure to the NUD dispatcher.
fn commit_parenthesized_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> ParenthesizedClose
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    loop {
        if parenthesized_close_absent_boundary(committed) {
            return ParenthesizedClose::Missing {
                at: committed_position(committed),
            };
        }

        let punctuation = committed.probe(|probe| probe.input().run(scan_punctuation));
        if let Some(punctuation) = punctuation {
            match punctuation.kind() {
                PunctuationKind::Close(Delimiter::Parenthesis) => {
                    return ParenthesizedClose::Matched(punctuation.range());
                }
                PunctuationKind::Close(actual @ (Delimiter::Bracket | Delimiter::Brace)) => {
                    emit_parenthesized_close_error(committed, punctuation.range(), actual);
                }
                _ => emit_parenthesized_error(
                    committed,
                    parenthesized_close_role(),
                    punctuation.range(),
                ),
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
                    if matches!(character, ')' | ']' | '}' | ';') {
                        return (start < end).then_some(start..end);
                    }
                    i.input
                        .next()
                        .expect("the scanned parenthesized-close byte exists");
                    end = i.pos();
                    let mut line = i.local.line();
                    line.at_line_start = false;
                    i.local.set_line(line);
                }
            })
            .expect("a non-boundary parenthesized-close position must consume invalid source");
        emit_parenthesized_error(committed, parenthesized_close_role(), range);
    }
}

fn commit_parenthesized_trivia<'parse, 'source, 'local, E, O>(
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

fn parenthesized_close_pending<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let pending = i.run(recognize_parenthesized_close).is_some();
        i.rollback(checkpoint);
        pending
    })
}

fn commit_parenthesized_comma<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| probe.input().run(recognize_parenthesized_comma))
}

fn parenthesized_close_absent_boundary<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| {
        probe.input().input.remainder().is_empty()
            || matches!(probe.input().input.remainder().chars().next(), Some(';'))
    })
}

fn parenthesized_close_role() -> GrammarRole {
    GrammarRole::ClosingDelimiter {
        owner: ConstructRole::ExpressionGroup,
        delimiter: Delimiter::Parenthesis,
    }
}

fn emit_expression_missing<'parse, 'source, 'local, E, O>(
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

fn emit_colon_application_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    colon_role: ColonApplicationRole,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::ColonApplication(colon_role);
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

fn emit_colon_application_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    colon_role: ColonApplicationRole,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let role = GrammarRole::ColonApplication(colon_role);
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
                expected: ExpectedSyntax::Expression,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn emit_parenthesized_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    at: usize,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let role = parenthesized_close_role();
    emit_parenthesized_missing(
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

fn emit_parenthesized_element_and_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    at: usize,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let close_role = parenthesized_close_role();
    let element_role = GrammarRole::Expression(ExpressionRole::Nud);
    emit_parenthesized_missing(
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
                role: element_role,
                expected: ExpectedSyntax::Expression,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            },
        ]),
    );
}

fn emit_parenthesized_missing<'parse, 'source, 'local, E, O>(
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

fn emit_parenthesized_close_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
    actual: Delimiter,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let role = parenthesized_close_role();
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

fn emit_parenthesized_error<'parse, 'source, 'local, E, O>(
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
        _ => unreachable!("parenthesized recovery only emits element or close roles"),
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

fn parenthesized_expression_stop_set() -> StopSet {
    StopSet::default()
        .with(StopKind::Comma)
        .with(StopKind::RightParenthesis)
}

fn push_parenthesized_expression_scope<E>(i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    i.local.push_delimiter(Delimiter::Parenthesis);
    i.local.push_stop_set(parenthesized_expression_stop_set());
}

fn pop_parenthesized_expression_scope<E>(i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    assert_eq!(
        i.local.pop_stop_set(),
        Some(parenthesized_expression_stop_set())
    );
}

fn push_direct_parenthesized_expression_scope<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| push_parenthesized_expression_scope(probe.input()));
}

fn pop_direct_parenthesized_expression_scope<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| pop_parenthesized_expression_scope(probe.input()));
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
        operator::{BindingPower, OperatorDeclaration, OperatorFixities},
        session::{CommittedRecoveryRecord, FullCstOutput, ParseLocal, Probe},
    };

    #[test]
    fn operator_chain_ast_preserves_parenthesized_element_counts_and_trailing_commas() {
        let cases = [
            ("()", 0, None, 0..2),
            ("(a)", 1, None, 0..3),
            ("(a,)", 1, Some(2..3), 0..4),
            ("(a,b)", 2, None, 0..5),
            ("(a,b,)", 2, Some(4..5), 0..6),
        ];

        for (source, expected_element_count, expected_trailing_comma, expected_range) in cases {
            let chain = parse(source, &canonical_operator_table());
            let [OperatorChainItem::Primary(PrimaryExpression::Parenthesized {
                elements,
                trailing_comma,
                range,
            })] = chain.items()
            else {
                panic!("expected parenthesized expression for {source:?}");
            };

            assert_eq!(elements.len(), expected_element_count, "{source:?}");
            assert_eq!(*trailing_comma, expected_trailing_comma, "{source:?}");
            assert_eq!(*range, expected_range, "{source:?}");
        }
    }

    #[test]
    fn operator_chain_ast_builds_nested_parenthesized_expressions() {
        let chain = parse("((a))", &canonical_operator_table());
        let [OperatorChainItem::Primary(PrimaryExpression::Parenthesized {
            elements,
            trailing_comma,
            range,
        })] = chain.items()
        else {
            panic!("expected outer parenthesized expression");
        };
        assert_eq!(*range, 0..5);
        assert_eq!(*trailing_comma, None);
        let [OperatorChain {
            items,
            range: inner_chain_range,
        }] = elements.as_slice() else {
            panic!("expected one nested chain");
        };
        assert_eq!(*inner_chain_range, 1..4);
        let [OperatorChainItem::Primary(PrimaryExpression::Parenthesized {
                elements,
                trailing_comma,
                range,
            })] = items.as_slice()
        else {
            panic!("expected one nested parenthesized element");
        };
        assert_eq!(*range, 1..4);
        assert_eq!(*trailing_comma, None);
        assert!(matches!(
            elements.as_slice(),
            [OperatorChain { items, .. }]
                if matches!(items.as_slice(), [OperatorChainItem::Primary(PrimaryExpression::Identifier(_))])
        ));
    }

    #[test]
    fn nud_role_selection_splits_long_infix_into_prefix_and_nullfix_uses() {
        let table = canonical_operator_table();
        let chain = parse("+!a", &table);
        assert!(matches!(
            chain.items(),
            [
                OperatorChainItem::PrefixUse(plus),
                OperatorChainItem::PrefixUse(bang),
                OperatorChainItem::Primary(PrimaryExpression::Identifier(identifier)),
            ] if plus.text() == "+" && plus.range() == (0..1)
                && bang.text() == "!" && bang.range() == (1..2)
                && identifier.text() == "a" && identifier.range() == (2..3)
        ));
    }

    #[test]
    fn led_role_selection_keeps_the_long_infix_use() {
        let table = canonical_operator_table();
        let chain = parse("a+!b", &table);
        assert!(matches!(
            chain.items(),
            [
                OperatorChainItem::Primary(PrimaryExpression::Identifier(left)),
                OperatorChainItem::InfixUse(operator),
                OperatorChainItem::Primary(PrimaryExpression::Identifier(right)),
            ] if left.text() == "a" && operator.text() == "+!" && operator.range() == (1..3)
                && right.text() == "b"
        ));
    }

    #[test]
    fn direct_nud_role_selection_emits_flat_prefix_uses_after_candidate_fallback() {
        let root = parse_direct("+!a", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(
            chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
            vec![SyntaxKind::PrefixOperatorUse, SyntaxKind::PrefixOperatorUse, SyntaxKind::IdentifierExpression]
        );
        assert_eq!(chain.children().nth(0).unwrap().first_token().unwrap().text(), "+");
        assert_eq!(chain.children().nth(1).unwrap().first_token().unwrap().text(), "!");
        assert_eq!(root.to_string(), "+!a");
    }

    #[test]
    fn direct_led_role_selection_emits_a_flat_infix_use() {
        let root = parse_direct("a+!b", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(
            chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
            vec![SyntaxKind::IdentifierExpression, SyntaxKind::InfixOperatorUse, SyntaxKind::IdentifierExpression]
        );
        let infix = chain.children().nth(1).unwrap();
        assert_eq!(direct_token_kinds(&infix), vec![SyntaxKind::Operator]);
        assert_eq!(infix.first_token().unwrap().text(), "+!");
    }

    #[test]
    fn direct_chain_assigns_accepted_led_trivia_once() {
        let root = parse_direct("a +! b", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);

        assert_eq!(
            chain
                .children_with_tokens()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            vec![
                SyntaxKind::IdentifierExpression,
                SyntaxKind::Whitespace,
                SyntaxKind::InfixOperatorUse,
                SyntaxKind::Whitespace,
                SyntaxKind::IdentifierExpression,
            ]
        );
        assert_eq!(root.to_string(), "a +! b");
    }

    #[test]
    fn direct_chain_emits_suffix_and_nullfix_use_nodes() {
        let table = canonical_operator_table();

        let suffix_root = parse_direct("a++", &table);
        let suffix_chain = only_child(&suffix_root, SyntaxKind::OperatorChain);
        let suffix = suffix_chain.children().nth(1).unwrap();
        assert_eq!(suffix.kind(), SyntaxKind::SuffixOperatorUse);
        assert_eq!(suffix_chain.to_string(), "a++");
        assert_eq!(
            suffix
                .children_with_tokens().map(|child| child.kind()).collect::<Vec<_>>(),
            vec![SyntaxKind::Operator]
        );

        let nullfix_root = parse_direct("!", &table);
        let nullfix_chain = only_child(&nullfix_root, SyntaxKind::OperatorChain);
        let nullfix = only_child(&nullfix_chain, SyntaxKind::NullfixOperatorUse);
        assert_eq!(nullfix_chain.to_string(), "!");
        assert_eq!(direct_token_kinds(&nullfix), vec![SyntaxKind::Operator]);
    }

    #[test]
    fn direct_chain_emits_parenthesized_trivia_and_nested_nodes_losslessly() {
        let source = "(\n/* note */ (a), b, \n)";
        let root = parse_direct(source, &canonical_operator_table());
        let outer_chain = only_child(&root, SyntaxKind::OperatorChain);
        let parenthesized = only_child(&outer_chain, SyntaxKind::ParenthesizedExpression);

        assert_eq!(parenthesized.to_string(), source);
        assert_eq!(
            parenthesized
                .children_with_tokens()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            vec![
                SyntaxKind::LParen,
                SyntaxKind::Newline,
                SyntaxKind::BlockComment,
                SyntaxKind::Whitespace,
                SyntaxKind::OperatorChain,
                SyntaxKind::Comma,
                SyntaxKind::Whitespace,
                SyntaxKind::OperatorChain,
                SyntaxKind::Comma,
                SyntaxKind::Whitespace,
                SyntaxKind::Newline,
                SyntaxKind::RParen,
            ]
        );
        assert_eq!(
            parenthesized.children().next().unwrap().children().next().unwrap().kind(),
            SyntaxKind::ParenthesizedExpression,
        );
    }

    #[test]
    fn direct_chain_uses_one_parenthesized_node_for_every_valid_list_shape() {
        let cases = [
            ("()", vec![SyntaxKind::LParen, SyntaxKind::RParen]),
            (
                "(a)",
                vec![
                    SyntaxKind::LParen,
                    SyntaxKind::OperatorChain,
                    SyntaxKind::RParen,
                ],
            ),
            (
                "(a,)",
                vec![
                    SyntaxKind::LParen,
                    SyntaxKind::OperatorChain,
                    SyntaxKind::Comma,
                    SyntaxKind::RParen,
                ],
            ),
            (
                "(a,b)",
                vec![
                    SyntaxKind::LParen,
                    SyntaxKind::OperatorChain,
                    SyntaxKind::Comma,
                    SyntaxKind::OperatorChain,
                    SyntaxKind::RParen,
                ],
            ),
            (
                "(a,b,)",
                vec![
                    SyntaxKind::LParen,
                    SyntaxKind::OperatorChain,
                    SyntaxKind::Comma,
                    SyntaxKind::OperatorChain,
                    SyntaxKind::Comma,
                    SyntaxKind::RParen,
                ],
            ),
        ];

        for (source, expected_children) in cases {
            let root = parse_direct(source, &canonical_operator_table());
            let chain = only_child(&root, SyntaxKind::OperatorChain);
            let parenthesized = only_child(&chain, SyntaxKind::ParenthesizedExpression);
            assert_eq!(parenthesized.to_string(), source, "{source:?}");
            assert_eq!(
                parenthesized
                    .children_with_tokens()
                    .map(|child| child.kind())
                    .collect::<Vec<_>>(),
                expected_children,
                "{source:?}"
            );
        }
    }

    #[test]
    fn parenthesized_primary_continues_to_outer_infix_and_suffix_uses() {
        let expression = parse("(a+!b)*c", &canonical_operator_table());
        assert!(matches!(
            expression.items(),
            [
                OperatorChainItem::Primary(PrimaryExpression::Parenthesized { elements, .. }),
                OperatorChainItem::InfixUse(operator),
                OperatorChainItem::Primary(PrimaryExpression::Identifier(_)),
            ] if operator.text() == "*" && matches!(elements.as_slice(), [OperatorChain { items, .. }]
                if matches!(items.as_slice(), [OperatorChainItem::Primary(_), OperatorChainItem::InfixUse(_), OperatorChainItem::Primary(_)]))
        ));
        let root = parse_direct("(a+!b)*c", &canonical_operator_table());
        let outer = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(
            outer.children().next().expect("left operand").kind(),
            SyntaxKind::ParenthesizedExpression
        );
        assert_eq!(outer.children().nth(1).unwrap().kind(), SyntaxKind::InfixOperatorUse);

        let suffix = parse_direct("(a)++", &canonical_operator_table());
        let suffix = only_child(&suffix, SyntaxKind::OperatorChain);
        assert_eq!(
            suffix.children().next()
                .expect("parenthesized operand")
                .kind(),
            SyntaxKind::ParenthesizedExpression
        );
        assert_eq!(suffix.children().nth(1).unwrap().kind(), SyntaxKind::SuffixOperatorUse);
    }

    #[test]
    fn operator_chain_ast_preserves_source_order_without_application_edges() {
        let chain = parse("+!a+!b++", &canonical_operator_table());
        assert_eq!(chain.range(), 0..8);
        assert!(matches!(
            chain.items(),
            [
                OperatorChainItem::PrefixUse(prefix),
                OperatorChainItem::PrefixUse(nested_prefix),
                OperatorChainItem::Primary(PrimaryExpression::Identifier(_)),
                OperatorChainItem::InfixUse(infix),
                OperatorChainItem::Primary(PrimaryExpression::Identifier(_)),
                OperatorChainItem::SuffixUse(suffix),
            ] if prefix.text() == "+" && nested_prefix.text() == "!" && infix.text() == "+!" && suffix.text() == "++"
        ));
    }

    #[test]
    fn direct_chain_emits_role_nodes_and_keeps_operator_trivia_outside_them() {
        let root = parse_direct("+!a +! b++", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(chain.to_string(), "+!a +! b++");
        assert_eq!(
            chain.children_with_tokens().map(|child| child.kind()).collect::<Vec<_>>(),
            vec![
                SyntaxKind::PrefixOperatorUse,
                SyntaxKind::PrefixOperatorUse,
                SyntaxKind::IdentifierExpression,
                SyntaxKind::Whitespace,
                SyntaxKind::InfixOperatorUse,
                SyntaxKind::Whitespace,
                SyntaxKind::IdentifierExpression,
                SyntaxKind::SuffixOperatorUse,
            ]
        );
        for use_kind in [
            SyntaxKind::PrefixOperatorUse,
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::SuffixOperatorUse,
        ] {
            for node in chain.children().filter(|node| node.kind() == use_kind) {
                assert_eq!(direct_token_kinds(&node), vec![SyntaxKind::Operator]);
            }
        }
    }

    #[test]
    fn colon_application_ast_and_cst_keep_inline_arguments_in_the_terminal_tail() {
        let chain = parse("f: x, y", &canonical_operator_table());
        assert!(matches!(
            chain.items(),
            [
                OperatorChainItem::Primary(PrimaryExpression::Identifier(target)),
                OperatorChainItem::TerminalOuter(TerminalOuterTail::ColonApplication(
                    ColonApplicationTail {
                        colon,
                        rhs: Recovered::Complete(ColonApplicationRhs::Inline { arguments }),
                        range,
                    }
                )),
            ] if target.text() == "f" && *colon == (1..2) && arguments.len() == 2 && *range == (1..7)
        ));

        let root = parse_direct("f: x, y", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        let tail = chain.children().nth(1).expect("terminal colon tail");
        assert_eq!(tail.kind(), SyntaxKind::ColonApplicationTail);
        assert_eq!(
            tail.children_with_tokens()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            vec![
                SyntaxKind::Colon,
                SyntaxKind::Whitespace,
                SyntaxKind::OperatorChain,
                SyntaxKind::Comma,
                SyntaxKind::Whitespace,
                SyntaxKind::OperatorChain,
            ]
        );
    }

    #[test]
    fn parenthesized_outer_comma_limits_a_colon_tail_to_one_argument() {
        let root = parse_direct("(f: x, y)", &canonical_operator_table());
        let outer = only_child(&root, SyntaxKind::OperatorChain);
        let group = only_child(&outer, SyntaxKind::ParenthesizedExpression);
        let elements = group
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .collect::<Vec<_>>();
        assert_eq!(elements.len(), 2);
        assert!(elements[0]
            .children()
            .any(|node| node.kind() == SyntaxKind::ColonApplicationTail));
        assert!(!elements[1]
            .children()
            .any(|node| node.kind() == SyntaxKind::ColonApplicationTail));
    }

    #[test]
    fn colon_application_recovery_keeps_commas_and_retries_valid_values() {
        let cases = [
            ("f:", vec![(RecoveryKind::Missing, 2..2)]),
            ("f: ,x", vec![(RecoveryKind::Missing, 3..3)]),
            ("f: x,", vec![(RecoveryKind::Missing, 5..5)]),
            ("f: @x", vec![(RecoveryKind::Error, 3..4)]),
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
            assert!(recoveries.iter().all(|recovery| {
                matches!(
                    recovery.site.role,
                    GrammarRole::ColonApplication(ColonApplicationRole::Rhs)
                        | GrammarRole::ColonApplication(ColonApplicationRole::InlineArgument)
                )
            }));
        }
    }

    #[test]
    fn newline_after_colon_is_temporarily_a_missing_inline_rhs() {
        let source = "my value = f:\n  x";
        let output = crate::grammar::declaration::parse_direct_root_candidate(
            source,
            &canonical_operator_table(),
            &[],
        );
        let root = SyntaxNode::new_root(output.green().clone());
        let tail = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .expect("colon tail");
        assert!(tail.children().any(|node| node.kind() == SyntaxKind::Missing));
        assert!(tail
            .children_with_tokens()
            .any(|child| child.kind() == SyntaxKind::Newline));
        assert_eq!(tail.to_string(), ":\n  ");
        assert_eq!(root.to_string(), source);
    }

    #[test]
    fn colon_tail_stays_flat_before_and_after_binding_power_changes() {
        let source = "a + b: x";
        let low = colon_operator_table(BindingPower::scalar(1));
        let high = colon_operator_table(BindingPower::scalar(99));

        let root = parse_direct(source, &low);
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(
            chain.children().map(|child| child.kind()).collect::<Vec<_>>(),
            vec![
                SyntaxKind::IdentifierExpression,
                SyntaxKind::InfixOperatorUse,
                SyntaxKind::IdentifierExpression,
                SyntaxKind::ColonApplicationTail,
            ]
        );
        assert_eq!(parse_direct(source, &low).green(), parse_direct(source, &high).green());
        assert_eq!(parse(source, &low), parse(source, &high));
    }

    #[test]
    fn binding_power_only_changes_do_not_change_surface_chain() {
        let source = "+!a+!b*c++";
        let low = canonical_operator_table();
        let high = OperatorTable::from_declarations([
            OperatorDeclaration::new("+!", OperatorFixities::new().with_infix(BindingPower::scalar(99), BindingPower::scalar(-99))),
            OperatorDeclaration::new("+", OperatorFixities::new().with_prefix(BindingPower::scalar(-90))),
            OperatorDeclaration::new("!", OperatorFixities::new().with_prefix(BindingPower::scalar(100)).with_nullfix()),
            OperatorDeclaration::new("++", OperatorFixities::new().with_suffix(BindingPower::scalar(-80))),
            OperatorDeclaration::new("*", OperatorFixities::new().with_infix(BindingPower::scalar(-70), BindingPower::scalar(70))),
        ]).expect("same recognition table");
        assert_eq!(parse_direct(source, &low).green(), parse_direct(source, &high).green());
        assert_eq!(parse(source, &low), parse(source, &high));
    }

    #[test]
    fn parenthesized_elements_are_operator_chains_and_outer_continues_flatly() {
        let chain = parse("(a+!b)*c", &canonical_operator_table());
        assert!(matches!(chain.items(), [
            OperatorChainItem::Primary(PrimaryExpression::Parenthesized { elements, .. }),
            OperatorChainItem::InfixUse(_),
            OperatorChainItem::Primary(PrimaryExpression::Identifier(_)),
        ] if matches!(elements.as_slice(), [OperatorChain { items, .. }] if matches!(items.as_slice(), [OperatorChainItem::Primary(_), OperatorChainItem::InfixUse(_), OperatorChainItem::Primary(_)]))));
        let root = parse_direct("(a+!b)*c", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert_eq!(chain.children().next().expect("primary").kind(), SyntaxKind::ParenthesizedExpression);
    }

    #[test]
    fn dangling_infix_preserves_the_use_and_emits_one_zero_width_missing_operand() {
        let (root, recoveries) = parse_direct_recovered("a+!", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert!(chain.children().any(|node| node.kind() == SyntaxKind::InfixOperatorUse));
        assert_eq!(
            recoveries.iter().map(|record| (record.kind, record.site.range.clone())).collect::<Vec<_>>(),
            vec![(RecoveryKind::Missing, 3..3)]
        );
    }

    #[test]
    fn dangling_prefix_preserves_the_use_and_emits_one_zero_width_missing_operand() {
        let (root, recoveries) = parse_direct_recovered("+", &canonical_operator_table());
        let chain = only_child(&root, SyntaxKind::OperatorChain);
        assert!(chain.children().any(|node| node.kind() == SyntaxKind::PrefixOperatorUse));
        assert_eq!(
            recoveries.iter().map(|record| (record.kind, record.site.range.clone())).collect::<Vec<_>>(),
            vec![(RecoveryKind::Missing, 1..1)]
        );
    }

    #[test]
    fn dangling_infix_stops_before_parenthesis_close() {
        let (root, recoveries) = parse_direct_recovered("(a+!)", &canonical_operator_table());
        assert_eq!(root.to_string(), "(a+!)");
        assert_eq!(
            recoveries.iter().map(|record| (record.kind, record.site.range.clone())).collect::<Vec<_>>(),
            vec![(RecoveryKind::Missing, 4..4)]
        );
    }

    #[test]
    fn direct_parenthesized_expression_recovers_mandatory_slots_without_duplicate_absences() {
        let cases = [
            ("()", Vec::new()),
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
            ("(a,,b)", vec![(RecoveryKind::Missing, 3..3)]),
            (
                "(a,",
                vec![(RecoveryKind::Missing, 3..3), (RecoveryKind::Missing, 3..3)],
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
        assert!(empty.is_empty());

        let (_, missing_close) = parse_direct_recovered("(value", &canonical_operator_table());
        assert_eq!(missing_close[0].site.role, parenthesized_close_role());

        let (_, mismatched) = parse_direct_recovered("(a]", &canonical_operator_table());
        assert_eq!(mismatched[0].site.role, parenthesized_close_role());
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
        assert_eq!(collapsed[0].site.role, parenthesized_close_role());
        assert_eq!(collapsed[0].expectations.len(), 1);

        let (_, invalid_at_eof) = parse_direct_recovered("(@", &canonical_operator_table());
        assert_eq!(invalid_at_eof[1].site.role, parenthesized_close_role());
        assert_eq!(invalid_at_eof[1].expectations.len(), 2);
    }

    #[test]
    fn parenthesized_probe_is_sink_free_and_committed_node_preserves_lossless_invariants() {
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

    fn colon_operator_table(binding_power: BindingPower) -> OperatorTable {
        OperatorTable::from_declarations([OperatorDeclaration::new(
            "+",
            OperatorFixities::new().with_infix(binding_power.clone(), binding_power),
        )])
        .expect("colon table should be valid")
    }

    fn parse<'source>(source: &'source str, table: &OperatorTable) -> OperatorChain<'source> {
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
