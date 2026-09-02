//! Standalone fixed-precedence Pratt grammar for Yulang patterns.
//!
//! This first slice deliberately has no production consumer.  Its fixed
//! primary/tail grammar is independent of expression operators and emits the
//! outer `Pattern` node forward, rather than wrapping an already-emitted left
//! operand for each tail.

use std::{marker::PhantomData, ops::Range, sync::Arc};

use chasa::{
    Back as _, ErrorSink, Input as _,
    error::std::{Unexpected, UnexpectedEndOfInput},
    parser::Parser as _,
    prelude::{from_fn, item},
};

use crate::{
    grammar::{
        declaration::Recovered,
        expression::{
            IntegerLiteral, OperatorChain, parse_direct_expression_with_operators,
            parse_expression_with_operators, parse_integer_literal,
        },
        type_expr::{
            RequiredTypeRecoveryContext, TypeExpression,
            commit_direct_type_expression_with_recovery_context,
            parse_required_type_expression_with_recovery_context,
        },
    },
    operator::OperatorTable,
    scan::{
        operator::LeadingTrivia,
        punctuation::{PunctuationKind, scan_punctuation},
        trivia::{TriviaRun, scan_trivia},
        word::{WordSpan, scan_word},
    },
    session::{
        CommitOutput, Committed, CommittedRecoveryRecord, ConstructRole, Delimiter,
        ExpectationSources, ExpectedSyntax, GrammarRole, IndentationBaseline,
        IndentationBaselineKind, LayoutDelimitedBoundary, LayoutDelimitedFrame, PatternRole, Probe,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, StopKind, StopSet, SynIn, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax, any_ambient_owner_claims,
    },
    syntax_kind::SyntaxKind,
};

/// A fixed pattern precedence.  It intentionally does not share expression
/// binding powers or an operator table.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum PatternPrecedence {
    Lowest = 0,
    TypeAnnotation = 1,
    Alternation = 2,
    Alias = 3,
}

/// Additional caller-owned boundaries for one mandatory Pattern slot.
///
/// Fresh-primary stops apply before the slot has accepted a NUD.  Recovered
/// primary-tail stops apply only after that outermost NUD's own delimited
/// close recovery consumed an error episode; recursive Pattern entries keep
/// using the default policy and therefore retain their ordinary tails.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct PatternMandatorySlotPolicy {
    pub(crate) fresh_primary_recovery_stops: StopSet,
    pub(crate) recovered_primary_tail_stops: StopSet,
}

/// The two pattern primaries with the same comma-delimited container contract.
///
/// This stays a closed policy rather than becoming a generic public AST: the
/// delimiters share recovery mechanics, but their item grammars and semantic
/// projections remain distinct.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PatternDelimitedPolicy {
    Parenthesized,
    List,
    Record,
}

/// One sink-free decision in ParenthesizedPattern's post-item close recovery.
/// `Complete` and `Error` consume exactly the bytes reported; `Missing` keeps
/// the caller-owned terminal position untouched.
enum ParenthesizedPatternCloseRecoveryStep {
    Complete {
        close: Range<usize>,
    },
    Error {
        range: Range<usize>,
        unexpected: UnexpectedCategory,
    },
    Missing {
        at: usize,
    },
}

impl PatternDelimitedPolicy {
    fn delimiter(self) -> Delimiter {
        match self {
            Self::Parenthesized => Delimiter::Parenthesis,
            Self::List => Delimiter::Bracket,
            Self::Record => Delimiter::Brace,
        }
    }

    fn close_stop(self) -> StopKind {
        match self {
            Self::Parenthesized => StopKind::RightParenthesis,
            Self::List => StopKind::RightBracket,
            Self::Record => StopKind::RightBrace,
        }
    }

    fn close_syntax_kind(self) -> SyntaxKind {
        match self {
            Self::Parenthesized => SyntaxKind::RParen,
            Self::List => SyntaxKind::RBracket,
            Self::Record => SyntaxKind::RBrace,
        }
    }

    fn close_role(self) -> GrammarRole {
        match self {
            Self::Parenthesized => GrammarRole::ClosingDelimiter {
                owner: ConstructRole::ParenthesizedPattern,
                delimiter: Delimiter::Parenthesis,
            },
            Self::List => GrammarRole::ClosingDelimiter {
                owner: ConstructRole::ListPattern,
                delimiter: Delimiter::Bracket,
            },
            Self::Record => GrammarRole::ClosingDelimiter {
                owner: ConstructRole::RecordPattern,
                delimiter: Delimiter::Brace,
            },
        }
    }

    fn stop_set(self) -> StopSet {
        StopSet::default()
            .with(StopKind::Comma)
            .with(self.close_stop())
    }

    fn ast_next_item_pending<E>(self, i: &mut SynIn<E>) -> bool
    where
        E: ErrorSink<usize>,
        Unexpected<char>: Into<E::Error>,
        UnexpectedEndOfInput: Into<E::Error>,
    {
        match self {
            Self::Parenthesized => pattern_nud_candidate_input(i),
            Self::List => exact_dot_dot_pending_input(i) || pattern_nud_candidate_input(i),
            Self::Record => exact_dot_dot_pending_input(i) || pattern_name_pending_input(i),
        }
    }

    fn recover_ast_separator_or_close<E>(self, i: &mut SynIn<E>) -> bool
    where
        E: ErrorSink<usize>,
        Unexpected<char>: Into<E::Error>,
        UnexpectedEndOfInput: Into<E::Error>,
    {
        match self {
            Self::Parenthesized => false,
            Self::List => recover_list_separator_or_close_ast(i),
            Self::Record => recover_list_separator_or_close_ast(i),
        }
    }

    fn separator_role(self) -> PatternRole {
        match self {
            Self::Parenthesized => PatternRole::ParenthesizedSeparator,
            Self::List => PatternRole::ListSeparator,
            Self::Record => PatternRole::RecordSeparator,
        }
    }

    fn separator_expected(self) -> ExpectedSyntax {
        match self {
            Self::Record => ExpectedSyntax::DelimitedSequenceSeparator,
            Self::Parenthesized | Self::List => {
                ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Comma)
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Pattern<'source> {
    head: Recovered<PatternPrimary<'source>>,
    tails: Vec<PatternTail<'source>>,
    type_annotation: Option<PatternTypeAnnotation<'source>>,
    range: Range<usize>,
}

impl Pattern<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
    pub(crate) fn tails(&self) -> &[PatternTail<'_>] {
        &self.tails
    }
    pub(crate) fn type_annotation(&self) -> Option<&PatternTypeAnnotation<'_>> {
        self.type_annotation.as_ref()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PatternTypeAnnotation<'source> {
    colon: Range<usize>,
    type_expr: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}

impl PatternTypeAnnotation<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
    pub(crate) fn type_expr(&self) -> &Recovered<Box<TypeExpression<'_>>> {
        &self.type_expr
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum PatternPrimary<'source> {
    Identifier(PatternNameSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Symbol(SymbolPattern<'source>),
    Parenthesized(ParenthesizedPattern<'source>),
    List(ListPattern<'source>),
    Record(RecordPattern<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PatternNameSpan<'source> {
    text: &'source str,
    range: Range<usize>,
    lexical_kind: PatternNameKind,
}

impl<'source> PatternNameSpan<'source> {
    fn from_word(word: WordSpan<'source>, lexical_kind: PatternNameKind) -> Self {
        Self {
            text: word.text(),
            range: word.range(),
            lexical_kind,
        }
    }

    pub(crate) fn text(&self) -> &'source str {
        self.text
    }
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
    pub(crate) fn lexical_kind(&self) -> PatternNameKind {
        self.lexical_kind
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PatternNameKind {
    Ordinary,
    Sigil,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SymbolPattern<'source> {
    colon: Range<usize>,
    name: Recovered<WordSpan<'source>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParenthesizedPattern<'source> {
    open: Range<usize>,
    elements: Vec<Recovered<Pattern<'source>>>,
    trailing_comma: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ListPattern<'source> {
    open: Range<usize>,
    items: Vec<Recovered<ListPatternItem<'source>>>,
    trailing_comma: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

impl ListPattern<'_> {
    pub(crate) fn items(&self) -> &[Recovered<ListPatternItem<'_>>] {
        &self.items
    }

    pub(crate) fn trailing_comma(&self) -> Option<Range<usize>> {
        self.trailing_comma.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ListPatternItem<'source> {
    Pattern(Pattern<'source>),
    Spread(ListPatternSpreadItem<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ListPatternSpreadItem<'source> {
    marker: Range<usize>,
    rhs: Recovered<Box<Pattern<'source>>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RecordPattern<'source> {
    open: Range<usize>,
    items: Vec<Recovered<RecordPatternItem<'source>>>,
    trailing_comma: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

impl RecordPattern<'_> {
    pub(crate) fn items(&self) -> &[Recovered<RecordPatternItem<'_>>] {
        &self.items
    }
    pub(crate) fn trailing_comma(&self) -> Option<Range<usize>> {
        self.trailing_comma.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RecordPatternItem<'source> {
    Field(RecordPatternField<'source>),
    Spread(RecordPatternSpreadItem<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RecordPatternField<'source> {
    name: PatternNameSpan<'source>,
    form: RecordPatternFieldForm<'source>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RecordPatternFieldForm<'source> {
    Shorthand,
    Nested {
        colon: Range<usize>,
        pattern: Recovered<Box<Pattern<'source>>>,
        default: Option<RecordPatternDefault<'source>>,
    },
    Default(RecordPatternDefault<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RecordPatternDefault<'source> {
    equals: Range<usize>,
    expression: Recovered<Box<OperatorChain<'source>>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RecordPatternSpreadItem<'source> {
    marker: Range<usize>,
    rhs: Recovered<Box<Pattern<'source>>>,
    range: Range<usize>,
}

impl ParenthesizedPattern<'_> {
    pub(crate) fn elements(&self) -> &[Recovered<Pattern<'_>>] {
        &self.elements
    }
    pub(crate) fn trailing_comma(&self) -> Option<Range<usize>> {
        self.trailing_comma.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum PatternTail<'source> {
    Alias(PatternAliasTail<'source>),
    Alternation(PatternAlternationTail<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PatternAliasTail<'source> {
    keyword: WordSpan<'source>,
    binding: Recovered<WordSpan<'source>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PatternAlternationTail<'source> {
    pipe: Range<usize>,
    rhs: Recovered<Box<Pattern<'source>>>,
    range: Range<usize>,
}

/// Parses a standalone pattern AST.  Consumers will own surrounding stops and
/// delimiters in later grammar slices.
pub(crate) fn parse_pattern<'source, E>(
    table: &OperatorTable,
    i: SynIn<'_, 'source, '_, E>,
) -> Option<Pattern<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_pattern_with_outer_missing_role(table, None, i)
}

/// AST counterpart of [`parse_direct_pattern_with_outer_missing_role`].  AST
/// recovery has no committed diagnostic record, but sharing the entry keeps a
/// caller's outer-slot ownership explicit on both parser paths.
pub(crate) fn parse_pattern_with_outer_missing_role<'source, E>(
    table: &OperatorTable,
    _outer_missing_role: Option<GrammarRole>,
    i: SynIn<'_, 'source, '_, E>,
) -> Option<Pattern<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_pattern_bp(table, i, PatternPrecedence::Lowest)
}

/// Mandatory AST entry whose policy applies only before its first Pattern NUD.
pub(crate) fn parse_required_pattern_with_outer_missing_role_and_policy<'source, E>(
    table: &OperatorTable,
    _outer_missing_role: Option<GrammarRole>,
    policy: PatternMandatorySlotPolicy,
    i: SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<Pattern<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match parse_pattern_bp_with_fresh_primary_policy(table, i, PatternPrecedence::Lowest, policy) {
        Some(pattern) if matches!(pattern.head, Recovered::Complete(_)) => {
            Recovered::Complete(Box::new(pattern))
        }
        Some(_) | None => Recovered::Incomplete,
    }
}

/// Direct-CST counterpart of [`parse_pattern`].  `leading` is currently
/// retained only for the shared entrypoint shape: patterns do not use it for
/// fixed NUD recognition.
pub(crate) fn parse_direct_pattern<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    leading: LeadingTrivia,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedPattern<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_direct_pattern_with_outer_missing_role(table, leading, None, committed)
}

/// Direct pattern entry for a construct that owns only the outermost absent
/// pattern slot.  Recursive pattern grammar continues to use its own typed
/// [`PatternRole`] sites.
pub(crate) fn parse_direct_pattern_with_outer_missing_role<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    _leading: LeadingTrivia,
    outer_missing_role: Option<GrammarRole>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedPattern<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_direct_pattern_bp(
        table,
        PatternPrecedence::Lowest,
        PatternRole::Primary,
        outer_missing_role.unwrap_or_else(|| pattern_role(PatternRole::Primary)),
        committed,
    )
}

/// Direct-CST counterpart of
/// [`parse_required_pattern_with_outer_missing_role_and_policy`].
pub(crate) fn commit_direct_pattern_with_outer_missing_role_and_policy<
    'parse,
    'source,
    'local,
    E,
    O,
>(
    table: &OperatorTable,
    _leading: LeadingTrivia,
    outer_missing_role: Option<GrammarRole>,
    policy: PatternMandatorySlotPolicy,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> ParsedPattern<O::Checkpoint>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_direct_pattern_bp_with_fresh_primary_policy(
        table,
        PatternPrecedence::Lowest,
        PatternRole::Primary,
        outer_missing_role.unwrap_or_else(|| pattern_role(PatternRole::Primary)),
        policy,
        committed,
    )
    .expect("a required Pattern slot is total after recovery")
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParsedPattern<C> {
    range: Range<usize>,
    complete: bool,
    marker: PhantomData<C>,
}

impl<C> ParsedPattern<C> {
    fn new(range: Range<usize>, complete: bool) -> Self {
        Self {
            range,
            complete,
            marker: PhantomData,
        }
    }
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    /// Whether the mandatory outer primary ultimately accepted a Pattern NUD.
    pub(crate) fn is_complete(&self) -> bool {
        self.complete
    }
}

fn parse_pattern_bp<'source, E>(
    table: &OperatorTable,
    i: SynIn<'_, 'source, '_, E>,
    minimum: PatternPrecedence,
) -> Option<Pattern<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_pattern_bp_with_fresh_primary_policy(
        table,
        i,
        minimum,
        PatternMandatorySlotPolicy::default(),
    )
}

/// Recursive Pattern entries deliberately use the ordinary wrapper above, so
/// this caller's extra fresh-primary boundaries end with its first NUD.
fn parse_pattern_bp_with_fresh_primary_policy<'source, E>(
    table: &OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
    minimum: PatternPrecedence,
    policy: PatternMandatorySlotPolicy,
) -> Option<Pattern<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let pattern_continuation_base = pattern_continuation_base(&i);
    let mut primary_close_recovered = false;
    let head = match i.run(from_fn(|i| {
        recognize_pattern_nud_with_fresh_primary_policy(policy, i)
    })) {
        Some(nud) => {
            let (primary, close_recovered) = parse_pattern_primary(table, nud, &mut i);
            primary_close_recovered = close_recovered;
            Recovered::Complete(primary)
        }
        None if recover_pattern_primary_ast_with_fresh_primary_policy(policy, &mut i) => {
            let nud = i
                .run(from_fn(|i| {
                    recognize_pattern_nud_with_fresh_primary_policy(policy, i)
                }))
                .expect("AST recovery stops at a pattern primary");
            let (primary, close_recovered) = parse_pattern_primary(table, nud, &mut i);
            primary_close_recovered = close_recovered;
            Recovered::Complete(primary)
        }
        None => Recovered::Incomplete,
    };
    if matches!(head, Recovered::Incomplete)
        && policy.fresh_primary_recovery_stops != StopSet::default()
    {
        return Some(Pattern {
            head,
            tails: Vec::new(),
            type_annotation: None,
            range: start..start,
        });
    }
    let mut tails = Vec::new();
    let mut type_annotation = None;
    while !primary_close_recovered
        || !recovered_primary_tail_stop_pending(policy, pattern_continuation_base, &mut i)
    {
        let Some(led) = i.run(from_fn(|i| {
            recognize_pattern_led(minimum, pattern_continuation_base, i)
        })) else {
            break;
        };
        match led {
            PatternLedRecognition::Alias { keyword, .. } => {
                consume_trivia(&mut i);
                let binding = i
                    .run(scan_word)
                    .map_or(Recovered::Incomplete, Recovered::Complete);
                let end = match &binding {
                    Recovered::Complete(word) => word.range().end,
                    Recovered::Incomplete => keyword.range().end,
                };
                tails.push(PatternTail::Alias(PatternAliasTail {
                    keyword,
                    binding,
                    range: keyword.range().start..end,
                }));
            }
            PatternLedRecognition::Alternation { pipe, .. } => {
                consume_trivia(&mut i);
                let rhs = i
                    .run(from_fn(|i| {
                        parse_pattern_bp(table, i, PatternPrecedence::Alternation)
                    }))
                    .map(|pattern| Recovered::Complete(Box::new(pattern)))
                    .unwrap_or(Recovered::Incomplete);
                let end = match &rhs {
                    Recovered::Complete(pattern) => pattern.range.end,
                    Recovered::Incomplete => pipe.end,
                };
                tails.push(PatternTail::Alternation(PatternAlternationTail {
                    pipe: pipe.clone(),
                    rhs,
                    range: pipe.start..end,
                }));
            }
            PatternLedRecognition::TypeAnnotation { colon, .. } => {
                let _ = consume_pattern_annotation_trivia(pattern_continuation_base, &mut i);
                let type_expr = match i
                    .run(from_fn(|i| {
                        Some(parse_required_type_expression_with_recovery_context(
                            RequiredTypeRecoveryContext::with_malformed_continuation_base(
                                Some(pattern_role(PatternRole::TypeAnnotation)),
                                pattern_continuation_base,
                            ),
                            i,
                        ))
                    }))
                    .expect("a mandatory type annotation entry is total")
                {
                    Recovered::Complete(type_expr) => Recovered::Complete(Box::new(type_expr)),
                    Recovered::Incomplete => Recovered::Incomplete,
                };
                let end = match &type_expr {
                    Recovered::Complete(type_expr) => type_expr.range().end,
                    Recovered::Incomplete => colon.end,
                };
                type_annotation = Some(PatternTypeAnnotation {
                    colon: colon.clone(),
                    type_expr,
                    range: colon.start..end,
                });
                break;
            }
        }
    }
    let end = type_annotation.as_ref().map_or_else(
        || {
            tails.last().map_or_else(
                || match &head {
                    Recovered::Complete(primary) => primary_range(primary).end,
                    Recovered::Incomplete => start,
                },
                |tail| match tail {
                    PatternTail::Alias(tail) => tail.range.end,
                    PatternTail::Alternation(tail) => tail.range.end,
                },
            )
        },
        |annotation| annotation.range.end,
    );
    Some(Pattern {
        head,
        tails,
        type_annotation,
        range: start..end,
    })
}

fn parse_pattern_primary<'source, E>(
    table: &OperatorTable,
    nud: PatternNudRecognition<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (PatternPrimary<'source>, bool)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match nud {
        PatternNudRecognition::Name(name) => (PatternPrimary::Identifier(name), false),
        PatternNudRecognition::Integer(integer) => (PatternPrimary::Integer(integer), false),
        PatternNudRecognition::Symbol { colon, name } => (
            PatternPrimary::Symbol(SymbolPattern {
                range: colon.start..name.range().end,
                colon,
                name: Recovered::Complete(name),
            }),
            false,
        ),
        PatternNudRecognition::MalformedSymbol { colon } => (
            PatternPrimary::Symbol(SymbolPattern {
                range: colon.clone(),
                colon,
                name: Recovered::Incomplete,
            }),
            false,
        ),
        PatternNudRecognition::Parenthesized { open } => {
            let (pattern, close_recovered) = parse_parenthesized_pattern(table, open, i);
            (PatternPrimary::Parenthesized(pattern), close_recovered)
        }
        PatternNudRecognition::List { open } => (
            PatternPrimary::List(parse_list_pattern(table, open, i)),
            false,
        ),
        PatternNudRecognition::Record { open } => (
            PatternPrimary::Record(parse_record_pattern(table, open, i)),
            false,
        ),
    }
}

fn primary_range(primary: &PatternPrimary<'_>) -> Range<usize> {
    match primary {
        PatternPrimary::Identifier(name) => name.range(),
        PatternPrimary::Integer(integer) => integer.range(),
        PatternPrimary::Symbol(symbol) => symbol.range.clone(),
        PatternPrimary::Parenthesized(parenthesized) => parenthesized.range.clone(),
        PatternPrimary::List(list) => list.range.clone(),
        PatternPrimary::Record(record) => record.range.clone(),
    }
}

fn parse_list_pattern<'source, E>(
    table: &OperatorTable,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ListPattern<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let policy = PatternDelimitedPolicy::List;
    let caller_close_stops = pattern_caller_close_stops(active_stop_set(i));
    let incoming_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    push_pattern_delimited_scope(policy, caller_close_stops, i);
    let opening_trivia = consume_trivia(i);
    let layout = LayoutDelimitedFrame::after_opening_trivia(
        incoming_base,
        &opening_trivia,
        i.local.line().line_indent,
    );
    push_pattern_layout_baseline(layout, i);
    let (items, trailing_comma, close, _) =
        parse_pattern_delimited_items_ast(policy, layout, caller_close_stops, i, |i| {
            parse_list_item_ast(table, i)
        });
    let end = match &close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => i.pos(),
    };
    pop_pattern_layout_baseline(layout, i);
    pop_pattern_delimited_scope(policy, caller_close_stops, i);
    ListPattern {
        open: open.clone(),
        items,
        trailing_comma,
        close,
        range: open.start..end,
    }
}

fn parse_list_item_ast<'source, E>(
    table: &OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<ListPatternItem<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(marker) = i.run(scan_exact_dot_dot) {
        consume_trivia(i);
        let rhs = i
            .run(from_fn(|i| {
                parse_pattern_bp(table, i, PatternPrecedence::Lowest)
            }))
            .map(|pattern| Recovered::Complete(Box::new(pattern)))
            .unwrap_or(Recovered::Incomplete);
        let end = match &rhs {
            Recovered::Complete(pattern) => pattern.range.end,
            Recovered::Incomplete => marker.end,
        };
        return Recovered::Complete(ListPatternItem::Spread(ListPatternSpreadItem {
            marker: marker.clone(),
            rhs,
            range: marker.start..end,
        }));
    }
    i.run(from_fn(|i| {
        parse_pattern_bp(table, i, PatternPrecedence::Lowest)
    }))
    .map(|pattern| Recovered::Complete(ListPatternItem::Pattern(pattern)))
    .unwrap_or(Recovered::Incomplete)
}

fn parse_record_pattern<'source, E>(
    table: &OperatorTable,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> RecordPattern<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let policy = PatternDelimitedPolicy::Record;
    let caller_close_stops = pattern_caller_close_stops(active_stop_set(i));
    let incoming_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    push_pattern_delimited_scope(policy, caller_close_stops, i);
    let opening_trivia = consume_trivia(i);
    let layout = LayoutDelimitedFrame::after_opening_trivia(
        incoming_base,
        &opening_trivia,
        i.local.line().line_indent,
    );
    push_pattern_layout_baseline(layout, i);
    let (items, trailing_comma, close, _) =
        parse_pattern_delimited_items_ast(policy, layout, caller_close_stops, i, |i| {
            parse_record_item_ast(table, i)
        });
    let end = match &close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => i.pos(),
    };
    pop_pattern_layout_baseline(layout, i);
    pop_pattern_delimited_scope(policy, caller_close_stops, i);
    RecordPattern {
        open: open.clone(),
        items,
        trailing_comma,
        close,
        range: open.start..end,
    }
}

fn parse_record_item_ast<'source, E>(
    table: &OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<RecordPatternItem<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(marker) = i.run(scan_exact_dot_dot) {
        consume_trivia(i);
        let rhs = i
            .run(from_fn(|i| {
                parse_pattern_bp(table, i, PatternPrecedence::Lowest)
            }))
            .map(|pattern| Recovered::Complete(Box::new(pattern)))
            .unwrap_or(Recovered::Incomplete);
        let end = match &rhs {
            Recovered::Complete(pattern) => pattern.range.end,
            Recovered::Incomplete => marker.end,
        };
        return Recovered::Complete(RecordPatternItem::Spread(RecordPatternSpreadItem {
            marker: marker.clone(),
            rhs,
            range: marker.start..end,
        }));
    }
    let Some(name) = i.run(scan_pattern_name) else {
        return Recovered::Incomplete;
    };
    let field_start = name.range().start;
    let checkpoint = i.checkpoint();
    let trailing = consume_trivia(i);
    if !trivia_has_physical_newline(&trailing) {
        if let Some(colon) = i.run(recognize_colon) {
            consume_trivia(i);
            let stops = active_stop_set(i).with(StopKind::Equal);
            i.local.push_stop_set(stops);
            let pattern = i
                .run(from_fn(|i| {
                    parse_pattern_bp(table, i, PatternPrecedence::Lowest)
                }))
                .map(|pattern| Recovered::Complete(Box::new(pattern)))
                .unwrap_or(Recovered::Incomplete);
            assert_eq!(i.local.pop_stop_set(), Some(stops));
            let default = parse_record_default_ast(table, i);
            let end = default.as_ref().map_or_else(
                || match &pattern {
                    Recovered::Complete(pattern) => pattern.range.end,
                    Recovered::Incomplete => colon.end,
                },
                |default| default.range.end,
            );
            return Recovered::Complete(RecordPatternItem::Field(RecordPatternField {
                name,
                form: RecordPatternFieldForm::Nested {
                    colon,
                    pattern,
                    default,
                },
                range: field_start..end,
            }));
        }
        if let Some(equals) = i.run(scan_exact_equals) {
            consume_trivia(i);
            let default = parse_record_default_expression_ast(table, equals, i);
            let end = default.range.end;
            return Recovered::Complete(RecordPatternItem::Field(RecordPatternField {
                name,
                form: RecordPatternFieldForm::Default(default),
                range: field_start..end,
            }));
        }
    }
    i.rollback(checkpoint);
    Recovered::Complete(RecordPatternItem::Field(RecordPatternField {
        name: name.clone(),
        form: RecordPatternFieldForm::Shorthand,
        range: field_start..name.range().end,
    }))
}

fn parse_record_default_ast<'source, E>(
    table: &OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<RecordPatternDefault<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i);
    if trivia_has_physical_newline(&trivia) {
        i.rollback(checkpoint);
        return None;
    }
    let equals = i.run(scan_exact_equals)?;
    consume_trivia(i);
    Some(parse_record_default_expression_ast(table, equals, i))
}

fn parse_record_default_expression_ast<'source, E>(
    table: &OperatorTable,
    equals: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> RecordPatternDefault<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let expression = i
        .run(from_fn(|i| parse_expression_with_operators(table, i)))
        .map(|expression| Recovered::Complete(Box::new(expression)))
        .unwrap_or(Recovered::Incomplete);
    let end = match &expression {
        Recovered::Complete(expression) => expression.range().end,
        Recovered::Incomplete => equals.end,
    };
    RecordPatternDefault {
        equals: equals.clone(),
        expression,
        range: equals.start..end,
    }
}

fn recover_list_separator_or_close_ast<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    loop {
        if any_ambient_owner_claims(i) {
            return false;
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return false;
        };
        if matches!(character, ']' | ')' | '}') || arm_stop_pending(i) {
            return false;
        }
        i.input.next().expect("the inspected character exists");
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        if exact_dot_dot_pending_input(i) || pattern_nud_candidate_input(i) {
            return true;
        }
    }
}

fn parse_parenthesized_pattern<'source, E>(
    table: &OperatorTable,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (ParenthesizedPattern<'source>, bool)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let policy = PatternDelimitedPolicy::Parenthesized;
    let caller_close_stops = pattern_caller_close_stops(active_stop_set(i));
    let incoming_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    push_pattern_delimited_scope(policy, caller_close_stops, i);
    let opening_trivia = consume_trivia(i);
    let layout = LayoutDelimitedFrame::after_opening_trivia(
        incoming_base,
        &opening_trivia,
        i.local.line().line_indent,
    );
    push_pattern_layout_baseline(layout, i);
    let (elements, trailing_comma, close, close_recovered) =
        parse_pattern_delimited_items_ast(policy, layout, caller_close_stops, i, |i| {
            i.run(from_fn(|i| {
                parse_pattern_bp(table, i, PatternPrecedence::Lowest)
            }))
            .map_or(Recovered::Incomplete, Recovered::Complete)
        });
    let end = match &close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => i.pos(),
    };
    pop_pattern_layout_baseline(layout, i);
    pop_pattern_delimited_scope(policy, caller_close_stops, i);
    (
        ParenthesizedPattern {
            open: open.clone(),
            elements,
            trailing_comma,
            close,
            range: open.start..end,
        },
        close_recovered,
    )
}

/// Runs the comma/close/retry control flow shared by the two fixed pattern
/// containers.  The caller keeps ownership of its item grammar and AST shape.
fn parse_pattern_delimited_items_ast<'source, E, Item>(
    policy: PatternDelimitedPolicy,
    layout: LayoutDelimitedFrame,
    caller_close_stops: StopSet,
    i: &mut SynIn<'_, 'source, '_, E>,
    mut parse_item: impl FnMut(&mut SynIn<'_, 'source, '_, E>) -> Recovered<Item>,
) -> (
    Vec<Recovered<Item>>,
    Option<Range<usize>>,
    Recovered<Range<usize>>,
    bool,
)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut items = Vec::new();
    let mut trailing_comma = None;
    let mut close_recovered = false;
    let close = if let Some(close) =
        i.run(from_fn(|i| recognize_pattern_delimited_close(policy, i)))
    {
        Recovered::Complete(close)
    } else if outer_pattern_close_stop_pending(policy, caller_close_stops, i) {
        Recovered::Incomplete
    } else {
        'items: loop {
            items.push(parse_item(i));
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let trivia = consume_trivia(i);
            if let Some(comma) = i.run(recognize_comma) {
                consume_trivia(i);
                if let Some(close) =
                    i.run(from_fn(|i| recognize_pattern_delimited_close(policy, i)))
                {
                    trailing_comma = Some(comma);
                    break Recovered::Complete(close);
                }
                if outer_pattern_close_stop_pending(policy, caller_close_stops, i) {
                    break Recovered::Incomplete;
                }
                continue;
            }
            if let Some(close) = i.run(from_fn(|i| recognize_pattern_delimited_close(policy, i))) {
                break Recovered::Complete(close);
            }
            if outer_pattern_close_stop_pending(policy, caller_close_stops, i) {
                break Recovered::Incomplete;
            }
            if layout.boundary_after_trivia(&trivia, i.local.line().line_indent)
                == LayoutDelimitedBoundary::ImplicitNewline
            {
                continue;
            }
            if policy.ast_next_item_pending(i) {
                continue;
            }
            if policy == PatternDelimitedPolicy::Parenthesized {
                match drive_parenthesized_pattern_close_recovery(caller_close_stops, i) {
                    ParenthesizedPatternCloseRecoveryStep::Complete { close } => {
                        break 'items Recovered::Complete(close);
                    }
                    ParenthesizedPatternCloseRecoveryStep::Error { .. } => {
                        close_recovered = true;
                        continue;
                    }
                    ParenthesizedPatternCloseRecoveryStep::Missing { .. } => {
                        break 'items Recovered::Incomplete;
                    }
                };
            }
            if policy.recover_ast_separator_or_close(i) {
                continue;
            }
            break i
                .run(from_fn(|i| recognize_pattern_delimited_close(policy, i)))
                .map_or(Recovered::Incomplete, Recovered::Complete);
        }
    };
    (items, trailing_comma, close, close_recovered)
}

/// Shares the direct Parenthesized close scanner's cursor decisions with the
/// AST path.  It intentionally has no sink: callers decide how an Error or a
/// Missing becomes their own AST/CST representation.
fn drive_parenthesized_pattern_close_recovery<E>(
    caller_close_stops: StopSet,
    i: &mut SynIn<E>,
) -> ParenthesizedPatternCloseRecoveryStep
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let at = i.pos();
    if any_ambient_owner_claims(i) || i.input.remainder().is_empty() {
        return ParenthesizedPatternCloseRecoveryStep::Missing { at };
    }
    if let Some(close) = i.run(from_fn(|i| {
        recognize_pattern_delimited_close(PatternDelimitedPolicy::Parenthesized, i)
    })) {
        return ParenthesizedPatternCloseRecoveryStep::Complete { close };
    }
    if outer_pattern_close_stop_pending(
        PatternDelimitedPolicy::Parenthesized,
        caller_close_stops,
        i,
    ) {
        return ParenthesizedPatternCloseRecoveryStep::Missing { at };
    }
    if let Some(punctuation) = i.run(scan_punctuation) {
        return match punctuation.kind() {
            PunctuationKind::Close(Delimiter::Parenthesis) => {
                ParenthesizedPatternCloseRecoveryStep::Complete {
                    close: punctuation.range(),
                }
            }
            PunctuationKind::Close(actual) => ParenthesizedPatternCloseRecoveryStep::Error {
                range: punctuation.range(),
                unexpected: UnexpectedCategory::Punctuation(
                    crate::session::PunctuationEvidence::Close(actual),
                ),
            },
            _ => ParenthesizedPatternCloseRecoveryStep::Error {
                range: punctuation.range(),
                unexpected: UnexpectedCategory::OtherCharacter,
            },
        };
    }
    i.input
        .next()
        .expect("the non-EOF close-recovery byte exists");
    let range = at..i.pos();
    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);
    ParenthesizedPatternCloseRecoveryStep::Error {
        range,
        unexpected: UnexpectedCategory::OtherCharacter,
    }
}

/// AST recovery mirrors the direct mandatory-primary retry without recording a
/// CST diagnostic.  It preserves caller-owned punctuation and only consumes a
/// non-empty invalid run when it can retry the same slot at a later primary.
fn recover_pattern_primary_ast<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    recover_pattern_primary_ast_with_fresh_primary_policy(PatternMandatorySlotPolicy::default(), i)
}

fn recover_pattern_primary_ast_with_fresh_primary_policy<E>(
    policy: PatternMandatorySlotPolicy,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if any_ambient_owner_claims(i) {
            return false;
        }
        if i.pos() > start && pattern_nud_candidate_input_with_fresh_primary_policy(policy, i) {
            return true;
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return false;
        };
        if matches!(character, ')' | ']' | '}' | ',' | ';')
            || (character == ':' && active_stop_set(i).contains(StopKind::Colon))
            || fresh_primary_policy_stop_pending(policy, i)
            || arm_stop_pending(i)
        {
            return false;
        }
        i.input.next().expect("the inspected character exists");
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        if pattern_nud_candidate_input_with_fresh_primary_policy(policy, i) {
            return i.pos() > start;
        }
    }
}

pub(crate) fn pattern_nud_candidate_input<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let candidate = i.run(from_fn(recognize_pattern_nud)).is_some();
    i.rollback(checkpoint);
    candidate
}

fn pattern_nud_candidate_input_with_fresh_primary_policy<E>(
    policy: PatternMandatorySlotPolicy,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let candidate = i
        .run(from_fn(|i| {
            recognize_pattern_nud_with_fresh_primary_policy(policy, i)
        }))
        .is_some();
    i.rollback(checkpoint);
    candidate
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum PatternNudRecognition<'source> {
    Name(PatternNameSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Symbol {
        colon: Range<usize>,
        name: WordSpan<'source>,
    },
    MalformedSymbol {
        colon: Range<usize>,
    },
    Parenthesized {
        open: Range<usize>,
    },
    List {
        open: Range<usize>,
    },
    Record {
        open: Range<usize>,
    },
}

fn recognize_pattern_nud<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<PatternNudRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if arm_stop_pending(&mut i) {
        return None;
    }
    if let Some(symbol) = i.run(from_fn(recognize_symbol_pattern)) {
        return Some(symbol);
    }
    if active_stop_set(&i).contains(StopKind::Colon) && colon_pending(&mut i) {
        return None;
    }
    if active_stop_set(&i).contains(StopKind::Equal) && exact_equals_pending_input(&mut i) {
        return None;
    }
    if let Some(colon) = i.run(recognize_colon) {
        return Some(PatternNudRecognition::MalformedSymbol { colon });
    }
    i.choice((
        from_fn(scan_pattern_name).map(PatternNudRecognition::Name),
        parse_integer_literal.map(PatternNudRecognition::Integer),
        recognize_open_parenthesis.map(|open| PatternNudRecognition::Parenthesized { open }),
        recognize_open_bracket.map(|open| PatternNudRecognition::List { open }),
        recognize_open_brace.map(|open| PatternNudRecognition::Record { open }),
    ))
}

/// `:symbol` wins before the caller-owned bare-colon stop; accepted NUDs then
/// return to the normal Pattern entry with its raw incoming stops.
fn recognize_pattern_nud_with_fresh_primary_policy<'source, E>(
    policy: PatternMandatorySlotPolicy,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<PatternNudRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if arm_stop_pending(&mut i) {
        return None;
    }
    if let Some(symbol) = i.run(from_fn(recognize_symbol_pattern)) {
        return Some(symbol);
    }
    if fresh_primary_policy_stop_pending(policy, &mut i) {
        return None;
    }
    recognize_pattern_nud(i)
}

fn fresh_primary_policy_stop_pending<E>(
    policy: PatternMandatorySlotPolicy,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let stops = policy.fresh_primary_recovery_stops;
    (stops.contains(StopKind::Colon) && colon_pending(i))
        || (stops.contains(StopKind::Equal) && exact_equals_pending_input(i))
        || (stops.contains(StopKind::LeftBrace) && i.input.remainder().starts_with('{'))
}

/// Keeps a recovered outer primary's annotation-looking colon available to
/// the mandatory slot owner.  The probe uses the same trivia eligibility as
/// the canonical annotation LED and always restores the input and line state.
fn recovered_primary_tail_stop_pending<E>(
    policy: PatternMandatorySlotPolicy,
    pattern_continuation_base: usize,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if !policy
        .recovered_primary_tail_stops
        .contains(StopKind::Colon)
    {
        return false;
    }
    let checkpoint = i.checkpoint();
    let pending = consume_pattern_annotation_trivia(pattern_continuation_base, i).is_some()
        && colon_pending(i);
    i.rollback(checkpoint);
    pending
}

fn arm_stop_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let stops = active_stop_set(i);
    if stops.contains(StopKind::Arrow) && i.input.remainder().starts_with("->") {
        return true;
    }
    let checkpoint = i.checkpoint();
    let word = i.run(scan_word).map(|word| word.text());
    i.rollback(checkpoint);
    matches!(word, Some("if") if stops.contains(StopKind::ArmGuardIf))
        || matches!(word, Some("where") if stops.contains(StopKind::ArmGuardWhere))
        || matches!(word, Some("in") if stops.contains(StopKind::In))
}

/// Composite probe: a symbol owns only a colon immediately followed by a word.
/// The caller's colon stop is checked only after this probe has rejected.
fn recognize_symbol_pattern<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<PatternNudRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let Some(colon) = i.run(recognize_colon) else {
        return None;
    };
    let Some(name) = i.run(scan_word) else {
        i.rollback(checkpoint);
        return None;
    };
    Some(PatternNudRecognition::Symbol { colon, name })
}

fn colon_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(recognize_colon).is_some();
    i.rollback(checkpoint);
    pending
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum PatternLedRecognition<'source> {
    Alias {
        leading: TriviaRun,
        keyword: WordSpan<'source>,
    },
    Alternation {
        leading: TriviaRun,
        pipe: Range<usize>,
    },
    TypeAnnotation {
        leading: TriviaRun,
        colon: Range<usize>,
    },
}

fn recognize_pattern_led<'source, E>(
    minimum: PatternPrecedence,
    pattern_continuation_base: usize,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<PatternLedRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(&mut i) {
        return None;
    }
    if minimum <= PatternPrecedence::Alias {
        let checkpoint = i.checkpoint();
        let leading = consume_trivia(&mut i);
        if let Some(keyword) = i.run(scan_word) {
            if keyword.text() == "as" {
                return Some(PatternLedRecognition::Alias { leading, keyword });
            }
        }
        i.rollback(checkpoint);
    }
    if minimum <= PatternPrecedence::Alternation {
        let checkpoint = i.checkpoint();
        let leading = consume_trivia(&mut i);
        if let Some(pipe) = i.run(recognize_pipe) {
            return Some(PatternLedRecognition::Alternation { leading, pipe });
        }
        i.rollback(checkpoint);
    }
    if minimum <= PatternPrecedence::TypeAnnotation
        && !active_stop_set(&i).contains(StopKind::Colon)
    {
        let checkpoint = i.checkpoint();
        if let Some(leading) = consume_pattern_annotation_trivia(pattern_continuation_base, &mut i)
        {
            if let Some(colon) = i.run(recognize_colon) {
                return Some(PatternLedRecognition::TypeAnnotation { leading, colon });
            }
        }
        i.rollback(checkpoint);
    }
    None
}

/// Sigil recognition runs before an ordinary word.  `_` is intentionally the
/// one exception: it remains an ordinary identifier, while `_bar` and `__`
/// are sigil names.
fn scan_pattern_name<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<PatternNameSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    if let Some(word) = i.run(scan_word) {
        if word.text().starts_with('_') && word.text() != "_" {
            return Some(PatternNameSpan {
                text: word.text(),
                range: start..word.range().end,
                lexical_kind: PatternNameKind::Sigil,
            });
        }
        i.rollback(checkpoint);
    }
    for sigil in ['$', '&', '\''] {
        let checkpoint = i.checkpoint();
        if i.skip(item(sigil)).is_some() {
            if let Some(word) = i.run(scan_word) {
                return Some(PatternNameSpan {
                    text: &i.input.source()[start..word.range().end],
                    range: start..word.range().end,
                    lexical_kind: PatternNameKind::Sigil,
                });
            }
        }
        i.rollback(checkpoint);
    }
    i.run(scan_word)
        .map(|word| PatternNameSpan::from_word(word, PatternNameKind::Ordinary))
}

fn recognize_open_parenthesis<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
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

fn recognize_open_bracket<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Open(Delimiter::Bracket)).then(|| punctuation.range())
}

fn recognize_open_brace<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Open(Delimiter::Brace)).then(|| punctuation.range())
}

/// Accepts a spread marker only when its maximal operator-shaped spelling is
/// exactly `..`.  This is independent of declared operators and deliberately
/// refuses to split `...` or `..+` into a marker plus a remainder.
fn scan_exact_dot_dot<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    while i
        .input
        .remainder()
        .chars()
        .next()
        .is_some_and(is_operator_shaped_character)
    {
        i.input.next()?;
    }
    let end = i.pos();
    if &i.input.source()[start..end] != ".." {
        i.rollback(checkpoint);
        return None;
    }
    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);
    Some(start..end)
}

fn scan_exact_equals<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    while i
        .input
        .remainder()
        .chars()
        .next()
        .is_some_and(is_operator_shaped_character)
    {
        i.input.next()?;
    }
    let end = i.pos();
    if &i.input.source()[start..end] != "=" {
        i.rollback(checkpoint);
        return None;
    }
    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);
    Some(start..end)
}

fn is_operator_shaped_character(character: char) -> bool {
    !character.is_whitespace()
        && !character.is_ascii_digit()
        && character != '_'
        && !unicode_ident::is_xid_continue(character)
        && !matches!(
            character,
            '(' | ')' | '[' | ']' | '{' | '}' | ',' | ':' | '/' | ';' | '\\' | '\'' | '@'
        )
}

fn exact_dot_dot_pending_input<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_exact_dot_dot).is_some();
    i.rollback(checkpoint);
    pending
}

fn exact_equals_pending_input<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_exact_equals).is_some();
    i.rollback(checkpoint);
    pending
}

fn pattern_name_pending_input<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_pattern_name).is_some();
    i.rollback(checkpoint);
    pending
}

fn recognize_pattern_delimited_close<'source, E>(
    policy: PatternDelimitedPolicy,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let close = i.run(scan_punctuation).and_then(|punctuation| {
        (punctuation.kind() == PunctuationKind::Close(policy.delimiter()))
            .then(|| punctuation.range())
    });
    if close.is_none() {
        i.rollback(checkpoint);
    }
    close
}

fn recognize_comma<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let comma = i.run(scan_punctuation).and_then(|punctuation| {
        (punctuation.kind() == PunctuationKind::Comma).then(|| punctuation.range())
    });
    if comma.is_none() {
        i.rollback(checkpoint);
    }
    comma
}

fn recognize_colon<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let colon = i.run(scan_punctuation).and_then(|punctuation| {
        (punctuation.kind() == PunctuationKind::Colon).then(|| punctuation.range())
    });
    if colon.is_none() {
        i.rollback(checkpoint);
    }
    colon
}

fn recognize_pipe<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = i.pos();
    i.skip(item('|'))?;
    Some(start..i.pos())
}

fn consume_trivia<E>(i: &mut SynIn<E>) -> TriviaRun
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.run(scan_trivia).expect("trivia scanning is total")
}

fn trivia_has_physical_newline(trivia: &TriviaRun) -> bool {
    trivia
        .parts()
        .iter()
        .any(|part| matches!(part.kind(), crate::scan::trivia::TriviaPartKind::Newline))
}

/// Own one maximal annotation gap only when it remains on the current line or
/// continues beyond the indentation captured at this Pattern entry.
fn consume_pattern_annotation_trivia<E>(
    pattern_continuation_base: usize,
    i: &mut SynIn<E>,
) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i);
    if trivia_has_physical_newline(&trivia)
        && i.local.line().line_indent <= pattern_continuation_base
    {
        i.rollback(checkpoint);
        return None;
    }
    Some(trivia)
}

fn pattern_continuation_base<E>(i: &SynIn<E>) -> usize
where
    E: ErrorSink<usize>,
{
    i.local.line().line_indent.max(
        i.local
            .indentation_baseline()
            .map_or(0, |baseline| baseline.column),
    )
}

fn active_stop_set<E>(i: &SynIn<E>) -> StopSet
where
    E: ErrorSink<usize>,
{
    i.local.stop_set().unwrap_or_default()
}

fn pattern_caller_close_stops(stops: StopSet) -> StopSet {
    let mut caller_closes = StopSet::default();
    for stop in [
        StopKind::RightParenthesis,
        StopKind::RightBracket,
        StopKind::RightBrace,
    ] {
        if stops.contains(stop) {
            caller_closes = caller_closes.with(stop);
        }
    }
    caller_closes
}

fn pattern_delimited_scope_stops(
    policy: PatternDelimitedPolicy,
    caller_close_stops: StopSet,
) -> StopSet {
    let mut stops = policy.stop_set();
    for stop in [
        StopKind::RightParenthesis,
        StopKind::RightBracket,
        StopKind::RightBrace,
    ] {
        if caller_close_stops.contains(stop) {
            stops = stops.with(stop);
        }
    }
    stops
}

fn push_pattern_delimited_scope<E>(
    policy: PatternDelimitedPolicy,
    caller_close_stops: StopSet,
    i: &mut SynIn<E>,
) where
    E: ErrorSink<usize>,
{
    i.local.push_delimiter(policy.delimiter());
    i.local
        .push_stop_set(pattern_delimited_scope_stops(policy, caller_close_stops));
}

fn pop_pattern_delimited_scope<E>(
    policy: PatternDelimitedPolicy,
    caller_close_stops: StopSet,
    i: &mut SynIn<E>,
) where
    E: ErrorSink<usize>,
{
    assert_eq!(i.local.pop_delimiter(), Some(policy.delimiter()));
    assert_eq!(
        i.local.pop_stop_set(),
        Some(pattern_delimited_scope_stops(policy, caller_close_stops))
    );
}

fn push_pattern_layout_baseline<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    i.local.push_indentation_baseline(IndentationBaseline {
        column: layout.base_indent(),
        kind: IndentationBaselineKind::Introducer,
    });
}

fn pop_pattern_layout_baseline<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    assert_eq!(
        i.local.pop_indentation_baseline(),
        Some(IndentationBaseline {
            column: layout.base_indent(),
            kind: IndentationBaselineKind::Introducer,
        })
    );
}

fn parse_direct_pattern_bp<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    minimum: PatternPrecedence,
    primary_role: PatternRole,
    outer_missing_role: GrammarRole,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedPattern<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_direct_pattern_bp_with_fresh_primary_policy(
        table,
        minimum,
        primary_role,
        outer_missing_role,
        PatternMandatorySlotPolicy::default(),
        committed,
    )
}

fn parse_direct_pattern_bp_with_fresh_primary_policy<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    minimum: PatternPrecedence,
    primary_role: PatternRole,
    outer_missing_role: GrammarRole,
    policy: PatternMandatorySlotPolicy,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedPattern<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = committed_position(committed);
    let pattern_continuation_base =
        committed.probe(|probe| pattern_continuation_base(probe.input()));
    committed.start_node(SyntaxKind::Pattern);
    let mut primary_close_recovered = false;
    let primary_accepted = if let Some(nud) =
        committed.probe(|probe| probe_pattern_nud_with_fresh_primary_policy(policy, probe))
    {
        primary_close_recovered = commit_direct_primary(table, nud, committed);
        true
    } else if committed.probe(pipe_pending) {
        // The RHS of `A | | B` owns a missing primary at the second pipe;
        // leaving that pipe lets this same Pattern consume its nested tail.
        emit_pattern_missing(committed, primary_role, ExpectedSyntax::Pattern);
        false
    } else if let Some(retry) = direct_pattern_primary_error_retry_with_fresh_primary_policy(
        policy,
        committed,
        primary_role,
    ) {
        if retry {
            primary_close_recovered = commit_direct_primary(
                table,
                committed
                    .probe(|probe| probe_pattern_nud_with_fresh_primary_policy(policy, probe))
                    .expect("recovery retried a pattern NUD"),
                committed,
            );
            true
        } else {
            if policy.fresh_primary_recovery_stops == StopSet::default() {
                emit_missing_with_role(committed, outer_missing_role, ExpectedSyntax::Pattern);
            }
            false
        }
    } else {
        emit_missing_with_role(committed, outer_missing_role, ExpectedSyntax::Pattern);
        false
    };
    if !primary_accepted && policy.fresh_primary_recovery_stops != StopSet::default() {
        let end = committed_position(committed);
        committed.finish_node();
        return Some(ParsedPattern::new(start..end, false));
    }

    loop {
        if primary_close_recovered
            && committed.probe(|probe| {
                recovered_primary_tail_stop_pending(
                    policy,
                    pattern_continuation_base,
                    probe.input(),
                )
            })
        {
            break;
        }
        let Some(led) =
            committed.probe(|probe| probe_pattern_led(minimum, pattern_continuation_base, probe))
        else {
            break;
        };
        match led {
            PatternLedRecognition::Alias { leading, keyword } => {
                committed.emit_trivia(&leading);
                committed.start_node(SyntaxKind::PatternAliasTail);
                committed.token(SyntaxKind::AsKw, keyword.range());
                let binding_trivia = consume_direct_trivia(committed);
                committed.emit_trivia(&binding_trivia);
                if let Some(binding) = committed.probe(|probe| probe.input().run(scan_word)) {
                    committed.token(SyntaxKind::Identifier, binding.range());
                } else {
                    match direct_alias_binding_error_retry(committed) {
                        Some(true) => {
                            let binding = committed
                                .probe(|probe| probe.input().run(scan_word))
                                .expect("recovery retried an ordinary alias binding");
                            committed.token(SyntaxKind::Identifier, binding.range());
                        }
                        Some(false) => {}
                        None => emit_pattern_missing(
                            committed,
                            PatternRole::AliasBinding,
                            ExpectedSyntax::Identifier,
                        ),
                    }
                }
                committed.finish_node();
            }
            PatternLedRecognition::Alternation { leading, pipe } => {
                committed.emit_trivia(&leading);
                committed.start_node(SyntaxKind::PatternAlternationTail);
                committed.token(SyntaxKind::Pipe, pipe);
                let rhs_trivia = consume_direct_trivia(committed);
                committed.emit_trivia(&rhs_trivia);
                parse_direct_pattern_bp(
                    table,
                    PatternPrecedence::Alternation,
                    PatternRole::AlternationRhs,
                    pattern_role(PatternRole::AlternationRhs),
                    committed,
                )
                .expect("a committed alternation owns a total RHS pattern");
                committed.finish_node();
            }
            PatternLedRecognition::TypeAnnotation { leading, colon } => {
                committed.emit_trivia(&leading);
                committed.start_node(SyntaxKind::PatternTypeAnnotation);
                committed.token(SyntaxKind::Colon, colon);
                if let Some(trivia) = committed.probe(|probe| {
                    consume_pattern_annotation_trivia(pattern_continuation_base, probe.input())
                }) {
                    committed.emit_trivia(&trivia);
                }
                commit_direct_type_expression_with_recovery_context(
                    RequiredTypeRecoveryContext::with_malformed_continuation_base(
                        Some(pattern_role(PatternRole::TypeAnnotation)),
                        pattern_continuation_base,
                    ),
                    committed,
                );
                committed.finish_node();
                break;
            }
        }
    }
    let end = committed_position(committed);
    committed.finish_node();
    Some(ParsedPattern::new(start..end, primary_accepted))
}

fn probe_pattern_nud<'parse, 'source, 'local, E>(
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> Option<PatternNudRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    probe.input().run(from_fn(recognize_pattern_nud))
}

fn probe_pattern_nud_with_fresh_primary_policy<'parse, 'source, 'local, E>(
    policy: PatternMandatorySlotPolicy,
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> Option<PatternNudRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    probe.input().run(from_fn(|i| {
        recognize_pattern_nud_with_fresh_primary_policy(policy, i)
    }))
}

fn pattern_nud_candidate<'parse, 'source, 'local, E>(
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let i = probe.input();
    let checkpoint = i.checkpoint();
    let candidate = i.run(from_fn(recognize_pattern_nud)).is_some();
    i.rollback(checkpoint);
    candidate
}

fn pattern_nud_candidate_with_fresh_primary_policy<'parse, 'source, 'local, E>(
    policy: PatternMandatorySlotPolicy,
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
        .run(from_fn(|i| {
            recognize_pattern_nud_with_fresh_primary_policy(policy, i)
        }))
        .is_some();
    i.rollback(checkpoint);
    candidate
}

fn exact_dot_dot_pending<'parse, 'source, 'local, E>(
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let i = probe.input();
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_exact_dot_dot).is_some();
    i.rollback(checkpoint);
    pending
}

fn pattern_name_pending<'parse, 'source, 'local, E>(
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let i = probe.input();
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_pattern_name).is_some();
    i.rollback(checkpoint);
    pending
}

fn pipe_pending<'parse, 'source, 'local, E>(probe: &mut Probe<'parse, 'source, 'local, E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let i = probe.input();
    let checkpoint = i.checkpoint();
    let pending = i.run(recognize_pipe).is_some();
    i.rollback(checkpoint);
    pending
}

fn probe_pattern_led<'parse, 'source, 'local, E>(
    minimum: PatternPrecedence,
    pattern_continuation_base: usize,
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> Option<PatternLedRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    probe.input().run(from_fn(|i| {
        recognize_pattern_led(minimum, pattern_continuation_base, i)
    }))
}

fn commit_direct_primary<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    nud: PatternNudRecognition<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| probe.input().cut());
    match nud {
        PatternNudRecognition::Name(name) => {
            committed.start_node(SyntaxKind::IdentifierPattern);
            let kind = match name.lexical_kind() {
                PatternNameKind::Ordinary => SyntaxKind::Identifier,
                PatternNameKind::Sigil => SyntaxKind::SigilIdentifier,
            };
            committed.token(kind, name.range());
            committed.finish_node();
            false
        }
        PatternNudRecognition::Integer(integer) => {
            committed.start_node(SyntaxKind::IntegerPattern);
            committed.token(SyntaxKind::Integer, integer.range());
            committed.finish_node();
            false
        }
        PatternNudRecognition::Symbol { colon, name } => {
            committed.start_node(SyntaxKind::SymbolPattern);
            committed.token(SyntaxKind::Colon, colon);
            committed.token(SyntaxKind::Identifier, name.range());
            committed.finish_node();
            false
        }
        PatternNudRecognition::MalformedSymbol { colon } => {
            committed.start_node(SyntaxKind::SymbolPattern);
            committed.token(SyntaxKind::Colon, colon);
            emit_pattern_missing(
                committed,
                PatternRole::SymbolName,
                ExpectedSyntax::Identifier,
            );
            committed.finish_node();
            false
        }
        PatternNudRecognition::Parenthesized { open } => {
            commit_direct_parenthesized_pattern(table, open, committed)
        }
        PatternNudRecognition::List { open } => {
            commit_direct_list_pattern(table, open, committed);
            false
        }
        PatternNudRecognition::Record { open } => {
            commit_direct_record_pattern(table, open, committed);
            false
        }
    }
}

fn commit_direct_list_pattern<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let policy = PatternDelimitedPolicy::List;
    let outer_stops = committed.probe(|probe| active_stop_set(probe.input()));
    let caller_close_stops = pattern_caller_close_stops(outer_stops);
    let incoming_base = committed.probe(|probe| {
        probe
            .input()
            .local
            .indentation_baseline()
            .map_or(0, |baseline| baseline.column)
    });
    committed.start_node(SyntaxKind::ListPattern);
    committed.token(SyntaxKind::LBracket, open);
    committed
        .probe(|probe| push_pattern_delimited_scope(policy, caller_close_stops, probe.input()));
    let initial = consume_direct_trivia(committed);
    let layout = committed.probe(|probe| {
        LayoutDelimitedFrame::after_opening_trivia(
            incoming_base,
            &initial,
            probe.input().local.line().line_indent,
        )
    });
    committed.probe(|probe| push_pattern_layout_baseline(layout, probe.input()));
    committed.emit_trivia(&initial);
    let _ = commit_direct_pattern_delimited_items(
        table,
        policy,
        layout,
        outer_stops,
        caller_close_stops,
        committed,
    );
}

fn commit_direct_list_item<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(marker) = committed.probe(|probe| probe.input().run(scan_exact_dot_dot)) {
        committed.start_node(SyntaxKind::ListPatternSpreadItem);
        committed.token(SyntaxKind::DotDot, marker);
        committed.probe(|probe| probe.input().cut());
        let trivia = consume_direct_trivia(committed);
        committed.emit_trivia(&trivia);
        parse_direct_pattern_bp(
            table,
            PatternPrecedence::Lowest,
            PatternRole::ListSpreadRhs,
            pattern_role(PatternRole::ListSpreadRhs),
            committed,
        )
        .expect("a committed spread owns a total RHS pattern");
        committed.finish_node();
    } else {
        parse_direct_pattern_bp(
            table,
            PatternPrecedence::Lowest,
            PatternRole::ListItem,
            pattern_role(PatternRole::ListItem),
            committed,
        )
        .expect("a list mandatory item is total after recovery");
    }
}

fn commit_direct_record_pattern<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let policy = PatternDelimitedPolicy::Record;
    let outer_stops = committed.probe(|probe| active_stop_set(probe.input()));
    let caller_close_stops = pattern_caller_close_stops(outer_stops);
    let incoming_base = committed.probe(|probe| {
        probe
            .input()
            .local
            .indentation_baseline()
            .map_or(0, |baseline| baseline.column)
    });
    committed.start_node(SyntaxKind::RecordPattern);
    committed.token(SyntaxKind::LBrace, open);
    committed
        .probe(|probe| push_pattern_delimited_scope(policy, caller_close_stops, probe.input()));
    let initial = consume_direct_trivia(committed);
    let layout = committed.probe(|probe| {
        LayoutDelimitedFrame::after_opening_trivia(
            incoming_base,
            &initial,
            probe.input().local.line().line_indent,
        )
    });
    committed.probe(|probe| push_pattern_layout_baseline(layout, probe.input()));
    committed.emit_trivia(&initial);
    let _ = commit_direct_pattern_delimited_items(
        table,
        policy,
        layout,
        outer_stops,
        caller_close_stops,
        committed,
    );
}

#[derive(Clone, Debug)]
enum RecordFieldIntroducer {
    Colon {
        leading: TriviaRun,
        range: Range<usize>,
    },
    Equals {
        leading: TriviaRun,
        range: Range<usize>,
    },
}

fn record_field_introducer<E>(i: &mut SynIn<E>) -> Option<RecordFieldIntroducer>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let leading = consume_trivia(i);
    if trivia_has_physical_newline(&leading) {
        i.rollback(checkpoint);
        return None;
    }
    if let Some(range) = i.run(recognize_colon) {
        return Some(RecordFieldIntroducer::Colon { leading, range });
    }
    if let Some(range) = i.run(scan_exact_equals) {
        return Some(RecordFieldIntroducer::Equals { leading, range });
    }
    i.rollback(checkpoint);
    None
}

fn commit_direct_record_item<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(marker) = committed.probe(|probe| probe.input().run(scan_exact_dot_dot)) {
        committed.start_node(SyntaxKind::RecordPatternSpreadItem);
        committed.token(SyntaxKind::DotDot, marker);
        committed.probe(|probe| probe.input().cut());
        let trivia = consume_direct_trivia(committed);
        committed.emit_trivia(&trivia);
        parse_direct_pattern_bp(
            table,
            PatternPrecedence::Lowest,
            PatternRole::RecordSpreadRhs,
            pattern_role(PatternRole::RecordSpreadRhs),
            committed,
        )
        .expect("a committed record spread owns a total RHS pattern");
        committed.finish_node();
        return;
    }
    let Some(name) = committed.probe(|probe| probe.input().run(scan_pattern_name)) else {
        emit_pattern_missing(
            committed,
            PatternRole::RecordItem,
            ExpectedSyntax::Identifier,
        );
        return;
    };
    committed.start_node(SyntaxKind::RecordPatternField);
    let kind = match name.lexical_kind() {
        PatternNameKind::Ordinary => SyntaxKind::Identifier,
        PatternNameKind::Sigil => SyntaxKind::SigilIdentifier,
    };
    committed.token(kind, name.range());
    if let Some(introducer) = committed.probe(|probe| record_field_introducer(probe.input())) {
        match introducer {
            RecordFieldIntroducer::Colon { leading, range } => {
                committed.emit_trivia(&leading);
                committed.token(SyntaxKind::Colon, range);
                let trivia = consume_direct_trivia(committed);
                committed.emit_trivia(&trivia);
                let stops =
                    committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Equal));
                committed.probe(|probe| probe.input().local.push_stop_set(stops));
                parse_direct_pattern_bp_with_fresh_primary_policy(
                    table,
                    PatternPrecedence::Lowest,
                    PatternRole::RecordNestedPattern,
                    pattern_role(PatternRole::RecordNestedPattern),
                    PatternMandatorySlotPolicy {
                        fresh_primary_recovery_stops: stops,
                        ..PatternMandatorySlotPolicy::default()
                    },
                    committed,
                )
                .expect("a committed record field owns a total nested pattern");
                committed
                    .probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stops)));
                commit_direct_record_default(table, committed);
            }
            RecordFieldIntroducer::Equals { leading, range } => {
                committed.emit_trivia(&leading);
                commit_direct_record_default_after_equals(table, range, committed);
            }
        }
    }
    committed.finish_node();
}

fn commit_direct_record_default<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let Some((leading, range)) = committed.probe(|probe| record_default_introducer(probe.input()))
    else {
        return;
    };
    committed.emit_trivia(&leading);
    commit_direct_record_default_after_equals(table, range, committed);
}

fn record_default_introducer<E>(i: &mut SynIn<E>) -> Option<(TriviaRun, Range<usize>)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let leading = consume_trivia(i);
    if trivia_has_physical_newline(&leading) {
        i.rollback(checkpoint);
        return None;
    }
    let Some(range) = i.run(scan_exact_equals) else {
        i.rollback(checkpoint);
        return None;
    };
    Some((leading, range))
}

fn commit_direct_record_default_after_equals<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    equals: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.token(SyntaxKind::Equals, equals);
    let trivia = consume_direct_trivia(committed);
    let leading = if trivia.is_empty() {
        LeadingTrivia::None
    } else {
        LeadingTrivia::Present
    };
    committed.emit_trivia(&trivia);
    if parse_direct_expression_with_operators(table, leading, committed).is_none() {
        emit_pattern_missing(
            committed,
            PatternRole::RecordDefaultExpression,
            ExpectedSyntax::Expression,
        );
    }
}

fn commit_direct_parenthesized_pattern<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let policy = PatternDelimitedPolicy::Parenthesized;
    let caller_close_stops =
        committed.probe(|probe| pattern_caller_close_stops(active_stop_set(probe.input())));
    let incoming_base = committed.probe(|probe| {
        probe
            .input()
            .local
            .indentation_baseline()
            .map_or(0, |baseline| baseline.column)
    });
    committed.start_node(SyntaxKind::ParenthesizedPattern);
    committed.token(SyntaxKind::LParen, open);
    committed
        .probe(|probe| push_pattern_delimited_scope(policy, caller_close_stops, probe.input()));
    let initial = consume_direct_trivia(committed);
    let layout = committed.probe(|probe| {
        LayoutDelimitedFrame::after_opening_trivia(
            incoming_base,
            &initial,
            probe.input().local.line().line_indent,
        )
    });
    committed.probe(|probe| push_pattern_layout_baseline(layout, probe.input()));
    committed.emit_trivia(&initial);
    commit_direct_pattern_delimited_items(
        table,
        policy,
        layout,
        StopSet::default(),
        caller_close_stops,
        committed,
    )
}

/// Runs the comma/close/retry control flow shared by parenthesized and list
/// patterns.  The policy selects the item grammar and its recovery boundary.
fn commit_direct_pattern_delimited_items<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    policy: PatternDelimitedPolicy,
    layout: LayoutDelimitedFrame,
    outer_stops: StopSet,
    caller_close_stops: StopSet,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if direct_pattern_delimited_close(policy, committed) {
        finish_pattern_delimited_scope(policy, layout, caller_close_stops, committed);
        return false;
    }
    if committed
        .probe(|probe| outer_pattern_close_stop_pending(policy, caller_close_stops, probe.input()))
    {
        emit_pattern_delimited_close_missing(policy, committed);
        finish_pattern_delimited_scope(policy, layout, caller_close_stops, committed);
        return false;
    }

    loop {
        commit_direct_pattern_delimited_item(table, policy, committed);
        if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
            emit_pattern_delimited_close_missing(policy, committed);
            finish_pattern_delimited_scope(policy, layout, caller_close_stops, committed);
            return false;
        }
        let trivia = consume_direct_trivia(committed);
        committed.emit_trivia(&trivia);
        if let Some(comma) = direct_comma(committed) {
            committed.token(SyntaxKind::Comma, comma);
            let trivia = consume_direct_trivia(committed);
            committed.emit_trivia(&trivia);
            if direct_pattern_delimited_close(policy, committed) {
                finish_pattern_delimited_scope(policy, layout, caller_close_stops, committed);
                return false;
            }
            if committed.probe(|probe| {
                outer_pattern_close_stop_pending(policy, caller_close_stops, probe.input())
            }) {
                emit_pattern_delimited_close_missing(policy, committed);
                finish_pattern_delimited_scope(policy, layout, caller_close_stops, committed);
                return false;
            }
            continue;
        }
        if direct_pattern_delimited_close(policy, committed) {
            finish_pattern_delimited_scope(policy, layout, caller_close_stops, committed);
            return false;
        }
        if committed.probe(|probe| {
            outer_pattern_close_stop_pending(policy, caller_close_stops, probe.input())
        }) {
            emit_pattern_delimited_close_missing(policy, committed);
            finish_pattern_delimited_scope(policy, layout, caller_close_stops, committed);
            return false;
        }
        if committed.probe(|probe| {
            layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent)
        }) == LayoutDelimitedBoundary::ImplicitNewline
        {
            continue;
        }
        if direct_pattern_delimited_item_pending(policy, committed) {
            emit_pattern_missing(
                committed,
                policy.separator_role(),
                policy.separator_expected(),
            );
            continue;
        }
        let (continue_items, close_recovered) = recover_pattern_delimited_separator_or_close(
            policy,
            outer_stops,
            caller_close_stops,
            committed,
        );
        if continue_items {
            continue;
        }
        finish_pattern_delimited_scope(policy, layout, caller_close_stops, committed);
        return close_recovered;
    }
}

fn commit_direct_pattern_delimited_item<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    policy: PatternDelimitedPolicy,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match policy {
        PatternDelimitedPolicy::Parenthesized => commit_parenthesized_element(table, committed),
        PatternDelimitedPolicy::List => commit_direct_list_item(table, committed),
        PatternDelimitedPolicy::Record => commit_direct_record_item(table, committed),
    }
}

fn direct_pattern_delimited_item_pending<'parse, 'source, 'local, E, O>(
    policy: PatternDelimitedPolicy,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match policy {
        PatternDelimitedPolicy::Parenthesized => committed.probe(pattern_nud_candidate),
        PatternDelimitedPolicy::List => {
            committed.probe(exact_dot_dot_pending) || committed.probe(pattern_nud_candidate)
        }
        PatternDelimitedPolicy::Record => {
            committed.probe(exact_dot_dot_pending) || committed.probe(pattern_name_pending)
        }
    }
}

fn recover_pattern_delimited_separator_or_close<'parse, 'source, 'local, E, O>(
    policy: PatternDelimitedPolicy,
    outer_stops: StopSet,
    caller_close_stops: StopSet,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> (bool, bool)
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match policy {
        PatternDelimitedPolicy::Parenthesized => (
            false,
            recover_pattern_delimited_close(policy, caller_close_stops, committed),
        ),
        PatternDelimitedPolicy::List => (
            recover_list_separator_or_close(policy, outer_stops, caller_close_stops, committed),
            false,
        ),
        PatternDelimitedPolicy::Record => (
            recover_record_separator_or_close(policy, outer_stops, caller_close_stops, committed),
            false,
        ),
    }
}

fn commit_parenthesized_element<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    // `parse_direct_pattern_bp` owns the sink-free NUD probe and therefore
    // must perform it itself.  Probing here would consume an accepted primary
    // before that continuation can emit it.
    parse_direct_pattern_bp(
        table,
        PatternPrecedence::Lowest,
        PatternRole::ParenthesizedElement,
        pattern_role(PatternRole::ParenthesizedElement),
        committed,
    )
    .expect("a parenthesized mandatory element is total after recovery");
}

fn direct_pattern_primary_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: PatternRole,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| scan_invalid_run_until_pattern(probe, false));
    let Some((range, retry)) = recovered else {
        return false;
    };
    emit_pattern_error(committed, role, range, ExpectedSyntax::Pattern);
    retry
}

fn direct_pattern_primary_error_retry_with_fresh_primary_policy<'parse, 'source, 'local, E, O>(
    policy: PatternMandatorySlotPolicy,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: PatternRole,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        scan_invalid_run_until_pattern_with_fresh_primary_policy(policy, probe, false)
    });
    let Some((range, retry)) = recovered else {
        return None;
    };
    emit_pattern_error(committed, role, range, ExpectedSyntax::Pattern);
    Some(retry)
}

fn direct_alias_binding_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let i = probe.input();
        let start = i.pos();
        let Some(character) = i.input.remainder().chars().next() else {
            return None;
        };
        if matches!(character, ')' | ',' | '|' | ':') {
            return None;
        }
        i.input.next()?;
        if matches!(character, '$' | '&' | '\'') {
            let _ = i.run(scan_word);
        }
        let end = i.pos();
        Some((start..end, pattern_nud_candidate(probe)))
    });
    let Some((range, retry)) = recovered else {
        return None;
    };
    emit_pattern_error(
        committed,
        PatternRole::AliasBinding,
        range,
        ExpectedSyntax::Identifier,
    );
    Some(retry)
}

/// Consumes one non-empty invalid episode and stops before delimiters.  It
/// probes the shared NUD judge after every byte so the same mandatory slot can
/// retry from a later valid primary without a second diagnostic.
fn scan_invalid_run_until_pattern<'parse, 'source, 'local, E>(
    probe: &mut Probe<'parse, 'source, 'local, E>,
    parenthesized: bool,
) -> Option<(Range<usize>, bool)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = probe.input().pos();
    let mut end = start;
    loop {
        if any_ambient_owner_claims(probe.input()) {
            return (start < end).then_some((start..end, false));
        }
        let i = probe.input();
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < end).then_some((start..end, false));
        };
        if matches!(character, ')' | ']' | '}' | ',' | ';')
            || (!parenthesized && character == ':')
            || arm_stop_pending(i)
        {
            return (start < end).then_some((start..end, false));
        }
        i.input.next()?;
        end = i.pos();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        if pattern_nud_candidate(probe) {
            return Some((start..end, true));
        }
    }
}

fn scan_invalid_run_until_pattern_with_fresh_primary_policy<'parse, 'source, 'local, E>(
    policy: PatternMandatorySlotPolicy,
    probe: &mut Probe<'parse, 'source, 'local, E>,
    parenthesized: bool,
) -> Option<(Range<usize>, bool)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = probe.input().pos();
    let mut end = start;
    loop {
        if any_ambient_owner_claims(probe.input()) {
            return (start < end).then_some((start..end, false));
        }
        if end > start
            && policy
                .fresh_primary_recovery_stops
                .contains(StopKind::Colon)
            && pattern_nud_candidate_with_fresh_primary_policy(policy, probe)
        {
            return Some((start..end, true));
        }
        let i = probe.input();
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < end).then_some((start..end, false));
        };
        if matches!(character, ')' | ']' | '}' | ',' | ';')
            || (!parenthesized && character == ':')
            || fresh_primary_policy_stop_pending(policy, i)
            || arm_stop_pending(i)
        {
            return (start < end).then_some((start..end, false));
        }
        i.input.next()?;
        end = i.pos();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        if pattern_nud_candidate_with_fresh_primary_policy(policy, probe) {
            return Some((start..end, true));
        }
    }
}

fn direct_comma<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
{
    committed.probe(|probe| probe.input().run(recognize_comma))
}

fn direct_pattern_delimited_close<'parse, 'source, 'local, E, O>(
    policy: PatternDelimitedPolicy,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
{
    let Some(close) = committed.probe(|probe| {
        probe
            .input()
            .run(from_fn(|i| recognize_pattern_delimited_close(policy, i)))
    }) else {
        return false;
    };
    committed.token(policy.close_syntax_kind(), close);
    true
}

fn consume_direct_trivia<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> TriviaRun
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| consume_trivia(probe.input()))
}

fn recover_pattern_delimited_close<'parse, 'source, 'local, E, O>(
    policy: PatternDelimitedPolicy,
    caller_close_stops: StopSet,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    debug_assert_eq!(policy, PatternDelimitedPolicy::Parenthesized);
    let mut recovered = false;
    loop {
        match committed.probe(|probe| {
            drive_parenthesized_pattern_close_recovery(caller_close_stops, probe.input())
        }) {
            ParenthesizedPatternCloseRecoveryStep::Complete { close } => {
                committed.token(SyntaxKind::RParen, close);
                return recovered;
            }
            ParenthesizedPatternCloseRecoveryStep::Error { range, unexpected } => {
                emit_pattern_delimited_close_error(policy, committed, range, unexpected);
                recovered = true;
            }
            ParenthesizedPatternCloseRecoveryStep::Missing { at } => {
                debug_assert_eq!(at, committed_position(committed));
                emit_pattern_delimited_close_missing(policy, committed);
                return recovered;
            }
        }
    }
}

/// Consumes one separator error episode, leaving the next item candidate or
/// closing boundary untouched.  A caller-owned arm boundary is an escape only
/// for a missing list close; it is never consumed by the list owner.
fn recover_list_separator_or_close<'parse, 'source, 'local, E, O>(
    policy: PatternDelimitedPolicy,
    outer_stops: StopSet,
    caller_close_stops: StopSet,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut start = None;
    loop {
        if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
            if let Some(start) = start {
                let end = committed_position(committed);
                emit_pattern_error(
                    committed,
                    PatternRole::ListSeparator,
                    start..end,
                    ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Comma),
                );
            }
            emit_pattern_delimited_close_missing(policy, committed);
            return false;
        }
        if committed.probe(|probe| probe.input().input.remainder().is_empty())
            || committed.probe(|probe| outer_arm_stop_pending(outer_stops, probe.input()))
        {
            if let Some(start) = start {
                let end = committed_position(committed);
                emit_pattern_error(
                    committed,
                    PatternRole::ListSeparator,
                    start..end,
                    ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Comma),
                );
            }
            emit_pattern_delimited_close_missing(policy, committed);
            return false;
        }
        if direct_pattern_delimited_close(policy, committed) {
            if let Some(start) = start {
                let end = committed_position(committed);
                emit_pattern_error(
                    committed,
                    PatternRole::ListSeparator,
                    start..end,
                    ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Comma),
                );
            }
            return false;
        }
        if committed.probe(|probe| {
            outer_pattern_close_stop_pending(policy, caller_close_stops, probe.input())
        }) {
            if let Some(start) = start {
                let end = committed_position(committed);
                emit_pattern_error(
                    committed,
                    PatternRole::ListSeparator,
                    start..end,
                    ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Comma),
                );
            }
            emit_pattern_delimited_close_missing(policy, committed);
            return false;
        }
        if committed.probe(exact_dot_dot_pending) || committed.probe(pattern_nud_candidate) {
            if let Some(start) = start {
                let end = committed_position(committed);
                emit_pattern_error(
                    committed,
                    PatternRole::ListSeparator,
                    start..end,
                    ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Comma),
                );
            }
            return true;
        }
        let range = committed.probe(|probe| {
            let i = probe.input();
            let start = i.pos();
            i.input.next()?;
            let end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            Some(start..end)
        });
        if let Some(range) = range {
            start.get_or_insert(range.start);
        }
    }
}

fn recover_record_separator_or_close<'parse, 'source, 'local, E, O>(
    policy: PatternDelimitedPolicy,
    outer_stops: StopSet,
    caller_close_stops: StopSet,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut start = None;
    loop {
        if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
            if let Some(start) = start {
                let end = committed_position(committed);
                emit_pattern_error(
                    committed,
                    PatternRole::RecordSeparator,
                    start..end,
                    ExpectedSyntax::DelimitedSequenceSeparator,
                );
            }
            emit_pattern_delimited_close_missing(policy, committed);
            return false;
        }
        if committed.probe(|probe| probe.input().input.remainder().is_empty())
            || committed.probe(|probe| outer_arm_stop_pending(outer_stops, probe.input()))
        {
            if let Some(start) = start {
                let end = committed_position(committed);
                emit_pattern_error(
                    committed,
                    PatternRole::RecordSeparator,
                    start..end,
                    ExpectedSyntax::DelimitedSequenceSeparator,
                );
            }
            emit_pattern_delimited_close_missing(policy, committed);
            return false;
        }
        if direct_pattern_delimited_close(policy, committed) {
            if let Some(start) = start {
                let end = committed_position(committed);
                emit_pattern_error(
                    committed,
                    PatternRole::RecordSeparator,
                    start..end,
                    ExpectedSyntax::DelimitedSequenceSeparator,
                );
            }
            return false;
        }
        if committed.probe(|probe| {
            outer_pattern_close_stop_pending(policy, caller_close_stops, probe.input())
        }) {
            if let Some(start) = start {
                let end = committed_position(committed);
                emit_pattern_error(
                    committed,
                    PatternRole::RecordSeparator,
                    start..end,
                    ExpectedSyntax::DelimitedSequenceSeparator,
                );
            }
            emit_pattern_delimited_close_missing(policy, committed);
            return false;
        }
        if committed.probe(exact_dot_dot_pending) || committed.probe(pattern_name_pending) {
            if let Some(start) = start {
                let end = committed_position(committed);
                emit_pattern_error(
                    committed,
                    PatternRole::RecordSeparator,
                    start..end,
                    ExpectedSyntax::DelimitedSequenceSeparator,
                );
            }
            return true;
        }
        let range = committed.probe(|probe| {
            let i = probe.input();
            let start = i.pos();
            i.input.next()?;
            let end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            Some(start..end)
        });
        if let Some(range) = range {
            start.get_or_insert(range.start);
        }
    }
}

fn outer_arm_stop_pending<E>(stops: StopSet, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if stops.contains(StopKind::Arrow) && i.input.remainder().starts_with("->") {
        return true;
    }
    let checkpoint = i.checkpoint();
    let word = i.run(scan_word).map(|word| word.text());
    i.rollback(checkpoint);
    matches!(word, Some("if") if stops.contains(StopKind::ArmGuardIf))
        || matches!(word, Some("where") if stops.contains(StopKind::ArmGuardWhere))
        || matches!(word, Some("in") if stops.contains(StopKind::In))
}

/// Recognizes only a carried caller close.  The current container's own close
/// remains its first-priority terminal, even when the same close bit is also
/// active in an outer frame.
fn outer_pattern_close_stop_pending<E>(
    policy: PatternDelimitedPolicy,
    caller_close_stops: StopSet,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        let stop = match punctuation.kind() {
            PunctuationKind::Close(Delimiter::Parenthesis) => StopKind::RightParenthesis,
            PunctuationKind::Close(Delimiter::Bracket) => StopKind::RightBracket,
            PunctuationKind::Close(Delimiter::Brace) => StopKind::RightBrace,
            _ => return false,
        };
        stop != policy.close_stop() && caller_close_stops.contains(stop)
    });
    i.rollback(checkpoint);
    pending
}

fn finish_pattern_delimited_scope<'parse, 'source, 'local, E, O>(
    policy: PatternDelimitedPolicy,
    layout: LayoutDelimitedFrame,
    caller_close_stops: StopSet,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| pop_pattern_layout_baseline(layout, probe.input()));
    committed.probe(|probe| pop_pattern_delimited_scope(policy, caller_close_stops, probe.input()));
    committed.finish_node();
}

fn pattern_role(role: PatternRole) -> GrammarRole {
    GrammarRole::Pattern(role)
}

fn emit_pattern_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: PatternRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_missing_with_role(committed, pattern_role(role), expected);
}

fn emit_missing_with_role<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: GrammarRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
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
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_pattern_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: PatternRole,
    range: Range<usize>,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = pattern_role(role);
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

fn emit_pattern_delimited_close_missing<'parse, 'source, 'local, E, O>(
    policy: PatternDelimitedPolicy,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = policy.close_role();
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
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    policy.delimiter(),
                )),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_pattern_delimited_close_error<'parse, 'source, 'local, E, O>(
    policy: PatternDelimitedPolicy,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
    category: UnexpectedCategory,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = policy.close_role();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category,
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    policy.delimiter(),
                )),
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

#[cfg(test)]
mod tests {
    use super::*;
    use chasa::{input::IsCut, prelude::In};

    use crate::{
        SyntaxKind, SyntaxNode,
        grammar::declaration::parse_direct_root_candidate,
        input::SourceInput,
        operator::{BindingPower, OperatorDeclaration, OperatorFixities, OperatorTable},
        session::{FullCstOutput, ParseLocal},
    };

    #[test]
    fn identifiers_and_integer_primaries_have_the_fixed_pattern_vocabulary() {
        for (source, token) in [
            ("x", SyntaxKind::Identifier),
            ("_", SyntaxKind::Identifier),
            ("_bar", SyntaxKind::SigilIdentifier),
            ("$x", SyntaxKind::SigilIdentifier),
            ("&x", SyntaxKind::SigilIdentifier),
            ("'x", SyntaxKind::SigilIdentifier),
        ] {
            let root = parse_direct(source);
            let pattern = only_child(&root, SyntaxKind::Pattern);
            let primary = pattern.children().next().expect("primary");
            assert_eq!(primary.kind(), SyntaxKind::IdentifierPattern, "{source:?}");
            assert_eq!(
                primary.first_token().expect("name token").kind(),
                token,
                "{source:?}"
            );
        }
        for source in ["0", "42"] {
            let root = parse_direct(source);
            assert!(
                root.descendants()
                    .any(|node| node.kind() == SyntaxKind::IntegerPattern)
            );
            assert!(
                !root
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::OperatorChain)
            );
        }
    }

    #[test]
    fn symbol_pattern_is_two_adjacent_tokens_and_never_an_expression_tail() {
        let root = parse_direct(":foo");
        let symbol = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::SymbolPattern)
            .expect("symbol");
        assert_eq!(
            symbol
                .children_with_tokens()
                .map(|it| it.kind())
                .collect::<Vec<_>>(),
            vec![SyntaxKind::Colon, SyntaxKind::Identifier]
        );
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        );
    }

    #[test]
    fn colon_stop_yields_only_a_non_composite_colon_to_the_caller() {
        assert_eq!(parse_direct_prefix(":foo: body", true), ": body");
        assert_eq!(parse_direct_prefix(": body", true), ": body");
        assert_eq!(parse_direct_prefix(": foo", false), " foo");
    }

    #[test]
    fn required_pattern_fresh_primary_policy_is_isolated_and_preserves_accepted_grammar() {
        let binding = parse_direct_root_candidate("my x: Int = 0", &OperatorTable::default(), &[]);
        assert_eq!(
            SyntaxNode::new_root(binding.green().clone()).to_string(),
            "my x: Int = 0"
        );
        assert!(binding.committed_recoveries().is_empty());

        let colon = PatternMandatorySlotPolicy {
            fresh_primary_recovery_stops: StopSet::default().with(StopKind::Colon),
            ..PatternMandatorySlotPolicy::default()
        };
        let equal = PatternMandatorySlotPolicy {
            fresh_primary_recovery_stops: StopSet::default().with(StopKind::Equal),
            ..PatternMandatorySlotPolicy::default()
        };
        for (source, policy) in [("@: target", colon), ("@= target", equal)] {
            let (ast, remainder) = parse_required_with_policy(source, policy);
            assert!(matches!(ast, Recovered::Incomplete), "{source:?}: {ast:#?}");
            assert_eq!(remainder, &source[1..]);
            let (remainder, recoveries) = parse_direct_required_with_policy(source, policy);
            assert_eq!(remainder, &source[1..]);
            assert!(
                matches!(recoveries.as_slice(), [record]
                if record.kind == RecoveryKind::Error
                    && record.site.role == GrammarRole::Pattern(PatternRole::Primary)
                    && record.site.range == (0..1)),
                "{source:?}: {recoveries:#?}"
            );
        }

        let (symbol, remainder) = parse_required_with_policy(":symbol", colon);
        assert!(matches!(symbol, Recovered::Complete(pattern) if pattern.range() == (0..7)));
        assert_eq!(remainder, "");
        let (annotated, remainder) = parse_required_with_policy("x: Int", colon);
        assert!(
            matches!(annotated, Recovered::Complete(pattern) if pattern.type_annotation().is_some())
        );
        assert_eq!(remainder, "");
        let (record, remainder) = parse_required_with_policy("{x = 1}", equal);
        assert!(matches!(record, Recovered::Complete(pattern) if pattern.range() == (0..7)));
        assert_eq!(remainder, "");
        for (source, policy) in [(":symbol", colon), ("x: Int", colon), ("{x = 1}", equal)] {
            let (remainder, recoveries) = parse_direct_required_with_policy(source, policy);
            assert_eq!(remainder, "", "{source:?}");
            assert!(recoveries.is_empty(), "{source:?}: {recoveries:#?}");
        }

        let recovered_tail = PatternMandatorySlotPolicy {
            recovered_primary_tail_stops: StopSet::default().with(StopKind::Colon),
            ..PatternMandatorySlotPolicy::default()
        };
        let (recovered, remainder) = parse_required_with_policy("(x @): Int", recovered_tail);
        assert!(matches!(recovered, Recovered::Complete(pattern) if pattern.range() == (0..5)));
        assert_eq!(remainder, ": Int");
        let (remainder, recoveries) =
            parse_direct_required_with_policy("(x @): Int", recovered_tail);
        assert_eq!(remainder, ": Int");
        assert!(
            matches!(recoveries.as_slice(), [record]
            if record.kind == RecoveryKind::Error
                && record.site.role == GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ParenthesizedPattern,
                    delimiter: Delimiter::Parenthesis,
                }
                && record.site.range == (3..4)),
            "{recoveries:#?}"
        );

        // Without the explicit recovered-tail reservation, the canonical
        // Pattern grammar still owns its ordinary type annotation.
        let (ordinary, remainder) =
            parse_required_with_policy("(x @): Int", PatternMandatorySlotPolicy::default());
        assert!(matches!(ordinary, Recovered::Complete(pattern)
            if pattern.type_annotation().is_some() && pattern.range() == (0..10)));
        assert_eq!(remainder, "");
        let (annotated, remainder) = parse_required_with_policy("x: Int", recovered_tail);
        assert!(matches!(annotated, Recovered::Complete(pattern)
            if pattern.type_annotation().is_some()));
        assert_eq!(remainder, "");
    }

    #[test]
    fn parenthesized_patterns_accept_comma_or_layout_newline_boundaries() {
        for (source, elements, commas) in [
            ("()", 0, 0),
            ("(a)", 1, 0),
            ("(a,)", 1, 1),
            ("(a,b)", 2, 1),
            ("(a,b,)", 2, 2),
            ("(a\nb)", 2, 0),
            ("(\n  a\n  b\n)", 2, 0),
        ] {
            let root = parse_direct(source);
            let group = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::ParenthesizedPattern)
                .expect("group");
            assert_eq!(
                group
                    .children()
                    .filter(|node| node.kind() == SyntaxKind::Pattern)
                    .count(),
                elements,
                "{source:?}"
            );
            assert_eq!(
                group
                    .children_with_tokens()
                    .filter(|item| item.kind() == SyntaxKind::Comma)
                    .count(),
                commas,
                "{source:?}"
            );
        }
        let (root, recoveries) = parse_direct_recovered("(a\nb)");
        assert_eq!(root.to_string(), "(a\nb)");
        assert!(recoveries.is_empty());
    }

    #[test]
    fn parenthesized_close_recovery_converges_ast_onto_existing_direct_ownership() {
        let source = "((x @))";
        let pattern = parse(source);
        let Pattern {
            head: Recovered::Complete(PatternPrimary::Parenthesized(outer)),
            ..
        } = pattern
        else {
            panic!("outer parenthesized pattern expected: {pattern:#?}");
        };
        let [Recovered::Complete(inner_pattern)] = outer.elements() else {
            panic!("one outer element expected: {outer:#?}");
        };
        let Pattern {
            head: Recovered::Complete(PatternPrimary::Parenthesized(inner)),
            ..
        } = inner_pattern
        else {
            panic!("inner parenthesized pattern expected: {inner_pattern:#?}");
        };
        assert!(matches!(&inner.close, Recovered::Complete(close) if close == &(5..6)));
        assert!(matches!(&outer.close, Recovered::Complete(close) if close == &(6..7)));

        let (root, recoveries) = parse_direct_recovered(source);
        assert_eq!(root.to_string(), source);
        assert!(
            matches!(recoveries.as_slice(), [record]
            if record.kind == RecoveryKind::Error
                && record.site.role == GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ParenthesizedPattern,
                    delimiter: Delimiter::Parenthesis,
                }
                && record.site.range == (4..5)),
            "{recoveries:#?}"
        );
    }

    #[test]
    fn list_patterns_accept_comma_or_layout_newline_and_keep_spread_items() {
        for (source, items, commas) in [
            ("[]", 0, 0),
            ("[a]", 1, 0),
            ("[a,]", 1, 1),
            ("[a,b]", 2, 1),
            ("[a,b,]", 2, 2),
            ("[a,\n b]", 2, 1),
            ("[a\nb]", 2, 0),
            ("[\n  head\n  ..middle\n  tail\n]", 3, 0),
        ] {
            let root = parse_direct(source);
            let list = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::ListPattern)
                .expect("list");
            assert_eq!(
                list.children()
                    .filter(|node| {
                        matches!(
                            node.kind(),
                            SyntaxKind::Pattern | SyntaxKind::ListPatternSpreadItem
                        )
                    })
                    .count(),
                items,
                "{source:?}"
            );
            assert_eq!(
                list.children_with_tokens()
                    .filter(|item| item.kind() == SyntaxKind::Comma)
                    .count(),
                commas,
                "{source:?}"
            );
        }

        let (root, recoveries) = parse_direct_recovered("[head, ..middle, tail]");
        assert_eq!(root.to_string(), "[head, ..middle, tail]");
        assert!(recoveries.is_empty());
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::ListPatternSpreadItem)
                .count(),
            1
        );

        let (root, recoveries) = parse_direct_recovered("[..a, b, ..c]");
        assert!(recoveries.is_empty());
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::ListPatternSpreadItem)
                .count(),
            2
        );

        let root = parse_direct("[..a | b, c]");
        let spread = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ListPatternSpreadItem)
            .expect("spread");
        assert!(
            spread
                .descendants()
                .any(|node| node.kind() == SyntaxKind::PatternAlternationTail)
        );
    }

    #[test]
    fn ambient_if_companion_vetoes_every_pattern_delimited_implicit_newline() {
        for (source, close_role) in [
            (
                "(x\nelse: 0",
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ParenthesizedPattern,
                    delimiter: Delimiter::Parenthesis,
                },
            ),
            (
                "[x\nelse: 0",
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ListPattern,
                    delimiter: Delimiter::Bracket,
                },
            ),
            (
                "{x\nelse: 0",
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::RecordPattern,
                    delimiter: Delimiter::Brace,
                },
            ),
        ] {
            let (pattern, remainder) = parse_with_active_if_companion(source);
            assert_eq!(
                remainder, "\nelse: 0",
                "AST keeps the original gap: {source:?}"
            );
            match &pattern.head {
                Recovered::Complete(PatternPrimary::Parenthesized(group)) => {
                    assert_eq!(group.elements().len(), 1, "{source:?}");
                    assert!(matches!(group.close, Recovered::Incomplete), "{source:?}");
                }
                Recovered::Complete(PatternPrimary::List(list)) => {
                    assert_eq!(list.items().len(), 1, "{source:?}");
                    assert!(matches!(list.close, Recovered::Incomplete), "{source:?}");
                }
                Recovered::Complete(PatternPrimary::Record(record)) => {
                    assert_eq!(record.items().len(), 1, "{source:?}");
                    assert!(matches!(record.close, Recovered::Incomplete), "{source:?}");
                }
                other => panic!("delimited pattern expected for {source:?}: {other:#?}"),
            }
            let (remainder, recoveries) = parse_direct_with_active_if_companion(source);
            assert_eq!(
                remainder, "\nelse: 0",
                "direct CST keeps the original gap: {source:?}"
            );
            assert!(
                matches!(recoveries.as_slice(),
                    [CommittedRecoveryRecord { kind: RecoveryKind::Missing, site, .. }]
                        if site.role == close_role && site.range == (2..2)
                ),
                "{source:?}: {recoveries:#?}"
            );
        }
    }

    #[test]
    fn binding_list_pattern_preserves_else_arm_after_an_ambient_veto() {
        let source = "if condition:\n  my [x\nelse: 0";
        let root = parse_direct_expression(source);
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::ElseArm)
                .count(),
            1,
            "{root:#?}"
        );
        let list = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ListPattern)
            .expect("binding target ListPattern");
        assert_eq!(
            list.children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1
        );
    }

    #[test]
    fn pattern_delimited_malformed_recovery_returns_the_same_ambient_gap() {
        for (source, separator_role, close_role) in [
            (
                "(x @\nelse: 0",
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ParenthesizedPattern,
                    delimiter: Delimiter::Parenthesis,
                },
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ParenthesizedPattern,
                    delimiter: Delimiter::Parenthesis,
                },
            ),
            (
                "[x @\nelse: 0",
                GrammarRole::Pattern(PatternRole::ListSeparator),
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ListPattern,
                    delimiter: Delimiter::Bracket,
                },
            ),
            (
                "{x @\nelse: 0",
                GrammarRole::Pattern(PatternRole::RecordSeparator),
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::RecordPattern,
                    delimiter: Delimiter::Brace,
                },
            ),
        ] {
            let (remainder, recoveries) = parse_direct_with_active_if_companion(source);
            assert_eq!(remainder, "\nelse: 0", "{source:?}");
            assert!(
                matches!(recoveries.as_slice(),
                    [first, close]
                        if first.kind == RecoveryKind::Error
                            && first.site.role == separator_role
                            && first.site.range == (3..4)
                            && close.kind == RecoveryKind::Missing
                            && close.site.role == close_role
                            && close.site.range == (4..4)
                ),
                "{source:?}: {recoveries:#?}"
            );
        }
    }

    #[test]
    fn list_pattern_recovery_preserves_item_and_separator_boundaries() {
        for (source, role) in [
            ("[,a]", PatternRole::ListItem),
            ("[a,,b]", PatternRole::ListItem),
            ("[a b]", PatternRole::ListSeparator),
            ("[a ..b]", PatternRole::ListSeparator),
            ("[a; b]", PatternRole::ListSeparator),
            ("[a, @ b]", PatternRole::ListItem),
            ("[..]", PatternRole::ListSpreadRhs),
            ("[..,a]", PatternRole::ListSpreadRhs),
            ("[..@tail]", PatternRole::ListSpreadRhs),
        ] {
            let (root, recoveries) = parse_direct_recovered(source);
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(
                recoveries
                    .iter()
                    .any(|record| record.site.role == GrammarRole::Pattern(role)),
                "{source:?}: {recoveries:#?}"
            );
        }

        for source in ["[...,a]", "[..+,a]"] {
            let (root, recoveries) = parse_direct_recovered(source);
            assert_eq!(root.to_string(), source);
            assert!(
                recoveries
                    .iter()
                    .any(|record| record.kind == RecoveryKind::Error)
            );
            assert!(
                !root
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::ListPatternSpreadItem)
            );
        }

        for source in ["[a", "[a)"] {
            let (root, recoveries) = parse_direct_recovered(source);
            assert_eq!(root.to_string(), source);
            assert!(recoveries.iter().any(|record| matches!(
                record.site.role,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ListPattern,
                    ..
                }
            )));
        }
    }

    #[test]
    fn list_pattern_typed_recovery_contract_has_direct_coverage_for_every_list_row() {
        for (source, has_recovery) in [
            ("[]", false),
            ("[a,]", false),
            ("[,a]", true),
            ("[a,,b]", true),
            ("[a b]", true),
            ("[a ..b]", true),
            ("[a; b]", true),
            ("[a, @ b]", true),
            ("[..tail]", false),
            ("[..]", true),
            ("[..,a]", true),
            ("[..@tail]", true),
            ("[...,a]", true),
            ("[a", true),
            ("[a)", true),
        ] {
            let (root, recoveries) = parse_direct_recovered(source);
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(!recoveries.is_empty(), has_recovery, "{source:?}");
        }
    }

    #[test]
    fn alias_and_alternation_follow_the_fixed_pratt_order() {
        let root = parse_direct("A | B as c");
        let outer = only_child(&root, SyntaxKind::Pattern);
        let alternation = outer
            .children()
            .find(|node| node.kind() == SyntaxKind::PatternAlternationTail)
            .expect("outer alternation");
        assert!(
            alternation
                .descendants()
                .any(|node| node.kind() == SyntaxKind::PatternAliasTail)
        );

        let root = parse_direct("A as x | B");
        let outer = only_child(&root, SyntaxKind::Pattern);
        assert_eq!(
            outer
                .children()
                .filter(|node| node.kind() == SyntaxKind::PatternAliasTail)
                .count(),
            1
        );
        assert_eq!(
            outer
                .children()
                .filter(|node| node.kind() == SyntaxKind::PatternAlternationTail)
                .count(),
            1
        );

        let root = parse_direct("A | B | C");
        let outer = only_child(&root, SyntaxKind::Pattern);
        let tail = outer
            .children()
            .find(|node| node.kind() == SyntaxKind::PatternAlternationTail)
            .expect("tail");
        assert_eq!(
            tail.children()
                .filter(|node| node.kind() == SyntaxKind::Pattern)
                .count(),
            1
        );
        let rhs = tail
            .children()
            .find(|node| node.kind() == SyntaxKind::Pattern)
            .expect("recursive rhs");
        assert_eq!(
            rhs.children()
                .filter(|node| node.kind() == SyntaxKind::PatternAlternationTail)
                .count(),
            1
        );

        let root = parse_direct("A as x as y");
        assert_eq!(
            only_child(&root, SyntaxKind::Pattern)
                .children()
                .filter(|node| node.kind() == SyntaxKind::PatternAliasTail)
                .count(),
            2
        );
    }

    #[test]
    fn type_annotation_is_terminal_and_qualifies_the_outer_pattern() {
        let pattern = parse("A | B as c: Int");
        assert!(matches!(pattern.tails(), [PatternTail::Alternation(_)]));
        let annotation = pattern.type_annotation().expect("outer annotation");
        assert_eq!(annotation.range(), 10..15);
        assert!(matches!(annotation.type_expr(), Recovered::Complete(_)));

        let root = parse_direct("A | B as c: Int");
        let outer = only_child(&root, SyntaxKind::Pattern);
        assert_eq!(
            outer
                .children()
                .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
                .count(),
            1
        );
        let alternation = outer
            .children()
            .find(|node| node.kind() == SyntaxKind::PatternAlternationTail)
            .expect("alternation");
        assert!(
            alternation
                .descendants()
                .any(|node| node.kind() == SyntaxKind::PatternAliasTail)
        );

        for source in ["A as c: Int", "A | B: Int"] {
            let root = parse_direct(source);
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
                    .count(),
                1,
                "{source:?}"
            );
        }
        assert_eq!(parse_direct_prefix("x: T: U", false), ": U");
    }

    #[test]
    fn type_annotation_reaches_nested_patterns_and_keeps_record_colons_owned() {
        for source in ["(x: Int)", "[x: Int]", "{a: A: Inner}", "{a: A} : SomeType"] {
            let root = parse_direct(source);
            assert_eq!(root.to_string(), source);
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
                    .count(),
                1,
                "{source:?}"
            );
        }
    }

    #[test]
    fn type_annotation_trivia_ranges_and_recovery_keep_owner_boundaries() {
        for source in ["x:Int", "x /* note */ : Int", "x\n  : Int"] {
            let root = parse_direct(source);
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(
                root.descendants()
                    .any(|node| node.kind() == SyntaxKind::PatternTypeAnnotation),
                "{source:?}: {root:#?}"
            );
        }
        assert_eq!(parse_direct_prefix("x::T", false), "::T");
        assert_eq!(parse_direct_prefix("x\n: Int", false), "\n: Int");

        let complete = parse("x: Int");
        assert_eq!(complete.range(), 0..6);
        assert_eq!(
            complete.type_annotation().expect("annotation").range(),
            1..6
        );
        let incomplete = parse("x:");
        assert_eq!(incomplete.range(), 0..2);
        let annotation = incomplete.type_annotation().expect("accepted colon");
        assert_eq!(annotation.range(), 1..2);
        assert!(matches!(annotation.type_expr(), Recovered::Incomplete));

        let (root, recoveries) = parse_direct_recovered("x: @Int");
        assert_eq!(root.to_string(), "x: @Int");
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
        );
        assert!(recoveries.iter().any(|record| {
            record.kind == RecoveryKind::Error
                && record.site.role == GrammarRole::Type(crate::session::TypeRole::Primary)
                && record.site.range == (3..4)
        }));

        for source in ["[x: Int, y]", "[x: , y]", "[x: @, y]", "(x: )"] {
            let (root, recoveries) = parse_direct_recovered(source);
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(
                root.descendants()
                    .any(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
            );
            assert!(
                recoveries
                    .iter()
                    .all(|record| record.site.range.end <= source.len())
            );
        }
    }

    #[test]
    fn annotation_malformed_recovery_uses_the_nested_pattern_base() {
        let source = "{\n  field:\n    x: @\n    Int\n}";
        let ast = parse(source);
        let Recovered::Complete(PatternPrimary::Record(record)) = &ast.head else {
            panic!("record pattern expected: {ast:#?}");
        };
        let [
            Recovered::Complete(RecordPatternItem::Field(RecordPatternField {
                form:
                    RecordPatternFieldForm::Nested {
                        pattern: Recovered::Complete(pattern),
                        ..
                    },
                ..
            })),
            Recovered::Complete(RecordPatternItem::Field(RecordPatternField {
                name: PatternNameSpan { text: "Int", .. },
                form: RecordPatternFieldForm::Shorthand,
                ..
            })),
        ] = record.items()
        else {
            panic!("nested field followed by the outer Int field expected: {record:#?}");
        };
        assert!(
            matches!(pattern.type_annotation(), Some(annotation)
            if matches!(annotation.type_expr(), Recovered::Incomplete)),
            "{pattern:#?}"
        );

        let (root, recoveries) = parse_direct_recovered(source);
        assert_eq!(root.to_string(), source);
        assert!(
            matches!(recoveries.as_slice(), [primary, separator]
            if primary.kind == RecoveryKind::Error
                && primary.site.role == GrammarRole::Type(crate::session::TypeRole::Primary)
                && primary.site.range == (18..19)
                && separator.kind == RecoveryKind::Missing
                && separator.site.role == GrammarRole::Pattern(PatternRole::RecordSeparator)
                && separator.site.range == (24..24)),
            "{recoveries:#?}"
        );
        let annotation = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
            .expect("annotation CST node");
        assert!(
            !annotation
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Identifier)
        );
    }

    #[test]
    fn enclosing_binding_case_and_catch_owners_keep_annotation_boundaries() {
        for source in ["my x: Int = 0", "my y: = 1"] {
            let output = parse_direct_root_candidate(source, &OperatorTable::default(), &[]);
            let recoveries = output.committed_recoveries();
            let root = SyntaxNode::new_root(output.green().clone());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(
                root.descendants()
                    .any(|node| node.kind() == SyntaxKind::PatternTypeAnnotation),
                "{source:?}"
            );
            if source == "my y: = 1" {
                assert!(recoveries.iter().any(|record| {
                    record.kind == RecoveryKind::Missing
                        && record.site.role == GrammarRole::Pattern(PatternRole::TypeAnnotation)
                }));
            }
        }

        for source in [
            "case value: x: Int -> 0",
            "case value: x: Int if ready -> 0",
            "case value: x: Int where ready -> 0",
            "catch action { err: Error, handler: Result -> recover }",
        ] {
            let root = parse_direct_expression(source);
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(
                root.descendants()
                    .any(|node| node.kind() == SyntaxKind::PatternTypeAnnotation),
                "{source:?}"
            );
        }
    }

    #[test]
    fn dynamic_operator_tables_cannot_change_pattern_cst() {
        let low = OperatorTable::from_declarations([
            OperatorDeclaration::new(
                "|",
                OperatorFixities::new()
                    .with_infix(BindingPower::scalar(1), BindingPower::scalar(1)),
            ),
            OperatorDeclaration::new(
                "..",
                OperatorFixities::new()
                    .with_infix(BindingPower::scalar(1), BindingPower::scalar(1)),
            ),
        ])
        .unwrap();
        let high = OperatorTable::from_declarations([
            OperatorDeclaration::new(
                "|",
                OperatorFixities::new()
                    .with_infix(BindingPower::scalar(99), BindingPower::scalar(99)),
            ),
            OperatorDeclaration::new(
                "..",
                OperatorFixities::new()
                    .with_infix(BindingPower::scalar(99), BindingPower::scalar(99)),
            ),
        ])
        .unwrap();
        assert_eq!(
            parse_direct_ignoring_operator_table("A | B as c", &low).green(),
            parse_direct_ignoring_operator_table("A | B as c", &high).green()
        );
        assert_eq!(
            parse_direct_ignoring_operator_table("[a, ..tail]", &low).green(),
            parse_direct_ignoring_operator_table("[a, ..tail]", &high).green()
        );
        // The direct entrypoint does not receive either table; this check pins
        // that API boundary in addition to the identical CST assertion.
    }

    #[test]
    fn mandatory_slot_recovery_keeps_accepted_syntax_and_one_record_per_slot() {
        for (source, expected) in [
            ("", vec![(RecoveryKind::Missing, 0..0)]),
            ("@ x", vec![(RecoveryKind::Error, 0..2)]),
            ("A as", vec![(RecoveryKind::Missing, 4..4)]),
            ("A as $x", vec![(RecoveryKind::Error, 5..7)]),
            ("A |", vec![(RecoveryKind::Missing, 3..3)]),
            ("A | | B", vec![(RecoveryKind::Missing, 4..4)]),
            (":", vec![(RecoveryKind::Missing, 1..1)]),
            ("(,a)", vec![(RecoveryKind::Missing, 1..1)]),
            ("(a", vec![(RecoveryKind::Missing, 2..2)]),
            (
                "(a]",
                vec![(RecoveryKind::Error, 2..3), (RecoveryKind::Missing, 3..3)],
            ),
        ] {
            let (root, recoveries) = parse_direct_recovered(source);
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                recoveries
                    .iter()
                    .map(|record| (record.kind, record.site.range.clone()))
                    .collect::<Vec<_>>(),
                expected,
                "{source:?}"
            );
        }

        let (_, alternation) = parse_direct_recovered("A |");
        assert_eq!(
            alternation[0].site.role,
            GrammarRole::Pattern(PatternRole::AlternationRhs)
        );
        let (_, alias) = parse_direct_recovered("A as $x");
        assert_eq!(
            alias[0].site.role,
            GrammarRole::Pattern(PatternRole::AliasBinding)
        );
        let (_, empty) = parse_direct_recovered("");
        assert_eq!(
            empty[0].site.role,
            GrammarRole::Pattern(PatternRole::Primary)
        );
    }

    #[test]
    fn excluded_forms_remain_unconsumed_after_a_first_slice_pattern() {
        for source in ["\"a\"", "A::B", "A.field", "Some(x)", "Some x"] {
            assert!(!parse_direct_prefix(source, false).is_empty(), "{source:?}");
        }
    }

    #[test]
    fn ast_and_direct_paths_agree_on_the_core_shapes() {
        let pattern = parse("(:foo, _bar,) | 42 as name");
        assert_eq!(pattern.range(), 0..26);
        assert!(matches!(pattern.tails(), [PatternTail::Alternation(_)]));
        let root = parse_direct("(:foo, _bar,) | 42 as name");
        assert_eq!(root.to_string(), "(:foo, _bar,) | 42 as name");

        let list = parse("[head, ..middle, tail]");
        let Recovered::Complete(PatternPrimary::List(list)) = &list.head else {
            panic!("list source must produce a list primary");
        };
        assert_eq!(list.items().len(), 3);
        assert!(matches!(
            list.items()[1],
            Recovered::Complete(ListPatternItem::Spread(_))
        ));
        let root = parse_direct("[head, ..middle, tail]");
        assert_eq!(root.to_string(), "[head, ..middle, tail]");
    }

    #[test]
    fn record_patterns_keep_field_forms_spreads_layout_and_recovery_local() {
        let source = "{a, width: local_width = 1, height = fallback, ..rest,}";
        let pattern = parse(source);
        let Recovered::Complete(PatternPrimary::Record(record)) = &pattern.head else {
            panic!("record source must produce a record primary");
        };
        assert_eq!(record.items().len(), 4);
        assert!(matches!(
            record.items()[0],
            Recovered::Complete(RecordPatternItem::Field(RecordPatternField {
                form: RecordPatternFieldForm::Shorthand,
                ..
            }))
        ));
        assert!(matches!(
            record.items()[1],
            Recovered::Complete(RecordPatternItem::Field(RecordPatternField {
                form: RecordPatternFieldForm::Nested {
                    default: Some(_),
                    ..
                },
                ..
            }))
        ));
        assert!(matches!(
            record.items()[2],
            Recovered::Complete(RecordPatternItem::Field(RecordPatternField {
                form: RecordPatternFieldForm::Default(_),
                ..
            }))
        ));
        assert!(matches!(
            record.items()[3],
            Recovered::Complete(RecordPatternItem::Spread(_))
        ));
        assert!(record.trailing_comma().is_some());

        for source in [
            "{}",
            "{a\nb}",
            "{a,\n b}",
            "{\n  a\n  b\n}",
            "{..left, a, ..right}",
            "{a b}",
            "{a\n  b}",
            "{a; b}",
            "{,a}",
            "{a:}",
            "{a: = 1}",
            "{a =}",
            "{a == value}",
            "{..}",
            "{...a}",
            "{outer: {x = 1} = fallback, value = (a, b)}",
        ] {
            let root = parse_direct(source);
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(
                root.descendants()
                    .any(|node| node.kind() == SyntaxKind::RecordPattern)
            );
        }

        let (root, recoveries) = parse_direct_recovered("{a b}");
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::RecordPattern)
            .expect("record");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::RecordPatternField)
                .count(),
            2
        );
        assert!(matches!(
            recoveries.as_slice(),
            [CommittedRecoveryRecord { kind: RecoveryKind::Missing, site, .. }]
                if site.role == GrammarRole::Pattern(PatternRole::RecordSeparator)
                    && site.range == (3..3)
        ));
    }

    #[test]
    fn gate3b_ordinary_primary_control_record_pattern() {
        fn assert_record(
            source: &str,
            index: usize,
            kind: RecoveryKind,
            role: GrammarRole,
            range: Range<usize>,
            expected: ExpectedSyntax,
        ) {
            let (_, records) = parse_direct_recovered(source);
            assert_eq!(records.len(), 1, "record count: {source:?}");
            let record = &records[index];
            assert_eq!(record.kind, kind, "kind: {source:?} record {index}");
            assert_eq!(record.site.role, role, "role: {source:?} record {index}");
            assert_eq!(record.site.range, range, "range: {source:?} record {index}");
            assert_eq!(
                record.expectations[record.primary_expectation].expected,
                expected,
                "primary expectation: {source:?} record {index}",
            );
        }

        for (source, kind, role, range, expected) in [
            (
                "{,a}",
                RecoveryKind::Missing,
                GrammarRole::Pattern(PatternRole::RecordItem),
                1..1,
                ExpectedSyntax::Identifier,
            ),
            (
                "{a:}",
                RecoveryKind::Missing,
                GrammarRole::Pattern(PatternRole::RecordNestedPattern),
                3..3,
                ExpectedSyntax::Pattern,
            ),
            (
                "{a =}",
                RecoveryKind::Missing,
                GrammarRole::Pattern(PatternRole::RecordDefaultExpression),
                4..4,
                ExpectedSyntax::Expression,
            ),
            (
                "{..}",
                RecoveryKind::Missing,
                GrammarRole::Pattern(PatternRole::RecordSpreadRhs),
                3..3,
                ExpectedSyntax::Pattern,
            ),
            (
                "{a b}",
                RecoveryKind::Missing,
                GrammarRole::Pattern(PatternRole::RecordSeparator),
                3..3,
                ExpectedSyntax::DelimitedSequenceSeparator,
            ),
            (
                "{a; b}",
                RecoveryKind::Error,
                GrammarRole::Pattern(PatternRole::RecordSeparator),
                2..4,
                ExpectedSyntax::DelimitedSequenceSeparator,
            ),
            (
                "{a",
                RecoveryKind::Missing,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::RecordPattern,
                    delimiter: Delimiter::Brace,
                },
                2..2,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
            ),
            (
                "{a: @}",
                RecoveryKind::Error,
                GrammarRole::Pattern(PatternRole::RecordNestedPattern),
                4..5,
                ExpectedSyntax::Pattern,
            ),
        ] {
            assert_record(source, 0, kind, role, range, expected);
        }

        let (root, records) = parse_direct_recovered("{a: @}");
        assert_eq!(records.len(), 1);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            0,
        );
    }

    #[test]
    fn pattern_caller_close_propagation_is_right_close_only() {
        for (source, arm_stop) in [
            ("(x ->)", StopKind::Arrow),
            ("(x if)", StopKind::ArmGuardIf),
            ("(x where)", StopKind::ArmGuardWhere),
        ] {
            let plain_ast = parse(source);
            let (active_ast, active_remainder) = parse_with_active_stop(source, arm_stop);
            assert_eq!(active_remainder, "");
            assert_eq!(active_ast, plain_ast, "AST must not inherit {arm_stop:?}");

            let (plain_direct, plain_recoveries) = parse_direct_recovered(source);
            let (active_direct, active_recoveries) =
                parse_direct_with_active_stop_complete(source, arm_stop);
            assert_eq!(active_direct.to_string(), plain_direct.to_string());
            assert_eq!(
                active_recoveries, plain_recoveries,
                "Parenthesized direct has no {arm_stop:?} query"
            );
        }

        for source in ["[x ->", "{x ->"] {
            let (ast, remainder) = parse_with_active_stop(source, StopKind::Arrow);
            assert_eq!(
                remainder, "",
                "AST keeps arm stops out of its local scope: {source:?}"
            );
            assert_eq!(ast.range(), 0..source.len(), "{source:?}");

            let (remainder, recoveries) = parse_direct_with_active_stop(source, StopKind::Arrow);
            assert_eq!(
                remainder, "->",
                "direct List/Record retain their existing arm query: {source:?}"
            );
            assert!(
                matches!(recoveries.as_slice(), [missing]
                    if missing.kind == RecoveryKind::Missing && missing.site.range == (3..3)
                ),
                "{source:?}: {recoveries:#?}"
            );
        }

        for (source, caller_stop, close_role, caller_boundary, error_end) in [
            (
                "(x @)",
                StopKind::RightParenthesis,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ParenthesizedPattern,
                    delimiter: Delimiter::Parenthesis,
                },
                false,
                4,
            ),
            (
                "(x @]",
                StopKind::RightBracket,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ParenthesizedPattern,
                    delimiter: Delimiter::Parenthesis,
                },
                true,
                4,
            ),
            (
                "(x @}",
                StopKind::RightBrace,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ParenthesizedPattern,
                    delimiter: Delimiter::Parenthesis,
                },
                true,
                4,
            ),
            (
                "[x @)",
                StopKind::RightParenthesis,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ListPattern,
                    delimiter: Delimiter::Bracket,
                },
                true,
                4,
            ),
            (
                "[x @]",
                StopKind::RightBracket,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ListPattern,
                    delimiter: Delimiter::Bracket,
                },
                false,
                5,
            ),
            (
                "[x @}",
                StopKind::RightBrace,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ListPattern,
                    delimiter: Delimiter::Bracket,
                },
                true,
                4,
            ),
            (
                "{x @)",
                StopKind::RightParenthesis,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::RecordPattern,
                    delimiter: Delimiter::Brace,
                },
                true,
                4,
            ),
            (
                "{x @]",
                StopKind::RightBracket,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::RecordPattern,
                    delimiter: Delimiter::Brace,
                },
                true,
                4,
            ),
            (
                "{x @}",
                StopKind::RightBrace,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::RecordPattern,
                    delimiter: Delimiter::Brace,
                },
                false,
                5,
            ),
        ] {
            let (ast, ast_remainder) = parse_with_active_stop(source, caller_stop);
            let expected_remainder = if caller_boundary { &source[4..] } else { "" };
            let expected_end = if caller_boundary { 4 } else { source.len() };
            assert_eq!(
                ast.range(),
                0..expected_end,
                "AST close ownership: {source:?}"
            );
            assert_eq!(
                ast_remainder, expected_remainder,
                "AST close ownership: {source:?}"
            );

            let (direct_remainder, recoveries) = parse_direct_with_active_stop(source, caller_stop);
            assert_eq!(
                direct_remainder, expected_remainder,
                "direct close ownership: {source:?}"
            );
            if caller_boundary {
                assert!(
                    matches!(recoveries.as_slice(), [error, missing]
                        if error.kind == RecoveryKind::Error
                            && error.site.range == (3..error_end)
                            && missing.kind == RecoveryKind::Missing
                            && missing.site.role == close_role
                            && missing.site.range == (4..4)
                    ),
                    "{source:?}: {recoveries:#?}"
                );
            } else {
                assert!(
                    matches!(recoveries.as_slice(), [error]
                        if error.kind == RecoveryKind::Error && error.site.range == (3..error_end)
                    ),
                    "{source:?}: {recoveries:#?}"
                );
            }
        }
    }

    fn parse<'source>(source: &'source str) -> Pattern<'source> {
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
        let table = OperatorTable::default();
        let pattern = i
            .run(from_fn(|i| parse_pattern(&table, i)))
            .expect("pattern AST");
        assert_eq!(i.input.remainder(), "");
        pattern
    }

    fn parse_with_active_stop<'source>(
        source: &'source str,
        stop: StopKind,
    ) -> (Pattern<'source>, &'source str) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let stops = StopSet::default().with(stop);
        local.push_stop_set(stops);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let (pattern, remainder) = {
            let mut i = In::new(
                &mut source_input,
                &mut expectations,
                IsCut::new(&mut is_cut),
            )
            .set_local(&mut local);
            let pattern = i
                .run(from_fn(|i| parse_pattern(&OperatorTable::default(), i)))
                .expect("pattern AST");
            (pattern, i.input.remainder())
        };
        assert_eq!(local.pop_stop_set(), Some(stops));
        (pattern, remainder)
    }

    fn parse_required_with_policy<'source>(
        source: &'source str,
        policy: PatternMandatorySlotPolicy,
    ) -> (Recovered<Box<Pattern<'source>>>, &'source str) {
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
        let parsed = i
            .run(from_fn(|i| {
                Some(parse_required_pattern_with_outer_missing_role_and_policy(
                    &OperatorTable::default(),
                    None,
                    policy,
                    i,
                ))
            }))
            .expect("required Pattern entry is total");
        (parsed, i.input.remainder())
    }

    fn parse_direct_required_with_policy<'source>(
        source: &'source str,
        policy: PatternMandatorySlotPolicy,
    ) -> (&'source str, Vec<CommittedRecoveryRecord>) {
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
        commit_direct_pattern_with_outer_missing_role_and_policy(
            &OperatorTable::default(),
            LeadingTrivia::None,
            None,
            policy,
            &mut committed,
        );
        let remainder = committed.probe(|probe| probe.input().input.remainder());
        let recoveries = committed.into_output().committed_recoveries().to_vec();
        (remainder, recoveries)
    }

    fn parse_direct(source: &str) -> SyntaxNode {
        let (root, remainder, _) = parse_direct_inner(source, false);
        assert_eq!(remainder, "", "complete pattern source");
        root.expect("complete direct CST")
    }

    fn parse_direct_ignoring_operator_table(source: &str, _table: &OperatorTable) -> SyntaxNode {
        parse_direct(source)
    }

    fn parse_direct_recovered(source: &str) -> (SyntaxNode, Vec<CommittedRecoveryRecord>) {
        let (root, remainder, recoveries) = parse_direct_inner(source, false);
        assert_eq!(remainder, "", "recovered pattern source");
        (root.expect("complete direct CST"), recoveries)
    }

    fn parse_direct_with_active_stop<'source>(
        source: &'source str,
        stop: StopKind,
    ) -> (&'source str, Vec<CommittedRecoveryRecord>) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let stops = StopSet::default().with(stop);
        local.push_stop_set(stops);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let (remainder, recoveries) = {
            let i = In::new(
                &mut source_input,
                &mut expectations,
                IsCut::new(&mut is_cut),
            )
            .set_local(&mut local);
            let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
            committed.start_node(SyntaxKind::Root);
            parse_direct_pattern(
                &OperatorTable::default(),
                LeadingTrivia::None,
                &mut committed,
            )
            .expect("direct pattern");
            let remainder = committed.probe(|probe| probe.input().input.remainder());
            let recoveries = committed.into_output().committed_recoveries().to_vec();
            (remainder, recoveries)
        };
        assert_eq!(local.pop_stop_set(), Some(stops));
        (remainder, recoveries)
    }

    fn parse_direct_with_active_stop_complete(
        source: &str,
        stop: StopKind,
    ) -> (SyntaxNode, Vec<CommittedRecoveryRecord>) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let stops = StopSet::default().with(stop);
        local.push_stop_set(stops);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let (root, recoveries) = {
            let i = In::new(
                &mut source_input,
                &mut expectations,
                IsCut::new(&mut is_cut),
            )
            .set_local(&mut local);
            let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
            committed.start_node(SyntaxKind::Root);
            parse_direct_pattern(
                &OperatorTable::default(),
                LeadingTrivia::None,
                &mut committed,
            )
            .expect("direct pattern");
            assert_eq!(committed.probe(|probe| probe.input().input.remainder()), "");
            committed.finish_node();
            let output = committed.into_output();
            let recoveries = output.committed_recoveries().to_vec();
            (SyntaxNode::new_root(output.finish_complete()), recoveries)
        };
        assert_eq!(local.pop_stop_set(), Some(stops));
        (root, recoveries)
    }

    fn parse_direct_expression(source: &str) -> SyntaxNode {
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
        parse_direct_expression_with_operators(
            &OperatorTable::default(),
            LeadingTrivia::None,
            &mut committed,
        )
        .expect("direct expression");
        assert_eq!(committed.probe(|probe| probe.input().input.remainder()), "");
        committed.finish_node();
        SyntaxNode::new_root(committed.into_output().finish_complete())
    }

    fn parse_direct_prefix(source: &str, colon_stop: bool) -> &str {
        let (_, remainder, _) = parse_direct_inner(source, colon_stop);
        remainder
    }

    fn parse_direct_inner<'source>(
        source: &'source str,
        colon_stop: bool,
    ) -> (
        Option<SyntaxNode>,
        &'source str,
        Vec<CommittedRecoveryRecord>,
    ) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        if colon_stop {
            local.push_stop_set(StopSet::default().with(StopKind::Colon));
        }
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
        let table = OperatorTable::default();
        parse_direct_pattern(&table, LeadingTrivia::None, &mut committed).expect("direct pattern");
        let remainder = committed.probe(|probe| probe.input().input.remainder());
        let recoveries = committed.into_output().committed_recoveries().to_vec();
        if remainder.is_empty() {
            // Build a fresh complete output; the prefix path intentionally
            // cannot finish a lossless sink while caller-owned bytes remain.
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            if colon_stop {
                local.push_stop_set(StopSet::default().with(StopKind::Colon));
            }
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
            let table = OperatorTable::default();
            parse_direct_pattern(&table, LeadingTrivia::None, &mut committed)
                .expect("direct pattern");
            committed.finish_node();
            let output = committed.into_output();
            return (
                Some(SyntaxNode::new_root(output.finish_complete())),
                remainder,
                recoveries,
            );
        }
        (None, remainder, recoveries)
    }

    fn parse_with_active_if_companion<'source>(
        source: &'source str,
    ) -> (Pattern<'source>, &'source str) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let root_scope = local.push_root_statement_ambient_scope();
        let block_scope = local.push_indented_statement_ambient_scope(2);
        let companion = local.push_if_expression_companion(0, &["elsif", "else"]);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let (pattern, remainder) = {
            let mut i = In::new(
                &mut source_input,
                &mut expectations,
                IsCut::new(&mut is_cut),
            )
            .set_local(&mut local);
            let pattern = i
                .run(from_fn(|i| parse_pattern(&OperatorTable::default(), i)))
                .expect("pattern AST");
            (pattern, i.input.remainder())
        };
        assert_eq!(
            local.pop_if_expression_companion().map(|frame| frame.id()),
            Some(companion)
        );
        assert_eq!(local.pop_ambient_owner_scope(), Some(block_scope));
        assert_eq!(local.pop_ambient_owner_scope(), Some(root_scope));
        (pattern, remainder)
    }

    fn parse_direct_with_active_if_companion<'source>(
        source: &'source str,
    ) -> (&'source str, Vec<CommittedRecoveryRecord>) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let root_scope = local.push_root_statement_ambient_scope();
        let block_scope = local.push_indented_statement_ambient_scope(2);
        let companion = local.push_if_expression_companion(0, &["elsif", "else"]);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let (remainder, recoveries) = {
            let i = In::new(
                &mut source_input,
                &mut expectations,
                IsCut::new(&mut is_cut),
            )
            .set_local(&mut local);
            let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
            committed.start_node(SyntaxKind::Root);
            parse_direct_pattern(
                &OperatorTable::default(),
                LeadingTrivia::None,
                &mut committed,
            )
            .expect("direct pattern");
            let remainder = committed.probe(|probe| probe.input().input.remainder());
            let recoveries = committed.into_output().committed_recoveries().to_vec();
            (remainder, recoveries)
        };
        assert_eq!(
            local.pop_if_expression_companion().map(|frame| frame.id()),
            Some(companion)
        );
        assert_eq!(local.pop_ambient_owner_scope(), Some(block_scope));
        assert_eq!(local.pop_ambient_owner_scope(), Some(root_scope));
        (remainder, recoveries)
    }

    fn only_child(node: &SyntaxNode, expected: SyntaxKind) -> SyntaxNode {
        let child = node.children().next().expect("child");
        assert_eq!(child.kind(), expected);
        child
    }
}
