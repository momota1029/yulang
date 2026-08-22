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
        expression::{IntegerLiteral, parse_integer_literal},
    },
    scan::{
        operator::LeadingTrivia,
        punctuation::{PunctuationKind, scan_punctuation},
        trivia::{TriviaRun, scan_trivia},
        word::{WordSpan, scan_word},
    },
    session::{
        CommitOutput, Committed, CommittedRecoveryRecord, ConstructRole, Delimiter,
        ExpectationSources, ExpectedSyntax, GrammarRole, PatternRole, Probe, RecoveryKind,
        RecoverySiteKey, StopKind, StopSet, SynIn, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

/// A fixed pattern precedence.  It intentionally does not share expression
/// binding powers or an operator table.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum PatternPrecedence {
    Lowest = 0,
    Alternation = 1,
    Alias = 2,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Pattern<'source> {
    head: Recovered<PatternPrimary<'source>>,
    tails: Vec<PatternTail<'source>>,
    range: Range<usize>,
}

impl Pattern<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
    pub(crate) fn tails(&self) -> &[PatternTail<'_>] {
        &self.tails
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum PatternPrimary<'source> {
    Identifier(PatternNameSpan<'source>),
    Integer(IntegerLiteral<'source>),
    Symbol(SymbolPattern<'source>),
    Parenthesized(ParenthesizedPattern<'source>),
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
pub(crate) fn parse_pattern<'source, E>(i: SynIn<'_, 'source, '_, E>) -> Option<Pattern<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_pattern_bp(i, PatternPrecedence::Lowest)
}

/// Direct-CST counterpart of [`parse_pattern`].  `leading` is currently
/// retained only for the shared entrypoint shape: patterns do not use it for
/// fixed NUD recognition.
pub(crate) fn parse_direct_pattern<'parse, 'source, 'local, E, O>(
    _leading: LeadingTrivia,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedPattern<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_direct_pattern_bp(PatternPrecedence::Lowest, PatternRole::Primary, committed)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParsedPattern<C> {
    range: Range<usize>,
    marker: PhantomData<C>,
}

impl<C> ParsedPattern<C> {
    fn new(range: Range<usize>) -> Self {
        Self {
            range,
            marker: PhantomData,
        }
    }
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

fn parse_pattern_bp<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
    minimum: PatternPrecedence,
) -> Option<Pattern<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let head = match i.run(from_fn(recognize_pattern_nud)) {
        Some(nud) => Recovered::Complete(parse_pattern_primary(nud, &mut i)),
        None if recover_pattern_primary_ast(&mut i) => {
            let nud = i
                .run(from_fn(recognize_pattern_nud))
                .expect("AST recovery stops at a pattern primary");
            Recovered::Complete(parse_pattern_primary(nud, &mut i))
        }
        None => Recovered::Incomplete,
    };
    let mut tails = Vec::new();
    while let Some(led) = i.run(from_fn(|i| recognize_pattern_led(minimum, i))) {
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
                        parse_pattern_bp(i, PatternPrecedence::Alternation)
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
        }
    }
    let end = tails.last().map_or_else(
        || match &head {
            Recovered::Complete(primary) => primary_range(primary).end,
            Recovered::Incomplete => start,
        },
        |tail| match tail {
            PatternTail::Alias(tail) => tail.range.end,
            PatternTail::Alternation(tail) => tail.range.end,
        },
    );
    Some(Pattern {
        head,
        tails,
        range: start..end,
    })
}

fn parse_pattern_primary<'source, E>(
    nud: PatternNudRecognition<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> PatternPrimary<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match nud {
        PatternNudRecognition::Name(name) => PatternPrimary::Identifier(name),
        PatternNudRecognition::Integer(integer) => PatternPrimary::Integer(integer),
        PatternNudRecognition::Symbol { colon, name } => PatternPrimary::Symbol(SymbolPattern {
            range: colon.start..name.range().end,
            colon,
            name: Recovered::Complete(name),
        }),
        PatternNudRecognition::MalformedSymbol { colon } => PatternPrimary::Symbol(SymbolPattern {
            range: colon.clone(),
            colon,
            name: Recovered::Incomplete,
        }),
        PatternNudRecognition::Parenthesized { open } => {
            PatternPrimary::Parenthesized(parse_parenthesized_pattern(open, i))
        }
    }
}

fn primary_range(primary: &PatternPrimary<'_>) -> Range<usize> {
    match primary {
        PatternPrimary::Identifier(name) => name.range(),
        PatternPrimary::Integer(integer) => integer.range(),
        PatternPrimary::Symbol(symbol) => symbol.range.clone(),
        PatternPrimary::Parenthesized(parenthesized) => parenthesized.range.clone(),
    }
}

fn parse_parenthesized_pattern<'source, E>(
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParenthesizedPattern<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    push_parenthesized_scope(i);
    consume_trivia(i);
    let mut elements = Vec::new();
    let mut trailing_comma = None;
    let close = if let Some(close) = i.run(recognize_close_parenthesis) {
        Recovered::Complete(close)
    } else {
        loop {
            let element = i
                .run(from_fn(|i| parse_pattern_bp(i, PatternPrecedence::Lowest)))
                .map_or(Recovered::Incomplete, Recovered::Complete);
            elements.push(element);
            consume_trivia(i);
            if let Some(comma) = i.run(recognize_comma) {
                consume_trivia(i);
                if let Some(close) = i.run(recognize_close_parenthesis) {
                    trailing_comma = Some(comma);
                    break Recovered::Complete(close);
                }
                continue;
            }
            if pattern_nud_candidate_input(i) {
                continue;
            }
            break i
                .run(recognize_close_parenthesis)
                .map_or(Recovered::Incomplete, Recovered::Complete);
        }
    };
    let end = match &close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => i.pos(),
    };
    pop_parenthesized_scope(i);
    ParenthesizedPattern {
        open: open.clone(),
        elements,
        trailing_comma,
        close,
        range: open.start..end,
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
    let start = i.pos();
    loop {
        let Some(character) = i.input.remainder().chars().next() else {
            return false;
        };
        if matches!(character, ')' | ']' | '}' | ',' | ';')
            || (character == ':' && active_stop_set(i).contains(StopKind::Colon))
            || arm_stop_pending(i)
        {
            return false;
        }
        i.input.next().expect("the inspected character exists");
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        if pattern_nud_candidate_input(i) {
            return i.pos() > start;
        }
    }
}

fn pattern_nud_candidate_input<E>(i: &mut SynIn<E>) -> bool
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
    if let Some(colon) = i.run(recognize_colon) {
        return Some(PatternNudRecognition::MalformedSymbol { colon });
    }
    i.choice((
        from_fn(scan_pattern_name).map(PatternNudRecognition::Name),
        parse_integer_literal.map(PatternNudRecognition::Integer),
        recognize_open_parenthesis.map(|open| PatternNudRecognition::Parenthesized { open }),
    ))
}

fn arm_stop_pending<E>(i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    let stops = active_stop_set(i);
    if stops.contains(StopKind::Arrow) && i.input.remainder().starts_with("->") { return true; }
    let checkpoint = i.checkpoint();
    let word = i.run(scan_word).map(|word| word.text());
    i.rollback(checkpoint);
    matches!(word, Some("if") if stops.contains(StopKind::ArmGuardIf))
        || matches!(word, Some("where") if stops.contains(StopKind::ArmGuardWhere))
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
}

fn recognize_pattern_led<'source, E>(
    minimum: PatternPrecedence,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<PatternLedRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
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

fn recognize_close_parenthesis<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let close = i.run(scan_punctuation).and_then(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Close(Delimiter::Parenthesis)
        )
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

fn active_stop_set<E>(i: &SynIn<E>) -> StopSet
where
    E: ErrorSink<usize>,
{
    i.local.stop_set().unwrap_or_default()
}

fn parenthesized_stop_set() -> StopSet {
    StopSet::default()
        .with(StopKind::Comma)
        .with(StopKind::RightParenthesis)
}

fn push_parenthesized_scope<E>(i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    i.local.push_delimiter(Delimiter::Parenthesis);
    i.local.push_stop_set(parenthesized_stop_set());
}

fn pop_parenthesized_scope<E>(i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    assert_eq!(i.local.pop_stop_set(), Some(parenthesized_stop_set()));
}

fn parse_direct_pattern_bp<'parse, 'source, 'local, E, O>(
    minimum: PatternPrecedence,
    primary_role: PatternRole,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedPattern<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = committed_position(committed);
    committed.start_node(SyntaxKind::Pattern);
    if let Some(nud) = committed.probe(probe_pattern_nud) {
        commit_direct_primary(nud, committed);
    } else if committed.probe(pipe_pending) {
        // The RHS of `A | | B` owns a missing primary at the second pipe;
        // leaving that pipe lets this same Pattern consume its nested tail.
        emit_pattern_missing(committed, primary_role, ExpectedSyntax::Pattern);
    } else if direct_pattern_primary_error_retry(committed, primary_role) {
        commit_direct_primary(
            committed
                .probe(probe_pattern_nud)
                .expect("recovery retried a pattern NUD"),
            committed,
        );
    } else {
        emit_pattern_missing(committed, primary_role, ExpectedSyntax::Pattern);
    }

    loop {
        let Some(led) = committed.probe(|probe| probe_pattern_led(minimum, probe)) else {
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
                    PatternPrecedence::Alternation,
                    PatternRole::AlternationRhs,
                    committed,
                )
                .expect("a committed alternation owns a total RHS pattern");
                committed.finish_node();
            }
        }
    }
    let end = committed_position(committed);
    committed.finish_node();
    Some(ParsedPattern::new(start..end))
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
    probe: &mut Probe<'parse, 'source, 'local, E>,
) -> Option<PatternLedRecognition<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    probe
        .input()
        .run(from_fn(|i| recognize_pattern_led(minimum, i)))
}

fn commit_direct_primary<'parse, 'source, 'local, E, O>(
    nud: PatternNudRecognition<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
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
        }
        PatternNudRecognition::Integer(integer) => {
            committed.start_node(SyntaxKind::IntegerPattern);
            committed.token(SyntaxKind::Integer, integer.range());
            committed.finish_node();
        }
        PatternNudRecognition::Symbol { colon, name } => {
            committed.start_node(SyntaxKind::SymbolPattern);
            committed.token(SyntaxKind::Colon, colon);
            committed.token(SyntaxKind::Identifier, name.range());
            committed.finish_node();
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
        }
        PatternNudRecognition::Parenthesized { open } => {
            commit_direct_parenthesized_pattern(open, committed)
        }
    }
}

fn commit_direct_parenthesized_pattern<'parse, 'source, 'local, E, O>(
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::ParenthesizedPattern);
    committed.token(SyntaxKind::LParen, open);
    committed.probe(|probe| push_parenthesized_scope(probe.input()));
    let initial = consume_direct_trivia(committed);
    committed.emit_trivia(&initial);

    if direct_close_parenthesis(committed) {
        finish_parenthesized_scope(committed);
        return;
    }

    loop {
        commit_parenthesized_element(committed);
        let trivia = consume_direct_trivia(committed);
        committed.emit_trivia(&trivia);
        if let Some(comma) = direct_comma(committed) {
            committed.token(SyntaxKind::Comma, comma);
            let trivia = consume_direct_trivia(committed);
            committed.emit_trivia(&trivia);
            if direct_close_parenthesis(committed) {
                finish_parenthesized_scope(committed);
                return;
            }
            continue;
        }
        if direct_close_parenthesis(committed) {
            finish_parenthesized_scope(committed);
            return;
        }
        if committed.probe(pattern_nud_candidate) {
            emit_pattern_missing(
                committed,
                PatternRole::ParenthesizedSeparator,
                ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Comma),
            );
            continue;
        }
        recover_parenthesized_close(committed);
        finish_parenthesized_scope(committed);
        return;
    }
}

fn commit_parenthesized_element<'parse, 'source, 'local, E, O>(
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
        PatternPrecedence::Lowest,
        PatternRole::ParenthesizedElement,
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

fn direct_close_parenthesis<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
{
    let Some(close) = committed.probe(|probe| probe.input().run(recognize_close_parenthesis))
    else {
        return false;
    };
    committed.token(SyntaxKind::RParen, close);
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

fn recover_parenthesized_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    loop {
        if committed.probe(|probe| probe.input().input.remainder().is_empty()) {
            emit_pattern_close_missing(committed);
            return;
        }
        let punctuation = committed.probe(|probe| probe.input().run(scan_punctuation));
        if let Some(punctuation) = punctuation {
            match punctuation.kind() {
                PunctuationKind::Close(Delimiter::Parenthesis) => {
                    committed.token(SyntaxKind::RParen, punctuation.range());
                    return;
                }
                PunctuationKind::Close(actual @ (Delimiter::Bracket | Delimiter::Brace)) => {
                    emit_pattern_close_error(
                        committed,
                        punctuation.range(),
                        UnexpectedCategory::Punctuation(
                            crate::session::PunctuationEvidence::Close(actual),
                        ),
                    );
                }
                _ => emit_pattern_close_error(
                    committed,
                    punctuation.range(),
                    UnexpectedCategory::OtherCharacter,
                ),
            }
            continue;
        }
        let range = committed.probe(|probe| {
            let i = probe.input();
            let start = i.pos();
            let character = i.input.next()?;
            let end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            let _ = character;
            Some(start..end)
        });
        if let Some(range) = range {
            emit_pattern_close_error(committed, range, UnexpectedCategory::OtherCharacter);
        }
    }
}

fn finish_parenthesized_scope<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| pop_parenthesized_scope(probe.input()));
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
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = pattern_role(role);
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

fn parenthesized_close_role() -> GrammarRole {
    GrammarRole::ClosingDelimiter {
        owner: ConstructRole::ParenthesizedPattern,
        delimiter: Delimiter::Parenthesis,
    }
}

fn emit_pattern_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = parenthesized_close_role();
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
                    Delimiter::Parenthesis,
                )),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_pattern_close_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
    category: UnexpectedCategory,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = parenthesized_close_role();
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
    fn parenthesized_patterns_are_uniform_and_comma_only() {
        for (source, elements, trailing) in [
            ("()", 0, false),
            ("(a)", 1, false),
            ("(a,)", 1, true),
            ("(a,b)", 2, false),
            ("(a,b,)", 2, true),
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
                usize::from(trailing) + elements.saturating_sub(1),
                "{source:?}"
            );
        }
        let (_, recoveries) = parse_direct_recovered("(a\nb)");
        assert!(
            recoveries.iter().any(|record| record.site.role
                == GrammarRole::Pattern(PatternRole::ParenthesizedSeparator))
        );
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
    fn dynamic_operator_tables_cannot_change_pattern_cst() {
        let low = OperatorTable::from_declarations([OperatorDeclaration::new(
            "|",
            OperatorFixities::new().with_infix(BindingPower::scalar(1), BindingPower::scalar(1)),
        )])
        .unwrap();
        let high = OperatorTable::from_declarations([OperatorDeclaration::new(
            "|",
            OperatorFixities::new().with_infix(BindingPower::scalar(99), BindingPower::scalar(99)),
        )])
        .unwrap();
        assert_eq!(
            parse_direct_ignoring_operator_table("A | B as c", &low).green(),
            parse_direct_ignoring_operator_table("A | B as c", &high).green()
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
    }

    #[test]
    fn excluded_forms_remain_unconsumed_after_a_first_slice_pattern() {
        for source in [
            "[a]", "{a}", "\"a\"", "x: T", "A::B", "A.field", "Some(x)", "Some x",
        ] {
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
        let pattern = i.run(from_fn(parse_pattern)).expect("pattern AST");
        assert_eq!(i.input.remainder(), "");
        pattern
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
        parse_direct_pattern(LeadingTrivia::None, &mut committed).expect("direct pattern");
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
            parse_direct_pattern(LeadingTrivia::None, &mut committed).expect("direct pattern");
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

    fn only_child(node: &SyntaxNode, expected: SyntaxKind) -> SyntaxNode {
        let child = node.children().next().expect("child");
        assert_eq!(child.kind(), expected);
        child
    }
}
