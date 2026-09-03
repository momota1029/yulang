use std::{ops::Range, sync::Arc};

use chasa::{
    Back as _, ErrorSink, Input as _,
    error::std::{Unexpected, UnexpectedEndOfInput},
    prelude::{from_fn, item},
};

use crate::{
    grammar::expression::{
        Statement, StatementSequenceSeparator, canonical_statement_candidate_input,
        canonical_statement_invalid_run, commit_canonical_statement,
        commit_declaration_companion_braced_missing_separator,
        commit_declaration_companion_braced_separator,
        commit_declaration_companion_indented_separator,
        declaration_companion_braced_boundary_pending,
        declaration_companion_indented_terminal_boundary, parse_canonical_statement,
        recognize_declaration_companion_braced_missing_separator,
        recognize_declaration_companion_braced_separator,
        recognize_declaration_companion_indented_separator,
    },
    operator::OperatorTable,
    scan::{
        operator::LeadingTrivia,
        punctuation::{PunctuationKind, scan_punctuation},
        trivia::{TriviaRun, scan_comment, scan_trivia},
        word::{WordSpan, scan_word},
    },
    session::{
        AmbientOwnerScopeFrame, BracedBarrierOrigin, CanonicalRecoveryContinuation,
        CanonicalRecoveryEpisode, CommitOutput, Committed, CommittedRecoveryRecord, ConstructRole,
        DeclarationCompanionRole, DeclarationRole, Delimiter, ExpectationSources, ExpectedSyntax,
        GrammarRole, IndentationBaseline, IndentationBaselineKind, InlineStatementOwnerKind,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, RecoverySiteSpec, StopKind, StopSet,
        SynIn, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax, YumarkEmbeddedRecoveryFact,
        any_ambient_owner_claims,
    },
    syntax_kind::SyntaxKind,
};

use super::{
    DeclarationCompanionDerivesLayout, DerivesClause, DerivesDriverSpec, Recovered,
    commit_declaration_companion_derives_clause, parse_declaration_companion_derives_clause,
    recognize_declaration_companion_derives_start,
};

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DeclarationCompanion<'source> {
    pub(super) keyword: Range<usize>,
    pub(super) form: DeclarationCompanionForm<'source>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeclarationCompanionForm<'source> {
    Colon {
        colon: Recovered<Range<usize>>,
        body: Recovered<DeclarationCompanionColonBody<'source>>,
    },
    Braced {
        open: Range<usize>,
        items: Vec<Recovered<DeclarationCompanionItem<'source>>>,
        close: Recovered<Range<usize>>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeclarationCompanionColonBody<'source> {
    Inline {
        item: Box<DeclarationCompanionItem<'source>>,
        semicolon: Option<Range<usize>>,
    },
    Indented(DeclarationCompanionIndentedBody<'source>),
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DeclarationCompanionIndentedBody<'source> {
    pub(super) base_indent: usize,
    pub(super) block_indent: usize,
    pub(super) items: Vec<Recovered<DeclarationCompanionItem<'source>>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeclarationCompanionItem<'source> {
    Statement(Box<Statement<'source>>),
    Derives(Vec<DerivesClause<'source>>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct DeclarationCompanionStart<'source> {
    keyword: WordSpan<'source>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DeclarationCompanionFormStarter {
    Colon,
    Braced,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DeclarationCompanionIntroducerRetry {
    Starter(DeclarationCompanionFormStarter),
    InlineItem,
    Boundary,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct DeclarationCompanionIntroducerEpisode {
    recovery: CanonicalRecoveryEpisode,
    retry: DeclarationCompanionIntroducerRetry,
}

impl DeclarationCompanionIntroducerEpisode {
    fn into_fact_and_retry(
        self,
    ) -> (
        YumarkEmbeddedRecoveryFact,
        DeclarationCompanionIntroducerRetry,
    ) {
        let expected_continuation = match self.retry {
            DeclarationCompanionIntroducerRetry::Starter(_)
            | DeclarationCompanionIntroducerRetry::InlineItem => {
                CanonicalRecoveryContinuation::RetrySameSlot
            }
            DeclarationCompanionIntroducerRetry::Boundary => {
                CanonicalRecoveryContinuation::StopAtBoundary
            }
        };
        assert_eq!(self.recovery.continuation, expected_continuation);
        (self.recovery.fact, self.retry)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DeclarationCompanionIndentedScope {
    inline: bool,
    ml_arg: bool,
    stop_set: StopSet,
    ambient_owner_scope: AmbientOwnerScopeFrame,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DeclarationCompanionBracedScope {
    inline: bool,
    ml_arg: bool,
    stop_set: StopSet,
    outer_stops: StopSet,
    ambient_owner_scope: AmbientOwnerScopeFrame,
    if_expression_companion_depth: usize,
}

fn recognize_declaration_companion_start<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<DeclarationCompanionStart<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let keyword = i.run(scan_word)?;
    if keyword.text() != "with" {
        i.rollback(checkpoint);
        return None;
    }
    Some(DeclarationCompanionStart { keyword })
}

fn scan_declaration_companion_form_starter<E>(
    i: &mut SynIn<E>,
) -> Option<(DeclarationCompanionFormStarter, Range<usize>)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    let starter = match punctuation.kind() {
        PunctuationKind::Open(Delimiter::Brace) => DeclarationCompanionFormStarter::Braced,
        PunctuationKind::Colon => DeclarationCompanionFormStarter::Colon,
        _ => {
            i.rollback(checkpoint);
            return None;
        }
    };
    Some((starter, punctuation.range()))
}

fn declaration_companion_form_starter_pending<E>(
    i: &mut SynIn<E>,
) -> Option<DeclarationCompanionFormStarter>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let starter = scan_declaration_companion_form_starter(i).map(|(starter, _)| starter);
    i.rollback(checkpoint);
    starter
}

fn declaration_companion_fixed_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty()
        || matches!(i.input.remainder().chars().next(), Some('\r' | '\n'))
        || any_ambient_owner_claims(i)
    {
        return true;
    }
    let checkpoint = i.checkpoint();
    let boundary = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Comma | PunctuationKind::Semicolon | PunctuationKind::Close(_)
        )
    });
    i.rollback(checkpoint);
    boundary
}

fn scan_declaration_companion_introducer_retry<E>(
    table: &OperatorTable,
    i: &mut SynIn<E>,
) -> (Range<usize>, DeclarationCompanionIntroducerRetry)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if i.run(scan_comment).is_some() {
            continue;
        }
        if let Some(starter) = declaration_companion_form_starter_pending(i) {
            return (
                start..i.pos(),
                DeclarationCompanionIntroducerRetry::Starter(starter),
            );
        }
        if canonical_statement_candidate_input(table, LeadingTrivia::None, i) {
            return (
                start..i.pos(),
                DeclarationCompanionIntroducerRetry::InlineItem,
            );
        }
        if declaration_companion_fixed_boundary_pending(i) {
            return (
                start..i.pos(),
                DeclarationCompanionIntroducerRetry::Boundary,
            );
        }
        i.input
            .next()
            .expect("the declaration companion introducer retry byte exists");
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn declaration_companion_introducer_episode<E>(
    table: &OperatorTable,
    i: &mut SynIn<E>,
) -> DeclarationCompanionIntroducerEpisode
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let (range, retry) = scan_declaration_companion_introducer_retry(table, i);
    let (kind, unexpected) = if range.is_empty() {
        (RecoveryKind::Missing, None)
    } else {
        (
            RecoveryKind::Error,
            Some(UnexpectedCategory::OtherCharacter),
        )
    };
    let continuation = match retry {
        DeclarationCompanionIntroducerRetry::Starter(_)
        | DeclarationCompanionIntroducerRetry::InlineItem => {
            CanonicalRecoveryContinuation::RetrySameSlot
        }
        DeclarationCompanionIntroducerRetry::Boundary => {
            CanonicalRecoveryContinuation::StopAtBoundary
        }
    };
    DeclarationCompanionIntroducerEpisode {
        recovery: CanonicalRecoveryEpisode {
            fact: YumarkEmbeddedRecoveryFact {
                spec: RecoverySiteSpec {
                    role: declaration_companion_introducer_role(),
                    expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Open(
                        Delimiter::Brace,
                    )),
                },
                range,
                kind,
                unexpected,
            },
            continuation,
        },
        retry,
    }
}

/// Judges whether the mandatory first slot of a colon body belongs to an
/// active outer owner. This runs only after the colon layout has been
/// classified, and never consumes its punctuation or contextual word.
fn declaration_companion_colon_body_first_slot_absent<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty() || any_ambient_owner_claims(i) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let absent = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Semicolon
                | PunctuationKind::Comma
                | PunctuationKind::Close(
                    Delimiter::Parenthesis | Delimiter::Bracket | Delimiter::Brace
                )
        )
    });
    i.rollback(checkpoint);
    absent
}

fn scan_horizontal_trivia<E>(i: &mut SynIn<E>) -> TriviaRun
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    if i.input.source()[trivia.range()].contains(['\r', '\n']) {
        i.rollback(checkpoint);
        TriviaRun::empty_at(start)
    } else {
        trivia
    }
}

fn push_declaration_companion_indented_scope<E>(
    block_indent: usize,
    i: &mut SynIn<E>,
) -> DeclarationCompanionIndentedScope
where
    E: ErrorSink<usize>,
{
    let ambient_owner_scope = i.local.push_indented_statement_ambient_scope(block_indent);
    let scope = DeclarationCompanionIndentedScope {
        inline: i.local.inline(),
        ml_arg: i.local.ml_arg(),
        stop_set: i.local.stop_set().unwrap_or_default(),
        ambient_owner_scope,
    };
    i.local.push_indentation_baseline(IndentationBaseline {
        column: block_indent,
        kind: IndentationBaselineKind::Block,
    });
    i.local.set_inline(false);
    i.local.set_ml_arg(false);
    i.local.push_stop_set(scope.stop_set);
    scope
}

fn pop_declaration_companion_indented_scope<E>(
    block_indent: usize,
    scope: DeclarationCompanionIndentedScope,
    i: &mut SynIn<E>,
) where
    E: ErrorSink<usize>,
{
    assert_eq!(
        i.local.pop_ambient_owner_scope(),
        Some(scope.ambient_owner_scope)
    );
    assert_eq!(i.local.pop_stop_set(), Some(scope.stop_set));
    i.local.set_inline(scope.inline);
    i.local.set_ml_arg(scope.ml_arg);
    assert_eq!(
        i.local.pop_indentation_baseline(),
        Some(IndentationBaseline {
            column: block_indent,
            kind: IndentationBaselineKind::Block,
        })
    );
}

fn declaration_companion_braced_stop_set() -> StopSet {
    StopSet::default()
        .with(StopKind::Comma)
        .with(StopKind::Semicolon)
        .with(StopKind::RightBrace)
}

fn push_declaration_companion_braced_scope<E>(i: &mut SynIn<E>) -> DeclarationCompanionBracedScope
where
    E: ErrorSink<usize>,
{
    let if_expression_companion_depth = i.local.if_expression_companion_depth();
    let ambient_owner_scope = i
        .local
        .push_braced_ambient_owner_barrier(BracedBarrierOrigin::DeclarationCompanion);
    let scope = DeclarationCompanionBracedScope {
        inline: i.local.inline(),
        ml_arg: i.local.ml_arg(),
        stop_set: declaration_companion_braced_stop_set(),
        outer_stops: i.local.stop_set().unwrap_or_default(),
        ambient_owner_scope,
        if_expression_companion_depth,
    };
    i.local.push_delimiter(Delimiter::Brace);
    i.local.set_inline(true);
    i.local.set_ml_arg(false);
    i.local.push_stop_set(scope.stop_set);
    scope
}

fn pop_declaration_companion_braced_scope<E>(
    scope: DeclarationCompanionBracedScope,
    i: &mut SynIn<E>,
) where
    E: ErrorSink<usize>,
{
    assert_eq!(
        i.local.if_expression_companion_depth(),
        scope.if_expression_companion_depth
    );
    assert_eq!(
        i.local.pop_ambient_owner_scope(),
        Some(scope.ambient_owner_scope)
    );
    assert_eq!(i.local.pop_stop_set(), Some(scope.stop_set));
    i.local.set_inline(scope.inline);
    i.local.set_ml_arg(scope.ml_arg);
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Brace));
}

fn push_declaration_companion_inline_scope<E>(i: &mut SynIn<E>) -> AmbientOwnerScopeFrame
where
    E: ErrorSink<usize>,
{
    i.local.push_inline_canonical_statement_ambient_scope(
        InlineStatementOwnerKind::DeclarationCompanion,
    )
}

fn pop_declaration_companion_inline_scope<E>(scope: AmbientOwnerScopeFrame, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    assert_eq!(i.local.pop_ambient_owner_scope(), Some(scope));
}

pub(super) fn declaration_companion_derives_sequence_boundary_pending<E>(
    layout: DeclarationCompanionDerivesLayout,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let boundary = match layout {
        DeclarationCompanionDerivesLayout::Inline => {
            let trivia = i.run(scan_trivia).expect("trivia scanning is total");
            if i.input.source()[trivia.range()].contains(['\r', '\n']) {
                true
            } else {
                let punctuation_checkpoint = i.checkpoint();
                let comma = i
                    .run(scan_punctuation)
                    .is_some_and(|punctuation| punctuation.kind() == PunctuationKind::Comma);
                i.rollback(punctuation_checkpoint);
                !comma && declaration_companion_colon_body_first_slot_absent(i)
            }
        }
        DeclarationCompanionDerivesLayout::Indented { block_indent } => {
            recognize_declaration_companion_indented_separator(block_indent, i).is_some()
                || declaration_companion_indented_terminal_boundary(i, block_indent)
        }
        DeclarationCompanionDerivesLayout::Braced => {
            match recognize_declaration_companion_braced_separator(i) {
                Some(StatementSequenceSeparator::Comma { .. }) => false,
                Some(_) => true,
                None => declaration_companion_braced_boundary_pending(i),
            }
        }
    };
    i.rollback(checkpoint);
    boundary
}

pub(super) fn declaration_companion_derives_mandatory_trivia_is_sequence_gap<E>(
    layout: DeclarationCompanionDerivesLayout,
    trivia: &TriviaRun,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
{
    if !i.input.source()[trivia.range()].contains(['\r', '\n']) {
        return false;
    }
    match layout {
        DeclarationCompanionDerivesLayout::Inline | DeclarationCompanionDerivesLayout::Braced => {
            true
        }
        DeclarationCompanionDerivesLayout::Indented { block_indent } => {
            i.local.line().line_indent <= block_indent
        }
    }
}

fn scan_terminal_semicolon<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let semicolon = i.run(scan_punctuation).and_then(|punctuation| {
        (punctuation.kind() == PunctuationKind::Semicolon).then(|| punctuation.range())
    });
    if semicolon.is_none() {
        i.rollback(checkpoint);
    }
    semicolon
}

/// Gate 3 isolated AST entry.  No declaration owner calls this until the
/// owner-specific promotion gates.
#[allow(dead_code)]
pub(super) fn parse_declaration_companion_isolated<'source, E>(
    table: &OperatorTable,
    base_indent: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<DeclarationCompanion<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.run(recognize_declaration_companion_start)?;
    let keyword = start.keyword.range();
    let _leading = scan_horizontal_trivia(i);
    let form = if let Some((starter, range)) = scan_declaration_companion_form_starter(i) {
        parse_declaration_companion_form_after_starter(table, base_indent, starter, range, i)
    } else {
        let (fact, retry) =
            declaration_companion_introducer_episode(table, i).into_fact_and_retry();
        i.local.record_yumark_embedded_recovery(fact);
        match retry {
            DeclarationCompanionIntroducerRetry::Starter(starter) => {
                let (accepted, range) = scan_declaration_companion_form_starter(i)
                    .expect("the companion introducer retry preserves its starter");
                assert_eq!(accepted, starter);
                parse_declaration_companion_form_after_starter(
                    table,
                    base_indent,
                    starter,
                    range,
                    i,
                )
            }
            DeclarationCompanionIntroducerRetry::InlineItem => {
                parse_declaration_companion_inline_form(table, Recovered::Incomplete, i)
            }
            DeclarationCompanionIntroducerRetry::Boundary => DeclarationCompanionForm::Colon {
                colon: Recovered::Incomplete,
                body: Recovered::Incomplete,
            },
        }
    };
    let end = i.pos();
    Some(DeclarationCompanion {
        keyword,
        form,
        range: start.keyword.range().start..end,
    })
}

#[cfg(test)]
pub(crate) fn probe_rejected_declaration_companion_introducer_episode_for_test<'source, E>(
    table: &OperatorTable,
    base_indent: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let errors_checkpoint = i.errors_checkpoint();
    let candidate = parse_declaration_companion_isolated(table, base_indent, i)
        .expect("the rejected D12a candidate starts with `with`");
    assert!(matches!(
        candidate.form,
        DeclarationCompanionForm::Colon {
            body: Recovered::Complete(DeclarationCompanionColonBody::Inline { .. }),
            ..
        }
    ));
    let facts = i.local.drain_yumark_embedded_recoveries();
    let observed = facts
        .last()
        .expect("the rejected D12a candidate observes its introducer episode");
    assert_eq!(
        (
            observed.spec.role,
            observed.spec.expected,
            observed.range.clone(),
            observed.kind,
            observed.unexpected,
        ),
        (
            declaration_companion_introducer_role(),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
            5..6,
            RecoveryKind::Error,
            Some(UnexpectedCategory::OtherCharacter),
        )
    );
    i.rollback(checkpoint);
    i.errors_rollback(errors_checkpoint);
    false
}

fn parse_declaration_companion_form_after_starter<'source, E>(
    table: &OperatorTable,
    base_indent: usize,
    starter: DeclarationCompanionFormStarter,
    range: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> DeclarationCompanionForm<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match starter {
        DeclarationCompanionFormStarter::Colon => {
            parse_declaration_companion_colon_form(table, base_indent, range, i)
        }
        DeclarationCompanionFormStarter::Braced => {
            parse_declaration_companion_braced_form(table, range, i)
        }
    }
}

fn parse_declaration_companion_colon_form<'source, E>(
    table: &OperatorTable,
    base_indent: usize,
    colon: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> DeclarationCompanionForm<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia_checkpoint = i.checkpoint();
    let opening_trivia = i.run(scan_trivia).expect("trivia scanning is total");
    let has_newline = i.input.source()[opening_trivia.range()].contains(['\r', '\n']);
    if has_newline {
        if i.local.line().line_indent <= base_indent {
            i.rollback(trivia_checkpoint);
            return DeclarationCompanionForm::Colon {
                colon: Recovered::Complete(colon),
                body: Recovered::Incomplete,
            };
        }
        let block_indent = i.local.line().line_indent;
        if declaration_companion_colon_body_first_slot_absent(i) {
            i.rollback(trivia_checkpoint);
            return DeclarationCompanionForm::Colon {
                colon: Recovered::Complete(colon),
                body: Recovered::Incomplete,
            };
        }
        let body_start = opening_trivia.range().start;
        let scope = push_declaration_companion_indented_scope(block_indent, i);
        let items = parse_indented_declaration_companion_statement_items(table, block_indent, i);
        let body_end = i.pos();
        pop_declaration_companion_indented_scope(block_indent, scope, i);
        return DeclarationCompanionForm::Colon {
            colon: Recovered::Complete(colon),
            body: Recovered::Complete(DeclarationCompanionColonBody::Indented(
                DeclarationCompanionIndentedBody {
                    base_indent,
                    block_indent,
                    items,
                    range: body_start..body_end,
                },
            )),
        };
    }
    parse_declaration_companion_inline_form(table, Recovered::Complete(colon), i)
}

fn parse_declaration_companion_inline_form<'source, E>(
    table: &OperatorTable,
    colon: Recovered<Range<usize>>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> DeclarationCompanionForm<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if declaration_companion_colon_body_first_slot_absent(i) {
        return DeclarationCompanionForm::Colon {
            colon,
            body: Recovered::Incomplete,
        };
    }
    let scope = push_declaration_companion_inline_scope(i);
    let item = parse_declaration_companion_statement_item(
        table,
        DeclarationCompanionDerivesLayout::Inline,
        i,
    );
    let body = match item {
        Recovered::Complete(item) => {
            let semicolon = scan_terminal_semicolon(i);
            Recovered::Complete(DeclarationCompanionColonBody::Inline {
                item: Box::new(item),
                semicolon,
            })
        }
        Recovered::Incomplete => Recovered::Incomplete,
    };
    pop_declaration_companion_inline_scope(scope, i);
    DeclarationCompanionForm::Colon { colon, body }
}

fn outer_stop_for_close(delimiter: Delimiter) -> StopKind {
    match delimiter {
        Delimiter::Parenthesis => StopKind::RightParenthesis,
        Delimiter::Bracket => StopKind::RightBracket,
        Delimiter::Brace => StopKind::RightBrace,
    }
}

fn scan_declaration_companion_close<E>(i: &mut SynIn<E>) -> Option<(Delimiter, Range<usize>)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = i.pos();
    let character = i.input.remainder().chars().next()?;
    let delimiter = match character {
        ')' => Delimiter::Parenthesis,
        ']' => Delimiter::Bracket,
        '}' => Delimiter::Brace,
        _ => return None,
    };
    i.run(item(character))?;
    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);
    Some((delimiter, start..i.pos()))
}

fn parse_declaration_companion_braced_close<E>(
    outer_stops: StopSet,
    i: &mut SynIn<E>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    loop {
        if i.input.remainder().is_empty() {
            return Recovered::Incomplete;
        }
        let checkpoint = i.checkpoint();
        let Some((actual, range)) = scan_declaration_companion_close(i) else {
            return Recovered::Incomplete;
        };
        match actual {
            Delimiter::Brace => return Recovered::Complete(range),
            actual if outer_stops.contains(outer_stop_for_close(actual)) => {
                i.rollback(checkpoint);
                return Recovered::Incomplete;
            }
            _ => {}
        }
    }
}

fn parse_declaration_companion_braced_form<'source, E>(
    table: &OperatorTable,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> DeclarationCompanionForm<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let scope = push_declaration_companion_braced_scope(i);
    i.run(scan_trivia).expect("trivia scanning is total");
    let items = parse_braced_declaration_companion_statement_items(table, i);
    i.run(scan_trivia).expect("trivia scanning is total");
    let close = parse_declaration_companion_braced_close(scope.outer_stops, i);
    pop_declaration_companion_braced_scope(scope, i);
    DeclarationCompanionForm::Braced { open, items, close }
}

/// Gate 3 isolated direct-CST entry.  It streams the companion node and does
/// not construct or replay the AST item vector.
#[allow(dead_code)]
pub(super) fn commit_declaration_companion_isolated<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    base_indent: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start =
        committed.probe(|probe| probe.input().run(recognize_declaration_companion_start))?;
    let companion_start = start.keyword.range().start;
    committed.start_node(SyntaxKind::DeclarationCompanion);
    committed.token(SyntaxKind::WithKw, start.keyword.range());
    let leading = committed.probe(|probe| scan_horizontal_trivia(probe.input()));
    committed.emit_trivia(&leading);

    if let Some((starter, range)) =
        committed.probe(|probe| scan_declaration_companion_form_starter(probe.input()))
    {
        commit_declaration_companion_form_after_starter(
            table,
            base_indent,
            starter,
            range,
            committed,
        );
    } else {
        let (fact, retry) = committed.probe(|probe| {
            declaration_companion_introducer_episode(table, probe.input()).into_fact_and_retry()
        });
        emit_declaration_companion_introducer_recovery(fact, committed);
        match retry {
            DeclarationCompanionIntroducerRetry::Starter(starter) => {
                let (accepted, range) = committed
                    .probe(|probe| scan_declaration_companion_form_starter(probe.input()))
                    .expect("the companion introducer retry preserves its starter");
                assert_eq!(accepted, starter);
                commit_declaration_companion_form_after_starter(
                    table,
                    base_indent,
                    starter,
                    range,
                    committed,
                );
            }
            DeclarationCompanionIntroducerRetry::InlineItem => {
                commit_declaration_companion_inline_form(table, committed);
            }
            DeclarationCompanionIntroducerRetry::Boundary => {}
        }
    }

    let end = committed.probe(|probe| probe.input().pos());
    committed.finish_node();
    Some(companion_start..end)
}

fn commit_declaration_companion_form_after_starter<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    base_indent: usize,
    starter: DeclarationCompanionFormStarter,
    range: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match starter {
        DeclarationCompanionFormStarter::Colon => {
            committed.token(SyntaxKind::Colon, range);
            commit_declaration_companion_colon_form(table, base_indent, committed);
        }
        DeclarationCompanionFormStarter::Braced => {
            committed.token(SyntaxKind::LBrace, range);
            commit_declaration_companion_braced_form(table, committed);
        }
    }
}

fn commit_declaration_companion_colon_form<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    base_indent: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    let opening_trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scanning is total");
    let has_newline = committed
        .probe(|probe| probe.input().input.source()[opening_trivia.range()].contains(['\r', '\n']));
    if has_newline {
        let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
        if block_indent <= base_indent {
            committed.probe(|probe| probe.input().rollback(checkpoint));
            emit_declaration_companion_missing(
                declaration_companion_body_role(),
                ExpectedSyntax::Statement,
                committed,
            );
            return;
        }
        if committed
            .probe(|probe| declaration_companion_colon_body_first_slot_absent(probe.input()))
        {
            committed.probe(|probe| probe.input().rollback(checkpoint));
            emit_declaration_companion_missing(
                declaration_companion_body_role(),
                ExpectedSyntax::Statement,
                committed,
            );
            return;
        }
        committed.start_node(SyntaxKind::DeclarationCompanionIndentedBody);
        committed.emit_trivia(&opening_trivia);
        let scope = committed
            .probe(|probe| push_declaration_companion_indented_scope(block_indent, probe.input()));
        commit_indented_declaration_companion_statement_items(table, block_indent, committed);
        committed.probe(|probe| {
            pop_declaration_companion_indented_scope(block_indent, scope, probe.input())
        });
        committed.finish_node();
        return;
    }
    committed.emit_trivia(&opening_trivia);
    commit_declaration_companion_inline_form(table, committed);
}

fn commit_declaration_companion_inline_form<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| declaration_companion_colon_body_first_slot_absent(probe.input())) {
        emit_declaration_companion_missing(
            declaration_companion_body_role(),
            ExpectedSyntax::Statement,
            committed,
        );
        return;
    }
    let scope = committed.probe(|probe| push_declaration_companion_inline_scope(probe.input()));
    let complete = commit_declaration_companion_statement_item(
        table,
        DeclarationCompanionDerivesLayout::Inline,
        declaration_companion_body_role(),
        LeadingTrivia::None,
        committed,
    );
    if complete
        && let Some(semicolon) = committed.probe(|probe| scan_terminal_semicolon(probe.input()))
    {
        committed.token(SyntaxKind::Semicolon, semicolon);
    }
    committed.probe(|probe| pop_declaration_companion_inline_scope(scope, probe.input()));
}

fn commit_declaration_companion_braced_form<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let scope = committed.probe(|probe| push_declaration_companion_braced_scope(probe.input()));
    let leading = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scanning is total");
    committed.emit_trivia(&leading);
    commit_braced_declaration_companion_statement_items(table, committed);
    let trailing = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scanning is total");
    committed.emit_trivia(&trailing);
    commit_declaration_companion_braced_close(scope.outer_stops, committed);
    committed.probe(|probe| pop_declaration_companion_braced_scope(scope, probe.input()));
}

fn commit_declaration_companion_braced_close<'parse, 'source, 'local, E, O>(
    outer_stops: StopSet,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    loop {
        if committed.probe(|probe| probe.input().input.remainder().is_empty()) {
            emit_declaration_companion_close_missing(committed);
            return;
        }
        let checkpoint = committed.probe(|probe| probe.input().checkpoint());
        let close = committed.probe(|probe| scan_declaration_companion_close(probe.input()));
        let Some((actual, range)) = close else {
            emit_declaration_companion_close_missing(committed);
            return;
        };
        match actual {
            Delimiter::Brace => {
                committed.token(SyntaxKind::RBrace, range);
                return;
            }
            actual if outer_stops.contains(outer_stop_for_close(actual)) => {
                committed.probe(|probe| probe.input().rollback(checkpoint));
                emit_declaration_companion_close_missing(committed);
                return;
            }
            actual => emit_declaration_companion_close_error(range, actual, committed),
        }
    }
}

/// Parses the mandatory statement-only sequence of a future indented
/// declaration companion. Gate 2 deliberately leaves this adapter
/// production-unreachable; Gate 3 owns companion form recognition and scope.
#[allow(dead_code)]
pub(super) fn parse_indented_declaration_companion_statement_items<'source, E>(
    table: &OperatorTable,
    block_indent: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Vec<Recovered<DeclarationCompanionItem<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let layout = DeclarationCompanionDerivesLayout::Indented { block_indent };
    let mut items = vec![parse_declaration_companion_statement_item(table, layout, i)];
    loop {
        let Some(separator) = recognize_declaration_companion_indented_separator(block_indent, i)
        else {
            break;
        };
        if separator.is_semicolon()
            && declaration_companion_indented_terminal_boundary(i, block_indent)
        {
            break;
        }
        items.push(parse_declaration_companion_statement_item(table, layout, i));
    }
    items
}

/// Parses the empty-allowed statement-only sequence of a future braced
/// declaration companion without consuming its closing or outer boundary.
#[allow(dead_code)]
pub(super) fn parse_braced_declaration_companion_statement_items<'source, E>(
    table: &OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Vec<Recovered<DeclarationCompanionItem<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if declaration_companion_braced_boundary_pending(i) {
        return Vec::new();
    }
    let layout = DeclarationCompanionDerivesLayout::Braced;
    let mut items = vec![parse_declaration_companion_statement_item(table, layout, i)];
    loop {
        if declaration_companion_braced_boundary_pending(i) {
            break;
        }
        let Some(transition) = recognize_braced_companion_statement_transition(table, i) else {
            break;
        };
        if matches!(transition, BracedCompanionStatementTransition::Separator(_))
            && declaration_companion_braced_boundary_pending(i)
        {
            break;
        }
        items.push(parse_declaration_companion_statement_item(table, layout, i));
    }
    items
}

/// Direct-CST counterpart of
/// [`parse_indented_declaration_companion_statement_items`].
#[allow(dead_code)]
pub(super) fn commit_indented_declaration_companion_statement_items<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    block_indent: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_declaration_companion_statement_item(
        table,
        DeclarationCompanionDerivesLayout::Indented { block_indent },
        declaration_companion_indented_item_role(),
        LeadingTrivia::None,
        committed,
    );
    loop {
        let Some(separator) =
            commit_declaration_companion_indented_separator(block_indent, committed)
        else {
            break;
        };
        if separator.is_semicolon()
            && committed.probe(|probe| {
                declaration_companion_indented_terminal_boundary(probe.input(), block_indent)
            })
        {
            break;
        }
        commit_declaration_companion_statement_item(
            table,
            DeclarationCompanionDerivesLayout::Indented { block_indent },
            declaration_companion_indented_item_role(),
            separator.following_leading_trivia(),
            committed,
        );
    }
}

/// Direct-CST counterpart of
/// [`parse_braced_declaration_companion_statement_items`].
#[allow(dead_code)]
pub(super) fn commit_braced_declaration_companion_statement_items<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| declaration_companion_braced_boundary_pending(probe.input())) {
        return;
    }
    commit_declaration_companion_statement_item(
        table,
        DeclarationCompanionDerivesLayout::Braced,
        declaration_companion_item_role(),
        LeadingTrivia::None,
        committed,
    );
    loop {
        if committed.probe(|probe| declaration_companion_braced_boundary_pending(probe.input())) {
            return;
        }
        let leading = if let Some(separator) =
            commit_declaration_companion_braced_separator(committed)
        {
            let leading = separator.following_leading_trivia();
            if committed.probe(|probe| declaration_companion_braced_boundary_pending(probe.input()))
            {
                return;
            }
            leading
        } else if let Some(leading) =
            commit_declaration_companion_braced_missing_separator(table, committed)
        {
            emit_declaration_companion_missing(
                declaration_companion_separator_role(),
                ExpectedSyntax::StatementSeparator,
                committed,
            );
            leading
        } else {
            return;
        };
        commit_declaration_companion_statement_item(
            table,
            DeclarationCompanionDerivesLayout::Braced,
            declaration_companion_item_role(),
            leading,
            committed,
        );
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum DeclarationCompanionStatementRecovery {
    Malformed { range: Range<usize>, retry: bool },
    Missing,
}

/// One sink-free failure decision is shared by all four companion adapters.
/// Normal items first take the unconditional canonical Statement path.  Only
/// a failed canonical parse/commit reaches this classifier, which advances one
/// maximal malformed episode to either a retry candidate or a retained
/// sequence boundary.
fn declaration_companion_statement_recovery<E>(
    table: &OperatorTable,
    i: &mut SynIn<E>,
) -> DeclarationCompanionStatementRecovery
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    canonical_statement_invalid_run(table, i).map_or(
        DeclarationCompanionStatementRecovery::Missing,
        |(range, retry)| DeclarationCompanionStatementRecovery::Malformed { range, retry },
    )
}

fn parse_declaration_companion_statement_item<'source, E>(
    table: &OperatorTable,
    layout: DeclarationCompanionDerivesLayout,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<DeclarationCompanionItem<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(mut start) = recognize_declaration_companion_derives_start(i) {
        let spec = DerivesDriverSpec::declaration_companion(layout);
        let mut clauses = Vec::new();
        loop {
            let (clause, repeated_start) =
                parse_declaration_companion_derives_clause(start, spec, i);
            clauses.push(clause);
            let Some(next) = repeated_start else {
                break;
            };
            start = next;
        }
        return Recovered::Complete(DeclarationCompanionItem::Derives(clauses));
    }
    let errors_checkpoint = i.errors_checkpoint();
    if let Some(statement) = i.run(from_fn(|i| parse_canonical_statement(table, i))) {
        return Recovered::Complete(DeclarationCompanionItem::Statement(Box::new(statement)));
    }
    i.errors_rollback(errors_checkpoint);
    match declaration_companion_statement_recovery(table, i) {
        DeclarationCompanionStatementRecovery::Malformed { retry: true, .. } => {
            let statement = i
                .run(from_fn(|i| parse_canonical_statement(table, i)))
                .expect("a retried companion Statement candidate must parse canonically");
            Recovered::Complete(DeclarationCompanionItem::Statement(Box::new(statement)))
        }
        DeclarationCompanionStatementRecovery::Malformed { retry: false, .. }
        | DeclarationCompanionStatementRecovery::Missing => Recovered::Incomplete,
    }
}

fn commit_declaration_companion_statement_item<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    layout: DeclarationCompanionDerivesLayout,
    role: GrammarRole,
    leading: LeadingTrivia,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(mut start) =
        committed.probe(|probe| recognize_declaration_companion_derives_start(probe.input()))
    {
        let spec = DerivesDriverSpec::declaration_companion(layout);
        loop {
            let repeated_start =
                commit_declaration_companion_derives_clause(start, spec, committed);
            let Some(next) = repeated_start else {
                break;
            };
            start = next;
        }
        return true;
    }
    committed.start_node(SyntaxKind::Statement);
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    let mut complete = commit_canonical_statement(table, leading, committed);
    if !complete {
        committed.probe(|probe| probe.input().errors_rollback(errors_checkpoint));
        match committed
            .probe(|probe| declaration_companion_statement_recovery(table, probe.input()))
        {
            DeclarationCompanionStatementRecovery::Malformed { range, retry } => {
                emit_declaration_companion_error(role, ExpectedSyntax::Statement, range, committed);
                if retry {
                    complete = commit_canonical_statement(table, LeadingTrivia::None, committed);
                    assert!(complete);
                }
            }
            DeclarationCompanionStatementRecovery::Missing => {
                emit_declaration_companion_missing(role, ExpectedSyntax::Statement, committed);
            }
        }
    }
    committed.finish_node();
    complete
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum BracedCompanionStatementTransition {
    Separator(StatementSequenceSeparator),
    MissingSeparator { leading: LeadingTrivia },
}

fn recognize_braced_companion_statement_transition<E>(
    table: &OperatorTable,
    i: &mut SynIn<E>,
) -> Option<BracedCompanionStatementTransition>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(separator) = recognize_declaration_companion_braced_separator(i) {
        return Some(BracedCompanionStatementTransition::Separator(separator));
    }
    recognize_declaration_companion_braced_missing_separator(table, i)
        .map(|leading| BracedCompanionStatementTransition::MissingSeparator { leading })
}

fn emit_declaration_companion_missing<'parse, 'source, 'local, E, O>(
    role: GrammarRole,
    expected: ExpectedSyntax,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
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

fn emit_declaration_companion_error<'parse, 'source, 'local, E, O>(
    role: GrammarRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
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

fn emit_declaration_companion_introducer_recovery<'parse, 'source, 'local, E, O>(
    fact: YumarkEmbeddedRecoveryFact,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let role = fact.spec.role;
    let range = fact.range;
    let kind = fact.kind;
    let record = committed.probe(|probe| {
        let i = probe.input();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            kind,
            match kind {
                RecoveryKind::Missing => Arc::from([]),
                RecoveryKind::Error => Arc::from([UnexpectedSyntax::Token {
                    range: range.clone(),
                    category: fact
                        .unexpected
                        .unwrap_or(UnexpectedCategory::OtherCharacter),
                }]),
            },
            Arc::from([
                SyntaxExpectation {
                    role,
                    expected: fact.spec.expected,
                    range: range.clone(),
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
                    range: range.clone(),
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                },
            ]),
            0,
        )
    });
    match kind {
        RecoveryKind::Missing => committed.emit_missing(record),
        RecoveryKind::Error => committed.emit_error(record),
    }
}

fn declaration_companion_close_role() -> GrammarRole {
    GrammarRole::ClosingDelimiter {
        owner: ConstructRole::DeclarationCompanion,
        delimiter: Delimiter::Brace,
    }
}

fn emit_declaration_companion_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_declaration_companion_missing(
        declaration_companion_close_role(),
        ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
        committed,
    );
}

fn emit_declaration_companion_close_error<'parse, 'source, 'local, E, O>(
    range: Range<usize>,
    actual: Delimiter,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let role = declaration_companion_close_role();
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
                category: UnexpectedCategory::Punctuation(PunctuationEvidence::Close(actual)),
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn declaration_companion_introducer_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Companion(
        DeclarationCompanionRole::Introducer,
    ))
}

fn declaration_companion_body_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Companion(DeclarationCompanionRole::Body))
}

fn declaration_companion_item_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Companion(DeclarationCompanionRole::Item))
}

fn declaration_companion_indented_item_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Companion(
        DeclarationCompanionRole::IndentedItem,
    ))
}

fn declaration_companion_separator_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Companion(
        DeclarationCompanionRole::Separator,
    ))
}

#[cfg(test)]
mod tests {
    use std::{hint::black_box, ops::Range, sync::Arc};

    use chasa::{
        error::std::{Expected, StdErr, StdSummary},
        input::IsCut,
        prelude::In,
    };

    use crate::{
        SyntaxNode,
        grammar::expression::{
            canonical_statement_candidate_input_calls,
            reset_canonical_statement_candidate_input_calls,
        },
        input::SourceInput,
        operator::{BindingPower, OperatorDeclaration, OperatorFixities},
        session::{
            CommittedRecoveryRecord, Delimiter, DerivesRole, EmbeddedLexicalMode,
            ExpressionDelimitedOwner, ExpressionRole, FullCstOutput, GrammarRole,
            IndentationBaseline, IndentationBaselineKind, InlineStatementOwnerKind, LineState,
            OperatorCandidateProbe, ParseLocal, ParseLocalValueSnapshot, Probe, RecoveryKind,
            RecoverySiteSpec, StagedHeaderFact, StopKind, StopSet, TypeDelimitedOwner,
            TypeExpressionEpisodePolicy, TypeExpressionScopedStopFrame,
            TypeMalformedCallerBoundaryFence, YumarkEmbeddedOuterKind, YumarkEmbeddedRecoveryFact,
            YumarkFrame, YumarkOwner,
        },
    };

    use super::super::{
        DerivesAttachmentOwner, DerivesAttachmentPosition, commit_derives_attachments_isolated,
        commit_derives_role_trivia, consume_derives_role_trivia,
        parse_derives_attachments_isolated, recognize_derives_attachment_start,
    };
    use super::*;

    #[derive(Debug)]
    struct AstOutcome {
        complete: Vec<bool>,
        remainder: String,
        before: ParseLocalValueSnapshot,
        after: ParseLocalValueSnapshot,
        sink_clean: bool,
        cut: bool,
    }

    #[derive(Debug)]
    struct DirectOutcome {
        statement_count: usize,
        remainder: String,
        recoveries: Vec<CommittedRecoveryRecord>,
        emitted: String,
        child_kinds: Vec<SyntaxKind>,
        first_child_kinds: Vec<SyntaxKind>,
        derives_parent_kinds: Vec<SyntaxKind>,
        node_kinds: Vec<SyntaxKind>,
        tokens: Vec<(SyntaxKind, Range<usize>, String)>,
        before: ParseLocalValueSnapshot,
        after: ParseLocalValueSnapshot,
        sink_clean: bool,
        cut: bool,
    }

    fn item_is_complete(item: &Recovered<DeclarationCompanionItem<'_>>) -> bool {
        matches!(
            item,
            Recovered::Complete(
                DeclarationCompanionItem::Statement(_) | DeclarationCompanionItem::Derives(_)
            )
        )
    }

    fn enter_test_braced_owner_scope(local: &mut ParseLocal) {
        local.set_inline(true);
        local.set_ml_arg(true);
        local.push_delimiter(Delimiter::Brace);
        local.push_stop_set(
            StopSet::default()
                .with(StopKind::Comma)
                .with(StopKind::Semicolon)
                .with(StopKind::RightBrace),
        );
    }

    fn seed_test_local(local: &mut ParseLocal) {
        local.set_line(LineState {
            at_line_start: false,
            ..LineState::default()
        });
        local.set_inline(true);
        local.set_ml_arg(true);
        local.set_type_ml_arg(true);
        local.push_indentation_baseline(IndentationBaseline {
            column: 0,
            kind: IndentationBaselineKind::Block,
        });
        local.push_indentation_baseline(IndentationBaseline {
            column: 0,
            kind: IndentationBaselineKind::Introducer,
        });
        local.push_type_expression_episode(TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: StopSet::default().with(StopKind::With),
            fresh_primary_owns_adjacent_polymorphic_variant_starter: false,
        });
        local.push_type_expression_episode(TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: StopSet::default().with(StopKind::Via),
            fresh_primary_owns_adjacent_polymorphic_variant_starter: true,
        });
        local.push_type_expression_scoped_stop_frame(TypeExpressionScopedStopFrame {
            stops: StopSet::default().with(StopKind::With),
            visible_episode_depth: 1,
        });
        local.push_type_expression_scoped_stop_frame(TypeExpressionScopedStopFrame {
            stops: StopSet::default().with(StopKind::Via),
            visible_episode_depth: 2,
        });
        local.push_stop_set(StopSet::default().with(StopKind::With));
        local.push_stop_set(StopSet::default().with(StopKind::RightBracket));
        local.push_delimiter(Delimiter::Brace);
        local.push_delimiter(Delimiter::Parenthesis);
        local.push_expression_delimited_owner(ExpressionDelimitedOwner::Call);
        local.push_expression_delimited_owner(ExpressionDelimitedOwner::Index);
        local.push_type_delimited_owner(TypeDelimitedOwner::Call);
        local.push_type_delimited_owner(TypeDelimitedOwner::NamedRecord);
        local.push_lexical_mode(EmbeddedLexicalMode::RuleLiteral);
        local.push_lexical_mode(EmbeddedLexicalMode::NormalString);
        local.push_root_statement_ambient_scope();
        local.push_inline_canonical_statement_ambient_scope(InlineStatementOwnerKind::WithBodyTail);
        local.push_if_expression_companion(37, &["__gate2_outer"]);
        local.push_if_expression_companion(41, &["__gate2_inner"]);
        local.stage_header_fact(StagedHeaderFact::Import);
        local.stage_header_fact(StagedHeaderFact::Operator);
        local.begin_operator_probe(OperatorCandidateProbe {
            start: 11,
            candidate_end: 17,
        });
        local.begin_operator_probe(OperatorCandidateProbe {
            start: 23,
            candidate_end: 29,
        });
        let _ = local.next_diagnostic_id();
        let _ = local.next_diagnostic_id();
        local.set_type_malformed_caller_boundary(Some(TypeMalformedCallerBoundaryFence {
            trivia_start: 31,
        }));
    }

    fn seeded_test_local() -> ParseLocal {
        let mut identity_owner = ParseLocal::new();
        let role = declaration_companion_item_role();
        let range = 97..97;
        let reusable = CommittedRecoveryRecord::new(
            &mut identity_owner,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Statement,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        );
        let mut local = ParseLocal::with_reusable_recoveries(&[reusable]);
        seed_test_local(&mut local);
        local
    }

    fn seeded_gate3_test_local() -> ParseLocal {
        let mut local = seeded_test_local();
        local.push_if_expression_companion(0, &["elsif", "else"]);
        local
    }

    fn run_indented_ast(source: &str, block_indent: usize) -> AstOutcome {
        let table = OperatorTable::empty();
        run_indented_ast_with_table(source, block_indent, &table)
    }

    fn run_indented_ast_with_table(
        source: &str,
        block_indent: usize,
        table: &OperatorTable,
    ) -> AstOutcome {
        let mut input = SourceInput::new(source);
        let mut local = seeded_test_local();
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let items =
            parse_indented_declaration_companion_statement_items(table, block_indent, &mut i);
        let remainder = i.input.remainder().to_owned();
        drop(i);
        AstOutcome {
            complete: items.iter().map(item_is_complete).collect(),
            remainder,
            before,
            after: local.value_snapshot(),
            sink_clean: sink.take_merged().is_none(),
            cut,
        }
    }

    fn run_braced_ast(source: &str) -> AstOutcome {
        let table = OperatorTable::empty();
        run_braced_ast_with_table(source, &table)
    }

    fn run_braced_ast_with_table(source: &str, table: &OperatorTable) -> AstOutcome {
        let mut input = SourceInput::new(source);
        let mut local = seeded_test_local();
        enter_test_braced_owner_scope(&mut local);
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let items = parse_braced_declaration_companion_statement_items(table, &mut i);
        let remainder = i.input.remainder().to_owned();
        drop(i);
        AstOutcome {
            complete: items.iter().map(item_is_complete).collect(),
            remainder,
            before,
            after: local.value_snapshot(),
            sink_clean: sink.take_merged().is_none(),
            cut,
        }
    }

    fn run_indented_direct(source: &str, block_indent: usize) -> DirectOutcome {
        let table = OperatorTable::empty();
        run_indented_direct_with_table(source, block_indent, &table)
    }

    fn run_indented_direct_with_table(
        source: &str,
        block_indent: usize,
        table: &OperatorTable,
    ) -> DirectOutcome {
        let mut input = SourceInput::new(source);
        let mut local = seeded_test_local();
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let probe = Probe::new(i);
        let mut committed = probe.commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_indented_declaration_companion_statement_items(table, block_indent, &mut committed);
        let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
        committed.finish_node();
        let output = committed.into_output();
        let recoveries = output.committed_recoveries().to_vec();
        let root = SyntaxNode::new_root(output.finish_prefix());
        let child_kinds = root.children().map(|node| node.kind()).collect();
        let first_child_kinds = root
            .children()
            .next()
            .map(|node| node.children().map(|child| child.kind()).collect())
            .unwrap_or_default();
        let derives_parent_kinds = root
            .descendants()
            .filter(|node| {
                node.children()
                    .any(|child| child.kind() == SyntaxKind::DerivesClause)
            })
            .map(|node| node.kind())
            .collect();
        let node_kinds = root.descendants().map(|node| node.kind()).collect();
        let tokens = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| {
                let range = token.text_range();
                (
                    token.kind(),
                    usize::from(range.start())..usize::from(range.end()),
                    token.text().to_owned(),
                )
            })
            .collect();
        DirectOutcome {
            statement_count: root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Statement)
                .count(),
            remainder,
            recoveries,
            emitted: root.to_string(),
            child_kinds,
            first_child_kinds,
            derives_parent_kinds,
            node_kinds,
            tokens,
            before,
            after: local.value_snapshot(),
            sink_clean: sink.take_merged().is_none(),
            cut,
        }
    }

    fn run_braced_direct(source: &str) -> DirectOutcome {
        let table = OperatorTable::empty();
        run_braced_direct_with_table(source, &table)
    }

    fn run_braced_direct_with_table(source: &str, table: &OperatorTable) -> DirectOutcome {
        let mut input = SourceInput::new(source);
        let mut local = seeded_test_local();
        enter_test_braced_owner_scope(&mut local);
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let probe = Probe::new(i);
        let mut committed = probe.commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_braced_declaration_companion_statement_items(table, &mut committed);
        let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
        committed.finish_node();
        let output = committed.into_output();
        let recoveries = output.committed_recoveries().to_vec();
        let root = SyntaxNode::new_root(output.finish_prefix());
        let child_kinds = root.children().map(|node| node.kind()).collect();
        let first_child_kinds = root
            .children()
            .next()
            .map(|node| node.children().map(|child| child.kind()).collect())
            .unwrap_or_default();
        let derives_parent_kinds = root
            .descendants()
            .filter(|node| {
                node.children()
                    .any(|child| child.kind() == SyntaxKind::DerivesClause)
            })
            .map(|node| node.kind())
            .collect();
        let node_kinds = root.descendants().map(|node| node.kind()).collect();
        let tokens = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| {
                let range = token.text_range();
                (
                    token.kind(),
                    usize::from(range.start())..usize::from(range.end()),
                    token.text().to_owned(),
                )
            })
            .collect();
        DirectOutcome {
            statement_count: root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Statement)
                .count(),
            remainder,
            recoveries,
            emitted: root.to_string(),
            child_kinds,
            first_child_kinds,
            derives_parent_kinds,
            node_kinds,
            tokens,
            before,
            after: local.value_snapshot(),
            sink_clean: sink.take_merged().is_none(),
            cut,
        }
    }

    fn expected_line_after_prefix(mut line: LineState, prefix: &str) -> LineState {
        let bytes = prefix.as_bytes();
        let mut index = 0;
        while index < bytes.len() {
            let start = index;
            let newline_end = if bytes[index] == b'\r' {
                index + 1 + usize::from(bytes.get(index + 1) == Some(&b'\n'))
            } else if bytes[index] == b'\n' {
                index + 1
            } else {
                0
            };
            if newline_end != 0 {
                line = LineState {
                    last_newline: Some((start, newline_end)),
                    line_start: newline_end,
                    line_indent: 0,
                    at_line_start: true,
                };
                index = newline_end;
                continue;
            }
            if matches!(bytes[index], b' ' | b'\t') && line.at_line_start {
                line.line_indent += 1;
            } else if !matches!(bytes[index], b' ' | b'\t') {
                line.at_line_start = false;
            }
            index += 1;
        }
        line
    }

    fn unterminated_block_comment_depth(prefix: &str) -> usize {
        let bytes = prefix.as_bytes();
        let mut index = 0;
        let mut depth = 0;
        while index + 1 < bytes.len() {
            if depth == 0 && bytes[index..].starts_with(b"//") {
                index += 2;
                while index < bytes.len() && !matches!(bytes[index], b'\r' | b'\n') {
                    index += 1;
                }
                continue;
            }
            if bytes[index..].starts_with(b"/*") {
                depth += 1;
                index += 2;
                continue;
            }
            if depth > 0 && bytes[index..].starts_with(b"*/") {
                depth -= 1;
                index += 2;
                continue;
            }
            index += 1;
        }
        depth
    }

    fn expected_local_after(
        before: &ParseLocalValueSnapshot,
        source: &str,
        remainder: &str,
        diagnostic_delta: u32,
        next_if_expression_companion_id_delta: u32,
    ) -> ParseLocalValueSnapshot {
        let consumed_end = source.len() - remainder.len();
        let prefix = &source[..consumed_end];
        let mut expected = before.clone();
        expected.line = expected_line_after_prefix(before.line, prefix);
        let unterminated_depth = unterminated_block_comment_depth(prefix);
        if unterminated_depth > 0 {
            expected
                .lexical_modes
                .push(EmbeddedLexicalMode::BlockComment {
                    depth: unterminated_depth,
                });
        }
        expected.next_diagnostic_id += diagnostic_delta;
        expected.next_if_expression_companion_id += next_if_expression_companion_id_delta;
        expected
    }

    fn assert_full_local_parity_with_semantic_delta(
        source: &str,
        ast: &AstOutcome,
        direct: &DirectOutcome,
        next_if_expression_companion_id_delta: u32,
    ) {
        let expected_ast_after = expected_local_after(
            &ast.before,
            source,
            &ast.remainder,
            0,
            next_if_expression_companion_id_delta,
        );
        assert_eq!(
            expected_ast_after, ast.after,
            "AST full local state: {source:?}"
        );
        let expected_direct_after = expected_local_after(
            &direct.before,
            source,
            &direct.remainder,
            direct.recoveries.len() as u32,
            next_if_expression_companion_id_delta,
        );
        assert_eq!(
            expected_direct_after, direct.after,
            "direct full local state: {source:?}"
        );
        assert_full_local_ast_direct_after_parity(source, ast, direct);
    }

    fn assert_full_local_ast_direct_after_parity(
        source: &str,
        ast: &AstOutcome,
        direct: &DirectOutcome,
    ) {
        let mut normalized_direct_after = direct.after.clone();
        normalized_direct_after.next_diagnostic_id = ast.after.next_diagnostic_id;
        assert_eq!(
            ast.after, normalized_direct_after,
            "AST/direct full local parity: {source:?}"
        );
    }

    fn assert_common_parity(source: &str, ast: &AstOutcome, direct: &DirectOutcome) {
        assert_common_parity_with_cut(source, ast, direct, false, false);
    }

    fn assert_common_parity_with_cut(
        source: &str,
        ast: &AstOutcome,
        direct: &DirectOutcome,
        expected_ast_cut: bool,
        expected_direct_cut: bool,
    ) {
        assert_common_parity_with_cut_and_semantic_delta(
            source,
            ast,
            direct,
            expected_ast_cut,
            expected_direct_cut,
            0,
        );
    }

    fn assert_common_parity_with_cut_and_semantic_delta(
        source: &str,
        ast: &AstOutcome,
        direct: &DirectOutcome,
        expected_ast_cut: bool,
        expected_direct_cut: bool,
        next_if_expression_companion_id_delta: u32,
    ) {
        assert_eq!(
            ast.complete.len(),
            direct.statement_count,
            "items: {source:?}"
        );
        assert_eq!(ast.remainder, direct.remainder, "remainder: {source:?}");
        assert_eq!(
            format!("{}{}", direct.emitted, direct.remainder),
            source,
            "parser prefix plus retained remainder: {source:?}"
        );
        assert_full_local_parity_with_semantic_delta(
            source,
            ast,
            direct,
            next_if_expression_companion_id_delta,
        );
        assert!(ast.sink_clean, "AST sink: {source:?}");
        assert!(direct.sink_clean, "direct sink: {source:?}");
        assert_eq!(ast.cut, expected_ast_cut, "AST cut: {source:?}");
        assert_eq!(direct.cut, expected_direct_cut, "direct cut: {source:?}");
        for (index, record) in direct.recoveries.iter().enumerate() {
            let expected = if record.site.role == declaration_companion_separator_role() {
                ExpectedSyntax::StatementSeparator
            } else {
                assert!(
                    record.site.role == declaration_companion_item_role()
                        || record.site.role == declaration_companion_indented_item_role(),
                    "unexpected Gate 2 companion recovery role: {source:?}"
                );
                ExpectedSyntax::Statement
            };
            assert_eq!(
                record.id.0,
                direct.before.next_diagnostic_id + index as u32,
                "recovery source order: {source:?}"
            );
            match record.kind {
                RecoveryKind::Missing => {
                    assert!(
                        record.unexpected.is_empty(),
                        "missing unexpected: {source:?}"
                    )
                }
                RecoveryKind::Error => assert_eq!(
                    record.unexpected.as_ref(),
                    [UnexpectedSyntax::Token {
                        range: record.site.range.clone(),
                        category: UnexpectedCategory::OtherCharacter,
                    }],
                    "error unexpected order: {source:?}"
                ),
            }
            assert_eq!(
                record.expectations.as_ref(),
                [SyntaxExpectation {
                    role: record.site.role,
                    expected,
                    range: record.site.range.clone(),
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }],
                "expectation/source order: {source:?}"
            );
            assert_eq!(
                record.primary_expectation, 0,
                "primary expectation: {source:?}"
            );
        }
    }

    fn recovery_summary(
        records: &[CommittedRecoveryRecord],
    ) -> Vec<(RecoveryKind, GrammarRole, Range<usize>)> {
        records
            .iter()
            .map(|record| (record.kind, record.site.role, record.site.range.clone()))
            .collect()
    }

    fn gate2_indented_statement_only_companion_recovery_and_boundaries_match() {
        let indented_item = declaration_companion_indented_item_role();
        for (source, block_indent, complete, remainder, recoveries) in [
            ("first\nsecond", 0, vec![true, true], "", vec![]),
            (
                "@ first\nsecond",
                0,
                vec![true, true],
                "",
                vec![(RecoveryKind::Error, indented_item, 0..2)],
            ),
            (
                "@ \nsecond",
                0,
                vec![false, true],
                "",
                vec![(RecoveryKind::Error, indented_item, 0..2)],
            ),
            (
                ";first",
                0,
                vec![false, true],
                "",
                vec![(RecoveryKind::Missing, indented_item, 0..0)],
            ),
            ("first;\nouter", 2, vec![true], "\nouter", vec![]),
            ("first\nouter", 2, vec![true], "\nouter", vec![]),
            (
                ")outer",
                0,
                vec![false],
                ")outer",
                vec![(RecoveryKind::Missing, indented_item, 0..0)],
            ),
        ] {
            let ast = run_indented_ast(source, block_indent);
            let direct = run_indented_direct(source, block_indent);
            assert_common_parity(source, &ast, &direct);
            assert_eq!(ast.complete, complete, "complete items: {source:?}");
            assert_eq!(ast.remainder, remainder, "boundary: {source:?}");
            assert_eq!(
                recovery_summary(&direct.recoveries),
                recoveries,
                "recoveries: {source:?}"
            );
        }
    }

    fn gate2_braced_statement_only_companion_recovery_and_transitions_match() {
        let item = declaration_companion_item_role();
        let separator = declaration_companion_separator_role();
        for (source, complete, remainder, recoveries) in [
            ("", vec![], "", vec![]),
            ("}outer", vec![], "}outer", vec![]),
            (")outer", vec![], ")outer", vec![]),
            ("]outer", vec![], "]outer", vec![]),
            (" \t)outer", vec![], " \t)outer", vec![]),
            ("first,second", vec![true, true], "", vec![]),
            (
                ",first",
                vec![false, true],
                "",
                vec![(RecoveryKind::Missing, item, 0..0)],
            ),
            (
                "first,,second",
                vec![true, false, true],
                "",
                vec![(RecoveryKind::Missing, item, 6..6)],
            ),
            ("first,}", vec![true], "}", vec![]),
            ("first,)", vec![true], ")", vec![]),
            ("first,]", vec![true], "]", vec![]),
            ("first)", vec![true], ")", vec![]),
            ("first]", vec![true], "]", vec![]),
            (
                "@ first}",
                vec![true],
                "}",
                vec![(RecoveryKind::Error, item, 0..2)],
            ),
            (
                "@}",
                vec![false],
                "}",
                vec![(RecoveryKind::Error, item, 0..1)],
            ),
            (
                "first second}",
                vec![true, true],
                "}",
                vec![(RecoveryKind::Missing, separator, 6..6)],
            ),
            ("first\nsecond}", vec![true, true], "}", vec![]),
        ] {
            let ast = run_braced_ast(source);
            let direct = run_braced_direct(source);
            assert_common_parity(source, &ast, &direct);
            assert_eq!(ast.complete, complete, "complete items: {source:?}");
            assert_eq!(ast.remainder, remainder, "boundary: {source:?}");
            assert_eq!(
                recovery_summary(&direct.recoveries),
                recoveries,
                "recoveries: {source:?}"
            );
        }
        for source in [")outer", "]outer", " \t)outer"] {
            let direct = run_braced_direct(source);
            assert_eq!(direct.child_kinds, Vec::<SyntaxKind>::new(), "{source:?}");
            assert_eq!(direct.node_kinds, vec![SyntaxKind::Root], "{source:?}");
            assert!(direct.tokens.is_empty(), "{source:?}");
            assert!(direct.recoveries.is_empty(), "{source:?}");
            assert_eq!(direct.emitted, "", "{source:?}");
            assert_eq!(direct.remainder, source, "{source:?}");
        }
    }

    fn gate2_statement_only_companion_keeps_ast_direct_cardinality_and_stack_state() {
        for source in ["first", "@ first", "@", ";first", "first;second"] {
            let ast = run_indented_ast(source, 0);
            let direct = run_indented_direct(source, 0);
            assert_common_parity(source, &ast, &direct);
        }
        for source in ["", "first", "@ first", "@", ",first", "first,second"] {
            let ast = run_braced_ast(source);
            let direct = run_braced_direct(source);
            assert_common_parity(source, &ast, &direct);
        }
    }

    fn assert_statement_recovery(
        record: &CommittedRecoveryRecord,
        kind: RecoveryKind,
        role: GrammarRole,
        range: Range<usize>,
    ) {
        assert_eq!(record.kind, kind);
        assert_eq!(record.site.role, role);
        assert_eq!(record.site.range, range);
        match kind {
            RecoveryKind::Missing => assert!(record.unexpected.is_empty()),
            RecoveryKind::Error => assert_eq!(
                record.unexpected.as_ref(),
                [UnexpectedSyntax::Token {
                    range: range.clone(),
                    category: UnexpectedCategory::OtherCharacter,
                }]
            ),
        }
        assert_eq!(
            record.expectations.as_ref(),
            [SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Statement,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]
        );
        assert_eq!(record.primary_expectation, 0);
    }

    fn gate2_comment_aware_recovery_is_atomic_and_ast_direct_exact() {
        let item = declaration_companion_item_role();
        for (source, complete, error_end, remainder) in [
            (
                "@ /* } first,;)] inside */ value}",
                vec![true],
                "@ /* } first,;)] inside */ ".len(),
                "}",
            ),
            (
                "@ /* outer /* first,;)]} */ end */ value}",
                vec![true],
                "@ /* outer /* first,;)]} */ end */ ".len(),
                "}",
            ),
            (
                "@ // first,;)]} inside\nvalue}",
                vec![false, true],
                "@ // first,;)]} inside".len(),
                "}",
            ),
            (
                "@ /* unterminated first,;)]}",
                vec![false],
                "@ /* unterminated first,;)]}".len(),
                "",
            ),
        ] {
            let ast = run_braced_ast(source);
            let direct = run_braced_direct(source);
            assert_common_parity(source, &ast, &direct);
            assert_eq!(ast.complete, complete, "{source:?}");
            assert_eq!(ast.remainder, remainder, "{source:?}");
            assert_eq!(direct.recoveries.len(), 1, "{source:?}");
            assert_statement_recovery(
                &direct.recoveries[0],
                RecoveryKind::Error,
                item,
                0..error_end,
            );
            assert_eq!(
                direct.recoveries[0].id.0, direct.before.next_diagnostic_id,
                "{source:?}"
            );
            let mut expected_lexical_modes = ast.before.lexical_modes.clone();
            if source.contains("unterminated") {
                expected_lexical_modes.push(EmbeddedLexicalMode::BlockComment { depth: 1 });
            }
            assert_eq!(
                ast.after.lexical_modes, expected_lexical_modes,
                "lexical mode exit: {source:?}"
            );
            assert_eq!(direct.tokens.first().map(|token| token.1.start), Some(0));
            assert_eq!(
                direct.tokens.last().map(|token| token.1.end),
                Some(source.len() - remainder.len())
            );
            assert_eq!(
                direct
                    .tokens
                    .windows(2)
                    .map(|pair| (pair[0].1.end, pair[1].1.start))
                    .collect::<Vec<_>>(),
                direct
                    .tokens
                    .windows(2)
                    .map(|pair| (pair[0].1.end, pair[0].1.end))
                    .collect::<Vec<_>>(),
                "contiguous token ranges: {source:?}"
            );
            assert_eq!(
                direct
                    .tokens
                    .iter()
                    .map(|token| token.2.as_str())
                    .collect::<String>(),
                &source[..source.len() - remainder.len()],
                "token text order: {source:?}"
            );
            let expected_tokens = if source.contains("unterminated") {
                vec![(SyntaxKind::Unknown, 0..source.len(), source.to_owned())]
            } else if complete.len() == 2 {
                vec![
                    (
                        SyntaxKind::Unknown,
                        0..error_end,
                        source[..error_end].to_owned(),
                    ),
                    (
                        SyntaxKind::Newline,
                        error_end..error_end + 1,
                        "\n".to_owned(),
                    ),
                    (
                        SyntaxKind::Identifier,
                        error_end + 1..source.len() - 1,
                        "value".to_owned(),
                    ),
                ]
            } else {
                vec![
                    (
                        SyntaxKind::Unknown,
                        0..error_end,
                        source[..error_end].to_owned(),
                    ),
                    (
                        SyntaxKind::Identifier,
                        error_end..source.len() - 1,
                        "value".to_owned(),
                    ),
                ]
            };
            assert_eq!(direct.tokens, expected_tokens, "exact tokens: {source:?}");
            assert_eq!(
                direct.child_kinds,
                if complete.len() == 2 {
                    vec![
                        SyntaxKind::Statement,
                        SyntaxKind::BlockStatementSeparator,
                        SyntaxKind::Statement,
                    ]
                } else {
                    vec![SyntaxKind::Statement]
                },
                "sequence shell nodes: {source:?}"
            );
            assert_eq!(
                direct.node_kinds,
                if complete.len() == 2 {
                    vec![
                        SyntaxKind::Root,
                        SyntaxKind::Statement,
                        SyntaxKind::Error,
                        SyntaxKind::BlockStatementSeparator,
                        SyntaxKind::Statement,
                        SyntaxKind::OperatorChain,
                        SyntaxKind::IdentifierExpression,
                    ]
                } else if source.contains("unterminated") {
                    vec![SyntaxKind::Root, SyntaxKind::Statement, SyntaxKind::Error]
                } else {
                    vec![
                        SyntaxKind::Root,
                        SyntaxKind::Statement,
                        SyntaxKind::Error,
                        SyntaxKind::OperatorChain,
                        SyntaxKind::IdentifierExpression,
                    ]
                },
                "exact sequence descendant nodes: {source:?}"
            );
        }
    }

    fn gate2_candidate_operator_table() -> OperatorTable {
        OperatorTable::from_declarations([
            OperatorDeclaration::new(
                "+",
                OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            ),
            OperatorDeclaration::new("!", OperatorFixities::new().with_nullfix()),
        ])
        .expect("Gate 2 candidate operators are non-conflicting")
    }

    fn gate2_comment_prefix_operator_table() -> OperatorTable {
        OperatorTable::from_declarations([OperatorDeclaration::new(
            "/",
            OperatorFixities::new()
                .with_prefix(BindingPower::scalar(70))
                .with_nullfix(),
        )])
        .expect("the comment-prefix regression operator is non-conflicting")
    }

    fn gate2_comment_openers_precede_slash_statement_candidates() {
        let table = gate2_comment_prefix_operator_table();
        for source in ["/", "/ value"] {
            let ast = run_indented_ast_with_table(source, 0, &table);
            let direct = run_indented_direct_with_table(source, 0, &table);
            assert_common_parity_with_cut(source, &ast, &direct, false, source != "/");
            assert_eq!(
                ast.complete,
                vec![true],
                "normal slash Statement: {source:?}"
            );
            assert!(direct.recoveries.is_empty(), "{source:?}");
        }

        let non_comment = "@ / value}";
        let ast = run_braced_ast_with_table(non_comment, &table);
        let direct = run_braced_direct_with_table(non_comment, &table);
        assert_common_parity_with_cut(non_comment, &ast, &direct, false, true);
        assert_eq!(ast.complete, vec![true]);
        assert_eq!(ast.remainder, "}");
        assert_eq!(
            recovery_summary(&direct.recoveries),
            vec![(RecoveryKind::Error, declaration_companion_item_role(), 0..2,)]
        );
        assert!(
            direct.node_kinds.contains(&SyntaxKind::PrefixOperatorUse),
            "the non-comment slash remains the retried Statement candidate"
        );

        for (source, complete, error_end) in [
            (
                "@ /* / internal value; ) ] } , */ value}",
                vec![true],
                "@ /* / internal value; ) ] } , */ ".len(),
            ),
            (
                "@ // / internal value; ) ] } ,\nvalue}",
                vec![false, true],
                "@ // / internal value; ) ] } ,".len(),
            ),
        ] {
            let ast = run_braced_ast_with_table(source, &table);
            let direct = run_braced_direct_with_table(source, &table);
            assert_common_parity(source, &ast, &direct);
            assert_eq!(ast.complete, complete, "{source:?}");
            assert_eq!(ast.remainder, "}", "{source:?}");
            assert_eq!(
                recovery_summary(&direct.recoveries),
                vec![(
                    RecoveryKind::Error,
                    declaration_companion_item_role(),
                    0..error_end,
                )]
            );
            assert!(
                !direct.node_kinds.iter().any(|kind| matches!(
                    kind,
                    SyntaxKind::PrefixOperatorUse | SyntaxKind::NullfixOperatorUse
                )),
                "a slash inside the comment cannot become a retry: {source:?}"
            );
        }
    }

    fn gate2_if_retry_allocates_one_identity_only_after_candidate_probe() {
        let table = OperatorTable::empty();
        let source = "@ if value: value}";

        let mut input = SourceInput::new(source);
        let mut local = seeded_test_local();
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        assert_eq!(
            canonical_statement_invalid_run(&table, &mut i),
            Some((0..2, true))
        );
        let remainder = i.input.remainder().to_owned();
        drop(i);
        assert_eq!(remainder, "if value: value}");
        assert_eq!(
            local.value_snapshot(),
            expected_local_after(&before, source, &remainder, 0, 0),
            "the candidate probe must not allocate an If companion identity"
        );
        assert!(sink.take_merged().is_none());
        assert!(!cut);

        let ast = run_braced_ast(source);
        let direct = run_braced_direct(source);
        assert_common_parity_with_cut_and_semantic_delta(source, &ast, &direct, true, true, 1);
        assert_eq!(ast.complete, vec![true]);
        assert_eq!(ast.remainder, "}");
        assert_eq!(
            recovery_summary(&direct.recoveries),
            vec![(RecoveryKind::Error, declaration_companion_item_role(), 0..2)]
        );
        assert_eq!(
            direct
                .node_kinds
                .iter()
                .filter(|kind| **kind == SyntaxKind::IfExpression)
                .count(),
            1
        );
    }

    fn gate2_every_canonical_statement_candidate_family_has_ast_direct_parity() {
        let table = gate2_candidate_operator_table();
        for (family, source) in [
            ("binding declaration", "my value = 1"),
            ("use declaration", "use std::io"),
            ("mod declaration", "mod outer;"),
            ("struct declaration", "struct Marker;"),
            ("enum declaration", "enum Choice { One }"),
            ("error declaration", "error Failure { One }"),
            ("type declaration", "type Value = Int"),
            ("role declaration", "role Eq;"),
            ("impl declaration", "impl Int;"),
            ("cast declaration", "cast(value: A): Int"),
            ("act declaration", "act Console::Read;"),
            ("for statement", "for value in values: value"),
            ("parenthesized NUD", "()"),
            ("braced-block NUD", "{}"),
            ("if NUD", "if value: value"),
            ("case NUD", "case value: item -> value"),
            ("catch NUD", "catch value: item -> value"),
            ("identifier NUD", "value"),
            ("integer NUD", "1"),
            ("prefix NUD", "+value"),
            ("nullfix NUD", "!"),
        ] {
            let ast = run_indented_ast_with_table(source, 0, &table);
            let direct = run_indented_direct_with_table(source, 0, &table);
            assert_eq!(ast.complete.len(), direct.statement_count, "{family}");
            assert_eq!(ast.remainder, direct.remainder, "{family}");
            assert_eq!(
                format!("{}{}", direct.emitted, direct.remainder),
                source,
                "{family}"
            );
            assert_full_local_parity_with_semantic_delta(
                source,
                &ast,
                &direct,
                u32::from(family == "if NUD"),
            );
            assert_eq!(ast.complete, vec![true], "{family}: {source:?}");
            assert_eq!(ast.remainder, "", "{family}: {source:?}");

            let braced_source = format!("{source}}}");
            let ast = run_braced_ast_with_table(&braced_source, &table);
            let direct = run_braced_direct_with_table(&braced_source, &table);
            assert_eq!(
                ast.complete.len(),
                direct.statement_count,
                "braced {family}"
            );
            assert_eq!(ast.remainder, direct.remainder, "braced {family}");
            assert_eq!(
                format!("{}{}", direct.emitted, direct.remainder),
                braced_source,
                "braced {family}"
            );
            assert_full_local_parity_with_semantic_delta(
                &braced_source,
                &ast,
                &direct,
                u32::from(family == "if NUD"),
            );
            assert_eq!(ast.complete, vec![true], "braced {family}: {source:?}");
            assert_eq!(ast.remainder, "}", "braced {family}: {source:?}");
        }
    }

    fn gate2_valid_large_sequences_never_call_the_recovery_candidate_helper() {
        let table = OperatorTable::empty();
        assert_eq!(synthetic_indented_source(0), "");
        assert_eq!(synthetic_indented_source(3), "item\nitem\nitem");
        assert_eq!(synthetic_braced_source(3), "item,item,item");
        for item_count in [1_000, 10_000] {
            let indented = synthetic_indented_source(item_count);
            reset_canonical_statement_candidate_input_calls();
            let (items, remainder) = timed_indented_ast(&table, &indented);
            assert_eq!(items.len(), item_count);
            assert_eq!(remainder, 0);
            assert_eq!(canonical_statement_candidate_input_calls(), 0);

            reset_canonical_statement_candidate_input_calls();
            let (output, remainder) = timed_indented_direct(&table, &indented);
            assert_eq!(remainder, 0);
            assert_eq!(canonical_statement_candidate_input_calls(), 0);
            black_box(output);

            let braced = synthetic_braced_source(item_count);
            reset_canonical_statement_candidate_input_calls();
            let (items, remainder) = timed_braced_ast(&table, &braced);
            assert_eq!(items.len(), item_count);
            assert_eq!(remainder, 0);
            assert_eq!(canonical_statement_candidate_input_calls(), 0);

            reset_canonical_statement_candidate_input_calls();
            let (output, remainder) = timed_braced_direct(&table, &braced);
            assert_eq!(remainder, 0);
            assert_eq!(canonical_statement_candidate_input_calls(), 0);
            black_box(output);
        }
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    enum Gate3FormSummary {
        ColonIncomplete,
        Inline {
            semicolon: Option<Range<usize>>,
        },
        Indented {
            base_indent: usize,
            block_indent: usize,
        },
        Braced {
            close_complete: bool,
        },
    }

    #[derive(Debug)]
    struct Gate3AstOutcome {
        accepted: bool,
        range: Option<Range<usize>>,
        form: Option<Gate3FormSummary>,
        merged: Option<StdSummary<char>>,
        latest_sink_debug: String,
        sequence: AstOutcome,
    }

    fn gate3_item_completeness(
        companion: &DeclarationCompanion<'_>,
    ) -> (Gate3FormSummary, Vec<bool>) {
        match &companion.form {
            DeclarationCompanionForm::Colon {
                body: Recovered::Incomplete,
                ..
            } => (Gate3FormSummary::ColonIncomplete, Vec::new()),
            DeclarationCompanionForm::Colon {
                body: Recovered::Complete(DeclarationCompanionColonBody::Inline { semicolon, .. }),
                ..
            } => (
                Gate3FormSummary::Inline {
                    semicolon: semicolon.clone(),
                },
                vec![true],
            ),
            DeclarationCompanionForm::Colon {
                body: Recovered::Complete(DeclarationCompanionColonBody::Indented(body)),
                ..
            } => (
                Gate3FormSummary::Indented {
                    base_indent: body.base_indent,
                    block_indent: body.block_indent,
                },
                body.items.iter().map(item_is_complete).collect(),
            ),
            DeclarationCompanionForm::Braced { items, close, .. } => (
                Gate3FormSummary::Braced {
                    close_complete: matches!(close, Recovered::Complete(_)),
                },
                items.iter().map(item_is_complete).collect(),
            ),
        }
    }

    fn run_gate3_ast(source: &str, base_indent: usize) -> Gate3AstOutcome {
        run_gate3_ast_with_table(source, base_indent, &OperatorTable::empty())
    }

    fn run_gate3_ast_with_table(
        source: &str,
        base_indent: usize,
        table: &OperatorTable,
    ) -> Gate3AstOutcome {
        let mut input = SourceInput::new(source);
        let mut local = seeded_gate3_test_local();
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let companion = parse_declaration_companion_isolated(table, base_indent, &mut i);
        let remainder = i.input.remainder().to_owned();
        let (form, complete) = companion
            .as_ref()
            .map(gate3_item_completeness)
            .map_or((None, Vec::new()), |(form, complete)| {
                (Some(form), complete)
            });
        let range = companion.as_ref().map(|companion| companion.range.clone());
        drop(i);
        let latest_sink_debug = format!("{sink:?}");
        let merged = sink.take_merged();
        let sink_clean = merged.is_none();
        Gate3AstOutcome {
            accepted: companion.is_some(),
            range,
            form,
            merged,
            latest_sink_debug,
            sequence: AstOutcome {
                complete,
                remainder,
                before,
                after: local.value_snapshot(),
                sink_clean,
                cut,
            },
        }
    }

    fn run_gate3_direct(source: &str, base_indent: usize) -> (Option<Range<usize>>, DirectOutcome) {
        run_gate3_direct_with_table(source, base_indent, &OperatorTable::empty())
    }

    fn run_gate3_direct_with_table(
        source: &str,
        base_indent: usize,
        table: &OperatorTable,
    ) -> (Option<Range<usize>>, DirectOutcome) {
        let mut input = SourceInput::new(source);
        let mut local = seeded_gate3_test_local();
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let probe = Probe::new(i);
        let mut committed = probe.commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        let range = commit_declaration_companion_isolated(table, base_indent, &mut committed);
        let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
        committed.finish_node();
        let output = committed.into_output();
        let recoveries = output.committed_recoveries().to_vec();
        let root = SyntaxNode::new_root(output.finish_prefix());
        let child_kinds = root.children().map(|node| node.kind()).collect();
        let first_child_kinds = root
            .children()
            .next()
            .map(|node| node.children().map(|child| child.kind()).collect())
            .unwrap_or_default();
        let derives_parent_kinds = root
            .descendants()
            .filter(|node| {
                node.children()
                    .any(|child| child.kind() == SyntaxKind::DerivesClause)
            })
            .map(|node| node.kind())
            .collect();
        let node_kinds = root.descendants().map(|node| node.kind()).collect();
        let tokens = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| {
                let range = token.text_range();
                (
                    token.kind(),
                    usize::from(range.start())..usize::from(range.end()),
                    token.text().to_owned(),
                )
            })
            .collect();
        (
            range,
            DirectOutcome {
                statement_count: root
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::Statement)
                    .count(),
                remainder,
                recoveries,
                emitted: root.to_string(),
                child_kinds,
                first_child_kinds,
                derives_parent_kinds,
                node_kinds,
                tokens,
                before,
                after: local.value_snapshot(),
                sink_clean: sink.take_merged().is_none(),
                cut,
            },
        )
    }

    fn seed_gate3_candidate_sink(sink: &mut chasa::LatestSink<usize, StdErr<char>>) {
        <chasa::LatestSink<usize, StdErr<char>> as ErrorSink<usize>>::push(
            sink,
            0..1,
            StdErr::Expected(Expected::new(31, "gate3-preseed-first", ())),
        );
        <chasa::LatestSink<usize, StdErr<char>> as ErrorSink<usize>>::push(
            sink,
            0..1,
            StdErr::Expected(Expected::new(31, "gate3-preseed-second", ())),
        );
    }

    fn gate3_candidate_preseed_summary() -> StdSummary<char> {
        StdSummary {
            unexpected: None,
            expected: vec![
                Expected::new(31, "gate3-preseed-first", ()),
                Expected::new(31, "gate3-preseed-second", ()),
            ],
        }
    }

    fn run_gate3_canonical_sink_control(
        source: &str,
        preseed: bool,
    ) -> (String, Option<StdSummary<char>>, String) {
        let table = OperatorTable::empty();
        let mut input = SourceInput::new(source);
        let mut local = seeded_gate3_test_local();
        enter_test_braced_owner_scope(&mut local);
        local.set_ml_arg(false);
        let mut sink: chasa::LatestSink<usize, StdErr<char>> = chasa::LatestSink::new();
        if preseed {
            seed_gate3_candidate_sink(&mut sink);
        }
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let items = parse_braced_declaration_companion_statement_items(&table, &mut i);
        assert_eq!(items.len(), 1, "canonical sink control Statement");
        let remainder = i.input.remainder().to_owned();
        drop(i);
        let latest_sink_debug = format!("{sink:?}");
        (remainder, sink.take_merged(), latest_sink_debug)
    }

    #[test]
    fn gate3_isolated_companion_form_recovery_and_state_table() {
        let introducer = declaration_companion_introducer_role();
        let body = declaration_companion_body_role();
        let item = declaration_companion_item_role();
        let separator = declaration_companion_separator_role();
        let close = declaration_companion_close_role();
        let nested_call_item = GrammarRole::Expression(ExpressionRole::CallArgument);
        for (
            source,
            base_indent,
            form,
            complete,
            direct_statement_count,
            remainder,
            next_if_delta,
            recoveries,
        ) in [
            (
                "with: item;tail",
                0,
                Some(Gate3FormSummary::Inline {
                    semicolon: Some(10..11),
                }),
                vec![true],
                1,
                "tail",
                0,
                vec![],
            ),
            (
                "with:\n  first\n  second\nouter",
                0,
                Some(Gate3FormSummary::Indented {
                    base_indent: 0,
                    block_indent: 2,
                }),
                vec![true, true],
                2,
                "\nouter",
                0,
                vec![],
            ),
            (
                "with { first, second }tail",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: true,
                }),
                vec![true, true],
                2,
                "tail",
                0,
                vec![],
            ),
            (
                "with {}tail",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: true,
                }),
                vec![],
                0,
                "tail",
                0,
                vec![],
            ),
            (
                "with",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                0,
                "",
                0,
                vec![(RecoveryKind::Missing, introducer, 4..4)],
            ),
            (
                "with]tail",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                0,
                "]tail",
                0,
                vec![(RecoveryKind::Missing, introducer, 4..4)],
            ),
            (
                "with item",
                0,
                Some(Gate3FormSummary::Inline { semicolon: None }),
                vec![true],
                1,
                "",
                0,
                vec![(RecoveryKind::Missing, introducer, 5..5)],
            ),
            (
                "with :: item",
                0,
                Some(Gate3FormSummary::Inline { semicolon: None }),
                vec![true],
                1,
                "",
                0,
                vec![(RecoveryKind::Error, introducer, 5..6)],
            ),
            (
                "with:\nouter",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                0,
                "\nouter",
                0,
                vec![(RecoveryKind::Missing, body, 5..5)],
            ),
            (
                "with { enum E {} type T = Int }",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: true,
                }),
                vec![true, true],
                2,
                "",
                0,
                vec![(RecoveryKind::Missing, separator, 17..17)],
            ),
            (
                "with { @ first }",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: true,
                }),
                vec![true],
                1,
                "",
                0,
                vec![(RecoveryKind::Error, item, 7..9)],
            ),
            (
                "with { f(@a) }tail",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: true,
                }),
                vec![true],
                1,
                "tail",
                0,
                vec![(RecoveryKind::Error, nested_call_item, 9..10)],
            ),
            (
                "with { first",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: false,
                }),
                vec![true],
                1,
                "",
                0,
                vec![(RecoveryKind::Missing, close, 12..12)],
            ),
            (
                "with { first)}tail",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: true,
                }),
                vec![true],
                1,
                "tail",
                0,
                vec![(RecoveryKind::Error, close, 12..13)],
            ),
            (
                "with { first]tail",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: false,
                }),
                vec![true],
                1,
                "]tail",
                0,
                vec![(RecoveryKind::Missing, close, 12..12)],
            ),
            (
                "with {,first}",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: true,
                }),
                vec![false, true],
                2,
                "",
                0,
                vec![(RecoveryKind::Missing, item, 6..6)],
            ),
            (
                "with {first,}",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: true,
                }),
                vec![true],
                1,
                "",
                0,
                vec![],
            ),
            (
                "with {,,first}",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: true,
                }),
                vec![false, false, true],
                3,
                "",
                0,
                vec![
                    (RecoveryKind::Missing, item, 6..6),
                    (RecoveryKind::Missing, item, 7..7),
                ],
            ),
            (
                "with {first;}tail",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: true,
                }),
                vec![true],
                1,
                "tail",
                0,
                vec![],
            ),
            (
                "with { @ }tail",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: true,
                }),
                vec![false],
                1,
                "tail",
                0,
                vec![(RecoveryKind::Error, item, 7..9)],
            ),
            (
                "with { @ ]tail",
                0,
                Some(Gate3FormSummary::Braced {
                    close_complete: false,
                }),
                vec![false],
                1,
                "]tail",
                0,
                vec![
                    (RecoveryKind::Error, item, 7..9),
                    (RecoveryKind::Missing, close, 9..9),
                ],
            ),
            (
                "with:",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                0,
                "",
                0,
                vec![(RecoveryKind::Missing, body, 5..5)],
            ),
            (
                "with: ,tail",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                0,
                ",tail",
                0,
                vec![(RecoveryKind::Missing, body, 6..6)],
            ),
            (
                "with: ;tail",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                0,
                ";tail",
                0,
                vec![(RecoveryKind::Missing, body, 6..6)],
            ),
            (
                "with: ]tail",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                0,
                "]tail",
                0,
                vec![(RecoveryKind::Missing, body, 6..6)],
            ),
            (
                "with:\n  ",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                0,
                "\n  ",
                0,
                vec![(RecoveryKind::Missing, body, 5..5)],
            ),
            (
                "with:\n  ]tail",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                0,
                "\n  ]tail",
                0,
                vec![(RecoveryKind::Missing, body, 5..5)],
            ),
            (
                "with:\n  else",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                0,
                "\n  else",
                0,
                vec![(RecoveryKind::Missing, body, 5..5)],
            ),
            (
                "with: @ ,tail",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                1,
                ",tail",
                0,
                vec![(RecoveryKind::Error, body, 6..8)],
            ),
            (
                "with: @ ;tail",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                1,
                ";tail",
                0,
                vec![(RecoveryKind::Error, body, 6..8)],
            ),
            (
                "with @// : { item\n: item",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                0,
                "\n: item",
                0,
                vec![(RecoveryKind::Error, introducer, 5..17)],
            ),
            (
                "with @/* : { ) ] item */: item",
                0,
                Some(Gate3FormSummary::Inline { semicolon: None }),
                vec![true],
                1,
                "",
                0,
                vec![(RecoveryKind::Error, introducer, 5..24)],
            ),
            (
                "with @/* outer : { ) ] item /* nested */ */: item",
                0,
                Some(Gate3FormSummary::Inline { semicolon: None }),
                vec![true],
                1,
                "",
                0,
                vec![(RecoveryKind::Error, introducer, 5..43)],
            ),
            (
                "with @/* : { ) ] item",
                0,
                Some(Gate3FormSummary::ColonIncomplete),
                vec![],
                0,
                "",
                0,
                vec![(RecoveryKind::Error, introducer, 5..21)],
            ),
            (
                "with: if condition: value",
                0,
                Some(Gate3FormSummary::Inline { semicolon: None }),
                vec![true],
                1,
                "",
                1,
                vec![],
            ),
        ] {
            let ast = run_gate3_ast(source, base_indent);
            let (direct_range, direct) = run_gate3_direct(source, base_indent);
            if source == "with { f(@a) }tail" {
                assert_eq!(
                    ast.merged,
                    Some(StdSummary {
                        unexpected: Some(Unexpected::Item('@')),
                        expected: Vec::new(),
                    }),
                    "nested canonical expectation remains committed"
                );
                assert_eq!(
                    ast.latest_sink_debug,
                    "LatestSink { range: Some(9..10), errors: [Unexpected(Item('@'))], \
                     group_start: 0, undo: [SetNone { old_len: 0 }], base_index: 0 }",
                    "exact nested canonical expectation range"
                );
            } else {
                assert!(ast.merged.is_none(), "clean AST sink: {source:?}");
            }
            assert!(ast.accepted, "accepted form: {source:?}");
            assert_eq!(ast.form, form, "AST form: {source:?}");
            assert_eq!(ast.sequence.complete, complete, "AST items: {source:?}");
            assert_eq!(
                ast.sequence.remainder, remainder,
                "AST remainder: {source:?}"
            );
            assert_eq!(direct.remainder, remainder, "direct remainder: {source:?}");
            assert_eq!(ast.range, direct_range, "range parity: {source:?}");
            assert_eq!(
                direct.statement_count, direct_statement_count,
                "item cardinality: {source:?}"
            );
            assert_eq!(
                recovery_summary(&direct.recoveries),
                recoveries,
                "typed recovery: {source:?}"
            );
            for (index, record) in direct.recoveries.iter().enumerate() {
                assert_eq!(
                    record.id.0,
                    direct.before.next_diagnostic_id + index as u32,
                    "recovery order: {source:?}"
                );
                assert_eq!(
                    record.primary_expectation, 0,
                    "primary recovery: {source:?}"
                );
                assert!(
                    record.expectations.iter().all(|expectation| {
                        expectation.role == record.site.role
                            && expectation.range == record.site.range
                            && expectation.sources == ExpectationSources::COMMITTED_RECOVERY_RULE
                    }),
                    "expectation ownership: {source:?}"
                );
                match record.kind {
                    RecoveryKind::Missing => {
                        assert!(record.unexpected.is_empty(), "missing payload: {source:?}")
                    }
                    RecoveryKind::Error if record.site.role == close => assert_eq!(
                        record.unexpected.as_ref(),
                        [UnexpectedSyntax::Token {
                            range: record.site.range.clone(),
                            category: UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                                Delimiter::Parenthesis
                            ),),
                        }],
                        "close error payload: {source:?}"
                    ),
                    RecoveryKind::Error => assert_eq!(
                        record.unexpected.as_ref(),
                        [UnexpectedSyntax::Token {
                            range: record.site.range.clone(),
                            category: UnexpectedCategory::OtherCharacter,
                        }],
                        "error payload: {source:?}"
                    ),
                }
                if record.site.role == introducer {
                    assert_eq!(
                        record.expectations[record.primary_expectation].expected,
                        ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
                        "introducer primary expectation: {source:?}",
                    );
                    assert_eq!(
                        record
                            .expectations
                            .iter()
                            .map(|expectation| expectation.expected)
                            .collect::<Vec<_>>(),
                        vec![
                            ExpectedSyntax::Punctuation(PunctuationEvidence::Open(
                                Delimiter::Brace,
                            )),
                            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
                        ],
                        "introducer expectation order: {source:?}"
                    );
                }
            }
            assert_eq!(
                format!("{}{}", direct.emitted, direct.remainder),
                source,
                "losslessness: {source:?}"
            );
            let consumed_end = source.len() - remainder.len();
            assert_eq!(
                direct.tokens.first().map(|token| token.1.start),
                Some(0),
                "first token range: {source:?}"
            );
            assert_eq!(
                direct.tokens.last().map(|token| token.1.end),
                Some(consumed_end),
                "last token range: {source:?}"
            );
            assert!(
                direct
                    .tokens
                    .windows(2)
                    .all(|pair| pair[0].1.end == pair[1].1.start),
                "contiguous token order: {source:?}"
            );
            assert_eq!(
                direct
                    .tokens
                    .iter()
                    .map(|token| token.2.as_str())
                    .collect::<String>(),
                &source[..consumed_end],
                "exact token text order: {source:?}"
            );
            assert_eq!(
                direct
                    .node_kinds
                    .iter()
                    .filter(|kind| **kind == SyntaxKind::Missing)
                    .count(),
                direct
                    .recoveries
                    .iter()
                    .filter(|record| record.kind == RecoveryKind::Missing)
                    .count(),
                "Missing node/record mapping: {source:?}"
            );
            assert_eq!(
                direct
                    .node_kinds
                    .iter()
                    .filter(|kind| **kind == SyntaxKind::Error)
                    .count(),
                direct
                    .recoveries
                    .iter()
                    .filter(|record| record.kind == RecoveryKind::Error)
                    .count(),
                "Error node/record mapping: {source:?}"
            );
            assert_eq!(
                direct.child_kinds,
                vec![SyntaxKind::DeclarationCompanion],
                "dedicated companion node: {source:?}"
            );
            assert_eq!(
                direct.tokens.first().map(|token| token.0),
                Some(SyntaxKind::WithKw)
            );
            assert!(
                !direct.node_kinds.iter().any(|kind| matches!(
                    kind,
                    SyntaxKind::WithBodyTail
                        | SyntaxKind::IndentedStatementBlock
                        | SyntaxKind::BracedStatementBlockExpression
                )),
                "generic body node leaked into companion CST: {source:?}"
            );
            assert_eq!(
                direct
                    .node_kinds
                    .contains(&SyntaxKind::DeclarationCompanionIndentedBody),
                matches!(form, Some(Gate3FormSummary::Indented { .. })),
                "dedicated indented node: {source:?}"
            );
            let expected_ast =
                expected_local_after(&ast.sequence.before, source, remainder, 0, next_if_delta);
            assert_eq!(expected_ast, ast.sequence.after, "AST state: {source:?}");
            let expected_direct = expected_local_after(
                &direct.before,
                source,
                remainder,
                direct.recoveries.len() as u32,
                next_if_delta,
            );
            assert_eq!(expected_direct, direct.after, "direct state: {source:?}");
            let expected_cut = next_if_delta == 1 || source == "with { f(@a) }tail";
            assert_eq!(ast.sequence.cut, expected_cut, "AST cut: {source:?}");
            assert_eq!(direct.cut, expected_cut, "direct cut: {source:?}");
        }

        let slash_table = gate2_comment_prefix_operator_table();
        for (source, introducer_range) in [
            ("with / value", 5..5),
            ("with @/* / : { item */ / value", 5..23),
        ] {
            let ast = run_gate3_ast_with_table(source, 0, &slash_table);
            let (range, direct) = run_gate3_direct_with_table(source, 0, &slash_table);
            assert!(ast.accepted, "slash form accepted: {source:?}");
            assert_eq!(ast.range, range, "slash range: {source:?}");
            assert_eq!(
                ast.form,
                Some(Gate3FormSummary::Inline { semicolon: None }),
                "slash form: {source:?}"
            );
            assert_eq!(ast.sequence.complete, vec![true], "slash AST: {source:?}");
            assert_eq!(ast.sequence.remainder, "", "slash AST remainder");
            assert_eq!(direct.remainder, "", "slash direct remainder");
            assert_eq!(direct.statement_count, 1, "slash Statement: {source:?}");
            assert_eq!(
                recovery_summary(&direct.recoveries),
                vec![(
                    if introducer_range.is_empty() {
                        RecoveryKind::Missing
                    } else {
                        RecoveryKind::Error
                    },
                    introducer,
                    introducer_range,
                )],
                "slash introducer recovery: {source:?}"
            );
            assert_eq!(
                direct
                    .node_kinds
                    .iter()
                    .filter(|kind| **kind == SyntaxKind::PrefixOperatorUse)
                    .count(),
                1,
                "only the non-comment slash is a Statement operator: {source:?}"
            );
            assert_eq!(direct.emitted, source, "slash losslessness: {source:?}");
            assert!(ast.merged.is_none(), "slash AST sink: {source:?}");
            assert_eq!(
                expected_local_after(&ast.sequence.before, source, "", 0, 0),
                ast.sequence.after,
                "slash AST state: {source:?}"
            );
            assert_eq!(
                expected_local_after(&direct.before, source, "", 1, 0),
                direct.after,
                "slash direct state: {source:?}"
            );
        }

        for source in ["withx: item", "within {item}", "item"] {
            let ast = run_gate3_ast(source, 0);
            let (range, direct) = run_gate3_direct(source, 0);
            assert!(!ast.accepted, "rejected exact word: {source:?}");
            assert!(range.is_none(), "direct rejection: {source:?}");
            assert_eq!(ast.sequence.remainder, source, "AST rollback: {source:?}");
            assert_eq!(direct.remainder, source, "direct rollback: {source:?}");
            assert_eq!(
                ast.sequence.before, ast.sequence.after,
                "AST state rollback"
            );
            assert_eq!(direct.before, direct.after, "direct state rollback");
            assert!(
                direct.child_kinds.is_empty(),
                "no rejected CST node: {source:?}"
            );
            assert!(
                direct.recoveries.is_empty(),
                "no rejected recovery: {source:?}"
            );
            assert!(ast.merged.is_none(), "AST rejection sink: {source:?}");
            assert!(direct.sink_clean, "direct rejection sink: {source:?}");
        }

        let (_, empty) = run_gate3_direct("with {}tail", 0);
        assert_eq!(
            empty.node_kinds,
            vec![SyntaxKind::Root, SyntaxKind::DeclarationCompanion]
        );
        assert_eq!(
            empty.tokens,
            vec![
                (SyntaxKind::WithKw, 0..4, "with".to_owned()),
                (SyntaxKind::Whitespace, 4..5, " ".to_owned()),
                (SyntaxKind::LBrace, 5..6, "{".to_owned()),
                (SyntaxKind::RBrace, 6..7, "}".to_owned()),
            ]
        );

        let (_, indented) = run_gate3_direct("with:\n  first\n  second\nouter", 0);
        assert_eq!(
            indented.node_kinds,
            vec![
                SyntaxKind::Root,
                SyntaxKind::DeclarationCompanion,
                SyntaxKind::DeclarationCompanionIndentedBody,
                SyntaxKind::Statement,
                SyntaxKind::OperatorChain,
                SyntaxKind::IdentifierExpression,
                SyntaxKind::BlockStatementSeparator,
                SyntaxKind::Statement,
                SyntaxKind::OperatorChain,
                SyntaxKind::IdentifierExpression,
            ]
        );

        let (_, absent_indented) = run_gate3_direct("with:\n  ]tail", 0);
        assert_eq!(
            absent_indented.node_kinds,
            vec![
                SyntaxKind::Root,
                SyntaxKind::DeclarationCompanion,
                SyntaxKind::Missing,
            ],
            "the absent deeper first slot never opens an indented body"
        );
        assert_eq!(
            absent_indented.tokens,
            vec![
                (SyntaxKind::WithKw, 0..4, "with".to_owned()),
                (SyntaxKind::Colon, 4..5, ":".to_owned()),
            ],
            "the rejected deeper trivia and caller close remain outside the companion"
        );

        let (_, line_comment) = run_gate3_direct("with @// : { item\n: item", 0);
        assert_eq!(
            line_comment.node_kinds,
            vec![
                SyntaxKind::Root,
                SyntaxKind::DeclarationCompanion,
                SyntaxKind::Error,
            ]
        );
        assert_eq!(
            line_comment.tokens,
            vec![
                (SyntaxKind::WithKw, 0..4, "with".to_owned()),
                (SyntaxKind::Whitespace, 4..5, " ".to_owned()),
                (SyntaxKind::Unknown, 5..17, "@// : { item".to_owned(),),
            ],
            "the line comment is one introducer-retry unit and its newline is retained"
        );

        let nested_source = "with @/* outer : { ) ] item /* nested */ */: item";
        let (_, nested_comment) = run_gate3_direct(nested_source, 0);
        assert_eq!(
            nested_comment.node_kinds,
            vec![
                SyntaxKind::Root,
                SyntaxKind::DeclarationCompanion,
                SyntaxKind::Error,
                SyntaxKind::Statement,
                SyntaxKind::OperatorChain,
                SyntaxKind::IdentifierExpression,
            ]
        );
        assert_eq!(
            nested_comment.tokens,
            vec![
                (SyntaxKind::WithKw, 0..4, "with".to_owned()),
                (SyntaxKind::Whitespace, 4..5, " ".to_owned()),
                (SyntaxKind::Unknown, 5..43, nested_source[5..43].to_owned(),),
                (SyntaxKind::Colon, 43..44, ":".to_owned()),
                (SyntaxKind::Whitespace, 44..45, " ".to_owned()),
                (SyntaxKind::Identifier, 45..49, "item".to_owned()),
            ],
            "nested comment contents never become introducer decisions"
        );

        let (_, inline_shell) = run_gate3_direct("with: item;tail", 0);
        assert_eq!(
            inline_shell.first_child_kinds,
            vec![SyntaxKind::Statement],
            "the inline item is a direct companion child"
        );
        assert_eq!(
            inline_shell.node_kinds,
            vec![
                SyntaxKind::Root,
                SyntaxKind::DeclarationCompanion,
                SyntaxKind::Statement,
                SyntaxKind::OperatorChain,
                SyntaxKind::IdentifierExpression,
            ],
            "exact inline companion descendant order"
        );

        let (_, braced_shell) = run_gate3_direct("with { first, second }tail", 0);
        assert_eq!(
            braced_shell.first_child_kinds,
            vec![
                SyntaxKind::Statement,
                SyntaxKind::BlockStatementSeparator,
                SyntaxKind::Statement,
            ],
            "braced items and their canonical separator are direct companion children"
        );
        assert_eq!(
            braced_shell.node_kinds,
            vec![
                SyntaxKind::Root,
                SyntaxKind::DeclarationCompanion,
                SyntaxKind::Statement,
                SyntaxKind::OperatorChain,
                SyntaxKind::IdentifierExpression,
                SyntaxKind::BlockStatementSeparator,
                SyntaxKind::Statement,
                SyntaxKind::OperatorChain,
                SyntaxKind::IdentifierExpression,
            ],
            "exact nonempty braced companion descendant order"
        );

        let (_, introducer_boundary) = run_gate3_direct("with]tail", 0);
        assert_eq!(introducer_boundary.remainder, "]tail");
        assert_eq!(
            introducer_boundary.node_kinds,
            vec![
                SyntaxKind::Root,
                SyntaxKind::DeclarationCompanion,
                SyntaxKind::Missing,
            ]
        );
        assert_eq!(
            introducer_boundary.tokens,
            vec![(SyntaxKind::WithKw, 0..4, "with".to_owned())],
            "the introducer-level outer close remains caller-owned"
        );

        let malformed_inline_source = "with: @ ;tail";
        let (_, malformed_inline) = run_gate3_direct(malformed_inline_source, 0);
        assert_eq!(malformed_inline.remainder, ";tail");
        assert_eq!(
            recovery_summary(&malformed_inline.recoveries),
            vec![(RecoveryKind::Error, body, 6..8)],
            "one inline Body recovery before the retained semicolon"
        );
        assert_eq!(
            malformed_inline.node_kinds,
            vec![
                SyntaxKind::Root,
                SyntaxKind::DeclarationCompanion,
                SyntaxKind::Statement,
                SyntaxKind::Error,
            ]
        );
        assert_eq!(
            malformed_inline.tokens,
            vec![
                (SyntaxKind::WithKw, 0..4, "with".to_owned()),
                (SyntaxKind::Colon, 4..5, ":".to_owned()),
                (SyntaxKind::Whitespace, 5..6, " ".to_owned()),
                (SyntaxKind::Unknown, 6..8, "@ ".to_owned()),
            ],
            "the outer semicolon has no companion token"
        );
        assert_eq!(
            format!("{}{}", malformed_inline.emitted, malformed_inline.remainder),
            malformed_inline_source
        );

        let control_source = "first }tail";
        let (control_remainder, control_merged, control_debug) =
            run_gate3_canonical_sink_control(control_source, false);
        assert_eq!(control_remainder, " }tail");
        assert!(control_merged.is_none(), "rejected close candidate sink");
        assert_eq!(
            control_debug,
            "LatestSink { range: None, errors: [], group_start: 0, undo: [], base_index: 0 }",
            "exact empty sink after rejected close candidate"
        );

        let (preseed_false_remainder, preseed_false_merged, preseed_false_debug) =
            run_gate3_canonical_sink_control(control_source, true);
        assert_eq!(preseed_false_remainder, " }tail");
        assert_eq!(
            preseed_false_merged,
            Some(gate3_candidate_preseed_summary()),
            "rejected candidate preserves incoming sink entries and order"
        );
        assert!(
            preseed_false_debug.contains("range: Some(0..1)"),
            "rejected candidate preserves the incoming sink range"
        );

        let (preseed_true_remainder, preseed_true_merged, preseed_true_debug) =
            run_gate3_canonical_sink_control("first second }tail", true);
        assert_eq!(preseed_true_remainder, " }tail");
        assert_eq!(
            preseed_true_merged,
            Some(gate3_candidate_preseed_summary()),
            "accepted candidate preserves incoming sink entries and order"
        );
        assert!(
            preseed_true_debug.contains("range: Some(0..1)"),
            "accepted candidate preserves the incoming sink range"
        );

        let gate3_sink = run_gate3_ast("with { first }tail", 0);
        let (_, gate3_sink_direct) = run_gate3_direct("with { first }tail", 0);
        assert_eq!(gate3_sink.sequence.remainder, "tail");
        assert_eq!(gate3_sink.merged, control_merged);
        assert_eq!(
            gate3_sink.latest_sink_debug,
            "LatestSink { range: None, errors: [], group_start: 0, undo: [], base_index: 0 }",
            "isolated Gate3 AST has an exact empty sink"
        );
        assert_eq!(gate3_sink_direct.remainder, "tail");
        assert!(gate3_sink_direct.sink_clean);
        assert!(gate3_sink_direct.recoveries.is_empty());
        assert_eq!(gate3_sink_direct.statement_count, 1);
        assert_eq!(
            format!(
                "{}{}",
                gate3_sink_direct.emitted, gate3_sink_direct.remainder
            ),
            "with { first }tail",
            "the sink fix does not change direct CST or remainder"
        );
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    enum Gate4ItemSummary {
        Statement,
        Derives { clauses: usize, roles: Vec<usize> },
        Incomplete,
    }

    fn gate4_item_summary(item: &Recovered<DeclarationCompanionItem<'_>>) -> Gate4ItemSummary {
        match item {
            Recovered::Complete(DeclarationCompanionItem::Statement(_)) => {
                Gate4ItemSummary::Statement
            }
            Recovered::Complete(DeclarationCompanionItem::Derives(clauses)) => {
                Gate4ItemSummary::Derives {
                    clauses: clauses.len(),
                    roles: clauses.iter().map(|clause| clause.roles.len()).collect(),
                }
            }
            Recovered::Incomplete => Gate4ItemSummary::Incomplete,
        }
    }

    fn gate4_companion_items(companion: &DeclarationCompanion<'_>) -> Vec<Gate4ItemSummary> {
        match &companion.form {
            DeclarationCompanionForm::Colon {
                body: Recovered::Complete(DeclarationCompanionColonBody::Inline { item, .. }),
                ..
            } => vec![gate4_item_summary(&Recovered::Complete((**item).clone()))],
            DeclarationCompanionForm::Colon {
                body: Recovered::Complete(DeclarationCompanionColonBody::Indented(body)),
                ..
            } => body.items.iter().map(gate4_item_summary).collect(),
            DeclarationCompanionForm::Braced { items, .. } => {
                items.iter().map(gate4_item_summary).collect()
            }
            DeclarationCompanionForm::Colon {
                body: Recovered::Incomplete,
                ..
            } => Vec::new(),
        }
    }

    fn run_gate4_ast(source: &str, base_indent: usize) -> (Vec<Gate4ItemSummary>, AstOutcome) {
        let table = OperatorTable::empty();
        let mut input = SourceInput::new(source);
        let mut local = seeded_gate3_test_local();
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let companion = parse_declaration_companion_isolated(&table, base_indent, &mut i)
            .expect("the focused Gate 4 source starts with an isolated companion");
        let items = gate4_companion_items(&companion);
        let remainder = i.input.remainder().to_owned();
        drop(i);
        (
            items,
            AstOutcome {
                complete: Vec::new(),
                remainder,
                before,
                after: local.value_snapshot(),
                sink_clean: sink.take_merged().is_none(),
                cut,
            },
        )
    }

    #[test]
    fn gate4_companion_derives_priority_recovery_and_layout_table() {
        let derives_role =
            GrammarRole::Declaration(DeclarationRole::Derives(DerivesRole::RoleReference));
        let via_role = GrammarRole::Declaration(DeclarationRole::Derives(DerivesRole::ViaTarget));
        let type_primary = GrammarRole::Type(crate::session::TypeRole::Primary);
        for (
            source,
            base_indent,
            expected_items,
            remainder,
            statement_count,
            derives_count,
            recoveries,
        ) in [
            (
                "with: derives Eq",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 1,
                    roles: vec![1],
                }],
                "",
                0,
                1,
                vec![],
            ),
            (
                "with: derives Eq derives Ord",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 2,
                    roles: vec![1, 1],
                }],
                "",
                0,
                2,
                vec![],
            ),
            (
                "with: derives Eq via key derives Ord",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 2,
                    roles: vec![1, 1],
                }],
                "",
                0,
                2,
                vec![],
            ),
            (
                "with { derives Eq derives Ord }tail",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 2,
                    roles: vec![1, 1],
                }],
                "tail",
                0,
                2,
                vec![],
            ),
            (
                "with:\n  derives Eq derives Ord\nouter",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 2,
                    roles: vec![1, 1],
                }],
                "\nouter",
                0,
                2,
                vec![],
            ),
            (
                "with { derives Eq; value }tail",
                0,
                vec![
                    Gate4ItemSummary::Derives {
                        clauses: 1,
                        roles: vec![1],
                    },
                    Gate4ItemSummary::Statement,
                ],
                "tail",
                1,
                1,
                vec![],
            ),
            (
                "with { derives Eq; derives Ord }tail",
                0,
                vec![
                    Gate4ItemSummary::Derives {
                        clauses: 1,
                        roles: vec![1],
                    },
                    Gate4ItemSummary::Derives {
                        clauses: 1,
                        roles: vec![1],
                    },
                ],
                "tail",
                0,
                2,
                vec![],
            ),
            (
                "with { derives Eq\nderives Ord }tail",
                0,
                vec![
                    Gate4ItemSummary::Derives {
                        clauses: 1,
                        roles: vec![1],
                    },
                    Gate4ItemSummary::Derives {
                        clauses: 1,
                        roles: vec![1],
                    },
                ],
                "tail",
                0,
                2,
                vec![],
            ),
            (
                "with:\n  derives Eq\n  derives Ord\nouter",
                0,
                vec![
                    Gate4ItemSummary::Derives {
                        clauses: 1,
                        roles: vec![1],
                    },
                    Gate4ItemSummary::Derives {
                        clauses: 1,
                        roles: vec![1],
                    },
                ],
                "\nouter",
                0,
                2,
                vec![],
            ),
            (
                "with: derives (Eq, Ord), Debug via key",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 1,
                    roles: vec![2],
                }],
                "",
                0,
                1,
                vec![],
            ),
            (
                "with: derivesx",
                0,
                vec![Gate4ItemSummary::Statement],
                "",
                1,
                0,
                vec![],
            ),
            (
                "with: within",
                0,
                vec![Gate4ItemSummary::Statement],
                "",
                1,
                0,
                vec![],
            ),
            (
                "with: derives;tail",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 1,
                    roles: vec![1],
                }],
                "tail",
                0,
                1,
                vec![(RecoveryKind::Missing, derives_role, 13..13)],
            ),
            (
                "with: derives @ Eq;tail",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 1,
                    roles: vec![1],
                }],
                "tail",
                0,
                1,
                vec![(RecoveryKind::Error, type_primary, 14..16)],
            ),
            (
                "with: derives Eq via ;tail",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 1,
                    roles: vec![1],
                }],
                "tail",
                0,
                1,
                vec![(RecoveryKind::Missing, via_role, 21..21)],
            ),
            (
                "with: derives Eq via @ key;tail",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 1,
                    roles: vec![1],
                }],
                "tail",
                0,
                1,
                vec![(RecoveryKind::Error, via_role, 21..23)],
            ),
            (
                "with: derives Eq]tail",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 1,
                    roles: vec![1],
                }],
                "]tail",
                0,
                1,
                vec![],
            ),
            (
                "with { derives Eq }tail",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 1,
                    roles: vec![1],
                }],
                "tail",
                0,
                1,
                vec![],
            ),
            (
                "with { derives Eq, }tail",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 1,
                    roles: vec![2],
                }],
                "tail",
                0,
                1,
                vec![(RecoveryKind::Missing, derives_role, 19..19)],
            ),
            (
                "with:\n  derives Eq\nelse tail",
                0,
                vec![Gate4ItemSummary::Derives {
                    clauses: 1,
                    roles: vec![1],
                }],
                "\nelse tail",
                0,
                1,
                vec![],
            ),
        ] {
            let (items, ast) = run_gate4_ast(source, base_indent);
            let (_, direct) = run_gate3_direct(source, base_indent);
            assert_eq!(items, expected_items, "AST item priority/run: {source:?}");
            assert_eq!(ast.remainder, remainder, "AST remainder: {source:?}");
            assert_eq!(direct.remainder, remainder, "direct remainder: {source:?}");
            assert_eq!(
                direct.statement_count, statement_count,
                "Statement wrappers: {source:?}"
            );
            assert_eq!(
                direct
                    .node_kinds
                    .iter()
                    .filter(|&&kind| kind == SyntaxKind::DerivesClause)
                    .count(),
                derives_count,
                "direct DerivesClause count: {source:?}"
            );
            assert_eq!(
                recovery_summary(&direct.recoveries),
                recoveries,
                "typed derives recovery: {source:?}"
            );
            assert!(
                direct.recoveries.iter().all(|record| {
                    !matches!(
                        record.site.role,
                        GrammarRole::Declaration(DeclarationRole::Companion(
                            DeclarationCompanionRole::Item | DeclarationCompanionRole::IndentedItem
                        ))
                    )
                }),
                "inner Derives recovery suppresses outer Item recovery: {source:?}"
            );
            assert_eq!(
                format!("{}{}", direct.emitted, direct.remainder),
                source,
                "lossless prefix plus retained boundary: {source:?}"
            );
            assert_full_local_parity_with_semantic_delta(source, &ast, &direct, 0);
            assert!(!ast.cut && !direct.cut, "Gate 4 does not cut: {source:?}");
        }

        for (source, expected_parent) in [
            ("with: derives Eq", SyntaxKind::DeclarationCompanion),
            (
                "with:\n  derives Eq\nouter",
                SyntaxKind::DeclarationCompanionIndentedBody,
            ),
            ("with { derives Eq }tail", SyntaxKind::DeclarationCompanion),
        ] {
            let (_, direct) = run_gate3_direct(source, 0);
            assert_eq!(
                direct.derives_parent_kinds,
                vec![expected_parent],
                "DerivesClause has the exact companion/body parent: {source:?}"
            );
            assert!(
                !direct.node_kinds.contains(&SyntaxKind::Statement),
                "a companion Derives run has no Statement wrapper: {source:?}"
            );
        }

        let (_, via_gap) = run_gate3_direct("with: derives Eq via ;tail", 0);
        assert!(
            via_gap
                .tokens
                .contains(&(SyntaxKind::Whitespace, 20..21, " ".to_owned(),)),
            "mandatory ViaTarget owns same-line horizontal trivia"
        );
        assert!(
            via_gap
                .tokens
                .contains(&(SyntaxKind::Semicolon, 21..22, ";".to_owned())),
            "the inline companion owns the terminal semicolon after Missing ViaTarget"
        );

        let (_, comma_close) = run_gate3_direct("with { derives Eq, }tail", 0);
        assert!(
            comma_close
                .tokens
                .contains(&(SyntaxKind::Whitespace, 18..19, " ".to_owned(),)),
            "mandatory RoleReference owns same-line horizontal trivia"
        );
        assert!(
            comma_close
                .tokens
                .contains(&(SyntaxKind::RBrace, 19..20, "}".to_owned())),
            "the companion close remains owned by the braced form"
        );

        let ambient_attachment_source = "  else";
        let ambient_attachment_spec = DerivesDriverSpec::new(
            DerivesAttachmentOwner::Type,
            DerivesAttachmentPosition::Header,
            0,
        );
        let mut ambient_attachment_input = SourceInput::new(ambient_attachment_source);
        let mut ambient_attachment_local = seeded_gate3_test_local();
        let mut ambient_attachment_sink = chasa::LatestSink::new();
        let mut ambient_attachment_cut = false;
        let mut ambient_attachment = In::new(
            &mut ambient_attachment_input,
            &mut ambient_attachment_sink,
            IsCut::new(&mut ambient_attachment_cut),
        )
        .set_local(&mut ambient_attachment_local);
        assert!(any_ambient_owner_claims(&mut ambient_attachment));
        consume_derives_role_trivia(ambient_attachment_spec, &mut ambient_attachment);
        assert_eq!(
            ambient_attachment.input.remainder(),
            "else",
            "attachment RoleRef historically consumes horizontal trivia despite ambient evidence"
        );

        let mut direct_ambient_input = SourceInput::new(ambient_attachment_source);
        let mut direct_ambient_local = seeded_gate3_test_local();
        let mut direct_ambient_sink = chasa::LatestSink::new();
        let mut direct_ambient_cut = false;
        let direct_ambient_input = In::new(
            &mut direct_ambient_input,
            &mut direct_ambient_sink,
            IsCut::new(&mut direct_ambient_cut),
        )
        .set_local(&mut direct_ambient_local);
        let direct_ambient_probe = Probe::new(direct_ambient_input);
        let mut direct_ambient =
            direct_ambient_probe.commit(FullCstOutput::new(ambient_attachment_source));
        assert!(direct_ambient.probe(|probe| any_ambient_owner_claims(probe.input())));
        commit_derives_role_trivia(ambient_attachment_spec, &mut direct_ambient);
        assert_eq!(
            direct_ambient.probe(|probe| probe.input().input.remainder()),
            "else",
            "direct attachment RoleRef preserves the historical horizontal-trivia ownership"
        );

        let attachment_source = " derives Eq = Tail";
        let mut attachment_input = SourceInput::new(attachment_source);
        let mut attachment_local = ParseLocal::new();
        let mut attachment_sink = chasa::LatestSink::new();
        let mut attachment_cut = false;
        let mut attachment = In::new(
            &mut attachment_input,
            &mut attachment_sink,
            IsCut::new(&mut attachment_cut),
        )
        .set_local(&mut attachment_local);
        let start = recognize_derives_attachment_start(
            DerivesAttachmentOwner::Type,
            DerivesAttachmentPosition::Header,
            0,
            &mut attachment,
        )
        .expect("the existing Type attachment control recognizes derives");
        let attachments = parse_derives_attachments_isolated(start, &mut attachment);
        assert_eq!(attachments.len(), 1);
        assert_eq!(attachments[0].position, DerivesAttachmentPosition::Header);
        assert_eq!(attachment.input.remainder(), " = Tail");
        assert!(attachment_sink.take_merged().is_none());

        let mut direct_attachment_input = SourceInput::new(attachment_source);
        let mut direct_attachment_local = ParseLocal::new();
        let mut direct_attachment_sink = chasa::LatestSink::new();
        let mut direct_attachment_cut = false;
        let direct_attachment_input = In::new(
            &mut direct_attachment_input,
            &mut direct_attachment_sink,
            IsCut::new(&mut direct_attachment_cut),
        )
        .set_local(&mut direct_attachment_local);
        let direct_attachment_probe = Probe::new(direct_attachment_input);
        let mut direct_attachment =
            direct_attachment_probe.commit(FullCstOutput::new(attachment_source));
        let direct_start = direct_attachment
            .probe(|probe| {
                recognize_derives_attachment_start(
                    DerivesAttachmentOwner::Type,
                    DerivesAttachmentPosition::Header,
                    0,
                    probe.input(),
                )
            })
            .expect("the existing direct Type attachment control recognizes derives");
        let direct_attachments =
            commit_derives_attachments_isolated(direct_start, &mut direct_attachment);
        assert_eq!(direct_attachments.len(), 1);
        assert_eq!(
            direct_attachments[0].position,
            DerivesAttachmentPosition::Header
        );
        assert_eq!(
            direct_attachment.probe(|probe| probe.input().input.remainder()),
            " = Tail"
        );
        drop(direct_attachment);
        assert!(direct_attachment_sink.take_merged().is_none());

        reset_canonical_statement_candidate_input_calls();
        let _ = run_gate4_ast("with: derives Eq derives Ord", 0);
        assert_eq!(
            canonical_statement_candidate_input_calls(),
            0,
            "valid companion Derives never probes canonical Statement recovery"
        );
        reset_canonical_statement_candidate_input_calls();
        let _ = run_gate3_direct("with: derives Eq derives Ord", 0);
        assert_eq!(
            canonical_statement_candidate_input_calls(),
            0,
            "direct companion Derives never probes canonical Statement recovery"
        );
    }

    fn synthetic_repeated_source(items: usize, item: &str, separator: char) -> String {
        let capacity = item
            .len()
            .checked_mul(items)
            .and_then(|bytes| {
                separator
                    .len_utf8()
                    .checked_mul(items.saturating_sub(1))
                    .and_then(|separator_bytes| bytes.checked_add(separator_bytes))
            })
            .expect("synthetic Gate 2 source length fits usize");
        let mut source = String::with_capacity(capacity);
        for index in 0..items {
            if index > 0 {
                source.push(separator);
            }
            source.push_str(item);
        }
        assert_eq!(source.len(), capacity);
        source
    }

    fn synthetic_indented_source(items: usize) -> String {
        synthetic_repeated_source(items, "item", '\n')
    }

    fn synthetic_braced_source(items: usize) -> String {
        synthetic_repeated_source(items, "item", ',')
    }

    fn timed_indented_ast<'source>(
        table: &OperatorTable,
        source: &'source str,
    ) -> (Vec<Recovered<DeclarationCompanionItem<'source>>>, usize) {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let parsed = parse_indented_declaration_companion_statement_items(table, 0, &mut i);
        let remainder = i.input.remainder().len();
        (parsed, remainder)
    }

    fn timed_braced_ast<'source>(
        table: &OperatorTable,
        source: &'source str,
    ) -> (Vec<Recovered<DeclarationCompanionItem<'source>>>, usize) {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        enter_test_braced_owner_scope(&mut local);
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let parsed = parse_braced_declaration_companion_statement_items(table, &mut i);
        let remainder = i.input.remainder().len();
        (parsed, remainder)
    }

    fn timed_indented_direct<'source>(
        table: &OperatorTable,
        source: &'source str,
    ) -> (FullCstOutput<'source>, usize) {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let probe = Probe::new(i);
        let mut committed = probe.commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_indented_declaration_companion_statement_items(table, 0, &mut committed);
        let remainder = committed.probe(|probe| probe.input().input.remainder().len());
        committed.finish_node();
        let output = committed.into_output();
        (output, remainder)
    }

    fn timed_braced_direct<'source>(
        table: &OperatorTable,
        source: &'source str,
    ) -> (FullCstOutput<'source>, usize) {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        enter_test_braced_owner_scope(&mut local);
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let probe = Probe::new(i);
        let mut committed = probe.commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_braced_declaration_companion_statement_items(table, &mut committed);
        let remainder = committed.probe(|probe| probe.input().input.remainder().len());
        committed.finish_node();
        let output = committed.into_output();
        (output, remainder)
    }

    #[test]
    fn gate2_companion_sequence_table() {
        gate2_indented_statement_only_companion_recovery_and_boundaries_match();
        gate2_braced_statement_only_companion_recovery_and_transitions_match();
        gate2_statement_only_companion_keeps_ast_direct_cardinality_and_stack_state();
        gate2_comment_aware_recovery_is_atomic_and_ast_direct_exact();
        gate2_comment_openers_precede_slash_statement_candidates();
        gate2_if_retry_allocates_one_identity_only_after_candidate_probe();
        gate2_every_canonical_statement_candidate_family_has_ast_direct_parity();
        gate2_valid_large_sequences_never_call_the_recovery_candidate_helper();
    }

    #[test]
    fn gate3b_declaration_companion_introducer_episode_rollback() {
        let source = "with :: item";
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let floor = local.push_yumark_delimiter(Delimiter::Parenthesis);
        local.push_yumark_frame(YumarkFrame::EmbeddedYulang {
            owner: YumarkOwner::InlineReference,
            outer_kind: YumarkEmbeddedOuterKind::Paired(Delimiter::Parenthesis),
            delimiter_floor: floor,
        });
        let retained_fact = YumarkEmbeddedRecoveryFact {
            spec: RecoverySiteSpec {
                role: GrammarRole::Expression(ExpressionRole::CallArgument),
                expected: ExpectedSyntax::Expression,
            },
            range: 0..0,
            kind: RecoveryKind::Missing,
            unexpected: None,
        };
        local.record_yumark_embedded_recovery(retained_fact.clone());
        let local_before = local.value_snapshot();
        let mut sink: chasa::LatestSink<usize, StdErr<char>> = chasa::LatestSink::new();
        <chasa::LatestSink<usize, StdErr<char>> as ErrorSink<usize>>::push(
            &mut sink,
            11..12,
            StdErr::Expected(Expected::new(98, "preseeded-companion", ())),
        );
        let sink_before = format!("{sink:?}");
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        assert!(!committed.probe(|probe| {
            probe_rejected_declaration_companion_introducer_episode_for_test(
                &OperatorTable::empty(),
                0,
                probe.input(),
            )
        }));
        let (position, remainder, local_after, retained) = committed.probe(|probe| {
            let i = probe.input();
            (
                i.pos(),
                i.input.remainder().to_owned(),
                i.local.value_snapshot(),
                i.local.drain_yumark_embedded_recoveries(),
            )
        });
        committed.finish_node();
        let output = committed.into_output();
        assert_eq!(position, 0);
        assert_eq!(remainder, source);
        assert_eq!(local_after, local_before);
        assert_eq!(retained, vec![retained_fact]);
        assert!(output.committed_recoveries().is_empty());
        let root = SyntaxNode::new_root(output.finish_prefix());
        assert_eq!(root.to_string(), "");
        assert!(root.children().next().is_none());
        assert_eq!(format!("{sink:?}"), sink_before);
        assert_eq!(
            sink.take_merged(),
            Some(StdSummary {
                unexpected: None,
                expected: vec![Expected::new(98, "preseeded-companion", ())],
            }),
        );
        assert!(!cut);
        assert!(matches!(
            local.pop_yumark_frame(),
            Some(YumarkFrame::EmbeddedYulang { .. })
        ));
        local.pop_yumark_delimiter(floor, Delimiter::Parenthesis);
    }

    #[test]
    fn gate3b_declaration_companion_introducer_episode_boundaries() {
        let role = declaration_companion_introducer_role();
        let primary = ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace));
        let auxiliary = ExpectedSyntax::Punctuation(PunctuationEvidence::Colon);
        let entry_line = LineState {
            last_newline: Some((40, 42)),
            line_start: 42,
            line_indent: 3,
            at_line_start: false,
        };

        for (source, range, remainder, inline) in [
            ("with]tail", 4..4, "]tail", false),
            ("with\nnext", 4..4, "\nnext", false),
            ("with item", 5..5, "", true),
        ] {
            let mut ast_input = SourceInput::new(source);
            let mut ast_local = ParseLocal::new();
            ast_local.set_line(entry_line);
            let ast_floor = ast_local.push_yumark_delimiter(Delimiter::Parenthesis);
            ast_local.push_yumark_frame(YumarkFrame::EmbeddedYulang {
                owner: YumarkOwner::InlineReference,
                outer_kind: YumarkEmbeddedOuterKind::Paired(Delimiter::Parenthesis),
                delimiter_floor: ast_floor,
            });
            let mut ast_sink = chasa::LatestSink::new();
            let mut ast_cut = false;
            let mut i = In::new(&mut ast_input, &mut ast_sink, IsCut::new(&mut ast_cut))
                .set_local(&mut ast_local);
            let companion = parse_declaration_companion_isolated(
                &OperatorTable::empty(),
                entry_line.line_indent,
                &mut i,
            )
            .expect("the D12a private source starts with a companion");
            let ast_range = companion.range.clone();
            assert_eq!(ast_range, 0..source.len() - remainder.len());
            assert_eq!(i.input.remainder(), remainder);
            assert_eq!(i.local.line(), entry_line, "AST line: {source:?}");
            if inline {
                assert!(matches!(
                    companion.form,
                    DeclarationCompanionForm::Colon {
                        body: Recovered::Complete(DeclarationCompanionColonBody::Inline {
                            item,
                            ..
                        }),
                        ..
                    } if matches!(*item, DeclarationCompanionItem::Statement(_))
                ));
            } else {
                assert!(matches!(
                    companion.form,
                    DeclarationCompanionForm::Colon {
                        colon: Recovered::Incomplete,
                        body: Recovered::Incomplete,
                    }
                ));
            }
            let facts = i.local.drain_yumark_embedded_recoveries();
            assert_eq!(
                facts,
                vec![YumarkEmbeddedRecoveryFact {
                    spec: RecoverySiteSpec {
                        role,
                        expected: primary,
                    },
                    range: range.clone(),
                    kind: RecoveryKind::Missing,
                    unexpected: None,
                }],
                "AST D12a fact: {source:?}",
            );
            assert_eq!(i.local.yumark_frame_depth(), 1);
            drop(i);
            assert!(ast_sink.take_merged().is_none(), "AST sink: {source:?}");
            assert!(matches!(
                ast_local.pop_yumark_frame(),
                Some(YumarkFrame::EmbeddedYulang { .. })
            ));
            ast_local.pop_yumark_delimiter(ast_floor, Delimiter::Parenthesis);

            let mut direct_input = SourceInput::new(source);
            let mut direct_local = ParseLocal::new();
            direct_local.set_line(entry_line);
            let direct_floor = direct_local.push_yumark_delimiter(Delimiter::Parenthesis);
            direct_local.push_yumark_frame(YumarkFrame::EmbeddedYulang {
                owner: YumarkOwner::InlineReference,
                outer_kind: YumarkEmbeddedOuterKind::Paired(Delimiter::Parenthesis),
                delimiter_floor: direct_floor,
            });
            let before_id = direct_local.value_snapshot().next_diagnostic_id;
            let mut direct_sink = chasa::LatestSink::new();
            let mut direct_cut = false;
            let i = In::new(
                &mut direct_input,
                &mut direct_sink,
                IsCut::new(&mut direct_cut),
            )
            .set_local(&mut direct_local);
            let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
            committed.start_node(SyntaxKind::Root);
            let direct_range = commit_declaration_companion_isolated(
                &OperatorTable::empty(),
                entry_line.line_indent,
                &mut committed,
            )
            .expect("the direct D12a private source starts with a companion");
            let direct_remainder =
                committed.probe(|probe| probe.input().input.remainder().to_owned());
            let direct_line = committed.probe(|probe| probe.input().local.line());
            let direct_frames = committed.probe(|probe| probe.input().local.yumark_frame_depth());
            committed.finish_node();
            let output = committed.into_output();
            assert_eq!(direct_range, ast_range);
            assert_eq!(direct_remainder, remainder);
            assert_eq!(direct_line, entry_line, "direct line: {source:?}");
            assert_eq!(direct_frames, 1);
            let [record] = output.committed_recoveries() else {
                panic!("one private D12a direct record: {source:?}");
            };
            assert_eq!(record.id.0, before_id);
            assert_eq!(record.site.role, role);
            assert_eq!(record.site.range, range.clone());
            assert_eq!(record.kind, RecoveryKind::Missing);
            assert!(record.unexpected.is_empty());
            assert_eq!(record.primary_expectation, 0);
            assert_eq!(
                record
                    .expectations
                    .iter()
                    .map(|expectation| expectation.expected)
                    .collect::<Vec<_>>(),
                vec![primary, auxiliary],
            );
            let root = SyntaxNode::new_root(output.finish_prefix());
            assert_eq!(
                format!("{}{}", root, direct_remainder),
                source,
                "direct lossless: {source:?}",
            );
            let generic = root
                .descendants()
                .filter(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
                .collect::<Vec<_>>();
            let [node] = generic.as_slice() else {
                panic!("one private D12a generic node: {source:?}");
            };
            assert_eq!(node.kind(), SyntaxKind::Missing);
            assert_eq!(
                usize::from(node.text_range().start())..usize::from(node.text_range().end()),
                range,
            );
            assert_eq!(
                node.parent().map(|parent| parent.kind()),
                Some(SyntaxKind::DeclarationCompanion),
            );
            if inline {
                let companion = root
                    .descendants()
                    .find(|node| node.kind() == SyntaxKind::DeclarationCompanion)
                    .expect("private direct companion node");
                assert!(companion.descendants_with_tokens().any(|element| {
                    element.into_token().is_some_and(|token| {
                        token.kind() == SyntaxKind::Identifier && token.text() == "item"
                    })
                }));
            }
            assert!(
                direct_sink.take_merged().is_none(),
                "direct sink: {source:?}",
            );
            assert!(matches!(
                direct_local.pop_yumark_frame(),
                Some(YumarkFrame::EmbeddedYulang { .. })
            ));
            direct_local.pop_yumark_delimiter(direct_floor, Delimiter::Parenthesis);
        }
    }

    #[test]
    fn gate3b_ordinary_primary_control_declaration_companion() {
        let introducer = declaration_companion_introducer_role();
        let body = declaration_companion_body_role();
        let separator = declaration_companion_separator_role();
        let close = declaration_companion_close_role();

        for (source, kind, role, range, expected) in [
            (
                "with",
                RecoveryKind::Missing,
                introducer,
                4..4,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
            ),
            (
                "with:",
                RecoveryKind::Missing,
                body,
                5..5,
                ExpectedSyntax::Statement,
            ),
            (
                "with: @",
                RecoveryKind::Error,
                body,
                6..7,
                ExpectedSyntax::Statement,
            ),
            (
                "with:\n  ",
                RecoveryKind::Missing,
                body,
                5..5,
                ExpectedSyntax::Statement,
            ),
            (
                "with { enum E {} type T = Int }",
                RecoveryKind::Missing,
                separator,
                17..17,
                ExpectedSyntax::StatementSeparator,
            ),
            (
                "with { a",
                RecoveryKind::Missing,
                close,
                8..8,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
            ),
        ] {
            let (_, direct) = run_gate3_direct(source, 0);
            let record = direct
                .recoveries
                .iter()
                .find(|record| {
                    record.kind == kind && record.site.role == role && record.site.range == range
                })
                .unwrap_or_else(|| {
                    panic!(
                        "missing ordinary recovery tuple for {source:?}: {:#?}",
                        direct.recoveries
                    )
                });
            assert_eq!(
                record.expectations[record.primary_expectation].expected, expected,
                "primary expectation: {source:?}",
            );
        }
    }
}
