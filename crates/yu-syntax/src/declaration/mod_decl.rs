//! Direct canonical `mod` declaration construction.

use crate::ambient_claim::AmbientClaimContext;
use crate::cst_output::RecoveryDraft;
use crate::recovery_record::{
    DeclarationRole, Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole, ModRole,
    PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
    UnexpectedSyntax,
};
use reborrow_generic::Reborrow as _;
use std::sync::Arc;

use crate::syntax_kind::SyntaxKind;

use crate::{
    cst_output::emit::{
        emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
    },
    cursor::{LexIn, SyntaxIn},
    handoff::{Either, NormalizedExit, complete, handoff},
    lexical::{
        current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
        item::{Item, LeadingTrivia, TokenKind},
        lexer::{
            introduced_body_indentation_normalized, scan_identifier, scan_statement_payload,
            source_identifier,
        },
        observation::{
            implicit_delimited_newline, indentation_after_newline, is_active_stop, token_kind,
        },
        position::{advanced_origin, suffix_marker},
        stops::Stops,
        trivia::{TriviaObservation, observe_fenced_trivia},
        yumark::FenceBoundary,
    },
    statement::{
        StatementAdmission, StatementLineHandoff, braced_statement_block_normalized,
        canonical_statement_from_admission_normalized, classify_statement_item_normalized,
        indented_statement_block_normalized,
    },
};

pub(crate) fn mod_declaration_selected_lexical(
    source: &str,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item_word(item) == Some("mod") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    prefixed_mod_candidate_normalized(source, item_origin, fence, baseline)
}

fn prefixed_mod_candidate_normalized(
    source: &str,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
) -> bool {
    let TriviaObservation::Visible(observed) =
        observe_fenced_trivia(source, item_origin, LineEntry::InLine, fence)
    else {
        return false;
    };
    observed
        .indentation
        .is_none_or(|indentation| indentation > baseline)
        && source_identifier(observed.source).is_some_and(|(word, _)| word == "mod")
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn mod_declaration_normalized(
    mut i: SyntaxIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::ModDeclaration.into());

    if item_word(&intro) == Some("mod") {
        emit_item_as(&mut i, intro, SyntaxKind::ModKw);
    } else {
        emit_visibility(&mut i, intro);
        let (mut keyword, next_origin, next_entry) = mod_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            false,
        );
        item_origin = next_origin;
        line_entry = next_entry;
        debug_assert!(gmod_allowed(&keyword, baseline));
        debug_assert_eq!(item_word(&keyword), Some("mod"));
        keyword.emit_all_remaining_leading(&mut *i.state);
        emit_item_as(&mut i, keyword, SyntaxKind::ModKw);
    }

    let (first, next_origin, next_entry) = mod_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        true,
    );
    item_origin = next_origin;
    line_entry = next_entry;
    let item = match parse_identity_normalized(
        i.rb(),
        first,
        baseline,
        stops,
        &mut item_origin,
        &mut line_entry,
        fence,
    ) {
        Ok(Some(item)) => item,
        Ok(None) => {
            let (item, next_origin, next_entry) = mod_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                false,
            );
            item_origin = next_origin;
            line_entry = next_entry;
            item
        }
        Err(item) => {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
    };

    let exit = parse_body_item_normalized(
        i.rb(),
        item,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    i.state.finish_node();
    exit
}

/// `Ok(None)` means the accepted name ended at the live suffix. `Ok(Some)`
/// carries an already acquired body starter. `Err` is an unchanged boundary.
#[allow(clippy::too_many_arguments)]
fn parse_identity_normalized(
    mut i: SyntaxIn,
    first: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> Result<Option<Item>, Item> {
    let first_is_test = match required_name_normalized(
        i.rb(),
        first,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
        ModRole::Name,
    )? {
        Ok(is_test) => is_test,
        Err(item) => return Ok(Some(item)),
    };
    if !first_is_test {
        return Ok(None);
    }

    let (second, next_origin, next_entry) = mod_item_normalized(
        i.rb(),
        *item_origin,
        *line_entry,
        fence,
        baseline,
        stops,
        true,
    );
    *item_origin = next_origin;
    *line_entry = next_entry;
    if !second.payload_view().is_boundary()
        && !second.payload_view().is_eof()
        && gmod_allowed(&second, baseline)
        && is_body_starter_item(&second)
    {
        return Ok(Some(second));
    }
    match required_name_normalized(
        i,
        second,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
        ModRole::TestName,
    )? {
        Ok(_) => Ok(None),
        Err(item) => Ok(Some(item)),
    }
}

/// The outer `Err` is a caller boundary; the inner `Err` is a local body
/// starter whose leading has already been emitted.
#[allow(clippy::too_many_arguments)]
fn required_name_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
    role: ModRole,
) -> Result<Result<bool, Item>, Item> {
    if item.payload_view().is_boundary() {
        mod_missing(&mut i, &item, *item_origin, role, false);
        return Err(item);
    }
    if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
        mod_missing(&mut i, &item, *item_origin, role, false);
        return Err(item);
    }
    if name_boundary(i.rb(), &item, baseline, stops) {
        mod_missing(&mut i, &item, *item_origin, role, false);
        return Err(item);
    }
    if !gmod_allowed(&item, baseline) {
        mod_missing(&mut i, &item, *item_origin, role, false);
        return Err(item);
    }
    if is_body_starter_item(&item) {
        item.emit_all_remaining_leading(&mut *i.state);
        mod_missing(&mut i, &item, *item_origin, role, false);
        return Ok(Err(item));
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if item_word(&item).is_some() {
        let is_test = role == ModRole::Name && item_word(&item) == Some("test");
        emit_name(&mut i, item, is_test);
        return Ok(Ok(is_test));
    }

    (item, *item_origin, *line_entry) = mod_error_run(
        i.rb(),
        item,
        role,
        baseline,
        stops,
        *item_origin,
        *line_entry,
        fence,
    );
    if name_boundary(i.rb(), &item, baseline, stops) || !gmod_allowed(&item, baseline) {
        return Err(item);
    }
    if is_body_starter_item(&item) {
        return Ok(Err(item));
    }
    let is_test = role == ModRole::Name && item_word(&item) == Some("test");
    emit_name(&mut i, item, is_test);
    Ok(Ok(is_test))
}

fn emit_name(i: &mut SyntaxIn, item: Item, is_test: bool) {
    if is_test {
        i.state.start_node(SyntaxKind::TestModuleMarker.into());
        emit_item_as(i, item, SyntaxKind::Identifier);
        i.state.finish_node();
    } else {
        emit_item_as(i, item, SyntaxKind::Identifier);
    }
}

#[allow(clippy::too_many_arguments)]
fn parse_body_item_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        mod_missing(&mut i, &item, item_origin, ModRole::BodyIntroducer, false);
        return complete(handoff(item), line_entry);
    }
    if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
        mod_missing(&mut i, &item, item_origin, ModRole::BodyIntroducer, false);
        return complete(handoff(item), line_entry);
    }
    if body_boundary(i.rb(), &item, baseline, stops) || !gmod_allowed(&item, baseline) {
        mod_missing(&mut i, &item, item_origin, ModRole::BodyIntroducer, false);
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    let admission = classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence);
    match token_kind(&item) {
        Some(TokenKind::Semicolon) => {
            emit_token_item(&mut i, item);
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        Some(TokenKind::LBrace) => {
            let entry = suffix_marker(i.rb());
            let exit = braced_statement_block_normalized(
                i.rb(),
                item,
                baseline,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
            let item_origin = advanced_origin(item_origin, entry, i.rb());
            match exit {
                NormalizedExit::Complete(Ok(()), next_entry) => {
                    after_completed_normalized(i, baseline, stops, item_origin, next_entry, fence)
                }
                exit => exit,
            }
        }
        Some(TokenKind::Colon) => {
            emit_token_item(&mut i, item);
            parse_colon_body_normalized(
                i,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        _ if admission.is_some() => {
            mod_missing(&mut i, &item, item_origin, ModRole::BodyIntroducer, true);
            parse_inline_statement_normalized(
                i,
                item,
                admission.expect("guard proved canonical Statement admission"),
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        _ => recover_body_introducer_normalized(
            i,
            item,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn recover_body_introducer_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    (item, item_origin, line_entry) = mod_error_run(
        i.rb(),
        item,
        ModRole::BodyIntroducer,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if body_boundary(i.rb(), &item, baseline, stops) {
        return complete(handoff(item), line_entry);
    }
    if is_body_starter_item(&item) {
        return parse_body_item_normalized(
            i,
            item,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if let Some(admission) =
        classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
    {
        return parse_inline_statement_normalized(
            i,
            item,
            admission,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    unreachable!("Mod introducer run stops at a boundary or retry")
}

#[allow(clippy::too_many_arguments)]
fn parse_colon_body_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    match introduced_body_indentation_normalized(i.rb(), item_origin, fence) {
        Some(indentation) if indentation > baseline => indented_statement_block_normalized(
            i,
            baseline,
            crate::recovery_record::GrammarRole::Declaration(
                crate::recovery_record::DeclarationRole::Mod(
                    crate::recovery_record::ModRole::IndentedStatement,
                ),
            ),
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(_) => {
            let (item, origin, next_entry) = mod_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                false,
            );
            mod_missing(&mut i, &item, origin, ModRole::Body, false);
            complete(handoff(item), next_entry)
        }
        None => {
            let (item, item_origin, line_entry) = mod_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                false,
            );
            parse_inline_body_item_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn parse_inline_body_item_normalized(
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary() || item.payload_view().is_eof() {
        mod_missing(&mut i, &item, item_origin, ModRole::Body, false);
        return complete(handoff(item), line_entry);
    }
    if inline_terminal_semicolon(&item) {
        mod_missing(&mut i, &item, item_origin, ModRole::Body, false);
        emit_token_item(&mut i, item);
        return after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence);
    }
    if mod_boundary(i.rb(), &item, baseline, stops) {
        mod_missing(&mut i, &item, item_origin, ModRole::Body, false);
        return complete(handoff(item), line_entry);
    }
    if let Some(admission) =
        classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
    {
        return parse_inline_statement_normalized(
            i,
            item,
            admission,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }

    recover_inline_body_normalized(
        i,
        item,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn recover_inline_body_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    item.emit_all_remaining_leading(&mut *i.state);
    (item, item_origin, line_entry) = mod_error_run(
        i.rb(),
        item,
        ModRole::Body,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if item.payload_view().is_boundary() || item.payload_view().is_eof() {
        return complete(handoff(item), line_entry);
    }
    if inline_terminal_semicolon(&item) {
        emit_token_item(&mut i, item);
        return after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence);
    }
    if mod_boundary(i.rb(), &item, baseline, stops) {
        return complete(handoff(item), line_entry);
    }
    if let Some(admission) =
        classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
    {
        return parse_inline_statement_normalized(
            i,
            item,
            admission,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    unreachable!("Mod body run stops at a boundary or Statement")
}

#[allow(clippy::too_many_arguments)]
fn parse_inline_statement_normalized(
    mut i: SyntaxIn,
    item: Item,
    admission: StatementAdmission,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let entry = suffix_marker(i.rb());
    let exit = canonical_statement_from_admission_normalized(
        i.rb(),
        item,
        admission,
        baseline,
        stops,
        line_handoff.through_inline_statement(),
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    match exit {
        NormalizedExit::Complete(Ok(()), next_entry) => {
            after_completed_normalized(i, baseline, stops, item_origin, next_entry, fence)
        }
        NormalizedExit::Complete(Err(Either::Left(item)), next_entry)
            if inline_terminal_semicolon(&item) =>
        {
            emit_token_item(&mut i, item);
            after_completed_normalized(i, baseline, stops, item_origin, next_entry, fence)
        }
        exit => exit,
    }
}

fn after_completed_normalized(
    i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, _, line_entry) =
        mod_item_normalized(i, item_origin, line_entry, fence, baseline, stops, false);
    complete(handoff(item), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn mod_item_normalized(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_name: bool,
) -> (Item, usize, LineEntry) {
    i.token(|lex| {
        Some(scan_mod_item(
            lex,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            raw_name,
        ))
    })
    .expect("total Mod scanner")
}

#[allow(clippy::too_many_arguments)]
fn scan_mod_item(
    mut i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_name: bool,
) -> (Item, usize, LineEntry) {
    let entry = i.remainder().len();
    let CurrentItem {
        item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(
                lex,
                item_origin,
                line_entry,
                fence,
                |mut lex, leading, origin, fence, _| {
                    if raw_name {
                        if let Some(name) = lex.token(scan_identifier) {
                            return Some(AcceptedPayload {
                                payload: CurrentPayload::Token(name),
                                next_line_entry: LineEntry::InLine,
                            });
                        }
                    }
                    scan_statement_payload(lex, leading, origin, fence, baseline, stops)
                },
            )
        })
        .expect("Mod payload scanning is total");
    (
        item,
        item_origin + entry - i.remainder().len(),
        next_line_entry,
    )
}

fn mod_draft(
    slot: ModRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
    colon_only: bool,
) -> RecoveryDraft {
    let role = GrammarRole::Declaration(DeclarationRole::Mod(slot));
    let expected: &[ExpectedSyntax] = match slot {
        ModRole::Name | ModRole::TestName => &[ExpectedSyntax::Identifier],
        ModRole::Body => &[ExpectedSyntax::Statement],
        ModRole::BodyIntroducer if colon_only => {
            &[ExpectedSyntax::Punctuation(PunctuationEvidence::Colon)]
        }
        ModRole::BodyIntroducer => &[
            ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        ],
        _ => unreachable!("local Mod recovery slot"),
    };
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        expected
            .iter()
            .map(|expected| SyntaxExpectation {
                role,
                expected: *expected,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            })
            .collect::<Vec<_>>()
            .into(),
        0,
    )
}

fn mod_missing(i: &mut SyntaxIn, item: &Item, origin: usize, role: ModRole, colon_only: bool) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        mod_draft(
            role,
            RecoveryKind::Missing,
            range,
            Arc::from([]),
            colon_only,
        )
    });
}

#[allow(clippy::too_many_arguments)]
fn mod_error_run(
    mut i: SyntaxIn,
    mut item: Item,
    role: ModRole,
    baseline: usize,
    stops: Stops,
    mut origin: usize,
    mut line: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let name = matches!(role, ModRole::Name | ModRole::TestName);
    let start = item.extent(origin).recovery_range().start;
    emit_recovery_error_run(
        i.rb(),
        |run| loop {
            let kind = token_kind(&item)
                .map(token_syntax_kind)
                .unwrap_or(SyntaxKind::Operator);
            let end = run.emit_item_as(item, origin, kind).recovery_range().end;
            (item, origin, line) =
                run.lexical(|lex| scan_mod_item(lex, origin, line, fence, baseline, stops, name));
            let boundary = item.payload_view().is_boundary()
                || item.payload_view().is_eof()
                || implicit_delimited_newline(baseline, item.leading_view())
                || (name && !gmod_allowed(&item, baseline))
                || run.lexical(|lex| {
                    crate::lexical::observation::is_active_stop_lex(lex, &item, stops)
                })
                || token_kind(&item) == Some(TokenKind::Comma);
            let retry = !boundary
                && if name {
                    is_body_starter_item(&item) || item_word(&item).is_some()
                } else {
                    (role == ModRole::BodyIntroducer && is_body_starter_item(&item))
                        || (role == ModRole::Body
                            && token_kind(&item) == Some(TokenKind::Semicolon))
                        || run
                            .lexical(|lex| {
                                crate::statement::classify_statement_item_lexical(
                                    lex.remainder(),
                                    &item,
                                    baseline,
                                    origin,
                                    fence,
                                )
                            })
                            .is_some()
                };
            if boundary || retry {
                run.append_unexpected(UnexpectedSyntax::Token {
                    range: start..end,
                    category: UnexpectedCategory::OtherCharacter,
                });
                return (item, origin, line);
            }
        },
        |range, unexpected| mod_draft(role, RecoveryKind::Error, range, unexpected, false),
    )
}

fn name_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || implicit_delimited_newline(baseline, item.leading_view())
        || is_active_stop(i.rb(), item, stops)
        || token_kind(item) == Some(TokenKind::Comma)
}

fn body_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || implicit_delimited_newline(baseline, item.leading_view())
        || is_active_stop(i.rb(), item, stops)
        || token_kind(item) == Some(TokenKind::Comma)
}

fn mod_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    body_boundary(i.rb(), item, baseline, stops) || token_kind(item) == Some(TokenKind::Semicolon)
}

fn gmod_allowed(item: &Item, baseline: usize) -> bool {
    indentation_after_newline(item.leading_view()).is_none_or(|indentation| indentation > baseline)
}

fn is_body_starter_item(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Semicolon | TokenKind::LBrace | TokenKind::Colon)
    )
}

fn inline_terminal_semicolon(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Semicolon)
        && indentation_after_newline(item.leading_view()).is_none()
}

fn item_word(item: &Item) -> Option<&str> {
    let payload = item.payload_view();
    assert!(!payload.is_boundary(), "a boundary is not a word");
    (payload.token_kind() == Some(TokenKind::Identifier))
        .then(|| payload.spelling())
        .flatten()
}

fn emit_item_as(i: &mut SyntaxIn, item: Item, kind: SyntaxKind) {
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_visibility(i: &mut SyntaxIn, item: Item) {
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("Mod visibility was selected from exact words"),
    };
    emit_item_as(i, item, kind);
}
