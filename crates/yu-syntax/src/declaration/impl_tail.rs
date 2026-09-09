//! Post-keyword `impl` head, description, body, and recovery construction.

use crate::ambient_claim::AmbientClaimContext;
use crate::cursor::recovery::RecoveryDraft;
use crate::recovery_record::{
    DeclarationRole, Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole, ImplRole,
    PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
    UnexpectedSyntax,
};
use std::sync::Arc;

use crate::syntax_kind::SyntaxKind;

use crate::{
    cursor::recovery::emit::{
        emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
    },
    cursor::{LexIn, SyntaxIn},
    expression::if_expr::active_statement_companion,
    handoff::{Either, NormalizedExit, complete, handoff},
    lexical::{
        current_item::LineEntry,
        item::{Item, LeadingTrivia, TokenKind},
        lexer::introduced_body_indentation_normalized,
        observation::{
            implicit_delimited_newline, indentation_after_newline, is_active_stop, is_separator,
            token_kind,
        },
        position::{advanced_origin, suffix_marker},
        stops::Stops,
        trivia::observe_fenced_trivia_with_newline,
        yumark::FenceBoundary,
    },
    statement::{
        StatementAdmission, StatementLineHandoff, braced_statement_block_normalized,
        canonical_statement_from_admission_normalized, classify_statement_item_normalized,
        indented_statement_block_normalized,
    },
    type_expr::{
        RequiredTypeFreshPrimaryPolicy, TypeOuterBoundary, is_type_caller_boundary,
        required_type_expr_with_caller_stops_and_outer_boundary_and_fresh_primary_policy_normalized,
        required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient,
    },
};

use super::impl_decl::{impl_gap_allowed, impl_item_normalized, scan_impl_item};

#[allow(clippy::too_many_arguments)]
pub(super) fn impl_tail_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let (mut head, next_origin, next_entry) = impl_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        false,
        true,
    );
    item_origin = next_origin;
    line_entry = next_entry;
    let retry_after_missing_head = body_starter(&head);
    let local_missing_head_gap = retry_after_missing_head && impl_gap_allowed(&head, baseline);
    if local_missing_head_gap || !head_gap_is_outer_owned(i.rb(), &head, baseline, stops) {
        head.emit_all_remaining_leading(&mut *i.state);
    }

    let child_entry = suffix_marker(i.rb());
    let (exit, head_complete) =
        required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient(
            i.rb(),
            head,
            GrammarRole::Declaration(DeclarationRole::Impl(ImplRole::Head)),
            baseline,
            stops,
            TypeOuterBoundary::VARIANT_BODY,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    item_origin = advanced_origin(item_origin, child_entry, i.rb());
    let (item, item_origin, line_entry) =
        successor_after_type_normalized(i.rb(), exit, item_origin, baseline, stops, fence);
    let exit = after_head_from_item_normalized(
        i.rb(),
        item,
        head_complete,
        retry_after_missing_head,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    exit
}

#[allow(clippy::too_many_arguments)]
fn successor_after_type_normalized(
    i: SyntaxIn,
    exit: NormalizedExit,
    item_origin: usize,
    baseline: usize,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => impl_item_normalized(
            i,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            false,
            false,
        ),
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            (item, item_origin, line_entry)
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            (end.item, item_origin, line_entry)
        }
        NormalizedExit::Deferred(_, _) => {
            unreachable!("normalized TypeExpression does not defer an Impl owner")
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn after_head_from_item_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    head_complete: bool,
    retry_after_missing_head: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if !impl_gap_allowed(&item, baseline)
        || (!body_starter(&item) && body_boundary(i.rb(), &item, baseline, stops))
    {
        if head_complete {
            if impl_gap_allowed(&item, baseline) && item.payload_view().is_eof() {
                item.emit_eof_leading(&mut *i.state);
            }
            impl_missing(&mut i, &item, item_origin, ImplRole::BodyIntroducer);
        }
        return complete(handoff(item), line_entry);
    }
    if !head_complete && (!retry_after_missing_head || !body_starter(&item)) {
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    match token_kind(&item) {
        Some(TokenKind::Semicolon) => {
            emit_token_item(&mut i, item);
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        Some(TokenKind::LBrace) => braced_body_normalized(
            i,
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(TokenKind::Colon)
            if !colon_following_has_physical_newline(i.rb(), item_origin, fence) =>
        {
            description_normalized(
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
        Some(TokenKind::Colon) => {
            emit_token_item(&mut i, item);
            colon_body_normalized(
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
        _ if head_complete => recover_body_introducer_normalized(
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
        _ => complete(handoff(item), line_entry),
    }
}

#[allow(clippy::too_many_arguments)]
fn description_normalized(
    mut i: SyntaxIn,
    colon: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::ImplDescription.into());
    emit_token_item(&mut i, colon);
    let (mut description, next_origin, next_entry) = impl_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        false,
        true,
    );
    item_origin = next_origin;
    line_entry = next_entry;
    let retry_after_missing_description = description_body_starter(&description);
    let local_missing_description_gap =
        retry_after_missing_description && impl_gap_allowed(&description, baseline);
    if local_missing_description_gap
        || !description_gap_is_outer_owned(i.rb(), &description, baseline, stops)
    {
        if description.payload_view().is_eof() {
            description.emit_eof_leading(&mut *i.state);
        } else {
            description.emit_all_remaining_leading(&mut *i.state);
        }
    }
    let child_entry = suffix_marker(i.rb());
    let (exit, description_complete) =
        required_type_expr_with_caller_stops_and_outer_boundary_and_fresh_primary_policy_normalized(
            i.rb(),
            description,
            GrammarRole::Declaration(DeclarationRole::Impl(ImplRole::Description)),
            baseline,
            stops,
            TypeOuterBoundary::VARIANT_BODY,
            RequiredTypeFreshPrimaryPolicy {
                owns_bare_left_brace: true,
            },
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    item_origin = advanced_origin(item_origin, child_entry, i.rb());
    let (item, item_origin, line_entry) =
        successor_after_type_normalized(i.rb(), exit, item_origin, baseline, stops, fence);
    i.state.finish_node();
    body_from_item_normalized(
        i,
        item,
        description_complete,
        retry_after_missing_description,
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
fn body_from_item_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    upstream_complete: bool,
    retry_after_missing_slot: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if !impl_gap_allowed(&item, baseline)
        || (!body_starter(&item) && body_boundary(i.rb(), &item, baseline, stops))
    {
        if upstream_complete {
            if impl_gap_allowed(&item, baseline) && item.payload_view().is_eof() {
                item.emit_eof_leading(&mut *i.state);
            }
            impl_missing(&mut i, &item, item_origin, ImplRole::BodyIntroducer);
        }
        return complete(handoff(item), line_entry);
    }
    if !upstream_complete && (!retry_after_missing_slot || !body_starter(&item)) {
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    match token_kind(&item) {
        Some(TokenKind::Semicolon) => {
            emit_token_item(&mut i, item);
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        Some(TokenKind::LBrace) => braced_body_normalized(
            i,
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(TokenKind::Colon) => {
            emit_token_item(&mut i, item);
            colon_body_normalized(
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
        _ if upstream_complete => recover_body_introducer_normalized(
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
        _ => complete(handoff(item), line_entry),
    }
}

#[allow(clippy::too_many_arguments)]
fn braced_body_normalized(
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let child_entry = suffix_marker(i.rb());
    let exit = braced_statement_block_normalized(
        i.rb(),
        item,
        baseline,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, child_entry, i.rb());
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => {
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        exit => exit,
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
    item.emit_all_remaining_leading(&mut *i.state);
    (item, item_origin, line_entry) = impl_error_run(
        i.rb(),
        item,
        ImplRole::BodyIntroducer,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if impl_gap_allowed(&item, baseline) && body_starter(&item) {
        return body_from_item_normalized(
            i,
            item,
            true,
            false,
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
    complete(handoff(item), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn colon_body_normalized(
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
                crate::recovery_record::DeclarationRole::Impl(
                    crate::recovery_record::ImplRole::IndentedStatement,
                ),
            ),
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(_) => {
            let (item, origin, line_entry) = impl_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                false,
                false,
            );
            impl_missing(&mut i, &item, origin, ImplRole::Body);
            complete(handoff(item), line_entry)
        }
        None => {
            let (item, item_origin, line_entry) = impl_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                false,
                false,
            );
            inline_body_from_item_normalized(
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
fn inline_body_from_item_normalized(
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
    if inline_body_boundary(i.rb(), &item, baseline, stops) {
        impl_missing(&mut i, &item, item_origin, ImplRole::Body);
        return complete(handoff(item), line_entry);
    }
    if let Some(admission) =
        classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
    {
        return inline_statement_normalized(
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
    (item, item_origin, line_entry) = impl_error_run(
        i.rb(),
        item,
        ImplRole::Body,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if inline_body_boundary(i.rb(), &item, baseline, stops) {
        return complete(handoff(item), line_entry);
    }
    if let Some(admission) =
        classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
    {
        return inline_statement_normalized(
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
    unreachable!("Impl body recovery stops at a boundary or Statement")
}

#[allow(clippy::too_many_arguments)]
fn inline_statement_normalized(
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
    let child_entry = suffix_marker(i.rb());
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
    let item_origin = advanced_origin(item_origin, child_entry, i.rb());
    match exit {
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if inline_terminal_semicolon(&item) =>
        {
            emit_token_item(&mut i, item);
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        NormalizedExit::Complete(Ok(()), line_entry) => {
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
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
    let (item, _, line_entry) = impl_item_normalized(
        i,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        false,
        false,
    );
    complete(handoff(item), line_entry)
}

fn colon_following_has_physical_newline(
    i: SyntaxIn,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            Some(
                observe_fenced_trivia_with_newline(
                    lex.remainder(),
                    item_origin,
                    LineEntry::InLine,
                    fence,
                )
                .saw_physical_newline,
            )
        },
        |has_newline| has_newline,
    )
    .unwrap_or(false)
}

fn head_gap_is_outer_owned(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || !impl_gap_allowed(item, baseline)
        || is_type_caller_boundary(item, stops)
        || body_starter(item)
        || is_active_stop(i.rb(), item, stops)
}

fn description_gap_is_outer_owned(
    mut i: SyntaxIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
) -> bool {
    item.payload_view().is_boundary()
        || !impl_gap_allowed(item, baseline)
        || is_type_caller_boundary(item, stops)
        || description_body_starter(item)
        || is_active_stop(i.rb(), item, stops)
}

fn body_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || implicit_delimited_newline(baseline, item.leading_view())
        || is_active_stop(i.rb(), item, stops)
        || is_separator(item)
        || matches!(
            token_kind(item),
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
        || active_statement_companion(i.rb(), item, baseline, stops).is_some()
}

fn inline_body_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    body_boundary(i.rb(), item, baseline, stops) || token_kind(item) == Some(TokenKind::Semicolon)
}

fn body_starter(item: &Item) -> bool {
    !item.payload_view().is_boundary()
        && matches!(
            token_kind(item),
            Some(TokenKind::Semicolon | TokenKind::LBrace | TokenKind::Colon)
        )
}

fn description_body_starter(item: &Item) -> bool {
    !item.payload_view().is_boundary()
        && matches!(
            token_kind(item),
            Some(TokenKind::Semicolon | TokenKind::Colon)
        )
}

fn inline_terminal_semicolon(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Semicolon)
        && indentation_after_newline(item.leading_view()).is_none()
}
fn impl_draft(
    slot: ImplRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let role = GrammarRole::Declaration(DeclarationRole::Impl(slot));
    let expected: &[ExpectedSyntax] = match slot {
        ImplRole::BodyIntroducer => &[
            ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        ],
        ImplRole::Body => &[ExpectedSyntax::Statement],
        _ => unreachable!("local Impl recovery slot"),
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

fn impl_missing(i: &mut SyntaxIn, item: &Item, origin: usize, role: ImplRole) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        impl_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

#[allow(clippy::too_many_arguments)]
fn impl_error_run(
    mut i: SyntaxIn,
    mut item: Item,
    role: ImplRole,
    baseline: usize,
    stops: Stops,
    mut origin: usize,
    mut line: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let start = item.extent(origin).recovery_range().start;
    emit_recovery_error_run(
        i.rb(),
        |run| loop {
            let kind = token_kind(&item)
                .map(token_syntax_kind)
                .unwrap_or(SyntaxKind::Operator);
            let end = run.emit_item_as(item, origin, kind).recovery_range().end;
            (item, origin, line) = run.lexical(|lex| {
                scan_impl_item(lex, origin, line, fence, baseline, stops, false, false)
            });
            let starter = role == ImplRole::BodyIntroducer && body_starter(&item);
            let boundary = item.payload_view().is_boundary()
                || item.payload_view().is_eof()
                || !impl_gap_allowed(&item, baseline)
                || (!starter
                    && (run.lexical(|lex| {
                        crate::lexical::observation::is_active_stop_lex(lex, &item, stops)
                    }) || is_separator(&item)
                        || matches!(
                            token_kind(&item),
                            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
                        )));
            let retry = !boundary
                && (starter
                    || (role == ImplRole::Body
                        && run
                            .lexical(|lex| {
                                crate::statement::classify_statement_item_lexical(
                                    lex.remainder(),
                                    &item,
                                    baseline,
                                    origin,
                                    fence,
                                )
                            })
                            .is_some()));
            if boundary || retry {
                run.append_unexpected(UnexpectedSyntax::Token {
                    range: start..end,
                    category: UnexpectedCategory::OtherCharacter,
                });
                return (item, origin, line);
            }
        },
        |range, unexpected| impl_draft(role, RecoveryKind::Error, range, unexpected),
    )
}
