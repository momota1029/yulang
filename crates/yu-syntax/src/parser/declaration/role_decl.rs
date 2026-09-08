//! Private direct `role` declaration construction.

use crate::parser::context::ambient_claim::AmbientClaimContext;
#[cfg(test)]
use crate::parser::context::ambient_claim::AmbientClaimView;
use crate::parser::output::RecoveryDraft;
use crate::session::{
    DeclarationRole, Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole,
    PunctuationEvidence, RecoveryKind, RecoverySiteKey, RoleDeclarationRole, SyntaxExpectation,
    UnexpectedCategory, UnexpectedSyntax,
};
use reborrow_generic::Reborrow as _;
use std::sync::Arc;

use crate::syntax_kind::SyntaxKind;

use crate::parser::{
    LexIn, ParserIn, Stops,
    expression::if_expr::active_statement_companion,
    handoff::{Either, NormalizedExit, complete, handoff},
    input::{
        current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
        item::{Item, LeadingTrivia, TokenKind},
        lexer::{
            introduced_body_indentation_normalized, scan_identifier, scan_statement_payload,
            scan_type_nud_payload, source_identifier,
        },
        observation::{
            implicit_delimited_newline, indentation_after_newline, is_active_stop, is_separator,
            token_kind,
        },
        operator::{TriviaObservation, observe_fenced_trivia},
        position::{advanced_origin, suffix_marker},
        yumark::FenceBoundary,
    },
    output::emit::{
        emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
    },
    statement::{
        StatementAdmission, StatementLineHandoff, braced_statement_block_normalized,
        canonical_statement_from_admission_normalized, classify_statement_item_normalized,
        indented_statement_block_normalized,
    },
    type_expr::{
        TypeOuterBoundary, is_type_caller_boundary,
        required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient,
    },
};

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(in crate::parser) fn role_declaration_witness(
    mut i: ParserIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<NormalizedExit> {
    if !role_source_selected_normalized(i.rb(), baseline, item_origin, line_entry, fence) {
        return None;
    }
    let (intro, item_origin, line_entry) = role_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        true,
        false,
    );
    role_declaration_selected_normalized(i.rb(), &intro, baseline, item_origin, fence).then(|| {
        role_declaration_normalized(
            i,
            intro,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            Some(AmbientClaimView::root_statement(baseline)).into(),
            Some(crate::parser::context::sequence::SequenceOwner::RootStatement),
        )
    })
}

#[cfg(test)]
fn role_source_selected_normalized(
    i: ParserIn,
    baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            let source = lex.remainder();
            let TriviaObservation::Visible(observed) =
                observe_fenced_trivia(source, item_origin, line_entry, fence)
            else {
                return Some(false);
            };
            if observed
                .indentation
                .is_some_and(|indentation| indentation <= baseline)
            {
                return Some(false);
            }
            let Some((word, suffix)) = source_identifier(observed.source) else {
                return Some(false);
            };
            if word == "role" {
                return Some(true);
            }
            if !matches!(word, "my" | "our" | "pub") {
                return Some(false);
            }
            let leading_len = source.len() - observed.source.len();
            Some(prefixed_role_candidate_normalized(
                suffix,
                item_origin + leading_len + word.len(),
                fence,
                baseline,
            ))
        },
        |selected| selected,
    )
    .unwrap_or(false)
}

#[cfg(test)]
pub(in crate::parser) fn role_declaration_selected_normalized(
    i: ParserIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            Some(role_declaration_selected_lexical(
                lex.remainder(),
                item,
                baseline,
                item_origin,
                fence,
            ))
        },
        |selected| selected,
    )
    .unwrap_or(false)
}

pub(in crate::parser) fn role_declaration_selected_lexical(
    source: &str,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item_word(item) == Some("role") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    prefixed_role_candidate_normalized(source, item_origin, fence, baseline)
}

fn prefixed_role_candidate_normalized(
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
    observed.present
        && observed
            .indentation
            .is_none_or(|indentation| indentation > baseline)
        && source_identifier(observed.source).is_some_and(|(word, _)| word == "role")
}

#[allow(clippy::too_many_arguments)]
pub(in crate::parser) fn role_declaration_normalized(
    mut i: ParserIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::RoleDeclaration.into());
    if item_word(&intro) == Some("role") {
        emit_item_as(&mut i, intro, SyntaxKind::RoleKw);
    } else {
        emit_visibility(&mut i, intro);
        let (mut keyword, next_origin, next_entry) = role_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            true,
            false,
        );
        item_origin = next_origin;
        line_entry = next_entry;
        debug_assert!(role_gap_allowed(&keyword, baseline));
        debug_assert_eq!(item_word(&keyword), Some("role"));
        keyword.emit_all_remaining_leading(&mut *i.state);
        emit_item_as(&mut i, keyword, SyntaxKind::RoleKw);
    }

    let (mut head, next_origin, next_entry) = role_item_normalized(
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
    let retry_body_after_missing_head = body_starter(&head);
    let local_missing_head_gap = retry_body_after_missing_head && role_gap_allowed(&head, baseline);
    if local_missing_head_gap || !head_gap_is_outer_owned(i.rb(), &head, baseline, stops) {
        head.emit_all_remaining_leading(&mut *i.state);
    }

    let child_entry = suffix_marker(i.rb());
    let (exit, head_complete) =
        required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient(
            i.rb(),
            head,
            GrammarRole::Declaration(DeclarationRole::Role(RoleDeclarationRole::Head)),
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
        successor_after_head_normalized(i.rb(), exit, item_origin, baseline, stops, fence);
    let exit = body_from_item_normalized(
        i.rb(),
        item,
        head_complete,
        retry_body_after_missing_head,
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

#[allow(clippy::too_many_arguments)]
fn successor_after_head_normalized(
    i: ParserIn,
    exit: NormalizedExit,
    item_origin: usize,
    baseline: usize,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => role_item_normalized(
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
            unreachable!("normalized TypeExpression does not defer a Role owner")
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn body_from_item_normalized(
    mut i: ParserIn,
    mut item: Item,
    head_complete: bool,
    retry_body_after_missing_head: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    if !role_gap_allowed(&item, baseline)
        || (!body_starter(&item) && body_boundary(i.rb(), &item, baseline, stops))
    {
        if head_complete {
            if item.payload_view().is_eof() {
                item.emit_eof_leading(&mut *i.state);
            }
            role_missing(
                &mut i,
                &item,
                item_origin,
                RoleDeclarationRole::BodyIntroducer,
            );
        }
        return complete(handoff(item), line_entry);
    }
    if !head_complete && (!retry_body_after_missing_head || !body_starter(&item)) {
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    match token_kind(&item) {
        Some(TokenKind::Semicolon) => {
            emit_token_item(&mut i, item);
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        Some(TokenKind::LBrace) => {
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
fn recover_body_introducer_normalized(
    mut i: ParserIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    (item, item_origin, line_entry) = role_error_run(
        i.rb(),
        item,
        RoleDeclarationRole::BodyIntroducer,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if role_gap_allowed(&item, baseline) && body_starter(&item) {
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
    mut i: ParserIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    match introduced_body_indentation_normalized(i.rb(), item_origin, fence) {
        Some(indentation) if indentation > baseline => indented_statement_block_normalized(
            i,
            baseline,
            crate::session::GrammarRole::Declaration(crate::session::DeclarationRole::Role(
                crate::session::RoleDeclarationRole::IndentedStatement,
            )),
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(_) => {
            let (item, origin, line_entry) = role_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                false,
                false,
            );
            role_missing(&mut i, &item, origin, RoleDeclarationRole::Body);
            complete(handoff(item), line_entry)
        }
        None => {
            let (item, item_origin, line_entry) = role_item_normalized(
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
    mut i: ParserIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    if inline_body_boundary(i.rb(), &item, baseline, stops) {
        role_missing(&mut i, &item, item_origin, RoleDeclarationRole::Body);
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
    mut i: ParserIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    item.emit_all_remaining_leading(&mut *i.state);
    (item, item_origin, line_entry) = role_error_run(
        i.rb(),
        item,
        RoleDeclarationRole::Body,
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
    unreachable!("Role body recovery stops at a boundary or Statement")
}

#[allow(clippy::too_many_arguments)]
fn inline_statement_normalized(
    mut i: ParserIn,
    item: Item,
    admission: StatementAdmission,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
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
    i: ParserIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, _, line_entry) = role_item_normalized(
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

fn head_gap_is_outer_owned(mut i: ParserIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || !role_gap_allowed(item, baseline)
        || is_type_caller_boundary(item, stops)
        || body_starter(item)
        || is_active_stop(i.rb(), item, stops)
}

fn body_boundary(mut i: ParserIn, item: &Item, baseline: usize, stops: Stops) -> bool {
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

fn inline_body_boundary(mut i: ParserIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    body_boundary(i.rb(), item, baseline, stops) || token_kind(item) == Some(TokenKind::Semicolon)
}

fn role_gap_allowed(item: &Item, baseline: usize) -> bool {
    indentation_after_newline(item.leading_view()).is_none_or(|indentation| indentation > baseline)
}

fn body_starter(item: &Item) -> bool {
    !item.payload_view().is_boundary()
        && matches!(
            token_kind(item),
            Some(TokenKind::Semicolon | TokenKind::LBrace | TokenKind::Colon)
        )
}

fn inline_terminal_semicolon(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Semicolon)
        && indentation_after_newline(item.leading_view()).is_none()
}

#[allow(clippy::too_many_arguments)]
fn role_item_normalized(
    mut i: ParserIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
) -> (Item, usize, LineEntry) {
    i.token(|lex| {
        Some(scan_role_item(
            lex,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            raw_identifier,
            type_vocabulary,
        ))
    })
    .expect("total Role scanner")
}

#[allow(clippy::too_many_arguments)]
fn scan_role_item(
    mut i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
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
                    if raw_identifier && let Some(identifier) = lex.token(scan_identifier) {
                        return Some(AcceptedPayload {
                            payload: CurrentPayload::Token(identifier),
                            next_line_entry: LineEntry::InLine,
                        });
                    }
                    if type_vocabulary {
                        scan_type_nud_payload(lex, leading, origin, fence)
                    } else {
                        scan_statement_payload(lex, leading, origin, fence, baseline, stops)
                    }
                },
            )
        })
        .expect("Role declaration payload scanning is total");
    (
        item,
        item_origin + entry - i.remainder().len(),
        next_line_entry,
    )
}

fn item_word(item: &Item) -> Option<&str> {
    (item.payload_view().token_kind() == Some(TokenKind::Identifier))
        .then(|| item.payload_view().spelling())
        .flatten()
}

fn role_draft(
    slot: RoleDeclarationRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let role = GrammarRole::Declaration(DeclarationRole::Role(slot));
    let expected: &[ExpectedSyntax] = match slot {
        RoleDeclarationRole::BodyIntroducer => &[
            ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        ],
        RoleDeclarationRole::Body => &[ExpectedSyntax::Statement],
        _ => unreachable!("local Role recovery slot"),
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

fn role_missing(i: &mut ParserIn, item: &Item, origin: usize, role: RoleDeclarationRole) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        role_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

#[allow(clippy::too_many_arguments)]
fn role_error_run(
    mut i: ParserIn,
    mut item: Item,
    role: RoleDeclarationRole,
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
                scan_role_item(lex, origin, line, fence, baseline, stops, false, false)
            });
            let starter = role == RoleDeclarationRole::BodyIntroducer && body_starter(&item);
            let boundary = item.payload_view().is_boundary()
                || item.payload_view().is_eof()
                || !role_gap_allowed(&item, baseline)
                || (!starter
                    && (run.lexical(|lex| {
                        crate::parser::input::observation::is_active_stop_lex(lex, &item, stops)
                    }) || is_separator(&item)
                        || matches!(
                            token_kind(&item),
                            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
                        )));
            let retry = !boundary
                && (starter
                    || (role == RoleDeclarationRole::Body
                        && run
                            .lexical(|lex| {
                                crate::parser::statement::classify_statement_item_lexical(
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
        |range, unexpected| role_draft(role, RecoveryKind::Error, range, unexpected),
    )
}

fn emit_item_as(i: &mut ParserIn, item: Item, kind: SyntaxKind) {
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_visibility(i: &mut ParserIn, item: Item) {
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("Role visibility uses exact declaration words"),
    };
    emit_item_as(i, item, kind);
}
