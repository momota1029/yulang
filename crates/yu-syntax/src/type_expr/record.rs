//! Named record type owner and its local recovery.

use crate::ambient_claim::AmbientClaimContext;
use reborrow_generic::Reborrow as _;
use std::sync::Arc;

use crate::{
    recovery_record::{
        ConstructRole, Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation, TypeRole,
        UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use crate::type_expr::{
    TypeApplyBoundary, TypeMlContext, TypeOuterBoundary, continue_type_tail_normalized,
    is_type_caller_boundary, is_type_caller_boundary_parts, is_type_implicit_boundary,
    is_type_mismatched_close, is_type_nud, is_type_outer_close, is_type_record_field_boundary,
    is_type_record_field_name, type_chain_trivia, type_delimited_baseline,
    type_expr_from_nud_normalized, type_item_with_pipe_lexical_normalized,
    type_nud_item_with_pipe_lexical_normalized,
    type_nud_item_with_pipe_lexical_normalized_in_error_run, type_recovery_error_syntax_kind,
    with_type_outer_close,
};
use crate::{
    cursor::recovery::{
        RecoveryDraft,
        emit::{emit_recovery_error_run, emit_recovery_missing, emit_token_item},
    },
    cursor::{LexIn, SyntaxIn},
    handoff::{Either, NormalizedExit, complete, handoff},
    lexical::{
        current_item::{AcceptedPayload, CurrentPayload, LineEntry},
        item::{Item, LeadingTrivia, Token, TokenKind},
        lexer::{scan_exact_pipe, scan_type_nud_payload},
        observation::token_kind,
        position::{advanced_origin, suffix_marker},
        stops::Stops,
        trivia::{TriviaObservation, observe_fenced_trivia},
        yumark::FenceBoundary,
    },
};

#[allow(clippy::too_many_arguments)]
pub(super) fn type_record_normalized(
    mut i: SyntaxIn,
    open: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::NamedRecordType.into());
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = type_record_fields_normalized(
        i.rb(),
        baseline,
        type_ml.dormant(),
        with_type_outer_close(outer_closes, TokenKind::RBrace),
        caller_stops,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_type_tail_normalized(
        i,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        exit,
        item_origin,
        fence,
        ambient,
    )
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RecordPosition {
    Initial,
    AfterComma,
    AfterField,
    AfterError,
}

#[allow(clippy::too_many_arguments)]
fn type_record_fields_normalized(
    mut i: SyntaxIn,
    incoming_baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let (mut item, next_origin, next_line_entry) = type_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
        ambient,
    );
    item_origin = next_origin;
    line_entry = next_line_entry;
    let baseline = type_delimited_baseline(incoming_baseline, item.leading_view());
    let mut position = RecordPosition::Initial;

    loop {
        let newline = !item.payload_view().is_boundary()
            && is_type_implicit_boundary(baseline, item.leading_view());
        let after_item = matches!(
            position,
            RecordPosition::AfterField | RecordPosition::AfterError
        );
        let missing_field = position == RecordPosition::AfterComma || (after_item && newline);
        if item.payload_view().is_boundary() || item.payload_view().is_eof() {
            return record_boundary_normalized(
                i,
                item,
                baseline,
                missing_field,
                item_origin,
                line_entry,
            );
        }
        if token_kind(&item) == Some(TokenKind::RBrace) {
            i.state.start_node(SyntaxKind::NamedRecordTypeClose.into());
            emit_token_item(&mut i, item);
            i.state.finish_node();
            return complete(Ok(()), line_entry);
        }
        // The local comma owns its slot before an enclosing comma stop.
        if token_kind(&item) == Some(TokenKind::Comma) {
            item.emit_all_remaining_leading(&mut *i.state);
            if matches!(
                position,
                RecordPosition::Initial | RecordPosition::AfterComma
            ) {
                emit_record_field_missing(&mut i, TypeRole::RecordField, &item, item_origin);
            }
            emit_token_item(&mut i, item);
            (item, item_origin, line_entry) = type_item_with_pipe_lexical_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
                ambient,
            );
            position = RecordPosition::AfterComma;
            continue;
        }

        let same_line_head = position == RecordPosition::AfterField
            && type_record_next_field_normalized(
                i.rb(),
                &item,
                baseline,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
                ambient,
            );
        let field_position = position != RecordPosition::AfterField || newline;
        let caller = is_type_caller_boundary(&item, caller_stops);
        let local_caller_head = caller
            && field_position
            && (is_record_colon_kind(token_kind(&item))
                || (is_type_record_field_name(&item)
                    && type_record_field_head_after_normalized(
                        i.rb(),
                        baseline,
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                        ambient,
                    )));
        if (caller && !same_line_head && !local_caller_head)
            || is_type_outer_close(&item, outer_closes)
        {
            return record_boundary_normalized(
                i,
                item,
                baseline,
                missing_field,
                item_origin,
                line_entry,
            );
        }
        if is_type_mismatched_close(&item, TokenKind::RBrace) {
            if missing_field {
                emit_record_field_missing(&mut i, TypeRole::RecordField, &item, item_origin);
            }
            i.state.start_node(SyntaxKind::NamedRecordTypeClose.into());
            let caller_owned;
            (item, item_origin, line_entry, caller_owned) = retry_record_run_normalized(
                i.rb(),
                item,
                RecordErrorSlot::Close,
                baseline,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
            if !caller_owned
                && !item.payload_view().is_boundary()
                && token_kind(&item) == Some(TokenKind::RBrace)
            {
                emit_token_item(&mut i, item);
                i.state.finish_node();
                return complete(Ok(()), line_entry);
            }
            if item.payload_view().is_eof() && type_chain_trivia(item.leading_view(), baseline) {
                item.emit_all_remaining_leading(&mut *i.state);
            }
            emit_record_close_missing(&mut i, &item, item_origin);
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if after_item && newline && !is_type_record_field_start(&item) {
            return record_boundary_normalized(i, item, baseline, true, item_origin, line_entry);
        }
        if same_line_head {
            item.emit_all_remaining_leading(&mut *i.state);
            i.state
                .start_node(SyntaxKind::NamedRecordTypeSeparator.into());
            emit_record_field_missing(&mut i, TypeRole::RecordFieldSeparator, &item, item_origin);
            i.state.finish_node();
        } else if token_kind(&item) == Some(TokenKind::Semicolon)
            || (position == RecordPosition::AfterField && !newline)
        {
            item.emit_all_remaining_leading(&mut *i.state);
            i.state
                .start_node(SyntaxKind::NamedRecordTypeSeparator.into());
            let caller_owned;
            (item, item_origin, line_entry, caller_owned) = retry_record_run_normalized(
                i.rb(),
                item,
                RecordErrorSlot::Separator,
                baseline,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
            i.state.finish_node();
            if caller_owned {
                let missing_field = is_type_implicit_boundary(baseline, item.leading_view());
                return record_boundary_normalized(
                    i,
                    item,
                    baseline,
                    missing_field,
                    item_origin,
                    line_entry,
                );
            }
            position = RecordPosition::AfterError;
            continue;
        }

        // This leading is now admitted by the record, not by a failed field
        // slot or a speculative next-field query.
        item.emit_all_remaining_leading(&mut *i.state);
        let child_entry = suffix_marker(i.rb());
        let exit = if is_type_record_field_name(&item) {
            type_record_field_normalized(
                i.rb(),
                item,
                baseline,
                type_ml,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        } else if is_record_colon_kind(token_kind(&item)) {
            type_record_missing_name_normalized(
                i.rb(),
                item,
                baseline,
                type_ml,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        } else if type_record_malformed_name_colon_normalized(
            i.rb(),
            &item,
            caller_stops,
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
        ) {
            type_record_malformed_name_normalized(
                i.rb(),
                item,
                baseline,
                type_ml,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        } else {
            let caller_owned;
            (item, item_origin, line_entry, caller_owned) = retry_record_run_normalized(
                i.rb(),
                item,
                RecordErrorSlot::Field,
                baseline,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
            if caller_owned {
                let missing_field = is_type_implicit_boundary(baseline, item.leading_view());
                return record_boundary_normalized(
                    i,
                    item,
                    baseline,
                    missing_field,
                    item_origin,
                    line_entry,
                );
            }
            position = RecordPosition::AfterError;
            continue;
        };
        item_origin = advanced_origin(item_origin, child_entry, i.rb());
        (item, line_entry) = match exit {
            NormalizedExit::Complete(Err(Either::Left(next)), line) => (next, line),
            NormalizedExit::Complete(Err(Either::Right(end)), line) => (end.item, line),
            NormalizedExit::Complete(Ok(()), line) => {
                let (next, origin, line) = type_item_with_pipe_lexical_normalized(
                    i.rb(),
                    item_origin,
                    line,
                    fence,
                    pipe_lexical,
                    ambient,
                );
                item_origin = origin;
                (next, line)
            }
            NormalizedExit::Deferred(..) => unreachable!("normalized Type owners do not defer"),
        };
        position = RecordPosition::AfterField;
    }
}

#[allow(clippy::too_many_arguments)]
fn type_record_field_normalized(
    mut i: SyntaxIn,
    name: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::TypeRecordField.into());
    emit_token_item(&mut i, name);
    let (colon, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
        ambient,
    );
    let exit = type_record_colon_normalized(
        i.rb(),
        colon,
        baseline,
        type_ml,
        outer_closes,
        caller_stops,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    i.state.finish_node();
    exit
}
#[allow(clippy::too_many_arguments)]
fn type_record_missing_name_normalized(
    mut i: SyntaxIn,
    colon: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::TypeRecordField.into());
    emit_record_field_missing(&mut i, TypeRole::RecordFieldName, &colon, item_origin);
    emit_token_item(&mut i, colon);
    let exit = type_record_rhs_normalized(
        i.rb(),
        baseline,
        type_ml,
        outer_closes,
        caller_stops,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    i.state.finish_node();
    exit
}

fn type_record_malformed_name_colon_normalized(
    mut i: SyntaxIn,
    item: &Item,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
) -> bool {
    i.rb()
        .token(|lex| {
            Some(type_record_malformed_name_colon_probe(
                lex,
                token_kind(item),
                caller_stops,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
            ))
        })
        .expect("the malformed-name probe always succeeds")
}

fn type_record_malformed_name_colon_probe(
    mut i: LexIn,
    initial_kind: Option<TokenKind>,
    caller_stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
) -> bool {
    let mut source = i.remainder();
    let mut closes = Vec::new();
    advance_record_nesting(&mut closes, initial_kind);
    loop {
        let Some((next, next_origin, next_line_entry, token, indentation)) =
            observe_type_item(i.rb(), source, item_origin, line_entry, fence, pipe_lexical)
        else {
            return false;
        };
        let kind = token.as_ref().map(|token| token.kind);
        let spelling = token.as_ref().map(|token| token.text.as_ref());
        if indentation.is_some() {
            return false;
        }
        if closes.is_empty() && is_record_colon_kind(kind) {
            return true;
        }
        if is_record_name_boundary(kind, spelling, closes.last().copied(), caller_stops) {
            return false;
        }
        advance_record_nesting(&mut closes, kind);
        source = next;
        item_origin = next_origin;
        line_entry = next_line_entry;
    }
}

#[allow(clippy::too_many_arguments)]
fn type_record_malformed_name_normalized(
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::TypeRecordField.into());
    let (item, item_origin, line_entry, caller_owned) = retry_record_run_normalized(
        i.rb(),
        item,
        RecordErrorSlot::Name,
        baseline,
        outer_closes,
        caller_stops,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    // The matching-kind probe and the committed run share the same boundary
    // rule; only a top-level local colon can complete the name skeleton.
    let exit = if !caller_owned
        && is_record_colon_kind(token_kind(&item))
        && !item.leading_view().contains_line_break()
    {
        emit_token_item(&mut i, item);
        type_record_rhs_normalized(
            i.rb(),
            baseline,
            type_ml,
            outer_closes,
            caller_stops,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
            ambient,
        )
    } else {
        complete(handoff(item), line_entry)
    };
    i.state.finish_node();
    exit
}

fn type_record_field_head_after_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
    _ambient: AmbientClaimContext<'_>,
) -> bool {
    i.rb()
        .token(|lex| {
            Some(type_record_field_head_probe(
                lex,
                baseline,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
            ))
        })
        .expect("the field-head probe always succeeds")
}

fn type_record_field_head_probe(
    mut i: LexIn,
    baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
) -> bool {
    let source = i.remainder();
    observe_type_item(i.rb(), source, item_origin, line_entry, fence, pipe_lexical).is_some_and(
        |(_, _, _, token, indentation)| {
            is_record_colon_kind(token.map(|token| token.kind))
                && indentation.is_none_or(|indentation| indentation > baseline)
        },
    )
}

pub(super) fn type_record_next_field_normalized(
    mut i: SyntaxIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
    ambient: AmbientClaimContext<'_>,
) -> bool {
    is_type_record_field_name(item)
        && item.leading_view().indentation_after_newline().is_none()
        && type_record_field_head_after_normalized(
            i.rb(),
            baseline,
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        )
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RecordErrorSlot {
    Field,
    Separator,
    Name,
    Close,
}

impl RecordErrorSlot {
    fn role(self) -> GrammarRole {
        match self {
            Self::Field => GrammarRole::Type(TypeRole::RecordField),
            Self::Separator => GrammarRole::Type(TypeRole::RecordFieldSeparator),
            Self::Name => GrammarRole::Type(TypeRole::RecordFieldName),
            Self::Close => record_close_role(),
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn retry_record_run_normalized(
    i: SyntaxIn,
    mut item: Item,
    slot: RecordErrorSlot,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> (Item, usize, LineEntry, bool) {
    item.emit_all_remaining_leading(&mut *i.state);
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(item_origin).recovery_range().start;
            let mut closes = Vec::new();
            let (end, caller_owned) = loop {
                advance_record_nesting(&mut closes, token_kind(&item));
                let kind = type_recovery_error_syntax_kind(&item);
                let end = run
                    .emit_item_as(item, item_origin, kind)
                    .recovery_range()
                    .end;
                (item, item_origin, line_entry) =
                    type_nud_item_with_pipe_lexical_normalized_in_error_run(
                        run,
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                        ambient,
                    );
                if item.payload_view().is_boundary() || item.payload_view().is_eof() {
                    break (end, false);
                }
                let kind = token_kind(&item);
                let local_close = closes.last().copied();
                let caller = is_type_caller_boundary(&item, caller_stops);
                if slot == RecordErrorSlot::Name {
                    let local_colon = local_close.is_none()
                        && is_record_colon_kind(kind)
                        && !item.leading_view().contains_line_break();
                    if item.leading_view().contains_line_break()
                        || is_record_name_boundary(
                            kind,
                            item.payload_view().spelling(),
                            local_close,
                            caller_stops,
                        )
                    {
                        break (end, caller && !local_colon);
                    }
                    continue;
                }
                let matching_nested_close = local_close.is_some() && kind == local_close;
                let candidate = closes.is_empty()
                    && slot != RecordErrorSlot::Close
                    && (is_record_colon_kind(kind)
                        || (is_type_record_field_name(&item)
                            && ((slot == RecordErrorSlot::Separator && !caller)
                                || run.lexical(|lex| {
                                    type_record_field_head_probe(
                                        lex,
                                        baseline,
                                        item_origin,
                                        line_entry,
                                        fence,
                                        pipe_lexical,
                                    )
                                }))));
                let local_comma = closes.is_empty()
                    && slot != RecordErrorSlot::Close
                    && kind == Some(TokenKind::Comma);
                let record_close = kind == Some(TokenKind::RBrace) && !matching_nested_close;
                if caller && !candidate && !local_comma && !record_close {
                    // Preserve this immediate ownership decision: the sequence
                    // must not reopen a nested caller Item as a fresh field.
                    break (end, true);
                }
                if candidate
                    || local_comma
                    || record_close
                    || (is_record_close_kind(kind)
                        && !matching_nested_close
                        && (slot != RecordErrorSlot::Close
                            || is_type_outer_close(&item, outer_closes)))
                    || (is_type_implicit_boundary(baseline, item.leading_view())
                        && !matching_nested_close)
                {
                    break (end, false);
                }
            };
            run.append_unexpected(UnexpectedSyntax::Token {
                range: start..end,
                category: UnexpectedCategory::OtherCharacter,
            });
            (item, item_origin, line_entry, caller_owned)
        },
        |range, unexpected| {
            record_recovery_draft(slot.role(), RecoveryKind::Error, range, unexpected)
        },
    )
}

fn advance_record_nesting(closes: &mut Vec<TokenKind>, kind: Option<TokenKind>) {
    match kind {
        Some(TokenKind::LParen) => closes.push(TokenKind::RParen),
        Some(TokenKind::LBracket) => closes.push(TokenKind::RBracket),
        Some(TokenKind::LBrace) => closes.push(TokenKind::RBrace),
        Some(close) if Some(&close) == closes.last() => {
            closes.pop();
        }
        _ => {}
    }
}

fn is_record_close_kind(kind: Option<TokenKind>) -> bool {
    matches!(
        kind,
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
    )
}

fn is_record_name_boundary(
    kind: Option<TokenKind>,
    spelling: Option<&str>,
    local_close: Option<TokenKind>,
    caller_stops: Stops,
) -> bool {
    (local_close.is_none() && is_record_colon_kind(kind))
        || is_type_caller_boundary_parts(kind, spelling, caller_stops)
        || (is_record_close_kind(kind) && kind != local_close)
        || (local_close.is_none()
            && matches!(
                kind,
                Some(TokenKind::Identifier | TokenKind::Comma | TokenKind::Semicolon)
            ))
}

#[allow(clippy::too_many_arguments)]
fn type_record_colon_normalized(
    mut i: SyntaxIn,
    mut colon: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let colon_stops = caller_stops & !crate::lexical::stops::STOP_COLON;
    let mut at_boundary = is_record_field_slot_boundary(&colon, baseline, colon_stops);
    let recovered =
        !at_boundary && !is_record_colon_kind(token_kind(&colon)) && !is_type_nud(&colon);
    if recovered {
        colon.emit_all_remaining_leading(&mut *i.state);
        (colon, item_origin, line_entry) = retry_record_field_slot_normalized(
            i.rb(),
            TypeRole::RecordFieldColon,
            colon,
            baseline,
            colon_stops,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        at_boundary = is_record_field_slot_boundary(&colon, baseline, colon_stops);
    }
    if at_boundary {
        if !recovered {
            emit_record_field_missing(&mut i, TypeRole::RecordFieldColon, &colon, item_origin);
        }
        return complete(handoff(colon), line_entry);
    }
    if is_record_colon_kind(token_kind(&colon)) {
        emit_token_item(&mut i, colon);
        return type_record_rhs_normalized(
            i,
            baseline,
            type_ml,
            outer_closes,
            caller_stops,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    debug_assert!(is_type_nud(&colon));
    colon.emit_all_remaining_leading(&mut *i.state);
    if !recovered {
        emit_record_field_missing(&mut i, TypeRole::RecordFieldColon, &colon, item_origin);
    }
    type_expr_from_nud_normalized(
        i,
        colon,
        baseline,
        type_ml,
        Some(TypeApplyBoundary::NamedRecord(baseline)),
        true,
        outer_closes,
        caller_stops,
        TypeOuterBoundary::NONE,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn type_record_rhs_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let (mut rhs, mut item_origin, mut line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
        ambient,
    );
    if is_record_field_slot_boundary(&rhs, baseline, caller_stops) {
        emit_record_field_missing(&mut i, TypeRole::RecordFieldType, &rhs, item_origin);
        return complete(handoff(rhs), line_entry);
    }
    if !is_type_nud(&rhs) {
        rhs.emit_all_remaining_leading(&mut *i.state);
        (rhs, item_origin, line_entry) = retry_record_field_slot_normalized(
            i.rb(),
            TypeRole::RecordFieldType,
            rhs,
            baseline,
            caller_stops,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        if is_record_field_slot_boundary(&rhs, baseline, caller_stops) {
            return complete(handoff(rhs), line_entry);
        }
    }
    debug_assert!(is_type_nud(&rhs));
    rhs.emit_all_remaining_leading(&mut *i.state);
    type_expr_from_nud_normalized(
        i,
        rhs,
        baseline,
        type_ml,
        Some(TypeApplyBoundary::NamedRecord(baseline)),
        true,
        outer_closes,
        caller_stops,
        TypeOuterBoundary::NONE,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

fn is_record_field_slot_boundary(item: &Item, baseline: usize, caller_stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || !type_chain_trivia(item.leading_view(), baseline)
        || is_type_record_field_boundary(item)
        || is_type_caller_boundary(item, caller_stops)
}

#[allow(clippy::too_many_arguments)]
fn retry_record_field_slot_normalized(
    i: SyntaxIn,
    role: TypeRole,
    mut item: Item,
    baseline: usize,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> (Item, usize, LineEntry) {
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(item_origin).recovery_range().start;
            let end = loop {
                let kind = type_recovery_error_syntax_kind(&item);
                let end = run
                    .emit_item_as(item, item_origin, kind)
                    .recovery_range()
                    .end;
                (item, item_origin, line_entry) =
                    type_nud_item_with_pipe_lexical_normalized_in_error_run(
                        run,
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                        ambient,
                    );
                if is_record_field_slot_boundary(&item, baseline, caller_stops)
                    || is_type_nud(&item)
                    || (role == TypeRole::RecordFieldColon
                        && is_record_colon_kind(token_kind(&item)))
                {
                    break end;
                }
            };
            run.append_unexpected(UnexpectedSyntax::Token {
                range: start..end,
                category: UnexpectedCategory::OtherCharacter,
            });
            (item, item_origin, line_entry)
        },
        |range, unexpected| {
            record_field_recovery_draft(role, RecoveryKind::Error, range, unexpected)
        },
    )
}

fn emit_record_field_missing(i: &mut SyntaxIn, role: TypeRole, item: &Item, item_origin: usize) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(item_origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        record_field_recovery_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn record_field_recovery_draft(
    role: TypeRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    record_recovery_draft(GrammarRole::Type(role), kind, range, unexpected)
}

fn record_recovery_draft(
    role: GrammarRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected = match role {
        GrammarRole::Type(TypeRole::RecordField | TypeRole::RecordFieldName) => {
            ExpectedSyntax::Identifier
        }
        GrammarRole::Type(TypeRole::RecordFieldColon) => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon)
        }
        GrammarRole::Type(TypeRole::RecordFieldType) => ExpectedSyntax::TypeExpression,
        GrammarRole::Type(TypeRole::RecordFieldSeparator) => {
            ExpectedSyntax::DelimitedSequenceSeparator
        }
        GrammarRole::ClosingDelimiter {
            owner: ConstructRole::NamedRecordType,
            delimiter: Delimiter::Brace,
        } => ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
        _ => unreachable!("only named-record recovery slots use this draft"),
    };
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

fn is_record_colon_kind(kind: Option<TokenKind>) -> bool {
    matches!(
        kind,
        Some(TokenKind::Colon | TokenKind::PolymorphicVariantColon)
    )
}

fn is_type_record_field_start(item: &Item) -> bool {
    is_type_record_field_name(item) || is_record_colon_kind(token_kind(item))
}

fn record_boundary_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    missing_field: bool,
    item_origin: usize,
    line_entry: LineEntry,
) -> NormalizedExit {
    if item.payload_view().is_eof() && type_chain_trivia(item.leading_view(), baseline) {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    if missing_field {
        emit_record_field_missing(&mut i, TypeRole::RecordField, &item, item_origin);
    }
    i.state.start_node(SyntaxKind::NamedRecordTypeClose.into());
    emit_record_close_missing(&mut i, &item, item_origin);
    i.state.finish_node();
    complete(handoff(item), line_entry)
}

fn emit_record_close_missing(i: &mut SyntaxIn, item: &Item, item_origin: usize) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(item_origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        record_recovery_draft(
            record_close_role(),
            RecoveryKind::Missing,
            range,
            Arc::from([]),
        )
    });
}

fn record_close_role() -> GrammarRole {
    GrammarRole::ClosingDelimiter {
        owner: ConstructRole::NamedRecordType,
        delimiter: Delimiter::Brace,
    }
}

fn observe_type_item<'source>(
    mut i: LexIn,
    source: &'source str,
    source_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
) -> Option<(&'source str, usize, LineEntry, Option<Token>, Option<usize>)> {
    let TriviaObservation::Visible(visible) =
        observe_fenced_trivia(source, source_origin, line_entry, fence)
    else {
        return None;
    };
    if visible.source.is_empty() {
        return None;
    }

    let payload_origin = source_origin + source.len() - visible.source.len();
    let mut suffix = visible.source;
    let mut lex = chasa_recover::In::new(&mut suffix, i.recovery(), ());
    let accepted = if pipe_lexical && let Some(pipe) = lex.rb().token(scan_exact_pipe) {
        AcceptedPayload {
            payload: CurrentPayload::Token(pipe),
            next_line_entry: LineEntry::InLine,
        }
    } else {
        scan_type_nud_payload(lex, visible.present, payload_origin, fence)?
    };
    let token = match accepted.payload {
        CurrentPayload::Token(token) => Some(token),
        CurrentPayload::Operator(_) => None,
    };
    let next_origin = payload_origin + visible.source.len() - suffix.len();
    Some((
        suffix,
        next_origin,
        accepted.next_line_entry,
        token,
        visible.indentation,
    ))
}
