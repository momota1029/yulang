//! Type delimiter recovery shared by groups, calls, effect rows, and bracket rows.

use super::super::ambient_claim::AmbientClaimContext;
use std::sync::Arc;

use reborrow_generic::Reborrow as _;

use crate::{
    session::{
        ConstructRole, Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation, TypeRole,
        UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use super::super::{
    RewriteIn, Stops,
    current_item::LineEntry,
    driver::{
        Either, NormalizedExit, advanced_origin, complete, handoff, suffix_marker, token_kind,
    },
    emit::{
        CallArgumentRetryLeadingSeal, emit_missing, emit_recovery_error_item,
        emit_recovery_error_run, emit_recovery_missing, emit_token_item,
    },
    item::{Item, LeadingTrivia, TokenKind},
    output::RecoveryDraft,
    yumark::FenceBoundary,
};
use super::{
    TypeMlContext, TypeOuterBoundary, is_type_caller_boundary, is_type_deeper_newline,
    is_type_implicit_boundary, is_type_mismatched_close, is_type_nud, is_type_outer_boundary,
    is_type_outer_close, is_type_separator, missing_bracket_row_close, missing_type_close,
    missing_type_item, type_chain_trivia, type_delimited_baseline, type_expr_from_nud_normalized,
    type_nud_item_with_pipe_lexical_normalized, with_type_outer_close,
};

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum TypeDelimitedOwner {
    Call,
    ParenthesizedGroup,
    EffectRow,
    BracketRow,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn type_delimited_normalized(
    mut i: RewriteIn,
    close: TokenKind,
    incoming_baseline: usize,
    owner: TypeDelimitedOwner,
    type_ml: TypeMlContext,
    call_outer_boundary: TypeOuterBoundary,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    debug_assert!(
        owner == TypeDelimitedOwner::Call || call_outer_boundary == TypeOuterBoundary::NONE
    );
    let item_type_ml = match owner {
        TypeDelimitedOwner::Call => type_ml,
        TypeDelimitedOwner::ParenthesizedGroup => type_ml.parenthesized_item(),
        TypeDelimitedOwner::EffectRow | TypeDelimitedOwner::BracketRow => type_ml.dormant(),
    };
    let inherited_separator = match owner {
        TypeDelimitedOwner::Call => type_ml.stops_tail(),
        TypeDelimitedOwner::ParenthesizedGroup => item_type_ml.stops_tail(),
        TypeDelimitedOwner::EffectRow | TypeDelimitedOwner::BracketRow => false,
    };
    let mut call_item_pending = owner == TypeDelimitedOwner::Call;
    let (mut item, next_origin, next_line_entry) = type_nud_item_with_pipe_lexical_normalized(
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

    if item.payload_view().is_boundary() {
        if matches!(
            owner,
            TypeDelimitedOwner::Call | TypeDelimitedOwner::BracketRow
        ) {
            emit_delimited_item_missing(&mut i, owner, &item, item_origin);
        }
        emit_delimited_close_missing(&mut i, owner, &item, item_origin);
        return complete(handoff(item), line_entry);
    }
    if emit_horizontal_delimited_boundary(
        &mut i,
        &mut item,
        close,
        owner,
        true,
        caller_stops,
        call_outer_boundary,
        outer_closes,
        item_origin,
    ) {
        return complete(handoff(item), line_entry);
    }
    if token_kind(&item) == Some(close) || !is_explicit_type_caller_close(&item, caller_stops) {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    if owner == TypeDelimitedOwner::BracketRow && item.payload_view().is_eof() {
        item = missing_type_item(i.rb(), item);
        return complete(missing_bracket_row_close(i, item, baseline), line_entry);
    }

    loop {
        if item.payload_view().is_boundary() {
            emit_delimited_close_missing(&mut i, owner, &item, item_origin);
            return complete(handoff(item), line_entry);
        }
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return complete(Ok(()), line_entry);
        }
        if owner == TypeDelimitedOwner::ParenthesizedGroup && is_type_mismatched_close(&item, close)
        {
            emit_parenthesized_mismatched_close_missing(
                &mut i,
                &item,
                outer_closes,
                caller_stops,
                item_origin,
            );
            return complete(handoff(item), line_entry);
        }
        if is_delimited_boundary(
            &item,
            owner,
            caller_stops,
            call_outer_boundary,
            outer_closes,
        ) && (owner == TypeDelimitedOwner::Call || !is_type_nud(&item))
        {
            if call_item_pending || owner == TypeDelimitedOwner::BracketRow {
                emit_delimited_item_missing(&mut i, owner, &item, item_origin);
            }
            emit_delimited_close_missing(&mut i, owner, &item, item_origin);
            return complete(handoff(item), line_entry);
        }
        if item.payload_view().is_eof() {
            if call_item_pending {
                item = missing_delimited_item(i.rb(), item, owner, item_origin);
            }
            let exit = missing_delimited_close(i, item, owner, baseline, item_origin);
            return complete(exit, line_entry);
        }
        if owner == TypeDelimitedOwner::Call && is_type_mismatched_close(&item, close) {
            return retry_type_call_close_normalized(
                i,
                item,
                close,
                baseline,
                caller_stops,
                outer_closes,
                call_outer_boundary,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
                ambient,
            );
        }
        if owner == TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&item, close) {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_missing(&mut i, LeadingTrivia::default());
            return retry_bracket_row_close_normalized(
                i,
                item,
                close,
                baseline,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
                ambient,
            );
        }
        if is_type_separator(&item) {
            item = missing_delimited_item(i.rb(), item, owner, item_origin);
            emit_token_item(&mut i, item);
            (item, item_origin, line_entry) = match type_after_separator_normalized(
                i.rb(),
                close,
                owner,
                baseline,
                caller_stops,
                outer_closes,
                call_outer_boundary,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
                ambient,
            ) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            call_item_pending = owner == TypeDelimitedOwner::Call;
            continue;
        }
        if !is_type_nud(&item) {
            if owner != TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&item, close) {
                return complete(handoff(item), line_entry);
            }
            call_item_pending = false;
            (item, item_origin, line_entry) = match retry_type_delimited_item_normalized(
                i.rb(),
                item,
                close,
                owner,
                baseline,
                caller_stops,
                outer_closes,
                call_outer_boundary,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
                ambient,
            ) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }

        call_item_pending = false;
        let entry = suffix_marker(i.rb());
        let exit = type_expr_from_nud_normalized(
            i.rb(),
            item,
            baseline,
            item_type_ml,
            None,
            true,
            with_type_outer_close(outer_closes, close),
            caller_stops,
            call_outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        item_origin = advanced_origin(item_origin, entry, i.rb());
        item = match exit {
            NormalizedExit::Complete(Ok(()), next_line_entry) => {
                line_entry = next_line_entry;
                let (mut next, next_origin, next_line_entry) =
                    type_nud_item_with_pipe_lexical_normalized(
                        i.rb(),
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                        ambient,
                    );
                item_origin = next_origin;
                line_entry = next_line_entry;
                if emit_horizontal_delimited_boundary(
                    &mut i,
                    &mut next,
                    close,
                    owner,
                    false,
                    caller_stops,
                    call_outer_boundary,
                    outer_closes,
                    item_origin,
                ) {
                    return complete(handoff(next), line_entry);
                }
                next
            }
            NormalizedExit::Complete(Err(Either::Left(mut next)), next_line_entry) => {
                line_entry = next_line_entry;
                if next.payload_view().is_boundary() {
                    emit_delimited_close_missing(&mut i, owner, &next, item_origin);
                    return complete(handoff(next), line_entry);
                }
                if emit_horizontal_delimited_boundary(
                    &mut i,
                    &mut next,
                    close,
                    owner,
                    false,
                    caller_stops,
                    call_outer_boundary,
                    outer_closes,
                    item_origin,
                ) {
                    return complete(handoff(next), line_entry);
                }
                if token_kind(&next) == Some(close) {
                    emit_token_item(&mut i, next);
                    return complete(Ok(()), line_entry);
                }
                if owner == TypeDelimitedOwner::ParenthesizedGroup
                    && is_type_mismatched_close(&next, close)
                {
                    emit_parenthesized_mismatched_close_missing(
                        &mut i,
                        &next,
                        outer_closes,
                        caller_stops,
                        item_origin,
                    );
                    return complete(handoff(next), line_entry);
                }
                if is_delimited_boundary(
                    &next,
                    owner,
                    caller_stops,
                    call_outer_boundary,
                    outer_closes,
                ) {
                    emit_delimited_close_missing(&mut i, owner, &next, item_origin);
                    return complete(handoff(next), line_entry);
                }
                if owner == TypeDelimitedOwner::Call && is_type_mismatched_close(&next, close) {
                    return retry_type_call_close_normalized(
                        i,
                        next,
                        close,
                        baseline,
                        caller_stops,
                        outer_closes,
                        call_outer_boundary,
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                        ambient,
                    );
                }
                if is_type_separator(&next) {
                    emit_token_item(&mut i, next);
                    match type_after_separator_normalized(
                        i.rb(),
                        close,
                        owner,
                        baseline,
                        caller_stops,
                        outer_closes,
                        call_outer_boundary,
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                        ambient,
                    ) {
                        Ok((next, next_origin, next_line_entry)) => {
                            item_origin = next_origin;
                            line_entry = next_line_entry;
                            next
                        }
                        Err(exit) => return exit,
                    }
                } else if pipe_lexical && token_kind(&next) == Some(TokenKind::Pipe) {
                    match retry_type_delimited_item_normalized(
                        i.rb(),
                        next,
                        close,
                        owner,
                        baseline,
                        caller_stops,
                        outer_closes,
                        call_outer_boundary,
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                        ambient,
                    ) {
                        Ok((next, next_origin, next_line_entry)) => {
                            item_origin = next_origin;
                            line_entry = next_line_entry;
                            next
                        }
                        Err(exit) => return exit,
                    }
                } else if owner == TypeDelimitedOwner::BracketRow
                    && is_type_mismatched_close(&next, close)
                {
                    let mut next = next;
                    next.emit_all_remaining_leading(&mut *i.state);
                    return retry_bracket_row_close_normalized(
                        i,
                        next,
                        close,
                        baseline,
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                        ambient,
                    );
                } else if owner == TypeDelimitedOwner::BracketRow
                    && is_type_deeper_newline(baseline, next.leading_view())
                    && is_type_nud(&next)
                {
                    emit_missing(&mut i, LeadingTrivia::default());
                    let mut next = next;
                    next.emit_all_remaining_leading(&mut *i.state);
                    next
                } else if owner == TypeDelimitedOwner::BracketRow
                    && type_chain_trivia(next.leading_view(), baseline)
                    && !is_type_deeper_newline(baseline, next.leading_view())
                    && !is_type_nud(&next)
                {
                    match retry_type_delimited_item_normalized(
                        i.rb(),
                        next,
                        close,
                        TypeDelimitedOwner::BracketRow,
                        baseline,
                        caller_stops,
                        outer_closes,
                        call_outer_boundary,
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                        ambient,
                    ) {
                        Ok((next, next_origin, next_line_entry)) => {
                            item_origin = next_origin;
                            line_entry = next_line_entry;
                            next
                        }
                        Err(exit) => return exit,
                    }
                } else if owner == TypeDelimitedOwner::BracketRow
                    && is_type_deeper_newline(baseline, next.leading_view())
                {
                    emit_missing(&mut i, LeadingTrivia::default());
                    return complete(handoff(next), line_entry);
                } else if is_type_implicit_boundary(baseline, next.leading_view()) {
                    let mut next = next;
                    next.emit_all_remaining_leading(&mut *i.state);
                    next
                } else if owner == TypeDelimitedOwner::ParenthesizedGroup
                    && next.leading_view().is_grammar_empty()
                    && is_type_nud(&next)
                {
                    emit_inherited_separator_missing(&mut i, owner, &next, item_origin);
                    next
                } else if inherited_separator
                    && !next.leading_view().is_grammar_empty()
                    && (!next.leading_view().contains_line_break()
                        || is_type_deeper_newline(baseline, next.leading_view()))
                    && is_type_nud(&next)
                {
                    let mut next = next;
                    next.emit_all_remaining_leading(&mut *i.state);
                    emit_inherited_separator_missing(&mut i, owner, &next, item_origin);
                    next
                } else {
                    return complete(handoff(next), line_entry);
                }
            }
            NormalizedExit::Complete(Err(Either::Right(end)), next_line_entry) => {
                let exit = missing_delimited_close(i, end.item, owner, baseline, item_origin);
                return complete(exit, next_line_entry);
            }
            _ => unreachable!("normalized Type owners do not defer"),
        };
    }
}

/// The accepted owner keeps a horizontal gap at a raw caller/outer boundary.
/// Fresh slots additionally miss their item; completed slots only miss a close.
#[allow(clippy::too_many_arguments)]
fn emit_horizontal_delimited_boundary(
    i: &mut RewriteIn,
    item: &mut Item,
    close: TokenKind,
    owner: TypeDelimitedOwner,
    fresh_slot: bool,
    caller_stops: Stops,
    call_outer_boundary: TypeOuterBoundary,
    outer_closes: u8,
    item_origin: usize,
) -> bool {
    if owner == TypeDelimitedOwner::BracketRow
        || item.payload_view().is_boundary()
        || token_kind(item) == Some(close)
        || (fresh_slot && owner != TypeDelimitedOwner::Call && is_type_nud(item))
        || !(is_delimited_boundary(item, owner, caller_stops, call_outer_boundary, outer_closes)
            || is_type_outer_close(item, outer_closes))
    {
        return false;
    }
    // The lexer coalesces a space/tab run into one Whitespace part. Requiring
    // that single remaining part excludes comments, newlines and fence carriers.
    let leading = item.leading_view();
    if leading.remaining_physical_parts() != 1 || !leading.has_ordinary_horizontal_gap() {
        return false;
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if fresh_slot {
        emit_delimited_item_missing(i, owner, item, item_origin);
    }
    if owner == TypeDelimitedOwner::ParenthesizedGroup && is_type_mismatched_close(item, close) {
        emit_parenthesized_mismatched_close_missing(
            i,
            item,
            outer_closes,
            caller_stops,
            item_origin,
        );
    } else {
        emit_delimited_close_missing(i, owner, item, item_origin);
    }
    true
}

#[allow(clippy::too_many_arguments)]
fn retry_type_delimited_item_normalized(
    mut i: RewriteIn,
    mut item: Item,
    close: TokenKind,
    owner: TypeDelimitedOwner,
    baseline: usize,
    caller_stops: Stops,
    outer_closes: u8,
    call_outer_boundary: TypeOuterBoundary,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
    ambient: AmbientClaimContext<'_>,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
    if owner == TypeDelimitedOwner::Call {
        return retry_type_call_argument_normalized(
            i,
            item,
            close,
            baseline,
            caller_stops,
            outer_closes,
            call_outer_boundary,
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        );
    }
    debug_assert!(!item.payload_view().is_boundary());
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            emit_delimited_close_missing(&mut i, owner, &item, item_origin);
            return Err(complete(handoff(item), line_entry));
        }
        if token_kind(&item) == Some(close) {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return Err(complete(Ok(()), line_entry));
        }
        if owner == TypeDelimitedOwner::ParenthesizedGroup && is_type_mismatched_close(&item, close)
        {
            i.state.finish_node();
            emit_parenthesized_mismatched_close_missing(
                &mut i,
                &item,
                outer_closes,
                caller_stops,
                item_origin,
            );
            return Err(complete(handoff(item), line_entry));
        }
        if is_delimited_boundary(
            &item,
            owner,
            caller_stops,
            call_outer_boundary,
            outer_closes,
        ) {
            i.state.finish_node();
            emit_delimited_close_missing(&mut i, owner, &item, item_origin);
            return Err(complete(handoff(item), line_entry));
        }
        if is_type_separator(&item) {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return type_after_separator_normalized(
                i,
                close,
                owner,
                baseline,
                caller_stops,
                outer_closes,
                call_outer_boundary,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
                ambient,
            );
        }
        if is_type_implicit_boundary(baseline, item.leading_view()) {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            return Ok((item, item_origin, line_entry));
        }
        if item.payload_view().is_eof() {
            i.state.finish_node();
            let exit = missing_delimited_close(i, item, owner, baseline, item_origin);
            return Err(complete(exit, line_entry));
        }
        if owner != TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&item, close) {
            i.state.finish_node();
            return Err(complete(handoff(item), line_entry));
        }
        item.emit_all_remaining_leading(&mut *i.state);
        if is_type_nud(&item) {
            i.state.finish_node();
            return Ok((item, item_origin, line_entry));
        }
        if is_type_mismatched_close(&item, close) {
            i.state.finish_node();
            return Err(retry_bracket_row_close_normalized(
                i,
                item,
                close,
                baseline,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
                ambient,
            ));
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn retry_type_call_argument_normalized(
    mut i: RewriteIn,
    mut item: Item,
    close: TokenKind,
    baseline: usize,
    caller_stops: Stops,
    outer_closes: u8,
    call_outer_boundary: TypeOuterBoundary,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
    ambient: AmbientClaimContext<'_>,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
    debug_assert!(!item.payload_view().is_boundary());
    let mut error_extent: Option<std::ops::Range<usize>> = None;
    (item, item_origin, line_entry) = emit_recovery_error_run(
        i.rb(),
        |run| loop {
            let extent = run.emit_item_as(item, item_origin, SyntaxKind::Unknown);
            let item_extent = extent.recovery_range();
            if let Some(error_extent) = &mut error_extent {
                assert_eq!(
                    error_extent.end, item_extent.start,
                    "a CallArgument malformed run remains physically contiguous"
                );
                error_extent.end = item_extent.end;
            } else {
                error_extent = Some(item_extent);
            }
            (item, item_origin, line_entry) =
                super::type_nud_item_with_pipe_lexical_normalized_in_error_run(
                    run,
                    item_origin,
                    line_entry,
                    fence,
                    pipe_lexical,
                    ambient,
                );

            let boundary = item.payload_view().is_boundary()
                || token_kind(&item) == Some(close)
                || is_delimited_boundary(
                    &item,
                    TypeDelimitedOwner::Call,
                    caller_stops,
                    call_outer_boundary,
                    outer_closes,
                )
                || is_type_separator(&item)
                || item.payload_view().is_eof()
                || is_type_mismatched_close(&item, close);
            if boundary || is_type_nud(&item) {
                let sealed = !boundary
                    && run.seal_call_argument_retry_leading_prefix(
                        &mut item,
                        item_origin,
                        UnexpectedCategory::OtherCharacter,
                    ) == CallArgumentRetryLeadingSeal::Sealed;
                if !sealed {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: error_extent
                            .clone()
                            .expect("a CallArgument Error emits a malformed Item"),
                        category: UnexpectedCategory::OtherCharacter,
                    });
                }
                return (item, item_origin, line_entry);
            }
        },
        |range, unexpected| {
            super::type_expression_error_draft(TypeRole::CallArgument, range, unexpected)
        },
    );

    if item.payload_view().is_boundary() {
        emit_delimited_close_missing(&mut i, TypeDelimitedOwner::Call, &item, item_origin);
        return Err(complete(handoff(item), line_entry));
    }
    if token_kind(&item) == Some(close) {
        emit_token_item(&mut i, item);
        return Err(complete(Ok(()), line_entry));
    }
    if is_delimited_boundary(
        &item,
        TypeDelimitedOwner::Call,
        caller_stops,
        call_outer_boundary,
        outer_closes,
    ) {
        emit_delimited_close_missing(&mut i, TypeDelimitedOwner::Call, &item, item_origin);
        return Err(complete(handoff(item), line_entry));
    }
    if is_type_separator(&item) {
        emit_token_item(&mut i, item);
        return type_after_separator_normalized(
            i,
            close,
            TypeDelimitedOwner::Call,
            baseline,
            caller_stops,
            outer_closes,
            call_outer_boundary,
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        );
    }
    if item.payload_view().is_eof() {
        let exit =
            missing_delimited_close(i, item, TypeDelimitedOwner::Call, baseline, item_origin);
        return Err(complete(exit, line_entry));
    }
    if is_type_mismatched_close(&item, close) {
        return Err(retry_type_call_close_normalized(
            i,
            item,
            close,
            baseline,
            caller_stops,
            outer_closes,
            call_outer_boundary,
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        ));
    }
    debug_assert!(is_type_nud(&item));
    item.emit_all_remaining_leading(&mut *i.state);
    Ok((item, item_origin, line_entry))
}

#[allow(clippy::too_many_arguments)]
fn retry_type_call_close_normalized(
    mut i: RewriteIn,
    mut item: Item,
    close: TokenKind,
    baseline: usize,
    caller_stops: Stops,
    outer_closes: u8,
    call_outer_boundary: TypeOuterBoundary,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    debug_assert!(is_type_mismatched_close(&item, close));
    loop {
        item.emit_all_remaining_leading(&mut *i.state);
        let range = item.extent(item_origin).recovery_range();
        let unexpected = UnexpectedSyntax::Token {
            range: range.clone(),
            category: UnexpectedCategory::OtherCharacter,
        };
        emit_recovery_error_item(
            i.rb(),
            item,
            item_origin,
            SyntaxKind::Unknown,
            unexpected,
            |range, unexpected| type_call_close_recovery_draft(range, unexpected),
        );
        (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        );
        if item.payload_view().is_boundary() {
            emit_delimited_close_missing(&mut i, TypeDelimitedOwner::Call, &item, item_origin);
            return complete(handoff(item), line_entry);
        }
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return complete(Ok(()), line_entry);
        }
        if is_delimited_boundary(
            &item,
            TypeDelimitedOwner::Call,
            caller_stops,
            call_outer_boundary,
            outer_closes,
        ) {
            emit_delimited_close_missing(&mut i, TypeDelimitedOwner::Call, &item, item_origin);
            return complete(handoff(item), line_entry);
        }
        if item.payload_view().is_eof() {
            let exit =
                missing_delimited_close(i, item, TypeDelimitedOwner::Call, baseline, item_origin);
            return complete(exit, line_entry);
        }
        // Once a local mismatched close transfers control to the Call close
        // slot, every non-boundary Item before the actual close is malformed
        // close content owned by that slot.  Keep advancing here so an
        // ordinary malformed Item cannot manufacture an early Missing close
        // and escape to the outer Type parser.
    }
}

fn retry_bracket_row_close_normalized(
    mut i: RewriteIn,
    mut item: Item,
    close: TokenKind,
    baseline: usize,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    debug_assert!(!item.payload_view().is_boundary());
    loop {
        i.state.start_node(SyntaxKind::Error.into());
        emit_token_item(&mut i, item);
        i.state.finish_node();
        (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        );
        if item.payload_view().is_boundary() {
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(item), line_entry);
        }
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return complete(Ok(()), line_entry);
        }
        if item.payload_view().is_eof() {
            return complete(missing_bracket_row_close(i, item, baseline), line_entry);
        }
        if !is_type_mismatched_close(&item, close) {
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(item), line_entry);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn type_after_separator_normalized(
    mut i: RewriteIn,
    close: TokenKind,
    owner: TypeDelimitedOwner,
    baseline: usize,
    caller_stops: Stops,
    outer_closes: u8,
    call_outer_boundary: TypeOuterBoundary,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
    ambient: AmbientClaimContext<'_>,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
    let (mut next, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
        ambient,
    );
    if next.payload_view().is_boundary() {
        emit_delimited_item_missing(&mut i, owner, &next, item_origin);
        emit_delimited_close_missing(&mut i, owner, &next, item_origin);
        return Err(complete(handoff(next), line_entry));
    }
    if emit_horizontal_delimited_boundary(
        &mut i,
        &mut next,
        close,
        owner,
        true,
        caller_stops,
        call_outer_boundary,
        outer_closes,
        item_origin,
    ) {
        return Err(complete(handoff(next), line_entry));
    }
    if token_kind(&next) == Some(close) {
        next.emit_all_remaining_leading(&mut *i.state);
        emit_token_item(&mut i, next);
        return Err(complete(Ok(()), line_entry));
    }
    if owner == TypeDelimitedOwner::ParenthesizedGroup && is_type_mismatched_close(&next, close) {
        if !is_type_outer_close(&next, outer_closes)
            && is_explicit_type_caller_close(&next, caller_stops)
        {
            emit_missing(&mut i, LeadingTrivia::default());
        }
        emit_parenthesized_mismatched_close_missing(
            &mut i,
            &next,
            outer_closes,
            caller_stops,
            item_origin,
        );
        return Err(complete(handoff(next), line_entry));
    }
    if is_delimited_boundary(
        &next,
        owner,
        caller_stops,
        call_outer_boundary,
        outer_closes,
    ) && (owner == TypeDelimitedOwner::Call || !is_type_nud(&next))
    {
        emit_delimited_item_missing(&mut i, owner, &next, item_origin);
        emit_delimited_close_missing(&mut i, owner, &next, item_origin);
        return Err(complete(handoff(next), line_entry));
    }
    if next.payload_view().is_eof() {
        next = missing_delimited_item(i.rb(), next, owner, item_origin);
        return Err(complete(
            missing_delimited_close(i, next, owner, baseline, item_origin),
            line_entry,
        ));
    }
    if owner == TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&next, close) {
        next = missing_type_item(i.rb(), next);
        return Err(retry_bracket_row_close_normalized(
            i,
            next,
            close,
            baseline,
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        ));
    }
    if is_type_nud(&next) {
        next.emit_all_remaining_leading(&mut *i.state);
    }
    Ok((next, item_origin, line_entry))
}

fn missing_delimited_close(
    mut i: RewriteIn,
    mut item: Item,
    owner: TypeDelimitedOwner,
    baseline: usize,
    item_origin: usize,
) -> super::super::driver::TailExit {
    match owner {
        TypeDelimitedOwner::ParenthesizedGroup => {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_delimited_close_missing(&mut i, owner, &item, item_origin);
            handoff(item)
        }
        TypeDelimitedOwner::Call => {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_delimited_close_missing(&mut i, owner, &item, item_origin);
            handoff(item)
        }
        TypeDelimitedOwner::BracketRow => missing_bracket_row_close(i, item, baseline),
        TypeDelimitedOwner::EffectRow => missing_type_close(i, item),
    }
}

fn missing_delimited_item(
    mut i: RewriteIn,
    mut item: Item,
    owner: TypeDelimitedOwner,
    item_origin: usize,
) -> Item {
    item.emit_all_remaining_leading(&mut *i.state);
    emit_delimited_item_missing(&mut i, owner, &item, item_origin);
    item
}

fn emit_delimited_item_missing(
    i: &mut RewriteIn,
    owner: TypeDelimitedOwner,
    item: &Item,
    item_origin: usize,
) {
    if owner != TypeDelimitedOwner::Call {
        emit_missing(i, LeadingTrivia::default());
        return;
    }
    let at = delimited_missing_anchor(item, item_origin);
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        super::type_expression_missing_draft(TypeRole::CallArgument, range)
    });
}

fn emit_inherited_separator_missing(
    i: &mut RewriteIn,
    owner: TypeDelimitedOwner,
    item: &Item,
    item_origin: usize,
) {
    let role = match owner {
        TypeDelimitedOwner::Call => TypeRole::CallArgumentSeparator,
        TypeDelimitedOwner::ParenthesizedGroup => TypeRole::ParenthesizedSeparator,
        TypeDelimitedOwner::EffectRow | TypeDelimitedOwner::BracketRow => {
            unreachable!("only inherited Type-ML separator owners reach this branch")
        }
    };
    let at = delimited_missing_anchor(item, item_origin);
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        let role = GrammarRole::Type(role);
        RecoveryDraft::new(
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::DelimitedSequenceSeparator,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
}

fn delimited_missing_anchor(item: &Item, item_origin: usize) -> usize {
    item.payload_view().pending_boundary().map_or_else(
        || item.extent(item_origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    )
}

fn is_delimited_boundary(
    item: &Item,
    owner: TypeDelimitedOwner,
    caller_stops: Stops,
    call_outer_boundary: TypeOuterBoundary,
    outer_closes: u8,
) -> bool {
    is_type_caller_boundary(item, caller_stops)
        || (owner == TypeDelimitedOwner::Call
            && (is_type_outer_boundary(item, call_outer_boundary)
                || is_type_outer_close(item, outer_closes)))
}

fn emit_delimited_close_missing(
    i: &mut RewriteIn,
    owner: TypeDelimitedOwner,
    item: &Item,
    item_origin: usize,
) {
    if !matches!(
        owner,
        TypeDelimitedOwner::Call | TypeDelimitedOwner::ParenthesizedGroup
    ) {
        emit_missing(i, LeadingTrivia::default());
        return;
    }
    let at = if owner == TypeDelimitedOwner::Call {
        delimited_missing_anchor(item, item_origin)
    } else {
        item.extent(item_origin).recovery_range().start
    };
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        let role = GrammarRole::ClosingDelimiter {
            owner: match owner {
                TypeDelimitedOwner::Call => ConstructRole::TypeCall,
                TypeDelimitedOwner::ParenthesizedGroup => ConstructRole::ParenthesizedTypeGroup,
                TypeDelimitedOwner::EffectRow | TypeDelimitedOwner::BracketRow => {
                    unreachable!("only typed delimited close owners reach this branch")
                }
            },
            delimiter: Delimiter::Parenthesis,
        };
        RecoveryDraft::new(
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Close(
                    Delimiter::Parenthesis,
                )),
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
}

fn type_call_close_recovery_draft(
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let role = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::TypeCall,
        delimiter: Delimiter::Parenthesis,
    };
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        RecoveryKind::Error,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Close(
                Delimiter::Parenthesis,
            )),
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

fn emit_parenthesized_mismatched_close_missing(
    i: &mut RewriteIn,
    item: &Item,
    outer_closes: u8,
    caller_stops: Stops,
    item_origin: usize,
) {
    if is_type_outer_close(item, outer_closes) {
        emit_delimited_close_missing(i, TypeDelimitedOwner::ParenthesizedGroup, item, item_origin);
    } else if is_explicit_type_caller_close(item, caller_stops) {
        emit_missing(i, LeadingTrivia::default());
    }
}

pub(super) fn is_explicit_type_caller_close(item: &Item, caller_stops: Stops) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
    ) && is_type_caller_boundary(item, caller_stops)
}
