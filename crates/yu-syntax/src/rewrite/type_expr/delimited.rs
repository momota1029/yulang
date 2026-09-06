//! Type delimiter recovery shared by groups, calls, effect rows, and bracket rows.

use std::sync::Arc;

use reborrow_generic::Reborrow as _;

use crate::{
    session::{
        ConstructRole, Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
    },
    syntax_kind::SyntaxKind,
};

use super::super::{
    RewriteIn, Stops,
    current_item::LineEntry,
    driver::{
        Either, NormalizedExit, advanced_origin, complete, handoff, suffix_marker, token_kind,
    },
    emit::{emit_missing, emit_recovery_missing, emit_token_item},
    item::{Item, LeadingTrivia, TokenKind},
    output::RecoveryDraft,
    yumark::FenceBoundary,
};
use super::{
    TypeOuterBoundary, is_type_caller_boundary, is_type_deeper_newline, is_type_implicit_boundary,
    is_type_mismatched_close, is_type_nud, is_type_outer_close, is_type_separator,
    missing_bracket_row_close, missing_type_close, missing_type_item, type_chain_trivia,
    type_delimited_baseline, type_expr_from_nud_normalized,
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
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (mut item, next_origin, next_line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
    );
    item_origin = next_origin;
    line_entry = next_line_entry;
    let baseline = type_delimited_baseline(incoming_baseline, item.leading_view());

    if item.payload_view().is_boundary() {
        if owner == TypeDelimitedOwner::BracketRow {
            emit_missing(&mut i, LeadingTrivia::default());
        }
        emit_delimited_close_missing(&mut i, owner, &item, item_origin);
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
        if is_type_caller_boundary(&item, caller_stops) && !is_type_nud(&item) {
            if owner == TypeDelimitedOwner::BracketRow {
                emit_missing(&mut i, LeadingTrivia::default());
            }
            emit_delimited_close_missing(&mut i, owner, &item, item_origin);
            return complete(handoff(item), line_entry);
        }
        if item.payload_view().is_eof() {
            let exit = missing_delimited_close(i, item, owner, baseline, item_origin);
            return complete(exit, line_entry);
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
            );
        }
        if is_type_separator(&item) {
            item = missing_type_item(i.rb(), item);
            emit_token_item(&mut i, item);
            (item, item_origin, line_entry) = match type_after_separator_normalized(
                i.rb(),
                close,
                owner,
                baseline,
                caller_stops,
                outer_closes,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
            ) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        if !is_type_nud(&item) {
            if owner != TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&item, close) {
                return complete(handoff(item), line_entry);
            }
            (item, item_origin, line_entry) = match retry_type_delimited_item_normalized(
                i.rb(),
                item,
                close,
                owner,
                baseline,
                caller_stops,
                outer_closes,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
            ) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }

        let entry = suffix_marker(i.rb());
        let exit = type_expr_from_nud_normalized(
            i.rb(),
            item,
            baseline,
            false,
            None,
            true,
            with_type_outer_close(outer_closes, close),
            caller_stops,
            TypeOuterBoundary::NONE,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
        item_origin = advanced_origin(item_origin, entry, i.rb());
        item = match exit {
            NormalizedExit::Complete(Ok(()), next_line_entry) => {
                line_entry = next_line_entry;
                let (next, next_origin, next_line_entry) =
                    type_nud_item_with_pipe_lexical_normalized(
                        i.rb(),
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                    );
                item_origin = next_origin;
                line_entry = next_line_entry;
                next
            }
            NormalizedExit::Complete(Err(Either::Left(next)), next_line_entry) => {
                line_entry = next_line_entry;
                if next.payload_view().is_boundary() {
                    emit_delimited_close_missing(&mut i, owner, &next, item_origin);
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
                if is_type_caller_boundary(&next, caller_stops) {
                    emit_delimited_close_missing(&mut i, owner, &next, item_origin);
                    return complete(handoff(next), line_entry);
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
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
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
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
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
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
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

#[allow(clippy::too_many_arguments)]
fn retry_type_delimited_item_normalized(
    mut i: RewriteIn,
    mut item: Item,
    close: TokenKind,
    owner: TypeDelimitedOwner,
    baseline: usize,
    caller_stops: Stops,
    outer_closes: u8,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
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
        if is_type_caller_boundary(&item, caller_stops) {
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
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
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
            ));
        }
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
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
    let (mut next, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
    );
    if next.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        emit_delimited_close_missing(&mut i, owner, &next, item_origin);
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
    if is_type_caller_boundary(&next, caller_stops) && !is_type_nud(&next) {
        emit_missing(&mut i, LeadingTrivia::default());
        emit_delimited_close_missing(&mut i, owner, &next, item_origin);
        return Err(complete(handoff(next), line_entry));
    }
    if next.payload_view().is_eof() {
        next = missing_type_item(i.rb(), next);
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
        TypeDelimitedOwner::BracketRow => missing_bracket_row_close(i, item, baseline),
        TypeDelimitedOwner::Call | TypeDelimitedOwner::EffectRow => missing_type_close(i, item),
    }
}

fn emit_delimited_close_missing(
    i: &mut RewriteIn,
    owner: TypeDelimitedOwner,
    item: &Item,
    item_origin: usize,
) {
    if owner != TypeDelimitedOwner::ParenthesizedGroup {
        emit_missing(i, LeadingTrivia::default());
        return;
    }
    let at = item.extent(item_origin).recovery_range().start;
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        let role = GrammarRole::ClosingDelimiter {
            owner: ConstructRole::ParenthesizedTypeGroup,
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
