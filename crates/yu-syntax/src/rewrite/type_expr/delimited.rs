//! Type delimiter recovery shared by groups, calls, effect rows, and bracket rows.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::super::{
    RewriteIn, Stops,
    current_item::LineEntry,
    driver::{
        Either, NormalizedExit, advanced_origin, complete, handoff, suffix_marker, token_kind,
    },
    emit::{emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, TokenKind},
    yumark::FenceBoundary,
};
use super::{
    TypeOuterBoundary, is_type_caller_boundary, is_type_deeper_newline, is_type_implicit_boundary,
    is_type_mismatched_close, is_type_nud, is_type_separator, missing_bracket_row_close,
    missing_type_close, missing_type_item, type_chain_trivia, type_delimited_baseline,
    type_expr_from_nud_normalized, type_nud_item_normalized, with_type_outer_close,
};

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum TypeDelimitedOwner {
    Generic,
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
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (mut item, next_origin, next_line_entry) =
        type_nud_item_normalized(i.rb(), item_origin, line_entry, fence);
    item_origin = next_origin;
    line_entry = next_line_entry;
    let baseline = type_delimited_baseline(incoming_baseline, item.leading_view());

    if item.payload_view().is_boundary() {
        if owner == TypeDelimitedOwner::BracketRow {
            emit_missing(&mut i, LeadingTrivia::default());
        }
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if owner == TypeDelimitedOwner::BracketRow && item.payload_view().is_eof() {
        item = missing_type_item(i.rb(), item);
        return complete(missing_bracket_row_close(i, item, baseline), line_entry);
    }

    loop {
        if item.payload_view().is_boundary() {
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(item), line_entry);
        }
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return complete(Ok(()), line_entry);
        }
        if is_type_caller_boundary(&item, caller_stops) && !is_type_nud(&item) {
            if owner == TypeDelimitedOwner::BracketRow {
                emit_missing(&mut i, LeadingTrivia::default());
            }
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(item), line_entry);
        }
        if item.payload_view().is_eof() {
            let exit = if owner == TypeDelimitedOwner::BracketRow {
                missing_bracket_row_close(i, item, baseline)
            } else {
                missing_type_close(i, item)
            };
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
                item_origin,
                line_entry,
                fence,
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
                item_origin,
                line_entry,
                fence,
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
            item_origin,
            line_entry,
            fence,
        );
        item_origin = advanced_origin(item_origin, entry, i.rb());
        item = match exit {
            NormalizedExit::Complete(Ok(()), next_line_entry) => {
                line_entry = next_line_entry;
                let (next, next_origin, next_line_entry) =
                    type_nud_item_normalized(i.rb(), item_origin, line_entry, fence);
                item_origin = next_origin;
                line_entry = next_line_entry;
                next
            }
            NormalizedExit::Complete(Err(Either::Left(next)), next_line_entry) => {
                line_entry = next_line_entry;
                if next.payload_view().is_boundary() {
                    emit_missing(&mut i, LeadingTrivia::default());
                    return complete(handoff(next), line_entry);
                }
                if token_kind(&next) == Some(close) {
                    emit_token_item(&mut i, next);
                    return complete(Ok(()), line_entry);
                }
                if is_type_caller_boundary(&next, caller_stops) {
                    emit_missing(&mut i, LeadingTrivia::default());
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
                        item_origin,
                        line_entry,
                        fence,
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
                        item_origin,
                        line_entry,
                        fence,
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
                let exit = if owner == TypeDelimitedOwner::BracketRow {
                    missing_bracket_row_close(i, end.item, baseline)
                } else {
                    missing_type_close(i, end.item)
                };
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
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
    debug_assert!(!item.payload_view().is_boundary());
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) =
            type_nud_item_normalized(i.rb(), item_origin, line_entry, fence);
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            emit_missing(&mut i, LeadingTrivia::default());
            return Err(complete(handoff(item), line_entry));
        }
        if token_kind(&item) == Some(close) {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return Err(complete(Ok(()), line_entry));
        }
        if is_type_caller_boundary(&item, caller_stops) {
            i.state.finish_node();
            emit_missing(&mut i, LeadingTrivia::default());
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
                item_origin,
                line_entry,
                fence,
            );
        }
        if is_type_implicit_boundary(baseline, item.leading_view()) {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            return Ok((item, item_origin, line_entry));
        }
        if item.payload_view().is_eof() {
            i.state.finish_node();
            let exit = if owner == TypeDelimitedOwner::BracketRow {
                missing_bracket_row_close(i, item, baseline)
            } else {
                missing_type_close(i, item)
            };
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
) -> NormalizedExit {
    debug_assert!(!item.payload_view().is_boundary());
    loop {
        i.state.start_node(SyntaxKind::Error.into());
        emit_token_item(&mut i, item);
        i.state.finish_node();
        (item, item_origin, line_entry) =
            type_nud_item_normalized(i.rb(), item_origin, line_entry, fence);
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
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
    let (mut next, item_origin, line_entry) =
        type_nud_item_normalized(i.rb(), item_origin, line_entry, fence);
    if next.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(complete(handoff(next), line_entry));
    }
    if token_kind(&next) == Some(close) {
        next.emit_all_remaining_leading(&mut *i.state);
        emit_token_item(&mut i, next);
        return Err(complete(Ok(()), line_entry));
    }
    if is_type_caller_boundary(&next, caller_stops) && !is_type_nud(&next) {
        emit_missing(&mut i, LeadingTrivia::default());
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(complete(handoff(next), line_entry));
    }
    if next.payload_view().is_eof() {
        next = missing_type_item(i.rb(), next);
        return Err(complete(missing_type_close(i, next), line_entry));
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
        ));
    }
    if is_type_nud(&next) {
        next.emit_all_remaining_leading(&mut *i.state);
    }
    Ok((next, item_origin, line_entry))
}
