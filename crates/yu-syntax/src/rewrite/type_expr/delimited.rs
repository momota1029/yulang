//! Type delimiter recovery shared by groups, calls, effect rows, and bracket rows.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::super::{
    RewriteIn, Stops,
    driver::{Either, TailExit, handoff, token_kind},
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{scan_trivia, type_nud_item_after_trivia},
};
use super::{
    is_type_caller_boundary, is_type_deeper_newline, is_type_implicit_boundary,
    is_type_mismatched_close, is_type_nud, is_type_separator, missing_bracket_row_close,
    missing_type_close, missing_type_item, type_chain_trivia, type_delimited_baseline,
    type_expr_from_nud, with_type_outer_close,
};

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum TypeDelimitedOwner {
    Generic,
    BracketRow,
}

pub(super) fn type_delimited(
    mut i: RewriteIn,
    close: TokenKind,
    incoming_baseline: usize,
    owner: TypeDelimitedOwner,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    let opening = scan_trivia(i.rb());
    let baseline = type_delimited_baseline(incoming_baseline, opening.view());
    emit_leading_trivia(&mut i, &opening);
    let mut item = type_nud_item_after_trivia(i.rb(), LeadingTrivia::default());
    if owner == TypeDelimitedOwner::BracketRow && item.payload_view().is_eof() {
        item = missing_type_item(i.rb(), item);
        return missing_bracket_row_close(i, item, baseline);
    }
    loop {
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if is_type_caller_boundary(&item, caller_stops) && !is_type_nud(&item) {
            if owner == TypeDelimitedOwner::BracketRow {
                emit_missing(&mut i, LeadingTrivia::default());
            }
            emit_missing(&mut i, LeadingTrivia::default());
            return handoff(item);
        }
        if item.payload_view().is_eof() {
            if owner == TypeDelimitedOwner::BracketRow {
                return missing_bracket_row_close(i, item, baseline);
            }
            return missing_type_close(i, item);
        }
        if owner == TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&item, close) {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_missing(&mut i, LeadingTrivia::default());
            return retry_bracket_row_close(i.rb(), item, close, baseline);
        }
        if is_type_separator(&item) {
            item = missing_type_item(i.rb(), item);
            emit_token_item(&mut i, item);
            item = match type_after_separator(i.rb(), close, owner, baseline, caller_stops) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        if !is_type_nud(&item) {
            if owner != TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&item, close) {
                return handoff(item);
            }
            item =
                match retry_type_delimited_item(i.rb(), item, close, owner, baseline, caller_stops)
                {
                    Ok(next) => next,
                    Err(exit) => return exit,
                };
            continue;
        }
        let exit = type_expr_from_nud(
            i.rb(),
            item,
            baseline,
            false,
            None,
            true,
            with_type_outer_close(outer_closes, close),
            caller_stops,
        );
        item = match exit {
            Ok(()) => type_nud_item_after_trivia(i.rb(), LeadingTrivia::default()),
            Err(Either::Left(next)) if token_kind(&next) == Some(close) => {
                emit_token_item(&mut i, next);
                return Ok(());
            }
            Err(Either::Left(next)) if is_type_caller_boundary(&next, caller_stops) => {
                emit_missing(&mut i, LeadingTrivia::default());
                return handoff(next);
            }
            Err(Either::Left(next)) if is_type_separator(&next) => {
                emit_token_item(&mut i, next);
                match type_after_separator(i.rb(), close, owner, baseline, caller_stops) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                }
            }
            Err(Either::Left(mut next))
                if owner == TypeDelimitedOwner::BracketRow
                    && is_type_mismatched_close(&next, close) =>
            {
                next.emit_all_remaining_leading(&mut *i.state);
                return retry_bracket_row_close(i.rb(), next, close, baseline);
            }
            Err(Either::Left(mut next))
                if owner == TypeDelimitedOwner::BracketRow
                    && is_type_deeper_newline(baseline, next.leading_view())
                    && is_type_nud(&next) =>
            {
                emit_missing(&mut i, LeadingTrivia::default());
                next.emit_all_remaining_leading(&mut *i.state);
                next
            }
            Err(Either::Left(next))
                if owner == TypeDelimitedOwner::BracketRow
                    && type_chain_trivia(next.leading_view(), baseline)
                    && !is_type_deeper_newline(baseline, next.leading_view())
                    && !is_type_nud(&next) =>
            {
                match retry_type_delimited_item(
                    i.rb(),
                    next,
                    close,
                    TypeDelimitedOwner::BracketRow,
                    baseline,
                    caller_stops,
                ) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                }
            }
            Err(Either::Left(next))
                if owner == TypeDelimitedOwner::BracketRow
                    && is_type_deeper_newline(baseline, next.leading_view()) =>
            {
                emit_missing(&mut i, LeadingTrivia::default());
                return handoff(next);
            }
            Err(Either::Left(mut next))
                if is_type_implicit_boundary(baseline, next.leading_view()) =>
            {
                next.emit_all_remaining_leading(&mut *i.state);
                next
            }
            Err(Either::Right(end)) => {
                if owner == TypeDelimitedOwner::BracketRow {
                    return missing_bracket_row_close(i, end.item, baseline);
                }
                return missing_type_close(i, end.item);
            }
            Err(exit) => return Err(exit),
        };
    }
}

fn retry_type_delimited_item(
    mut i: RewriteIn,
    mut item: Item,
    close: TokenKind,
    owner: TypeDelimitedOwner,
    baseline: usize,
    caller_stops: Stops,
) -> Result<Item, TailExit> {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if token_kind(&item) == Some(close) {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return Err(Ok(()));
        }
        if is_type_caller_boundary(&item, caller_stops) {
            i.state.finish_node();
            emit_missing(&mut i, LeadingTrivia::default());
            return Err(handoff(item));
        }
        if is_type_separator(&item) {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return type_after_separator(i, close, owner, baseline, caller_stops);
        }
        if is_type_implicit_boundary(baseline, item.leading_view()) {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            return Ok(item);
        }
        if item.payload_view().is_eof() {
            i.state.finish_node();
            return Err(if owner == TypeDelimitedOwner::BracketRow {
                missing_bracket_row_close(i, item, baseline)
            } else {
                missing_type_close(i, item)
            });
        }
        if owner != TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&item, close) {
            i.state.finish_node();
            return Err(handoff(item));
        }
        item.emit_all_remaining_leading(&mut *i.state);
        if is_type_nud(&item) {
            i.state.finish_node();
            return Ok(item);
        }
        if is_type_mismatched_close(&item, close) {
            i.state.finish_node();
            return Err(retry_bracket_row_close(i, item, close, baseline));
        }
    }
}

fn retry_bracket_row_close(
    mut i: RewriteIn,
    mut item: Item,
    close: TokenKind,
    baseline: usize,
) -> TailExit {
    loop {
        i.state.start_node(SyntaxKind::Error.into());
        emit_token_item(&mut i, item);
        i.state.finish_node();
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if item.payload_view().is_eof() {
            return missing_bracket_row_close(i, item, baseline);
        }
        if !is_type_mismatched_close(&item, close) {
            emit_missing(&mut i, LeadingTrivia::default());
            return handoff(item);
        }
    }
}

fn type_after_separator(
    mut i: RewriteIn,
    close: TokenKind,
    owner: TypeDelimitedOwner,
    baseline: usize,
    caller_stops: Stops,
) -> Result<Item, TailExit> {
    let leading = scan_trivia(i.rb());
    let mut next = type_nud_item_after_trivia(i.rb(), leading);
    if token_kind(&next) == Some(close) {
        next.emit_all_remaining_leading(&mut *i.state);
        emit_token_item(&mut i, next);
        return Err(Ok(()));
    }
    if is_type_caller_boundary(&next, caller_stops) && !is_type_nud(&next) {
        emit_missing(&mut i, LeadingTrivia::default());
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(handoff(next));
    }
    if next.payload_view().is_eof() {
        next = missing_type_item(i.rb(), next);
        return Err(missing_type_close(i, next));
    }
    if owner == TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&next, close) {
        next = missing_type_item(i.rb(), next);
        return Err(retry_bracket_row_close(i, next, close, baseline));
    }
    if is_type_nud(&next) {
        next.emit_all_remaining_leading(&mut *i.state);
    }
    Ok(next)
}
