//! Type delimiter recovery shared by groups, calls, effect rows, and bracket rows.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::super::{
    RewriteIn,
    driver::{Either, TailExit, handoff, token_kind},
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{scan_trivia, type_nud_item_after_trivia},
};
use super::{
    is_type_deeper_newline, is_type_implicit_boundary, is_type_mismatched_close, is_type_nud,
    is_type_separator, missing_bracket_row_close, missing_type_close, missing_type_item,
    type_chain_trivia, type_delimited_baseline, type_expr_from_nud,
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
) -> TailExit {
    let opening = scan_trivia(i.rb());
    let baseline = type_delimited_baseline(incoming_baseline, &opening);
    emit_leading_trivia(&mut i, &opening);
    let mut item = type_nud_item_after_trivia(i.rb(), LeadingTrivia::default());
    if owner == TypeDelimitedOwner::BracketRow && matches!(&item.payload, Payload::Eof) {
        item = missing_type_item(i.rb(), item);
        return missing_bracket_row_close(i, item, baseline);
    }
    loop {
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if matches!(&item.payload, Payload::Eof) {
            if owner == TypeDelimitedOwner::BracketRow {
                return missing_bracket_row_close(i, item, baseline);
            }
            return missing_type_close(i, item);
        }
        if owner == TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&item, close) {
            let leading = std::mem::take(&mut item.leading);
            emit_missing(&mut i, leading);
            return retry_bracket_row_close(i.rb(), item, close, baseline);
        }
        if is_type_separator(&item) {
            item = missing_type_item(i.rb(), item);
            emit_token_item(&mut i, item);
            item = match type_after_separator(i.rb(), close, owner, baseline) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        if !is_type_nud(&item) {
            if owner != TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&item, close) {
                return handoff(item);
            }
            item = match retry_type_delimited_item(i.rb(), item, close, owner, baseline) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        let exit = type_expr_from_nud(i.rb(), item, baseline, false, None, true);
        item = match exit {
            Ok(()) => type_nud_item_after_trivia(i.rb(), LeadingTrivia::default()),
            Err(Either::Left(next)) if is_type_separator(&next) => {
                emit_token_item(&mut i, next);
                match type_after_separator(i.rb(), close, owner, baseline) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                }
            }
            Err(Either::Left(next)) if token_kind(&next) == Some(close) => {
                emit_token_item(&mut i, next);
                return Ok(());
            }
            Err(Either::Left(mut next))
                if owner == TypeDelimitedOwner::BracketRow
                    && is_type_mismatched_close(&next, close) =>
            {
                let leading = std::mem::take(&mut next.leading);
                emit_leading_trivia(&mut i, &leading);
                return retry_bracket_row_close(i.rb(), next, close, baseline);
            }
            Err(Either::Left(mut next))
                if owner == TypeDelimitedOwner::BracketRow
                    && is_type_deeper_newline(baseline, &next.leading)
                    && is_type_nud(&next) =>
            {
                emit_missing(&mut i, LeadingTrivia::default());
                let leading = std::mem::take(&mut next.leading);
                emit_leading_trivia(&mut i, &leading);
                next
            }
            Err(Either::Left(next))
                if owner == TypeDelimitedOwner::BracketRow
                    && type_chain_trivia(&next.leading, baseline)
                    && !is_type_deeper_newline(baseline, &next.leading)
                    && !is_type_nud(&next) =>
            {
                match retry_type_delimited_item(
                    i.rb(),
                    next,
                    close,
                    TypeDelimitedOwner::BracketRow,
                    baseline,
                ) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                }
            }
            Err(Either::Left(next))
                if owner == TypeDelimitedOwner::BracketRow
                    && is_type_deeper_newline(baseline, &next.leading) =>
            {
                emit_missing(&mut i, LeadingTrivia::default());
                return handoff(next);
            }
            Err(Either::Left(mut next)) if is_type_implicit_boundary(baseline, &next.leading) => {
                let leading = std::mem::take(&mut next.leading);
                emit_leading_trivia(&mut i, &leading);
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
        if is_type_separator(&item) {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return type_after_separator(i, close, owner, baseline);
        }
        if is_type_implicit_boundary(baseline, &item.leading) {
            i.state.finish_node();
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            return Ok(item);
        }
        if matches!(&item.payload, Payload::Eof) {
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
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
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
        if matches!(&item.payload, Payload::Eof) {
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
) -> Result<Item, TailExit> {
    let leading = scan_trivia(i.rb());
    let mut next = type_nud_item_after_trivia(i.rb(), leading);
    if token_kind(&next) == Some(close) {
        let leading = std::mem::take(&mut next.leading);
        emit_leading_trivia(&mut i, &leading);
        emit_token_item(&mut i, next);
        return Err(Ok(()));
    }
    if matches!(&next.payload, Payload::Eof) {
        next = missing_type_item(i.rb(), next);
        return Err(missing_type_close(i, next));
    }
    if owner == TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&next, close) {
        next = missing_type_item(i.rb(), next);
        return Err(retry_bracket_row_close(i, next, close, baseline));
    }
    if is_type_nud(&next) {
        let leading = std::mem::take(&mut next.leading);
        emit_leading_trivia(&mut i, &leading);
    }
    Ok(next)
}
