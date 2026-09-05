//! Rule-owned ordinary expression lists for bracket atoms, calls, and indices.

use reborrow_generic::Reborrow as _;

use crate::{scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    super::{
        RewriteIn,
        driver::{Either, MlMode, expr_from_nud, is_close, is_nud_item},
        emit::emit_error_item,
        item::{Item, TokenKind, TriviaKind},
        lexer::{scan_trivia, tail_item_after_trivia},
        operator::{STOP_LINE_BREAK, stops_for},
        statement::StatementLineHandoff,
    },
    advance_origin, current_suffix_marker, emit_item_as, emit_missing, is_newline, is_token,
};

pub(super) enum ExpressionListExit {
    Close(Item),
    Returned(Item),
}

/// Parses the ordinary expression interior without introducing a CST wrapper.
/// The RuleCall/RuleIndex/RuleItem caller owns and emits the returned close.
pub(super) fn expression_list(
    mut i: RewriteIn,
    mut current: Item,
    close: TokenKind,
    origin: &mut usize,
) -> ExpressionListExit {
    let stops = stops_for(close) | STOP_LINE_BREAK;
    let mut needs_expression = true;
    let mut recovery_requires_expression = false;

    loop {
        if current.payload_view().is_eof() || current.payload_view().is_boundary() {
            if recovery_requires_expression {
                emit_missing(&mut i);
            }
            emit_missing(&mut i);
            return ExpressionListExit::Returned(current);
        }
        if is_unread_close(&current) && token_kind_or_boundary(&current) != Some(close) {
            if recovery_requires_expression {
                emit_missing(&mut i);
            }
            emit_missing(&mut i);
            return ExpressionListExit::Returned(current);
        }

        if emit_leading_newline_separators(
            &mut i,
            &mut current,
            &mut needs_expression,
            &mut recovery_requires_expression,
        ) {
            continue;
        }

        if token_kind_or_boundary(&current) == Some(close) {
            if recovery_requires_expression {
                emit_missing(&mut i);
            }
            return ExpressionListExit::Close(current);
        }

        if is_token(&current, TokenKind::Comma) || is_newline(&current) {
            if needs_expression {
                emit_missing(&mut i);
            }
            let kind = if is_newline(&current) {
                SyntaxKind::Newline
            } else {
                SyntaxKind::Comma
            };
            emit_item_as(&mut i, current, kind);
            current = next_item(i.rb(), stops, origin);
            needs_expression = true;
            recovery_requires_expression = false;
            continue;
        }

        if needs_expression {
            if !is_nud_item(&current) {
                emit_error_item(&mut i, current);
                current = next_item(i.rb(), stops, origin);
                recovery_requires_expression = true;
                continue;
            }

            let start = current_suffix_marker(i.rb());
            let exit = expr_from_nud(
                i.rb(),
                current,
                None,
                0,
                stops,
                MlMode::All,
                StatementLineHandoff::OrdinaryLayout,
            );
            advance_origin(origin, start, current_suffix_marker(i.rb()));
            current = match exit {
                Ok(()) => next_item(i.rb(), stops, origin),
                Err(Either::Left(item)) => item,
                Err(Either::Right(end)) => end.item,
            };
            needs_expression = false;
            recovery_requires_expression = false;
            continue;
        }

        emit_error_item(&mut i, current);
        current = next_item(i.rb(), stops, origin);
    }
}

pub(super) fn first_item(mut i: RewriteIn, close: TokenKind, origin: &mut usize) -> Item {
    next_item(i.rb(), stops_for(close) | STOP_LINE_BREAK, origin)
}

fn next_item(mut i: RewriteIn, stops: u16, origin: &mut usize) -> Item {
    let start = current_suffix_marker(i.rb());
    let leading = scan_trivia(i.rb());
    let item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, 0, stops);
    advance_origin(origin, start, current_suffix_marker(i));
    item
}

fn emit_leading_newline_separators(
    i: &mut RewriteIn,
    item: &mut Item,
    needs_expression: &mut bool,
    recovery_requires_expression: &mut bool,
) -> bool {
    let Some(end_part) = item.leading_view().cut_after_last_ordinary_newline() else {
        return false;
    };
    item.emit_leading_prefix_with(&mut *i.state, end_part, |kind, builder| {
        if kind == TriviaKind::Newline {
            if *needs_expression {
                builder.start_node(SyntaxKind::Missing.into());
                builder.finish_node();
            }
            *needs_expression = true;
            *recovery_requires_expression = false;
        }
    });
    true
}

fn is_unread_close(item: &Item) -> bool {
    item.payload_view().token_kind().is_some() && is_close(item)
}

fn token_kind_or_boundary(item: &Item) -> Option<TokenKind> {
    item.payload_view().token_kind()
}
