//! Rule-owned ordinary expression lists for bracket atoms, calls, and indices.

use reborrow_generic::Reborrow as _;

use crate::{scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    super::{
        RewriteIn,
        current_item::LineEntry,
        driver::{
            Either, MlMode, NormalizedExit, advanced_origin, expr_from_nud_normalized,
            expression_item, is_close, is_nud_item, suffix_marker,
        },
        emit::emit_error_item,
        item::{Item, TokenKind, TriviaKind},
        operator::{STOP_LINE_BREAK, stops_for},
        statement::StatementLineHandoff,
        yumark::FenceBoundary,
    },
    emit_item_as, emit_missing, is_token,
};

pub(super) enum ExpressionListExit {
    Close(Item, LineEntry),
    Returned(Item, LineEntry),
    Deferred(Item, LineEntry),
}

/// Parses the ordinary expression interior without introducing a CST wrapper.
/// The RuleCall/RuleIndex/RuleItem caller owns and emits the returned close.
pub(super) fn expression_list(
    mut i: RewriteIn,
    mut current: Item,
    close: TokenKind,
    origin: &mut usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> ExpressionListExit {
    let stops = stops_for(close) | STOP_LINE_BREAK;
    let mut needs_expression = true;
    let mut recovery_requires_expression = false;

    loop {
        if current.payload_view().is_boundary() {
            if recovery_requires_expression {
                emit_missing(&mut i);
            }
            emit_missing(&mut i);
            return ExpressionListExit::Returned(current, line_entry);
        }

        if emit_leading_newline_separators(
            &mut i,
            &mut current,
            &mut needs_expression,
            &mut recovery_requires_expression,
        ) {
            continue;
        }

        if current.payload_view().is_eof() {
            if recovery_requires_expression {
                emit_missing(&mut i);
            }
            emit_missing(&mut i);
            return ExpressionListExit::Returned(current, line_entry);
        }
        if is_unread_close(&current) && token_kind_or_boundary(&current) != Some(close) {
            if recovery_requires_expression {
                emit_missing(&mut i);
            }
            emit_missing(&mut i);
            return ExpressionListExit::Returned(current, line_entry);
        }

        if token_kind_or_boundary(&current) == Some(close) {
            if recovery_requires_expression {
                emit_missing(&mut i);
            }
            return ExpressionListExit::Close(current, line_entry);
        }

        if is_token(&current, TokenKind::Comma) {
            if needs_expression {
                emit_missing(&mut i);
            }
            emit_item_as(&mut i, current, SyntaxKind::Comma);
            (current, line_entry) = next_item(i.rb(), stops, origin, line_entry, fence);
            needs_expression = true;
            recovery_requires_expression = false;
            continue;
        }

        if needs_expression {
            if !is_nud_item(&current) {
                emit_error_item(&mut i, current);
                (current, line_entry) = next_item(i.rb(), stops, origin, line_entry, fence);
                recovery_requires_expression = true;
                continue;
            }

            let entry = suffix_marker(i.rb());
            let exit = expr_from_nud_normalized(
                i.rb(),
                current,
                None,
                0,
                stops,
                MlMode::All,
                StatementLineHandoff::OrdinaryLayout,
                *origin,
                line_entry,
                fence,
            );
            *origin = advanced_origin(*origin, entry, i.rb());
            (current, line_entry) = match exit {
                NormalizedExit::Complete(Ok(()), line_entry) => {
                    next_item(i.rb(), stops, origin, line_entry, fence)
                }
                NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => (item, line_entry),
                NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
                    (end.item, line_entry)
                }
                NormalizedExit::Deferred(item, line_entry) => {
                    return ExpressionListExit::Deferred(item, line_entry);
                }
            };
            needs_expression = false;
            recovery_requires_expression = false;
            continue;
        }

        emit_error_item(&mut i, current);
        (current, line_entry) = next_item(i.rb(), stops, origin, line_entry, fence);
    }
}

pub(super) fn first_item(
    mut i: RewriteIn,
    close: TokenKind,
    origin: &mut usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, LineEntry) {
    next_item(
        i.rb(),
        stops_for(close) | STOP_LINE_BREAK,
        origin,
        line_entry,
        fence,
    )
}

fn next_item(
    mut i: RewriteIn,
    stops: u16,
    origin: &mut usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, LineEntry) {
    let (item, next_origin, next_line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        *origin,
        line_entry,
        fence,
        0,
        stops,
    );
    *origin = next_origin;
    (item, next_line_entry)
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
