//! Mandatory operands: boundary publication, lexical Error runs and NUD retry.

use super::operator_chain::{append_nud, is_nud_item};
use crate::{
    ambient_claim::AmbientClaimContext,
    cursor::SyntaxIn,
    cursor::recovery::emit::{ErrorRunOutput, emit_recovery_error_run, emit_recovery_missing},
    handoff::{MlMode, NormalizedExit, complete, handoff},
    lexical::{
        current_item::LineEntry,
        expression_item::{expression_item, scan_expression_item_lexical},
        item::{Item, LeadingTrivia, TokenKind},
        observation::{is_active_stop, is_active_stop_lex, is_close, is_line_stop, token_kind},
        operator_scan::OperatorSite,
        stops::{STOP_RECORD_SPREAD, STOP_RECORD_SPREAD_AFTER_OPERATOR, Stops},
        yumark::FenceBoundary,
    },
    operator_table::BindingPower,
    statement::StatementLineHandoff,
};

#[allow(clippy::too_many_arguments)]
pub(super) fn required_expr_after_accept_normalized(
    mut i: SyntaxIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let (item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops & !(STOP_RECORD_SPREAD | STOP_RECORD_SPREAD_AFTER_OPERATOR),
    );
    required_expr_item_normalized(
        i,
        item,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn required_expr_item_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if is_required_operand_boundary(i.rb(), &item, stops) {
        emit_required_expression_missing(&mut i, &mut item, item_origin, stops);
        return complete(handoff(item), line_entry);
    }
    if is_nud_item(&item) {
        return append_nud(
            i,
            item,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    item.emit_all_remaining_leading(&mut *i.state);
    (item, item_origin, line_entry) = emit_required_expression_error_run(
        i.rb(),
        item,
        stops,
        item_origin,
        line_entry,
        fence,
        baseline,
    );
    if is_required_operand_boundary(i.rb(), &item, stops) {
        return complete(handoff(item), line_entry);
    }
    debug_assert!(is_nud_item(&item));
    append_nud(
        i,
        item,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

pub(crate) fn is_required_operand_boundary(mut i: SyntaxIn, item: &Item, stops: Stops) -> bool {
    (item.payload_view().is_eof() || item.payload_view().is_boundary())
        || is_active_stop(i.rb(), item, stops)
        || is_line_stop(item, stops)
        || is_unread_operand_boundary(item)
}

fn is_unread_operand_boundary(item: &Item) -> bool {
    !is_nud_item(item)
        && (is_close(item)
            || matches!(
                token_kind(item),
                Some(TokenKind::LBracket | TokenKind::LBrace)
            ))
}

fn is_required_operand_boundary_in_error_run(
    run: &mut ErrorRunOutput<'_, '_, '_, '_>,
    item: &Item,
    stops: Stops,
) -> bool {
    (item.payload_view().is_eof() || item.payload_view().is_boundary())
        || is_line_stop(item, stops)
        || is_unread_operand_boundary(item)
        || run.lexical(|lex| is_active_stop_lex(lex, item, stops))
}

pub(crate) fn emit_required_expression_missing(
    i: &mut SyntaxIn,
    item: &mut Item,
    item_origin: usize,
    stops: Stops,
) {
    let at = if item.payload_view().is_boundary() {
        item.payload_view()
            .pending_boundary()
            .expect("a boundary Item retains its inspected boundary")
            .coordinate()
    } else if is_active_stop(i.rb(), item, stops)
        || is_line_stop(item, stops)
        || is_unread_operand_boundary(item)
    {
        item.extent(item_origin).recovery_range().start
    } else if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
        item.extent(item_origin).recovery_range().start
    } else {
        item.extent(item_origin).recovery_range().start
    };
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at);
}

#[allow(clippy::too_many_arguments)]
fn emit_required_expression_error_run(
    i: SyntaxIn,
    mut item: Item,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
) -> (Item, usize, LineEntry) {
    emit_recovery_error_run(i, |run| {
        loop {
            run.emit_item_as(item, item_origin);
            (item, item_origin, line_entry) = run.lexical(|lex| {
                scan_expression_item_lexical(
                    lex,
                    OperatorSite::Nud,
                    item_origin,
                    line_entry,
                    fence,
                    baseline,
                    stops & !(STOP_RECORD_SPREAD | STOP_RECORD_SPREAD_AFTER_OPERATOR),
                )
            });
            if is_required_operand_boundary_in_error_run(run, &item, stops) || is_nud_item(&item) {
                return (item, item_origin, line_entry);
            }
        }
    })
}
