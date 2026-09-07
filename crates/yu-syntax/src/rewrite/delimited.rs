//! Shared direct-delimited owner and local item recovery.

use super::ambient_claim::AmbientClaimContext;
use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    RewriteIn, Stops,
    current_item::LineEntry,
    driver::{
        Either, MlMode, NormalizedExit, advanced_origin, complete, continue_normalized_tail,
        expr_from_nud_normalized, expression_item, handoff, implicit_delimited_newline, is_close,
        is_nud_item, is_separator, suffix_marker, token_kind,
    },
    emit::{emit_error_item, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{is_operator_shaped_unknown, scan_operator_shaped_unknown},
    operator::{
        STOP_RECORD_SPREAD, STOP_RECORD_SPREAD_AFTER_OPERATOR,
        newline_indentation_after_fenced_trivia, stops_for,
    },
    statement::StatementLineHandoff,
    yumark::FenceBoundary,
};

#[allow(clippy::too_many_arguments)]
pub(super) fn parenthesized_nud_normalized(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state
        .start_node(SyntaxKind::ParenthesizedExpression.into());
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = delimited_items_normalized(
        i.rb(),
        TokenKind::RParen,
        None,
        false,
        baseline,
        MlMode::LayoutOnly,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn delimited_items_normalized(
    mut i: RewriteIn,
    close: TokenKind,
    item_node: Option<SyntaxKind>,
    record_spread: bool,
    incoming_baseline: usize,
    item_ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let mut stops = stops_for(close);
    if record_spread {
        stops |= STOP_RECORD_SPREAD;
    }
    let baseline =
        delimited_baseline_from_source(i.rb(), incoming_baseline, item_origin, line_entry, fence);
    let (mut item, next_origin, next_line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    item_origin = next_origin;
    line_entry = next_line_entry;
    loop {
        if item.payload_view().is_boundary() {
            return missing_close_normalized(i, item, line_entry);
        }
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return complete(Ok(()), line_entry);
        }
        if item.payload_view().is_eof() {
            return missing_close_normalized(i, item, line_entry);
        }
        if is_separator(&item) {
            item = missing_item(i.rb(), item);
            emit_token_item(&mut i, item);
            (item, item_origin, line_entry) = expression_item(
                i.rb(),
                OperatorSite::Nud,
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
            );
            continue;
        }
        if is_close(&item) {
            (item, item_origin, line_entry) = wrong_close_item_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            );
            continue;
        }
        if is_record_spread_item(&item) {
            let entry = suffix_marker(i.rb());
            let exit = record_spread_item_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
            item_origin = advanced_origin(item_origin, entry, i.rb());
            match delimited_successor_normalized(
                i.rb(),
                exit,
                close,
                baseline,
                stops,
                item_ml_mode,
                item_origin,
                fence,
            ) {
                Ok(next) => (item, item_origin, line_entry) = next,
                Err(exit) => return exit,
            }
            continue;
        }
        if !is_nud_item(&item) {
            (item, item_origin, line_entry) = retry_nud_item_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            );
            continue;
        }
        if let Some(kind) = item_node {
            i.state.start_node(kind.into());
        }
        let entry = suffix_marker(i.rb());
        let exit = expr_from_nud_normalized(
            i.rb(),
            item,
            None,
            baseline,
            stops,
            item_ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        item_origin = advanced_origin(item_origin, entry, i.rb());
        if item_node.is_some() {
            i.state.finish_node();
        }
        match delimited_successor_normalized(
            i.rb(),
            exit,
            close,
            baseline,
            stops,
            item_ml_mode,
            item_origin,
            fence,
        ) {
            Ok(next) => (item, item_origin, line_entry) = next,
            Err(exit) => return exit,
        }
    }
}

fn delimited_baseline_from_source(
    mut i: RewriteIn,
    incoming: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> usize {
    let indentation = i
        .token(|lex| {
            Some(newline_indentation_after_fenced_trivia(
                lex.remainder(),
                item_origin,
                line_entry,
                fence,
            ))
        })
        .expect("the direct delimiter layout probe is total");
    indentation
        .filter(|&indentation| indentation > incoming)
        .unwrap_or(incoming)
}

#[allow(clippy::too_many_arguments)]
fn delimited_successor_normalized(
    mut i: RewriteIn,
    exit: NormalizedExit,
    close: TokenKind,
    baseline: usize,
    stops: Stops,
    item_ml_mode: MlMode,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
    match exit {
        NormalizedExit::Complete(Err(Either::Left(next)), line_entry)
            if next.payload_view().is_boundary() =>
        {
            Err(missing_close_normalized(i, next, line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(next)), line_entry) if is_separator(&next) => {
            emit_token_item(&mut i, next);
            Ok(expression_item(
                i,
                OperatorSite::Nud,
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
            ))
        }
        NormalizedExit::Complete(Err(Either::Left(next)), line_entry)
            if token_kind(&next) == Some(close) =>
        {
            emit_token_item(&mut i, next);
            Err(complete(Ok(()), line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(next)), line_entry) if is_close(&next) => Ok(
            wrong_close_item_normalized(i, next, baseline, stops, item_origin, line_entry, fence),
        ),
        NormalizedExit::Complete(Err(Either::Left(next)), line_entry)
            if stops & STOP_RECORD_SPREAD != 0 && is_record_spread_item(&next) =>
        {
            Ok((missing_item(i, next), item_origin, line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(next)), line_entry)
            if is_nud_item(&next) && implicit_delimited_newline(baseline, next.leading_view()) =>
        {
            Ok((next, item_origin, line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(next)), line_entry)
            if matches!(item_ml_mode, MlMode::LayoutOnly) && is_nud_item(&next) =>
        {
            Ok((missing_item(i, next), item_origin, line_entry))
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            Err(missing_close_normalized(i, end.item, line_entry))
        }
        exit => Err(exit),
    }
}

#[allow(clippy::too_many_arguments)]
fn record_spread_item_normalized(
    mut i: RewriteIn,
    marker: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state
        .start_node(SyntaxKind::ProjectionRecordSpreadItem.into());
    emit_token_item(&mut i, marker);
    let rhs_stops = (stops & !STOP_RECORD_SPREAD) | STOP_RECORD_SPREAD_AFTER_OPERATOR;
    let (mut rhs, next_origin, next_line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        rhs_stops,
    );
    item_origin = next_origin;
    line_entry = next_line_entry;
    if !rhs.payload_view().is_boundary() && !is_nud_item(&rhs) && !is_spread_boundary(&rhs) {
        (rhs, item_origin, line_entry) = retry_nud_item_normalized(
            i.rb(),
            rhs,
            baseline,
            rhs_stops,
            item_origin,
            line_entry,
            fence,
        );
    }
    let exit = if rhs.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        complete(handoff(rhs), line_entry)
    } else if is_nud_item(&rhs) {
        expr_from_nud_normalized(
            i.rb(),
            rhs,
            None,
            baseline,
            stops,
            MlMode::All,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        )
    } else {
        rhs.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        complete(handoff(rhs), line_entry)
    };
    i.state.finish_node();
    exit
}

fn is_spread_boundary(item: &Item) -> bool {
    item.payload_view().is_eof()
        || item.payload_view().is_boundary()
        || is_separator(item)
        || is_close(item)
        || is_record_spread_item(item)
}

fn missing_close_normalized(
    mut i: RewriteIn,
    mut end: Item,
    line_entry: LineEntry,
) -> NormalizedExit {
    if !end.payload_view().is_boundary() {
        end.emit_all_remaining_leading(&mut *i.state);
    }
    emit_missing(&mut i, LeadingTrivia::default());
    complete(handoff(end), line_entry)
}

fn missing_item(mut i: RewriteIn, mut item: Item) -> Item {
    debug_assert!(!item.payload_view().is_boundary());
    item.emit_all_remaining_leading(&mut *i.state);
    emit_missing(&mut i, LeadingTrivia::default());
    item
}

#[allow(clippy::too_many_arguments)]
fn wrong_close_item_normalized(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    debug_assert!(!item.payload_view().is_boundary());
    emit_error_item(&mut i, item);
    expression_item(
        i,
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    )
}

#[allow(clippy::too_many_arguments)]
fn retry_nud_item_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        debug_assert!(!item.payload_view().is_boundary());
        let continues_operator_spelling =
            stops & (STOP_RECORD_SPREAD | STOP_RECORD_SPREAD_AFTER_OPERATOR) != 0
                && is_operator_shaped_unknown(&item);
        emit_token_item(&mut i, item);
        if continues_operator_spelling {
            let entry = suffix_marker(i.rb());
            while let Some(token) = i.token(scan_operator_shaped_unknown) {
                emit_token_item(
                    &mut i,
                    Item::plain(LeadingTrivia::default(), Payload::Token(token)),
                );
            }
            item_origin = advanced_origin(item_origin, entry, i.rb());
        }
        (item, item_origin, line_entry) = expression_item(
            i.rb(),
            OperatorSite::Nud,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
        );
        if item.payload_view().is_boundary()
            || is_nud_item(&item)
            || is_separator(&item)
            || is_close(&item)
            || is_record_spread_item(&item)
            || item.payload_view().is_eof()
        {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
    }
}

fn is_record_spread_item(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::DotDot)
}
