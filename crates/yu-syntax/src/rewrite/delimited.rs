//! Shared direct-delimited owner and local item recovery.

use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    RewriteIn, Stops,
    driver::{
        CompleteItemSite, Either, L5aExit, MlMode, TailExit, continue_completed_tail,
        continue_l5a_tail, delimited_baseline, expr_from_nud, expr_from_nud_l5a, handoff,
        implicit_delimited_newline, is_close, is_nud_item, is_separator, token_kind,
    },
    emit::{emit_error_item, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{
        is_operator_shaped_unknown, scan_operator_shaped_unknown, scan_trivia,
        tail_item_after_trivia,
    },
    operator::{STOP_RECORD_SPREAD, STOP_RECORD_SPREAD_AFTER_OPERATOR, stops_for},
    statement::StatementLineHandoff,
};

pub(super) fn parenthesized_nud(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    i.state
        .start_node(SyntaxKind::ParenthesizedExpression.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(
        i.rb(),
        TokenKind::RParen,
        None,
        false,
        baseline,
        MlMode::LayoutOnly,
        line_handoff,
    );
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, line_handoff, exit)
}

pub(super) fn parenthesized_nud_with<F>(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    defer_distinct_owner: bool,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    debug_assert!(defer_distinct_owner);
    i.state
        .start_node(SyntaxKind::ParenthesizedExpression.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items_l5a(
        i.rb(),
        TokenKind::RParen,
        None,
        false,
        baseline,
        MlMode::LayoutOnly,
        line_handoff,
        acquire,
    );
    i.state.finish_node();
    continue_l5a_tail(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        exit,
        acquire,
    )
}

pub(super) fn delimited_items_l5a<F>(
    mut i: RewriteIn,
    close: TokenKind,
    item_node: Option<SyntaxKind>,
    record_spread: bool,
    incoming_baseline: usize,
    item_ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    let mut stops = stops_for(close);
    if record_spread {
        stops |= STOP_RECORD_SPREAD;
    }
    let mut item = acquire(&mut i, CompleteItemSite::Nud, incoming_baseline, stops);
    let baseline = delimited_baseline(incoming_baseline, item.leading_view());
    loop {
        if item.payload_view().is_boundary() {
            return L5aExit::Complete(missing_close(i, item));
        }
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return L5aExit::Complete(Ok(()));
        }
        if item.payload_view().is_eof() {
            return L5aExit::Complete(missing_close(i, item));
        }
        if is_separator(&item) {
            item = missing_item(i.rb(), item);
            emit_token_item(&mut i, item);
            item = acquire(&mut i, CompleteItemSite::Nud, baseline, stops);
            continue;
        }
        if is_close(&item) {
            item = wrong_close_item_l5a(i.rb(), item, baseline, stops, acquire);
            continue;
        }
        if is_record_spread_item(&item) {
            let exit = record_spread_item_l5a(i.rb(), item, baseline, stops, line_handoff, acquire);
            item = match delimited_successor_l5a(
                i.rb(),
                exit,
                close,
                baseline,
                stops,
                item_ml_mode,
                acquire,
            ) {
                Ok(item) => item,
                Err(exit) => return exit,
            };
            continue;
        }
        if !is_nud_item(&item) {
            item = retry_nud_item_l5a(i.rb(), item, baseline, stops, acquire);
            continue;
        }
        if let Some(kind) = item_node {
            i.state.start_node(kind.into());
        }
        let exit = expr_from_nud_l5a(
            i.rb(),
            item,
            None,
            baseline,
            stops,
            item_ml_mode,
            line_handoff,
            acquire,
        );
        if item_node.is_some() {
            i.state.finish_node();
        }
        if matches!(exit, L5aExit::Deferred(_)) {
            return exit;
        }
        item = match delimited_successor_l5a(
            i.rb(),
            exit,
            close,
            baseline,
            stops,
            item_ml_mode,
            acquire,
        ) {
            Ok(item) => item,
            Err(exit) => return exit,
        };
    }
}

pub(super) fn delimited_items(
    mut i: RewriteIn,
    close: TokenKind,
    item_node: Option<SyntaxKind>,
    record_spread: bool,
    incoming_baseline: usize,
    item_ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let mut stops = stops_for(close);
    if record_spread {
        stops |= STOP_RECORD_SPREAD;
    }
    let leading = scan_trivia(i.rb());
    let baseline = delimited_baseline(incoming_baseline, leading.view());
    let mut item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
    loop {
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if item.payload_view().is_eof() {
            return missing_close(i, item);
        }
        if is_separator(&item) {
            item = missing_item(i.rb(), item);
            emit_token_item(&mut i, item);
            let leading = scan_trivia(i.rb());
            item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
            continue;
        }
        if is_close(&item) {
            item = wrong_close_item(i.rb(), item, baseline, stops);
            continue;
        }
        if is_record_spread_item(&item) {
            let exit = record_spread_item(i.rb(), item, baseline, stops, line_handoff);
            item = match delimited_successor(i.rb(), exit, close, baseline, stops, item_ml_mode) {
                Ok(item) => item,
                Err(exit) => return exit,
            };
            continue;
        }
        if !is_nud_item(&item) {
            item = retry_nud_item(i.rb(), item, baseline, stops);
            continue;
        }
        if let Some(kind) = item_node {
            i.state.start_node(kind.into());
        }
        let exit = expr_from_nud(
            i.rb(),
            item,
            None,
            baseline,
            stops,
            item_ml_mode,
            line_handoff,
        );
        if item_node.is_some() {
            i.state.finish_node();
        }
        item = match delimited_successor(i.rb(), exit, close, baseline, stops, item_ml_mode) {
            Ok(item) => item,
            Err(exit) => return exit,
        };
    }
}

fn delimited_successor(
    mut i: RewriteIn,
    exit: TailExit,
    close: TokenKind,
    baseline: usize,
    stops: Stops,
    item_ml_mode: MlMode,
) -> Result<Item, TailExit> {
    match exit {
        Err(Either::Left(next)) if is_separator(&next) => {
            emit_token_item(&mut i, next);
            let leading = scan_trivia(i.rb());
            Ok(tail_item_after_trivia(
                i.rb(),
                leading,
                OperatorSite::Nud,
                baseline,
                stops,
            ))
        }
        Err(Either::Left(next)) if token_kind(&next) == Some(close) => {
            emit_token_item(&mut i, next);
            Err(Ok(()))
        }
        Err(Either::Left(next)) if is_close(&next) => {
            Ok(wrong_close_item(i.rb(), next, baseline, stops))
        }
        Err(Either::Left(next))
            if stops & STOP_RECORD_SPREAD != 0 && is_record_spread_item(&next) =>
        {
            Ok(missing_item(i.rb(), next))
        }
        Err(Either::Left(next))
            if is_nud_item(&next) && implicit_delimited_newline(baseline, next.leading_view()) =>
        {
            Ok(next)
        }
        Err(Either::Left(next))
            if matches!(item_ml_mode, MlMode::LayoutOnly) && is_nud_item(&next) =>
        {
            Ok(missing_item(i.rb(), next))
        }
        Err(Either::Right(end)) => Err(missing_close(i, end.item)),
        exit => Err(exit),
    }
}

fn delimited_successor_l5a<F>(
    mut i: RewriteIn,
    exit: L5aExit,
    close: TokenKind,
    baseline: usize,
    stops: Stops,
    item_ml_mode: MlMode,
    acquire: &mut F,
) -> Result<Item, L5aExit>
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    match exit {
        L5aExit::Deferred(item) => Err(L5aExit::Deferred(item)),
        L5aExit::Complete(Err(Either::Left(next))) if is_separator(&next) => {
            emit_token_item(&mut i, next);
            Ok(acquire(&mut i, CompleteItemSite::Nud, baseline, stops))
        }
        L5aExit::Complete(Err(Either::Left(next))) if token_kind(&next) == Some(close) => {
            emit_token_item(&mut i, next);
            Err(L5aExit::Complete(Ok(())))
        }
        L5aExit::Complete(Err(Either::Left(next))) if is_close(&next) => {
            Ok(wrong_close_item_l5a(i.rb(), next, baseline, stops, acquire))
        }
        L5aExit::Complete(Err(Either::Left(next)))
            if stops & STOP_RECORD_SPREAD != 0 && is_record_spread_item(&next) =>
        {
            Ok(missing_item(i.rb(), next))
        }
        L5aExit::Complete(Err(Either::Left(next)))
            if is_nud_item(&next) && implicit_delimited_newline(baseline, next.leading_view()) =>
        {
            Ok(next)
        }
        L5aExit::Complete(Err(Either::Left(next)))
            if matches!(item_ml_mode, MlMode::LayoutOnly) && is_nud_item(&next) =>
        {
            Ok(missing_item(i.rb(), next))
        }
        L5aExit::Complete(Err(Either::Right(end))) => {
            Err(L5aExit::Complete(missing_close(i, end.item)))
        }
        exit => Err(exit),
    }
}

fn record_spread_item(
    mut i: RewriteIn,
    marker: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    i.state
        .start_node(SyntaxKind::ProjectionRecordSpreadItem.into());
    emit_token_item(&mut i, marker);
    let leading = scan_trivia(i.rb());
    let rhs_stops = (stops & !STOP_RECORD_SPREAD) | STOP_RECORD_SPREAD_AFTER_OPERATOR;
    let mut rhs = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, rhs_stops);
    if !is_nud_item(&rhs) && !is_spread_boundary(&rhs) {
        rhs = retry_nud_item(i.rb(), rhs, baseline, rhs_stops);
    }
    let exit = if is_nud_item(&rhs) {
        expr_from_nud(
            i.rb(),
            rhs,
            None,
            baseline,
            stops,
            MlMode::All,
            line_handoff,
        )
    } else {
        rhs.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        handoff(rhs)
    };
    i.state.finish_node();
    exit
}

fn record_spread_item_l5a<F>(
    mut i: RewriteIn,
    marker: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    i.state
        .start_node(SyntaxKind::ProjectionRecordSpreadItem.into());
    emit_token_item(&mut i, marker);
    let rhs_stops = (stops & !STOP_RECORD_SPREAD) | STOP_RECORD_SPREAD_AFTER_OPERATOR;
    let mut rhs = acquire(&mut i, CompleteItemSite::Nud, baseline, rhs_stops);
    if !is_nud_item(&rhs) && !is_spread_boundary(&rhs) {
        rhs = retry_nud_item_l5a(i.rb(), rhs, baseline, rhs_stops, acquire);
    }
    let exit = if is_nud_item(&rhs) {
        expr_from_nud_l5a(
            i.rb(),
            rhs,
            None,
            baseline,
            stops,
            MlMode::All,
            line_handoff,
            acquire,
        )
    } else {
        rhs.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        L5aExit::Complete(handoff(rhs))
    };
    i.state.finish_node();
    exit
}

fn is_spread_boundary(item: &Item) -> bool {
    item.payload_view().is_eof()
        || is_separator(item)
        || is_close(item)
        || is_record_spread_item(item)
}

fn missing_close(mut i: RewriteIn, mut end: Item) -> TailExit {
    end.emit_all_remaining_leading(&mut *i.state);
    emit_missing(&mut i, LeadingTrivia::default());
    handoff(end)
}

fn missing_item(mut i: RewriteIn, mut item: Item) -> Item {
    item.emit_all_remaining_leading(&mut *i.state);
    emit_missing(&mut i, LeadingTrivia::default());
    item
}

fn wrong_close_item(mut i: RewriteIn, item: Item, baseline: usize, stops: Stops) -> Item {
    emit_error_item(&mut i, item);
    let leading = scan_trivia(i.rb());
    tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops)
}

fn wrong_close_item_l5a<F>(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    acquire: &mut F,
) -> Item
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    emit_error_item(&mut i, item);
    acquire(&mut i, CompleteItemSite::Nud, baseline, stops)
}

fn retry_nud_item(mut i: RewriteIn, mut item: Item, baseline: usize, stops: Stops) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        let continues_operator_spelling =
            stops & (STOP_RECORD_SPREAD | STOP_RECORD_SPREAD_AFTER_OPERATOR) != 0
                && is_operator_shaped_unknown(&item);
        emit_token_item(&mut i, item);
        if continues_operator_spelling {
            while let Some(token) = i.token(scan_operator_shaped_unknown) {
                emit_token_item(
                    &mut i,
                    Item::plain(LeadingTrivia::default(), Payload::Token(token)),
                );
            }
        }
        let leading = scan_trivia(i.rb());
        item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
        if is_nud_item(&item)
            || is_separator(&item)
            || is_close(&item)
            || is_record_spread_item(&item)
            || item.payload_view().is_eof()
        {
            i.state.finish_node();
            return item;
        }
    }
}

fn retry_nud_item_l5a<F>(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    acquire: &mut F,
) -> Item
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        let continues_operator_spelling =
            stops & (STOP_RECORD_SPREAD | STOP_RECORD_SPREAD_AFTER_OPERATOR) != 0
                && is_operator_shaped_unknown(&item);
        emit_token_item(&mut i, item);
        if continues_operator_spelling {
            while let Some(token) = i.token(scan_operator_shaped_unknown) {
                emit_token_item(
                    &mut i,
                    Item::plain(LeadingTrivia::default(), Payload::Token(token)),
                );
            }
        }
        item = acquire(&mut i, CompleteItemSite::Nud, baseline, stops);
        if is_nud_item(&item)
            || is_separator(&item)
            || is_close(&item)
            || is_record_spread_item(&item)
            || (item.payload_view().is_eof() || item.payload_view().is_boundary())
        {
            i.state.finish_node();
            return item;
        }
    }
}

fn is_record_spread_item(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::DotDot)
}
