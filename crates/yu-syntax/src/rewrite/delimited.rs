//! Shared direct-delimited owner and local item recovery.

use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    RewriteIn, Stops,
    driver::{
        Either, MlMode, TailExit, continue_completed_tail, delimited_baseline, expr_from_nud,
        handoff, implicit_delimited_newline, is_close, is_nud_item, is_separator, token_kind,
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
    let baseline = delimited_baseline(incoming_baseline, &leading);
    let mut item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
    loop {
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if matches!(&item.payload, Payload::Eof) {
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
            if is_nud_item(&next) && implicit_delimited_newline(baseline, &next.leading) =>
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
        let leading = std::mem::take(&mut rhs.leading);
        emit_missing(&mut i, leading);
        handoff(rhs)
    };
    i.state.finish_node();
    exit
}

fn is_spread_boundary(item: &Item) -> bool {
    matches!(&item.payload, Payload::Eof)
        || is_separator(item)
        || is_close(item)
        || is_record_spread_item(item)
}

fn missing_close(mut i: RewriteIn, mut end: Item) -> TailExit {
    let leading = std::mem::take(&mut end.leading);
    emit_missing(&mut i, leading);
    handoff(end)
}

fn missing_item(mut i: RewriteIn, mut item: Item) -> Item {
    let leading = std::mem::take(&mut item.leading);
    emit_missing(&mut i, leading);
    item
}

fn wrong_close_item(mut i: RewriteIn, item: Item, baseline: usize, stops: Stops) -> Item {
    emit_error_item(&mut i, item);
    let leading = scan_trivia(i.rb());
    tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops)
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
            || matches!(&item.payload, Payload::Eof)
        {
            i.state.finish_node();
            return item;
        }
    }
}

fn is_record_spread_item(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::DotDot)
}
