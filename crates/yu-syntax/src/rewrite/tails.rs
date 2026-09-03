//! Direct fixed continuations over already-owned Items.

use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    RewriteIn,
    delimited::delimited_items,
    driver::{
        MlMode, TailExit, continue_completed_tail, is_close, is_led_operator, is_separator,
        scan_tail_after_accept, tail, token_kind,
    },
    emit::{emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{path_segment_item_after_trivia, scan_trivia, tail_item_after_trivia},
};

pub(super) fn call_tail(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    i.state.start_node(SyntaxKind::CallTail.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(
        i.rb(),
        TokenKind::RParen,
        None,
        false,
        baseline,
        MlMode::All,
    );
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, exit)
}

pub(super) fn index_tail(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    i.state.start_node(SyntaxKind::IndexTail.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(
        i.rb(),
        TokenKind::RBracket,
        Some(SyntaxKind::IndexItem),
        false,
        baseline,
        MlMode::All,
    );
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, exit)
}

pub(super) fn dot_tail(
    mut i: RewriteIn,
    dot: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let next = tail_item_after_trivia(i.rb(), leading, OperatorSite::Led, baseline, stops);
    if next.leading.0.is_empty() {
        match token_kind(&next) {
            Some(TokenKind::LParen) => {
                return projection_tuple_tail(i, dot, next, threshold, baseline, stops, ml_mode);
            }
            Some(TokenKind::LBrace) => {
                return projection_record_tail(i, dot, next, threshold, baseline, stops, ml_mode);
            }
            _ => {}
        }
    }
    field_tail(i, dot, next, threshold, baseline, stops, ml_mode)
}

fn field_tail(
    mut i: RewriteIn,
    dot: Item,
    mut name: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    i.state.start_node(SyntaxKind::FieldTail.into());
    emit_token_item(&mut i, dot);
    if token_kind(&name) == Some(TokenKind::Identifier) && name.leading.0.is_empty() {
        emit_token_item(&mut i, name);
        i.state.finish_node();
        return scan_tail_after_accept(i, threshold, baseline, stops, ml_mode);
    }
    if !name.leading.0.is_empty() || is_fixed_tail_boundary(&name) {
        emit_missing(&mut i, LeadingTrivia::default());
    } else {
        name = retry_fixed_tail_item(i.rb(), name, baseline, stops);
    }
    i.state.finish_node();
    tail(i, name, threshold, baseline, stops, ml_mode)
}

fn projection_tuple_tail(
    mut i: RewriteIn,
    dot: Item,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    i.state.start_node(SyntaxKind::ProjectionTupleTail.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let exit = delimited_items(
        i.rb(),
        TokenKind::RParen,
        None,
        false,
        baseline,
        MlMode::All,
    );
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, exit)
}

fn projection_record_tail(
    mut i: RewriteIn,
    dot: Item,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    i.state.start_node(SyntaxKind::ProjectionRecordTail.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let exit = delimited_items(i.rb(), TokenKind::RBrace, None, true, baseline, MlMode::All);
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, exit)
}

pub(super) fn path_tail(
    mut i: RewriteIn,
    separator: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    i.state.start_node(SyntaxKind::PathTail.into());
    emit_token_item(&mut i, separator);
    let leading = scan_trivia(i.rb());
    let mut segment = path_segment_item_after_trivia(i.rb(), leading, baseline, stops);
    if matches!(
        token_kind(&segment),
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier)
    ) {
        emit_token_item(&mut i, segment);
        i.state.finish_node();
        return scan_tail_after_accept(i, threshold, baseline, stops, ml_mode);
    }
    if is_fixed_tail_boundary(&segment) {
        let leading = std::mem::take(&mut segment.leading);
        emit_missing(&mut i, leading);
    } else {
        segment = retry_fixed_tail_item(i.rb(), segment, baseline, stops);
    }
    i.state.finish_node();
    tail(i, segment, threshold, baseline, stops, ml_mode)
}

fn retry_fixed_tail_item(mut i: RewriteIn, mut item: Item, baseline: usize, stops: u8) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Led, baseline, stops);
        if !item.leading.0.is_empty() || is_fixed_tail_boundary(&item) {
            i.state.finish_node();
            return item;
        }
    }
}

fn is_fixed_tail_boundary(item: &Item) -> bool {
    matches!(&item.payload, Payload::Eof)
        || is_separator(item)
        || is_close(item)
        || is_led_operator(item)
        || matches!(
            token_kind(item),
            Some(
                TokenKind::LParen | TokenKind::LBracket | TokenKind::Dot | TokenKind::PathSeparator
            )
        )
}
