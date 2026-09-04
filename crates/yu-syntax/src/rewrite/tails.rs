//! Direct fixed continuations over already-owned Items.

use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    RewriteIn,
    delimited::delimited_items,
    driver::{
        Either, MlMode, TailExit, chain_continuation, continue_completed_tail, expr_from_nud,
        handoff, is_close, is_led_operator, is_nud_item, is_separator, scan_tail_after_accept,
        tail, token_kind,
    },
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{
        inline_normal_nud_follower, path_segment_item_after_trivia, scan_trivia,
        tail_item_after_trivia,
    },
    operator::STOP_COMMA,
};

/// The C1 construction witness owns a lone colon only for a same-line inline
/// argument sequence. Newline bodies and mandatory-slot recovery remain for
/// the canonical statement/block owner, so this isolated parser hands those
/// inputs back without constructing recovery nodes.
pub(super) fn colon_tail(
    mut i: RewriteIn,
    mut colon: Item,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    if matches!(ml_mode, MlMode::None) || !chain_continuation(&colon.leading, baseline) {
        return handoff(colon);
    }
    if !same_line_normal_nud_follows(i.rb()) {
        return handoff(colon);
    }

    emit_leading_trivia(&mut i, &colon.leading);
    colon.leading = LeadingTrivia::default();
    i.state.start_node(SyntaxKind::ColonApplicationTail.into());
    emit_token_item(&mut i, colon);

    let leading = scan_trivia(i.rb());
    let mut item = tail_item_after_trivia(
        i.rb(),
        leading,
        OperatorSite::Nud,
        baseline,
        stops | STOP_COMMA,
    );
    let leading = std::mem::take(&mut item.leading);
    emit_leading_trivia(&mut i, &leading);
    let exit = inline_colon_argument(i.rb(), item, baseline, stops, ml_mode);
    i.state.finish_node();
    exit
}

fn inline_colon_argument(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    if !is_nud_item(&item) {
        return handoff(item);
    }
    let exit = expr_from_nud(i.rb(), item, None, baseline, stops | STOP_COMMA, ml_mode);
    inline_colon_successor(i, exit, baseline, stops, ml_mode)
}

fn inline_colon_successor(
    mut i: RewriteIn,
    exit: TailExit,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    match exit {
        Ok(()) => Ok(()),
        Err(Either::Left(comma))
            if token_kind(&comma) == Some(TokenKind::Comma) && stops & STOP_COMMA == 0 =>
        {
            if !same_line_normal_nud_follows(i.rb()) {
                return handoff(comma);
            }
            emit_token_item(&mut i, comma);
            let leading = scan_trivia(i.rb());
            let mut item = tail_item_after_trivia(
                i.rb(),
                leading,
                OperatorSite::Nud,
                baseline,
                stops | STOP_COMMA,
            );
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            inline_colon_argument(i, item, baseline, stops, ml_mode)
        }
        exit => exit,
    }
}

fn same_line_normal_nud_follows(i: RewriteIn) -> bool {
    i.map(inline_normal_nud_follower, |follower| follower)
        .unwrap_or(false)
}

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
