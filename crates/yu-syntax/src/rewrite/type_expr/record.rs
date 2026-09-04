//! Named record type owner and its local recovery.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::super::{
    LexIn, RewriteIn, Stops,
    driver::{Either, TailExit, handoff, token_kind},
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{scan_trivia, type_item_after_trivia, type_nud_item_after_trivia},
};
use super::{
    TypeApplyBoundary, continue_type_tail, indentation_after_newline, is_type_caller_boundary,
    is_type_implicit_boundary, is_type_mismatched_close, is_type_nud,
    is_type_record_field_boundary, is_type_record_field_name, is_type_record_field_start,
    missing_type_close, missing_type_item, retry_type_rhs, type_chain_trivia,
    type_delimited_baseline, type_expr_from_nud, with_type_outer_close,
};

pub(super) fn type_record(
    mut i: RewriteIn,
    open: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    i.state.start_node(SyntaxKind::NamedRecordType.into());
    emit_token_item(&mut i, open);
    let exit = type_record_fields(
        i.rb(),
        baseline,
        with_type_outer_close(outer_closes, TokenKind::RBrace),
        caller_stops,
    );
    i.state.finish_node();
    continue_type_tail(
        i,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        exit,
    )
}

fn type_record_fields(
    mut i: RewriteIn,
    incoming_baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    let opening = scan_trivia(i.rb());
    let baseline = type_delimited_baseline(incoming_baseline, &opening);
    emit_leading_trivia(&mut i, &opening);
    let mut item = type_item_after_trivia(i.rb(), LeadingTrivia::default());
    loop {
        if token_kind(&item) == Some(TokenKind::RBrace) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if is_type_caller_boundary(&item, caller_stops)
            && !type_record_next_field(i.rb(), &item, baseline)
        {
            emit_missing(&mut i, LeadingTrivia::default());
            return handoff(item);
        }
        if matches!(&item.payload, Payload::Eof)
            || is_type_mismatched_close(&item, TokenKind::RBrace)
        {
            return type_record_missing_close(i, item);
        }
        if token_kind(&item) == Some(TokenKind::Comma) {
            item = missing_type_item(i.rb(), item);
            emit_token_item(&mut i, item);
            item = match type_record_after_comma(i.rb(), baseline, caller_stops) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        if token_kind(&item) == Some(TokenKind::Semicolon) {
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            item = match retry_type_record_separator(i.rb(), item, baseline, caller_stops) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        let exit = if is_type_record_field_name(&item) {
            type_record_field(i.rb(), item, baseline, outer_closes, caller_stops)
        } else if token_kind(&item) == Some(TokenKind::Colon) {
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            type_record_missing_name(i.rb(), item, baseline, outer_closes, caller_stops)
        } else {
            let malformed_name_colon = i
                .rb()
                .then(type_record_malformed_name_colon, |has_colon, _| has_colon)
                .expect("the malformed-name probe always succeeds");
            if malformed_name_colon && indentation_after_newline(&item.leading).is_none() {
                type_record_malformed_name(i.rb(), item, baseline, outer_closes, caller_stops)
            } else {
                item = match retry_type_record_field(i.rb(), item, baseline, caller_stops) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                };
                continue;
            }
        };
        item = match type_record_successor(i.rb(), exit, baseline, caller_stops) {
            Ok(next) => next,
            Err(exit) => return exit,
        };
    }
}

fn type_record_field(
    mut i: RewriteIn,
    name: Item,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    i.state.start_node(SyntaxKind::TypeRecordField.into());
    emit_token_item(&mut i, name);
    let leading = scan_trivia(i.rb());
    let mut colon = type_nud_item_after_trivia(i.rb(), leading);
    if !type_chain_trivia(&colon.leading, baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return handoff(colon);
    }
    if token_kind(&colon) != Some(TokenKind::Colon) {
        if is_type_record_field_boundary(&colon) {
            let leading = std::mem::take(&mut colon.leading);
            emit_missing(&mut i, leading);
            i.state.finish_node();
            return handoff(colon);
        }
        if is_type_nud(&colon) {
            let leading = std::mem::take(&mut colon.leading);
            emit_missing(&mut i, leading);
            let exit = type_expr_from_nud(
                i.rb(),
                colon,
                baseline,
                false,
                Some(TypeApplyBoundary::NamedRecord(baseline)),
                true,
                outer_closes,
                caller_stops,
            );
            i.state.finish_node();
            return exit;
        }
        let leading = std::mem::take(&mut colon.leading);
        emit_leading_trivia(&mut i, &leading);
        let exit = retry_type_record_colon(i.rb(), colon, baseline, outer_closes, caller_stops);
        i.state.finish_node();
        return exit;
    }
    emit_token_item(&mut i, colon);
    let exit = type_record_rhs(i.rb(), baseline, outer_closes, caller_stops);
    i.state.finish_node();
    exit
}

fn type_record_missing_name(
    mut i: RewriteIn,
    colon: Item,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    i.state.start_node(SyntaxKind::TypeRecordField.into());
    emit_missing(&mut i, LeadingTrivia::default());
    emit_token_item(&mut i, colon);
    let exit = type_record_rhs(i.rb(), baseline, outer_closes, caller_stops);
    i.state.finish_node();
    exit
}

fn type_record_malformed_name_colon(mut i: LexIn) -> Option<bool> {
    let mut input = i.remainder();
    let mut probe: LexIn = chasa_recover::In::new(&mut input, i.recovery(), ());
    let mut nested_depth = 0usize;
    loop {
        let leading = scan_trivia(probe.rb());
        let item = type_nud_item_after_trivia(probe.rb(), leading);
        if indentation_after_newline(&item.leading).is_some()
            || matches!(item.payload, Payload::Eof)
        {
            return Some(false);
        }
        match token_kind(&item) {
            Some(TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace) => {
                nested_depth += 1;
                continue;
            }
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
                if nested_depth != 0 =>
            {
                nested_depth -= 1;
                continue;
            }
            _ => {}
        }
        if nested_depth == 0 && token_kind(&item) == Some(TokenKind::Colon) {
            return Some(true);
        }
        if nested_depth == 0
            && (is_type_record_field_name(&item) || is_type_record_field_boundary(&item))
        {
            return Some(false);
        }
    }
}

fn type_record_malformed_name(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    let leading = std::mem::take(&mut item.leading);
    emit_leading_trivia(&mut i, &leading);
    i.state.start_node(SyntaxKind::TypeRecordField.into());
    i.state.start_node(SyntaxKind::Error.into());
    let mut nested_depth = 0usize;
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if token_kind(&item) == Some(TokenKind::Colon) && nested_depth == 0 {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            let exit = type_record_rhs(i.rb(), baseline, outer_closes, caller_stops);
            i.state.finish_node();
            return exit;
        }
        let was_nested = nested_depth != 0;
        match token_kind(&item) {
            Some(TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace) => {
                nested_depth += 1;
            }
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
                if nested_depth != 0 =>
            {
                nested_depth -= 1;
            }
            _ => {}
        }
        if matches!(item.payload, Payload::Eof)
            || (nested_depth == 0
                && (is_type_record_field_name(&item)
                    || (!was_nested && is_type_record_field_boundary(&item))
                    || is_type_implicit_boundary(baseline, &item.leading)))
        {
            i.state.finish_node();
            i.state.finish_node();
            return handoff(item);
        }
    }
}

fn type_record_field_head_colon(mut i: LexIn) -> Option<(bool, Option<usize>)> {
    let mut input = i.remainder();
    let mut probe: LexIn = chasa_recover::In::new(&mut input, i.recovery(), ());
    let leading = scan_trivia(probe.rb());
    let item = type_nud_item_after_trivia(probe, leading);
    Some((
        token_kind(&item) == Some(TokenKind::Colon),
        indentation_after_newline(&item.leading),
    ))
}

fn type_record_field_head_after(mut i: RewriteIn, baseline: usize) -> bool {
    let (has_colon, colon_indentation) = i
        .rb()
        .then(type_record_field_head_colon, |head, _| head)
        .expect("the field-head probe always succeeds");
    has_colon && colon_indentation.is_none_or(|indentation| indentation > baseline)
}

pub(super) fn type_record_next_field(mut i: RewriteIn, item: &Item, baseline: usize) -> bool {
    is_type_record_field_name(item)
        && indentation_after_newline(&item.leading).is_none()
        && type_record_field_head_after(i.rb(), baseline)
}

fn retry_type_record_field(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    caller_stops: Stops,
) -> Result<Item, TailExit> {
    let leading = std::mem::take(&mut item.leading);
    emit_leading_trivia(&mut i, &leading);
    i.state.start_node(SyntaxKind::Error.into());
    let mut nested_depth = 0usize;
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if matches!(item.payload, Payload::Eof) {
            i.state.finish_node();
            return Err(type_record_missing_close(i, item));
        }
        if token_kind(&item) == Some(TokenKind::RBrace) && nested_depth == 0 {
            i.state.finish_node();
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            emit_token_item(&mut i, item);
            return Err(Ok(()));
        }
        if token_kind(&item) == Some(TokenKind::Comma) && nested_depth == 0 {
            i.state.finish_node();
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            emit_token_item(&mut i, item);
            return type_record_after_comma(i, baseline, caller_stops);
        }
        if token_kind(&item) == Some(TokenKind::Colon)
            && nested_depth == 0
            && type_chain_trivia(&item.leading, baseline)
        {
            i.state.finish_node();
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            return Ok(item);
        }
        if is_type_record_field_name(&item) && nested_depth == 0 {
            if type_chain_trivia(&item.leading, baseline)
                && type_record_field_head_after(i.rb(), baseline)
            {
                i.state.finish_node();
                let leading = std::mem::take(&mut item.leading);
                emit_leading_trivia(&mut i, &leading);
                return Ok(item);
            }
        }
        if nested_depth == 0 && is_type_caller_boundary(&item, caller_stops) {
            i.state.finish_node();
            emit_missing(&mut i, LeadingTrivia::default());
            return Err(handoff(item));
        }
        let was_nested = nested_depth != 0;
        match token_kind(&item) {
            Some(TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace) => {
                nested_depth += 1;
            }
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
                if nested_depth != 0 =>
            {
                nested_depth -= 1;
            }
            _ => {}
        }
        if nested_depth == 0 && !was_nested && is_type_mismatched_close(&item, TokenKind::RBrace) {
            i.state.finish_node();
            return Err(type_record_missing_close(i, item));
        }
        if nested_depth == 0 && !was_nested && is_type_implicit_boundary(baseline, &item.leading) {
            i.state.finish_node();
            return Err(handoff(item));
        }
    }
}

fn retry_type_record_colon(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if token_kind(&item) == Some(TokenKind::Colon) {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return type_record_rhs(i, baseline, outer_closes, caller_stops);
        }
        if !type_chain_trivia(&item.leading, baseline) || is_type_record_field_boundary(&item) {
            i.state.finish_node();
            return handoff(item);
        }
        if is_type_caller_boundary(&item, caller_stops) {
            i.state.finish_node();
            return handoff(item);
        }
        if is_type_nud(&item) {
            i.state.finish_node();
            return type_expr_from_nud(
                i,
                item,
                baseline,
                false,
                Some(TypeApplyBoundary::NamedRecord(baseline)),
                true,
                outer_closes,
                caller_stops,
            );
        }
    }
}

fn type_record_rhs(
    mut i: RewriteIn,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let mut rhs = type_nud_item_after_trivia(i.rb(), leading);
    if !type_chain_trivia(&rhs.leading, baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(rhs);
    }
    if is_type_record_field_boundary(&rhs) {
        let leading = std::mem::take(&mut rhs.leading);
        emit_missing(&mut i, leading);
        return handoff(rhs);
    }
    if !is_type_nud(&rhs) {
        let leading = std::mem::take(&mut rhs.leading);
        emit_leading_trivia(&mut i, &leading);
        rhs = retry_type_rhs(i.rb(), rhs, baseline, caller_stops);
        if !type_chain_trivia(&rhs.leading, baseline)
            || is_type_caller_boundary(&rhs, caller_stops)
            || !is_type_nud(&rhs)
        {
            return handoff(rhs);
        }
    }
    let leading = std::mem::take(&mut rhs.leading);
    emit_leading_trivia(&mut i, &leading);
    type_expr_from_nud(
        i,
        rhs,
        baseline,
        false,
        Some(TypeApplyBoundary::NamedRecord(baseline)),
        true,
        outer_closes,
        caller_stops,
    )
}

fn type_record_after_comma(
    mut i: RewriteIn,
    baseline: usize,
    caller_stops: Stops,
) -> Result<Item, TailExit> {
    let leading = scan_trivia(i.rb());
    let mut next = type_item_after_trivia(i.rb(), leading);
    if token_kind(&next) == Some(TokenKind::RBrace) || is_type_record_field_start(&next) {
        let leading = std::mem::take(&mut next.leading);
        emit_leading_trivia(&mut i, &leading);
    }
    if token_kind(&next) == Some(TokenKind::RBrace) {
        emit_token_item(&mut i, next);
        return Err(Ok(()));
    }
    if is_type_caller_boundary(&next, caller_stops)
        && !type_record_next_field(i.rb(), &next, baseline)
    {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(handoff(next));
    }
    if matches!(&next.payload, Payload::Eof) || is_type_mismatched_close(&next, TokenKind::RBrace) {
        next = missing_type_item(i.rb(), next);
        return Err(type_record_missing_close(i, next));
    }
    Ok(next)
}

fn type_record_missing_close(i: RewriteIn, item: Item) -> TailExit {
    missing_type_close(i, item)
}

fn retry_type_record_separator(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    caller_stops: Stops,
) -> Result<Item, TailExit> {
    i.state.start_node(SyntaxKind::Error.into());
    let mut nested_depth = 0usize;
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if matches!(item.payload, Payload::Eof) {
            i.state.finish_node();
            return Err(type_record_missing_close(i, item));
        }
        if token_kind(&item) == Some(TokenKind::RBrace) && nested_depth == 0 {
            i.state.finish_node();
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            emit_token_item(&mut i, item);
            return Err(Ok(()));
        }
        if token_kind(&item) == Some(TokenKind::Comma) && nested_depth == 0 {
            i.state.finish_node();
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            emit_token_item(&mut i, item);
            return type_record_after_comma(i, baseline, caller_stops);
        }
        if is_type_record_field_start(&item) && nested_depth == 0 {
            i.state.finish_node();
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            return Ok(item);
        }
        if nested_depth == 0 && is_type_caller_boundary(&item, caller_stops) {
            i.state.finish_node();
            emit_missing(&mut i, LeadingTrivia::default());
            return Err(handoff(item));
        }
        let was_nested = nested_depth != 0;
        match token_kind(&item) {
            Some(TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace) => {
                nested_depth += 1;
            }
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
                if nested_depth != 0 =>
            {
                nested_depth -= 1;
            }
            _ => {}
        }
        if nested_depth == 0 && !was_nested && is_type_mismatched_close(&item, TokenKind::RBrace) {
            i.state.finish_node();
            return Err(type_record_missing_close(i, item));
        }
        if nested_depth == 0 && !was_nested && is_type_implicit_boundary(baseline, &item.leading) {
            i.state.finish_node();
            return Err(handoff(item));
        }
    }
}

fn type_record_successor(
    mut i: RewriteIn,
    exit: TailExit,
    baseline: usize,
    caller_stops: Stops,
) -> Result<Item, TailExit> {
    match exit {
        Err(Either::Left(next)) if token_kind(&next) == Some(TokenKind::Comma) => {
            emit_token_item(&mut i, next);
            type_record_after_comma(i, baseline, caller_stops)
        }
        Err(Either::Left(next)) if token_kind(&next) == Some(TokenKind::RBrace) => {
            emit_token_item(&mut i, next);
            Err(Ok(()))
        }
        Err(Either::Left(mut next)) if type_record_next_field(i.rb(), &next, baseline) => {
            let leading = std::mem::take(&mut next.leading);
            emit_leading_trivia(&mut i, &leading);
            emit_missing(&mut i, LeadingTrivia::default());
            Ok(next)
        }
        Err(Either::Left(next)) if is_type_caller_boundary(&next, caller_stops) => {
            emit_missing(&mut i, LeadingTrivia::default());
            Err(handoff(next))
        }
        Err(Either::Left(mut next)) if token_kind(&next) == Some(TokenKind::Semicolon) => {
            let leading = std::mem::take(&mut next.leading);
            emit_leading_trivia(&mut i, &leading);
            retry_type_record_separator(i, next, baseline, caller_stops)
        }
        Err(Either::Left(next)) if is_type_mismatched_close(&next, TokenKind::RBrace) => {
            Err(type_record_missing_close(i, next))
        }
        Err(Either::Right(end)) => Err(type_record_missing_close(i, end.item)),
        Err(Either::Left(mut next))
            if is_type_record_field_start(&next)
                && is_type_implicit_boundary(baseline, &next.leading) =>
        {
            let leading = std::mem::take(&mut next.leading);
            emit_leading_trivia(&mut i, &leading);
            Ok(next)
        }
        exit => Err(exit),
    }
}
