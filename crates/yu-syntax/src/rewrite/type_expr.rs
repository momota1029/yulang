//! Standalone source-free direct TypeExpression core.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    RewriteIn,
    driver::{Either, TailExit, handoff, token_kind},
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind, TriviaKind},
    lexer::{scan_trivia, scan_type_nud_item, type_item_after_trivia, type_nud_item_after_trivia},
};

pub(super) fn type_expr(mut i: RewriteIn) -> Option<TailExit> {
    let primary = i.token(scan_type_nud_item)?;
    Some(type_expr_from_primary(i, primary, 0, false))
}

fn type_expr_from_primary(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
) -> TailExit {
    i.state.start_node(SyntaxKind::TypeExpression.into());
    let exit = match token_kind(&primary) {
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier | TokenKind::Integer) => {
            emit_token_item(&mut i, primary);
            scan_type_tail(i.rb(), baseline, type_ml)
        }
        Some(TokenKind::LParen) => type_group(i.rb(), primary, baseline, type_ml),
        Some(TokenKind::LBrace) => type_record(i.rb(), primary, baseline, type_ml),
        Some(TokenKind::Forall) => type_forall(i.rb(), primary, baseline),
        _ => unreachable!("the type NUD scanner accepts only type primaries"),
    };
    i.state.finish_node();
    exit
}

fn scan_type_tail(mut i: RewriteIn, baseline: usize, type_ml: bool) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = type_item_after_trivia(i.rb(), leading);
    type_tail(i, item, baseline, type_ml)
}

fn type_tail(mut i: RewriteIn, item: Item, baseline: usize, type_ml: bool) -> TailExit {
    if !type_chain_trivia(&item.leading, baseline) {
        return handoff(item);
    }
    if type_ml && !item.leading.0.is_empty() {
        return handoff(item);
    }
    match token_kind(&item) {
        Some(TokenKind::Arrow) => return type_arrow_tail(i.rb(), item, baseline),
        Some(TokenKind::LParen) if item.leading.0.is_empty() => {
            return type_call_tail(i.rb(), item, baseline, type_ml);
        }
        Some(TokenKind::PathSeparator) => {
            return type_path_tail(i.rb(), item, baseline, type_ml);
        }
        _ => {}
    }
    if !item.leading.0.is_empty() && is_type_primary(&item) {
        return type_apply_argument(i, item, baseline);
    }
    handoff(item)
}

fn type_group(mut i: RewriteIn, open: Item, baseline: usize, type_ml: bool) -> TailExit {
    i.state
        .start_node(SyntaxKind::ParenthesizedTypeGroup.into());
    emit_token_item(&mut i, open);
    let exit = type_delimited(i.rb(), baseline);
    i.state.finish_node();
    continue_type_tail(i, baseline, type_ml, exit)
}

fn type_call_tail(mut i: RewriteIn, open: Item, baseline: usize, type_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::TypeCallTail.into());
    emit_token_item(&mut i, open);
    let exit = type_delimited(i.rb(), baseline);
    i.state.finish_node();
    continue_type_tail(i, baseline, type_ml, exit)
}

fn type_record(mut i: RewriteIn, open: Item, baseline: usize, type_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::NamedRecordType.into());
    emit_token_item(&mut i, open);
    let exit = type_record_fields(i.rb(), baseline);
    i.state.finish_node();
    continue_type_tail(i, baseline, type_ml, exit)
}

fn type_record_fields(mut i: RewriteIn, incoming_baseline: usize) -> TailExit {
    let opening = scan_trivia(i.rb());
    let baseline = type_delimited_baseline(incoming_baseline, &opening);
    emit_leading_trivia(&mut i, &opening);
    let mut item = type_item_after_trivia(i.rb(), LeadingTrivia::default());
    loop {
        if token_kind(&item) == Some(TokenKind::RBrace) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if matches!(&item.payload, Payload::Eof) || !is_type_record_field_name(&item) {
            return handoff(item);
        }
        let exit = type_record_field(i.rb(), item, baseline);
        item = match type_record_successor(i.rb(), exit, baseline) {
            Ok(next) => next,
            Err(exit) => return exit,
        };
    }
}

fn type_record_field(mut i: RewriteIn, name: Item, baseline: usize) -> TailExit {
    i.state.start_node(SyntaxKind::TypeRecordField.into());
    emit_token_item(&mut i, name);
    let leading = scan_trivia(i.rb());
    let colon = type_item_after_trivia(i.rb(), leading);
    if !type_chain_trivia(&colon.leading, baseline) || token_kind(&colon) != Some(TokenKind::Colon)
    {
        i.state.finish_node();
        return handoff(colon);
    }
    emit_token_item(&mut i, colon);
    let leading = scan_trivia(i.rb());
    let mut rhs = type_nud_item_after_trivia(i.rb(), leading);
    if !type_chain_trivia(&rhs.leading, baseline) || !is_type_primary(&rhs) {
        i.state.finish_node();
        return handoff(rhs);
    }
    let leading = std::mem::take(&mut rhs.leading);
    emit_leading_trivia(&mut i, &leading);
    let exit = type_expr_from_primary(i.rb(), rhs, baseline, false);
    i.state.finish_node();
    exit
}

fn type_record_successor(
    mut i: RewriteIn,
    exit: TailExit,
    baseline: usize,
) -> Result<Item, TailExit> {
    match exit {
        Err(Either::Left(next)) if token_kind(&next) == Some(TokenKind::Comma) => {
            emit_token_item(&mut i, next);
            let leading = scan_trivia(i.rb());
            let mut next = type_item_after_trivia(i.rb(), leading);
            if token_kind(&next) == Some(TokenKind::RBrace) {
                let leading = std::mem::take(&mut next.leading);
                emit_leading_trivia(&mut i, &leading);
                emit_token_item(&mut i, next);
                return Err(Ok(()));
            }
            if is_type_record_field_name(&next) {
                let leading = std::mem::take(&mut next.leading);
                emit_leading_trivia(&mut i, &leading);
            }
            Ok(next)
        }
        Err(Either::Left(next)) if token_kind(&next) == Some(TokenKind::RBrace) => {
            emit_token_item(&mut i, next);
            Err(Ok(()))
        }
        Err(Either::Left(mut next))
            if is_type_record_field_name(&next)
                && is_type_implicit_boundary(baseline, &next.leading) =>
        {
            let leading = std::mem::take(&mut next.leading);
            emit_leading_trivia(&mut i, &leading);
            Ok(next)
        }
        exit => Err(exit),
    }
}

fn type_forall(mut i: RewriteIn, keyword: Item, baseline: usize) -> TailExit {
    i.state.start_node(SyntaxKind::ForallType.into());
    emit_token_item(&mut i, keyword);
    let leading = scan_trivia(i.rb());
    let mut binder = type_item_after_trivia(i.rb(), leading);
    if binder.leading.0.is_empty()
        || !type_chain_trivia(&binder.leading, baseline)
        || !is_forall_binder(&binder)
    {
        i.state.finish_node();
        return handoff(binder);
    }
    loop {
        type_forall_binder(i.rb(), binder);
        let leading = scan_trivia(i.rb());
        let next = type_item_after_trivia(i.rb(), leading);
        if token_kind(&next) == Some(TokenKind::Colon) && type_chain_trivia(&next.leading, baseline)
        {
            emit_token_item(&mut i, next);
            let leading = scan_trivia(i.rb());
            let mut body = type_nud_item_after_trivia(i.rb(), leading);
            if !type_chain_trivia(&body.leading, baseline) || !is_type_primary(&body) {
                i.state.finish_node();
                return handoff(body);
            }
            let leading = std::mem::take(&mut body.leading);
            emit_leading_trivia(&mut i, &leading);
            let exit = type_expr_from_primary(i.rb(), body, baseline, false);
            i.state.finish_node();
            return exit;
        }
        if !next.leading.0.is_empty()
            && type_chain_trivia(&next.leading, baseline)
            && is_forall_binder(&next)
        {
            binder = next;
            continue;
        }
        i.state.finish_node();
        return handoff(next);
    }
}

fn type_forall_binder(mut i: RewriteIn, mut binder: Item) {
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    let leading = std::mem::take(&mut binder.leading);
    emit_leading_trivia(&mut i, &leading);
    emit_token_item(&mut i, binder);
    i.state.finish_node();
}

fn type_delimited(mut i: RewriteIn, incoming_baseline: usize) -> TailExit {
    let opening = scan_trivia(i.rb());
    let baseline = type_delimited_baseline(incoming_baseline, &opening);
    emit_leading_trivia(&mut i, &opening);
    let mut item = type_nud_item_after_trivia(i.rb(), LeadingTrivia::default());
    loop {
        if token_kind(&item) == Some(TokenKind::RParen) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if matches!(&item.payload, Payload::Eof) {
            return missing_type_close(i, item);
        }
        if is_type_separator(&item) {
            item = missing_type_item(i.rb(), item);
            emit_token_item(&mut i, item);
            item = match type_after_separator(i.rb()) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        if !is_type_primary(&item) {
            return handoff(item);
        }
        let exit = type_expr_from_primary(i.rb(), item, baseline, false);
        item = match exit {
            Ok(()) => type_nud_item_after_trivia(i.rb(), LeadingTrivia::default()),
            Err(Either::Left(next)) if is_type_separator(&next) => {
                emit_token_item(&mut i, next);
                match type_after_separator(i.rb()) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                }
            }
            Err(Either::Left(next)) if token_kind(&next) == Some(TokenKind::RParen) => {
                emit_token_item(&mut i, next);
                return Ok(());
            }
            Err(Either::Left(mut next)) if is_type_implicit_boundary(baseline, &next.leading) => {
                let leading = std::mem::take(&mut next.leading);
                emit_leading_trivia(&mut i, &leading);
                next
            }
            Err(Either::Right(end)) => return missing_type_close(i, end.item),
            Err(exit) => return Err(exit),
        };
    }
}

fn type_after_separator(mut i: RewriteIn) -> Result<Item, TailExit> {
    let leading = scan_trivia(i.rb());
    let mut next = type_nud_item_after_trivia(i.rb(), leading);
    if token_kind(&next) == Some(TokenKind::RParen) {
        let leading = std::mem::take(&mut next.leading);
        emit_leading_trivia(&mut i, &leading);
        emit_token_item(&mut i, next);
        return Err(Ok(()));
    }
    if matches!(&next.payload, Payload::Eof) {
        next = missing_type_item(i.rb(), next);
        return Err(missing_type_close(i, next));
    }
    if is_type_primary(&next) {
        let leading = std::mem::take(&mut next.leading);
        emit_leading_trivia(&mut i, &leading);
    }
    Ok(next)
}

fn missing_type_item(mut i: RewriteIn, mut item: Item) -> Item {
    let leading = std::mem::take(&mut item.leading);
    emit_missing(&mut i, leading);
    item
}

fn missing_type_close(mut i: RewriteIn, mut item: Item) -> TailExit {
    let leading = std::mem::take(&mut item.leading);
    emit_missing(&mut i, leading);
    handoff(item)
}

fn type_path_tail(mut i: RewriteIn, separator: Item, baseline: usize, type_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::TypePathTail.into());
    emit_token_item(&mut i, separator);
    let trivia = scan_trivia(i.rb());
    let mut segment = type_item_after_trivia(i.rb(), trivia);
    if !type_chain_trivia(&segment.leading, baseline) || is_type_path_boundary(&segment) {
        let leading = std::mem::take(&mut segment.leading);
        emit_missing(&mut i, leading);
        i.state.finish_node();
        return type_tail(i, segment, baseline, type_ml);
    }
    if !is_type_path_segment(&segment) {
        segment = retry_type_path_segment(i.rb(), segment, baseline);
    }
    if !is_type_path_segment(&segment) {
        i.state.finish_node();
        return type_tail(i, segment, baseline, type_ml);
    }
    emit_token_item(&mut i, segment);
    i.state.finish_node();
    scan_type_tail(i, baseline, type_ml)
}

fn retry_type_path_segment(mut i: RewriteIn, mut item: Item, baseline: usize) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_item_after_trivia(i.rb(), leading);
        if is_type_path_segment(&item)
            || !type_chain_trivia(&item.leading, baseline)
            || is_type_path_boundary(&item)
        {
            i.state.finish_node();
            return item;
        }
    }
}

fn type_apply_argument(mut i: RewriteIn, mut argument: Item, baseline: usize) -> TailExit {
    i.state.start_node(SyntaxKind::TypeApplyArgument.into());
    let boundary = std::mem::take(&mut argument.leading);
    emit_leading_trivia(&mut i, &boundary);
    let exit = type_expr_from_primary(i.rb(), argument, baseline, true);
    i.state.finish_node();
    continue_type_tail(i, baseline, false, exit)
}

fn type_arrow_tail(mut i: RewriteIn, arrow: Item, baseline: usize) -> TailExit {
    i.state.start_node(SyntaxKind::TypeArrowTail.into());
    emit_token_item(&mut i, arrow);
    let trivia = scan_trivia(i.rb());
    let mut rhs = type_nud_item_after_trivia(i.rb(), trivia);
    if !type_chain_trivia(&rhs.leading, baseline) || is_type_rhs_boundary(&rhs) {
        let leading = std::mem::take(&mut rhs.leading);
        emit_missing(&mut i, leading);
        i.state.finish_node();
        return handoff(rhs);
    }
    if !is_type_primary(&rhs) {
        rhs = retry_type_rhs(i.rb(), rhs, baseline);
    }
    if !is_type_primary(&rhs) {
        i.state.finish_node();
        return handoff(rhs);
    }
    let exit = type_expr_from_primary(i.rb(), rhs, baseline, false);
    i.state.finish_node();
    exit
}

fn retry_type_rhs(mut i: RewriteIn, mut item: Item, baseline: usize) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if is_type_primary(&item)
            || !type_chain_trivia(&item.leading, baseline)
            || is_type_rhs_boundary(&item)
        {
            i.state.finish_node();
            return item;
        }
    }
}

fn continue_type_tail(i: RewriteIn, baseline: usize, type_ml: bool, exit: TailExit) -> TailExit {
    match exit {
        Ok(()) => scan_type_tail(i, baseline, type_ml),
        Err(Either::Left(item)) => type_tail(i, item, baseline, type_ml),
        Err(Either::Right(end)) => Err(Either::Right(end)),
    }
}

fn is_type_primary(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(
            TokenKind::Identifier
                | TokenKind::SigilIdentifier
                | TokenKind::Integer
                | TokenKind::LParen
                | TokenKind::LBrace
                | TokenKind::Forall
        )
    )
}

fn is_type_record_field_name(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
}

fn is_forall_binder(item: &Item) -> bool {
    matches!(
        &item.payload,
        Payload::Token(token)
            if token.kind == TokenKind::SigilIdentifier && token.text.starts_with('\'')
    )
}

fn is_type_path_segment(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier)
    )
}

fn is_type_path_boundary(item: &Item) -> bool {
    matches!(&item.payload, Payload::Eof)
        || is_type_separator(item)
        || matches!(
            token_kind(item),
            Some(
                TokenKind::Arrow
                    | TokenKind::LParen
                    | TokenKind::RParen
                    | TokenKind::PathSeparator
                    | TokenKind::RBracket
                    | TokenKind::RBrace
            )
        )
}

fn is_type_rhs_boundary(item: &Item) -> bool {
    matches!(&item.payload, Payload::Eof)
        || is_type_separator(item)
        || matches!(
            token_kind(item),
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
}

fn is_type_separator(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Comma | TokenKind::Semicolon)
    )
}

fn type_chain_trivia(leading: &LeadingTrivia, baseline: usize) -> bool {
    indentation_after_newline(leading).is_none_or(|indentation| indentation > baseline)
}

fn is_type_implicit_boundary(baseline: usize, leading: &LeadingTrivia) -> bool {
    indentation_after_newline(leading).is_some_and(|indentation| indentation <= baseline)
}

fn type_delimited_baseline(incoming: usize, opening: &LeadingTrivia) -> usize {
    indentation_after_newline(opening)
        .filter(|&indentation| indentation > incoming)
        .unwrap_or(incoming)
}

fn indentation_after_newline(leading: &LeadingTrivia) -> Option<usize> {
    let mut saw_newline = false;
    let mut at_line_start = false;
    let mut indentation = 0usize;
    for part in &leading.0 {
        match part.kind {
            TriviaKind::Newline => {
                saw_newline = true;
                at_line_start = true;
                indentation = 0;
            }
            TriviaKind::Whitespace if at_line_start => indentation += part.text.chars().count(),
            _ => at_line_start = false,
        }
    }
    saw_newline.then_some(indentation)
}
