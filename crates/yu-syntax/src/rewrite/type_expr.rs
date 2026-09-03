//! Standalone source-free direct TypeExpression core.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    RewriteIn,
    driver::{Either, TailExit, handoff, token_kind},
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind, TriviaKind},
    lexer::{
        scan_balanced_bracket_suffix, scan_lbrace, scan_lbracket, scan_trivia, scan_type_nud_item,
        type_item_after_trivia, type_nud_item_after_trivia,
    },
};

pub(super) fn type_expr(mut i: RewriteIn) -> Option<TailExit> {
    let primary = i.token(scan_type_nud_item)?;
    Some(type_expr_from_nud(i, primary, 0, false))
}

fn type_expr_from_nud(mut i: RewriteIn, primary: Item, baseline: usize, type_ml: bool) -> TailExit {
    if token_kind(&primary) == Some(TokenKind::LBracket) {
        i.state.start_node(SyntaxKind::TypeExpression.into());
        let exit = type_leading_bracket_row(i.rb(), primary, baseline, type_ml);
        i.state.finish_node();
        return exit;
    }
    type_expr_from_primary(i, primary, baseline, type_ml)
}

fn type_expr_from_primary(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
) -> TailExit {
    i.state.start_node(SyntaxKind::TypeExpression.into());
    let exit = type_expr_from_primary_started(i.rb(), primary, baseline, type_ml);
    i.state.finish_node();
    exit
}

fn type_expr_from_primary_started(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
) -> TailExit {
    match token_kind(&primary) {
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier | TokenKind::Integer) => {
            emit_token_item(&mut i, primary);
            scan_type_tail(i.rb(), baseline, type_ml)
        }
        Some(TokenKind::LParen) => type_group(i.rb(), primary, baseline, type_ml),
        Some(TokenKind::LBrace) => type_record(i.rb(), primary, baseline, type_ml),
        Some(TokenKind::Forall) => type_forall(i.rb(), primary, baseline),
        Some(TokenKind::EffectRowApostrophe) => type_effect_row(i.rb(), primary, baseline, type_ml),
        Some(TokenKind::PolymorphicVariantColon) => {
            type_polymorphic_variant(i.rb(), primary, baseline, type_ml)
        }
        _ => unreachable!("the type NUD scanner accepts only type primaries"),
    }
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
        Some(TokenKind::LBracket) => return type_bracket_arrow_tail(i.rb(), item, baseline),
        _ => {}
    }
    if !item.leading.0.is_empty() && is_type_primary(&item) {
        return type_apply_argument(i, item, baseline);
    }
    handoff(item)
}

fn type_leading_bracket_row(
    mut i: RewriteIn,
    open: Item,
    baseline: usize,
    type_ml: bool,
) -> TailExit {
    let exit = type_bracket_row(i.rb(), open, baseline);
    let Ok(()) = exit else {
        return exit;
    };
    let leading = scan_trivia(i.rb());
    let mut head = type_nud_item_after_trivia(i.rb(), leading);
    loop {
        if !type_chain_trivia(&head.leading, baseline) {
            emit_missing(&mut i, LeadingTrivia::default());
            return handoff(head);
        }
        if is_type_primary(&head) {
            let leading = std::mem::take(&mut head.leading);
            emit_leading_trivia(&mut i, &leading);
            return type_expr_from_primary_started(i, head, baseline, type_ml);
        }
        if token_kind(&head) == Some(TokenKind::LBracket) {
            head = match retry_leading_bracket_row_head(i.rb(), head) {
                Ok(next) => next,
                Err(head) => return handoff(head),
            };
            continue;
        }
        if is_type_rhs_boundary(&head) {
            let leading = std::mem::take(&mut head.leading);
            emit_missing(&mut i, leading);
            return handoff(head);
        }
        let leading = std::mem::take(&mut head.leading);
        emit_leading_trivia(&mut i, &leading);
        return retry_leading_bracket_row_head_error(i, head, baseline, type_ml);
    }
}

fn retry_leading_bracket_row_head(mut i: RewriteIn, head: Item) -> Result<Item, Item> {
    let Some(suffix) = i.token(scan_balanced_bracket_suffix) else {
        return Err(head);
    };
    i.state.start_node(SyntaxKind::Error.into());
    emit_token_item(&mut i, head);
    emit_token_item(
        &mut i,
        Item {
            leading: LeadingTrivia::default(),
            payload: Payload::Token(suffix),
        },
    );
    i.state.finish_node();
    let leading = scan_trivia(i.rb());
    Ok(type_nud_item_after_trivia(i, leading))
}

fn retry_leading_bracket_row_head_error(
    mut i: RewriteIn,
    mut head: Item,
    baseline: usize,
    type_ml: bool,
) -> TailExit {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, head);
        let leading = scan_trivia(i.rb());
        head = type_nud_item_after_trivia(i.rb(), leading);
        if !type_chain_trivia(&head.leading, baseline) || is_type_rhs_boundary(&head) {
            i.state.finish_node();
            return handoff(head);
        }
        if is_type_primary(&head) {
            i.state.finish_node();
            let leading = std::mem::take(&mut head.leading);
            emit_leading_trivia(&mut i, &leading);
            return type_expr_from_primary_started(i, head, baseline, type_ml);
        }
        if token_kind(&head) == Some(TokenKind::LBracket) {
            i.state.finish_node();
            return handoff(head);
        }
    }
}

fn type_bracket_arrow_tail(mut i: RewriteIn, mut open: Item, baseline: usize) -> TailExit {
    let leading = std::mem::take(&mut open.leading);
    emit_leading_trivia(&mut i, &leading);
    i.state.start_node(SyntaxKind::TypeArrowTail.into());
    let exit = type_bracket_row(i.rb(), open, baseline);
    let exit = match exit {
        Ok(()) => type_bracket_arrow_after_row(i.rb(), baseline),
        Err(exit) => Err(exit),
    };
    i.state.finish_node();
    exit
}

fn type_bracket_row(mut i: RewriteIn, open: Item, baseline: usize) -> TailExit {
    i.state.start_node(SyntaxKind::BracketRow.into());
    emit_token_item(&mut i, open);
    let exit = type_delimited(
        i.rb(),
        TokenKind::RBracket,
        baseline,
        TypeDelimitedOwner::BracketRow,
    );
    i.state.finish_node();
    exit
}

fn type_bracket_arrow_after_row(mut i: RewriteIn, baseline: usize) -> TailExit {
    let leading = scan_trivia(i.rb());
    let mut arrow = type_nud_item_after_trivia(i.rb(), leading);
    if !type_chain_trivia(&arrow.leading, baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(arrow);
    }
    if token_kind(&arrow) == Some(TokenKind::Arrow) {
        return type_arrow_rhs(i, arrow, baseline);
    }
    if is_type_nud(&arrow) {
        let leading = std::mem::take(&mut arrow.leading);
        emit_missing(&mut i, leading);
        return type_expr_from_nud(i, arrow, baseline, false);
    }
    if is_type_rhs_boundary(&arrow) {
        let leading = std::mem::take(&mut arrow.leading);
        emit_missing(&mut i, leading);
    }
    handoff(arrow)
}

fn type_group(mut i: RewriteIn, open: Item, baseline: usize, type_ml: bool) -> TailExit {
    i.state
        .start_node(SyntaxKind::ParenthesizedTypeGroup.into());
    emit_token_item(&mut i, open);
    let exit = type_delimited(
        i.rb(),
        TokenKind::RParen,
        baseline,
        TypeDelimitedOwner::Generic,
    );
    i.state.finish_node();
    continue_type_tail(i, baseline, type_ml, exit)
}

fn type_call_tail(mut i: RewriteIn, open: Item, baseline: usize, type_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::TypeCallTail.into());
    emit_token_item(&mut i, open);
    let exit = type_delimited(
        i.rb(),
        TokenKind::RParen,
        baseline,
        TypeDelimitedOwner::Generic,
    );
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
    if !type_chain_trivia(&rhs.leading, baseline) || !is_type_nud(&rhs) {
        i.state.finish_node();
        return handoff(rhs);
    }
    let leading = std::mem::take(&mut rhs.leading);
    emit_leading_trivia(&mut i, &leading);
    let exit = type_expr_from_nud(i.rb(), rhs, baseline, false);
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
            if !type_chain_trivia(&body.leading, baseline) || !is_type_nud(&body) {
                i.state.finish_node();
                return handoff(body);
            }
            let leading = std::mem::take(&mut body.leading);
            emit_leading_trivia(&mut i, &leading);
            let exit = type_expr_from_nud(i.rb(), body, baseline, false);
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

fn type_effect_row(mut i: RewriteIn, apostrophe: Item, baseline: usize, type_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::EffectRowType.into());
    emit_token_item(&mut i, apostrophe);
    let open = i
        .token(scan_lbracket)
        .expect("the effect-row compound probe accepted an adjacent bracket");
    emit_token_item(
        &mut i,
        Item {
            leading: LeadingTrivia::default(),
            payload: Payload::Token(open),
        },
    );
    let exit = type_delimited(
        i.rb(),
        TokenKind::RBracket,
        baseline,
        TypeDelimitedOwner::Generic,
    );
    i.state.finish_node();
    continue_type_tail(i, baseline, type_ml, exit)
}

fn type_polymorphic_variant(
    mut i: RewriteIn,
    colon: Item,
    baseline: usize,
    type_ml: bool,
) -> TailExit {
    i.state
        .start_node(SyntaxKind::PolymorphicVariantType.into());
    emit_token_item(&mut i, colon);
    let open = i
        .token(scan_lbrace)
        .expect("the polymorphic-variant compound probe accepted an adjacent brace");
    emit_token_item(
        &mut i,
        Item {
            leading: LeadingTrivia::default(),
            payload: Payload::Token(open),
        },
    );
    let exit = type_polymorphic_variant_tags(i.rb(), baseline);
    i.state.finish_node();
    continue_type_tail(i, baseline, type_ml, exit)
}

fn type_polymorphic_variant_tags(mut i: RewriteIn, incoming_baseline: usize) -> TailExit {
    let opening = scan_trivia(i.rb());
    let baseline = type_delimited_baseline(incoming_baseline, &opening);
    emit_leading_trivia(&mut i, &opening);
    let mut item = type_nud_item_after_trivia(i.rb(), LeadingTrivia::default());
    loop {
        if token_kind(&item) == Some(TokenKind::RBrace) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if matches!(&item.payload, Payload::Eof) || !is_type_polymorphic_variant_tag_name(&item) {
            return handoff(item);
        }
        let exit = type_polymorphic_variant_tag(i.rb(), item, baseline);
        item = match type_polymorphic_variant_successor(i.rb(), exit, baseline) {
            Ok(next) => next,
            Err(exit) => return exit,
        };
    }
}

fn type_polymorphic_variant_tag(mut i: RewriteIn, name: Item, baseline: usize) -> TailExit {
    i.state.start_node(SyntaxKind::PolymorphicVariantTag.into());
    emit_token_item(&mut i, name);
    let leading = scan_trivia(i.rb());
    let mut item = type_nud_item_after_trivia(i.rb(), leading);
    loop {
        if !is_type_payload_boundary(&item.leading) || !is_type_nud(&item) {
            i.state.finish_node();
            return handoff(item);
        }
        let exit = type_polymorphic_variant_payload(i.rb(), item, baseline);
        item = match exit {
            Ok(()) => type_nud_item_after_trivia(i.rb(), LeadingTrivia::default()),
            Err(Either::Left(next)) => next,
            Err(Either::Right(end)) => {
                i.state.finish_node();
                return Err(Either::Right(end));
            }
        };
    }
}

fn type_polymorphic_variant_payload(
    mut i: RewriteIn,
    mut primary: Item,
    baseline: usize,
) -> TailExit {
    i.state
        .start_node(SyntaxKind::PolymorphicVariantPayload.into());
    let boundary = std::mem::take(&mut primary.leading);
    emit_leading_trivia(&mut i, &boundary);
    let exit = type_expr_from_nud(i.rb(), primary, baseline, true);
    i.state.finish_node();
    exit
}

fn type_polymorphic_variant_successor(
    mut i: RewriteIn,
    exit: TailExit,
    baseline: usize,
) -> Result<Item, TailExit> {
    match exit {
        Err(Either::Left(next)) if token_kind(&next) == Some(TokenKind::Comma) => {
            emit_token_item(&mut i, next);
            let leading = scan_trivia(i.rb());
            let mut next = type_nud_item_after_trivia(i.rb(), leading);
            if token_kind(&next) == Some(TokenKind::RBrace)
                || is_type_polymorphic_variant_tag_name(&next)
            {
                let leading = std::mem::take(&mut next.leading);
                emit_leading_trivia(&mut i, &leading);
            }
            if token_kind(&next) == Some(TokenKind::RBrace) {
                emit_token_item(&mut i, next);
                return Err(Ok(()));
            }
            Ok(next)
        }
        Err(Either::Left(next)) if token_kind(&next) == Some(TokenKind::RBrace) => {
            emit_token_item(&mut i, next);
            Err(Ok(()))
        }
        Err(Either::Left(mut next))
            if is_type_polymorphic_variant_tag_name(&next)
                && is_type_implicit_boundary(baseline, &next.leading) =>
        {
            let leading = std::mem::take(&mut next.leading);
            emit_leading_trivia(&mut i, &leading);
            Ok(next)
        }
        exit => Err(exit),
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum TypeDelimitedOwner {
    Generic,
    BracketRow,
}

fn type_delimited(
    mut i: RewriteIn,
    close: TokenKind,
    incoming_baseline: usize,
    owner: TypeDelimitedOwner,
) -> TailExit {
    let opening = scan_trivia(i.rb());
    let baseline = type_delimited_baseline(incoming_baseline, &opening);
    emit_leading_trivia(&mut i, &opening);
    let mut item = type_nud_item_after_trivia(i.rb(), LeadingTrivia::default());
    loop {
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if matches!(&item.payload, Payload::Eof) {
            return missing_type_close(i, item);
        }
        if owner == TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&item, close) {
            let leading = std::mem::take(&mut item.leading);
            emit_missing(&mut i, leading);
            item = match retry_bracket_row_close(i.rb(), item, close) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        if is_type_separator(&item) {
            item = missing_type_item(i.rb(), item);
            emit_token_item(&mut i, item);
            item = match type_after_separator(i.rb(), close) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        if !is_type_nud(&item) {
            if owner == TypeDelimitedOwner::BracketRow {
                item = match retry_bracket_row_item(i.rb(), item, close, baseline) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                };
                continue;
            }
            return handoff(item);
        }
        let exit = type_expr_from_nud(i.rb(), item, baseline, false);
        item = match exit {
            Ok(()) => type_nud_item_after_trivia(i.rb(), LeadingTrivia::default()),
            Err(Either::Left(next)) if is_type_separator(&next) => {
                emit_token_item(&mut i, next);
                match type_after_separator(i.rb(), close) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                }
            }
            Err(Either::Left(next)) if token_kind(&next) == Some(close) => {
                emit_token_item(&mut i, next);
                return Ok(());
            }
            Err(Either::Left(mut next))
                if owner == TypeDelimitedOwner::BracketRow
                    && is_type_mismatched_close(&next, close) =>
            {
                let leading = std::mem::take(&mut next.leading);
                emit_leading_trivia(&mut i, &leading);
                match retry_bracket_row_close(i.rb(), next, close) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                }
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

fn retry_bracket_row_item(
    mut i: RewriteIn,
    mut item: Item,
    close: TokenKind,
    baseline: usize,
) -> Result<Item, TailExit> {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if token_kind(&item) == Some(close) {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return Err(Ok(()));
        }
        if is_type_separator(&item) {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return type_after_separator(i, close);
        }
        if is_type_implicit_boundary(baseline, &item.leading) {
            i.state.finish_node();
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            return Ok(item);
        }
        if !type_chain_trivia(&item.leading, baseline) {
            i.state.finish_node();
            return Err(handoff(item));
        }
        if matches!(&item.payload, Payload::Eof) {
            i.state.finish_node();
            return Err(missing_type_close(i, item));
        }
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        if is_type_nud(&item) {
            i.state.finish_node();
            return Ok(item);
        }
        if is_type_mismatched_close(&item, close) {
            i.state.finish_node();
            return retry_bracket_row_close(i, item, close);
        }
    }
}

fn retry_bracket_row_close(
    mut i: RewriteIn,
    mut item: Item,
    close: TokenKind,
) -> Result<Item, TailExit> {
    loop {
        i.state.start_node(SyntaxKind::Error.into());
        emit_token_item(&mut i, item);
        i.state.finish_node();
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return Err(Ok(()));
        }
        if matches!(&item.payload, Payload::Eof) {
            return Err(missing_type_close(i, item));
        }
        if !is_type_mismatched_close(&item, close) {
            return Ok(item);
        }
    }
}

fn type_after_separator(mut i: RewriteIn, close: TokenKind) -> Result<Item, TailExit> {
    let leading = scan_trivia(i.rb());
    let mut next = type_nud_item_after_trivia(i.rb(), leading);
    if token_kind(&next) == Some(close) {
        let leading = std::mem::take(&mut next.leading);
        emit_leading_trivia(&mut i, &leading);
        emit_token_item(&mut i, next);
        return Err(Ok(()));
    }
    if matches!(&next.payload, Payload::Eof) {
        next = missing_type_item(i.rb(), next);
        return Err(missing_type_close(i, next));
    }
    if is_type_nud(&next) {
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
    let exit = type_expr_from_nud(i.rb(), argument, baseline, true);
    i.state.finish_node();
    continue_type_tail(i, baseline, false, exit)
}

fn type_arrow_tail(mut i: RewriteIn, arrow: Item, baseline: usize) -> TailExit {
    i.state.start_node(SyntaxKind::TypeArrowTail.into());
    let exit = type_arrow_rhs(i.rb(), arrow, baseline);
    i.state.finish_node();
    exit
}

fn type_arrow_rhs(mut i: RewriteIn, arrow: Item, baseline: usize) -> TailExit {
    emit_token_item(&mut i, arrow);
    let trivia = scan_trivia(i.rb());
    let mut rhs = type_nud_item_after_trivia(i.rb(), trivia);
    if !type_chain_trivia(&rhs.leading, baseline) || is_type_rhs_boundary(&rhs) {
        let leading = std::mem::take(&mut rhs.leading);
        emit_missing(&mut i, leading);
        return handoff(rhs);
    }
    if !is_type_nud(&rhs) {
        rhs = retry_type_rhs(i.rb(), rhs, baseline);
    }
    if !is_type_nud(&rhs) {
        return handoff(rhs);
    }
    let exit = type_expr_from_nud(i.rb(), rhs, baseline, false);
    exit
}

fn retry_type_rhs(mut i: RewriteIn, mut item: Item, baseline: usize) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if is_type_nud(&item)
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
                | TokenKind::EffectRowApostrophe
                | TokenKind::PolymorphicVariantColon
        )
    )
}

fn is_type_nud(item: &Item) -> bool {
    is_type_primary(item) || token_kind(item) == Some(TokenKind::LBracket)
}

fn is_type_record_field_name(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
}

fn is_type_polymorphic_variant_tag_name(item: &Item) -> bool {
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

fn is_type_mismatched_close(item: &Item, expected: TokenKind) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
    ) && token_kind(item) != Some(expected)
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

fn is_type_payload_boundary(leading: &LeadingTrivia) -> bool {
    !leading.0.is_empty() && indentation_after_newline(leading).is_none()
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
