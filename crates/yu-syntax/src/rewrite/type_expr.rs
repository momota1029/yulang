//! Standalone source-free direct TypeExpression core.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn,
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
    Some(type_expr_from_nud(i, primary, 0, false, None))
}

fn type_expr_from_nud(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
) -> TailExit {
    if token_kind(&primary) == Some(TokenKind::LBracket) {
        i.state.start_node(SyntaxKind::TypeExpression.into());
        let exit = type_leading_bracket_row(i.rb(), primary, baseline, type_ml, record_base);
        i.state.finish_node();
        return exit;
    }
    type_expr_from_primary(i, primary, baseline, type_ml, record_base)
}

fn type_expr_from_primary(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
) -> TailExit {
    i.state.start_node(SyntaxKind::TypeExpression.into());
    let exit = type_expr_from_primary_started(i.rb(), primary, baseline, type_ml, record_base);
    i.state.finish_node();
    exit
}

fn type_expr_from_primary_started(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
) -> TailExit {
    match token_kind(&primary) {
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier | TokenKind::Integer) => {
            emit_token_item(&mut i, primary);
            scan_type_tail(i.rb(), baseline, type_ml, record_base)
        }
        Some(TokenKind::LParen) => type_group(i.rb(), primary, baseline, type_ml, record_base),
        Some(TokenKind::LBrace) => type_record(i.rb(), primary, baseline, type_ml, record_base),
        Some(TokenKind::Forall) => type_forall(i.rb(), primary, baseline, record_base),
        Some(TokenKind::EffectRowApostrophe) => {
            type_effect_row(i.rb(), primary, baseline, type_ml, record_base)
        }
        Some(TokenKind::PolymorphicVariantColon) => {
            type_polymorphic_variant(i.rb(), primary, baseline, type_ml, record_base)
        }
        _ => unreachable!("the type NUD scanner accepts only type primaries"),
    }
}

fn scan_type_tail(
    mut i: RewriteIn,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = type_item_after_trivia(i.rb(), leading);
    type_tail(i, item, baseline, type_ml, record_base)
}

fn type_tail(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
) -> TailExit {
    if !type_chain_trivia(&item.leading, baseline) {
        return handoff(item);
    }
    if type_ml && !item.leading.0.is_empty() {
        return handoff(item);
    }
    match token_kind(&item) {
        Some(TokenKind::Arrow) => return type_arrow_tail(i.rb(), item, baseline, record_base),
        Some(TokenKind::LParen) if item.leading.0.is_empty() => {
            return type_call_tail(i.rb(), item, baseline, type_ml, record_base);
        }
        Some(TokenKind::PathSeparator) => {
            return type_path_tail(i.rb(), item, baseline, type_ml, record_base);
        }
        Some(TokenKind::LBracket) => {
            return type_bracket_arrow_tail(i.rb(), item, baseline, record_base);
        }
        _ => {}
    }
    if record_base.is_some_and(|base| type_record_next_field(i.rb(), &item, base)) {
        return handoff(item);
    }
    if !item.leading.0.is_empty() && is_type_primary(&item) {
        return type_apply_argument(i, item, baseline, record_base);
    }
    handoff(item)
}

fn type_leading_bracket_row(
    mut i: RewriteIn,
    open: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
) -> TailExit {
    let exit = type_bracket_row(i.rb(), open, baseline);
    let Ok(()) = exit else {
        if let Err(Either::Right(end)) = exit {
            emit_missing(&mut i, LeadingTrivia::default());
            return Err(Either::Right(end));
        }
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
            return type_expr_from_primary_started(i, head, baseline, type_ml, record_base);
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
        return retry_leading_bracket_row_head_error(i, head, baseline, type_ml, record_base);
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
    record_base: Option<usize>,
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
            return type_expr_from_primary_started(i, head, baseline, type_ml, record_base);
        }
        if token_kind(&head) == Some(TokenKind::LBracket) {
            i.state.finish_node();
            return handoff(head);
        }
    }
}

fn type_bracket_arrow_tail(
    mut i: RewriteIn,
    mut open: Item,
    baseline: usize,
    record_base: Option<usize>,
) -> TailExit {
    let leading = std::mem::take(&mut open.leading);
    emit_leading_trivia(&mut i, &leading);
    i.state.start_node(SyntaxKind::TypeArrowTail.into());
    let exit = type_bracket_row(i.rb(), open, baseline);
    let exit = match exit {
        Ok(()) => type_bracket_arrow_after_row(i.rb(), baseline, record_base),
        Err(Either::Right(end)) => {
            emit_missing(&mut i, LeadingTrivia::default());
            Err(Either::Right(end))
        }
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

fn type_bracket_arrow_after_row(
    mut i: RewriteIn,
    baseline: usize,
    record_base: Option<usize>,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let mut arrow = type_nud_item_after_trivia(i.rb(), leading);
    if !type_chain_trivia(&arrow.leading, baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(arrow);
    }
    if token_kind(&arrow) == Some(TokenKind::Arrow) {
        return type_arrow_rhs(i, arrow, baseline, record_base);
    }
    if is_type_nud(&arrow) {
        let leading = std::mem::take(&mut arrow.leading);
        emit_missing(&mut i, leading);
        return type_expr_from_nud(i, arrow, baseline, false, record_base);
    }
    if is_type_rhs_boundary(&arrow) {
        let leading = std::mem::take(&mut arrow.leading);
        emit_missing(&mut i, leading);
    }
    handoff(arrow)
}

fn type_group(
    mut i: RewriteIn,
    open: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
) -> TailExit {
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
    continue_type_tail(i, baseline, type_ml, record_base, exit)
}

fn type_call_tail(
    mut i: RewriteIn,
    open: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
) -> TailExit {
    i.state.start_node(SyntaxKind::TypeCallTail.into());
    emit_token_item(&mut i, open);
    let exit = type_delimited(
        i.rb(),
        TokenKind::RParen,
        baseline,
        TypeDelimitedOwner::Generic,
    );
    i.state.finish_node();
    continue_type_tail(i, baseline, type_ml, record_base, exit)
}

fn type_record(
    mut i: RewriteIn,
    open: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
) -> TailExit {
    i.state.start_node(SyntaxKind::NamedRecordType.into());
    emit_token_item(&mut i, open);
    let exit = type_record_fields(i.rb(), baseline);
    i.state.finish_node();
    continue_type_tail(i, baseline, type_ml, record_base, exit)
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
        if matches!(&item.payload, Payload::Eof)
            || is_type_mismatched_close(&item, TokenKind::RBrace)
        {
            return type_record_missing_close(i, item);
        }
        if token_kind(&item) == Some(TokenKind::Comma) {
            item = missing_type_item(i.rb(), item);
            emit_token_item(&mut i, item);
            item = match type_record_after_comma(i.rb()) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        if token_kind(&item) == Some(TokenKind::Semicolon) {
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            item = match retry_type_record_separator(i.rb(), item, baseline) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        let exit = if is_type_record_field_name(&item) {
            type_record_field(i.rb(), item, baseline)
        } else if token_kind(&item) == Some(TokenKind::Colon) {
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            type_record_missing_name(i.rb(), item, baseline)
        } else {
            let malformed_name_colon = i
                .rb()
                .then(type_record_malformed_name_colon, |has_colon, _| has_colon)
                .expect("the malformed-name probe always succeeds");
            if malformed_name_colon && indentation_after_newline(&item.leading).is_none() {
                type_record_malformed_name(i.rb(), item, baseline)
            } else {
                item = match retry_type_record_field(i.rb(), item, baseline) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                };
                continue;
            }
        };
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
            let exit = type_expr_from_nud(i.rb(), colon, baseline, false, Some(baseline));
            i.state.finish_node();
            return exit;
        }
        let leading = std::mem::take(&mut colon.leading);
        emit_leading_trivia(&mut i, &leading);
        let exit = retry_type_record_colon(i.rb(), colon, baseline);
        i.state.finish_node();
        return exit;
    }
    emit_token_item(&mut i, colon);
    let exit = type_record_rhs(i.rb(), baseline);
    i.state.finish_node();
    exit
}

fn type_record_missing_name(mut i: RewriteIn, colon: Item, baseline: usize) -> TailExit {
    i.state.start_node(SyntaxKind::TypeRecordField.into());
    emit_missing(&mut i, LeadingTrivia::default());
    emit_token_item(&mut i, colon);
    let exit = type_record_rhs(i.rb(), baseline);
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

fn type_record_malformed_name(mut i: RewriteIn, mut item: Item, baseline: usize) -> TailExit {
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
            let exit = type_record_rhs(i.rb(), baseline);
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

fn type_record_next_field(mut i: RewriteIn, item: &Item, baseline: usize) -> bool {
    is_type_record_field_name(item)
        && indentation_after_newline(&item.leading).is_none()
        && type_record_field_head_after(i.rb(), baseline)
}

fn retry_type_record_field(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
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
            return type_record_after_comma(i);
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

fn retry_type_record_colon(mut i: RewriteIn, mut item: Item, baseline: usize) -> TailExit {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if token_kind(&item) == Some(TokenKind::Colon) {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return type_record_rhs(i, baseline);
        }
        if !type_chain_trivia(&item.leading, baseline) || is_type_record_field_boundary(&item) {
            i.state.finish_node();
            return handoff(item);
        }
        if is_type_nud(&item) {
            i.state.finish_node();
            return type_expr_from_nud(i, item, baseline, false, Some(baseline));
        }
    }
}

fn type_record_rhs(mut i: RewriteIn, baseline: usize) -> TailExit {
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
        rhs = retry_type_rhs(i.rb(), rhs, baseline);
        if !type_chain_trivia(&rhs.leading, baseline) || !is_type_nud(&rhs) {
            return handoff(rhs);
        }
    }
    let leading = std::mem::take(&mut rhs.leading);
    emit_leading_trivia(&mut i, &leading);
    type_expr_from_nud(i, rhs, baseline, false, Some(baseline))
}

fn type_record_after_comma(mut i: RewriteIn) -> Result<Item, TailExit> {
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
            return type_record_after_comma(i);
        }
        if is_type_record_field_start(&item) && nested_depth == 0 {
            i.state.finish_node();
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            return Ok(item);
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
) -> Result<Item, TailExit> {
    match exit {
        Err(Either::Left(next)) if token_kind(&next) == Some(TokenKind::Comma) => {
            emit_token_item(&mut i, next);
            type_record_after_comma(i)
        }
        Err(Either::Left(mut next)) if token_kind(&next) == Some(TokenKind::Semicolon) => {
            let leading = std::mem::take(&mut next.leading);
            emit_leading_trivia(&mut i, &leading);
            retry_type_record_separator(i, next, baseline)
        }
        Err(Either::Left(next)) if token_kind(&next) == Some(TokenKind::RBrace) => {
            emit_token_item(&mut i, next);
            Err(Ok(()))
        }
        Err(Either::Left(next)) if is_type_mismatched_close(&next, TokenKind::RBrace) => {
            Err(type_record_missing_close(i, next))
        }
        Err(Either::Right(end)) => Err(type_record_missing_close(i, end.item)),
        Err(Either::Left(mut next)) if type_record_next_field(i.rb(), &next, baseline) => {
            let leading = std::mem::take(&mut next.leading);
            emit_leading_trivia(&mut i, &leading);
            emit_missing(&mut i, LeadingTrivia::default());
            Ok(next)
        }
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

fn type_forall(
    mut i: RewriteIn,
    keyword: Item,
    baseline: usize,
    record_base: Option<usize>,
) -> TailExit {
    i.state.start_node(SyntaxKind::ForallType.into());
    emit_token_item(&mut i, keyword);
    let leading = scan_trivia(i.rb());
    let binder = type_item_after_trivia(i.rb(), leading);
    if !type_chain_trivia(&binder.leading, baseline) {
        let binder = type_forall_missing_binder(i.rb(), binder, false);
        i.state.finish_node();
        return handoff(binder);
    }
    if token_kind(&binder) == Some(TokenKind::Colon) {
        let binder = type_forall_missing_binder(i.rb(), binder, true);
        let exit = type_forall_body(i.rb(), binder, baseline, record_base);
        i.state.finish_node();
        return exit;
    }
    if !is_forall_binder(&binder) {
        if is_type_rhs_boundary(&binder) {
            let binder = type_forall_missing_binder(i.rb(), binder, true);
            i.state.finish_node();
            return handoff(binder);
        }
        i.state.finish_node();
        return handoff(binder);
    }
    let missing_boundary = binder.leading.0.is_empty();
    type_forall_binder(i.rb(), binder, missing_boundary);
    let exit = type_forall_after_binder(i.rb(), baseline, record_base);
    i.state.finish_node();
    exit
}

fn type_forall_after_binder(
    mut i: RewriteIn,
    baseline: usize,
    record_base: Option<usize>,
) -> TailExit {
    loop {
        let leading = scan_trivia(i.rb());
        let mut next = type_item_after_trivia(i.rb(), leading);
        if !type_chain_trivia(&next.leading, baseline) {
            emit_missing(&mut i, LeadingTrivia::default());
            return handoff(next);
        }
        if token_kind(&next) == Some(TokenKind::Colon) {
            return type_forall_body(i, next, baseline, record_base);
        }
        if is_forall_binder(&next) {
            let missing_boundary = next.leading.0.is_empty();
            type_forall_binder(i.rb(), next, missing_boundary);
            continue;
        }
        if is_type_nud(&next) {
            let leading = std::mem::take(&mut next.leading);
            emit_missing(&mut i, leading);
            return type_expr_from_nud(i, next, baseline, false, record_base);
        }
        if is_type_rhs_boundary(&next) {
            let leading = std::mem::take(&mut next.leading);
            emit_missing(&mut i, leading);
        }
        return handoff(next);
    }
}

fn type_forall_missing_binder(mut i: RewriteIn, mut item: Item, own_leading: bool) -> Item {
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    let leading = own_leading
        .then(|| std::mem::take(&mut item.leading))
        .unwrap_or_default();
    emit_missing(&mut i, leading);
    i.state.finish_node();
    item
}

fn type_forall_binder(mut i: RewriteIn, mut binder: Item, missing_boundary: bool) {
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    let leading = std::mem::take(&mut binder.leading);
    if missing_boundary {
        emit_missing(&mut i, LeadingTrivia::default());
    } else {
        emit_leading_trivia(&mut i, &leading);
    }
    emit_token_item(&mut i, binder);
    i.state.finish_node();
}

fn type_forall_body(
    mut i: RewriteIn,
    colon: Item,
    baseline: usize,
    record_base: Option<usize>,
) -> TailExit {
    emit_token_item(&mut i, colon);
    let leading = scan_trivia(i.rb());
    let mut body = type_nud_item_after_trivia(i.rb(), leading);
    if !type_chain_trivia(&body.leading, baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(body);
    }
    if is_type_rhs_boundary(&body) {
        let leading = std::mem::take(&mut body.leading);
        emit_missing(&mut i, leading);
        return handoff(body);
    }
    if !is_type_nud(&body) {
        return handoff(body);
    }
    let leading = std::mem::take(&mut body.leading);
    emit_leading_trivia(&mut i, &leading);
    type_expr_from_nud(i, body, baseline, false, record_base)
}

fn type_effect_row(
    mut i: RewriteIn,
    apostrophe: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
) -> TailExit {
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
    continue_type_tail(i, baseline, type_ml, record_base, exit)
}

fn type_polymorphic_variant(
    mut i: RewriteIn,
    colon: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
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
    continue_type_tail(i, baseline, type_ml, record_base, exit)
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
    let exit = type_expr_from_nud(i.rb(), primary, baseline, true, None);
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
    if owner == TypeDelimitedOwner::BracketRow && matches!(&item.payload, Payload::Eof) {
        item = missing_type_item(i.rb(), item);
        return missing_bracket_row_close(i, item, baseline);
    }
    loop {
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if matches!(&item.payload, Payload::Eof) {
            if owner == TypeDelimitedOwner::BracketRow {
                return missing_bracket_row_close(i, item, baseline);
            }
            return missing_type_close(i, item);
        }
        if owner == TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&item, close) {
            let leading = std::mem::take(&mut item.leading);
            emit_missing(&mut i, leading);
            return retry_bracket_row_close(i.rb(), item, close, baseline);
        }
        if is_type_separator(&item) {
            item = missing_type_item(i.rb(), item);
            emit_token_item(&mut i, item);
            item = match type_after_separator(i.rb(), close, owner, baseline) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        if !is_type_nud(&item) {
            if owner != TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&item, close) {
                return handoff(item);
            }
            item = match retry_type_delimited_item(i.rb(), item, close, owner, baseline) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        let exit = type_expr_from_nud(i.rb(), item, baseline, false, None);
        item = match exit {
            Ok(()) => type_nud_item_after_trivia(i.rb(), LeadingTrivia::default()),
            Err(Either::Left(next)) if is_type_separator(&next) => {
                emit_token_item(&mut i, next);
                match type_after_separator(i.rb(), close, owner, baseline) {
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
                return retry_bracket_row_close(i.rb(), next, close, baseline);
            }
            Err(Either::Left(mut next))
                if owner == TypeDelimitedOwner::BracketRow
                    && is_type_deeper_newline(baseline, &next.leading)
                    && is_type_nud(&next) =>
            {
                emit_missing(&mut i, LeadingTrivia::default());
                let leading = std::mem::take(&mut next.leading);
                emit_leading_trivia(&mut i, &leading);
                next
            }
            Err(Either::Left(next))
                if owner == TypeDelimitedOwner::BracketRow
                    && type_chain_trivia(&next.leading, baseline)
                    && !is_type_deeper_newline(baseline, &next.leading)
                    && !is_type_nud(&next) =>
            {
                match retry_type_delimited_item(
                    i.rb(),
                    next,
                    close,
                    TypeDelimitedOwner::BracketRow,
                    baseline,
                ) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                }
            }
            Err(Either::Left(next))
                if owner == TypeDelimitedOwner::BracketRow
                    && is_type_deeper_newline(baseline, &next.leading) =>
            {
                emit_missing(&mut i, LeadingTrivia::default());
                return handoff(next);
            }
            Err(Either::Left(mut next)) if is_type_implicit_boundary(baseline, &next.leading) => {
                let leading = std::mem::take(&mut next.leading);
                emit_leading_trivia(&mut i, &leading);
                next
            }
            Err(Either::Right(end)) => {
                if owner == TypeDelimitedOwner::BracketRow {
                    return missing_bracket_row_close(i, end.item, baseline);
                }
                return missing_type_close(i, end.item);
            }
            Err(exit) => return Err(exit),
        };
    }
}

fn retry_type_delimited_item(
    mut i: RewriteIn,
    mut item: Item,
    close: TokenKind,
    owner: TypeDelimitedOwner,
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
            return type_after_separator(i, close, owner, baseline);
        }
        if is_type_implicit_boundary(baseline, &item.leading) {
            i.state.finish_node();
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            return Ok(item);
        }
        if matches!(&item.payload, Payload::Eof) {
            i.state.finish_node();
            return Err(if owner == TypeDelimitedOwner::BracketRow {
                missing_bracket_row_close(i, item, baseline)
            } else {
                missing_type_close(i, item)
            });
        }
        if owner != TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&item, close) {
            i.state.finish_node();
            return Err(handoff(item));
        }
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        if is_type_nud(&item) {
            i.state.finish_node();
            return Ok(item);
        }
        if is_type_mismatched_close(&item, close) {
            i.state.finish_node();
            return Err(retry_bracket_row_close(i, item, close, baseline));
        }
    }
}

fn retry_bracket_row_close(
    mut i: RewriteIn,
    mut item: Item,
    close: TokenKind,
    baseline: usize,
) -> TailExit {
    loop {
        i.state.start_node(SyntaxKind::Error.into());
        emit_token_item(&mut i, item);
        i.state.finish_node();
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if matches!(&item.payload, Payload::Eof) {
            return missing_bracket_row_close(i, item, baseline);
        }
        if !is_type_mismatched_close(&item, close) {
            emit_missing(&mut i, LeadingTrivia::default());
            return handoff(item);
        }
    }
}

fn type_after_separator(
    mut i: RewriteIn,
    close: TokenKind,
    owner: TypeDelimitedOwner,
    baseline: usize,
) -> Result<Item, TailExit> {
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
    if owner == TypeDelimitedOwner::BracketRow && is_type_mismatched_close(&next, close) {
        next = missing_type_item(i.rb(), next);
        return Err(retry_bracket_row_close(i, next, close, baseline));
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

fn missing_bracket_row_close(mut i: RewriteIn, item: Item, baseline: usize) -> TailExit {
    if is_type_implicit_boundary(baseline, &item.leading) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(item);
    }
    missing_type_close(i, item)
}

fn type_path_tail(
    mut i: RewriteIn,
    separator: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
) -> TailExit {
    i.state.start_node(SyntaxKind::TypePathTail.into());
    emit_token_item(&mut i, separator);
    let trivia = scan_trivia(i.rb());
    let mut segment = type_item_after_trivia(i.rb(), trivia);
    if !type_chain_trivia(&segment.leading, baseline) || is_type_path_boundary(&segment) {
        let leading = std::mem::take(&mut segment.leading);
        emit_missing(&mut i, leading);
        i.state.finish_node();
        return type_tail(i, segment, baseline, type_ml, record_base);
    }
    if !is_type_path_segment(&segment) {
        segment = retry_type_path_segment(i.rb(), segment, baseline);
    }
    if !is_type_path_segment(&segment) {
        i.state.finish_node();
        return type_tail(i, segment, baseline, type_ml, record_base);
    }
    emit_token_item(&mut i, segment);
    i.state.finish_node();
    scan_type_tail(i, baseline, type_ml, record_base)
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

fn type_apply_argument(
    mut i: RewriteIn,
    mut argument: Item,
    baseline: usize,
    record_base: Option<usize>,
) -> TailExit {
    i.state.start_node(SyntaxKind::TypeApplyArgument.into());
    let boundary = std::mem::take(&mut argument.leading);
    emit_leading_trivia(&mut i, &boundary);
    let exit = type_expr_from_nud(i.rb(), argument, baseline, true, None);
    i.state.finish_node();
    continue_type_tail(i, baseline, false, record_base, exit)
}

fn type_arrow_tail(
    mut i: RewriteIn,
    arrow: Item,
    baseline: usize,
    record_base: Option<usize>,
) -> TailExit {
    i.state.start_node(SyntaxKind::TypeArrowTail.into());
    let exit = type_arrow_rhs(i.rb(), arrow, baseline, record_base);
    i.state.finish_node();
    exit
}

fn type_arrow_rhs(
    mut i: RewriteIn,
    arrow: Item,
    baseline: usize,
    record_base: Option<usize>,
) -> TailExit {
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
    let exit = type_expr_from_nud(i.rb(), rhs, baseline, false, record_base);
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

fn continue_type_tail(
    i: RewriteIn,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
    exit: TailExit,
) -> TailExit {
    match exit {
        Ok(()) => scan_type_tail(i, baseline, type_ml, record_base),
        Err(Either::Left(item)) => type_tail(i, item, baseline, type_ml, record_base),
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

fn is_type_record_field_start(item: &Item) -> bool {
    is_type_record_field_name(item) || token_kind(item) == Some(TokenKind::Colon)
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

fn is_type_record_field_boundary(item: &Item) -> bool {
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

fn is_type_deeper_newline(baseline: usize, leading: &LeadingTrivia) -> bool {
    indentation_after_newline(leading).is_some_and(|indentation| indentation > baseline)
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
