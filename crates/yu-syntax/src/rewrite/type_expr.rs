//! Standalone source-free direct TypeExpression core.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

mod delimited;
mod forall;
mod record;
mod variants;

use super::{
    RewriteIn,
    driver::{Either, TailExit, handoff, token_kind},
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind, TriviaKind},
    lexer::{
        scan_balanced_bracket_suffix, scan_trivia, scan_type_nud_item, type_item_after_trivia,
        type_nud_item_after_trivia,
    },
};

use self::{
    delimited::{TypeDelimitedOwner, type_delimited},
    forall::type_forall,
    record::{type_record, type_record_next_field},
    variants::{type_effect_row, type_polymorphic_variant},
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
