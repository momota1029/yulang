//! Forall type owner and its local recovery.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::super::{
    LexIn, RewriteIn, Stops,
    driver::{TailExit, handoff, token_kind},
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{scan_trivia, type_item_after_trivia, type_nud_item_after_trivia},
};
use super::{
    TypeApplyBoundary, TypeOuterBoundary, indentation_after_newline, is_forall_binder,
    is_type_caller_boundary, is_type_nud, is_type_outer_boundary, is_type_rhs_boundary,
    is_type_separator, type_chain_trivia, type_expr_from_nud,
};

pub(super) fn type_forall(
    mut i: RewriteIn,
    keyword: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
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
        let exit = type_forall_body(
            i.rb(),
            binder,
            baseline,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
        );
        i.state.finish_node();
        return exit;
    }
    if !is_forall_binder(&binder) {
        if is_forall_local_separator(&binder, outer_separators)
            && !is_type_caller_boundary(&binder, caller_stops)
        {
            let exit = type_forall_first_separator(
                i.rb(),
                binder,
                baseline,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
            );
            i.state.finish_node();
            return exit;
        }
        if is_forall_outer_separator(&binder, outer_separators) {
            let binder = type_forall_missing_binder(i.rb(), binder, false);
            i.state.finish_node();
            return handoff(binder);
        }
        if is_type_outer_boundary(&binder, outer_boundary) {
            let binder = type_forall_missing_binder(i.rb(), binder, false);
            i.state.finish_node();
            return handoff(binder);
        }
        if is_forall_boundary(
            &binder,
            baseline,
            outer_separators,
            caller_stops,
            outer_boundary,
        ) {
            let binder = type_forall_missing_binder(i.rb(), binder, true);
            i.state.finish_node();
            return handoff(binder);
        }
        let exit = type_forall_first_malformed_binder(
            i.rb(),
            binder,
            baseline,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
        );
        i.state.finish_node();
        return exit;
    }
    let missing_boundary = binder.leading.0.is_empty();
    type_forall_binder(i.rb(), binder, missing_boundary);
    let exit = type_forall_after_binder(
        i.rb(),
        baseline,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
    );
    i.state.finish_node();
    exit
}

fn type_forall_after_binder(
    mut i: RewriteIn,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> TailExit {
    loop {
        let leading = scan_trivia(i.rb());
        let mut next = type_item_after_trivia(i.rb(), leading);
        if !type_chain_trivia(&next.leading, baseline) {
            emit_missing(&mut i, LeadingTrivia::default());
            return handoff(next);
        }
        if token_kind(&next) == Some(TokenKind::Colon) {
            return type_forall_body(
                i,
                next,
                baseline,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
            );
        }
        if is_forall_binder(&next) {
            let missing_boundary = next.leading.0.is_empty();
            type_forall_binder(i.rb(), next, missing_boundary);
            continue;
        }
        if is_forall_local_separator(&next, outer_separators)
            && !is_type_caller_boundary(&next, caller_stops)
        {
            return type_forall_continuation_separator(
                i,
                next,
                baseline,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
            );
        }
        if is_type_outer_boundary(&next, outer_boundary) {
            emit_missing(&mut i, LeadingTrivia::default());
            return handoff(next);
        }
        if is_forall_boundary(
            &next,
            baseline,
            outer_separators,
            caller_stops,
            outer_boundary,
        ) {
            let leading = if is_forall_outer_separator(&next, outer_separators) {
                LeadingTrivia::default()
            } else {
                std::mem::take(&mut next.leading)
            };
            emit_missing(&mut i, leading);
            return handoff(next);
        }
        if is_type_nud(&next) {
            let leading = std::mem::take(&mut next.leading);
            emit_missing(&mut i, leading);
            return type_expr_from_nud(
                i,
                next,
                baseline,
                false,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
            );
        }
        return type_forall_malformed_after_binder(
            i,
            next,
            baseline,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
        );
    }
}

fn type_forall_first_separator(
    mut i: RewriteIn,
    separator: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> TailExit {
    emit_forall_separator_binder(i.rb(), separator);
    let leading = scan_trivia(i.rb());
    let next = type_item_after_trivia(i.rb(), leading);
    if matches!(next.payload, Payload::Eof)
        || is_forall_boundary(
            &next,
            baseline,
            outer_separators,
            caller_stops,
            outer_boundary,
        )
    {
        return handoff(next);
    }
    if is_forall_local_separator(&next, outer_separators) {
        return type_forall_first_separator(
            i,
            next,
            baseline,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
        );
    }
    if token_kind(&next) == Some(TokenKind::Colon) {
        return type_forall_body(
            i,
            next,
            baseline,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
        );
    }
    if is_forall_binder(&next) {
        let missing_boundary = next.leading.0.is_empty();
        type_forall_binder(i.rb(), next, missing_boundary);
        return type_forall_after_binder(
            i,
            baseline,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
        );
    }
    if is_type_nud(&next) {
        return handoff(next);
    }
    type_forall_first_malformed_binder(
        i,
        next,
        baseline,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
    )
}

fn type_forall_continuation_separator(
    mut i: RewriteIn,
    separator: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> TailExit {
    emit_forall_separator_binder(i.rb(), separator);
    type_forall_after_binder(
        i,
        baseline,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
    )
}

fn type_forall_first_malformed_binder(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> TailExit {
    let leading = std::mem::take(&mut item.leading);
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    emit_leading_trivia(&mut i, &leading);
    i.state.start_node(SyntaxKind::Error.into());
    let mut nested_depth = 0usize;
    loop {
        let kind = token_kind(&item);
        emit_token_item(&mut i, item);
        match kind {
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
        let leading = scan_trivia(i.rb());
        item = type_item_after_trivia(i.rb(), leading);
        if nested_depth == 0
            && is_forall_local_separator(&item, outer_separators)
            && !is_type_caller_boundary(&item, caller_stops)
        {
            i.state.finish_node();
            i.state.finish_node();
            return type_forall_first_separator(
                i,
                item,
                baseline,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
            );
        }
        if matches!(item.payload, Payload::Eof)
            || (nested_depth == 0
                && is_forall_boundary(
                    &item,
                    baseline,
                    outer_separators,
                    caller_stops,
                    outer_boundary,
                ))
        {
            i.state.finish_node();
            i.state.finish_node();
            return handoff(item);
        }
        if nested_depth == 0 && token_kind(&item) == Some(TokenKind::Colon) {
            i.state.finish_node();
            i.state.finish_node();
            return type_forall_body(
                i,
                item,
                baseline,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
            );
        }
        if nested_depth == 0 && is_forall_binder(&item) {
            i.state.finish_node();
            i.state.finish_node();
            let missing_boundary = item.leading.0.is_empty();
            type_forall_binder(i.rb(), item, missing_boundary);
            return type_forall_after_binder(
                i,
                baseline,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
            );
        }
    }
}

fn type_forall_malformed_after_binder(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> TailExit {
    let retry_binder = i
        .rb()
        .then(
            |lex: LexIn| {
                type_forall_malformed_retries_binder(
                    lex,
                    outer_separators,
                    caller_stops,
                    outer_boundary,
                )
            },
            |(is_binder, indent), _| is_binder && indent.is_none_or(|indent| indent > baseline),
        )
        .expect("the forall malformed-retry probe always succeeds");
    if retry_binder {
        return type_forall_retry_binder(
            i,
            item,
            baseline,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
        );
    }
    type_forall_retry_colon_or_body(
        i,
        item,
        baseline,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
    )
}

fn type_forall_malformed_retries_binder(
    mut i: LexIn,
    outer_separators: bool,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> Option<(bool, Option<usize>)> {
    let mut input = i.remainder();
    let mut probe: LexIn = chasa_recover::In::new(&mut input, i.recovery(), ());
    let mut minimum_indentation: Option<usize> = None;
    let mut nested_depth = 0usize;
    loop {
        let leading = scan_trivia(probe.rb());
        if nested_depth == 0 {
            if let Some(indentation) = indentation_after_newline(&leading) {
                minimum_indentation =
                    Some(minimum_indentation.map_or(indentation, |min| min.min(indentation)));
            }
        }
        let item = type_nud_item_after_trivia(probe.rb(), leading);
        if matches!(item.payload, Payload::Eof) {
            return Some((false, minimum_indentation));
        }
        if nested_depth == 0 {
            if (is_type_rhs_boundary(&item) && (outer_separators || !is_type_separator(&item)))
                || is_type_caller_boundary(&item, caller_stops)
                || is_type_outer_boundary(&item, outer_boundary)
            {
                return Some((false, minimum_indentation));
            }
            if is_forall_binder(&item) {
                return Some((true, minimum_indentation));
            }
            if token_kind(&item) == Some(TokenKind::Colon) || is_type_nud(&item) {
                return Some((false, minimum_indentation));
            }
        }
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
    }
}

fn type_forall_retry_binder(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> TailExit {
    let leading = std::mem::take(&mut item.leading);
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    emit_leading_trivia(&mut i, &leading);
    i.state.start_node(SyntaxKind::Error.into());
    let mut nested_depth = 0usize;
    loop {
        let kind = token_kind(&item);
        emit_token_item(&mut i, item);
        match kind {
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
        let leading = scan_trivia(i.rb());
        item = type_item_after_trivia(i.rb(), leading);
        if nested_depth == 0 && is_forall_binder(&item) {
            i.state.finish_node();
            i.state.finish_node();
            let missing_boundary = item.leading.0.is_empty();
            type_forall_binder(i.rb(), item, missing_boundary);
            return type_forall_after_binder(
                i,
                baseline,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
            );
        }
        if nested_depth == 0
            && is_forall_local_separator(&item, outer_separators)
            && !is_type_caller_boundary(&item, caller_stops)
        {
            i.state.finish_node();
            i.state.finish_node();
            return type_forall_continuation_separator(
                i,
                item,
                baseline,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
            );
        }
        if matches!(item.payload, Payload::Eof)
            || (nested_depth == 0
                && is_forall_boundary(
                    &item,
                    baseline,
                    outer_separators,
                    caller_stops,
                    outer_boundary,
                ))
        {
            i.state.finish_node();
            i.state.finish_node();
            return handoff(item);
        }
    }
}

fn type_forall_retry_colon_or_body(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> TailExit {
    let leading = std::mem::take(&mut item.leading);
    emit_leading_trivia(&mut i, &leading);
    i.state.start_node(SyntaxKind::Error.into());
    let mut nested_depth = 0usize;
    loop {
        let kind = token_kind(&item);
        emit_token_item(&mut i, item);
        match kind {
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
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if nested_depth == 0
            && is_forall_local_separator(&item, outer_separators)
            && !is_type_caller_boundary(&item, caller_stops)
        {
            i.state.finish_node();
            return type_forall_continuation_separator(
                i,
                item,
                baseline,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
            );
        }
        if matches!(item.payload, Payload::Eof)
            || (nested_depth == 0
                && is_forall_boundary(
                    &item,
                    baseline,
                    outer_separators,
                    caller_stops,
                    outer_boundary,
                ))
        {
            i.state.finish_node();
            return handoff(item);
        }
        if nested_depth == 0 && token_kind(&item) == Some(TokenKind::Colon) {
            i.state.finish_node();
            return type_forall_body(
                i,
                item,
                baseline,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
            );
        }
        if nested_depth == 0 && is_type_nud(&item) {
            i.state.finish_node();
            return type_expr_from_nud(
                i,
                item,
                baseline,
                false,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
            );
        }
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

fn emit_forall_separator_binder(mut i: RewriteIn, mut separator: Item) {
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    let leading = std::mem::take(&mut separator.leading);
    emit_leading_trivia(&mut i, &leading);
    i.state.start_node(SyntaxKind::Error.into());
    emit_token_item(&mut i, separator);
    i.state.finish_node();
    i.state.finish_node();
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
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    emit_token_item(&mut i, colon);
    let leading = scan_trivia(i.rb());
    let mut body = type_nud_item_after_trivia(i.rb(), leading);
    if !type_chain_trivia(&body.leading, baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(body);
    }
    if is_forall_boundary(
        &body,
        baseline,
        outer_separators,
        caller_stops,
        TypeOuterBoundary::NONE,
    ) {
        let leading = if is_forall_outer_separator(&body, outer_separators) {
            LeadingTrivia::default()
        } else {
            std::mem::take(&mut body.leading)
        };
        emit_missing(&mut i, leading);
        return handoff(body);
    }
    if !is_type_nud(&body) {
        body = type_forall_retry_body(i.rb(), body, baseline, outer_separators, caller_stops);
        if is_forall_boundary(
            &body,
            baseline,
            outer_separators,
            caller_stops,
            TypeOuterBoundary::NONE,
        ) {
            return handoff(body);
        }
        if !is_type_nud(&body) {
            return handoff(body);
        }
    }
    let leading = std::mem::take(&mut body.leading);
    emit_leading_trivia(&mut i, &leading);
    type_expr_from_nud(
        i,
        body,
        baseline,
        false,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
    )
}

fn type_forall_retry_body(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    outer_separators: bool,
    caller_stops: Stops,
) -> Item {
    let leading = std::mem::take(&mut item.leading);
    emit_leading_trivia(&mut i, &leading);
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if is_type_nud(&item)
            || is_forall_boundary(
                &item,
                baseline,
                outer_separators,
                caller_stops,
                TypeOuterBoundary::NONE,
            )
        {
            i.state.finish_node();
            return item;
        }
    }
}

fn is_forall_boundary(
    item: &Item,
    baseline: usize,
    outer_separators: bool,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> bool {
    !type_chain_trivia(&item.leading, baseline)
        || (is_type_rhs_boundary(item) && (outer_separators || !is_type_separator(item)))
        || is_type_caller_boundary(item, caller_stops)
        || is_type_outer_boundary(item, outer_boundary)
}

fn is_forall_outer_separator(item: &Item, outer_separators: bool) -> bool {
    outer_separators && is_type_separator(item)
}

fn is_forall_local_separator(item: &Item, outer_separators: bool) -> bool {
    !outer_separators && is_type_separator(item)
}
