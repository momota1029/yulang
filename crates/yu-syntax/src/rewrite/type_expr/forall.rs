//! Forall type owner and its local recovery.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::super::{
    LexIn, RewriteIn, Stops,
    current_item::{AcceptedPayload, CurrentPayload, LineEntry},
    driver::{NormalizedExit, complete, handoff, token_kind},
    emit::{emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{scan_exact_pipe, scan_type_nud_payload},
    operator::{TriviaObservation, observe_fenced_trivia},
    yumark::FenceBoundary,
};
use super::{
    TypeApplyBoundary, TypeMlContext, TypeOuterBoundary, is_forall_binder, is_type_caller_boundary,
    is_type_nud, is_type_outer_boundary, is_type_rhs_boundary, is_type_separator,
    type_chain_trivia, type_expr_from_nud_normalized, type_item_with_pipe_lexical_normalized,
    type_nud_item_with_pipe_lexical_normalized,
};

#[allow(clippy::too_many_arguments)]
pub(super) fn type_forall_normalized(
    mut i: RewriteIn,
    keyword: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::ForallType.into());
    emit_token_item(&mut i, keyword);
    let exit = type_forall_head_normalized(
        i.rb(),
        baseline,
        type_ml.dormant(),
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn type_forall_head_normalized(
    mut i: RewriteIn,
    baseline: usize,
    type_ml: TypeMlContext,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (binder, item_origin, line_entry) = type_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
    );
    if binder.payload_view().is_boundary() {
        let binder = type_forall_missing_binder(i.rb(), binder, true);
        return complete(handoff(binder), line_entry);
    }
    if !type_chain_trivia(binder.leading_view(), baseline) {
        let binder = type_forall_missing_binder(i.rb(), binder, false);
        return complete(handoff(binder), line_entry);
    }
    if token_kind(&binder) == Some(TokenKind::Colon) {
        let binder = type_forall_missing_binder(i.rb(), binder, true);
        return type_forall_body_normalized(
            i,
            binder,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
    if !is_forall_binder(&binder) {
        if is_forall_local_separator(&binder, outer_separators)
            && !is_type_caller_boundary(&binder, caller_stops)
        {
            return type_forall_first_separator_normalized(
                i,
                binder,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        if is_forall_outer_separator(&binder, outer_separators)
            || is_type_outer_boundary(&binder, outer_boundary)
        {
            let binder = type_forall_missing_binder(i.rb(), binder, false);
            return complete(handoff(binder), line_entry);
        }
        if is_forall_boundary(
            &binder,
            baseline,
            outer_separators,
            caller_stops,
            outer_boundary,
        ) {
            let binder = type_forall_missing_binder(i.rb(), binder, true);
            return complete(handoff(binder), line_entry);
        }
        return type_forall_first_malformed_binder_normalized(
            i,
            binder,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }

    let missing_boundary = binder.leading_view().is_grammar_empty();
    type_forall_binder(i.rb(), binder, missing_boundary);
    type_forall_after_binder_normalized(
        i,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn type_forall_after_binder_normalized(
    mut i: RewriteIn,
    baseline: usize,
    type_ml: TypeMlContext,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    loop {
        let (mut next, next_origin, next_line_entry) = type_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
        );
        item_origin = next_origin;
        line_entry = next_line_entry;
        if next.payload_view().is_boundary() {
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(next), line_entry);
        }
        if !type_chain_trivia(next.leading_view(), baseline) {
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(next), line_entry);
        }
        if token_kind(&next) == Some(TokenKind::Colon) {
            return type_forall_body_normalized(
                i,
                next,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        if is_forall_binder(&next) {
            let missing_boundary = next.leading_view().is_grammar_empty();
            type_forall_binder(i.rb(), next, missing_boundary);
            continue;
        }
        if is_forall_local_separator(&next, outer_separators)
            && !is_type_caller_boundary(&next, caller_stops)
        {
            return type_forall_continuation_separator_normalized(
                i,
                next,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        if is_type_outer_boundary(&next, outer_boundary) {
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(next), line_entry);
        }
        if is_forall_boundary(
            &next,
            baseline,
            outer_separators,
            caller_stops,
            outer_boundary,
        ) {
            if !is_forall_outer_separator(&next, outer_separators) {
                next.emit_all_remaining_leading(&mut *i.state);
            }
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(next), line_entry);
        }
        if is_type_nud(&next) {
            next.emit_all_remaining_leading(&mut *i.state);
            emit_missing(&mut i, LeadingTrivia::default());
            return type_expr_from_nud_normalized(
                i,
                next,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                TypeOuterBoundary::NONE,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        return type_forall_malformed_after_binder_normalized(
            i,
            next,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
}

#[allow(clippy::too_many_arguments)]
fn type_forall_first_separator_normalized(
    mut i: RewriteIn,
    separator: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    emit_forall_separator_binder(i.rb(), separator);
    let (next, item_origin, line_entry) = type_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
    );
    if next.payload_view().is_boundary() {
        return complete(handoff(next), line_entry);
    }
    if next.payload_view().is_eof()
        || is_forall_boundary(
            &next,
            baseline,
            outer_separators,
            caller_stops,
            outer_boundary,
        )
    {
        return complete(handoff(next), line_entry);
    }
    if is_forall_local_separator(&next, outer_separators) {
        return type_forall_first_separator_normalized(
            i,
            next,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
    if token_kind(&next) == Some(TokenKind::Colon) {
        return type_forall_body_normalized(
            i,
            next,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
    if is_forall_binder(&next) {
        let missing_boundary = next.leading_view().is_grammar_empty();
        type_forall_binder(i.rb(), next, missing_boundary);
        return type_forall_after_binder_normalized(
            i,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
    if is_type_nud(&next) {
        return complete(handoff(next), line_entry);
    }
    type_forall_first_malformed_binder_normalized(
        i,
        next,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn type_forall_continuation_separator_normalized(
    mut i: RewriteIn,
    separator: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    emit_forall_separator_binder(i.rb(), separator);
    type_forall_after_binder_normalized(
        i,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn type_forall_first_malformed_binder_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::Error.into());
    let mut nested_depth = 0usize;
    loop {
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
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
        (item, item_origin, line_entry) = type_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if nested_depth == 0
            && is_forall_local_separator(&item, outer_separators)
            && !is_type_caller_boundary(&item, caller_stops)
        {
            i.state.finish_node();
            i.state.finish_node();
            return type_forall_first_separator_normalized(
                i,
                item,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        if item.payload_view().is_eof()
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
            return complete(handoff(item), line_entry);
        }
        if nested_depth == 0 && token_kind(&item) == Some(TokenKind::Colon) {
            i.state.finish_node();
            i.state.finish_node();
            return type_forall_body_normalized(
                i,
                item,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        if nested_depth == 0 && is_forall_binder(&item) {
            i.state.finish_node();
            i.state.finish_node();
            let missing_boundary = item.leading_view().is_grammar_empty();
            type_forall_binder(i.rb(), item, missing_boundary);
            return type_forall_after_binder_normalized(
                i,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn type_forall_malformed_after_binder_normalized(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let retry_binder = i
        .rb()
        .map(
            |lex: LexIn| {
                Some(type_forall_malformed_retries_binder(
                    lex,
                    outer_separators,
                    caller_stops,
                    outer_boundary,
                    pipe_lexical,
                    item_origin,
                    line_entry,
                    fence,
                ))
            },
            |(is_binder, indent)| is_binder && indent.is_none_or(|indent| indent > baseline),
        )
        .expect("the forall malformed-retry probe always succeeds");
    if retry_binder {
        return type_forall_retry_binder_normalized(
            i,
            item,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
    type_forall_retry_colon_or_body_normalized(
        i,
        item,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn type_forall_malformed_retries_binder(
    mut i: LexIn,
    outer_separators: bool,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (bool, Option<usize>) {
    let mut source = i.remainder();
    let mut minimum_indentation: Option<usize> = None;
    let mut nested_depth = 0usize;
    loop {
        let Some((
            next,
            next_origin,
            next_line_entry,
            kind,
            is_binder,
            caller_boundary,
            observed_outer_boundary,
            indentation,
        )) = observe_type_nud(
            i.rb(),
            source,
            item_origin,
            line_entry,
            fence,
            caller_stops,
            outer_boundary,
            pipe_lexical,
        )
        else {
            return (false, minimum_indentation);
        };
        source = next;
        item_origin = next_origin;
        line_entry = next_line_entry;
        if nested_depth == 0
            && let Some(indentation) = indentation
        {
            minimum_indentation =
                Some(minimum_indentation.map_or(indentation, |min| min.min(indentation)));
        }
        if nested_depth == 0 {
            if (is_type_rhs_boundary_kind(kind)
                && (outer_separators || !is_type_separator_kind(kind)))
                || caller_boundary
                || observed_outer_boundary
            {
                return (false, minimum_indentation);
            }
            if is_binder {
                return (true, minimum_indentation);
            }
            if kind == Some(TokenKind::Colon) || is_type_nud_kind(kind) {
                return (false, minimum_indentation);
            }
        }
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
    }
}

#[allow(clippy::too_many_arguments)]
fn type_forall_retry_binder_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::Error.into());
    let mut nested_depth = 0usize;
    loop {
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
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
        (item, item_origin, line_entry) = type_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if nested_depth == 0 && is_forall_binder(&item) {
            i.state.finish_node();
            i.state.finish_node();
            let missing_boundary = item.leading_view().is_grammar_empty();
            type_forall_binder(i.rb(), item, missing_boundary);
            return type_forall_after_binder_normalized(
                i,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        if nested_depth == 0
            && is_forall_local_separator(&item, outer_separators)
            && !is_type_caller_boundary(&item, caller_stops)
        {
            i.state.finish_node();
            i.state.finish_node();
            return type_forall_continuation_separator_normalized(
                i,
                item,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        if item.payload_view().is_eof()
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
            return complete(handoff(item), line_entry);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn type_forall_retry_colon_or_body_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::Error.into());
    let mut nested_depth = 0usize;
    loop {
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
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
        (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if nested_depth == 0
            && is_forall_local_separator(&item, outer_separators)
            && !is_type_caller_boundary(&item, caller_stops)
        {
            i.state.finish_node();
            return type_forall_continuation_separator_normalized(
                i,
                item,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        if item.payload_view().is_eof()
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
            return complete(handoff(item), line_entry);
        }
        if nested_depth == 0 && token_kind(&item) == Some(TokenKind::Colon) {
            i.state.finish_node();
            return type_forall_body_normalized(
                i,
                item,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        if nested_depth == 0 && is_type_nud(&item) {
            i.state.finish_node();
            return type_expr_from_nud_normalized(
                i,
                item,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                TypeOuterBoundary::NONE,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
    }
}

fn type_forall_missing_binder(mut i: RewriteIn, mut item: Item, own_leading: bool) -> Item {
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    if own_leading && !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    emit_missing(&mut i, LeadingTrivia::default());
    i.state.finish_node();
    item
}

fn emit_forall_separator_binder(mut i: RewriteIn, mut separator: Item) {
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    separator.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::Error.into());
    emit_token_item(&mut i, separator);
    i.state.finish_node();
    i.state.finish_node();
}

fn type_forall_binder(mut i: RewriteIn, mut binder: Item, missing_boundary: bool) {
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    if missing_boundary {
        emit_missing(&mut i, LeadingTrivia::default());
    }
    binder.emit_all_remaining_leading(&mut *i.state);
    emit_token_item(&mut i, binder);
    i.state.finish_node();
}

#[allow(clippy::too_many_arguments)]
fn type_forall_body_normalized(
    mut i: RewriteIn,
    colon: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    emit_token_item(&mut i, colon);
    let (mut body, mut item_origin, mut line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
    );
    if body.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(body), line_entry);
    }
    if !type_chain_trivia(body.leading_view(), baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(body), line_entry);
    }
    if is_forall_boundary(
        &body,
        baseline,
        outer_separators,
        caller_stops,
        TypeOuterBoundary::NONE,
    ) {
        if !is_forall_outer_separator(&body, outer_separators) {
            body.emit_all_remaining_leading(&mut *i.state);
        }
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(body), line_entry);
    }
    if !is_type_nud(&body) {
        (body, item_origin, line_entry) = type_forall_retry_body_normalized(
            i.rb(),
            body,
            baseline,
            outer_separators,
            caller_stops,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
        if body.payload_view().is_boundary() {
            return complete(handoff(body), line_entry);
        }
        if is_forall_boundary(
            &body,
            baseline,
            outer_separators,
            caller_stops,
            TypeOuterBoundary::NONE,
        ) || !is_type_nud(&body)
        {
            return complete(handoff(body), line_entry);
        }
    }
    body.emit_all_remaining_leading(&mut *i.state);
    type_expr_from_nud_normalized(
        i,
        body,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        TypeOuterBoundary::NONE,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn type_forall_retry_body_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    outer_separators: bool,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    if item.payload_view().is_boundary() {
        return (item, item_origin, line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
        );
        if item.payload_view().is_boundary()
            || is_type_nud(&item)
            || is_forall_boundary(
                &item,
                baseline,
                outer_separators,
                caller_stops,
                TypeOuterBoundary::NONE,
            )
        {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
    }
}

fn observe_type_nud<'source>(
    mut i: LexIn,
    source: &'source str,
    source_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
) -> Option<(
    &'source str,
    usize,
    LineEntry,
    Option<TokenKind>,
    bool,
    bool,
    bool,
    Option<usize>,
)> {
    let TriviaObservation::Visible(visible) =
        observe_fenced_trivia(source, source_origin, line_entry, fence)
    else {
        return None;
    };
    if visible.source.is_empty() {
        return None;
    }

    let payload_origin = source_origin + source.len() - visible.source.len();
    let mut suffix = visible.source;
    let mut lex = chasa_recover::In::new(&mut suffix, i.recovery(), ());
    let accepted = if pipe_lexical && let Some(pipe) = lex.rb().token(scan_exact_pipe) {
        AcceptedPayload {
            payload: CurrentPayload::Token(pipe),
            next_line_entry: LineEntry::InLine,
        }
    } else {
        scan_type_nud_payload(lex, visible.present, payload_origin, fence)?
    };
    let (kind, is_binder, caller_boundary, outer_boundary) = match accepted.payload {
        CurrentPayload::Token(token) => {
            let kind = token.kind;
            let spelling = token.text.as_ref();
            (
                Some(kind),
                kind == TokenKind::SigilIdentifier && spelling.starts_with('\''),
                is_type_caller_boundary_parts(kind, spelling, caller_stops),
                is_type_outer_boundary_parts(kind, spelling, outer_boundary),
            )
        }
        CurrentPayload::Operator(_) => (None, false, false, false),
    };
    let next_origin = payload_origin + visible.source.len() - suffix.len();
    Some((
        suffix,
        next_origin,
        accepted.next_line_entry,
        kind,
        is_binder,
        caller_boundary,
        outer_boundary,
        visible.indentation,
    ))
}

fn is_type_nud_kind(kind: Option<TokenKind>) -> bool {
    matches!(
        kind,
        Some(
            TokenKind::Identifier
                | TokenKind::SigilIdentifier
                | TokenKind::Integer
                | TokenKind::LParen
                | TokenKind::LBrace
                | TokenKind::Forall
                | TokenKind::EffectRowApostrophe
                | TokenKind::PolymorphicVariantColon
                | TokenKind::LBracket
        )
    )
}

fn is_type_rhs_boundary_kind(kind: Option<TokenKind>) -> bool {
    matches!(
        kind,
        Some(
            TokenKind::Comma
                | TokenKind::Semicolon
                | TokenKind::RParen
                | TokenKind::RBracket
                | TokenKind::RBrace
        )
    )
}

fn is_type_separator_kind(kind: Option<TokenKind>) -> bool {
    matches!(kind, Some(TokenKind::Comma | TokenKind::Semicolon))
}

fn is_type_caller_boundary_parts(kind: TokenKind, spelling: &str, caller_stops: Stops) -> bool {
    if super::super::operator::active_stop_item(kind, caller_stops) {
        return true;
    }
    kind == TokenKind::Identifier
        && ((caller_stops & super::super::operator::STOP_WITH != 0 && spelling == "with")
            || (caller_stops & super::super::operator::STOP_IN != 0 && spelling == "in")
            || (caller_stops & super::super::operator::STOP_ELSIF != 0 && spelling == "elsif")
            || (caller_stops & super::super::operator::STOP_ELSE != 0 && spelling == "else"))
}

fn is_type_outer_boundary_parts(
    kind: TokenKind,
    spelling: &str,
    outer_boundary: TypeOuterBoundary,
) -> bool {
    if kind == TokenKind::Pipe {
        return outer_boundary.contains(TypeOuterBoundary::PIPE);
    }
    if kind == TokenKind::Equals {
        return outer_boundary.contains(TypeOuterBoundary::EQUALS);
    }
    kind == TokenKind::Identifier
        && match spelling {
            "derives" => outer_boundary.contains(TypeOuterBoundary::DERIVES),
            "via" => outer_boundary.contains(TypeOuterBoundary::VIA),
            "with" => outer_boundary.contains(TypeOuterBoundary::WITH),
            "impl" => outer_boundary.contains(TypeOuterBoundary::IMPL),
            _ => false,
        }
}

fn is_forall_boundary(
    item: &Item,
    baseline: usize,
    outer_separators: bool,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> bool {
    !type_chain_trivia(item.leading_view(), baseline)
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
