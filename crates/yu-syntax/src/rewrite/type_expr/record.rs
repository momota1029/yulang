//! Named record type owner and its local recovery.

use super::super::ambient_claim::AmbientClaimContext;
use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::super::{
    LexIn, RewriteIn, Stops,
    current_item::{AcceptedPayload, CurrentPayload, LineEntry},
    driver::{
        Either, NormalizedExit, TailExit, advanced_origin, complete, handoff, suffix_marker,
        token_kind,
    },
    emit::{emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{scan_exact_pipe, scan_type_nud_payload},
    operator::{TriviaObservation, observe_fenced_trivia},
    yumark::FenceBoundary,
};
use super::{
    TypeApplyBoundary, TypeMlContext, TypeOuterBoundary, continue_type_tail_normalized,
    delimited::is_explicit_type_caller_close, is_type_caller_boundary, is_type_implicit_boundary,
    is_type_mismatched_close, is_type_nud, is_type_record_field_boundary,
    is_type_record_field_name, is_type_record_field_start, missing_type_close, missing_type_item,
    retry_type_rhs_normalized, type_chain_trivia, type_delimited_baseline,
    type_expr_from_nud_normalized, type_item_with_pipe_lexical_normalized,
    type_nud_item_with_pipe_lexical_normalized, with_type_outer_close,
};

#[allow(clippy::too_many_arguments)]
pub(super) fn type_record_normalized(
    mut i: RewriteIn,
    open: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::NamedRecordType.into());
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = type_record_fields_normalized(
        i.rb(),
        baseline,
        type_ml.dormant(),
        with_type_outer_close(outer_closes, TokenKind::RBrace),
        caller_stops,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_type_tail_normalized(
        i,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        exit,
        item_origin,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn type_record_fields_normalized(
    mut i: RewriteIn,
    incoming_baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let (mut item, next_origin, next_line_entry) = type_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
        ambient,
    );
    item_origin = next_origin;
    line_entry = next_line_entry;
    let baseline = type_delimited_baseline(incoming_baseline, item.leading_view());

    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    if token_kind(&item) == Some(TokenKind::RBrace)
        || !is_explicit_type_caller_close(&item, caller_stops)
    {
        item.emit_all_remaining_leading(&mut *i.state);
    }

    loop {
        if item.payload_view().is_boundary() {
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(item), line_entry);
        }
        if token_kind(&item) == Some(TokenKind::RBrace) {
            emit_token_item(&mut i, item);
            return complete(Ok(()), line_entry);
        }
        if is_type_caller_boundary(&item, caller_stops)
            && !type_record_next_field_normalized(
                i.rb(),
                &item,
                baseline,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
                ambient,
            )
        {
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(item), line_entry);
        }
        if item.payload_view().is_eof() || is_type_mismatched_close(&item, TokenKind::RBrace) {
            return complete(type_record_missing_close(i, item), line_entry);
        }
        if token_kind(&item) == Some(TokenKind::Comma) {
            item = missing_type_item(i.rb(), item);
            emit_token_item(&mut i, item);
            (item, item_origin, line_entry) = match type_record_after_comma_normalized(
                i.rb(),
                baseline,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            ) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        if token_kind(&item) == Some(TokenKind::Semicolon) {
            item.emit_all_remaining_leading(&mut *i.state);
            (item, item_origin, line_entry) = match retry_type_record_separator_normalized(
                i.rb(),
                item,
                baseline,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            ) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }

        let child_entry = suffix_marker(i.rb());
        let exit = if is_type_record_field_name(&item) {
            type_record_field_normalized(
                i.rb(),
                item,
                baseline,
                type_ml,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        } else if token_kind(&item) == Some(TokenKind::Colon) {
            item.emit_all_remaining_leading(&mut *i.state);
            type_record_missing_name_normalized(
                i.rb(),
                item,
                baseline,
                type_ml,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        } else if type_record_malformed_name_colon_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        ) && item.leading_view().indentation_after_newline().is_none()
        {
            type_record_malformed_name_normalized(
                i.rb(),
                item,
                baseline,
                type_ml,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        } else {
            (item, item_origin, line_entry) = match retry_type_record_field_normalized(
                i.rb(),
                item,
                baseline,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            ) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        };

        item_origin = advanced_origin(item_origin, child_entry, i.rb());
        let successor_entry = suffix_marker(i.rb());
        let successor = type_record_successor_normalized(
            i.rb(),
            exit,
            baseline,
            caller_stops,
            pipe_lexical,
            item_origin,
            fence,
            ambient,
        );
        item_origin = advanced_origin(item_origin, successor_entry, i.rb());
        (item, line_entry) = match successor {
            Ok(next) => next,
            Err(exit) => return exit,
        };
    }
}

#[allow(clippy::too_many_arguments)]
fn type_record_field_normalized(
    mut i: RewriteIn,
    name: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::TypeRecordField.into());
    emit_token_item(&mut i, name);
    let (mut colon, next_origin, next_line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
        ambient,
    );
    item_origin = next_origin;
    line_entry = next_line_entry;

    if colon.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return complete(handoff(colon), line_entry);
    }
    if !type_chain_trivia(colon.leading_view(), baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return complete(handoff(colon), line_entry);
    }
    if token_kind(&colon) != Some(TokenKind::Colon) {
        if is_type_record_field_boundary(&colon) {
            if token_kind(&colon) == Some(TokenKind::RBrace)
                || !is_explicit_type_caller_close(&colon, caller_stops)
            {
                colon.emit_all_remaining_leading(&mut *i.state);
            }
            emit_missing(&mut i, LeadingTrivia::default());
            i.state.finish_node();
            return complete(handoff(colon), line_entry);
        }
        if is_type_nud(&colon) {
            colon.emit_all_remaining_leading(&mut *i.state);
            emit_missing(&mut i, LeadingTrivia::default());
            let exit = type_expr_from_nud_normalized(
                i.rb(),
                colon,
                baseline,
                type_ml,
                Some(TypeApplyBoundary::NamedRecord(baseline)),
                true,
                outer_closes,
                caller_stops,
                TypeOuterBoundary::NONE,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
            i.state.finish_node();
            return exit;
        }
        colon.emit_all_remaining_leading(&mut *i.state);
        let exit = retry_type_record_colon_normalized(
            i.rb(),
            colon,
            baseline,
            type_ml,
            outer_closes,
            caller_stops,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        i.state.finish_node();
        return exit;
    }

    emit_token_item(&mut i, colon);
    let exit = type_record_rhs_normalized(
        i.rb(),
        baseline,
        type_ml,
        outer_closes,
        caller_stops,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn type_record_missing_name_normalized(
    mut i: RewriteIn,
    colon: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::TypeRecordField.into());
    emit_missing(&mut i, LeadingTrivia::default());
    emit_token_item(&mut i, colon);
    let exit = type_record_rhs_normalized(
        i.rb(),
        baseline,
        type_ml,
        outer_closes,
        caller_stops,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    i.state.finish_node();
    exit
}

fn type_record_malformed_name_colon_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
    _ambient: AmbientClaimContext<'_>,
) -> bool {
    i.rb()
        .map(
            |lex: LexIn| {
                Some(type_record_malformed_name_colon_probe(
                    lex,
                    item_origin,
                    line_entry,
                    fence,
                    pipe_lexical,
                ))
            },
            |has_colon| has_colon,
        )
        .expect("the malformed-name probe always succeeds")
}

fn type_record_malformed_name_colon_probe(
    mut i: LexIn,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
) -> bool {
    let mut source = i.remainder();
    let mut nested_depth = 0usize;
    loop {
        let Some((next, next_origin, next_line_entry, kind, indentation)) =
            observe_type_item(i.rb(), source, item_origin, line_entry, fence, pipe_lexical)
        else {
            return false;
        };
        source = next;
        item_origin = next_origin;
        line_entry = next_line_entry;
        if indentation.is_some() {
            return false;
        }
        match kind {
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
        if nested_depth == 0 && kind == Some(TokenKind::Colon) {
            return true;
        }
        if nested_depth == 0 && is_type_record_probe_boundary(kind) {
            return false;
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn type_record_malformed_name_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::TypeRecordField.into());
    i.state.start_node(SyntaxKind::Error.into());
    let mut nested_depth = 0usize;
    loop {
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if token_kind(&item) == Some(TokenKind::Colon) && nested_depth == 0 {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            let exit = type_record_rhs_normalized(
                i.rb(),
                baseline,
                type_ml,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
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
        if item.payload_view().is_eof()
            || (nested_depth == 0
                && (is_type_record_field_name(&item)
                    || (!was_nested && is_type_record_field_boundary(&item))
                    || is_type_implicit_boundary(baseline, item.leading_view())))
        {
            i.state.finish_node();
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
    }
}

fn type_record_field_head_after_normalized(
    mut i: RewriteIn,
    baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
    _ambient: AmbientClaimContext<'_>,
) -> bool {
    i.rb()
        .map(
            |mut lex: LexIn| {
                let source = lex.remainder();
                Some(
                    observe_type_item(
                        lex.rb(),
                        source,
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                    )
                    .is_some_and(|(_, _, _, kind, indentation)| {
                        kind == Some(TokenKind::Colon)
                            && indentation.is_none_or(|indentation| indentation > baseline)
                    }),
                )
            },
            |has_colon| has_colon,
        )
        .expect("the field-head probe always succeeds")
}

pub(super) fn type_record_next_field_normalized(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
    ambient: AmbientClaimContext<'_>,
) -> bool {
    is_type_record_field_name(item)
        && item.leading_view().indentation_after_newline().is_none()
        && type_record_field_head_after_normalized(
            i.rb(),
            baseline,
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        )
}

#[allow(clippy::too_many_arguments)]
fn retry_type_record_field_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::Error.into());
    let mut nested_depth = 0usize;
    loop {
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            emit_missing(&mut i, LeadingTrivia::default());
            return Err(complete(handoff(item), line_entry));
        }
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            emit_missing(&mut i, LeadingTrivia::default());
            return Err(complete(handoff(item), line_entry));
        }
        if item.payload_view().is_eof() {
            i.state.finish_node();
            return Err(complete(type_record_missing_close(i, item), line_entry));
        }
        if token_kind(&item) == Some(TokenKind::RBrace) && nested_depth == 0 {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            emit_token_item(&mut i, item);
            return Err(complete(Ok(()), line_entry));
        }
        if token_kind(&item) == Some(TokenKind::Comma) && nested_depth == 0 {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            emit_token_item(&mut i, item);
            return type_record_after_comma_normalized(
                i,
                baseline,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
        if token_kind(&item) == Some(TokenKind::Colon)
            && nested_depth == 0
            && type_chain_trivia(item.leading_view(), baseline)
        {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            return Ok((item, item_origin, line_entry));
        }
        if is_type_record_field_name(&item)
            && nested_depth == 0
            && type_chain_trivia(item.leading_view(), baseline)
            && type_record_field_head_after_normalized(
                i.rb(),
                baseline,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
                ambient,
            )
        {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            return Ok((item, item_origin, line_entry));
        }
        if nested_depth == 0 && is_type_caller_boundary(&item, caller_stops) {
            i.state.finish_node();
            emit_missing(&mut i, LeadingTrivia::default());
            return Err(complete(handoff(item), line_entry));
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
            return Err(complete(type_record_missing_close(i, item), line_entry));
        }
        if nested_depth == 0
            && !was_nested
            && is_type_implicit_boundary(baseline, item.leading_view())
        {
            i.state.finish_node();
            return Err(complete(handoff(item), line_entry));
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn retry_type_record_colon_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if token_kind(&item) == Some(TokenKind::Colon) {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return type_record_rhs_normalized(
                i,
                baseline,
                type_ml,
                outer_closes,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
        if !type_chain_trivia(item.leading_view(), baseline)
            || is_type_record_field_boundary(&item)
            || is_type_caller_boundary(&item, caller_stops)
        {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if is_type_nud(&item) {
            i.state.finish_node();
            return type_expr_from_nud_normalized(
                i,
                item,
                baseline,
                type_ml,
                Some(TypeApplyBoundary::NamedRecord(baseline)),
                true,
                outer_closes,
                caller_stops,
                TypeOuterBoundary::NONE,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn type_record_rhs_normalized(
    mut i: RewriteIn,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let (mut rhs, next_origin, next_line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
        ambient,
    );
    item_origin = next_origin;
    line_entry = next_line_entry;
    if rhs.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(rhs), line_entry);
    }
    if !type_chain_trivia(rhs.leading_view(), baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(rhs), line_entry);
    }
    if is_type_record_field_boundary(&rhs) {
        if token_kind(&rhs) == Some(TokenKind::RBrace)
            || !is_explicit_type_caller_close(&rhs, caller_stops)
        {
            rhs.emit_all_remaining_leading(&mut *i.state);
        }
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(rhs), line_entry);
    }
    if !is_type_nud(&rhs) {
        rhs.emit_all_remaining_leading(&mut *i.state);
        (rhs, item_origin, line_entry) = retry_type_rhs_normalized(
            i.rb(),
            rhs,
            baseline,
            caller_stops,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        if rhs.payload_view().is_boundary() {
            return complete(handoff(rhs), line_entry);
        }
        if !type_chain_trivia(rhs.leading_view(), baseline)
            || is_type_caller_boundary(&rhs, caller_stops)
            || !is_type_nud(&rhs)
        {
            return complete(handoff(rhs), line_entry);
        }
    }
    rhs.emit_all_remaining_leading(&mut *i.state);
    type_expr_from_nud_normalized(
        i,
        rhs,
        baseline,
        type_ml,
        Some(TypeApplyBoundary::NamedRecord(baseline)),
        true,
        outer_closes,
        caller_stops,
        TypeOuterBoundary::NONE,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

fn type_record_after_comma_normalized(
    mut i: RewriteIn,
    baseline: usize,
    caller_stops: Stops,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
    let (mut next, item_origin, line_entry) = type_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
        ambient,
    );
    if next.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(complete(handoff(next), line_entry));
    }
    if token_kind(&next) == Some(TokenKind::RBrace) || is_type_record_field_start(&next) {
        next.emit_all_remaining_leading(&mut *i.state);
    }
    if token_kind(&next) == Some(TokenKind::RBrace) {
        emit_token_item(&mut i, next);
        return Err(complete(Ok(()), line_entry));
    }
    if is_type_caller_boundary(&next, caller_stops)
        && !type_record_next_field_normalized(
            i.rb(),
            &next,
            baseline,
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        )
    {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(complete(handoff(next), line_entry));
    }
    if next.payload_view().is_eof() || is_type_mismatched_close(&next, TokenKind::RBrace) {
        next = missing_type_item(i.rb(), next);
        return Err(complete(type_record_missing_close(i, next), line_entry));
    }
    Ok((next, item_origin, line_entry))
}

fn type_record_missing_close(i: RewriteIn, item: Item) -> TailExit {
    missing_type_close(i, item)
}

#[allow(clippy::too_many_arguments)]
fn retry_type_record_separator_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
    i.state.start_node(SyntaxKind::Error.into());
    let mut nested_depth = 0usize;
    loop {
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            emit_missing(&mut i, LeadingTrivia::default());
            return Err(complete(handoff(item), line_entry));
        }
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            emit_missing(&mut i, LeadingTrivia::default());
            return Err(complete(handoff(item), line_entry));
        }
        if item.payload_view().is_eof() {
            i.state.finish_node();
            return Err(complete(type_record_missing_close(i, item), line_entry));
        }
        if token_kind(&item) == Some(TokenKind::RBrace) && nested_depth == 0 {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            emit_token_item(&mut i, item);
            return Err(complete(Ok(()), line_entry));
        }
        if token_kind(&item) == Some(TokenKind::Comma) && nested_depth == 0 {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            emit_token_item(&mut i, item);
            return type_record_after_comma_normalized(
                i,
                baseline,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
        if is_type_record_field_start(&item) && nested_depth == 0 {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            return Ok((item, item_origin, line_entry));
        }
        if nested_depth == 0 && is_type_caller_boundary(&item, caller_stops) {
            i.state.finish_node();
            emit_missing(&mut i, LeadingTrivia::default());
            return Err(complete(handoff(item), line_entry));
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
            return Err(complete(type_record_missing_close(i, item), line_entry));
        }
        if nested_depth == 0
            && !was_nested
            && is_type_implicit_boundary(baseline, item.leading_view())
        {
            i.state.finish_node();
            return Err(complete(handoff(item), line_entry));
        }
    }
}

fn type_record_successor_normalized(
    mut i: RewriteIn,
    exit: NormalizedExit,
    baseline: usize,
    caller_stops: Stops,
    pipe_lexical: bool,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> Result<(Item, LineEntry), NormalizedExit> {
    match exit {
        NormalizedExit::Complete(Err(Either::Left(next)), line_entry)
            if next.payload_view().is_boundary() =>
        {
            emit_missing(&mut i, LeadingTrivia::default());
            Err(complete(handoff(next), line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(next)), line_entry)
            if token_kind(&next) == Some(TokenKind::Comma) =>
        {
            emit_token_item(&mut i, next);
            match type_record_after_comma_normalized(
                i,
                baseline,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            ) {
                Ok((next, _, line_entry)) => Ok((next, line_entry)),
                Err(exit) => Err(exit),
            }
        }
        NormalizedExit::Complete(Err(Either::Left(next)), line_entry)
            if token_kind(&next) == Some(TokenKind::RBrace) =>
        {
            emit_token_item(&mut i, next);
            Err(complete(Ok(()), line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(mut next)), line_entry)
            if type_record_next_field_normalized(
                i.rb(),
                &next,
                baseline,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
                ambient,
            ) =>
        {
            next.emit_all_remaining_leading(&mut *i.state);
            emit_missing(&mut i, LeadingTrivia::default());
            Ok((next, line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(next)), line_entry)
            if is_type_caller_boundary(&next, caller_stops) =>
        {
            emit_missing(&mut i, LeadingTrivia::default());
            Err(complete(handoff(next), line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(mut next)), line_entry)
            if token_kind(&next) == Some(TokenKind::Semicolon) =>
        {
            next.emit_all_remaining_leading(&mut *i.state);
            match retry_type_record_separator_normalized(
                i,
                next,
                baseline,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            ) {
                Ok((next, _, line_entry)) => Ok((next, line_entry)),
                Err(exit) => Err(exit),
            }
        }
        NormalizedExit::Complete(Err(Either::Left(mut next)), line_entry)
            if pipe_lexical && token_kind(&next) == Some(TokenKind::Pipe) =>
        {
            next.emit_all_remaining_leading(&mut *i.state);
            match retry_type_record_separator_normalized(
                i,
                next,
                baseline,
                caller_stops,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            ) {
                Ok((next, _, line_entry)) => Ok((next, line_entry)),
                Err(exit) => Err(exit),
            }
        }
        NormalizedExit::Complete(Err(Either::Left(next)), line_entry)
            if is_type_mismatched_close(&next, TokenKind::RBrace) =>
        {
            Err(complete(type_record_missing_close(i, next), line_entry))
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            Err(complete(type_record_missing_close(i, end.item), line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(mut next)), line_entry)
            if is_type_record_field_start(&next)
                && is_type_implicit_boundary(baseline, next.leading_view()) =>
        {
            next.emit_all_remaining_leading(&mut *i.state);
            Ok((next, line_entry))
        }
        NormalizedExit::Complete(exit, line_entry) => Err(complete(exit, line_entry)),
        _ => unreachable!("normalized Type owners do not defer"),
    }
}

fn observe_type_item<'source>(
    mut i: LexIn,
    source: &'source str,
    source_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
) -> Option<(
    &'source str,
    usize,
    LineEntry,
    Option<TokenKind>,
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
    let kind = match accepted.payload {
        CurrentPayload::Token(token) => Some(token.kind),
        CurrentPayload::Operator(_) => None,
    };
    let next_origin = payload_origin + visible.source.len() - suffix.len();
    Some((
        suffix,
        next_origin,
        accepted.next_line_entry,
        kind,
        visible.indentation,
    ))
}

fn is_type_record_probe_boundary(kind: Option<TokenKind>) -> bool {
    matches!(
        kind,
        Some(
            TokenKind::Identifier
                | TokenKind::Comma
                | TokenKind::Semicolon
                | TokenKind::RBrace
                | TokenKind::RParen
                | TokenKind::RBracket
        )
    )
}
