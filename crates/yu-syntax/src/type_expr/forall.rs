//! Forall type owner and its phase-local, forward recovery.

use crate::ambient_claim::AmbientClaimContext;

use crate::syntax_kind::SyntaxKind;

use crate::type_expr::{
    TypeApplyBoundary, TypeMlContext, TypeOuterBoundary, is_forall_binder, is_type_caller_boundary,
    is_type_nud, is_type_outer_boundary, is_type_separator, type_chain_trivia,
    type_expr_from_nud_normalized, type_nud_item_with_pipe_lexical_normalized,
    type_nud_item_with_pipe_lexical_normalized_in_error_run,
};
use crate::{
    cursor::SyntaxIn,
    cursor::recovery::emit::{
        emit_recovery_error_item, emit_recovery_error_run, emit_recovery_missing, emit_token_item,
    },
    handoff::{NormalizedExit, complete, handoff},
    lexical::{
        current_item::LineEntry,
        item::{Item, LeadingTrivia, TokenKind},
        observation::token_kind,
        stops::Stops,
        yumark::FenceBoundary,
    },
};

#[allow(clippy::too_many_arguments)]
pub(super) fn type_forall_normalized(
    mut i: SyntaxIn,
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
    ambient: AmbientClaimContext<'_>,
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
        ambient,
    );
    i.state.finish_node();
    exit
}

/// Error covers a mandatory slot until an actual first binder opens the
/// distinct colon slot. Extending an existing binder list does not reset it.
#[derive(Clone, Copy)]
enum ForallHeadPhase {
    First,
    RecoveredFirst,
    Binders,
    RecoveredColon,
}

impl ForallHeadPhase {
    fn is_first(self) -> bool {
        matches!(self, Self::First | Self::RecoveredFirst)
    }

    fn recovered(self) -> bool {
        matches!(self, Self::RecoveredFirst | Self::RecoveredColon)
    }

    fn after_error(self) -> Self {
        if self.is_first() {
            Self::RecoveredFirst
        } else {
            Self::RecoveredColon
        }
    }

    fn after_binder(self) -> Self {
        if self.is_first() { Self::Binders } else { self }
    }
}

/// A recovery-local decision, returned together with exactly one owned Item.
#[derive(Clone, Copy, Eq, PartialEq)]
enum ForallRetry {
    Boundary,
    Binder,
    Colon,
    Body,
}

#[allow(clippy::too_many_arguments)]
fn type_forall_head_normalized(
    mut i: SyntaxIn,
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
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let (mut item, next_origin, next_line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
        ambient,
    );
    item_origin = next_origin;
    line_entry = next_line_entry;
    let mut phase = ForallHeadPhase::First;
    let mut target = forall_retry(
        &item,
        true,
        phase.is_first(),
        baseline,
        outer_separators,
        caller_stops,
        outer_boundary,
        None,
    );
    loop {
        match target {
            Some(ForallRetry::Boundary) => {
                if !phase.recovered() {
                    emit_forall_missing(&mut i, phase.is_first(), &item, item_origin);
                }
                return complete(handoff(item), line_entry);
            }
            Some(ForallRetry::Colon) => {
                item.emit_all_remaining_leading(&mut *i.state);
                if phase.is_first() && !phase.recovered() {
                    emit_forall_missing(&mut i, true, &item, item_origin);
                }
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
                    ambient,
                );
            }
            Some(ForallRetry::Body) => {
                item.emit_all_remaining_leading(&mut *i.state);
                if !phase.recovered() {
                    emit_forall_missing(&mut i, false, &item, item_origin);
                }
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
                    ambient,
                );
            }
            Some(ForallRetry::Binder) => {
                type_forall_binder(i.rb(), item, item_origin);
                phase = phase.after_binder();
            }
            None if !phase.is_first() && is_type_separator(&item) => {
                emit_forall_separator_binder(i.rb(), item, item_origin);
            }
            None => {
                if phase.is_first() {
                    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
                }
                let retry;
                (item, item_origin, line_entry, retry) = retry_forall_normalized(
                    i.rb(),
                    item,
                    true,
                    phase.is_first(),
                    baseline,
                    outer_separators,
                    caller_stops,
                    outer_boundary,
                    pipe_lexical,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                );
                if phase.is_first() {
                    i.state.finish_node();
                }
                phase = phase.after_error();
                // In particular, a nested caller colon must remain Boundary
                // after the local matching stack has been discarded.
                target = Some(retry);
                continue;
            }
        }
        (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        );
        target = forall_retry(
            &item,
            true,
            phase.is_first(),
            baseline,
            outer_separators,
            caller_stops,
            outer_boundary,
            None,
        );
    }
}

fn forall_retry(
    item: &Item,
    accepts_colon: bool,
    first_head_slot: bool,
    baseline: usize,
    outer_separators: bool,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    local_close: Option<TokenKind>,
) -> Option<ForallRetry> {
    if item.payload_view().is_boundary() || item.payload_view().is_eof() {
        return Some(ForallRetry::Boundary);
    }
    let kind = token_kind(item);
    let matching_nested_close = local_close.is_some() && kind == local_close;
    if !type_chain_trivia(item.leading_view(), baseline) && !matching_nested_close {
        return Some(ForallRetry::Boundary);
    }
    let local_colon = accepts_colon
        && local_close.is_none()
        && matches!(
            kind,
            Some(TokenKind::Colon | TokenKind::PolymorphicVariantColon)
        );
    if ((!local_colon
        && (is_type_caller_boundary(item, caller_stops)
            || is_type_outer_boundary(item, outer_boundary)))
        || (outer_separators && is_type_separator(item)))
        || (matches!(
            kind,
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        ) && !matching_nested_close)
    {
        return Some(ForallRetry::Boundary);
    }
    if local_close.is_some() {
        return None;
    }
    if local_colon {
        return Some(ForallRetry::Colon);
    }
    if is_forall_binder(item) {
        return Some(ForallRetry::Binder);
    }
    if !first_head_slot && is_type_nud(item) {
        return Some(ForallRetry::Body);
    }
    None
}

#[allow(clippy::too_many_arguments)]
fn retry_forall_normalized(
    i: SyntaxIn,
    mut item: Item,
    accepts_colon: bool,
    first_head_slot: bool,
    baseline: usize,
    outer_separators: bool,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> (Item, usize, LineEntry, ForallRetry) {
    item.emit_all_remaining_leading(&mut *i.state);
    emit_recovery_error_run(i, |run| {
        let mut closes = Vec::new();
        loop {
            match token_kind(&item) {
                Some(TokenKind::LParen) => closes.push(TokenKind::RParen),
                Some(TokenKind::LBracket) => closes.push(TokenKind::RBracket),
                Some(TokenKind::LBrace) => closes.push(TokenKind::RBrace),
                Some(close) if Some(&close) == closes.last() => {
                    closes.pop();
                }
                _ => {}
            }
            run.emit_item_as(item, item_origin);
            (item, item_origin, line_entry) =
                type_nud_item_with_pipe_lexical_normalized_in_error_run(
                    run,
                    item_origin,
                    line_entry,
                    fence,
                    pipe_lexical,
                    ambient,
                );
            if let Some(target) = forall_retry(
                &item,
                accepts_colon,
                first_head_slot,
                baseline,
                outer_separators,
                caller_stops,
                outer_boundary,
                closes.last().copied(),
            ) {
                return (item, item_origin, line_entry, target);
            }
        }
    })
}

fn emit_forall_separator_binder(mut i: SyntaxIn, mut separator: Item, item_origin: usize) {
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    separator.emit_all_remaining_leading(&mut *i.state);
    emit_recovery_error_item(i.rb(), separator, item_origin);
    i.state.finish_node();
}

fn type_forall_binder(mut i: SyntaxIn, mut binder: Item, item_origin: usize) {
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    if binder.leading_view().is_grammar_empty() {
        emit_forall_missing(&mut i, false, &binder, item_origin);
    }
    binder.emit_all_remaining_leading(&mut *i.state);
    emit_token_item(&mut i, binder);
    i.state.finish_node();
}

#[allow(clippy::too_many_arguments)]
fn type_forall_body_normalized(
    mut i: SyntaxIn,
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
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    emit_token_item(&mut i, colon);
    let (mut body, mut item_origin, mut line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
        ambient,
    );
    let target = forall_retry(
        &body,
        false,
        false,
        baseline,
        outer_separators,
        caller_stops,
        TypeOuterBoundary::NONE,
        None,
    );
    if target == Some(ForallRetry::Boundary) {
        emit_forall_missing(&mut i, false, &body, item_origin);
        return complete(handoff(body), line_entry);
    }
    if target.is_none() {
        let retry;
        (body, item_origin, line_entry, retry) = retry_forall_normalized(
            i.rb(),
            body,
            false,
            false,
            baseline,
            outer_separators,
            caller_stops,
            TypeOuterBoundary::NONE,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        if retry == ForallRetry::Boundary {
            return complete(handoff(body), line_entry);
        }
        debug_assert!(retry == ForallRetry::Body);
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
        ambient,
    )
}

fn emit_forall_missing(i: &mut SyntaxIn, opens_binder: bool, item: &Item, item_origin: usize) {
    if opens_binder {
        i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    }
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(item_origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at);
    if opens_binder {
        i.state.finish_node();
    }
}
