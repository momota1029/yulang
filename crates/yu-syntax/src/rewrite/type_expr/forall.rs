//! Forall type owner and its phase-local, forward recovery.

use super::super::ambient_claim::AmbientClaimContext;
use reborrow_generic::Reborrow as _;
use std::sync::Arc;

use crate::{
    session::{
        ExpectationSources, ExpectedSyntax, GrammarRole, PunctuationEvidence, RecoveryKind,
        RecoverySiteKey, SyntaxExpectation, TypeRole, UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use super::super::{
    RewriteIn, Stops,
    current_item::LineEntry,
    driver::{NormalizedExit, complete, handoff, token_kind},
    emit::{
        emit_recovery_error_item, emit_recovery_error_run, emit_recovery_missing, emit_token_item,
    },
    item::{Item, LeadingTrivia, TokenKind},
    output::RecoveryDraft,
    yumark::FenceBoundary,
};
use super::{
    TypeApplyBoundary, TypeMlContext, TypeOuterBoundary, is_forall_binder, is_type_caller_boundary,
    is_type_nud, is_type_outer_boundary, is_type_separator, type_chain_trivia,
    type_expr_from_nud_normalized, type_nud_item_with_pipe_lexical_normalized,
    type_nud_item_with_pipe_lexical_normalized_in_error_run, type_recovery_error_syntax_kind,
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

    fn role(self) -> TypeRole {
        if self.is_first() {
            TypeRole::ForallBinder
        } else {
            TypeRole::ForallColon
        }
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
        phase.role(),
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
                    emit_forall_missing(&mut i, phase.role(), &item, item_origin);
                }
                return complete(handoff(item), line_entry);
            }
            Some(ForallRetry::Colon) => {
                item.emit_all_remaining_leading(&mut *i.state);
                if phase.is_first() && !phase.recovered() {
                    emit_forall_missing(&mut i, TypeRole::ForallBinder, &item, item_origin);
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
                    emit_forall_missing(&mut i, TypeRole::ForallColon, &item, item_origin);
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
                    phase.role(),
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
            phase.role(),
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
    role: TypeRole,
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
    let local_colon = role != TypeRole::ForallBody
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
    if role != TypeRole::ForallBody && is_forall_binder(item) {
        return Some(ForallRetry::Binder);
    }
    if role != TypeRole::ForallBinder && is_type_nud(item) {
        return Some(ForallRetry::Body);
    }
    None
}

#[allow(clippy::too_many_arguments)]
fn retry_forall_normalized(
    i: RewriteIn,
    mut item: Item,
    role: TypeRole,
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
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(item_origin).recovery_range().start;
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
                let kind = type_recovery_error_syntax_kind(&item);
                let end = run
                    .emit_item_as(item, item_origin, kind)
                    .recovery_range()
                    .end;
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
                    role,
                    baseline,
                    outer_separators,
                    caller_stops,
                    outer_boundary,
                    closes.last().copied(),
                ) {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return (item, item_origin, line_entry, target);
                }
            }
        },
        |range, unexpected| forall_recovery_draft(role, RecoveryKind::Error, range, unexpected),
    )
}

fn emit_forall_separator_binder(mut i: RewriteIn, mut separator: Item, item_origin: usize) {
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    separator.emit_all_remaining_leading(&mut *i.state);
    let range = separator.extent(item_origin).recovery_range();
    let kind = type_recovery_error_syntax_kind(&separator);
    emit_recovery_error_item(
        i.rb(),
        separator,
        item_origin,
        kind,
        UnexpectedSyntax::Token {
            range,
            category: UnexpectedCategory::OtherCharacter,
        },
        |range, unexpected| {
            forall_recovery_draft(
                TypeRole::ForallBinderBoundary,
                RecoveryKind::Error,
                range,
                unexpected,
            )
        },
    );
    i.state.finish_node();
}

fn type_forall_binder(mut i: RewriteIn, mut binder: Item, item_origin: usize) {
    i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    if binder.leading_view().is_grammar_empty() {
        emit_forall_missing(&mut i, TypeRole::ForallBinderBoundary, &binder, item_origin);
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
        TypeRole::ForallBody,
        baseline,
        outer_separators,
        caller_stops,
        TypeOuterBoundary::NONE,
        None,
    );
    if target == Some(ForallRetry::Boundary) {
        emit_forall_missing(&mut i, TypeRole::ForallBody, &body, item_origin);
        return complete(handoff(body), line_entry);
    }
    if target.is_none() {
        let retry;
        (body, item_origin, line_entry, retry) = retry_forall_normalized(
            i.rb(),
            body,
            TypeRole::ForallBody,
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

fn emit_forall_missing(i: &mut RewriteIn, role: TypeRole, item: &Item, item_origin: usize) {
    if role == TypeRole::ForallBinder {
        i.state.start_node(SyntaxKind::ForallTypeBinder.into());
    }
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(item_origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        forall_recovery_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
    if role == TypeRole::ForallBinder {
        i.state.finish_node();
    }
}

fn forall_recovery_draft(
    role: TypeRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected = match role {
        TypeRole::ForallBinder => ExpectedSyntax::ForallTypeBinder,
        TypeRole::ForallBinderBoundary => ExpectedSyntax::TypeBinderBoundary,
        TypeRole::ForallColon => ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        TypeRole::ForallBody => ExpectedSyntax::TypeExpression,
        _ => unreachable!("only forall recovery slots use this draft"),
    };
    let role = GrammarRole::Type(role);
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}
