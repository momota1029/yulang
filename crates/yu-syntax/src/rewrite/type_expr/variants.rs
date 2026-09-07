//! Effect-row and polymorphic-variant type primaries.

use super::super::ambient_claim::AmbientClaimContext;
use std::sync::Arc;

use reborrow_generic::Reborrow as _;

use crate::{
    session::{
        ExpectationSources, ExpectedSyntax, GrammarRole, RecoveryKind, RecoverySiteKey,
        SyntaxExpectation, TypeRole, UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use super::super::{
    RewriteIn, Stops,
    current_item::LineEntry,
    driver::{
        Either, NormalizedExit, advanced_origin, complete, handoff, suffix_marker, token_kind,
    },
    emit::{emit_error_item, emit_missing, emit_recovery_error_run, emit_token_item},
    item::{Item, LeadingTrivia, TokenKind},
    output::{RecoveryDraft, StructuredRecoverySpec, emit_structured_recovery_error_from_item},
    yumark::FenceBoundary,
};
use super::{
    TypeApplyBoundary, TypeDelimitedOwner, TypeMlContext, TypeOuterBoundary,
    continue_type_tail_normalized, indentation_after_newline, is_type_caller_boundary,
    is_type_mismatched_close, is_type_nud, is_type_outer_close, is_type_payload_boundary,
    is_type_polymorphic_variant_tag_name, type_delimited_baseline, type_delimited_normalized,
    type_expr_from_nud_normalized, type_nud_item_with_pipe_lexical_normalized,
    type_nud_item_with_pipe_lexical_normalized_in_error_run, with_type_outer_close,
};

#[allow(clippy::too_many_arguments)]
pub(super) fn type_effect_row_normalized(
    mut i: RewriteIn,
    apostrophe: Item,
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
    i.state.start_node(SyntaxKind::EffectRowType.into());
    emit_token_item(&mut i, apostrophe);
    let (open, next_origin, next_line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
        ambient,
    );
    item_origin = next_origin;
    debug_assert_eq!(token_kind(&open), Some(TokenKind::LBracket));
    debug_assert!(open.leading_view().is_grammar_empty());
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = type_delimited_normalized(
        i.rb(),
        TokenKind::RBracket,
        baseline,
        TypeDelimitedOwner::EffectRow,
        type_ml,
        TypeOuterBoundary::NONE,
        outer_closes,
        caller_stops,
        pipe_lexical,
        item_origin,
        next_line_entry,
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
pub(super) fn type_polymorphic_variant_normalized(
    mut i: RewriteIn,
    colon: Item,
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
    #[cfg(test)]
    ambient.observe(super::super::ambient_claim::ProofSite::PolymorphicVariant);
    i.state
        .start_node(SyntaxKind::PolymorphicVariantType.into());
    emit_token_item(&mut i, colon);

    let (open, next_origin, next_line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
        ambient,
    );
    item_origin = next_origin;
    debug_assert_eq!(token_kind(&open), Some(TokenKind::LBrace));
    debug_assert!(open.leading_view().is_grammar_empty());
    emit_token_item(&mut i, open);

    let entry = suffix_marker(i.rb());
    let exit = type_polymorphic_variant_tags_normalized(
        i.rb(),
        baseline,
        type_ml.dormant(),
        outer_separators,
        with_type_outer_close(outer_closes, TokenKind::RBrace),
        caller_stops,
        pipe_lexical,
        item_origin,
        next_line_entry,
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

#[derive(Clone, Copy)]
enum TagPosition {
    Open,
    AfterTag,
    Unfilled,
    Filled,
}

#[allow(clippy::too_many_arguments)]
fn type_polymorphic_variant_tags_normalized(
    mut i: RewriteIn,
    incoming_baseline: usize,
    type_ml: TypeMlContext,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
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
    let baseline = type_delimited_baseline(incoming_baseline, item.leading_view());
    let mut position = TagPosition::Open;

    if item.payload_view().is_boundary() {
        return type_polymorphic_variant_boundary(i, item, position, line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);

    loop {
        if item.payload_view().is_boundary() {
            return type_polymorphic_variant_boundary(i, item, position, line_entry);
        }
        if let Some(indentation) = indentation_after_newline(item.leading_view()) {
            if indentation > baseline {
                return type_polymorphic_variant_boundary(i, item, position, line_entry);
            }
            item.emit_all_remaining_leading(&mut *i.state);
            if matches!(position, TagPosition::AfterTag) {
                position = TagPosition::Unfilled;
            }
            continue;
        }
        if token_kind(&item) == Some(TokenKind::RBrace) {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_token_item(&mut i, item);
            return complete(Ok(()), line_entry);
        }
        if is_type_caller_boundary(&item, caller_stops)
            && !is_type_polymorphic_variant_tag_name(&item)
        {
            return type_polymorphic_variant_boundary(i, item, position, line_entry);
        }
        if is_type_mismatched_close(&item, TokenKind::RBrace) {
            if is_type_outer_close(&item, outer_closes) {
                return type_polymorphic_variant_boundary(i, item, position, line_entry);
            }
            item.emit_all_remaining_leading(&mut *i.state);
            emit_error_item(&mut i, item);
            (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
                ambient,
            );
            continue;
        }
        if token_kind(&item) == Some(TokenKind::Comma) {
            item.emit_all_remaining_leading(&mut *i.state);
            if !matches!(position, TagPosition::AfterTag) {
                emit_missing(&mut i, LeadingTrivia::default());
                position = TagPosition::Filled;
            } else {
                position = TagPosition::Unfilled;
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
            continue;
        }
        if token_kind(&item) == Some(TokenKind::Semicolon) {
            if outer_separators {
                return type_polymorphic_variant_boundary(i, item, position, line_entry);
            }
            item.emit_all_remaining_leading(&mut *i.state);
            emit_error_item(&mut i, item);
            (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
                ambient,
            );
            continue;
        }
        if item.payload_view().is_eof() {
            return type_polymorphic_variant_boundary(i, item, position, line_entry);
        }

        item.emit_all_remaining_leading(&mut *i.state);
        let entry = suffix_marker(i.rb());
        let exit = if is_type_polymorphic_variant_tag_name(&item) {
            type_polymorphic_variant_tag_normalized(
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
        } else if is_type_nud(&item) {
            type_polymorphic_variant_wrong_kind_tag_normalized(
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
            type_polymorphic_variant_malformed_tag_normalized(
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
        };
        item_origin = advanced_origin(item_origin, entry, i.rb());
        position = TagPosition::AfterTag;
        let NormalizedExit::Complete(exit, next_line_entry) = exit else {
            unreachable!("normalized Type owners do not defer")
        };
        line_entry = next_line_entry;
        item = match exit {
            Ok(()) => {
                let (next, next_origin, next_line_entry) =
                    type_nud_item_with_pipe_lexical_normalized(
                        i.rb(),
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                        ambient,
                    );
                item_origin = next_origin;
                line_entry = next_line_entry;
                next
            }
            Err(Either::Left(next)) if next.payload_view().is_boundary() => {
                return type_polymorphic_variant_boundary(i, next, position, line_entry);
            }
            Err(Either::Left(next)) if is_type_caller_boundary(&next, caller_stops) => {
                return type_polymorphic_variant_boundary(i, next, position, line_entry);
            }
            Err(Either::Left(next)) => next,
            Err(Either::Right(end)) => end.item,
        };
    }
}

fn type_polymorphic_variant_boundary(
    mut i: RewriteIn,
    item: Item,
    position: TagPosition,
    line_entry: LineEntry,
) -> NormalizedExit {
    if matches!(position, TagPosition::Unfilled) {
        emit_missing(&mut i, LeadingTrivia::default());
    }
    emit_missing(&mut i, LeadingTrivia::default());
    complete(handoff(item), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn type_polymorphic_variant_tag_normalized(
    mut i: RewriteIn,
    name: Item,
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
    i.state.start_node(SyntaxKind::PolymorphicVariantTag.into());
    let exit = type_polymorphic_variant_tag_after_name_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        name,
        baseline,
        type_ml,
        outer_closes,
        caller_stops,
        pipe_lexical,
        ambient,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn type_polymorphic_variant_wrong_kind_tag_normalized(
    mut i: RewriteIn,
    primary: Item,
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
    i.state.start_node(SyntaxKind::PolymorphicVariantTag.into());
    let exit = type_polymorphic_variant_tag_after_wrong_kind_normalized(
        i.rb(),
        primary,
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
fn type_polymorphic_variant_tag_after_name_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    name: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    emit_token_item(&mut i, name);
    let (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
        ambient,
    );
    type_polymorphic_variant_tag_payloads_normalized(
        i,
        item,
        baseline,
        type_ml,
        outer_closes,
        caller_stops,
        pipe_lexical,
        false,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn type_polymorphic_variant_tag_after_wrong_kind_normalized(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let successor_origin = item_origin;
    let exit = emit_structured_recovery_error_from_item(
        i.rb(),
        primary,
        successor_origin,
        StructuredRecoverySpec::new(
            GrammarRole::Type(TypeRole::PolymorphicVariantTagName),
            UnexpectedCategory::OtherCharacter,
            ExpectedSyntax::Identifier,
            ExpectationSources::COMMITTED_RECOVERY_RULE,
            0,
        ),
        |mut nested, primary| {
            let entry = suffix_marker(nested.rb());
            let exit = type_expr_from_nud_normalized(
                nested.rb(),
                primary,
                baseline,
                type_ml.enter_non_type_apply(),
                None,
                true,
                outer_closes,
                caller_stops,
                TypeOuterBoundary::NONE,
                pipe_lexical,
                successor_origin,
                line_entry,
                fence,
                ambient,
            );
            let post_origin = advanced_origin(successor_origin, entry, nested.rb());
            let end = structured_tag_name_end(&exit, post_origin);
            ((exit, post_origin), end)
        },
    );
    let (exit, next_origin) = exit;
    item_origin = next_origin;
    type_polymorphic_variant_tag_payloads_after_head_normalized(
        i,
        exit,
        baseline,
        type_ml,
        outer_closes,
        caller_stops,
        pipe_lexical,
        item_origin,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn type_polymorphic_variant_malformed_tag_normalized(
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
    i.state.start_node(SyntaxKind::PolymorphicVariantTag.into());
    let (next, next_origin, next_line_entry) = emit_recovery_error_run(
        i.rb(),
        |run| {
            let mut run_start = None;
            loop {
                let kind = polymorphic_variant_malformed_item_syntax_kind(&item);
                let extent = run.emit_item_as(item, item_origin, kind);
                let range = extent.recovery_range();
                run_start.get_or_insert(range.start);
                let run_end = range.end;
                (item, item_origin, line_entry) =
                    type_nud_item_with_pipe_lexical_normalized_in_error_run(
                        run,
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                        ambient,
                    );
                if is_type_polymorphic_variant_tag_safe(&item) {
                    let range = run_start.expect("an NT-8 Error run is nonempty")..run_end;
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return (item, item_origin, line_entry);
                }
            }
        },
        |range, unexpected| polymorphic_variant_tag_error_draft(range, unexpected),
    );
    item = next;
    item_origin = next_origin;
    line_entry = next_line_entry;
    let exit =
        if item.payload_view().is_boundary() || is_type_polymorphic_variant_tag_boundary(&item) {
            complete(handoff(item), line_entry)
        } else {
            item.emit_all_remaining_leading(&mut *i.state);
            if is_type_polymorphic_variant_tag_name(&item) {
                type_polymorphic_variant_tag_after_name_normalized(
                    i.rb(),
                    item_origin,
                    line_entry,
                    fence,
                    item,
                    baseline,
                    type_ml,
                    outer_closes,
                    caller_stops,
                    pipe_lexical,
                    ambient,
                )
            } else {
                type_polymorphic_variant_tag_after_wrong_kind_normalized(
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
            }
        };
    i.state.finish_node();
    exit
}

fn structured_tag_name_end(exit: &NormalizedExit, post_origin: usize) -> usize {
    let NormalizedExit::Complete(exit, _) = exit else {
        unreachable!("normalized Type owners do not defer")
    };
    match exit {
        Ok(()) => post_origin,
        Err(Either::Left(item)) => pending_structured_end(item, post_origin),
        Err(Either::Right(end)) => pending_structured_end(&end.item, post_origin),
    }
}

fn pending_structured_end(item: &Item, post_origin: usize) -> usize {
    let pending = item.extent(post_origin).recovery_range();
    if pending.start < pending.end {
        pending.start
    } else {
        post_origin
    }
}

fn polymorphic_variant_tag_error_draft(
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let role = GrammarRole::Type(TypeRole::PolymorphicVariantTag);
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        RecoveryKind::Error,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Identifier,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

fn polymorphic_variant_malformed_item_syntax_kind(item: &Item) -> SyntaxKind {
    match token_kind(item).expect("an NT-8 Error run contains lexical Items") {
        TokenKind::Identifier => SyntaxKind::Identifier,
        TokenKind::SigilIdentifier => SyntaxKind::SigilIdentifier,
        TokenKind::Integer => SyntaxKind::Integer,
        TokenKind::Operator => SyntaxKind::Operator,
        TokenKind::LParen => SyntaxKind::LParen,
        TokenKind::RParen => SyntaxKind::RParen,
        TokenKind::LBracket => SyntaxKind::LBracket,
        TokenKind::RBracket => SyntaxKind::RBracket,
        TokenKind::LBrace => SyntaxKind::LBrace,
        TokenKind::RBrace => SyntaxKind::RBrace,
        TokenKind::Comma => SyntaxKind::Comma,
        TokenKind::Semicolon => SyntaxKind::Semicolon,
        TokenKind::Dot => SyntaxKind::Dot,
        TokenKind::DotDot => SyntaxKind::DotDot,
        TokenKind::Arrow => SyntaxKind::Arrow,
        TokenKind::Colon => SyntaxKind::Colon,
        TokenKind::Equals => SyntaxKind::Equals,
        TokenKind::Forall => SyntaxKind::ForKw,
        TokenKind::EffectRowApostrophe => SyntaxKind::Apostrophe,
        TokenKind::PolymorphicVariantColon | TokenKind::PatternSymbolColon => SyntaxKind::Colon,
        TokenKind::PathSeparator => SyntaxKind::ColonColon,
        TokenKind::Pipe => SyntaxKind::Pipe,
        TokenKind::Unknown => SyntaxKind::Unknown,
    }
}

#[allow(clippy::too_many_arguments)]
fn type_polymorphic_variant_tag_payloads_after_head_normalized(
    mut i: RewriteIn,
    exit: NormalizedExit,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let NormalizedExit::Complete(exit, line_entry) = exit else {
        unreachable!("normalized Type owners do not defer")
    };
    let (item, item_origin, line_entry) = match exit {
        Ok(()) => type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
            ambient,
        ),
        Err(Either::Left(item)) if item.payload_view().is_boundary() => {
            return complete(handoff(item), line_entry);
        }
        Err(Either::Left(item)) if is_type_caller_boundary(&item, caller_stops) => {
            return complete(handoff(item), line_entry);
        }
        Err(Either::Left(item)) => (item, item_origin, line_entry),
        Err(Either::Right(end)) => return complete(handoff(end.item), line_entry),
    };
    type_polymorphic_variant_tag_payloads_normalized(
        i,
        item,
        baseline,
        type_ml,
        outer_closes,
        caller_stops,
        pipe_lexical,
        true,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn type_polymorphic_variant_tag_payloads_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    type_ml: TypeMlContext,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut completed_payload: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    loop {
        if item.payload_view().is_boundary() {
            return complete(handoff(item), line_entry);
        }
        if completed_payload && is_type_caller_boundary(&item, caller_stops) {
            return complete(handoff(item), line_entry);
        }
        if is_type_polymorphic_variant_payload_boundary(&item) {
            return complete(handoff(item), line_entry);
        }
        if is_type_nud(&item) {
            let entry = suffix_marker(i.rb());
            let exit = type_polymorphic_variant_payload_normalized(
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
            );
            item_origin = advanced_origin(item_origin, entry, i.rb());
            let NormalizedExit::Complete(exit, next_line_entry) = exit else {
                unreachable!("normalized Type owners do not defer")
            };
            line_entry = next_line_entry;
            item = match exit {
                Ok(()) => {
                    let (next, next_origin, next_line_entry) =
                        type_nud_item_with_pipe_lexical_normalized(
                            i.rb(),
                            item_origin,
                            line_entry,
                            fence,
                            pipe_lexical,
                            ambient,
                        );
                    item_origin = next_origin;
                    line_entry = next_line_entry;
                    next
                }
                Err(Either::Left(next)) => next,
                Err(Either::Right(end)) => return complete(handoff(end.item), line_entry),
            };
            completed_payload = true;
            continue;
        }
        if !is_type_payload_boundary(item.leading_view()) {
            return complete(handoff(item), line_entry);
        }
        let entry = suffix_marker(i.rb());
        let exit = type_polymorphic_variant_malformed_payload_normalized(
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
        );
        item_origin = advanced_origin(item_origin, entry, i.rb());
        let NormalizedExit::Complete(exit, next_line_entry) = exit else {
            unreachable!("normalized Type owners do not defer")
        };
        line_entry = next_line_entry;
        item = match exit {
            Ok(()) => {
                let (next, next_origin, next_line_entry) =
                    type_nud_item_with_pipe_lexical_normalized(
                        i.rb(),
                        item_origin,
                        line_entry,
                        fence,
                        pipe_lexical,
                        ambient,
                    );
                item_origin = next_origin;
                line_entry = next_line_entry;
                next
            }
            Err(Either::Left(next)) if next.payload_view().is_boundary() => {
                return complete(handoff(next), line_entry);
            }
            Err(Either::Left(next)) if is_type_caller_boundary(&next, caller_stops) => {
                return complete(handoff(next), line_entry);
            }
            Err(Either::Left(next)) => next,
            Err(Either::Right(end)) => return complete(handoff(end.item), line_entry),
        };
    }
}

#[allow(clippy::too_many_arguments)]
fn type_polymorphic_variant_payload_normalized(
    mut i: RewriteIn,
    mut primary: Item,
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
    i.state
        .start_node(SyntaxKind::PolymorphicVariantPayload.into());
    if primary.leading_view().is_grammar_empty() {
        emit_missing(&mut i, LeadingTrivia::default());
    } else {
        primary.emit_all_remaining_leading(&mut *i.state);
    }
    let exit = type_expr_from_nud_normalized(
        i.rb(),
        primary,
        baseline,
        type_ml.enter_non_type_apply(),
        None,
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
    exit
}

#[allow(clippy::too_many_arguments)]
fn type_polymorphic_variant_malformed_payload_normalized(
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
    i.state
        .start_node(SyntaxKind::PolymorphicVariantPayload.into());
    if item.payload_view().is_boundary() {
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        item.emit_all_remaining_leading(&mut *i.state);
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
        if is_type_polymorphic_variant_payload_boundary(&item)
            || is_type_caller_boundary(&item, caller_stops)
        {
            i.state.finish_node();
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if !is_type_nud(&item) {
            continue;
        }
        i.state.finish_node();
        item.emit_all_remaining_leading(&mut *i.state);
        let exit = type_expr_from_nud_normalized(
            i.rb(),
            item,
            baseline,
            type_ml.enter_non_type_apply(),
            None,
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
}

fn is_type_polymorphic_variant_payload_boundary(item: &Item) -> bool {
    indentation_after_newline(item.leading_view()).is_some()
        || matches!(
            token_kind(item),
            Some(
                TokenKind::Comma
                    | TokenKind::Semicolon
                    | TokenKind::RParen
                    | TokenKind::RBracket
                    | TokenKind::RBrace
            )
        )
        || item.payload_view().is_eof()
}

fn is_type_polymorphic_variant_tag_safe(item: &Item) -> bool {
    item.payload_view().is_boundary()
        || is_type_polymorphic_variant_tag_boundary(item)
        || is_type_nud(item)
}

fn is_type_polymorphic_variant_tag_boundary(item: &Item) -> bool {
    indentation_after_newline(item.leading_view()).is_some()
        || matches!(
            token_kind(item),
            Some(
                TokenKind::Comma
                    | TokenKind::Semicolon
                    | TokenKind::RParen
                    | TokenKind::RBracket
                    | TokenKind::RBrace
            )
        )
        || item.payload_view().is_eof()
}
