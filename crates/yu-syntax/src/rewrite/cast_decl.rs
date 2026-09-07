//! Private isolated direct standalone `cast` declaration construction.

use super::ambient_claim::{AmbientClaimContext, AmbientClaimView};
use crate::session::{CastRole, DeclarationRole, GrammarRole};
use crate::{scan::operator::OperatorSite, syntax_kind::SyntaxKind};
use reborrow_generic::Reborrow as _;

use super::{
    LexIn, RewriteIn, Stops,
    current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
    driver::{
        Either, MlMode, NormalizedExit, advanced_origin, complete, expr_from_nud_normalized,
        expression_item, handoff, implicit_delimited_newline, is_active_stop, is_line_stop,
        is_nud_item, is_separator, suffix_marker, token_kind,
    },
    emit::{emit_missing, emit_token_item},
    if_expr::active_statement_companion,
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{
        introduced_body_indentation_normalized, scan_identifier, scan_pattern_nud_payload,
        scan_statement_payload, scan_type_nud_payload, source_identifier,
    },
    operator::{TriviaObservation, active_stop_item, observe_fenced_trivia},
    pattern::{
        PATTERN_STOP_COLON, PATTERN_STOP_EQUALS, PatternCallerCloses, PatternCompletion,
        PatternMandatorySlotPolicy, is_pattern_nud,
        required_pattern_from_entry_item_with_policy_normalized,
    },
    statement::{StatementLineHandoff, indented_statement_block_normalized},
    type_expr::{
        TypeOuterBoundary, is_type_nud,
        required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient,
    },
    yumark::FenceBoundary,
};

#[derive(Clone, Copy)]
enum CastVocabulary {
    RawIdentifier,
    Pattern,
    Type,
    Statement,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CastTransition {
    LocalClose,
    Target,
    Form,
    OuterBoundary,
    Other,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn cast_declaration_witness(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<NormalizedExit> {
    if !cast_source_selected_normalized(i.rb(), baseline, item_origin, line_entry, fence) {
        return None;
    }
    let (intro, item_origin, line_entry) = cast_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        CastVocabulary::RawIdentifier,
    );
    cast_declaration_selected_normalized(i.rb(), &intro, baseline, item_origin, fence).then(|| {
        cast_declaration_normalized(
            i,
            intro,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            Some(AmbientClaimView::root_statement(baseline)).into(),
        )
    })
}

fn cast_source_selected_normalized(
    i: RewriteIn,
    baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            let source = lex.remainder();
            let TriviaObservation::Visible(observed) =
                observe_fenced_trivia(source, item_origin, line_entry, fence)
            else {
                return Some(false);
            };
            if observed
                .indentation
                .is_some_and(|indentation| indentation <= baseline)
            {
                return Some(false);
            }
            let Some((word, suffix)) = source_identifier(observed.source) else {
                return Some(false);
            };
            if word == "cast" {
                return Some(true);
            }
            if !matches!(word, "my" | "our" | "pub") {
                return Some(false);
            }
            let leading_len = source.len() - observed.source.len();
            Some(prefixed_cast_candidate_normalized(
                suffix,
                item_origin + leading_len + word.len(),
                fence,
                baseline,
            ))
        },
        |selected| selected,
    )
    .unwrap_or(false)
}

pub(super) fn cast_declaration_selected_normalized(
    i: RewriteIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item_word(item) == Some("cast") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    observes(i, |source| {
        prefixed_cast_candidate_normalized(source, item_origin, fence, baseline)
    })
}

fn prefixed_cast_candidate_normalized(
    source: &str,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
) -> bool {
    let TriviaObservation::Visible(observed) =
        observe_fenced_trivia(source, item_origin, LineEntry::InLine, fence)
    else {
        return false;
    };
    observed.present
        && observed
            .indentation
            .is_none_or(|indentation| indentation > baseline)
        && source_identifier(observed.source).is_some_and(|(word, _)| word == "cast")
}

#[allow(clippy::too_many_arguments)]
pub(super) fn cast_declaration_normalized(
    mut i: RewriteIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::CastDeclaration.into());
    if item_word(&intro) == Some("cast") {
        emit_item_as(&mut i, intro, SyntaxKind::CastKw);
    } else {
        emit_visibility(&mut i, intro);
        let (mut keyword, next_origin, next_entry) = cast_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            CastVocabulary::RawIdentifier,
        );
        item_origin = next_origin;
        line_entry = next_entry;
        debug_assert!(cast_gap_allowed(&keyword, baseline));
        debug_assert_eq!(item_word(&keyword), Some("cast"));
        keyword.emit_all_remaining_leading(&mut *i.state);
        emit_item_as(&mut i, keyword, SyntaxKind::CastKw);
    }

    let (item, item_origin, line_entry) = cast_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        CastVocabulary::Pattern,
    );
    let exit = cast_pattern_introducer_normalized(
        i.rb(),
        item,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn cast_pattern_introducer_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if is_form_starter(&item) && cast_gap_allowed(&item, baseline) {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        return cast_form_normalized(
            i,
            item,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    if cast_token_kind(&item) == Some(TokenKind::Colon) && cast_gap_allowed(&item, baseline) {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        return cast_target_introducer_normalized(
            i,
            item,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    if cast_token_kind(&item) == Some(TokenKind::RParen) {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    if slot_outer_boundary(i.rb(), &item, baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if cast_token_kind(&item) == Some(TokenKind::LParen) {
        i.state.start_node(SyntaxKind::CastPattern.into());
        emit_token_item(&mut i, item);
        let (item, item_origin, line_entry) = cast_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            CastVocabulary::Pattern,
        );
        return cast_pattern_value_normalized(
            i,
            item,
            true,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    if is_pattern_nud(&item, 0) {
        i.state.start_node(SyntaxKind::CastPattern.into());
        emit_missing(&mut i, LeadingTrivia::default());
        return cast_pattern_value_normalized(
            i,
            item,
            false,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = cast_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            CastVocabulary::Pattern,
        );
        if cast_token_kind(&item) == Some(TokenKind::Colon) && cast_gap_allowed(&item, baseline) {
            i.state.finish_node();
            return cast_target_introducer_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
        if is_form_starter(&item) && cast_gap_allowed(&item, baseline) {
            i.state.finish_node();
            return cast_form_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
        if slot_outer_boundary(i.rb(), &item, baseline, stops)
            || cast_token_kind(&item) == Some(TokenKind::RParen)
        {
            if cast_error_owns_eof_leading(&item) {
                item.emit_eof_leading(&mut *i.state);
            }
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if cast_token_kind(&item) == Some(TokenKind::LParen) || is_pattern_nud(&item, 0) {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            i.state.start_node(SyntaxKind::CastPattern.into());
            let has_local_close = cast_token_kind(&item) == Some(TokenKind::LParen);
            if has_local_close {
                emit_token_item(&mut i, item);
                (item, item_origin, line_entry) = cast_item_normalized(
                    i.rb(),
                    item_origin,
                    line_entry,
                    fence,
                    baseline,
                    stops,
                    CastVocabulary::Pattern,
                );
            } else {
                emit_missing(&mut i, LeadingTrivia::default());
            }
            return cast_pattern_value_normalized(
                i,
                item,
                has_local_close,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_pattern_value_normalized(
    mut i: RewriteIn,
    mut item: Item,
    has_local_close: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if slot_outer_boundary(i.rb(), &item, baseline, stops)
        && !(has_local_close && cast_token_kind(&item) == Some(TokenKind::RParen))
    {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    let child_entry = suffix_marker(i.rb());
    let policy = PatternMandatorySlotPolicy {
        fresh_primary_recovery_stops: PATTERN_STOP_COLON | PATTERN_STOP_EQUALS,
        recovered_primary_tail_stops: PATTERN_STOP_COLON,
    };
    let (exit, completion) = required_pattern_from_entry_item_with_policy_normalized(
        i.rb(),
        item,
        baseline,
        0,
        line_handoff,
        policy,
        cast_pattern_caller_closes(stops),
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    item_origin = advanced_origin(item_origin, child_entry, i.rb());
    let (item, line_entry) = successor_item(exit);
    if completion == PatternCompletion::Incomplete {
        return cast_after_incomplete_pattern_normalized(
            i,
            item,
            has_local_close,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    cast_pattern_close_normalized(
        i,
        item,
        has_local_close,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn cast_after_incomplete_pattern_normalized(
    mut i: RewriteIn,
    mut item: Item,
    has_local_close: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    match cast_transition(i.rb(), &item, baseline, stops, has_local_close) {
        CastTransition::LocalClose => {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_token_item(&mut i, item);
            i.state.finish_node();
            target_after_local_close_normalized(
                i,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
        CastTransition::Target => {
            i.state.finish_node();
            cast_target_introducer_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
        CastTransition::Form => {
            i.state.finish_node();
            cast_form_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
        CastTransition::OuterBoundary | CastTransition::Other => {
            i.state.finish_node();
            complete(handoff(item), line_entry)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_pattern_close_normalized(
    mut i: RewriteIn,
    mut item: Item,
    has_local_close: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let transition = cast_transition(i.rb(), &item, baseline, stops, has_local_close);
    if !has_local_close {
        i.state.finish_node();
        return match transition {
            CastTransition::Target => cast_target_introducer_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            ),
            CastTransition::Form => cast_form_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            ),
            CastTransition::OuterBoundary | CastTransition::LocalClose => {
                complete(handoff(item), line_entry)
            }
            CastTransition::Other => cast_target_introducer_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            ),
        };
    }
    if transition == CastTransition::LocalClose {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_token_item(&mut i, item);
        i.state.finish_node();
        return target_after_local_close_normalized(
            i,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    if matches!(transition, CastTransition::Target | CastTransition::Form) {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return if transition == CastTransition::Target {
            cast_target_introducer_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        } else {
            cast_form_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        };
    }
    if transition == CastTransition::OuterBoundary {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }

    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = cast_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            CastVocabulary::Statement,
        );
        let transition = cast_transition(i.rb(), &item, baseline, stops, true);
        if transition == CastTransition::LocalClose {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            emit_token_item(&mut i, item);
            i.state.finish_node();
            return target_after_local_close_normalized(
                i,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
        if matches!(transition, CastTransition::Target | CastTransition::Form) {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            i.state.finish_node();
            return if transition == CastTransition::Target {
                cast_target_introducer_normalized(
                    i,
                    item,
                    baseline,
                    stops,
                    line_handoff,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                )
            } else {
                cast_form_normalized(
                    i,
                    item,
                    baseline,
                    stops,
                    line_handoff,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                )
            };
        }
        if transition == CastTransition::OuterBoundary {
            if item.payload_view().is_eof() && cast_gap_allowed(&item, baseline) {
                item.emit_eof_leading(&mut *i.state);
            }
            i.state.finish_node();
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        item.emit_all_remaining_leading(&mut *i.state);
    }
}

#[allow(clippy::too_many_arguments)]
fn target_after_local_close_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let (item, item_origin, line_entry) = cast_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        CastVocabulary::Type,
    );
    cast_target_introducer_normalized(
        i,
        item,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn cast_target_introducer_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let transition = cast_transition(i.rb(), &item, baseline, stops, false);
    if transition == CastTransition::Form {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        return cast_form_normalized(
            i,
            item,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    if transition == CastTransition::OuterBoundary {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if transition == CastTransition::Target {
        i.state.start_node(SyntaxKind::CastTarget.into());
        emit_token_item(&mut i, item);
        let (item, item_origin, line_entry) = cast_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            CastVocabulary::Type,
        );
        return cast_target_type_normalized(
            i,
            item,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    if is_type_nud(&item) {
        i.state.start_node(SyntaxKind::CastTarget.into());
        emit_missing(&mut i, LeadingTrivia::default());
        return cast_target_type_normalized(
            i,
            item,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = cast_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            CastVocabulary::Type,
        );
        let transition = cast_transition(i.rb(), &item, baseline, stops, false);
        if transition == CastTransition::Form {
            i.state.finish_node();
            return cast_form_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
        if transition == CastTransition::OuterBoundary {
            if item.payload_view().is_eof() && cast_gap_allowed(&item, baseline) {
                item.emit_eof_leading(&mut *i.state);
            }
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if transition == CastTransition::Target || is_type_nud(&item) {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            i.state.start_node(SyntaxKind::CastTarget.into());
            let has_colon = transition == CastTransition::Target;
            if has_colon {
                emit_token_item(&mut i, item);
                (item, item_origin, line_entry) = cast_item_normalized(
                    i.rb(),
                    item_origin,
                    line_entry,
                    fence,
                    baseline,
                    stops,
                    CastVocabulary::Type,
                );
            } else {
                emit_missing(&mut i, LeadingTrivia::default());
            }
            return cast_target_type_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_target_type_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let transition = cast_transition(i.rb(), &item, baseline, stops, false);
    if transition != CastTransition::OuterBoundary {
        if item.payload_view().is_eof() {
            item.emit_eof_leading(&mut *i.state);
        } else {
            item.emit_all_remaining_leading(&mut *i.state);
        }
    }
    let child_entry = suffix_marker(i.rb());
    let (exit, type_complete) =
        required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient(
            i.rb(),
            item,
            GrammarRole::Declaration(DeclarationRole::Cast(CastRole::TargetType)),
            baseline,
            stops,
            TypeOuterBoundary::EQUALS,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    item_origin = advanced_origin(item_origin, child_entry, i.rb());
    let (item, line_entry) = successor_item(exit);
    i.state.finish_node();
    let transition = cast_transition(i.rb(), &item, baseline, stops, false);
    if type_complete || transition == CastTransition::Form {
        cast_form_normalized(
            i,
            item,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        )
    } else {
        complete(handoff(item), line_entry)
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_form_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if is_form_starter(&item) && cast_gap_allowed(&item, baseline) {
        item.emit_all_remaining_leading(&mut *i.state);
        match token_kind(&item) {
            Some(TokenKind::Semicolon) => {
                emit_token_item(&mut i, item);
                return after_bodyless_normalized(
                    i,
                    baseline,
                    stops,
                    item_origin,
                    line_entry,
                    fence,
                );
            }
            Some(TokenKind::Equals) => {
                emit_token_item(&mut i, item);
                i.state.start_node(SyntaxKind::CastBody.into());
                let exit = cast_definition_body_normalized(
                    i.rb(),
                    baseline,
                    stops,
                    line_handoff,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                );
                i.state.finish_node();
                return exit;
            }
            _ => unreachable!("a Cast form starter is semicolon or exact equals"),
        }
    }
    if slot_outer_boundary(i.rb(), &item, baseline, stops)
        || cast_token_kind(&item) == Some(TokenKind::RParen)
    {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }

    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = cast_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            CastVocabulary::Statement,
        );
        if is_form_starter(&item) && cast_gap_allowed(&item, baseline) {
            i.state.finish_node();
            return cast_form_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
        if slot_outer_boundary(i.rb(), &item, baseline, stops)
            || cast_token_kind(&item) == Some(TokenKind::RParen)
        {
            if item.payload_view().is_eof() && cast_gap_allowed(&item, baseline) {
                item.emit_eof_leading(&mut *i.state);
            }
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        item.emit_all_remaining_leading(&mut *i.state);
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_definition_body_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    match introduced_body_indentation_normalized(i.rb(), item_origin, fence) {
        Some(indentation) if indentation > baseline => indented_statement_block_normalized(
            i,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(_) => {
            emit_missing(&mut i, LeadingTrivia::default());
            let (item, _, line_entry) = cast_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                CastVocabulary::Statement,
            );
            complete(handoff(item), line_entry)
        }
        None => cast_inline_body_normalized(
            i,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_inline_body_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let (mut item, mut item_origin, mut line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    if cast_inline_body_boundary(i.rb(), &item, baseline, stops) {
        if !item.payload_view().is_boundary()
            && !implicit_delimited_newline(baseline, item.leading_view())
        {
            if item.payload_view().is_eof() {
                item.emit_eof_leading(&mut *i.state);
            } else {
                item.emit_all_remaining_leading(&mut *i.state);
            }
        }
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if is_nud_item(&item) {
        return expr_from_nud_normalized(
            i,
            item,
            None,
            baseline,
            stops,
            MlMode::All,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let (next, next_origin, next_line_entry) = expression_item(
            i.rb(),
            OperatorSite::Nud,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
        );
        item = next;
        if cast_inline_body_boundary(i.rb(), &item, baseline, stops) {
            if item.payload_view().is_eof()
                && !implicit_delimited_newline(baseline, item.leading_view())
            {
                item.emit_eof_leading(&mut *i.state);
            }
            i.state.finish_node();
            return complete(handoff(item), next_line_entry);
        }
        if is_nud_item(&item) {
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            return expr_from_nud_normalized(
                i,
                item,
                None,
                baseline,
                stops,
                MlMode::All,
                line_handoff,
                next_origin,
                next_line_entry,
                fence,
                ambient,
            );
        }
        item_origin = next_origin;
        line_entry = next_line_entry;
        item.emit_all_remaining_leading(&mut *i.state);
    }
}

fn cast_inline_body_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || is_line_stop(item, stops)
        || implicit_delimited_newline(baseline, item.leading_view())
        || matches!(
            cast_token_kind(item),
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
}

fn after_bodyless_normalized(
    i: RewriteIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, _, line_entry) = cast_item_normalized(
        i,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        CastVocabulary::Statement,
    );
    complete(handoff(item), line_entry)
}

fn successor_item(exit: NormalizedExit) -> (Item, LineEntry) {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => {
            unreachable!("a mandatory direct child returns one successor Item: {line_entry:?}")
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => (item, line_entry),
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => (end.item, line_entry),
        NormalizedExit::Deferred(_, _) => {
            unreachable!("a normalized Cast child does not defer")
        }
    }
}

fn slot_outer_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || !cast_gap_allowed(item, baseline)
        || is_active_stop(i.rb(), item, stops)
        || is_line_stop(item, stops)
        || is_separator(item)
        || matches!(
            cast_token_kind(item),
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
        || active_statement_companion(i.rb(), item, baseline, stops).is_some()
}

fn cast_transition(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    owns_local_close: bool,
) -> CastTransition {
    if owns_local_close && cast_token_kind(item) == Some(TokenKind::RParen) {
        return CastTransition::LocalClose;
    }
    if !cast_gap_allowed(item, baseline) {
        return CastTransition::OuterBoundary;
    }
    if cast_token_kind(item) == Some(TokenKind::Colon) {
        return CastTransition::Target;
    }
    if is_form_starter(item) {
        return CastTransition::Form;
    }
    if slot_outer_boundary(i.rb(), item, baseline, stops)
        || cast_token_kind(item) == Some(TokenKind::RParen)
    {
        return CastTransition::OuterBoundary;
    }
    CastTransition::Other
}

fn cast_error_owns_eof_leading(item: &Item) -> bool {
    item.payload_view().is_eof() && !item.leading_view().contains_line_break()
}

fn cast_gap_allowed(item: &Item, baseline: usize) -> bool {
    super::driver::indentation_after_newline(item.leading_view())
        .is_none_or(|indentation| indentation > baseline)
}

fn is_form_starter(item: &Item) -> bool {
    !item.payload_view().is_boundary()
        && matches!(
            cast_token_kind(item),
            Some(TokenKind::Semicolon | TokenKind::Equals)
        )
}

fn cast_token_kind(item: &Item) -> Option<TokenKind> {
    (!item.payload_view().is_boundary())
        .then(|| token_kind(item))
        .flatten()
}

fn cast_pattern_caller_closes(stops: Stops) -> PatternCallerCloses {
    let mut closes = PatternCallerCloses::RPAREN;
    if active_stop_item(TokenKind::RBracket, stops) {
        closes = closes.union(PatternCallerCloses::RBRACKET);
    }
    if active_stop_item(TokenKind::RBrace, stops) {
        closes = closes.union(PatternCallerCloses::RBRACE);
    }
    closes
}

#[allow(clippy::too_many_arguments)]
fn cast_item_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    vocabulary: CastVocabulary,
) -> (Item, usize, LineEntry) {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(
                lex,
                item_origin,
                line_entry,
                fence,
                |lex, leading, origin, fence, _| match vocabulary {
                    CastVocabulary::RawIdentifier => {
                        scan_identifier(lex).map(|identifier| AcceptedPayload {
                            payload: CurrentPayload::Token(identifier),
                            next_line_entry: LineEntry::InLine,
                        })
                    }
                    CastVocabulary::Pattern => {
                        scan_pattern_nud_payload(lex, leading, origin, fence, 0)
                    }
                    CastVocabulary::Type => scan_type_nud_payload(lex, leading, origin, fence),
                    CastVocabulary::Statement => {
                        scan_statement_payload(lex, leading, origin, fence, baseline, stops)
                    }
                },
            )
        })
        .expect("Cast declaration payload scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

fn item_word(item: &Item) -> Option<&str> {
    (item.payload_view().token_kind() == Some(TokenKind::Identifier))
        .then(|| item.payload_view().spelling())
        .flatten()
}

fn emit_item_as(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_visibility(i: &mut RewriteIn, item: Item) {
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("Cast visibility uses exact declaration words"),
    };
    emit_item_as(i, item, kind);
}

fn observes<F>(i: RewriteIn, predicate: F) -> bool
where
    F: FnOnce(&str) -> bool,
{
    i.map(
        |lex: LexIn| Some(predicate(lex.remainder())),
        |observed| observed,
    )
    .expect("source observation is total")
}
