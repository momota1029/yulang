//! Private isolated direct standalone `cast` declaration construction.

use crate::ambient_claim::AmbientClaimContext;
#[cfg(test)]
use crate::ambient_claim::AmbientClaimView;
use crate::recovery_record::{
    CastRole, DeclarationRole, Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole,
    PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
    UnexpectedSyntax,
};
use crate::{lexical::operator_scan::OperatorSite, syntax_kind::SyntaxKind};
use reborrow_generic::Reborrow as _;
use std::sync::Arc;

use crate::{
    cst_output::{
        RecoveryDraft,
        emit::{
            emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
        },
    },
    cursor::{LexIn, SyntaxIn},
    expression::{expr_from_nud_normalized, if_expr::active_statement_companion, is_nud_item},
    handoff::{Either, MlMode, NormalizedExit, complete, handoff},
    lexical::{
        current_item::{AcceptedPayload, CurrentPayload, LineEntry, current_item},
        expression_item::expression_item,
        item::{Item, LeadingTrivia, TokenKind},
        lexer::{
            introduced_body_indentation_normalized, scan_identifier, scan_pattern_nud_payload,
            scan_statement_payload, scan_type_nud_payload, source_identifier,
        },
        observation::{
            implicit_delimited_newline, is_active_stop, is_active_stop_lex, is_line_stop,
            is_separator, token_kind,
        },
        position::{advanced_origin, suffix_marker},
        stops::{Stops, active_stop_item},
        trivia::{TriviaObservation, observe_fenced_trivia},
        yumark::FenceBoundary,
    },
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
};

#[derive(Clone, Copy)]
enum CastVocabulary {
    RawIdentifier,
    Pattern,
    Type,
    Form,
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
#[cfg(test)]
pub(crate) fn cast_declaration_witness(
    mut i: SyntaxIn,
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
            Some(crate::sequence::SequenceOwner::RootStatement),
        )
    })
}

#[cfg(test)]
fn cast_source_selected_normalized(
    i: SyntaxIn,
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

#[cfg(test)]
pub(crate) fn cast_declaration_selected_normalized(
    i: SyntaxIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            Some(cast_declaration_selected_lexical(
                lex.remainder(),
                item,
                baseline,
                item_origin,
                fence,
            ))
        },
        |selected| selected,
    )
    .unwrap_or(false)
}

pub(crate) fn cast_declaration_selected_lexical(
    source: &str,
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
    prefixed_cast_candidate_normalized(source, item_origin, fence, baseline)
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
pub(crate) fn cast_declaration_normalized(
    mut i: SyntaxIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
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
        sequence,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn cast_pattern_introducer_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if is_form_starter(&item) && cast_gap_allowed(&item, baseline) {
        item.emit_all_remaining_leading(&mut *i.state);
        cast_pattern_introducer_missing(&mut i, &item, item_origin);
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
            sequence,
        );
    }
    if cast_token_kind(&item) == Some(TokenKind::Colon) && cast_gap_allowed(&item, baseline) {
        item.emit_all_remaining_leading(&mut *i.state);
        cast_pattern_introducer_missing(&mut i, &item, item_origin);
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
            sequence,
        );
    }
    if cast_token_kind(&item) == Some(TokenKind::RParen) {
        cast_pattern_introducer_missing(&mut i, &item, item_origin);
        return complete(handoff(item), line_entry);
    }
    if slot_outer_boundary(i.rb(), &item, baseline, stops) {
        cast_pattern_introducer_missing(&mut i, &item, item_origin);
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
            sequence,
        );
    }
    if is_pattern_nud(&item, 0) {
        i.state.start_node(SyntaxKind::CastPattern.into());
        cast_pattern_introducer_missing(&mut i, &item, item_origin);
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
            sequence,
        );
    }
    let (next, next_origin, next_line, exit) = cast_pattern_introducer_error_run(
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    item = next;
    item_origin = next_origin;
    line_entry = next_line;
    match exit {
        CastPatternIntroducerErrorExit::Target => cast_target_introducer_normalized(
            i,
            item,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        CastPatternIntroducerErrorExit::Form => cast_form_normalized(
            i,
            item,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        CastPatternIntroducerErrorExit::Boundary => complete(handoff(item), line_entry),
        CastPatternIntroducerErrorExit::Pattern => {
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
                sequence,
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_pattern_value_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    has_local_close: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let immediate_absence = has_local_close && cast_token_kind(&item) == Some(TokenKind::RParen)
        || (cast_token_kind(&item) == Some(TokenKind::Colon) && cast_gap_allowed(&item, baseline))
        || (is_form_starter(&item) && cast_gap_allowed(&item, baseline))
        || slot_outer_boundary(i.rb(), &item, baseline, stops);
    if immediate_absence {
        cast_pattern_missing(&mut i, &item, item_origin);
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
            sequence,
        );
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
            sequence,
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
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn cast_after_incomplete_pattern_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    has_local_close: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
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
                sequence,
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
                sequence,
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
                sequence,
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
    mut i: SyntaxIn,
    mut item: Item,
    has_local_close: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let mut transition = cast_transition(i.rb(), &item, baseline, stops, has_local_close);
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
                sequence,
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
                sequence,
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
                sequence,
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
            sequence,
        );
    }
    if matches!(transition, CastTransition::Target | CastTransition::Form) {
        item.emit_all_remaining_leading(&mut *i.state);
        cast_pattern_close_missing(&mut i, &item, item_origin);
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
                sequence,
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
                sequence,
            )
        };
    }
    if transition == CastTransition::OuterBoundary {
        cast_pattern_close_missing(&mut i, &item, item_origin);
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }

    item.emit_all_remaining_leading(&mut *i.state);
    (item, item_origin, line_entry, transition) = cast_pattern_close_error_run(
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    match transition {
        CastTransition::LocalClose => {
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
                sequence,
            );
        }
        CastTransition::Target | CastTransition::Form => {
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
                    sequence,
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
                    sequence,
                )
            };
        }
        CastTransition::OuterBoundary => {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        CastTransition::Other => unreachable!("close Error returns a transition"),
    }
}

#[allow(clippy::too_many_arguments)]
fn target_after_local_close_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
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
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn cast_target_introducer_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let transition = cast_transition(i.rb(), &item, baseline, stops, false);
    if transition == CastTransition::Form {
        item.emit_all_remaining_leading(&mut *i.state);
        cast_target_introducer_missing(&mut i, &item, item_origin);
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
            sequence,
        );
    }
    if transition == CastTransition::OuterBoundary {
        cast_target_introducer_missing(&mut i, &item, item_origin);
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
            sequence,
        );
    }
    if is_type_nud(&item) {
        i.state.start_node(SyntaxKind::CastTarget.into());
        cast_target_introducer_missing(&mut i, &item, item_origin);
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
            sequence,
        );
    }

    let (next_item, next_origin, next_line, error_exit) = cast_target_introducer_error_run(
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    item = next_item;
    item_origin = next_origin;
    line_entry = next_line;
    match error_exit {
        CastTargetIntroducerErrorExit::Form => {
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
                sequence,
            );
        }
        CastTargetIntroducerErrorExit::Boundary => {
            return complete(handoff(item), line_entry);
        }
        CastTargetIntroducerErrorExit::Target | CastTargetIntroducerErrorExit::Type => {
            item.emit_all_remaining_leading(&mut *i.state);
            i.state.start_node(SyntaxKind::CastTarget.into());
            let has_colon = error_exit == CastTargetIntroducerErrorExit::Target;
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
                sequence,
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_target_type_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
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
            sequence,
        )
    } else {
        complete(handoff(item), line_entry)
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_form_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
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
                    sequence,
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
        cast_body_introducer_missing(&mut i, &item, item_origin);
        return complete(handoff(item), line_entry);
    }

    item.emit_all_remaining_leading(&mut *i.state);
    let (item, item_origin, line_entry, exit) = cast_body_introducer_error_run(
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    match exit {
        CastBodyIntroducerErrorExit::Form => {
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
                sequence,
            );
        }
        CastBodyIntroducerErrorExit::Boundary => {
            return complete(handoff(item), line_entry);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_definition_body_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    match introduced_body_indentation_normalized(i.rb(), item_origin, fence) {
        Some(indentation) if indentation > baseline => indented_statement_block_normalized(
            i,
            baseline,
            crate::recovery_record::GrammarRole::Declaration(
                crate::recovery_record::DeclarationRole::Cast(
                    crate::recovery_record::CastRole::IndentedStatement,
                ),
            ),
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(_) => {
            let (item, item_origin, line_entry) = cast_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                CastVocabulary::Statement,
            );
            cast_body_missing(&mut i, &item, item_origin);
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
            sequence,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_inline_body_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let (mut item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    if cast_inline_body_boundary(i.rb(), &item, baseline, stops) {
        emit_cast_body_eof_leading(&mut i, &mut item, baseline, stops);
        cast_body_missing(&mut i, &item, item_origin);
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
            sequence,
        );
    }

    let (mut item, item_origin, line_entry) = cast_body_error_run(
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if cast_inline_body_boundary(i.rb(), &item, baseline, stops) {
        emit_cast_body_eof_leading(&mut i, &mut item, baseline, stops);
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    debug_assert!(is_nud_item(&item));
    expr_from_nud_normalized(
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
        sequence,
    )
}

fn cast_inline_body_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    cast_inline_body_static_boundary(item, baseline, stops) || is_active_stop(i.rb(), item, stops)
}

fn cast_inline_body_static_boundary(item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_line_stop(item, stops)
        || implicit_delimited_newline(baseline, item.leading_view())
        || matches!(
            cast_token_kind(item),
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
}

fn emit_cast_body_eof_leading(i: &mut SyntaxIn, item: &mut Item, baseline: usize, stops: Stops) {
    if item.payload_view().is_eof()
        && !item.payload_view().is_boundary()
        && !is_line_stop(item, stops)
        && !implicit_delimited_newline(baseline, item.leading_view())
        && !item.leading_view().contains_line_break()
    {
        item.emit_eof_leading(&mut *i.state);
    }
}

fn after_bodyless_normalized(
    i: SyntaxIn,
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

fn slot_outer_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
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
    mut i: SyntaxIn,
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CastPatternIntroducerErrorExit {
    Pattern,
    Target,
    Form,
    Boundary,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CastTargetIntroducerErrorExit {
    Target,
    Type,
    Form,
    Boundary,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CastBodyIntroducerErrorExit {
    Form,
    Boundary,
}

fn cast_pattern_introducer_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Cast(CastRole::PatternIntroducer))
}

fn cast_pattern_introducer_draft(
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let role = cast_pattern_introducer_role();
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Open(
                Delimiter::Parenthesis,
            )),
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

fn cast_pattern_introducer_missing(i: &mut SyntaxIn, item: &Item, origin: usize) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        cast_pattern_introducer_draft(RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn cast_pattern_missing(i: &mut SyntaxIn, item: &Item, origin: usize) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    let role = GrammarRole::Declaration(DeclarationRole::Cast(CastRole::Pattern));
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        RecoveryDraft::new(
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Pattern,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
}

fn cast_target_introducer_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Cast(CastRole::TargetIntroducer))
}

fn cast_target_introducer_draft(
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let role = cast_target_introducer_role();
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

fn cast_target_introducer_missing(i: &mut SyntaxIn, item: &Item, origin: usize) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        cast_target_introducer_draft(RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn cast_body_introducer_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Cast(CastRole::BodyIntroducer))
}

fn cast_body_introducer_draft(
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let role = cast_body_introducer_role();
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

fn cast_body_introducer_missing(i: &mut SyntaxIn, item: &Item, origin: usize) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        cast_body_introducer_draft(RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn cast_body_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Cast(CastRole::Body))
}

fn cast_body_draft(
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let role = cast_body_role();
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Expression,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

fn cast_body_missing(i: &mut SyntaxIn, item: &Item, origin: usize) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(
        i.rb(),
        crate::lexical::item::LeadingTrivia::default(),
        at,
        |range| cast_body_draft(RecoveryKind::Missing, range, Arc::from([])),
    );
}

fn cast_pattern_close_role() -> GrammarRole {
    GrammarRole::ClosingDelimiter {
        owner: crate::recovery_record::ConstructRole::CastPattern,
        delimiter: Delimiter::Parenthesis,
    }
}

fn cast_pattern_close_missing(i: &mut SyntaxIn, item: &Item, origin: usize) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    let role = cast_pattern_close_role();
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        RecoveryDraft::new(
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Close(
                    Delimiter::Parenthesis,
                )),
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
}

#[allow(clippy::too_many_arguments)]
fn cast_pattern_close_error_run(
    i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut origin: usize,
    mut line: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry, CastTransition) {
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(origin).recovery_range().start;
            loop {
                let kind = cast_error_syntax_kind(&item);
                let end = run.emit_item_as(item, origin, kind).recovery_range().end;
                (item, origin, line) = run.lexical(|lex| {
                    scan_cast_item_lexical(
                        lex,
                        origin,
                        line,
                        fence,
                        baseline,
                        stops,
                        CastVocabulary::Statement,
                    )
                });
                let transition = cast_transition_lex(run, &item, baseline, stops);
                if transition != CastTransition::Other {
                    let error_end = if transition == CastTransition::OuterBoundary
                        && cast_error_owns_eof_leading(&item)
                        && !item.extent(origin).remaining().is_empty()
                    {
                        run.emit_same_line_eof_leading(&mut item, origin).end
                    } else {
                        end
                    };
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..error_end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return (item, origin, line, transition);
                }
            }
        },
        |range, unexpected| {
            let role = cast_pattern_close_role();
            RecoveryDraft::new(
                RecoverySiteKey {
                    role,
                    range: range.clone(),
                },
                RecoveryKind::Error,
                unexpected,
                Arc::from([SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Close(
                        Delimiter::Parenthesis,
                    )),
                    range,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }]),
                0,
            )
        },
    )
}

fn cast_transition_lex(
    run: &mut crate::cst_output::emit::ErrorRunOutput<'_, '_, '_, '_, '_, '_>,
    item: &Item,
    baseline: usize,
    stops: Stops,
) -> CastTransition {
    if cast_token_kind(item) == Some(TokenKind::RParen) {
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
    if item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || run.lexical(|lex| is_active_stop_lex(lex, item, stops))
        || is_line_stop(item, stops)
        || is_separator(item)
        || matches!(
            cast_token_kind(item),
            Some(TokenKind::RBracket | TokenKind::RBrace)
        )
    {
        CastTransition::OuterBoundary
    } else {
        CastTransition::Other
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_body_introducer_error_run(
    i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut origin: usize,
    mut line: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry, CastBodyIntroducerErrorExit) {
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(origin).recovery_range().start;
            loop {
                let kind = cast_error_syntax_kind(&item);
                let end = run.emit_item_as(item, origin, kind).recovery_range().end;
                (item, origin, line) = run.lexical(|lex| {
                    scan_cast_item_lexical(
                        lex,
                        origin,
                        line,
                        fence,
                        baseline,
                        stops,
                        CastVocabulary::Form,
                    )
                });
                let exit = if is_form_starter(&item) && cast_gap_allowed(&item, baseline) {
                    Some(CastBodyIntroducerErrorExit::Form)
                } else if cast_prefix_boundary_lex(run, &item, baseline, stops) {
                    Some(CastBodyIntroducerErrorExit::Boundary)
                } else {
                    None
                };
                if let Some(exit) = exit {
                    let error_end = if exit == CastBodyIntroducerErrorExit::Boundary
                        && cast_error_owns_eof_leading(&item)
                        && !item.extent(origin).remaining().is_empty()
                    {
                        run.emit_same_line_eof_leading(&mut item, origin).end
                    } else {
                        end
                    };
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..error_end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return (item, origin, line, exit);
                }
            }
        },
        |range, unexpected| cast_body_introducer_draft(RecoveryKind::Error, range, unexpected),
    )
}

#[allow(clippy::too_many_arguments)]
fn cast_body_error_run(
    i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut origin: usize,
    mut line: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let start = item.extent(origin).recovery_range().start;
    emit_recovery_error_run(
        i,
        |run| loop {
            let kind = cast_error_syntax_kind(&item);
            let end = run.emit_item_as(item, origin, kind).recovery_range().end;
            (item, origin, line) = run.lexical(|lex| {
                crate::lexical::expression_item::scan_expression_item_lexical(
                    lex,
                    OperatorSite::Nud,
                    origin,
                    line,
                    fence,
                    baseline,
                    stops,
                )
            });
            if cast_inline_body_static_boundary(&item, baseline, stops)
                || run.lexical(|lex| is_active_stop_lex(lex, &item, stops))
                || is_nud_item(&item)
            {
                let error_end = if cast_inline_body_static_boundary(&item, baseline, stops)
                    && cast_error_owns_eof_leading(&item)
                    && !item.extent(origin).remaining().is_empty()
                {
                    run.emit_same_line_eof_leading(&mut item, origin).end
                } else {
                    end
                };
                run.append_unexpected(UnexpectedSyntax::Token {
                    range: start..error_end,
                    category: UnexpectedCategory::OtherCharacter,
                });
                return (item, origin, line);
            }
        },
        |range, unexpected| cast_body_draft(RecoveryKind::Error, range, unexpected),
    )
}

#[allow(clippy::too_many_arguments)]
fn cast_target_introducer_error_run(
    i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut origin: usize,
    mut line: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry, CastTargetIntroducerErrorExit) {
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(origin).recovery_range().start;
            loop {
                let kind = cast_error_syntax_kind(&item);
                let end = run.emit_item_as(item, origin, kind).recovery_range().end;
                (item, origin, line) = run.lexical(|lex| {
                    scan_cast_item_lexical(
                        lex,
                        origin,
                        line,
                        fence,
                        baseline,
                        stops,
                        CastVocabulary::Type,
                    )
                });
                let exit = if cast_token_kind(&item) == Some(TokenKind::Colon)
                    && cast_gap_allowed(&item, baseline)
                {
                    Some(CastTargetIntroducerErrorExit::Target)
                } else if is_form_starter(&item) && cast_gap_allowed(&item, baseline) {
                    Some(CastTargetIntroducerErrorExit::Form)
                } else if cast_prefix_boundary_lex(run, &item, baseline, stops) {
                    Some(CastTargetIntroducerErrorExit::Boundary)
                } else if is_type_nud(&item) {
                    Some(CastTargetIntroducerErrorExit::Type)
                } else {
                    None
                };
                if let Some(exit) = exit {
                    let error_end = if exit == CastTargetIntroducerErrorExit::Boundary
                        && cast_error_owns_eof_leading(&item)
                        && !item.extent(origin).remaining().is_empty()
                    {
                        run.emit_same_line_eof_leading(&mut item, origin).end
                    } else {
                        end
                    };
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..error_end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return (item, origin, line, exit);
                }
            }
        },
        |range, unexpected| cast_target_introducer_draft(RecoveryKind::Error, range, unexpected),
    )
}

#[allow(clippy::too_many_arguments)]
fn cast_pattern_introducer_error_run(
    i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut origin: usize,
    mut line: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry, CastPatternIntroducerErrorExit) {
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(origin).recovery_range().start;
            loop {
                let kind = cast_error_syntax_kind(&item);
                let end = run.emit_item_as(item, origin, kind).recovery_range().end;
                (item, origin, line) = run.lexical(|lex| {
                    scan_cast_item_lexical(
                        lex,
                        origin,
                        line,
                        fence,
                        baseline,
                        stops,
                        CastVocabulary::Pattern,
                    )
                });
                let exit = if cast_token_kind(&item) == Some(TokenKind::Colon)
                    && cast_gap_allowed(&item, baseline)
                {
                    Some(CastPatternIntroducerErrorExit::Target)
                } else if is_form_starter(&item) && cast_gap_allowed(&item, baseline) {
                    Some(CastPatternIntroducerErrorExit::Form)
                } else if cast_prefix_boundary_lex(run, &item, baseline, stops) {
                    Some(CastPatternIntroducerErrorExit::Boundary)
                } else if cast_token_kind(&item) == Some(TokenKind::LParen)
                    || is_pattern_nud(&item, 0)
                {
                    Some(CastPatternIntroducerErrorExit::Pattern)
                } else {
                    None
                };
                if let Some(exit) = exit {
                    let error_end = if exit == CastPatternIntroducerErrorExit::Boundary
                        && cast_error_owns_eof_leading(&item)
                        && !item.extent(origin).remaining().is_empty()
                    {
                        run.emit_same_line_eof_leading(&mut item, origin).end
                    } else {
                        end
                    };
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..error_end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return (item, origin, line, exit);
                }
            }
        },
        |range, unexpected| cast_pattern_introducer_draft(RecoveryKind::Error, range, unexpected),
    )
}

fn cast_prefix_boundary_lex(
    run: &mut crate::cst_output::emit::ErrorRunOutput<'_, '_, '_, '_, '_, '_>,
    item: &Item,
    baseline: usize,
    stops: Stops,
) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || !cast_gap_allowed(item, baseline)
        || run.lexical(|lex| is_active_stop_lex(lex, item, stops))
        || is_line_stop(item, stops)
        || is_separator(item)
        || matches!(
            cast_token_kind(item),
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
}

fn cast_error_syntax_kind(item: &Item) -> SyntaxKind {
    token_kind(item)
        .map(token_syntax_kind)
        .unwrap_or(SyntaxKind::Operator)
}

fn cast_gap_allowed(item: &Item, baseline: usize) -> bool {
    crate::lexical::observation::indentation_after_newline(item.leading_view())
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
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    vocabulary: CastVocabulary,
) -> (Item, usize, LineEntry) {
    let entry = suffix_marker(i.rb());
    let (item, _, next_line_entry) = i
        .token(|lex| {
            Some(scan_cast_item_lexical(
                lex,
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                vocabulary,
            ))
        })
        .expect("Cast declaration payload scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

#[allow(clippy::too_many_arguments)]
fn scan_cast_item_lexical(
    i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    vocabulary: CastVocabulary,
) -> (Item, usize, LineEntry) {
    let (current, consumed) = i.with_str(|lex| {
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
                CastVocabulary::Pattern => scan_pattern_nud_payload(lex, leading, origin, fence, 0),
                CastVocabulary::Type => scan_type_nud_payload(lex, leading, origin, fence),
                // This is lexical-only form punctuation acquisition. The existing
                // Type token vocabulary keeps exact `=` distinct from malformed
                // Statement operators so the form owner can retry it unchanged.
                CastVocabulary::Form => scan_type_nud_payload(lex, leading, origin, fence),
                CastVocabulary::Statement => {
                    scan_statement_payload(lex, leading, origin, fence, baseline, stops)
                }
            },
        )
        .expect("Cast declaration payload scanning is total")
    });
    (
        current.item,
        item_origin
            .checked_add(consumed.len())
            .expect("Cast declaration coordinate fits usize"),
        current.next_line_entry,
    )
}

fn item_word(item: &Item) -> Option<&str> {
    (item.payload_view().token_kind() == Some(TokenKind::Identifier))
        .then(|| item.payload_view().spelling())
        .flatten()
}

fn emit_item_as(i: &mut SyntaxIn, item: Item, kind: SyntaxKind) {
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_visibility(i: &mut SyntaxIn, item: Item) {
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("Cast visibility uses exact declaration words"),
    };
    emit_item_as(i, item, kind);
}
