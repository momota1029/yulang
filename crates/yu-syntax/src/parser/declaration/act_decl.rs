//! Private direct `act` declaration construction.

use crate::parser::context::ambient_claim::AmbientClaimContext;
#[cfg(test)]
use crate::parser::context::ambient_claim::AmbientClaimView;
use crate::parser::output::RecoveryDraft;
use crate::session::{
    ActDeclarationRole, DeclarationRole, Delimiter, ExpectationSources, ExpectedSyntax,
    GrammarRole, PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
    UnexpectedCategory, UnexpectedSyntax,
};
use reborrow_generic::Reborrow as _;
use std::sync::Arc;

use crate::syntax_kind::SyntaxKind;

use crate::parser::{
    LexIn, ParserIn, Stops,
    declaration::{
        declaration_companion::declaration_companion_normalized,
        derives::{derives_clause_normalized, is_word},
    },
    expression::if_expr::active_statement_companion,
    handoff::{Either, NormalizedExit, complete, handoff},
    input::{
        current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
        item::{Item, LeadingTrivia, TokenKind},
        lexer::{
            introduced_body_indentation_normalized, scan_identifier, scan_statement_payload,
            scan_type_nud_payload, source_declaration_head, source_identifier,
        },
        observation::{
            implicit_delimited_newline, indentation_after_newline, is_active_stop, is_separator,
            token_kind,
        },
        operator::{STOP_WITH, TriviaObservation, observe_fenced_trivia},
        position::{advanced_origin, suffix_marker},
        yumark::FenceBoundary,
    },
    output::emit::{
        emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
    },
    statement::{
        StatementAdmission, StatementLineHandoff, braced_statement_block_normalized,
        canonical_statement_from_admission_normalized, classify_statement_item_normalized,
        indented_statement_block_normalized,
    },
    type_expr::{
        TypeOuterBoundary, is_type_caller_boundary,
        required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient,
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ActTypeSlot {
    Head,
    Source,
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(in crate::parser) fn act_declaration_witness(
    mut i: ParserIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<NormalizedExit> {
    if !act_source_selected_normalized(i.rb(), baseline, item_origin, line_entry, fence) {
        return None;
    }
    let (intro, item_origin, line_entry) = act_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        true,
        false,
    );
    act_declaration_selected_normalized(i.rb(), &intro, baseline, item_origin, fence).then(|| {
        act_declaration_normalized(
            i,
            intro,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            Some(AmbientClaimView::root_statement(baseline)).into(),
            Some(crate::parser::context::sequence::SequenceOwner::RootStatement),
        )
    })
}

#[cfg(test)]
fn act_source_selected_normalized(
    i: ParserIn,
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
            let Some((word, suffix)) = source_identifier(observed.source) else {
                return Some(false);
            };
            if word == "act" {
                return Some(true);
            }
            if !matches!(word, "my" | "our" | "pub") {
                return Some(false);
            }
            let leading_len = source.len() - observed.source.len();
            Some(prefixed_act_candidate_normalized(
                suffix,
                item_origin + leading_len + word.len(),
                fence,
                baseline,
                word == "my",
            ))
        },
        |selected| selected,
    )
    .unwrap_or(false)
}

#[cfg(test)]
pub(in crate::parser) fn act_declaration_selected_normalized(
    i: ParserIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            Some(act_declaration_selected_lexical(
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

pub(in crate::parser) fn act_declaration_selected_lexical(
    source: &str,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item_word(item) == Some("act") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    prefixed_act_candidate_normalized(
        source,
        item_origin,
        fence,
        baseline,
        item_word(item) == Some("my"),
    )
}

fn prefixed_act_candidate_normalized(
    source: &str,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    require_head: bool,
) -> bool {
    let TriviaObservation::Visible(observed) =
        observe_fenced_trivia(source, item_origin, LineEntry::InLine, fence)
    else {
        return false;
    };
    if !observed.present
        || observed
            .indentation
            .is_some_and(|indentation| indentation <= baseline)
    {
        return false;
    }
    let Some((word, after_keyword)) = source_identifier(observed.source) else {
        return false;
    };
    if word != "act" {
        return false;
    }
    if !require_head {
        return true;
    }

    let leading_len = source.len() - observed.source.len();
    let keyword_end = item_origin + leading_len + word.len();
    let TriviaObservation::Visible(head) =
        observe_fenced_trivia(after_keyword, keyword_end, LineEntry::InLine, fence)
    else {
        return false;
    };
    head.indentation
        .is_none_or(|indentation| indentation > baseline)
        && source_declaration_head(head.source)
}

#[allow(clippy::too_many_arguments)]
pub(in crate::parser) fn act_declaration_normalized(
    mut i: ParserIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::ActDeclaration.into());
    if item_word(&intro) == Some("act") {
        emit_item_as(&mut i, intro, SyntaxKind::ActKw);
    } else {
        emit_visibility(&mut i, intro);
        let (mut keyword, next_origin, next_entry) = act_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            true,
            false,
        );
        item_origin = next_origin;
        line_entry = next_entry;
        debug_assert!(act_gap_allowed(&keyword, baseline));
        debug_assert_eq!(item_word(&keyword), Some("act"));
        keyword.emit_all_remaining_leading(&mut *i.state);
        emit_item_as(&mut i, keyword, SyntaxKind::ActKw);
    }

    let (head, next_origin, next_entry) = act_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        false,
        true,
    );
    item_origin = next_origin;
    line_entry = next_entry;
    let (item, head_complete, next_origin, next_entry) = type_slot_from_item_normalized(
        i.rb(),
        head,
        ActTypeSlot::Head,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let exit = after_head_normalized(
        i.rb(),
        item,
        head_complete,
        baseline,
        stops,
        line_handoff,
        next_origin,
        next_entry,
        fence,
        ambient,
        sequence,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn type_slot_from_item_normalized(
    mut i: ParserIn,
    mut primary: Item,
    slot: ActTypeSlot,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> (Item, bool, usize, LineEntry) {
    let fresh_derives = is_word(&primary, "derives")
        && act_gap_allowed(&primary, baseline)
        && !is_type_caller_boundary(&primary, stops);
    let outer_boundary = act_type_outer_boundary(slot, !fresh_derives);
    if !type_slot_gap_is_outer_owned(i.rb(), &primary, slot, baseline, stops, !fresh_derives) {
        primary.emit_all_remaining_leading(&mut *i.state);
    }

    let child_entry = suffix_marker(i.rb());
    let (exit, primary_found) =
        required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient(
            i.rb(),
            primary,
            GrammarRole::Declaration(DeclarationRole::Act(match slot {
                ActTypeSlot::Head => ActDeclarationRole::Head,
                ActTypeSlot::Source => ActDeclarationRole::Source,
            })),
            baseline,
            stops,
            outer_boundary,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    let item_origin = advanced_origin(item_origin, child_entry, i.rb());
    let (item, item_origin, line_entry) =
        successor_after_type_normalized(i, exit, item_origin, baseline, stops, fence);
    (item, primary_found, item_origin, line_entry)
}

fn act_type_outer_boundary(slot: ActTypeSlot, derives: bool) -> TypeOuterBoundary {
    let mut boundary = TypeOuterBoundary::WITH.with(TypeOuterBoundary::VARIANT_BODY);
    if slot == ActTypeSlot::Head {
        boundary = boundary.with(TypeOuterBoundary::EQUALS);
    }
    if derives {
        boundary = boundary.with(TypeOuterBoundary::DERIVES);
    }
    boundary
}

#[allow(clippy::too_many_arguments)]
fn successor_after_type_normalized(
    i: ParserIn,
    exit: NormalizedExit,
    item_origin: usize,
    baseline: usize,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => act_item_normalized(
            i,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            false,
            true,
        ),
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            (item, item_origin, line_entry)
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            (end.item, item_origin, line_entry)
        }
        NormalizedExit::Deferred(_, _) => {
            unreachable!("normalized TypeExpression does not defer an Act owner")
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn after_head_normalized(
    mut i: ParserIn,
    mut item: Item,
    head_complete: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    if stops & STOP_WITH != 0 && is_word(&item, "with") {
        return complete(handoff(item), line_entry);
    }
    if head_complete {
        (item, item_origin, line_entry) = header_derives_normalized(
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
    }
    if declaration_companion_start(i.rb(), &item, baseline, stops, line_handoff) {
        return declaration_companion_normalized(
            i,
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if source_clause_start(i.rb(), &item, baseline, stops, line_handoff) {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_token_item(&mut i, item);
        return source_slot_normalized(
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
    body_from_item_normalized(
        i,
        item,
        head_complete,
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
fn source_slot_normalized(
    mut i: ParserIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    let (source, item_origin, line_entry) = act_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        false,
        true,
    );
    let (mut item, source_complete, mut item_origin, mut line_entry) =
        type_slot_from_item_normalized(
            i.rb(),
            source,
            ActTypeSlot::Source,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    if stops & STOP_WITH != 0 && is_word(&item, "with") {
        return complete(handoff(item), line_entry);
    }
    if source_complete {
        (item, item_origin, line_entry) = header_derives_normalized(
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
    }
    if declaration_companion_start(i.rb(), &item, baseline, stops, line_handoff) {
        return declaration_companion_normalized(
            i,
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    body_from_item_normalized(
        i,
        item,
        source_complete,
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
fn header_derives_normalized(
    mut i: ParserIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> (Item, usize, LineEntry) {
    while derives_attachment_start(i.rb(), &item, baseline, stops, line_handoff) {
        (item, item_origin, line_entry) = derives_clause_normalized(
            i.rb(),
            item,
            baseline,
            stops,
            line_handoff,
            act_header_role_boundary(),
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    (item, item_origin, line_entry)
}

#[allow(clippy::too_many_arguments)]
fn body_from_item_normalized(
    mut i: ParserIn,
    mut item: Item,
    predecessor_complete: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    if !body_starter(&item) && body_boundary(i.rb(), &item, baseline, stops) {
        return complete(handoff(item), line_entry);
    }
    if !act_gap_allowed(&item, baseline) {
        return complete(handoff(item), line_entry);
    }
    if !predecessor_complete && !body_starter(&item) {
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    match token_kind(&item) {
        Some(TokenKind::Semicolon) => {
            emit_token_item(&mut i, item);
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        Some(TokenKind::LBrace) => {
            let child_entry = suffix_marker(i.rb());
            let exit = braced_statement_block_normalized(
                i.rb(),
                item,
                baseline,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
            let item_origin = advanced_origin(item_origin, child_entry, i.rb());
            match exit {
                NormalizedExit::Complete(Ok(()), line_entry) => trailing_after_brace_normalized(
                    i,
                    baseline,
                    stops,
                    line_handoff,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                ),
                exit => exit,
            }
        }
        Some(TokenKind::Colon) => {
            emit_token_item(&mut i, item);
            colon_body_normalized(
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
        _ if predecessor_complete => recover_body_introducer_normalized(
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
        _ => complete(handoff(item), line_entry),
    }
}

#[allow(clippy::too_many_arguments)]
fn recover_body_introducer_normalized(
    mut i: ParserIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    item.emit_all_remaining_leading(&mut *i.state);
    (item, item_origin, line_entry) = act_error_run(
        i.rb(),
        item,
        ActDeclarationRole::BodyIntroducer,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if act_gap_allowed(&item, baseline) && body_starter(&item) {
        return body_from_item_normalized(
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
    complete(handoff(item), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn colon_body_normalized(
    mut i: ParserIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    match introduced_body_indentation_normalized(i.rb(), item_origin, fence) {
        Some(indentation) if indentation > baseline => indented_statement_block_normalized(
            i,
            baseline,
            crate::session::GrammarRole::Declaration(crate::session::DeclarationRole::Act(
                crate::session::ActDeclarationRole::IndentedStatement,
            )),
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(_) => {
            let (item, origin, line_entry) = act_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                false,
                false,
            );
            act_missing(&mut i, &item, origin, ActDeclarationRole::Body);
            complete(handoff(item), line_entry)
        }
        None => {
            let (item, item_origin, line_entry) = act_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                false,
                false,
            );
            inline_body_from_item_normalized(
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
    }
}

#[allow(clippy::too_many_arguments)]
fn inline_body_from_item_normalized(
    mut i: ParserIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    if inline_body_boundary(i.rb(), &item, baseline, stops) {
        act_missing(&mut i, &item, item_origin, ActDeclarationRole::Body);
        return complete(handoff(item), line_entry);
    }
    if let Some(admission) =
        classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
    {
        return inline_statement_normalized(
            i,
            item,
            admission,
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
    recover_inline_body_normalized(
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
fn recover_inline_body_normalized(
    mut i: ParserIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    item.emit_all_remaining_leading(&mut *i.state);
    (item, item_origin, line_entry) = act_error_run(
        i.rb(),
        item,
        ActDeclarationRole::Body,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if inline_body_boundary(i.rb(), &item, baseline, stops) {
        return complete(handoff(item), line_entry);
    }
    if let Some(admission) =
        classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
    {
        return inline_statement_normalized(
            i,
            item,
            admission,
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
    unreachable!("Act body recovery stops at a boundary or Statement")
}

#[allow(clippy::too_many_arguments)]
fn inline_statement_normalized(
    mut i: ParserIn,
    item: Item,
    admission: StatementAdmission,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
) -> NormalizedExit {
    let child_entry = suffix_marker(i.rb());
    let exit = canonical_statement_from_admission_normalized(
        i.rb(),
        item,
        admission,
        baseline,
        stops,
        line_handoff.through_inline_statement(),
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    let item_origin = advanced_origin(item_origin, child_entry, i.rb());
    match exit {
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if inline_terminal_semicolon(&item) =>
        {
            emit_token_item(&mut i, item);
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        NormalizedExit::Complete(Ok(()), line_entry) => {
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        exit => exit,
    }
}

#[allow(clippy::too_many_arguments)]
fn trailing_after_brace_normalized(
    mut i: ParserIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let (mut item, next_origin, next_entry) = act_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        false,
        true,
    );
    item_origin = next_origin;
    line_entry = next_entry;
    while derives_attachment_start(i.rb(), &item, baseline, stops, line_handoff) {
        (item, item_origin, line_entry) = derives_clause_normalized(
            i.rb(),
            item,
            baseline,
            stops,
            line_handoff,
            act_trailing_role_boundary(),
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    complete(handoff(item), line_entry)
}

fn after_completed_normalized(
    i: ParserIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, _, line_entry) = act_item_normalized(
        i,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        false,
        false,
    );
    complete(handoff(item), line_entry)
}

fn source_clause_start(
    mut i: ParserIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> bool {
    attachment_gap_continues(i.rb(), item, baseline, stops, line_handoff)
        && token_kind(item) == Some(TokenKind::Equals)
}

fn derives_attachment_start(
    mut i: ParserIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> bool {
    is_word(item, "derives")
        && item.leading_view().has_ordinary_trivia()
        && attachment_gap_continues(i.rb(), item, baseline, stops, line_handoff)
}

fn declaration_companion_start(
    mut i: ParserIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> bool {
    is_word(item, "with")
        && item.leading_view().has_ordinary_trivia()
        && attachment_gap_continues(i.rb(), item, baseline, stops, line_handoff)
}

fn attachment_gap_continues(
    mut i: ParserIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> bool {
    !item.payload_view().is_boundary()
        && !is_active_stop(i.rb(), item, stops)
        && !(stops & STOP_WITH != 0 && is_word(item, "with"))
        && active_statement_companion(i.rb(), item, baseline, stops).is_none()
        && indentation_after_newline(item.leading_view()).is_none_or(|indentation| {
            matches!(line_handoff, StatementLineHandoff::OrdinaryLayout) && indentation > baseline
        })
}

fn act_header_role_boundary() -> TypeOuterBoundary {
    TypeOuterBoundary::DERIVES
        .with(TypeOuterBoundary::VIA)
        .with(TypeOuterBoundary::WITH)
        .with(TypeOuterBoundary::EQUALS)
        .with(TypeOuterBoundary::VARIANT_BODY)
}

fn act_trailing_role_boundary() -> TypeOuterBoundary {
    TypeOuterBoundary::DERIVES.with(TypeOuterBoundary::VIA)
}

fn type_slot_gap_is_outer_owned(
    mut i: ParserIn,
    item: &Item,
    slot: ActTypeSlot,
    baseline: usize,
    stops: Stops,
    derives_boundary: bool,
) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || !act_gap_allowed(item, baseline)
        || is_type_caller_boundary(item, stops)
        || matches!(
            token_kind(item),
            Some(TokenKind::Colon | TokenKind::LBrace | TokenKind::Semicolon)
        )
        || (slot == ActTypeSlot::Head && token_kind(item) == Some(TokenKind::Equals))
        || is_word(item, "with")
        || (derives_boundary && is_word(item, "derives"))
        || is_active_stop(i.rb(), item, stops)
}

fn body_boundary(mut i: ParserIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || implicit_delimited_newline(baseline, item.leading_view())
        || is_active_stop(i.rb(), item, stops)
        || is_separator(item)
        || matches!(
            token_kind(item),
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
        || active_statement_companion(i.rb(), item, baseline, stops).is_some()
}

fn inline_body_boundary(mut i: ParserIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    body_boundary(i.rb(), item, baseline, stops) || token_kind(item) == Some(TokenKind::Semicolon)
}

fn act_gap_allowed(item: &Item, baseline: usize) -> bool {
    indentation_after_newline(item.leading_view()).is_none_or(|indentation| indentation > baseline)
}

fn body_starter(item: &Item) -> bool {
    !item.payload_view().is_boundary()
        && matches!(
            token_kind(item),
            Some(TokenKind::Semicolon | TokenKind::LBrace | TokenKind::Colon)
        )
}

fn inline_terminal_semicolon(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Semicolon)
        && indentation_after_newline(item.leading_view()).is_none()
}

#[allow(clippy::too_many_arguments)]
fn act_item_normalized(
    mut i: ParserIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
) -> (Item, usize, LineEntry) {
    i.token(|lex| {
        Some(scan_act_item(
            lex,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            raw_identifier,
            type_vocabulary,
        ))
    })
    .expect("Act Item scan is total")
}

#[allow(clippy::too_many_arguments)]
fn scan_act_item(
    mut i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
) -> (Item, usize, LineEntry) {
    let entry = i.remainder().len();
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
                |mut lex, leading, origin, fence, _| {
                    if raw_identifier && let Some(identifier) = lex.token(scan_identifier) {
                        return Some(AcceptedPayload {
                            payload: CurrentPayload::Token(identifier),
                            next_line_entry: LineEntry::InLine,
                        });
                    }
                    if type_vocabulary {
                        scan_type_nud_payload(lex, leading, origin, fence)
                    } else {
                        scan_statement_payload(lex, leading, origin, fence, baseline, stops)
                    }
                },
            )
        })
        .expect("Act declaration payload scanning is total");
    (
        item,
        item_origin + entry - i.remainder().len(),
        next_line_entry,
    )
}

fn item_word(item: &Item) -> Option<&str> {
    (item.payload_view().token_kind() == Some(TokenKind::Identifier))
        .then(|| item.payload_view().spelling())
        .flatten()
}

fn act_draft(
    slot: ActDeclarationRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let role = GrammarRole::Declaration(DeclarationRole::Act(slot));
    let expected: &[ExpectedSyntax] = match slot {
        ActDeclarationRole::BodyIntroducer => &[
            ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        ],
        ActDeclarationRole::Body => &[ExpectedSyntax::Statement],
        _ => unreachable!("local Act recovery slot"),
    };
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        expected
            .iter()
            .map(|expected| SyntaxExpectation {
                role,
                expected: *expected,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            })
            .collect::<Vec<_>>()
            .into(),
        0,
    )
}

fn act_missing(i: &mut ParserIn, item: &Item, origin: usize, role: ActDeclarationRole) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        act_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

#[allow(clippy::too_many_arguments)]
fn act_error_run(
    mut i: ParserIn,
    mut item: Item,
    role: ActDeclarationRole,
    baseline: usize,
    stops: Stops,
    mut origin: usize,
    mut line: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let start = item.extent(origin).recovery_range().start;
    emit_recovery_error_run(
        i.rb(),
        |run| loop {
            let kind = token_kind(&item)
                .map(token_syntax_kind)
                .unwrap_or(SyntaxKind::Operator);
            let end = run.emit_item_as(item, origin, kind).recovery_range().end;
            (item, origin, line) = run.lexical(|lex| {
                scan_act_item(lex, origin, line, fence, baseline, stops, false, false)
            });
            let starter = role == ActDeclarationRole::BodyIntroducer && body_starter(&item);
            let boundary = item.payload_view().is_boundary()
                || item.payload_view().is_eof()
                || !act_gap_allowed(&item, baseline)
                || (!starter
                    && (run.lexical(|lex| {
                        crate::parser::input::observation::is_active_stop_lex(lex, &item, stops)
                    }) || is_separator(&item)
                        || matches!(
                            token_kind(&item),
                            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
                        )));
            let retry = !boundary
                && (starter
                    || (role == ActDeclarationRole::Body
                        && run
                            .lexical(|lex| {
                                crate::parser::statement::classify_statement_item_lexical(
                                    lex.remainder(),
                                    &item,
                                    baseline,
                                    origin,
                                    fence,
                                )
                            })
                            .is_some()));
            if boundary || retry {
                run.append_unexpected(UnexpectedSyntax::Token {
                    range: start..end,
                    category: UnexpectedCategory::OtherCharacter,
                });
                return (item, origin, line);
            }
        },
        |range, unexpected| act_draft(role, RecoveryKind::Error, range, unexpected),
    )
}

fn emit_item_as(i: &mut ParserIn, item: Item, kind: SyntaxKind) {
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_visibility(i: &mut ParserIn, item: Item) {
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("Act visibility uses exact declaration words"),
    };
    emit_item_as(i, item, kind);
}
