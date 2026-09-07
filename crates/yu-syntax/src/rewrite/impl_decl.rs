//! Private direct standalone `impl` declaration construction.

use super::ambient_claim::{AmbientClaimContext, AmbientClaimView};
use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn, Stops,
    current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
    driver::{
        Either, NormalizedExit, advanced_origin, complete, handoff, implicit_delimited_newline,
        indentation_after_newline, is_active_stop, is_separator, suffix_marker, token_kind,
    },
    emit::{emit_missing, emit_token_item},
    if_expr::active_statement_companion,
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{
        introduced_body_indentation_normalized, scan_identifier, scan_statement_payload,
        scan_type_nud_payload, source_identifier,
    },
    operator::{TriviaObservation, observe_fenced_trivia, observe_fenced_trivia_with_newline},
    statement::{
        StatementAdmission, StatementLineHandoff, braced_statement_block_normalized,
        canonical_statement_from_admission_normalized, classify_statement_item_normalized,
        indented_statement_block_normalized,
    },
    type_expr::{
        RequiredTypeFreshPrimaryPolicy, TypeOuterBoundary, is_type_caller_boundary,
        required_type_expr_with_caller_stops_and_outer_boundary_and_fresh_primary_policy_normalized,
        required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient,
    },
    yumark::FenceBoundary,
};

#[allow(clippy::too_many_arguments)]
pub(super) fn impl_declaration_witness(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<NormalizedExit> {
    if !impl_source_selected_normalized(i.rb(), baseline, item_origin, line_entry, fence) {
        return None;
    }
    let (intro, item_origin, line_entry) = impl_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        true,
        false,
    );
    impl_declaration_selected_normalized(i.rb(), &intro, baseline, item_origin, fence).then(|| {
        impl_declaration_normalized(
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

fn impl_source_selected_normalized(
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
            if word == "impl" {
                return Some(true);
            }
            if !matches!(word, "my" | "our" | "pub") {
                return Some(false);
            }
            let leading_len = source.len() - observed.source.len();
            Some(prefixed_impl_candidate_normalized(
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

pub(super) fn impl_declaration_selected_normalized(
    i: RewriteIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item_word(item) == Some("impl") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    observes(i, |source| {
        prefixed_impl_candidate_normalized(source, item_origin, fence, baseline)
    })
}

fn prefixed_impl_candidate_normalized(
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
        && source_identifier(observed.source).is_some_and(|(word, _)| word == "impl")
}

#[allow(clippy::too_many_arguments)]
pub(super) fn impl_declaration_normalized(
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
    i.state.start_node(SyntaxKind::ImplDeclaration.into());
    if item_word(&intro) == Some("impl") {
        emit_item_as(&mut i, intro, SyntaxKind::ImplKw);
    } else {
        emit_visibility(&mut i, intro);
        let (mut keyword, next_origin, next_entry) = impl_item_normalized(
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
        debug_assert!(impl_gap_allowed(&keyword, baseline));
        debug_assert_eq!(item_word(&keyword), Some("impl"));
        keyword.emit_all_remaining_leading(&mut *i.state);
        emit_item_as(&mut i, keyword, SyntaxKind::ImplKw);
    }

    let (mut head, next_origin, next_entry) = impl_item_normalized(
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
    let retry_after_missing_head = body_starter(&head);
    let local_missing_head_gap = retry_after_missing_head && impl_gap_allowed(&head, baseline);
    if local_missing_head_gap || !head_gap_is_outer_owned(i.rb(), &head, baseline, stops) {
        head.emit_all_remaining_leading(&mut *i.state);
    }

    let child_entry = suffix_marker(i.rb());
    let (exit, head_complete) =
        required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient(
            i.rb(),
            head,
            baseline,
            stops,
            TypeOuterBoundary::VARIANT_BODY,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    item_origin = advanced_origin(item_origin, child_entry, i.rb());
    let (item, item_origin, line_entry) =
        successor_after_type_normalized(i.rb(), exit, item_origin, baseline, stops, fence);
    let exit = after_head_from_item_normalized(
        i.rb(),
        item,
        head_complete,
        retry_after_missing_head,
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
fn successor_after_type_normalized(
    i: RewriteIn,
    exit: NormalizedExit,
    item_origin: usize,
    baseline: usize,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => impl_item_normalized(
            i,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            false,
            false,
        ),
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            (item, item_origin, line_entry)
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            (end.item, item_origin, line_entry)
        }
        NormalizedExit::Deferred(_, _) => {
            unreachable!("normalized TypeExpression does not defer an Impl owner")
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn after_head_from_item_normalized(
    mut i: RewriteIn,
    mut item: Item,
    head_complete: bool,
    retry_after_missing_head: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if !impl_gap_allowed(&item, baseline)
        || (!body_starter(&item) && body_boundary(i.rb(), &item, baseline, stops))
    {
        if head_complete {
            emit_missing(&mut i, LeadingTrivia::default());
        }
        return complete(handoff(item), line_entry);
    }
    if !head_complete && (!retry_after_missing_head || !body_starter(&item)) {
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    match token_kind(&item) {
        Some(TokenKind::Semicolon) => {
            emit_token_item(&mut i, item);
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        Some(TokenKind::LBrace) => braced_body_normalized(
            i,
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(TokenKind::Colon)
            if !colon_following_has_physical_newline(i.rb(), item_origin, fence) =>
        {
            description_normalized(
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
            )
        }
        _ if head_complete => recover_body_introducer_normalized(
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
        _ => complete(handoff(item), line_entry),
    }
}

#[allow(clippy::too_many_arguments)]
fn description_normalized(
    mut i: RewriteIn,
    colon: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::ImplDescription.into());
    emit_token_item(&mut i, colon);
    let (mut description, next_origin, next_entry) = impl_item_normalized(
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
    let retry_after_missing_description = description_body_starter(&description);
    let local_missing_description_gap =
        retry_after_missing_description && impl_gap_allowed(&description, baseline);
    if local_missing_description_gap
        || !description_gap_is_outer_owned(i.rb(), &description, baseline, stops)
    {
        if description.payload_view().is_eof() {
            description.emit_eof_leading(&mut *i.state);
        } else {
            description.emit_all_remaining_leading(&mut *i.state);
        }
    }
    let child_entry = suffix_marker(i.rb());
    let (exit, description_complete) =
        required_type_expr_with_caller_stops_and_outer_boundary_and_fresh_primary_policy_normalized(
            i.rb(),
            description,
            baseline,
            stops,
            TypeOuterBoundary::VARIANT_BODY,
            RequiredTypeFreshPrimaryPolicy {
                owns_bare_left_brace: true,
            },
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    item_origin = advanced_origin(item_origin, child_entry, i.rb());
    let (item, item_origin, line_entry) =
        successor_after_type_normalized(i.rb(), exit, item_origin, baseline, stops, fence);
    i.state.finish_node();
    body_from_item_normalized(
        i,
        item,
        description_complete,
        retry_after_missing_description,
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
fn body_from_item_normalized(
    mut i: RewriteIn,
    mut item: Item,
    upstream_complete: bool,
    retry_after_missing_slot: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if !impl_gap_allowed(&item, baseline)
        || (!body_starter(&item) && body_boundary(i.rb(), &item, baseline, stops))
    {
        if upstream_complete {
            emit_missing(&mut i, LeadingTrivia::default());
        }
        return complete(handoff(item), line_entry);
    }
    if !upstream_complete && (!retry_after_missing_slot || !body_starter(&item)) {
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    match token_kind(&item) {
        Some(TokenKind::Semicolon) => {
            emit_token_item(&mut i, item);
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        Some(TokenKind::LBrace) => braced_body_normalized(
            i,
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
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
            )
        }
        _ if upstream_complete => recover_body_introducer_normalized(
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
        _ => complete(handoff(item), line_entry),
    }
}

#[allow(clippy::too_many_arguments)]
fn braced_body_normalized(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
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
        NormalizedExit::Complete(Ok(()), line_entry) => {
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        exit => exit,
    }
}

#[allow(clippy::too_many_arguments)]
fn recover_body_introducer_normalized(
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
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = impl_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            false,
            false,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if item.payload_view().is_eof() {
            item.emit_eof_leading(&mut *i.state);
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if !impl_gap_allowed(&item, baseline) {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if body_starter(&item) {
            i.state.finish_node();
            return body_from_item_normalized(
                i,
                item,
                true,
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
        if body_boundary(i.rb(), &item, baseline, stops) {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        item.emit_all_remaining_leading(&mut *i.state);
    }
}

#[allow(clippy::too_many_arguments)]
fn colon_body_normalized(
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
            let (item, _, line_entry) = impl_item_normalized(
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
        None => {
            let (item, item_origin, line_entry) = impl_item_normalized(
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
            )
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn inline_body_from_item_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if inline_body_boundary(i.rb(), &item, baseline, stops) {
        if colon_body_gap_is_local(i.rb(), &item, baseline, stops) {
            if item.payload_view().is_eof() {
                item.emit_eof_leading(&mut *i.state);
            } else {
                item.emit_all_remaining_leading(&mut *i.state);
            }
        }
        emit_missing(&mut i, LeadingTrivia::default());
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
    )
}

#[allow(clippy::too_many_arguments)]
fn recover_inline_body_normalized(
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
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = impl_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            false,
            false,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if item.payload_view().is_eof() {
            item.emit_eof_leading(&mut *i.state);
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if inline_body_boundary(i.rb(), &item, baseline, stops) {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if let Some(admission) =
            classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
        {
            i.state.finish_node();
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
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn inline_statement_normalized(
    mut i: RewriteIn,
    item: Item,
    admission: StatementAdmission,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
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

fn after_completed_normalized(
    i: RewriteIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, _, line_entry) = impl_item_normalized(
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

fn colon_following_has_physical_newline(
    i: RewriteIn,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            Some(
                observe_fenced_trivia_with_newline(
                    lex.remainder(),
                    item_origin,
                    LineEntry::InLine,
                    fence,
                )
                .saw_physical_newline,
            )
        },
        |has_newline| has_newline,
    )
    .unwrap_or(false)
}

fn head_gap_is_outer_owned(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || !impl_gap_allowed(item, baseline)
        || is_type_caller_boundary(item, stops)
        || body_starter(item)
        || is_active_stop(i.rb(), item, stops)
}

fn description_gap_is_outer_owned(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
) -> bool {
    item.payload_view().is_boundary()
        || !impl_gap_allowed(item, baseline)
        || is_type_caller_boundary(item, stops)
        || description_body_starter(item)
        || is_active_stop(i.rb(), item, stops)
}

fn body_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
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

fn inline_body_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    body_boundary(i.rb(), item, baseline, stops) || token_kind(item) == Some(TokenKind::Semicolon)
}

fn colon_body_gap_is_local(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    !item.payload_view().is_boundary()
        && indentation_after_newline(item.leading_view()).is_none()
        && !is_active_stop(i.rb(), item, stops)
        && active_statement_companion(i.rb(), item, baseline, stops).is_none()
}

fn impl_gap_allowed(item: &Item, baseline: usize) -> bool {
    indentation_after_newline(item.leading_view()).is_none_or(|indentation| indentation > baseline)
}

fn body_starter(item: &Item) -> bool {
    !item.payload_view().is_boundary()
        && matches!(
            token_kind(item),
            Some(TokenKind::Semicolon | TokenKind::LBrace | TokenKind::Colon)
        )
}

fn description_body_starter(item: &Item) -> bool {
    !item.payload_view().is_boundary()
        && matches!(
            token_kind(item),
            Some(TokenKind::Semicolon | TokenKind::Colon)
        )
}

fn inline_terminal_semicolon(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Semicolon)
        && indentation_after_newline(item.leading_view()).is_none()
}

#[allow(clippy::too_many_arguments)]
fn impl_item_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
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
        .expect("Impl declaration payload scanning is total");
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
        _ => unreachable!("Impl visibility uses exact declaration words"),
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
