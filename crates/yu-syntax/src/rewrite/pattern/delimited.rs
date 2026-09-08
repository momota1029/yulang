//! Direct owners for Pattern's three comma-or-layout delimited primaries.

use super::super::ambient_claim::AmbientClaimContext;
use reborrow_generic::Reborrow as _;

use crate::{
    scan::operator::OperatorSite,
    session::{
        ConstructRole, Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole, PatternRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
    },
    syntax_kind::SyntaxKind,
};
use std::sync::Arc;

use super::{
    super::{
        current_item::LineEntry,
        driver::{
            Either, MlMode, NormalizedExit, advanced_origin, complete, delimited_baseline,
            expression_item, handoff, implicit_delimited_newline, is_nud_item, suffix_marker,
            token_kind,
        },
        emit::{emit_error_item, emit_missing, emit_recovery_missing, emit_token_item},
        item::{Item, LeadingTrivia, LeadingView, TokenKind},
        operator::stops_for,
        output::RecoveryDraft,
        statement::StatementLineHandoff,
        yumark::FenceBoundary,
    },
    PATTERN_STOP_COMMA, PATTERN_STOP_EQUALS, PATTERN_STOP_RBRACE, PATTERN_STOP_RBRACKET,
    PATTERN_STOP_RPAREN, PatternCallerCloses, PatternCompletion, PatternMandatorySlotPolicy,
    PatternPrecedence, PatternStops, RewriteIn, emit_pattern_missing,
    pattern_from_item_recording_with_policy_normalized, pattern_item_normalized,
    pattern_nud_item_normalized, pattern_primary_stop_token, pattern_tail_normalized,
    scan_pattern_tail_normalized,
};

#[derive(Clone, Copy)]
enum Owner {
    Parenthesized,
    List,
    Record,
}

impl Owner {
    fn node(self) -> SyntaxKind {
        match self {
            Self::Parenthesized => SyntaxKind::ParenthesizedPattern,
            Self::List => SyntaxKind::ListPattern,
            Self::Record => SyntaxKind::RecordPattern,
        }
    }

    fn close(self) -> TokenKind {
        match self {
            Self::Parenthesized => TokenKind::RParen,
            Self::List => TokenKind::RBracket,
            Self::Record => TokenKind::RBrace,
        }
    }

    fn separator_role(self) -> PatternRole {
        match self {
            Self::Parenthesized => PatternRole::ParenthesizedSeparator,
            Self::List => PatternRole::ListSeparator,
            Self::Record => PatternRole::RecordSeparator,
        }
    }

    fn closing_owner(self) -> (ConstructRole, Delimiter) {
        match self {
            Self::Parenthesized => (ConstructRole::ParenthesizedPattern, Delimiter::Parenthesis),
            Self::List => (ConstructRole::ListPattern, Delimiter::Bracket),
            Self::Record => (ConstructRole::RecordPattern, Delimiter::Brace),
        }
    }

    fn local_stops(self, caller_closes: PatternCallerCloses) -> PatternStops {
        PATTERN_STOP_COMMA
            | match self {
                Self::Parenthesized => PATTERN_STOP_RPAREN,
                Self::List => PATTERN_STOP_RBRACKET,
                Self::Record => PATTERN_STOP_RBRACE,
            }
            | caller_closes.pattern_stops()
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn parenthesized_pattern(
    i: RewriteIn,
    open: Item,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    outer_stops: PatternStops,
    line_handoff: StatementLineHandoff,
    recovered_primary_tail_stops: PatternStops,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    pattern_delimited(
        i,
        open,
        Owner::Parenthesized,
        minimum,
        incoming_baseline,
        outer_stops,
        line_handoff,
        recovered_primary_tail_stops,
        caller_closes,
        completion,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn list_pattern(
    i: RewriteIn,
    open: Item,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    outer_stops: PatternStops,
    line_handoff: StatementLineHandoff,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    pattern_delimited(
        i,
        open,
        Owner::List,
        minimum,
        incoming_baseline,
        outer_stops,
        line_handoff,
        0,
        caller_closes,
        completion,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn record_pattern(
    i: RewriteIn,
    open: Item,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    outer_stops: PatternStops,
    line_handoff: StatementLineHandoff,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    pattern_delimited(
        i,
        open,
        Owner::Record,
        minimum,
        incoming_baseline,
        outer_stops,
        line_handoff,
        0,
        caller_closes,
        completion,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn pattern_delimited(
    mut i: RewriteIn,
    open: Item,
    owner: Owner,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    outer_stops: PatternStops,
    line_handoff: StatementLineHandoff,
    recovered_primary_tail_stops: PatternStops,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(owner.node().into());
    emit_token_item(&mut i, open);
    let local_stops = owner.local_stops(caller_closes);
    let descendant_caller_closes = caller_closes.with_close(owner.close());
    let (mut item, mut item_origin, mut line_entry) =
        pattern_nud_item_normalized(i.rb(), item_origin, line_entry, fence, local_stops);
    let baseline = delimited_baseline(incoming_baseline, item.leading_view());
    if !item.payload_view().is_boundary()
        && (token_kind(&item) == Some(owner.close())
            || !is_carried_caller_close(caller_closes, &item))
    {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    let mut expect_item = true;
    let mut contents_completion = PatternCompletion::Complete;
    let mut own_recovery_consumed_error = false;

    loop {
        if item.payload_view().is_boundary() {
            *completion = PatternCompletion::Incomplete;
            return missing_close(i, item, owner, caller_closes, item_origin, line_entry);
        }

        if expect_item {
            if token_kind(&item) == Some(owner.close()) {
                emit_token_item(&mut i, item);
                i.state.finish_node();
                return finish_delimited_pattern(
                    i,
                    minimum,
                    incoming_baseline,
                    outer_stops,
                    contents_completion,
                    own_recovery_consumed_error,
                    recovered_primary_tail_stops,
                    line_handoff,
                    caller_closes,
                    completion,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                );
            }
            if is_carried_caller_close(caller_closes, &item) {
                *completion = PatternCompletion::Incomplete;
                return missing_close(i, item, owner, caller_closes, item_origin, line_entry);
            }
            if matches!(owner, Owner::Record) && token_kind(&item) == Some(TokenKind::Comma) {
                item.emit_all_remaining_leading(&mut *i.state);
                emit_pattern_missing(&mut i, PatternRole::RecordItem, &item, item_origin);
                contents_completion = PatternCompletion::Incomplete;
                emit_token_item(&mut i, item);
                (item, item_origin, line_entry) = pattern_nud_item_normalized(
                    i.rb(),
                    item_origin,
                    line_entry,
                    fence,
                    local_stops,
                );
                continue;
            }
            if token_kind(&item).is_none() {
                *completion = PatternCompletion::Incomplete;
                return missing_close(i, item, owner, caller_closes, item_origin, line_entry);
            }
            if is_other_close(owner, &item) {
                own_recovery_consumed_error = true;
                emit_error_item(&mut i, item);
                (item, item_origin, line_entry) = pattern_nud_item_normalized(
                    i.rb(),
                    item_origin,
                    line_entry,
                    fence,
                    local_stops,
                );
                continue;
            }
            if matches!(owner, Owner::Record) && !is_item_start(owner, &item) {
                own_recovery_consumed_error = true;
                emit_error_item(&mut i, item);
                (item, item_origin, line_entry) = pattern_nud_item_normalized(
                    i.rb(),
                    item_origin,
                    line_entry,
                    fence,
                    local_stops,
                );
                continue;
            }
            let item_baseline = delimited_baseline(baseline, item.leading_view());
            item.emit_all_remaining_leading(&mut *i.state);
            let mut item_completion = PatternCompletion::Incomplete;
            let entry = suffix_marker(i.rb());
            let exit = match owner {
                Owner::Parenthesized => pattern_from_item_recording_with_policy_normalized(
                    i.rb(),
                    item,
                    PatternPrecedence::Lowest,
                    item_baseline,
                    local_stops,
                    line_handoff,
                    PatternMandatorySlotPolicy::default(),
                    descendant_caller_closes,
                    PatternRole::ParenthesizedElement,
                    &mut item_completion,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                ),
                Owner::List => list_item(
                    i.rb(),
                    item,
                    item_baseline,
                    local_stops,
                    line_handoff,
                    descendant_caller_closes,
                    &mut item_completion,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                ),
                Owner::Record => record_item(
                    i.rb(),
                    item,
                    item_baseline,
                    local_stops,
                    line_handoff,
                    descendant_caller_closes,
                    &mut item_completion,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                ),
            };
            item_origin = advanced_origin(item_origin, entry, i.rb());
            merge_completion(&mut contents_completion, item_completion);
            match exit {
                NormalizedExit::Complete(Ok(()), next_line_entry) => {
                    (item, item_origin, line_entry) = pattern_nud_item_normalized(
                        i.rb(),
                        item_origin,
                        next_line_entry,
                        fence,
                        local_stops,
                    );
                }
                NormalizedExit::Complete(Err(Either::Left(next)), next_line_entry) => {
                    item = next;
                    line_entry = next_line_entry;
                }
                NormalizedExit::Complete(Err(Either::Right(end)), next_line_entry) => {
                    *completion = PatternCompletion::Incomplete;
                    return missing_close(
                        i,
                        end.item,
                        owner,
                        caller_closes,
                        item_origin,
                        next_line_entry,
                    );
                }
                deferred @ NormalizedExit::Deferred(_, _) => {
                    i.state.finish_node();
                    return deferred;
                }
            }
            expect_item = false;
            continue;
        }

        if token_kind(&item) == Some(owner.close()) {
            emit_token_item(&mut i, item);
            i.state.finish_node();
            return finish_delimited_pattern(
                i,
                minimum,
                incoming_baseline,
                outer_stops,
                contents_completion,
                own_recovery_consumed_error,
                recovered_primary_tail_stops,
                line_handoff,
                caller_closes,
                completion,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
        if is_carried_caller_close(caller_closes, &item) {
            *completion = PatternCompletion::Incomplete;
            return missing_close(i, item, owner, caller_closes, item_origin, line_entry);
        }
        if token_kind(&item) == Some(TokenKind::Comma) {
            emit_token_item(&mut i, item);
            (item, item_origin, line_entry) =
                pattern_nud_item_normalized(i.rb(), item_origin, line_entry, fence, local_stops);
            expect_item = true;
            continue;
        }
        if token_kind(&item).is_none() {
            *completion = PatternCompletion::Incomplete;
            return missing_close(i, item, owner, caller_closes, item_origin, line_entry);
        }
        if is_other_close(owner, &item) {
            own_recovery_consumed_error = true;
            emit_error_item(&mut i, item);
            (item, item_origin, line_entry) =
                pattern_nud_item_normalized(i.rb(), item_origin, line_entry, fence, local_stops);
            continue;
        }
        if is_item_start(owner, &item) {
            let separated_by_layout = implicit_delimited_newline(baseline, item.leading_view());
            item.emit_all_remaining_leading(&mut *i.state);
            if !separated_by_layout {
                emit_pattern_missing(&mut i, owner.separator_role(), &item, item_origin);
            }
            expect_item = true;
            continue;
        }
        own_recovery_consumed_error = true;
        emit_error_item(&mut i, item);
        (item, item_origin, line_entry) =
            pattern_nud_item_normalized(i.rb(), item_origin, line_entry, fence, local_stops);
        if matches!(owner, Owner::Record) {
            expect_item = true;
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn finish_delimited_pattern(
    i: RewriteIn,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    outer_stops: PatternStops,
    contents_completion: PatternCompletion,
    own_recovery_consumed_error: bool,
    recovered_primary_tail_stops: PatternStops,
    line_handoff: StatementLineHandoff,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let mut tail_completion = PatternCompletion::Complete;
    let exit = if own_recovery_consumed_error && recovered_primary_tail_stops != 0 {
        let mut i = i;
        let (item, item_origin, line_entry) =
            pattern_item_normalized(i.rb(), item_origin, line_entry, fence, outer_stops);
        if token_kind(&item)
            .is_some_and(|kind| pattern_primary_stop_token(kind, recovered_primary_tail_stops))
        {
            complete(handoff(item), line_entry)
        } else {
            pattern_tail_normalized(
                i,
                item,
                minimum,
                incoming_baseline,
                outer_stops,
                line_handoff,
                caller_closes,
                &mut tail_completion,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
    } else {
        scan_pattern_tail_normalized(
            i,
            minimum,
            incoming_baseline,
            outer_stops,
            line_handoff,
            caller_closes,
            &mut tail_completion,
            item_origin,
            line_entry,
            fence,
            ambient,
        )
    };
    *completion = contents_completion;
    merge_completion(completion, tail_completion);
    exit
}

fn merge_completion(completion: &mut PatternCompletion, nested: PatternCompletion) {
    if nested == PatternCompletion::Incomplete {
        *completion = PatternCompletion::Incomplete;
    }
}

#[allow(clippy::too_many_arguments)]
fn list_item(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    local_stops: PatternStops,
    line_handoff: StatementLineHandoff,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if token_kind(&item) != Some(TokenKind::DotDot) {
        return pattern_from_item_recording_with_policy_normalized(
            i,
            item,
            PatternPrecedence::Lowest,
            baseline,
            local_stops,
            line_handoff,
            PatternMandatorySlotPolicy::default(),
            caller_closes,
            PatternRole::ListItem,
            completion,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    i.state.start_node(SyntaxKind::ListPatternSpreadItem.into());
    emit_token_item(&mut i, item);
    let (mut rhs, item_origin, line_entry) =
        pattern_nud_item_normalized(i.rb(), item_origin, line_entry, fence, local_stops);
    let rhs_baseline = delimited_baseline(baseline, rhs.leading_view());
    if !rhs.payload_view().is_boundary() && !is_carried_caller_close(caller_closes, &rhs) {
        rhs.emit_all_remaining_leading(&mut *i.state);
    }
    let exit = pattern_from_item_recording_with_policy_normalized(
        i.rb(),
        rhs,
        PatternPrecedence::Lowest,
        rhs_baseline,
        local_stops,
        line_handoff,
        PatternMandatorySlotPolicy::default(),
        caller_closes,
        PatternRole::ListSpreadRhs,
        completion,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn record_item(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    local_stops: PatternStops,
    line_handoff: StatementLineHandoff,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if token_kind(&item) == Some(TokenKind::DotDot) {
        i.state
            .start_node(SyntaxKind::RecordPatternSpreadItem.into());
        emit_token_item(&mut i, item);
        let (mut rhs, item_origin, line_entry) =
            pattern_nud_item_normalized(i.rb(), item_origin, line_entry, fence, local_stops);
        let rhs_baseline = delimited_baseline(baseline, rhs.leading_view());
        if !rhs.payload_view().is_boundary() && !is_carried_caller_close(caller_closes, &rhs) {
            rhs.emit_all_remaining_leading(&mut *i.state);
        }
        let exit = pattern_from_item_recording_with_policy_normalized(
            i.rb(),
            rhs,
            PatternPrecedence::Lowest,
            rhs_baseline,
            local_stops,
            line_handoff,
            PatternMandatorySlotPolicy::default(),
            caller_closes,
            PatternRole::RecordSpreadRhs,
            completion,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        i.state.finish_node();
        return exit;
    }
    // The sequence admits only a name or DotDot; the spread branch returned.
    debug_assert!(is_pattern_name(&item));

    *completion = PatternCompletion::Complete;
    i.state.start_node(SyntaxKind::RecordPatternField.into());
    emit_token_item(&mut i, item);
    let record_stops = local_stops | PATTERN_STOP_EQUALS;
    let (item, mut item_origin, line_entry) =
        pattern_item_normalized(i.rb(), item_origin, line_entry, fence, record_stops);
    let exit = if !item.payload_view().is_boundary()
        && !has_newline(item.leading_view())
        && token_kind(&item) == Some(TokenKind::Colon)
    {
        emit_token_item(&mut i, item);
        let (mut nested, nested_origin, nested_line_entry) =
            pattern_nud_item_normalized(i.rb(), item_origin, line_entry, fence, record_stops);
        let nested_baseline = delimited_baseline(baseline, nested.leading_view());
        if !nested.payload_view().is_boundary() && !is_carried_caller_close(caller_closes, &nested)
        {
            nested.emit_all_remaining_leading(&mut *i.state);
        }
        let entry = suffix_marker(i.rb());
        let exit = pattern_from_item_recording_with_policy_normalized(
            i.rb(),
            nested,
            PatternPrecedence::Lowest,
            nested_baseline,
            record_stops,
            line_handoff,
            PatternMandatorySlotPolicy::default(),
            caller_closes,
            PatternRole::RecordNestedPattern,
            completion,
            nested_origin,
            nested_line_entry,
            fence,
            ambient,
        );
        item_origin = advanced_origin(nested_origin, entry, i.rb());
        record_default_after_pattern(
            i.rb(),
            exit,
            baseline,
            record_stops,
            line_handoff,
            item_origin,
            fence,
            ambient,
        )
    } else if !item.payload_view().is_boundary()
        && !has_newline(item.leading_view())
        && token_kind(&item) == Some(TokenKind::Equals)
    {
        record_default_after_equals(
            i.rb(),
            item,
            baseline,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        )
    } else {
        complete(handoff(item), line_entry)
    };
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn record_default_after_pattern(
    mut i: RewriteIn,
    exit: NormalizedExit,
    baseline: usize,
    record_stops: PatternStops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let (item, item_origin, line_entry) = match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => {
            pattern_nud_item_normalized(i.rb(), item_origin, line_entry, fence, record_stops)
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            (item, item_origin, line_entry)
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            return complete(Err(Either::Right(end)), line_entry);
        }
        deferred @ NormalizedExit::Deferred(_, _) => return deferred,
    };
    if !item.payload_view().is_boundary()
        && !has_newline(item.leading_view())
        && token_kind(&item) == Some(TokenKind::Equals)
    {
        record_default_after_equals(
            i,
            item,
            baseline,
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
fn record_default_after_equals(
    mut i: RewriteIn,
    equals: Item,
    baseline: usize,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    emit_token_item(&mut i, equals);
    let expression_stops = stops_for(TokenKind::RBrace);
    let (mut rhs, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        expression_stops,
    );
    if rhs.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(rhs), line_entry);
    }
    if is_nud_item(&rhs) {
        let rhs_baseline = delimited_baseline(baseline, rhs.leading_view());
        rhs.emit_all_remaining_leading(&mut *i.state);
        return super::super::driver::expr_from_nud_normalized(
            i,
            rhs,
            None,
            rhs_baseline,
            expression_stops,
            MlMode::All,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    rhs.emit_all_remaining_leading(&mut *i.state);
    emit_missing(&mut i, LeadingTrivia::default());
    complete(handoff(rhs), line_entry)
}

fn missing_close(
    mut i: RewriteIn,
    mut item: Item,
    owner: Owner,
    caller_closes: PatternCallerCloses,
    item_origin: usize,
    line_entry: LineEntry,
) -> NormalizedExit {
    if !item.payload_view().is_boundary() && !is_carried_caller_close(caller_closes, &item) {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(item_origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    let (owner, delimiter) = owner.closing_owner();
    let role = GrammarRole::ClosingDelimiter { owner, delimiter };
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
                expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter)),
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    i.state.finish_node();
    complete(handoff(item), line_entry)
}

fn is_carried_caller_close(caller_closes: PatternCallerCloses, item: &Item) -> bool {
    token_kind(item).is_some_and(|kind| caller_closes.contains(kind))
}

fn is_item_start(owner: Owner, item: &Item) -> bool {
    match owner {
        Owner::Parenthesized => can_start_pattern(item),
        Owner::List => token_kind(item) == Some(TokenKind::DotDot) || can_start_pattern(item),
        Owner::Record => token_kind(item) == Some(TokenKind::DotDot) || is_pattern_name(item),
    }
}

fn can_start_pattern(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(
            TokenKind::Identifier
                | TokenKind::SigilIdentifier
                | TokenKind::Integer
                | TokenKind::Colon
                | TokenKind::PatternSymbolColon
                | TokenKind::LParen
                | TokenKind::LBracket
                | TokenKind::LBrace
        )
    )
}

fn is_pattern_name(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier)
    )
}

fn is_other_close(owner: Owner, item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
    ) && token_kind(item) != Some(owner.close())
}

fn has_newline(leading: LeadingView<'_>) -> bool {
    leading.has_ordinary_newline()
}
