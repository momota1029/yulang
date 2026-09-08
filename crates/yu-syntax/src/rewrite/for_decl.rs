//! Direct canonical `for` statement construction.

use super::ambient_claim::AmbientClaimContext;
use reborrow_generic::Reborrow as _;

use crate::{
    scan::operator::OperatorSite,
    session::{ForStatementRole, GrammarRole},
    syntax_kind::SyntaxKind,
};

use super::{
    LexIn, RewriteIn, Stops,
    current_item::{CurrentItem, LineEntry, current_item},
    driver::{
        Either, MlMode, NormalizedExit, advanced_origin, complete, expression_item, handoff,
        implicit_delimited_newline, is_active_stop, is_active_stop_lex,
        is_required_operand_boundary, is_separator, required_expr_item_normalized, suffix_marker,
        token_kind,
    },
    emit::{emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{
        introduced_body_indentation_normalized, scan_case_label_payload, scan_pattern_nud_payload,
        scan_statement_payload,
    },
    operator::{STOP_COLON, STOP_COMMA, STOP_LBRACE, STOP_SEMICOLON},
    pattern::{
        PATTERN_STOP_IN, PATTERN_STOP_LBRACE, PATTERN_STOP_PRIMARY_COLON, PatternCompletion,
        pattern_from_entry_item_with_completion_normalized, pattern_stops_from_owner,
    },
    statement::{
        StatementLineHandoff, braced_statement_block_normalized,
        indented_statement_block_normalized,
    },
    yumark::FenceBoundary,
};

pub(super) fn for_statement_selected(item: &Item) -> bool {
    item_word(item) == Some("for")
}

#[allow(clippy::too_many_arguments)]
pub(super) fn for_statement_normalized(
    mut i: RewriteIn,
    keyword: Item,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    debug_assert!(for_statement_selected(&keyword));
    i.state.start_node(SyntaxKind::ForStatement.into());
    emit_keyword(&mut i, keyword, SyntaxKind::ForKw, "for");
    (item_origin, line_entry) = emit_optional_label_normalized(
        i.rb(),
        baseline,
        outer_stops,
        item_origin,
        line_entry,
        fence,
    );
    let exit = pattern_slot_normalized(
        i.rb(),
        baseline,
        outer_stops,
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
fn emit_optional_label_normalized(
    mut i: RewriteIn,
    baseline: usize,
    outer_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (usize, LineEntry) {
    let mut accepted = false;
    let rolled_back: Option<()> = i.token(|mut probe: LexIn| {
        let (label, text) = probe.rb().with_str(|label| {
            current_item(label, item_origin, line_entry, fence, |lex, _, _, _, _| {
                scan_case_label_payload(lex)
            })
        });
        let Some(CurrentItem {
            item: label,
            next_line_entry,
        }) = label
        else {
            return None;
        };
        if label.payload_view().is_boundary()
            || label.payload_view().is_eof()
            || implicit_gap(baseline, label.leading_view())
        {
            return None;
        }
        let next_origin = item_origin
            .checked_add(text.len())
            .expect("a tentative For label coordinate must fit usize");
        let Some(CurrentItem { item: next, .. }) = current_item(
            probe.rb(),
            next_origin,
            next_line_entry,
            fence,
            |lex, leading, origin, fence, _| {
                scan_statement_payload(lex, leading, origin, fence, baseline, outer_stops)
            },
        ) else {
            return None;
        };
        accepted = !label_following_boundary(probe.rb(), &next, baseline, outer_stops)
            && item_word(&next) != Some("in");
        None
    });
    debug_assert!(rolled_back.is_none());
    if !accepted {
        return (item_origin, line_entry);
    }

    let entry = suffix_marker(i.rb());
    let CurrentItem {
        mut item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(lex, item_origin, line_entry, fence, |lex, _, _, _, _| {
                scan_case_label_payload(lex)
            })
        })
        .expect("an accepted For label must reacquire identically");
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    debug_assert!(!item.payload_view().is_boundary());
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::ForLabel.into());
    emit_token_item(&mut i, item);
    i.state.finish_node();
    (item_origin, next_line_entry)
}

#[allow(clippy::too_many_arguments)]
fn pattern_slot_normalized(
    mut i: RewriteIn,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let stops = pattern_stops_from_owner(outer_stops)
        | PATTERN_STOP_PRIMARY_COLON
        | PATTERN_STOP_LBRACE
        | PATTERN_STOP_IN;
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        mut item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(
                lex,
                item_origin,
                line_entry,
                fence,
                |lex, leading, origin, fence, _| {
                    scan_pattern_nud_payload(lex, leading, origin, fence, stops)
                },
            )
        })
        .expect("For Pattern payload scanning is total");
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    if item.payload_view().is_boundary()
        || implicit_delimited_newline(baseline, item.leading_view())
    {
        i.state.start_node(SyntaxKind::Pattern.into());
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return complete(handoff(item), next_line_entry);
    }
    let missing_at_in = item_word(&item) == Some("in");
    let missing_at_body = matches!(
        token_kind(&item),
        Some(TokenKind::Colon | TokenKind::LBrace)
    );
    item.emit_all_remaining_leading(&mut *i.state);
    let child_entry = suffix_marker(i.rb());
    let (exit, completion) = pattern_from_entry_item_with_completion_normalized(
        i.rb(),
        item,
        baseline,
        stops,
        line_handoff,
        item_origin,
        next_line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, child_entry, i.rb());
    match exit {
        NormalizedExit::Deferred(item, line_entry) => NormalizedExit::Deferred(item, line_entry),
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => match completion {
            PatternCompletion::Complete => in_slot_normalized(
                i,
                item,
                baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            ),
            PatternCompletion::Incomplete if missing_at_in => in_slot_normalized(
                i,
                item,
                baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            ),
            PatternCompletion::Incomplete if missing_at_body => body_normalized(
                i,
                item,
                baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            ),
            PatternCompletion::Incomplete => complete(handoff(item), line_entry),
        },
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            complete(Err(Either::Right(end)), line_entry)
        }
        NormalizedExit::Complete(Ok(()), _) => {
            unreachable!("a Pattern leaves its successor Item")
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn in_slot_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if item.payload_view().is_boundary()
        || implicit_delimited_newline(baseline, item.leading_view())
    {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    if item_word(&item) == Some("in") {
        emit_keyword(&mut i, item, SyntaxKind::InKw, "in");
        return iterable_normalized(
            i,
            baseline,
            outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }

    if !outer_boundary(i.rb(), &item, baseline, outer_stops)
        && !matches!(
            token_kind(&item),
            Some(TokenKind::Colon | TokenKind::LBrace)
        )
    {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    emit_missing(&mut i, LeadingTrivia::default());
    if matches!(
        token_kind(&item),
        Some(TokenKind::Colon | TokenKind::LBrace)
    ) {
        return body_normalized(
            i,
            item,
            baseline,
            outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    if outer_boundary(i.rb(), &item, baseline, outer_stops) {
        return complete(handoff(item), line_entry);
    }
    iterable_from_item_normalized(
        i,
        item,
        baseline,
        outer_stops,
        false,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn iterable_normalized(
    mut i: RewriteIn,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let (mut item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        iterable_stops(outer_stops),
    );
    let missing = implicit_delimited_newline(baseline, item.leading_view())
        || is_required_operand_boundary(i.rb(), &item, iterable_stops(outer_stops));
    if !item.payload_view().is_boundary()
        && !implicit_delimited_newline(baseline, item.leading_view())
    {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    iterable_from_item_normalized(
        i,
        item,
        baseline,
        outer_stops,
        missing,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn iterable_from_item_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    outer_stops: Stops,
    missing: bool,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if !item.payload_view().is_boundary()
        && !implicit_delimited_newline(baseline, item.leading_view())
        && !item.leading_view().is_grammar_empty()
    {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    i.state.start_node(SyntaxKind::ForIterable.into());
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let child_entry = suffix_marker(i.rb());
    let exit = if item.payload_view().is_boundary()
        || implicit_delimited_newline(baseline, item.leading_view())
    {
        super::driver::emit_required_expression_missing(
            &mut i,
            &mut item,
            item_origin,
            iterable_stops(outer_stops),
            GrammarRole::ForStatement(ForStatementRole::Iterable),
        );
        complete(handoff(item), line_entry)
    } else {
        required_expr_item_normalized(
            i.rb(),
            item,
            GrammarRole::ForStatement(ForStatementRole::Iterable),
            None,
            baseline,
            iterable_stops(outer_stops),
            MlMode::All,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        )
    };
    let item_origin = advanced_origin(item_origin, child_entry, i.rb());
    i.state.finish_node();
    i.state.finish_node();

    match exit {
        NormalizedExit::Deferred(item, line_entry) => NormalizedExit::Deferred(item, line_entry),
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if !item.payload_view().is_boundary()
                && matches!(
                    token_kind(&item),
                    Some(TokenKind::Colon | TokenKind::LBrace)
                ) =>
        {
            body_normalized(
                i,
                item,
                baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) if missing => {
            complete(handoff(item), line_entry)
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => body_normalized(
            i,
            item,
            baseline,
            outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) if missing => {
            complete(Err(Either::Right(end)), line_entry)
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            emit_missing(&mut i, LeadingTrivia::default());
            complete(Err(Either::Right(end)), line_entry)
        }
        NormalizedExit::Complete(Ok(()), _) => {
            unreachable!("an iterable leaves its successor Item")
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn body_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if item.payload_view().is_boundary()
        || implicit_delimited_newline(baseline, item.leading_view())
    {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    match token_kind(&item) {
        Some(TokenKind::Colon) => {
            emit_token_item(&mut i, item);
            colon_body_normalized(
                i,
                baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
        Some(TokenKind::LBrace) => {
            item.emit_all_remaining_leading(&mut *i.state);
            braced_statement_block_normalized(
                i,
                item,
                baseline,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
        _ if outer_boundary(i.rb(), &item, baseline, outer_stops) => {
            emit_missing(&mut i, LeadingTrivia::default());
            complete(handoff(item), line_entry)
        }
        _ => recover_body_introducer_normalized(
            i,
            item,
            baseline,
            outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn colon_body_normalized(
    mut i: RewriteIn,
    baseline: usize,
    outer_stops: Stops,
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
            GrammarRole::ForStatement(ForStatementRole::IndentedStatement),
            outer_stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(_) => {
            emit_missing(&mut i, LeadingTrivia::default());
            let (item, _, line_entry) = statement_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                outer_stops,
            );
            complete(handoff(item), line_entry)
        }
        None => inline_body_normalized(
            i,
            baseline,
            outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn inline_body_normalized(
    mut i: RewriteIn,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let stops = outer_stops | STOP_COMMA | STOP_SEMICOLON;
    let (mut item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    if !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = required_expr_item_normalized(
        i.rb(),
        item,
        GrammarRole::ForStatement(ForStatementRole::Body),
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
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn recover_body_introducer_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        debug_assert!(!item.payload_view().is_boundary());
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = statement_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            outer_stops,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if matches!(
            token_kind(&item),
            Some(TokenKind::Colon | TokenKind::LBrace)
        ) {
            i.state.finish_node();
            return body_normalized(
                i,
                item,
                baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
        if implicit_delimited_newline(baseline, item.leading_view())
            || outer_boundary(i.rb(), &item, baseline, outer_stops)
        {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
    }
}

fn statement_item_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
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
                |lex, leading, origin, fence, _| {
                    scan_statement_payload(lex, leading, origin, fence, baseline, stops)
                },
            )
        })
        .expect("For recovery Statement payload scanning is total");
    let item_origin = advanced_origin(item_origin, entry, i);
    (item, item_origin, next_line_entry)
}

fn iterable_stops(outer_stops: Stops) -> Stops {
    outer_stops | STOP_COLON | STOP_LBRACE | STOP_COMMA | STOP_SEMICOLON
}

fn iterable_boundary(mut i: RewriteIn, item: &Item, baseline: usize, outer_stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || implicit_delimited_newline(baseline, item.leading_view())
        || item.payload_view().is_eof()
        || is_active_stop(i.rb(), item, iterable_stops(outer_stops))
}

fn outer_boundary(mut i: RewriteIn, item: &Item, baseline: usize, outer_stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || implicit_delimited_newline(baseline, item.leading_view())
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_active_stop(i.rb(), item, outer_stops)
}

fn label_following_boundary(
    mut i: LexIn,
    item: &Item,
    baseline: usize,
    outer_stops: Stops,
) -> bool {
    item.payload_view().is_boundary()
        || implicit_gap(baseline, item.leading_view())
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_active_stop_lex(i.rb(), item, outer_stops)
        || matches!(token_kind(item), Some(TokenKind::Colon | TokenKind::LBrace))
}

fn implicit_gap(baseline: usize, leading: super::item::LeadingView<'_>) -> bool {
    implicit_delimited_newline(baseline, leading)
}

fn item_word(item: &Item) -> Option<&str> {
    let payload = item.payload_view();
    assert!(!payload.is_boundary(), "a boundary is not a word");
    (payload.token_kind() == Some(TokenKind::Identifier))
        .then(|| payload.spelling())
        .flatten()
}

fn emit_keyword(i: &mut RewriteIn, item: Item, kind: SyntaxKind, spelling: &str) {
    debug_assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    debug_assert_eq!(item.payload_view().spelling(), Some(spelling));
    item.emit_remaining(&mut *i.state, kind);
}
