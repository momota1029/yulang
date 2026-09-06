//! One direct-CST `DerivesClause`, shared by the Type header and equality tail.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn, Stops,
    current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
    driver::{
        Either, NormalizedExit, advanced_origin, indentation_after_newline, is_active_stop,
        suffix_marker, token_kind,
    },
    emit::{emit_missing, emit_token_item},
    if_expr::active_statement_companion,
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{scan_identifier, scan_type_nud_payload},
    statement::StatementLineHandoff,
    type_expr::{
        TypeOuterBoundary, required_type_expr_with_caller_stops_and_outer_boundary_normalized,
    },
    yumark::FenceBoundary,
};

#[allow(clippy::too_many_arguments)]
pub(super) fn derives_clause_normalized(
    mut i: RewriteIn,
    keyword: Item,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
    role_boundary: TypeOuterBoundary,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    debug_assert!(is_word(&keyword, "derives"));
    i.state.start_node(SyntaxKind::DerivesClause.into());
    emit_contextual_keyword(&mut i, keyword, SyntaxKind::DerivesKw);

    let (mut next, mut item_origin, mut line_entry) = required_role_normalized(
        i.rb(),
        baseline,
        caller_stops,
        line_handoff,
        role_boundary,
        item_origin,
        line_entry,
        fence,
    );
    loop {
        if !clause_gap_continues(i.rb(), &next, baseline, caller_stops, line_handoff) {
            i.state.finish_node();
            return (next, item_origin, line_entry);
        }
        if token_kind(&next) == Some(TokenKind::Comma) {
            emit_token_item(&mut i, next);
            (next, item_origin, line_entry) = required_role_normalized(
                i.rb(),
                baseline,
                caller_stops,
                line_handoff,
                role_boundary,
                item_origin,
                line_entry,
                fence,
            );
            continue;
        }
        if is_word(&next, "via") {
            emit_contextual_keyword(&mut i, next, SyntaxKind::ViaKw);
            (next, item_origin, line_entry) = required_via_target_normalized(
                i.rb(),
                baseline,
                caller_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
            );
        }
        i.state.finish_node();
        return (next, item_origin, line_entry);
    }
}

#[allow(clippy::too_many_arguments)]
fn required_role_normalized(
    mut i: RewriteIn,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
    role_boundary: TypeOuterBoundary,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let (primary, item_origin, line_entry) =
        next_clause_item_normalized(i.rb(), item_origin, line_entry, fence, false);
    if !clause_gap_continues(i.rb(), &primary, baseline, caller_stops, line_handoff) {
        emit_missing_type_expression(&mut i);
        return (primary, item_origin, line_entry);
    }
    let child_entry = suffix_marker(i.rb());
    let (exit, _) = required_type_expr_with_caller_stops_and_outer_boundary_normalized(
        i.rb(),
        primary,
        baseline,
        caller_stops,
        role_boundary,
        item_origin,
        line_entry,
        fence,
    );
    let item_origin = advanced_origin(item_origin, child_entry, i.rb());
    successor_after_type_normalized(i, exit, item_origin, fence)
}

#[allow(clippy::too_many_arguments)]
fn required_via_target_normalized(
    mut i: RewriteIn,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let (mut target, next_origin, next_entry) =
        next_clause_item_normalized(i.rb(), item_origin, line_entry, fence, true);
    item_origin = next_origin;
    line_entry = next_entry;
    if !clause_gap_continues(i.rb(), &target, baseline, caller_stops, line_handoff)
        || via_target_boundary(&target)
    {
        emit_missing(&mut i, LeadingTrivia::default());
        return (target, item_origin, line_entry);
    }
    if raw_identifier(&target) {
        emit_token_item(&mut i, target);
        return next_clause_item_normalized(i, item_origin, line_entry, fence, false);
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, target);
        (target, item_origin, line_entry) =
            next_clause_item_normalized(i.rb(), item_origin, line_entry, fence, true);
        if !clause_gap_continues(i.rb(), &target, baseline, caller_stops, line_handoff)
            || via_target_boundary(&target)
            || raw_identifier(&target)
        {
            i.state.finish_node();
            if raw_identifier(&target) {
                emit_token_item(&mut i, target);
                return next_clause_item_normalized(i, item_origin, line_entry, fence, false);
            }
            return (target, item_origin, line_entry);
        }
    }
}

/// The raw Identifier slot keeps contextual clause words pending for the
/// clause or Type owner.
fn via_target_boundary(item: &Item) -> bool {
    item.payload_view().is_boundary()
        || matches!(
            token_kind(item),
            Some(
                TokenKind::Comma
                    | TokenKind::Semicolon
                    | TokenKind::Equals
                    | TokenKind::RParen
                    | TokenKind::RBracket
                    | TokenKind::RBrace
            )
        )
        || item.payload_view().is_eof()
        || matches!(item_word(item), Some("derives" | "via" | "with" | "impl"))
}

fn successor_after_type_normalized(
    i: RewriteIn,
    exit: NormalizedExit,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => {
            next_clause_item_normalized(i, item_origin, line_entry, fence, false)
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            (item, item_origin, line_entry)
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            (end.item, item_origin, line_entry)
        }
        NormalizedExit::Deferred(_, _) => {
            unreachable!("normalized TypeExpression does not defer a declaration owner")
        }
    }
}

fn next_clause_item_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    raw_identifier_first: bool,
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
                |mut lex: LexIn, leading, origin, fence, _| {
                    if raw_identifier_first && let Some(identifier) = lex.token(scan_identifier) {
                        return Some(AcceptedPayload {
                            payload: CurrentPayload::Token(identifier),
                            next_line_entry: LineEntry::InLine,
                        });
                    }
                    scan_type_nud_payload(lex, leading, origin, fence)
                },
            )
        })
        .expect("Derives payload scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

/// This is the complete direct-C15 gap decision.  It is deliberately local:
/// `StatementLineHandoff` comes from the Type owner and is never recovered
/// from state or attached to an Item.
fn clause_gap_continues(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> bool {
    if item.payload_view().is_boundary() {
        return false;
    }
    if is_active_stop(i.rb(), item, caller_stops)
        || active_statement_companion(i.rb(), item, baseline, caller_stops).is_some()
    {
        return false;
    }
    let Some(indentation) = indentation_after_newline(item.leading_view()) else {
        return true;
    };
    matches!(line_handoff, StatementLineHandoff::OrdinaryLayout) && indentation > baseline
}

fn emit_missing_type_expression(i: &mut RewriteIn) {
    i.state.start_node(SyntaxKind::TypeExpression.into());
    emit_missing(i, LeadingTrivia::default());
    i.state.finish_node();
}

fn emit_contextual_keyword(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    debug_assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    item.emit_remaining(&mut *i.state, kind);
}

fn raw_identifier(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
}

pub(super) fn is_word(item: &Item, word: &str) -> bool {
    item.payload_view().token_kind() == Some(TokenKind::Identifier)
        && item.payload_view().spelling() == Some(word)
}

fn item_word(item: &Item) -> Option<&str> {
    (item.payload_view().token_kind() == Some(TokenKind::Identifier))
        .then(|| item.payload_view().spelling())
        .flatten()
}
