//! One direct-CST `DerivesClause`, shared by the Type header and equality tail.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    RewriteIn, Stops,
    driver::{Either, TailExit, indentation_after_newline, is_active_stop, token_kind},
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    if_expr::active_statement_companion,
    item::{Item, LeadingTrivia, Payload, Token, TokenKind},
    lexer::{scan_trivia, type_nud_item_after_trivia},
    statement::StatementLineHandoff,
    type_expr::{TypeOuterBoundary, required_type_expr_with_caller_stops_and_outer_boundary},
};

/// Consume one already-qualified `derives` clause and return its first pending
/// successor.  The Type owner alone decides whether that successor starts a
/// repeated clause or belongs to the declaration form/outer statement.
pub(super) fn derives_clause(
    mut i: RewriteIn,
    keyword: Item,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
    role_boundary: TypeOuterBoundary,
) -> Item {
    debug_assert!(is_word(&keyword, "derives"));
    i.state.start_node(SyntaxKind::DerivesClause.into());
    emit_contextual_keyword(&mut i, keyword, SyntaxKind::DerivesKw);

    let mut next = required_role(i.rb(), baseline, caller_stops, line_handoff, role_boundary);
    loop {
        if !clause_gap_continues(i.rb(), &next, baseline, caller_stops, line_handoff) {
            i.state.finish_node();
            return next;
        }
        if token_kind(&next) == Some(TokenKind::Comma) {
            emit_token_item(&mut i, next);
            next = required_role(i.rb(), baseline, caller_stops, line_handoff, role_boundary);
            continue;
        }
        if is_word(&next, "via") {
            emit_contextual_keyword(&mut i, next, SyntaxKind::ViaKw);
            next = required_via_target(i.rb(), baseline, caller_stops, line_handoff);
        }
        i.state.finish_node();
        return next;
    }
}

fn required_role(
    mut i: RewriteIn,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
    role_boundary: TypeOuterBoundary,
) -> Item {
    let leading = scan_trivia(i.rb());
    let primary = type_nud_item_after_trivia(i.rb(), leading);
    if !clause_gap_continues(i.rb(), &primary, baseline, caller_stops, line_handoff) {
        emit_missing_type_expression(&mut i);
        return primary;
    }
    let (exit, _) = required_type_expr_with_caller_stops_and_outer_boundary(
        i.rb(),
        primary,
        baseline,
        caller_stops,
        role_boundary,
    );
    successor_after_type(i, exit)
}

fn required_via_target(
    mut i: RewriteIn,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> Item {
    let leading = scan_trivia(i.rb());
    let mut target = type_nud_item_after_trivia(i.rb(), leading);
    if !clause_gap_continues(i.rb(), &target, baseline, caller_stops, line_handoff)
        || via_target_boundary(&target)
    {
        emit_missing(&mut i, LeadingTrivia::default());
        return target;
    }
    if raw_identifier(&target) {
        emit_token_item(&mut i, target);
        return next_type_item(i);
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, target);
        target = next_type_item(i.rb());
        if !clause_gap_continues(i.rb(), &target, baseline, caller_stops, line_handoff)
            || via_target_boundary(&target)
            || raw_identifier(&target)
        {
            i.state.finish_node();
            if raw_identifier(&target) {
                emit_token_item(&mut i, target);
                return next_type_item(i);
            }
            return target;
        }
    }
}

/// The raw Identifier slot keeps contextual clause words pending for the
/// clause or Type owner.
fn via_target_boundary(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(
            TokenKind::Comma
                | TokenKind::Semicolon
                | TokenKind::Equals
                | TokenKind::RParen
                | TokenKind::RBracket
                | TokenKind::RBrace
        )
    ) || matches!(item.payload, Payload::Eof)
        || matches!(item_word(item), Some("derives" | "via" | "with" | "impl"))
}

fn successor_after_type(i: RewriteIn, exit: TailExit) -> Item {
    match exit {
        Ok(()) => next_type_item(i),
        Err(Either::Left(item)) => item,
        Err(Either::Right(end)) => end.item,
    }
}

fn next_type_item(mut i: RewriteIn) -> Item {
    let leading = scan_trivia(i.rb());
    type_nud_item_after_trivia(i, leading)
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
    if is_active_stop(i.rb(), item, caller_stops)
        || active_statement_companion(i.rb(), item, baseline, caller_stops).is_some()
    {
        return false;
    }
    let Some(indentation) = indentation_after_newline(&item.leading) else {
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
    let Payload::Token(Token {
        kind: TokenKind::Identifier,
        text,
    }) = item.payload
    else {
        unreachable!("accepted derives contextual words are raw identifiers")
    };
    emit_leading_trivia(i, &item.leading);
    i.state.token(kind.into(), &text);
}

fn raw_identifier(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
}

pub(super) fn is_word(item: &Item, word: &str) -> bool {
    matches!(
        &item.payload,
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text,
        }) if &**text == word
    )
}

fn item_word(item: &Item) -> Option<&str> {
    match &item.payload {
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text,
        }) => Some(text),
        _ => None,
    }
}
