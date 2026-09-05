//! Source-free direct Pattern construction.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

mod delimited;

use super::{
    RewriteIn, Stops,
    driver::{
        Either, TailExit, delimited_baseline, handoff, implicit_delimited_newline, token_kind,
    },
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, Token, TokenKind},
    lexer::{
        pattern_item_after_trivia, pattern_nud_item_after_trivia, scan_identifier, scan_trivia,
        type_item_after_trivia, type_nud_item_after_trivia,
    },
    operator::STOP_IN,
    statement::StatementLineHandoff,
    type_expr::required_type_expr,
};

use self::delimited::{list_pattern, parenthesized_pattern, record_pattern};

/// Caller-owned Pattern boundaries. This is a passed capability, never a
/// parser state: nested Pattern delimiters replace it with their own local
/// close/comma mask.
pub(super) type PatternStops = u16;

pub(super) const PATTERN_STOP_COLON: PatternStops = 1 << 0;
pub(super) const PATTERN_STOP_ARROW: PatternStops = 1 << 1;
pub(super) const PATTERN_STOP_ARM_GUARD_IF: PatternStops = 1 << 2;
pub(super) const PATTERN_STOP_ARM_GUARD_WHERE: PatternStops = 1 << 3;
pub(super) const PATTERN_STOP_COMMA: PatternStops = 1 << 4;
pub(super) const PATTERN_STOP_SEMICOLON: PatternStops = 1 << 5;
pub(super) const PATTERN_STOP_RPAREN: PatternStops = 1 << 6;
pub(super) const PATTERN_STOP_RBRACKET: PatternStops = 1 << 7;
pub(super) const PATTERN_STOP_RBRACE: PatternStops = 1 << 8;
pub(super) const PATTERN_STOP_EQUALS: PatternStops = 1 << 9;
/// An arm owner may preserve a comma only while recovering a missing or
/// malformed first Pattern. It is deliberately not a completed-Pattern tail
/// boundary, so it cannot change ordinary case-arm grammar.
pub(super) const PATTERN_STOP_ARM_RECOVERY_SEPARATOR: PatternStops = 1 << 10;
pub(super) const PATTERN_STOP_IN: PatternStops = 1 << 11;
pub(super) const PATTERN_STOP_LBRACE: PatternStops = 1 << 12;
pub(super) const PATTERN_STOP_PRIMARY_COLON: PatternStops = 1 << 13;

pub(super) const PATTERN_DEFAULT_STOPS: PatternStops = PATTERN_STOP_COMMA
    | PATTERN_STOP_SEMICOLON
    | PATTERN_STOP_RPAREN
    | PATTERN_STOP_RBRACKET
    | PATTERN_STOP_RBRACE
    | PATTERN_STOP_EQUALS;

pub(super) fn pattern_stops_from_owner(stops: Stops) -> PatternStops {
    [
        (TokenKind::Colon, PATTERN_STOP_COLON),
        (TokenKind::Comma, PATTERN_STOP_COMMA),
        (TokenKind::Semicolon, PATTERN_STOP_SEMICOLON),
        (TokenKind::RParen, PATTERN_STOP_RPAREN),
        (TokenKind::RBracket, PATTERN_STOP_RBRACKET),
        (TokenKind::RBrace, PATTERN_STOP_RBRACE),
        (TokenKind::Arrow, PATTERN_STOP_ARROW),
    ]
    .into_iter()
    .filter_map(|(kind, stop)| super::operator::active_stop_item(kind, stops).then_some(stop))
    .fold(0, |stops, stop| stops | stop)
}

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum PatternPrecedence {
    Lowest,
    TypeAnnotation,
    Alternation,
    Alias,
}

pub(super) fn pattern(i: RewriteIn) -> TailExit {
    pattern_with_stops(i, PATTERN_DEFAULT_STOPS)
}

pub(super) fn pattern_with_stops(mut i: RewriteIn, stops: PatternStops) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = pattern_nud_item_after_trivia(i.rb(), leading, stops);
    pattern_from_item(
        i,
        item,
        PatternPrecedence::Lowest,
        0,
        stops,
        StatementLineHandoff::OrdinaryLayout,
    )
}

fn pattern_from_item(
    i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    pattern_from_item_with_completion(i, item, minimum, baseline, stops, line_handoff).exit
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum PatternCompletion {
    Complete,
    Incomplete,
}

pub(super) struct PatternOutcome {
    pub(super) exit: TailExit,
    pub(super) completion: PatternCompletion,
}

fn pattern_from_item_with_completion(
    i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
) -> PatternOutcome {
    let mut completion = PatternCompletion::Incomplete;
    let exit = pattern_from_item_recording(
        i,
        item,
        minimum,
        baseline,
        stops,
        line_handoff,
        &mut completion,
    );
    PatternOutcome { exit, completion }
}

fn pattern_from_item_recording(
    mut i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    let baseline = delimited_baseline(baseline, &item.leading);
    i.state.start_node(SyntaxKind::Pattern.into());
    let exit = pattern_from_item_core(
        i.rb(),
        item,
        minimum,
        baseline,
        stops,
        line_handoff,
        completion,
    );
    i.state.finish_node();
    exit
}

fn pattern_from_item_core(
    i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    if is_pattern_nud(&item, stops) {
        *completion = PatternCompletion::Complete;
        pattern_from_primary(i, item, minimum, baseline, stops, line_handoff, completion)
    } else {
        recover_pattern_primary(i, item, minimum, baseline, stops, line_handoff, completion)
    }
}

pub(super) fn pattern_from_entry_item(
    i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    pattern_from_item(
        i,
        item,
        PatternPrecedence::Lowest,
        baseline,
        stops,
        line_handoff,
    )
}

pub(super) fn pattern_from_entry_item_with_completion(
    i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
) -> PatternOutcome {
    pattern_from_item_with_completion(
        i,
        item,
        PatternPrecedence::Lowest,
        baseline,
        stops,
        line_handoff,
    )
}

fn recover_pattern_primary(
    mut i: RewriteIn,
    mut item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    *completion = PatternCompletion::Incomplete;
    if is_pattern_primary_boundary(&item, baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(item);
    }
    if is_current_pattern_tail(&item, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return pattern_tail(i, item, minimum, baseline, stops, line_handoff, completion);
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = pattern_nud_item_after_trivia(i.rb(), leading, stops);
        if is_pattern_primary_boundary(&item, baseline, stops) {
            i.state.finish_node();
            return handoff(item);
        }
        if is_current_pattern_tail(&item, stops) {
            i.state.finish_node();
            return pattern_tail(i, item, minimum, baseline, stops, line_handoff, completion);
        }
        if is_pattern_nud(&item, stops) {
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            i.state.finish_node();
            *completion = PatternCompletion::Complete;
            return pattern_from_primary(
                i,
                item,
                minimum,
                baseline,
                stops,
                line_handoff,
                completion,
            );
        }
    }
}

fn pattern_from_primary(
    mut i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    match token_kind(&item) {
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier) => {
            i.state.start_node(SyntaxKind::IdentifierPattern.into());
            emit_token_item(&mut i, item);
            i.state.finish_node();
            scan_pattern_tail(i, minimum, baseline, stops, line_handoff, completion)
        }
        Some(TokenKind::Integer) => {
            i.state.start_node(SyntaxKind::IntegerPattern.into());
            emit_token_item(&mut i, item);
            i.state.finish_node();
            scan_pattern_tail(i, minimum, baseline, stops, line_handoff, completion)
        }
        Some(TokenKind::Colon | TokenKind::PatternSymbolColon) => {
            i.state.start_node(SyntaxKind::SymbolPattern.into());
            emit_token_item(&mut i, item);
            if let Some(name) = i.token(scan_identifier) {
                emit_token_item(
                    &mut i,
                    Item::plain(LeadingTrivia::default(), Payload::Token(name)),
                );
            } else {
                emit_missing(&mut i, LeadingTrivia::default());
                *completion = PatternCompletion::Incomplete;
            }
            i.state.finish_node();
            scan_pattern_tail(i, minimum, baseline, stops, line_handoff, completion)
        }
        Some(TokenKind::LParen) => {
            parenthesized_pattern(i, item, minimum, baseline, stops, line_handoff, completion)
        }
        Some(TokenKind::LBracket) => {
            list_pattern(i, item, minimum, baseline, stops, line_handoff, completion)
        }
        Some(TokenKind::LBrace) => {
            record_pattern(i, item, minimum, baseline, stops, line_handoff, completion)
        }
        _ => unreachable!("the Pattern NUD judge accepted only Pattern primaries"),
    }
}

fn scan_pattern_tail(
    mut i: RewriteIn,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = pattern_item_after_trivia(i.rb(), leading, stops);
    pattern_tail(i, item, minimum, baseline, stops, line_handoff, completion)
}

fn pattern_tail(
    mut i: RewriteIn,
    mut item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    if implicit_delimited_newline(baseline, &item.leading) {
        return handoff(item);
    }
    if is_pattern_tail_boundary(i.rb(), &item, stops) {
        return handoff(item);
    }
    if is_pattern_alias(&item) && minimum <= PatternPrecedence::Alias {
        *completion = PatternCompletion::Incomplete;
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        i.state.start_node(SyntaxKind::PatternAliasTail.into());
        emit_pattern_alias_keyword(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = pattern_item_after_trivia(i.rb(), leading, stops);
        if token_kind(&item) == Some(TokenKind::Identifier) && !is_pattern_word_stop(&item, stops) {
            emit_token_item(&mut i, item);
            *completion = PatternCompletion::Complete;
            item = scan_pattern_successor(i.rb(), stops);
        } else {
            item = recover_pattern_alias_binding(i.rb(), item, baseline, stops, completion);
        }
        i.state.finish_node();
        return pattern_tail(i, item, minimum, baseline, stops, line_handoff, completion);
    }
    if token_kind(&item) == Some(TokenKind::Pipe) && minimum <= PatternPrecedence::Alternation {
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        i.state
            .start_node(SyntaxKind::PatternAlternationTail.into());
        emit_token_item(&mut i, item);
        *completion = PatternCompletion::Incomplete;
        let leading = scan_trivia(i.rb());
        let mut rhs = pattern_nud_item_after_trivia(i.rb(), leading, stops);
        let rhs_baseline = delimited_baseline(baseline, &rhs.leading);
        let leading = std::mem::take(&mut rhs.leading);
        emit_leading_trivia(&mut i, &leading);
        let exit = pattern_from_item_recording(
            i.rb(),
            rhs,
            PatternPrecedence::Alternation,
            rhs_baseline,
            stops,
            line_handoff,
            completion,
        );
        i.state.finish_node();
        return continue_pattern_tail(i, exit, minimum, baseline, stops, line_handoff, completion);
    }
    if token_kind(&item) == Some(TokenKind::Colon)
        && stops & PATTERN_STOP_COLON == 0
        && minimum <= PatternPrecedence::TypeAnnotation
    {
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        i.state.start_node(SyntaxKind::PatternTypeAnnotation.into());
        emit_token_item(&mut i, item);
        *completion = PatternCompletion::Incomplete;
        let exit = pattern_type_annotation_rhs(i.rb(), baseline, stops, completion);
        i.state.finish_node();
        return exit;
    }
    handoff(item)
}

fn recover_pattern_alias_binding(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: PatternStops,
    completion: &mut PatternCompletion,
) -> Item {
    if is_pattern_primary_boundary(&item, baseline, stops) || is_current_pattern_tail(&item, stops)
    {
        emit_missing(&mut i, LeadingTrivia::default());
        return item;
    }

    let leading = std::mem::take(&mut item.leading);
    emit_leading_trivia(&mut i, &leading);
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = pattern_item_after_trivia(i.rb(), leading, stops);
        if token_kind(&item) == Some(TokenKind::Identifier) && !is_pattern_word_stop(&item, stops) {
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            i.state.finish_node();
            emit_token_item(&mut i, item);
            *completion = PatternCompletion::Complete;
            return scan_pattern_successor(i, stops);
        }
        if is_pattern_primary_boundary(&item, baseline, stops)
            || is_current_pattern_tail(&item, stops)
        {
            i.state.finish_node();
            return item;
        }
    }
}

fn scan_pattern_successor(mut i: RewriteIn, stops: PatternStops) -> Item {
    let leading = scan_trivia(i.rb());
    pattern_item_after_trivia(i, leading, stops)
}

fn continue_pattern_tail(
    i: RewriteIn,
    exit: TailExit,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    match exit {
        Ok(()) => scan_pattern_tail(i, minimum, baseline, stops, line_handoff, completion),
        Err(Either::Left(item)) => {
            pattern_tail(i, item, minimum, baseline, stops, line_handoff, completion)
        }
        Err(Either::Right(end)) => Err(Either::Right(end)),
    }
}

fn pattern_type_annotation_rhs(
    mut i: RewriteIn,
    baseline: usize,
    stops: PatternStops,
    completion: &mut PatternCompletion,
) -> TailExit {
    let Some(leading) = i.token(|lex| {
        let leading = scan_trivia(lex);
        (!implicit_delimited_newline(baseline, &leading)).then_some(leading)
    }) else {
        i.state.start_node(SyntaxKind::TypeExpression.into());
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        let leading = scan_trivia(i.rb());
        return handoff(type_item_after_trivia(i.rb(), leading));
    };
    emit_leading_trivia(&mut i, &leading);
    let primary = type_nud_item_after_trivia(i.rb(), LeadingTrivia::default());
    if stops & PATTERN_STOP_IN != 0 {
        let (exit, primary_found) =
            super::type_expr::required_type_expr_with_caller_stops_and_completion(
                i, primary, baseline, STOP_IN,
            );
        if primary_found {
            *completion = PatternCompletion::Complete;
        }
        exit
    } else {
        *completion = PatternCompletion::Complete;
        required_type_expr(i, primary, baseline)
    }
}

fn is_pattern_primary(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(
            TokenKind::Identifier
                | TokenKind::SigilIdentifier
                | TokenKind::Integer
                | TokenKind::LParen
                | TokenKind::LBracket
                | TokenKind::LBrace
        )
    )
}

pub(super) fn is_pattern_nud(item: &Item, stops: PatternStops) -> bool {
    (!is_pattern_word_stop(item, stops)
        && is_pattern_primary(item)
        && !(stops & PATTERN_STOP_LBRACE != 0 && token_kind(item) == Some(TokenKind::LBrace)))
        || token_kind(item) == Some(TokenKind::PatternSymbolColon)
        || (token_kind(item) == Some(TokenKind::Colon)
            && stops & (PATTERN_STOP_COLON | PATTERN_STOP_PRIMARY_COLON) == 0)
}

fn is_pattern_primary_boundary(item: &Item, baseline: usize, stops: PatternStops) -> bool {
    implicit_delimited_newline(baseline, &item.leading)
        || matches!(item.payload, Payload::Eof)
        || is_pattern_word_stop(item, stops)
        || token_kind(item).is_some_and(|kind| pattern_primary_stop_token(kind, stops))
}

fn is_pattern_tail_boundary(mut i: RewriteIn, item: &Item, stops: PatternStops) -> bool {
    token_kind(item).is_some_and(|kind| pattern_tail_stop_token(kind, stops))
        || (stops & PATTERN_STOP_ARM_GUARD_IF != 0
            && super::driver::is_contextual_word(i.rb(), item, "if"))
        || (stops & PATTERN_STOP_ARM_GUARD_WHERE != 0
            && super::driver::is_contextual_word(i, item, "where"))
        || is_pattern_word_stop(item, stops)
}

fn is_pattern_word_stop(item: &Item, stops: PatternStops) -> bool {
    matches!(
        &item.payload,
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text,
        }) if stops & PATTERN_STOP_IN != 0 && &**text == "in"
    )
}

fn pattern_primary_stop_token(kind: TokenKind, stops: PatternStops) -> bool {
    match kind {
        TokenKind::Colon => stops & (PATTERN_STOP_COLON | PATTERN_STOP_PRIMARY_COLON) != 0,
        TokenKind::Arrow => stops & PATTERN_STOP_ARROW != 0,
        TokenKind::Comma => stops & (PATTERN_STOP_COMMA | PATTERN_STOP_ARM_RECOVERY_SEPARATOR) != 0,
        TokenKind::Semicolon => stops & PATTERN_STOP_SEMICOLON != 0,
        TokenKind::RParen => stops & PATTERN_STOP_RPAREN != 0,
        TokenKind::RBracket => stops & PATTERN_STOP_RBRACKET != 0,
        TokenKind::RBrace => stops & PATTERN_STOP_RBRACE != 0,
        TokenKind::Equals => stops & PATTERN_STOP_EQUALS != 0,
        TokenKind::LBrace => stops & PATTERN_STOP_LBRACE != 0,
        _ => false,
    }
}

fn pattern_tail_stop_token(kind: TokenKind, stops: PatternStops) -> bool {
    match kind {
        TokenKind::Colon => stops & PATTERN_STOP_COLON != 0,
        TokenKind::Comma => stops & PATTERN_STOP_COMMA != 0,
        _ => pattern_primary_stop_token(kind, stops),
    }
}

fn is_current_pattern_tail(item: &Item, stops: PatternStops) -> bool {
    is_pattern_alias(item)
        || token_kind(item) == Some(TokenKind::Pipe)
        || (stops & PATTERN_STOP_COLON == 0 && token_kind(item) == Some(TokenKind::Colon))
}

fn is_pattern_alias(item: &Item) -> bool {
    matches!(
        &item.payload,
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text,
        }) if &**text == "as"
    )
}

fn emit_pattern_alias_keyword(i: &mut RewriteIn, item: Item) {
    let Payload::Token(Token {
        kind: TokenKind::Identifier,
        text,
    }) = item.payload
    else {
        unreachable!("the Pattern alias judge accepted only `as`");
    };
    debug_assert_eq!(&*text, "as");
    i.state.token(SyntaxKind::AsKw.into(), &text);
}
