//! Direct owners for Pattern's three comma-or-layout delimited primaries.

use reborrow_generic::Reborrow as _;

use crate::{scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    super::{
        driver::{
            Either, MlMode, TailExit, delimited_baseline, handoff, implicit_delimited_newline,
            is_nud_item, token_kind,
        },
        emit::{emit_error_item, emit_leading_trivia, emit_missing, emit_token_item},
        item::{Item, LeadingTrivia, LeadingView, TokenKind},
        lexer::{
            pattern_item_after_trivia, pattern_nud_item_after_trivia, scan_trivia,
            tail_item_after_trivia,
        },
    },
    super::{operator::stops_for, statement::StatementLineHandoff},
    PATTERN_STOP_COMMA, PATTERN_STOP_EQUALS, PATTERN_STOP_RBRACE, PATTERN_STOP_RBRACKET,
    PATTERN_STOP_RPAREN, PatternCompletion, PatternPrecedence, PatternStops, RewriteIn,
    pattern_from_item_recording, scan_pattern_tail,
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

    fn local_stops(self) -> PatternStops {
        PATTERN_STOP_COMMA
            | match self {
                Self::Parenthesized => PATTERN_STOP_RPAREN,
                Self::List => PATTERN_STOP_RBRACKET,
                Self::Record => PATTERN_STOP_RBRACE,
            }
    }
}

pub(super) fn parenthesized_pattern(
    i: RewriteIn,
    open: Item,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    outer_stops: PatternStops,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    pattern_delimited(
        i,
        open,
        Owner::Parenthesized,
        minimum,
        incoming_baseline,
        outer_stops,
        line_handoff,
        completion,
    )
}

pub(super) fn list_pattern(
    i: RewriteIn,
    open: Item,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    outer_stops: PatternStops,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    pattern_delimited(
        i,
        open,
        Owner::List,
        minimum,
        incoming_baseline,
        outer_stops,
        line_handoff,
        completion,
    )
}

pub(super) fn record_pattern(
    i: RewriteIn,
    open: Item,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    outer_stops: PatternStops,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    pattern_delimited(
        i,
        open,
        Owner::Record,
        minimum,
        incoming_baseline,
        outer_stops,
        line_handoff,
        completion,
    )
}

fn pattern_delimited(
    mut i: RewriteIn,
    open: Item,
    owner: Owner,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    outer_stops: PatternStops,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    i.state.start_node(owner.node().into());
    emit_token_item(&mut i, open);
    let opening = scan_trivia(i.rb());
    let baseline = delimited_baseline(incoming_baseline, opening.view());
    emit_leading_trivia(&mut i, &opening);
    let local_stops = owner.local_stops();
    let mut item = pattern_nud_item_after_trivia(i.rb(), LeadingTrivia::default(), local_stops);
    let mut expect_item = true;
    let mut contents_completion = PatternCompletion::Complete;

    loop {
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
                    line_handoff,
                    completion,
                );
            }
            if matches!(owner, Owner::Record) && token_kind(&item) == Some(TokenKind::Comma) {
                item.emit_all_remaining_leading(&mut *i.state);
                emit_missing(&mut i, LeadingTrivia::default());
                contents_completion = PatternCompletion::Incomplete;
                emit_token_item(&mut i, item);
                item = scan_pattern_nud_successor(i.rb(), local_stops);
                continue;
            }
            if token_kind(&item).is_none() {
                *completion = PatternCompletion::Incomplete;
                return missing_close(i, item);
            }
            if is_other_close(owner, &item) {
                emit_error_item(&mut i, item);
                item = scan_pattern_nud_successor(i.rb(), local_stops);
                continue;
            }
            if matches!(owner, Owner::Record) && !is_item_start(owner, &item) {
                emit_error_item(&mut i, item);
                item = scan_pattern_nud_successor(i.rb(), local_stops);
                continue;
            }
            let item_baseline = delimited_baseline(baseline, item.leading_view());
            item.emit_all_remaining_leading(&mut *i.state);
            let mut item_completion = PatternCompletion::Incomplete;
            let exit = match owner {
                Owner::Parenthesized => pattern_from_item_recording(
                    i.rb(),
                    item,
                    PatternPrecedence::Lowest,
                    item_baseline,
                    local_stops,
                    line_handoff,
                    &mut item_completion,
                ),
                Owner::List => list_item(
                    i.rb(),
                    item,
                    item_baseline,
                    line_handoff,
                    &mut item_completion,
                ),
                Owner::Record => record_item(
                    i.rb(),
                    item,
                    item_baseline,
                    line_handoff,
                    &mut item_completion,
                ),
            };
            merge_completion(&mut contents_completion, item_completion);
            item = match exit {
                Ok(()) => scan_pattern_nud_successor(i.rb(), local_stops),
                Err(Either::Left(next)) => next,
                Err(Either::Right(end)) => {
                    *completion = PatternCompletion::Incomplete;
                    return missing_close(i, end.item);
                }
            };
            expect_item = false;
            continue;
        }

        if token_kind(&item) == Some(TokenKind::Comma) {
            emit_token_item(&mut i, item);
            item = scan_pattern_nud_successor(i.rb(), local_stops);
            expect_item = true;
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
                line_handoff,
                completion,
            );
        }
        if token_kind(&item).is_none() {
            *completion = PatternCompletion::Incomplete;
            return missing_close(i, item);
        }
        if is_other_close(owner, &item) {
            emit_error_item(&mut i, item);
            item = scan_pattern_nud_successor(i.rb(), local_stops);
            continue;
        }
        if is_item_start(owner, &item) {
            if implicit_delimited_newline(baseline, item.leading_view()) {
                item.emit_all_remaining_leading(&mut *i.state);
            } else {
                item.emit_all_remaining_leading(&mut *i.state);
                emit_missing(&mut i, LeadingTrivia::default());
            }
            expect_item = true;
            continue;
        }
        emit_error_item(&mut i, item);
        item = scan_pattern_nud_successor(i.rb(), local_stops);
        if matches!(owner, Owner::Record) {
            expect_item = true;
        }
    }
}

fn finish_delimited_pattern(
    i: RewriteIn,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    outer_stops: PatternStops,
    contents_completion: PatternCompletion,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    let mut tail_completion = PatternCompletion::Complete;
    let exit = scan_pattern_tail(
        i,
        minimum,
        incoming_baseline,
        outer_stops,
        line_handoff,
        &mut tail_completion,
    );
    *completion = contents_completion;
    merge_completion(completion, tail_completion);
    exit
}

fn merge_completion(completion: &mut PatternCompletion, nested: PatternCompletion) {
    if nested == PatternCompletion::Incomplete {
        *completion = PatternCompletion::Incomplete;
    }
}

fn list_item(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    if token_kind(&item) != Some(TokenKind::DotDot) {
        return pattern_from_item_recording(
            i,
            item,
            PatternPrecedence::Lowest,
            baseline,
            PATTERN_STOP_COMMA | PATTERN_STOP_RBRACKET,
            line_handoff,
            completion,
        );
    }
    i.state.start_node(SyntaxKind::ListPatternSpreadItem.into());
    emit_token_item(&mut i, item);
    let leading = scan_trivia(i.rb());
    let mut rhs =
        pattern_nud_item_after_trivia(i.rb(), leading, PATTERN_STOP_COMMA | PATTERN_STOP_RBRACKET);
    let rhs_baseline = delimited_baseline(baseline, rhs.leading_view());
    rhs.emit_all_remaining_leading(&mut *i.state);
    let exit = pattern_from_item_recording(
        i.rb(),
        rhs,
        PatternPrecedence::Lowest,
        rhs_baseline,
        PATTERN_STOP_COMMA | PATTERN_STOP_RBRACKET,
        line_handoff,
        completion,
    );
    i.state.finish_node();
    exit
}

fn record_item(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
) -> TailExit {
    if token_kind(&item) == Some(TokenKind::DotDot) {
        i.state
            .start_node(SyntaxKind::RecordPatternSpreadItem.into());
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        let mut rhs = pattern_nud_item_after_trivia(
            i.rb(),
            leading,
            PATTERN_STOP_COMMA | PATTERN_STOP_RBRACE,
        );
        let rhs_baseline = delimited_baseline(baseline, rhs.leading_view());
        rhs.emit_all_remaining_leading(&mut *i.state);
        let exit = pattern_from_item_recording(
            i.rb(),
            rhs,
            PatternPrecedence::Lowest,
            rhs_baseline,
            PATTERN_STOP_COMMA | PATTERN_STOP_RBRACE,
            line_handoff,
            completion,
        );
        i.state.finish_node();
        return exit;
    }
    if !is_pattern_name(&item) {
        *completion = PatternCompletion::Incomplete;
        let mut item = item;
        item.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(item);
    }

    *completion = PatternCompletion::Complete;
    i.state.start_node(SyntaxKind::RecordPatternField.into());
    emit_token_item(&mut i, item);
    let leading = scan_trivia(i.rb());
    let record_stops = PATTERN_STOP_COMMA | PATTERN_STOP_RBRACE | PATTERN_STOP_EQUALS;
    let item = pattern_item_after_trivia(i.rb(), leading, record_stops);
    let exit = if !has_newline(item.leading_view()) && token_kind(&item) == Some(TokenKind::Colon) {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        let mut nested = pattern_nud_item_after_trivia(i.rb(), leading, record_stops);
        let nested_baseline = delimited_baseline(baseline, nested.leading_view());
        nested.emit_all_remaining_leading(&mut *i.state);
        let exit = pattern_from_item_recording(
            i.rb(),
            nested,
            PatternPrecedence::Lowest,
            nested_baseline,
            record_stops,
            line_handoff,
            completion,
        );
        record_default_after_pattern(i.rb(), exit, baseline, line_handoff)
    } else if !has_newline(item.leading_view()) && token_kind(&item) == Some(TokenKind::Equals) {
        record_default_after_equals(i.rb(), item, baseline, line_handoff)
    } else {
        handoff(item)
    };
    i.state.finish_node();
    exit
}

fn record_default_after_pattern(
    mut i: RewriteIn,
    exit: TailExit,
    baseline: usize,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let item = match exit {
        Ok(()) => scan_pattern_nud_successor(
            i.rb(),
            PATTERN_STOP_COMMA | PATTERN_STOP_RBRACE | PATTERN_STOP_EQUALS,
        ),
        Err(Either::Left(item)) => item,
        Err(Either::Right(end)) => return Err(Either::Right(end)),
    };
    if !has_newline(item.leading_view()) && token_kind(&item) == Some(TokenKind::Equals) {
        record_default_after_equals(i, item, baseline, line_handoff)
    } else {
        handoff(item)
    }
}

fn record_default_after_equals(
    mut i: RewriteIn,
    equals: Item,
    baseline: usize,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    emit_token_item(&mut i, equals);
    let leading = scan_trivia(i.rb());
    let mut rhs = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, 0);
    if is_nud_item(&rhs) {
        let rhs_baseline = delimited_baseline(baseline, rhs.leading_view());
        rhs.emit_all_remaining_leading(&mut *i.state);
        return super::super::driver::expr_from_nud(
            i,
            rhs,
            None,
            rhs_baseline,
            stops_for(TokenKind::RBrace),
            MlMode::All,
            line_handoff,
        );
    }
    rhs.emit_all_remaining_leading(&mut *i.state);
    emit_missing(&mut i, LeadingTrivia::default());
    handoff(rhs)
}

fn scan_pattern_nud_successor(mut i: RewriteIn, stops: PatternStops) -> Item {
    let leading = scan_trivia(i.rb());
    pattern_nud_item_after_trivia(i, leading, stops)
}

fn missing_close(mut i: RewriteIn, mut item: Item) -> TailExit {
    item.emit_all_remaining_leading(&mut *i.state);
    emit_missing(&mut i, LeadingTrivia::default());
    i.state.finish_node();
    handoff(item)
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
