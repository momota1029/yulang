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
        item::{Item, LeadingTrivia, TokenKind, TriviaKind},
        lexer::{
            pattern_item_after_trivia, pattern_nud_item_after_trivia, scan_trivia,
            tail_item_after_trivia,
        },
    },
    PatternPrecedence, RewriteIn, pattern_from_item, scan_pattern_tail,
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
}

pub(super) fn parenthesized_pattern(
    i: RewriteIn,
    open: Item,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    colon_stop: bool,
) -> TailExit {
    pattern_delimited(
        i,
        open,
        Owner::Parenthesized,
        minimum,
        incoming_baseline,
        colon_stop,
    )
}

pub(super) fn list_pattern(
    i: RewriteIn,
    open: Item,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    colon_stop: bool,
) -> TailExit {
    pattern_delimited(i, open, Owner::List, minimum, incoming_baseline, colon_stop)
}

pub(super) fn record_pattern(
    i: RewriteIn,
    open: Item,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    colon_stop: bool,
) -> TailExit {
    pattern_delimited(
        i,
        open,
        Owner::Record,
        minimum,
        incoming_baseline,
        colon_stop,
    )
}

fn pattern_delimited(
    mut i: RewriteIn,
    open: Item,
    owner: Owner,
    minimum: PatternPrecedence,
    incoming_baseline: usize,
    colon_stop: bool,
) -> TailExit {
    i.state.start_node(owner.node().into());
    emit_token_item(&mut i, open);
    let opening = scan_trivia(i.rb());
    let baseline = delimited_baseline(incoming_baseline, &opening);
    emit_leading_trivia(&mut i, &opening);
    let mut item = pattern_nud_item_after_trivia(i.rb(), LeadingTrivia::default());
    let mut expect_item = true;

    loop {
        if expect_item {
            if token_kind(&item) == Some(owner.close()) {
                emit_token_item(&mut i, item);
                i.state.finish_node();
                return scan_pattern_tail(i, minimum, incoming_baseline, colon_stop);
            }
            if matches!(owner, Owner::Record) && token_kind(&item) == Some(TokenKind::Comma) {
                let leading = std::mem::take(&mut item.leading);
                emit_missing(&mut i, leading);
                emit_token_item(&mut i, item);
                item = scan_pattern_nud_successor(i.rb());
                continue;
            }
            if token_kind(&item).is_none() {
                return missing_close(i, item);
            }
            if is_other_close(owner, &item) {
                emit_error_item(&mut i, item);
                item = scan_pattern_nud_successor(i.rb());
                continue;
            }
            if matches!(owner, Owner::Record) && !is_item_start(owner, &item) {
                emit_error_item(&mut i, item);
                item = scan_pattern_nud_successor(i.rb());
                continue;
            }
            let item_baseline = delimited_baseline(baseline, &item.leading);
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            let exit = match owner {
                Owner::Parenthesized => pattern_from_item(
                    i.rb(),
                    item,
                    PatternPrecedence::Lowest,
                    item_baseline,
                    false,
                ),
                Owner::List => list_item(i.rb(), item, item_baseline),
                Owner::Record => record_item(i.rb(), item, item_baseline),
            };
            item = match exit {
                Ok(()) => scan_pattern_nud_successor(i.rb()),
                Err(Either::Left(next)) => next,
                Err(Either::Right(end)) => return missing_close(i, end.item),
            };
            expect_item = false;
            continue;
        }

        if token_kind(&item) == Some(TokenKind::Comma) {
            emit_token_item(&mut i, item);
            item = scan_pattern_nud_successor(i.rb());
            expect_item = true;
            continue;
        }
        if token_kind(&item) == Some(owner.close()) {
            emit_token_item(&mut i, item);
            i.state.finish_node();
            return scan_pattern_tail(i, minimum, incoming_baseline, colon_stop);
        }
        if token_kind(&item).is_none() {
            return missing_close(i, item);
        }
        if is_other_close(owner, &item) {
            emit_error_item(&mut i, item);
            item = scan_pattern_nud_successor(i.rb());
            continue;
        }
        if is_item_start(owner, &item) {
            if implicit_delimited_newline(baseline, &item.leading) {
                let leading = std::mem::take(&mut item.leading);
                emit_leading_trivia(&mut i, &leading);
            } else {
                let leading = std::mem::take(&mut item.leading);
                emit_missing(&mut i, leading);
            }
            expect_item = true;
            continue;
        }
        emit_error_item(&mut i, item);
        item = scan_pattern_nud_successor(i.rb());
        if matches!(owner, Owner::Record) {
            expect_item = true;
        }
    }
}

fn list_item(mut i: RewriteIn, item: Item, baseline: usize) -> TailExit {
    if token_kind(&item) != Some(TokenKind::DotDot) {
        return pattern_from_item(i, item, PatternPrecedence::Lowest, baseline, false);
    }
    i.state.start_node(SyntaxKind::ListPatternSpreadItem.into());
    emit_token_item(&mut i, item);
    let leading = scan_trivia(i.rb());
    let mut rhs = pattern_nud_item_after_trivia(i.rb(), leading);
    let rhs_baseline = delimited_baseline(baseline, &rhs.leading);
    let leading = std::mem::take(&mut rhs.leading);
    emit_leading_trivia(&mut i, &leading);
    let exit = pattern_from_item(i.rb(), rhs, PatternPrecedence::Lowest, rhs_baseline, false);
    i.state.finish_node();
    exit
}

fn record_item(mut i: RewriteIn, item: Item, baseline: usize) -> TailExit {
    if token_kind(&item) == Some(TokenKind::DotDot) {
        i.state
            .start_node(SyntaxKind::RecordPatternSpreadItem.into());
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        let mut rhs = pattern_nud_item_after_trivia(i.rb(), leading);
        let rhs_baseline = delimited_baseline(baseline, &rhs.leading);
        let leading = std::mem::take(&mut rhs.leading);
        emit_leading_trivia(&mut i, &leading);
        let exit = pattern_from_item(i.rb(), rhs, PatternPrecedence::Lowest, rhs_baseline, false);
        i.state.finish_node();
        return exit;
    }
    if !is_pattern_name(&item) {
        let mut item = item;
        let leading = std::mem::take(&mut item.leading);
        emit_missing(&mut i, leading);
        return handoff(item);
    }

    i.state.start_node(SyntaxKind::RecordPatternField.into());
    emit_token_item(&mut i, item);
    let leading = scan_trivia(i.rb());
    let item = pattern_item_after_trivia(i.rb(), leading);
    let exit = if !has_newline(&item.leading) && token_kind(&item) == Some(TokenKind::Colon) {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        let mut nested = pattern_nud_item_after_trivia(i.rb(), leading);
        let nested_baseline = delimited_baseline(baseline, &nested.leading);
        let leading = std::mem::take(&mut nested.leading);
        emit_leading_trivia(&mut i, &leading);
        let exit = pattern_from_item(
            i.rb(),
            nested,
            PatternPrecedence::Lowest,
            nested_baseline,
            false,
        );
        record_default_after_pattern(i.rb(), exit, baseline)
    } else if !has_newline(&item.leading) && token_kind(&item) == Some(TokenKind::Equals) {
        record_default_after_equals(i.rb(), item, baseline)
    } else {
        handoff(item)
    };
    i.state.finish_node();
    exit
}

fn record_default_after_pattern(mut i: RewriteIn, exit: TailExit, baseline: usize) -> TailExit {
    let item = match exit {
        Ok(()) => scan_pattern_nud_successor(i.rb()),
        Err(Either::Left(item)) => item,
        Err(Either::Right(end)) => return Err(Either::Right(end)),
    };
    if !has_newline(&item.leading) && token_kind(&item) == Some(TokenKind::Equals) {
        record_default_after_equals(i, item, baseline)
    } else {
        handoff(item)
    }
}

fn record_default_after_equals(mut i: RewriteIn, equals: Item, baseline: usize) -> TailExit {
    emit_token_item(&mut i, equals);
    let leading = scan_trivia(i.rb());
    let mut rhs = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, 0);
    if is_nud_item(&rhs) {
        let rhs_baseline = delimited_baseline(baseline, &rhs.leading);
        let leading = std::mem::take(&mut rhs.leading);
        emit_leading_trivia(&mut i, &leading);
        return super::super::driver::expr_from_nud(i, rhs, None, rhs_baseline, 0, MlMode::All);
    }
    let leading = std::mem::take(&mut rhs.leading);
    emit_missing(&mut i, leading);
    handoff(rhs)
}

fn scan_pattern_nud_successor(mut i: RewriteIn) -> Item {
    let leading = scan_trivia(i.rb());
    pattern_nud_item_after_trivia(i, leading)
}

fn missing_close(mut i: RewriteIn, mut item: Item) -> TailExit {
    let leading = std::mem::take(&mut item.leading);
    emit_missing(&mut i, leading);
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

fn has_newline(leading: &LeadingTrivia) -> bool {
    leading
        .0
        .iter()
        .any(|part| matches!(part.kind, TriviaKind::Newline))
}
