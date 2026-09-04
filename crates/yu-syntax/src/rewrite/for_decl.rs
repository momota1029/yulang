//! Direct canonical `for` statement construction.

use reborrow_generic::Reborrow as _;

use crate::{scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    LexIn, RewriteIn, Stops,
    driver::{
        Either, MlMode, TailExit, handoff, implicit_delimited_newline, is_active_stop,
        is_active_stop_lex, is_separator, required_expr_item, token_kind,
    },
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, Token, TokenKind},
    lexer::{
        introduced_body_indentation, pattern_nud_item_after_trivia,
        scan_apostrophe_sigil_identifier, scan_statement_item, scan_trivia,
        statement_item_after_trivia, tail_item_after_trivia,
    },
    operator::{STOP_COLON, STOP_COMMA, STOP_LBRACE, STOP_SEMICOLON},
    pattern::{
        PATTERN_STOP_IN, PATTERN_STOP_LBRACE, PATTERN_STOP_PRIMARY_COLON, PatternCompletion,
        pattern_from_entry_item_with_completion, pattern_stops_from_owner,
    },
    statement::{braced_statement_block, indented_statement_block},
};

pub(super) fn for_statement_selected(item: &Item) -> bool {
    item_word(item) == Some("for")
}

pub(super) fn for_statement(
    mut i: RewriteIn,
    keyword: Item,
    baseline: usize,
    outer_stops: Stops,
) -> TailExit {
    debug_assert!(for_statement_selected(&keyword));
    i.state.start_node(SyntaxKind::ForStatement.into());
    emit_keyword(&mut i, keyword, SyntaxKind::ForKw, "for");
    emit_optional_label(i.rb(), baseline, outer_stops);
    let exit = pattern_slot(i.rb(), baseline, outer_stops);
    i.state.finish_node();
    exit
}

fn emit_optional_label(mut i: RewriteIn, baseline: usize, outer_stops: Stops) {
    let Some((before, label, after)) = i.token(|lex| scan_label(lex, baseline, outer_stops)) else {
        return;
    };
    emit_leading_trivia(&mut i, &before);
    i.state.start_node(SyntaxKind::ForLabel.into());
    emit_token_item(
        &mut i,
        Item {
            leading: LeadingTrivia::default(),
            payload: Payload::Token(label),
        },
    );
    i.state.finish_node();
    emit_leading_trivia(&mut i, &after);
}

fn scan_label(
    mut i: LexIn,
    baseline: usize,
    outer_stops: Stops,
) -> Option<(LeadingTrivia, Token, LeadingTrivia)> {
    let mut accepted = false;
    let rolled_back: Option<()> = i.token(|mut probe| {
        let before = scan_trivia(probe.rb());
        if implicit_gap(baseline, &before) {
            return None;
        }
        scan_apostrophe_sigil_identifier(probe.rb())?;
        let after = scan_trivia(probe.rb());
        if implicit_gap(baseline, &after) {
            return None;
        }
        let next = scan_statement_item(probe.rb(), baseline, outer_stops)?;
        accepted = !label_following_boundary(probe.rb(), &next, baseline, outer_stops)
            && item_word(&next) != Some("in");
        None
    });
    debug_assert!(rolled_back.is_none());
    accepted.then_some(())?;

    let before = scan_trivia(i.rb());
    let label = scan_apostrophe_sigil_identifier(i.rb())?;
    let after = scan_trivia(i.rb());
    Some((before, label, after))
}

fn pattern_slot(mut i: RewriteIn, baseline: usize, outer_stops: Stops) -> TailExit {
    let stops = pattern_stops_from_owner(outer_stops)
        | PATTERN_STOP_PRIMARY_COLON
        | PATTERN_STOP_LBRACE
        | PATTERN_STOP_IN;
    let leading = scan_trivia(i.rb());
    let mut item = pattern_nud_item_after_trivia(i.rb(), leading, stops);
    let missing_at_in = item_word(&item) == Some("in");
    let missing_at_body = matches!(
        token_kind(&item),
        Some(TokenKind::Colon | TokenKind::LBrace)
    );
    if implicit_delimited_newline(baseline, &item.leading) {
        i.state.start_node(SyntaxKind::Pattern.into());
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return handoff(item);
    }
    emit_leading_trivia(&mut i, &std::mem::take(&mut item.leading));
    let outcome = pattern_from_entry_item_with_completion(i.rb(), item, baseline, stops);
    match outcome.exit {
        Err(Either::Left(item)) => match outcome.completion {
            PatternCompletion::Complete => in_slot(i, item, baseline, outer_stops),
            PatternCompletion::Incomplete if missing_at_in => {
                in_slot(i, item, baseline, outer_stops)
            }
            PatternCompletion::Incomplete if missing_at_body => {
                body(i, item, baseline, outer_stops)
            }
            PatternCompletion::Incomplete => handoff(item),
        },
        Err(Either::Right(end)) => Err(Either::Right(end)),
        Ok(()) => unreachable!("a Pattern leaves its successor Item"),
    }
}

fn in_slot(mut i: RewriteIn, mut item: Item, baseline: usize, outer_stops: Stops) -> TailExit {
    if implicit_delimited_newline(baseline, &item.leading) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(item);
    }
    if item_word(&item) == Some("in") {
        emit_keyword(&mut i, item, SyntaxKind::InKw, "in");
        return iterable(i, baseline, outer_stops);
    }

    if !outer_boundary(i.rb(), &item, baseline, outer_stops)
        && !matches!(
            token_kind(&item),
            Some(TokenKind::Colon | TokenKind::LBrace)
        )
    {
        emit_leading_trivia(&mut i, &std::mem::take(&mut item.leading));
    }
    emit_missing(&mut i, LeadingTrivia::default());
    if matches!(
        token_kind(&item),
        Some(TokenKind::Colon | TokenKind::LBrace)
    ) {
        return body(i, item, baseline, outer_stops);
    }
    if outer_boundary(i.rb(), &item, baseline, outer_stops) {
        return handoff(item);
    }
    iterable_from_item(i, item, baseline, outer_stops, false)
}

fn iterable(mut i: RewriteIn, baseline: usize, outer_stops: Stops) -> TailExit {
    let leading = scan_trivia(i.rb());
    let mut item = tail_item_after_trivia(
        i.rb(),
        leading,
        OperatorSite::Nud,
        baseline,
        iterable_stops(outer_stops),
    );
    let missing = iterable_boundary(i.rb(), &item, baseline, outer_stops);
    if !implicit_delimited_newline(baseline, &item.leading) {
        emit_leading_trivia(&mut i, &std::mem::take(&mut item.leading));
    }
    iterable_from_item(i, item, baseline, outer_stops, missing)
}

fn iterable_from_item(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    outer_stops: Stops,
    missing: bool,
) -> TailExit {
    if !implicit_delimited_newline(baseline, &item.leading) && !item.leading.0.is_empty() {
        emit_leading_trivia(&mut i, &std::mem::take(&mut item.leading));
    }
    i.state.start_node(SyntaxKind::ForIterable.into());
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = if implicit_delimited_newline(baseline, &item.leading) {
        emit_missing(&mut i, LeadingTrivia::default());
        handoff(item)
    } else {
        required_expr_item(
            i.rb(),
            item,
            None,
            baseline,
            iterable_stops(outer_stops),
            MlMode::All,
        )
    };
    i.state.finish_node();
    i.state.finish_node();

    match exit {
        Err(Either::Left(item))
            if matches!(
                token_kind(&item),
                Some(TokenKind::Colon | TokenKind::LBrace)
            ) =>
        {
            body(i, item, baseline, outer_stops)
        }
        Err(Either::Left(item)) if missing => handoff(item),
        Err(Either::Left(item)) => body(i, item, baseline, outer_stops),
        Err(Either::Right(end)) if missing => Err(Either::Right(end)),
        Err(Either::Right(end)) => missing_body_introducer(i, Err(Either::Right(end))),
        Ok(()) => unreachable!("an iterable leaves its successor Item"),
    }
}

fn body(mut i: RewriteIn, mut item: Item, baseline: usize, outer_stops: Stops) -> TailExit {
    if implicit_delimited_newline(baseline, &item.leading) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(item);
    }
    match token_kind(&item) {
        Some(TokenKind::Colon) => {
            emit_token_item(&mut i, item);
            colon_body(i, baseline, outer_stops)
        }
        Some(TokenKind::LBrace) => {
            emit_leading_trivia(&mut i, &std::mem::take(&mut item.leading));
            braced_statement_block(i, item, baseline)
        }
        _ if outer_boundary(i.rb(), &item, baseline, outer_stops) => {
            missing_body_introducer(i, handoff(item))
        }
        _ => recover_body_introducer(i, item, baseline, outer_stops),
    }
}

fn colon_body(mut i: RewriteIn, baseline: usize, outer_stops: Stops) -> TailExit {
    match introduced_body_indentation(i.rb()) {
        Some(indentation) if indentation > baseline => {
            indented_statement_block(i, baseline, outer_stops)
        }
        Some(_) => {
            emit_missing(&mut i, LeadingTrivia::default());
            let leading = scan_trivia(i.rb());
            let item = statement_item_after_trivia(i, leading, baseline, outer_stops);
            handoff(item)
        }
        None => inline_body(i, baseline, outer_stops),
    }
}

fn inline_body(mut i: RewriteIn, baseline: usize, outer_stops: Stops) -> TailExit {
    let stops = outer_stops | STOP_COMMA | STOP_SEMICOLON;
    let leading = scan_trivia(i.rb());
    let mut item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
    emit_leading_trivia(&mut i, &std::mem::take(&mut item.leading));
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = required_expr_item(i.rb(), item, None, baseline, stops, MlMode::All);
    i.state.finish_node();
    exit
}

fn recover_body_introducer(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    outer_stops: Stops,
) -> TailExit {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = statement_item_after_trivia(i.rb(), leading, baseline, outer_stops);
        if matches!(
            token_kind(&item),
            Some(TokenKind::Colon | TokenKind::LBrace)
        ) {
            i.state.finish_node();
            return body(i, item, baseline, outer_stops);
        }
        if implicit_delimited_newline(baseline, &item.leading)
            || outer_boundary(i.rb(), &item, baseline, outer_stops)
        {
            i.state.finish_node();
            return handoff(item);
        }
    }
}

fn missing_body_introducer(mut i: RewriteIn, exit: TailExit) -> TailExit {
    emit_missing(&mut i, LeadingTrivia::default());
    exit
}

fn iterable_stops(outer_stops: Stops) -> Stops {
    outer_stops | STOP_COLON | STOP_LBRACE | STOP_COMMA | STOP_SEMICOLON
}

fn iterable_boundary(mut i: RewriteIn, item: &Item, baseline: usize, outer_stops: Stops) -> bool {
    implicit_delimited_newline(baseline, &item.leading)
        || matches!(item.payload, Payload::Eof)
        || is_active_stop(i.rb(), item, iterable_stops(outer_stops))
}

fn outer_boundary(mut i: RewriteIn, item: &Item, baseline: usize, outer_stops: Stops) -> bool {
    implicit_delimited_newline(baseline, &item.leading)
        || matches!(item.payload, Payload::Eof)
        || is_separator(item)
        || is_active_stop(i.rb(), item, outer_stops)
}

fn label_following_boundary(
    mut i: LexIn,
    item: &Item,
    baseline: usize,
    outer_stops: Stops,
) -> bool {
    implicit_gap(baseline, &item.leading)
        || matches!(item.payload, Payload::Eof)
        || is_separator(item)
        || is_active_stop_lex(i.rb(), item, outer_stops)
        || matches!(token_kind(item), Some(TokenKind::Colon | TokenKind::LBrace))
}

fn implicit_gap(baseline: usize, leading: &LeadingTrivia) -> bool {
    implicit_delimited_newline(baseline, leading)
}

fn item_word(item: &Item) -> Option<&str> {
    match &item.payload {
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text,
        }) => Some(text),
        Payload::Token(_) | Payload::Operator(_) | Payload::Eof => None,
    }
}

fn emit_keyword(i: &mut RewriteIn, item: Item, kind: SyntaxKind, spelling: &str) {
    emit_leading_trivia(i, &item.leading);
    let Payload::Token(Token {
        kind: TokenKind::Identifier,
        text,
    }) = item.payload
    else {
        unreachable!("a For keyword is an identifier-shaped token")
    };
    debug_assert_eq!(&*text, spelling);
    i.state.token(kind.into(), &text);
}
