//! Standalone source-free direct TypeExpression core.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    RewriteIn,
    driver::{Either, TailExit, handoff, token_kind},
    emit::{emit_leading_trivia, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind, TriviaKind},
    lexer::{scan_trivia, scan_type_nud_item, type_item_after_trivia},
};

pub(super) fn type_expr(mut i: RewriteIn) -> Option<TailExit> {
    let primary = i.token(scan_type_nud_item)?;
    Some(type_expr_from_primary(i, primary, 0, false))
}

fn type_expr_from_primary(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
) -> TailExit {
    i.state.start_node(SyntaxKind::TypeExpression.into());
    let exit = match token_kind(&primary) {
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier | TokenKind::Integer) => {
            emit_token_item(&mut i, primary);
            scan_type_tail(i.rb(), baseline, type_ml)
        }
        Some(TokenKind::LParen) => type_group(i.rb(), primary, baseline, type_ml),
        _ => unreachable!("the type NUD scanner accepts only type primaries"),
    };
    i.state.finish_node();
    exit
}

fn scan_type_tail(mut i: RewriteIn, baseline: usize, type_ml: bool) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = type_item_after_trivia(i.rb(), leading);
    type_tail(i, item, baseline, type_ml)
}

fn type_tail(mut i: RewriteIn, item: Item, baseline: usize, type_ml: bool) -> TailExit {
    if !type_chain_trivia(&item.leading, baseline) {
        return handoff(item);
    }
    if type_ml && !item.leading.0.is_empty() {
        return handoff(item);
    }
    match token_kind(&item) {
        Some(TokenKind::Arrow) => return type_arrow_tail(i.rb(), item, baseline),
        Some(TokenKind::LParen) if item.leading.0.is_empty() => {
            return type_call_tail(i.rb(), item, baseline, type_ml);
        }
        Some(TokenKind::PathSeparator) => {
            return type_path_tail(i.rb(), item, baseline, type_ml);
        }
        _ => {}
    }
    if !item.leading.0.is_empty() && is_type_primary(&item) {
        return type_apply_argument(i, item, baseline);
    }
    handoff(item)
}

fn type_group(mut i: RewriteIn, open: Item, baseline: usize, type_ml: bool) -> TailExit {
    i.state
        .start_node(SyntaxKind::ParenthesizedTypeGroup.into());
    emit_token_item(&mut i, open);
    let exit = type_delimited(i.rb(), baseline);
    i.state.finish_node();
    continue_type_tail(i, baseline, type_ml, exit)
}

fn type_call_tail(mut i: RewriteIn, open: Item, baseline: usize, type_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::TypeCallTail.into());
    emit_token_item(&mut i, open);
    let exit = type_delimited(i.rb(), baseline);
    i.state.finish_node();
    continue_type_tail(i, baseline, type_ml, exit)
}

fn type_delimited(mut i: RewriteIn, incoming_baseline: usize) -> TailExit {
    let opening = scan_trivia(i.rb());
    let baseline = type_delimited_baseline(incoming_baseline, &opening);
    emit_leading_trivia(&mut i, &opening);
    let mut item = type_item_after_trivia(i.rb(), LeadingTrivia::default());
    loop {
        if token_kind(&item) == Some(TokenKind::RParen) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if matches!(&item.payload, Payload::Eof) {
            return handoff(item);
        }
        if !is_type_primary(&item) {
            return handoff(item);
        }
        let exit = type_expr_from_primary(i.rb(), item, baseline, false);
        item = match exit {
            Ok(()) => type_item_after_trivia(i.rb(), LeadingTrivia::default()),
            Err(Either::Left(next)) if is_type_separator(&next) => {
                emit_token_item(&mut i, next);
                let leading = scan_trivia(i.rb());
                emit_leading_trivia(&mut i, &leading);
                type_item_after_trivia(i.rb(), LeadingTrivia::default())
            }
            Err(Either::Left(next)) if token_kind(&next) == Some(TokenKind::RParen) => {
                emit_token_item(&mut i, next);
                return Ok(());
            }
            Err(Either::Left(mut next)) if is_type_implicit_boundary(baseline, &next.leading) => {
                let leading = std::mem::take(&mut next.leading);
                emit_leading_trivia(&mut i, &leading);
                next
            }
            Err(exit) => return Err(exit),
        };
    }
}

fn type_path_tail(mut i: RewriteIn, separator: Item, baseline: usize, type_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::TypePathTail.into());
    emit_token_item(&mut i, separator);
    let trivia = scan_trivia(i.rb());
    if !type_chain_trivia(&trivia, baseline) {
        i.state.finish_node();
        return handoff(type_item_after_trivia(i, trivia));
    }
    emit_leading_trivia(&mut i, &trivia);
    let Some(segment) = i.token(scan_type_path_segment_item) else {
        i.state.finish_node();
        return handoff(type_item_after_trivia(i, LeadingTrivia::default()));
    };
    emit_token_item(&mut i, segment);
    i.state.finish_node();
    scan_type_tail(i, baseline, type_ml)
}

fn scan_type_path_segment_item(mut i: super::LexIn) -> Option<Item> {
    let token = i.token(super::lexer::scan_path_segment)?;
    Some(Item {
        leading: LeadingTrivia::default(),
        payload: Payload::Token(token),
    })
}

fn type_apply_argument(mut i: RewriteIn, mut argument: Item, baseline: usize) -> TailExit {
    i.state.start_node(SyntaxKind::TypeApplyArgument.into());
    let boundary = std::mem::take(&mut argument.leading);
    emit_leading_trivia(&mut i, &boundary);
    let exit = type_expr_from_primary(i.rb(), argument, baseline, true);
    i.state.finish_node();
    continue_type_tail(i, baseline, false, exit)
}

fn type_arrow_tail(mut i: RewriteIn, arrow: Item, baseline: usize) -> TailExit {
    i.state.start_node(SyntaxKind::TypeArrowTail.into());
    emit_token_item(&mut i, arrow);
    let trivia = scan_trivia(i.rb());
    if !type_chain_trivia(&trivia, baseline) {
        i.state.finish_node();
        return handoff(type_item_after_trivia(i, trivia));
    }
    emit_leading_trivia(&mut i, &trivia);
    let Some(rhs) = i.token(scan_type_nud_item) else {
        i.state.finish_node();
        return handoff(type_item_after_trivia(i, LeadingTrivia::default()));
    };
    let exit = type_expr_from_primary(i.rb(), rhs, baseline, false);
    i.state.finish_node();
    exit
}

fn continue_type_tail(i: RewriteIn, baseline: usize, type_ml: bool, exit: TailExit) -> TailExit {
    match exit {
        Ok(()) => scan_type_tail(i, baseline, type_ml),
        Err(Either::Left(item)) => type_tail(i, item, baseline, type_ml),
        Err(Either::Right(end)) => Err(Either::Right(end)),
    }
}

fn is_type_primary(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(
            TokenKind::Identifier
                | TokenKind::SigilIdentifier
                | TokenKind::Integer
                | TokenKind::LParen
        )
    )
}

fn is_type_separator(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Comma | TokenKind::Semicolon)
    )
}

fn type_chain_trivia(leading: &LeadingTrivia, baseline: usize) -> bool {
    indentation_after_newline(leading).is_none_or(|indentation| indentation > baseline)
}

fn is_type_implicit_boundary(baseline: usize, leading: &LeadingTrivia) -> bool {
    indentation_after_newline(leading).is_some_and(|indentation| indentation <= baseline)
}

fn type_delimited_baseline(incoming: usize, opening: &LeadingTrivia) -> usize {
    indentation_after_newline(opening)
        .filter(|&indentation| indentation > incoming)
        .unwrap_or(incoming)
}

fn indentation_after_newline(leading: &LeadingTrivia) -> Option<usize> {
    let mut saw_newline = false;
    let mut at_line_start = false;
    let mut indentation = 0usize;
    for part in &leading.0 {
        match part.kind {
            TriviaKind::Newline => {
                saw_newline = true;
                at_line_start = true;
                indentation = 0;
            }
            TriviaKind::Whitespace if at_line_start => indentation += part.text.chars().count(),
            _ => at_line_start = false,
        }
    }
    saw_newline.then_some(indentation)
}
