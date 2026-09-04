//! Source-free direct Pattern construction.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

mod delimited;

use super::{
    RewriteIn,
    driver::{
        Either, TailExit, delimited_baseline, handoff, implicit_delimited_newline, token_kind,
    },
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, Token, TokenKind},
    lexer::{
        pattern_item_after_trivia, pattern_nud_item_after_trivia, scan_identifier, scan_trivia,
        type_item_after_trivia,
    },
    type_expr::type_expr,
};

use self::delimited::{list_pattern, parenthesized_pattern, record_pattern};

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum PatternPrecedence {
    Lowest,
    TypeAnnotation,
    Alternation,
    Alias,
}

pub(super) fn pattern(i: RewriteIn) -> TailExit {
    pattern_with_colon_stop(i, false)
}

pub(super) fn pattern_with_colon_stop(mut i: RewriteIn, colon_stop: bool) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = pattern_nud_item_after_trivia(i.rb(), leading);
    pattern_from_item(i, item, PatternPrecedence::Lowest, 0, colon_stop)
}

fn pattern_from_item(
    mut i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    colon_stop: bool,
) -> TailExit {
    let accepted_symbol = token_kind(&item) == Some(TokenKind::PatternSymbolColon)
        || (token_kind(&item) == Some(TokenKind::Colon) && !colon_stop);
    if !is_pattern_primary(&item) && !accepted_symbol {
        return handoff(item);
    }
    let baseline = delimited_baseline(baseline, &item.leading);
    i.state.start_node(SyntaxKind::Pattern.into());
    let exit = pattern_from_primary(i.rb(), item, minimum, baseline, colon_stop);
    i.state.finish_node();
    exit
}

fn pattern_from_primary(
    mut i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    colon_stop: bool,
) -> TailExit {
    match token_kind(&item) {
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier) => {
            i.state.start_node(SyntaxKind::IdentifierPattern.into());
            emit_token_item(&mut i, item);
            i.state.finish_node();
            scan_pattern_tail(i, minimum, baseline, colon_stop)
        }
        Some(TokenKind::Integer) => {
            i.state.start_node(SyntaxKind::IntegerPattern.into());
            emit_token_item(&mut i, item);
            i.state.finish_node();
            scan_pattern_tail(i, minimum, baseline, colon_stop)
        }
        Some(TokenKind::Colon | TokenKind::PatternSymbolColon) => {
            i.state.start_node(SyntaxKind::SymbolPattern.into());
            emit_token_item(&mut i, item);
            if let Some(name) = i.token(scan_identifier) {
                emit_token_item(
                    &mut i,
                    Item {
                        leading: LeadingTrivia::default(),
                        payload: Payload::Token(name),
                    },
                );
            } else {
                emit_missing(&mut i, LeadingTrivia::default());
            }
            i.state.finish_node();
            scan_pattern_tail(i, minimum, baseline, colon_stop)
        }
        Some(TokenKind::LParen) => parenthesized_pattern(i, item, minimum, baseline, colon_stop),
        Some(TokenKind::LBracket) => list_pattern(i, item, minimum, baseline, colon_stop),
        Some(TokenKind::LBrace) => record_pattern(i, item, minimum, baseline, colon_stop),
        _ => unreachable!("the Pattern NUD judge accepted only Pattern primaries"),
    }
}

fn scan_pattern_tail(
    mut i: RewriteIn,
    minimum: PatternPrecedence,
    baseline: usize,
    colon_stop: bool,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = pattern_item_after_trivia(i.rb(), leading);
    pattern_tail(i, item, minimum, baseline, colon_stop)
}

fn pattern_tail(
    mut i: RewriteIn,
    mut item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    colon_stop: bool,
) -> TailExit {
    if implicit_delimited_newline(baseline, &item.leading) {
        return handoff(item);
    }
    if is_pattern_alias(&item) && minimum <= PatternPrecedence::Alias {
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        i.state.start_node(SyntaxKind::PatternAliasTail.into());
        emit_pattern_alias_keyword(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = pattern_item_after_trivia(i.rb(), leading);
        if token_kind(&item) == Some(TokenKind::Identifier) {
            emit_token_item(&mut i, item);
        } else {
            let leading = std::mem::take(&mut item.leading);
            emit_missing(&mut i, leading);
            i.state.finish_node();
            return handoff(item);
        }
        i.state.finish_node();
        return scan_pattern_tail(i, minimum, baseline, colon_stop);
    }
    if token_kind(&item) == Some(TokenKind::Pipe) && minimum <= PatternPrecedence::Alternation {
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        i.state
            .start_node(SyntaxKind::PatternAlternationTail.into());
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        let mut rhs = pattern_nud_item_after_trivia(i.rb(), leading);
        let rhs_baseline = delimited_baseline(baseline, &rhs.leading);
        let leading = std::mem::take(&mut rhs.leading);
        emit_leading_trivia(&mut i, &leading);
        let exit = pattern_from_item(
            i.rb(),
            rhs,
            PatternPrecedence::Alternation,
            rhs_baseline,
            colon_stop,
        );
        i.state.finish_node();
        return continue_pattern_tail(i, exit, minimum, baseline, colon_stop);
    }
    if token_kind(&item) == Some(TokenKind::Colon)
        && !colon_stop
        && minimum <= PatternPrecedence::TypeAnnotation
    {
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        i.state.start_node(SyntaxKind::PatternTypeAnnotation.into());
        emit_token_item(&mut i, item);
        let exit = pattern_type_annotation_rhs(i.rb(), baseline);
        i.state.finish_node();
        return exit;
    }
    handoff(item)
}

fn continue_pattern_tail(
    i: RewriteIn,
    exit: TailExit,
    minimum: PatternPrecedence,
    baseline: usize,
    colon_stop: bool,
) -> TailExit {
    match exit {
        Ok(()) => scan_pattern_tail(i, minimum, baseline, colon_stop),
        Err(Either::Left(item)) => pattern_tail(i, item, minimum, baseline, colon_stop),
        Err(Either::Right(end)) => Err(Either::Right(end)),
    }
}

fn pattern_type_annotation_rhs(mut i: RewriteIn, baseline: usize) -> TailExit {
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
    if let Some(exit) = type_expr(i.rb()) {
        return exit;
    }
    i.state.start_node(SyntaxKind::TypeExpression.into());
    emit_missing(&mut i, LeadingTrivia::default());
    i.state.finish_node();
    handoff(type_item_after_trivia(i, LeadingTrivia::default()))
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
