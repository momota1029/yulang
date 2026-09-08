//! Lexical-only token, contextual-stop and physical-leading observations.
use crate::{
    cursor::{LexIn, SyntaxIn},
    lexical::{
        item::{Item, LeadingView, TokenKind},
        lexer::contextual_word_suffix_follower,
        stops::{STOP_LINE_BREAK, Stops, active_stop_item},
    },
};
use reborrow_generic::Reborrow as _;

/// Dynamic word operators retain `elsif?` and `else!` through lexical suffix observation.
pub(crate) fn is_active_stop(i: SyntaxIn, item: &Item, stops: Stops) -> bool {
    i.map(
        |lex: LexIn| Some(is_active_stop_lex(lex, item, stops)),
        |active| active,
    )
    .expect("typed stop observation is total")
}

pub(crate) fn is_active_stop_lex(mut i: LexIn, item: &Item, stops: Stops) -> bool {
    if token_kind(item).is_some_and(|kind| active_stop_item(kind, stops)) {
        return true;
    }
    (stops & crate::lexical::stops::STOP_ELSIF != 0
        && is_contextual_word_lex(i.rb(), item, "elsif"))
        || (stops & crate::lexical::stops::STOP_ELSE != 0
            && is_contextual_word_lex(i, item, "else"))
}

pub(crate) fn is_contextual_word(mut i: SyntaxIn, item: &Item, word: &str) -> bool {
    let payload = item.payload_view();
    if payload.token_kind() == Some(TokenKind::Identifier) {
        return payload.spelling() == Some(word);
    }
    if payload.operator_use().is_some() {
        return payload.spelling() == Some(word)
            && i.rb()
                .map(contextual_word_suffix_follower, |follower| follower)
                .unwrap_or(false);
    }
    assert!(
        !payload.is_boundary(),
        "a boundary is not a contextual word"
    );
    false
}

fn is_contextual_word_lex(mut i: LexIn, item: &Item, word: &str) -> bool {
    let payload = item.payload_view();
    if payload.token_kind() == Some(TokenKind::Identifier) {
        return payload.spelling() == Some(word);
    }
    if payload.operator_use().is_some() {
        return payload.spelling() == Some(word)
            && i.token(contextual_word_suffix_follower)
                .expect("contextual suffix observation is total");
    }
    assert!(
        !payload.is_boundary(),
        "a boundary is not a contextual word"
    );
    false
}

pub(crate) fn token_kind(item: &Item) -> Option<TokenKind> {
    let payload = item.payload_view();
    if let Some(kind) = payload.token_kind() {
        return Some(kind);
    }
    if payload.operator_use().is_some() {
        return Some(TokenKind::Operator);
    }
    assert!(!payload.is_boundary(), "a boundary has no token kind");
    None
}

pub(crate) fn is_separator(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Comma | TokenKind::Semicolon)
    )
}

pub(crate) fn is_close(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
    )
}

pub(crate) fn delimited_baseline(incoming: usize, leading: LeadingView<'_>) -> usize {
    indentation_after_newline(leading)
        .filter(|&indentation| indentation > incoming)
        .unwrap_or(incoming)
}

pub(crate) fn implicit_delimited_newline(baseline: usize, leading: LeadingView<'_>) -> bool {
    indentation_after_newline(leading).is_some_and(|indentation| indentation <= baseline)
}

pub(crate) fn indentation_after_newline(leading: LeadingView<'_>) -> Option<usize> {
    leading.indentation_after_newline()
}

pub(crate) fn is_line_stop(item: &Item, stops: Stops) -> bool {
    stops & STOP_LINE_BREAK != 0 && indentation_after_newline(item.leading_view()).is_some()
}
