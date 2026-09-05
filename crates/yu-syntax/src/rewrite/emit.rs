//! Direct Rowan emission for already-accepted rewrite items.

use rowan::GreenNodeBuilder;

use crate::syntax_kind::SyntaxKind;

use super::{
    RewriteIn,
    driver::End,
    item::{Item, LeadingTrivia, TokenKind},
};

pub(super) fn emit_identifier_core(i: &mut RewriteIn, item: Item) {
    debug_assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    i.state.start_node(SyntaxKind::IdentifierExpression.into());
    item.emit_remaining(&mut *i.state, SyntaxKind::Identifier);
    i.state.finish_node();
}

pub(super) fn emit_integer_core(i: &mut RewriteIn, item: Item) {
    debug_assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Integer));
    i.state.start_node(SyntaxKind::IntegerLiteral.into());
    item.emit_remaining(&mut *i.state, SyntaxKind::Integer);
    i.state.finish_node();
}

pub(super) fn emit_operator_use(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    debug_assert!(item.payload_view().operator_use().is_some());
    i.state.start_node(kind.into());
    item.emit_remaining(&mut *i.state, SyntaxKind::Operator);
    i.state.finish_node();
}

/// An accepted contextual `with` outranks an otherwise selected dynamic word
/// operator, but remains a single already-owned Item.
pub(super) fn emit_with_keyword(i: &mut RewriteIn, item: Item) {
    let payload = item.payload_view();
    debug_assert!(
        payload.token_kind() == Some(TokenKind::Identifier) || payload.operator_use().is_some()
    );
    debug_assert_eq!(payload.spelling(), Some("with"));
    item.emit_remaining(&mut *i.state, SyntaxKind::WithKw);
}

pub(super) fn emit_token_item(i: &mut RewriteIn, item: Item) {
    let payload = item.payload_view();
    let kind = if payload.operator_use().is_some() {
        SyntaxKind::Operator
    } else {
        token_syntax_kind(
            payload
                .token_kind()
                .expect("only a lexical item can be emitted"),
        )
    };
    item.emit_remaining(&mut *i.state, kind);
}

/// Emits one committed interior literal Item while keeping accepted Yumark
/// quote prefixes outside the literal token kind.
pub(super) fn emit_literal_item(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    debug_assert!(item.leading_view().is_grammar_empty());
    debug_assert!(item.payload_view().token_kind().is_some());
    item.emit_remaining(&mut *i.state, kind);
}

/// Gate 3's isolated cell fixture emits one already-accepted segmented item
/// without changing the ordinary canonical emitters before lexical closure.
#[cfg(test)]
pub(super) fn emit_fragmented_item(i: &mut RewriteIn, item: Item) {
    let payload = item.payload_view();
    let kind = if payload.operator_use().is_some() {
        Some(SyntaxKind::Operator)
    } else {
        payload.token_kind().map(token_syntax_kind)
    };
    let is_eof = payload.is_eof();
    match kind {
        Some(kind) => item.emit_remaining(&mut *i.state, kind),
        None if is_eof => {
            let mut item = item;
            item.emit_eof_leading(&mut *i.state);
        }
        None => unreachable!("a boundary has a dedicated terminal adapter"),
    }
}

/// An accepted owner emits the pending item's trivia before its zero-width
/// missing slot.
pub(super) fn emit_missing(i: &mut RewriteIn, leading: LeadingTrivia) {
    emit_trivia(i, &leading);
    i.state.start_node(SyntaxKind::Missing.into());
    i.state.finish_node();
}

pub(super) fn emit_leading_trivia(i: &mut RewriteIn, trivia: &LeadingTrivia) {
    emit_trivia(i, trivia);
}

pub(super) fn emit_error_item(i: &mut RewriteIn, item: Item) {
    i.state.start_node(SyntaxKind::Error.into());
    emit_token_item(i, item);
    i.state.finish_node();
}

/// The enclosing owner emits accepted EOF trivia after receiving `End`.
pub(super) fn emit_end(builder: &mut GreenNodeBuilder<'static>, end: &mut End) {
    end.item.emit_eof_leading(builder);
}

fn emit_trivia(i: &mut RewriteIn, trivia: &LeadingTrivia) {
    emit_trivia_builder(&mut *i.state, trivia);
}

fn emit_trivia_builder(builder: &mut GreenNodeBuilder<'static>, trivia: &LeadingTrivia) {
    trivia.emit(builder);
}

fn token_syntax_kind(kind: TokenKind) -> SyntaxKind {
    match kind {
        TokenKind::Identifier => SyntaxKind::Identifier,
        TokenKind::SigilIdentifier => SyntaxKind::SigilIdentifier,
        TokenKind::Integer => SyntaxKind::Integer,
        TokenKind::Operator => unreachable!("operators have a selected dynamic role"),
        TokenKind::LParen => SyntaxKind::LParen,
        TokenKind::RParen => SyntaxKind::RParen,
        TokenKind::LBracket => SyntaxKind::LBracket,
        TokenKind::RBracket => SyntaxKind::RBracket,
        TokenKind::LBrace => SyntaxKind::LBrace,
        TokenKind::RBrace => SyntaxKind::RBrace,
        TokenKind::Comma => SyntaxKind::Comma,
        TokenKind::Semicolon => SyntaxKind::Semicolon,
        TokenKind::Dot => SyntaxKind::Dot,
        TokenKind::DotDot => SyntaxKind::DotDot,
        TokenKind::Arrow => SyntaxKind::Arrow,
        TokenKind::Colon => SyntaxKind::Colon,
        TokenKind::Equals => SyntaxKind::Equals,
        TokenKind::Forall => SyntaxKind::ForKw,
        TokenKind::EffectRowApostrophe => SyntaxKind::Apostrophe,
        TokenKind::PolymorphicVariantColon => SyntaxKind::Colon,
        TokenKind::PatternSymbolColon => SyntaxKind::Colon,
        TokenKind::PathSeparator => SyntaxKind::ColonColon,
        TokenKind::Pipe => SyntaxKind::Pipe,
        TokenKind::Unknown => SyntaxKind::Unknown,
    }
}
