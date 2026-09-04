//! Direct Rowan emission for already-accepted rewrite items.

use rowan::GreenNodeBuilder;

use crate::syntax_kind::SyntaxKind;

use super::{
    RewriteIn,
    driver::End,
    item::{Item, LeadingTrivia, Payload, TokenKind, TriviaKind},
};

pub(super) fn emit_identifier_core(i: &mut RewriteIn, item: Item) {
    let Payload::Token(token) = item.payload else {
        unreachable!("a core scanner always returns a token")
    };
    debug_assert_eq!(token.kind, TokenKind::Identifier);
    i.state.start_node(SyntaxKind::IdentifierExpression.into());
    emit_trivia(i, &item.leading);
    i.state.token(SyntaxKind::Identifier.into(), &token.text);
    i.state.finish_node();
}

pub(super) fn emit_integer_core(i: &mut RewriteIn, item: Item) {
    let Payload::Token(token) = item.payload else {
        unreachable!("a core scanner always returns a token")
    };
    debug_assert_eq!(token.kind, TokenKind::Integer);
    i.state.start_node(SyntaxKind::IntegerLiteral.into());
    emit_trivia(i, &item.leading);
    i.state.token(SyntaxKind::Integer.into(), &token.text);
    i.state.finish_node();
}

pub(super) fn emit_operator_use(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    let Payload::Operator(operator) = item.payload else {
        unreachable!("an operator use always owns an operator token")
    };
    i.state.start_node(kind.into());
    emit_trivia(i, &item.leading);
    i.state.token(SyntaxKind::Operator.into(), &operator.text);
    i.state.finish_node();
}

pub(super) fn emit_token_item(i: &mut RewriteIn, item: Item) {
    emit_trivia(i, &item.leading);
    match item.payload {
        Payload::Operator(operator) => {
            i.state.token(SyntaxKind::Operator.into(), &operator.text);
        }
        Payload::Token(token) => {
            let kind = match token.kind {
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
            };
            i.state.token(kind.into(), &token.text);
        }
        Payload::Eof => unreachable!("only a lexical item can be emitted"),
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
pub(super) fn emit_end(builder: &mut GreenNodeBuilder<'static>, end: &End) {
    emit_trivia_builder(builder, &end.item.leading);
}

fn emit_trivia(i: &mut RewriteIn, trivia: &LeadingTrivia) {
    emit_trivia_builder(&mut *i.state, trivia);
}

fn emit_trivia_builder(builder: &mut GreenNodeBuilder<'static>, trivia: &LeadingTrivia) {
    for part in &trivia.0 {
        let kind = match part.kind {
            TriviaKind::Whitespace => SyntaxKind::Whitespace,
            TriviaKind::Newline => SyntaxKind::Newline,
            TriviaKind::LineComment => SyntaxKind::LineComment,
            TriviaKind::BlockComment => SyntaxKind::BlockComment,
        };
        builder.token(kind.into(), &part.text);
    }
}
