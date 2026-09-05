//! Direct Rowan emission for already-accepted rewrite items.

use rowan::GreenNodeBuilder;

use crate::syntax_kind::SyntaxKind;

use super::{
    RewriteIn,
    driver::End,
    item::{Item, LeadingTrivia, Payload, TokenKind, TriviaKind},
};

#[cfg(test)]
use super::item::{ForeignKind, ItemTextPart};

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

/// An accepted contextual `with` outranks an otherwise selected dynamic word
/// operator, but remains a single already-owned Item.
pub(super) fn emit_with_keyword(i: &mut RewriteIn, item: Item) {
    emit_trivia(i, &item.leading);
    match item.payload {
        Payload::Token(token) => {
            debug_assert_eq!(token.kind, TokenKind::Identifier);
            debug_assert_eq!(&*token.text, "with");
            i.state.token(SyntaxKind::WithKw.into(), &token.text);
        }
        Payload::Operator(operator) => {
            debug_assert_eq!(&*operator.text, "with");
            i.state.token(SyntaxKind::WithKw.into(), &operator.text);
        }
        Payload::Eof => unreachable!("an accepted contextual keyword is lexical"),
        Payload::Boundary(_) => unreachable!("Gate 2 boundaries cannot be emitted"),
    }
}

pub(super) fn emit_token_item(i: &mut RewriteIn, item: Item) {
    emit_trivia(i, &item.leading);
    match item.payload {
        Payload::Operator(operator) => {
            i.state.token(SyntaxKind::Operator.into(), &operator.text);
        }
        Payload::Token(token) => {
            let kind = token_syntax_kind(token.kind);
            i.state.token(kind.into(), &token.text);
        }
        Payload::Eof => unreachable!("only a lexical item can be emitted"),
        Payload::Boundary(_) => unreachable!("Gate 2 boundaries cannot be emitted"),
    }
}

/// Gate 3's isolated cell fixture emits one already-accepted segmented item
/// without changing the ordinary canonical emitters before lexical closure.
#[cfg(test)]
pub(super) fn emit_fragmented_item(i: &mut RewriteIn, item: &Item) {
    for part in item
        .fragmented_parts()
        .expect("the cell fixture accepts a segmented item")
    {
        let ordinary = match part.kind {
            ItemTextPart::LeadingTrivia(index) => trivia_syntax_kind(item.leading.0[index].kind),
            ItemTextPart::PayloadToken => {
                let Payload::Token(token) = &item.payload else {
                    unreachable!("a token part belongs to a token payload")
                };
                token_syntax_kind(token.kind)
            }
            ItemTextPart::PayloadOperator => SyntaxKind::Operator,
        };
        let mut cursor = 0;
        for split in part.foreign {
            let start = split.offset - part.physical.start;
            let end = start + split.length;
            if cursor < start {
                i.state.token(ordinary.into(), &part.text[cursor..start]);
            }
            let foreign = match split.kind {
                ForeignKind::YmQuotePrefix => SyntaxKind::YmQuotePrefix,
            };
            i.state.token(foreign.into(), &part.text[start..end]);
            cursor = end;
        }
        if cursor < part.text.len() {
            i.state.token(ordinary.into(), &part.text[cursor..]);
        }
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
        let kind = trivia_syntax_kind(part.kind);
        builder.token(kind.into(), &part.text);
    }
}

fn trivia_syntax_kind(kind: TriviaKind) -> SyntaxKind {
    match kind {
        TriviaKind::Whitespace => SyntaxKind::Whitespace,
        TriviaKind::Newline => SyntaxKind::Newline,
        TriviaKind::LineComment => SyntaxKind::LineComment,
        TriviaKind::BlockComment => SyntaxKind::BlockComment,
    }
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
