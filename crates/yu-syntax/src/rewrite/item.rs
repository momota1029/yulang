#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct LeadingTrivia(pub(super) Box<[Trivia]>);

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Trivia {
    pub(super) kind: TriviaKind,
    pub(super) text: Box<str>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TriviaKind {
    Whitespace,
    Newline,
    LineComment,
    BlockComment,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TokenKind {
    Identifier,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Token {
    pub(super) kind: TokenKind,
    pub(super) text: Box<str>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Payload {
    Token(Token),
    Eof,
}

/// A scanned logical item owns every byte it retains.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Item {
    pub(super) leading: LeadingTrivia,
    pub(super) payload: Payload,
}
