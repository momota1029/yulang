use std::ops::Range;

use crate::input::checked_root_range;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ItemIdentity {
    pub(super) ordinal: u64,
    pub(super) byte_offset: usize,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct LogicalPosition {
    pub(super) line: usize,
    pub(super) column: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceSpan<'source> {
    pub(super) text: &'source str,
    pub(super) range: Range<usize>,
}

impl<'source> SourceSpan<'source> {
    pub(super) fn checked(root: &'source str, text: &'source str) -> Self {
        let range = checked_root_range(root, text)
            .expect("a rewrite item span must belong to the parse root");
        Self { text, range }
    }

    pub(super) fn empty_at(root: &'source str, offset: usize) -> Self {
        Self::checked(root, &root[offset..offset])
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Delimiter {
    Parenthesis,
    Bracket,
    Brace,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct LayoutEvidence {
    pub(super) baseline: usize,
    pub(super) observed_indent: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum StopKind {
    Comma,
    Semicolon,
    Colon,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Boundary {
    Close(Delimiter),
    BorrowedClose(Delimiter),
    Dedent(LayoutEvidence),
    Stop(StopKind),
    EofAfterTrivia,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum BinaryOperator {
    Add,
    Multiply,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Level(pub(super) u8);

impl Level {
    pub(super) const OUTER: Self = Self(0);
    pub(super) const PREFIX: Self = Self(30);
}

impl BinaryOperator {
    pub(super) fn left_level(self) -> Level {
        match self {
            Self::Add => Level(10),
            Self::Multiply => Level(20),
        }
    }

    pub(super) fn right_level(self) -> Level {
        Level(self.left_level().0 + 1)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NudKind {
    Atom,
    Prefix,
    OpenParenthesis,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum MalformedTailKind {
    Adjacent,
    Spaced,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TailKind {
    Binary(BinaryOperator),
    CallOpen,
    Field,
    Path,
    Deferred,
    MlNud(NudKind),
    Malformed(MalformedTailKind),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TokenKind {
    Identifier,
    Integer,
    PrefixOperator,
    InfixOperator(BinaryOperator),
    LeftParenthesis,
    RightParenthesis,
    Dot,
    ColonColon,
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Token<'source> {
    pub(super) kind: TokenKind,
    pub(super) lexeme: SourceSpan<'source>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Payload<'source> {
    Tail {
        kind: TailKind,
        token: Token<'source>,
    },
    Boundary(Boundary),
}

/// One completed logical item. Its trivia, identity, extent and logical
/// position survive owner handoff and boundary resumption unchanged.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Item<'source> {
    pub(super) identity: ItemIdentity,
    pub(super) leading_trivia: SourceSpan<'source>,
    pub(super) payload: Payload<'source>,
    pub(super) lexical_boundary_token: Option<Token<'source>>,
    pub(super) extent: Range<usize>,
    pub(super) logical_position: LogicalPosition,
}

impl Item<'_> {
    pub(super) fn tail_kind(&self) -> Option<TailKind> {
        match self.payload {
            Payload::Tail { kind, .. } => Some(kind),
            Payload::Boundary(_) => None,
        }
    }
}
