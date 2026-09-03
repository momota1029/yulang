use std::ops::{Deref, Range};

use crate::{input::checked_root_range, operator::BindingPower};

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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TriviaPartKind {
    Whitespace,
    Newline,
    LineComment,
    BlockComment,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct TriviaPart {
    pub(super) kind: TriviaPartKind,
    pub(super) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LeadingTrivia<'source> {
    pub(super) span: SourceSpan<'source>,
    pub(super) parts: Vec<TriviaPart>,
}

impl<'source> LeadingTrivia<'source> {
    pub(super) fn empty_at(root: &'source str, offset: usize) -> Self {
        Self {
            span: SourceSpan::empty_at(root, offset),
            parts: Vec::new(),
        }
    }
}

impl<'source> Deref for LeadingTrivia<'source> {
    type Target = SourceSpan<'source>;

    fn deref(&self) -> &Self::Target {
        &self.span
    }
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Level {
    Outer,
    Binding(BindingPower),
}

impl Level {
    pub(super) const OUTER: Self = Self::Outer;

    pub(super) fn binding(power: BindingPower) -> Self {
        Self::Binding(power)
    }

    #[cfg(test)]
    pub(super) fn scalar(value: i8) -> Self {
        Self::binding(BindingPower::scalar(value))
    }

    pub(super) fn reads(&self, left: &BindingPower) -> bool {
        match self {
            Self::Outer => true,
            Self::Binding(threshold) => left >= threshold,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum NudKind {
    Atom,
    Prefix { right: BindingPower },
    Nullfix,
    OpenParenthesis,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum MalformedTailKind {
    Adjacent,
    Spaced,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum TailKind {
    Infix {
        left: BindingPower,
        right: BindingPower,
    },
    Suffix {
        left: BindingPower,
    },
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
    DynamicOperator,
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
    pub(super) leading_trivia: LeadingTrivia<'source>,
    pub(super) payload: Payload<'source>,
    pub(super) lexical_boundary_token: Option<Token<'source>>,
    pub(super) extent: Range<usize>,
    pub(super) logical_position: LogicalPosition,
}

impl Item<'_> {
    pub(super) fn tail_kind(&self) -> Option<TailKind> {
        match &self.payload {
            Payload::Tail { kind, .. } => Some(kind.clone()),
            Payload::Boundary(_) => None,
        }
    }
}
