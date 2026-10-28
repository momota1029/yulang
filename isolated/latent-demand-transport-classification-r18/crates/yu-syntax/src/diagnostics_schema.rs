//! Public schema payload for CST/environment-derived syntax diagnostics.

use crate::SyntaxKind;

/// The diagnostic class selected by the one CST/environment analysis walk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SyntaxDiagnosticKind {
    Missing,
    RawError,
    Invalid,
    ConflictingOperatorFixity,
}

/// The semantic child position of a mapped grammar slot.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GrammarSlotRole {
    Item,
    Separator,
    Close,
}

/// A mapped grammar slot, identified by its CST owner and semantic child role.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GrammarSlot {
    owner: SyntaxKind,
    role: GrammarSlotRole,
}

impl GrammarSlot {
    pub(crate) fn new(owner: SyntaxKind, role: GrammarSlotRole) -> Self {
        Self { owner, role }
    }

    pub fn owner(&self) -> SyntaxKind {
        self.owner
    }

    pub fn role(&self) -> GrammarSlotRole {
        self.role
    }
}

/// A schema-derived expectation for a mapped recovery slot.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExpectedSyntax {
    Expression,
    DelimitedSequenceSeparator,
    ClosingParenthesis,
    ClosingBracket,
    ClosingBrace,
}

/// Snapshot-local identity for one output of the shared analysis walk.
///
/// `occurrence_path` records child-with-token positions from the `Root` node.
/// It is an occurrence identity, unlike an ancestor-kind path: repeated green
/// subtrees and same-offset recovery children therefore remain distinct.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxDiagnosticIdentity {
    occurrence_path: Box<[u32]>,
    slot: Option<GrammarSlot>,
    kind: SyntaxDiagnosticKind,
    ordinal: u32,
}

impl SyntaxDiagnosticIdentity {
    pub(crate) fn new(
        occurrence_path: Box<[u32]>,
        slot: Option<GrammarSlot>,
        kind: SyntaxDiagnosticKind,
        ordinal: u32,
    ) -> Self {
        Self {
            occurrence_path,
            slot,
            kind,
            ordinal,
        }
    }

    pub fn occurrence_path(&self) -> &[u32] {
        &self.occurrence_path
    }

    pub fn slot(&self) -> Option<GrammarSlot> {
        self.slot
    }

    pub fn kind(&self) -> SyntaxDiagnosticKind {
        self.kind
    }

    pub fn ordinal(&self) -> u32 {
        self.ordinal
    }
}
