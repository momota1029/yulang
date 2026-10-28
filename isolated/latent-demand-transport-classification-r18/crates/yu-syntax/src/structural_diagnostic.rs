//! Shadow CST-derived structural diagnostics.
//!
//! One whole-tree walk over a Rowan syntax tree derives the structural recovery
//! occurrences (`Missing`, maximal same-slot raw `Error` groups, structured
//! `Invalid`) from the CST alone. It never consults the temporary parser
//! recovery ledger, replays parsing, relexes `Error` text, or creates synthetic
//! recovery nodes.
//!
//! A bounded set of mapped catalog rows supplies precise slot and expectation
//! information; every other occurrence falls back to a deterministic generic
//! structural diagnostic carrying only CST-derived facts. The generic fallback
//! is total over recovery structure, so an unmapped slot never suppresses a
//! diagnosis or blocks the walk.
//!
//! This module owns the CST half of the final diagnostic publication path.

use std::ops::Range;

use rowan::NodeOrToken;

use crate::{
    diagnostics_schema::{
        ExpectedSyntax as SchemaExpectedSyntax, GrammarSlot, GrammarSlotRole,
        SyntaxDiagnosticIdentity, SyntaxDiagnosticKind,
    },
    expression::delimited::DelimitedOwner,
    syntax_kind::{SyntaxKind, SyntaxNode, SyntaxToken},
};

/// The structural recovery kind derived from the CST.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructuralKind {
    /// A zero-width `Missing` node.
    Missing,
    /// A maximal run of adjacent raw `Error` tokens at one immediate parent.
    ErrorGroup,
    /// A structured `Invalid` node, reported over its own nonempty extent.
    Invalid,
}

impl StructuralKind {
    fn diagnostic_kind(self) -> SyntaxDiagnosticKind {
        match self {
            Self::Missing => SyntaxDiagnosticKind::Missing,
            Self::ErrorGroup => SyntaxDiagnosticKind::RawError,
            Self::Invalid => SyntaxDiagnosticKind::Invalid,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum StructuralProjectionError {
    OrdinalExhausted,
    StructuralInvariant,
}

/// Precise schema information for a mapped catalog occurrence.
///
/// Only a mapped bounded catalog row supplies this. Everything absent here is
/// the conservative generic fallback, not a collapsed or invented alternative.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CatalogSlot {
    slot: GrammarSlot,
    expectations: Box<[SchemaExpectedSyntax]>,
    primary: usize,
}

impl CatalogSlot {
    fn new(slot: GrammarSlot, expected: SchemaExpectedSyntax) -> Self {
        Self {
            slot,
            expectations: Box::from([expected]),
            primary: 0,
        }
    }

    pub(crate) fn expectations(&self) -> &[SchemaExpectedSyntax] {
        &self.expectations
    }

    pub(crate) fn primary(&self) -> usize {
        self.primary
    }
}

/// One CST-derived structural diagnostic occurrence.
///
/// `path` is the ancestor kind chain from the tree root to the occurrence's
/// immediate structural parent. `slot` is present only for a mapped catalog
/// occurrence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructuralDiagnostic {
    kind: StructuralKind,
    range: Range<usize>,
    ordinal: u32,
    path: Box<[SyntaxKind]>,
    occurrence_path: Box<[u32]>,
    slot: Option<CatalogSlot>,
    direct_root_ordinal: Option<u32>,
}

impl StructuralDiagnostic {
    pub fn kind(&self) -> StructuralKind {
        self.kind
    }

    pub fn range(&self) -> &Range<usize> {
        &self.range
    }

    /// The source/preorder ordinal that keeps even same-slot same-offset
    /// encounters distinct.
    pub fn ordinal(&self) -> u32 {
        self.ordinal
    }

    pub fn identity(&self) -> SyntaxDiagnosticIdentity {
        SyntaxDiagnosticIdentity::new(
            self.occurrence_path.clone(),
            self.slot.as_ref().map(|slot| slot.slot),
            self.kind.diagnostic_kind(),
            self.ordinal,
        )
    }

    /// Schema expectations are present only for a mapped occurrence.
    pub fn expectations(&self) -> Option<&[SchemaExpectedSyntax]> {
        self.slot.as_ref().map(CatalogSlot::expectations)
    }

    pub fn primary_expectation(&self) -> Option<usize> {
        self.slot.as_ref().map(CatalogSlot::primary)
    }

    pub fn path(&self) -> &[SyntaxKind] {
        &self.path
    }

    /// The immediate structural parent kind.
    pub fn parent(&self) -> SyntaxKind {
        *self
            .path
            .last()
            .expect("every structural occurrence has a parent")
    }

    pub fn direct_root_ordinal(&self) -> Option<u32> {
        self.direct_root_ordinal
    }
}

/// Convenience whole-tree collector for tests and tools.
#[cfg(test)]
pub(crate) fn collect(root: &SyntaxNode) -> Vec<StructuralDiagnostic> {
    try_collect(root).expect("structural diagnostic adapter preserves the legacy total contract")
}

pub(crate) fn try_collect(
    root: &SyntaxNode,
) -> Result<Vec<StructuralDiagnostic>, StructuralProjectionError> {
    let mut occurrences = Vec::new();
    walk(root, &mut |occurrence| occurrences.push(occurrence))?;
    Ok(occurrences)
}

/// Callback-based interpretation over one whole Rowan tree.
///
/// The walk visits every syntax child in deterministic source/preorder order,
/// including children whose later semantic analysis would fail.
pub(crate) fn walk(
    root: &SyntaxNode,
    visit: &mut impl FnMut(StructuralDiagnostic),
) -> Result<(), StructuralProjectionError> {
    walk_with_node_entry(root, &mut |_, _, _| false, visit)
}

pub(crate) fn walk_with_node_entry(
    root: &SyntaxNode,
    enter: &mut impl FnMut(&SyntaxNode, &[u32], u32) -> bool,
    visit: &mut impl FnMut(StructuralDiagnostic),
) -> Result<(), StructuralProjectionError> {
    let mut walk = Walk::new(enter, visit);
    let mut path = vec![root.kind()];
    let mut occurrence_path = Vec::new();
    walk.visit(root, &mut path, &mut occurrence_path, None)
}

struct Walk<'a> {
    enter: &'a mut dyn FnMut(&SyntaxNode, &[u32], u32) -> bool,
    visit: &'a mut dyn FnMut(StructuralDiagnostic),
    ordinal: u32,
}

impl<'a> Walk<'a> {
    fn new(
        enter: &'a mut dyn FnMut(&SyntaxNode, &[u32], u32) -> bool,
        visit: &'a mut dyn FnMut(StructuralDiagnostic),
    ) -> Self {
        Self {
            enter,
            visit,
            ordinal: 0,
        }
    }

    fn visit(
        &mut self,
        node: &SyntaxNode,
        path: &mut Vec<SyntaxKind>,
        occurrence_path: &mut Vec<u32>,
        direct_root_ordinal: Option<u32>,
    ) -> Result<(), StructuralProjectionError> {
        if (self.enter)(node, occurrence_path, self.ordinal) {
            self.ordinal = self
                .ordinal
                .checked_add(1)
                .ok_or(StructuralProjectionError::OrdinalExhausted)?;
        }
        let children = node.children_with_tokens().collect::<Vec<_>>();
        let mut run: Option<(Range<usize>, usize)> = None;
        let mut next_root_ordinal = 0u32;
        for (index, child) in children.iter().enumerate() {
            match child {
                NodeOrToken::Node(child) => {
                    self.flush(&mut run, path, occurrence_path, direct_root_ordinal)?;
                    let child_root_ordinal = if node.kind() == SyntaxKind::Root {
                        let ordinal = next_root_ordinal;
                        next_root_ordinal = ordinal
                            .checked_add(1)
                            .ok_or(StructuralProjectionError::OrdinalExhausted)?;
                        Some(ordinal)
                    } else {
                        direct_root_ordinal
                    };
                    match child.kind() {
                        SyntaxKind::Missing => {
                            let range = byte_range(child.text_range());
                            if !range.is_empty() {
                                return Err(StructuralProjectionError::StructuralInvariant);
                            }
                            let slot = precise_missing(path, &children, index);
                            self.push(
                                StructuralKind::Missing,
                                range,
                                path,
                                occurrence_path,
                                index,
                                slot,
                                direct_root_ordinal,
                            )?;
                        }
                        SyntaxKind::Invalid => {
                            let range = byte_range(child.text_range());
                            if range.is_empty() {
                                return Err(StructuralProjectionError::StructuralInvariant);
                            }
                            self.push(
                                StructuralKind::Invalid,
                                range,
                                path,
                                occurrence_path,
                                index,
                                None,
                                direct_root_ordinal,
                            )?;
                            path.push(SyntaxKind::Invalid);
                            occurrence_path.push(index as u32);
                            self.visit(child, path, occurrence_path, child_root_ordinal)?;
                            occurrence_path.pop();
                            path.pop();
                        }
                        SyntaxKind::Error => {
                            return Err(StructuralProjectionError::StructuralInvariant);
                        }
                        kind => {
                            path.push(kind);
                            occurrence_path.push(index as u32);
                            self.visit(child, path, occurrence_path, child_root_ordinal)?;
                            occurrence_path.pop();
                            path.pop();
                        }
                    }
                }
                NodeOrToken::Token(token) if token.kind() == SyntaxKind::Error => {
                    let range = byte_range(token.text_range());
                    if token.text().is_empty() || range.end - range.start != token.text().len() {
                        return Err(StructuralProjectionError::StructuralInvariant);
                    }
                    let adjacent = run.as_ref().is_some_and(|(run, _)| run.end == range.start);
                    if !adjacent {
                        self.flush(&mut run, path, occurrence_path, direct_root_ordinal)?;
                    }
                    match &mut run {
                        Some((run, _)) => run.end = range.end,
                        None => run = Some((range, index)),
                    }
                }
                _ => self.flush(&mut run, path, occurrence_path, direct_root_ordinal)?,
            }
        }
        self.flush(&mut run, path, occurrence_path, direct_root_ordinal)
    }

    fn flush(
        &mut self,
        run: &mut Option<(Range<usize>, usize)>,
        path: &[SyntaxKind],
        occurrence_path: &[u32],
        direct_root_ordinal: Option<u32>,
    ) -> Result<(), StructuralProjectionError> {
        if let Some((range, index)) = run.take() {
            let slot = precise_error_group(path);
            self.push(
                StructuralKind::ErrorGroup,
                range,
                path,
                occurrence_path,
                index,
                slot,
                direct_root_ordinal,
            )?;
        }
        Ok(())
    }

    fn push(
        &mut self,
        kind: StructuralKind,
        range: Range<usize>,
        path: &[SyntaxKind],
        parent_occurrence_path: &[u32],
        child_index: usize,
        slot: Option<CatalogSlot>,
        direct_root_ordinal: Option<u32>,
    ) -> Result<(), StructuralProjectionError> {
        let ordinal = self.ordinal;
        self.ordinal = ordinal
            .checked_add(1)
            .ok_or(StructuralProjectionError::OrdinalExhausted)?;
        let mut occurrence_path = parent_occurrence_path.to_vec();
        occurrence_path.push(
            u32::try_from(child_index).map_err(|_| StructuralProjectionError::OrdinalExhausted)?,
        );
        (self.visit)(StructuralDiagnostic {
            kind,
            range,
            ordinal,
            path: path.into(),
            occurrence_path: occurrence_path.into(),
            slot,
            direct_root_ordinal,
        });
        Ok(())
    }
}

/// Precise `Missing` slot for the mapped expression-delimited row.
///
/// Identity is the owner plus the ordered child phase, exactly as the catalog
/// row states: a direct empty `Missing` before a leading comma is `Item`;
/// between two admitted items with no separator it is `Separator`; a final
/// direct `Missing` after one admitted item is the terminal `Close`. Any other
/// placement is left to the generic fallback.
///
/// Trivia is not an ordered child phase, so the phase is read from the nearest
/// structural sibling rather than a literal adjacent element. This generalizes
/// the trivia-free audited witnesses to their trivia-interleaved forms, and the
/// resulting role always equals the slot the owner actually emitted.
fn precise_missing(
    path: &[SyntaxKind],
    children: &[NodeOrToken<SyntaxNode, SyntaxToken>],
    index: usize,
) -> Option<CatalogSlot> {
    let owner = missing_row_owner(*path.last()?)?;
    match next_significant(children, index) {
        Some(SyntaxKind::Comma) => Some(item_slot(owner)),
        Some(kind) if kind == admitted_item_kind(owner) => (previous_significant(children, index)
            == Some(admitted_item_kind(owner)))
        .then(|| separator_slot(owner)),
        Some(_) => None,
        None => Some(close_slot(owner)),
    }
}

/// Precise raw `Error` group slot for the mapped expression-delimited row.
///
/// A direct owner `Error` group projects the owner's `Item` expectation. A
/// group under `ExpressionDelimitedSeparator` or
/// `ExpressionDelimitedForeignClose` projects the owner's `Separator` or
/// matching-close expectation.
fn precise_error_group(path: &[SyntaxKind]) -> Option<CatalogSlot> {
    match *path.last()? {
        SyntaxKind::ExpressionDelimitedSeparator => {
            Some(separator_slot(raw_row_owner(grandparent(path)?)?))
        }
        SyntaxKind::ExpressionDelimitedForeignClose => {
            Some(close_slot(raw_row_owner(grandparent(path)?)?))
        }
        kind => raw_row_owner(kind).map(item_slot),
    }
}

fn item_slot(owner: DelimitedOwner) -> CatalogSlot {
    CatalogSlot::new(
        GrammarSlot::new(owner_kind(owner), GrammarSlotRole::Item),
        SchemaExpectedSyntax::Expression,
    )
}

fn separator_slot(owner: DelimitedOwner) -> CatalogSlot {
    CatalogSlot::new(
        GrammarSlot::new(owner_kind(owner), GrammarSlotRole::Separator),
        SchemaExpectedSyntax::DelimitedSequenceSeparator,
    )
}

fn close_slot(owner: DelimitedOwner) -> CatalogSlot {
    CatalogSlot::new(
        GrammarSlot::new(owner_kind(owner), GrammarSlotRole::Close),
        match owner {
            DelimitedOwner::Index => SchemaExpectedSyntax::ClosingBracket,
            DelimitedOwner::ProjectionRecord => SchemaExpectedSyntax::ClosingBrace,
            DelimitedOwner::Parenthesized
            | DelimitedOwner::Call
            | DelimitedOwner::ProjectionTuple => SchemaExpectedSyntax::ClosingParenthesis,
        },
    )
}

/// The owners whose direct ordinary `Missing` slots the mapped Missing row
/// covers. Projection tails have a separate bounded row and stay generic here.
fn missing_row_owner(kind: SyntaxKind) -> Option<DelimitedOwner> {
    match kind {
        SyntaxKind::ParenthesizedExpression => Some(DelimitedOwner::Parenthesized),
        SyntaxKind::CallTail => Some(DelimitedOwner::Call),
        SyntaxKind::IndexTail => Some(DelimitedOwner::Index),
        _ => None,
    }
}

/// The five owners whose raw `Error` group slots the mapped raw row covers.
fn raw_row_owner(kind: SyntaxKind) -> Option<DelimitedOwner> {
    match kind {
        SyntaxKind::ParenthesizedExpression => Some(DelimitedOwner::Parenthesized),
        SyntaxKind::CallTail => Some(DelimitedOwner::Call),
        SyntaxKind::IndexTail => Some(DelimitedOwner::Index),
        SyntaxKind::ProjectionTupleTail => Some(DelimitedOwner::ProjectionTuple),
        SyntaxKind::ProjectionRecordTail => Some(DelimitedOwner::ProjectionRecord),
        _ => None,
    }
}

fn admitted_item_kind(owner: DelimitedOwner) -> SyntaxKind {
    match owner {
        DelimitedOwner::Index => SyntaxKind::IndexItem,
        DelimitedOwner::Parenthesized
        | DelimitedOwner::Call
        | DelimitedOwner::ProjectionTuple
        | DelimitedOwner::ProjectionRecord => SyntaxKind::OperatorChain,
    }
}

fn grandparent(path: &[SyntaxKind]) -> Option<SyntaxKind> {
    path.len()
        .checked_sub(2)
        .and_then(|index| path.get(index))
        .copied()
}

fn next_significant(
    children: &[NodeOrToken<SyntaxNode, SyntaxToken>],
    index: usize,
) -> Option<SyntaxKind> {
    children[index + 1..]
        .iter()
        .find(|child| !is_trivia(child.kind()))
        .map(|child| child.kind())
}

fn previous_significant(
    children: &[NodeOrToken<SyntaxNode, SyntaxToken>],
    index: usize,
) -> Option<SyntaxKind> {
    children[..index]
        .iter()
        .rev()
        .find(|child| !is_trivia(child.kind()))
        .map(|child| child.kind())
}

fn is_trivia(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Whitespace
            | SyntaxKind::Newline
            | SyntaxKind::LineComment
            | SyntaxKind::BlockComment
    )
}

fn owner_kind(owner: DelimitedOwner) -> SyntaxKind {
    match owner {
        DelimitedOwner::Parenthesized => SyntaxKind::ParenthesizedExpression,
        DelimitedOwner::Call => SyntaxKind::CallTail,
        DelimitedOwner::Index => SyntaxKind::IndexTail,
        DelimitedOwner::ProjectionTuple => SyntaxKind::ProjectionTupleTail,
        DelimitedOwner::ProjectionRecord => SyntaxKind::ProjectionRecordTail,
    }
}

fn byte_range(range: rowan::TextRange) -> Range<usize> {
    usize::from(range.start())..usize::from(range.end())
}
