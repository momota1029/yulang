//! Default-off observation of finalized current F5 member schemes.
//!
//! Q/R are current scheme-local binders, not source `beta` or `Slots`.
//! This borrowed view supplies no successor semantics or use-time freshening
//! observation. Typed endpoint/profile association remains unimplemented.

use crate::{
    ArtifactMismatch, ConstraintBatch, DefinitionRootId, HirOccurrenceId,
    PendingApplicationOccurrence, SolvedModule,
};
use yu_hir::NameResolution;
use yu_types::{ClosedValueScheme, ClosedValueSchemeView, NeutralValueView};

/// Syntactic operand position only; neither position assigns a callable role.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PendingApplicationOperandPosition {
    Callee,
    Argument,
}

/// A direct Name operand borrowed from one exact retained application row.
/// This is not a production dependency, a DefinitionUseId, or a typed use.
#[derive(Clone, Copy)]
pub struct PendingApplicationSourceUseRef<'a> {
    row: &'a PendingApplicationOccurrence,
    position: PendingApplicationOperandPosition,
    occurrence: &'a HirOccurrenceId,
    resolution: &'a NameResolution,
}

impl<'a> PendingApplicationSourceUseRef<'a> {
    pub fn application(self) -> &'a PendingApplicationOccurrence {
        self.row
    }

    pub fn position(self) -> PendingApplicationOperandPosition {
        self.position
    }

    pub fn enclosing_root(self) -> Option<&'a DefinitionRootId> {
        self.row.enclosing_root.as_ref()
    }

    pub fn occurrence(self) -> &'a HirOccurrenceId {
        self.occurrence
    }

    pub fn resolution(self) -> &'a NameResolution {
        self.resolution
    }

    pub fn same_identity(self, other: Self) -> bool {
        std::ptr::eq(self.row, other.row) && self.position == other.position
    }
}

impl ConstraintBatch {
    /// Borrows the HIR-owned nested carrier without creating application rows.
    pub fn shadow_captured_source(
        &self,
        root: &DefinitionRootId,
    ) -> Result<
        Option<&std::sync::Arc<yu_hir::shadow::ShadowArtifact>>,
        yu_hir::shadow::SourceIdentityError,
    > {
        self.hir.shadow_captured_source(root)
    }
    /// Direct Names in retained row order, then callee/argument order.
    /// Unresolved Names are retained; this inventory asserts no completeness
    /// and leaves each row's application typing premise unresolved.
    pub fn shadow_pending_application_source_uses(
        &self,
    ) -> impl Iterator<Item = PendingApplicationSourceUseRef<'_>> {
        pending_application_source_uses(self.pending_applications())
    }
}

impl SolvedModule {
    /// Borrows the same carrier through the retained immutable HIR module.
    pub fn shadow_captured_source(
        &self,
        root: &DefinitionRootId,
    ) -> Result<
        Option<&std::sync::Arc<yu_hir::shadow::ShadowArtifact>>,
        yu_hir::shadow::SourceIdentityError,
    > {
        self.hir.shadow_captured_source(root)
    }
    /// Borrow the same ordered direct Name inventory after collection is solved.
    /// Rows remain unresolved structural evidence owned by this frozen result.
    pub fn shadow_pending_application_source_uses(
        &self,
    ) -> impl Iterator<Item = PendingApplicationSourceUseRef<'_>> {
        pending_application_source_uses(self.pending_applications())
    }
}

fn pending_application_source_uses(
    rows: &[PendingApplicationOccurrence],
) -> impl Iterator<Item = PendingApplicationSourceUseRef<'_>> {
    rows.iter().flat_map(|row| {
        [
            (PendingApplicationOperandPosition::Callee, &row.callee),
            (PendingApplicationOperandPosition::Argument, &row.argument),
        ]
        .into_iter()
        .filter_map(move |(position, operand)| {
            operand.direct_name_resolution.as_ref().map(|resolution| {
                PendingApplicationSourceUseRef {
                    row,
                    position,
                    occurrence: &operand.occurrence,
                    resolution,
                }
            })
        })
    })
}

/// Borrowed inventory of the solve result's already finalized member schemes.
pub struct ClosedSchemes<'a> {
    solved: &'a SolvedModule,
}

impl<'a> ClosedSchemes<'a> {
    pub(crate) fn new(solved: &'a SolvedModule) -> Self {
        Self { solved }
    }

    /// Resolve an exact retained HIR root without production query accounting.
    pub fn for_root(
        &self,
        root: &DefinitionRootId,
    ) -> Result<ClosedSchemeRef<'a>, ArtifactMismatch> {
        if !self.solved.hir.owns_definition_root(root) {
            return Err(ArtifactMismatch);
        }
        let (owner, &position) = self
            .solved
            .root_scheme_positions
            .get_key_value(root)
            .expect("admitted root retains its exact scheme position");
        let scheme = self.solved.schemes[position]
            .as_ref()
            .expect("admitted root retains its finalized scheme");
        Ok(ClosedSchemeRef {
            solved: self.solved,
            owner,
            scheme,
        })
    }
}

/// Exact root and scheme owner for every endpoint and binder observed here.
#[derive(Clone, Copy)]
pub struct ClosedSchemeRef<'a> {
    solved: &'a SolvedModule,
    owner: &'a DefinitionRootId,
    scheme: &'a ClosedValueScheme,
}

impl<'a> ClosedSchemeRef<'a> {
    pub fn owner(self) -> &'a DefinitionRootId {
        self.owner
    }

    pub fn same_identity(self, other: Self) -> bool {
        self.owner == other.owner && std::ptr::eq(self.scheme, other.scheme)
    }

    pub fn definition_source_position(
        self,
        shadow: &yu_hir::shadow::ShadowArtifact,
    ) -> Result<yu_hir::shadow::PositionId, yu_hir::shadow::SourceIdentityError> {
        shadow.definition_source_position(&self.solved.hir, self.owner)
    }

    /// Existing closed endpoints, interpreted only in this owning scheme.
    /// Q/R ordinals in these views are local metadata, never source identities.
    pub fn endpoints(self) -> ClosedValueSchemeView<'a> {
        self.solved
            .closed_types
            .scheme_view(self.scheme)
            .expect("solved module retains the exact finalized arena")
    }

    pub fn quantifiers(self) -> impl Iterator<Item = QuantifierRef<'a>> + 'a {
        (0..self.endpoints().quantifier_count()).map(move |ordinal| QuantifierRef {
            scheme: self,
            ordinal,
        })
    }

    pub fn recursive_binders(self) -> impl Iterator<Item = RecursiveRef<'a>> + 'a {
        let view = self.endpoints();
        view.recursive_bounds()
            .iter()
            .map(move |bound| RecursiveRef {
                scheme: self,
                view,
                bound,
            })
    }
}

/// Q identity qualified by its exact root and finalized scheme.
#[derive(Clone, Copy)]
pub struct QuantifierRef<'a> {
    scheme: ClosedSchemeRef<'a>,
    ordinal: u32,
}

impl<'a> QuantifierRef<'a> {
    pub fn scheme(self) -> ClosedSchemeRef<'a> {
        self.scheme
    }
    pub fn ordinal(self) -> u32 {
        self.ordinal
    }
    pub fn same_identity(self, other: Self) -> bool {
        self.scheme.same_identity(other.scheme) && self.ordinal == other.ordinal
    }
}

/// R identity and both retained recursive endpoints in its owning scheme.
#[derive(Clone, Copy)]
pub struct RecursiveRef<'a> {
    scheme: ClosedSchemeRef<'a>,
    // Validate the scheme once per inventory, rather than once per bound query.
    view: ClosedValueSchemeView<'a>,
    bound: &'a yu_types::ClosedRecursiveBound,
}

impl<'a> RecursiveRef<'a> {
    pub fn scheme(self) -> ClosedSchemeRef<'a> {
        self.scheme
    }
    pub fn ordinal(self) -> u32 {
        self.bound.binder().ordinal()
    }
    pub fn same_identity(self, other: Self) -> bool {
        self.scheme.same_identity(other.scheme) && self.ordinal() == other.ordinal()
    }
    /// Lower and upper IDs borrow the arena retained by `scheme().endpoints()`.
    pub fn endpoints(self) -> (yu_types::PositiveValueId, yu_types::NegativeValueId) {
        let NeutralValueView::Bounds { lower, upper } = self
            .view
            .neutral_value(self.bound.bounds())
            .expect("finalized recursive bounds remain valid");
        (lower, upper)
    }
}
