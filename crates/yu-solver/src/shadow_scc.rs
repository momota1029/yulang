//! Default-off borrowed view of the already-frozen current F0–F2 SCC plan.
//!
//! This observes current declaration dependency topology and exact retained
//! source positions. It does not form a successor generalized interface,
//! assign Q/R, freshen a scheme, or execute F4/F5.

use crate::{
    ConstraintBatch, DefinitionOrderId, DefinitionUseId,
    scc::{SccComponentId, SccPlan},
};

/// Read-only view over one collected batch's existing SCC plan.
pub struct SccTopology<'a> {
    batch: &'a ConstraintBatch,
    plan: &'a SccPlan,
}

impl<'a> SccTopology<'a> {
    pub(crate) fn new(batch: &'a ConstraintBatch) -> Self {
        Self {
            batch,
            plan: batch.scc_plan(),
        }
    }

    /// Exact retained declaration position; no solving or topology query accounting.
    pub fn definition_source_position(
        &self,
        shadow: &yu_hir::shadow::ShadowArtifact,
        definition: SccDefinitionRef<'_>,
    ) -> Result<yu_hir::shadow::PositionId, SccSourceLookupError> {
        if !std::sync::Arc::ptr_eq(&self.batch.collection_artifact, &definition.id.artifact) {
            return Err(SccSourceLookupError::ForeignCollection);
        }
        let record = self
            .batch
            .definition_positions
            .get(definition.id)
            .and_then(|&position| self.batch.definitions.get(position))
            .ok_or(SccSourceLookupError::MissingIdentity)?;
        shadow
            .definition_source_position(&self.batch.hir, &record.root)
            .map_err(SccSourceLookupError::SourceIdentity)
    }

    /// Exact retained resolved-use position, available from the raw shadow artifact.
    pub fn use_source_position(
        &self,
        shadow: &yu_hir::shadow::ShadowArtifact,
        use_id: SccUseRef<'_>,
    ) -> Result<yu_hir::shadow::PositionId, SccSourceLookupError> {
        if !std::sync::Arc::ptr_eq(&self.batch.collection_artifact, &use_id.id.artifact) {
            return Err(SccSourceLookupError::ForeignCollection);
        }
        let record = self
            .batch
            .definition_use_positions
            .get(use_id.id)
            .and_then(|&position| self.batch.definition_uses.get(position))
            .ok_or(SccSourceLookupError::MissingIdentity)?;
        shadow
            .occurrence_source_position(&self.batch.hir, &record.occurrence)
            .map_err(SccSourceLookupError::SourceIdentity)
    }

    /// Components in the frozen dependency-first order.
    pub fn components(&self) -> impl Iterator<Item = SccComponentRef<'a>> + '_ {
        self.plan
            .components_in_dependency_first_order()
            .map(|id| SccComponentRef {
                plan: self.plan,
                id,
            })
    }

    /// Definitions in plan order, retaining their batch-branded identities.
    pub fn definitions(&self) -> impl Iterator<Item = SccDefinitionRef<'a>> + '_ {
        self.components().flat_map(SccComponentRef::members)
    }

    /// Resolve an identity obtained from this or another observer.
    pub fn component_of(
        &self,
        definition: SccDefinitionRef<'_>,
    ) -> Result<SccComponentRef<'a>, SccTopologyLookupError> {
        let id =
            self.plan
                .component_for_definition(definition.id)
                .map_err(|error| match error {
                    crate::CollectionLookupError::ArtifactMismatch => {
                        SccTopologyLookupError::ForeignArtifact
                    }
                    crate::CollectionLookupError::MissingIdentity => {
                        SccTopologyLookupError::MissingIdentity
                    }
                })?;
        Ok(SccComponentRef {
            plan: self.plan,
            id,
        })
    }
}

/// One component in the current frozen dependency graph.
#[derive(Clone, Copy)]
pub struct SccComponentRef<'a> {
    plan: &'a SccPlan,
    id: &'a SccComponentId,
}

impl<'a> SccComponentRef<'a> {
    /// Compare exact component identity, including its collection artifact.
    pub fn same_identity(self, other: Self) -> bool {
        self.id == other.id
    }

    /// The canonical definition is an identity handle, not a display name.
    pub fn canonical_definition(self) -> SccDefinitionRef<'a> {
        SccDefinitionRef {
            id: self.id.canonical_definition(),
        }
    }

    /// Members of this component, preserving the solver-owned identity brand.
    pub fn members(self) -> impl Iterator<Item = SccDefinitionRef<'a>> + 'a {
        self.plan
            .members(self.id)
            .expect("component handle belongs to its borrowed plan")
            .iter()
            .map(|id| SccDefinitionRef { id })
    }

    /// Resolved dependency occurrences whose endpoints are in this component.
    pub fn internal_uses(self) -> impl Iterator<Item = SccUseRef<'a>> + 'a {
        self.plan
            .internal_uses(self.id)
            .expect("component handle belongs to its borrowed plan")
            .iter()
            .map(|id| SccUseRef { id })
    }

    /// Resolved dependency occurrences entering this component from another.
    pub fn incoming_uses(self) -> impl Iterator<Item = SccUseRef<'a>> + 'a {
        self.plan
            .incoming_uses(self.id)
            .expect("component handle belongs to its borrowed plan")
            .iter()
            .map(|id| SccUseRef { id })
    }
}

/// Opaque definition identity borrowed from a collected batch.
#[derive(Clone, Copy)]
pub struct SccDefinitionRef<'a> {
    id: &'a DefinitionOrderId,
}

impl<'a> SccDefinitionRef<'a> {
    #[cfg(test)]
    pub(crate) fn collection_identity(self) -> &'a DefinitionOrderId {
        self.id
    }
    /// Compare exact identity, including the collection artifact brand.
    pub fn same_identity(self, other: Self) -> bool {
        self.id == other.id
    }

    /// Collection-local ordering metadata; never a cross-artifact identifier.
    pub fn collection_ordinal(self) -> u32 {
        self.id.ordinal()
    }
}

/// Opaque resolved-use identity borrowed from a collected batch.
#[derive(Clone, Copy)]
pub struct SccUseRef<'a> {
    id: &'a DefinitionUseId,
}

impl<'a> SccUseRef<'a> {
    #[cfg(test)]
    pub(crate) fn collection_identity(self) -> &'a DefinitionUseId {
        self.id
    }
    /// Compare exact identity, including the collection artifact brand.
    pub fn same_identity(self, other: Self) -> bool {
        self.id == other.id
    }

    /// Collection-local occurrence ordering metadata; not a source position.
    pub fn occurrence_ordinal(self) -> u32 {
        self.id.occurrence().ordinal()
    }
}

/// Failure to resolve an opaque definition handle in a topology view.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SccTopologyLookupError {
    ForeignArtifact,
    MissingIdentity,
}

/// Collection rejection is distinct from parse/source correspondence failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SccSourceLookupError {
    ForeignCollection,
    MissingIdentity,
    SourceIdentity(yu_hir::shadow::SourceIdentityError),
}
