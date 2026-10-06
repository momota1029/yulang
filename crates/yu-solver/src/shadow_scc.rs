//! Default-off borrowed view of the already-frozen current F0–F2 SCC plan.
//!
//! This observes current declaration dependency topology only. It does not
//! map those identities to `yu-hir` shadow IDs, form a successor generalized
//! interface, assign Q/R, freshen a scheme, or execute F4/F5.

use crate::{
    DefinitionOrderId, DefinitionUseId,
    scc::{SccComponentId, SccPlan},
};

/// Read-only view over one collected batch's existing SCC plan.
pub struct SccTopology<'a> {
    plan: &'a SccPlan,
}

impl<'a> SccTopology<'a> {
    pub(crate) fn new(plan: &'a SccPlan) -> Self {
        Self { plan }
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

impl SccDefinitionRef<'_> {
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

impl SccUseRef<'_> {
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
