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
    /// Retain current use-time evidence without establishing successor instantiation.
    #[cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]
    pub fn pending_use_instantiation<'s>(
        &self,
        solved: &'s crate::SolvedModule,
        occurrence: SccUseRef<'_>,
    ) -> Result<PendingUseInstantiationRef<'a, 's>, PendingUseInstantiationLookupError> {
        let (parent, target) = self
            .use_definitions(occurrence)
            .map_err(PendingUseInstantiationLookupError::Topology)?;
        let component = self
            .component_of(target)
            .map_err(PendingUseInstantiationLookupError::Topology)?;
        let current_scheme = self
            .use_closed_scheme(solved, occurrence)
            .map_err(PendingUseInstantiationLookupError::ClosedScheme)?;
        let record =
            &self.batch.definition_uses[self.batch.definition_use_positions[occurrence.id]];
        Ok(PendingUseInstantiationRef {
            occurrence: SccUseRef { id: &record.id },
            parent,
            target,
            generalization: component.pending_successor_generalization(),
            current_scheme,
            current_route: solved
                .shadow_current_use_route(occurrence.id)
                .map(|(route, store)| CurrentUseRouteRef { route, store }),
            closed_route: !self
                .component_of(parent)
                .map_err(PendingUseInstantiationLookupError::Topology)?
                .same_identity(component),
        })
    }

    /// Join an exact retained use to its target's finalized current-local scheme.
    #[cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]
    pub fn use_closed_scheme<'s>(
        &self,
        solved: &'s crate::SolvedModule,
        occurrence: SccUseRef<'_>,
    ) -> Result<crate::shadow_f5::ClosedSchemeRef<'s>, SccClosedSchemeLookupError> {
        if !std::sync::Arc::ptr_eq(&self.batch.collection_artifact, &occurrence.id.artifact)
            || !std::sync::Arc::ptr_eq(&self.batch.collection_artifact, &solved.collection_artifact)
        {
            return Err(SccClosedSchemeLookupError::ForeignCollection);
        }
        let record = self
            .batch
            .definition_use_positions
            .get(occurrence.id)
            .and_then(|&position| self.batch.definition_uses.get(position))
            .ok_or(SccClosedSchemeLookupError::MissingIdentity)?;
        self.definition_closed_scheme(solved, SccDefinitionRef { id: &record.target })
    }

    /// Join a current member to its exact finalized current-local scheme.
    /// This does not identify Q/R with successor interfaces or source slots.
    #[cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]
    pub fn definition_closed_scheme<'s>(
        &self,
        solved: &'s crate::SolvedModule,
        definition: SccDefinitionRef<'_>,
    ) -> Result<crate::shadow_f5::ClosedSchemeRef<'s>, SccClosedSchemeLookupError> {
        if !std::sync::Arc::ptr_eq(&self.batch.collection_artifact, &definition.id.artifact)
            || !std::sync::Arc::ptr_eq(&self.batch.collection_artifact, &solved.collection_artifact)
        {
            return Err(SccClosedSchemeLookupError::ForeignCollection);
        }
        let record = self
            .batch
            .definition_positions
            .get(definition.id)
            .and_then(|&position| self.batch.definitions.get(position))
            .ok_or(SccClosedSchemeLookupError::MissingIdentity)?;
        solved
            .shadow_closed_schemes()
            .for_root(&record.root)
            .map_err(|_| SccClosedSchemeLookupError::ForeignRoot)
    }

    /// Exact structural correspondence only; absence does not remove an SCC member.
    pub fn definition_shadow_ref<'s>(
        &self,
        crosswalk: &yu_hir::shadow::SkeletonSourceCrosswalk<'s>,
        definition: SccDefinitionRef<'_>,
    ) -> Result<
        Option<(&'s yu_hir::shadow::Expression, &'s yu_hir::shadow::BinderId)>,
        SccShadowLookupError,
    > {
        let position = self
            .definition_source_position(crosswalk.artifact(), definition)
            .map_err(SccShadowLookupError::Source)?;
        crosswalk
            .definition_at_position(&position)
            .map_err(SccShadowLookupError::Shadow)
    }

    /// Retains the collection use even when no skeleton use represents it.
    pub fn use_shadow_ref<'s>(
        &self,
        crosswalk: &yu_hir::shadow::SkeletonSourceCrosswalk<'s>,
        occurrence: SccUseRef<'_>,
    ) -> Result<Option<&'s yu_hir::shadow::UseId>, SccShadowLookupError> {
        let position = self
            .use_source_position(crosswalk.artifact(), occurrence)
            .map_err(SccShadowLookupError::Source)?;
        crosswalk
            .use_at_position(&position)
            .map_err(SccShadowLookupError::Shadow)
    }
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

    /// Exact retained occurrences leaving this component for another component.
    /// Validate the complete inventory before returning the borrowed iterator;
    /// an absent endpoint must not appear to be an absent dependency.
    pub fn outgoing_uses(
        &self,
        component: SccComponentRef<'_>,
    ) -> Result<impl Iterator<Item = SccUseRef<'a>> + '_, SccTopologyLookupError> {
        let component = self.component_of(component.canonical_definition())?;
        for record in &self.batch.definition_uses {
            self.use_definitions(SccUseRef { id: &record.id })?;
        }
        Ok(self.batch.definition_uses.iter().filter_map(move |record| {
            let parent = self
                .component_of(SccDefinitionRef { id: &record.parent })
                .expect("outgoing inventory endpoints were validated");
            let target = self
                .component_of(SccDefinitionRef { id: &record.target })
                .expect("outgoing inventory endpoints were validated");
            (parent.same_identity(component) && !target.same_identity(component))
                .then_some(SccUseRef { id: &record.id })
        }))
    }

    /// Exact retained `(parent, target)` definitions of one resolved use.
    /// Both endpoints must belong to this batch's frozen plan.
    pub fn use_definitions(
        &self,
        occurrence: SccUseRef<'_>,
    ) -> Result<(SccDefinitionRef<'a>, SccDefinitionRef<'a>), SccTopologyLookupError> {
        if !std::sync::Arc::ptr_eq(&self.batch.collection_artifact, &occurrence.id.artifact) {
            return Err(SccTopologyLookupError::ForeignArtifact);
        }
        let record = self
            .batch
            .definition_use_positions
            .get(occurrence.id)
            .and_then(|&position| self.batch.definition_uses.get(position))
            .ok_or(SccTopologyLookupError::MissingIdentity)?;
        let parent = SccDefinitionRef { id: &record.parent };
        let target = SccDefinitionRef { id: &record.target };
        self.component_of(parent)?;
        self.component_of(target)?;
        Ok((parent, target))
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
    /// Retain this current component while successor generalization is unresolved.
    /// Empty uses or absent shadow syntax do not discharge the premise.
    pub fn pending_successor_generalization(self) -> PendingSccGeneralizationRef<'a> {
        PendingSccGeneralizationRef { component: self }
    }

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

/// Structural carrier of a current component, not a generalized interface.
/// This asserts neither eligibility nor equality with a successor generalized SCC.
#[derive(Clone, Copy)]
pub struct PendingSccGeneralizationRef<'a> {
    component: SccComponentRef<'a>,
}

impl<'a> PendingSccGeneralizationRef<'a> {
    pub fn component(self) -> SccComponentRef<'a> {
        self.component
    }

    /// The semantic rule remains unresolved for every current component.
    pub fn premise(self) -> PendingSccGeneralizationPremise {
        PendingSccGeneralizationPremise::SuccessorGeneralizationRuleUnresolved
    }
}

/// No successor eligibility, binder arrangement, or freshening is established.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PendingSccGeneralizationPremise {
    SuccessorGeneralizationRuleUnresolved,
}

/// Borrowed current evidence; internal recursive uses have the same open premises.
#[cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]
#[derive(Clone, Copy)]
pub struct PendingUseInstantiationRef<'a, 's> {
    occurrence: SccUseRef<'a>,
    parent: SccDefinitionRef<'a>,
    target: SccDefinitionRef<'a>,
    generalization: PendingSccGeneralizationRef<'a>,
    current_scheme: crate::shadow_f5::ClosedSchemeRef<'s>,
    current_route: Option<CurrentUseRouteRef<'s>>,
    closed_route: bool,
}

#[cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]
impl<'a, 's> PendingUseInstantiationRef<'a, 's> {
    pub fn occurrence(self) -> SccUseRef<'a> {
        self.occurrence
    }
    pub fn parent(self) -> SccDefinitionRef<'a> {
        self.parent
    }
    pub fn target(self) -> SccDefinitionRef<'a> {
        self.target
    }
    pub fn target_component(self) -> SccComponentRef<'a> {
        self.generalization.component()
    }
    pub fn pending_generalization(self) -> PendingSccGeneralizationRef<'a> {
        self.generalization
    }
    pub fn current_scheme(self) -> crate::shadow_f5::ClosedSchemeRef<'s> {
        self.current_scheme
    }

    /// Absence means no committed route was retained, including failed uses.
    pub fn current_route(self) -> Option<CurrentUseRouteRef<'s>> {
        self.current_route
    }

    /// Current solve evidence only; the pending successor premises remain unchanged.
    pub fn current_fresh_capture(self) -> crate::shadow_f5::FreshCaptureState<'s> {
        self.current_scheme
            .fresh_capture(self.occurrence.id, self.target.id, self.closed_route)
    }

    /// Current Q/R inventories, including empty ones, cannot establish correspondence.
    pub fn qr_correspondence_premise(self) -> PendingUseInstantiationPremise {
        PendingUseInstantiationPremise::CurrentToSuccessorQrCorrespondenceUnresolved
    }

    pub fn shared_contract_transport_premise(self) -> PendingUseInstantiationPremise {
        PendingUseInstantiationPremise::UseTimeSharedContractTransportUnresolved
    }
}

/// A committed current route, borrowed together with its owning fact store.
/// No successor correspondence follows from this current implementation evidence.
#[cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]
#[derive(Clone, Copy)]
pub struct CurrentUseRouteRef<'s> {
    route: &'s crate::RoutedUseProvenance,
    store: &'s crate::ConstraintStore,
}

#[cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]
impl<'s> CurrentUseRouteRef<'s> {
    pub fn kind(self) -> CurrentUseRouteKind {
        match self.route.kind {
            crate::RoutedUseKind::Internal => CurrentUseRouteKind::Internal,
            crate::RoutedUseKind::IncomingInt => CurrentUseRouteKind::IncomingInt,
            crate::RoutedUseKind::IncomingBottomTrivial => {
                CurrentUseRouteKind::IncomingBottomTrivial
            }
            crate::RoutedUseKind::IncomingStructured => CurrentUseRouteKind::IncomingStructured,
        }
    }

    /// Bottom-trivial routes are recorded but have no admitted fact.
    pub fn fact(self) -> Option<&'s crate::SemanticFact> {
        self.route
            .fact
            .map(|id| &self.store.facts()[id.index() as usize])
    }

    /// Match the exact source cause and fact only inside this route's own store.
    /// A structured union's fact is its retained public representative.
    pub fn provenance(self) -> impl Iterator<Item = &'s crate::ProvenanceEdge> {
        self.store.provenance().iter().filter(move |edge| {
            Some(edge.fact()) == self.route.fact
                && edge.cause().occurrence().local_slot() == 0
                && edge.cause().occurrence().occurrence() == self.route.use_id.occurrence()
        })
    }
}

#[cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CurrentUseRouteKind {
    Internal,
    IncomingInt,
    IncomingBottomTrivial,
    IncomingStructured,
}

#[cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PendingUseInstantiationPremise {
    CurrentToSuccessorQrCorrespondenceUnresolved,
    UseTimeSharedContractTransportUnresolved,
}

#[cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PendingUseInstantiationLookupError {
    Topology(SccTopologyLookupError),
    ClosedScheme(SccClosedSchemeLookupError),
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

/// Failure to resolve an opaque definition or use handle in a topology view.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SccTopologyLookupError {
    ForeignArtifact,
    MissingIdentity,
}

/// Collection, absent identity, and retained-root rejection remain distinct.
#[cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SccClosedSchemeLookupError {
    ForeignCollection,
    MissingIdentity,
    ForeignRoot,
}

/// Collection rejection is distinct from parse/source correspondence failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SccSourceLookupError {
    ForeignCollection,
    MissingIdentity,
    SourceIdentity(yu_hir::shadow::SourceIdentityError),
}

/// Source/artifact rejection remains distinct from an unrepresented position.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SccShadowLookupError {
    Source(SccSourceLookupError),
    Shadow(yu_hir::shadow::ShadowError),
}
