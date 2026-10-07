//! Cold structural evidence for whole-Name resolved self initializers.
//!
//! A candidate is not the exact q1 source judgment, an execution decision,
//! a type admission, or a runtime value. Both premises remain pending after solve.

use crate::{
    ConstraintBatch, DefinitionOrderId, DefinitionRootId, DefinitionUseId, HirOccurrenceId,
    SolvedModule, scc::SccComponentId,
};
use std::sync::Arc;
use yu_hir::{HirItem, HirModule, NameResolution, ResolvedExpr};

/// Owned collection-branded evidence that can survive consuming the batch.
/// Captured only by an explicit cold observer call; production retains no new rows.
pub struct InitializationCandidates {
    hir: Arc<HirModule>,
    artifact: Arc<crate::CollectionArtifactToken>,
    candidates: Vec<InitializationCandidate>,
}

impl ConstraintBatch {
    /// Scan original complete binding bodies, never spelling or inferred types.
    pub fn shadow_initialization_candidates(&self) -> InitializationCandidates {
        let mut candidates = Vec::new();
        let mut definitions = self.definitions.iter();
        for item in self.hir.items() {
            let HirItem::Binding(binding) = item else {
                continue;
            };
            let definition = definitions
                .next()
                .expect("collected binding has a definition");
            let ResolvedExpr::Name {
                resolution: NameResolution::Resolved(target),
                ..
            } = binding.value()
            else {
                continue;
            };
            if target != binding.id() {
                continue;
            }
            let occurrence = binding.value().occurrence();
            let id = DefinitionUseId::new(self.collection_artifact.clone(), occurrence.clone());
            let use_record = &self.definition_uses[self.definition_use_positions[&id]];
            assert_eq!(use_record.parent, definition.definition);
            assert_eq!(use_record.target, definition.definition);
            let component = self
                .scc_plan()
                .component_for_definition(&definition.definition)
                .expect("collected definition belongs to frozen SCC plan")
                .clone();
            candidates.push(InitializationCandidate {
                root: definition.root.clone(),
                occurrence: occurrence.clone(),
                use_id: use_record.id.clone(),
                parent: use_record.parent.clone(),
                target: use_record.target.clone(),
                component,
            });
        }
        InitializationCandidates {
            hir: self.hir.clone(),
            artifact: self.collection_artifact.clone(),
            candidates,
        }
    }
}

impl InitializationCandidates {
    pub fn candidates(&self) -> impl Iterator<Item = InitializationCandidateRef<'_>> {
        self.candidates
            .iter()
            .map(|candidate| InitializationCandidateRef {
                inventory: self,
                candidate,
            })
    }
}

impl SolvedModule {
    /// Validate collection ownership before exposing retained rows and current schemes.
    /// Even another batch collected from the identical HIR is foreign.
    pub fn shadow_initialization<'a, 's>(
        &'s self,
        inventory: &'a InitializationCandidates,
    ) -> Result<SolvedInitializationRef<'a, 's>, InitializationLookupError> {
        if !Arc::ptr_eq(&self.collection_artifact, &inventory.artifact) {
            return Err(InitializationLookupError::ForeignCollection);
        }
        Ok(SolvedInitializationRef {
            inventory,
            solved: self,
        })
    }
}

/// Borrowed evidence joined to the current finalized solve result.
#[derive(Clone, Copy)]
pub struct SolvedInitializationRef<'a, 's> {
    inventory: &'a InitializationCandidates,
    solved: &'s SolvedModule,
}
impl<'a, 's> SolvedInitializationRef<'a, 's> {
    pub fn candidates(self) -> impl Iterator<Item = InitializationCandidateRef<'a>> {
        self.inventory.candidates()
    }
    pub fn current_scheme(
        self,
        candidate: InitializationCandidateRef<'_>,
    ) -> Result<crate::shadow_f5::ClosedSchemeRef<'s>, InitializationLookupError> {
        if !Arc::ptr_eq(&self.inventory.artifact, &candidate.inventory.artifact) {
            return Err(InitializationLookupError::ForeignCollection);
        }
        self.solved
            .shadow_closed_schemes()
            .for_root(candidate.root())
            .map_err(|_| InitializationLookupError::ForeignRoot)
    }
}

/// Exact collection identities retained independently of display/source spelling.
struct InitializationCandidate {
    root: DefinitionRootId,
    occurrence: HirOccurrenceId,
    use_id: DefinitionUseId,
    parent: DefinitionOrderId,
    target: DefinitionOrderId,
    component: SccComponentId,
}

#[derive(Clone, Copy)]
pub struct InitializationCandidateRef<'a> {
    inventory: &'a InitializationCandidates,
    candidate: &'a InitializationCandidate,
}
impl<'a> InitializationCandidateRef<'a> {
    pub fn root(self) -> &'a DefinitionRootId {
        &self.candidate.root
    }
    pub fn rhs_occurrence(self) -> &'a HirOccurrenceId {
        &self.candidate.occurrence
    }
    pub fn same_use_identity(self, other: Self) -> bool {
        self.candidate.use_id == other.candidate.use_id
    }
    pub fn same_component_identity(self, other: Self) -> bool {
        self.candidate.component == other.candidate.component
    }
    /// Collection-local metadata only; retained parent and target are exact branded IDs.
    pub fn parent_ordinal(self) -> u32 {
        self.candidate.parent.ordinal()
    }
    pub fn target_ordinal(self) -> u32 {
        self.candidate.target.ordinal()
    }
    pub fn component_canonical_ordinal(self) -> u32 {
        self.candidate.component.canonical_definition().ordinal()
    }
    pub fn original_q1_source_envelope_premise(self) -> InitializationPremise {
        InitializationPremise::OriginalQ1SourceEnvelopeRecognitionPending
    }
    pub fn pre_execution_enforcement_premise(self) -> InitializationPremise {
        InitializationPremise::PreExecutionEnforcementPending
    }
    pub fn definition_source_position(
        self,
        shadow: &yu_hir::shadow::ShadowArtifact,
    ) -> Result<yu_hir::shadow::PositionId, yu_hir::shadow::SourceIdentityError> {
        shadow.definition_source_position(&self.inventory.hir, self.root())
    }
    pub fn rhs_source_position(
        self,
        shadow: &yu_hir::shadow::ShadowArtifact,
    ) -> Result<yu_hir::shadow::PositionId, yu_hir::shadow::SourceIdentityError> {
        shadow.occurrence_source_position(&self.inventory.hir, self.rhs_occurrence())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InitializationPremise {
    OriginalQ1SourceEnvelopeRecognitionPending,
    PreExecutionEnforcementPending,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InitializationLookupError {
    ForeignCollection,
    ForeignRoot,
}
