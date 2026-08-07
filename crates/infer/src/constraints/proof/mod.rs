//! Constraint Proof Kernel boundary.
//!
//! CPK-1 defines read-only adapters over current semantic records and their legacy proof payloads.
//! CPK-2 established the typed occurrence contract; CPK-8E removes its migration-only
//! thread-local capture now that tests assert the production store directly.

use super::*;
use std::sync::Arc;

/// Projection representation selected once for one `ConstraintMachine` lifetime.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ProofReadAuthority {
    Cpk,
    LegacyRollback(ProofFailure),
}

/// One canonical claimed support returned by [`ProofOccurrenceStore::project_lower`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ProjectionClaimSupport {
    pub(crate) coverage_root: UpperReplayClaimId,
    pub(crate) representative_claim: UpperReplayClaimId,
}

/// All currently qualifying supports for one included lower record.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct ProjectionSupportSet {
    pub(crate) uncovered_claims: Vec<ProjectionClaimSupport>,
    pub(crate) independent_supports: Vec<ProjectionProofCarrier>,
}

/// Fallible projection result for one active lower record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ProjectionDecision {
    Unclaimed,
    Excluded,
    Included { supports: ProjectionSupportSet },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ProjectionSupportIdentity {
    Claimed(ProjectionClaimSupport),
    Independent(ProjectionProofCarrier),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ProofFactRef {
    Semantic(SemanticFactRef),
    ProjectionSupports(BoundRecordId),
    ProjectionFormula(BoundRecordId),
    ProjectionSupport {
        record: BoundRecordId,
        support: ProjectionSupportIdentity,
    },
    UpperClaim(UpperReplayClaimId),
    CoverageRoot(UpperReplayClaimId),
    Origin(OriginId),
    RowDerivation(RowDerivationId),
    RowReduction(UnweightedRowReductionRecordId),
    GeneralizedWitness(GeneralizedSchemeWitnessId),
    ReplayClaims(BoundRecordId),
    ReplayParent {
        lower: BoundRecordId,
        upper: BoundRecordId,
        side: ReplayClaimParentSide,
        coverage_root: UpperReplayClaimId,
    },
    IncrementalReplayRoute(IncrementalRouteKey),
    LiveCoverage(UpperReplayClaimId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MandatoryProofField {
    SupportIdentity,
    RepresentativeClaim,
    CoverageRoot,
    LiveCoverage,
    Formula,
    FormulaPremise,
    ExactCarrier,
    ReplayParentIdentity,
    ReplayParentSide,
    ReplayParentLineage,
    ReplayClaimIndex,
    IncrementalRouteClaim,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProjectionInvariantViolation {
    OrphanFormula,
    DuplicateClaimedRoot,
    DuplicateIndependentCarrier,
    RepresentativeRootMismatch,
    FormulaSupportMismatch,
    FormulaCategoryOrder,
    VisitingStateEscaped,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProofOperation {
    AdmitOriginalClaim,
    AdmitDerivedClaim,
    UpdateClaimLifecycle,
    ProjectLowerPreflight,
    ProjectLowerSupportCollection,
    ProjectLowerEvaluation,
    PrepareReplayRoutePreflight,
    PrepareReplayRouteParentCollection,
    PrepareReplayRouteBatch,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplayRouteTargetViolation {
    LowerDirectionOrState,
    UpperDirectionOrState,
    OwnerMismatch,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplayRoutingInvariantViolation {
    ClaimIndexMismatch,
    DuplicateParentRoot(ReplayClaimParentSide),
    RepresentativeRootMismatch,
    IncrementalUpperMismatch,
    IncrementalClaimMismatch,
    DuplicatePreparedIncrementalRoute,
    RoutingPayloadMismatch,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ProofFailure {
    MissingSemanticFact {
        fact: SemanticFactRef,
    },
    InvalidProjectionTarget {
        record: BoundRecordId,
        direction: BoundDirection,
        state: BoundRecordState,
    },
    MissingProofFact {
        fact: ProofFactRef,
    },
    DanglingProofReference {
        owner: ProofFactRef,
        target: ProofFactRef,
    },
    IncompleteMandatoryData {
        owner: ProofFactRef,
        field: MandatoryProofField,
    },
    NonCanonicalProjectionOrder {
        record: BoundRecordId,
    },
    ProjectionInvariantViolation {
        record: BoundRecordId,
        kind: ProjectionInvariantViolation,
    },
    InvalidReplayRouteTarget {
        lower: BoundRecordId,
        upper: BoundRecordId,
        kind: ReplayRouteTargetViolation,
    },
    NonCanonicalReplayParentOrder {
        lower: BoundRecordId,
        upper: BoundRecordId,
        side: ReplayClaimParentSide,
    },
    ReplayRoutingInvariantViolation {
        lower: BoundRecordId,
        upper: BoundRecordId,
        kind: ReplayRoutingInvariantViolation,
    },
    ResourceExhausted {
        operation: ProofOperation,
    },
}

/// Memo and cycle-cut state shared only within one immutable projection traversal.
pub(crate) struct ProjectionEvaluationRound<'a> {
    states: FxHashMap<ProofEvalNode, ProofEvalState>,
    memo_sharing_disabled: bool,
    terminal_failure: Option<ProofFailure>,
    cycle_cuts: usize,
    snapshot: std::marker::PhantomData<&'a ()>,
}

impl ProjectionEvaluationRound<'_> {
    pub(crate) fn new() -> Self {
        Self {
            states: FxHashMap::default(),
            memo_sharing_disabled: false,
            terminal_failure: None,
            cycle_cuts: 0,
            snapshot: std::marker::PhantomData,
        }
    }

    #[cfg(test)]
    fn cycle_cuts(&self) -> usize {
        self.cycle_cuts
    }
}

impl Default for ProjectionEvaluationRound<'_> {
    fn default() -> Self {
        Self::new()
    }
}

/// Stable reference from proof state to a semantic fact owned by the constraint machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum SemanticFactRef {
    Constraint(ConstraintRecordId),
    Bound(BoundRecordId),
    Subtract(SubtractFactRecordId),
    RowDerivation(RowDerivationId),
    RowReduction(UnweightedRowReductionRecordId),
    SchemeInstantiation(SchemeInstantiationId),
}

/// Semantic portion of a canonical subtype constraint.
#[derive(Debug, Clone, Copy)]
pub(crate) struct SemanticConstraintRecordRef<'a> {
    key: &'a SubtypeConstraintKey,
}

impl<'a> SemanticConstraintRecordRef<'a> {
    pub(crate) fn key(self) -> &'a SubtypeConstraintKey {
        self.key
    }
}

/// Semantic portion of an active or tombstoned bound record.
#[derive(Debug, Clone, Copy)]
pub(crate) struct SemanticBoundRecordRef<'a> {
    direction: BoundDirection,
    owner: TypeVar,
    endpoint: BoundEndpoint,
    weights: &'a ConstraintWeights,
    state: BoundRecordState,
}

impl<'a> SemanticBoundRecordRef<'a> {
    pub(crate) fn direction(self) -> BoundDirection {
        self.direction
    }

    pub(crate) fn owner(self) -> TypeVar {
        self.owner
    }

    pub(crate) fn endpoint(self) -> BoundEndpoint {
        self.endpoint
    }

    pub(crate) fn weights(self) -> &'a ConstraintWeights {
        self.weights
    }

    pub(crate) fn state(self) -> BoundRecordState {
        self.state
    }
}

/// Semantic state of one unweighted row reduction.
///
/// `provenance_head` is intentionally absent: it belongs to proof payload, not the semantic state
/// controlling replay and materialization.
#[derive(Debug, Clone, Copy)]
pub(crate) struct SemanticRowReductionRecordRef<'a> {
    source: TypeVar,
    producer_constraint: Option<ConstraintRecordId>,
    original_items: &'a [NegId],
    original_tail: NegId,
    original_upper: NegId,
    consumed_items: &'a [NegId],
    remaining_items: &'a [NegId],
    current_reduced_upper: NegId,
    current_record: BoundRecordId,
    processed_lower_records: &'a FxHashSet<BoundRecordId>,
}

impl<'a> SemanticRowReductionRecordRef<'a> {
    pub(crate) fn source(self) -> TypeVar {
        self.source
    }

    pub(crate) fn producer_constraint(self) -> Option<ConstraintRecordId> {
        self.producer_constraint
    }

    pub(crate) fn original_items(self) -> &'a [NegId] {
        self.original_items
    }

    pub(crate) fn original_tail(self) -> NegId {
        self.original_tail
    }

    pub(crate) fn original_upper(self) -> NegId {
        self.original_upper
    }

    pub(crate) fn consumed_items(self) -> &'a [NegId] {
        self.consumed_items
    }

    pub(crate) fn remaining_items(self) -> &'a [NegId] {
        self.remaining_items
    }

    pub(crate) fn current_reduced_upper(self) -> NegId {
        self.current_reduced_upper
    }

    pub(crate) fn current_record(self) -> BoundRecordId {
        self.current_record
    }

    pub(crate) fn processed_lower_records(self) -> &'a FxHashSet<BoundRecordId> {
        self.processed_lower_records
    }
}

/// Narrow, read-only semantic surface available to proof backends.
pub(crate) trait SemanticFactView {
    fn constraint(&self, id: ConstraintRecordId) -> Option<SemanticConstraintRecordRef<'_>>;

    fn bound(&self, id: BoundRecordId) -> Option<SemanticBoundRecordRef<'_>>;

    fn row_reduction(
        &self,
        id: UnweightedRowReductionRecordId,
    ) -> Option<SemanticRowReductionRecordRef<'_>>;

    fn lower_record_for_constraint(&self, id: ConstraintRecordId) -> Option<BoundRecordId>;

    fn is_var_pos(&self, id: PosId) -> bool;
}

impl SemanticFactView for ConstraintMachine {
    fn constraint(&self, id: ConstraintRecordId) -> Option<SemanticConstraintRecordRef<'_>> {
        self.constraint_records
            .get(id.0 as usize)
            .map(ConstraintRecord::semantic_ref)
    }

    fn bound(&self, id: BoundRecordId) -> Option<SemanticBoundRecordRef<'_>> {
        self.bounds
            .records
            .get(id.0 as usize)
            .map(BoundRecord::semantic_ref)
    }

    fn row_reduction(
        &self,
        id: UnweightedRowReductionRecordId,
    ) -> Option<SemanticRowReductionRecordRef<'_>> {
        self.unweighted_row_reduction_records
            .get(id.0 as usize)
            .map(UnweightedRowReductionRecord::semantic_ref)
    }

    fn lower_record_for_constraint(&self, id: ConstraintRecordId) -> Option<BoundRecordId> {
        ConstraintMachine::lower_record_for_constraint(self, id)
    }

    fn is_var_pos(&self, id: PosId) -> bool {
        matches!(self.types.pos(id), Pos::Var(_))
    }
}

/// Read-only constraint proof fields retained by the legacy representation.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ConstraintProofPayloadRef<'a> {
    root_origins: &'a [OriginId],
    structural_derivations: &'a [StructuralDerivation],
    row_derivations: &'a [RowDerivationId],
    replay_derivations: &'a [BinaryReplayDerivation],
    scheme_instantiation_derivations: &'a [SchemeInstantiationDerivation],
    scheme_instantiation_routes: &'a [SchemeInstantiationRoute],
    canonicalization_dispositions: &'a [ConstraintCanonicalizationDisposition],
    replay_provenance: ProvenanceCompleteness,
}

impl<'a> ConstraintProofPayloadRef<'a> {
    pub(crate) fn root_origins(self) -> &'a [OriginId] {
        self.root_origins
    }

    pub(crate) fn structural_derivations(self) -> &'a [StructuralDerivation] {
        self.structural_derivations
    }

    pub(crate) fn row_derivations(self) -> &'a [RowDerivationId] {
        self.row_derivations
    }

    pub(crate) fn replay_derivations(self) -> &'a [BinaryReplayDerivation] {
        self.replay_derivations
    }

    pub(crate) fn scheme_instantiation_derivations(self) -> &'a [SchemeInstantiationDerivation] {
        self.scheme_instantiation_derivations
    }

    pub(crate) fn scheme_instantiation_routes(self) -> &'a [SchemeInstantiationRoute] {
        self.scheme_instantiation_routes
    }

    pub(crate) fn canonicalization_dispositions(
        self,
    ) -> &'a [ConstraintCanonicalizationDisposition] {
        self.canonicalization_dispositions
    }

    pub(crate) fn replay_provenance(self) -> ProvenanceCompleteness {
        self.replay_provenance
    }
}

/// Read-only bound proof fields retained by the legacy representation.
#[derive(Debug, Clone, Copy)]
pub(crate) struct BoundProofPayloadRef<'a> {
    derivations: &'a [BoundDerivation],
    disposition: Option<BoundDispositionRecordId>,
}

impl<'a> BoundProofPayloadRef<'a> {
    pub(crate) fn derivations(self) -> &'a [BoundDerivation] {
        self.derivations
    }

    pub(crate) fn disposition(self) -> Option<BoundDispositionRecordId> {
        self.disposition
    }
}

/// Transitional read backend for proof payloads still embedded in semantic records.
pub(crate) trait ProofPayloadView {
    fn constraint_payload(&self, id: ConstraintRecordId) -> Option<ConstraintProofPayloadRef<'_>>;

    fn bound_payload(&self, id: BoundRecordId) -> Option<BoundProofPayloadRef<'_>>;
}

/// Legacy authority adapter. It borrows current storage and cannot mutate it.
#[derive(Clone, Copy)]
pub(crate) struct LegacyProofBackend<'a> {
    machine: &'a ConstraintMachine,
}

impl<'a> LegacyProofBackend<'a> {
    pub(crate) fn new(machine: &'a ConstraintMachine) -> Self {
        Self { machine }
    }
}

impl ProofPayloadView for LegacyProofBackend<'_> {
    fn constraint_payload(&self, id: ConstraintRecordId) -> Option<ConstraintProofPayloadRef<'_>> {
        self.machine
            .constraint_records
            .get(id.0 as usize)
            .map(ConstraintRecord::proof_payload_ref)
    }

    fn bound_payload(&self, id: BoundRecordId) -> Option<BoundProofPayloadRef<'_>> {
        self.machine
            .bounds
            .records
            .get(id.0 as usize)
            .map(BoundRecord::proof_payload_ref)
    }
}

/// Empty backend used while legacy remains authoritative.
///
/// It owns no fields by construction and therefore cannot record a shadow write accidentally.
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct NullProofBackend;

impl ProofPayloadView for NullProofBackend {
    fn constraint_payload(&self, _id: ConstraintRecordId) -> Option<ConstraintProofPayloadRef<'_>> {
        None
    }

    fn bound_payload(&self, _id: BoundRecordId) -> Option<BoundProofPayloadRef<'_>> {
        None
    }
}

impl ConstraintRecord {
    fn semantic_ref(&self) -> SemanticConstraintRecordRef<'_> {
        SemanticConstraintRecordRef { key: &self.key }
    }

    fn proof_payload_ref(&self) -> ConstraintProofPayloadRef<'_> {
        ConstraintProofPayloadRef {
            root_origins: &self.root_origins,
            structural_derivations: &self.structural_derivations,
            row_derivations: &self.row_derivations,
            replay_derivations: &self.replay_derivations,
            scheme_instantiation_derivations: &self.scheme_instantiation_derivations,
            scheme_instantiation_routes: &self.scheme_instantiation_routes,
            canonicalization_dispositions: &self.canonicalization_dispositions,
            replay_provenance: self.replay_provenance,
        }
    }
}

impl BoundRecord {
    fn semantic_ref(&self) -> SemanticBoundRecordRef<'_> {
        SemanticBoundRecordRef {
            direction: self.direction,
            owner: self.owner,
            endpoint: self.endpoint,
            weights: &self.weights,
            state: self.state,
        }
    }

    fn proof_payload_ref(&self) -> BoundProofPayloadRef<'_> {
        BoundProofPayloadRef {
            derivations: &self.derivations,
            disposition: self.disposition,
        }
    }
}

impl UnweightedRowReductionRecord {
    fn semantic_ref(&self) -> SemanticRowReductionRecordRef<'_> {
        SemanticRowReductionRecordRef {
            source: self.source,
            producer_constraint: self.producer_constraint,
            original_items: &self.original_items,
            original_tail: self.original_tail,
            original_upper: self.original_upper,
            consumed_items: &self.consumed_items,
            remaining_items: &self.remaining_items,
            current_reduced_upper: self.current_reduced_upper.endpoint,
            current_record: self.current_reduced_upper.record,
            processed_lower_records: &self.processed_lower_records,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofOccurrence {
    pub(crate) result: ProofResult,
    pub(crate) cause: ProofCause,
    pub(crate) parents: Vec<ProofParent>,
    pub(crate) event: usize,
    pub(crate) completeness: ProvenanceCompleteness,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ProofResult {
    Semantic(SemanticFactRef),
    TrivialReplay(ReplayDropRecordId),
    EvidenceBound(BoundRecordId),
    /// Some rejected/equivalent admissions have no newly persisted semantic bound.
    BoundDisposition(BoundDispositionRecordId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ProofCause {
    Root(OriginId),
    Structural(StructuralDerivation),
    RowDefinition(RowDerivation),
    RowConstraint(RowDerivationId),
    ConstraintDisposition(ConstraintCanonicalizationDisposition),
    Bound(BoundDerivation),
    BoundDisposition(BoundDispositionRecord),
    Subtract(SubtractFactDerivation),
    SchemeInstantiationRecord(SchemeInstantiationRecord),
    SchemeInstantiationDerivation(SchemeInstantiationDerivation),
    SchemeInstantiationRoute(SchemeInstantiationRoute),
    Replay(BinaryReplayDerivation),
    ReplayEvidence(BinaryReplayDerivation),
    ReplayDrop(ReplayDropRecord),
    RowReduction {
        derivation: RowDerivationId,
        root_claim: Option<UpperReplayClaimId>,
    },
    ReductionRoute {
        derivation: RowDerivationId,
        parent_claim: UpperReplayClaimId,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ProjectionLineage {
    Original,
    ReplayConstraint,
    ReplayEvidence,
    StructuralConstraint,
    ReductionRouteConstraint,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ReplayProofParent {
    pub(crate) side: ReplayClaimParentSide,
    pub(crate) coverage_root: UpperReplayClaimId,
    pub(crate) representative_claim: UpperReplayClaimId,
    pub(crate) lineage: ProjectionLineage,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReplayProofOccurrence {
    pub(crate) result: ConstraintRecordId,
    pub(crate) carrier: BinaryReplayDerivation,
    pub(crate) lower_parents: Vec<ReplayProofParent>,
    pub(crate) upper_parents: Vec<ReplayProofParent>,
    pub(crate) first_event: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplayAdmissionDisposition {
    NewSemantic,
    CanonicalDuplicate,
    ExactDuplicate,
    Trivial,
    EvidenceOnly,
    Incomplete,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplayRouting {
    Generic,
    IncrementalOnly,
    SkipAlreadyCovered,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct PreparedReplayParent {
    pub(crate) side: ReplayClaimParentSide,
    pub(crate) coverage_root: UpperReplayClaimId,
    pub(crate) representative_claim: UpperReplayClaimId,
    pub(crate) lineage: ProjectionLineage,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) enum PreparedReplayParentBlock {
    #[default]
    Empty,
    Shared(Arc<[PreparedReplayParent]>),
}

impl PreparedReplayParentBlock {
    fn as_slice(&self) -> &[PreparedReplayParent] {
        match self {
            Self::Empty => &[],
            Self::Shared(entries) => entries,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct PreparedReplayParentSet {
    pub(crate) lower: PreparedReplayParentBlock,
    pub(crate) upper: PreparedReplayParentBlock,
}

impl PreparedReplayParentSet {
    pub(crate) fn iter(&self) -> impl Iterator<Item = &PreparedReplayParent> {
        self.lower
            .as_slice()
            .iter()
            .chain(self.upper.as_slice().iter())
    }
}

fn prepared_parent_block_from_entries(
    entries: Vec<PreparedReplayParent>,
) -> PreparedReplayParentBlock {
    if entries.is_empty() {
        PreparedReplayParentBlock::Empty
    } else {
        PreparedReplayParentBlock::Shared(Arc::from(entries))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct IncrementalRouteKey {
    pub(crate) upper: NegId,
    pub(crate) upper_record: BoundRecordId,
    pub(crate) provenance: RowDerivationId,
    pub(crate) claim: Option<UpperReplayClaimId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PreparedIncrementalReplay {
    pub(crate) route: IncrementalRouteKey,
    pub(crate) parents: PreparedReplayParentSet,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct PreparedReplayParents {
    pub(crate) pair_replay: Option<PreparedReplayParentSet>,
    pub(crate) incremental_replays: Vec<PreparedIncrementalReplay>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PreparedReplayRoute {
    pub(crate) routing: ReplayRouting,
    pub(crate) proof_event: PreparedReplayParents,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ReplayRoutingShadowToken {
    routes_before: usize,
    admissions_before: usize,
    canonical_constraints_before: usize,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct ShadowReplayRouteObservation {
    lower: BoundRecordId,
    upper: BoundRecordId,
    legacy: ReplayRouting,
    shadow: ReplayRouting,
    lower_parent_roots: usize,
    upper_parent_roots: usize,
    legacy_prepared: PreparedReplayRoute,
    shadow_prepared: PreparedReplayRoute,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ShadowReplayDirection {
    Lower,
    Upper,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct ShadowReplayEventObservation {
    direction: ShadowReplayDirection,
    legacy_input_count: usize,
    shadow_input_count: usize,
    legacy_generated_count: usize,
    shadow_generated_count: usize,
    legacy_accepted_count: usize,
    shadow_accepted_count: usize,
    accepted_results: Vec<ConstraintRecordId>,
    admissions: Vec<ReplayAdmissionEvent>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ReplayAdmissionEvent {
    pub(crate) result: Option<ConstraintRecordId>,
    pub(crate) carrier: BinaryReplayDerivation,
    pub(crate) disposition: ReplayAdmissionDisposition,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ReplayFirstWitness {
    pub(crate) carrier: BinaryReplayDerivation,
    pub(crate) side: ReplayClaimParentSide,
    pub(crate) representative_claim: UpperReplayClaimId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum UpperClaimKind {
    Direct,
    Reduced(UnweightedRowReductionRecordId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum UpperClaimLineage {
    Original,
    ReplayConstraint {
        parent_claim: UpperReplayClaimId,
        parent_side: ReplayClaimParentSide,
        result: ConstraintRecordId,
        replay: BinaryReplayDerivation,
        depth: u32,
    },
    ReplayEvidence {
        parent_claim: UpperReplayClaimId,
        parent_side: ReplayClaimParentSide,
        replay: BinaryReplayDerivation,
        depth: u32,
    },
    StructuralConstraint {
        parent_claim: UpperReplayClaimId,
        result: ConstraintRecordId,
        derivation: StructuralDerivation,
        depth: u32,
    },
    ReductionRouteConstraint {
        parent_claim: UpperReplayClaimId,
        result: ConstraintRecordId,
        derivation: RowDerivationId,
        depth: u32,
    },
}

impl UpperClaimLineage {
    fn depth(self) -> u32 {
        match self {
            Self::Original => 0,
            Self::ReplayConstraint { depth, .. }
            | Self::ReplayEvidence { depth, .. }
            | Self::StructuralConstraint { depth, .. }
            | Self::ReductionRouteConstraint { depth, .. } => depth,
        }
    }

    fn projection_lineage(self) -> ProjectionLineage {
        match self {
            Self::Original => ProjectionLineage::Original,
            Self::ReplayConstraint { .. } => ProjectionLineage::ReplayConstraint,
            Self::ReplayEvidence { .. } => ProjectionLineage::ReplayEvidence,
            Self::StructuralConstraint { .. } => ProjectionLineage::StructuralConstraint,
            Self::ReductionRouteConstraint { .. } => {
                ProjectionLineage::ReductionRouteConstraint
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UpperClaimOccurrence {
    pub(crate) claim: UpperReplayClaimId,
    pub(crate) coverage_root: UpperReplayClaimId,
    pub(crate) kind: UpperClaimKind,
    pub(crate) full_lineage: UpperClaimLineage,
    pub(crate) lineage: ProjectionLineage,
    pub(crate) producer: ConstraintRecordId,
    pub(crate) current_record: BoundRecordId,
}

/// CPK claim payload frozen by the allocating transaction before control returns to its caller.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct PreparedUpperClaimAdmission {
    pub(super) occurrence: UpperClaimOccurrence,
    new_record_claims: Option<Vec<UpperReplayClaimId>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum PreparedDerivedClaimDecision {
    Coalesced {
        claim: UpperReplayClaimId,
        coverage_root: UpperReplayClaimId,
    },
    New(PreparedUpperClaimAdmission),
}

/// Claim-location mutation frozen by the CPK transaction before publication to the flat mirror.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct PreparedUpperClaimMove {
    pub(super) claim: UpperReplayClaimId,
    pub(super) previous_record: BoundRecordId,
    pub(super) current_record: BoundRecordId,
    pub(super) producer: ConstraintRecordId,
    pub(super) coverage_root: UpperReplayClaimId,
    pub(super) full_lineage: UpperClaimLineage,
    new_record_claims: Option<Vec<UpperReplayClaimId>>,
}

pub(super) struct PreparedLiveCoverageMutation {
    pub(super) transition: PreparedLiveCoverageTransition,
    new_root_states: Option<FxHashSet<UnweightedRowReductionRecordId>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ProjectionClause {
    Standalone {
        support: SchemeProjectionProofSupport,
        attribution: Option<ProjectionLineage>,
    },
    DerivedUnary {
        support: SchemeProjectionProofSupport,
        carrier: DerivedUnaryCarrier,
        premise: ProofPremise,
        attribution: Option<ProjectionLineage>,
    },
    ReplayConjunction {
        support: SchemeProjectionProofSupport,
        carrier: BinaryReplayDerivation,
        lower: BoundRecordId,
        upper: BoundRecordId,
        attribution: Option<ProjectionLineage>,
    },
}

impl ProjectionClause {
    fn support(self) -> SchemeProjectionProofSupport {
        match self {
            Self::Standalone { support, .. }
            | Self::DerivedUnary { support, .. }
            | Self::ReplayConjunction { support, .. } => support,
        }
    }

    fn category_rank(self) -> u8 {
        match self {
            Self::Standalone { .. } => 0,
            Self::DerivedUnary { .. } => 1,
            Self::ReplayConjunction { .. } => 2,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ResolvedProjectionSupport {
    Claimed(ProjectionClaimSupport),
    Independent(ProjectionProofCarrier),
}

impl ResolvedProjectionSupport {
    fn same_key(self, other: Self) -> bool {
        match self {
            Self::Claimed(left) => {
                matches!(other, Self::Claimed(right) if left.coverage_root == right.coverage_root)
            }
            Self::Independent(left) => {
                matches!(other, Self::Independent(right) if left == right)
            }
        }
    }

    fn cmp(self, other: Self) -> std::cmp::Ordering {
        match (self, other) {
            (Self::Claimed(left), Self::Claimed(right)) => {
                left.coverage_root.cmp(&right.coverage_root)
            }
            (Self::Claimed(_), Self::Independent(_)) => std::cmp::Ordering::Less,
            (Self::Independent(_), Self::Claimed(_)) => std::cmp::Ordering::Greater,
            (Self::Independent(left), Self::Independent(right)) => {
                canonical_projection_key::carrier_cmp(&left, &right)
            }
        }
    }
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ShadowProjectabilityObservation {
    record: BoundRecordId,
    legacy: bool,
    shadow: bool,
    legacy_cycle_cut: bool,
    shadow_cycle_cut: bool,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ShadowProjectionPublicationClass {
    None,
    MetadataOnly,
    InclusionFlip,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct ShadowProjectionPublicationObservation {
    lower_record: BoundRecordId,
    legacy_class: ShadowProjectionPublicationClass,
    shadow_class: ShadowProjectionPublicationClass,
    legacy_affected_owners: Vec<TypeVar>,
    shadow_affected_owners: Vec<TypeVar>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RowReductionOccurrence {
    pub(crate) state: UnweightedRowReductionRecordId,
    pub(crate) root_claim: Option<UpperReplayClaimId>,
    pub(crate) provenance: RowDerivationId,
    pub(crate) current_record: BoundRecordId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PreparedLiveCoverageTransition {
    Unchanged,
    Changed {
        root: UpperReplayClaimId,
        state: UnweightedRowReductionRecordId,
        active: bool,
        was_empty: bool,
        is_empty: bool,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum QualifiedParentIdentity {
    Replay {
        parent_side: ReplayClaimParentSide,
        replay: BinaryReplayDerivation,
    },
    Structural(StructuralDerivation),
    ReductionRoute {
        derivation: RowDerivationId,
        parent_claim: UpperReplayClaimId,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct QualifiedParentKey {
    result: ConstraintRecordId,
    coverage_root: UpperReplayClaimId,
    identity: QualifiedParentIdentity,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ExactQualifiedParent {
    pub(super) coverage_root: UpperReplayClaimId,
    pub(super) parent: ClaimQualifiedParent,
}

#[derive(Debug)]
pub(super) struct PreparedQualifiedParentAdmission {
    result: ConstraintRecordId,
    accepted: Vec<ExactQualifiedParent>,
    canonical: Vec<ExactQualifiedParent>,
    new_result_entries: Option<Vec<ExactQualifiedParent>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ProjectionTarget {
    Constraint(ConstraintRecordId),
    Replay(BinaryReplayDerivation),
}

#[derive(Debug)]
pub(super) struct PreparedProjectionIndexAdmission {
    target: Option<(ProjectionTarget, BoundRecordId)>,
    accepted_edges: Vec<(ProofPremise, BoundRecordId)>,
    new_dependent_sets: Vec<(ProofPremise, FxHashSet<BoundRecordId>)>,
}

impl PreparedProjectionIndexAdmission {
    pub(super) fn target(&self) -> Option<(ProjectionTarget, BoundRecordId)> {
        self.target
    }

    pub(super) fn accepted_edges(&self) -> &[(ProofPremise, BoundRecordId)] {
        &self.accepted_edges
    }
}

impl PreparedQualifiedParentAdmission {
    pub(super) fn result(&self) -> ConstraintRecordId {
        self.result
    }

    pub(super) fn accepted(&self) -> &[ExactQualifiedParent] {
        &self.accepted
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ProofParent {
    Semantic(SemanticFactRef),
    Origin(OriginId),
    LowerFilter(LowerFilterRecordId),
    GeneralizedWitness(GeneralizedSchemeWitnessId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofOccurrenceStore {
    pub(crate) occurrences: Vec<ProofOccurrence>,
    pub(crate) replay_finite_map: Vec<ReplayProofOccurrence>,
    replay_finite_map_index: FxHashMap<(ConstraintRecordId, BinaryReplayDerivation), usize>,
    pub(crate) replay_admissions: Vec<ReplayAdmissionEvent>,
    pub(crate) first_replay_witnesses:
        FxHashMap<(ConstraintRecordId, UpperReplayClaimId), ReplayFirstWitness>,
    pub(crate) upper_claims: Vec<UpperClaimOccurrence>,
    upper_claim_index: FxHashMap<UpperReplayClaimId, usize>,
    original_claim_by_record_and_producer:
        FxHashMap<(BoundRecordId, ConstraintRecordId), UpperReplayClaimId>,
    derived_claim_by_record_and_root:
        FxHashMap<(BoundRecordId, UpperReplayClaimId), UpperReplayClaimId>,
    root_claim_by_producer_constraint: FxHashMap<ConstraintRecordId, UpperReplayClaimId>,
    reduction_claim_by_state:
        FxHashMap<UnweightedRowReductionRecordId, UpperReplayClaimId>,
    replay_claim_cycle_coalesces: usize,
    claims_by_upper_record: FxHashMap<BoundRecordId, Vec<UpperReplayClaimId>>,
    pub(crate) row_reductions: Vec<RowReductionOccurrence>,
    qualified_parent_keys: FxHashSet<QualifiedParentKey>,
    qualified_parents_by_result:
        FxHashMap<ConstraintRecordId, Vec<ExactQualifiedParent>>,
    projection_lower_record_by_constraint: FxHashMap<ConstraintRecordId, BoundRecordId>,
    projection_lower_record_by_replay: FxHashMap<BinaryReplayDerivation, BoundRecordId>,
    dependent_records_by_premise: FxHashMap<ProofPremise, FxHashSet<BoundRecordId>>,
    pub(crate) live_coverage: FxHashSet<(UpperReplayClaimId, UnweightedRowReductionRecordId)>,
    live_states_by_coverage_root:
        FxHashMap<UpperReplayClaimId, FxHashSet<UnweightedRowReductionRecordId>>,
    pub(crate) replay_coverage_connected: bool,
    projection_supports: FxHashMap<BoundRecordId, Vec<SchemeProjectionProofSupport>>,
    claimed_parents_by_lower_record: FxHashMap<BoundRecordId, Vec<UpperReplayClaimId>>,
    projection_formulas: FxHashMap<BoundRecordId, Vec<ProjectionClause>>,
    #[cfg(test)]
    replay_index_record_comparisons: Cell<usize>,
    #[cfg(test)]
    fail_next_original_claim_reservation: bool,
    #[cfg(test)]
    fail_next_derived_claim_reservation: bool,
    #[cfg(test)]
    fail_next_claim_move_reservation: bool,
    #[cfg(test)]
    fail_next_qualified_parent_reservation: bool,
    #[cfg(test)]
    fail_next_projection_index_reservation: bool,
    #[cfg(test)]
    projectability_observations: RefCell<Vec<ShadowProjectabilityObservation>>,
    #[cfg(test)]
    projection_publication_observations: RefCell<Vec<ShadowProjectionPublicationObservation>>,
    #[cfg(test)]
    replay_route_observations: RefCell<Vec<ShadowReplayRouteObservation>>,
    #[cfg(test)]
    replay_event_observations: RefCell<Vec<ShadowReplayEventObservation>>,
}

impl Default for ProofOccurrenceStore {
    fn default() -> Self {
        Self {
            occurrences: Vec::new(),
            replay_finite_map: Vec::new(),
            replay_finite_map_index: FxHashMap::default(),
            replay_admissions: Vec::new(),
            first_replay_witnesses: FxHashMap::default(),
            upper_claims: Vec::new(),
            upper_claim_index: FxHashMap::default(),
            original_claim_by_record_and_producer: FxHashMap::default(),
            derived_claim_by_record_and_root: FxHashMap::default(),
            root_claim_by_producer_constraint: FxHashMap::default(),
            reduction_claim_by_state: FxHashMap::default(),
            replay_claim_cycle_coalesces: 0,
            claims_by_upper_record: FxHashMap::default(),
            row_reductions: Vec::new(),
            qualified_parent_keys: FxHashSet::default(),
            qualified_parents_by_result: FxHashMap::default(),
            projection_lower_record_by_constraint: FxHashMap::default(),
            projection_lower_record_by_replay: FxHashMap::default(),
            dependent_records_by_premise: FxHashMap::default(),
            live_coverage: FxHashSet::default(),
            live_states_by_coverage_root: FxHashMap::default(),
            replay_coverage_connected: true,
            projection_supports: FxHashMap::default(),
            claimed_parents_by_lower_record: FxHashMap::default(),
            projection_formulas: FxHashMap::default(),
            #[cfg(test)]
            replay_index_record_comparisons: Cell::new(0),
            #[cfg(test)]
            fail_next_original_claim_reservation: false,
            #[cfg(test)]
            fail_next_derived_claim_reservation: false,
            #[cfg(test)]
            fail_next_claim_move_reservation: false,
            #[cfg(test)]
            fail_next_qualified_parent_reservation: false,
            #[cfg(test)]
            fail_next_projection_index_reservation: false,
            #[cfg(test)]
            projectability_observations: RefCell::default(),
            #[cfg(test)]
            projection_publication_observations: RefCell::default(),
            #[cfg(test)]
            replay_route_observations: RefCell::default(),
            #[cfg(test)]
            replay_event_observations: RefCell::default(),
        }
    }
}

impl ProofOccurrenceStore {
    pub(super) fn claim_coverage_root(
        &self,
        claim: UpperReplayClaimId,
    ) -> Option<UpperReplayClaimId> {
        self.upper_claim_index
            .get(&claim)
            .map(|index| self.upper_claims[*index].coverage_root)
    }

    pub(super) fn derived_claim(
        &self,
        record: BoundRecordId,
        coverage_root: UpperReplayClaimId,
    ) -> Option<UpperReplayClaimId> {
        self.derived_claim_by_record_and_root
            .get(&(record, coverage_root))
            .copied()
    }

    pub(super) fn next_derived_claim_depth(
        &self,
        parent_claim: UpperReplayClaimId,
    ) -> u32 {
        let parent_index = self.upper_claim_index[&parent_claim];
        self.upper_claims[parent_index]
            .full_lineage
            .depth()
            .checked_add(1)
            .expect("upper claim lineage depth overflow")
    }

    #[cfg(test)]
    fn claim_allocation_census(&self) -> (usize, usize, usize, usize, usize, usize, usize) {
        let upper_claims = &self.upper_claims;
        let upper_claim_index = &self.upper_claim_index;
        let record_claims = &self.claims_by_upper_record;
        (
            upper_claims.len(),
            upper_claims.capacity(),
            upper_claim_index.len(),
            upper_claim_index.capacity(),
            record_claims.len(),
            record_claims.capacity(),
            self.replay_index_record_comparisons.get(),
        )
    }

    fn record_occurrence(
        &mut self,
        result: ProofResult,
        cause: ProofCause,
        parents: Vec<ProofParent>,
        completeness: ProvenanceCompleteness,
    ) {
        let event = self.occurrences.len();
        self.occurrences.push(ProofOccurrence {
            result,
            cause,
            parents,
            event,
            completeness,
        });
    }
}

fn projection_lineage(lineage: UpperReplayClaimLineage) -> ProjectionLineage {
    match lineage {
        UpperReplayClaimLineage::Original => ProjectionLineage::Original,
        UpperReplayClaimLineage::ReplayConstraint { .. } => ProjectionLineage::ReplayConstraint,
        UpperReplayClaimLineage::ReplayEvidence { .. } => ProjectionLineage::ReplayEvidence,
        UpperReplayClaimLineage::StructuralConstraint { .. } => {
            ProjectionLineage::StructuralConstraint
        }
        UpperReplayClaimLineage::ReductionRouteConstraint { .. } => {
            ProjectionLineage::ReductionRouteConstraint
        }
    }
}

fn upper_claim_kind(kind: UpperReplayClaimKind) -> UpperClaimKind {
    match kind {
        UpperReplayClaimKind::Direct => UpperClaimKind::Direct,
        UpperReplayClaimKind::Reduced(state) => UpperClaimKind::Reduced(state),
    }
}

pub(super) fn upper_claim_lineage(lineage: UpperReplayClaimLineage) -> UpperClaimLineage {
    match lineage {
        UpperReplayClaimLineage::Original => UpperClaimLineage::Original,
        UpperReplayClaimLineage::ReplayConstraint {
            parent_claim,
            parent_side,
            result,
            replay,
            depth,
        } => UpperClaimLineage::ReplayConstraint {
            parent_claim,
            parent_side,
            result,
            replay,
            depth,
        },
        UpperReplayClaimLineage::ReplayEvidence {
            parent_claim,
            parent_side,
            replay,
            depth,
        } => UpperClaimLineage::ReplayEvidence {
            parent_claim,
            parent_side,
            replay,
            depth,
        },
        UpperReplayClaimLineage::StructuralConstraint {
            parent_claim,
            result,
            derivation,
            depth,
        } => UpperClaimLineage::StructuralConstraint {
            parent_claim,
            result,
            derivation,
            depth,
        },
        UpperReplayClaimLineage::ReductionRouteConstraint {
            parent_claim,
            result,
            derivation,
            depth,
        } => UpperClaimLineage::ReductionRouteConstraint {
            parent_claim,
            result,
            derivation,
            depth,
        },
    }
}

pub(super) fn prepare_upper_claim_admission(
    claim: &UpperReplayClaim,
) -> PreparedUpperClaimAdmission {
    let full_lineage = upper_claim_lineage(claim.lineage);
    PreparedUpperClaimAdmission {
        occurrence: UpperClaimOccurrence {
            claim: claim.id,
            coverage_root: claim.coverage_root,
            kind: upper_claim_kind(claim.kind),
            full_lineage,
            lineage: full_lineage.projection_lineage(),
            producer: claim.producer_constraint,
            current_record: claim.current_record,
        },
        new_record_claims: None,
    }
}

fn prepare_original_upper_claim_admission(
    claim: UpperReplayClaimId,
    record: BoundRecordId,
    producer: ConstraintRecordId,
    kind: UpperReplayClaimKind,
    new_record_claims: Option<Vec<UpperReplayClaimId>>,
) -> PreparedUpperClaimAdmission {
    PreparedUpperClaimAdmission {
        occurrence: UpperClaimOccurrence {
            claim,
            coverage_root: claim,
            kind: upper_claim_kind(kind),
            full_lineage: UpperClaimLineage::Original,
            lineage: ProjectionLineage::Original,
            producer,
            current_record: record,
        },
        new_record_claims,
    }
}

impl ProofOccurrenceStore {
    pub(super) fn original_claim(
        &self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
    ) -> Option<UpperReplayClaimId> {
        let claim = self.original_claim_by_record_and_producer
            .get(&(record, producer))
            .copied();
        if let Some(claim) = claim {
            debug_assert_eq!(self.root_claim_by_producer_constraint.get(&producer), Some(&claim));
        }
        claim
    }

    pub(super) fn try_reserve_reduction_claim_index(
        &mut self,
    ) -> Result<(), std::collections::TryReserveError> {
        self.reduction_claim_by_state.try_reserve(1)
    }

    pub(super) fn commit_reduction_claim_index(
        &mut self,
        state: UnweightedRowReductionRecordId,
        claim: UpperReplayClaimId,
    ) {
        assert!(self.reduction_claim_by_state.insert(state, claim).is_none());
    }

    pub(super) fn reduction_claim(
        &self,
        state: UnweightedRowReductionRecordId,
    ) -> Option<UpperReplayClaimId> {
        self.reduction_claim_by_state.get(&state).copied()
    }

    pub(super) fn try_prepare_original_claim_admission(
        &mut self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        kind: UpperReplayClaimKind,
    ) -> Result<PreparedUpperClaimAdmission, ProofFailure> {
        #[cfg(test)]
        if std::mem::take(&mut self.fail_next_original_claim_reservation) {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::AdmitOriginalClaim,
            });
        }
        let exhausted = |_| ProofFailure::ResourceExhausted {
            operation: ProofOperation::AdmitOriginalClaim,
        };
        self.upper_claims.try_reserve(1).map_err(exhausted)?;
        self.upper_claim_index.try_reserve(1).map_err(exhausted)?;
        self.original_claim_by_record_and_producer
            .try_reserve(1)
            .map_err(exhausted)?;
        self.root_claim_by_producer_constraint
            .try_reserve(1)
            .map_err(exhausted)?;
        let new_record_claims = if let Some(claims) = self.claims_by_upper_record.get_mut(&record) {
            claims.try_reserve(1).map_err(exhausted)?;
            None
        } else {
            self.claims_by_upper_record
                .try_reserve(1)
                .map_err(exhausted)?;
            let mut claims = Vec::new();
            claims.try_reserve(1).map_err(exhausted)?;
            Some(claims)
        };
        let next = u32::try_from(self.upper_claims.len()).map_err(|_| {
            ProofFailure::ResourceExhausted {
                operation: ProofOperation::AdmitOriginalClaim,
            }
        })?;
        Ok(prepare_original_upper_claim_admission(
            UpperReplayClaimId(next), record, producer, kind, new_record_claims,
        ))
    }

    pub(super) fn commit_original_claim_admission(
        &mut self,
        admission: &mut PreparedUpperClaimAdmission,
    ) {
        let claim = &admission.occurrence;
        assert_eq!(claim.claim.0 as usize, self.upper_claims.len());
        assert_eq!(claim.coverage_root, claim.claim);
        assert_eq!(claim.full_lineage, UpperClaimLineage::Original);
        let index = self.upper_claims.len();
        self.upper_claims.push(claim.clone());
        assert!(self.upper_claim_index.insert(claim.claim, index).is_none());
        assert!(self
            .original_claim_by_record_and_producer
            .insert((claim.current_record, claim.producer), claim.claim)
            .is_none());
        assert!(self
            .root_claim_by_producer_constraint
            .insert(claim.producer, claim.claim)
            .is_none());
        if let Some(claims) = admission.new_record_claims.take() {
            assert!(self
                .claims_by_upper_record
                .insert(claim.current_record, claims)
                .is_none());
        }
        self.insert_claim_into_upper_record_index(claim.current_record, claim.claim);
    }

    #[cfg(test)]
    pub(super) fn fail_next_original_claim_reservation(&mut self) {
        self.fail_next_original_claim_reservation = true;
    }

    pub(super) fn try_prepare_derived_claim_admission(
        &mut self,
        record: BoundRecordId,
        parent_claim: UpperReplayClaimId,
        producer: ConstraintRecordId,
        lineage: UpperReplayClaimLineage,
    ) -> Result<PreparedDerivedClaimDecision, ProofFailure> {
        let parent_index = self.upper_claim_index[&parent_claim];
        let parent = &self.upper_claims[parent_index];
        let coverage_root = parent.coverage_root;
        let kind = parent.kind;
        let depth = parent
            .full_lineage
            .depth()
            .checked_add(1)
            .expect("upper claim lineage depth overflow");
        assert_eq!(lineage.depth(), depth);
        let root_index = self.upper_claim_index[&coverage_root];
        if self.upper_claims[root_index].current_record == record {
            return Ok(PreparedDerivedClaimDecision::Coalesced {
                claim: coverage_root,
                coverage_root,
            });
        }
        if let Some(claim) = self
            .derived_claim_by_record_and_root
            .get(&(record, coverage_root))
            .copied()
        {
            return Ok(PreparedDerivedClaimDecision::Coalesced {
                claim,
                coverage_root,
            });
        }
        #[cfg(test)]
        if std::mem::take(&mut self.fail_next_derived_claim_reservation) {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::AdmitDerivedClaim,
            });
        }
        let exhausted = |_| ProofFailure::ResourceExhausted {
            operation: ProofOperation::AdmitDerivedClaim,
        };
        self.upper_claims.try_reserve(1).map_err(exhausted)?;
        self.upper_claim_index.try_reserve(1).map_err(exhausted)?;
        self.derived_claim_by_record_and_root
            .try_reserve(1)
            .map_err(exhausted)?;
        let new_record_claims = if let Some(claims) = self.claims_by_upper_record.get_mut(&record) {
            claims.try_reserve(1).map_err(exhausted)?;
            None
        } else {
            self.claims_by_upper_record
                .try_reserve(1)
                .map_err(exhausted)?;
            let mut claims = Vec::new();
            claims.try_reserve(1).map_err(exhausted)?;
            Some(claims)
        };
        let next = u32::try_from(self.upper_claims.len()).map_err(|_| {
            ProofFailure::ResourceExhausted {
                operation: ProofOperation::AdmitDerivedClaim,
            }
        })?;
        let full_lineage = upper_claim_lineage(lineage);
        Ok(PreparedDerivedClaimDecision::New(
            PreparedUpperClaimAdmission {
                occurrence: UpperClaimOccurrence {
                    claim: UpperReplayClaimId(next),
                    coverage_root,
                    kind,
                    full_lineage,
                    lineage: full_lineage.projection_lineage(),
                    producer,
                    current_record: record,
                },
                new_record_claims,
            },
        ))
    }

    pub(super) fn commit_derived_claim_decision(
        &mut self,
        decision: &mut PreparedDerivedClaimDecision,
    ) {
        match decision {
            PreparedDerivedClaimDecision::Coalesced { .. } => {
                self.replay_claim_cycle_coalesces += 1;
            }
            PreparedDerivedClaimDecision::New(admission) => {
                let claim = &admission.occurrence;
                assert_eq!(claim.claim.0 as usize, self.upper_claims.len());
                let index = self.upper_claims.len();
                self.upper_claims.push(claim.clone());
                assert!(self.upper_claim_index.insert(claim.claim, index).is_none());
                assert!(self
                    .derived_claim_by_record_and_root
                    .insert((claim.current_record, claim.coverage_root), claim.claim)
                    .is_none());
                if let Some(claims) = admission.new_record_claims.take() {
                    assert!(self
                        .claims_by_upper_record
                        .insert(claim.current_record, claims)
                        .is_none());
                }
                self.insert_claim_into_upper_record_index(claim.current_record, claim.claim);
            }
        }
    }

    #[cfg(test)]
    pub(super) fn fail_next_derived_claim_reservation(&mut self) {
        self.fail_next_derived_claim_reservation = true;
    }

    pub(super) fn try_prepare_upper_claim_move(
        &mut self,
        claim: UpperReplayClaimId,
        current_record: BoundRecordId,
    ) -> Result<PreparedUpperClaimMove, ProofFailure> {
        let index = self.upper_claim_index[&claim];
        let occurrence = &self.upper_claims[index];
        let previous_record = occurrence.current_record;
        let producer = occurrence.producer;
        let coverage_root = occurrence.coverage_root;
        let full_lineage = occurrence.full_lineage;
        if previous_record == current_record {
            return Ok(PreparedUpperClaimMove {
                claim,
                previous_record,
                current_record,
                producer,
                coverage_root,
                full_lineage,
                new_record_claims: None,
            });
        }
        #[cfg(test)]
        if std::mem::take(&mut self.fail_next_claim_move_reservation) {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }
        let exhausted = |_| ProofFailure::ResourceExhausted {
            operation: ProofOperation::UpdateClaimLifecycle,
        };
        match full_lineage {
            UpperClaimLineage::Original => self
                .original_claim_by_record_and_producer
                .try_reserve(1)
                .map_err(exhausted)?,
            _ => self
                .derived_claim_by_record_and_root
                .try_reserve(1)
                .map_err(exhausted)?,
        }
        let new_record_claims =
            if let Some(claims) = self.claims_by_upper_record.get_mut(&current_record) {
                claims.try_reserve(1).map_err(exhausted)?;
                None
            } else {
                self.claims_by_upper_record
                    .try_reserve(1)
                    .map_err(exhausted)?;
                let mut claims = Vec::new();
                claims.try_reserve(1).map_err(exhausted)?;
                Some(claims)
            };
        Ok(PreparedUpperClaimMove {
            claim,
            previous_record,
            current_record,
            producer,
            coverage_root,
            full_lineage,
            new_record_claims,
        })
    }

    #[cfg(test)]
    pub(super) fn fail_next_claim_move_reservation(&mut self) {
        self.fail_next_claim_move_reservation = true;
    }

    pub(super) fn record_upper_claim(&mut self, claim: &UpperReplayClaim) {
        let admission = prepare_upper_claim_admission(claim);
        self.record_prepared_upper_claim(&admission);
    }

    pub(super) fn record_prepared_upper_claim(&mut self, admission: &PreparedUpperClaimAdmission) {
        let claim = &admission.occurrence;
        if let Some(index) = self.upper_claim_index.get(&claim.claim).copied() {
            let old_record = self.upper_claims[index].current_record;
            if old_record != claim.current_record {
                self.remove_claim_from_upper_record_index(old_record, claim.claim);
                self.upper_claims[index].current_record = claim.current_record;
                self.insert_claim_into_upper_record_index(claim.current_record, claim.claim);
            }
            return;
        }
        let index = self.upper_claims.len();
        self.upper_claims.push(claim.clone());
        self.upper_claim_index.insert(claim.claim, index);
        self.insert_claim_into_upper_record_index(claim.current_record, claim.claim);
    }

    pub(super) fn commit_upper_claim_move(&mut self, mutation: &mut PreparedUpperClaimMove) {
        let index = self
            .upper_claim_index
            .get(&mutation.claim)
            .copied()
            .expect("a moved upper claim must already exist in the CPK store");
        let old_record = self.upper_claims[index].current_record;
        assert_eq!(old_record, mutation.previous_record);
        if old_record == mutation.current_record {
            return;
        }
        assert_eq!(self.upper_claims[index].producer, mutation.producer);
        assert_eq!(self.upper_claims[index].coverage_root, mutation.coverage_root);
        assert_eq!(self.upper_claims[index].full_lineage, mutation.full_lineage);
        if mutation.full_lineage == UpperClaimLineage::Original {
            assert_eq!(
                self.original_claim_by_record_and_producer
                    .remove(&(old_record, mutation.producer)),
                Some(mutation.claim)
            );
            assert!(self
                .original_claim_by_record_and_producer
                .insert((mutation.current_record, mutation.producer), mutation.claim)
                .is_none());
            self.derived_claim_by_record_and_root
                .remove(&(mutation.current_record, mutation.coverage_root));
        } else {
            assert_eq!(
                self.derived_claim_by_record_and_root
                    .remove(&(old_record, mutation.coverage_root)),
                Some(mutation.claim)
            );
            self.derived_claim_by_record_and_root
                .insert(
                    (mutation.current_record, mutation.coverage_root),
                    mutation.claim,
                );
        }
        self.remove_claim_from_upper_record_index(old_record, mutation.claim);
        self.upper_claims[index].current_record = mutation.current_record;
        if let Some(claims) = mutation.new_record_claims.take() {
            assert!(self
                .claims_by_upper_record
                .insert(mutation.current_record, claims)
                .is_none());
        }
        self.insert_claim_into_upper_record_index(mutation.current_record, mutation.claim);
    }

    fn insert_claim_into_upper_record_index(
        &mut self,
        record: BoundRecordId,
        claim: UpperReplayClaimId,
    ) {
        let occurrence_index = self.upper_claim_index[&claim];
        let incoming_root = self.upper_claims[occurrence_index].coverage_root;
        let upper_claims = &self.upper_claims;
        let claim_by_id = &self.upper_claim_index;
        #[cfg(test)]
        let comparisons = &self.replay_index_record_comparisons;
        let claims = self.claims_by_upper_record.entry(record).or_default();
        match claims.binary_search_by(|existing| {
            #[cfg(test)]
            comparisons.set(comparisons.get() + 1);
            let existing_index = claim_by_id[existing];
            canonical_upper_claim_key::cmp(
                upper_claims[existing_index].coverage_root,
                incoming_root,
            )
        }) {
            Ok(position) => claims[position] = claim,
            Err(position) => claims.insert(position, claim),
        }
    }

    fn remove_claim_from_upper_record_index(
        &mut self,
        record: BoundRecordId,
        claim: UpperReplayClaimId,
    ) {
        let occurrence_index = self.upper_claim_index[&claim];
        let root = self.upper_claims[occurrence_index].coverage_root;
        let upper_claims = &self.upper_claims;
        let claim_by_id = &self.upper_claim_index;
        #[cfg(test)]
        let comparisons = &self.replay_index_record_comparisons;
        let remove_record_entry = {
            let Some(claims) = self.claims_by_upper_record.get_mut(&record) else {
                return;
            };
            if let Ok(position) = claims.binary_search_by(|existing| {
                #[cfg(test)]
                comparisons.set(comparisons.get() + 1);
                let existing_index = claim_by_id[existing];
                canonical_upper_claim_key::cmp(upper_claims[existing_index].coverage_root, root)
            }) && claims[position] == claim
            {
                claims.remove(position);
            }
            claims.is_empty()
        };
        if remove_record_entry {
            self.claims_by_upper_record.remove(&record);
        }
    }
}

impl ProofOccurrenceStore {
    pub(super) fn record_projection_supports(
        &mut self,
        lower_record: BoundRecordId,
        proofs: &[SchemeProjectionProof],
    ) {
        let claimed_parents = proofs
            .iter()
            .filter_map(|proof| match proof.support {
                SchemeProjectionProofSupport::Claimed(claim) => Some(claim),
                SchemeProjectionProofSupport::Independent(_) => None,
            })
            .collect::<Vec<_>>();
        if claimed_parents.is_empty() {
            self.claimed_parents_by_lower_record.remove(&lower_record);
        } else {
            self.claimed_parents_by_lower_record
                .insert(lower_record, claimed_parents);
        }
        self.projection_supports.insert(
            lower_record,
            proofs.iter().map(|proof| proof.support).collect(),
        );
    }

    pub(super) fn record_projection_clause(
        &mut self,
        lower_record: BoundRecordId,
        admission: RecordProofClauseLinkAdmission,
    ) {
        let attribution = match (admission.clause, admission.claimed_attribution_source) {
        (_, None) => None,
        (RecordProofClause::Standalone { .. }, Some(_)) => Some(ProjectionLineage::Original),
        (
            RecordProofClause::DerivedUnary {
                carrier: DerivedUnaryCarrier::Structural(_),
                ..
            },
            Some(_),
        ) => Some(ProjectionLineage::StructuralConstraint),
        (
            RecordProofClause::DerivedUnary {
                carrier: DerivedUnaryCarrier::ReductionRoute(_),
                ..
            },
            Some(_),
        ) => Some(ProjectionLineage::ReductionRouteConstraint),
        (
            RecordProofClause::ReplayConjunction { .. },
            Some(ClaimedAttributionSource::CanonicalReplay),
        ) => Some(ProjectionLineage::ReplayConstraint),
        (
            RecordProofClause::ReplayConjunction { .. },
            Some(ClaimedAttributionSource::FlatRetained),
        ) => Some(ProjectionLineage::ReplayEvidence),
    };
        let clause = match admission.clause {
        RecordProofClause::Standalone { .. } => ProjectionClause::Standalone {
            support: admission.support,
            attribution,
        },
        RecordProofClause::DerivedUnary { carrier, premise } => {
            ProjectionClause::DerivedUnary {
                support: admission.support,
                carrier,
                premise,
                attribution,
            }
        }
        RecordProofClause::ReplayConjunction {
            carrier,
            lower_premise,
            upper_premise,
        } => ProjectionClause::ReplayConjunction {
            support: admission.support,
            carrier,
            lower: lower_premise,
            upper: upper_premise,
            attribution,
        },
    };
        let formula = self.projection_formulas.entry(lower_record).or_default();
        // The legacy clause-link admission has already established exact-key uniqueness before
        // this writer runs. Preserve its stable category order without rescanning and resorting
        // the complete per-record formula for every admitted link.
        let rank = clause.category_rank();
        if formula.last().is_none_or(|last| last.category_rank() <= rank) {
            formula.push(clause);
        } else {
            let position = formula.partition_point(|existing| existing.category_rank() <= rank);
            formula.insert(position, clause);
        }
    }

    /// Preflight one lower/upper replay pair from indexed CPK state.
    ///
    /// Slice B exposes the complete fallible query but does not make it a production authority.
    pub(crate) fn prepare_replay_route(
        &self,
        view: &impl SemanticFactView,
        lower: BoundRecordId,
        upper: BoundRecordId,
        incremental_routes: &[IncrementalRouteKey],
    ) -> Result<PreparedReplayRoute, ProofFailure> {
        let lower_bound = view.bound(lower).ok_or(ProofFailure::MissingSemanticFact {
            fact: SemanticFactRef::Bound(lower),
        })?;
        let upper_bound = view.bound(upper).ok_or(ProofFailure::MissingSemanticFact {
            fact: SemanticFactRef::Bound(upper),
        })?;
        if lower_bound.direction() != BoundDirection::Lower
            || lower_bound.state() == BoundRecordState::Tombstone
        {
            return Err(ProofFailure::InvalidReplayRouteTarget {
                lower,
                upper,
                kind: ReplayRouteTargetViolation::LowerDirectionOrState,
            });
        }
        if upper_bound.direction() != BoundDirection::Upper
            || upper_bound.state() == BoundRecordState::Tombstone
        {
            return Err(ProofFailure::InvalidReplayRouteTarget {
                lower,
                upper,
                kind: ReplayRouteTargetViolation::UpperDirectionOrState,
            });
        }
        if lower_bound.owner() != upper_bound.owner() {
            return Err(ProofFailure::InvalidReplayRouteTarget {
                lower,
                upper,
                kind: ReplayRouteTargetViolation::OwnerMismatch,
            });
        }
        let BoundEndpoint::Lower(lower_endpoint) = lower_bound.endpoint() else {
            return Err(ProofFailure::InvalidReplayRouteTarget {
                lower,
                upper,
                kind: ReplayRouteTargetViolation::LowerDirectionOrState,
            });
        };
        let BoundEndpoint::Upper(upper_endpoint) = upper_bound.endpoint() else {
            return Err(ProofFailure::InvalidReplayRouteTarget {
                lower,
                upper,
                kind: ReplayRouteTargetViolation::UpperDirectionOrState,
            });
        };

        let lower_ids = self
            .claimed_parents_by_lower_record
            .get(&lower)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let lower_block = self.prepare_replay_parent_block(
            lower,
            upper,
            ReplayClaimParentSide::Lower,
            lower_ids,
            None,
        )?;

        let upper_ids = self
            .claims_by_upper_record
            .get(&upper)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let upper_entries = self.prepare_replay_parent_entries(
            lower,
            upper,
            ReplayClaimParentSide::Upper,
            upper_ids,
            Some(upper),
        )?;

        let mut handled_incremental_claims = FxHashSet::default();
        handled_incremental_claims
            .try_reserve(incremental_routes.len())
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::PrepareReplayRoutePreflight,
            })?;
        for route in incremental_routes {
            self.validate_incremental_route_target(lower, upper, route, upper_ids)?;
            if let Some(claim) = route.claim {
                handled_incremental_claims.insert(claim);
            }
        }

        let mut any_uncovered = false;
        let mut pair_upper_entries = Vec::new();
        pair_upper_entries
            .try_reserve(upper_entries.len())
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::PrepareReplayRouteParentCollection,
            })?;
        let lower_is_var = view.is_var_pos(lower_endpoint);
        for parent in &upper_entries {
            let covered = self
                .live_states_by_coverage_root
                .get(&parent.coverage_root)
                .is_some_and(|states| !states.is_empty());
            any_uncovered |= !covered;
            if !covered
                || (lower_is_var
                    && covered
                    && !handled_incremental_claims.contains(&parent.representative_claim))
            {
                pair_upper_entries.push(*parent);
            }
        }
        let requires_generic = upper_entries.is_empty() || any_uncovered;

        let mut prepared_incremental = Vec::new();
        prepared_incremental
            .try_reserve(incremental_routes.len())
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::PrepareReplayRouteBatch,
            })?;
        let mut seen_incremental_actions = FxHashSet::default();
        seen_incremental_actions
            .try_reserve(incremental_routes.len())
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::PrepareReplayRoutePreflight,
            })?;
        for route in incremental_routes {
            let generic_covers = requires_generic && route.upper == upper_endpoint;
            if generic_covers {
                continue;
            }
            let action_key = (route.upper, route.upper_record);
            if !seen_incremental_actions.insert(action_key) {
                continue;
            }
            let upper = match route.claim {
                None => PreparedReplayParentBlock::Empty,
                Some(claim) => {
                    let parent = self.resolve_prepared_replay_parent(
                        lower,
                        upper,
                        ReplayClaimParentSide::Upper,
                        claim,
                        Some(upper),
                    )?;
                    PreparedReplayParentBlock::Shared(Arc::from([parent]))
                }
            };
            prepared_incremental.push(PreparedIncrementalReplay {
                route: *route,
                parents: PreparedReplayParentSet {
                    lower: lower_block.clone(),
                    upper,
                },
            });
        }

        let pair_replay = if requires_generic || !pair_upper_entries.is_empty() {
            Some(PreparedReplayParentSet {
                lower: lower_block,
                upper: prepared_parent_block_from_entries(pair_upper_entries),
                })
        } else {
            None
        };
        let routing = if requires_generic {
            ReplayRouting::Generic
        } else if pair_replay.is_some() || !prepared_incremental.is_empty() {
            ReplayRouting::IncrementalOnly
        } else {
            ReplayRouting::SkipAlreadyCovered
        };
        let prepared = PreparedReplayRoute {
            routing,
            proof_event: PreparedReplayParents {
                pair_replay,
                incremental_replays: prepared_incremental,
            },
        };
        self.validate_prepared_replay_route(lower, upper, &prepared)?;
        Ok(prepared)
        }

    fn prepare_replay_parent_block(
        &self,
        lower: BoundRecordId,
        upper: BoundRecordId,
        side: ReplayClaimParentSide,
        claims: &[UpperReplayClaimId],
        expected_record: Option<BoundRecordId>,
    ) -> Result<PreparedReplayParentBlock, ProofFailure> {
        self.prepare_replay_parent_entries(lower, upper, side, claims, expected_record)
            .map(prepared_parent_block_from_entries)
    }

    fn prepare_replay_parent_entries(
        &self,
        lower: BoundRecordId,
        upper: BoundRecordId,
        side: ReplayClaimParentSide,
        claims: &[UpperReplayClaimId],
        expected_record: Option<BoundRecordId>,
    ) -> Result<Vec<PreparedReplayParent>, ProofFailure> {
        let mut entries = Vec::new();
        entries
            .try_reserve(claims.len())
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::PrepareReplayRouteParentCollection,
            })?;
        let mut previous: Option<PreparedReplayParent> = None;
        for &claim in claims {
            let parent =
                self.resolve_prepared_replay_parent(lower, upper, side, claim, expected_record)?;
            if let Some(previous_parent) = previous {
                if previous_parent.coverage_root == parent.coverage_root {
                    return Err(ProofFailure::ReplayRoutingInvariantViolation {
                        lower,
                        upper,
                        kind: ReplayRoutingInvariantViolation::DuplicateParentRoot(side),
                    });
                }
                if (
                    previous_parent.coverage_root,
                    previous_parent.representative_claim,
                ) >= (parent.coverage_root, parent.representative_claim)
                {
                    return Err(ProofFailure::NonCanonicalReplayParentOrder { lower, upper, side });
                }
            }
            previous = Some(parent);
            entries.push(parent);
        }
        Ok(entries)
        }

    fn resolve_prepared_replay_parent(
        &self,
        lower: BoundRecordId,
        upper: BoundRecordId,
        side: ReplayClaimParentSide,
        claim: UpperReplayClaimId,
        expected_record: Option<BoundRecordId>,
    ) -> Result<PreparedReplayParent, ProofFailure> {
        let owner = match side {
            ReplayClaimParentSide::Lower => ProofFactRef::ProjectionSupports(lower),
            ReplayClaimParentSide::Upper => ProofFactRef::ReplayClaims(upper),
        };
        let occurrence =
            self.indexed_upper_claim(lower, upper, owner, claim, ProofFactRef::UpperClaim(claim))?;
        if expected_record.is_some_and(|record| occurrence.current_record != record) {
            return Err(ProofFailure::ReplayRoutingInvariantViolation {
                lower,
                upper,
                kind: ReplayRoutingInvariantViolation::ClaimIndexMismatch,
            });
        }
        let coverage_root = occurrence.coverage_root;
        let parent_owner = ProofFactRef::ReplayParent {
            lower,
            upper,
            side,
            coverage_root,
        };
        let root = self.indexed_upper_claim(
            lower,
            upper,
            parent_owner,
            coverage_root,
            ProofFactRef::CoverageRoot(coverage_root),
        )?;
        if root.claim != coverage_root || root.coverage_root != coverage_root {
            return Err(ProofFailure::ReplayRoutingInvariantViolation {
                lower,
                upper,
                kind: ReplayRoutingInvariantViolation::RepresentativeRootMismatch,
            });
        }
        Ok(PreparedReplayParent {
            side,
            coverage_root,
            representative_claim: occurrence.claim,
            lineage: occurrence.lineage,
        })
    }

    fn indexed_upper_claim(
        &self,
        lower: BoundRecordId,
        upper: BoundRecordId,
        owner: ProofFactRef,
        claim: UpperReplayClaimId,
        missing_target: ProofFactRef,
    ) -> Result<&UpperClaimOccurrence, ProofFailure> {
        let Some(index) = self.upper_claim_index.get(&claim).copied() else {
            return Err(ProofFailure::DanglingProofReference {
                owner,
                target: missing_target,
            });
        };
        let Some(occurrence) = self.upper_claims.get(index) else {
            return Err(ProofFailure::ReplayRoutingInvariantViolation {
                lower,
                upper,
                kind: ReplayRoutingInvariantViolation::ClaimIndexMismatch,
            });
        };
        if occurrence.claim != claim {
            return Err(ProofFailure::ReplayRoutingInvariantViolation {
                lower,
                upper,
                kind: ReplayRoutingInvariantViolation::ClaimIndexMismatch,
            });
        }
        Ok(occurrence)
    }

    fn validate_incremental_route_target(
        &self,
        lower: BoundRecordId,
        upper: BoundRecordId,
        route: &IncrementalRouteKey,
        upper_claims: &[UpperReplayClaimId],
    ) -> Result<(), ProofFailure> {
        if route.upper_record != upper {
            return Err(ProofFailure::ReplayRoutingInvariantViolation {
                lower,
                upper,
                kind: ReplayRoutingInvariantViolation::IncrementalUpperMismatch,
                });
            }
        let Some(claim) = route.claim else {
            return Ok(());
        };
        let owner = ProofFactRef::IncrementalReplayRoute(*route);
        let occurrence =
            self.indexed_upper_claim(lower, upper, owner, claim, ProofFactRef::UpperClaim(claim))?;
        if occurrence.current_record != upper {
            return Err(ProofFailure::ReplayRoutingInvariantViolation {
                lower,
                upper,
                kind: ReplayRoutingInvariantViolation::IncrementalClaimMismatch,
                });
            }
        let root = occurrence.coverage_root;
        let representative = upper_claims.binary_search_by(|candidate| {
            let Some(index) = self.upper_claim_index.get(candidate).copied() else {
                return std::cmp::Ordering::Less;
            };
            let Some(candidate) = self.upper_claims.get(index) else {
                return std::cmp::Ordering::Less;
            };
            canonical_upper_claim_key::cmp(candidate.coverage_root, root)
        });
        if !matches!(representative, Ok(position) if upper_claims[position] == claim) {
            return Err(ProofFailure::ReplayRoutingInvariantViolation {
                lower,
                upper,
                kind: ReplayRoutingInvariantViolation::IncrementalClaimMismatch,
            });
        }
        self.resolve_prepared_replay_parent(
            lower,
            upper,
            ReplayClaimParentSide::Upper,
            claim,
            Some(upper),
        )?;
        Ok(())
        }

    fn validate_prepared_replay_route(
        &self,
        lower: BoundRecordId,
        upper: BoundRecordId,
        prepared: &PreparedReplayRoute,
    ) -> Result<(), ProofFailure> {
        let payload_matches = match prepared.routing {
            ReplayRouting::Generic => prepared.proof_event.pair_replay.is_some(),
            ReplayRouting::IncrementalOnly => {
                prepared.proof_event.pair_replay.is_some()
                    || !prepared.proof_event.incremental_replays.is_empty()
            }
            ReplayRouting::SkipAlreadyCovered => {
                prepared.proof_event.pair_replay.is_none()
                    && prepared.proof_event.incremental_replays.is_empty()
            }
        };
        if !payload_matches {
            return Err(ProofFailure::ReplayRoutingInvariantViolation {
                lower,
                upper,
                kind: ReplayRoutingInvariantViolation::RoutingPayloadMismatch,
            });
        }
        if let Some(parents) = &prepared.proof_event.pair_replay {
            self.validate_prepared_parent_set(lower, upper, parents)?;
        }
        let mut seen = FxHashSet::default();
        seen.try_reserve(prepared.proof_event.incremental_replays.len())
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::PrepareReplayRouteBatch,
            })?;
        for incremental in &prepared.proof_event.incremental_replays {
            let key = (incremental.route.upper, incremental.route.upper_record);
            if !seen.insert(key) {
                return Err(ProofFailure::ReplayRoutingInvariantViolation {
                    lower,
                    upper,
                    kind: ReplayRoutingInvariantViolation::DuplicatePreparedIncrementalRoute,
                });
            }
            if incremental.route.upper_record != upper {
                return Err(ProofFailure::ReplayRoutingInvariantViolation {
                    lower,
                    upper,
                    kind: ReplayRoutingInvariantViolation::IncrementalUpperMismatch,
                });
            }
            self.validate_prepared_parent_set(lower, upper, &incremental.parents)?;
        }
        Ok(())
    }

    fn validate_prepared_parent_set(
        &self,
        lower: BoundRecordId,
        upper: BoundRecordId,
        parents: &PreparedReplayParentSet,
    ) -> Result<(), ProofFailure> {
        for (side, block) in [
            (ReplayClaimParentSide::Lower, &parents.lower),
            (ReplayClaimParentSide::Upper, &parents.upper),
        ] {
            let mut previous: Option<PreparedReplayParent> = None;
            for parent in block.as_slice() {
                let owner = ProofFactRef::ReplayParent {
                    lower,
                    upper,
                    side,
                    coverage_root: parent.coverage_root,
                };
                if parent.side != side {
                    return Err(ProofFailure::IncompleteMandatoryData {
                        owner,
                        field: MandatoryProofField::ReplayParentSide,
                    });
                }
                let occurrence = self.indexed_upper_claim(
                    lower,
                    upper,
                    owner,
                    parent.representative_claim,
                    ProofFactRef::UpperClaim(parent.representative_claim),
                )?;
                if occurrence.coverage_root != parent.coverage_root {
                    return Err(ProofFailure::ReplayRoutingInvariantViolation {
                        lower,
                        upper,
                        kind: ReplayRoutingInvariantViolation::RepresentativeRootMismatch,
                    });
                }
                if occurrence.lineage != parent.lineage {
                    return Err(ProofFailure::IncompleteMandatoryData {
                        owner,
                        field: MandatoryProofField::ReplayParentLineage,
                    });
                }
                let root = self.indexed_upper_claim(
                    lower,
                    upper,
                    owner,
                    parent.coverage_root,
                    ProofFactRef::CoverageRoot(parent.coverage_root),
                )?;
                if root.claim != parent.coverage_root || root.coverage_root != parent.coverage_root
                {
                    return Err(ProofFailure::ReplayRoutingInvariantViolation {
                        lower,
                        upper,
                        kind: ReplayRoutingInvariantViolation::RepresentativeRootMismatch,
                    });
                }
                if let Some(previous_parent) = previous {
                    if previous_parent.coverage_root == parent.coverage_root {
                        return Err(ProofFailure::ReplayRoutingInvariantViolation {
                            lower,
                            upper,
                            kind: ReplayRoutingInvariantViolation::DuplicateParentRoot(side),
                        });
                    }
                    if (
                        previous_parent.coverage_root,
                        previous_parent.representative_claim,
                    ) >= (parent.coverage_root, parent.representative_claim)
                    {
                        return Err(ProofFailure::NonCanonicalReplayParentOrder {
                            lower,
                            upper,
                            side,
                        });
                    }
                }
                previous = Some(*parent);
            }
        }
        Ok(())
    }

    pub(crate) fn project_lower<'a>(
        &'a self,
        view: &'a impl SemanticFactView,
        record: BoundRecordId,
        round: &mut ProjectionEvaluationRound<'a>,
    ) -> Result<ProjectionDecision, ProofFailure> {
        if let Some(failure) = &round.terminal_failure {
            return Err(failure.clone());
        }

        let result = self.project_lower_inner(view, record, round);
        if let Err(failure) = &result {
            round.states.clear();
            round.terminal_failure = Some(failure.clone());
        }
        result
    }

    fn project_lower_inner(
        &self,
        view: &impl SemanticFactView,
        record: BoundRecordId,
        round: &mut ProjectionEvaluationRound<'_>,
    ) -> Result<ProjectionDecision, ProofFailure> {
        let Some(bound) = view.bound(record) else {
            return Err(ProofFailure::MissingSemanticFact {
                fact: SemanticFactRef::Bound(record),
            });
        };
        if bound.direction() != BoundDirection::Lower
            || bound.state() == BoundRecordState::Tombstone
        {
            return Err(ProofFailure::InvalidProjectionTarget {
                record,
                direction: bound.direction(),
                state: bound.state(),
            });
        }

        let supports = self.projection_supports.get(&record);
        let formula = self.projection_formulas.get(&record);
        let has_supports = supports.is_some_and(|supports| !supports.is_empty());
        let has_formula = formula.is_some_and(|formula| !formula.is_empty());
        match (has_supports, has_formula) {
            (false, false) => return Ok(ProjectionDecision::Unclaimed),
            (false, true) => {
                return Err(ProofFailure::ProjectionInvariantViolation {
                    record,
                    kind: ProjectionInvariantViolation::OrphanFormula,
                });
            }
            (true, false) => {
                return Err(ProofFailure::MissingProofFact {
                    fact: ProofFactRef::ProjectionFormula(record),
                });
            }
            (true, true) => {}
        }

        let mut preflight = ProjectionPreflight::new(self, view, record);
        preflight.validate_record(record, ProofFactRef::ProjectionSupports(record))?;

        let supports = supports.expect("non-empty supports were classified above");
        let claimed_count = supports
            .iter()
            .filter(|support| matches!(support, SchemeProjectionProofSupport::Claimed(_)))
            .count();
        let independent_count = supports.len() - claimed_count;
        let mut payload = ProjectionSupportSet::default();
        payload
            .uncovered_claims
            .try_reserve_exact(claimed_count)
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::ProjectLowerSupportCollection,
            })?;
        payload
            .independent_supports
            .try_reserve_exact(independent_count)
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::ProjectLowerSupportCollection,
            })?;
        for support in supports {
            match *support {
                SchemeProjectionProofSupport::Claimed(claim) => {
                    let resolved = preflight.resolve_claim(
                        record,
                        claim,
                        ProofFactRef::ProjectionSupports(record),
                    )?;
                    if !self
                        .live_coverage
                        .iter()
                        .any(|(root, _)| *root == resolved.coverage_root)
                    {
                        payload.uncovered_claims.push(resolved);
                    }
                }
                SchemeProjectionProofSupport::Independent(carrier) => {
                    payload.independent_supports.push(carrier);
                }
            }
        }

        let evaluation_nodes =
            preflight.checked_records.len() + preflight.checked_constraints.len();
        let sharing_was_disabled = round.memo_sharing_disabled;
        let mut states = if sharing_was_disabled {
            FxHashMap::default()
        } else {
            std::mem::take(&mut round.states)
        };
        states
            .try_reserve(evaluation_nodes.saturating_sub(states.len()))
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::ProjectLowerEvaluation,
            })?;
        let mut evaluator = CpkProjectionEvaluator::new(view, self);
        evaluator.states = states;
        let included = evaluator.eval_record(record);
        if evaluator
            .states
            .values()
            .any(|state| *state == ProofEvalState::Visiting)
        {
            return Err(ProofFailure::ProjectionInvariantViolation {
                record,
                kind: ProjectionInvariantViolation::VisitingStateEscaped,
            });
        }
        let cycle_cuts = evaluator.cycle_cuts();
        round.cycle_cuts += cycle_cuts;
        if cycle_cuts != 0 {
            round.memo_sharing_disabled = true;
            round.states.clear();
        } else if !sharing_was_disabled {
            round.states = std::mem::take(&mut evaluator.states);
        }

        Ok(if included {
            ProjectionDecision::Included { supports: payload }
        } else {
            ProjectionDecision::Excluded
        })
    }
}

struct ProjectionPreflight<'a> {
    store: &'a ProofOccurrenceStore,
    view: &'a dyn SemanticFactView,
    target_record: BoundRecordId,
    visiting_records: FxHashSet<BoundRecordId>,
    checked_records: FxHashSet<BoundRecordId>,
    visiting_constraints: FxHashSet<ConstraintRecordId>,
    checked_constraints: FxHashSet<ConstraintRecordId>,
}

impl<'a> ProjectionPreflight<'a> {
    fn new(
        store: &'a ProofOccurrenceStore,
        view: &'a dyn SemanticFactView,
        target_record: BoundRecordId,
    ) -> Self {
        Self {
            store,
            view,
            target_record,
            visiting_records: FxHashSet::default(),
            checked_records: FxHashSet::default(),
            visiting_constraints: FxHashSet::default(),
            checked_constraints: FxHashSet::default(),
        }
    }

    fn validate_record(
        &mut self,
        record: BoundRecordId,
        owner: ProofFactRef,
    ) -> Result<(), ProofFailure> {
        let Some(bound) = self.view.bound(record) else {
            return Err(self.dangling(
                owner,
                ProofFactRef::Semantic(SemanticFactRef::Bound(record)),
            ));
        };
        if bound.state() == BoundRecordState::Tombstone
            || self.checked_records.contains(&record)
            || !self.visiting_records.insert(record)
        {
            return Ok(());
        }

        let result = match bound.direction() {
            BoundDirection::Upper => {
                let claims = self
                    .store
                    .upper_claims
                    .iter()
                    .filter(|claim| claim.current_record == record)
                    .map(|claim| claim.claim)
                    .collect::<Vec<_>>();
                for claim in claims {
                    self.validate_claim_reference(owner, claim)?;
                }
                Ok(())
            }
            BoundDirection::Lower => self.validate_projection_record(record),
        };
        self.visiting_records.remove(&record);
        if result.is_ok() {
            self.checked_records.insert(record);
        }
        result
    }

    fn validate_projection_record(&mut self, record: BoundRecordId) -> Result<(), ProofFailure> {
        let supports = self.store.projection_supports.get(&record);
        let clauses = self.store.projection_formulas.get(&record);
        let has_supports = supports.is_some_and(|supports| !supports.is_empty());
        let has_clauses = clauses.is_some_and(|clauses| !clauses.is_empty());
        match (has_supports, has_clauses) {
            (false, false) => return Ok(()),
            (false, true) => {
                return Err(ProofFailure::ProjectionInvariantViolation {
                    record,
                    kind: ProjectionInvariantViolation::OrphanFormula,
                });
            }
            (true, false) => {
                return Err(ProofFailure::MissingProofFact {
                    fact: ProofFactRef::ProjectionFormula(record),
                });
            }
            (true, true) => {}
        }

        let supports = supports.expect("non-empty supports were classified above");
        let clauses = clauses.expect("non-empty clauses were classified above");
        let mut resolved: Vec<ResolvedProjectionSupport> = Vec::new();
        resolved.try_reserve_exact(supports.len()).map_err(|_| {
            ProofFailure::ResourceExhausted {
                operation: ProofOperation::ProjectLowerPreflight,
            }
        })?;
        for support in supports {
            let support = self.resolve_support(record, *support)?;
            if let Some(previous) = resolved.last().copied() {
                match previous.cmp(support) {
                    std::cmp::Ordering::Less => {}
                    std::cmp::Ordering::Equal => {
                        let kind = match support {
                            ResolvedProjectionSupport::Claimed(_) => {
                                ProjectionInvariantViolation::DuplicateClaimedRoot
                            }
                            ResolvedProjectionSupport::Independent(_) => {
                                ProjectionInvariantViolation::DuplicateIndependentCarrier
                            }
                        };
                        return Err(ProofFailure::ProjectionInvariantViolation { record, kind });
                    }
                    std::cmp::Ordering::Greater => {
                        return Err(ProofFailure::NonCanonicalProjectionOrder { record });
                    }
                }
            }
            resolved.push(support);
        }

        if clauses
            .windows(2)
            .any(|pair| pair[0].category_rank() > pair[1].category_rank())
        {
            return Err(ProofFailure::NonCanonicalProjectionOrder { record });
        }

        let mut matched = Vec::new();
        matched
            .try_reserve_exact(resolved.len())
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::ProjectLowerPreflight,
            })?;
        matched.resize(resolved.len(), false);
        for clause in clauses.iter().copied() {
            let clause_support = self.resolve_support(record, clause.support())?;
            let Some(index) = resolved
                .iter()
                .position(|support| support.same_key(clause_support))
            else {
                return Err(ProofFailure::ProjectionInvariantViolation {
                    record,
                    kind: ProjectionInvariantViolation::OrphanFormula,
                });
            };
            matched[index] = true;
            self.validate_clause(record, clause)?;
        }
        if matched.iter().any(|matched| !matched) {
            return Err(ProofFailure::MissingProofFact {
                fact: ProofFactRef::ProjectionFormula(record),
            });
        }
        Ok(())
    }

    fn resolve_support(
        &mut self,
        record: BoundRecordId,
        support: SchemeProjectionProofSupport,
    ) -> Result<ResolvedProjectionSupport, ProofFailure> {
        match support {
            SchemeProjectionProofSupport::Claimed(claim) => self
                .resolve_claim(record, claim, ProofFactRef::ProjectionSupports(record))
                .map(ResolvedProjectionSupport::Claimed),
            SchemeProjectionProofSupport::Independent(carrier) => {
                self.validate_carrier(record, carrier)?;
                Ok(ResolvedProjectionSupport::Independent(carrier))
            }
        }
    }

    fn resolve_claim(
        &mut self,
        record: BoundRecordId,
        claim: UpperReplayClaimId,
        owner: ProofFactRef,
    ) -> Result<ProjectionClaimSupport, ProofFailure> {
        let Some(representative) = self.store.upper_claim(claim) else {
            return Err(self.dangling(owner, ProofFactRef::UpperClaim(claim)));
        };
        let root = representative.coverage_root;
        let Some(root_claim) = self.store.upper_claim(root) else {
            return Err(self.dangling(owner, ProofFactRef::CoverageRoot(root)));
        };
        if root_claim.coverage_root != root {
            return Err(ProofFailure::ProjectionInvariantViolation {
                record,
                kind: ProjectionInvariantViolation::RepresentativeRootMismatch,
            });
        }
        self.validate_bound_reference(owner, representative.current_record)?;
        self.validate_bound_reference(owner, root_claim.current_record)?;
        for (_, state) in self
            .store
            .live_coverage
            .iter()
            .filter(|(candidate, _)| *candidate == root)
        {
            if self.view.row_reduction(*state).is_none() {
                return Err(self.dangling(owner, ProofFactRef::RowReduction(*state)));
            }
        }
        Ok(ProjectionClaimSupport {
            coverage_root: root,
            representative_claim: claim,
        })
    }

    fn validate_clause(
        &mut self,
        record: BoundRecordId,
        clause: ProjectionClause,
    ) -> Result<(), ProofFailure> {
        let owner = ProofFactRef::ProjectionFormula(record);
        match clause {
            ProjectionClause::Standalone { .. } => Ok(()),
            ProjectionClause::DerivedUnary {
                carrier, premise, ..
            } => {
                match carrier {
                    DerivedUnaryCarrier::Structural(derivation) => {
                        self.validate_constraint(derivation.parent, owner)?;
                    }
                    DerivedUnaryCarrier::ReductionRoute(derivation) => {
                        self.validate_row_derivation(owner, derivation)?;
                    }
                }
                self.validate_premise(owner, premise)
            }
            ProjectionClause::ReplayConjunction {
                carrier,
                lower,
                upper,
                ..
            } => {
                self.validate_bound_reference(owner, carrier.lower)?;
                self.validate_bound_reference(owner, carrier.upper)?;
                self.validate_record(lower, owner)?;
                self.validate_record(upper, owner)
            }
        }
    }

    fn validate_premise(
        &mut self,
        owner: ProofFactRef,
        premise: ProofPremise,
    ) -> Result<(), ProofFailure> {
        match premise {
            ProofPremise::Record(record) => self.validate_record(record, owner),
            ProofPremise::Constraint(constraint) => self.validate_constraint(constraint, owner),
            ProofPremise::RootCoverage(root) => {
                self.validate_claim_reference(owner, root).map(|_| ())
            }
        }
    }

    fn validate_constraint(
        &mut self,
        constraint: ConstraintRecordId,
        owner: ProofFactRef,
    ) -> Result<(), ProofFailure> {
        if self.view.constraint(constraint).is_none() {
            return Err(self.dangling(
                owner,
                ProofFactRef::Semantic(SemanticFactRef::Constraint(constraint)),
            ));
        }
        if self.checked_constraints.contains(&constraint)
            || !self.visiting_constraints.insert(constraint)
        {
            return Ok(());
        }

        let result = (|| {
            if let Some(lower) = self.view.lower_record_for_constraint(constraint) {
                self.validate_record(lower, owner)?;
            }
            let replays = self
                .store
                .replay_finite_map
                .iter()
                .filter(|occurrence| occurrence.result == constraint)
                .map(|occurrence| occurrence.carrier)
                .collect::<Vec<_>>();
            for replay in replays {
                self.validate_record(replay.lower, owner)?;
                self.validate_record(replay.upper, owner)?;
            }
            let sources = self
                .store
                .occurrences
                .iter()
                .filter(|occurrence| {
                    occurrence.result
                        == ProofResult::Semantic(SemanticFactRef::Constraint(constraint))
                })
                .filter_map(|occurrence| match occurrence.cause {
                    ProofCause::Structural(derivation) => Some(Ok(derivation.parent)),
                    ProofCause::ReductionRoute { parent_claim, .. } => Some(Err(parent_claim)),
                    _ => None,
                })
                .collect::<Vec<_>>();
            for source in sources {
                match source {
                    Ok(parent) => self.validate_constraint(parent, owner)?,
                    Err(root) => {
                        self.validate_claim_reference(owner, root)?;
                    }
                }
            }
            let roots = self
                .store
                .upper_claims
                .iter()
                .filter(|claim| {
                    claim.producer == constraint && claim.lineage == ProjectionLineage::Original
                })
                .map(|claim| claim.claim)
                .collect::<Vec<_>>();
            for root in roots {
                self.validate_claim_reference(owner, root)?;
            }
            Ok(())
        })();
        self.visiting_constraints.remove(&constraint);
        if result.is_ok() {
            self.checked_constraints.insert(constraint);
        }
        result
    }

    fn validate_carrier(
        &mut self,
        record: BoundRecordId,
        carrier: ProjectionProofCarrier,
    ) -> Result<(), ProofFailure> {
        let owner = ProofFactRef::ProjectionSupport {
            record,
            support: ProjectionSupportIdentity::Independent(carrier),
        };
        let missing_carrier = || ProofFailure::DanglingProofReference {
            owner: ProofFactRef::ProjectionSupports(record),
            target: owner,
        };
        match carrier {
            ProjectionProofCarrier::ConstraintOrigin { constraint, origin } => {
                if self.view.constraint(constraint).is_none() {
                    return Err(self.dangling(
                        owner,
                        ProofFactRef::Semantic(SemanticFactRef::Constraint(constraint)),
                    ));
                }
                if !self.store.occurrences.iter().any(|occurrence| {
                        occurrence.result
                            == ProofResult::Semantic(SemanticFactRef::Constraint(constraint))
                            && matches!(occurrence.cause, ProofCause::Root(candidate) if candidate == origin)
                    }) {
                    return Err(self.dangling(owner, ProofFactRef::Origin(origin)));
                }
            }
            ProjectionProofCarrier::StructuralConstraint { result, derivation } => {
                if self.view.constraint(result).is_none() {
                    return Err(self.dangling(
                        owner,
                        ProofFactRef::Semantic(SemanticFactRef::Constraint(result)),
                    ));
                }
                if self.view.constraint(derivation.parent).is_none() {
                    return Err(self.dangling(
                        owner,
                        ProofFactRef::Semantic(SemanticFactRef::Constraint(derivation.parent)),
                    ));
                }
                if !self.store.occurrences.iter().any(|occurrence| {
                        occurrence.result
                            == ProofResult::Semantic(SemanticFactRef::Constraint(result))
                            && matches!(&occurrence.cause, ProofCause::Structural(candidate) if *candidate == derivation)
                    }) {
                    return Err(missing_carrier());
                }
            }
            ProjectionProofCarrier::ReplayConstraint { result, derivation } => {
                if self.view.constraint(result).is_none() {
                    return Err(self.dangling(
                        owner,
                        ProofFactRef::Semantic(SemanticFactRef::Constraint(result)),
                    ));
                }
                self.validate_bound_reference(owner, derivation.lower)?;
                self.validate_bound_reference(owner, derivation.upper)?;
                if !self.store.replay_finite_map.iter().any(|occurrence| {
                    occurrence.result == result && occurrence.carrier == derivation
                }) {
                    return Err(missing_carrier());
                }
            }
            ProjectionProofCarrier::RowConstraint { result, derivation } => {
                if self.view.constraint(result).is_none() {
                    return Err(self.dangling(
                        owner,
                        ProofFactRef::Semantic(SemanticFactRef::Constraint(result)),
                    ));
                }
                self.validate_row_derivation(owner, derivation)?;
                if !self.store.occurrences.iter().any(|occurrence| {
                        occurrence.result
                            == ProofResult::Semantic(SemanticFactRef::Constraint(result))
                            && matches!(occurrence.cause, ProofCause::RowConstraint(candidate) if candidate == derivation)
                    }) {
                    return Err(missing_carrier());
                }
            }
            ProjectionProofCarrier::SchemeInstantiationConstraint {
                result,
                source_witness,
            } => {
                if self.view.constraint(result).is_none() {
                    return Err(self.dangling(
                        owner,
                        ProofFactRef::Semantic(SemanticFactRef::Constraint(result)),
                    ));
                }
                if !self.store.occurrences.iter().any(|occurrence| {
                    occurrence.result == ProofResult::Semantic(SemanticFactRef::Constraint(result))
                        && match &occurrence.cause {
                            ProofCause::SchemeInstantiationDerivation(derivation) => {
                                derivation.source_witness == source_witness
                            }
                            ProofCause::SchemeInstantiationRoute(route) => {
                                route.derivation.source_witness == source_witness
                            }
                            _ => false,
                        }
                }) {
                    return Err(
                        self.dangling(owner, ProofFactRef::GeneralizedWitness(source_witness))
                    );
                }
            }
            ProjectionProofCarrier::Origin(origin) => {
                if !self.has_origin(origin) {
                    return Err(self.dangling(owner, ProofFactRef::Origin(origin)));
                }
            }
            ProjectionProofCarrier::ReplayEvidence(derivation) => {
                self.validate_bound_reference(owner, derivation.lower)?;
                self.validate_bound_reference(owner, derivation.upper)?;
                if !self.store.occurrences.iter().any(|occurrence| {
                        matches!(&occurrence.cause, ProofCause::ReplayEvidence(candidate) if *candidate == derivation)
                    }) {
                    return Err(missing_carrier());
                }
            }
            ProjectionProofCarrier::Row(derivation) => {
                self.validate_row_derivation(owner, derivation)?;
            }
            ProjectionProofCarrier::SchemeInstantiation(witness) => {
                if !self.has_generalized_witness(witness) {
                    return Err(self.dangling(owner, ProofFactRef::GeneralizedWitness(witness)));
                }
            }
            ProjectionProofCarrier::Incomplete => {}
        }
        Ok(())
    }

    fn validate_claim_reference(
        &mut self,
        owner: ProofFactRef,
        claim: UpperReplayClaimId,
    ) -> Result<ProjectionClaimSupport, ProofFailure> {
        self.resolve_claim(self.target_record, claim, owner)
    }

    fn validate_bound_reference(
        &self,
        owner: ProofFactRef,
        record: BoundRecordId,
    ) -> Result<(), ProofFailure> {
        self.view.bound(record).map(|_| ()).ok_or_else(|| {
            self.dangling(
                owner,
                ProofFactRef::Semantic(SemanticFactRef::Bound(record)),
            )
        })
    }

    fn validate_row_derivation(
        &self,
        owner: ProofFactRef,
        derivation: RowDerivationId,
    ) -> Result<(), ProofFailure> {
        self.has_row_derivation(derivation)
            .then_some(())
            .ok_or_else(|| self.dangling(owner, ProofFactRef::RowDerivation(derivation)))
    }

    fn has_origin(&self, origin: OriginId) -> bool {
        self.store.occurrences.iter().any(|occurrence| {
            matches!(occurrence.cause, ProofCause::Root(candidate) if candidate == origin)
                || matches!(occurrence.cause, ProofCause::Bound(BoundDerivation::Origin(candidate)) if candidate == origin)
                || occurrence
                    .parents
                    .iter()
                    .any(|parent| *parent == ProofParent::Origin(origin))
        })
    }

    fn has_row_derivation(&self, derivation: RowDerivationId) -> bool {
        self.store.occurrences.iter().any(|occurrence| {
            occurrence.result == ProofResult::Semantic(SemanticFactRef::RowDerivation(derivation))
        })
    }

    fn has_generalized_witness(&self, witness: GeneralizedSchemeWitnessId) -> bool {
        self.store.occurrences.iter().any(|occurrence| {
            occurrence
                .parents
                .iter()
                .any(|parent| *parent == ProofParent::GeneralizedWitness(witness))
        })
    }

    fn dangling(&self, owner: ProofFactRef, target: ProofFactRef) -> ProofFailure {
        ProofFailure::DanglingProofReference { owner, target }
    }
}

impl ProofOccurrenceStore {
    fn upper_claim(&self, claim: UpperReplayClaimId) -> Option<&UpperClaimOccurrence> {
        let index = self.upper_claim_index.get(&claim).copied()?;
        self.upper_claims.get(index)
    }
}

pub(super) struct CpkProjectionEvaluator<'a> {
    view: &'a dyn SemanticFactView,
    store: &'a ProofOccurrenceStore,
    states: FxHashMap<ProofEvalNode, ProofEvalState>,
    record_overrides: FxHashMap<BoundRecordId, bool>,
    root_overrides: FxHashMap<UpperReplayClaimId, bool>,
    cycle_cuts: usize,
}

impl<'a> CpkProjectionEvaluator<'a> {
    pub(super) fn new(
        view: &'a dyn SemanticFactView,
        store: &'a ProofOccurrenceStore,
    ) -> Self {
        Self {
            view,
            store,
            states: FxHashMap::default(),
            record_overrides: FxHashMap::default(),
            root_overrides: FxHashMap::default(),
            cycle_cuts: 0,
        }
    }

    pub(super) fn eval_record(&mut self, record: BoundRecordId) -> bool {
        if let Some(result) = self.record_overrides.get(&record) {
            return *result;
        }
        let node = ProofEvalNode::Record(record);
        if let Some(result) = self.enter(node) {
            return result;
        }
        let result = self.eval_record_uncached(record);
        self.finish(node, result)
    }

    fn eval_record_uncached(&mut self, record: BoundRecordId) -> bool {
        let Some(bound) = self.view.bound(record) else {
            return true;
        };
        if bound.state() == BoundRecordState::Tombstone {
            return true;
        }
        if bound.direction() == BoundDirection::Upper {
            let claims = self
                .store
                .upper_claims
                .iter()
                .filter(|claim| claim.current_record == record)
                .collect::<Vec<_>>();
            return claims.is_empty()
                || claims
                    .into_iter()
                    .any(|claim| self.eval_root_coverage(claim.claim));
        }

        let Some(supports) = self.store.projection_supports.get(&record) else {
            return true;
        };
        if supports.is_empty() {
            return true;
        }
        let clauses = self.store.projection_formulas.get(&record);
        if supports.iter().copied().any(|support| {
            self.support_is_qualifying(support)
                && !clauses.is_some_and(|clauses| {
                    clauses.iter().copied().any(|clause| {
                        self.supports_match(support, clause.support())
                    })
                })
        }) {
            return true;
        }
        clauses.is_some_and(|clauses| {
            clauses
                .iter()
                .copied()
                .any(|clause| self.eval_clause(clause))
        })
    }

    fn eval_clause(&mut self, clause: ProjectionClause) -> bool {
        match clause {
            ProjectionClause::Standalone { support, .. } => {
                self.support_is_qualifying(support)
            }
            ProjectionClause::DerivedUnary { premise, .. } => self.eval_premise(premise),
            ProjectionClause::ReplayConjunction { lower, upper, .. } => {
                self.eval_record(lower) && self.eval_record(upper)
            }
        }
    }

    fn eval_premise(&mut self, premise: ProofPremise) -> bool {
        match premise {
            ProofPremise::Record(record) => self.eval_record(record),
            ProofPremise::Constraint(constraint) => self.eval_constraint(constraint),
            ProofPremise::RootCoverage(root) => self.eval_root_coverage(root),
        }
    }

    fn eval_constraint(&mut self, constraint: ConstraintRecordId) -> bool {
        let node = ProofEvalNode::Constraint(constraint);
        if let Some(result) = self.enter(node) {
            return result;
        }
        let result = self.eval_constraint_uncached(constraint);
        self.finish(node, result)
    }

    fn eval_constraint_uncached(&mut self, constraint: ConstraintRecordId) -> bool {
        if self.view.constraint(constraint).is_none() {
            return true;
        }
        let mut has_source = false;
        if let Some(lower_record) = self.view.lower_record_for_constraint(constraint) {
            has_source = true;
            if self.eval_record(lower_record) {
                return true;
            }
        }
        let replay_carriers = self
            .store
            .replay_finite_map
            .iter()
            .filter(|occurrence| occurrence.result == constraint)
            .map(|occurrence| occurrence.carrier)
            .collect::<Vec<_>>();
        for replay in replay_carriers {
            has_source = true;
            if self.eval_record(replay.lower) && self.eval_record(replay.upper) {
                return true;
            }
        }
        let non_replay = self
            .store
            .occurrences
            .iter()
            .filter(|occurrence| {
                occurrence.result
                    == ProofResult::Semantic(SemanticFactRef::Constraint(constraint))
            })
            .filter_map(|occurrence| match occurrence.cause {
                ProofCause::Structural(derivation) => Some(Ok(derivation.parent)),
                ProofCause::ReductionRoute { parent_claim, .. } => Some(Err(parent_claim)),
                _ => None,
            })
            .collect::<Vec<_>>();
        for source in non_replay {
            has_source = true;
            let projectable = match source {
                Ok(parent) => self.eval_constraint(parent),
                Err(root) => self.eval_root_coverage(root),
            };
            if projectable {
                return true;
            }
        }
        let producer_roots = self
            .store
            .upper_claims
            .iter()
            .filter(|claim| {
                claim.producer == constraint && claim.lineage == ProjectionLineage::Original
            })
            .map(|claim| claim.claim)
            .collect::<Vec<_>>();
        for root in producer_roots {
            has_source = true;
            if self.eval_root_coverage(root) {
                return true;
            }
        }
        !has_source
    }

    fn eval_root_coverage(&self, claim: UpperReplayClaimId) -> bool {
        let Some(root) = self
            .store
            .upper_claims
            .iter()
            .find(|candidate| candidate.claim == claim)
            .map(|claim| claim.coverage_root)
        else {
            return true;
        };
        if let Some(result) = self.root_overrides.get(&root) {
            return *result;
        }
        !self
            .store
            .live_coverage
            .iter()
            .any(|(candidate, _)| *candidate == root)
    }

    fn support_is_qualifying(&self, support: SchemeProjectionProofSupport) -> bool {
        match support {
            SchemeProjectionProofSupport::Independent(_) => true,
            SchemeProjectionProofSupport::Claimed(claim) => self.eval_root_coverage(claim),
        }
    }

    fn supports_match(
        &self,
        left: SchemeProjectionProofSupport,
        right: SchemeProjectionProofSupport,
    ) -> bool {
        match (left, right) {
            (
                SchemeProjectionProofSupport::Independent(left),
                SchemeProjectionProofSupport::Independent(right),
            ) => left == right,
            (
                SchemeProjectionProofSupport::Claimed(left),
                SchemeProjectionProofSupport::Claimed(right),
            ) => {
                let root = |claim| {
                    self.store
                        .upper_claims
                        .iter()
                        .find(|candidate| candidate.claim == claim)
                        .map(|claim| claim.coverage_root)
                };
                root(left).is_some() && root(left) == root(right)
            }
            _ => false,
        }
    }

    fn enter(&mut self, node: ProofEvalNode) -> Option<bool> {
        match self.states.get(&node).copied() {
            Some(ProofEvalState::Done(result)) => Some(result),
            Some(ProofEvalState::Visiting) => {
                self.cycle_cuts += 1;
                Some(false)
            }
            None => {
                self.states.insert(node, ProofEvalState::Visiting);
                None
            }
        }
    }

    fn finish(&mut self, node: ProofEvalNode, result: bool) -> bool {
        self.states.insert(node, ProofEvalState::Done(result));
        result
    }

    pub(super) fn cycle_cuts(&self) -> usize {
        self.cycle_cuts
    }
}

#[cfg(test)]
pub(super) fn compare_projection_record_shadow(
    machine: &ConstraintMachine,
    record: BoundRecordId,
    legacy_result: bool,
    legacy_cycle_cuts: usize,
) {
    if !machine.cpk_proof_oracle_active {
        return;
    }
    let snapshot = &machine.proof_store;
    if machine
        .bounds
        .projection_proofs_by_lower_record
        .contains_key(&record)
        && !snapshot.projection_supports.contains_key(&record)
    {
        // Capture began after this record's writer events; it is not a complete shadow view.
        return;
    }
    let mut evaluator = CpkProjectionEvaluator::new(machine, &snapshot);
    let shadow_result = evaluator.eval_record(record);
    let observation = ShadowProjectabilityObservation {
        record,
        legacy: legacy_result,
        shadow: shadow_result,
        legacy_cycle_cut: legacy_cycle_cuts != 0,
        shadow_cycle_cut: evaluator.cycle_cuts() != 0,
    };
    assert_eq!(shadow_result, legacy_result, "CPK-4 projectability diverged");
    assert_eq!(
        observation.shadow_cycle_cut, observation.legacy_cycle_cut,
        "CPK-4 cycle-cut behavior diverged"
    );
    snapshot
        .projectability_observations
        .borrow_mut()
        .push(observation);
}

#[cfg(test)]
pub(super) fn compare_projection_publication_shadow(
    machine: &ConstraintMachine,
    lower_record: BoundRecordId,
    was_included: bool,
    is_included: bool,
    metadata_changed: bool,
    legacy_intent: &SchemeProjectionPublicationIntent,
) {
    if !machine.cpk_proof_oracle_active {
        return;
    }
    let snapshot = &machine.proof_store;
    if machine
        .bounds
        .projection_proofs_by_lower_record
        .keys()
        .any(|record| !snapshot.projection_supports.contains_key(record))
        || machine
            .bounds
            .record_proof_clause_links_by_lower_record
            .keys()
            .any(|record| !snapshot.projection_formulas.contains_key(record))
        || machine.bounds.upper_replay_claims.len() != snapshot.upper_claims.len()
    {
        // Capture began after an input writer event, so the shadow cannot classify this event.
        return;
    }

    let mut current = CpkProjectionEvaluator::new(machine, &snapshot);
    let shadow_is_included = current.eval_record(lower_record);
    assert_eq!(
        shadow_is_included, is_included,
        "CPK-4 publication oracle observed divergent current projectability",
    );

    let mut shadow_affected_owners = FxHashSet::default();
    if was_included != shadow_is_included {
        for (index, record) in machine.bounds.records.iter().enumerate() {
            if record.direction() != BoundDirection::Lower
                || record.state() == BoundRecordState::Tombstone
            {
                continue;
            }
            let record_id = BoundRecordId(index as u32);
            let mut before = CpkProjectionEvaluator::new(machine, &snapshot);
            before.record_overrides.insert(lower_record, was_included);
            let before = before.eval_record(record_id);
            let mut after = CpkProjectionEvaluator::new(machine, &snapshot);
            let after = after.eval_record(record_id);
            if before != after {
                shadow_affected_owners.insert(record.owner());
            }
        }
    }

    let (legacy_class, legacy_affected_owners) = match legacy_intent {
        SchemeProjectionPublicationIntent::None => (
            ShadowProjectionPublicationClass::None,
            FxHashSet::default(),
        ),
        SchemeProjectionPublicationIntent::MetadataOnly => (
            ShadowProjectionPublicationClass::MetadataOnly,
            FxHashSet::default(),
        ),
        SchemeProjectionPublicationIntent::OwnersChanged(owners) => (
            ShadowProjectionPublicationClass::InclusionFlip,
            owners.clone(),
        ),
    };
    let shadow_class = if !shadow_affected_owners.is_empty() {
        ShadowProjectionPublicationClass::InclusionFlip
    } else if metadata_changed {
        ShadowProjectionPublicationClass::MetadataOnly
    } else {
        ShadowProjectionPublicationClass::None
    };
    assert_eq!(
        shadow_affected_owners, legacy_affected_owners,
        "CPK-4 affected-owner set diverged",
    );
    assert_eq!(
        shadow_class, legacy_class,
        "CPK-4 projection publication class diverged",
    );

    let sorted = |owners: FxHashSet<TypeVar>| {
        let mut owners = owners.into_iter().collect::<Vec<_>>();
        owners.sort_by_key(|owner| owner.0);
        owners
    };
    snapshot
        .projection_publication_observations
        .borrow_mut()
        .push(ShadowProjectionPublicationObservation {
            lower_record,
            legacy_class,
            shadow_class,
            legacy_affected_owners: sorted(legacy_affected_owners),
            shadow_affected_owners: sorted(shadow_affected_owners),
        });
}

#[cfg(test)]
pub(super) fn begin_replay_routing_shadow(
    machine: &ConstraintMachine,
) -> Option<ReplayRoutingShadowToken> {
    if !machine.cpk_proof_oracle_active {
        return None;
    }
    Some(ReplayRoutingShadowToken {
        routes_before: machine
            .proof_store
            .replay_route_observations
            .borrow()
            .len(),
        admissions_before: machine.proof_store.replay_admissions.len(),
        canonical_constraints_before: machine.canonical_constraints.len(),
    })
}

#[cfg(test)]
pub(super) fn compare_replay_route_shadow(
    machine: &ConstraintMachine,
    lower: BoundRecordId,
    upper: BoundRecordId,
    incremental_routes: &[UnweightedRowReductionReplayRoute],
    legacy_requires_generic: bool,
    legacy_pair_replay: bool,
    legacy_pair_parents: &[SideTaggedReplayClaim],
) {
    if !machine.cpk_proof_oracle_active {
        return;
    }
    let snapshot = &machine.proof_store;
    assert_eq!(
        machine.bounds.upper_replay_claims.len(),
        snapshot.upper_claims.len(),
        "CPK-7 upper-claim mirror census diverged",
    );
    assert_eq!(
        machine
            .bounds
            .projection_proofs_by_lower_record
            .contains_key(&lower),
        snapshot.projection_supports.contains_key(&lower),
        "CPK-7 lower projection mirror census diverged",
    );
    let incremental_routes = incremental_routes
        .iter()
        .filter(|route| route.upper_record == upper)
        .map(|route| IncrementalRouteKey {
            upper: route.upper,
            upper_record: route.upper_record,
            provenance: route.provenance,
            claim: route.claim,
        })
        .collect::<Vec<_>>();
    let has_incremental_route = !incremental_routes.is_empty();
    let legacy = if legacy_requires_generic {
        ReplayRouting::Generic
    } else if legacy_pair_replay || has_incremental_route {
        ReplayRouting::IncrementalOnly
    } else {
        ReplayRouting::SkipAlreadyCovered
    };

    let prepared = snapshot
        .prepare_replay_route(machine, lower, upper, &incremental_routes)
        .expect("CPK-7 replay routing shadow preflight failed");
    let legacy_prepared = legacy_prepared_replay_route(
        machine,
        lower,
        upper,
        legacy,
        legacy_requires_generic,
        legacy_pair_replay,
        legacy_pair_parents,
        &incremental_routes,
    );
    assert_eq!(
        prepared, legacy_prepared,
        "CPK-7 exact replay routing plan diverged",
    );
    snapshot
        .replay_route_observations
        .borrow_mut()
        .push(ShadowReplayRouteObservation {
            lower,
            upper,
            legacy,
            shadow: prepared.routing,
            lower_parent_roots: prepared
                .proof_event
                .pair_replay
                .as_ref()
                .map_or(0, |parents| parents.lower.as_slice().len()),
            upper_parent_roots: prepared
                .proof_event
                .pair_replay
                .as_ref()
                .map_or(0, |parents| parents.upper.as_slice().len()),
            legacy_prepared,
            shadow_prepared: prepared,
        });
}

#[cfg(test)]
fn legacy_prepared_replay_route(
    machine: &ConstraintMachine,
    lower_record: BoundRecordId,
    upper: BoundRecordId,
    routing: ReplayRouting,
    requires_generic: bool,
    pair_replay: bool,
    pair_parents: &[SideTaggedReplayClaim],
    incremental_routes: &[IncrementalRouteKey],
) -> PreparedReplayRoute {
    let canonicalize = |parents: &[SideTaggedReplayClaim]| {
        let mut parents = parents
            .iter()
            .map(|parent| {
                let claim = &machine.bounds.upper_replay_claims[parent.claim.0 as usize];
                assert_eq!(claim.id, parent.claim, "Legacy replay parent claim is dangling");
                PreparedReplayParent {
                    side: parent.parent_side,
                    coverage_root: claim.coverage_root,
                    representative_claim: parent.claim,
                    lineage: projection_lineage(claim.lineage),
                }
            })
            .collect::<Vec<_>>();
        parents.sort_by_key(|parent| {
            (
                match parent.side {
                    ReplayClaimParentSide::Lower => 0,
                    ReplayClaimParentSide::Upper => 1,
                },
                parent.coverage_root,
                parent.representative_claim,
            )
        });
        for pair in parents.windows(2) {
            assert!(
                pair[0].side != pair[1].side
                    || pair[0].coverage_root != pair[1].coverage_root,
                "Legacy replay parent relation contains a duplicate side/root",
            );
        }
        PreparedReplayParentSet {
            lower: prepared_parent_block_from_entries(
                parents
                    .iter()
                    .copied()
                    .filter(|parent| parent.side == ReplayClaimParentSide::Lower)
                    .collect(),
            ),
            upper: prepared_parent_block_from_entries(
                parents
                    .into_iter()
                    .filter(|parent| parent.side == ReplayClaimParentSide::Upper)
                    .collect(),
            ),
        }
    };
    let canonical_pair = canonicalize(pair_parents);
    let lower_block = canonical_pair.lower.clone();
    let current_upper_endpoint = match machine
        .bounds
        .record(upper)
        .expect("Legacy replay upper record is missing")
        .endpoint()
    {
        BoundEndpoint::Upper(endpoint) => endpoint,
        BoundEndpoint::Lower(_) => panic!("Legacy replay upper record has lower direction"),
    };
    let mut seen = FxHashSet::default();
    let incremental_replays = incremental_routes
        .iter()
        .copied()
        .filter(|route| {
            let generic_covers = requires_generic && route.upper == current_upper_endpoint;
            !generic_covers
        })
        .filter(|route| seen.insert((route.upper, route.upper_record)))
        .map(|route| {
            let upper = route
                .claim
                .map_or(PreparedReplayParentBlock::Empty, |claim| {
                    canonicalize(&[SideTaggedReplayClaim {
                        claim,
                        parent_side: ReplayClaimParentSide::Upper,
                    }])
                    .upper
                });
            PreparedIncrementalReplay {
                route,
                parents: PreparedReplayParentSet {
                    lower: lower_block.clone(),
                    upper,
                },
            }
        })
        .collect();
    let prepared = PreparedReplayRoute {
        routing,
        proof_event: PreparedReplayParents {
            pair_replay: pair_replay.then_some(canonical_pair),
            incremental_replays,
        },
    };
    machine
        .proof_store
        .validate_prepared_replay_route(lower_record, upper, &prepared)
        .unwrap_or_else(|failure| panic!("Legacy replay routing plan is invalid: {failure:?}"));
    prepared
}

#[cfg(test)]
pub(super) fn finish_replay_routing_shadow(
    machine: &ConstraintMachine,
    token: Option<ReplayRoutingShadowToken>,
    direction: BoundDirection,
    legacy_input_count: usize,
    legacy_generated_count: usize,
    legacy_accepted_count: usize,
) {
    let Some(token) = token else {
        return;
    };
    let store = &machine.proof_store;
    let shadow_input_count = store.replay_route_observations.borrow()[token.routes_before..]
            .iter()
            .map(|observation| {
                usize::from(observation.shadow_prepared.proof_event.pair_replay.is_some())
                    + observation
                        .shadow_prepared
                        .proof_event
                        .incremental_replays
                        .len()
            })
            .sum();
    let admissions = store.replay_admissions[token.admissions_before..].to_vec();
    let shadow_generated_count = admissions.len();
    let mut accepted_result_set = FxHashSet::default();
    let accepted_results = admissions
        .iter()
        .filter_map(|admission| {
            let result = admission.result?;
            let accepted = admission.disposition == ReplayAdmissionDisposition::NewSemantic
                || (admission.disposition == ReplayAdmissionDisposition::Incomplete
                    && result.0 as usize >= token.canonical_constraints_before);
            (accepted && accepted_result_set.insert(result)).then_some(result)
        })
        .collect::<Vec<_>>();
    let shadow_accepted_count = accepted_results.len();
    assert_eq!(
        shadow_generated_count, legacy_generated_count,
        "CPK-7 replay generated-work count diverged",
    );
    assert!(
        accepted_results.iter().all(|result| machine
            .constraint_records
            .get(result.0 as usize)
            .is_some()),
        "CPK-7 accepted replay result is missing from semantic constraint storage",
    );
    assert_eq!(
        shadow_input_count, legacy_input_count,
        "CPK-7 replay input count diverged",
    );
    assert_eq!(
        shadow_accepted_count, legacy_accepted_count,
        "CPK-7 replay accepted count diverged",
    );
    assert_eq!(
        machine.canonical_constraints.len() - token.canonical_constraints_before,
        shadow_accepted_count,
        "CPK-7 accepted replay results diverged from canonical constraint growth",
    );
    store
        .replay_event_observations
        .borrow_mut()
        .push(ShadowReplayEventObservation {
            direction: match direction {
                BoundDirection::Lower => ShadowReplayDirection::Lower,
                BoundDirection::Upper => ShadowReplayDirection::Upper,
            },
            legacy_input_count,
            shadow_input_count,
            legacy_generated_count,
            shadow_generated_count,
            legacy_accepted_count,
            shadow_accepted_count,
            accepted_results,
            admissions,
        });
}

impl ProofOccurrenceStore {
    pub(super) fn record_replay_admission(
        &mut self,
        result: Option<ConstraintRecordId>,
        carrier: BinaryReplayDerivation,
        disposition: ReplayAdmissionDisposition,
    ) {
        self.replay_admissions.push(ReplayAdmissionEvent {
            result,
            carrier,
            disposition,
        });
    }

    pub(super) fn record_cpk_replay_parent_snapshot(
        &mut self,
        result: ConstraintRecordId,
        carrier: BinaryReplayDerivation,
        parents: &[SideTaggedReplayClaim],
    ) {
        if parents.is_empty() {
            return;
        }
        // Resolve the entire event before mutating the snapshot. Under CPK authority a missing
        // claim is a writer-order bug, never permission to fall back to the flat claim arena.
        let parents = parents
            .iter()
            .map(|parent| {
                let claim = self
                    .upper_claim(parent.claim)
                    .filter(|claim| claim.claim == parent.claim)
                    .expect("a CPK replay parent must be admitted before its snapshot");
                ReplayProofParent {
                    side: parent.parent_side,
                    coverage_root: claim.coverage_root,
                    representative_claim: parent.claim,
                    lineage: claim.lineage,
                }
            })
            .collect::<Vec<_>>();
        let key = (result, carrier);
        let index = self
            .replay_finite_map_index
            .get(&key)
            .copied()
            .unwrap_or_else(|| {
                let index = self.replay_finite_map.len();
                let first_event = self.replay_admissions.len();
                self.replay_finite_map.push(ReplayProofOccurrence {
                    result,
                    carrier,
                    lower_parents: Vec::new(),
                    upper_parents: Vec::new(),
                    first_event,
                });
                self.replay_finite_map_index.insert(key, index);
                index
            });
        let mut inserted = false;
        for parent in parents {
            let target = match parent.side {
                ReplayClaimParentSide::Lower => {
                    &mut self.replay_finite_map[index].lower_parents
                }
                ReplayClaimParentSide::Upper => {
                    &mut self.replay_finite_map[index].upper_parents
                }
            };
            if target
                .iter()
                .any(|entry| entry.coverage_root == parent.coverage_root)
            {
                continue;
            }
            target.push(parent);
            inserted = true;
            self.first_replay_witnesses
                .entry((result, parent.coverage_root))
                .or_insert(ReplayFirstWitness {
                    carrier,
                    side: parent.side,
                    representative_claim: parent.representative_claim,
                });
        }
        if !inserted {
            return;
        }
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::Constraint(result)),
            ProofCause::Replay(carrier),
            vec![
                ProofParent::Semantic(SemanticFactRef::Bound(carrier.lower)),
                ProofParent::Semantic(SemanticFactRef::Bound(carrier.upper)),
            ],
            ProvenanceCompleteness::Complete,
        );
    }

    pub(super) fn record_legacy_replay_parent_snapshot(
        &mut self,
        bounds: &TypeBounds,
        result: ConstraintRecordId,
        carrier: BinaryReplayDerivation,
        parents: &[ClaimQualifiedParent],
    ) {
        if parents.is_empty() {
            return;
        }
        let key = (result, carrier);
        let index = self
            .replay_finite_map_index
            .get(&key)
            .copied()
            .unwrap_or_else(|| {
                let index = self.replay_finite_map.len();
                let first_event = self.replay_admissions.len();
                self.replay_finite_map.push(ReplayProofOccurrence {
                    result,
                    carrier,
                    lower_parents: Vec::new(),
                    upper_parents: Vec::new(),
                    first_event,
                });
                self.replay_finite_map_index.insert(key, index);
                index
            });
        for parent in parents {
            let ClaimQualifiedParent::ReplayConstraint {
                parent_claim,
                parent_side,
                ..
            } = *parent
            else {
                continue;
            };
            let claim = &bounds.upper_replay_claims[parent_claim.0 as usize];
            let proof_parent = ReplayProofParent {
                side: parent_side,
                coverage_root: claim.coverage_root,
                representative_claim: parent_claim,
                lineage: projection_lineage(claim.lineage),
            };
            let target = match parent_side {
                ReplayClaimParentSide::Lower => {
                    &mut self.replay_finite_map[index].lower_parents
                }
                ReplayClaimParentSide::Upper => {
                    &mut self.replay_finite_map[index].upper_parents
                }
            };
            if !target.iter().any(|entry| entry.coverage_root == claim.coverage_root) {
                target.push(proof_parent);
            }
            self
                .first_replay_witnesses
                .entry((result, claim.coverage_root))
                .or_insert(ReplayFirstWitness {
                    carrier,
                    side: parent_side,
                    representative_claim: parent_claim,
                });
        }
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::Constraint(result)),
            ProofCause::Replay(carrier),
            vec![
                ProofParent::Semantic(SemanticFactRef::Bound(carrier.lower)),
                ProofParent::Semantic(SemanticFactRef::Bound(carrier.upper)),
            ],
            ProvenanceCompleteness::Complete,
        );
    }

    pub(super) fn record_replay_evidence(
        &mut self,
        result: BoundRecordId,
        carrier: BinaryReplayDerivation,
    ) {
        self.record_occurrence(
            ProofResult::EvidenceBound(result),
            ProofCause::ReplayEvidence(carrier),
            vec![
                ProofParent::Semantic(SemanticFactRef::Bound(carrier.lower)),
                ProofParent::Semantic(SemanticFactRef::Bound(carrier.upper)),
            ],
            ProvenanceCompleteness::Complete,
        );
    }

    pub(super) fn record_replay_drop(&mut self, id: ReplayDropRecordId, record: ReplayDropRecord) {
        self.record_occurrence(
            ProofResult::TrivialReplay(id),
            ProofCause::ReplayDrop(record),
            Vec::new(),
            ProvenanceCompleteness::Complete,
        );
    }

    pub(super) fn record_row_reduction(
        &mut self,
        state: UnweightedRowReductionRecordId,
        record: &UnweightedRowReductionRecord,
        root_claim: Option<UpperReplayClaimId>,
    ) {
        self.row_reductions.push(RowReductionOccurrence {
            state,
            root_claim,
            provenance: record.provenance_head,
            current_record: record.current_reduced_upper.record,
        });
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::RowReduction(state)),
            ProofCause::RowReduction {
                derivation: record.provenance_head,
                root_claim,
            },
            vec![ProofParent::Semantic(SemanticFactRef::RowDerivation(
                record.provenance_head,
            ))],
            ProvenanceCompleteness::Complete,
        );
    }

    pub(super) fn prepare_live_coverage_transition(
        &self,
        root: UpperReplayClaimId,
        state: UnweightedRowReductionRecordId,
        active: bool,
    ) -> PreparedLiveCoverageTransition {
        let states = self.live_states_by_coverage_root.get(&root);
        let contains = states.is_some_and(|states| states.contains(&state));
        if active == contains {
            return PreparedLiveCoverageTransition::Unchanged;
        }
        PreparedLiveCoverageTransition::Changed {
            root,
            state,
            active,
            was_empty: states.is_none_or(FxHashSet::is_empty),
            is_empty: !active && states.is_some_and(|states| states.len() == 1),
        }
    }

    pub(super) fn try_prepare_live_coverage_mutation(
        &mut self,
        root: UpperReplayClaimId,
        state: UnweightedRowReductionRecordId,
        active: bool,
    ) -> Result<PreparedLiveCoverageMutation, ProofFailure> {
        let transition = self.prepare_live_coverage_transition(root, state, active);
        let mut new_root_states = None;
        if matches!(transition, PreparedLiveCoverageTransition::Changed { active: true, .. }) {
            let exhausted = |_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            };
            self.live_coverage.try_reserve(1).map_err(exhausted)?;
            if let Some(states) = self.live_states_by_coverage_root.get_mut(&root) {
                states.try_reserve(1).map_err(exhausted)?;
            } else {
                self.live_states_by_coverage_root
                    .try_reserve(1)
                    .map_err(exhausted)?;
                let mut states = FxHashSet::default();
                states.try_reserve(1).map_err(exhausted)?;
                new_root_states = Some(states);
            }
        }
        Ok(PreparedLiveCoverageMutation {
            transition,
            new_root_states,
        })
    }

    pub(super) fn commit_live_coverage_mutation(
        &mut self,
        mutation: &mut PreparedLiveCoverageMutation,
    ) {
        if let (
            PreparedLiveCoverageTransition::Changed {
                root, active: true, ..
            },
            Some(states),
        ) = (mutation.transition, mutation.new_root_states.take())
        {
            assert!(self
                .live_states_by_coverage_root
                .insert(root, states)
                .is_none());
        }
        self.record_prepared_live_coverage(mutation.transition);
    }

    pub(super) fn record_prepared_live_coverage(
        &mut self,
        transition: PreparedLiveCoverageTransition,
    ) {
        let PreparedLiveCoverageTransition::Changed {
            root,
            state,
            active,
            ..
        } = transition
        else {
            return;
        };
        if active {
            let occurrence_inserted = self.live_coverage.insert((root, state));
            let index_inserted = self
                .live_states_by_coverage_root
                .entry(root)
                .or_default()
                .insert(state);
            debug_assert!(occurrence_inserted && index_inserted);
            return;
        }
        let occurrence_removed = self.live_coverage.remove(&(root, state));
        let remove_root_entry = {
            let states = self
                .live_states_by_coverage_root
                .get_mut(&root)
                .expect("live coverage index must mirror the flat occurrence set");
            let index_removed = states.remove(&state);
            debug_assert!(occurrence_removed && index_removed);
            states.is_empty()
        };
        if remove_root_entry {
            self.live_states_by_coverage_root.remove(&root);
        }
    }

    pub(super) fn record_live_coverage(
        &mut self,
        root: UpperReplayClaimId,
        state: UnweightedRowReductionRecordId,
        active: bool,
    ) -> PreparedLiveCoverageTransition {
        let transition = self.prepare_live_coverage_transition(root, state, active);
        self.record_prepared_live_coverage(transition);
        transition
    }

    pub(super) fn try_prepare_qualified_parent_admission(
        &mut self,
        result: ConstraintRecordId,
        parents: &[ClaimQualifiedParent],
    ) -> Result<PreparedQualifiedParentAdmission, ProofFailure> {
        let exhausted = |_| ProofFailure::ResourceExhausted {
            operation: ProofOperation::UpdateClaimLifecycle,
        };
        let mut pending_keys = FxHashSet::default();
        pending_keys.try_reserve(parents.len()).map_err(exhausted)?;
        let mut accepted = Vec::new();
        accepted.try_reserve(parents.len()).map_err(exhausted)?;
        for &parent in parents {
            let parent_claim = parent.parent_claim();
            let claim = self
                .upper_claim(parent_claim)
                .filter(|claim| claim.claim == parent_claim)
                .expect("a qualified parent claim must be admitted before its route");
            let identity = match parent {
                ClaimQualifiedParent::ReplayConstraint {
                    parent_side,
                    replay,
                    ..
                } => QualifiedParentIdentity::Replay {
                    parent_side,
                    replay,
                },
                ClaimQualifiedParent::StructuralConstraint { derivation, .. } => {
                    QualifiedParentIdentity::Structural(derivation)
                }
                ClaimQualifiedParent::ReductionRouteConstraint { derivation, .. } => {
                    QualifiedParentIdentity::ReductionRoute {
                        derivation,
                        parent_claim,
                    }
                }
            };
            let key = QualifiedParentKey {
                result,
                coverage_root: claim.coverage_root,
                identity,
            };
            if self.qualified_parent_keys.contains(&key) || !pending_keys.insert(key) {
                continue;
            }
            accepted.push(ExactQualifiedParent {
                coverage_root: claim.coverage_root,
                parent,
            });
        }

        #[cfg(test)]
        if !accepted.is_empty()
            && std::mem::take(&mut self.fail_next_qualified_parent_reservation)
        {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }
        self.qualified_parent_keys
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        let new_result_entries =
            if let Some(entries) = self.qualified_parents_by_result.get_mut(&result) {
                entries.try_reserve(accepted.len()).map_err(exhausted)?;
                None
            } else if accepted.is_empty() {
                None
            } else {
                self.qualified_parents_by_result
                    .try_reserve(1)
                    .map_err(exhausted)?;
                let mut entries = Vec::new();
                entries.try_reserve(accepted.len()).map_err(exhausted)?;
                Some(entries)
            };
        let mut canonical = Vec::new();
        canonical
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        canonical.extend_from_slice(&accepted);
        canonical.sort_unstable_by(qualified_parent_entry_cmp);
        Ok(PreparedQualifiedParentAdmission {
            result,
            accepted,
            canonical,
            new_result_entries,
        })
    }

    pub(super) fn commit_qualified_parent_admission(
        &mut self,
        admission: &mut PreparedQualifiedParentAdmission,
    ) {
        if admission.accepted.is_empty() {
            return;
        }
        if let Some(entries) = admission.new_result_entries.take() {
            assert!(self
                .qualified_parents_by_result
                .insert(admission.result, entries)
                .is_none());
        }
        for &entry in &admission.accepted {
            let identity = match entry.parent {
                ClaimQualifiedParent::ReplayConstraint {
                    parent_side,
                    replay,
                    ..
                } => QualifiedParentIdentity::Replay {
                    parent_side,
                    replay,
                },
                ClaimQualifiedParent::StructuralConstraint { derivation, .. } => {
                    QualifiedParentIdentity::Structural(derivation)
                }
                ClaimQualifiedParent::ReductionRouteConstraint {
                    derivation,
                    parent_claim,
                } => QualifiedParentIdentity::ReductionRoute {
                    derivation,
                    parent_claim,
                },
            };
            assert!(self.qualified_parent_keys.insert(QualifiedParentKey {
                result: admission.result,
                coverage_root: entry.coverage_root,
                identity,
            }));
        }
        let entries = self
            .qualified_parents_by_result
            .get_mut(&admission.result)
            .expect("qualified-parent result capacity was prepared before commit");
        entries.extend(admission.canonical.iter().copied());
        entries.sort_unstable_by(qualified_parent_entry_cmp);
    }

    pub(super) fn qualified_parents_for_result(
        &self,
        result: ConstraintRecordId,
    ) -> &[ExactQualifiedParent] {
        self.qualified_parents_by_result
            .get(&result)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    #[cfg(test)]
    pub(super) fn fail_next_qualified_parent_reservation(&mut self) {
        self.fail_next_qualified_parent_reservation = true;
    }

    pub(super) fn try_prepare_projection_index_admission(
        &mut self,
        target: Option<(ProjectionTarget, BoundRecordId)>,
        edges: &[(ProofPremise, BoundRecordId)],
    ) -> Result<PreparedProjectionIndexAdmission, ProofFailure> {
        let exhausted = |_| ProofFailure::ResourceExhausted {
            operation: ProofOperation::UpdateClaimLifecycle,
        };
        let target = target.and_then(|(target, record)| {
            let existing = match target {
                ProjectionTarget::Constraint(constraint) => self
                    .projection_lower_record_by_constraint
                    .get(&constraint)
                    .copied(),
                ProjectionTarget::Replay(replay) => {
                    self.projection_lower_record_by_replay.get(&replay).copied()
                }
            };
            if let Some(existing) = existing {
                assert_eq!(existing, record, "one projection target mapped to two lower records");
                None
            } else {
                Some((target, record))
            }
        });

        let mut pending = FxHashSet::default();
        pending
            .try_reserve(edges.len().saturating_add(8))
            .map_err(exhausted)?;
        pending.extend(edges.iter().copied());
        if let Some((ProjectionTarget::Constraint(constraint), lower_record)) = target {
            if let Some(dependents) = self
                .dependent_records_by_premise
                .get(&ProofPremise::Constraint(constraint))
            {
                pending.extend(
                    dependents
                        .iter()
                        .copied()
                        .map(|dependent| (ProofPremise::Record(lower_record), dependent)),
                );
            }
        }
        let constraint_targets = pending
            .iter()
            .filter_map(|(premise, dependent)| match premise {
                ProofPremise::Constraint(constraint) => self
                    .projection_lower_record_by_constraint
                    .get(constraint)
                    .copied()
                    .or_else(|| match target {
                        Some((ProjectionTarget::Constraint(incoming), record))
                            if incoming == *constraint =>
                        {
                            Some(record)
                        }
                        _ => None,
                    })
                    .map(|record| (ProofPremise::Record(record), *dependent)),
                ProofPremise::Record(_) | ProofPremise::RootCoverage(_) => None,
            })
            .collect::<Vec<_>>();
        pending.extend(constraint_targets);

        let mut accepted_edges = Vec::new();
        accepted_edges.try_reserve(pending.len()).map_err(exhausted)?;
        for edge @ (premise, dependent) in pending {
            if self
                .dependent_records_by_premise
                .get(&premise)
                .is_some_and(|dependents| dependents.contains(&dependent))
            {
                continue;
            }
            accepted_edges.push(edge);
        }

        #[cfg(test)]
        if (target.is_some() || !accepted_edges.is_empty())
            && std::mem::take(&mut self.fail_next_projection_index_reservation)
        {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }
        match target {
            Some((ProjectionTarget::Constraint(_), _)) => self
                .projection_lower_record_by_constraint
                .try_reserve(1)
                .map_err(exhausted)?,
            Some((ProjectionTarget::Replay(_), _)) => self
                .projection_lower_record_by_replay
                .try_reserve(1)
                .map_err(exhausted)?,
            None => {}
        }

        let mut counts = FxHashMap::default();
        counts.try_reserve(accepted_edges.len()).map_err(exhausted)?;
        for (premise, _) in &accepted_edges {
            *counts.entry(*premise).or_insert(0usize) += 1;
        }
        self.dependent_records_by_premise
            .try_reserve(counts.len())
            .map_err(exhausted)?;
        let mut new_dependent_sets = Vec::new();
        new_dependent_sets.try_reserve(counts.len()).map_err(exhausted)?;
        for (premise, count) in counts {
            if let Some(dependents) = self.dependent_records_by_premise.get_mut(&premise) {
                dependents.try_reserve(count).map_err(exhausted)?;
            } else {
                let mut dependents = FxHashSet::default();
                dependents.try_reserve(count).map_err(exhausted)?;
                new_dependent_sets.push((premise, dependents));
            }
        }
        Ok(PreparedProjectionIndexAdmission {
            target,
            accepted_edges,
            new_dependent_sets,
        })
    }

    pub(super) fn commit_projection_index_admission(
        &mut self,
        admission: &mut PreparedProjectionIndexAdmission,
    ) {
        if let Some((target, record)) = admission.target {
            let previous = match target {
                ProjectionTarget::Constraint(constraint) => self
                    .projection_lower_record_by_constraint
                    .insert(constraint, record),
                ProjectionTarget::Replay(replay) => {
                    self.projection_lower_record_by_replay.insert(replay, record)
                }
            };
            assert!(previous.is_none());
        }
        for (premise, dependents) in admission.new_dependent_sets.drain(..) {
            assert!(self
                .dependent_records_by_premise
                .insert(premise, dependents)
                .is_none());
        }
        for (premise, dependent) in admission.accepted_edges.iter().copied() {
            assert!(self
                .dependent_records_by_premise
                .get_mut(&premise)
                .expect("dependency index capacity was prepared before commit")
                .insert(dependent));
        }
    }

    pub(super) fn projection_lower_record_for_constraint(
        &self,
        constraint: ConstraintRecordId,
    ) -> Option<BoundRecordId> {
        self.projection_lower_record_by_constraint
            .get(&constraint)
            .copied()
    }

    pub(super) fn projection_lower_record_for_replay(
        &self,
        replay: BinaryReplayDerivation,
    ) -> Option<BoundRecordId> {
        self.projection_lower_record_by_replay.get(&replay).copied()
    }

    pub(super) fn dependent_records(
        &self,
        premise: ProofPremise,
    ) -> Option<&FxHashSet<BoundRecordId>> {
        self.dependent_records_by_premise.get(&premise)
    }

    #[cfg(test)]
    pub(super) fn fail_next_projection_index_reservation(&mut self) {
        self.fail_next_projection_index_reservation = true;
    }

    pub(super) fn record_reduction_route(
        &mut self,
        result: ConstraintRecordId,
        derivation: RowDerivationId,
        parent_claim: UpperReplayClaimId,
    ) {
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::Constraint(result)),
            ProofCause::ReductionRoute {
                derivation,
                parent_claim,
            },
            vec![ProofParent::Semantic(SemanticFactRef::RowDerivation(
                derivation,
            ))],
            ProvenanceCompleteness::Complete,
        );
    }
}

fn qualified_parent_entry_cmp(
    left: &ExactQualifiedParent,
    right: &ExactQualifiedParent,
) -> std::cmp::Ordering {
    left.coverage_root
        .cmp(&right.coverage_root)
        .then_with(|| {
            canonical_projection_key::carrier_cmp(
                &qualified_parent_projection_carrier(left.parent),
                &qualified_parent_projection_carrier(right.parent),
            )
        })
        .then_with(|| {
            qualified_parent_side_rank(left.parent).cmp(&qualified_parent_side_rank(right.parent))
        })
        .then_with(|| left.parent.parent_claim().cmp(&right.parent.parent_claim()))
}

fn qualified_parent_projection_carrier(parent: ClaimQualifiedParent) -> ProjectionProofCarrier {
    match parent {
        ClaimQualifiedParent::ReplayConstraint { replay, .. } => {
            ProjectionProofCarrier::ReplayConstraint {
                result: ConstraintRecordId(0),
                derivation: replay,
            }
        }
        ClaimQualifiedParent::StructuralConstraint { derivation, .. } => {
            ProjectionProofCarrier::StructuralConstraint {
                result: ConstraintRecordId(0),
                derivation,
            }
        }
        ClaimQualifiedParent::ReductionRouteConstraint { derivation, .. } => {
            ProjectionProofCarrier::RowConstraint {
                result: ConstraintRecordId(0),
                derivation,
            }
        }
    }
}

fn qualified_parent_side_rank(parent: ClaimQualifiedParent) -> u8 {
    match parent {
        ClaimQualifiedParent::ReplayConstraint {
            parent_side: ReplayClaimParentSide::Lower,
            ..
        } => 0,
        ClaimQualifiedParent::ReplayConstraint {
            parent_side: ReplayClaimParentSide::Upper,
            ..
        } => 1,
        ClaimQualifiedParent::StructuralConstraint { .. } => 0,
        ClaimQualifiedParent::ReductionRouteConstraint { .. } => 0,
    }
}

fn row_parent(parent: RowDerivationParent) -> ProofParent {
    match parent {
        RowDerivationParent::Constraint(id) => {
            ProofParent::Semantic(SemanticFactRef::Constraint(id))
        }
        RowDerivationParent::Bound(id) => ProofParent::Semantic(SemanticFactRef::Bound(id)),
        RowDerivationParent::SubtractFact(id) => {
            ProofParent::Semantic(SemanticFactRef::Subtract(id))
        }
        RowDerivationParent::RowDerivation(id) => {
            ProofParent::Semantic(SemanticFactRef::RowDerivation(id))
        }
        RowDerivationParent::LowerFilter(id) => ProofParent::LowerFilter(id),
        RowDerivationParent::Origin(id) => ProofParent::Origin(id),
    }
}

fn bound_derivation_parents(derivation: &BoundDerivation) -> Vec<ProofParent> {
    match derivation {
        BoundDerivation::Constraint(id) => {
            vec![ProofParent::Semantic(SemanticFactRef::Constraint(*id))]
        }
        BoundDerivation::Origin(id) => vec![ProofParent::Origin(*id)],
        BoundDerivation::ReplayEvidence(_) | BoundDerivation::IncompleteReplay => Vec::new(),
        BoundDerivation::Row(id) => {
            vec![ProofParent::Semantic(SemanticFactRef::RowDerivation(*id))]
        }
        BoundDerivation::SchemeInstantiation(derivation) => vec![
            ProofParent::Semantic(SemanticFactRef::SchemeInstantiation(
                derivation.instantiation,
            )),
            ProofParent::GeneralizedWitness(derivation.source_witness),
        ],
    }
}

impl ProofOccurrenceStore {
    pub(crate) fn record_constraint_root(
        &mut self,
        result: ConstraintRecordId,
        origin: OriginId,
    ) {
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::Constraint(result)),
            ProofCause::Root(origin),
            vec![ProofParent::Origin(origin)],
            ProvenanceCompleteness::Complete,
        );
    }

    pub(crate) fn record_structural(
        &mut self,
        result: ConstraintRecordId,
        derivation: StructuralDerivation,
    ) {
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::Constraint(result)),
            ProofCause::Structural(derivation),
            vec![ProofParent::Semantic(SemanticFactRef::Constraint(
                derivation.parent,
            ))],
            ProvenanceCompleteness::Complete,
        );
    }

    pub(crate) fn record_row_definition(
        &mut self,
        id: RowDerivationId,
        derivation: RowDerivation,
    ) {
        let parents = derivation.parents.iter().copied().map(row_parent).collect();
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::RowDerivation(id)),
            ProofCause::RowDefinition(derivation),
            parents,
            ProvenanceCompleteness::Complete,
        );
    }

    pub(crate) fn record_row_constraint(
        &mut self,
        result: ConstraintRecordId,
        derivation: RowDerivationId,
    ) {
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::Constraint(result)),
            ProofCause::RowConstraint(derivation),
            vec![ProofParent::Semantic(SemanticFactRef::RowDerivation(
                derivation,
            ))],
            ProvenanceCompleteness::Complete,
        );
    }

    pub(crate) fn record_bound(&mut self, result: BoundRecordId, derivation: BoundDerivation) {
        if matches!(
            derivation,
            BoundDerivation::ReplayEvidence(_) | BoundDerivation::IncompleteReplay
        ) {
            return;
        }
        let parents = bound_derivation_parents(&derivation);
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::Bound(result)),
            ProofCause::Bound(derivation),
            parents,
            ProvenanceCompleteness::Complete,
        );
    }

    pub(crate) fn record_bound_disposition(
        &mut self,
        id: BoundDispositionRecordId,
        result: Option<BoundRecordId>,
        disposition: BoundDispositionRecord,
    ) {
        self.record_occurrence(
            result.map_or(ProofResult::BoundDisposition(id), |result| {
                ProofResult::Semantic(SemanticFactRef::Bound(result))
            }),
            ProofCause::BoundDisposition(disposition),
            Vec::new(),
            ProvenanceCompleteness::Complete,
        );
    }

    pub(crate) fn record_subtract(
        &mut self,
        result: SubtractFactRecordId,
        derivation: SubtractFactDerivation,
    ) {
        let origin = match derivation {
            SubtractFactDerivation::Declaration(origin)
            | SubtractFactDerivation::Import(origin)
            | SubtractFactDerivation::Internal(origin) => origin,
        };
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::Subtract(result)),
            ProofCause::Subtract(derivation),
            vec![ProofParent::Origin(origin)],
            ProvenanceCompleteness::Complete,
        );
    }

    pub(crate) fn record_scheme_instantiation_record(
        &mut self,
        result: SchemeInstantiationId,
        record: SchemeInstantiationRecord,
    ) {
        let completeness = record.completeness;
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::SchemeInstantiation(result)),
            ProofCause::SchemeInstantiationRecord(record),
            Vec::new(),
            completeness,
        );
    }

    pub(crate) fn record_scheme_instantiation_derivation(
        &mut self,
        result: ConstraintRecordId,
        derivation: SchemeInstantiationDerivation,
    ) {
        let parents = vec![
            ProofParent::Semantic(SemanticFactRef::SchemeInstantiation(
                derivation.instantiation,
            )),
            ProofParent::GeneralizedWitness(derivation.source_witness),
        ];
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::Constraint(result)),
            ProofCause::SchemeInstantiationDerivation(derivation),
            parents,
            ProvenanceCompleteness::Complete,
        );
    }

    pub(crate) fn record_scheme_instantiation_route(
        &mut self,
        result: ConstraintRecordId,
        route: SchemeInstantiationRoute,
    ) {
        let parents = vec![
            ProofParent::Semantic(SemanticFactRef::SchemeInstantiation(
                route.derivation.instantiation,
            )),
            ProofParent::GeneralizedWitness(route.derivation.source_witness),
        ];
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::Constraint(result)),
            ProofCause::SchemeInstantiationRoute(route),
            parents,
            ProvenanceCompleteness::Complete,
        );
    }

    pub(crate) fn record_constraint_disposition(
        &mut self,
        result: ConstraintRecordId,
        disposition: ConstraintCanonicalizationDisposition,
    ) {
        self.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::Constraint(result)),
            ProofCause::ConstraintDisposition(disposition),
            Vec::new(),
            ProvenanceCompleteness::Complete,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraints::{
        ReplaySoakEventOrigin, capture_replay_soak_test_events,
        with_intentional_replay_soak_test_injection,
    };

    fn cpk_machine() -> ConstraintMachine {
        cpk_machine_with_authority(ProofReadAuthority::Cpk)
    }

    fn cpk_machine_with_authority(
        proof_read_authority: ProofReadAuthority,
    ) -> ConstraintMachine {
        ConstraintMachine::new_with_read_authorities(
            ReplayReadAuthority::Factored,
            proof_read_authority,
        )
    }

    fn cpk_migration_oracle_machine_with_authority(
        proof_read_authority: ProofReadAuthority,
    ) -> ConstraintMachine {
        let mut machine = cpk_machine_with_authority(proof_read_authority);
        machine.cpk_proof_oracle_active = true;
        machine
    }

    fn project_lower_for_test(
        machine: &ConstraintMachine,
        record: BoundRecordId,
    ) -> (
        Result<ProjectionDecision, ProofFailure>,
        ProjectionEvaluationRound<'_>,
    ) {
        let mut round = ProjectionEvaluationRound::new();
        let decision = machine
            .proof_store
            .project_lower(machine, record, &mut round);
        (decision, round)
    }

    fn cpk_7_record_original_claim(
        machine: &mut ConstraintMachine,
        ordinal: u32,
    ) -> (BoundRecordId, UpperReplayClaimId) {
        cpk_record_original_claim_with_kind(machine, ordinal, UpperReplayClaimKind::Direct)
    }

    fn cpk_record_original_claim_with_kind(
        machine: &mut ConstraintMachine,
        ordinal: u32,
        kind: UpperReplayClaimKind,
    ) -> (BoundRecordId, UpperReplayClaimId) {
        let endpoint = machine.alloc_neg(Neg::Var(TypeVar(70_000 + ordinal)));
        let record = machine
            .bounds
            .add_upper(
                TypeVar(80_000 + ordinal),
                endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let registration = machine.original_upper_replay_claim(
            record,
            ConstraintRecordId(90_000 + ordinal),
            kind,
        );
        (record, registration.claim)
    }

    struct Cpk7RoutingFixture {
        machine: ConstraintMachine,
        lower: BoundRecordId,
        upper: BoundRecordId,
        upper_endpoint: NegId,
    }

    fn cpk_7_routing_fixture(lower_is_var: bool) -> Cpk7RoutingFixture {
        let mut machine = cpk_machine();
        let owner = TypeVar(71_000);
        let lower_endpoint = if lower_is_var {
            machine.alloc_pos(Pos::Var(TypeVar(71_001)))
        } else {
            machine.alloc_pos(Pos::Con(vec!["cpk-7-lower".into()], Vec::new()))
        };
        let upper_endpoint = machine.alloc_neg(Neg::Con(vec!["cpk-7-upper".into()], Vec::new()));
        let lower = machine
            .bounds
            .add_lower(
                owner,
                lower_endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let upper = machine
            .bounds
            .add_upper(
                owner,
                upper_endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        Cpk7RoutingFixture {
            machine,
            lower,
            upper,
            upper_endpoint,
        }
    }

    fn cpk_7_add_upper_claim(fixture: &mut Cpk7RoutingFixture, ordinal: u32) -> UpperReplayClaimId {
        let registration = fixture.machine.original_upper_replay_claim(
            fixture.upper,
            ConstraintRecordId(91_000 + ordinal),
            UpperReplayClaimKind::Direct,
        );
        fixture.machine.proof_store.record_upper_claim(
            &fixture.machine.bounds.upper_replay_claims[registration.claim.0 as usize],
        );
        registration.claim
    }

    fn cpk_7_incremental_route(
        fixture: &Cpk7RoutingFixture,
        claim: Option<UpperReplayClaimId>,
    ) -> IncrementalRouteKey {
        IncrementalRouteKey {
            upper: fixture.upper_endpoint,
            upper_record: fixture.upper,
            provenance: RowDerivationId(71_000),
            claim,
        }
    }

    #[test]
    fn cpk_7_slice_b_rejects_missing_invalid_and_cross_owner_targets() {
        let mut fixture = cpk_7_routing_fixture(false);
        let missing = BoundRecordId(u32::MAX);
        assert_eq!(
            fixture.machine.proof_store.prepare_replay_route(
                &fixture.machine,
                missing,
                fixture.upper,
                &[],
            ),
            Err(ProofFailure::MissingSemanticFact {
                fact: SemanticFactRef::Bound(missing),
            }),
        );
        assert_eq!(
            fixture.machine.proof_store.prepare_replay_route(
                &fixture.machine,
                fixture.lower,
                missing,
                &[],
            ),
            Err(ProofFailure::MissingSemanticFact {
                fact: SemanticFactRef::Bound(missing),
            }),
        );
        assert_eq!(
            fixture.machine.proof_store.prepare_replay_route(
                &fixture.machine,
                fixture.upper,
                fixture.upper,
                &[],
            ),
            Err(ProofFailure::InvalidReplayRouteTarget {
                lower: fixture.upper,
                upper: fixture.upper,
                kind: ReplayRouteTargetViolation::LowerDirectionOrState,
            }),
        );
        assert_eq!(
            fixture.machine.proof_store.prepare_replay_route(
                &fixture.machine,
                fixture.lower,
                fixture.lower,
                &[],
            ),
            Err(ProofFailure::InvalidReplayRouteTarget {
                lower: fixture.lower,
                upper: fixture.lower,
                kind: ReplayRouteTargetViolation::UpperDirectionOrState,
            }),
        );
        fixture.machine.bounds.records[fixture.lower.0 as usize].state =
            BoundRecordState::Tombstone;
        assert_eq!(
            fixture.machine.proof_store.prepare_replay_route(
                &fixture.machine,
                fixture.lower,
                fixture.upper,
                &[],
            ),
            Err(ProofFailure::InvalidReplayRouteTarget {
                lower: fixture.lower,
                upper: fixture.upper,
                kind: ReplayRouteTargetViolation::LowerDirectionOrState,
            }),
        );

        let mut fixture = cpk_7_routing_fixture(false);
        let other_upper = fixture
            .machine
            .bounds
            .add_upper(
                TypeVar(71_999),
                fixture.upper_endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        assert_eq!(
            fixture.machine.proof_store.prepare_replay_route(
                &fixture.machine,
                fixture.lower,
                other_upper,
                &[],
            ),
            Err(ProofFailure::InvalidReplayRouteTarget {
                lower: fixture.lower,
                upper: other_upper,
                kind: ReplayRouteTargetViolation::OwnerMismatch,
            }),
        );
    }

    #[test]
    fn cpk_7_slice_b_distinguishes_dangling_claim_root_and_valid_uncovered_absence() {
        let mut fixture = cpk_7_routing_fixture(false);
        let missing_claim = UpperReplayClaimId(71_000);
        fixture
            .machine
            .proof_store
            .claims_by_upper_record
            .insert(fixture.upper, vec![missing_claim]);
        assert_eq!(
            fixture.machine.proof_store.prepare_replay_route(
                &fixture.machine,
                fixture.lower,
                fixture.upper,
                &[],
            ),
            Err(ProofFailure::DanglingProofReference {
                owner: ProofFactRef::ReplayClaims(fixture.upper),
                target: ProofFactRef::UpperClaim(missing_claim),
            }),
        );

        let mut fixture = cpk_7_routing_fixture(false);
        let claim = cpk_7_add_upper_claim(&mut fixture, 0);
        let missing_root = UpperReplayClaimId(71_001);
        let index = fixture.machine.proof_store.upper_claim_index[&claim];
        fixture.machine.proof_store.upper_claims[index].coverage_root = missing_root;
        assert!(matches!(
            fixture.machine.proof_store.prepare_replay_route(
                &fixture.machine,
                fixture.lower,
                fixture.upper,
                &[],
            ),
            Err(ProofFailure::DanglingProofReference {
                target: ProofFactRef::CoverageRoot(root),
                ..
            }) if root == missing_root
        ));

        let mut fixture = cpk_7_routing_fixture(false);
        let claim = cpk_7_add_upper_claim(&mut fixture, 1);
        let prepared = fixture
            .machine
            .proof_store
            .prepare_replay_route(&fixture.machine, fixture.lower, fixture.upper, &[])
            .expect("missing live coverage is a valid uncovered root");
        assert_eq!(prepared.routing, ReplayRouting::Generic);
        let parents = prepared.proof_event.pair_replay.expect("generic pair");
        assert_eq!(parents.upper.as_slice()[0].representative_claim, claim,);

        fixture
            .machine
            .proof_store
            .live_states_by_coverage_root
            .insert(claim, FxHashSet::default());
        assert_eq!(
            fixture
                .machine
                .proof_store
                .prepare_replay_route(&fixture.machine, fixture.lower, fixture.upper, &[])
                .expect("an empty live-state set remains uncovered")
                .routing,
            ReplayRouting::Generic,
        );

        let index = fixture.machine.proof_store.upper_claim_index[&claim];
        fixture
            .machine
            .proof_store
            .upper_claim_index
            .insert(claim, index + 10_000);
        assert!(matches!(
            fixture.machine.proof_store.prepare_replay_route(
                &fixture.machine,
                fixture.lower,
                fixture.upper,
                &[],
            ),
            Err(ProofFailure::ReplayRoutingInvariantViolation {
                kind: ReplayRoutingInvariantViolation::ClaimIndexMismatch,
                ..
            })
        ));
    }

    #[test]
    fn cpk_7_slice_b_routes_covered_pairs_and_deduplicates_incremental_input() {
        let mut fixture = cpk_7_routing_fixture(false);
        let claim = cpk_7_add_upper_claim(&mut fixture, 0);
        fixture.machine.proof_store.record_live_coverage(
            claim,
            UnweightedRowReductionRecordId(71_000),
            true,
        );
        let skipped = fixture
            .machine
            .proof_store
            .prepare_replay_route(&fixture.machine, fixture.lower, fixture.upper, &[])
            .expect("covered non-variable pair is complete");
        assert_eq!(skipped.routing, ReplayRouting::SkipAlreadyCovered);

        let route = cpk_7_incremental_route(&fixture, None);
        let incremental = fixture
            .machine
            .proof_store
            .prepare_replay_route(
                &fixture.machine,
                fixture.lower,
                fixture.upper,
                &[route, route],
            )
            .expect("duplicate incremental input keeps its first semantic action");
        assert_eq!(incremental.routing, ReplayRouting::IncrementalOnly);
        assert_eq!(incremental.proof_event.incremental_replays.len(), 1);
        assert_eq!(incremental.proof_event.incremental_replays[0].route, route);

        let mut variable_fixture = cpk_7_routing_fixture(true);
        let variable_claim = cpk_7_add_upper_claim(&mut variable_fixture, 1);
        variable_fixture.machine.proof_store.record_live_coverage(
            variable_claim,
            UnweightedRowReductionRecordId(71_001),
            true,
        );
        let attachment = variable_fixture
            .machine
            .proof_store
            .prepare_replay_route(
                &variable_fixture.machine,
                variable_fixture.lower,
                variable_fixture.upper,
                &[],
            )
            .expect("an unhandled covered parent retains variable-lower attachment work");
        assert_eq!(attachment.routing, ReplayRouting::IncrementalOnly);
        assert_eq!(
            attachment
                .proof_event
                .pair_replay
                .expect("covered attachment pair")
                .upper
                .as_slice()[0]
                .representative_claim,
            variable_claim,
        );
    }

    #[test]
    fn cpk_7_slice_b_keeps_covered_decoupled_route_as_incremental_only() {
        let mut fixture = cpk_7_routing_fixture(false);
        let claim = cpk_7_add_upper_claim(&mut fixture, 0);
        fixture.machine.proof_store.record_live_coverage(
            claim,
            UnweightedRowReductionRecordId(71_000),
            true,
        );
        let residual_endpoint = fixture.machine.alloc_neg(Neg::Con(
            vec!["cpk-7-original-upper".into()],
            Vec::new(),
        ));
        let mut route = cpk_7_incremental_route(&fixture, Some(claim));
        route.upper = residual_endpoint;

        let prepared = fixture
            .machine
            .proof_store
            .prepare_replay_route(
                &fixture.machine,
                fixture.lower,
                fixture.upper,
                &[route],
            )
            .expect("a covered decoupled route remains incremental work");

        assert_eq!(prepared.routing, ReplayRouting::IncrementalOnly);
        assert!(prepared.proof_event.pair_replay.is_none());
        assert_eq!(prepared.proof_event.incremental_replays.len(), 1);
        assert_eq!(prepared.proof_event.incremental_replays[0].route, route);
        assert_eq!(
            prepared.proof_event.incremental_replays[0]
                .parents
                .upper
                .as_slice()[0]
                .representative_claim,
            claim,
        );
    }

    #[test]
    fn cpk_7_slice_b_keeps_uncovered_decoupled_route_beside_generic_pair() {
        let mut fixture = cpk_7_routing_fixture(false);
        let claim = cpk_7_add_upper_claim(&mut fixture, 0);
        let residual_endpoint = fixture.machine.alloc_neg(Neg::Con(
            vec!["cpk-7-original-upper".into()],
            Vec::new(),
        ));
        let mut route = cpk_7_incremental_route(&fixture, Some(claim));
        route.upper = residual_endpoint;

        let prepared = fixture
            .machine
            .proof_store
            .prepare_replay_route(
                &fixture.machine,
                fixture.lower,
                fixture.upper,
                &[route],
            )
            .expect("a generic pair retains decoupled residual incremental work");

        assert_eq!(prepared.routing, ReplayRouting::Generic);
        assert_eq!(
            prepared
                .proof_event
                .pair_replay
                .as_ref()
                .expect("uncovered claim requires generic pair replay")
                .upper
                .as_slice()[0]
                .representative_claim,
            claim,
        );
        assert_eq!(prepared.proof_event.incremental_replays.len(), 1);
        assert_eq!(prepared.proof_event.incremental_replays[0].route, route);
        assert_eq!(
            prepared.proof_event.incremental_replays[0]
                .parents
                .upper
                .as_slice()[0]
                .representative_claim,
            claim,
        );
    }

    #[test]
    fn cpk_7_slice_b_rejects_invalid_incremental_claims_and_upper_grouping() {
        let mut fixture = cpk_7_routing_fixture(false);
        let claim = cpk_7_add_upper_claim(&mut fixture, 0);
        fixture.machine.proof_store.record_live_coverage(
            claim,
            UnweightedRowReductionRecordId(71_000),
            true,
        );
        let missing = UpperReplayClaimId(71_999);
        let dangling = cpk_7_incremental_route(&fixture, Some(missing));
        assert!(matches!(
            fixture.machine.proof_store.prepare_replay_route(
                &fixture.machine,
                fixture.lower,
                fixture.upper,
                &[dangling],
            ),
            Err(ProofFailure::DanglingProofReference {
                target: ProofFactRef::UpperClaim(found),
                ..
            }) if found == missing
        ));

        let (_, foreign_claim) = cpk_7_record_original_claim(&mut fixture.machine, 500);
        let mismatch = cpk_7_incremental_route(&fixture, Some(foreign_claim));
        assert!(matches!(
            fixture.machine.proof_store.prepare_replay_route(
                &fixture.machine,
                fixture.lower,
                fixture.upper,
                &[mismatch],
            ),
            Err(ProofFailure::ReplayRoutingInvariantViolation {
                kind: ReplayRoutingInvariantViolation::IncrementalClaimMismatch,
                ..
            })
        ));

        let mut wrong_upper = cpk_7_incremental_route(&fixture, None);
        wrong_upper.upper_record = fixture.lower;
        assert!(matches!(
            fixture.machine.proof_store.prepare_replay_route(
                &fixture.machine,
                fixture.lower,
                fixture.upper,
                &[wrong_upper],
            ),
            Err(ProofFailure::ReplayRoutingInvariantViolation {
                kind: ReplayRoutingInvariantViolation::IncrementalUpperMismatch,
                ..
            })
        ));
    }

    #[test]
    fn cpk_7_slice_b_prepared_output_validator_rejects_every_canonicality_fault() {
        let mut fixture = cpk_7_routing_fixture(false);
        let first_claim = cpk_7_add_upper_claim(&mut fixture, 0);
        let second_claim = cpk_7_add_upper_claim(&mut fixture, 1);
        let make_parent = |claim| {
            let occurrence = fixture
                .machine
            .proof_store
                .upper_claim(claim)
                .expect("fixture claim");
            PreparedReplayParent {
                side: ReplayClaimParentSide::Upper,
                coverage_root: occurrence.coverage_root,
                representative_claim: claim,
                lineage: occurrence.lineage,
    }
        };
        let first = make_parent(first_claim);
        let second = make_parent(second_claim);
        let generic = |parents| PreparedReplayRoute {
            routing: ReplayRouting::Generic,
            proof_event: PreparedReplayParents {
                pair_replay: Some(PreparedReplayParentSet {
                    lower: PreparedReplayParentBlock::Empty,
                    upper: PreparedReplayParentBlock::Shared(Arc::from(parents)),
                }),
                incremental_replays: Vec::new(),
            },
        };

        let duplicate = generic(vec![first, first]);
        assert!(matches!(
            fixture.machine.proof_store.validate_prepared_replay_route(
                fixture.lower,
                fixture.upper,
                &duplicate,
            ),
            Err(ProofFailure::ReplayRoutingInvariantViolation {
                kind: ReplayRoutingInvariantViolation::DuplicateParentRoot(
                    ReplayClaimParentSide::Upper
                ),
                ..
            })
        ));
        let noncanonical = generic(vec![second, first]);
        assert!(matches!(
            fixture.machine.proof_store.validate_prepared_replay_route(
                fixture.lower,
                fixture.upper,
                &noncanonical,
            ),
            Err(ProofFailure::NonCanonicalReplayParentOrder {
                side: ReplayClaimParentSide::Upper,
                ..
            })
        ));
        let mut wrong_root = first;
        wrong_root.coverage_root = second.coverage_root;
        let representative_mismatch = generic(vec![wrong_root]);
        assert!(matches!(
            fixture.machine.proof_store.validate_prepared_replay_route(
                fixture.lower,
                fixture.upper,
                &representative_mismatch,
            ),
            Err(ProofFailure::ReplayRoutingInvariantViolation {
                kind: ReplayRoutingInvariantViolation::RepresentativeRootMismatch,
                ..
            })
        ));

        let mut wrong_side = first;
        wrong_side.side = ReplayClaimParentSide::Lower;
        let incomplete_side = generic(vec![wrong_side]);
        assert!(matches!(
            fixture.machine.proof_store.validate_prepared_replay_route(
                fixture.lower,
                fixture.upper,
                &incomplete_side,
            ),
            Err(ProofFailure::IncompleteMandatoryData {
                field: MandatoryProofField::ReplayParentSide,
                ..
            })
        ));

        let mut wrong_lineage = first;
        wrong_lineage.lineage = ProjectionLineage::ReplayEvidence;
        let incomplete_lineage = generic(vec![wrong_lineage]);
        assert!(matches!(
            fixture.machine.proof_store.validate_prepared_replay_route(
                fixture.lower,
                fixture.upper,
                &incomplete_lineage,
            ),
            Err(ProofFailure::IncompleteMandatoryData {
                field: MandatoryProofField::ReplayParentLineage,
                ..
            })
        ));

        let route = cpk_7_incremental_route(&fixture, None);
        let duplicate_incremental = PreparedReplayRoute {
            routing: ReplayRouting::IncrementalOnly,
            proof_event: PreparedReplayParents {
                pair_replay: None,
                incremental_replays: vec![
                    PreparedIncrementalReplay {
                        route,
                        parents: PreparedReplayParentSet::default(),
                    },
                    PreparedIncrementalReplay {
                        route,
                        parents: PreparedReplayParentSet::default(),
                    },
                ],
            },
        };
        assert!(matches!(
            fixture.machine.proof_store.validate_prepared_replay_route(
                fixture.lower,
                fixture.upper,
                &duplicate_incremental,
            ),
            Err(ProofFailure::ReplayRoutingInvariantViolation {
                kind: ReplayRoutingInvariantViolation::DuplicatePreparedIncrementalRoute,
                ..
            })
        ));

        let payload_mismatch = PreparedReplayRoute {
            routing: ReplayRouting::Generic,
            proof_event: PreparedReplayParents::default(),
        };
        assert!(matches!(
            fixture.machine.proof_store.validate_prepared_replay_route(
                fixture.lower,
                fixture.upper,
                &payload_mismatch,
            ),
            Err(ProofFailure::ReplayRoutingInvariantViolation {
                kind: ReplayRoutingInvariantViolation::RoutingPayloadMismatch,
                ..
            })
        ));
    }

    #[test]
    fn cpk_7_slice_a_prepared_parent_blocks_share_exact_entries() {
        let lower_parent = PreparedReplayParent {
            side: ReplayClaimParentSide::Lower,
            coverage_root: UpperReplayClaimId(1),
            representative_claim: UpperReplayClaimId(2),
            lineage: ProjectionLineage::ReplayConstraint,
        };
        let upper_parent = PreparedReplayParent {
            side: ReplayClaimParentSide::Upper,
            coverage_root: UpperReplayClaimId(3),
            representative_claim: UpperReplayClaimId(4),
            lineage: ProjectionLineage::ReplayEvidence,
        };
        let entries: Arc<[PreparedReplayParent]> = Arc::from([lower_parent]);
        let first = PreparedReplayParentBlock::Shared(Arc::clone(&entries));
        let second = PreparedReplayParentBlock::Shared(Arc::clone(&entries));
        let (
            PreparedReplayParentBlock::Shared(first),
            PreparedReplayParentBlock::Shared(second),
        ) = (first, second)
        else {
            unreachable!("the fixture constructs shared parent blocks")
        };
        assert!(Arc::ptr_eq(&first, &second));
        assert_eq!(first.as_ref(), [lower_parent]);
        assert_eq!(
            PreparedReplayParentBlock::default(),
            PreparedReplayParentBlock::Empty
        );
        let parents = PreparedReplayParentSet {
            lower: PreparedReplayParentBlock::Shared(first),
            upper: PreparedReplayParentBlock::Shared(Arc::from([upper_parent])),
        };
        assert_eq!(
            parents.iter().copied().collect::<Vec<_>>(),
            vec![lower_parent, upper_parent],
            "the logical adapter always emits the complete lower block before the upper block",
        );
    }

    #[test]
    fn cpk_7_slice_a_replay_indexes_update_atomically_with_writers() {
        let mut machine = cpk_machine();
        let (old_record, claim) = cpk_7_record_original_claim(&mut machine, 0);
        let occurrence_index = machine.proof_store.upper_claim_index[&claim];
        assert_eq!(machine.proof_store.upper_claims[occurrence_index].claim, claim);
        assert_eq!(
            machine.proof_store.claims_by_upper_record.get(&old_record),
            Some(&vec![claim]),
        );

        let (new_record, existing_claim) = cpk_7_record_original_claim(&mut machine, 1);
        machine.move_upper_replay_claim(claim, new_record);
        assert!(!machine.proof_store.claims_by_upper_record.contains_key(&old_record));
        assert_eq!(
            machine.proof_store.claims_by_upper_record.get(&new_record),
            Some(&vec![claim, existing_claim]),
            "the moved representative is inserted in canonical coverage-root order",
        );
        assert_eq!(
            machine.proof_store.upper_claims[occurrence_index].current_record,
            new_record,
        );

        let lower_record = BoundRecordId(70_000);
        let proofs = [SchemeProjectionProof {
            lower_record,
            support: SchemeProjectionProofSupport::Claimed(claim),
        }];
        machine
            .proof_store
            .record_projection_supports(lower_record, &proofs);
        assert_eq!(
            machine
                .proof_store
                .claimed_parents_by_lower_record
                .get(&lower_record),
            Some(&vec![claim]),
        );

        let root = claim;
        let state = UnweightedRowReductionRecordId(70_000);
        machine.proof_store.record_live_coverage(root, state, true);
        machine.proof_store.record_live_coverage(root, state, true);
        assert_eq!(
            machine.proof_store.live_states_by_coverage_root[&root].len(),
            1,
            "duplicate live writes must remain idempotent in both indexes",
        );
        assert!(machine.proof_store.live_coverage.contains(&(root, state)));
        machine.proof_store.record_live_coverage(root, state, false);
        assert!(!machine.proof_store.live_coverage.contains(&(root, state)));
        assert!(
            !machine
                .proof_store
                .live_states_by_coverage_root
                .contains_key(&root),
            "empty live-state sets canonicalize to no root entry",
        );
    }

    #[test]
    fn cpk_8b_live_coverage_transition_is_owned_by_the_cpk_index() {
        let mut store = ProofOccurrenceStore::default();
        let root = UpperReplayClaimId(71_000);
        let state = UnweightedRowReductionRecordId(71_000);
        let insertion = store.prepare_live_coverage_transition(root, state, true);
        assert_eq!(
            insertion,
            PreparedLiveCoverageTransition::Changed {
                root,
                state,
                active: true,
                was_empty: true,
                is_empty: false,
            },
        );
        store.record_prepared_live_coverage(insertion);
        assert_eq!(
            store.prepare_live_coverage_transition(root, state, true),
            PreparedLiveCoverageTransition::Unchanged,
            "the CPK index owns exact duplicate classification",
        );

        let removal = store.prepare_live_coverage_transition(root, state, false);
        assert_eq!(
            removal,
            PreparedLiveCoverageTransition::Changed {
                root,
                state,
                active: false,
                was_empty: false,
                is_empty: true,
            },
        );
        store.record_prepared_live_coverage(removal);
        assert_eq!(
            store.prepare_live_coverage_transition(root, state, false),
            PreparedLiveCoverageTransition::Unchanged,
        );
    }

    #[test]
    fn cpk_8b_original_claim_writer_uses_the_allocation_snapshot() {
        let mut machine = cpk_machine();
        let owner = TypeVar(71_100);
        let endpoint = machine.alloc_neg(Neg::Var(TypeVar(71_101)));
        let record = machine
            .bounds
            .add_upper(
                owner,
                endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let producer = ConstraintRecordId(71_102);
        let registration = machine.original_upper_replay_claim(
            record,
            producer,
            UpperReplayClaimKind::Direct,
        );
        let claim = registration.claim;

        machine.bounds.upper_replay_claims[claim.0 as usize].current_record =
            BoundRecordId(71_103);
        machine
            .proof_store
            .record_prepared_upper_claim(&registration.proof_admission);

        assert_eq!(
            machine.proof_store.upper_claims,
            vec![UpperClaimOccurrence {
                claim,
                coverage_root: claim,
                kind: UpperClaimKind::Direct,
                full_lineage: UpperClaimLineage::Original,
                lineage: ProjectionLineage::Original,
                producer,
                current_record: record,
            }],
            "the CPK claim writer must consume the allocation-time event, not re-read flat state",
        );
    }

    #[test]
    fn cpk_7_slice_a_claim_index_writes_do_not_scan_the_global_claim_store() {
        let mut machine = cpk_machine();
        machine
            .proof_store
            .replay_index_record_comparisons
            .set(0);
        for ordinal in 0..128 {
            cpk_7_record_original_claim(&mut machine, ordinal);
        }
        assert_eq!(machine.proof_store.upper_claims.len(), 128);
        assert_eq!(machine.proof_store.claims_by_upper_record.len(), 128);
        assert_eq!(
            machine.proof_store.replay_index_record_comparisons.get(),
            0,
            "one claim per record requires point lookup only, independent of global store size",
        );
    }

    fn cpk_gap_1_projection_record(machine: &mut ConstraintMachine, ordinal: u32) -> BoundRecordId {
        cpk_4_projection_record(machine, 50_000 + ordinal).0
    }

    fn cpk_gap_1_set_supports_and_formula(
        machine: &mut ConstraintMachine,
        record: BoundRecordId,
        supports: Vec<SchemeProjectionProofSupport>,
        clauses: Vec<ProjectionClause>,
    ) {
        machine
            .proof_store
            .projection_supports
            .insert(record, supports);
        machine
            .proof_store
            .projection_formulas
            .insert(record, clauses);
    }

    #[test]
    fn cpk_gap_1_project_lower_rejects_missing_semantic_record() {
        let machine = cpk_machine();
        let missing = BoundRecordId(u32::MAX);
        let (actual, _) = project_lower_for_test(&machine, missing);
        assert_eq!(
            actual,
            Err(ProofFailure::MissingSemanticFact {
                fact: SemanticFactRef::Bound(missing),
            })
        );
    }

    #[test]
    fn cpk_gap_1_project_lower_preserves_no_ledger_unclaimed() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 0);
        let (actual, _) = project_lower_for_test(&machine, record);
        assert_eq!(actual, Ok(ProjectionDecision::Unclaimed));
    }

    #[test]
    fn cpk_8b_projection_support_writer_uses_the_admission_snapshot() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 101);
        let initial = ProjectionProofCarrier::Origin(OriginId(70_101));
        cpk_4_add_independent_support(&mut machine, record, initial);
        let admitted = ProjectionProofCarrier::Origin(OriginId(70_102));
        let mutation = machine
            .bounds
            .update_scheme_projection_proofs(record, &[], &[admitted]);

        let later = ProjectionProofCarrier::Origin(OriginId(70_103));
        let _later_mutation = machine
            .bounds
            .update_scheme_projection_proofs(record, &[], &[later]);
        machine.record_projection_mutation_in_proof_store(&mutation);

        assert_eq!(
            machine.proof_store.projection_supports[&record],
            vec![
                SchemeProjectionProofSupport::Independent(initial),
                SchemeProjectionProofSupport::Independent(admitted),
            ],
            "the CPK writer must consume the admission-fixed payload, not re-read the flat ledger",
        );
    }

    #[test]
    fn cpk_gap_1_project_lower_rejects_orphan_formula() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 1);
        let support = SchemeProjectionProofSupport::Independent(ProjectionProofCarrier::Incomplete);
        machine.proof_store.projection_formulas.insert(
            record,
            vec![ProjectionClause::Standalone {
                support,
                attribution: None,
            }],
        );
        let (actual, _) = project_lower_for_test(&machine, record);
        assert_eq!(
            actual,
            Err(ProofFailure::ProjectionInvariantViolation {
                record,
                kind: ProjectionInvariantViolation::OrphanFormula,
            })
        );
    }

    #[test]
    fn cpk_gap_1_project_lower_rejects_support_without_formula() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 2);
        machine.proof_store.projection_supports.insert(
            record,
            vec![SchemeProjectionProofSupport::Independent(
                ProjectionProofCarrier::Incomplete,
            )],
        );
        let (actual, _) = project_lower_for_test(&machine, record);
        assert_eq!(
            actual,
            Err(ProofFailure::MissingProofFact {
                fact: ProofFactRef::ProjectionFormula(record),
            })
        );
    }

    #[test]
    fn cpk_gap_1_project_lower_rejects_dangling_claim() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 3);
        let claim = UpperReplayClaimId(50_003);
        let support = SchemeProjectionProofSupport::Claimed(claim);
        cpk_gap_1_set_supports_and_formula(
            &mut machine,
            record,
            vec![support],
            vec![ProjectionClause::Standalone {
                support,
                attribution: None,
            }],
        );
        let (actual, _) = project_lower_for_test(&machine, record);
        assert_eq!(
            actual,
            Err(ProofFailure::DanglingProofReference {
                owner: ProofFactRef::ProjectionSupports(record),
                target: ProofFactRef::UpperClaim(claim),
            })
        );
    }

    #[test]
    fn cpk_gap_1_project_lower_rejects_duplicate_coverage_root() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 4);
        let root = UpperReplayClaimId(0);
        let representative = UpperReplayClaimId(1);
        for (claim, coverage_root) in [(root, root), (representative, root)] {
            let index = machine.proof_store.upper_claims.len();
            machine.proof_store.upper_claims.push(UpperClaimOccurrence {
                claim,
                coverage_root,
                kind: UpperClaimKind::Direct,
                full_lineage: UpperClaimLineage::Original,
                lineage: ProjectionLineage::Original,
                producer: ConstraintRecordId(50_004),
                current_record: record,
            });
            machine.proof_store.upper_claim_index.insert(claim, index);
        }
        let supports = vec![
            SchemeProjectionProofSupport::Claimed(root),
            SchemeProjectionProofSupport::Claimed(representative),
        ];
        let clauses = supports
            .iter()
            .copied()
            .map(|support| ProjectionClause::Standalone {
                support,
                attribution: None,
            })
            .collect();
        cpk_gap_1_set_supports_and_formula(&mut machine, record, supports, clauses);
        let (actual, _) = project_lower_for_test(&machine, record);
        assert_eq!(
            actual,
            Err(ProofFailure::ProjectionInvariantViolation {
                record,
                kind: ProjectionInvariantViolation::DuplicateClaimedRoot,
            })
        );
    }

    #[test]
    fn cpk_gap_1_formula_matches_claimed_support_by_coverage_root() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 9);
        let root = UpperReplayClaimId(0);
        let representative = UpperReplayClaimId(1);
        for (claim, coverage_root) in [(root, root), (representative, root)] {
            let index = machine.proof_store.upper_claims.len();
            machine.proof_store.upper_claims.push(UpperClaimOccurrence {
                claim,
                coverage_root,
                kind: UpperClaimKind::Direct,
                full_lineage: UpperClaimLineage::Original,
                lineage: ProjectionLineage::Original,
                producer: ConstraintRecordId(50_009),
                current_record: record,
            });
            machine.proof_store.upper_claim_index.insert(claim, index);
        }
        let stored_support = SchemeProjectionProofSupport::Claimed(representative);
        let formula_support = SchemeProjectionProofSupport::Claimed(root);
        cpk_gap_1_set_supports_and_formula(
            &mut machine,
            record,
            vec![stored_support],
            vec![ProjectionClause::Standalone {
                support: formula_support,
                attribution: None,
            }],
        );

        let (actual, _) = project_lower_for_test(&machine, record);
        assert_eq!(
            actual,
            Ok(ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    uncovered_claims: vec![ProjectionClaimSupport {
                        coverage_root: root,
                        representative_claim: representative,
                    }],
                    independent_supports: Vec::new(),
                },
            })
        );
    }

    #[test]
    fn cpk_gap_1_project_lower_rejects_noncanonical_support_order() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 5);
        let high = OriginId(50_005);
        let low = OriginId(50_004);
        for origin in [high, low] {
            machine.proof_store.record_occurrence(
                ProofResult::Semantic(SemanticFactRef::Constraint(ConstraintRecordId(origin.0))),
                ProofCause::Root(origin),
                vec![ProofParent::Origin(origin)],
                ProvenanceCompleteness::Complete,
            );
        }
        let supports = vec![
            SchemeProjectionProofSupport::Independent(ProjectionProofCarrier::Origin(high)),
            SchemeProjectionProofSupport::Independent(ProjectionProofCarrier::Origin(low)),
        ];
        let clauses = supports
            .iter()
            .copied()
            .map(|support| ProjectionClause::Standalone {
                support,
                attribution: None,
            })
            .collect();
        cpk_gap_1_set_supports_and_formula(&mut machine, record, supports, clauses);
        let (actual, _) = project_lower_for_test(&machine, record);
        assert_eq!(
            actual,
            Err(ProofFailure::NonCanonicalProjectionOrder { record })
        );
    }

    #[test]
    fn cpk_gap_1_project_lower_cycle_cuts_only_the_circular_route() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 6);
        let other = cpk_gap_1_projection_record(&mut machine, 7);
        let support = SchemeProjectionProofSupport::Independent(ProjectionProofCarrier::Incomplete);
        let replay = BinaryReplayDerivation {
            pivot: TypeVar(50_006),
            lower: record,
            upper: other,
            rule: ReplayRule::LowerBoundAdded,
        };
        cpk_gap_1_set_supports_and_formula(
            &mut machine,
            record,
            vec![support],
            vec![ProjectionClause::ReplayConjunction {
                support,
                carrier: replay,
                lower: record,
                upper: other,
                attribution: None,
            }],
        );
        let (actual, round) = project_lower_for_test(&machine, record);
        assert_eq!(actual, Ok(ProjectionDecision::Excluded));
        assert_eq!(round.cycle_cuts(), 1);
        assert!(round.memo_sharing_disabled);
    }

    #[test]
    fn cpk_gap_1_incomplete_is_a_normal_independent_support() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 8);
        let carrier = ProjectionProofCarrier::Incomplete;
        let support = SchemeProjectionProofSupport::Independent(carrier);
        cpk_gap_1_set_supports_and_formula(
            &mut machine,
            record,
            vec![support],
            vec![ProjectionClause::Standalone {
                support,
                attribution: None,
            }],
        );
        let (actual, _) = project_lower_for_test(&machine, record);
        assert_eq!(
            actual,
            Ok(ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    uncovered_claims: Vec::new(),
                    independent_supports: vec![carrier],
                },
            })
        );
    }

    #[test]
    fn cpk_original_standalone_writer_publishes_mixed_projection_contract() {
        let (machine, endpoint, owner, covered_root) =
            ConstraintMachine::compact_scheme_projection_unmatched_route_fixture(true);
        let record = machine
            .bounds()
            .of(owner)
            .expect("fixture owner")
            .generalized_projection_lowers()
            .find_map(|(record, bound)| {
                matches!(machine.types().pos(bound.pos), Pos::Var(found) if *found == endpoint)
                    .then_some(record)
            })
            .expect("mixed fixture lower record");
        let cpk = machine.proof_store.projection_formulas[&record]
            .iter()
            .copied()
            .map(|clause| match clause {
                ProjectionClause::Standalone { support, .. } => {
                    (support, RecordProofClause::Standalone { support })
                }
                ProjectionClause::DerivedUnary {
                    support,
                    carrier,
                    premise,
                    ..
                } => (
                    support,
                    RecordProofClause::DerivedUnary { carrier, premise },
                ),
                ProjectionClause::ReplayConjunction {
                    support,
                    carrier,
                    lower,
                    upper,
                    ..
                } => (
                    support,
                    RecordProofClause::ReplayConjunction {
                        carrier,
                        lower_premise: lower,
                        upper_premise: upper,
                    },
                ),
            })
            .collect::<Vec<_>>();
        assert_eq!(cpk.len(), 2, "fixture has one clause per canonical root");
        for (support, clause) in &cpk {
            assert!(
                machine
                    .bounds
                    .record_proof_clause_link_is_registered(record, *support, *clause),
                "each CPK formula entry must be the exact legacy clause link",
            );
        }
        assert!(matches!(
            machine.proof_store.projection_formulas[&record].as_slice(),
            [
                ProjectionClause::Standalone {
                    attribution: Some(ProjectionLineage::Original),
                    ..
                },
                ProjectionClause::DerivedUnary {
                    attribution: Some(ProjectionLineage::ReductionRouteConstraint),
                    ..
                }
            ]
        ));

        let direct_claim = machine.proof_store.projection_supports[&record]
            .iter()
            .find_map(|support| match support {
                SchemeProjectionProofSupport::Claimed(claim)
                    if machine
                        .proof_store
                        .upper_claim(*claim)
                        .is_some_and(|occurrence| occurrence.coverage_root != covered_root) =>
                {
                    Some(*claim)
                }
                SchemeProjectionProofSupport::Claimed(_)
                | SchemeProjectionProofSupport::Independent(_) => None,
            })
            .expect("mixed fixture has one uncovered direct claim");
        let direct_root = machine
            .proof_store
            .upper_claim(direct_claim)
            .expect("direct claim is present in CPK")
            .coverage_root;
        let (decision, _) = project_lower_for_test(&machine, record);
        assert_eq!(
            decision,
            Ok(ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    uncovered_claims: vec![ProjectionClaimSupport {
                        coverage_root: direct_root,
                        representative_claim: direct_claim,
                    }],
                    independent_supports: Vec::new(),
                },
            })
        );
    }

    #[test]
    fn cpk_gap_1_mixed_claim_fixture_matches_all_four_cpk_consumers_exactly() {
        let (mut machine, endpoint, owner, covered_root) =
            ConstraintMachine::compact_scheme_projection_unmatched_route_fixture(true);
        let mixed_record = machine
            .bounds()
            .of(owner)
            .expect("fixture owner")
            .generalized_projection_lowers()
            .find_map(|(record, bound)| {
                matches!(machine.types().pos(bound.pos), Pos::Var(found) if *found == endpoint)
                    .then_some(record)
            })
            .expect("mixed fixture target record");
        let independent = ProjectionProofCarrier::Incomplete;
        let independent_support = SchemeProjectionProofSupport::Independent(independent);
        let mutation = machine
            .bounds
            .update_scheme_projection_proofs(mixed_record, &[], &[independent]);
        machine.apply_scheme_projection_mutation(mutation);
        machine.register_cpk_projection_clause_for_test(
            mixed_record,
            RecordProofClauseLinkAdmission::independent(
                independent_support,
                RecordProofClause::Standalone {
                    support: independent_support,
                },
            ),
        );
        let raw_records = machine
            .bounds()
            .of(owner)
            .expect("fixture owner")
            .generalized_projection_lowers()
            .map(|(record, bound)| (record, bound.pos, bound.weights.clone()))
            .collect::<Vec<_>>();
        let mut round = ProjectionEvaluationRound::new();
        let cpk_entries = raw_records
            .iter()
            .filter_map(|(record, pos, weights)| {
                let decision = machine
                    .proof_store
                    .project_lower(&machine, *record, &mut round)
                    .expect("mixed fixture has complete CPK projection metadata");
                match decision {
                    ProjectionDecision::Excluded => None,
                    ProjectionDecision::Unclaimed => Some((
                        *record,
                        *pos,
                        weights.clone(),
                        SchemeProjectableLowerReason::Unclaimed,
                    )),
                    ProjectionDecision::Included { supports } => Some((
                        *record,
                        *pos,
                        weights.clone(),
                        SchemeProjectableLowerReason::Qualified {
                            uncovered_claims: supports
                                .uncovered_claims
                                .iter()
                                .map(|support| support.representative_claim)
                                .collect(),
                            independent_supports: supports.independent_supports,
                        },
                    )),
                }
            })
            .collect::<Vec<_>>();
        assert_eq!(cpk_entries.len(), 1, "only the mixed lower is projectable");

        let (record, _, _, reason) = cpk_entries
            .iter()
            .find(|(_, pos, _, _)| {
                matches!(machine.types().pos(*pos), Pos::Var(found) if *found == endpoint)
            })
            .expect("mixed fixture target record");
        let SchemeProjectableLowerReason::Qualified { .. } = reason
        else {
            panic!("mixed fixture target must be qualified");
        };
        let (decision, _) = project_lower_for_test(&machine, *record);
        let ProjectionDecision::Included { supports } = decision.expect("complete CPK decision")
        else {
            panic!("mixed fixture target must be included");
        };
        let direct_claim = machine.proof_store.projection_supports[record]
            .iter()
            .find_map(|support| match support {
                SchemeProjectionProofSupport::Claimed(claim)
                    if machine
                        .proof_store
                        .upper_claim(*claim)
                        .is_some_and(|occurrence| occurrence.coverage_root != covered_root) =>
                {
                    Some(*claim)
                }
                SchemeProjectionProofSupport::Claimed(_)
                | SchemeProjectionProofSupport::Independent(_) => None,
            })
            .expect("mixed fixture has one uncovered direct claim");
        let direct_root = machine
            .proof_store
            .upper_claim(direct_claim)
            .expect("direct claim is present in CPK")
            .coverage_root;
        assert_eq!(
            supports,
            ProjectionSupportSet {
                uncovered_claims: vec![ProjectionClaimSupport {
                    coverage_root: direct_root,
                    representative_claim: direct_claim,
                }],
                independent_supports: vec![independent],
            },
        );
        assert_eq!(supports.independent_supports, vec![independent]);
        assert!(supports
            .uncovered_claims
            .windows(2)
            .all(|pair| pair[0].coverage_root.0 < pair[1].coverage_root.0));

        let compact = crate::compact::compact_type_var_for_scheme(&machine, owner);
        assert_eq!(
            compact,
            crate::compact::compact_type_var(&machine, owner),
            "every raw lower selected by CPK must produce the exact raw compact root"
        );
        let aliases = crate::generalize::positive_aliases_within_scheme_for_cpk_test(
            &machine,
            [endpoint],
            owner,
        );
        assert_eq!(aliases, vec![endpoint]);

        let generalized = crate::generalize::GeneralizedCompactRoot {
            compact: crate::compact::CompactRoot::default(),
            role_predicates: Vec::new(),
            quantifiers: Vec::new(),
            stack_quantifiers: Vec::new(),
            substitutions: Vec::new(),
            sandwiches: Vec::new(),
        };
        let (witnesses, completeness) =
            crate::generalize::capture_generalized_witnesses(&machine, owner, &generalized);
        assert_eq!(
            completeness,
            ProvenanceCompleteness::Incomplete,
            "PUSP-C keeps whole-scheme completeness incomplete even when exact parents survive",
        );
        let expected_parents = supports
            .uncovered_claims
            .iter()
            .map(|support| GeneralizationParent::BoundClaim {
                bound: *record,
                claim: support.representative_claim,
            })
            .chain(supports.independent_supports.iter().map(|carrier| {
                GeneralizationParent::BoundProjectionProof {
                    bound: *record,
                    carrier: *carrier,
                }
            }))
            .collect::<Vec<_>>();
        for role in [
            GeneralizedWitnessRole::LowerBound,
            GeneralizedWitnessRole::ConstraintRelation,
        ] {
            let actual = witnesses
                .iter()
                .find(|draft| draft.path == GeneralizedTypePath::default() && draft.role == role)
                .expect("mixed fixture root witness")
                .incoming
                .iter()
                .flat_map(|edge| &edge.parents)
                .copied()
                .collect::<Vec<_>>();
            assert_eq!(actual, expected_parents, "exact witness parent order for {role:?}");
        }
    }

    #[test]
    fn cpk_gap_1_replay_conjunction_matches_all_four_cpk_consumers() {
        let mut included = cpk_machine();
        let included_record = cpk_gap_1_projection_record(&mut included, 25);
        let included_owner = included.bounds.record(included_record).unwrap().owner();
        let lower = cpk_gap_1_projection_record(&mut included, 26);
        let upper = cpk_gap_1_projection_record(&mut included, 27);
        let carrier = ProjectionProofCarrier::Incomplete;
        let support = cpk_4_add_independent_support(&mut included, included_record, carrier);
        let replay = BinaryReplayDerivation {
            pivot: TypeVar(50_025),
            lower,
            upper,
            rule: ReplayRule::LowerBoundAdded,
        };
        included.register_cpk_projection_clause_for_test(
            included_record,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::ReplayConjunction {
                    carrier: replay,
                    lower_premise: lower,
                    upper_premise: upper,
                },
            ),
        );
        assert_single_lower_matches_all_four_cpk_consumers(
            &included,
            included_owner,
            included_record,
            ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    uncovered_claims: Vec::new(),
                    independent_supports: vec![carrier],
                },
            },
        );

        let mut excluded = cpk_machine();
        let excluded_record = cpk_gap_1_projection_record(&mut excluded, 28);
        let excluded_owner = excluded.bounds.record(excluded_record).unwrap().owner();
        let other = cpk_gap_1_projection_record(&mut excluded, 29);
        let support = cpk_4_add_independent_support(&mut excluded, excluded_record, carrier);
        let replay = BinaryReplayDerivation {
            pivot: TypeVar(50_028),
            lower: excluded_record,
            upper: other,
            rule: ReplayRule::LowerBoundAdded,
        };
        excluded.register_cpk_projection_clause_for_test(
            excluded_record,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::ReplayConjunction {
                    carrier: replay,
                    lower_premise: excluded_record,
                    upper_premise: other,
                },
            ),
        );
        let mut round = ProjectionEvaluationRound::new();
        assert_eq!(
            excluded
                .proof_store
                .project_lower(&excluded, excluded_record, &mut round),
            Ok(ProjectionDecision::Excluded),
        );
        assert_eq!(round.cycle_cuts(), 1);
        assert_single_lower_matches_all_four_cpk_consumers(
            &excluded,
            excluded_owner,
            excluded_record,
            ProjectionDecision::Excluded,
        );
    }

    fn assert_single_lower_matches_all_four_cpk_consumers(
        machine: &ConstraintMachine,
        owner: TypeVar,
        record: BoundRecordId,
        expected: ProjectionDecision,
    ) {
        let (actual, _) = project_lower_for_test(machine, record);
        assert_eq!(actual, Ok(expected.clone()));
        if !matches!(expected, ProjectionDecision::Excluded) {
            assert_eq!(
                crate::compact::compact_type_var_for_scheme(machine, owner),
                crate::compact::compact_type_var(machine, owner),
            );
        }
        assert!(crate::generalize::positive_aliases_within_scheme_for_cpk_test(
            machine,
            std::iter::empty(),
            owner,
        )
        .is_empty());

        let generalized = crate::generalize::GeneralizedCompactRoot {
            compact: crate::compact::CompactRoot::default(),
            role_predicates: Vec::new(),
            quantifiers: Vec::new(),
            stack_quantifiers: Vec::new(),
            substitutions: Vec::new(),
            sandwiches: Vec::new(),
        };
        let (witnesses, _) =
            crate::generalize::capture_generalized_witnesses(machine, owner, &generalized);
        let actual_parents = witnesses
            .iter()
            .find(|draft| {
                draft.path == GeneralizedTypePath::default()
                    && draft.role == GeneralizedWitnessRole::LowerBound
            })
            .map(|draft| {
                draft
                    .incoming
                    .iter()
                    .flat_map(|edge| &edge.parents)
                    .copied()
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let expected_parents = match expected {
            ProjectionDecision::Excluded => Vec::new(),
            ProjectionDecision::Unclaimed => vec![GeneralizationParent::Bound(record)],
            ProjectionDecision::Included { supports } => supports
                .uncovered_claims
                .into_iter()
                .map(|support| GeneralizationParent::BoundClaim {
                    bound: record,
                    claim: support.representative_claim,
                })
                .chain(supports.independent_supports.into_iter().map(|carrier| {
                    GeneralizationParent::BoundProjectionProof {
                        bound: record,
                        carrier,
                    }
                }))
                .collect(),
        };
        assert_eq!(actual_parents, expected_parents);
    }

    fn record_test_origin(
        machine: &mut ConstraintMachine,
        record: BoundRecordId,
        origin: OriginId,
    ) {
        machine.proof_store.record_occurrence(
            ProofResult::Semantic(SemanticFactRef::Bound(record)),
            ProofCause::Bound(BoundDerivation::Origin(origin)),
            vec![ProofParent::Origin(origin)],
            ProvenanceCompleteness::Complete,
        );
    }

    #[test]
    fn cpk_gap_1_unclaimed_standalone_derived_and_incomplete_match_cpk_consumers() {
        let mut no_ledger = cpk_machine();
        let no_ledger_record = cpk_gap_1_projection_record(&mut no_ledger, 20);
        let no_ledger_owner = no_ledger.bounds.record(no_ledger_record).unwrap().owner();
        let before = (
            no_ledger.proof_store.projection_supports.len(),
            no_ledger.proof_store.projection_formulas.len(),
        );
        assert_single_lower_matches_all_four_cpk_consumers(
            &no_ledger,
            no_ledger_owner,
            no_ledger_record,
            ProjectionDecision::Unclaimed,
        );
        assert_eq!(
            before,
            (
                no_ledger.proof_store.projection_supports.len(),
                no_ledger.proof_store.projection_formulas.len(),
            ),
            "the no-claim query must allocate no persistent proof state",
        );

        no_ledger
            .bounds
            .projection_proofs_by_lower_record
            .insert(no_ledger_record, Vec::new());
        no_ledger
            .bounds
            .scheme_projection_claimed_lower_owners
            .insert(no_ledger_owner);
        no_ledger
            .proof_store
            .projection_supports
            .insert(no_ledger_record, Vec::new());
        no_ledger
            .proof_store
            .projection_formulas
            .insert(no_ledger_record, Vec::new());
        assert_single_lower_matches_all_four_cpk_consumers(
            &no_ledger,
            no_ledger_owner,
            no_ledger_record,
            ProjectionDecision::Unclaimed,
        );

        let mut standalone = cpk_machine();
        let standalone_record = cpk_gap_1_projection_record(&mut standalone, 21);
        let standalone_owner = standalone.bounds.record(standalone_record).unwrap().owner();
        let origin = OriginId(50_021);
        record_test_origin(&mut standalone, standalone_record, origin);
        let carrier = ProjectionProofCarrier::Origin(origin);
        let support = cpk_4_add_independent_support(&mut standalone, standalone_record, carrier);
        standalone.register_cpk_projection_clause_for_test(
            standalone_record,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::Standalone { support },
            ),
        );
        assert_single_lower_matches_all_four_cpk_consumers(
            &standalone,
            standalone_owner,
            standalone_record,
            ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    uncovered_claims: Vec::new(),
                    independent_supports: vec![carrier],
                },
            },
        );

        let mut derived = cpk_machine();
        let lower = derived.alloc_pos(Pos::Var(TypeVar(61_000)));
        let upper = derived.alloc_neg(Neg::Var(TypeVar(61_001)));
        derived.subtype(lower, upper, OriginId::unknown_internal());
        let constraint = derived
            .constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("derived-unary fixture constraint");
        let derived_record = cpk_gap_1_projection_record(&mut derived, 22);
        let derived_owner = derived.bounds.record(derived_record).unwrap().owner();
        let origin = OriginId(50_022);
        record_test_origin(&mut derived, derived_record, origin);
        let carrier = ProjectionProofCarrier::Origin(origin);
        let support = cpk_4_add_independent_support(&mut derived, derived_record, carrier);
        derived.register_cpk_projection_clause_for_test(
            derived_record,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                        parent: constraint,
                        rule: StructuralDerivationRule::FunctionReturn,
                    }),
                    premise: ProofPremise::Constraint(constraint),
                },
            ),
        );
        assert_single_lower_matches_all_four_cpk_consumers(
            &derived,
            derived_owner,
            derived_record,
            ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    uncovered_claims: Vec::new(),
                    independent_supports: vec![carrier],
                },
            },
        );

        let mut incomplete = cpk_machine();
        let incomplete_record = cpk_gap_1_projection_record(&mut incomplete, 23);
        let incomplete_owner = incomplete.bounds.record(incomplete_record).unwrap().owner();
        let carrier = ProjectionProofCarrier::Incomplete;
        let support = cpk_4_add_independent_support(&mut incomplete, incomplete_record, carrier);
        incomplete.register_cpk_projection_clause_for_test(
            incomplete_record,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::Standalone { support },
            ),
        );
        assert_single_lower_matches_all_four_cpk_consumers(
            &incomplete,
            incomplete_owner,
            incomplete_record,
            ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    uncovered_claims: Vec::new(),
                    independent_supports: vec![carrier],
                },
            },
        );
    }

    #[test]
    fn cpk_gap_1_included_empty_keeps_generalized_witness_parentless() {
        let (mut machine, endpoint, owner, _) =
            ConstraintMachine::compact_scheme_projection_unmatched_route_fixture(true);
        let record = machine
            .bounds()
            .of(owner)
            .expect("fixture owner")
            .generalized_projection_lowers()
            .find_map(|(record, bound)| {
                matches!(machine.types().pos(bound.pos), Pos::Var(found) if *found == endpoint)
                    .then_some(record)
            })
            .expect("mixed fixture lower record");
        let ProjectionDecision::Included { supports } =
            project_lower_for_test(&machine, record).0.expect("complete initial projection")
        else {
            panic!("mixed fixture must start included");
        };
        let uncovered = supports.uncovered_claims[0];

        // Add a formula route whose premise remains true after every direct claimed support is
        // covered. This is the reachable Included(empty) shape pinned by addendum section 4.4.
        let premise = cpk_gap_1_projection_record(&mut machine, 24);
        machine.register_cpk_projection_clause_for_test(
            record,
            RecordProofClauseLinkAdmission::claimed(
                uncovered.coverage_root,
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                        parent: ConstraintRecordId(0),
                        rule: StructuralDerivationRule::FunctionReturn,
                    }),
                    premise: ProofPremise::Record(premise),
                },
                ClaimedAttributionSource::FlatRetained,
            ),
        );
        let state = machine
            .proof_store
            .live_coverage
            .iter()
            .next()
            .expect("fixture has a live reduction state")
            .1;
        assert!(machine.insert_scheme_projection_live_coverage_state(
            uncovered.coverage_root,
            state,
        ));
        assert_eq!(
            project_lower_for_test(&machine, record).0,
            Ok(ProjectionDecision::Included {
                supports: ProjectionSupportSet::default(),
            }),
        );
        let generalized = crate::generalize::GeneralizedCompactRoot {
            compact: crate::compact::CompactRoot::default(),
            role_predicates: Vec::new(),
            quantifiers: Vec::new(),
            stack_quantifiers: Vec::new(),
            substitutions: Vec::new(),
            sandwiches: Vec::new(),
        };
        let (drafts, completeness) =
            crate::generalize::capture_generalized_witnesses(&machine, owner, &generalized);
        assert_eq!(completeness, ProvenanceCompleteness::Incomplete);
        assert!(drafts.iter().flat_map(|draft| &draft.incoming).flat_map(|edge| {
            &edge.parents
        }).all(|parent| match parent {
            GeneralizationParent::Bound(found)
            | GeneralizationParent::BoundClaim { bound: found, .. }
            | GeneralizationParent::BoundProjectionProof { bound: found, .. } => *found != record,
            GeneralizationParent::Constraint(_) => true,
        }), "Included(empty) must not fabricate any parent for the qualified record");

        machine.alloc_generalized_scheme_record(
            poly::expr::DefId(0),
            0,
            drafts,
            completeness,
        );
        let snapshot = machine.logical_proof_snapshot();
        assert!(
            snapshot
                .generalized
                .witnesses
                .iter()
                .flat_map(|witness| &witness.incoming)
                .flat_map(|edge| &edge.parents)
                .all(|parent| match parent {
                    crate::constraints::logical_proof_snapshot::CanonicalGeneralizationParent::Bound(found)
                    | crate::constraints::logical_proof_snapshot::CanonicalGeneralizationParent::BoundClaim { bound: found, .. }
                    | crate::constraints::logical_proof_snapshot::CanonicalGeneralizationParent::BoundProjectionProof { bound: found, .. } => *found != record.0 as usize,
                    crate::constraints::logical_proof_snapshot::CanonicalGeneralizationParent::Constraint(_) => true,
                }),
            "stored witnesses must retain the absence of a fallback bound parent",
        );
        let target_root = snapshot
            .portable
            .roots
            .iter()
            .position(|root| {
                matches!(
                    root,
                    crate::constraints::logical_proof_snapshot::CanonicalPortableRoot::Bound(
                        found
                    ) if *found == record.0 as usize
                )
            })
            .expect("portable target-bound root");
        let target_anchor = snapshot.portable.root_anchors[target_root]
            .expect("portable target-bound anchor");
        let target_node = snapshot.portable.snapshot.anchors()[target_anchor].node;
        let witness_nodes = snapshot
            .portable
            .roots
            .iter()
            .enumerate()
            .filter_map(|(index, root)| {
                matches!(
                    root,
                    crate::constraints::logical_proof_snapshot::CanonicalPortableRoot::GeneralizedWitness(_)
                )
                .then(|| {
                    let anchor = snapshot.portable.root_anchors[index]
                        .expect("portable generalized-witness anchor");
                    snapshot.portable.snapshot.anchors()[anchor].node
                })
            })
            .collect::<Vec<_>>();
        assert!(
            snapshot.portable.snapshot.edges().iter().all(|edge| {
                !witness_nodes.contains(&edge.child) || !edge.parents.contains(&target_node)
            }),
            "portable generalized witnesses must not fabricate the qualified bound as a parent",
        );
    }

    #[test]
    fn cpk_gap_1_five_lineages_project_through_the_real_formula_graph() {
        // CPK-4's writer matrix separately pins the five source-to-lineage mappings. Here each
        // attribution is placed on the same well-formed formula shape so this query/consumer
        // oracle isolates the required fact that attribution metadata never changes projection.
        let mut machine = cpk_machine();
        let lineages = [
            ProjectionLineage::Original,
            ProjectionLineage::ReplayConstraint,
            ProjectionLineage::ReplayEvidence,
            ProjectionLineage::StructuralConstraint,
            ProjectionLineage::ReductionRouteConstraint,
        ];
        for (index, lineage) in lineages.into_iter().enumerate() {
            let record = cpk_gap_1_projection_record(&mut machine, 31 + index as u32);
            let carrier = ProjectionProofCarrier::Incomplete;
            let support = cpk_4_add_independent_support(&mut machine, record, carrier);
            machine.register_cpk_projection_clause_for_test(
                record,
                RecordProofClauseLinkAdmission::independent(
                    support,
                    RecordProofClause::Standalone { support },
                ),
            );
            let [ProjectionClause::Standalone { attribution, .. }] = machine
                .proof_store
                .projection_formulas
                .get_mut(&record)
                .expect("five-lineage formula")
                .as_mut_slice()
            else {
                panic!("five-lineage fixture must stay standalone");
            };
            *attribution = Some(lineage);
            let owner = machine.bounds.record(record).unwrap().owner();
            assert_single_lower_matches_all_four_cpk_consumers(
                &machine,
                owner,
                record,
                ProjectionDecision::Included {
                    supports: ProjectionSupportSet {
                        uncovered_claims: Vec::new(),
                        independent_supports: vec![carrier],
                    },
                },
            );
        }
    }

    fn make_same_root_projection_included(
        order: [usize; 3],
    ) -> (CpkReplayAdmissionFixture, [UpperReplayClaimId; 3], BoundRecordId) {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let claims = [
            fixture.coverage_root,
            add_same_root_replay_claim(
                &mut fixture,
                TypeVar(62_000),
                ConstraintRecordId(62_000),
            ),
            add_same_root_replay_claim(
                &mut fixture,
                TypeVar(62_001),
                ConstraintRecordId(62_001),
            ),
        ];
        for index in order {
            fixture.machine.apply_cpk_replay_parent_arrival_for_test(
                fixture.result,
                fixture.carrier,
                claims[index],
            );
        }
        let record = fixture.carrier.lower;
        let support = SchemeProjectionProofSupport::Claimed(claims[order[0]]);
        fixture.machine.register_cpk_projection_clause_for_test(
            record,
            RecordProofClauseLinkAdmission::claimed(
                fixture.coverage_root,
                RecordProofClause::Standalone { support },
                ClaimedAttributionSource::FlatRetained,
            ),
        );
        (fixture, claims, record)
    }

    #[test]
    fn cpk_gap_1_same_root_representative_replacement_matches_all_consumers() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let replacement_claim = add_same_root_replay_claim(
            &mut fixture,
            TypeVar(63_000),
            ConstraintRecordId(63_000),
        );
        let record = cpk_gap_1_projection_record(&mut fixture.machine, 40);
        let owner = fixture.machine.bounds.record(record).unwrap().owner();
        let mutation = fixture.machine.bounds.update_scheme_projection_proofs(
            record,
            &[fixture.coverage_root],
            &[],
        );
        fixture.machine.apply_scheme_projection_mutation(mutation);
        fixture.machine.register_cpk_projection_clause_for_test(
            record,
            RecordProofClauseLinkAdmission::claimed(
                fixture.coverage_root,
                RecordProofClause::Standalone {
                    support: SchemeProjectionProofSupport::Claimed(fixture.coverage_root),
                },
                ClaimedAttributionSource::FlatRetained,
            ),
        );
        let before = project_lower_for_test(&fixture.machine, record)
            .0
            .expect("same-root fixture has complete CPK projection metadata");
        assert_eq!(
            before,
            ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    uncovered_claims: vec![ProjectionClaimSupport {
                        coverage_root: fixture.coverage_root,
                        representative_claim: fixture.coverage_root,
                    }],
                    independent_supports: Vec::new(),
                },
            },
        );
        let ProjectionDecision::Included { supports } = before else {
            panic!("same-root fixture must be included");
        };
        let before_representative = supports
            .uncovered_claims
            .iter()
            .find(|support| support.coverage_root == fixture.coverage_root)
            .expect("same-root support")
            .representative_claim;
        let mutation = fixture.machine.bounds.update_scheme_projection_proofs(
            record,
            &[replacement_claim],
            &[],
        );
        fixture.machine.apply_scheme_projection_mutation(mutation);
        let expected = ProjectionDecision::Included {
            supports: ProjectionSupportSet {
                uncovered_claims: vec![ProjectionClaimSupport {
                    coverage_root: fixture.coverage_root,
                    representative_claim: replacement_claim,
                }],
                independent_supports: Vec::new(),
            },
        };
        let ProjectionDecision::Included { supports } = &expected else {
            panic!("replacement must preserve inclusion");
        };
        let replacement = supports
            .uncovered_claims
            .iter()
            .find(|support| support.coverage_root == fixture.coverage_root)
            .expect("replacement support");
        assert_ne!(replacement.representative_claim, before_representative);
        assert_eq!(replacement.representative_claim, replacement_claim);
        assert_single_lower_matches_all_four_cpk_consumers(
            &fixture.machine,
            owner,
            record,
            expected,
        );
        let upper = fixture
            .machine
            .alloc_neg(Neg::Con(vec!["cpk-7-representative".into()], Vec::new()));
        fixture.machine.add_upper_bound(
            owner,
            upper,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );
        let prepared = cpk_7_direct_pair_route(&fixture.machine, record, owner, upper);
        assert_eq!(prepared.routing, ReplayRouting::Generic);
        assert_eq!(
            prepared
                .proof_event
                .pair_replay
                .as_ref()
                .expect("the no-claim upper requires Generic replay")
                .lower
                .as_slice()[0]
                .representative_claim,
            replacement_claim,
        );
    }

    #[test]
    fn cpk_gap_1_same_root_permutations_preserve_canonical_payload_shape() {
        let permutations = [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ];
        let mut canonical_decision = None;
        for order in permutations {
            let (fixture, _claims, record) = make_same_root_projection_included(order);
            let owner = fixture.machine.bounds.record(record).unwrap().owner();
            let expected = ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    uncovered_claims: vec![
                        ProjectionClaimSupport {
                            coverage_root: UpperReplayClaimId(0),
                            representative_claim: UpperReplayClaimId(0),
                        },
                        ProjectionClaimSupport {
                            coverage_root: fixture.coverage_root,
                            representative_claim: UpperReplayClaimId(4),
                        },
                    ],
                    independent_supports: Vec::new(),
                },
            };
            let (actual, _) = project_lower_for_test(&fixture.machine, record);
            assert_eq!(actual, Ok(expected.clone()), "arrival order {order:?}");
            assert_single_lower_matches_all_four_cpk_consumers(
                &fixture.machine,
                owner,
                record,
                expected.clone(),
            );
            let ProjectionDecision::Included { supports } = expected else {
                panic!("permutation fixture must be included");
            };
            let representative = supports
                .uncovered_claims
                .iter()
                .find(|support| support.coverage_root == fixture.coverage_root)
                .expect("same-root permutation support");
            assert_eq!(representative.coverage_root, fixture.coverage_root);
            let decision = ProjectionDecision::Included { supports };
            assert_eq!(
                decision,
                *canonical_decision.get_or_insert_with(|| decision.clone()),
                "the full project_lower payload must be invariant for {order:?}",
            );
        }
    }

    #[test]
    fn cpk_gap_1_every_proof_failure_is_attempt_terminal() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 30);
        let owner = ProofFactRef::ProjectionSupports(record);
        let failures = [
            ProofFailure::MissingSemanticFact {
                fact: SemanticFactRef::Bound(record),
            },
            ProofFailure::InvalidProjectionTarget {
                record,
                direction: BoundDirection::Upper,
                state: BoundRecordState::Ordinary,
            },
            ProofFailure::MissingProofFact {
                fact: ProofFactRef::ProjectionFormula(record),
            },
            ProofFailure::DanglingProofReference {
                owner,
                target: ProofFactRef::CoverageRoot(UpperReplayClaimId(60_000)),
            },
            ProofFailure::IncompleteMandatoryData {
                owner,
                field: MandatoryProofField::ExactCarrier,
            },
            ProofFailure::NonCanonicalProjectionOrder { record },
            ProofFailure::ResourceExhausted {
                operation: ProofOperation::ProjectLowerPreflight,
            },
        ];
        for failure in failures {
            let mut round = ProjectionEvaluationRound::new();
            round.terminal_failure = Some(failure.clone());
            assert_eq!(
                machine.proof_store.project_lower(&machine, record, &mut round),
                Err(failure.clone()),
            );
            assert_eq!(
                machine.proof_store.project_lower(&machine, record, &mut round),
                Err(failure),
                "an attempt-terminal failure must remain sticky",
            );
        }
        for kind in [
            ProjectionInvariantViolation::OrphanFormula,
            ProjectionInvariantViolation::DuplicateClaimedRoot,
            ProjectionInvariantViolation::DuplicateIndependentCarrier,
            ProjectionInvariantViolation::RepresentativeRootMismatch,
            ProjectionInvariantViolation::FormulaSupportMismatch,
            ProjectionInvariantViolation::FormulaCategoryOrder,
            ProjectionInvariantViolation::VisitingStateEscaped,
        ] {
            let failure = ProofFailure::ProjectionInvariantViolation { record, kind };
            let mut round = ProjectionEvaluationRound::new();
            round.terminal_failure = Some(failure.clone());
            assert_eq!(
                machine.proof_store.project_lower(&machine, record, &mut round),
                Err(failure),
            );
        }
        for operation in [
            ProofOperation::ProjectLowerPreflight,
            ProofOperation::ProjectLowerSupportCollection,
            ProofOperation::ProjectLowerEvaluation,
        ] {
            let failure = ProofFailure::ResourceExhausted { operation };
            let mut round = ProjectionEvaluationRound::new();
            round.terminal_failure = Some(failure.clone());
            assert_eq!(
                machine.proof_store.project_lower(&machine, record, &mut round),
                Err(failure),
            );
        }
    }

    fn cpk_4_projection_record(
        machine: &mut ConstraintMachine,
        ordinal: u32,
    ) -> (BoundRecordId, ProjectionProofCarrier) {
        let endpoint = machine.alloc_pos(Pos::Con(
            vec![format!("cpk-4-projection-{ordinal}")],
            Vec::new(),
        ));
        let record = machine
            .bounds
            .add_lower(
                TypeVar(30_000 + ordinal),
                endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        (
            record,
            ProjectionProofCarrier::ConstraintOrigin {
                constraint: ConstraintRecordId(30_000 + ordinal),
                origin: OriginId::unknown_internal(),
            },
        )
    }

    fn cpk_4_add_independent_support(
        machine: &mut ConstraintMachine,
        record: BoundRecordId,
        carrier: ProjectionProofCarrier,
    ) -> SchemeProjectionProofSupport {
        let support = SchemeProjectionProofSupport::Independent(carrier);
        machine
            .bounds
            .projection_proofs_by_lower_record
            .insert(record, Vec::new());
        let mutation = machine
            .bounds
            .update_scheme_projection_proofs(record, &[], &[carrier]);
        machine.apply_scheme_projection_mutation(mutation);
        support
    }

    struct CpkReplayAdmissionFixture {
        machine: ConstraintMachine,
        result: ConstraintRecordId,
        carrier: BinaryReplayDerivation,
        coverage_root: UpperReplayClaimId,
        parent_owner: TypeVar,
        parent_record: BoundRecordId,
    }

    fn cpk_3_replay_admission_fixture() -> CpkReplayAdmissionFixture {
        cpk_3_replay_admission_fixture_with_oracle(ProofReadAuthority::Cpk, true)
    }

    fn cpk_3_cpk_only_replay_admission_fixture() -> CpkReplayAdmissionFixture {
        cpk_3_replay_admission_fixture_with_oracle(ProofReadAuthority::Cpk, false)
    }

    fn cpk_3_replay_admission_fixture_with_authority(
        proof_read_authority: ProofReadAuthority,
    ) -> CpkReplayAdmissionFixture {
        cpk_3_replay_admission_fixture_with_oracle(proof_read_authority, true)
    }

    fn cpk_3_replay_admission_fixture_with_oracle(
        proof_read_authority: ProofReadAuthority,
        oracle_active: bool,
    ) -> CpkReplayAdmissionFixture {
        let mut machine = if oracle_active {
            cpk_migration_oracle_machine_with_authority(proof_read_authority)
        } else {
            cpk_machine_with_authority(proof_read_authority)
        };
        let origin = OriginId::unknown_internal();
        let source = TypeVar(0);
        let target = TypeVar(1);
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Var(target));
        machine.subtype(lower, upper, origin);
        let result = machine
            .constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("the replay fixture relation is canonical");
        let lower_record = machine.bounds.of(target).unwrap().lower_record_ids()[0];
        let upper_record = machine.bounds.of(source).unwrap().upper_record_ids()[0];
        let parent_record = machine
            .bounds
            .add_upper(
                TypeVar(2),
                upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;
        let registration = machine.original_upper_replay_claim(
            parent_record,
            ConstraintRecordId(10_000),
            UpperReplayClaimKind::Direct,
        );
        machine.proof_store.record_upper_claim(
            &machine.bounds.upper_replay_claims[registration.claim.0 as usize],
        );
        machine.apply_scheme_projection_mutation(registration.scheme_projection_mutation);
        CpkReplayAdmissionFixture {
            machine,
            result,
            carrier: BinaryReplayDerivation {
                pivot: source,
                lower: lower_record,
                upper: upper_record,
                rule: ReplayRule::LowerBoundAdded,
            },
            coverage_root: registration.claim,
            parent_owner: TypeVar(2),
            parent_record,
        }
    }

    fn add_same_root_replay_claim(
        fixture: &mut CpkReplayAdmissionFixture,
        owner: TypeVar,
        producer: ConstraintRecordId,
    ) -> UpperReplayClaimId {
        let endpoint = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .upper;
        let record = fixture
            .machine
            .bounds
            .add_upper(
                owner,
                endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let registration = fixture
            .machine
            .derived_upper_replay_claim(record, fixture.coverage_root, producer, |depth| {
                UpperReplayClaimLineage::ReplayConstraint {
                    parent_claim: fixture.coverage_root,
                    parent_side: ReplayClaimParentSide::Lower,
                    result: fixture.result,
                    replay: fixture.carrier,
                    depth,
                }
            });
        registration.claim
    }

    fn cpk_3_replay_fixture_with_oracle(cpk_proof_oracle_active: bool) -> ConstraintMachine {
        let mut machine = cpk_machine();
        machine.cpk_proof_oracle_active = cpk_proof_oracle_active;
        let origin = OriginId::unknown_internal();
        let a = machine.alloc_pos(Pos::Var(TypeVar(30)));
        let p1_upper = machine.alloc_neg(Neg::Var(TypeVar(31)));
        machine.subtype(a, p1_upper, origin);

        let p1 = machine.alloc_pos(Pos::Var(TypeVar(31)));
        let z_upper = machine.alloc_neg(Neg::Var(TypeVar(34)));
        machine.subtype(p1, z_upper, origin);

        let p2_upper = machine.alloc_neg(Neg::Var(TypeVar(32)));
        machine.subtype(a, p2_upper, origin);
        let p2 = machine.alloc_pos(Pos::Var(TypeVar(32)));
        machine.subtype(p2, z_upper, origin);

        let producer = machine
            .constraint_record_id(p1, ConstraintWeights::empty(), z_upper)
            .expect("reduction producer");
        let upper_record = machine
            .bounds
            .records
            .iter()
            .enumerate()
            .find_map(|(index, record)| {
                (record.direction == BoundDirection::Upper
                    && record.derivations.contains(&BoundDerivation::Constraint(producer)))
                .then_some(BoundRecordId(index as u32))
            })
            .expect("producer upper record");
        let row = machine.intern_row_derivation(
            RowDerivationRule::UnweightedReduction,
            vec![RowDerivationParent::Constraint(producer)],
            Vec::new(),
        );
        let (state, root_claim) = machine.register_unweighted_row_reduction_for_test(
            UnweightedRowReductionRecord {
                source: TypeVar(31),
                producer_constraint: Some(producer),
                original_items: Vec::new(),
                original_tail: z_upper,
                original_upper: z_upper,
                consumed_items: Vec::new(),
                remaining_items: Vec::new(),
                current_reduced_upper: UnweightedRowReductionMaterialization {
                    endpoint: z_upper,
                    record: upper_record,
                },
                processed_lower_records: FxHashSet::default(),
                provenance_head: row,
            },
        );
        assert_eq!(state, UnweightedRowReductionRecordId(0));
        let root_claim = root_claim.expect("reduction live coverage root");
        let route_lower = machine.alloc_pos(Pos::Var(TypeVar(35)));
        let route_upper = machine.alloc_neg(Neg::Var(TypeVar(36)));
        machine.enqueue_row_derived_subtype(
            route_lower,
            ConstraintWeights::empty(),
            route_upper,
            row,
        );
        machine.drain();
        let route = machine
            .constraint_record_id(route_lower, ConstraintWeights::empty(), route_upper)
            .expect("reduction route constraint");
        machine.register_reduction_route_claim_parent(route, row, root_claim);

        let replay = machine.replay_occurrences.occurrences[0].carrier;
        for (offset, lineage) in [
            UpperReplayClaimLineage::ReplayConstraint {
                parent_claim: root_claim,
                parent_side: ReplayClaimParentSide::Lower,
                result: route,
                replay,
                depth: 1,
            },
            UpperReplayClaimLineage::ReplayEvidence {
                parent_claim: root_claim,
                parent_side: ReplayClaimParentSide::Upper,
                replay,
                depth: 1,
            },
            UpperReplayClaimLineage::StructuralConstraint {
                parent_claim: root_claim,
                result: route,
                derivation: StructuralDerivation {
                    parent: producer,
                    rule: StructuralDerivationRule::FunctionReturn,
                },
                depth: 1,
            },
            UpperReplayClaimLineage::ReductionRouteConstraint {
                parent_claim: root_claim,
                result: route,
                derivation: row,
                depth: 1,
            },
        ]
        .into_iter()
        .enumerate()
        {
            let endpoint = machine.alloc_neg(Neg::Var(TypeVar(40 + offset as u32)));
            let insertion = machine.bounds.add_upper(
                TypeVar(50 + offset as u32),
                endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            );
            machine.derived_upper_replay_claim(
                insertion.id,
                root_claim,
                producer,
                |_| lineage,
            );
        }
        machine
    }

    fn cpk_3_replay_fixture() -> ConstraintMachine {
        cpk_3_replay_fixture_with_oracle(true)
    }

    fn assert_cpk_claim_payload_matches_flat(
        actual: &UpperClaimOccurrence,
        expected: &UpperReplayClaim,
    ) {
        assert_eq!(actual.claim, expected.id);
        assert_eq!(actual.coverage_root, expected.coverage_root);
        assert_eq!(actual.producer, expected.producer_constraint);
        assert_eq!(actual.current_record, expected.current_record);
        match (actual.kind, expected.kind) {
            (UpperClaimKind::Direct, UpperReplayClaimKind::Direct) => {}
            (
                UpperClaimKind::Reduced(actual_state),
                UpperReplayClaimKind::Reduced(expected_state),
            ) => assert_eq!(actual_state, expected_state),
            (actual, expected) => panic!("CPK claim kind {actual:?} != flat kind {expected:?}"),
        }
        match (actual.full_lineage, expected.lineage) {
            (UpperClaimLineage::Original, UpperReplayClaimLineage::Original) => {}
            (
                UpperClaimLineage::ReplayConstraint {
                    parent_claim: actual_parent,
                    parent_side: actual_side,
                    result: actual_result,
                    replay: actual_replay,
                    depth: actual_depth,
                },
                UpperReplayClaimLineage::ReplayConstraint {
                    parent_claim: expected_parent,
                    parent_side: expected_side,
                    result: expected_result,
                    replay: expected_replay,
                    depth: expected_depth,
                },
            ) => assert_eq!(
                (
                    actual_parent,
                    actual_side,
                    actual_result,
                    actual_replay,
                    actual_depth,
                ),
                (
                    expected_parent,
                    expected_side,
                    expected_result,
                    expected_replay,
                    expected_depth,
                ),
            ),
            (
                UpperClaimLineage::ReplayEvidence {
                    parent_claim: actual_parent,
                    parent_side: actual_side,
                    replay: actual_replay,
                    depth: actual_depth,
                },
                UpperReplayClaimLineage::ReplayEvidence {
                    parent_claim: expected_parent,
                    parent_side: expected_side,
                    replay: expected_replay,
                    depth: expected_depth,
                },
            ) => assert_eq!(
                (actual_parent, actual_side, actual_replay, actual_depth),
                (
                    expected_parent,
                    expected_side,
                    expected_replay,
                    expected_depth,
                ),
            ),
            (
                UpperClaimLineage::StructuralConstraint {
                    parent_claim: actual_parent,
                    result: actual_result,
                    derivation: actual_derivation,
                    depth: actual_depth,
                },
                UpperReplayClaimLineage::StructuralConstraint {
                    parent_claim: expected_parent,
                    result: expected_result,
                    derivation: expected_derivation,
                    depth: expected_depth,
                },
            ) => assert_eq!(
                (
                    actual_parent,
                    actual_result,
                    actual_derivation,
                    actual_depth,
                ),
                (
                    expected_parent,
                    expected_result,
                    expected_derivation,
                    expected_depth,
                ),
            ),
            (
                UpperClaimLineage::ReductionRouteConstraint {
                    parent_claim: actual_parent,
                    result: actual_result,
                    derivation: actual_derivation,
                    depth: actual_depth,
                },
                UpperReplayClaimLineage::ReductionRouteConstraint {
                    parent_claim: expected_parent,
                    result: expected_result,
                    derivation: expected_derivation,
                    depth: expected_depth,
                },
            ) => assert_eq!(
                (
                    actual_parent,
                    actual_result,
                    actual_derivation,
                    actual_depth,
                ),
                (
                    expected_parent,
                    expected_result,
                    expected_derivation,
                    expected_depth,
                ),
            ),
            (actual, expected) => {
                panic!("CPK claim lineage {actual:?} != flat lineage {expected:?}")
            }
        }
        assert_eq!(actual.lineage, projection_lineage(expected.lineage));
    }

    #[test]
    fn cpk_claim_payload_matches_flat_across_five_lineages_and_move() {
        let mut machine = cpk_3_replay_fixture_with_oracle(false);
        cpk_record_original_claim_with_kind(
            &mut machine,
            100,
            UpperReplayClaimKind::Reduced(UnweightedRowReductionRecordId(0)),
        );
        let cpk_claims = machine.proof_store.upper_claims.clone();
        assert_eq!(cpk_claims.len(), machine.bounds.upper_replay_claims.len());

        for actual in &cpk_claims {
            assert_eq!(
                actual.claim.0 as usize,
                machine.proof_store.upper_claim_index[&actual.claim]
            );
            assert_cpk_claim_payload_matches_flat(
                actual,
                &machine.bounds.upper_replay_claims[actual.claim.0 as usize],
            );
        }
        assert_eq!(
            machine
                .proof_store
                .upper_claims
                .iter()
                .map(|claim| claim.lineage)
                .collect::<FxHashSet<_>>(),
            FxHashSet::from_iter([
                ProjectionLineage::Original,
                ProjectionLineage::ReplayConstraint,
                ProjectionLineage::ReplayEvidence,
                ProjectionLineage::StructuralConstraint,
                ProjectionLineage::ReductionRouteConstraint,
            ]),
        );
        let kinds = machine
            .proof_store
            .upper_claims
            .iter()
            .map(|claim| claim.kind)
            .collect::<FxHashSet<_>>();
        assert!(kinds.contains(&UpperClaimKind::Direct));
        assert!(kinds.contains(&UpperClaimKind::Reduced(
            UnweightedRowReductionRecordId(0)
        )));
        assert_eq!(
            machine.proof_store.reduction_claim_by_state,
            machine.bounds.reduction_claim_by_state,
            "the CPK reduction-state index issues the claim mirrored by flat storage"
        );

        let moved_claim = cpk_claims
            .iter()
            .find_map(|claim| {
                (claim.lineage == ProjectionLineage::ReplayEvidence).then_some(claim.claim)
            })
            .expect("the five-lineage fixture contains one replay-evidence claim");
        let moved_index = machine.proof_store.upper_claim_index[&moved_claim];
        let before_move = machine.proof_store.upper_claims[moved_index].clone();
        let moved_endpoint = machine.alloc_neg(Neg::Con(
            vec!["cpk-claim-payload-move".into()],
            Vec::new(),
        ));
        let moved_record = machine
            .bounds
            .add_upper(
                TypeVar(95_000),
                moved_endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        machine.move_upper_replay_claim(moved_claim, moved_record);

        let expected_after_move =
            machine.bounds.upper_replay_claims[moved_claim.0 as usize].clone();
        let actual_after_move = &machine.proof_store.upper_claims[moved_index];
        assert_cpk_claim_payload_matches_flat(actual_after_move, &expected_after_move);
        assert_eq!(actual_after_move.current_record, moved_record);
        assert_eq!(actual_after_move.kind, before_move.kind);
        assert_eq!(actual_after_move.full_lineage, before_move.full_lineage);
        assert_eq!(
            machine.proof_store.claims_by_upper_record,
            machine
                .bounds
                .claims_by_upper_record
                .iter()
                .filter(|(_, claims)| !claims.is_empty())
                .map(|(record, claims)| (*record, claims.clone()))
                .collect(),
            "the flat record index mirrors every live CPK association while preserving its historical empty containers",
        );
        assert_eq!(
            machine.proof_store.derived_claim_by_record_and_root,
            machine.bounds.derived_claim_by_record_and_root,
            "the moved derived lineage remains byte-for-byte mirrored",
        );
    }

    #[test]
    fn cpk_original_claim_allocation_preflight_failure_is_atomic() {
        let mut machine = cpk_machine();
        let origin = OriginId::unknown_internal();
        let owner = TypeVar(96_000);
        let lower = machine.alloc_pos(Pos::Var(TypeVar(96_001)));
        let lower_record = machine
            .bounds
            .add_lower(
                owner,
                lower,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;
        let upper = machine.alloc_neg(Neg::Var(TypeVar(96_002)));
        let upper_record = machine
            .bounds
            .add_upper(
                owner,
                upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;
        let producer = ConstraintRecordId(96_003);
        machine
            .bounds
            .scheme_projection_lower_record_by_constraint
            .insert(producer, lower_record);
        let cpk_before = (
            machine.proof_store.upper_claims.len(),
            machine.proof_store.upper_claim_index.len(),
            machine.proof_store.original_claim_by_record_and_producer.len(),
            machine.proof_store.root_claim_by_producer_constraint.len(),
            machine.proof_store.claims_by_upper_record.len(),
            machine.proof_store.projection_supports.len(),
        );
        let flat_before = (
            machine.bounds.upper_replay_claims.len(),
            machine.bounds.original_claim_by_record_and_producer.len(),
            machine.bounds.root_claim_by_producer_constraint.len(),
            machine.bounds.claims_by_upper_record.len(),
            machine.bounds.scheme_projection_claims_by_lower_record.len(),
            machine.bounds.projection_proofs_by_lower_record.len(),
            machine.bounds.record_proof_clauses.len(),
        );
        let next_id = UpperReplayClaimId(cpk_before.0 as u32);

        machine.proof_store.fail_next_original_claim_reservation();
        assert!(matches!(
            machine.try_original_upper_replay_claim(
                upper_record,
                producer,
                UpperReplayClaimKind::Direct,
            ),
            Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::AdmitOriginalClaim,
            })
        ));
        assert_eq!(
            (
                machine.proof_store.upper_claims.len(),
                machine.proof_store.upper_claim_index.len(),
                machine.proof_store.original_claim_by_record_and_producer.len(),
                machine.proof_store.root_claim_by_producer_constraint.len(),
                machine.proof_store.claims_by_upper_record.len(),
                machine.proof_store.projection_supports.len(),
            ),
            cpk_before
        );
        assert_eq!(
            (
                machine.bounds.upper_replay_claims.len(),
                machine.bounds.original_claim_by_record_and_producer.len(),
                machine.bounds.root_claim_by_producer_constraint.len(),
                machine.bounds.claims_by_upper_record.len(),
                machine.bounds.scheme_projection_claims_by_lower_record.len(),
                machine.bounds.projection_proofs_by_lower_record.len(),
                machine.bounds.record_proof_clauses.len(),
            ),
            flat_before
        );

        let registration = machine
            .try_original_upper_replay_claim(
                upper_record,
                producer,
                UpperReplayClaimKind::Direct,
            )
            .expect("the failed preflight leaves its dense ID unconsumed");
        assert_eq!(registration.claim, next_id);
        assert_eq!(machine.proof_store.upper_claims[next_id.0 as usize].claim, next_id);
        assert_eq!(machine.bounds.upper_replay_claims[next_id.0 as usize].id, next_id);
        assert_eq!(
            machine.proof_store.original_claim(upper_record, producer),
            Some(next_id)
        );
        assert_eq!(
            machine.proof_store.root_claim_by_producer_constraint[&producer],
            next_id
        );
        assert_eq!(
            machine.bounds.original_claim_by_record_and_producer[&(upper_record, producer)],
            next_id
        );
    }

    #[test]
    fn cpk_derived_claim_allocation_preserves_root_and_cycle_coalescing() {
        let mut machine = cpk_machine();
        let origin = OriginId::unknown_internal();
        let endpoint = machine.alloc_neg(Neg::Var(TypeVar(96_100)));
        let add_record = |machine: &mut ConstraintMachine, owner| {
            machine
                .bounds
                .add_upper(
                    owner,
                    endpoint,
                    ConstraintWeights::empty(),
                    BoundDerivation::Origin(origin),
                )
                .id
        };
        let root_record = add_record(&mut machine, TypeVar(96_101));
        let producer = ConstraintRecordId(96_102);
        let root = machine
            .original_upper_replay_claim(root_record, producer, UpperReplayClaimKind::Direct)
            .claim;
        let replay = BinaryReplayDerivation {
            pivot: TypeVar(96_103),
            lower: root_record,
            upper: root_record,
            rule: ReplayRule::UpperBoundAdded,
        };
        let first_record = add_record(&mut machine, TypeVar(96_104));
        let first = machine
            .derived_upper_replay_claim(first_record, root, producer, |depth| {
                UpperReplayClaimLineage::ReplayConstraint {
                    parent_claim: root,
                    parent_side: ReplayClaimParentSide::Lower,
                    result: producer,
                    replay,
                    depth,
                }
            })
            .claim;
        let second_record = add_record(&mut machine, TypeVar(96_105));
        let second = machine
            .derived_upper_replay_claim(second_record, first, producer, |depth| {
                UpperReplayClaimLineage::ReplayEvidence {
                    parent_claim: first,
                    parent_side: ReplayClaimParentSide::Upper,
                    replay,
                    depth,
                }
            })
            .claim;
        let duplicate = machine
            .derived_upper_replay_claim(second_record, root, producer, |depth| {
                UpperReplayClaimLineage::ReplayEvidence {
                    parent_claim: root,
                    parent_side: ReplayClaimParentSide::Upper,
                    replay,
                    depth,
                }
            })
            .claim;
        let cycle = machine
            .derived_upper_replay_claim(root_record, second, producer, |depth| {
                UpperReplayClaimLineage::ReplayConstraint {
                    parent_claim: second,
                    parent_side: ReplayClaimParentSide::Lower,
                    result: producer,
                    replay,
                    depth,
                }
            })
            .claim;

        assert_eq!(duplicate, second);
        assert_eq!(cycle, root);
        assert_eq!(machine.proof_store.replay_claim_cycle_coalesces, 2);
        assert_eq!(
            machine.proof_store.replay_claim_cycle_coalesces,
            machine.bounds.replay_claim_cycle_coalesces
        );
        assert_eq!(
            machine.proof_store.derived_claim_by_record_and_root,
            machine.bounds.derived_claim_by_record_and_root
        );
        assert_eq!(machine.proof_store.upper_claims[first.0 as usize].coverage_root, root);
        assert_eq!(machine.proof_store.upper_claims[second.0 as usize].coverage_root, root);
        assert_eq!(machine.proof_store.upper_claims[first.0 as usize].full_lineage.depth(), 1);
        assert_eq!(machine.proof_store.upper_claims[second.0 as usize].full_lineage.depth(), 2);
        for claim in [root, first, second] {
            assert_cpk_claim_payload_matches_flat(
                &machine.proof_store.upper_claims[claim.0 as usize],
                &machine.bounds.upper_replay_claims[claim.0 as usize],
            );
        }
    }

    #[test]
    fn cpk_derived_claim_allocation_preflight_failure_is_atomic() {
        let mut machine = cpk_machine();
        let origin = OriginId::unknown_internal();
        let endpoint = machine.alloc_neg(Neg::Var(TypeVar(96_200)));
        let root_record = machine
            .bounds
            .add_upper(
                TypeVar(96_201),
                endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;
        let producer = ConstraintRecordId(96_202);
        let root = machine
            .original_upper_replay_claim(root_record, producer, UpperReplayClaimKind::Direct)
            .claim;
        let derived_record = machine
            .bounds
            .add_upper(
                TypeVar(96_203),
                endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;
        let before = (
            machine.proof_store.upper_claims.len(),
            machine.proof_store.derived_claim_by_record_and_root.clone(),
            machine.proof_store.claims_by_upper_record.clone(),
            machine.proof_store.reduction_claim_by_state.clone(),
            machine.proof_store.replay_claim_cycle_coalesces,
            machine.bounds.upper_replay_claims.len(),
            machine.bounds.derived_claim_by_record_and_root.clone(),
            machine.bounds.claims_by_upper_record.clone(),
            machine.bounds.reduction_claim_by_state.clone(),
            machine.bounds.replay_claim_cycle_coalesces,
        );
        let next = UpperReplayClaimId(before.0 as u32);
        machine.proof_store.fail_next_derived_claim_reservation();
        let lineage = |depth| UpperReplayClaimLineage::StructuralConstraint {
            parent_claim: root,
            result: producer,
            derivation: StructuralDerivation {
                parent: producer,
                rule: StructuralDerivationRule::FunctionReturn,
            },
            depth,
        };
        assert!(matches!(
            machine.try_derived_upper_replay_claim(derived_record, root, producer, lineage),
            Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::AdmitDerivedClaim,
            })
        ));
        assert_eq!(
            (
                machine.proof_store.upper_claims.len(),
                machine.proof_store.derived_claim_by_record_and_root.clone(),
                machine.proof_store.claims_by_upper_record.clone(),
                machine.proof_store.reduction_claim_by_state.clone(),
                machine.proof_store.replay_claim_cycle_coalesces,
                machine.bounds.upper_replay_claims.len(),
                machine.bounds.derived_claim_by_record_and_root.clone(),
                machine.bounds.claims_by_upper_record.clone(),
                machine.bounds.reduction_claim_by_state.clone(),
                machine.bounds.replay_claim_cycle_coalesces,
            ),
            before
        );
        let registration = machine
            .try_derived_upper_replay_claim(derived_record, root, producer, lineage)
            .expect("failed preflight leaves the derived dense ID unconsumed");
        assert_eq!(registration.claim, next);
        assert_eq!(
            machine.proof_store.derived_claim_by_record_and_root[&(derived_record, root)],
            next
        );
        assert_eq!(
            machine.bounds.derived_claim_by_record_and_root[&(derived_record, root)],
            next
        );
    }

    #[test]
    fn cpk_claim_move_preflight_failure_is_atomic() {
        let mut machine = cpk_machine();
        let (old_record, claim) = cpk_7_record_original_claim(&mut machine, 960);
        let endpoint = machine.alloc_neg(Neg::Var(TypeVar(96_961)));
        let new_record = machine
            .bounds
            .add_upper(
                TypeVar(96_962),
                endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let before = (
            machine.proof_store.upper_claims.clone(),
            machine.proof_store.original_claim_by_record_and_producer.clone(),
            machine.proof_store.derived_claim_by_record_and_root.clone(),
            machine.proof_store.claims_by_upper_record.clone(),
            machine.bounds.upper_replay_claims.clone(),
            machine.bounds.original_claim_by_record_and_producer.clone(),
            machine.bounds.derived_claim_by_record_and_root.clone(),
            machine.bounds.claims_by_upper_record.clone(),
        );

        machine.proof_store.fail_next_claim_move_reservation();
        assert!(matches!(
            machine.try_move_upper_replay_claim(claim, new_record),
            Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            })
        ));
        assert_eq!(
            (
                machine.proof_store.upper_claims.clone(),
                machine.proof_store.original_claim_by_record_and_producer.clone(),
                machine.proof_store.derived_claim_by_record_and_root.clone(),
                machine.proof_store.claims_by_upper_record.clone(),
                machine.bounds.upper_replay_claims.clone(),
                machine.bounds.original_claim_by_record_and_producer.clone(),
                machine.bounds.derived_claim_by_record_and_root.clone(),
                machine.bounds.claims_by_upper_record.clone(),
            ),
            before,
            "a failed move preflight commits neither CPK state nor flat mirror state",
        );
        assert_eq!(
            machine.proof_store.upper_claims[claim.0 as usize].current_record,
            old_record,
        );

        machine
            .try_move_upper_replay_claim(claim, new_record)
            .expect("the failed preflight leaves the same claim movable");
        assert_eq!(
            machine.proof_store.upper_claims[claim.0 as usize].current_record,
            new_record,
        );
        assert_eq!(
            machine.bounds.upper_replay_claims[claim.0 as usize].current_record,
            new_record,
        );
    }

    #[test]
    fn cpk_claim_move_updates_record_coverage_and_preserves_root_liveness() {
        let mut machine = cpk_machine();
        let (shared_record, first) = cpk_7_record_original_claim(&mut machine, 970);
        let (second_record, second) = cpk_7_record_original_claim(&mut machine, 971);
        machine.move_upper_replay_claim(second, shared_record);
        assert_eq!(
            machine.proof_store.claims_by_upper_record[&shared_record],
            vec![first, second],
            "two roots can share one current record in canonical root order",
        );

        let first_state = UnweightedRowReductionRecordId(96_972);
        let second_state = UnweightedRowReductionRecordId(96_973);
        assert!(machine.insert_scheme_projection_live_coverage_state(first, first_state));
        assert!(machine.insert_scheme_projection_live_coverage_state(second, second_state));
        let third_endpoint = machine.alloc_neg(Neg::Var(TypeVar(96_975)));
        let third_record = machine
            .bounds
            .add_upper(
                TypeVar(96_974),
                third_endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let fourth_endpoint = machine.alloc_neg(Neg::Var(TypeVar(96_977)));
        let fourth_record = machine
            .bounds
            .add_upper(
                TypeVar(96_976),
                fourth_endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;

        machine.move_upper_replay_claim(first, third_record);
        assert_eq!(machine.proof_store.claims_by_upper_record[&shared_record], vec![second]);
        assert_eq!(machine.proof_store.claims_by_upper_record[&third_record], vec![first]);
        machine.move_upper_replay_claim(first, fourth_record);
        assert!(!machine.proof_store.claims_by_upper_record.contains_key(&third_record));
        assert_eq!(machine.proof_store.claims_by_upper_record[&fourth_record], vec![first]);
        assert_eq!(
            machine.proof_store.claims_by_upper_record,
            machine
                .bounds
                .claims_by_upper_record
                .iter()
                .filter(|(_, claims)| !claims.is_empty())
                .map(|(record, claims)| (*record, claims.clone()))
                .collect(),
            "flat current-record coverage mirrors every live CPK association after repeated moves",
        );
        assert!(machine.proof_store.live_coverage.contains(&(first, first_state)));
        assert!(machine.proof_store.live_coverage.contains(&(second, second_state)));
        assert_eq!(
            machine.bounds.live_coverage_by_root[&first],
            vec![first_state],
            "root liveness follows stable claim identity and is not reassigned by a move",
        );
        assert_eq!(machine.bounds.live_coverage_by_root[&second], vec![second_state]);
        assert!(!machine.proof_store.claims_by_upper_record.contains_key(&second_record));
    }

    #[test]
    fn cpk_qualified_parent_admission_is_atomic_and_canonically_indexed() {
        let mut machine = cpk_machine();
        let (lower_record, first) = cpk_7_record_original_claim(&mut machine, 980);
        let (upper_record, second) = cpk_7_record_original_claim(&mut machine, 981);
        let (_, third) = cpk_7_record_original_claim(&mut machine, 982);
        let result = ConstraintRecordId(96_983);
        let lower_replay = BinaryReplayDerivation {
            pivot: TypeVar(96_984),
            lower: lower_record,
            upper: upper_record,
            rule: ReplayRule::LowerBoundAdded,
        };
        let upper_replay = BinaryReplayDerivation {
            rule: ReplayRule::UpperBoundAdded,
            ..lower_replay
        };
        let structural = StructuralDerivation {
            parent: ConstraintRecordId(96_985),
            rule: StructuralDerivationRule::FunctionReturn,
        };
        let parents = [
            ClaimQualifiedParent::ReductionRouteConstraint {
                parent_claim: third,
                derivation: RowDerivationId(96_986),
            },
            ClaimQualifiedParent::ReplayConstraint {
                parent_claim: first,
                parent_side: ReplayClaimParentSide::Upper,
                replay: upper_replay,
            },
            ClaimQualifiedParent::StructuralConstraint {
                parent_claim: second,
                derivation: structural,
            },
            ClaimQualifiedParent::ReplayConstraint {
                parent_claim: first,
                parent_side: ReplayClaimParentSide::Lower,
                replay: lower_replay,
            },
            // One event-local exact duplicate must not allocate or reach either mirror.
            ClaimQualifiedParent::ReplayConstraint {
                parent_claim: first,
                parent_side: ReplayClaimParentSide::Lower,
                replay: lower_replay,
            },
        ];
        let cpk_before = (
            machine.proof_store.qualified_parent_keys.clone(),
            machine.proof_store.qualified_parents_by_result.clone(),
        );
        let flat_before = (
            machine.bounds.claim_parents_by_constraint.clone(),
            machine.bounds.qualified_carrier_index.clone(),
            machine.bounds.replay_claim_parent_keys.clone(),
            machine.bounds.structural_claim_parent_keys.clone(),
        );

        machine
            .proof_store
            .fail_next_qualified_parent_reservation();
        machine.admit_claim_qualified_parents(result, &parents);
        assert_eq!(
            (
                machine.proof_store.qualified_parent_keys.clone(),
                machine.proof_store.qualified_parents_by_result.clone(),
            ),
            cpk_before,
            "a failed CPK preflight commits no key or result-local order state",
        );
        assert_eq!(
            (
                machine.bounds.claim_parents_by_constraint.clone(),
                machine.bounds.qualified_carrier_index.clone(),
                machine.bounds.replay_claim_parent_keys.clone(),
                machine.bounds.structural_claim_parent_keys.clone(),
            ),
            flat_before,
            "the flat mirror is untouched until the CPK transaction commits",
        );

        machine.admit_claim_qualified_parents(result, &parents);
        let canonical = machine.proof_store.qualified_parents_for_result(result);
        assert_eq!(canonical.len(), 4);
        assert!(canonical
            .windows(2)
            .all(|pair| qualified_parent_entry_cmp(&pair[0], &pair[1]).is_lt()));
        assert_eq!(
            canonical
                .iter()
                .map(|entry| entry.coverage_root)
                .collect::<Vec<_>>(),
            vec![first, first, second, third],
            "claimed parents remain in canonical coverage-root order",
        );
        assert_eq!(
            machine.bounds.claim_parents_by_constraint[&result]
                .iter()
                .copied()
                .collect::<FxHashSet<_>>(),
            canonical
                .iter()
                .map(|entry| entry.parent)
                .collect::<FxHashSet<_>>(),
            "flat receives exactly the event-local CPK decision",
        );
    }

    #[test]
    fn cpk_projection_target_and_dependency_admission_is_atomic_and_target_late() {
        let mut store = ProofOccurrenceStore::default();
        let constraint = ConstraintRecordId(96_990);
        let lower_record = BoundRecordId(96_991);
        let dependent = BoundRecordId(96_992);
        let edge = (ProofPremise::Constraint(constraint), dependent);
        let before = (
            store.projection_lower_record_by_constraint.clone(),
            store.projection_lower_record_by_replay.clone(),
            store.dependent_records_by_premise.clone(),
        );

        store.fail_next_projection_index_reservation();
        assert!(matches!(
            store.try_prepare_projection_index_admission(
                Some((ProjectionTarget::Constraint(constraint), lower_record)),
                &[edge],
            ),
            Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            })
        ));
        assert_eq!(
            (
                store.projection_lower_record_by_constraint.clone(),
                store.projection_lower_record_by_replay.clone(),
                store.dependent_records_by_premise.clone(),
            ),
            before,
            "failed preflight leaves every CPK projection index unchanged",
        );

        let mut dependency = store
            .try_prepare_projection_index_admission(None, &[edge])
            .unwrap();
        store.commit_projection_index_admission(&mut dependency);
        let mut target = store
            .try_prepare_projection_index_admission(
                Some((ProjectionTarget::Constraint(constraint), lower_record)),
                &[],
            )
            .unwrap();
        store.commit_projection_index_admission(&mut target);
        assert_eq!(
            store.projection_lower_record_for_constraint(constraint),
            Some(lower_record),
        );
        assert_eq!(
            store.dependent_records(ProofPremise::Constraint(constraint)),
            Some(&FxHashSet::from_iter([dependent])),
        );
        assert_eq!(
            store.dependent_records(ProofPremise::Record(lower_record)),
            Some(&FxHashSet::from_iter([dependent])),
            "a late target atomically publishes the derived Record-premise edge",
        );
    }

    #[test]
    fn cpk_3_exact_replay_and_first_witness_match_factored_oracle() {
        let inactive = with_semantic_execution_snapshot_capture_for_new_machines(|| {
            cpk_3_replay_fixture_with_oracle(false)
        });
        let active = with_semantic_execution_snapshot_capture_for_new_machines(|| {
            cpk_3_replay_fixture_with_oracle(false)
        });
        let snapshot = active.proof_store.clone();
        let carrier = |pivot, lower, upper| BinaryReplayDerivation {
            pivot: TypeVar(pivot),
            lower: BoundRecordId(lower),
            upper: BoundRecordId(upper),
            rule: ReplayRule::UpperBoundAdded,
        };
        let parent = |side, root, claim| ReplayProofParent {
            side,
            coverage_root: UpperReplayClaimId(root),
            representative_claim: UpperReplayClaimId(claim),
            lineage: ProjectionLineage::Original,
        };
        let first_carrier = carrier(31, 0, 3);
        let second_carrier = carrier(32, 6, 9);
        assert_eq!(
            snapshot.replay_finite_map,
            vec![
                ReplayProofOccurrence {
                    result: ConstraintRecordId(2),
                    carrier: first_carrier,
                    lower_parents: vec![parent(ReplayClaimParentSide::Lower, 0, 0)],
                    upper_parents: vec![parent(ReplayClaimParentSide::Upper, 1, 1)],
                    first_event: 0,
                },
                ReplayProofOccurrence {
                    result: ConstraintRecordId(2),
                    carrier: second_carrier,
                    lower_parents: vec![parent(ReplayClaimParentSide::Lower, 4, 4)],
                    upper_parents: vec![parent(ReplayClaimParentSide::Upper, 5, 5)],
                    first_event: 1,
                },
            ],
        );
        assert_eq!(
            snapshot.first_replay_witnesses,
            FxHashMap::from_iter([
                (
                    (ConstraintRecordId(2), UpperReplayClaimId(0)),
                    ReplayFirstWitness {
                        carrier: first_carrier,
                        side: ReplayClaimParentSide::Lower,
                        representative_claim: UpperReplayClaimId(0),
                    },
                ),
                (
                    (ConstraintRecordId(2), UpperReplayClaimId(1)),
                    ReplayFirstWitness {
                        carrier: first_carrier,
                        side: ReplayClaimParentSide::Upper,
                        representative_claim: UpperReplayClaimId(1),
                    },
                ),
                (
                    (ConstraintRecordId(2), UpperReplayClaimId(4)),
                    ReplayFirstWitness {
                        carrier: second_carrier,
                        side: ReplayClaimParentSide::Lower,
                        representative_claim: UpperReplayClaimId(4),
                    },
                ),
                (
                    (ConstraintRecordId(2), UpperReplayClaimId(5)),
                    ReplayFirstWitness {
                        carrier: second_carrier,
                        side: ReplayClaimParentSide::Upper,
                        representative_claim: UpperReplayClaimId(5),
                    },
                ),
            ]),
        );
        let claims = snapshot
            .upper_claims
            .iter()
            .map(|claim| {
                (
                    claim.claim,
                    claim.coverage_root,
                    claim.lineage,
                    claim.producer,
                    claim.current_record,
                )
            })
            .collect::<Vec<_>>();
        let claim = |id, root, lineage, producer, record| {
            (
                UpperReplayClaimId(id),
                UpperReplayClaimId(root),
                lineage,
                ConstraintRecordId(producer),
                BoundRecordId(record),
            )
        };
        assert_eq!(
            claims,
            vec![
                claim(0, 0, ProjectionLineage::Original, 0, 1),
                claim(1, 1, ProjectionLineage::Original, 1, 3),
                claim(2, 0, ProjectionLineage::ReplayConstraint, 2, 5),
                claim(3, 1, ProjectionLineage::ReplayConstraint, 2, 5),
                claim(4, 4, ProjectionLineage::Original, 3, 7),
                claim(5, 5, ProjectionLineage::Original, 4, 9),
                claim(6, 4, ProjectionLineage::ReplayConstraint, 2, 5),
                claim(7, 5, ProjectionLineage::ReplayConstraint, 2, 5),
                claim(8, 8, ProjectionLineage::Original, 5, 11),
                claim(9, 1, ProjectionLineage::ReductionRouteConstraint, 5, 11),
                claim(10, 1, ProjectionLineage::ReplayConstraint, 1, 12),
                claim(11, 1, ProjectionLineage::ReplayEvidence, 1, 13),
                claim(12, 1, ProjectionLineage::StructuralConstraint, 1, 14),
                claim(13, 1, ProjectionLineage::ReductionRouteConstraint, 1, 15),
            ],
        );
        assert_eq!(
            snapshot.row_reductions,
            vec![RowReductionOccurrence {
                state: UnweightedRowReductionRecordId(0),
                root_claim: Some(UpperReplayClaimId(1)),
                provenance: RowDerivationId(0),
                current_record: BoundRecordId(3),
            }],
        );
        assert_eq!(
            snapshot.live_coverage,
            FxHashSet::from_iter([(
                UpperReplayClaimId(1),
                UnweightedRowReductionRecordId(0),
            )]),
        );
        assert_eq!(
            snapshot.replay_admissions,
            vec![
                ReplayAdmissionEvent {
                    result: Some(ConstraintRecordId(2)),
                    carrier: first_carrier,
                    disposition: ReplayAdmissionDisposition::NewSemantic,
                },
                ReplayAdmissionEvent {
                    result: Some(ConstraintRecordId(2)),
                    carrier: second_carrier,
                    disposition: ReplayAdmissionDisposition::CanonicalDuplicate,
                },
            ],
        );
        assert!(snapshot.replay_coverage_connected);
        assert!(snapshot.occurrences.iter().any(|occurrence| {
            matches!(occurrence.cause, ProofCause::ReductionRoute { .. })
        }));
        let lineages = snapshot
            .upper_claims
            .iter()
            .map(|claim| claim.lineage)
            .collect::<FxHashSet<_>>();
        assert_eq!(
            lineages,
            FxHashSet::from_iter([
                ProjectionLineage::Original,
                ProjectionLineage::ReplayConstraint,
                ProjectionLineage::ReplayEvidence,
                ProjectionLineage::StructuralConstraint,
                ProjectionLineage::ReductionRouteConstraint,
            ]),
        );
        let scc = crate::scc::SccMachine::new();
        let inactive_semantic = inactive.semantic_execution_snapshot(
            SccExecutionSnapshot::new(scc.stats(), Vec::new()),
            SemanticOutputSnapshot::default(),
        );
        let scc = crate::scc::SccMachine::new();
        let active_semantic = active.semantic_execution_snapshot(
            SccExecutionSnapshot::new(scc.stats(), Vec::new()),
            SemanticOutputSnapshot::default(),
        );
        assert_eq!(active_semantic, inactive_semantic);
    }

    struct Cpk7ClaimMoveFixture {
        machine: ConstraintMachine,
        source_neg: NegId,
        late_family: PosId,
        original_upper: NegId,
        state: UnweightedRowReductionRecordId,
        claim: UpperReplayClaimId,
        record_before_move: BoundRecordId,
    }

    fn cpk_7_two_stage_row_claim_move_fixture() -> Cpk7ClaimMoveFixture {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(72_000);
        let residual = TypeVar(72_001);
        let initial_family =
            machine.alloc_pos(Pos::Con(vec!["cpk-7-family-f".into()], Vec::new()));
        let late_family =
            machine.alloc_pos(Pos::Con(vec!["cpk-7-family-g".into()], Vec::new()));
        let first_upper =
            machine.alloc_neg(Neg::Con(vec!["cpk-7-family-f".into()], Vec::new()));
        let second_upper =
            machine.alloc_neg(Neg::Con(vec!["cpk-7-family-g".into()], Vec::new()));
        let source_neg = machine.alloc_neg(Neg::Var(source));
        let source_pos = machine.alloc_pos(Pos::Var(source));
        let tail = machine.alloc_neg(Neg::Var(residual));
        let original_upper = machine.alloc_neg(Neg::Row(vec![first_upper, second_upper], tail));
        let origin = OriginId::unknown_internal();

        machine.subtype(initial_family, source_neg, origin);
        machine.subtype(source_pos, original_upper, origin);

        let states = machine
            .unweighted_row_reductions_by_source
            .get(&source)
            .expect("the first row stage creates a source-local reduction state");
        assert_eq!(states.len(), 1);
        let state = states[0];
        let claim = machine.bounds.reduction_claim_by_state[&state];
        let record_before_move =
            machine.bounds.upper_replay_claims[claim.0 as usize].current_record;

        Cpk7ClaimMoveFixture {
            machine,
            source_neg,
            late_family,
            original_upper,
            state,
            claim,
            record_before_move,
        }
    }

    fn cpk_7_run_second_row_stage(
        fixture: &mut Cpk7ClaimMoveFixture,
    ) -> PreparedReplayRoute {
        fixture.machine.subtype(
            fixture.late_family,
            fixture.source_neg,
            OriginId::unknown_internal(),
        );
        let lower_record = fixture
            .machine
            .bounds
            .records
            .iter()
            .enumerate()
            .find_map(|(index, record)| {
                (record.owner() == TypeVar(72_000)
                    && record.endpoint() == BoundEndpoint::Lower(fixture.late_family))
                .then_some(BoundRecordId(index as u32))
            })
            .expect("the second row stage must retain its lower record");
        let upper_record = fixture.machine.bounds.upper_replay_claims
            [fixture.claim.0 as usize]
            .current_record;
        let route = IncrementalRouteKey {
            upper: fixture.original_upper,
            upper_record,
            provenance: fixture.machine.unweighted_row_reduction_records
                [fixture.state.0 as usize]
                .provenance_head,
            claim: Some(fixture.claim),
        };
        fixture
            .machine
            .proof_store
            .prepare_replay_route(&fixture.machine, lower_record, upper_record, &[route])
            .expect("the moved claim must produce one direct CPK route")
    }

    fn assert_cpk_7_decoupled_claim_move_route(
        fixture: &Cpk7ClaimMoveFixture,
        prepared: &PreparedReplayRoute,
    ) {
        let incremental = prepared
            .proof_event
            .incremental_replays
            .iter()
            .find(|incremental| incremental.route.upper == fixture.original_upper)
            .expect("the original row endpoint remains residual incremental work");
        assert_eq!(incremental.route.claim, Some(fixture.claim));
        let current_endpoint = match fixture
            .machine
            .bounds
            .record(incremental.route.upper_record)
            .expect("the moved claim materialization record remains active")
            .endpoint()
        {
            BoundEndpoint::Upper(endpoint) => endpoint,
            BoundEndpoint::Lower(_) => panic!("claim move target must be an upper record"),
        };
        assert_ne!(incremental.route.upper, current_endpoint);
        assert_eq!(
            fixture.machine.bounds.upper_replay_claims[fixture.claim.0 as usize].current_record,
            incremental.route.upper_record,
        );
        assert_ne!(fixture.record_before_move, incremental.route.upper_record);
        let result = fixture
            .machine
            .constraint_record_id(
                fixture.late_family,
                ConstraintWeights::empty(),
                incremental.route.upper,
            )
            .expect("the residual semantic action is admitted at the original endpoint");
        assert!(fixture.machine.constraint_records[result.0 as usize]
            .row_derivations
            .contains(&incremental.route.provenance));
    }

    #[test]
    fn cpk_7_shadow_real_row_route_is_incremental_only_end_to_end() {
        let mut machine = cpk_3_replay_fixture_with_oracle(false);
        let lower = machine.alloc_pos(Pos::Con(
            vec!["cpk-7-real-incremental".into()],
            Vec::new(),
        ));
        machine.add_lower_bound(
            TypeVar(31),
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );
        let lower_record = machine
            .bounds
            .records
            .iter()
            .enumerate()
            .find_map(|(index, record)| {
                (record.owner() == TypeVar(31)
                    && record.endpoint() == BoundEndpoint::Lower(lower))
                .then_some(BoundRecordId(index as u32))
            })
            .expect("the real incremental route must retain its lower record");
        let state = UnweightedRowReductionRecordId(0);
        let reduction = &machine.unweighted_row_reduction_records[state.0 as usize];
        let route = IncrementalRouteKey {
            upper: reduction.original_upper,
            upper_record: reduction.current_reduced_upper.record,
            provenance: reduction.provenance_head,
            claim: Some(machine.bounds.reduction_claim_by_state[&state]),
        };
        let prepared = machine
            .proof_store
            .prepare_replay_route(&machine, lower_record, route.upper_record, &[route])
            .expect("the real row-reduction route must validate directly in CPK");
        assert_eq!(prepared.routing, ReplayRouting::IncrementalOnly);
        assert!(prepared.proof_event.pair_replay.is_none());
        assert_eq!(
            prepared.proof_event.incremental_replays.len(),
            1,
        );
        assert_eq!(prepared.proof_event.incremental_replays[0].route, route);
        assert_eq!(
            prepared.proof_event.incremental_replays[0]
                .parents
                .upper
                .as_slice()[0]
                .representative_claim,
            route.claim.expect("the real route remains claim-qualified"),
        );
    }

    #[test]
    fn cpk_7_shadow_distinct_incremental_arrivals_preserve_first_seen_order() {
        let run = |order: [usize; 2]| {
            let mut machine = ConstraintMachine::new();
            let source = TypeVar(72_100);
            let current_upper = machine.alloc_neg(Neg::Con(
                vec!["cpk-7-incremental-current".into()],
                Vec::new(),
            ));
            let producers = [0, 1]
                .map(|index| cpk_7_admit_inert_constraint(&mut machine, 100 + index, "route"));
            let roots = producers.map(|producer| {
                machine.add_upper_bound(
                    source,
                    current_upper,
                    ConstraintWeights::empty(),
                    BoundDerivation::Constraint(producer),
                );
                machine.bounds.root_claim_by_producer_constraint[&producer]
            });
            let upper_record = machine
                .bounds
                .records
                .iter()
                .enumerate()
                .find_map(|(index, record)| {
                    (record.owner() == source
                        && record.endpoint() == BoundEndpoint::Upper(current_upper))
                    .then_some(BoundRecordId(index as u32))
                })
                .expect("the two claims share one upper record");
            let route_uppers = [0, 1].map(|index| {
                machine.alloc_neg(Neg::Con(
                    vec!["cpk-7-incremental-original".into(), index.to_string()],
                    Vec::new(),
                ))
            });
            let matched_upper = machine.alloc_neg(Neg::Con(
                vec!["cpk-7-incremental-matched".into()],
                Vec::new(),
            ));
            let provenance = producers.map(|producer| {
                machine.intern_row_derivation(
                    RowDerivationRule::UnweightedReduction,
                    vec![RowDerivationParent::Constraint(producer)],
                    Vec::new(),
                )
            });
            let mut states = [UnweightedRowReductionRecordId(u32::MAX); 2];
            for index in order {
                let (state, registered_root) = machine.register_unweighted_row_reduction_for_test(
                    UnweightedRowReductionRecord {
                        source,
                        producer_constraint: Some(producers[index]),
                        original_items: vec![matched_upper],
                        original_tail: current_upper,
                        original_upper: route_uppers[index],
                        consumed_items: Vec::new(),
                        remaining_items: vec![matched_upper],
                        current_reduced_upper: UnweightedRowReductionMaterialization {
                            endpoint: current_upper,
                            record: upper_record,
                        },
                        processed_lower_records: FxHashSet::default(),
                        provenance_head: provenance[index],
                    },
                );
                states[index] = state;
                assert_eq!(registered_root, Some(roots[index]));
            }

            let lower = machine.alloc_pos(Pos::Con(
                vec!["cpk-7-incremental-matched".into()],
                Vec::new(),
            ));
            machine.add_lower_bound(
                source,
                lower,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            );
            let lower_record = machine
                .bounds
                .records
                .iter()
                .enumerate()
                .find_map(|(index, record)| {
                    (record.owner() == source
                        && record.endpoint() == BoundEndpoint::Lower(lower))
                    .then_some(BoundRecordId(index as u32))
                })
                .expect("the direct incremental route must retain its lower record");
            let routes = order.map(|index| IncrementalRouteKey {
                upper: route_uppers[index],
                upper_record,
                provenance: machine.unweighted_row_reduction_records[states[index].0 as usize]
                    .provenance_head,
                claim: Some(roots[index]),
            });
            let prepared = machine
                .proof_store
                .prepare_replay_route(&machine, lower_record, upper_record, &routes)
                .expect("the direct CPK route retains both incremental actions");
            assert_eq!(prepared.routing, ReplayRouting::IncrementalOnly);
            assert!(prepared.proof_event.pair_replay.is_none());
            let incremental = &prepared.proof_event.incremental_replays;
            assert_eq!(incremental.len(), 2);
            assert_eq!(
                incremental
                    .iter()
                    .map(|replay| replay.route.upper)
                    .collect::<Vec<_>>(),
                order.map(|index| route_uppers[index]),
                "distinct semantic actions retain their input arrival order",
            );
            assert_eq!(
                incremental
                    .iter()
                    .map(|replay| replay.route.claim)
                    .collect::<Vec<_>>(),
                order.map(|index| Some(roots[index])),
            );
            for replay in incremental {
                assert!(replay.parents.lower.as_slice().is_empty());
                let parent = replay
                    .parents
                    .upper
                    .as_slice()
                    .first()
                    .copied()
                    .expect("each covered route retains its exact upper claim parent");
                assert_eq!(Some(parent.representative_claim), replay.route.claim);
                assert_eq!(parent.coverage_root, parent.representative_claim);
                assert_eq!(parent.lineage, ProjectionLineage::Original);
            }
            let normalized = route_uppers.map(|upper| {
                let replay = incremental
                    .iter()
                    .find(|replay| replay.route.upper == upper)
                    .expect("both semantic route identities survive every permutation");
                (upper, replay.route.claim)
            });
            (prepared, normalized)
        };

        let (first, first_normalized) = run([0, 1]);
        let (second, second_normalized) = run([1, 0]);
        assert_eq!(first.routing, second.routing);
        assert_eq!(first_normalized, second_normalized);
        assert_ne!(
            first.proof_event.incremental_replays,
            second.proof_event.incremental_replays,
            "the contract preserves semantic input order instead of sorting distinct routes",
        );
    }

    #[test]
    fn cpk_7_shadow_duplicate_decoupled_incremental_routes_keep_first_seen_action() {
        let run = |order: [usize; 2]| {
            let mut machine = ConstraintMachine::new();
            let source = TypeVar(72_200);
            let current_upper = machine.alloc_neg(Neg::Con(
                vec!["cpk-7-dedup-current".into()],
                Vec::new(),
            ));
            let original_upper = machine.alloc_neg(Neg::Con(
                vec!["cpk-7-dedup-original".into()],
                Vec::new(),
            ));
            let matched_upper = machine.alloc_neg(Neg::Con(
                vec!["cpk-7-dedup-matched".into()],
                Vec::new(),
            ));
            let producers = [0, 1]
                .map(|index| cpk_7_admit_inert_constraint(&mut machine, 120 + index, "dedup"));
            let roots = producers.map(|producer| {
                machine.add_upper_bound(
                    source,
                    current_upper,
                    ConstraintWeights::empty(),
                    BoundDerivation::Constraint(producer),
                );
                machine.bounds.root_claim_by_producer_constraint[&producer]
            });
            let upper_record = machine
                .bounds
                .records
                .iter()
                .enumerate()
                .find_map(|(index, record)| {
                    (record.owner() == source
                        && record.endpoint() == BoundEndpoint::Upper(current_upper))
                    .then_some(BoundRecordId(index as u32))
                })
                .expect("the duplicate routes share one materialization record");
            let provenance = producers.map(|producer| {
                machine.intern_row_derivation(
                    RowDerivationRule::UnweightedReduction,
                    vec![RowDerivationParent::Constraint(producer)],
                    Vec::new(),
                )
            });
            let mut states = [UnweightedRowReductionRecordId(u32::MAX); 2];
            for index in order {
                let (state, registered_root) = machine.register_unweighted_row_reduction_for_test(
                    UnweightedRowReductionRecord {
                        source,
                        producer_constraint: Some(producers[index]),
                        original_items: vec![matched_upper],
                        original_tail: current_upper,
                        original_upper,
                        consumed_items: Vec::new(),
                        remaining_items: vec![matched_upper],
                        current_reduced_upper: UnweightedRowReductionMaterialization {
                            endpoint: current_upper,
                            record: upper_record,
                        },
                        processed_lower_records: FxHashSet::default(),
                        provenance_head: provenance[index],
                    },
                );
                states[index] = state;
                assert_eq!(registered_root, Some(roots[index]));
            }

            let lower = machine.alloc_pos(Pos::Con(
                vec!["cpk-7-dedup-matched".into()],
                Vec::new(),
            ));
            machine.add_lower_bound(
                source,
                lower,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            );
            let lower_record = machine
                .bounds
                .records
                .iter()
                .enumerate()
                .find_map(|(index, record)| {
                    (record.owner() == source
                        && record.endpoint() == BoundEndpoint::Lower(lower))
                    .then_some(BoundRecordId(index as u32))
                })
                .expect("the direct duplicate route must retain its lower record");
            let routes = order.map(|index| IncrementalRouteKey {
                upper: original_upper,
                upper_record,
                provenance: machine.unweighted_row_reduction_records[states[index].0 as usize]
                    .provenance_head,
                claim: Some(roots[index]),
            });
            let prepared = machine
                .proof_store
                .prepare_replay_route(&machine, lower_record, upper_record, &routes)
                .expect("the direct CPK route deduplicates the exact semantic action");
            assert_eq!(prepared.routing, ReplayRouting::IncrementalOnly);
            let incremental = &prepared.proof_event.incremental_replays;
            assert_eq!(incremental.len(), 1);
            assert_eq!(incremental[0].route.upper, original_upper);
            assert_eq!(incremental[0].route.upper_record, upper_record);
            assert_eq!(incremental[0].route.claim, Some(roots[order[0]]));
            assert_ne!(
                machine.bounds.record(upper_record).unwrap().endpoint(),
                BoundEndpoint::Upper(original_upper),
                "the exact-key dedup also covers the matched decoupled route shape",
            );

            let result = machine
                .constraint_record_id(lower, ConstraintWeights::empty(), original_upper)
                .expect("the first-seen semantic action is admitted once");
            let merged = &machine.constraint_records[result.0 as usize].row_derivations;
            for state in states {
                let successor = machine.unweighted_row_reduction_records[state.0 as usize]
                    .provenance_head;
                assert!(
                    merged.contains(&successor),
                    "deduping semantic work must not drop either row-provenance merge",
                );
            }
        };

        run([0, 1]);
        run([1, 0]);
    }

    #[test]
    fn cpk_7_shadow_claim_move_keeps_decoupled_incremental_route() {
        let mut fixture = cpk_7_two_stage_row_claim_move_fixture();
        let prepared = cpk_7_run_second_row_stage(&mut fixture);

        assert_eq!(prepared.routing, ReplayRouting::IncrementalOnly);
        assert!(prepared.proof_event.pair_replay.is_none());
        assert_eq!(
            prepared.proof_event.incremental_replays.len(),
            1,
        );
        assert_cpk_7_decoupled_claim_move_route(&fixture, &prepared);
    }

    #[test]
    fn cpk_7_shadow_generic_pair_keeps_decoupled_incremental_route() {
        let mut fixture = cpk_7_two_stage_row_claim_move_fixture();
        assert!(fixture
            .machine
            .remove_scheme_projection_live_coverage_state(fixture.claim, fixture.state));
        let prepared = cpk_7_run_second_row_stage(&mut fixture);

        assert_eq!(prepared.routing, ReplayRouting::Generic);
        assert!(prepared.proof_event.pair_replay.is_some());
        assert_eq!(
            prepared.proof_event.incremental_replays.len(),
            1,
        );
        assert_cpk_7_decoupled_claim_move_route(&fixture, &prepared);
    }

    #[test]
    fn cpk_7_shadow_routes_all_five_lineages_exactly() {
        for (offset, lineage) in [
            ProjectionLineage::Original,
            ProjectionLineage::ReplayConstraint,
            ProjectionLineage::ReplayEvidence,
            ProjectionLineage::StructuralConstraint,
            ProjectionLineage::ReductionRouteConstraint,
        ]
        .into_iter()
        .enumerate()
        {
            let mut machine = cpk_3_replay_fixture_with_oracle(false);
            let claim = machine
                .proof_store
                .upper_claims
                .iter()
                .find(|claim| {
                    claim.lineage == lineage
                        && machine
                            .proof_store
                            .live_states_by_coverage_root
                            .contains_key(&claim.coverage_root)
                })
                .cloned()
                .expect("the replay fixture must materialize every live lineage");
            let owner = machine
                .bounds
                .record(claim.current_record)
                .expect("the representative claim must point at a semantic upper record")
                .owner;
            let lower = machine.alloc_pos(Pos::Var(TypeVar(91_000 + offset as u32)));
            machine.add_lower_bound(
                owner,
                lower,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            );
            let lower_record = machine
                .bounds
                .records
                .iter()
                .enumerate()
                .find_map(|(index, record)| {
                    (record.owner() == owner
                        && record.endpoint() == BoundEndpoint::Lower(lower))
                    .then_some(BoundRecordId(index as u32))
                })
                .expect("the lineage route must retain its lower record");
            let prepared = machine
                .proof_store
                .prepare_replay_route(&machine, lower_record, claim.current_record, &[])
                .expect("the direct CPK pair must retain the claim lineage");
            let routed_lineages = prepared
                .proof_event
                .pair_replay
                .iter()
                .flat_map(PreparedReplayParentSet::iter)
                .chain(
                    prepared
                        .proof_event
                        .incremental_replays
                        .iter()
                        .flat_map(|replay| replay.parents.iter()),
                )
                .map(|parent| parent.lineage)
                .collect::<FxHashSet<_>>();
            assert!(
                routed_lineages.contains(&lineage),
                "the exact prepared route must retain {lineage:?} attribution",
            );
        }
    }

    #[test]
    fn cpk_3_trivial_replay_records_drop_and_admission_in_active_shadow() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let admissions_before = fixture.machine.proof_store.replay_admissions.len();
        let occurrences_before = fixture.machine.proof_store.occurrences.len();
        let attempted = SubtypeConstraintKey {
            lower: fixture.machine.alloc_pos(Pos::Bot),
            upper: fixture.machine.constraint_records[fixture.result.0 as usize]
                .key
                .upper,
            weights: ConstraintWeights::empty(),
        };
        let expected_drop = ReplayDropRecord {
            attempted: attempted.clone(),
            derivation: fixture.carrier,
        };
        fixture
            .machine
            .apply_cpk_trivial_replay_for_test(attempted, fixture.carrier);
        let machine = fixture.machine;
        let snapshot = machine.proof_store.clone();

        assert_eq!(
            machine.replay_drop_records.as_slice(),
            &[expected_drop.clone()]
        );
        assert_eq!(
            &snapshot.replay_admissions[admissions_before..],
            &[ReplayAdmissionEvent {
                result: None,
                carrier: expected_drop.derivation,
                disposition: ReplayAdmissionDisposition::Trivial,
            }],
        );
        assert_eq!(
            &snapshot.occurrences[occurrences_before..],
            &[ProofOccurrence {
                result: ProofResult::TrivialReplay(ReplayDropRecordId(0)),
                cause: ProofCause::ReplayDrop(expected_drop),
                parents: Vec::new(),
                event: occurrences_before,
                completeness: ProvenanceCompleteness::Complete,
            }],
        );
        assert!(snapshot.replay_finite_map.is_empty());
        assert!(snapshot.first_replay_witnesses.is_empty());
    }

    #[test]
    fn cpk_3_evidence_only_replay_records_both_bound_edges_in_active_shadow() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let admissions_before = fixture.machine.proof_store.replay_admissions.len();
        let occurrences_before = fixture.machine.proof_store.occurrences.len();
        let constraint = SubtypeConstraintKey {
            lower: fixture.machine.alloc_pos(Pos::Var(TypeVar(10))),
            upper: fixture.machine.alloc_neg(Neg::Var(TypeVar(11))),
            weights: ConstraintWeights::empty(),
        };
        fixture
            .machine
            .apply_cpk_evidence_only_replay_for_test(constraint, fixture.carrier);
        let carrier = fixture.carrier;
        let machine = fixture.machine;
        let snapshot = machine.proof_store.clone();

        assert_eq!(
            &snapshot.replay_admissions[admissions_before..],
            &[ReplayAdmissionEvent {
                result: None,
                carrier,
                disposition: ReplayAdmissionDisposition::EvidenceOnly,
            }],
        );
        let evidence = &snapshot.occurrences[occurrences_before..];
        assert_eq!(evidence.len(), 2);
        assert_eq!(
            evidence
                .iter()
                .map(|occurrence| occurrence.result)
                .collect::<Vec<_>>(),
            vec![
                ProofResult::EvidenceBound(BoundRecordId(3)),
                ProofResult::EvidenceBound(BoundRecordId(4)),
            ],
        );
        for (offset, occurrence) in evidence.iter().enumerate() {
            assert_eq!(occurrence.cause, ProofCause::ReplayEvidence(carrier));
            assert_eq!(
                occurrence.parents,
                vec![
                    ProofParent::Semantic(SemanticFactRef::Bound(carrier.lower)),
                    ProofParent::Semantic(SemanticFactRef::Bound(carrier.upper)),
                ],
            );
            assert_eq!(occurrence.event, occurrences_before + offset);
            assert_eq!(occurrence.completeness, ProvenanceCompleteness::Complete);
        }
        assert!(snapshot.replay_finite_map.is_empty());
        assert!(snapshot.first_replay_witnesses.is_empty());
    }

    #[test]
    fn cpk_3_replay_first_winner_matches_factored_for_every_parent_arrival_order() {
        let permutations = [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ];
        for order in permutations {
            let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
            let claims = [
                fixture.coverage_root,
                add_same_root_replay_claim(
                    &mut fixture,
                    TypeVar(20),
                    ConstraintRecordId(20_000),
                ),
                add_same_root_replay_claim(
                    &mut fixture,
                    TypeVar(21),
                    ConstraintRecordId(20_001),
                ),
            ];
            for index in order {
                fixture.machine.apply_cpk_replay_parent_arrival_for_test(
                    fixture.result,
                    fixture.carrier,
                    claims[index],
                );
            }
            let result = fixture.result;
            let root = fixture.coverage_root;
            let machine = fixture.machine;
            let snapshot = machine.proof_store.clone();

            assert_eq!(snapshot.replay_finite_map.len(), 1);
            assert_eq!(snapshot.first_replay_witnesses.len(), 1);
            let first = snapshot.first_replay_witnesses[&(result, root)];
            assert_eq!(
                first.representative_claim, claims[order[0]],
                "the event-first claim must remain representative for order {order:?}"
            );
            let occurrence = snapshot
                .replay_finite_map
                .iter()
                .find(|occurrence| occurrence.result == result)
                .expect("the permutation produces one exact replay occurrence");
            assert_eq!(occurrence.carrier, fixture.carrier);
            assert_eq!(occurrence.first_event, 0);
            assert_eq!(occurrence.lower_parents.len(), 1);
            assert!(occurrence.upper_parents.is_empty());
            assert_eq!(
                occurrence.lower_parents[0],
                ReplayProofParent {
                    side: ReplayClaimParentSide::Lower,
                    coverage_root: root,
                    representative_claim: claims[order[0]],
                    lineage: if order[0] == 0 {
                        ProjectionLineage::Original
                    } else {
                        ProjectionLineage::ReplayConstraint
                    },
                },
            );
        }
    }

    #[test]
    fn cpk_4_replay_formula_and_projectability_match_legacy_end_to_end() {
        let machine = cpk_3_replay_fixture_with_oracle(false);
        let snapshot = machine.proof_store.clone();
        let claimed = |claim| SchemeProjectionProofSupport::Claimed(UpperReplayClaimId(claim));
        let replay = |pivot, lower, upper| BinaryReplayDerivation {
            pivot: TypeVar(pivot),
            lower: BoundRecordId(lower),
            upper: BoundRecordId(upper),
            rule: ReplayRule::UpperBoundAdded,
        };
        let replay_clause = |claim, pivot, lower, upper| ProjectionClause::ReplayConjunction {
            support: claimed(claim),
            carrier: replay(pivot, lower, upper),
            lower: BoundRecordId(lower),
            upper: BoundRecordId(upper),
            attribution: Some(ProjectionLineage::ReplayConstraint),
        };
        let expected_formulas = FxHashMap::from_iter([
            (
                BoundRecordId(0),
                vec![ProjectionClause::Standalone {
                    support: claimed(0),
                    attribution: Some(ProjectionLineage::Original),
                }],
            ),
            (
                BoundRecordId(2),
                vec![ProjectionClause::Standalone {
                    support: claimed(1),
                    attribution: Some(ProjectionLineage::Original),
                }],
            ),
            (
                BoundRecordId(4),
                vec![
                    replay_clause(0, 31, 0, 3),
                    replay_clause(1, 31, 0, 3),
                    replay_clause(4, 32, 6, 9),
                    replay_clause(5, 32, 6, 9),
                ],
            ),
            (
                BoundRecordId(6),
                vec![ProjectionClause::Standalone {
                    support: claimed(4),
                    attribution: Some(ProjectionLineage::Original),
                }],
            ),
            (
                BoundRecordId(8),
                vec![ProjectionClause::Standalone {
                    support: claimed(5),
                    attribution: Some(ProjectionLineage::Original),
                }],
            ),
            (
                BoundRecordId(10),
                vec![
                    ProjectionClause::Standalone {
                        support: claimed(8),
                        attribution: Some(ProjectionLineage::Original),
                    },
                    ProjectionClause::DerivedUnary {
                        support: claimed(1),
                        carrier: DerivedUnaryCarrier::ReductionRoute(RowDerivationId(0)),
                        premise: ProofPremise::RootCoverage(UpperReplayClaimId(1)),
                        attribution: Some(ProjectionLineage::ReductionRouteConstraint),
                    },
                ],
            ),
        ]);
        assert_eq!(snapshot.projection_formulas, expected_formulas);

        let included = |supports: Vec<(u32, u32)>| ProjectionDecision::Included {
            supports: ProjectionSupportSet {
                uncovered_claims: supports
                    .into_iter()
                    .map(|(coverage_root, representative_claim)| ProjectionClaimSupport {
                        coverage_root: UpperReplayClaimId(coverage_root),
                        representative_claim: UpperReplayClaimId(representative_claim),
                    })
                    .collect(),
                independent_supports: Vec::new(),
            },
        };
        for (record, owner, decision) in [
            (BoundRecordId(0), TypeVar(31), included(vec![(0, 0)])),
            (BoundRecordId(2), TypeVar(34), ProjectionDecision::Excluded),
            (
                BoundRecordId(4),
                TypeVar(34),
                included(vec![(0, 2), (4, 6), (5, 7)]),
            ),
            (BoundRecordId(6), TypeVar(32), included(vec![(4, 4)])),
            (BoundRecordId(8), TypeVar(34), included(vec![(5, 5)])),
            (BoundRecordId(10), TypeVar(36), included(vec![(8, 8)])),
        ] {
            assert_cpk_projection_decision_and_consumer(&machine, owner, record, decision);
        }
    }

    fn assert_cpk_projection_decision_and_consumer(
        machine: &ConstraintMachine,
        owner: TypeVar,
        record: BoundRecordId,
        expected: ProjectionDecision,
    ) {
        assert!(matches!(machine.proof_read_authority(), ProofReadAuthority::Cpk));
        assert_eq!(project_lower_for_test(machine, record).0, Ok(expected.clone()));
        let entry = machine
            .scheme_projectable_lowers(owner)
            .find(|entry| entry.record == record);
        match expected {
            ProjectionDecision::Excluded => assert!(entry.is_none()),
            ProjectionDecision::Unclaimed => assert_eq!(
                entry.expect("an unclaimed lower remains a direct consumer input").reason,
                SchemeProjectableLowerReason::Unclaimed,
            ),
            ProjectionDecision::Included { supports } => assert_eq!(
                entry.expect("an included lower reaches the direct consumer").reason,
                SchemeProjectableLowerReason::Qualified {
                    uncovered_claims: supports
                        .uncovered_claims
                        .into_iter()
                        .map(|support| support.representative_claim)
                        .collect(),
                    independent_supports: supports.independent_supports,
                },
            ),
        }
        assert!(machine.proof_terminal_failure().is_none());
    }

    #[test]
    fn cpk_4_standalone_only_is_projectable_and_metadata_only() {
        let mut machine = ConstraintMachine::new();
        let (record, _) = cpk_4_projection_record(&mut machine, 1);
        let owner = machine.bounds.record(record).unwrap().owner();
        let origin = OriginId(40_001);
        record_test_origin(&mut machine, record, origin);
        let carrier = ProjectionProofCarrier::Origin(origin);
        let semantic_epoch = machine.epoch;
        let provenance_epoch = machine.provenance_epoch;
        let journal = machine.activate_method_role_mutations();
        let support = cpk_4_add_independent_support(&mut machine, record, carrier);
        machine.register_cpk_projection_clause_for_test(
            record,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::Standalone { support },
            ),
        );
        let publications = machine.take_method_role_mutations();
        journal.finish();

        assert_eq!(
            machine.proof_store.projection_formulas[&record],
            vec![ProjectionClause::Standalone {
                support,
                attribution: None,
            }],
        );
        assert_eq!(machine.epoch, semantic_epoch);
        assert!(machine.provenance_epoch > provenance_epoch);
        assert!(publications.is_empty());
        assert_cpk_projection_decision_and_consumer(
            &machine,
            owner,
            record,
            ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    uncovered_claims: Vec::new(),
                    independent_supports: vec![carrier],
                },
            },
        );
    }

    #[test]
    fn cpk_4_derived_unary_only_cycle_flips_inclusion_and_owner() {
        let mut machine = ConstraintMachine::new();
        let (record, _) = cpk_4_projection_record(&mut machine, 2);
        let owner = machine.bounds.record(record).unwrap().owner();
        let origin = OriginId(40_002);
        record_test_origin(&mut machine, record, origin);
        let carrier = ProjectionProofCarrier::Origin(origin);
        let support = cpk_4_add_independent_support(&mut machine, record, carrier);

        let (dependent, _) = cpk_4_projection_record(&mut machine, 4);
        let dependent_owner = machine.bounds.record(dependent).unwrap().owner();
        let dependent_origin = OriginId(40_004);
        record_test_origin(&mut machine, dependent, dependent_origin);
        let dependent_carrier = ProjectionProofCarrier::Origin(dependent_origin);
        let dependent_support =
            cpk_4_add_independent_support(&mut machine, dependent, dependent_carrier);
        let dependent_parent =
            cpk_7_admit_inert_constraint(&mut machine, 40_005, "projection-dependent");
        machine.register_cpk_projection_clause_for_test(
            dependent,
            RecordProofClauseLinkAdmission::independent(
                dependent_support,
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                        parent: dependent_parent,
                        rule: StructuralDerivationRule::FunctionReturn,
                    }),
                    premise: ProofPremise::Record(record),
                },
            ),
        );
        let cycle_parent =
            cpk_7_admit_inert_constraint(&mut machine, 40_006, "projection-cycle");
        let semantic_epoch = machine.epoch;
        let journal = machine.activate_method_role_mutations();
        machine.register_cpk_projection_clause_for_test(
            record,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                        parent: cycle_parent,
                        rule: StructuralDerivationRule::FunctionReturn,
                    }),
                    premise: ProofPremise::Record(record),
                },
            ),
        );
        let publications = machine.take_method_role_mutations();
        journal.finish();

        assert!(matches!(
            machine.proof_store.projection_formulas[&record].as_slice(),
            [ProjectionClause::DerivedUnary { .. }]
        ));
        assert!(machine.epoch > semantic_epoch);
        let mut affected_owners = publications
            .into_iter()
            .filter_map(|mutation| match mutation {
                crate::constraints::mutation::MethodRoleMutation::Changed {
                    key: crate::constraints::mutation::DependencyKey::ConstraintBounds(owner),
                    ..
                } => Some(owner),
                _ => None,
            })
            .collect::<Vec<_>>();
        affected_owners.sort_by_key(|owner| owner.0);
        assert_eq!(affected_owners, vec![owner, dependent_owner]);
        for (owner, record) in [(owner, record), (dependent_owner, dependent)] {
            let (decision, round) = project_lower_for_test(&machine, record);
            assert_eq!(decision, Ok(ProjectionDecision::Excluded));
            assert!(round.cycle_cuts() > 0);
            assert_cpk_projection_decision_and_consumer(
                &machine,
                owner,
                record,
                ProjectionDecision::Excluded,
            );
        }
    }

    #[test]
    fn cpk_4_no_claim_record_passthrough_has_no_formula_or_publication() {
        let mut machine = ConstraintMachine::new();
        let (record, _) = cpk_4_projection_record(&mut machine, 3);
        let owner = machine.bounds.record(record).unwrap().owner();
        let epochs = (machine.epoch, machine.provenance_epoch);
        let journal = machine.activate_method_role_mutations();

        assert!(!machine.proof_store.projection_supports.contains_key(&record));
        assert!(!machine.proof_store.projection_formulas.contains_key(&record));
        assert_cpk_projection_decision_and_consumer(
            &machine,
            owner,
            record,
            ProjectionDecision::Unclaimed,
        );
        assert_eq!((machine.epoch, machine.provenance_epoch), epochs);
        assert!(machine.take_method_role_mutations().is_empty());
        journal.finish();
    }

    #[test]
    fn cpk_no_claim_path_allocates_no_claim_storage_or_index_work() {
        let mut machine = ConstraintMachine::new();
        let before = machine.proof_store.claim_allocation_census();
        assert_eq!(before, (0, 0, 0, 0, 0, 0, 0));

        let target = TypeVar(40_010);
        let lower = machine.alloc_pos(Pos::Con(vec!["cpk-no-claim".into()], Vec::new()));
        machine.add_lower_bound(
            target,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );

        assert_eq!(
            machine.proof_store.claim_allocation_census(),
            before,
            "an ordinary no-claim bound must not allocate the CPK claim arena, grow either claim index, or perform claim-index maintenance",
        );
    }

    #[test]
    fn cpk_4_five_source_attribution_matrix_is_writer_classified() {
        let mut machine = cpk_machine();
            let support = |claim| SchemeProjectionProofSupport::Claimed(claim);
            let replay = BinaryReplayDerivation {
                pivot: TypeVar(40_000),
                lower: BoundRecordId(40_001),
                upper: BoundRecordId(40_002),
                rule: ReplayRule::LowerBoundAdded,
            };
            let entries = [
                RecordProofClauseLinkAdmission::claimed(
                    UpperReplayClaimId(0),
                    RecordProofClause::Standalone {
                        support: support(UpperReplayClaimId(0)),
                    },
                    ClaimedAttributionSource::FlatRetained,
                ),
                RecordProofClauseLinkAdmission::claimed(
                    UpperReplayClaimId(1),
                    RecordProofClause::ReplayConjunction {
                        carrier: replay,
                        lower_premise: replay.lower,
                        upper_premise: replay.upper,
                    },
                    ClaimedAttributionSource::CanonicalReplay,
                ),
                RecordProofClauseLinkAdmission::claimed(
                    UpperReplayClaimId(2),
                    RecordProofClause::ReplayConjunction {
                        carrier: replay,
                        lower_premise: replay.lower,
                        upper_premise: replay.upper,
                    },
                    ClaimedAttributionSource::FlatRetained,
                ),
                RecordProofClauseLinkAdmission::claimed(
                    UpperReplayClaimId(3),
                    RecordProofClause::DerivedUnary {
                        carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                            parent: ConstraintRecordId(40_003),
                            rule: StructuralDerivationRule::FunctionReturn,
                        }),
                        premise: ProofPremise::Constraint(ConstraintRecordId(40_003)),
                    },
                    ClaimedAttributionSource::FlatRetained,
                ),
                RecordProofClauseLinkAdmission::claimed(
                    UpperReplayClaimId(4),
                    RecordProofClause::DerivedUnary {
                        carrier: DerivedUnaryCarrier::ReductionRoute(RowDerivationId(40_004)),
                        premise: ProofPremise::RootCoverage(UpperReplayClaimId(4)),
                    },
                    ClaimedAttributionSource::FlatRetained,
                ),
            ];
            for (index, admission) in entries.into_iter().enumerate() {
                machine
                    .proof_store
                    .record_projection_clause(BoundRecordId(index as u32), admission);
            }
        let snapshot = machine.proof_store.clone();

        let actual = snapshot
            .projection_formulas
            .values()
            .flatten()
            .filter_map(|clause| match *clause {
                ProjectionClause::Standalone { attribution, .. }
                | ProjectionClause::DerivedUnary { attribution, .. }
                | ProjectionClause::ReplayConjunction { attribution, .. } => attribution,
            })
            .collect::<FxHashSet<_>>();
        assert_eq!(
            actual,
            FxHashSet::from_iter([
                ProjectionLineage::Original,
                ProjectionLineage::ReplayConstraint,
                ProjectionLineage::ReplayEvidence,
                ProjectionLineage::StructuralConstraint,
                ProjectionLineage::ReductionRouteConstraint,
            ]),
        );
    }

    fn cpk_5_trigger_lower_route(
        fixture: &mut CpkReplayAdmissionFixture,
        lower_is_var: bool,
    ) {
        let lower = if lower_is_var {
            fixture.machine.alloc_pos(Pos::Var(TypeVar(41_000)))
        } else {
            fixture.machine.alloc_pos(Pos::Con(
                vec!["cpk-5-lower".into()],
                Vec::new(),
            ))
        };
        let upper = fixture.machine.alloc_neg(Neg::Var(fixture.parent_owner));
        fixture
            .machine
            .subtype(lower, upper, OriginId::unknown_internal());
    }

    fn assert_cpk_5_event_count_parity(snapshot: &ProofOccurrenceStore) {
        assert!(!snapshot.replay_event_observations.borrow().is_empty());
        assert!(snapshot
            .replay_event_observations
            .borrow()
            .iter()
            .all(|observation| {
            observation.legacy_input_count == observation.shadow_input_count
                && observation.legacy_generated_count == observation.shadow_generated_count
                && observation.legacy_accepted_count == observation.shadow_accepted_count
                && observation.admissions.len() == observation.shadow_generated_count
                && observation.accepted_results.len() == observation.shadow_accepted_count
        }));
    }

    #[test]
    fn cpk_7_shadow_natural_events_expose_replay_disposition_matrix() {
        const EVIDENCE_CHILD: &str = "YULANG_CPK_7_EVIDENCE_ONLY_DISPOSITION_CHILD";
        if std::env::var_os(EVIDENCE_CHILD).is_some() {
            let mut machine = ConstraintMachine::new();
            let a = machine.alloc_pos(Pos::Var(TypeVar(43_102)));
            let b_upper = machine.alloc_neg(Neg::Var(TypeVar(43_103)));
            machine.subtype(a, b_upper, OriginId::unknown_internal());
            let b = machine.alloc_pos(Pos::Var(TypeVar(43_103)));
            let c_upper = machine.alloc_neg(Neg::Var(TypeVar(43_104)));
            machine.subtype(b, c_upper, OriginId::unknown_internal());
            let dispositions = machine
                .proof_store
                .replay_admissions
                .iter()
                .map(|admission| admission.disposition)
                .collect::<Vec<_>>();
            assert!(
                dispositions.contains(&ReplayAdmissionDisposition::EvidenceOnly),
                "natural evidence-only replay-event dispositions were {dispositions:?}",
            );
            return;
        }

        let mut dispositions = Vec::new();
        let mut collect = |machine: &ConstraintMachine| {
            dispositions.extend(
                machine
                    .proof_store
                    .replay_admissions
                    .iter()
                    .map(|admission| admission.disposition),
            );
        };

        collect(&cpk_3_replay_fixture_with_oracle(false));

        let mut trivial = ConstraintMachine::new();
        let trivial_owner = TypeVar(43_100);
        let trivial_upper = trivial.alloc_neg(Neg::Con(vec!["cpk-7-trivial".into()], Vec::new()));
        trivial.add_upper_bound(
            trivial_owner,
            trivial_upper,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );
        let bottom = trivial.alloc_pos(Pos::Bot);
        trivial.add_lower_bound(
            trivial_owner,
            bottom,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );
        collect(&trivial);

        let mut incomplete = ConstraintMachine::new();
        incomplete.set_replay_derivation_budget_for_test(0, usize::MAX);
        let incomplete_owner = TypeVar(43_101);
        let incomplete_upper = incomplete.alloc_neg(Neg::Con(
            vec!["cpk-7-incomplete-upper".into()],
            Vec::new(),
        ));
        incomplete.add_upper_bound(
            incomplete_owner,
            incomplete_upper,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );
        let incomplete_lower = incomplete.alloc_pos(Pos::Con(
            vec!["cpk-7-incomplete-lower".into()],
            Vec::new(),
        ));
        incomplete.add_lower_bound(
            incomplete_owner,
            incomplete_lower,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );
        collect(&incomplete);

        let required = [
            ReplayAdmissionDisposition::CanonicalDuplicate,
            ReplayAdmissionDisposition::Trivial,
            ReplayAdmissionDisposition::Incomplete,
        ];
        assert!(
            required.iter().all(|disposition| dispositions.contains(disposition)),
            "natural replay-event dispositions were {dispositions:?}",
        );

        let output = std::process::Command::new(
            std::env::current_exe().expect("the evidence-only child uses this test binary"),
        )
        .args([
            "--exact",
            "constraints::proof::tests::cpk_7_shadow_natural_events_expose_replay_disposition_matrix",
            "--nocapture",
        ])
        .env(EVIDENCE_CHILD, "1")
        .env("YULANG_REPLAY_EVIDENCE_ONLY_SKIP", "1")
        .output()
        .expect("the isolated evidence-only natural-event test must run");
        assert!(
            output.status.success(),
            "isolated evidence-only natural-event test failed:\n{}",
            String::from_utf8_lossy(&output.stderr),
        );
    }

    #[test]
    fn cpk_7_shadow_no_claim_generic_preserves_some_empty_in_both_directions() {
        let run = |lower_first: bool| {
            let mut machine = ConstraintMachine::new();
            let owner = TypeVar(43_000 + u32::from(lower_first));
            let lower = machine.alloc_pos(Pos::Con(vec!["cpk-7-empty".into()], Vec::new()));
            let upper = machine.alloc_neg(Neg::Con(vec!["cpk-7-empty".into()], Vec::new()));
            if lower_first {
                machine.add_lower_bound(
                    owner,
                    lower,
                    ConstraintWeights::empty(),
                    BoundDerivation::Origin(OriginId::unknown_internal()),
                );
                machine.add_upper_bound(
                    owner,
                    upper,
                    ConstraintWeights::empty(),
                    BoundDerivation::Origin(OriginId::unknown_internal()),
                );
            } else {
                machine.add_upper_bound(
                    owner,
                    upper,
                    ConstraintWeights::empty(),
                    BoundDerivation::Origin(OriginId::unknown_internal()),
                );
                machine.add_lower_bound(
                    owner,
                    lower,
                    ConstraintWeights::empty(),
                    BoundDerivation::Origin(OriginId::unknown_internal()),
                );
            }
            let lower_record = machine
                .bounds
                .records
                .iter()
                .enumerate()
                .find_map(|(index, record)| {
                    (record.owner() == owner
                        && record.endpoint() == BoundEndpoint::Lower(lower))
                    .then_some(BoundRecordId(index as u32))
                })
                .expect("the no-claim lower must be a semantic record");
            let prepared = cpk_7_direct_pair_route(&machine, lower_record, owner, upper);
            assert_eq!(prepared.routing, ReplayRouting::Generic);
            let parents = prepared
                .proof_event
                .pair_replay
                .as_ref()
                .expect("no-claim Generic retains an explicit empty pair");
            assert!(parents.lower.as_slice().is_empty());
            assert!(parents.upper.as_slice().is_empty());
            assert!(prepared.proof_event.incremental_replays.is_empty());
        };
        run(false);
        run(true);
    }

    #[test]
    fn cpk_7_shadow_target_late_frontiers_preserve_exact_routing() {
        let run = |lower_first: bool| {
            let mut machine = ConstraintMachine::new();
            let owner = TypeVar(73_000 + u32::from(lower_first));
            let lower = machine.alloc_pos(Pos::Con(
                vec!["cpk-7-target-late-lower".into()],
                Vec::new(),
            ));
            let upper = machine.alloc_neg(Neg::Con(
                vec!["cpk-7-target-late-upper".into()],
                Vec::new(),
            ));
            let owner_pos = machine.alloc_pos(Pos::Var(owner));
            let owner_neg = machine.alloc_neg(Neg::Var(owner));
            let origin = OriginId::unknown_internal();

            if lower_first {
                machine.subtype(lower, owner_neg, origin);
            } else {
                machine.subtype(owner_pos, upper, origin);
            }
            let early_record = machine
                .bounds
                .records
                .iter()
                .enumerate()
                .find_map(|(index, record)| {
                    (record.owner() == owner
                        && record.endpoint()
                            == if lower_first {
                                BoundEndpoint::Lower(lower)
                            } else {
                                BoundEndpoint::Upper(upper)
                            })
                    .then_some(BoundRecordId(index as u32))
                })
                .expect("the early target frontier record is materialized");

            for offset in 0..16 {
                let unrelated = TypeVar(73_100 + offset);
                let unrelated_lower = machine.alloc_pos(Pos::Con(
                    vec!["cpk-7-target-late-churn".into(), offset.to_string()],
                    Vec::new(),
                ));
                let unrelated_upper = machine.alloc_neg(Neg::Con(
                    vec!["cpk-7-target-late-churn".into(), offset.to_string()],
                    Vec::new(),
                ));
                let unrelated_pos = machine.alloc_pos(Pos::Var(unrelated));
                let unrelated_neg = machine.alloc_neg(Neg::Var(unrelated));
                machine.subtype(unrelated_lower, unrelated_neg, origin);
                machine.subtype(unrelated_pos, unrelated_upper, origin);
            }

            let admissions_before = machine.proof_store.replay_admissions.len();
            if lower_first {
                machine.subtype(owner_pos, upper, origin);
            } else {
                machine.subtype(lower, owner_neg, origin);
            }
            let lower_record = machine
                .bounds
                .records
                .iter()
                .enumerate()
                .find_map(|(index, record)| {
                    (record.owner() == owner
                        && record.endpoint() == BoundEndpoint::Lower(lower))
                    .then_some(BoundRecordId(index as u32))
                })
                .expect("the target lower record exists after the late insertion");
            let upper_record = machine
                .bounds
                .records
                .iter()
                .enumerate()
                .find_map(|(index, record)| {
                    (record.owner() == owner
                        && record.endpoint() == BoundEndpoint::Upper(upper))
                    .then_some(BoundRecordId(index as u32))
                })
                .expect("the target upper record exists after the late insertion");
            let late_record = if lower_first {
                upper_record
            } else {
                lower_record
            };
            assert!(late_record.0 >= early_record.0 + 32);

            let prepared = machine
                .proof_store
                .prepare_replay_route(&machine, lower_record, upper_record, &[])
                .expect("the late frontier pair must validate directly in CPK");
            assert_eq!(prepared.routing, ReplayRouting::Generic);
            let parents = prepared
                .proof_event
                .pair_replay
                .as_ref()
                .expect("the uncovered late upper claim requires generic pair replay");
            assert!(parents.lower.as_slice().is_empty());
            assert_eq!(parents.upper.as_slice().len(), 1);
            assert!(prepared.proof_event.incremental_replays.is_empty());
            let admissions = &machine.proof_store.replay_admissions[admissions_before..];
            assert_eq!(admissions.len(), 1);
            assert_eq!(admissions[0].disposition, ReplayAdmissionDisposition::NewSemantic);
            let accepted = admissions[0]
                .result
                .expect("the late-frontier replay must retain its accepted result");
            assert!(machine.constraint_records.get(accepted.0 as usize).is_some());
        };

        run(true);
        run(false);
    }

    #[test]
    fn cpk_7_shadow_generic_route_preserves_all_uncovered_upper_roots() {
        let mut machine = ConstraintMachine::new();
        let owner = TypeVar(73_200);
        let upper = machine.alloc_neg(Neg::Con(
            vec!["cpk-7-multi-root-upper".into()],
            Vec::new(),
        ));
        let origin = OriginId::unknown_internal();
        let producers = ["first", "second"].map(|suffix| {
            let lower = machine.alloc_pos(Pos::Con(
                vec!["cpk-7-multi-root-producer".into(), suffix.into()],
                Vec::new(),
            ));
            let upper = machine.alloc_neg(Neg::Con(
                vec!["cpk-7-multi-root-result".into(), suffix.into()],
                Vec::new(),
            ));
            machine.subtype(lower, upper, origin);
            machine
                .constraint_record_id(lower, ConstraintWeights::empty(), upper)
                .expect("the producer relation is canonical")
        });
        let mut roots = producers.map(|producer| {
            machine.add_upper_bound(
                owner,
                upper,
                ConstraintWeights::empty(),
                BoundDerivation::Constraint(producer),
            );
            machine.bounds.root_claim_by_producer_constraint[&producer]
        });
        roots.sort();
        let upper_records = roots.map(|root| {
            let claim = &machine.bounds.upper_replay_claims[root.0 as usize];
            assert_eq!(claim.coverage_root, root);
            claim.current_record
        });
        assert_eq!(upper_records[0], upper_records[1]);

        let admissions_before = machine.proof_store.replay_admissions.len();
        let lower = machine.alloc_pos(Pos::Con(
            vec!["cpk-7-multi-root-lower".into()],
            Vec::new(),
        ));
        machine.add_lower_bound(
            owner,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(origin),
        );

        let lower_record = machine
            .bounds
            .records
            .iter()
            .enumerate()
            .find_map(|(index, record)| {
                (record.owner() == owner && record.endpoint() == BoundEndpoint::Lower(lower))
                    .then_some(BoundRecordId(index as u32))
            })
            .expect("the multi-root route must retain its lower record");
        let prepared = machine
            .proof_store
            .prepare_replay_route(&machine, lower_record, upper_records[0], &[])
            .expect("the multi-root pair must validate directly in CPK");
        assert_eq!(prepared.routing, ReplayRouting::Generic);
        let parents = prepared
            .proof_event
            .pair_replay
            .as_ref()
            .expect("uncovered upper roots require generic pair replay");
        assert!(parents.lower.as_slice().is_empty());
        assert_eq!(
            parents.upper.as_slice(),
            roots.map(|root| PreparedReplayParent {
                side: ReplayClaimParentSide::Upper,
                coverage_root: root,
                representative_claim: root,
                lineage: ProjectionLineage::Original,
            }),
            "every uncovered root is retained once in canonical root order",
        );
        assert!(prepared.proof_event.incremental_replays.is_empty());
        let admissions = &machine.proof_store.replay_admissions[admissions_before..];
        assert_eq!(admissions.len(), 1);
        assert_eq!(admissions[0].disposition, ReplayAdmissionDisposition::NewSemantic);
        let accepted = admissions[0]
            .result
            .expect("the multi-root replay must retain its accepted result");
        assert!(machine.constraint_records.get(accepted.0 as usize).is_some());
    }

    fn cpk_7_admit_inert_constraint(
        machine: &mut ConstraintMachine,
        ordinal: u32,
        role: &str,
    ) -> ConstraintRecordId {
        let lower = machine.alloc_pos(Pos::Con(
            vec!["cpk-7-sided-parent".into(), role.into(), ordinal.to_string()],
            Vec::new(),
        ));
        let upper = machine.alloc_neg(Neg::Con(
            vec!["cpk-7-sided-result".into(), role.into(), ordinal.to_string()],
            Vec::new(),
        ));
        assert!(machine.enqueue_subtype(lower, ConstraintWeights::empty(), upper));
        let record = machine
            .constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("the inert fixture constraint is canonical");
        assert!(
            machine.queue.pop_back().is_some(),
            "the fixture removes only its own pending semantic work",
        );
        record
    }

    fn cpk_7_claimed_result(
        machine: &mut ConstraintMachine,
        ordinal: u32,
    ) -> (ConstraintRecordId, UpperReplayClaimId) {
        let producer = cpk_7_admit_inert_constraint(machine, ordinal, "producer");
        let claim_upper = machine.alloc_neg(Neg::Con(
            vec!["cpk-7-sided-claim".into(), ordinal.to_string()],
            Vec::new(),
        ));
        machine.add_upper_bound(
            TypeVar(73_300 + ordinal),
            claim_upper,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(producer),
        );
        let root = machine.bounds.root_claim_by_producer_constraint[&producer];

        let result = cpk_7_admit_inert_constraint(machine, ordinal, "result");
        let derivation = machine.intern_row_derivation(
            RowDerivationRule::UnweightedReduction,
            vec![RowDerivationParent::Constraint(producer)],
            Vec::new(),
        );
        let key = machine.constraint_records[result.0 as usize].key.clone();
        assert!(!machine.enqueue_row_derived_subtype(
            key.lower,
            key.weights,
            key.upper,
            derivation,
        ));
        machine.register_reduction_route_claim_parent(result, derivation, root);
        (result, root)
    }

    #[test]
    fn cpk_8b_reduction_route_dedup_is_owned_by_the_cpk_index() {
        let mut machine = cpk_machine();
        let (result, root) = cpk_7_claimed_result(&mut machine, 80_000);
        let derivation = machine.constraint_records[result.0 as usize].row_derivations[0];
        let occurrence_count = |machine: &ConstraintMachine| {
            machine
                .proof_store
                .occurrences
                .iter()
                .filter(|occurrence| {
                    occurrence.result == ProofResult::Semantic(SemanticFactRef::Constraint(result))
                        && occurrence.cause
                            == (ProofCause::ReductionRoute {
                                derivation,
                                parent_claim: root,
                            })
                })
                .count()
        };
        assert_eq!(occurrence_count(&machine), 1);

        machine
            .bounds
            .claim_parents_by_constraint
            .get_mut(&result)
            .expect("the first route wrote the Legacy mirror")
            .clear();
        machine.register_reduction_route_claim_parent(result, derivation, root);

        assert_eq!(
            occurrence_count(&machine),
            1,
            "CPK exact dedup must not depend on the corrupted Legacy mirror",
        );
        assert!(
            machine.bounds.claim_parents_by_constraint[&result].is_empty(),
            "a CPK duplicate must return before rewriting the Legacy mirror",
        );
    }

    #[test]
    fn cpk_projection_target_late_metadata_bootstraps_formula() {
        let mut machine = ConstraintMachine::new();
        let pivot = TypeVar(80_100);
        let source = TypeVar(80_101);
        let target = TypeVar(80_102);
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Var(target));
        let producer = cpk_7_admit_inert_constraint(&mut machine, 80_103, "target-late");

        machine.add_lower_bound(
            target,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );
        let lower_record = machine.bounds.of(target).unwrap().lower_record_ids()[0];
        assert_eq!(
            machine
                .proof_store
                .projection_lower_record_for_constraint(producer),
            None,
            "the replay exists before its target lower record is linked",
        );

        machine.add_upper_bound(
            pivot,
            upper,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(producer),
        );
        let root = machine.bounds.root_claim_by_producer_constraint[&producer];
        machine.add_lower_bound(
            pivot,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );

        let result = machine
            .constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("the natural replay admission is canonical");
        assert_eq!(machine.proof_store.replay_finite_map.len(), 1);
        let replay = machine.proof_store.replay_finite_map[0].carrier;
        assert_eq!(machine.proof_store.replay_finite_map[0].result, result);
        assert_eq!(
            machine.proof_store.replay_finite_map[0].upper_parents,
            vec![ReplayProofParent {
                side: ReplayClaimParentSide::Upper,
                coverage_root: root,
                representative_claim: root,
                lineage: ProjectionLineage::Original,
            }],
            "the typed replay occurrence exists before target metadata",
        );
        assert!(!machine.proof_store.projection_formulas.contains_key(&lower_record));
        assert!(
            machine.queue.pop_back().is_some(),
            "delay only the newly admitted replay constraint",
        );

        let epoch_before = machine.epoch.as_u64();
        let provenance_before = machine.provenance_epoch.as_u64();
        let journal = machine.activate_method_role_mutations();
        machine.add_lower_bound(
            target,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(result),
        );
        let published = machine.take_method_role_mutations();
        journal.finish();
        assert_eq!(machine.lower_record_for_constraint(result), Some(lower_record));
        assert_eq!(
            machine
                .proof_store
                .projection_lower_record_for_constraint(result),
            Some(lower_record),
            "target-late linkage is owned by the CPK target index",
        );
        assert_eq!(
            machine.epoch.as_u64(),
            epoch_before,
            "the already-projectable target publishes MetadataOnly",
        );
        assert!(machine.provenance_epoch.as_u64() > provenance_before);
        assert!(published.is_empty(), "MetadataOnly has no affected owner");

        let replay_clause = ProjectionClause::ReplayConjunction {
            support: SchemeProjectionProofSupport::Claimed(root),
            carrier: replay,
            lower: replay.lower,
            upper: replay.upper,
            attribution: Some(ProjectionLineage::ReplayConstraint),
        };
        let independent_carrier = ProjectionProofCarrier::Origin(OriginId::unknown_internal());
        let independent = SchemeProjectionProofSupport::Independent(independent_carrier);
        assert_eq!(
            machine.proof_store.projection_formulas[&lower_record],
            vec![
                ProjectionClause::Standalone {
                    support: independent,
                    attribution: None,
                },
                replay_clause,
            ],
            "target-late bootstrap preserves Standalone-before-ReplayConjunction order",
        );
        let (decision, _) = project_lower_for_test(&machine, lower_record);
        assert_eq!(
            decision,
            Ok(ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    uncovered_claims: vec![ProjectionClaimSupport {
                        coverage_root: root,
                        representative_claim: root,
                    }],
                    independent_supports: vec![independent_carrier],
                },
            }),
        );
    }

    #[test]
    fn cpk_evidence_and_trivial_replays_do_not_create_projection_formula() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let formulas_before = fixture.machine.proof_store.projection_formulas.clone();
        let supports_before = fixture.machine.proof_store.projection_supports.clone();
        let claimed_before = fixture
            .machine
            .proof_store
            .claimed_parents_by_lower_record
            .clone();
        let admissions_before = fixture.machine.proof_store.replay_admissions.len();
        let occurrences_before = fixture.machine.proof_store.occurrences.len();

        let evidence_constraint = SubtypeConstraintKey {
            lower: fixture.machine.alloc_pos(Pos::Var(TypeVar(80_200))),
            upper: fixture.machine.alloc_neg(Neg::Var(TypeVar(80_201))),
            weights: ConstraintWeights::empty(),
        };
        fixture
            .machine
            .apply_cpk_evidence_only_replay_for_test(evidence_constraint, fixture.carrier);
        let trivial_constraint = SubtypeConstraintKey {
            lower: fixture.machine.alloc_pos(Pos::Bot),
            upper: fixture.machine.constraint_records[fixture.result.0 as usize]
                .key
                .upper,
            weights: ConstraintWeights::empty(),
        };
        fixture
            .machine
            .apply_cpk_trivial_replay_for_test(trivial_constraint, fixture.carrier);

        let new_admissions = &fixture.machine.proof_store.replay_admissions[admissions_before..];
        assert_eq!(new_admissions.len(), 2);
        assert!(new_admissions.iter().any(|event| {
            event.result.is_none()
                && event.carrier == fixture.carrier
                && event.disposition == ReplayAdmissionDisposition::EvidenceOnly
        }));
        assert!(new_admissions.iter().any(|event| {
            event.result.is_none()
                && event.carrier == fixture.carrier
                && event.disposition == ReplayAdmissionDisposition::Trivial
        }));

        let new_occurrences = &fixture.machine.proof_store.occurrences[occurrences_before..];
        let evidence_records = new_occurrences
            .iter()
            .filter_map(|occurrence| match (&occurrence.result, &occurrence.cause) {
                (ProofResult::EvidenceBound(record), ProofCause::ReplayEvidence(carrier))
                    if *carrier == fixture.carrier =>
                {
                    Some(*record)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(evidence_records.len(), 2);
        assert!(new_occurrences.iter().any(|occurrence| matches!(
            (&occurrence.result, &occurrence.cause),
            (ProofResult::TrivialReplay(_), ProofCause::ReplayDrop(drop))
                if drop.derivation == fixture.carrier
        )));
        assert_eq!(fixture.machine.proof_store.projection_formulas, formulas_before);
        assert_eq!(fixture.machine.proof_store.projection_supports, supports_before);
        assert_eq!(
            fixture.machine.proof_store.claimed_parents_by_lower_record,
            claimed_before,
        );
        for record in evidence_records {
            let direction = fixture.machine.bounds.record(record).unwrap().direction();
            let (decision, _) = project_lower_for_test(&fixture.machine, record);
            match direction {
                BoundDirection::Lower => assert_eq!(decision, Ok(ProjectionDecision::Unclaimed)),
                BoundDirection::Upper => assert_eq!(
                    decision,
                    Err(ProofFailure::InvalidProjectionTarget {
                        record,
                        direction,
                        state: BoundRecordState::Evidence,
                    }),
                ),
            }
        }
    }

    fn cpk_premise_dependency_fixture(reverse_replay_order: bool) -> ConstraintMachine {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let alternate = BinaryReplayDerivation {
            rule: ReplayRule::UpperBoundAdded,
            ..fixture.carrier
        };
        let carriers = if reverse_replay_order {
            [alternate, fixture.carrier]
        } else {
            [fixture.carrier, alternate]
        };
        for carrier in carriers {
            fixture.machine.apply_cpk_replay_parent_arrival_for_test(
                fixture.result,
                carrier,
                fixture.coverage_root,
            );
        }
        assert_eq!(fixture.machine.proof_store.replay_finite_map.len(), 2);

        let dependent_owner = TypeVar(80_300);
        let dependent_endpoint = fixture.machine.alloc_pos(Pos::Con(
            vec!["cpk-premise-dependent".into()],
            Vec::new(),
        ));
        fixture.machine.add_lower_bound(
            dependent_owner,
            dependent_endpoint,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );
        let dependent = fixture
            .machine
            .bounds
            .of(dependent_owner)
            .expect("the dependent owner has bounds")
            .lower_record_ids()[0];
        let origin = ProjectionProofCarrier::Origin(OriginId::unknown_internal());
        let support = cpk_4_add_independent_support(&mut fixture.machine, dependent, origin);
        let admission = RecordProofClauseLinkAdmission::independent(
            support,
            RecordProofClause::DerivedUnary {
                carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                    parent: fixture.result,
                    rule: StructuralDerivationRule::FunctionReturn,
                }),
                premise: ProofPremise::Constraint(fixture.result),
            },
        );
        fixture
            .machine
            .register_cpk_projection_clause_for_test(dependent, admission);

        let before_duplicate = fixture.machine.logical_proof_snapshot().dependencies;
        fixture
            .machine
            .register_cpk_projection_clause_for_test(dependent, admission);
        assert_eq!(
            fixture.machine.logical_proof_snapshot().dependencies,
            before_duplicate,
            "duplicate registration cannot duplicate dependency edges",
        );

        for premise in [
            ProofPremise::Constraint(fixture.result),
            ProofPremise::Record(fixture.carrier.lower),
            ProofPremise::Record(fixture.carrier.upper),
        ] {
            let dependents = fixture
                .machine
                .proof_store
                .dependent_records(premise)
                .unwrap_or_else(|| panic!("missing exact replay premise {premise:?}"));
            assert!(dependents.contains(&dependent));
            assert_eq!(
                dependents.iter().filter(|record| **record == dependent).count(),
                1,
            );
        }
        fixture.machine
    }

    #[test]
    fn cpk_premise_dependency_chain_contains_exact_replay_endpoints() {
        let forward = cpk_premise_dependency_fixture(false);
        let reverse = cpk_premise_dependency_fixture(true);
        assert_eq!(
            forward.logical_proof_snapshot().dependencies,
            reverse.logical_proof_snapshot().dependencies,
            "premise admission order cannot perturb canonical provenance dependencies",
        );
    }

    fn cpk_7_direct_pair_route(
        machine: &ConstraintMachine,
        lower: BoundRecordId,
        owner: TypeVar,
        upper_endpoint: NegId,
    ) -> PreparedReplayRoute {
        let upper = machine
            .bounds
            .records
            .iter()
            .enumerate()
            .find_map(|(index, record)| {
                (record.owner() == owner
                    && record.endpoint() == BoundEndpoint::Upper(upper_endpoint))
                .then_some(BoundRecordId(index as u32))
            })
            .expect("the direct CPK route target must be a semantic upper record");
        machine
            .proof_store
            .prepare_replay_route(machine, lower, upper, &[])
            .expect("the direct CPK sided-parent route must validate")
    }

    #[test]
    fn cpk_7_shadow_pair_parents_preserve_lower_only_block() {
        let mut machine = ConstraintMachine::new();
        let (result, root) = cpk_7_claimed_result(&mut machine, 0);
        let owner = TypeVar(73_400);
        let lower = machine.constraint_records[result.0 as usize].key.lower;
        machine.add_lower_bound(
            owner,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(result),
        );
        let lower_record = machine.bounds.scheme_projection_lower_record_by_constraint[&result];

        let upper = machine.alloc_neg(Neg::Con(
            vec!["cpk-7-lower-only-upper".into()],
            Vec::new(),
        ));
        machine.add_upper_bound(
            owner,
            upper,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );

        let prepared = cpk_7_direct_pair_route(&machine, lower_record, owner, upper);
        assert_eq!(prepared.routing, ReplayRouting::Generic);
        let parents = prepared
            .proof_event
            .pair_replay
            .expect("the no-claim upper still requires generic pair replay");
        let expected = PreparedReplayParent {
            side: ReplayClaimParentSide::Lower,
            coverage_root: root,
            representative_claim: root,
            lineage: ProjectionLineage::Original,
        };
        assert_eq!(parents.lower.as_slice(), [expected]);
        assert!(parents.upper.as_slice().is_empty());
        assert_eq!(parents.iter().copied().collect::<Vec<_>>(), vec![expected]);
    }

    #[test]
    fn cpk_7_shadow_pair_parents_preserve_upper_only_block() {
        let mut machine = ConstraintMachine::new();
        let owner = TypeVar(73_401);
        let lower = machine.alloc_pos(Pos::Con(
            vec!["cpk-7-upper-only-lower".into()],
            Vec::new(),
        ));
        machine.add_lower_bound(
            owner,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );
        let lower_record = machine
            .bounds
            .records
            .iter()
            .enumerate()
            .find_map(|(index, record)| {
                (record.owner() == owner && record.endpoint() == BoundEndpoint::Lower(lower))
                    .then_some(BoundRecordId(index as u32))
            })
            .expect("the lower-only frontier record exists");
        let producer = cpk_7_admit_inert_constraint(&mut machine, 1, "upper-only");

        let upper = machine.alloc_neg(Neg::Con(
            vec!["cpk-7-upper-only-upper".into()],
            Vec::new(),
        ));
        machine.add_upper_bound(
            owner,
            upper,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(producer),
        );
        let root = machine.bounds.root_claim_by_producer_constraint[&producer];

        let prepared = cpk_7_direct_pair_route(&machine, lower_record, owner, upper);
        assert_eq!(prepared.routing, ReplayRouting::Generic);
        let parents = prepared
            .proof_event
            .pair_replay
            .expect("the uncovered upper claim requires generic pair replay");
        let expected = PreparedReplayParent {
            side: ReplayClaimParentSide::Upper,
            coverage_root: root,
            representative_claim: root,
            lineage: ProjectionLineage::Original,
        };
        assert!(parents.lower.as_slice().is_empty());
        assert_eq!(parents.upper.as_slice(), [expected]);
        assert_eq!(parents.iter().copied().collect::<Vec<_>>(), vec![expected]);
    }

    #[test]
    fn cpk_7_shadow_pair_parents_preserve_lower_then_upper_blocks() {
        let mut machine = ConstraintMachine::new();
        let (result, root) = cpk_7_claimed_result(&mut machine, 2);
        let owner = TypeVar(73_402);
        let lower = machine.constraint_records[result.0 as usize].key.lower;
        machine.add_lower_bound(
            owner,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(result),
        );
        let lower_record = machine.bounds.scheme_projection_lower_record_by_constraint[&result];

        let upper = machine.alloc_neg(Neg::Con(
            vec!["cpk-7-mixed-side-upper".into()],
            Vec::new(),
        ));
        machine.add_upper_bound(
            owner,
            upper,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(result),
        );

        let prepared = cpk_7_direct_pair_route(&machine, lower_record, owner, upper);
        assert_eq!(prepared.routing, ReplayRouting::Generic);
        let parents = prepared
            .proof_event
            .pair_replay
            .expect("the mixed-side fixture requires generic pair replay");
        let upper_parent = parents
            .upper
            .as_slice()
            .first()
            .copied()
            .expect("the materialized result claim remains an upper parent");
        assert_eq!(upper_parent.side, ReplayClaimParentSide::Upper);
        assert_eq!(upper_parent.coverage_root, root);
        assert_ne!(upper_parent.representative_claim, root);
        assert_eq!(
            upper_parent.lineage,
            ProjectionLineage::ReductionRouteConstraint,
        );
        let lower_parent = PreparedReplayParent {
            side: ReplayClaimParentSide::Lower,
            coverage_root: upper_parent.coverage_root,
            representative_claim: upper_parent.representative_claim,
            lineage: upper_parent.lineage,
        };
        assert_eq!(parents.lower.as_slice(), [lower_parent]);
        assert_eq!(parents.upper.as_slice(), [upper_parent]);
        assert_eq!(
            parents.iter().copied().collect::<Vec<_>>(),
            vec![lower_parent, upper_parent],
            "the same writer-fixed representative remains distinct across sides, with the complete lower block before the upper block",
        );
    }

    #[test]
    fn cpk_5_generic_route_matches_legacy_and_counts() {
        let mut fixture = cpk_3_replay_admission_fixture();
        cpk_5_trigger_lower_route(&mut fixture, false);
        let snapshot = fixture.machine.proof_store.clone();

        assert!(snapshot.replay_route_observations.borrow().iter().any(|observation| {
            observation.legacy == ReplayRouting::Generic
                && observation.shadow == ReplayRouting::Generic
                && observation.legacy_prepared == observation.shadow_prepared
        }));
        assert_cpk_5_event_count_parity(&snapshot);
    }

    #[test]
    #[should_panic(expected = "CPK-7 replay routing shadow preflight failed")]
    fn cpk_7_shadow_oracle_rejects_claim_index_corruption() {
        let mut fixture = cpk_3_replay_admission_fixture_with_authority(
            ProofReadAuthority::LegacyRollback(ProofFailure::ResourceExhausted {
                operation: ProofOperation::PrepareReplayRoutePreflight,
            }),
        );
        assert_eq!(
            fixture.machine.bounds.upper_replay_claims.len(),
            fixture.machine.proof_store.upper_claims.len(),
            "the injected fault must preserve the outer claim census",
        );
        assert!(
            fixture
                .machine
                .proof_store
                .upper_claim_index
                .remove(&fixture.coverage_root)
                .is_some(),
            "the fixture must corrupt an existing CPK claim index entry",
        );

        cpk_5_trigger_lower_route(&mut fixture, false);
    }

    #[test]
    fn cpk_7_cpk_authority_preflight_rejects_claim_index_corruption() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        assert_eq!(fixture.machine.proof_read_authority(), &ProofReadAuthority::Cpk);
        let lower = fixture.machine.alloc_pos(Pos::Con(
            vec!["cpk-7-corrupt-index-lower".into()],
            Vec::new(),
        ));
        fixture.machine.add_lower_bound(
            fixture.parent_owner,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );
        let lower_record = fixture
            .machine
            .bounds
            .of(fixture.parent_owner)
            .expect("the parent owner must retain the new lower")
            .lower_record_ids()
            .iter()
            .copied()
            .find(|record| {
                fixture
                    .machine
                    .bounds
                    .record(*record)
                    .is_some_and(|record| record.endpoint() == BoundEndpoint::Lower(lower))
            })
            .expect("the production lower writer must expose its semantic record");
        assert!(
            fixture
                .machine
                .proof_store
                .upper_claim_index
                .remove(&fixture.coverage_root)
                .is_some(),
            "the fixture must corrupt an existing CPK claim index entry",
        );

        let failure = fixture
            .machine
            .proof_store
            .prepare_replay_route(
                &fixture.machine,
                lower_record,
                fixture.parent_record,
                &[],
            )
            .expect_err("CPK authority preflight must reject internal claim-index corruption");
        assert!(matches!(
            failure,
            ProofFailure::DanglingProofReference {
                target: ProofFactRef::UpperClaim(claim),
                ..
            } if claim == fixture.coverage_root
        ));
    }

    #[test]
    fn cpk_8a_cpk_terminal_failure_telemetry_counts_first_organic_failure_once() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        assert!(
            fixture
                .machine
                .proof_store
                .upper_claim_index
                .remove(&fixture.coverage_root)
                .is_some(),
            "the fixture must corrupt an existing CPK claim index entry",
        );

        let ((), telemetry) = capture_replay_soak_test_events(|| {
            cpk_5_trigger_lower_route(&mut fixture, false);
            cpk_5_trigger_lower_route(&mut fixture, true);
        });

        assert!(matches!(
            fixture.machine.proof_terminal_failure(),
            Some(ProofFailure::DanglingProofReference { .. }),
        ));
        assert_eq!(
            telemetry.proof_terminal_failures(
                ReplaySoakEventOrigin::Organic,
                ProofOperation::PrepareReplayRouteBatch,
            ),
            1,
            "the sticky terminal failure must be counted only once",
        );
        assert_eq!(
            telemetry.proof_terminal_failures(
                ReplaySoakEventOrigin::IntentionalTestInjection,
                ProofOperation::PrepareReplayRouteBatch,
            ),
            0,
        );
    }

    #[test]
    fn cpk_terminal_failure_stops_drain_before_the_next_queued_work() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let first_source = TypeVar(91_102);
        let sentinel_source = TypeVar(91_103);
        let sentinel_target = TypeVar(91_104);
        let origin = OriginId::unknown_internal();

        let first_lower = fixture.machine.alloc_pos(Pos::Var(first_source));
        let first_upper = fixture.machine.alloc_neg(Neg::Var(fixture.parent_owner));
        assert!(fixture.machine.enqueue_root_subtype(
            first_lower,
            ConstraintWeights::empty(),
            first_upper,
            origin,
        ));
        let sentinel_lower = fixture.machine.alloc_pos(Pos::Var(sentinel_source));
        let sentinel_upper = fixture.machine.alloc_neg(Neg::Var(sentinel_target));
        assert!(fixture.machine.enqueue_root_subtype(
            sentinel_lower,
            ConstraintWeights::empty(),
            sentinel_upper,
            origin,
        ));
        let sentinel = fixture
            .machine
            .constraint_record_id(sentinel_lower, ConstraintWeights::empty(), sentinel_upper)
            .expect("the sentinel work item is queued");
        assert_eq!(
            fixture.machine.queue.len(),
            2,
            "the failure trigger precedes a real sentinel"
        );
        assert!(
            fixture
                .machine
                .proof_store
                .upper_claim_index
                .remove(&fixture.coverage_root)
                .is_some(),
            "the fixture must corrupt an existing CPK claim index entry",
        );

        with_intentional_replay_soak_test_injection(|| fixture.machine.drain());

        assert!(matches!(
            fixture.machine.proof_terminal_failure(),
            Some(ProofFailure::DanglingProofReference {
                target: ProofFactRef::UpperClaim(claim),
                ..
            }) if claim == fixture.coverage_root
        ));
        assert_eq!(
            fixture.machine.queue.front(),
            Some(&ConstraintWork::Subtype(sentinel))
        );
        assert_eq!(
            fixture.machine.queue.len(),
            1,
            "only the failing work item is drained"
        );
        assert!(
            fixture.machine.bounds.of(sentinel_target).is_none(),
            "the queued sentinel must not mutate bounds after CPK terminal failure",
        );
    }

    #[test]
    fn cpk_8a_successful_cpk_route_emits_no_proof_failure_telemetry() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let ((), telemetry) = capture_replay_soak_test_events(|| {
            cpk_5_trigger_lower_route(&mut fixture, false);
        });

        assert_eq!(
            telemetry.total_for_origin(ReplaySoakEventOrigin::Organic),
            0,
            "a normal successful CPK route must not resemble an organic soak failure",
        );
        assert_eq!(
            telemetry.total_for_origin(ReplaySoakEventOrigin::IntentionalTestInjection),
            0,
        );
    }

    #[test]
    fn cpk_5_incremental_only_and_skip_routes_match_legacy() {
        for (lower_is_var, expected) in [
            (true, ReplayRouting::IncrementalOnly),
            (false, ReplayRouting::SkipAlreadyCovered),
        ] {
            let mut fixture = cpk_3_replay_admission_fixture();
            fixture.machine.insert_scheme_projection_live_coverage_state(
                fixture.coverage_root,
                UnweightedRowReductionRecordId(41_000),
            );
            cpk_5_trigger_lower_route(&mut fixture, lower_is_var);
            let parent_record = fixture.parent_record;
            let machine = fixture.machine;
            let snapshot = machine.proof_store.clone();

            assert!(snapshot.replay_route_observations.borrow().iter().any(|observation| {
                observation.upper == parent_record
                    && observation.legacy == expected
                    && observation.shadow == expected
                    && observation.legacy_prepared == observation.shadow_prepared
            }));
            assert_cpk_5_event_count_parity(&snapshot);
            assert_eq!(
                machine.timing.lower_replay_accepted + machine.timing.upper_replay_accepted,
                snapshot
                    .replay_event_observations
                    .borrow()
                    .iter()
                    .map(|observation| observation.legacy_accepted_count)
                    .sum::<usize>(),
            );
        }
    }

    #[test]
    fn cpk_5_routing_is_invariant_across_same_root_parent_arrival_orders() {
        let permutations = [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ];
        let mut routing = Vec::new();
        for order in permutations {
            let mut fixture = cpk_3_replay_admission_fixture();
            let claims = [
                fixture.coverage_root,
                add_same_root_replay_claim(
                    &mut fixture,
                    TypeVar(42_000),
                    ConstraintRecordId(42_000),
                ),
                add_same_root_replay_claim(
                    &mut fixture,
                    TypeVar(42_001),
                    ConstraintRecordId(42_001),
                ),
            ];
            for index in order {
                fixture.machine.apply_cpk_replay_parent_arrival_for_test(
                    fixture.result,
                    fixture.carrier,
                    claims[index],
                );
            }
            cpk_5_trigger_lower_route(&mut fixture, false);
            let result = fixture.result;
            let root = fixture.coverage_root;
            let snapshot = fixture.machine.proof_store.clone();
            assert_eq!(
                snapshot.first_replay_witnesses[&(result, root)].representative_claim,
                snapshot.replay_finite_map
                    .iter()
                    .find(|occurrence| occurrence.result == result)
                    .unwrap()
                    .lower_parents[0]
                    .representative_claim,
            );
            assert_cpk_5_event_count_parity(&snapshot);
            routing.push(
                snapshot
                    .replay_route_observations
                    .borrow()
                    .iter()
                    .map(|observation| {
                        assert_eq!(observation.legacy_prepared, observation.shadow_prepared);
                        observation.shadow_prepared.clone()
                    })
                    .collect::<Vec<_>>(),
            );
        }
        assert!(routing.windows(2).all(|pair| pair[0] == pair[1]));
    }

    #[test]
    fn cpk_2_non_replay_proof_events_match_frozen_contract() {
        let mut machine = ConstraintMachine::new();
            let origin = OriginId::unknown_internal();
            let lower = machine.alloc_pos(Pos::Var(TypeVar(10)));
            let upper = machine.alloc_neg(Neg::Var(TypeVar(11)));
            machine.subtype(lower, upper, origin);
            let parent = machine
                .constraint_record_id(lower, ConstraintWeights::empty(), upper)
                .expect("root constraint");

            let structural_lower = machine.alloc_pos(Pos::Var(TypeVar(12)));
            let structural_upper = machine.alloc_neg(Neg::Var(TypeVar(13)));
            assert!(machine.enqueue_derived_subtype(
                structural_lower,
                ConstraintWeights::empty(),
                structural_upper,
                parent,
                StructuralDerivationRule::FunctionReturn,
            ));
            machine.drain();
            let structural = machine
                .constraint_record_id(
                    structural_lower,
                    ConstraintWeights::empty(),
                    structural_upper,
                )
                .expect("structural constraint");

            let row = machine.intern_row_derivation(
                RowDerivationRule::RowItemMatch,
                vec![RowDerivationParent::Constraint(parent)],
                Vec::new(),
            );
            let row_lower = machine.alloc_pos(Pos::Var(TypeVar(14)));
            let row_upper = machine.alloc_neg(Neg::Var(TypeVar(15)));
            assert!(machine.enqueue_row_derived_subtype(
                row_lower,
                ConstraintWeights::empty(),
                row_upper,
                row,
            ));
            machine.drain();

            machine.subtract_fact(TypeVar(16), SubtractId(7), Subtractability::All);

            let instantiation = machine.intern_scheme_instantiation(
                GeneralizedSchemeRecordId(0),
                DefId(0),
                DefId(1),
                TypeVar(17),
                ProvenanceCompleteness::Complete,
            );
            let derivation = SchemeInstantiationDerivation {
                instantiation,
                source_witness: GeneralizedSchemeWitnessId(0),
                path: GeneralizedTypePath::default(),
            };
            machine.merge_scheme_instantiation_routes_for_test(
                structural,
                vec![
                    SchemeInstantiationRoute {
                        derivation: derivation.clone(),
                        remaining: GeneralizedTypePath::default(),
                    },
                    SchemeInstantiationRoute {
                        derivation,
                        remaining: GeneralizedTypePath(vec![
                            GeneralizedTypePathStep::FunctionReturn,
                        ]),
                    },
                ],
            );

            let alternate = machine.alloc_source_boundary(ConstraintOriginKind::Annotation);
            assert!(machine.attach_root_origin_to_existing_subtype(
                lower,
                upper,
                alternate.origin,
            ));
            let before_duplicate = machine.proof_store.occurrences.len();
            assert!(!machine.attach_root_origin_to_existing_subtype(
                lower,
                upper,
                alternate.origin,
            ));
            assert_eq!(
                machine.proof_store.occurrences.len(),
                before_duplicate,
                "an exact metadata duplicate must not create an occurrence",
            );
        let snapshot = machine.proof_store.clone();
        assert_eq!(snapshot.occurrences.len(), 21);
        assert_eq!(
            snapshot
                .occurrences
                .iter()
                .map(|occurrence| occurrence.event)
                .collect::<Vec<_>>(),
            (0..21).collect::<Vec<_>>(),
        );
        assert!(snapshot
            .occurrences
            .iter()
            .all(|occurrence| occurrence.completeness == ProvenanceCompleteness::Complete));
        let assert_occurrence =
            |event: usize, result: ProofResult, cause: ProofCause, parents: Vec<ProofParent>| {
                let occurrence = &snapshot.occurrences[event];
                assert_eq!(occurrence.result, result, "event {event} result");
                assert_eq!(occurrence.cause, cause, "event {event} cause");
                assert_eq!(occurrence.parents, parents, "event {event} parents");
            };
        let semantic_constraint = |id| {
            ProofResult::Semantic(SemanticFactRef::Constraint(ConstraintRecordId(id)))
        };
        let semantic_bound = |id| ProofResult::Semantic(SemanticFactRef::Bound(BoundRecordId(id)));
        let constraint_parent = |id| {
            vec![ProofParent::Semantic(SemanticFactRef::Constraint(
                ConstraintRecordId(id),
            ))]
        };
        assert_occurrence(
            0,
            semantic_constraint(0),
            ProofCause::Root(origin),
            vec![ProofParent::Origin(origin)],
        );
        for (event, bound, constraint) in [(1, 0, 0), (3, 1, 0), (6, 2, 1), (8, 3, 1), (12, 4, 2), (14, 5, 2)] {
            assert_occurrence(
                event,
                semantic_bound(bound),
                ProofCause::Bound(BoundDerivation::Constraint(ConstraintRecordId(constraint))),
                constraint_parent(constraint),
            );
        }
        assert_occurrence(
            5,
            semantic_constraint(1),
            ProofCause::Structural(StructuralDerivation {
                parent,
                rule: StructuralDerivationRule::FunctionReturn,
            }),
            constraint_parent(0),
        );
        assert_occurrence(
            10,
            ProofResult::Semantic(SemanticFactRef::RowDerivation(row)),
            ProofCause::RowDefinition(RowDerivation {
                rule: RowDerivationRule::RowItemMatch,
                parents: vec![RowDerivationParent::Constraint(parent)],
                retained_items: Vec::new(),
            }),
            constraint_parent(0),
        );
        assert_occurrence(
            11,
            semantic_constraint(2),
            ProofCause::RowConstraint(row),
            vec![ProofParent::Semantic(SemanticFactRef::RowDerivation(row))],
        );
        assert_occurrence(
            16,
            ProofResult::Semantic(SemanticFactRef::Subtract(SubtractFactRecordId(0))),
            ProofCause::Subtract(SubtractFactDerivation::Internal(origin)),
            vec![ProofParent::Origin(origin)],
        );
        assert_occurrence(
            17,
            ProofResult::Semantic(SemanticFactRef::SchemeInstantiation(instantiation)),
            ProofCause::SchemeInstantiationRecord(SchemeInstantiationRecord {
                source: GeneralizedSchemeRecordId(0),
                owner: DefId(0),
                target: DefId(1),
                use_value: TypeVar(17),
                completeness: ProvenanceCompleteness::Complete,
            }),
            Vec::new(),
        );
        let instantiation_derivation = SchemeInstantiationDerivation {
            instantiation,
            source_witness: GeneralizedSchemeWitnessId(0),
            path: GeneralizedTypePath::default(),
        };
        let instantiation_parents = vec![
            ProofParent::Semantic(SemanticFactRef::SchemeInstantiation(instantiation)),
            ProofParent::GeneralizedWitness(GeneralizedSchemeWitnessId(0)),
        ];
        assert_occurrence(
            18,
            semantic_constraint(1),
            ProofCause::SchemeInstantiationDerivation(instantiation_derivation.clone()),
            instantiation_parents.clone(),
        );
        assert_occurrence(
            19,
            semantic_constraint(1),
            ProofCause::SchemeInstantiationRoute(SchemeInstantiationRoute {
                derivation: instantiation_derivation,
                remaining: GeneralizedTypePath(vec![GeneralizedTypePathStep::FunctionReturn]),
            }),
            instantiation_parents,
        );
        assert_occurrence(
            20,
            semantic_constraint(0),
            ProofCause::Root(alternate.origin),
            vec![ProofParent::Origin(alternate.origin)],
        );
        for (event, disposition, direction, owner, endpoint, constraint, bound) in [
            (2, 0, BoundDirection::Lower, TypeVar(11), BoundEndpoint::Lower(PosId(0)), 0, 0),
            (4, 1, BoundDirection::Upper, TypeVar(10), BoundEndpoint::Upper(NegId(0)), 0, 1),
            (7, 2, BoundDirection::Lower, TypeVar(13), BoundEndpoint::Lower(PosId(1)), 1, 2),
            (9, 3, BoundDirection::Upper, TypeVar(12), BoundEndpoint::Upper(NegId(1)), 1, 3),
            (13, 4, BoundDirection::Lower, TypeVar(15), BoundEndpoint::Lower(PosId(2)), 2, 4),
            (15, 5, BoundDirection::Upper, TypeVar(14), BoundEndpoint::Upper(NegId(2)), 2, 5),
        ] {
            let occurrence = &snapshot.occurrences[event];
            assert_eq!(
                occurrence.result,
                ProofResult::BoundDisposition(BoundDispositionRecordId(disposition)),
            );
            let ProofCause::BoundDisposition(actual) = &occurrence.cause else {
                panic!("event {event} must retain its bound disposition");
            };
            assert_eq!(actual.direction, direction);
            assert_eq!(actual.owner, owner);
            assert_eq!(actual.endpoint, endpoint);
            assert_eq!(actual.weights, ConstraintWeights::empty());
            assert_eq!(
                actual.derivation,
                Some(BoundDerivation::Constraint(ConstraintRecordId(constraint))),
            );
            assert_eq!(actual.disposition, BoundDisposition::Inserted(BoundRecordId(bound)));
            assert!(occurrence.parents.is_empty());
        }
        for predicate in [
            snapshot
                .occurrences
                .iter()
                .any(|entry| matches!(entry.cause, ProofCause::Root(_))),
            snapshot
                .occurrences
                .iter()
                .any(|entry| matches!(entry.cause, ProofCause::Structural(_))),
            snapshot.occurrences.iter().any(|entry| {
                matches!(
                    entry.cause,
                    ProofCause::RowDefinition(_) | ProofCause::RowConstraint(_)
                )
            }),
            snapshot
                .occurrences
                .iter()
                .any(|entry| matches!(entry.cause, ProofCause::Bound(_))),
            snapshot
                .occurrences
                .iter()
                .any(|entry| matches!(entry.cause, ProofCause::Subtract(_))),
            snapshot
                .occurrences
                .iter()
                .any(|entry| matches!(entry.cause, ProofCause::SchemeInstantiationRecord(_))),
            snapshot.occurrences.iter().any(|entry| {
                matches!(entry.cause, ProofCause::SchemeInstantiationDerivation(_))
            }),
            snapshot
                .occurrences
                .iter()
                .any(|entry| matches!(entry.cause, ProofCause::SchemeInstantiationRoute(_))),
        ] {
            assert!(predicate, "each CPK-2 non-replay source must be exercised");
        }
        assert!(snapshot.replay_coverage_connected);
    }

    #[test]
    fn cpk_1_semantic_view_and_legacy_payload_match_embedded_records() {
        let (mut machine, lower, upper) =
            with_semantic_execution_snapshot_capture_for_new_machines(|| {
                let mut machine = ConstraintMachine::new();
                let source = TypeVar(0);
                let target = TypeVar(1);
                let lower = machine.alloc_pos(Pos::Var(source));
                let upper = machine.alloc_neg(Neg::Var(target));
                machine.subtype(lower, upper, OriginId::unknown_internal());
                (machine, lower, upper)
            });
        let source = TypeVar(0);
        let target = TypeVar(1);

        let constraint = machine
            .constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("fixture constraint is canonical");
        let lower_record = machine.bounds.of(target).unwrap().lower_record_ids()[0];
        let upper_record = machine.bounds.of(source).unwrap().upper_record_ids()[0];

        let semantic_constraint = machine.constraint(constraint).expect("semantic constraint");
        assert_eq!(
            semantic_constraint.key(),
            &machine.constraint_records[constraint.0 as usize].key
        );
        {
            let semantic_bound = machine.bound(lower_record).expect("semantic bound");
            let direct_bound = &machine.bounds.records[lower_record.0 as usize];
            assert_eq!(semantic_bound.direction(), direct_bound.direction);
            assert_eq!(semantic_bound.owner(), direct_bound.owner);
            assert_eq!(semantic_bound.endpoint(), direct_bound.endpoint);
            assert_eq!(semantic_bound.weights(), &direct_bound.weights);
            assert_eq!(semantic_bound.state(), direct_bound.state);
        }

        let row_id = UnweightedRowReductionRecordId(0);
        machine
            .unweighted_row_reduction_records
            .push(UnweightedRowReductionRecord {
                source,
                producer_constraint: Some(constraint),
                original_items: vec![upper],
                original_tail: upper,
                original_upper: upper,
                consumed_items: Vec::new(),
                remaining_items: vec![upper],
                current_reduced_upper: UnweightedRowReductionMaterialization {
                    endpoint: upper,
                    record: upper_record,
                },
                processed_lower_records: FxHashSet::from_iter([lower_record]),
                provenance_head: RowDerivationId(0),
            });
        let scc = crate::scc::SccMachine::new();
        let semantic_before = machine.semantic_execution_snapshot(
            SccExecutionSnapshot::new(scc.stats(), Vec::new()),
            SemanticOutputSnapshot::default(),
        );
        let semantic_row = machine
            .row_reduction(row_id)
            .expect("semantic row reduction");
        assert_eq!(semantic_row.source(), source);
        assert_eq!(semantic_row.producer_constraint(), Some(constraint));
        assert_eq!(semantic_row.original_items(), &[upper]);
        assert_eq!(semantic_row.original_tail(), upper);
        assert_eq!(semantic_row.original_upper(), upper);
        assert!(semantic_row.consumed_items().is_empty());
        assert_eq!(semantic_row.remaining_items(), &[upper]);
        assert_eq!(semantic_row.current_reduced_upper(), upper);
        assert_eq!(semantic_row.current_record(), upper_record);
        assert!(
            semantic_row
                .processed_lower_records()
                .contains(&lower_record)
        );

        let legacy = LegacyProofBackend::new(&machine);
        let constraint_payload = legacy
            .constraint_payload(constraint)
            .expect("legacy constraint payload");
        let direct_constraint = &machine.constraint_records[constraint.0 as usize];
        assert_eq!(
            constraint_payload.root_origins(),
            direct_constraint.root_origins
        );
        assert_eq!(
            constraint_payload.structural_derivations(),
            direct_constraint.structural_derivations
        );
        assert_eq!(
            constraint_payload.row_derivations(),
            direct_constraint.row_derivations
        );
        assert_eq!(
            constraint_payload.replay_derivations(),
            direct_constraint.replay_derivations
        );
        assert_eq!(
            constraint_payload.scheme_instantiation_derivations(),
            direct_constraint.scheme_instantiation_derivations
        );
        assert_eq!(
            constraint_payload.scheme_instantiation_routes(),
            direct_constraint.scheme_instantiation_routes
        );
        assert_eq!(
            constraint_payload.canonicalization_dispositions(),
            direct_constraint.canonicalization_dispositions
        );
        assert_eq!(
            constraint_payload.replay_provenance(),
            direct_constraint.replay_provenance
        );
        let bound_payload = legacy
            .bound_payload(lower_record)
            .expect("legacy bound payload");
        let direct_bound = &machine.bounds.records[lower_record.0 as usize];
        assert_eq!(bound_payload.derivations(), direct_bound.derivations);
        assert_eq!(bound_payload.disposition(), direct_bound.disposition);

        let null = NullProofBackend;
        assert!(null.constraint_payload(constraint).is_none());
        assert!(null.bound_payload(lower_record).is_none());
        assert!(machine.constraint(ConstraintRecordId(u32::MAX)).is_none());
        assert!(machine.bound(BoundRecordId(u32::MAX)).is_none());
        assert!(
            machine
                .row_reduction(UnweightedRowReductionRecordId(u32::MAX))
                .is_none()
        );

        let facts = [
            SemanticFactRef::Constraint(constraint),
            SemanticFactRef::Bound(lower_record),
            SemanticFactRef::RowReduction(row_id),
        ];
        assert_eq!(facts.len(), 3);

        let scc = crate::scc::SccMachine::new();
        let semantic_after = machine.semantic_execution_snapshot(
            SccExecutionSnapshot::new(scc.stats(), Vec::new()),
            SemanticOutputSnapshot::default(),
        );
        assert_eq!(
            semantic_after, semantic_before,
            "reading either seam must not change queue, records, epochs, events, or output"
        );
    }
}
