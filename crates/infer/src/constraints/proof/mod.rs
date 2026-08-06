//! Constraint Proof Kernel boundary.
//!
//! CPK-1 defines read-only adapters over current semantic records and their legacy proof payloads.
//! CPK-2 adds a test-only occurrence shadow below that seam. It does not own production state,
//! receive replay occurrences, or influence worklist identity and ordering.

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UpperClaimOccurrence {
    pub(crate) claim: UpperReplayClaimId,
    pub(crate) coverage_root: UpperReplayClaimId,
    pub(crate) lineage: ProjectionLineage,
    pub(crate) producer: ConstraintRecordId,
    pub(crate) current_record: BoundRecordId,
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
    claims_by_upper_record: FxHashMap<BoundRecordId, Vec<UpperReplayClaimId>>,
    pub(crate) row_reductions: Vec<RowReductionOccurrence>,
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
            claims_by_upper_record: FxHashMap::default(),
            row_reductions: Vec::new(),
            live_coverage: FxHashSet::default(),
            live_states_by_coverage_root: FxHashMap::default(),
            replay_coverage_connected: true,
            projection_supports: FxHashMap::default(),
            claimed_parents_by_lower_record: FxHashMap::default(),
            projection_formulas: FxHashMap::default(),
            #[cfg(test)]
            replay_index_record_comparisons: Cell::new(0),
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

#[cfg(test)]
thread_local! {
    static SHADOW_CAPTURE_DEPTH: Cell<usize> = const { Cell::new(0) };
    static SHADOW_STORE: RefCell<ProofOccurrenceStore> = RefCell::default();
}

#[cfg(test)]
pub(crate) fn capture_proof_occurrence_shadow<R>(
    f: impl FnOnce() -> R,
) -> (R, ProofOccurrenceStore) {
    struct Reset(usize);
    impl Drop for Reset {
        fn drop(&mut self) {
            SHADOW_CAPTURE_DEPTH.set(self.0);
        }
    }

    let previous = SHADOW_CAPTURE_DEPTH.get();
    assert_eq!(previous, 0, "CPK proof shadow capture is not nestable");
    SHADOW_STORE.with(|store| *store.borrow_mut() = ProofOccurrenceStore::default());
    SHADOW_CAPTURE_DEPTH.set(1);
    let _reset = Reset(previous);
    let value = f();
    let snapshot = SHADOW_STORE.with(|store| store.borrow().clone());
    (value, snapshot)
}

#[cfg(test)]
pub(crate) fn proof_occurrence_shadow_is_active() -> bool {
    SHADOW_CAPTURE_DEPTH.get() != 0
}

#[cfg(test)]
fn proof_occurrence_shadow_len() -> usize {
    SHADOW_STORE.with(|store| store.borrow().occurrences.len())
}

impl ProofOccurrenceStore {
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

#[cfg(test)]
fn record_shadow_occurrence(
    result: ProofResult,
    cause: ProofCause,
    parents: Vec<ProofParent>,
    completeness: ProvenanceCompleteness,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| {
        store
            .borrow_mut()
            .record_occurrence(result, cause, parents, completeness);
    });
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

#[cfg(test)]
pub(super) fn record_upper_claim_shadow(claim: &UpperReplayClaim) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| store.borrow_mut().record_upper_claim(claim));
}

#[cfg(test)]
pub(super) fn update_upper_claim_shadow(claim: &UpperReplayClaim) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| store.borrow_mut().update_upper_claim(claim));
}

impl ProofOccurrenceStore {
    pub(super) fn record_upper_claim(&mut self, claim: &UpperReplayClaim) {
        if let Some(index) = self.upper_claim_index.get(&claim.id).copied() {
            let old_record = self.upper_claims[index].current_record;
            if old_record != claim.current_record {
                self.remove_claim_from_upper_record_index(old_record, claim.id);
                self.upper_claims[index].current_record = claim.current_record;
                self.insert_claim_into_upper_record_index(claim.current_record, claim.id);
            }
            return;
        }
        let index = self.upper_claims.len();
        self.upper_claims.push(UpperClaimOccurrence {
            claim: claim.id,
            coverage_root: claim.coverage_root,
            lineage: projection_lineage(claim.lineage),
            producer: claim.producer_constraint,
            current_record: claim.current_record,
        });
        self.upper_claim_index.insert(claim.id, index);
        self.insert_claim_into_upper_record_index(claim.current_record, claim.id);
    }

    pub(super) fn update_upper_claim(&mut self, claim: &UpperReplayClaim) {
        let index = self
            .upper_claim_index
            .get(&claim.id)
            .copied()
            .expect("a moved upper claim must already exist in the CPK store");
        let old_record = self.upper_claims[index].current_record;
        if old_record == claim.current_record {
            return;
        }
        self.remove_claim_from_upper_record_index(old_record, claim.id);
        self.upper_claims[index].current_record = claim.current_record;
        self.insert_claim_into_upper_record_index(claim.current_record, claim.id);
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

#[cfg(test)]
pub(super) fn record_projection_supports_shadow(
    lower_record: BoundRecordId,
    proofs: &[SchemeProjectionProof],
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| {
        store
            .borrow_mut()
            .record_projection_supports(lower_record, proofs)
    });
}

#[cfg(test)]
pub(super) fn record_projection_clause_shadow(
    lower_record: BoundRecordId,
    admission: RecordProofClauseLinkAdmission,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| {
        store
            .borrow_mut()
            .record_projection_clause(lower_record, admission)
    });
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
            self.validate_incremental_route_target(lower, upper, upper_endpoint, route, upper_ids)?;
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
        if !requires_generic {
            for route in incremental_routes {
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
        upper_endpoint: NegId,
        route: &IncrementalRouteKey,
        upper_claims: &[UpperReplayClaimId],
    ) -> Result<(), ProofFailure> {
        if route.upper_record != upper || route.upper != upper_endpoint {
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
            ReplayRouting::Generic => {
                prepared.proof_event.pair_replay.is_some()
                    && prepared.proof_event.incremental_replays.is_empty()
            }
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
    let mut seen = FxHashSet::default();
    let incremental_replays = if routing == ReplayRouting::Generic {
        Vec::new()
    } else {
        incremental_routes
            .iter()
            .copied()
            .filter(|route| seen.insert((route.upper, route.upper_record)))
            .map(|route| {
                let upper = route.claim.map_or(PreparedReplayParentBlock::Empty, |claim| {
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
            .collect()
    };
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
    let accepted_results = admissions
        .iter()
        .filter_map(|admission| {
            (admission.disposition == ReplayAdmissionDisposition::NewSemantic)
                .then_some(admission.result)
                .flatten()
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

#[cfg(test)]
pub(super) fn record_replay_admission_shadow(
    result: Option<ConstraintRecordId>,
    carrier: BinaryReplayDerivation,
    disposition: ReplayAdmissionDisposition,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| {
        store
            .borrow_mut()
            .record_replay_admission(result, carrier, disposition)
    });
}

#[cfg(test)]
pub(super) fn record_replay_parent_snapshot_shadow(
    bounds: &TypeBounds,
    result: ConstraintRecordId,
    carrier: BinaryReplayDerivation,
    parents: &[ClaimQualifiedParent],
) {
    if !proof_occurrence_shadow_is_active() || parents.is_empty() {
        return;
    }
    SHADOW_STORE.with(|store| {
        store
            .borrow_mut()
            .record_replay_parent_snapshot(bounds, result, carrier, parents)
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

    pub(super) fn record_replay_parent_snapshot(
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

    pub(super) fn record_live_coverage(
        &mut self,
        root: UpperReplayClaimId,
        state: UnweightedRowReductionRecordId,
        active: bool,
    ) {
        if active {
            if self.live_coverage.insert((root, state)) {
                self.live_states_by_coverage_root
                    .entry(root)
                    .or_default()
                    .insert(state);
            }
        } else if self.live_coverage.remove(&(root, state)) {
            let remove_root_entry = {
                let states = self
                    .live_states_by_coverage_root
                    .get_mut(&root)
                    .expect("live coverage index must mirror the flat occurrence set");
                states.remove(&state);
                states.is_empty()
            };
            if remove_root_entry {
                self.live_states_by_coverage_root.remove(&root);
            }
        }
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

#[cfg(test)]
pub(super) fn record_replay_evidence_shadow(
    result: BoundRecordId,
    carrier: BinaryReplayDerivation,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| store.borrow_mut().record_replay_evidence(result, carrier));
}

#[cfg(test)]
pub(super) fn record_replay_drop_shadow(id: ReplayDropRecordId, record: ReplayDropRecord) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| store.borrow_mut().record_replay_drop(id, record));
}

#[cfg(test)]
pub(super) fn record_row_reduction_shadow(
    state: UnweightedRowReductionRecordId,
    record: &UnweightedRowReductionRecord,
    root_claim: Option<UpperReplayClaimId>,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| {
        store
            .borrow_mut()
            .record_row_reduction(state, record, root_claim)
    });
}

#[cfg(test)]
pub(super) fn record_live_coverage_shadow(
    root: UpperReplayClaimId,
    state: UnweightedRowReductionRecordId,
    active: bool,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| store.borrow_mut().record_live_coverage(root, state, active));
}

#[cfg(test)]
pub(super) fn record_reduction_route_shadow(
    result: ConstraintRecordId,
    derivation: RowDerivationId,
    parent_claim: UpperReplayClaimId,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| {
        store
            .borrow_mut()
            .record_reduction_route(result, derivation, parent_claim)
    });
}

#[cfg(test)]
pub(crate) fn record_constraint_root_shadow(result: ConstraintRecordId, origin: OriginId) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| store.borrow_mut().record_constraint_root(result, origin));
}

#[cfg(test)]
pub(crate) fn record_structural_shadow(
    result: ConstraintRecordId,
    derivation: StructuralDerivation,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| store.borrow_mut().record_structural(result, derivation));
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

#[cfg(test)]
pub(crate) fn record_row_definition_shadow(id: RowDerivationId, derivation: RowDerivation) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| store.borrow_mut().record_row_definition(id, derivation));
}

#[cfg(test)]
pub(crate) fn record_row_constraint_shadow(
    result: ConstraintRecordId,
    derivation: RowDerivationId,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| store.borrow_mut().record_row_constraint(result, derivation));
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
pub(crate) fn record_bound_shadow(result: BoundRecordId, derivation: BoundDerivation) {
    if !proof_occurrence_shadow_is_active() {
        // Replay occurrences, including evidence-only replay bounds, start in CPK-3.
        return;
    }
    SHADOW_STORE.with(|store| store.borrow_mut().record_bound(result, derivation));
}

#[cfg(test)]
pub(crate) fn record_bound_disposition_shadow(
    id: BoundDispositionRecordId,
    result: Option<BoundRecordId>,
    disposition: BoundDispositionRecord,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| {
        store
            .borrow_mut()
            .record_bound_disposition(id, result, disposition)
    });
}

#[cfg(test)]
pub(crate) fn record_subtract_shadow(
    result: SubtractFactRecordId,
    derivation: SubtractFactDerivation,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| store.borrow_mut().record_subtract(result, derivation));
}

#[cfg(test)]
pub(crate) fn record_scheme_instantiation_record_shadow(
    result: SchemeInstantiationId,
    record: SchemeInstantiationRecord,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| {
        store
            .borrow_mut()
            .record_scheme_instantiation_record(result, record)
    });
}

#[cfg(test)]
pub(crate) fn record_scheme_instantiation_derivation_shadow(
    result: ConstraintRecordId,
    derivation: SchemeInstantiationDerivation,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| {
        store
            .borrow_mut()
            .record_scheme_instantiation_derivation(result, derivation)
    });
}

#[cfg(test)]
pub(crate) fn record_scheme_instantiation_route_shadow(
    result: ConstraintRecordId,
    route: SchemeInstantiationRoute,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| {
        store
            .borrow_mut()
            .record_scheme_instantiation_route(result, route)
    });
}

#[cfg(test)]
pub(crate) fn record_constraint_disposition_shadow(
    result: ConstraintRecordId,
    disposition: ConstraintCanonicalizationDisposition,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| {
        store
            .borrow_mut()
            .record_constraint_disposition(result, disposition)
    });
}

#[cfg(test)]
fn occurrence_without_event(
    result: ProofResult,
    cause: ProofCause,
    parents: Vec<ProofParent>,
    completeness: ProvenanceCompleteness,
) -> ProofOccurrence {
    ProofOccurrence {
        result,
        cause,
        parents,
        event: 0,
        completeness,
    }
}

#[cfg(test)]
fn legacy_cpk2_shadow_expected(machine: &ConstraintMachine) -> Vec<ProofOccurrence> {
    let mut occurrences = Vec::new();
    for (index, record) in machine.constraint_records.iter().enumerate() {
        let id = ConstraintRecordId(index as u32);
        let result = ProofResult::Semantic(SemanticFactRef::Constraint(id));
        occurrences.extend(record.root_origins.iter().copied().map(|origin| {
            occurrence_without_event(
                result,
                ProofCause::Root(origin),
                vec![ProofParent::Origin(origin)],
                ProvenanceCompleteness::Complete,
            )
        }));
        occurrences.extend(record.structural_derivations.iter().copied().map(|derivation| {
            occurrence_without_event(
                result,
                ProofCause::Structural(derivation),
                vec![ProofParent::Semantic(SemanticFactRef::Constraint(
                    derivation.parent,
                ))],
                ProvenanceCompleteness::Complete,
            )
        }));
        occurrences.extend(record.row_derivations.iter().copied().map(|derivation| {
            occurrence_without_event(
                result,
                ProofCause::RowConstraint(derivation),
                vec![ProofParent::Semantic(SemanticFactRef::RowDerivation(
                    derivation,
                ))],
                ProvenanceCompleteness::Complete,
            )
        }));
        occurrences.extend(record.canonicalization_dispositions.iter().cloned().map(
            |disposition| {
                occurrence_without_event(
                    result,
                    ProofCause::ConstraintDisposition(disposition),
                    Vec::new(),
                    ProvenanceCompleteness::Complete,
                )
            },
        ));
        occurrences.extend(record.scheme_instantiation_derivations.iter().cloned().map(
            |derivation| {
                occurrence_without_event(
                    result,
                    ProofCause::SchemeInstantiationDerivation(derivation.clone()),
                    vec![
                        ProofParent::Semantic(SemanticFactRef::SchemeInstantiation(
                            derivation.instantiation,
                        )),
                        ProofParent::GeneralizedWitness(derivation.source_witness),
                    ],
                    ProvenanceCompleteness::Complete,
                )
            },
        ));
        occurrences.extend(record.scheme_instantiation_routes.iter().cloned().map(|route| {
            occurrence_without_event(
                result,
                ProofCause::SchemeInstantiationRoute(route.clone()),
                vec![
                    ProofParent::Semantic(SemanticFactRef::SchemeInstantiation(
                        route.derivation.instantiation,
                    )),
                    ProofParent::GeneralizedWitness(route.derivation.source_witness),
                ],
                ProvenanceCompleteness::Complete,
            )
        }));
    }
    for (index, record) in machine.bounds.records.iter().enumerate() {
        let id = BoundRecordId(index as u32);
        occurrences.extend(record.derivations.iter().filter_map(|derivation| {
            if matches!(
                derivation,
                BoundDerivation::ReplayEvidence(_) | BoundDerivation::IncompleteReplay
            ) {
                return None;
            }
            Some(occurrence_without_event(
                ProofResult::Semantic(SemanticFactRef::Bound(id)),
                ProofCause::Bound(derivation.clone()),
                bound_derivation_parents(derivation),
                ProvenanceCompleteness::Complete,
            ))
        }));
    }
    for (index, record) in machine.bound_dispositions.iter().enumerate() {
        let id = BoundDispositionRecordId(index as u32);
        let bound = machine.bounds.records.iter().enumerate().find_map(|(index, bound)| {
            (bound.disposition == Some(id)).then_some(BoundRecordId(index as u32))
        });
        occurrences.push(occurrence_without_event(
            bound.map_or(ProofResult::BoundDisposition(id), |bound| {
                ProofResult::Semantic(SemanticFactRef::Bound(bound))
            }),
            ProofCause::BoundDisposition(record.clone()),
            Vec::new(),
            ProvenanceCompleteness::Complete,
        ));
    }
    for (index, record) in machine.subtracts.records.iter().enumerate() {
        let id = SubtractFactRecordId(index as u32);
        occurrences.extend(record.derivations.iter().copied().map(|derivation| {
            let origin = match derivation {
                SubtractFactDerivation::Declaration(origin)
                | SubtractFactDerivation::Import(origin)
                | SubtractFactDerivation::Internal(origin) => origin,
            };
            occurrence_without_event(
                ProofResult::Semantic(SemanticFactRef::Subtract(id)),
                ProofCause::Subtract(derivation),
                vec![ProofParent::Origin(origin)],
                ProvenanceCompleteness::Complete,
            )
        }));
    }
    occurrences.extend(machine.row_derivations.iter().cloned().enumerate().map(
        |(index, derivation)| {
            let id = RowDerivationId(index as u32);
            let parents = derivation.parents.iter().copied().map(row_parent).collect();
            occurrence_without_event(
                ProofResult::Semantic(SemanticFactRef::RowDerivation(id)),
                ProofCause::RowDefinition(derivation),
                parents,
                ProvenanceCompleteness::Complete,
            )
        },
    ));
    occurrences.extend(machine.scheme_instantiations.iter().cloned().enumerate().map(
        |(index, record)| {
            occurrence_without_event(
                ProofResult::Semantic(SemanticFactRef::SchemeInstantiation(
                    SchemeInstantiationId(index as u32),
                )),
                ProofCause::SchemeInstantiationRecord(record.clone()),
                Vec::new(),
                record.completeness,
            )
        },
    ));
    occurrences
}

#[cfg(test)]
fn assert_non_replay_shadow_parity(
    machine: &ConstraintMachine,
    snapshot: &ProofOccurrenceStore,
) {
    assert!(snapshot.replay_coverage_connected, "CPK-3 connects replay coverage");
    assert_eq!(
        snapshot.occurrences.iter().map(|entry| entry.event).collect::<Vec<_>>(),
        (0..snapshot.occurrences.len()).collect::<Vec<_>>(),
        "shadow occurrence ordinals must preserve writer order",
    );
    let mut actual = snapshot.occurrences.clone();
    for occurrence in &mut actual {
        occurrence.event = 0;
    }
    for expected in legacy_cpk2_shadow_expected(machine) {
        let position = actual
            .iter()
            .position(|actual| actual == &expected)
            .unwrap_or_else(|| panic!("missing CPK shadow occurrence: {expected:#?}"));
        actual.swap_remove(position);
    }
    assert!(actual.is_empty(), "unexpected CPK shadow occurrences: {actual:#?}");
}

#[cfg(test)]
fn assert_replay_shadow_parity(
    machine: &ConstraintMachine,
    snapshot: &ProofOccurrenceStore,
) {
    assert!(snapshot.replay_coverage_connected);
    assert_eq!(
        snapshot.replay_finite_map.len(),
        machine.replay_occurrences.occurrences.len(),
        "CPK and RCPF must expose the same exact replay finite map",
    );
    for expected in &machine.replay_occurrences.occurrences {
        let actual = snapshot
            .replay_finite_map
            .iter()
            .find(|actual| {
                actual.result == expected.result && actual.carrier == expected.carrier
            })
            .expect("CPK exact replay occurrence");
        for (side, version, actual_parents) in [
            (
                ReplayClaimParentSide::Lower,
                expected.lower_parents,
                &actual.lower_parents,
            ),
            (
                ReplayClaimParentSide::Upper,
                expected.upper_parents,
                &actual.upper_parents,
            ),
        ] {
            let expected_parents = machine
                .replay_parent_sets
                .iter(version)
                .expect("RCPF parent set")
                .collect::<Vec<_>>();
            assert_eq!(actual_parents.len(), expected_parents.len());
            for parent in expected_parents {
                let actual_parent = actual_parents
                    .iter()
                    .find(|candidate| candidate.coverage_root == parent.coverage_root)
                    .expect("CPK replay parent root");
                assert_eq!(actual_parent.side, side);
                assert_eq!(actual_parent.representative_claim, parent.representative_claim);
                assert_eq!(
                    actual_parent.lineage,
                    projection_lineage(
                        machine.bounds.upper_replay_claims
                            [parent.representative_claim.0 as usize]
                            .lineage,
                    ),
                );
            }
        }
    }
    for (&(result, root), expected) in &machine.replay_result_summary.first_parent_by_root {
        let occurrence = machine
            .replay_occurrences
            .occurrence(expected.occurrence)
            .expect("RCPF first witness occurrence");
        assert_eq!(
            snapshot.first_replay_witnesses.get(&(result, root)),
            Some(&ReplayFirstWitness {
                carrier: occurrence.carrier,
                side: expected.parent_side,
                representative_claim: expected.parent_claim,
            }),
            "CPK first representative must equal RCPF's event-time winner",
        );
    }
    assert_eq!(snapshot.upper_claims.len(), machine.bounds.upper_replay_claims.len());
    for claim in &machine.bounds.upper_replay_claims {
        assert!(snapshot.upper_claims.contains(&UpperClaimOccurrence {
            claim: claim.id,
            coverage_root: claim.coverage_root,
            lineage: projection_lineage(claim.lineage),
            producer: claim.producer_constraint,
            current_record: claim.current_record,
        }));
    }
    assert_eq!(
        snapshot.row_reductions.len(),
        machine.unweighted_row_reduction_records.len(),
    );
    let expected_live_coverage = machine
        .bounds
        .live_coverage_by_root
        .iter()
        .flat_map(|(&root, states)| states.iter().copied().map(move |state| (root, state)))
        .collect::<FxHashSet<_>>();
    assert_eq!(snapshot.live_coverage, expected_live_coverage);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cpk_oracle_machine() -> ConstraintMachine {
        let mut machine = ConstraintMachine::new();
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
        let registration = machine.bounds.original_upper_replay_claim(
            record,
            ConstraintRecordId(90_000 + ordinal),
            UpperReplayClaimKind::Direct,
        );
        machine
            .proof_store
            .record_upper_claim(&machine.bounds.upper_replay_claims[registration.claim.0 as usize]);
        (record, registration.claim)
    }

    struct Cpk7RoutingFixture {
        machine: ConstraintMachine,
        lower: BoundRecordId,
        upper: BoundRecordId,
        upper_endpoint: NegId,
    }

    fn cpk_7_routing_fixture(lower_is_var: bool) -> Cpk7RoutingFixture {
        let mut machine = cpk_oracle_machine();
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
        let registration = fixture.machine.bounds.original_upper_replay_claim(
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
        let mut machine = cpk_oracle_machine();
        let (old_record, claim) = cpk_7_record_original_claim(&mut machine, 0);
        let occurrence_index = machine.proof_store.upper_claim_index[&claim];
        assert_eq!(machine.proof_store.upper_claims[occurrence_index].claim, claim);
        assert_eq!(
            machine.proof_store.claims_by_upper_record.get(&old_record),
            Some(&vec![claim]),
        );

        let (new_record, existing_claim) = cpk_7_record_original_claim(&mut machine, 1);
        let mut moved_claim = machine.bounds.upper_replay_claims[claim.0 as usize].clone();
        moved_claim.current_record = new_record;
        machine.proof_store.update_upper_claim(&moved_claim);
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

        let root = moved_claim.coverage_root;
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
    fn cpk_7_slice_a_claim_index_writes_do_not_scan_the_global_claim_store() {
        let mut machine = cpk_oracle_machine();
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
        let machine = cpk_oracle_machine();
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
        let mut machine = cpk_oracle_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 0);
        let (actual, _) = project_lower_for_test(&machine, record);
        assert_eq!(actual, Ok(ProjectionDecision::Unclaimed));
    }

    #[test]
    fn cpk_gap_1_project_lower_rejects_orphan_formula() {
        let mut machine = cpk_oracle_machine();
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
        let mut machine = cpk_oracle_machine();
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
        let mut machine = cpk_oracle_machine();
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
        let mut machine = cpk_oracle_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 4);
        let root = UpperReplayClaimId(0);
        let representative = UpperReplayClaimId(1);
        for (claim, coverage_root) in [(root, root), (representative, root)] {
            let index = machine.proof_store.upper_claims.len();
            machine.proof_store.upper_claims.push(UpperClaimOccurrence {
                claim,
                coverage_root,
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
        let mut machine = cpk_oracle_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 9);
        let root = UpperReplayClaimId(0);
        let representative = UpperReplayClaimId(1);
        for (claim, coverage_root) in [(root, root), (representative, root)] {
            let index = machine.proof_store.upper_claims.len();
            machine.proof_store.upper_claims.push(UpperClaimOccurrence {
                claim,
                coverage_root,
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
        let mut machine = cpk_oracle_machine();
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
        let mut machine = cpk_oracle_machine();
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
        let mut machine = cpk_oracle_machine();
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
    fn cpk_original_standalone_writer_matches_legacy_on_mixed_projection_fixture() {
        let (machine, endpoint, owner, _) =
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

        let legacy_reason = machine
            .legacy_scheme_projectable_lowers_for_test(owner)
            .find(|entry| entry.record == record)
            .expect("legacy includes the mixed record")
            .reason;
        let (decision, _) = project_lower_for_test(&machine, record);
        let SchemeProjectableLowerReason::Qualified {
            uncovered_claims,
            independent_supports,
        } = legacy_reason
        else {
            panic!("mixed fixture must be qualified");
        };
        assert_eq!(
            decision,
            Ok(ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    uncovered_claims: uncovered_claims
                        .into_iter()
                        .map(|representative_claim| ProjectionClaimSupport {
                            coverage_root: machine
                                .proof_store
                                .upper_claim(representative_claim)
                                .expect("legacy representative is mirrored into CPK")
                                .coverage_root,
                            representative_claim,
                        })
                        .collect(),
                    independent_supports,
                },
            })
        );
    }

    #[test]
    fn cpk_gap_1_mixed_claim_fixture_matches_all_four_legacy_consumers_exactly() {
        let (mut machine, endpoint, owner, _) =
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
        let legacy_entries = machine
            .legacy_scheme_projectable_lowers_for_test(owner)
            .map(|entry| {
                (
                    entry.record,
                    entry.bound.pos,
                    entry.bound.weights.clone(),
                    entry.reason,
                )
            })
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
        assert_eq!(
            cpk_entries, legacy_entries,
            "project_lower must preserve owner-internal record/bound/support order"
        );

        let (record, _, _, reason) = cpk_entries
            .iter()
            .find(|(_, pos, _, _)| {
                matches!(machine.types().pos(*pos), Pos::Var(found) if *found == endpoint)
            })
            .expect("mixed fixture target record");
        let SchemeProjectableLowerReason::Qualified {
            uncovered_claims,
            independent_supports,
        } = reason
        else {
            panic!("mixed fixture target must be qualified");
        };
        let (decision, _) = project_lower_for_test(&machine, *record);
        let ProjectionDecision::Included { supports } = decision.expect("complete CPK decision")
        else {
            panic!("mixed fixture target must be included");
        };
        assert_eq!(
            supports
                .uncovered_claims
                .iter()
                .map(|support| support.representative_claim)
                .collect::<Vec<_>>(),
            *uncovered_claims,
        );
        assert_eq!(supports.independent_supports, *independent_supports);
        assert!(!supports.uncovered_claims.is_empty());
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
    fn cpk_gap_1_replay_conjunction_matches_all_four_legacy_consumers() {
        let mut included = cpk_oracle_machine();
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
        assert_single_lower_matches_all_four_legacy_consumers(
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

        let mut excluded = cpk_oracle_machine();
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
        assert_single_lower_matches_all_four_legacy_consumers(
            &excluded,
            excluded_owner,
            excluded_record,
            ProjectionDecision::Excluded,
        );
    }

    fn assert_single_lower_matches_all_four_legacy_consumers(
        machine: &ConstraintMachine,
        owner: TypeVar,
        record: BoundRecordId,
        expected: ProjectionDecision,
    ) {
        let (actual, _) = project_lower_for_test(machine, record);
        assert_eq!(actual, Ok(expected.clone()));
        let entries = machine
            .legacy_scheme_projectable_lowers_for_test(owner)
            .collect::<Vec<_>>();
        match &expected {
            ProjectionDecision::Excluded => assert!(entries.is_empty()),
            ProjectionDecision::Unclaimed => {
                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].record, record);
                assert_eq!(entries[0].reason, SchemeProjectableLowerReason::Unclaimed);
            }
            ProjectionDecision::Included { supports } => {
                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].record, record);
                assert_eq!(
                    entries[0].reason,
                    SchemeProjectableLowerReason::Qualified {
                        uncovered_claims: supports
                            .uncovered_claims
                            .iter()
                            .map(|support| support.representative_claim)
                            .collect(),
                        independent_supports: supports.independent_supports.clone(),
                    }
                );
            }
        }

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

    fn legacy_projection_decision(
        machine: &ConstraintMachine,
        owner: TypeVar,
        record: BoundRecordId,
    ) -> ProjectionDecision {
        let Some(entry) = machine
            .legacy_scheme_projectable_lowers_for_test(owner)
            .find(|entry| entry.record == record)
        else {
            return ProjectionDecision::Excluded;
        };
        match entry.reason {
            SchemeProjectableLowerReason::Unclaimed => ProjectionDecision::Unclaimed,
            SchemeProjectableLowerReason::Qualified {
                uncovered_claims,
                independent_supports,
            } => ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    uncovered_claims: uncovered_claims
                        .into_iter()
                        .map(|representative_claim| ProjectionClaimSupport {
                            coverage_root: machine
                                .proof_store
                                .upper_claim(representative_claim)
                                .expect("legacy claim must exist in the CPK store")
                                .coverage_root,
                            representative_claim,
                        })
                        .collect(),
                    independent_supports,
                },
            },
        }
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
    fn cpk_gap_1_unclaimed_standalone_derived_and_incomplete_match_legacy_consumers() {
        let mut no_ledger = cpk_oracle_machine();
        let no_ledger_record = cpk_gap_1_projection_record(&mut no_ledger, 20);
        let no_ledger_owner = no_ledger.bounds.record(no_ledger_record).unwrap().owner();
        let before = (
            no_ledger.proof_store.projection_supports.len(),
            no_ledger.proof_store.projection_formulas.len(),
        );
        assert_single_lower_matches_all_four_legacy_consumers(
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
        assert_single_lower_matches_all_four_legacy_consumers(
            &no_ledger,
            no_ledger_owner,
            no_ledger_record,
            ProjectionDecision::Unclaimed,
        );

        let mut standalone = cpk_oracle_machine();
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
        assert_single_lower_matches_all_four_legacy_consumers(
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

        let mut derived = cpk_oracle_machine();
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
        assert_single_lower_matches_all_four_legacy_consumers(
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

        let mut incomplete = cpk_oracle_machine();
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
        assert_single_lower_matches_all_four_legacy_consumers(
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
        assert_eq!(
            machine
                .legacy_scheme_projectable_lowers_for_test(owner)
                .find(|entry| entry.record == record)
                .expect("legacy formula still includes the record")
                .reason,
            SchemeProjectableLowerReason::Qualified {
                uncovered_claims: Vec::new(),
                independent_supports: Vec::new(),
            },
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
        let mut machine = cpk_oracle_machine();
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
            assert_single_lower_matches_all_four_legacy_consumers(
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
        let mut fixture = cpk_3_replay_admission_fixture();
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
        let mut fixture = cpk_3_replay_admission_fixture();
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
        let before = legacy_projection_decision(&fixture.machine, owner, record);
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
        let expected = legacy_projection_decision(&fixture.machine, owner, record);
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
        assert_single_lower_matches_all_four_legacy_consumers(
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
        let observations = fixture
            .machine
            .proof_store
            .replay_route_observations
            .borrow();
        let observation = observations
            .iter()
            .rev()
            .find(|observation| observation.lower == record)
            .expect("the replacement fixture must route the claimed lower");
        assert_eq!(observation.legacy_prepared, observation.shadow_prepared);
        assert_eq!(
            observation
                .shadow_prepared
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
            let expected = legacy_projection_decision(&fixture.machine, owner, record);
            let (actual, _) = project_lower_for_test(&fixture.machine, record);
            assert_eq!(actual, Ok(expected.clone()), "arrival order {order:?}");
            assert_single_lower_matches_all_four_legacy_consumers(
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
        let mut machine = cpk_oracle_machine();
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
        let mut machine = cpk_oracle_machine();
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
        let registration = machine.bounds.original_upper_replay_claim(
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
            .bounds
            .derived_upper_replay_claim(record, fixture.coverage_root, producer, |depth| {
                UpperReplayClaimLineage::ReplayConstraint {
                    parent_claim: fixture.coverage_root,
                    parent_side: ReplayClaimParentSide::Lower,
                    result: fixture.result,
                    replay: fixture.carrier,
                    depth,
                }
            });
        fixture.machine.proof_store.record_upper_claim(
            &fixture.machine.bounds.upper_replay_claims[registration.claim.0 as usize],
        );
        registration.claim
    }

    fn cpk_3_replay_fixture() -> ConstraintMachine {
        let mut machine = cpk_oracle_machine();
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
            let registration = machine.bounds.derived_upper_replay_claim(
                insertion.id,
                root_claim,
                producer,
                |_| lineage,
            );
            machine.proof_store.record_upper_claim(
                &machine.bounds.upper_replay_claims[registration.claim.0 as usize],
            );
        }
        machine
    }

    #[test]
    fn cpk_3_exact_replay_and_first_witness_match_factored_oracle() {
        let inactive =
            with_semantic_execution_snapshot_capture_for_new_machines(cpk_3_replay_fixture);
        let active =
            with_semantic_execution_snapshot_capture_for_new_machines(cpk_3_replay_fixture);
        let snapshot = active.proof_store.clone();

        assert_replay_shadow_parity(&active, &snapshot);
        assert!(!snapshot.replay_finite_map.is_empty());
        assert!(!snapshot.first_replay_witnesses.is_empty());
        assert!(!snapshot.row_reductions.is_empty());
        assert!(!snapshot.live_coverage.is_empty());
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
        assert!(snapshot.replay_admissions.iter().any(|event| {
            event.disposition == ReplayAdmissionDisposition::CanonicalDuplicate
        }));
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

    #[test]
    fn cpk_3_trivial_replay_records_drop_and_admission_in_active_shadow() {
        let mut fixture = cpk_3_replay_admission_fixture();
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
        assert!(snapshot.replay_admissions.iter().any(|event| {
            event.result.is_none()
                && event.carrier == expected_drop.derivation
                && event.disposition == ReplayAdmissionDisposition::Trivial
        }));
        assert!(snapshot.occurrences.iter().any(|occurrence| {
            occurrence.result == ProofResult::TrivialReplay(ReplayDropRecordId(0))
                && occurrence.cause == ProofCause::ReplayDrop(expected_drop.clone())
        }));
        assert_replay_shadow_parity(&machine, &snapshot);
    }

    #[test]
    fn cpk_3_evidence_only_replay_records_both_bound_edges_in_active_shadow() {
        let mut fixture = cpk_3_replay_admission_fixture();
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

        assert!(snapshot.replay_admissions.iter().any(|event| {
            event.result.is_none()
                && event.carrier == carrier
                && event.disposition == ReplayAdmissionDisposition::EvidenceOnly
        }));
        let legacy_records = machine
            .bounds
            .records
            .iter()
            .enumerate()
            .filter_map(|(index, record)| {
                record
                    .derivations
                    .contains(&BoundDerivation::ReplayEvidence(carrier))
                    .then_some(BoundRecordId(index as u32))
            })
            .collect::<FxHashSet<_>>();
        let shadow_records = snapshot
            .occurrences
            .iter()
            .filter_map(|occurrence| match (&occurrence.result, &occurrence.cause) {
                (ProofResult::EvidenceBound(record), ProofCause::ReplayEvidence(replay))
                    if *replay == carrier =>
                {
                    Some(*record)
                }
                _ => None,
            })
            .collect::<FxHashSet<_>>();
        assert_eq!(legacy_records.len(), 2);
        assert_eq!(shadow_records, legacy_records);
        assert_replay_shadow_parity(&machine, &snapshot);
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
            let mut fixture = cpk_3_replay_admission_fixture();
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

            assert_replay_shadow_parity(&machine, &snapshot);
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
            assert_eq!(occurrence.lower_parents.len(), 1);
            assert_eq!(
                occurrence.lower_parents[0].representative_claim,
                claims[order[0]]
            );
        }
    }

    #[test]
    fn cpk_4_replay_formula_and_projectability_match_legacy_end_to_end() {
        let machine = cpk_3_replay_fixture();
        let snapshot = machine.proof_store.clone();

        assert_replay_shadow_parity(&machine, &snapshot);
        assert!(
            !snapshot.projection_formulas.is_empty(),
            "the production clause-link writers must populate the CPK projection formula",
        );
        assert!(
            snapshot
                .projection_formulas
                .values()
                .flatten()
                .any(|clause| matches!(clause, ProjectionClause::ReplayConjunction { .. })),
            "the representative fixture must exercise replay-conjunction support",
        );
        assert!(
            !snapshot.projectability_observations.borrow().is_empty(),
            "legacy production evaluation must invoke the CPK-4 shadow oracle",
        );
        assert!(snapshot
            .projectability_observations
            .borrow()
            .iter()
            .all(|observation| {
            observation.legacy == observation.shadow
                && observation.legacy_cycle_cut == observation.shadow_cycle_cut
        }));
        assert!(snapshot
            .projection_publication_observations
            .borrow()
            .iter()
            .all(|observation| {
                observation.legacy_class == observation.shadow_class
                    && observation.legacy_affected_owners
                        == observation.shadow_affected_owners
            }));
    }

    #[test]
    fn cpk_4_standalone_only_is_projectable_and_metadata_only() {
        let mut machine = cpk_oracle_machine();
        let (record, carrier) = cpk_4_projection_record(&mut machine, 1);
        let support = cpk_4_add_independent_support(&mut machine, record, carrier);
        machine.register_cpk_projection_clause_for_test(
            record,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::Standalone { support },
            ),
        );
        assert!(machine.scheme_projection_record_is_included(record));
        let snapshot = machine.proof_store.clone();

        assert_eq!(
            snapshot.projection_formulas[&record],
            vec![ProjectionClause::Standalone {
                support: snapshot.projection_supports[&record][0],
                attribution: None,
            }],
        );
        assert!(snapshot
            .projectability_observations
            .borrow()
            .iter()
            .any(|observation| observation.record == record && observation.shadow));
        assert!(snapshot.projection_publication_observations.borrow().iter().any(
            |observation| observation.lower_record == record
                && observation.legacy_class == ShadowProjectionPublicationClass::MetadataOnly
                && observation.legacy_affected_owners.is_empty()
        ));
        assert_eq!(
            machine.scheme_projection_record_is_included(record),
            true,
        );
    }

    #[test]
    fn cpk_4_derived_unary_only_cycle_flips_inclusion_and_owner() {
        let mut machine = cpk_oracle_machine();
            let (record, carrier) = cpk_4_projection_record(&mut machine, 2);
            let owner = machine.bounds.record(record).unwrap().owner();
            let support = cpk_4_add_independent_support(&mut machine, record, carrier);

            let (dependent, dependent_carrier) = cpk_4_projection_record(&mut machine, 4);
            let dependent_owner = machine.bounds.record(dependent).unwrap().owner();
            let dependent_support =
                cpk_4_add_independent_support(&mut machine, dependent, dependent_carrier);
            machine.register_cpk_projection_clause_for_test(
                dependent,
                RecordProofClauseLinkAdmission::independent(
                    dependent_support,
                    RecordProofClause::DerivedUnary {
                        carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                            parent: ConstraintRecordId(32_001),
                            rule: StructuralDerivationRule::FunctionReturn,
                        }),
                        premise: ProofPremise::Record(record),
                    },
                ),
            );
            machine.register_cpk_projection_clause_for_test(
                record,
                RecordProofClauseLinkAdmission::independent(
                    support,
                    RecordProofClause::DerivedUnary {
                        carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                            parent: ConstraintRecordId(32_000),
                            rule: StructuralDerivationRule::FunctionReturn,
                        }),
                        premise: ProofPremise::Record(record),
                    },
                ),
            );
            assert!(!machine.scheme_projection_record_is_included(record));
            assert!(!machine.scheme_projection_record_is_included(dependent));
        let expected_owners = vec![owner, dependent_owner];
        let snapshot = machine.proof_store.clone();

        assert!(matches!(
            snapshot.projection_formulas[&record].as_slice(),
            [ProjectionClause::DerivedUnary { .. }]
        ));
        let publications = snapshot.projection_publication_observations.borrow();
        let publication = publications
            .iter()
            .find(|observation| {
                observation.lower_record == record
                    && observation.legacy_class
                        == ShadowProjectionPublicationClass::InclusionFlip
            })
            .expect("the self-cycle must publish an inclusion flip");
        assert_eq!(publication.legacy_affected_owners, expected_owners);
        assert_eq!(publication.shadow_affected_owners, expected_owners);
        assert!(!machine.scheme_projection_record_is_included(record));
        assert!(!machine.scheme_projection_record_is_included(dependent));
    }

    #[test]
    fn cpk_4_no_claim_record_passthrough_has_no_formula_or_publication() {
        let mut machine = cpk_oracle_machine();
        let (record, _) = cpk_4_projection_record(&mut machine, 3);
        assert!(machine.scheme_projection_record_is_included(record));
        let snapshot = machine.proof_store.clone();

        assert!(!snapshot.projection_supports.contains_key(&record));
        assert!(!snapshot.projection_formulas.contains_key(&record));
        assert!(snapshot
            .projection_publication_observations
            .borrow()
            .is_empty());
        assert!(snapshot
            .projectability_observations
            .borrow()
            .iter()
            .any(|observation| observation.record == record && observation.shadow));
        assert!(machine.scheme_projection_record_is_included(record));
    }

    #[test]
    fn cpk_4_five_source_attribution_matrix_is_writer_classified() {
        let mut machine = cpk_oracle_machine();
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
    fn cpk_7_shadow_no_claim_generic_preserves_some_empty_in_both_directions() {
        let run = |lower_first: bool| {
            let mut machine = cpk_oracle_machine();
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
            let observations = machine.proof_store.replay_route_observations.borrow();
            let observation = observations
                .last()
                .expect("the second frontier insertion must preflight one replay pair");
            assert_eq!(observation.legacy, ReplayRouting::Generic);
            assert_eq!(observation.legacy_prepared, observation.shadow_prepared);
            let parents = observation
                .shadow_prepared
                .proof_event
                .pair_replay
                .as_ref()
                .expect("no-claim Generic retains an explicit empty pair");
            assert!(parents.lower.as_slice().is_empty());
            assert!(parents.upper.as_slice().is_empty());
            assert!(observation
                .shadow_prepared
                .proof_event
                .incremental_replays
                .is_empty());
        };
        run(false);
        run(true);
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
    fn cpk_2_non_replay_shadow_matches_legacy_and_is_off_by_default() {
        let (_, empty) = capture_proof_occurrence_shadow(|| {});
        assert!(empty.occurrences.is_empty());
        assert!(!proof_occurrence_shadow_is_active());

        let mut inactive_machine = ConstraintMachine::new();
        let inactive_lower = inactive_machine.alloc_pos(Pos::Var(TypeVar(0)));
        let inactive_upper = inactive_machine.alloc_neg(Neg::Var(TypeVar(1)));
        inactive_machine.subtype(
            inactive_lower,
            inactive_upper,
            OriginId::unknown_internal(),
        );
        assert_eq!(
            proof_occurrence_shadow_len(),
            0,
            "inactive shadow hooks must not retain an occurrence",
        );

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

        assert_non_replay_shadow_parity(&machine, &snapshot);
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
