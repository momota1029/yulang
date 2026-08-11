//! Constraint Proof Kernel boundary.
//!
//! CPK-1 defines read-only adapters over current semantic records. CPK-2 established the typed
//! occurrence contract; CPK-8E removes its migration-only thread-local capture now that tests
//! assert the production store directly.

use super::*;
use std::sync::Arc;

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

/// Provenance-only evidence captured by the same projection evaluation that decides inclusion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProjectionEvidence {
    DecisiveClaimedArm(ClaimedProjectionProof),
    ExactWithoutClaimedArm,
    FailOpenIncomplete,
}

/// Fallible projection result for one active lower record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ProjectionDecision {
    Unclaimed,
    Excluded,
    Included {
        supports: ProjectionSupportSet,
        evidence: ProjectionEvidence,
    },
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

pub(crate) type ProofKernelResult<T> = Result<T, ProofFailure>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ProofEvalNode {
    Record(BoundRecordId),
    Constraint(ConstraintRecordId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ProofEvalState {
    Visiting,
    Done(ProofEvalMemo),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ProofEvalMemo {
    summary: CpkProjectionEvaluationSummary,
    evidence: ProofEvalEvidenceMemo,
}

impl ProofEvalMemo {
    fn summary_only(summary: CpkProjectionEvaluationSummary) -> Self {
        Self {
            summary,
            evidence: ProofEvalEvidenceMemo::none(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ProofEvalEvidenceMemo {
    support_or_tag: u32,
    entry_or_state: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DecodedProofEvalEvidenceMemo {
    None,
    DecisiveClaimedIncidence {
        support_id: ProjectionSupportGroupId,
        entry_id: ProjectionFormulaEntryId,
    },
    ExactWithoutClaimedArm,
    FailOpenIncomplete,
}

impl ProofEvalEvidenceMemo {
    const STATE_TAG: u32 = u32::MAX;
    const NONE_STATE: u32 = 0;
    const EXACT_WITHOUT_CLAIMED_ARM_STATE: u32 = 1;
    const FAIL_OPEN_INCOMPLETE_STATE: u32 = 2;

    const fn none() -> Self {
        Self {
            support_or_tag: Self::STATE_TAG,
            entry_or_state: Self::NONE_STATE,
        }
    }

    const fn exact_without_claimed_arm() -> Self {
        Self {
            support_or_tag: Self::STATE_TAG,
            entry_or_state: Self::EXACT_WITHOUT_CLAIMED_ARM_STATE,
        }
    }

    const fn fail_open_incomplete() -> Self {
        Self {
            support_or_tag: Self::STATE_TAG,
            entry_or_state: Self::FAIL_OPEN_INCOMPLETE_STATE,
        }
    }

    fn decisive_claimed_incidence(
        support_id: ProjectionSupportGroupId,
        entry_id: ProjectionFormulaEntryId,
    ) -> Self {
        assert_ne!(
            support_id.0,
            Self::STATE_TAG,
            "PCLF support-group IDs must not collide with the evidence state tag",
        );
        Self {
            support_or_tag: support_id.0,
            entry_or_state: entry_id.0,
        }
    }

    fn decode(self) -> DecodedProofEvalEvidenceMemo {
        if self.support_or_tag != Self::STATE_TAG {
            return DecodedProofEvalEvidenceMemo::DecisiveClaimedIncidence {
                support_id: ProjectionSupportGroupId(self.support_or_tag),
                entry_id: ProjectionFormulaEntryId(self.entry_or_state),
            };
        }
        match self.entry_or_state {
            Self::NONE_STATE => DecodedProofEvalEvidenceMemo::None,
            Self::EXACT_WITHOUT_CLAIMED_ARM_STATE => {
                DecodedProofEvalEvidenceMemo::ExactWithoutClaimedArm
            }
            Self::FAIL_OPEN_INCOMPLETE_STATE => {
                DecodedProofEvalEvidenceMemo::FailOpenIncomplete
            }
            state => panic!("invalid packed proof-evidence memo state {state}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CpkProjectionEvaluationSummary {
    Excluded,
    IncludedExact,
    IncludedFailOpen,
}

impl CpkProjectionEvaluationSummary {
    fn is_included(self) -> bool {
        self != Self::Excluded
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CpkProjectionEvaluation {
    Excluded,
    Included { evidence: ProjectionEvidence },
}

/// Preflight, memo, and cycle-cut state shared only within one immutable projection traversal.
pub(crate) struct ProjectionEvaluationRound<'a> {
    preflight: Option<ProjectionPreflight<'a>>,
    states: FxHashMap<ProofEvalNode, ProofEvalState>,
    memo_sharing_disabled: bool,
    terminal_failure: Option<ProofFailure>,
    cycle_cuts: usize,
    snapshot: std::marker::PhantomData<&'a ()>,
}

impl ProjectionEvaluationRound<'_> {
    pub(crate) fn new() -> Self {
        Self {
            preflight: None,
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

impl ConstraintRecord {
    fn semantic_ref(&self) -> SemanticConstraintRecordRef<'_> {
        SemanticConstraintRecordRef { key: &self.key }
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
    lower_parents: Vec<ReplayProofParent>,
    upper_parents: Vec<ReplayProofParent>,
    pub(crate) first_event: usize,
    // QORF-C read authority. Expanded Vecs remain dual-written as the rollback/test oracle.
    replay_parent_sides: [ReplayParentSideIndex; 2],
}

// QORF-A fixes the representation boundary before any production authority moves. These types
// intentionally are not fields of `ProofOccurrenceStore`; QORF-B is the first slice allowed to
// allocate or dual-write them in production.
const QORF_REPLAY_PARENT_CHUNK_CAPACITY: usize = 128;
const QORF_REPLAY_PARENT_CURSOR_STACK_CAPACITY: usize = 64;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayFiniteMapEntryId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayParentChunkId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayQualifiedArmChunkId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CanonicalQualifiedParentRootChunkId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct NonReplayQualifiedParentId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct QorfReplayParentEntry {
    coverage_root: UpperReplayClaimId,
    representative_claim: UpperReplayClaimId,
    lineage: ProjectionLineage,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct ReplayParentSideIndex {
    root: Option<ReplayParentChunkId>,
    len: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ReplayParentChunkNode {
    entries: Vec<QorfReplayParentEntry>,
    left: Option<ReplayParentChunkId>,
    right: Option<ReplayParentChunkId>,
    height: u8,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct ReplayParentChunkArena {
    nodes: Vec<ReplayParentChunkNode>,
}

impl ReplayParentChunkArena {
    fn node(&self, id: ReplayParentChunkId) -> &ReplayParentChunkNode {
        &self.nodes[id.0 as usize]
    }

    fn node_mut(&mut self, id: ReplayParentChunkId) -> &mut ReplayParentChunkNode {
        &mut self.nodes[id.0 as usize]
    }

    fn height(&self, id: Option<ReplayParentChunkId>) -> u8 {
        id.map_or(0, |id| self.node(id).height)
    }

    fn update_height(&mut self, id: ReplayParentChunkId) {
        let (left, right) = {
            let node = self.node(id);
            (node.left, node.right)
        };
        self.node_mut(id).height = 1 + self.height(left).max(self.height(right));
    }

    fn rotate_left(&mut self, root: ReplayParentChunkId) -> ReplayParentChunkId {
        let right = self
            .node(root)
            .right
            .expect("QORF AVL left rotation requires a right child");
        let middle = self.node(right).left;
        self.node_mut(root).right = middle;
        self.update_height(root);
        self.node_mut(right).left = Some(root);
        self.update_height(right);
        right
    }

    fn rotate_right(&mut self, root: ReplayParentChunkId) -> ReplayParentChunkId {
        let left = self
            .node(root)
            .left
            .expect("QORF AVL right rotation requires a left child");
        let middle = self.node(left).right;
        self.node_mut(root).left = middle;
        self.update_height(root);
        self.node_mut(left).right = Some(root);
        self.update_height(left);
        left
    }

    fn rebalance(&mut self, root: ReplayParentChunkId) -> ReplayParentChunkId {
        self.update_height(root);
        let (left, right) = {
            let node = self.node(root);
            (node.left, node.right)
        };
        let balance = i16::from(self.height(left)) - i16::from(self.height(right));
        if balance > 1 {
            let left = left.expect("left-heavy QORF node must have a left child");
            if self.height(self.node(left).left) < self.height(self.node(left).right) {
                let rotated = self.rotate_left(left);
                self.node_mut(root).left = Some(rotated);
            }
            return self.rotate_right(root);
        }
        if balance < -1 {
            let right = right.expect("right-heavy QORF node must have a right child");
            if self.height(self.node(right).right) < self.height(self.node(right).left) {
                let rotated = self.rotate_right(right);
                self.node_mut(root).right = Some(rotated);
            }
            return self.rotate_left(root);
        }
        root
    }

    fn insert_node(
        &mut self,
        root: Option<ReplayParentChunkId>,
        inserted: ReplayParentChunkId,
    ) -> ReplayParentChunkId {
        let Some(root) = root else { return inserted };
        let inserted_key = self.node(inserted).entries[0].coverage_root;
        let root_key = self.node(root).entries[0].coverage_root;
        assert_ne!(inserted_key, root_key, "QORF chunk pivots must be unique");
        if inserted_key < root_key {
            let child = self.insert_node(self.node(root).left, inserted);
            self.node_mut(root).left = Some(child);
        } else {
            let child = self.insert_node(self.node(root).right, inserted);
            self.node_mut(root).right = Some(child);
        }
        self.rebalance(root)
    }

    fn target_chunk(
        &self,
        mut root: ReplayParentChunkId,
        key: UpperReplayClaimId,
    ) -> ReplayParentChunkId {
        loop {
            let node = self.node(root);
            let first = node.entries[0].coverage_root;
            let last = node.entries[node.entries.len() - 1].coverage_root;
            if key < first {
                if let Some(left) = node.left {
                    root = left;
                } else {
                    return root;
                }
            } else if key > last {
                if let Some(right) = node.right {
                    root = right;
                } else {
                    return root;
                }
            } else {
                return root;
            }
        }
    }

    fn contains(&self, side: ReplayParentSideIndex, key: UpperReplayClaimId) -> bool {
        let Some(root) = side.root else { return false };
        let target = self.target_chunk(root, key);
        self.node(target)
            .entries
            .binary_search_by_key(&key, |entry| entry.coverage_root)
            .is_ok()
    }

    fn qorf_entry(
        &self,
        side: ReplayParentSideIndex,
        key: UpperReplayClaimId,
    ) -> Option<QorfReplayParentEntry> {
        let root = side.root?;
        let target = self.target_chunk(root, key);
        let entries = &self.node(target).entries;
        entries
            .binary_search_by_key(&key, |entry| entry.coverage_root)
            .ok()
            .map(|index| entries[index])
    }
}

struct ReplayParentSideCursor<'a> {
    arena: &'a ReplayParentChunkArena,
    side: ReplayClaimParentSide,
    stack: [ReplayParentChunkId; QORF_REPLAY_PARENT_CURSOR_STACK_CAPACITY],
    stack_len: usize,
    current: Option<ReplayParentChunkId>,
    entry_index: usize,
    remaining: usize,
}

impl<'a> ReplayParentSideCursor<'a> {
    fn new(
        arena: &'a ReplayParentChunkArena,
        side_index: ReplayParentSideIndex,
        side: ReplayClaimParentSide,
    ) -> Self {
        let mut cursor = Self {
            arena,
            side,
            stack: [ReplayParentChunkId(0); QORF_REPLAY_PARENT_CURSOR_STACK_CAPACITY],
            stack_len: 0,
            current: None,
            entry_index: 0,
            remaining: side_index.len as usize,
        };
        cursor.push_left(side_index.root);
        cursor
    }

    fn push_left(&mut self, mut root: Option<ReplayParentChunkId>) {
        while let Some(id) = root {
            assert!(
                self.stack_len < self.stack.len(),
                "QORF side cursor stack must cover every valid u32-indexed AVL height"
            );
            self.stack[self.stack_len] = id;
            self.stack_len += 1;
            root = self.arena.node(id).left;
        }
    }
}

impl Iterator for ReplayParentSideCursor<'_> {
    type Item = ReplayProofParent;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(id) = self.current {
                let node = self.arena.node(id);
                if let Some(entry) = node.entries.get(self.entry_index).copied() {
                    self.entry_index += 1;
                    self.remaining -= 1;
                    return Some(ReplayProofParent {
                        side: self.side,
                        coverage_root: entry.coverage_root,
                        representative_claim: entry.representative_claim,
                        lineage: entry.lineage,
                    });
                }
                let right = node.right;
                self.current = None;
                self.entry_index = 0;
                self.push_left(right);
            }
            if self.stack_len == 0 {
                debug_assert_eq!(self.remaining, 0);
                return None;
            }
            self.stack_len -= 1;
            self.current = Some(self.stack[self.stack_len]);
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl ExactSizeIterator for ReplayParentSideCursor<'_> {}

#[derive(Debug)]
struct PreparedReplayParentSideShadowDelta {
    side: ReplayClaimParentSide,
    replacements: Vec<(ReplayParentChunkId, Vec<QorfReplayParentEntry>)>,
    new_nodes: Vec<ReplayParentChunkNode>,
    new_root: Option<ReplayParentChunkId>,
    first_new_node_index: usize,
    resulting_len: u32,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QorfReplayReservationFailurePoint {
    AfterQualifiedSourceSummary,
    AfterQualified,
    AfterSideChunks,
    AfterReplayFiniteMap,
    AfterReplayFiniteMapIndex,
    AfterReplayResultIndex,
    AfterOccurrence,
    AfterArm,
    AfterRootWinner,
    AfterSummary,
    AfterProofOccurrence,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct QorfReplaySideOperationCensus {
    admission_events: usize,
    accepted_parents: usize,
    scanned_existing: usize,
    max_scanned_existing: usize,
    created_chunks: usize,
    split_chunks: usize,
    snapshot_duplicate_comparisons: usize,
}

#[cfg(test)]
thread_local! {
    static QORF_REPLAY_SIDE_OPERATION_CENSUS: Cell<QorfReplaySideOperationCensus> =
        const { Cell::new(QorfReplaySideOperationCensus {
            admission_events: 0,
            accepted_parents: 0,
            scanned_existing: 0,
            max_scanned_existing: 0,
            created_chunks: 0,
            split_chunks: 0,
            snapshot_duplicate_comparisons: 0,
        }) };
}

#[cfg(test)]
thread_local! {
    // The full-workload gate performs one exhaustive comparison after lowering. Suppress the
    // per-event fixture oracle while it runs: retaining both would turn the gate itself into a
    // repeated side-prefix scan and make its cost unrelated to the production read topology.
    static QORF_C_FULL_STD_PARITY_ACTIVE: Cell<bool> = const { Cell::new(false) };
}

fn try_replay_parent_chunk_id(index: usize) -> Result<ReplayParentChunkId, ProofFailure> {
    u32::try_from(index)
        .map(ReplayParentChunkId)
        .map_err(|_| ProofFailure::ResourceExhausted {
            operation: ProofOperation::UpdateClaimLifecycle,
        })
}

fn try_exact_qorf_entries(
    entries: &[QorfReplayParentEntry],
) -> Result<Vec<QorfReplayParentEntry>, std::collections::TryReserveError> {
    let mut output = Vec::new();
    output.try_reserve_exact(entries.len())?;
    output.extend_from_slice(entries);
    Ok(output)
}

fn try_qorf_resulting_side_len(
    existing: ReplayParentSideIndex,
    accepted_len: usize,
) -> Result<u32, ProofFailure> {
    let exhausted = || ProofFailure::ResourceExhausted {
        operation: ProofOperation::UpdateClaimLifecycle,
    };
    let accepted_len = u32::try_from(accepted_len).map_err(|_| exhausted())?;
    existing.len.checked_add(accepted_len).ok_or_else(exhausted)
}

fn try_build_qorf_balanced_chunks(
    entries: &[QorfReplayParentEntry],
    arena_base: usize,
) -> Result<(Vec<ReplayParentChunkNode>, Option<ReplayParentChunkId>), ProofFailure> {
    if entries.is_empty() {
        return Ok((Vec::new(), None));
    }
    let exhausted = |_| ProofFailure::ResourceExhausted {
        operation: ProofOperation::UpdateClaimLifecycle,
    };
    let chunk_count = entries.len().div_ceil(QORF_REPLAY_PARENT_CHUNK_CAPACITY);
    let mut chunks = Vec::new();
    chunks.try_reserve_exact(chunk_count).map_err(exhausted)?;
    for chunk in entries.chunks(QORF_REPLAY_PARENT_CHUNK_CAPACITY) {
        chunks.push(try_exact_qorf_entries(chunk).map_err(exhausted)?);
    }
    fn build(
        chunks: &mut [Vec<QorfReplayParentEntry>],
        start: usize,
        end: usize,
        arena_base: usize,
        output: &mut Vec<ReplayParentChunkNode>,
    ) -> Result<Option<ReplayParentChunkId>, ProofFailure> {
        if start == end {
            return Ok(None);
        }
        let middle = start + (end - start) / 2;
        let left = build(chunks, start, middle, arena_base, output)?;
        let right = build(chunks, middle + 1, end, arena_base, output)?;
        let id = try_replay_parent_chunk_id(arena_base + output.len())?;
        let height = 1 + left
            .map_or(0, |id| output[id.0 as usize - arena_base].height)
            .max(right.map_or(0, |id| output[id.0 as usize - arena_base].height));
        output.push(ReplayParentChunkNode {
            entries: std::mem::take(&mut chunks[middle]),
            left,
            right,
            height,
        });
        Ok(Some(id))
    }
    let mut nodes = Vec::new();
    nodes.try_reserve_exact(chunk_count).map_err(exhausted)?;
    let root = build(&mut chunks, 0, chunk_count, arena_base, &mut nodes)?;
    Ok((nodes, root))
}

fn try_prepare_qorf_side_delta(
    arena: &ReplayParentChunkArena,
    side: ReplayClaimParentSide,
    existing: ReplayParentSideIndex,
    mut accepted: Vec<QorfReplayParentEntry>,
    arena_base: usize,
) -> Result<Option<PreparedReplayParentSideShadowDelta>, ProofFailure> {
    if accepted.is_empty() {
        return Ok(None);
    }
    let exhausted = |_| ProofFailure::ResourceExhausted {
        operation: ProofOperation::UpdateClaimLifecycle,
    };
    accepted.sort_unstable_by_key(|entry| entry.coverage_root);
    accepted.dedup_by_key(|entry| entry.coverage_root);
    #[cfg(test)]
    QORF_REPLAY_SIDE_OPERATION_CENSUS.with(|cell| {
        let mut census = cell.get();
        census.admission_events += 1;
        census.accepted_parents += accepted.len();
        cell.set(census);
    });
    if existing.root.is_none() {
        let accepted_len = accepted.len();
        let resulting_len = try_qorf_resulting_side_len(existing, accepted_len)?;
        let (new_nodes, new_root) = try_build_qorf_balanced_chunks(&accepted, arena_base)?;
        #[cfg(test)]
        QORF_REPLAY_SIDE_OPERATION_CENSUS.with(|cell| {
            let mut census = cell.get();
            census.created_chunks += new_nodes.len();
            cell.set(census);
        });
        return Ok(Some(PreparedReplayParentSideShadowDelta {
            side,
            replacements: Vec::new(),
            new_nodes,
            new_root,
            first_new_node_index: arena_base,
            resulting_len,
        }));
    }

    let root = existing.root.expect("nonempty QORF side has a root");
    let mut routed = Vec::new();
    routed
        .try_reserve_exact(accepted.len())
        .map_err(exhausted)?;
    for entry in accepted {
        if arena.contains(existing, entry.coverage_root) {
            continue;
        }
        routed.push((arena.target_chunk(root, entry.coverage_root), entry));
    }
    if routed.is_empty() {
        return Ok(None);
    }
    routed.sort_unstable_by_key(|(id, entry)| (id.0, entry.coverage_root));
    let mut replacements = Vec::new();
    let mut new_nodes = Vec::new();
    replacements
        .try_reserve_exact(routed.len())
        .map_err(exhausted)?;
    new_nodes
        .try_reserve_exact(routed.len())
        .map_err(exhausted)?;
    let accepted_len = routed.len();
    let resulting_len = try_qorf_resulting_side_len(existing, accepted_len)?;
    let mut cursor = 0;
    while cursor < routed.len() {
        let target = routed[cursor].0;
        let end = cursor
            + routed[cursor..]
                .iter()
                .take_while(|(id, _)| *id == target)
                .count();
        let existing_entries = &arena.node(target).entries;
        #[cfg(test)]
        QORF_REPLAY_SIDE_OPERATION_CENSUS.with(|cell| {
            let mut census = cell.get();
            census.scanned_existing += existing_entries.len();
            census.max_scanned_existing = census.max_scanned_existing.max(existing_entries.len());
            cell.set(census);
        });
        let mut merged = Vec::new();
        merged
            .try_reserve_exact(existing_entries.len() + end - cursor)
            .map_err(exhausted)?;
        merged.extend_from_slice(existing_entries);
        merged.extend(routed[cursor..end].iter().map(|(_, entry)| *entry));
        merged.sort_unstable_by_key(|entry| entry.coverage_root);
        merged.dedup_by_key(|entry| entry.coverage_root);
        let output_count = merged.len().div_ceil(QORF_REPLAY_PARENT_CHUNK_CAPACITY);
        let base_len = merged.len() / output_count;
        let longer_outputs = merged.len() % output_count;
        let mut output_cursor = 0;
        for output_index in 0..output_count {
            let output_len = base_len + usize::from(output_index < longer_outputs);
            let output = &merged[output_cursor..output_cursor + output_len];
            output_cursor += output_len;
            if output_index == 0 {
                replacements.push((target, try_exact_qorf_entries(output).map_err(exhausted)?));
                continue;
            }
            let id = try_replay_parent_chunk_id(arena_base + new_nodes.len())?;
            let _ = id;
            new_nodes.push(ReplayParentChunkNode {
                entries: try_exact_qorf_entries(output).map_err(exhausted)?,
                left: None,
                right: None,
                height: 1,
            });
            #[cfg(test)]
            QORF_REPLAY_SIDE_OPERATION_CENSUS.with(|cell| {
                let mut census = cell.get();
                census.created_chunks += 1;
                census.split_chunks += 1;
                cell.set(census);
            });
        }
        debug_assert_eq!(output_cursor, merged.len());
        cursor = end;
    }
    Ok(Some(PreparedReplayParentSideShadowDelta {
        side,
        replacements,
        new_nodes,
        new_root: None,
        first_new_node_index: arena_base,
        resulting_len,
    }))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct ReplayQualifiedArmTree {
    root: Option<ReplayQualifiedArmChunkId>,
    len: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ReplayQualifiedArmChunkNode {
    entries: Vec<ReplayFiniteMapEntryId>,
    left: Option<ReplayQualifiedArmChunkId>,
    right: Option<ReplayQualifiedArmChunkId>,
    height: u8,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct ReplayQualifiedArmIndex {
    by_result: FxHashMap<ConstraintRecordId, ReplayQualifiedArmTree>,
    chunks: Vec<ReplayQualifiedArmChunkNode>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CanonicalQualifiedParentRef {
    Replay {
        finite_map_id: ReplayFiniteMapEntryId,
        side: ReplayClaimParentSide,
    },
    NonReplay {
        parent_id: NonReplayQualifiedParentId,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CanonicalQualifiedParentRootEntry {
    coverage_root: UpperReplayClaimId,
    winner: CanonicalQualifiedParentRef,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct CanonicalQualifiedParentRootTree {
    root: Option<CanonicalQualifiedParentRootChunkId>,
    len: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CanonicalQualifiedParentRootChunkNode {
    entries: Vec<CanonicalQualifiedParentRootEntry>,
    left: Option<CanonicalQualifiedParentRootChunkId>,
    right: Option<CanonicalQualifiedParentRootChunkId>,
    height: u8,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct CanonicalQualifiedParentRootIndex {
    by_result: FxHashMap<ConstraintRecordId, CanonicalQualifiedParentRootTree>,
    chunks: Vec<CanonicalQualifiedParentRootChunkNode>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct NonReplayQualifiedParentStore {
    entries: Vec<ExactQualifiedParent>,
    by_result: FxHashMap<ConstraintRecordId, Vec<NonReplayQualifiedParentId>>,
}

enum QorfExactQualifiedParentSource<'a> {
    Replay {
        carrier: BinaryReplayDerivation,
        cursor: ReplayParentSideCursor<'a>,
    },
    NonReplay {
        entries: &'a [ExactQualifiedParent],
        ids: &'a [NonReplayQualifiedParentId],
        position: usize,
    },
}

impl QorfExactQualifiedParentSource<'_> {
    fn next_parent(&mut self) -> Option<ExactQualifiedParent> {
        match self {
            Self::Replay { carrier, cursor } => cursor.next().map(|entry| ExactQualifiedParent {
                coverage_root: entry.coverage_root,
                parent: ClaimQualifiedParent::ReplayConstraint {
                    parent_claim: entry.representative_claim,
                    parent_side: entry.side,
                    replay: *carrier,
                },
            }),
            Self::NonReplay {
                entries,
                ids,
                position,
            } => {
                let id = *ids.get(*position)?;
                *position += 1;
                Some(entries[id.0 as usize])
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct QorfExactQualifiedParentHeapEntry {
    parent: ExactQualifiedParent,
    source: usize,
}

impl PartialEq for QorfExactQualifiedParentHeapEntry {
    fn eq(&self, other: &Self) -> bool {
        self.source == other.source
            && qualified_parent_entry_cmp(&self.parent, &other.parent).is_eq()
    }
}

impl Eq for QorfExactQualifiedParentHeapEntry {}

impl PartialOrd for QorfExactQualifiedParentHeapEntry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for QorfExactQualifiedParentHeapEntry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // BinaryHeap is a max-heap; reverse the canonical comparison so pop yields the minimum.
        qualified_parent_entry_cmp(&other.parent, &self.parent)
            .then_with(|| other.source.cmp(&self.source))
    }
}

struct QorfExactQualifiedParentCursor<'a> {
    sources: Vec<QorfExactQualifiedParentSource<'a>>,
    frontier: std::collections::BinaryHeap<QorfExactQualifiedParentHeapEntry>,
}

impl Iterator for QorfExactQualifiedParentCursor<'_> {
    type Item = ExactQualifiedParent;

    fn next(&mut self) -> Option<Self::Item> {
        let head = self.frontier.pop()?;
        if let Some(parent) = self.sources[head.source].next_parent() {
            // Construction reserves one slot per source. Every pop frees the slot reused here,
            // so iteration cannot allocate after the fallible constructor succeeds.
            self.frontier.push(QorfExactQualifiedParentHeapEntry {
                parent,
                source: head.source,
            });
        }
        Some(head.parent)
    }
}

struct QorfClauseLinkAssociationCursor<'a> {
    exact: QorfExactQualifiedParentCursor<'a>,
    previous: Option<(UpperReplayClaimId, ProjectionProofCarrier)>,
}

impl Iterator for QorfClauseLinkAssociationCursor<'_> {
    type Item = ExactQualifiedParent;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let parent = self.exact.next()?;
            let key = (
                parent.coverage_root,
                qualified_parent_projection_carrier(parent.parent),
            );
            if self.previous == Some(key) {
                continue;
            }
            self.previous = Some(key);
            return Some(parent);
        }
    }
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct QorfPreparedReplayParentSideDelta {
    side: ReplayClaimParentSide,
    accepted: Vec<QorfReplayParentEntry>,
    replacement_chunks: Vec<ReplayParentChunkNode>,
}

#[derive(Debug)]
struct QorfPreparedChunkBuffers<T> {
    merged: Vec<T>,
    right: Vec<T>,
}

#[derive(Debug)]
struct QorfPreparedReplayQualifiedArmEdit {
    result: ConstraintRecordId,
    occurrence: ReplayFiniteMapEntryId,
    rekey: bool,
    buffers: QorfPreparedChunkBuffers<ReplayFiniteMapEntryId>,
}

#[derive(Debug)]
struct QorfPreparedCanonicalRootWinnerUpdate {
    result: ConstraintRecordId,
    entry: CanonicalQualifiedParentRootEntry,
    buffers: QorfPreparedChunkBuffers<CanonicalQualifiedParentRootEntry>,
}

impl<T> QorfPreparedChunkBuffers<T> {
    fn try_new() -> Result<Self, ProofFailure> {
        let exhausted = |_| ProofFailure::ResourceExhausted {
            operation: ProofOperation::UpdateClaimLifecycle,
        };
        let mut merged = Vec::new();
        let mut right = Vec::new();
        merged
            .try_reserve_exact(QORF_REPLAY_PARENT_CHUNK_CAPACITY + 1)
            .map_err(exhausted)?;
        right
            .try_reserve_exact(QORF_REPLAY_PARENT_CHUNK_CAPACITY / 2 + 1)
            .map_err(exhausted)?;
        Ok(Self { merged, right })
    }
}

impl ReplayQualifiedArmIndex {
    fn height(&self, id: Option<ReplayQualifiedArmChunkId>) -> u8 {
        id.map_or(0, |id| self.chunks[id.0 as usize].height)
    }

    fn update_height(&mut self, id: ReplayQualifiedArmChunkId) {
        let node = &self.chunks[id.0 as usize];
        self.chunks[id.0 as usize].height = 1 + self.height(node.left).max(self.height(node.right));
    }

    fn rotate_left(&mut self, root: ReplayQualifiedArmChunkId) -> ReplayQualifiedArmChunkId {
        let pivot = self.chunks[root.0 as usize]
            .right
            .expect("QORF arm left rotation requires a right child");
        let middle = self.chunks[pivot.0 as usize].left;
        self.chunks[root.0 as usize].right = middle;
        self.update_height(root);
        self.chunks[pivot.0 as usize].left = Some(root);
        self.update_height(pivot);
        pivot
    }

    fn rotate_right(&mut self, root: ReplayQualifiedArmChunkId) -> ReplayQualifiedArmChunkId {
        let pivot = self.chunks[root.0 as usize]
            .left
            .expect("QORF arm right rotation requires a left child");
        let middle = self.chunks[pivot.0 as usize].right;
        self.chunks[root.0 as usize].left = middle;
        self.update_height(root);
        self.chunks[pivot.0 as usize].right = Some(root);
        self.update_height(pivot);
        pivot
    }

    fn rebalance(&mut self, root: ReplayQualifiedArmChunkId) -> ReplayQualifiedArmChunkId {
        self.update_height(root);
        let node = &self.chunks[root.0 as usize];
        let balance = i16::from(self.height(node.left)) - i16::from(self.height(node.right));
        if balance > 1 {
            let left = node.left.expect("left-heavy QORF arm node has a child");
            if self.height(self.chunks[left.0 as usize].right)
                > self.height(self.chunks[left.0 as usize].left)
            {
                let rotated = self.rotate_left(left);
                self.chunks[root.0 as usize].left = Some(rotated);
            }
            return self.rotate_right(root);
        }
        if balance < -1 {
            let right = node.right.expect("right-heavy QORF arm node has a child");
            if self.height(self.chunks[right.0 as usize].left)
                > self.height(self.chunks[right.0 as usize].right)
            {
                let rotated = self.rotate_right(right);
                self.chunks[root.0 as usize].right = Some(rotated);
            }
            return self.rotate_left(root);
        }
        root
    }

    fn insert_node(
        &mut self,
        root: Option<ReplayQualifiedArmChunkId>,
        inserted: ReplayQualifiedArmChunkId,
        cmp: &impl Fn(ReplayFiniteMapEntryId, ReplayFiniteMapEntryId) -> std::cmp::Ordering,
    ) -> ReplayQualifiedArmChunkId {
        let Some(root) = root else { return inserted };
        let inserted_first = self.chunks[inserted.0 as usize].entries[0];
        let root_first = self.chunks[root.0 as usize].entries[0];
        if cmp(inserted_first, root_first).is_lt() {
            let child = self.insert_node(self.chunks[root.0 as usize].left, inserted, cmp);
            self.chunks[root.0 as usize].left = Some(child);
        } else {
            assert!(cmp(inserted_first, root_first).is_gt());
            let child = self.insert_node(self.chunks[root.0 as usize].right, inserted, cmp);
            self.chunks[root.0 as usize].right = Some(child);
        }
        self.rebalance(root)
    }

    fn detach_min(
        &mut self,
        root: ReplayQualifiedArmChunkId,
    ) -> (ReplayQualifiedArmChunkId, Option<ReplayQualifiedArmChunkId>) {
        let Some(left) = self.chunks[root.0 as usize].left else {
            return (root, self.chunks[root.0 as usize].right);
        };
        let (minimum, new_left) = self.detach_min(left);
        self.chunks[root.0 as usize].left = new_left;
        (minimum, Some(self.rebalance(root)))
    }

    fn unlink_node(
        &mut self,
        root: Option<ReplayQualifiedArmChunkId>,
        removed: ReplayQualifiedArmChunkId,
        cmp: &impl Fn(ReplayFiniteMapEntryId, ReplayFiniteMapEntryId) -> std::cmp::Ordering,
    ) -> Option<ReplayQualifiedArmChunkId> {
        let root = root.expect("QORF arm removal target must exist");
        if root != removed {
            let removed_first = self.chunks[removed.0 as usize].entries[0];
            let root_first = self.chunks[root.0 as usize].entries[0];
            if cmp(removed_first, root_first).is_lt() {
                self.chunks[root.0 as usize].left =
                    self.unlink_node(self.chunks[root.0 as usize].left, removed, cmp);
            } else {
                self.chunks[root.0 as usize].right =
                    self.unlink_node(self.chunks[root.0 as usize].right, removed, cmp);
            }
            return Some(self.rebalance(root));
        }
        let (left, right) = {
            let node = &self.chunks[root.0 as usize];
            (node.left, node.right)
        };
        match (left, right) {
            (None, right) => right,
            (left, None) => left,
            (Some(left), Some(right)) => {
                let (successor, new_right) = self.detach_min(right);
                self.chunks[successor.0 as usize].left = Some(left);
                self.chunks[successor.0 as usize].right = new_right;
                Some(self.rebalance(successor))
            }
        }
    }

    fn target_chunk(
        &self,
        mut root: ReplayQualifiedArmChunkId,
        entry: ReplayFiniteMapEntryId,
        cmp: &impl Fn(ReplayFiniteMapEntryId, ReplayFiniteMapEntryId) -> std::cmp::Ordering,
    ) -> ReplayQualifiedArmChunkId {
        loop {
            let node = &self.chunks[root.0 as usize];
            if cmp(entry, node.entries[0]).is_lt() {
                if let Some(left) = node.left {
                    root = left;
                    continue;
                }
            } else if cmp(entry, *node.entries.last().unwrap()).is_gt() {
                if let Some(right) = node.right {
                    root = right;
                    continue;
                }
            }
            return root;
        }
    }

    fn remove(
        &mut self,
        result: ConstraintRecordId,
        entry: ReplayFiniteMapEntryId,
        cmp: &impl Fn(ReplayFiniteMapEntryId, ReplayFiniteMapEntryId) -> std::cmp::Ordering,
    ) -> Option<ReplayQualifiedArmChunkId> {
        let tree = self.by_result[&result];
        let target = self.target_chunk(tree.root.unwrap(), entry, cmp);
        let position = self.chunks[target.0 as usize]
            .entries
            .iter()
            .position(|candidate| *candidate == entry)
            .expect("QORF arm rekey must remove its existing occurrence");
        let singleton = self.chunks[target.0 as usize].entries.len() == 1;
        let new_root = if singleton {
            self.unlink_node(tree.root, target, cmp)
        } else {
            self.chunks[target.0 as usize].entries.remove(position);
            tree.root
        };
        let tree = self.by_result.get_mut(&result).unwrap();
        tree.root = new_root;
        tree.len -= 1;
        singleton.then_some(target)
    }

    fn insert(
        &mut self,
        result: ConstraintRecordId,
        entry: ReplayFiniteMapEntryId,
        recycled: Option<ReplayQualifiedArmChunkId>,
        mut buffers: QorfPreparedChunkBuffers<ReplayFiniteMapEntryId>,
        cmp: &impl Fn(ReplayFiniteMapEntryId, ReplayFiniteMapEntryId) -> std::cmp::Ordering,
    ) {
        let tree = self.by_result.get(&result).copied().unwrap_or_default();
        let Some(root) = tree.root else {
            buffers.merged.push(entry);
            let node = ReplayQualifiedArmChunkNode {
                entries: buffers.merged,
                left: None,
                right: None,
                height: 1,
            };
            let id = if let Some(id) = recycled {
                self.chunks[id.0 as usize] = node;
                id
            } else {
                let id = ReplayQualifiedArmChunkId(self.chunks.len() as u32);
                self.chunks.push(node);
                id
            };
            self.by_result.insert(
                result,
                ReplayQualifiedArmTree {
                    root: Some(id),
                    len: 1,
                },
            );
            return;
        };
        // A singleton removed for a rekey owns an arena slot that is no longer reachable from
        // the AVL. Reinsert through that same slot instead of appending a replacement node. This
        // keeps physical arm chunks bounded by the logical arm population even when one
        // occurrence is repeatedly rekeyed to a smaller canonical minimum.
        if let Some(id) = recycled {
            buffers.merged.push(entry);
            self.chunks[id.0 as usize] = ReplayQualifiedArmChunkNode {
                entries: buffers.merged,
                left: None,
                right: None,
                height: 1,
            };
            let root = self.insert_node(Some(root), id, cmp);
            let tree = self.by_result.get_mut(&result).unwrap();
            tree.root = Some(root);
            tree.len += 1;
            return;
        }
        let target = self.target_chunk(root, entry, cmp);
        buffers
            .merged
            .extend_from_slice(&self.chunks[target.0 as usize].entries);
        let position = buffers
            .merged
            .binary_search_by(|candidate| cmp(*candidate, entry))
            .expect_err("QORF arm occurrence must be unique");
        buffers.merged.insert(position, entry);
        if buffers.merged.len() <= QORF_REPLAY_PARENT_CHUNK_CAPACITY {
            self.chunks[target.0 as usize].entries = buffers.merged;
        } else {
            let middle = buffers.merged.len() / 2;
            buffers.right.extend(buffers.merged.drain(middle..));
            self.chunks[target.0 as usize].entries = buffers.merged;
            let inserted = ReplayQualifiedArmChunkId(self.chunks.len() as u32);
            self.chunks.push(ReplayQualifiedArmChunkNode {
                entries: buffers.right,
                left: None,
                right: None,
                height: 1,
            });
            let root = self.insert_node(Some(root), inserted, cmp);
            self.by_result.get_mut(&result).unwrap().root = Some(root);
        }
        self.by_result.get_mut(&result).unwrap().len += 1;
    }

    #[cfg(test)]
    fn flatten(&self, result: ConstraintRecordId) -> Vec<ReplayFiniteMapEntryId> {
        fn append(
            index: &ReplayQualifiedArmIndex,
            node: Option<ReplayQualifiedArmChunkId>,
            output: &mut Vec<ReplayFiniteMapEntryId>,
        ) {
            let Some(node) = node else { return };
            let chunk = &index.chunks[node.0 as usize];
            append(index, chunk.left, output);
            output.extend_from_slice(&chunk.entries);
            append(index, chunk.right, output);
        }
        let mut output = Vec::new();
        let tree = self.by_result.get(&result).copied().unwrap_or_default();
        output.reserve(tree.len as usize);
        append(self, tree.root, &mut output);
        output
    }
}

impl CanonicalQualifiedParentRootIndex {
    fn height(&self, id: Option<CanonicalQualifiedParentRootChunkId>) -> u8 {
        id.map_or(0, |id| self.chunks[id.0 as usize].height)
    }

    fn update_height(&mut self, id: CanonicalQualifiedParentRootChunkId) {
        let node = &self.chunks[id.0 as usize];
        self.chunks[id.0 as usize].height = 1 + self.height(node.left).max(self.height(node.right));
    }

    fn rotate_left(
        &mut self,
        root: CanonicalQualifiedParentRootChunkId,
    ) -> CanonicalQualifiedParentRootChunkId {
        let pivot = self.chunks[root.0 as usize].right.unwrap();
        self.chunks[root.0 as usize].right = self.chunks[pivot.0 as usize].left;
        self.update_height(root);
        self.chunks[pivot.0 as usize].left = Some(root);
        self.update_height(pivot);
        pivot
    }

    fn rotate_right(
        &mut self,
        root: CanonicalQualifiedParentRootChunkId,
    ) -> CanonicalQualifiedParentRootChunkId {
        let pivot = self.chunks[root.0 as usize].left.unwrap();
        self.chunks[root.0 as usize].left = self.chunks[pivot.0 as usize].right;
        self.update_height(root);
        self.chunks[pivot.0 as usize].right = Some(root);
        self.update_height(pivot);
        pivot
    }

    fn rebalance(
        &mut self,
        root: CanonicalQualifiedParentRootChunkId,
    ) -> CanonicalQualifiedParentRootChunkId {
        self.update_height(root);
        let node = &self.chunks[root.0 as usize];
        let balance = i16::from(self.height(node.left)) - i16::from(self.height(node.right));
        if balance > 1 {
            let left = node.left.unwrap();
            if self.height(self.chunks[left.0 as usize].right)
                > self.height(self.chunks[left.0 as usize].left)
            {
                let rotated = self.rotate_left(left);
                self.chunks[root.0 as usize].left = Some(rotated);
            }
            return self.rotate_right(root);
        }
        if balance < -1 {
            let right = node.right.unwrap();
            if self.height(self.chunks[right.0 as usize].left)
                > self.height(self.chunks[right.0 as usize].right)
            {
                let rotated = self.rotate_right(right);
                self.chunks[root.0 as usize].right = Some(rotated);
            }
            return self.rotate_left(root);
        }
        root
    }

    fn insert_node(
        &mut self,
        root: Option<CanonicalQualifiedParentRootChunkId>,
        inserted: CanonicalQualifiedParentRootChunkId,
    ) -> CanonicalQualifiedParentRootChunkId {
        let Some(root) = root else { return inserted };
        let incoming = self.chunks[inserted.0 as usize].entries[0].coverage_root;
        let current = self.chunks[root.0 as usize].entries[0].coverage_root;
        if incoming < current {
            let child = self.insert_node(self.chunks[root.0 as usize].left, inserted);
            self.chunks[root.0 as usize].left = Some(child);
        } else {
            assert!(incoming > current);
            let child = self.insert_node(self.chunks[root.0 as usize].right, inserted);
            self.chunks[root.0 as usize].right = Some(child);
        }
        self.rebalance(root)
    }

    fn target_chunk(
        &self,
        mut root: CanonicalQualifiedParentRootChunkId,
        key: UpperReplayClaimId,
    ) -> CanonicalQualifiedParentRootChunkId {
        loop {
            let node = &self.chunks[root.0 as usize];
            if key < node.entries[0].coverage_root {
                if let Some(left) = node.left {
                    root = left;
                    continue;
                }
            } else if key > node.entries.last().unwrap().coverage_root {
                if let Some(right) = node.right {
                    root = right;
                    continue;
                }
            }
            return root;
        }
    }

    fn get(
        &self,
        result: ConstraintRecordId,
        key: UpperReplayClaimId,
    ) -> Option<CanonicalQualifiedParentRootEntry> {
        let root = self.by_result.get(&result)?.root?;
        let target = self.target_chunk(root, key);
        let entries = &self.chunks[target.0 as usize].entries;
        entries
            .binary_search_by_key(&key, |entry| entry.coverage_root)
            .ok()
            .map(|index| entries[index])
    }

    fn apply(&mut self, update: QorfPreparedCanonicalRootWinnerUpdate) {
        let result = update.result;
        let entry = update.entry;
        let mut buffers = update.buffers;
        let tree = self.by_result.get(&result).copied().unwrap_or_default();
        let Some(root) = tree.root else {
            buffers.merged.push(entry);
            let id = CanonicalQualifiedParentRootChunkId(self.chunks.len() as u32);
            self.chunks.push(CanonicalQualifiedParentRootChunkNode {
                entries: buffers.merged,
                left: None,
                right: None,
                height: 1,
            });
            self.by_result.insert(
                result,
                CanonicalQualifiedParentRootTree {
                    root: Some(id),
                    len: 1,
                },
            );
            return;
        };
        let target = self.target_chunk(root, entry.coverage_root);
        let existing = &self.chunks[target.0 as usize].entries;
        match existing.binary_search_by_key(&entry.coverage_root, |entry| entry.coverage_root) {
            Ok(position) => self.chunks[target.0 as usize].entries[position] = entry,
            Err(position) => {
                buffers.merged.extend_from_slice(existing);
                buffers.merged.insert(position, entry);
                if buffers.merged.len() <= QORF_REPLAY_PARENT_CHUNK_CAPACITY {
                    self.chunks[target.0 as usize].entries = buffers.merged;
                } else {
                    let middle = buffers.merged.len() / 2;
                    buffers.right.extend(buffers.merged.drain(middle..));
                    self.chunks[target.0 as usize].entries = buffers.merged;
                    let inserted = CanonicalQualifiedParentRootChunkId(self.chunks.len() as u32);
                    self.chunks.push(CanonicalQualifiedParentRootChunkNode {
                        entries: buffers.right,
                        left: None,
                        right: None,
                        height: 1,
                    });
                    let root = self.insert_node(Some(root), inserted);
                    self.by_result.get_mut(&result).unwrap().root = Some(root);
                }
                self.by_result.get_mut(&result).unwrap().len += 1;
            }
        }
    }

    #[cfg(test)]
    fn flatten(&self, result: ConstraintRecordId) -> Vec<CanonicalQualifiedParentRootEntry> {
        fn append(
            index: &CanonicalQualifiedParentRootIndex,
            node: Option<CanonicalQualifiedParentRootChunkId>,
            output: &mut Vec<CanonicalQualifiedParentRootEntry>,
        ) {
            let Some(node) = node else { return };
            let chunk = &index.chunks[node.0 as usize];
            append(index, chunk.left, output);
            output.extend_from_slice(&chunk.entries);
            append(index, chunk.right, output);
        }
        let mut output = Vec::new();
        let tree = self.by_result.get(&result).copied().unwrap_or_default();
        output.reserve(tree.len as usize);
        append(self, tree.root, &mut output);
        output
    }
}

/// QORF-A's non-authoritative constructor boundary: all frontier allocation is fallible before an
/// eventual cursor is published, while iteration itself cannot allocate or report exhaustion.
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct QorfPreparedCursorFrontier {
    active_sources: usize,
    reserved_capacity: usize,
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

/// One capacity-preflighted CPK support-ledger mutation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct PreparedProjectionSupportMutation {
    pub(super) lower_record: BoundRecordId,
    pub(super) current_supports: Vec<SchemeProjectionProofSupport>,
    pub(super) current_claims: Vec<UpperReplayClaimId>,
    pub(super) new_root_memberships: Vec<UpperReplayClaimId>,
    new_root_record_entries: Vec<(UpperReplayClaimId, Vec<BoundRecordId>)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct AcceptedProjectionClauseAdmission {
    pub(super) admission: RecordProofClauseLinkAdmission,
    pub(super) clause_inserted: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct PreparedProjectionClauseAdmission {
    lower_record: BoundRecordId,
    accepted: Vec<AcceptedProjectionClauseAdmission>,
    #[cfg(test)]
    new_clause_keys: Vec<(BoundRecordId, RecordProofClause)>,
    #[cfg(test)]
    new_link_keys: Vec<(
        BoundRecordId,
        SchemeProjectionProofSupport,
        RecordProofClause,
    )>,
    #[cfg(test)]
    canonical_formula: Vec<ProjectionClause>,
    #[cfg(test)]
    formula_support_keys: FxHashSet<ProjectionSupportMatchKey>,
    #[cfg(test)]
    new_claimed_link_audit_entries: Vec<(
        RawProjectionClauseLinkIdentity,
        ClaimedProjectionProofSource,
    )>,
    #[cfg(test)]
    new_projection_attributions: Vec<(BoundRecordId, UpperReplayClaimId)>,
    #[cfg(test)]
    new_flat_retained_projection_attributions: Vec<(BoundRecordId, UpperReplayClaimId)>,
    shadow: PreparedProjectionFormulaShadowAdmission,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PreparedProjectionFormulaShadowAdmission {
    new_record_bucket: Option<ProjectionFormulaBucket>,
    delta: ProjectionFormulaShadowDelta,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct ProjectionFormulaShadowDelta {
    new_entries: Vec<ProjectionFormulaEntry>,
    new_support_groups: Vec<ProjectionSupportGroup>,
    exact_links: Vec<(
        ProjectionSupportGroupId,
        ProjectionFormulaEntryId,
        ProjectionIncidenceMetadata,
    )>,
    canonical_run_deltas: Vec<PreparedCanonicalProjectionRunDelta>,
    new_canonical_runs: Vec<CanonicalProjectionRun>,
    support_match_key_promotions: Vec<(ProjectionSupportGroupId, ProjectionSupportMatchKey)>,
    normalized_support_keys: FxHashSet<ProjectionSupportMatchKey>,
    attributed_roots: Vec<UpperReplayClaimId>,
    flat_retained_attributed_roots: Vec<UpperReplayClaimId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PreparedCanonicalProjectionRunDelta {
    category: CanonicalProjectionCategory,
    support_id: ProjectionSupportGroupId,
    existing_run_index: usize,
    entry_count: usize,
    chunks: Vec<PreparedCanonicalProjectionChunkDelta>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PreparedCanonicalProjectionChunkDelta {
    target_pivot: ProjectionFormulaEntryId,
    replacement_entries: Vec<ProjectionFormulaEntryId>,
    new_chunks: Vec<ProjectionRunChunkBox>,
    lookup_comparisons: usize,
    merge_comparisons: usize,
    scanned_existing: usize,
    moved_entries: usize,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ProjectionClauseReservationFailurePoint {
    Initial,
    AfterLegacyPreflight,
    ShadowStructure,
    ShadowCanonicalRuns,
    ShadowNormalizedSupport,
}

impl PreparedProjectionClauseAdmission {
    pub(super) fn accepted(&self) -> &[AcceptedProjectionClauseAdmission] {
        &self.accepted
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ProjectionClause {
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

/// The exact claimed OR-arm frozen at clause admission time.
///
/// `representative_claim` is audit payload only. [`ClaimedProjectionProofKey`] normalizes it to
/// `coverage_root`, so representative replacement cannot change semantic certificate identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClaimedProjectionProof {
    kind: ClaimedProjectionProofKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ClaimedProjectionProofKind {
    Standalone {
        bound: BoundRecordId,
        coverage_root: UpperReplayClaimId,
        representative_claim: UpperReplayClaimId,
        producer: ConstraintRecordId,
        attribution: ClaimedProjectionProofAttribution,
    },
    DerivedUnary {
        bound: BoundRecordId,
        coverage_root: UpperReplayClaimId,
        representative_claim: UpperReplayClaimId,
        result: ConstraintRecordId,
        carrier: DerivedUnaryCarrier,
        premise: ProofPremise,
        attribution: ClaimedProjectionProofAttribution,
    },
    ReplayConjunction {
        bound: BoundRecordId,
        coverage_root: UpperReplayClaimId,
        representative_claim: UpperReplayClaimId,
        carrier: BinaryReplayDerivation,
        lower_premise: BoundRecordId,
        upper_premise: BoundRecordId,
        attribution: ClaimedProjectionProofAttribution,
    },
}

impl ClaimedProjectionProof {
    fn new(kind: ClaimedProjectionProofKind) -> Self {
        Self { kind }
    }

    fn from_key(
        key: ClaimedProjectionProofKey,
        representative_claim: UpperReplayClaimId,
    ) -> Self {
        let kind = match key {
            ClaimedProjectionProofKey::Standalone {
                bound,
                coverage_root,
                producer,
                attribution,
                ..
            } => ClaimedProjectionProofKind::Standalone {
                bound,
                coverage_root,
                representative_claim,
                producer,
                attribution,
            },
            ClaimedProjectionProofKey::DerivedUnary {
                bound,
                coverage_root,
                result,
                carrier,
                premise,
                attribution,
            } => ClaimedProjectionProofKind::DerivedUnary {
                bound,
                coverage_root,
                representative_claim,
                result,
                carrier,
                premise,
                attribution,
            },
            ClaimedProjectionProofKey::ReplayConjunction {
                bound,
                coverage_root,
                carrier,
                lower_premise,
                upper_premise,
                attribution,
            } => ClaimedProjectionProofKind::ReplayConjunction {
                bound,
                coverage_root,
                representative_claim,
                carrier,
                lower_premise,
                upper_premise,
                attribution,
            },
        };
        Self::new(kind)
    }

    pub(crate) fn kind(&self) -> ClaimedProjectionProofKind {
        self.kind
    }

    pub(crate) fn bound(&self) -> BoundRecordId {
        match self.kind {
            ClaimedProjectionProofKind::Standalone { bound, .. }
            | ClaimedProjectionProofKind::DerivedUnary { bound, .. }
            | ClaimedProjectionProofKind::ReplayConjunction { bound, .. } => bound,
        }
    }

    pub(crate) fn coverage_root(&self) -> UpperReplayClaimId {
        match self.kind {
            ClaimedProjectionProofKind::Standalone { coverage_root, .. }
            | ClaimedProjectionProofKind::DerivedUnary { coverage_root, .. }
            | ClaimedProjectionProofKind::ReplayConjunction { coverage_root, .. } => coverage_root,
        }
    }

    pub(crate) fn representative_claim(&self) -> UpperReplayClaimId {
        match self.kind {
            ClaimedProjectionProofKind::Standalone {
                representative_claim,
                ..
            }
            | ClaimedProjectionProofKind::DerivedUnary {
                representative_claim,
                ..
            }
            | ClaimedProjectionProofKind::ReplayConjunction {
                representative_claim,
                ..
            } => representative_claim,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ClaimedProjectionProofAttribution {
    Original,
    StructuralConstraint,
    ReductionRouteConstraint,
    ReplayConstraint { result: ConstraintRecordId },
    ReplayEvidence,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ClaimedProjectionProofKey {
    Standalone {
        bound: BoundRecordId,
        coverage_root: UpperReplayClaimId,
        embedded_support: ProjectionSupportMatchKey,
        producer: ConstraintRecordId,
        attribution: ClaimedProjectionProofAttribution,
    },
    DerivedUnary {
        bound: BoundRecordId,
        coverage_root: UpperReplayClaimId,
        result: ConstraintRecordId,
        carrier: DerivedUnaryCarrier,
        premise: ProofPremise,
        attribution: ClaimedProjectionProofAttribution,
    },
    ReplayConjunction {
        bound: BoundRecordId,
        coverage_root: UpperReplayClaimId,
        carrier: BinaryReplayDerivation,
        lower_premise: BoundRecordId,
        upper_premise: BoundRecordId,
        attribution: ClaimedProjectionProofAttribution,
    },
}

type RawProjectionClauseLinkIdentity = (
    BoundRecordId,
    SchemeProjectionProofSupport,
    RecordProofClause,
);

// PCLF-C made exact-link and distinct-clause membership authoritative here; PCLF-D1 also reads
// formulas, evaluator arms, and GWCB evidence from this store. Legacy faces remain dual-written
// as parity oracles until PCLF-E.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ProjectionFormulaEntryId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ProjectionSupportGroupId(u32);

const PROJECTION_RUN_CHUNK_CAPACITY: usize = 128;

fn try_projection_support_group_id(
    index: usize,
) -> Result<ProjectionSupportGroupId, ProofFailure> {
    let raw = u32::try_from(index).map_err(|_| ProofFailure::ResourceExhausted {
        operation: ProofOperation::UpdateClaimLifecycle,
    })?;
    if raw == ProofEvalEvidenceMemo::STATE_TAG {
        return Err(ProofFailure::ResourceExhausted {
            operation: ProofOperation::UpdateClaimLifecycle,
        });
    }
    Ok(ProjectionSupportGroupId(raw))
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ProjectionFormulaEntry {
    clause: RecordProofClause,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ProjectionSupportGroup {
    raw_support: SchemeProjectionProofSupport,
    match_key: Option<ProjectionSupportMatchKey>,
    coverage_root: Option<UpperReplayClaimId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum CanonicalProjectionCategory {
    Standalone,
    DerivedUnary,
    ReplayConjunction,
}

impl CanonicalProjectionCategory {
    fn from_clause(clause: RecordProofClause) -> Self {
        match clause {
            RecordProofClause::Standalone { .. } => Self::Standalone,
            RecordProofClause::DerivedUnary { .. } => Self::DerivedUnary,
            RecordProofClause::ReplayConjunction { .. } => Self::ReplayConjunction,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CanonicalProjectionRun {
    category: CanonicalProjectionCategory,
    support_id: ProjectionSupportGroupId,
    chunk_root: Option<ProjectionRunChunkBox>,
    entry_len: usize,
}

type ProjectionRunChunkBox = Box<[ProjectionRunChunk]>;

#[derive(Debug, Clone, PartialEq, Eq)]
struct ProjectionRunChunk {
    entries: Vec<ProjectionFormulaEntryId>,
    left: Option<ProjectionRunChunkBox>,
    right: Option<ProjectionRunChunkBox>,
    height: u8,
}

impl CanonicalProjectionRun {
    fn merge_placeholder() -> Self {
        Self {
            category: CanonicalProjectionCategory::Standalone,
            support_id: ProjectionSupportGroupId(u32::MAX),
            chunk_root: None,
            entry_len: 0,
        }
    }

    fn try_box_chunk(
        entries: Vec<ProjectionFormulaEntryId>,
    ) -> Result<ProjectionRunChunkBox, std::collections::TryReserveError> {
        assert!(!entries.is_empty());
        assert!(entries.len() <= PROJECTION_RUN_CHUNK_CAPACITY);
        let mut allocation = Vec::new();
        allocation.try_reserve_exact(1)?;
        allocation.push(ProjectionRunChunk {
            entries,
            left: None,
            right: None,
            height: 1,
        });
        Ok(allocation.into_boxed_slice())
    }

    fn chunk(node: &ProjectionRunChunkBox) -> &ProjectionRunChunk {
        node.first().expect("PCLF chunk box must contain exactly one node")
    }

    fn chunk_mut(node: &mut ProjectionRunChunkBox) -> &mut ProjectionRunChunk {
        node.first_mut()
            .expect("PCLF chunk box must contain exactly one node")
    }

    fn from_sorted_entries(
        category: CanonicalProjectionCategory,
        support_id: ProjectionSupportGroupId,
        entries: Vec<ProjectionFormulaEntryId>,
    ) -> Result<Self, std::collections::TryReserveError> {
        assert!(!entries.is_empty());
        let chunk_count = entries.len().div_ceil(PROJECTION_RUN_CHUNK_CAPACITY);
        let base_len = entries.len() / chunk_count;
        let longer_chunks = entries.len() % chunk_count;
        fn chunk_start(index: usize, base_len: usize, longer_chunks: usize) -> usize {
            index * base_len + index.min(longer_chunks)
        }
        fn build(
            entries: &[ProjectionFormulaEntryId],
            start_chunk: usize,
            end_chunk: usize,
            base_len: usize,
            longer_chunks: usize,
        ) -> Result<Option<ProjectionRunChunkBox>, std::collections::TryReserveError> {
            if start_chunk == end_chunk {
                return Ok(None);
            }
            let middle = start_chunk + (end_chunk - start_chunk) / 2;
            let start = chunk_start(middle, base_len, longer_chunks);
            let end = chunk_start(middle + 1, base_len, longer_chunks);
            let mut chunk_entries = Vec::new();
            chunk_entries.try_reserve_exact(end - start)?;
            chunk_entries.extend_from_slice(&entries[start..end]);
            let mut node = CanonicalProjectionRun::try_box_chunk(chunk_entries)?;
            CanonicalProjectionRun::chunk_mut(&mut node).left = build(
                entries,
                start_chunk,
                middle,
                base_len,
                longer_chunks,
            )?;
            CanonicalProjectionRun::chunk_mut(&mut node).right = build(
                entries,
                middle + 1,
                end_chunk,
                base_len,
                longer_chunks,
            )?;
            CanonicalProjectionRun::update_chunk_height(&mut node);
            Ok(Some(node))
        }
        let root = build(&entries, 0, chunk_count, base_len, longer_chunks)?;
        Ok(Self {
            category,
            support_id,
            chunk_root: root,
            entry_len: entries.len(),
        })
    }

    fn chunk_height(node: &Option<ProjectionRunChunkBox>) -> u8 {
        node.as_ref().map_or(0, |node| Self::chunk(node).height)
    }

    fn update_chunk_height(node: &mut ProjectionRunChunkBox) {
        let chunk = Self::chunk(node);
        let height = 1 + Self::chunk_height(&chunk.left).max(Self::chunk_height(&chunk.right));
        Self::chunk_mut(node).height = height;
    }

    fn rotate_chunk_left(mut root: ProjectionRunChunkBox) -> ProjectionRunChunkBox {
        let mut right = Self::chunk_mut(&mut root)
            .right
            .take()
            .expect("AVL left rotation requires a right child");
        let middle = Self::chunk_mut(&mut right).left.take();
        Self::chunk_mut(&mut root).right = middle;
        Self::update_chunk_height(&mut root);
        Self::chunk_mut(&mut right).left = Some(root);
        Self::update_chunk_height(&mut right);
        right
    }

    fn rotate_chunk_right(mut root: ProjectionRunChunkBox) -> ProjectionRunChunkBox {
        let mut left = Self::chunk_mut(&mut root)
            .left
            .take()
            .expect("AVL right rotation requires a left child");
        let middle = Self::chunk_mut(&mut left).right.take();
        Self::chunk_mut(&mut root).left = middle;
        Self::update_chunk_height(&mut root);
        Self::chunk_mut(&mut left).right = Some(root);
        Self::update_chunk_height(&mut left);
        left
    }

    fn rebalance_chunk(mut root: ProjectionRunChunkBox) -> ProjectionRunChunkBox {
        Self::update_chunk_height(&mut root);
        let chunk = Self::chunk(&root);
        let balance = i16::from(Self::chunk_height(&chunk.left))
            - i16::from(Self::chunk_height(&chunk.right));
        if balance > 1 {
            let left = Self::chunk(&root)
                .left
                .as_ref()
                .expect("left-heavy AVL node must have a left child");
            if Self::chunk_height(&Self::chunk(left).left)
                < Self::chunk_height(&Self::chunk(left).right)
            {
                let left = Self::chunk_mut(&mut root).left.take().unwrap();
                Self::chunk_mut(&mut root).left = Some(Self::rotate_chunk_left(left));
            }
            return Self::rotate_chunk_right(root);
        }
        if balance < -1 {
            let right = Self::chunk(&root)
                .right
                .as_ref()
                .expect("right-heavy AVL node must have a right child");
            if Self::chunk_height(&Self::chunk(right).right)
                < Self::chunk_height(&Self::chunk(right).left)
            {
                let right = Self::chunk_mut(&mut root).right.take().unwrap();
                Self::chunk_mut(&mut root).right = Some(Self::rotate_chunk_right(right));
            }
            return Self::rotate_chunk_left(root);
        }
        root
    }

    fn insert_chunk_by<F>(
        root: Option<ProjectionRunChunkBox>,
        new_node: ProjectionRunChunkBox,
        compare: &F,
    ) -> ProjectionRunChunkBox
    where
        F: Fn(ProjectionFormulaEntryId, ProjectionFormulaEntryId) -> std::cmp::Ordering,
    {
        let Some(mut root) = root else {
            return new_node;
        };
        let new_pivot = Self::chunk(&new_node).entries[0];
        let root_pivot = Self::chunk(&root).entries[0];
        match compare(new_pivot, root_pivot) {
            std::cmp::Ordering::Less => {
                let left = Self::chunk_mut(&mut root).left.take();
                Self::chunk_mut(&mut root).left =
                    Some(Self::insert_chunk_by(left, new_node, compare));
            }
            std::cmp::Ordering::Greater => {
                let right = Self::chunk_mut(&mut root).right.take();
                Self::chunk_mut(&mut root).right =
                    Some(Self::insert_chunk_by(right, new_node, compare));
            }
            std::cmp::Ordering::Equal => panic!("PCLF chunk pivots must stay unique"),
        }
        Self::rebalance_chunk(root)
    }

    fn target_chunk_by<F>(&self, mut compare_pivot: F) -> (&ProjectionRunChunk, usize)
    where
        F: FnMut(ProjectionFormulaEntryId) -> std::cmp::Ordering,
    {
        let mut cursor = self.chunk_root.as_ref();
        let mut predecessor = None;
        let mut comparisons = 0usize;
        while let Some(node) = cursor {
            comparisons += 1;
            let chunk = Self::chunk(node);
            match compare_pivot(chunk.entries[0]) {
                std::cmp::Ordering::Greater => cursor = chunk.left.as_ref(),
                std::cmp::Ordering::Less | std::cmp::Ordering::Equal => {
                    predecessor = Some(chunk);
                    cursor = chunk.right.as_ref();
                }
            }
        }
        let first = || {
            let mut node = self
                .chunk_root
                .as_ref()
                .expect("nonempty canonical run must have a chunk root");
            while let Some(left) = Self::chunk(node).left.as_ref() {
                node = left;
            }
            Self::chunk(node)
        };
        (predecessor.unwrap_or_else(first), comparisons)
    }

    fn chunk_mut_by_pivot<F>(
        &mut self,
        pivot: ProjectionFormulaEntryId,
        compare: &F,
    ) -> &mut ProjectionRunChunk
    where
        F: Fn(ProjectionFormulaEntryId, ProjectionFormulaEntryId) -> std::cmp::Ordering,
    {
        let mut cursor = self
            .chunk_root
            .as_mut()
            .expect("nonempty canonical run must have a chunk root");
        loop {
            let ordering = compare(pivot, Self::chunk(cursor).entries[0]);
            if ordering == std::cmp::Ordering::Equal {
                return Self::chunk_mut(cursor);
            }
            cursor = if ordering == std::cmp::Ordering::Less {
                Self::chunk_mut(cursor).left.as_mut()
            } else {
                Self::chunk_mut(cursor).right.as_mut()
            }
            .expect("prepared PCLF chunk pivot must remain in the AVL");
        }
    }

    #[cfg(test)]
    fn chunk_count(&self) -> usize {
        fn count(node: Option<&ProjectionRunChunkBox>) -> usize {
            node.map_or(0, |node| {
                let chunk = CanonicalProjectionRun::chunk(node);
                1 + count(chunk.left.as_ref()) + count(chunk.right.as_ref())
            })
        }
        count(self.chunk_root.as_ref())
    }

    #[cfg(test)]
    fn append_entries_in_order(&self, entries: &mut Vec<ProjectionFormulaEntryId>) {
        fn append(node: Option<&ProjectionRunChunkBox>, entries: &mut Vec<ProjectionFormulaEntryId>) {
            let Some(node) = node else {
                return;
            };
            let chunk = CanonicalProjectionRun::chunk(node);
            append(chunk.left.as_ref(), entries);
            entries.extend_from_slice(&chunk.entries);
            append(chunk.right.as_ref(), entries);
        }
        append(self.chunk_root.as_ref(), entries);
    }

    #[cfg(test)]
    fn chunks_are_nonempty_and_bounded(&self) -> bool {
        fn check(node: Option<&ProjectionRunChunkBox>) -> bool {
            node.is_none_or(|node| {
                let chunk = CanonicalProjectionRun::chunk(node);
                !chunk.entries.is_empty()
                    && chunk.entries.len() <= PROJECTION_RUN_CHUNK_CAPACITY
                    && check(chunk.left.as_ref())
                    && check(chunk.right.as_ref())
            })
        }
        check(self.chunk_root.as_ref())
    }

    #[cfg(test)]
    fn chunk_tree_is_balanced(&self) -> bool {
        fn check(node: Option<&ProjectionRunChunkBox>) -> Option<u8> {
            let Some(node) = node else {
                return Some(0);
            };
            let chunk = CanonicalProjectionRun::chunk(node);
            let left = check(chunk.left.as_ref())?;
            let right = check(chunk.right.as_ref())?;
            let height = 1 + left.max(right);
            (left.abs_diff(right) <= 1 && chunk.height == height).then_some(height)
        }
        check(self.chunk_root.as_ref()).is_some()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ProjectionIncidenceMetadata {
    Independent,
    Claimed(ClaimedProjectionSourceTemplate),
    #[cfg(test)]
    IndependentWithForcedLineage(ProjectionLineage),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClaimedProjectionSourceTemplate {
    Original { producer: ConstraintRecordId },
    DerivedUnary { result: ConstraintRecordId },
    ReplayConstraint { result: ConstraintRecordId },
    ReplayEvidence,
}

impl ClaimedProjectionSourceTemplate {
    fn from_source(source: ClaimedProjectionProofSource) -> (UpperReplayClaimId, Self) {
        match source {
            ClaimedProjectionProofSource::Original {
                coverage_root,
                producer,
            } => (coverage_root, Self::Original { producer }),
            ClaimedProjectionProofSource::DerivedUnary {
                coverage_root,
                result,
            } => (coverage_root, Self::DerivedUnary { result }),
            ClaimedProjectionProofSource::ReplayConstraint {
                coverage_root,
                result,
            } => (coverage_root, Self::ReplayConstraint { result }),
            ClaimedProjectionProofSource::ReplayEvidence { coverage_root } => {
                (coverage_root, Self::ReplayEvidence)
            }
        }
    }

    fn with_coverage_root(self, coverage_root: UpperReplayClaimId) -> ClaimedProjectionProofSource {
        match self {
            Self::Original { producer } => ClaimedProjectionProofSource::Original {
                coverage_root,
                producer,
            },
            Self::DerivedUnary { result } => ClaimedProjectionProofSource::DerivedUnary {
                coverage_root,
                result,
            },
            Self::ReplayConstraint { result } => ClaimedProjectionProofSource::ReplayConstraint {
                coverage_root,
                result,
            },
            Self::ReplayEvidence => ClaimedProjectionProofSource::ReplayEvidence { coverage_root },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct ProjectionFormulaBucket {
    entries: Vec<ProjectionFormulaEntry>,
    entry_by_clause: FxHashMap<RecordProofClause, ProjectionFormulaEntryId>,
    support_groups: Vec<ProjectionSupportGroup>,
    support_group_by_raw:
        FxHashMap<SchemeProjectionProofSupport, ProjectionSupportGroupId>,
    exact_links: FxHashMap<
        (ProjectionSupportGroupId, ProjectionFormulaEntryId),
        ProjectionIncidenceMetadata,
    >,
    canonical_runs: Vec<CanonicalProjectionRun>,
    normalized_support_keys: FxHashSet<ProjectionSupportMatchKey>,
    attributed_roots: FxHashSet<UpperReplayClaimId>,
    flat_retained_attributed_roots: FxHashSet<UpperReplayClaimId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct ProjectionFormulaMovementCensus {
    run_delta_count: u64,
    run_delta_entries: u64,
    run_delta_max_entries: usize,
    run_delta_size_histogram: [u64; 16],
    merge_calls: u64,
    merge_comparisons: u64,
    merge_scanned_entries: u64,
    merge_moved_entries: u64,
    merge_max_scanned_entries: usize,
    merge_scan_histogram: [u64; 16],
    chunk_lookup_comparisons: u64,
    chunk_splits: u64,
    new_run_insertions: u64,
    descriptor_comparisons: u64,
    descriptor_moved: u64,
    descriptor_max_moved: usize,
    descriptor_move_histogram: [u64; 16],
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct ProjectionFormulaStore {
    by_record: FxHashMap<BoundRecordId, ProjectionFormulaBucket>,
    movement: ProjectionFormulaMovementCensus,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct ProjectionClauseMembershipCensus {
    membership_queries: usize,
    record_bucket_hash_lookups: usize,
    support_hash_lookups: usize,
    clause_hash_lookups: usize,
    incidence_hash_lookups: usize,
}

#[cfg(test)]
thread_local! {
    static PROJECTION_CLAUSE_MEMBERSHIP_CENSUS: Cell<ProjectionClauseMembershipCensus> =
        const { Cell::new(ProjectionClauseMembershipCensus {
            membership_queries: 0,
            record_bucket_hash_lookups: 0,
            support_hash_lookups: 0,
            clause_hash_lookups: 0,
            incidence_hash_lookups: 0,
        }) };
    static PROJECTION_SUPPORT_PREPARE_COPIED_ENTRIES: Cell<usize> = const { Cell::new(0) };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ProjectionClauseMembership {
    exact_link_registered: bool,
    clause_registered: bool,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct ProjectionFormulaReadModel {
    formulas: FxHashMap<BoundRecordId, Vec<ProjectionClause>>,
    claimed_links:
        FxHashMap<RawProjectionClauseLinkIdentity, ClaimedProjectionProofSource>,
    independent_links: FxHashSet<RawProjectionClauseLinkIdentity>,
    distinct_clauses: FxHashSet<(BoundRecordId, RecordProofClause)>,
    normalized_support_keys:
        FxHashMap<BoundRecordId, FxHashSet<ProjectionSupportMatchKey>>,
    attributed_roots: FxHashSet<(BoundRecordId, UpperReplayClaimId)>,
    flat_retained_attributed_roots: FxHashSet<(BoundRecordId, UpperReplayClaimId)>,
}

/// Test-only read model for the exact bridge already present in CPK storage before GWCB changes
/// any production payload. Arena ids are observations, never lookup constants in the fixture.
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Gwcb0ClaimedReplayBridge {
    pub(super) bound: BoundRecordId,
    pub(super) coverage_root: UpperReplayClaimId,
    pub(super) representative_claim: UpperReplayClaimId,
    pub(super) result: ConstraintRecordId,
    pub(super) carrier: BinaryReplayDerivation,
    pub(super) lower: BoundRecordId,
    pub(super) upper: BoundRecordId,
    pub(super) producer: ConstraintRecordId,
}

impl ProjectionClause {
    pub(super) fn support(self) -> SchemeProjectionProofSupport {
        match self {
            Self::Standalone { support, .. }
            | Self::DerivedUnary { support, .. }
            | Self::ReplayConjunction { support, .. } => support,
        }
    }

    fn record_clause(self) -> RecordProofClause {
        match self {
            Self::Standalone { support, .. } => RecordProofClause::Standalone { support },
            Self::DerivedUnary {
                carrier, premise, ..
            } => RecordProofClause::DerivedUnary { carrier, premise },
            Self::ReplayConjunction {
                carrier,
                lower,
                upper,
                ..
            } => RecordProofClause::ReplayConjunction {
                carrier,
                lower_premise: lower,
                upper_premise: upper,
            },
        }
    }

    fn category_rank(self) -> u8 {
        match self {
            Self::Standalone { .. } => 0,
            Self::DerivedUnary { .. } => 1,
            Self::ReplayConjunction { .. } => 2,
        }
    }

    fn canonical_cmp(self, other: Self) -> std::cmp::Ordering {
        self.category_rank()
            .cmp(&other.category_rank())
            .then_with(|| match (self, other) {
                (
                    Self::Standalone {
                        support: left,
                        attribution: left_attribution,
                    },
                    Self::Standalone {
                        support: right,
                        attribution: right_attribution,
                    },
                ) => projection_support_cmp(left, right).then_with(|| {
                    projection_lineage_rank(left_attribution)
                        .cmp(&projection_lineage_rank(right_attribution))
                }),
                (
                    Self::DerivedUnary {
                        support: left_support,
                        carrier: left_carrier,
                        premise: left_premise,
                        attribution: left_attribution,
                    },
                    Self::DerivedUnary {
                        support: right_support,
                        carrier: right_carrier,
                        premise: right_premise,
                        attribution: right_attribution,
                    },
                ) => projection_support_cmp(left_support, right_support)
                    .then_with(|| derived_unary_carrier_cmp(left_carrier, right_carrier))
                    .then_with(|| proof_premise_cmp(left_premise, right_premise))
                    .then_with(|| {
                        projection_lineage_rank(left_attribution)
                            .cmp(&projection_lineage_rank(right_attribution))
                    }),
                (
                    Self::ReplayConjunction {
                        support: left_support,
                        carrier: left_carrier,
                        lower: left_lower,
                        upper: left_upper,
                        attribution: left_attribution,
                    },
                    Self::ReplayConjunction {
                        support: right_support,
                        carrier: right_carrier,
                        lower: right_lower,
                        upper: right_upper,
                        attribution: right_attribution,
                    },
                ) => projection_support_cmp(left_support, right_support)
                    .then_with(|| {
                        canonical_projection_key::carrier_cmp(
                            &ProjectionProofCarrier::ReplayEvidence(left_carrier),
                            &ProjectionProofCarrier::ReplayEvidence(right_carrier),
                        )
                    })
                    .then_with(|| left_lower.0.cmp(&right_lower.0))
                    .then_with(|| left_upper.0.cmp(&right_upper.0))
                    .then_with(|| {
                        projection_lineage_rank(left_attribution)
                            .cmp(&projection_lineage_rank(right_attribution))
                    }),
                _ => std::cmp::Ordering::Equal,
            })
    }
}

fn canonical_projection_incidence_cmp(
    left_clause: ProjectionClause,
    left_entry: ProjectionFormulaEntryId,
    right_clause: ProjectionClause,
    right_entry: ProjectionFormulaEntryId,
) -> std::cmp::Ordering {
    // Distinct Standalone bodies can reconstruct to byte-identical clauses under one outer
    // support. Their stable entry IDs close the physical order for AVL pivots without changing
    // the observable clause sequence; decisive source lookup separately follows legacy's raw
    // embedded-outer identity rule.
    left_clause
        .canonical_cmp(right_clause)
        .then_with(|| left_entry.0.cmp(&right_entry.0))
}

fn projection_support_cmp(
    left: SchemeProjectionProofSupport,
    right: SchemeProjectionProofSupport,
) -> std::cmp::Ordering {
    let key = |support| match support {
        SchemeProjectionProofSupport::Claimed(root) => {
            canonical_projection_key::Key::Claimed(root)
        }
        SchemeProjectionProofSupport::Independent(carrier) => {
            canonical_projection_key::Key::Independent(carrier)
        }
    };
    canonical_projection_key::cmp(&key(left), &key(right))
}

fn derived_unary_carrier_cmp(
    left: DerivedUnaryCarrier,
    right: DerivedUnaryCarrier,
) -> std::cmp::Ordering {
    match (left, right) {
        (DerivedUnaryCarrier::Structural(left), DerivedUnaryCarrier::Structural(right)) => {
            canonical_projection_key::carrier_cmp(
                &ProjectionProofCarrier::StructuralConstraint {
                    result: ConstraintRecordId(0),
                    derivation: left,
                },
                &ProjectionProofCarrier::StructuralConstraint {
                    result: ConstraintRecordId(0),
                    derivation: right,
                },
            )
        }
        (DerivedUnaryCarrier::Structural(_), DerivedUnaryCarrier::ReductionRoute(_)) => {
            std::cmp::Ordering::Less
        }
        (DerivedUnaryCarrier::ReductionRoute(_), DerivedUnaryCarrier::Structural(_)) => {
            std::cmp::Ordering::Greater
        }
        (
            DerivedUnaryCarrier::ReductionRoute(left),
            DerivedUnaryCarrier::ReductionRoute(right),
        ) => left.0.cmp(&right.0),
    }
}

fn proof_premise_cmp(left: ProofPremise, right: ProofPremise) -> std::cmp::Ordering {
    let key = |premise| match premise {
        ProofPremise::Record(record) => (0, record.0),
        ProofPremise::Constraint(constraint) => (1, constraint.0),
        ProofPremise::RootCoverage(root) => (2, root.0),
    };
    key(left).cmp(&key(right))
}

pub(super) fn record_proof_clause_cmp(
    left: RecordProofClause,
    right: RecordProofClause,
) -> std::cmp::Ordering {
    let rank = |clause| match clause {
        RecordProofClause::Standalone { .. } => 0,
        RecordProofClause::DerivedUnary { .. } => 1,
        RecordProofClause::ReplayConjunction { .. } => 2,
    };
    rank(left)
        .cmp(&rank(right))
        .then_with(|| match (left, right) {
            (
                RecordProofClause::Standalone { support: left },
                RecordProofClause::Standalone { support: right },
            ) => projection_support_cmp(left, right),
            (
                RecordProofClause::DerivedUnary {
                    carrier: left_carrier,
                    premise: left_premise,
                },
                RecordProofClause::DerivedUnary {
                    carrier: right_carrier,
                    premise: right_premise,
                },
            ) => derived_unary_carrier_cmp(left_carrier, right_carrier)
                .then_with(|| proof_premise_cmp(left_premise, right_premise)),
            (
                RecordProofClause::ReplayConjunction {
                    carrier: left_carrier,
                    lower_premise: left_lower,
                    upper_premise: left_upper,
                },
                RecordProofClause::ReplayConjunction {
                    carrier: right_carrier,
                    lower_premise: right_lower,
                    upper_premise: right_upper,
                },
            ) => canonical_projection_key::carrier_cmp(
                &ProjectionProofCarrier::ReplayEvidence(left_carrier),
                &ProjectionProofCarrier::ReplayEvidence(right_carrier),
            )
            .then_with(|| left_lower.0.cmp(&right_lower.0))
            .then_with(|| left_upper.0.cmp(&right_upper.0)),
            _ => std::cmp::Ordering::Equal,
        })
}

fn projection_lineage_rank(lineage: Option<ProjectionLineage>) -> u8 {
    match lineage {
        None => 0,
        Some(ProjectionLineage::Original) => 1,
        Some(ProjectionLineage::ReplayConstraint) => 2,
        Some(ProjectionLineage::ReplayEvidence) => 3,
        Some(ProjectionLineage::StructuralConstraint) => 4,
        Some(ProjectionLineage::ReductionRouteConstraint) => 5,
    }
}

impl ProjectionFormulaBucket {
    #[cfg(test)]
    fn push_legacy_clause(
        &mut self,
        clause: ProjectionClause,
        metadata: ProjectionIncidenceMetadata,
        match_key: Option<ProjectionSupportMatchKey>,
        coverage_root: Option<UpperReplayClaimId>,
    ) {
        let record_clause = clause.record_clause();
        let entry_id = if let Some(entry) = self.entry_by_clause.get(&record_clause).copied() {
            entry
        } else {
            let id = ProjectionFormulaEntryId(
                u32::try_from(self.entries.len()).expect("test formula entry id must fit u32"),
            );
            self.entries.push(ProjectionFormulaEntry {
                clause: record_clause,
            });
            assert!(self.entry_by_clause.insert(record_clause, id).is_none());
            id
        };
        let support = clause.support();
        let support_id = if let Some(group) = self.support_group_by_raw.get(&support).copied() {
            let existing = &self.support_groups[group.0 as usize];
            assert_eq!(existing.match_key, match_key);
            assert_eq!(existing.coverage_root, coverage_root);
            group
        } else {
            let id = ProjectionSupportGroupId(
                u32::try_from(self.support_groups.len())
                    .expect("test projection support id must fit u32"),
            );
            self.support_groups.push(ProjectionSupportGroup {
                raw_support: support,
                match_key,
                coverage_root,
            });
            assert!(self.support_group_by_raw.insert(support, id).is_none());
            id
        };
        assert!(self
            .exact_links
            .insert((support_id, entry_id), metadata)
            .is_none());
        let category = CanonicalProjectionCategory::from_clause(record_clause);
        let run_position = self.canonical_run_partition_point(category, support);
        if self.canonical_runs.get(run_position).is_some_and(|run| {
            run.category == category && run.support_id == support_id
        }) {
            let mut entries = Vec::new();
            self.canonical_runs[run_position].append_entries_in_order(&mut entries);
            entries.push(entry_id);
            entries.sort_unstable_by(|left, right| {
                canonical_projection_incidence_cmp(
                    self.reconstructed_clause(support_id, *left),
                    *left,
                    self.reconstructed_clause(support_id, *right),
                    *right,
                )
            });
            self.canonical_runs[run_position] = CanonicalProjectionRun::from_sorted_entries(
                category,
                support_id,
                entries,
            )
            .expect("test canonical run allocation");
        } else {
            self.canonical_runs.insert(
                run_position,
                CanonicalProjectionRun::from_sorted_entries(category, support_id, vec![entry_id])
                    .expect("test canonical run allocation"),
            );
        }
    }

    fn reconstructed_clause(
        &self,
        support_id: ProjectionSupportGroupId,
        entry_id: ProjectionFormulaEntryId,
    ) -> ProjectionClause {
        reconstructed_projection_clause(
            &self.entries,
            &self.support_groups,
            &self.exact_links,
            support_id,
            entry_id,
        )
    }

    fn evaluation_item(
        &self,
        support_id: ProjectionSupportGroupId,
        entry_id: ProjectionFormulaEntryId,
    ) -> ProjectionEvaluationItem {
        ProjectionEvaluationItem {
            support_id,
            entry_id,
            raw_support: self.support_groups[support_id.0 as usize].raw_support,
            clause: self.entries[entry_id.0 as usize].clause,
        }
    }

    fn legacy_decisive_entry_id(
        &self,
        support_id: ProjectionSupportGroupId,
        selected_entry_id: ProjectionFormulaEntryId,
    ) -> Option<ProjectionFormulaEntryId> {
        let selected = self.entries.get(selected_entry_id.0 as usize)?;
        if !matches!(selected.clause, RecordProofClause::Standalone { .. }) {
            return Some(selected_entry_id);
        }
        let raw_support = self.support_groups.get(support_id.0 as usize)?.raw_support;
        let legacy_entry_id = self
            .entry_by_clause
            .get(&RecordProofClause::Standalone {
                support: raw_support,
            })
            .copied()?;
        self.exact_links
            .contains_key(&(support_id, legacy_entry_id))
            .then_some(legacy_entry_id)
    }

    fn canonical_run_partition_point(
        &self,
        category: CanonicalProjectionCategory,
        support: SchemeProjectionProofSupport,
    ) -> usize {
        self.canonical_runs.partition_point(|run| {
            run.category < category
                || (run.category == category
                    && projection_support_cmp(
                        self.support_groups[run.support_id.0 as usize].raw_support,
                        support,
                    ) == std::cmp::Ordering::Less)
        })
    }

    fn canonical_run_cursor(&self) -> ProjectionCanonicalRunCursor<'_> {
        ProjectionCanonicalRunCursor {
            bucket: self,
            run_index: 0,
            chunk_stack: [None; 64],
            chunk_stack_len: 0,
            active_chunk: None,
            active_support_id: ProjectionSupportGroupId(u32::MAX),
            entry_index: 0,
        }
    }

    fn canonical_clauses(&self) -> Vec<ProjectionClause> {
        let mut clauses = Vec::with_capacity(self.exact_links.len());
        clauses.extend(self.canonical_clause_cursor());
        clauses
    }

    fn canonical_clause_cursor(&self) -> ProjectionFormulaRecordCursor<'_> {
        ProjectionFormulaRecordCursor {
            cursor: Some(self.canonical_run_cursor()),
            empty: self.exact_links.is_empty(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ProjectionEvaluationItem {
    support_id: ProjectionSupportGroupId,
    entry_id: ProjectionFormulaEntryId,
    raw_support: SchemeProjectionProofSupport,
    clause: RecordProofClause,
}

fn reconstructed_projection_clause(
    entries: &[ProjectionFormulaEntry],
    support_groups: &[ProjectionSupportGroup],
    exact_links: &FxHashMap<
        (ProjectionSupportGroupId, ProjectionFormulaEntryId),
        ProjectionIncidenceMetadata,
    >,
    support_id: ProjectionSupportGroupId,
    entry_id: ProjectionFormulaEntryId,
) -> ProjectionClause {
        let group = &support_groups[support_id.0 as usize];
        let entry = &entries[entry_id.0 as usize];
        let metadata = exact_links[&(support_id, entry_id)];
        let attribution = match (metadata, entry.clause) {
            (ProjectionIncidenceMetadata::Independent, _) => None,
            #[cfg(test)]
            (
                ProjectionIncidenceMetadata::IndependentWithForcedLineage(lineage),
                RecordProofClause::Standalone { .. },
            ) => Some(lineage),
            (
                ProjectionIncidenceMetadata::Claimed(
                    ClaimedProjectionSourceTemplate::Original { .. },
                ),
                RecordProofClause::Standalone { .. },
            ) => Some(ProjectionLineage::Original),
            (
                ProjectionIncidenceMetadata::Claimed(
                    ClaimedProjectionSourceTemplate::DerivedUnary { .. },
                ),
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::Structural(_),
                    ..
                },
            ) => Some(ProjectionLineage::StructuralConstraint),
            (
                ProjectionIncidenceMetadata::Claimed(
                    ClaimedProjectionSourceTemplate::DerivedUnary { .. },
                ),
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::ReductionRoute(_),
                    ..
                },
            ) => Some(ProjectionLineage::ReductionRouteConstraint),
            (
                ProjectionIncidenceMetadata::Claimed(
                    ClaimedProjectionSourceTemplate::ReplayConstraint { .. },
                ),
                RecordProofClause::ReplayConjunction { .. },
            ) => Some(ProjectionLineage::ReplayConstraint),
            (
                ProjectionIncidenceMetadata::Claimed(
                    ClaimedProjectionSourceTemplate::ReplayEvidence,
                ),
                RecordProofClause::ReplayConjunction { .. },
            ) => Some(ProjectionLineage::ReplayEvidence),
            _ => panic!("PCLF incidence metadata must match its exact clause kind"),
        };
        match entry.clause {
            RecordProofClause::Standalone { .. } => ProjectionClause::Standalone {
                support: group.raw_support,
                attribution,
            },
            RecordProofClause::DerivedUnary { carrier, premise } => {
                ProjectionClause::DerivedUnary {
                    support: group.raw_support,
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
                support: group.raw_support,
                carrier,
                lower: lower_premise,
                upper: upper_premise,
                attribution,
            },
        }
}

struct ProjectionCanonicalRunCursor<'a> {
    bucket: &'a ProjectionFormulaBucket,
    run_index: usize,
    chunk_stack: [Option<&'a ProjectionRunChunk>; 64],
    chunk_stack_len: usize,
    active_chunk: Option<&'a ProjectionRunChunk>,
    active_support_id: ProjectionSupportGroupId,
    entry_index: usize,
}

pub(super) struct ProjectionFormulaRecordCursor<'a> {
    cursor: Option<ProjectionCanonicalRunCursor<'a>>,
    empty: bool,
}

impl ProjectionFormulaRecordCursor<'_> {
    pub(super) fn is_empty(&self) -> bool {
        self.empty
    }
}

impl Iterator for ProjectionFormulaRecordCursor<'_> {
    type Item = ProjectionClause;

    fn next(&mut self) -> Option<Self::Item> {
        let cursor = self.cursor.as_mut()?;
        let (support_id, entry_id) = cursor.next()?;
        Some(cursor.bucket.reconstructed_clause(support_id, entry_id))
    }
}

impl Iterator for ProjectionCanonicalRunCursor<'_> {
    type Item = (ProjectionSupportGroupId, ProjectionFormulaEntryId);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(chunk) = self.active_chunk
                && let Some(&entry_id) = chunk.entries.get(self.entry_index)
            {
                self.entry_index += 1;
                return Some((self.active_support_id, entry_id));
            }

            if self.chunk_stack_len > 0 {
                self.chunk_stack_len -= 1;
                let chunk = self.chunk_stack[self.chunk_stack_len]
                    .take()
                    .expect("PCLF cursor stack slot below its length must be occupied");
                let mut right = chunk.right.as_ref();
                while let Some(node) = right {
                    let node = CanonicalProjectionRun::chunk(node);
                    assert!(
                        self.chunk_stack_len < self.chunk_stack.len(),
                        "PCLF AVL depth must fit the fixed canonical cursor stack"
                    );
                    self.chunk_stack[self.chunk_stack_len] = Some(node);
                    self.chunk_stack_len += 1;
                    right = node.left.as_ref();
                }
                self.active_chunk = Some(chunk);
                self.entry_index = 0;
                continue;
            }

            let run = self.bucket.canonical_runs.get(self.run_index)?;
            self.run_index += 1;
            self.active_support_id = run.support_id;
            let mut node = run.chunk_root.as_ref();
            while let Some(chunk) = node {
                let chunk = CanonicalProjectionRun::chunk(chunk);
                assert!(
                    self.chunk_stack_len < self.chunk_stack.len(),
                    "PCLF AVL depth must fit the fixed canonical cursor stack"
                );
                self.chunk_stack[self.chunk_stack_len] = Some(chunk);
                self.chunk_stack_len += 1;
                node = chunk.left.as_ref();
            }
            self.active_chunk = None;
            self.entry_index = 0;
        }
    }
}

fn try_prepare_projection_chunk_outputs(
    bucket: &ProjectionFormulaBucket,
    support_id: ProjectionSupportGroupId,
    existing: &[ProjectionFormulaEntryId],
    delta: &[(ProjectionFormulaEntryId, ProjectionClause)],
) -> Result<
    (Vec<Vec<ProjectionFormulaEntryId>>, usize, usize),
    std::collections::TryReserveError,
> {
    let total_len = existing.len() + delta.len();
    let mut merged = Vec::new();
    merged.try_reserve_exact(total_len)?;
    merged.resize(total_len, ProjectionFormulaEntryId(0));
    let mut comparisons = 0usize;
    let mut scanned_existing = 0usize;
    let mut disjoint = false;
    let mut last_existing_vs_first_delta = None;
    let mut first_existing_vs_last_delta = None;
    if !existing.is_empty() && !delta.is_empty() {
        comparisons += 1;
        scanned_existing += 1;
        let existing_entry = existing[existing.len() - 1];
        let ordering = canonical_projection_incidence_cmp(
            bucket.reconstructed_clause(support_id, existing_entry),
            existing_entry,
            delta[0].1,
            delta[0].0,
        );
        last_existing_vs_first_delta = Some(ordering);
        if ordering != std::cmp::Ordering::Greater {
            merged[..existing.len()].copy_from_slice(existing);
            for (output, item) in merged[existing.len()..].iter_mut().zip(delta) {
                *output = item.0;
            }
            disjoint = true;
        } else {
            comparisons += 1;
            scanned_existing += 1;
            let existing_entry = existing[0];
            let ordering = canonical_projection_incidence_cmp(
                bucket.reconstructed_clause(support_id, existing_entry),
                existing_entry,
                delta[delta.len() - 1].1,
                delta[delta.len() - 1].0,
            );
            first_existing_vs_last_delta = Some(ordering);
            if ordering == std::cmp::Ordering::Greater {
                for (output, item) in merged[..delta.len()].iter_mut().zip(delta) {
                    *output = item.0;
                }
                merged[delta.len()..].copy_from_slice(existing);
                disjoint = true;
            }
        }
    }
    let mut existing_cursor = existing.len();
    let mut delta_cursor = delta.len();
    let mut output_cursor = total_len;
    while !disjoint && existing_cursor > 0 && delta_cursor > 0 {
        let ordering = if existing_cursor == existing.len() && delta_cursor == 1 {
            last_existing_vs_first_delta
                .expect("overlap merge must retain its last/first endpoint comparison")
        } else if existing_cursor == 1 && delta_cursor == delta.len() {
            first_existing_vs_last_delta
                .expect("overlap merge must retain its first/last endpoint comparison")
        } else {
            comparisons += 1;
            scanned_existing += 1;
            let existing_entry = existing[existing_cursor - 1];
            canonical_projection_incidence_cmp(
                bucket.reconstructed_clause(support_id, existing_entry),
                existing_entry,
                delta[delta_cursor - 1].1,
                delta[delta_cursor - 1].0,
            )
        };
        output_cursor -= 1;
        if ordering == std::cmp::Ordering::Greater {
            existing_cursor -= 1;
            merged[output_cursor] = existing[existing_cursor];
        } else {
            delta_cursor -= 1;
            merged[output_cursor] = delta[delta_cursor].0;
        }
    }
    while !disjoint && delta_cursor > 0 {
        delta_cursor -= 1;
        output_cursor -= 1;
        merged[output_cursor] = delta[delta_cursor].0;
    }
    while !disjoint && existing_cursor > 0 {
        existing_cursor -= 1;
        output_cursor -= 1;
        merged[output_cursor] = existing[existing_cursor];
    }
    debug_assert!(disjoint || output_cursor == 0);

    let chunk_count = total_len.div_ceil(PROJECTION_RUN_CHUNK_CAPACITY);
    let base_len = total_len / chunk_count;
    let longer_chunks = total_len % chunk_count;
    let mut outputs = Vec::new();
    outputs.try_reserve(chunk_count)?;
    let mut cursor = 0usize;
    for chunk_index in 0..chunk_count {
        let chunk_len = base_len + usize::from(chunk_index < longer_chunks);
        let mut entries = Vec::new();
        entries.try_reserve_exact(chunk_len)?;
        entries.extend_from_slice(&merged[cursor..cursor + chunk_len]);
        cursor += chunk_len;
        outputs.push(entries);
    }
    Ok((outputs, comparisons, scanned_existing))
}

#[cfg(test)]
impl ProjectionFormulaStore {
    fn from_legacy(store: &ProofOccurrenceStore) -> Self {
        let mut factored = Self::default();
        for (&record, legacy_formula) in &store.projection_formulas {
            let mut bucket = ProjectionFormulaBucket::default();
            bucket.normalized_support_keys = store
                .projection_formula_support_keys
                .get(&record)
                .cloned()
                .unwrap_or_default();
            bucket.attributed_roots.extend(
                store
                    .projection_attributions
                    .iter()
                    .filter_map(|(bound, root)| (*bound == record).then_some(*root)),
            );
            bucket.flat_retained_attributed_roots.extend(
                store
                    .flat_retained_projection_attributions
                    .iter()
                    .filter_map(|(bound, root)| (*bound == record).then_some(*root)),
            );
            for &clause in legacy_formula {
                let raw_identity = (record, clause.support(), clause.record_clause());
                let (metadata, match_key, coverage_root) = match clause.support() {
                    SchemeProjectionProofSupport::Claimed(_) => {
                        let source = store.projection_claimed_link_audit[&raw_identity];
                        let (root, template) =
                            ClaimedProjectionSourceTemplate::from_source(source);
                        (
                            ProjectionIncidenceMetadata::Claimed(template),
                            Some(ProjectionSupportMatchKey::Claimed(root)),
                            Some(root),
                        )
                    }
                    SchemeProjectionProofSupport::Independent(carrier) => {
                        assert!(store
                            .independent_projection_clause_link_keys
                            .contains(&raw_identity));
                        (
                            ProjectionIncidenceMetadata::Independent,
                            Some(ProjectionSupportMatchKey::Independent(carrier)),
                            None,
                        )
                    }
                };
                bucket.push_legacy_clause(clause, metadata, match_key, coverage_root);
            }
            assert!(factored.by_record.insert(record, bucket).is_none());
        }
        factored
    }

    fn read_model(&self) -> ProjectionFormulaReadModel {
        let mut model = ProjectionFormulaReadModel::default();
        for (&record, bucket) in &self.by_record {
            model.formulas.insert(record, bucket.canonical_clauses());
            model
                .normalized_support_keys
                .insert(record, bucket.normalized_support_keys.clone());
            model.attributed_roots.extend(
                bucket
                    .attributed_roots
                    .iter()
                    .map(|root| (record, *root)),
            );
            model.flat_retained_attributed_roots.extend(
                bucket
                    .flat_retained_attributed_roots
                    .iter()
                    .map(|root| (record, *root)),
            );
            for (&(support_id, entry_id), &metadata) in &bucket.exact_links {
                let group = &bucket.support_groups[support_id.0 as usize];
                let clause = bucket.entries[entry_id.0 as usize].clause;
                let identity = (record, group.raw_support, clause);
                model.distinct_clauses.insert((record, clause));
                match metadata {
                    ProjectionIncidenceMetadata::Independent => {
                        model.independent_links.insert(identity);
                    }
                    #[cfg(test)]
                    ProjectionIncidenceMetadata::IndependentWithForcedLineage(_) => {
                        model.independent_links.insert(identity);
                    }
                    ProjectionIncidenceMetadata::Claimed(template) => {
                        let root = group
                            .coverage_root
                            .expect("claimed PCLF support group must freeze one root");
                        assert!(model
                            .claimed_links
                            .insert(identity, template.with_coverage_root(root))
                            .is_none());
                    }
                }
            }
        }
        model
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ResolvedProjectionSupport {
    Claimed(ProjectionClaimSupport),
    Independent(ProjectionProofCarrier),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ProjectionSupportMatchKey {
    Claimed(UpperReplayClaimId),
    Independent(ProjectionProofCarrier),
}

impl ResolvedProjectionSupport {
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

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct QorfReplayRelationKey {
    result: ConstraintRecordId,
    carrier: BinaryReplayDerivation,
    side: ReplayClaimParentSide,
    coverage_root: UpperReplayClaimId,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct QorfReplayRelationValue {
    representative_claim: UpperReplayClaimId,
    lineage: ProjectionLineage,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct QorfReplayRelationSnapshot {
    qualified: FxHashMap<QorfReplayRelationKey, QorfReplayRelationValue>,
    finite_map: FxHashMap<QorfReplayRelationKey, QorfReplayRelationValue>,
    qualified_duplicate_keys: usize,
    finite_map_duplicate_keys: usize,
    side_container_mismatches: usize,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct QorfCFullStdParityReport {
    occurrences: usize,
    nonempty_sides: usize,
    side_entries: usize,
    qualified_replay_entries: usize,
    qualified_replay_keys: usize,
    replay_arms: usize,
    root_winners: usize,
    d0_projection_census: QorfD0ProjectionAllocationCensus,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct QorfD0ProjectionAllocationCensus {
    arm_result_buckets: (usize, usize),
    arm_chunks: (usize, usize),
    arm_entries: (usize, usize),
    root_result_buckets: (usize, usize),
    root_chunks: (usize, usize),
    root_entries: (usize, usize),
    non_replay_entries: (usize, usize),
    non_replay_result_buckets: (usize, usize),
    non_replay_result_ids: (usize, usize),
    capacity_inclusive_payload_bytes: usize,
}

#[cfg(test)]
impl QorfReplayRelationSnapshot {
    fn assert_exact_parity(&self) {
        assert_eq!(self.qualified_duplicate_keys, 0);
        assert_eq!(self.finite_map_duplicate_keys, 0);
        assert_eq!(self.side_container_mismatches, 0);
        assert_eq!(self.qualified, self.finite_map);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ExactQualifiedParent {
    pub(super) coverage_root: UpperReplayClaimId,
    pub(super) parent: ClaimQualifiedParent,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FirstQualifiedParentSource {
    Replay,
    NonReplay(ClaimQualifiedParent),
}

#[derive(Debug)]
pub(super) struct PreparedQualifiedParentAdmission {
    result: ConstraintRecordId,
    accepted: Vec<ExactQualifiedParent>,
    canonical: Vec<ExactQualifiedParent>,
    new_result_entries: Option<Vec<ExactQualifiedParent>>,
    new_first_sources: Vec<(
        (ConstraintRecordId, UpperReplayClaimId),
        FirstQualifiedParentSource,
    )>,
    new_non_replay_parents: Vec<ExactQualifiedParent>,
    new_non_replay_result_entries: Option<Vec<NonReplayQualifiedParentId>>,
    root_winner_updates: Vec<QorfPreparedCanonicalRootWinnerUpdate>,
    #[cfg(test)]
    pending_first_source_capacity: usize,
}

#[derive(Debug)]
pub(super) struct PreparedReplayQualifiedParentTransaction {
    qualified: PreparedQualifiedParentAdmission,
    carrier: BinaryReplayDerivation,
    occurrence_index: Option<usize>,
    new_occurrence: Option<ReplayProofOccurrence>,
    new_replay_result_indices: Option<Vec<usize>>,
    accepted_parents: Vec<ReplayProofParent>,
    lower_shadow: Option<PreparedReplayParentSideShadowDelta>,
    upper_shadow: Option<PreparedReplayParentSideShadowDelta>,
    arm_edit: Option<QorfPreparedReplayQualifiedArmEdit>,
    new_first_witnesses: Vec<((ConstraintRecordId, UpperReplayClaimId), ReplayFirstWitness)>,
    proof_occurrence: Option<ProofOccurrence>,
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

impl PreparedQualifiedParentAdmission {
    pub(super) fn result(&self) -> ConstraintRecordId {
        self.result
    }

    pub(super) fn accepted(&self) -> &[ExactQualifiedParent] {
        &self.accepted
    }
}

impl PreparedReplayQualifiedParentTransaction {
    pub(super) fn result(&self) -> ConstraintRecordId {
        self.qualified.result()
    }

    pub(super) fn accepted(&self) -> &[ExactQualifiedParent] {
        self.qualified.accepted()
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
    dependency_occurrence_indices_by_result: FxHashMap<ConstraintRecordId, Vec<usize>>,
    projection_carrier_occurrence_index: FxHashMap<ProjectionProofCarrier, usize>,
    row_derivation_occurrence_index: FxHashMap<RowDerivationId, usize>,
    pub(crate) replay_finite_map: Vec<ReplayProofOccurrence>,
    replay_finite_map_index: FxHashMap<(ConstraintRecordId, BinaryReplayDerivation), usize>,
    replay_indices_by_result: FxHashMap<ConstraintRecordId, Vec<usize>>,
    replay_parent_chunks: ReplayParentChunkArena,
    // QORF-D0 shadow projections. Production readers remain on the QORF-C/legacy authorities
    // until D1; these are maintained only for parity and rollback-safe cutover preparation.
    replay_qualified_arms: ReplayQualifiedArmIndex,
    canonical_qualified_parent_by_root: CanonicalQualifiedParentRootIndex,
    non_replay_qualified_parents: NonReplayQualifiedParentStore,
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
    // The sole historical-order fact retained by CPK: cross-kind first source per result/root.
    // Canonical qualified-parent storage stays arrival-order independent.
    first_qualified_parent_source_by_root:
        FxHashMap<(ConstraintRecordId, UpperReplayClaimId), FirstQualifiedParentSource>,
    projection_lower_record_by_constraint: FxHashMap<ConstraintRecordId, BoundRecordId>,
    projection_lower_record_by_replay: FxHashMap<BinaryReplayDerivation, BoundRecordId>,
    dependent_records_by_premise: FxHashMap<ProofPremise, FxHashSet<BoundRecordId>>,
    pub(crate) live_coverage: FxHashSet<(UpperReplayClaimId, UnweightedRowReductionRecordId)>,
    live_states_by_coverage_root:
        FxHashMap<UpperReplayClaimId, FxHashSet<UnweightedRowReductionRecordId>>,
    pub(crate) replay_coverage_connected: bool,
    projection_supports: FxHashMap<BoundRecordId, Vec<SchemeProjectionProofSupport>>,
    claimed_parents_by_lower_record: FxHashMap<BoundRecordId, Vec<UpperReplayClaimId>>,
    projection_lower_records_by_root: FxHashMap<UpperReplayClaimId, Vec<BoundRecordId>>,
    projection_lower_record_memberships: FxHashSet<(UpperReplayClaimId, BoundRecordId)>,
    // PCLF-E makes this the sole production projection-clause/link representation.
    projection_formula_shadow: ProjectionFormulaStore,
    // Expanded faces remain only in test builds as the independent PCLF parity oracle. Release
    // admission neither allocates nor writes any of these containers.
    #[cfg(test)]
    projection_formulas: FxHashMap<BoundRecordId, Vec<ProjectionClause>>,
    #[cfg(test)]
    projection_formula_support_keys:
        FxHashMap<BoundRecordId, FxHashSet<ProjectionSupportMatchKey>>,
    #[cfg(test)]
    projection_clause_keys: FxHashSet<(BoundRecordId, RecordProofClause)>,
    #[cfg(test)]
    independent_projection_clause_link_keys: FxHashSet<RawProjectionClauseLinkIdentity>,
    #[cfg(test)]
    projection_claimed_link_audit:
        FxHashMap<RawProjectionClauseLinkIdentity, ClaimedProjectionProofSource>,
    #[cfg(test)]
    projection_attributions: FxHashSet<(BoundRecordId, UpperReplayClaimId)>,
    #[cfg(test)]
    flat_retained_projection_attributions: FxHashSet<(BoundRecordId, UpperReplayClaimId)>,
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
    fail_next_projection_support_reservation: bool,
    #[cfg(test)]
    projection_clause_reservation_failure_point: Option<ProjectionClauseReservationFailurePoint>,
    #[cfg(test)]
    projection_clause_canonical_run_reservation_failure_after: Option<usize>,
    #[cfg(test)]
    qorf_replay_reservation_failure_point: Option<QorfReplayReservationFailurePoint>,
}

/// Persistent-store allocation census only.
///
/// In particular, this does not observe the temporary `Vec` and `FxHashSet`
/// allocations used while preparing an admission. Therefore equality of two
/// censuses proves zero persistent index growth, not zero heap allocation for
/// the whole admission path. The final GWCB audit ledger is a flat map, so its
/// persistent footprint is represented directly by `(len, capacity)` rather
/// than by a synthetic per-record bucket count.
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PerformanceIndexAllocationCensus {
    dependency_result_buckets: (usize, usize, usize, usize),
    projection_carrier_occurrences: (usize, usize),
    row_derivation_occurrences: (usize, usize),
    replay_result_buckets: (usize, usize, usize, usize),
    formula_support_buckets: (usize, usize, usize, usize),
    claimed_projection_audit: (usize, usize),
    legacy_projection_formula: ProjectionFormulaAllocationCensus,
    shadow_projection_formula: ProjectionFormulaAllocationCensus,
    shadow_incidence_metadata: (usize, usize, usize),
    shadow_movement: ProjectionFormulaMovementCensus,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct ProjectionFormulaAllocationCensus {
    bucket_map: (usize, usize),
    entry_arena: (usize, usize),
    distinct_clause_index: (usize, usize),
    support_group_arena: (usize, usize),
    support_group_index: (usize, usize),
    exact_incidence_index: (usize, usize),
    canonical_run_table: (usize, usize),
    canonical_run_chunks: (usize, usize),
    canonical_run_entries: (usize, usize),
    nonempty_canonical_runs: usize,
    empty_canonical_runs: usize,
    canonical_run_max_entries: usize,
    canonical_run_size_histogram: [usize; 16],
    normalized_support_summary: (usize, usize),
    attributed_summary: (usize, usize),
    flat_attributed_summary: (usize, usize),
    estimated_retained_bytes: usize,
}

impl Default for ProofOccurrenceStore {
    fn default() -> Self {
        Self {
            occurrences: Vec::new(),
            dependency_occurrence_indices_by_result: FxHashMap::default(),
            projection_carrier_occurrence_index: FxHashMap::default(),
            row_derivation_occurrence_index: FxHashMap::default(),
            replay_finite_map: Vec::new(),
            replay_finite_map_index: FxHashMap::default(),
            replay_indices_by_result: FxHashMap::default(),
            replay_parent_chunks: ReplayParentChunkArena::default(),
            replay_qualified_arms: ReplayQualifiedArmIndex::default(),
            canonical_qualified_parent_by_root: CanonicalQualifiedParentRootIndex::default(),
            non_replay_qualified_parents: NonReplayQualifiedParentStore::default(),
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
            first_qualified_parent_source_by_root: FxHashMap::default(),
            projection_lower_record_by_constraint: FxHashMap::default(),
            projection_lower_record_by_replay: FxHashMap::default(),
            dependent_records_by_premise: FxHashMap::default(),
            live_coverage: FxHashSet::default(),
            live_states_by_coverage_root: FxHashMap::default(),
            replay_coverage_connected: true,
            projection_supports: FxHashMap::default(),
            claimed_parents_by_lower_record: FxHashMap::default(),
            projection_lower_records_by_root: FxHashMap::default(),
            projection_lower_record_memberships: FxHashSet::default(),
            projection_formula_shadow: ProjectionFormulaStore::default(),
            #[cfg(test)]
            projection_formulas: FxHashMap::default(),
            #[cfg(test)]
            projection_formula_support_keys: FxHashMap::default(),
            #[cfg(test)]
            projection_clause_keys: FxHashSet::default(),
            #[cfg(test)]
            independent_projection_clause_link_keys: FxHashSet::default(),
            #[cfg(test)]
            projection_claimed_link_audit: FxHashMap::default(),
            #[cfg(test)]
            projection_attributions: FxHashSet::default(),
            #[cfg(test)]
            flat_retained_projection_attributions: FxHashSet::default(),
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
            fail_next_projection_support_reservation: false,
            #[cfg(test)]
            projection_clause_reservation_failure_point: None,
            #[cfg(test)]
            projection_clause_canonical_run_reservation_failure_after: None,
            #[cfg(test)]
            qorf_replay_reservation_failure_point: None,
        }
    }
}

impl ProofOccurrenceStore {
    #[cfg(test)]
    fn qorf_fail_after(&mut self, point: QorfReplayReservationFailurePoint) -> bool {
        if self.qorf_replay_reservation_failure_point == Some(point) {
            self.qorf_replay_reservation_failure_point = None;
            true
        } else {
            false
        }
    }

    #[cfg(test)]
    fn performance_index_allocation_census(&self) -> PerformanceIndexAllocationCensus {
        let hash_bytes = |capacity: usize, entry_size: usize| {
            capacity.saturating_mul(entry_size.saturating_add(1))
        };
        let legacy_formula = (
            self.projection_formulas
                .values()
                .map(Vec::len)
                .sum::<usize>(),
            self.projection_formulas
                .values()
                .map(Vec::capacity)
                .sum::<usize>(),
        );
        let legacy_support = (
            self.projection_formula_support_keys
                .values()
                .map(FxHashSet::len)
                .sum::<usize>(),
            self.projection_formula_support_keys
                .values()
                .map(FxHashSet::capacity)
                .sum::<usize>(),
        );
        let legacy_bytes = hash_bytes(
            self.projection_formulas.capacity(),
            std::mem::size_of::<(BoundRecordId, Vec<ProjectionClause>)>(),
        ) + legacy_formula.1 * std::mem::size_of::<ProjectionClause>()
            + hash_bytes(
                self.projection_clause_keys.capacity(),
                std::mem::size_of::<(BoundRecordId, RecordProofClause)>(),
            )
            + hash_bytes(
                self.independent_projection_clause_link_keys.capacity(),
                std::mem::size_of::<RawProjectionClauseLinkIdentity>(),
            )
            + hash_bytes(
                self.projection_claimed_link_audit.capacity(),
                std::mem::size_of::<(
                    RawProjectionClauseLinkIdentity,
                    ClaimedProjectionProofSource,
                )>(),
            )
            + hash_bytes(
                self.projection_formula_support_keys.capacity(),
                std::mem::size_of::<(BoundRecordId, FxHashSet<ProjectionSupportMatchKey>)>(),
            )
            + hash_bytes(
                legacy_support.1,
                std::mem::size_of::<ProjectionSupportMatchKey>(),
            )
            + hash_bytes(
                self.projection_attributions.capacity(),
                std::mem::size_of::<(BoundRecordId, UpperReplayClaimId)>(),
            )
            + hash_bytes(
                self.flat_retained_projection_attributions.capacity(),
                std::mem::size_of::<(BoundRecordId, UpperReplayClaimId)>(),
            );
        let shadow = &self.projection_formula_shadow;
        macro_rules! bucket_sum {
            ($field:ident, $method:ident) => {
                shadow
                    .by_record
                    .values()
                    .map(|bucket| bucket.$field.$method())
                    .sum::<usize>()
            };
        }
        let shadow_entries = (bucket_sum!(entries, len), bucket_sum!(entries, capacity));
        let shadow_entry_index = (
            bucket_sum!(entry_by_clause, len),
            bucket_sum!(entry_by_clause, capacity),
        );
        let shadow_supports = (
            bucket_sum!(support_groups, len),
            bucket_sum!(support_groups, capacity),
        );
        let shadow_support_index = (
            bucket_sum!(support_group_by_raw, len),
            bucket_sum!(support_group_by_raw, capacity),
        );
        let shadow_exact = (
            bucket_sum!(exact_links, len),
            bucket_sum!(exact_links, capacity),
        );
        let shadow_normalized = (
            bucket_sum!(normalized_support_keys, len),
            bucket_sum!(normalized_support_keys, capacity),
        );
        let shadow_attributed = (
            bucket_sum!(attributed_roots, len),
            bucket_sum!(attributed_roots, capacity),
        );
        let shadow_flat = (
            bucket_sum!(flat_retained_attributed_roots, len),
            bucket_sum!(flat_retained_attributed_roots, capacity),
        );
        let shadow_runs = (
            shadow
                .by_record
                .values()
                .map(|bucket| bucket.canonical_runs.len())
                .sum::<usize>(),
            shadow
                .by_record
                .values()
                .map(|bucket| bucket.canonical_runs.capacity())
                .sum::<usize>(),
        );
        fn chunk_allocation_census(
            node: Option<&ProjectionRunChunkBox>,
        ) -> (usize, usize, usize) {
            let Some(node) = node else {
                return (0, 0, 0);
            };
            let chunk = CanonicalProjectionRun::chunk(node);
            let left = chunk_allocation_census(chunk.left.as_ref());
            let right = chunk_allocation_census(chunk.right.as_ref());
            (
                1 + left.0 + right.0,
                chunk.entries.len() + left.1 + right.1,
                chunk.entries.capacity() + left.2 + right.2,
            )
        }
        let (chunk_count, run_entry_len, run_entry_capacity) = shadow
            .by_record
            .values()
            .flat_map(|bucket| &bucket.canonical_runs)
            .map(|run| chunk_allocation_census(run.chunk_root.as_ref()))
            .fold((0, 0, 0), |left, right| {
                (left.0 + right.0, left.1 + right.1, left.2 + right.2)
            });
        let shadow_run_chunks = (chunk_count, chunk_count);
        let shadow_run_entries = (run_entry_len, run_entry_capacity);
        let mut shadow_run_histogram = [0usize; 16];
        let mut shadow_run_max_entries = 0usize;
        let mut empty_canonical_runs = 0usize;
        for run in shadow
            .by_record
            .values()
            .flat_map(|bucket| &bucket.canonical_runs)
        {
            empty_canonical_runs += usize::from(run.entry_len == 0);
            shadow_run_max_entries = shadow_run_max_entries.max(run.entry_len);
            shadow_run_histogram
                [Self::projection_formula_movement_bucket(run.entry_len)] += 1;
        }
        let shadow_bytes = hash_bytes(
            shadow.by_record.capacity(),
            std::mem::size_of::<(BoundRecordId, ProjectionFormulaBucket)>(),
        ) + shadow_entries.1 * std::mem::size_of::<ProjectionFormulaEntry>()
            + hash_bytes(
                shadow_entry_index.1,
                std::mem::size_of::<(RecordProofClause, ProjectionFormulaEntryId)>(),
            )
            + shadow_supports.1 * std::mem::size_of::<ProjectionSupportGroup>()
            + hash_bytes(
                shadow_support_index.1,
                std::mem::size_of::<(SchemeProjectionProofSupport, ProjectionSupportGroupId)>(),
            )
            + hash_bytes(
                shadow_exact.1,
                std::mem::size_of::<(
                    (ProjectionSupportGroupId, ProjectionFormulaEntryId),
                    ProjectionIncidenceMetadata,
                )>(),
            )
            + shadow_runs.1 * std::mem::size_of::<CanonicalProjectionRun>()
            + shadow_run_chunks.1 * std::mem::size_of::<ProjectionRunChunk>()
            + shadow_run_entries.1 * std::mem::size_of::<ProjectionFormulaEntryId>()
            + hash_bytes(
                shadow_normalized.1,
                std::mem::size_of::<ProjectionSupportMatchKey>(),
            )
            + hash_bytes(
                shadow_attributed.1,
                std::mem::size_of::<UpperReplayClaimId>(),
            )
            + hash_bytes(shadow_flat.1, std::mem::size_of::<UpperReplayClaimId>());
        let metadata = shadow
            .by_record
            .values()
            .flat_map(|bucket| bucket.exact_links.values())
            .fold(
                (0usize, 0usize),
                |(independent, claimed), value| match value {
                    ProjectionIncidenceMetadata::Independent => (independent + 1, claimed),
                    #[cfg(test)]
                    ProjectionIncidenceMetadata::IndependentWithForcedLineage(_) => {
                        (independent + 1, claimed)
                    }
                    ProjectionIncidenceMetadata::Claimed(_) => (independent, claimed + 1),
                },
            );
        PerformanceIndexAllocationCensus {
            dependency_result_buckets: (
                self.dependency_occurrence_indices_by_result.len(),
                self.dependency_occurrence_indices_by_result.capacity(),
                self.dependency_occurrence_indices_by_result
                    .values()
                    .map(Vec::len)
                    .sum(),
                self.dependency_occurrence_indices_by_result
                    .values()
                    .map(Vec::capacity)
                    .sum(),
            ),
            projection_carrier_occurrences: (
                self.projection_carrier_occurrence_index.len(),
                self.projection_carrier_occurrence_index.capacity(),
            ),
            row_derivation_occurrences: (
                self.row_derivation_occurrence_index.len(),
                self.row_derivation_occurrence_index.capacity(),
            ),
            replay_result_buckets: (
                self.replay_indices_by_result.len(),
                self.replay_indices_by_result.capacity(),
                self.replay_indices_by_result
                    .values()
                    .map(Vec::len)
                    .sum(),
                self.replay_indices_by_result
                    .values()
                    .map(Vec::capacity)
                    .sum(),
            ),
            formula_support_buckets: (
                self.projection_formula_support_keys.len(),
                self.projection_formula_support_keys.capacity(),
                self.projection_formula_support_keys
                    .values()
                    .map(FxHashSet::len)
                    .sum(),
                self.projection_formula_support_keys
                    .values()
                    .map(FxHashSet::capacity)
                    .sum(),
            ),
            claimed_projection_audit: (
                self.projection_claimed_link_audit.len(),
                self.projection_claimed_link_audit.capacity(),
            ),
            legacy_projection_formula: ProjectionFormulaAllocationCensus {
                bucket_map: (
                    self.projection_formulas.len(),
                    self.projection_formulas.capacity(),
                ),
                entry_arena: legacy_formula,
                distinct_clause_index: (
                    self.projection_clause_keys.len(),
                    self.projection_clause_keys.capacity(),
                ),
                support_group_arena: (0, 0),
                support_group_index: (0, 0),
                exact_incidence_index: (
                    self.independent_projection_clause_link_keys.len()
                        + self.projection_claimed_link_audit.len(),
                    self.independent_projection_clause_link_keys.capacity()
                        + self.projection_claimed_link_audit.capacity(),
                ),
                canonical_run_table: (0, 0),
                canonical_run_chunks: (0, 0),
                canonical_run_entries: (0, 0),
                nonempty_canonical_runs: 0,
                empty_canonical_runs: 0,
                canonical_run_max_entries: 0,
                canonical_run_size_histogram: [0; 16],
                normalized_support_summary: legacy_support,
                attributed_summary: (
                    self.projection_attributions.len(),
                    self.projection_attributions.capacity(),
                ),
                flat_attributed_summary: (
                    self.flat_retained_projection_attributions.len(),
                    self.flat_retained_projection_attributions.capacity(),
                ),
                estimated_retained_bytes: legacy_bytes,
            },
            shadow_projection_formula: ProjectionFormulaAllocationCensus {
                bucket_map: (shadow.by_record.len(), shadow.by_record.capacity()),
                entry_arena: shadow_entries,
                distinct_clause_index: shadow_entry_index,
                support_group_arena: shadow_supports,
                support_group_index: shadow_support_index,
                exact_incidence_index: shadow_exact,
                canonical_run_table: shadow_runs,
                canonical_run_chunks: shadow_run_chunks,
                canonical_run_entries: shadow_run_entries,
                nonempty_canonical_runs: shadow_runs.0 - empty_canonical_runs,
                empty_canonical_runs,
                canonical_run_max_entries: shadow_run_max_entries,
                canonical_run_size_histogram: shadow_run_histogram,
                normalized_support_summary: shadow_normalized,
                attributed_summary: shadow_attributed,
                flat_attributed_summary: shadow_flat,
                estimated_retained_bytes: shadow_bytes,
            },
            shadow_incidence_metadata: (
                metadata.0,
                metadata.1,
                std::mem::size_of::<ProjectionIncidenceMetadata>(),
            ),
            shadow_movement: shadow.movement,
        }
    }

    pub(super) fn try_prepare_projection_support_mutation(
        &mut self,
        lower_record: BoundRecordId,
        claims_to_link: &[UpperReplayClaimId],
        independent_supports: &[ProjectionProofCarrier],
    ) -> Result<Option<PreparedProjectionSupportMutation>, ProofFailure> {
        if claims_to_link.is_empty()
            && !self.projection_supports.contains_key(&lower_record)
        {
            return Ok(None);
        }
        let exhausted = |_| ProofFailure::ResourceExhausted {
            operation: ProofOperation::UpdateClaimLifecycle,
        };
        let existing_supports = self.projection_supports.get(&lower_record);
        let existing_claims = self.claimed_parents_by_lower_record.get(&lower_record);
        // Replay events usually revisit metadata already attached to this record. Prove that
        // immutable no-op before cloning either canonical bucket; changed transactions still use
        // the admission-fixed snapshots below and preserve the existing atomic commit contract.
        let metadata_would_change = claims_to_link.iter().any(|claim| {
            let Some(root) = self.upper_claim(*claim).map(|claim| claim.coverage_root) else {
                return false;
            };
            let claim_changes = existing_claims.is_none_or(|claims| {
                match claims.binary_search_by_key(&root, |existing| {
                    self.upper_claim(*existing)
                        .expect("stored projection claims must be admitted")
                        .coverage_root
                }) {
                    Ok(position) => claims[position] < *claim,
                    Err(_) => true,
                }
            });
            let incoming_key = canonical_projection_key::Key::Claimed(root);
            let support_changes = existing_supports.is_none_or(|supports| {
                match supports.binary_search_by(|support| {
                    self.stored_projection_support_cmp(*support, &incoming_key)
                }) {
                    Ok(position) => matches!(supports[position],
                        SchemeProjectionProofSupport::Claimed(existing) if existing < *claim),
                    Err(_) => true,
                }
            });
            claim_changes
                || support_changes
                || !self
                    .projection_lower_record_memberships
                    .contains(&(root, lower_record))
        }) || independent_supports.iter().any(|carrier| {
            let incoming_key = canonical_projection_key::Key::Independent(*carrier);
            existing_supports.is_none_or(|supports| {
                supports
                    .binary_search_by(|support| {
                        self.stored_projection_support_cmp(*support, &incoming_key)
                    })
                    .is_err()
            })
        });
        if !metadata_would_change {
            return Ok(None);
        }

        #[cfg(test)]
        PROJECTION_SUPPORT_PREPARE_COPIED_ENTRIES.with(|cell| {
            cell.set(
                cell.get()
                    + existing_supports.map_or(0, Vec::len)
                    + existing_claims.map_or(0, Vec::len),
            );
        });
        let mut current_supports = Vec::new();
        current_supports
            .try_reserve(
                existing_supports.map_or(0, Vec::len)
                    + claims_to_link.len()
                    + independent_supports.len(),
            )
            .map_err(exhausted)?;
        current_supports.extend(existing_supports.into_iter().flatten().copied());
        let mut current_claims = Vec::new();
        current_claims
            .try_reserve(existing_claims.map_or(0, Vec::len) + claims_to_link.len())
            .map_err(exhausted)?;
        current_claims.extend(existing_claims.into_iter().flatten().copied());
        let mut new_root_memberships = Vec::new();
        new_root_memberships
            .try_reserve(claims_to_link.len())
            .map_err(exhausted)?;
        let mut metadata_changed = false;
        for claim in claims_to_link {
            let Some(root) = self.upper_claim(*claim).map(|claim| claim.coverage_root) else {
                continue;
            };
            match current_claims.binary_search_by_key(&root, |existing| {
                self.upper_claim(*existing)
                    .expect("stored projection claims must be admitted")
                    .coverage_root
            }) {
                Ok(position) if current_claims[position] < *claim => {
                    current_claims[position] = *claim;
                    metadata_changed = true;
                }
                Ok(_) => {}
                Err(position) => {
                    #[cfg(test)]
                    record_canonical_projection_insertion_moves(current_claims.len() - position);
                    current_claims.insert(position, *claim);
                    metadata_changed = true;
                }
            }
            let incoming_key = canonical_projection_key::Key::Claimed(root);
            match current_supports.binary_search_by(|support| {
                self.stored_projection_support_cmp(*support, &incoming_key)
            }) {
                Ok(position)
                    if matches!(current_supports[position],
                        SchemeProjectionProofSupport::Claimed(existing) if existing < *claim) =>
                {
                    current_supports[position] = SchemeProjectionProofSupport::Claimed(*claim);
                    metadata_changed = true;
                }
                Ok(_) => {}
                Err(position) => {
                    #[cfg(test)]
                    record_canonical_projection_insertion_moves(current_supports.len() - position);
                    current_supports.insert(
                        position,
                        SchemeProjectionProofSupport::Claimed(*claim),
                    );
                    metadata_changed = true;
                }
            }
            if !self
                .projection_lower_record_memberships
                .contains(&(root, lower_record))
                && !new_root_memberships.contains(&root)
            {
                new_root_memberships.push(root);
                metadata_changed = true;
            }
        }
        for carrier in independent_supports {
            let incoming = SchemeProjectionProofSupport::Independent(*carrier);
            let incoming_key = canonical_projection_key::Key::Independent(*carrier);
            if let Err(position) = current_supports.binary_search_by(|support| {
                self.stored_projection_support_cmp(*support, &incoming_key)
            }) {
                #[cfg(test)]
                record_canonical_projection_insertion_moves(current_supports.len() - position);
                current_supports.insert(position, incoming);
                metadata_changed = true;
            }
        }
        if !metadata_changed {
            return Ok(None);
        }
        #[cfg(test)]
        if std::mem::take(&mut self.fail_next_projection_support_reservation) {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }
        self.projection_supports.try_reserve(1).map_err(exhausted)?;
        self.claimed_parents_by_lower_record
            .try_reserve(1)
            .map_err(exhausted)?;
        self.projection_lower_record_memberships
            .try_reserve(new_root_memberships.len())
            .map_err(exhausted)?;
        self.projection_lower_records_by_root
            .try_reserve(new_root_memberships.len())
            .map_err(exhausted)?;
        let mut new_root_record_entries = Vec::new();
        new_root_record_entries
            .try_reserve(new_root_memberships.len())
            .map_err(exhausted)?;
        for root in &new_root_memberships {
            if let Some(records) = self.projection_lower_records_by_root.get_mut(root) {
                records.try_reserve(1).map_err(exhausted)?;
            } else {
                let mut records = Vec::new();
                records.try_reserve(1).map_err(exhausted)?;
                new_root_record_entries.push((*root, records));
            }
        }
        Ok(Some(PreparedProjectionSupportMutation {
            lower_record,
            current_supports,
            current_claims,
            new_root_memberships,
            new_root_record_entries,
        }))
    }

    pub(super) fn commit_projection_support_mutation(
        &mut self,
        mutation: &mut PreparedProjectionSupportMutation,
    ) {
        for (root, records) in mutation.new_root_record_entries.drain(..) {
            assert!(self
                .projection_lower_records_by_root
                .insert(root, records)
                .is_none());
        }
        for root in &mutation.new_root_memberships {
            assert!(self
                .projection_lower_record_memberships
                .insert((*root, mutation.lower_record)));
            self.projection_lower_records_by_root
                .get_mut(root)
                .expect("projection root entry was preflighted")
                .push(mutation.lower_record);
        }
        if mutation.current_claims.is_empty() {
            self.claimed_parents_by_lower_record
                .remove(&mutation.lower_record);
        } else {
            self.claimed_parents_by_lower_record.insert(
                mutation.lower_record,
                std::mem::take(&mut mutation.current_claims),
            );
        }
        self.projection_supports.insert(
            mutation.lower_record,
            std::mem::take(&mut mutation.current_supports),
        );
    }

    pub(super) fn claim_coverage_root(
        &self,
        claim: UpperReplayClaimId,
    ) -> Option<UpperReplayClaimId> {
        self.upper_claim_index
            .get(&claim)
            .map(|index| self.upper_claims[*index].coverage_root)
    }

    fn stored_projection_support_cmp(
        &self,
        support: SchemeProjectionProofSupport,
        incoming: &canonical_projection_key::Key,
    ) -> std::cmp::Ordering {
        let key = match support {
            SchemeProjectionProofSupport::Claimed(existing) => {
                canonical_projection_key::Key::Claimed(
                    self.upper_claim(existing)
                        .expect("stored projection supports must be admitted")
                        .coverage_root,
                )
            }
            SchemeProjectionProofSupport::Independent(carrier) => {
                canonical_projection_key::Key::Independent(carrier)
            }
        };
        canonical_projection_key::cmp(&key, incoming)
    }

    fn projection_support_match_key(
        &self,
        support: SchemeProjectionProofSupport,
    ) -> Option<ProjectionSupportMatchKey> {
        match support {
            SchemeProjectionProofSupport::Claimed(claim) => self
                .claim_coverage_root(claim)
                .map(ProjectionSupportMatchKey::Claimed),
            SchemeProjectionProofSupport::Independent(carrier) => {
                Some(ProjectionSupportMatchKey::Independent(carrier))
            }
        }
    }

    fn claimed_projection_support_match_key(
        &self,
        support: SchemeProjectionProofSupport,
        representative_claim: UpperReplayClaimId,
        coverage_root: UpperReplayClaimId,
    ) -> Result<ProjectionSupportMatchKey, ProofFailure> {
        match support {
            SchemeProjectionProofSupport::Claimed(claim) if claim == representative_claim => {
                Ok(ProjectionSupportMatchKey::Claimed(coverage_root))
            }
            SchemeProjectionProofSupport::Claimed(claim) => self
                .claim_coverage_root(claim)
                .map(ProjectionSupportMatchKey::Claimed)
                .ok_or(ProofFailure::MissingProofFact {
                    fact: ProofFactRef::UpperClaim(claim),
                }),
            SchemeProjectionProofSupport::Independent(carrier) => {
                Ok(ProjectionSupportMatchKey::Independent(carrier))
            }
        }
    }

    fn claimed_projection_proof(
        &self,
        bound: BoundRecordId,
        admission: RecordProofClauseLinkAdmission,
    ) -> Result<Option<(ClaimedProjectionProofKey, ClaimedProjectionProof)>, ProofFailure> {
        let SchemeProjectionProofSupport::Claimed(representative_claim) = admission.support else {
            return Ok(None);
        };
        let source = admission
            .claimed_proof_source
            .expect("claimed clause admission must carry event-local certificate metadata");
        let source_coverage_root = match source {
            ClaimedProjectionProofSource::Original { coverage_root, .. }
            | ClaimedProjectionProofSource::DerivedUnary { coverage_root, .. }
            | ClaimedProjectionProofSource::ReplayConstraint { coverage_root, .. }
            | ClaimedProjectionProofSource::ReplayEvidence { coverage_root } => coverage_root,
        };
        if let Some(actual_root) = self.claim_coverage_root(representative_claim) {
            assert_eq!(
                source_coverage_root, actual_root,
                "writer-time certificate root must match the admitted representative claim",
            );
        }
        let (key, proof) = match (admission.clause, source) {
            (
                RecordProofClause::Standalone { support },
                ClaimedProjectionProofSource::Original {
                    coverage_root,
                    producer,
                },
            ) => {
                let attribution = ClaimedProjectionProofAttribution::Original;
                let embedded_support = self.claimed_projection_support_match_key(
                    support,
                    representative_claim,
                    coverage_root,
                )?;
                (
                    ClaimedProjectionProofKey::Standalone {
                        bound,
                        coverage_root,
                        embedded_support,
                        producer,
                        attribution,
                    },
                    ClaimedProjectionProof::new(ClaimedProjectionProofKind::Standalone {
                        bound,
                        coverage_root,
                        representative_claim,
                        producer,
                        attribution,
                    }),
                )
            }
            (
                RecordProofClause::DerivedUnary { carrier, premise },
                ClaimedProjectionProofSource::DerivedUnary {
                    coverage_root,
                    result,
                },
            ) => {
                let attribution = match carrier {
                    DerivedUnaryCarrier::Structural(_) => {
                        ClaimedProjectionProofAttribution::StructuralConstraint
                    }
                    DerivedUnaryCarrier::ReductionRoute(_) => {
                        ClaimedProjectionProofAttribution::ReductionRouteConstraint
                    }
                };
                (
                    ClaimedProjectionProofKey::DerivedUnary {
                        bound,
                        coverage_root,
                        result,
                        carrier,
                        premise,
                        attribution,
                    },
                    ClaimedProjectionProof::new(ClaimedProjectionProofKind::DerivedUnary {
                        bound,
                        coverage_root,
                        representative_claim,
                        result,
                        carrier,
                        premise,
                        attribution,
                    }),
                )
            }
            (
                RecordProofClause::ReplayConjunction {
                    carrier,
                    lower_premise,
                    upper_premise,
                },
                source @ (ClaimedProjectionProofSource::ReplayConstraint { .. }
                | ClaimedProjectionProofSource::ReplayEvidence { .. }),
            ) => {
                assert_eq!(carrier.lower, lower_premise);
                assert_eq!(carrier.upper, upper_premise);
                let (coverage_root, attribution) = match source {
                    ClaimedProjectionProofSource::ReplayConstraint {
                        coverage_root,
                        result,
                    } => (
                        coverage_root,
                        ClaimedProjectionProofAttribution::ReplayConstraint { result },
                    ),
                    ClaimedProjectionProofSource::ReplayEvidence { coverage_root } => {
                        (coverage_root, ClaimedProjectionProofAttribution::ReplayEvidence)
                    }
                    _ => unreachable!(),
                };
                (
                    ClaimedProjectionProofKey::ReplayConjunction {
                        bound,
                        coverage_root,
                        carrier,
                        lower_premise,
                        upper_premise,
                        attribution,
                    },
                    ClaimedProjectionProof::new(ClaimedProjectionProofKind::ReplayConjunction {
                        bound,
                        coverage_root,
                        representative_claim,
                        carrier,
                        lower_premise,
                        upper_premise,
                        attribution,
                    }),
                )
            }
            _ => unreachable!("claimed clause constructor rejects mismatched certificate metadata"),
        };
        Ok(Some((key, proof)))
    }

    #[cfg(test)]
    fn decisive_claimed_projection_proof(
        &self,
        bound: BoundRecordId,
        clause: ProjectionClause,
    ) -> Result<Option<ClaimedProjectionProof>, ProofFailure> {
        let SchemeProjectionProofSupport::Claimed(_) = clause.support() else {
            return Ok(None);
        };
        let raw_identity = (bound, clause.support(), clause.record_clause());
        let Some(source) = self.projection_claimed_link_audit.get(&raw_identity).copied() else {
            debug_assert!(
                false,
                "decisive claimed projection clause must retain its raw audit link: {raw_identity:?}"
            );
            return Ok(None);
        };
        let claimed_attribution_source = match source {
            ClaimedProjectionProofSource::ReplayConstraint { .. } => {
                ClaimedAttributionSource::CanonicalReplay
            }
            ClaimedProjectionProofSource::Original { .. }
            | ClaimedProjectionProofSource::DerivedUnary { .. }
            | ClaimedProjectionProofSource::ReplayEvidence { .. } => {
                ClaimedAttributionSource::FlatRetained
            }
        };
        let admission = RecordProofClauseLinkAdmission {
            support: clause.support(),
            clause: clause.record_clause(),
            claimed_attribution_source: Some(claimed_attribution_source),
            claimed_proof_source: Some(source),
        };
        if Self::projection_clause(admission) != clause {
            debug_assert!(
                false,
                "decisive claimed clause attribution must match its raw audit metadata"
            );
            return Ok(None);
        }
        let (key, proof) = self
            .claimed_projection_proof(bound, admission)?
            .expect("claimed decisive clause produces one normalized certificate key");
        Ok(Some(ClaimedProjectionProof::from_key(
            key,
            proof.representative_claim(),
        )))
    }

    fn decisive_claimed_projection_proof_from_incidence(
        &self,
        bound: BoundRecordId,
        support_id: ProjectionSupportGroupId,
        entry_id: ProjectionFormulaEntryId,
    ) -> Result<Option<ClaimedProjectionProof>, ProofFailure> {
        let Some(bucket) = self.projection_formula_shadow.by_record.get(&bound) else {
            debug_assert!(false, "decisive PCLF incidence must retain its record bucket");
            return Ok(None);
        };
        let Some(group) = bucket.support_groups.get(support_id.0 as usize) else {
            debug_assert!(false, "decisive PCLF incidence must retain its support group");
            return Ok(None);
        };
        let Some(entry_id) = bucket.legacy_decisive_entry_id(support_id, entry_id) else {
            debug_assert!(
                false,
                "decisive claimed standalone clause must retain the exact raw audit identity selected by legacy"
            );
            return Ok(None);
        };
        let Some(entry) = bucket.entries.get(entry_id.0 as usize) else {
            debug_assert!(false, "decisive PCLF incidence must retain its clause entry");
            return Ok(None);
        };
        let SchemeProjectionProofSupport::Claimed(_) = group.raw_support else {
            debug_assert!(false, "decisive claimed PCLF incidence must use a claimed support");
            return Ok(None);
        };
        let Some(ProjectionIncidenceMetadata::Claimed(template)) =
            bucket.exact_links.get(&(support_id, entry_id)).copied()
        else {
            debug_assert!(false, "decisive claimed PCLF incidence must retain claimed metadata");
            return Ok(None);
        };
        let Some(coverage_root) = group.coverage_root else {
            debug_assert!(false, "claimed PCLF support group must retain its frozen coverage root");
            return Ok(None);
        };
        let source = template.with_coverage_root(coverage_root);
        let claimed_attribution_source = match source {
            ClaimedProjectionProofSource::ReplayConstraint { .. } => {
                ClaimedAttributionSource::CanonicalReplay
            }
            ClaimedProjectionProofSource::Original { .. }
            | ClaimedProjectionProofSource::DerivedUnary { .. }
            | ClaimedProjectionProofSource::ReplayEvidence { .. } => {
                ClaimedAttributionSource::FlatRetained
            }
        };
        let admission = RecordProofClauseLinkAdmission {
            support: group.raw_support,
            clause: entry.clause,
            claimed_attribution_source: Some(claimed_attribution_source),
            claimed_proof_source: Some(source),
        };
        let (key, proof) = self
            .claimed_projection_proof(bound, admission)?
            .expect("claimed decisive PCLF incidence produces one normalized certificate key");
        let proof = ClaimedProjectionProof::from_key(key, proof.representative_claim());
        #[cfg(test)]
        {
            let legacy_clause = Self::projection_clause(admission);
            debug_assert_eq!(
                self.decisive_claimed_projection_proof(bound, legacy_clause)?,
                Some(proof),
                "PCLF decisive incidence reconstruction must remain byte-equal to legacy audit lookup",
            );
        }
        Ok(Some(proof))
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
        let dependency_result = match (&result, &cause) {
            (
                ProofResult::Semantic(SemanticFactRef::Constraint(result)),
                ProofCause::Structural(_) | ProofCause::ReductionRoute { .. },
            ) => Some(*result),
            _ => None,
        };
        let event = self.occurrences.len();
        self.occurrences.push(ProofOccurrence {
            result,
            cause,
            parents,
            event,
            completeness,
        });
        if let Some(result) = dependency_result {
            self.dependency_occurrence_indices_by_result
                .entry(result)
                .or_default()
                .push(event);
        }
        let occurrence = &self.occurrences[event];
        let carrier_index = &mut self.projection_carrier_occurrence_index;
        let mut record_carrier = |carrier| {
            carrier_index.entry(carrier).or_insert(event);
        };
        match (&occurrence.result, &occurrence.cause) {
            (
                ProofResult::Semantic(SemanticFactRef::Constraint(constraint)),
                ProofCause::Root(origin),
            ) => record_carrier(ProjectionProofCarrier::ConstraintOrigin {
                constraint: *constraint,
                origin: *origin,
            }),
            (
                ProofResult::Semantic(SemanticFactRef::Constraint(result)),
                ProofCause::Structural(derivation),
            ) => record_carrier(ProjectionProofCarrier::StructuralConstraint {
                result: *result,
                derivation: *derivation,
            }),
            (
                ProofResult::Semantic(SemanticFactRef::Constraint(result)),
                ProofCause::RowConstraint(derivation),
            ) => record_carrier(ProjectionProofCarrier::RowConstraint {
                result: *result,
                derivation: *derivation,
            }),
            (
                ProofResult::Semantic(SemanticFactRef::Constraint(result)),
                ProofCause::SchemeInstantiationDerivation(derivation),
            ) => record_carrier(ProjectionProofCarrier::SchemeInstantiationConstraint {
                result: *result,
                source_witness: derivation.source_witness,
            }),
            (
                ProofResult::Semantic(SemanticFactRef::Constraint(result)),
                ProofCause::SchemeInstantiationRoute(route),
            ) => record_carrier(ProjectionProofCarrier::SchemeInstantiationConstraint {
                result: *result,
                source_witness: route.derivation.source_witness,
            }),
            _ => {}
        }
        match &occurrence.cause {
            ProofCause::Root(origin) | ProofCause::Bound(BoundDerivation::Origin(origin)) => {
                record_carrier(ProjectionProofCarrier::Origin(*origin));
            }
            ProofCause::ReplayEvidence(derivation) => {
                record_carrier(ProjectionProofCarrier::ReplayEvidence(*derivation));
            }
            _ => {}
        }
        for parent in &occurrence.parents {
            match parent {
                ProofParent::Origin(origin) => {
                    record_carrier(ProjectionProofCarrier::Origin(*origin));
                }
                ProofParent::GeneralizedWitness(witness) => {
                    record_carrier(ProjectionProofCarrier::SchemeInstantiation(*witness));
                }
                _ => {}
            }
        }
        if let ProofResult::Semantic(SemanticFactRef::RowDerivation(derivation)) =
            occurrence.result
        {
            self.row_derivation_occurrence_index
                .entry(derivation)
                .or_insert(event);
        }
    }

    fn projection_carrier_occurrence(
        &self,
        carrier: ProjectionProofCarrier,
    ) -> Option<&ProofOccurrence> {
        let index = self
            .projection_carrier_occurrence_index
            .get(&carrier)
            .copied()?;
        let occurrence = self
            .occurrences
            .get(index)
            .expect("a projection carrier occurrence index must reference a recorded occurrence");
        assert!(
            Self::occurrence_matches_projection_carrier(occurrence, carrier),
            "a projection carrier occurrence index must reference its own carrier"
        );
        Some(occurrence)
    }

    fn row_derivation_occurrence(
        &self,
        derivation: RowDerivationId,
    ) -> Option<&ProofOccurrence> {
        let index = self
            .row_derivation_occurrence_index
            .get(&derivation)
            .copied()?;
        let occurrence = self
            .occurrences
            .get(index)
            .expect("a row derivation occurrence index must reference a recorded occurrence");
        assert_eq!(
            occurrence.result,
            ProofResult::Semantic(SemanticFactRef::RowDerivation(derivation)),
            "a row derivation occurrence index must reference its own derivation"
        );
        Some(occurrence)
    }

    fn occurrence_matches_projection_carrier(
        occurrence: &ProofOccurrence,
        carrier: ProjectionProofCarrier,
    ) -> bool {
        match carrier {
            ProjectionProofCarrier::ConstraintOrigin { constraint, origin } => {
                occurrence.result
                    == ProofResult::Semantic(SemanticFactRef::Constraint(constraint))
                    && matches!(occurrence.cause, ProofCause::Root(candidate) if candidate == origin)
            }
            ProjectionProofCarrier::StructuralConstraint { result, derivation } => {
                occurrence.result
                    == ProofResult::Semantic(SemanticFactRef::Constraint(result))
                    && matches!(&occurrence.cause, ProofCause::Structural(candidate) if *candidate == derivation)
            }
            ProjectionProofCarrier::RowConstraint { result, derivation } => {
                occurrence.result
                    == ProofResult::Semantic(SemanticFactRef::Constraint(result))
                    && matches!(occurrence.cause, ProofCause::RowConstraint(candidate) if candidate == derivation)
            }
            ProjectionProofCarrier::SchemeInstantiationConstraint {
                result,
                source_witness,
            } => {
                occurrence.result
                    == ProofResult::Semantic(SemanticFactRef::Constraint(result))
                    && match &occurrence.cause {
                        ProofCause::SchemeInstantiationDerivation(derivation) => {
                            derivation.source_witness == source_witness
                        }
                        ProofCause::SchemeInstantiationRoute(route) => {
                            route.derivation.source_witness == source_witness
                        }
                        _ => false,
                    }
            }
            ProjectionProofCarrier::Origin(origin) => {
                matches!(occurrence.cause, ProofCause::Root(candidate) if candidate == origin)
                    || matches!(occurrence.cause, ProofCause::Bound(BoundDerivation::Origin(candidate)) if candidate == origin)
                    || occurrence
                        .parents
                        .iter()
                        .any(|parent| *parent == ProofParent::Origin(origin))
            }
            ProjectionProofCarrier::ReplayEvidence(derivation) => {
                matches!(&occurrence.cause, ProofCause::ReplayEvidence(candidate) if *candidate == derivation)
            }
            ProjectionProofCarrier::SchemeInstantiation(witness) => occurrence
                .parents
                .iter()
                .any(|parent| *parent == ProofParent::GeneralizedWitness(witness)),
            ProjectionProofCarrier::ReplayConstraint { .. }
            | ProjectionProofCarrier::Row(_)
            | ProjectionProofCarrier::Incomplete => false,
        }
    }

    #[cfg(test)]
    fn debug_assert_result_bucket_indexes_match_linear_scans(&self) {
        let mut expected_replays = FxHashMap::<ConstraintRecordId, Vec<usize>>::default();
        for (index, occurrence) in self.replay_finite_map.iter().enumerate() {
            expected_replays
                .entry(occurrence.result)
                .or_default()
                .push(index);
        }
        debug_assert_eq!(self.replay_indices_by_result, expected_replays);

        let mut expected_dependencies = FxHashMap::<ConstraintRecordId, Vec<usize>>::default();
        for (index, occurrence) in self.occurrences.iter().enumerate() {
            let ProofResult::Semantic(SemanticFactRef::Constraint(result)) = occurrence.result
            else {
                continue;
            };
            if matches!(
                occurrence.cause,
                ProofCause::Structural(_) | ProofCause::ReductionRoute { .. }
            ) {
                expected_dependencies.entry(result).or_default().push(index);
            }
        }
        debug_assert_eq!(
            self.dependency_occurrence_indices_by_result,
            expected_dependencies
        );
    }

    #[cfg(test)]
    fn debug_assert_occurrence_membership_indexes_match_linear_scans(&self) {
        let mut expected_carriers = FxHashMap::<ProjectionProofCarrier, usize>::default();
        let mut expected_row_derivations = FxHashMap::<RowDerivationId, usize>::default();
        for (index, occurrence) in self.occurrences.iter().enumerate() {
            let mut record_carrier = |carrier| {
                expected_carriers.entry(carrier).or_insert(index);
            };
            match (&occurrence.result, &occurrence.cause) {
                (
                    ProofResult::Semantic(SemanticFactRef::Constraint(constraint)),
                    ProofCause::Root(origin),
                ) => record_carrier(ProjectionProofCarrier::ConstraintOrigin {
                    constraint: *constraint,
                    origin: *origin,
                }),
                (
                    ProofResult::Semantic(SemanticFactRef::Constraint(result)),
                    ProofCause::Structural(derivation),
                ) => record_carrier(ProjectionProofCarrier::StructuralConstraint {
                    result: *result,
                    derivation: *derivation,
                }),
                (
                    ProofResult::Semantic(SemanticFactRef::Constraint(result)),
                    ProofCause::RowConstraint(derivation),
                ) => record_carrier(ProjectionProofCarrier::RowConstraint {
                    result: *result,
                    derivation: *derivation,
                }),
                (
                    ProofResult::Semantic(SemanticFactRef::Constraint(result)),
                    ProofCause::SchemeInstantiationDerivation(derivation),
                ) => record_carrier(ProjectionProofCarrier::SchemeInstantiationConstraint {
                    result: *result,
                    source_witness: derivation.source_witness,
                }),
                (
                    ProofResult::Semantic(SemanticFactRef::Constraint(result)),
                    ProofCause::SchemeInstantiationRoute(route),
                ) => record_carrier(ProjectionProofCarrier::SchemeInstantiationConstraint {
                    result: *result,
                    source_witness: route.derivation.source_witness,
                }),
                _ => {}
            }
            match &occurrence.cause {
                ProofCause::Root(origin) | ProofCause::Bound(BoundDerivation::Origin(origin)) => {
                    record_carrier(ProjectionProofCarrier::Origin(*origin));
                }
                ProofCause::ReplayEvidence(derivation) => {
                    record_carrier(ProjectionProofCarrier::ReplayEvidence(*derivation));
                }
                _ => {}
            }
            for parent in &occurrence.parents {
                match parent {
                    ProofParent::Origin(origin) => {
                        record_carrier(ProjectionProofCarrier::Origin(*origin));
                    }
                    ProofParent::GeneralizedWitness(witness) => {
                        record_carrier(ProjectionProofCarrier::SchemeInstantiation(*witness));
                    }
                    _ => {}
                }
            }
            if let ProofResult::Semantic(SemanticFactRef::RowDerivation(derivation)) =
                occurrence.result
            {
                expected_row_derivations
                    .entry(derivation)
                    .or_insert(index);
            }
        }
        debug_assert_eq!(self.projection_carrier_occurrence_index, expected_carriers);
        debug_assert_eq!(
            self.row_derivation_occurrence_index,
            expected_row_derivations
        );
        for (carrier, index) in &self.projection_carrier_occurrence_index {
            let occurrence = self
                .occurrences
                .get(*index)
                .expect("a projection carrier occurrence index must reference a raw occurrence");
            debug_assert!(Self::occurrence_matches_projection_carrier(
                occurrence,
                *carrier
            ));
        }
        for (derivation, index) in &self.row_derivation_occurrence_index {
            debug_assert_eq!(
                self.occurrences
                    .get(*index)
                    .expect("a row derivation occurrence index must reference a raw occurrence")
                    .result,
                ProofResult::Semantic(SemanticFactRef::RowDerivation(*derivation))
            );
        }
    }

    #[cfg(test)]
    fn debug_assert_projection_formula_support_keys_match_linear_scan(&self) {
        let expected = self
            .projection_formulas
            .iter()
            .map(|(record, clauses)| {
                let support_keys = clauses
                    .iter()
                    .copied()
                    .filter_map(|clause| self.projection_support_match_key(clause.support()))
                    .collect::<FxHashSet<_>>();
                (*record, support_keys)
            })
            .collect::<FxHashMap<_, _>>();
        debug_assert_eq!(self.projection_formula_support_keys, expected);
    }

    #[cfg(test)]
    fn legacy_projection_formula_read_model(&self) -> ProjectionFormulaReadModel {
        ProjectionFormulaReadModel {
            formulas: self.projection_formulas.clone(),
            claimed_links: self.projection_claimed_link_audit.clone(),
            independent_links: self.independent_projection_clause_link_keys.clone(),
            distinct_clauses: self.projection_clause_keys.clone(),
            normalized_support_keys: self.projection_formula_support_keys.clone(),
            attributed_roots: self.projection_attributions.clone(),
            flat_retained_attributed_roots: self
                .flat_retained_projection_attributions
                .clone(),
        }
    }

    #[cfg(test)]
    fn debug_assert_pclf_a_read_model_matches_legacy(&self) {
        if QORF_C_FULL_STD_PARITY_ACTIVE.with(Cell::get) {
            return;
        }
        let legacy = self.legacy_projection_formula_read_model();
        let factored = self.projection_formula_shadow.read_model();
        debug_assert_eq!(factored, legacy);
    }

    #[cfg(test)]
    fn claimed_projection_proofs_from_audit_for_test(
        &self,
    ) -> FxHashMap<
        BoundRecordId,
        FxHashMap<ClaimedProjectionProofKey, UpperReplayClaimId>,
    > {
        let mut reconstructed = FxHashMap::<
            BoundRecordId,
            FxHashMap<ClaimedProjectionProofKey, UpperReplayClaimId>,
        >::default();
        for (&(bound, support, clause), &source) in &self.projection_claimed_link_audit {
            let admission = RecordProofClauseLinkAdmission {
                support,
                clause,
                claimed_attribution_source: Some(match source {
                    ClaimedProjectionProofSource::ReplayConstraint { .. } => {
                        ClaimedAttributionSource::CanonicalReplay
                    }
                    ClaimedProjectionProofSource::Original { .. }
                    | ClaimedProjectionProofSource::DerivedUnary { .. }
                    | ClaimedProjectionProofSource::ReplayEvidence { .. } => {
                        ClaimedAttributionSource::FlatRetained
                    }
                }),
                claimed_proof_source: Some(source),
            };
            let (key, proof) = self
                .claimed_projection_proof(bound, admission)
                .expect("raw claimed certificate source must remain resolvable")
                .expect("raw claimed certificate source must produce one certificate");
            let representative_claim = proof.representative_claim();
            reconstructed
                .entry(bound)
                .or_default()
                .entry(key)
                .and_modify(|current| *current = (*current).min(representative_claim))
                .or_insert(representative_claim);
        }
        reconstructed
    }

    #[cfg(test)]
    fn debug_assert_claimed_projection_audit_reconstructs(&self) {
        for &(_, support, _) in &self.independent_projection_clause_link_keys {
            debug_assert!(
                matches!(support, SchemeProjectionProofSupport::Independent(_)),
                "the independent raw-link ledger must not duplicate claimed audit identities",
            );
        }
        for &(_, support, _) in self.projection_claimed_link_audit.keys() {
            debug_assert!(
                matches!(support, SchemeProjectionProofSupport::Claimed(_)),
                "the claimed audit ledger must contain only claimed raw-link identities",
            );
        }
        let reconstructed = self.claimed_projection_proofs_from_audit_for_test();
        debug_assert!(
            reconstructed
                .values()
                .map(FxHashMap::len)
                .sum::<usize>()
                <= self.projection_claimed_link_audit.len(),
            "normalized certificate count cannot exceed exact raw claimed-link count",
        );
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

    pub(super) fn root_claim_for_producer(
        &self,
        producer: ConstraintRecordId,
    ) -> Option<UpperReplayClaimId> {
        self.root_claim_by_producer_constraint
            .get(&producer)
            .copied()
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
        let mut pending_roots = Vec::new();
        for claim in &claimed_parents {
            let root = self
                .upper_claim(*claim)
                .expect("a projection support must reference an admitted CPK claim")
                .coverage_root;
            if !self
                .projection_lower_record_memberships
                .contains(&(root, lower_record))
                && !pending_roots.contains(&root)
            {
                pending_roots.push(root);
            }
        }
        self.projection_lower_record_memberships
            .reserve(pending_roots.len());
        self.projection_lower_records_by_root
            .reserve(pending_roots.len());
        for root in &pending_roots {
            self.projection_lower_records_by_root
                .entry(*root)
                .or_default()
                .reserve(1);
        }
        self.claimed_parents_by_lower_record.reserve(1);
        self.projection_supports.reserve(1);

        for root in pending_roots {
            let inserted = self
                .projection_lower_record_memberships
                .insert((root, lower_record));
            debug_assert!(inserted);
            self.projection_lower_records_by_root
                .entry(root)
                .or_default()
                .push(lower_record);
        }
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

    pub(super) fn projection_clause_link_is_registered(
        &self,
        lower_record: BoundRecordId,
        support: SchemeProjectionProofSupport,
        clause: RecordProofClause,
    ) -> bool {
        self.projection_clause_membership(lower_record, support, clause)
            .exact_link_registered
    }

    fn projection_clause_membership(
        &self,
        lower_record: BoundRecordId,
        support: SchemeProjectionProofSupport,
        clause: RecordProofClause,
    ) -> ProjectionClauseMembership {
        let bucket = self.projection_formula_shadow.by_record.get(&lower_record);
        let support_id = bucket
            .and_then(|bucket| bucket.support_group_by_raw.get(&support).copied());
        let entry_id = bucket.and_then(|bucket| bucket.entry_by_clause.get(&clause).copied());
        let exact_link_registered = match (bucket, support_id, entry_id) {
            (Some(bucket), Some(support_id), Some(entry_id)) => {
                bucket.exact_links.contains_key(&(support_id, entry_id))
            }
            _ => false,
        };
        #[cfg(test)]
        {
            PROJECTION_CLAUSE_MEMBERSHIP_CENSUS.with(|cell| {
                let mut census = cell.get();
                census.membership_queries += 1;
                census.record_bucket_hash_lookups += 1;
                census.support_hash_lookups += usize::from(bucket.is_some());
                census.clause_hash_lookups += usize::from(bucket.is_some());
                census.incidence_hash_lookups +=
                    usize::from(bucket.is_some() && support_id.is_some() && entry_id.is_some());
                cell.set(census);
            });
        }
        ProjectionClauseMembership {
            exact_link_registered,
            clause_registered: entry_id.is_some(),
        }
    }

    fn registered_projection_incidence_claimed_source(
        &self,
        lower_record: BoundRecordId,
        support: SchemeProjectionProofSupport,
        clause: RecordProofClause,
    ) -> Option<ClaimedProjectionProofSource> {
        let bucket = self
            .projection_formula_shadow
            .by_record
            .get(&lower_record)
            .expect("registered PCLF incidence must retain its record bucket");
        let support_id = bucket.support_group_by_raw[&support];
        let entry_id = bucket.entry_by_clause[&clause];
        let metadata = bucket.exact_links[&(support_id, entry_id)];
        let group = &bucket.support_groups[support_id.0 as usize];
        assert_eq!(group.raw_support, support);
        match (support, metadata) {
            (
                SchemeProjectionProofSupport::Claimed(_),
                ProjectionIncidenceMetadata::Claimed(template),
            ) => Some(template.with_coverage_root(
                group
                    .coverage_root
                    .expect("claimed PCLF support group must retain its frozen root"),
            )),
            (
                SchemeProjectionProofSupport::Independent(_),
                ProjectionIncidenceMetadata::Independent,
            ) => None,
            #[cfg(test)]
            (
                SchemeProjectionProofSupport::Independent(_),
                ProjectionIncidenceMetadata::IndependentWithForcedLineage(_),
            ) => None,
            _ => panic!("registered PCLF incidence metadata must match its raw support kind"),
        }
    }

    #[cfg(test)]
    fn projection_clause_is_registered(
        &self,
        lower_record: BoundRecordId,
        clause: RecordProofClause,
    ) -> bool {
        self.projection_formula_shadow
            .by_record
            .get(&lower_record)
            .is_some_and(|bucket| bucket.entry_by_clause.contains_key(&clause))
    }

    #[cfg(test)]
    fn legacy_projection_clause_link_is_registered_for_test(
        &self,
        lower_record: BoundRecordId,
        support: SchemeProjectionProofSupport,
        clause: RecordProofClause,
    ) -> bool {
        let identity = (lower_record, support, clause);
        match support {
            SchemeProjectionProofSupport::Claimed(_) => {
                self.projection_claimed_link_audit.contains_key(&identity)
            }
            SchemeProjectionProofSupport::Independent(_) => self
                .independent_projection_clause_link_keys
                .contains(&identity),
        }
    }

    #[cfg(test)]
    fn legacy_projection_clause_is_registered_for_test(
        &self,
        lower_record: BoundRecordId,
        clause: RecordProofClause,
    ) -> bool {
        self.projection_clause_keys
            .contains(&(lower_record, clause))
    }

    #[cfg(test)]
    fn reset_projection_clause_membership_census_for_test(&self) {
        PROJECTION_CLAUSE_MEMBERSHIP_CENSUS.with(|cell| cell.set(Default::default()));
    }

    #[cfg(test)]
    fn projection_clause_membership_census_for_test(
        &self,
    ) -> ProjectionClauseMembershipCensus {
        PROJECTION_CLAUSE_MEMBERSHIP_CENSUS.with(Cell::get)
    }

    #[cfg(test)]
    pub(super) fn projection_clauses_for_test(
        &self,
        lower_record: BoundRecordId,
    ) -> Vec<RecordProofClause> {
        let mut clauses = self
            .projection_clause_keys
            .iter()
            .filter_map(|(record, clause)| (*record == lower_record).then_some(*clause))
            .collect::<Vec<_>>();
        clauses.sort_unstable_by(|left, right| record_proof_clause_cmp(*left, *right));
        clauses
    }

    #[cfg(test)]
    pub(super) fn projection_clause_links_for_test(
        &self,
        lower_record: BoundRecordId,
    ) -> Vec<(SchemeProjectionProofSupport, RecordProofClause)> {
        self.independent_projection_clause_link_keys
            .iter()
            .filter_map(|(record, support, clause)| {
                (*record == lower_record).then_some((*support, *clause))
            })
            .chain(
                self.projection_claimed_link_audit
                    .keys()
                    .filter_map(|(record, support, clause)| {
                        (*record == lower_record).then_some((*support, *clause))
                    }),
            )
            .collect()
    }

    #[cfg(test)]
    pub(super) fn projection_clause_storage_census_for_test(
        &self,
    ) -> (usize, usize, usize, usize) {
        (
            self.projection_clause_keys.len(),
            self.independent_projection_clause_link_keys.len()
                + self.projection_claimed_link_audit.len(),
            self.projection_formulas.len(),
            self.projection_attributions.len(),
        )
    }

    #[cfg(test)]
    fn force_noncanonical_projection_formula_order_for_test(
        &mut self,
        record: BoundRecordId,
        clauses: Vec<ProjectionClause>,
    ) {
        let existing = self
            .projection_formulas
            .get(&record)
            .expect("the production writer must create the formula before order corruption");
        let mut canonical_existing = existing.clone();
        let mut canonical_replacement = clauses.clone();
        canonical_existing.sort_unstable_by(|left, right| left.canonical_cmp(*right));
        canonical_replacement.sort_unstable_by(|left, right| left.canonical_cmp(*right));
        assert_eq!(canonical_replacement, canonical_existing);
        let bucket = self
            .projection_formula_shadow
            .by_record
            .get_mut(&record)
            .expect("the production writer must create the factored formula before corruption");
        let mut available = std::mem::take(&mut bucket.canonical_runs);
        let mut replacement_runs = Vec::new();
        replacement_runs.reserve_exact(available.len());
        for clause in &clauses {
            let support_id = bucket.support_group_by_raw[&clause.support()];
            let category = CanonicalProjectionCategory::from_clause(clause.record_clause());
            let position = available
                .iter()
                .position(|run| run.category == category && run.support_id == support_id)
                .expect("the replacement order must name every existing one-entry run");
            assert_eq!(
                available[position].entry_len, 1,
                "this narrow corruption hook only reorders one-entry canonical runs",
            );
            replacement_runs.push(available.remove(position));
        }
        assert!(available.is_empty());
        bucket.canonical_runs = replacement_runs;
        self.projection_formulas.insert(record, clauses);
    }

    #[cfg(test)]
    fn force_projection_clause_lineage_for_test(
        &mut self,
        record: BoundRecordId,
        lineage: ProjectionLineage,
    ) {
        let [ProjectionClause::Standalone { support, .. }] = self
            .projection_formulas
            .get(&record)
            .expect("the production writer must create the formula before lineage corruption")
            .as_slice()
        else {
            panic!("lineage corruption fixture must stay standalone");
        };
        let support = *support;
        let clause = RecordProofClause::Standalone { support };
        let bucket = self
            .projection_formula_shadow
            .by_record
            .get_mut(&record)
            .expect("the production writer must create the shadow bucket before corruption");
        let support_id = bucket.support_group_by_raw[&support];
        let entry_id = bucket.entry_by_clause[&clause];
        let metadata = bucket
            .exact_links
            .get_mut(&(support_id, entry_id))
            .expect("the production writer must create the exact shadow incidence");
        assert_eq!(*metadata, ProjectionIncidenceMetadata::Independent);
        *metadata = ProjectionIncidenceMetadata::IndependentWithForcedLineage(lineage);

        let [ProjectionClause::Standalone { attribution, .. }] = self
            .projection_formulas
            .get_mut(&record)
            .expect("the production writer must create the formula before lineage corruption")
            .as_mut_slice()
        else {
            unreachable!("lineage corruption fixture shape was validated before mutation");
        };
        *attribution = Some(lineage);
    }

    #[cfg(test)]
    fn force_present_empty_projection_formula_for_test(&mut self, record: BoundRecordId) {
        assert!(!self.projection_formulas.contains_key(&record));
        assert!(!self.projection_formula_shadow.by_record.contains_key(&record));
        self.projection_formulas.insert(record, Vec::new());
        self.projection_formula_support_keys
            .insert(record, FxHashSet::default());
        self.projection_formula_shadow
            .by_record
            .insert(record, ProjectionFormulaBucket::default());
    }

    fn try_prepare_projection_formula_shadow_admission(
        &mut self,
        lower_record: BoundRecordId,
        accepted: &[AcceptedProjectionClauseAdmission],
    ) -> Result<PreparedProjectionFormulaShadowAdmission, ProofFailure> {
        let exhausted = |_| ProofFailure::ResourceExhausted {
            operation: ProofOperation::UpdateClaimLifecycle,
        };
        #[cfg(test)]
        let fail_during_shadow_structure = self.take_projection_clause_reservation_failure(
            ProjectionClauseReservationFailurePoint::ShadowStructure,
        );
        #[cfg(test)]
        let fail_during_shadow_canonical_runs = self.take_projection_clause_reservation_failure(
            ProjectionClauseReservationFailurePoint::ShadowCanonicalRuns,
        );
        #[cfg(test)]
        let mut fail_after_canonical_run_reservations = self
            .projection_clause_canonical_run_reservation_failure_after
            .take();
        #[cfg(test)]
        let fail_during_shadow_normalized_support = self
            .take_projection_clause_reservation_failure(
                ProjectionClauseReservationFailurePoint::ShadowNormalizedSupport,
            );
        let existing = self.projection_formula_shadow.by_record.get(&lower_record);
        let base_entry_len = existing.map_or(0, |bucket| bucket.entries.len());
        let base_support_len = existing.map_or(0, |bucket| bucket.support_groups.len());
        let mut delta = ProjectionFormulaShadowDelta::default();
        delta
            .new_entries
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        delta
            .new_support_groups
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        delta
            .exact_links
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        delta
            .canonical_run_deltas
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        delta
            .new_canonical_runs
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        delta
            .support_match_key_promotions
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        delta
            .normalized_support_keys
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        delta
            .attributed_roots
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        delta
            .flat_retained_attributed_roots
            .try_reserve(accepted.len())
            .map_err(exhausted)?;

        let mut pending_entries = FxHashMap::default();
        let mut pending_supports = FxHashMap::default();
        let mut pending_exact = FxHashSet::default();
        let mut pending_normalized = FxHashSet::default();
        let mut pending_match_key_promotions = FxHashMap::default();
        let mut pending_attributed = FxHashSet::default();
        let mut pending_flat = FxHashSet::default();
        let mut pending_run_entries = Vec::<(
            CanonicalProjectionCategory,
            SchemeProjectionProofSupport,
            ProjectionSupportGroupId,
            ProjectionFormulaEntryId,
            ProjectionClause,
        )>::new();
        pending_entries
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        pending_supports
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        pending_exact
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        pending_normalized
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        pending_match_key_promotions
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        pending_attributed
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        pending_flat
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        pending_run_entries
            .try_reserve(accepted.len())
            .map_err(exhausted)?;

        for event in accepted {
            let admission = event.admission;
            let entry_id = existing
                .and_then(|bucket| bucket.entry_by_clause.get(&admission.clause).copied())
                .or_else(|| pending_entries.get(&admission.clause).copied())
                .unwrap_or_else(|| {
                    let id = ProjectionFormulaEntryId(
                        u32::try_from(base_entry_len + delta.new_entries.len())
                            .expect("PCLF record-local entry id must fit u32"),
                    );
                    delta.new_entries.push(ProjectionFormulaEntry {
                        clause: admission.clause,
                    });
                    assert!(pending_entries.insert(admission.clause, id).is_none());
                    id
                });
            let (metadata, match_key, coverage_root) = match admission.support {
                SchemeProjectionProofSupport::Claimed(_) => {
                    let source = admission
                        .claimed_proof_source
                        .expect("claimed admission metadata was constructor-validated");
                    let (root, template) = ClaimedProjectionSourceTemplate::from_source(source);
                    (
                        ProjectionIncidenceMetadata::Claimed(template),
                        None,
                        Some(root),
                    )
                }
                SchemeProjectionProofSupport::Independent(carrier) => (
                    ProjectionIncidenceMetadata::Independent,
                    Some(ProjectionSupportMatchKey::Independent(carrier)),
                    None,
                ),
            };
            let support_id = if let Some(support_id) = existing
                .and_then(|bucket| bucket.support_group_by_raw.get(&admission.support).copied())
                .or_else(|| pending_supports.get(&admission.support).copied())
            {
                support_id
            } else {
                let id = try_projection_support_group_id(
                    base_support_len + delta.new_support_groups.len(),
                )?;
                delta.new_support_groups.push(ProjectionSupportGroup {
                    raw_support: admission.support,
                    match_key,
                    coverage_root,
                });
                assert!(pending_supports.insert(admission.support, id).is_none());
                id
            };
            let group = if (support_id.0 as usize) < base_support_len {
                &existing
                    .expect("existing support has a bucket")
                    .support_groups[support_id.0 as usize]
            } else {
                &delta.new_support_groups[support_id.0 as usize - base_support_len]
            };
            assert_eq!(group.coverage_root, coverage_root);
            let effective_match_key = pending_match_key_promotions
                .get(&support_id)
                .copied()
                .or(group.match_key);
            match (effective_match_key, match_key) {
                (None, Some(key)) => {
                    assert!(
                        pending_match_key_promotions
                            .insert(support_id, key)
                            .is_none()
                    );
                    delta.support_match_key_promotions.push((support_id, key));
                }
                (Some(existing), Some(current)) => assert_eq!(existing, current),
                (Some(_), None) | (None, None) => {}
            }
            let incidence = (support_id, entry_id);
            assert!(existing.is_none_or(|bucket| !bucket.exact_links.contains_key(&incidence)));
            assert!(pending_exact.insert(incidence));
            delta.exact_links.push((support_id, entry_id, metadata));
            pending_run_entries.push((
                CanonicalProjectionCategory::from_clause(admission.clause),
                admission.support,
                support_id,
                entry_id,
                Self::projection_clause(admission),
            ));
            if let Some(match_key) = match_key
                && existing
                    .is_none_or(|bucket| !bucket.normalized_support_keys.contains(&match_key))
                && pending_normalized.insert(match_key)
            {
                assert!(delta.normalized_support_keys.insert(match_key));
            }
            if let SchemeProjectionProofSupport::Claimed(claim) = admission.support {
                if existing.is_none_or(|bucket| !bucket.attributed_roots.contains(&claim))
                    && pending_attributed.insert(claim)
                {
                    delta.attributed_roots.push(claim);
                }
                if admission.claimed_attribution_source
                    == Some(ClaimedAttributionSource::FlatRetained)
                    && existing.is_none_or(|bucket| {
                        !bucket.flat_retained_attributed_roots.contains(&claim)
                    })
                    && pending_flat.insert(claim)
                {
                    delta.flat_retained_attributed_roots.push(claim);
                }
            }
        }

        pending_run_entries.sort_unstable_by(|left, right| {
            left.0
                .cmp(&right.0)
                .then_with(|| projection_support_cmp(left.1, right.1))
                .then_with(|| {
                    canonical_projection_incidence_cmp(left.4, left.3, right.4, right.3)
                })
        });
        let mut cursor = 0;
        while cursor < pending_run_entries.len() {
            let category = pending_run_entries[cursor].0;
            let support = pending_run_entries[cursor].1;
            let support_id = pending_run_entries[cursor].2;
            let mut end = cursor + 1;
            while end < pending_run_entries.len()
                && pending_run_entries[end].0 == category
                && pending_run_entries[end].2 == support_id
            {
                end += 1;
            }
            let existing_run_index = existing.and_then(|bucket| {
                let position = bucket.canonical_run_partition_point(category, support);
                bucket.canonical_runs.get(position).and_then(|run| {
                    (run.category == category && run.support_id == support_id).then_some(position)
                })
            });
            let mut entries = Vec::new();
            entries.try_reserve(end - cursor).map_err(exhausted)?;
            for item in &pending_run_entries[cursor..end] {
                entries.push((item.3, item.4));
            }
            if let Some(existing_run_index) = existing_run_index {
                let bucket = existing.expect("existing run has an existing bucket");
                let run = &bucket.canonical_runs[existing_run_index];
                let mut chunk_deltas = Vec::new();
                chunk_deltas.try_reserve(entries.len()).map_err(exhausted)?;
                let mut entry_cursor = 0usize;
                while entry_cursor < entries.len() {
                    let (target_entry, target_clause) = entries[entry_cursor];
                    let (target_chunk, mut lookup_comparisons) = run.target_chunk_by(|pivot| {
                        canonical_projection_incidence_cmp(
                            bucket.reconstructed_clause(support_id, pivot),
                            pivot,
                            target_clause,
                            target_entry,
                        )
                    });
                    let target_pivot = target_chunk.entries[0];
                    let start = entry_cursor;
                    entry_cursor += 1;
                    while entry_cursor < entries.len() {
                        let (entry, clause) = entries[entry_cursor];
                        let (next_chunk, comparisons) = run.target_chunk_by(|pivot| {
                            canonical_projection_incidence_cmp(
                                bucket.reconstructed_clause(support_id, pivot),
                                pivot,
                                clause,
                                entry,
                            )
                        });
                        lookup_comparisons += comparisons;
                        if next_chunk.entries[0] != target_pivot {
                            break;
                        }
                        entry_cursor += 1;
                    }
                    let existing_entries = &target_chunk.entries;
                    let (mut output_chunks, merge_comparisons, scanned_existing) =
                        try_prepare_projection_chunk_outputs(
                            bucket,
                            support_id,
                            existing_entries,
                            &entries[start..entry_cursor],
                        )
                        .map_err(exhausted)?;
                    let moved_entries = existing_entries.len() + entry_cursor - start;
                    let replacement_entries = output_chunks.remove(0);
                    let mut new_chunks = Vec::new();
                    new_chunks
                        .try_reserve_exact(output_chunks.len())
                        .map_err(exhausted)?;
                    for output in output_chunks {
                        new_chunks.push(
                            CanonicalProjectionRun::try_box_chunk(output).map_err(exhausted)?,
                        );
                    }
                    chunk_deltas.push(PreparedCanonicalProjectionChunkDelta {
                        target_pivot,
                        replacement_entries,
                        new_chunks,
                        lookup_comparisons,
                        merge_comparisons,
                        scanned_existing,
                        moved_entries,
                    });
                }
                delta
                    .canonical_run_deltas
                    .push(PreparedCanonicalProjectionRunDelta {
                        category,
                        support_id,
                        existing_run_index,
                        entry_count: entries.len(),
                        chunks: chunk_deltas,
                    });
                #[cfg(test)]
                if let Some(remaining) = fail_after_canonical_run_reservations.as_mut() {
                    assert!(*remaining > 0);
                    *remaining -= 1;
                    if *remaining == 0 {
                        return Err(ProofFailure::ResourceExhausted {
                            operation: ProofOperation::UpdateClaimLifecycle,
                        });
                    }
                }
            } else {
                let mut entry_ids = Vec::new();
                entry_ids.try_reserve(entries.len()).map_err(exhausted)?;
                entry_ids.extend(entries.into_iter().map(|item| item.0));
                delta.new_canonical_runs.push(
                    CanonicalProjectionRun::from_sorted_entries(
                        category,
                        support_id,
                        entry_ids,
                    )
                    .map_err(exhausted)?,
                );
            }
            cursor = end;
        }

        let mut new_record_bucket = (!self
            .projection_formula_shadow
            .by_record
            .contains_key(&lower_record))
        .then(ProjectionFormulaBucket::default);
        if new_record_bucket.is_some() {
            self.projection_formula_shadow
                .by_record
                .try_reserve(1)
                .map_err(exhausted)?;
        }
        let bucket = match new_record_bucket.as_mut() {
            Some(bucket) => bucket,
            None => self
                .projection_formula_shadow
                .by_record
                .get_mut(&lower_record)
                .expect("existing PCLF bucket must remain present during preflight"),
        };
        bucket
            .entries
            .try_reserve(delta.new_entries.len())
            .map_err(exhausted)?;
        bucket
            .entry_by_clause
            .try_reserve(delta.new_entries.len())
            .map_err(exhausted)?;
        bucket
            .support_groups
            .try_reserve(delta.new_support_groups.len())
            .map_err(exhausted)?;
        bucket
            .support_group_by_raw
            .try_reserve(delta.new_support_groups.len())
            .map_err(exhausted)?;
        bucket
            .exact_links
            .try_reserve(delta.exact_links.len())
            .map_err(exhausted)?;
        #[cfg(test)]
        if fail_during_shadow_structure {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }
        #[cfg(test)]
        if fail_during_shadow_normalized_support {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }
        // A claimed support can acquire its normalized coverage-root key after prepare but
        // before commit. Reserve the strict per-admission upper bound now; reserving only the
        // currently resolvable keys would permit commit-time promotion to allocate after the
        // legacy representation had already begun mutating.
        bucket
            .normalized_support_keys
            .try_reserve(accepted.len())
            .map_err(exhausted)?;
        bucket
            .attributed_roots
            .try_reserve(delta.attributed_roots.len())
            .map_err(exhausted)?;
        bucket
            .flat_retained_attributed_roots
            .try_reserve(delta.flat_retained_attributed_roots.len())
            .map_err(exhausted)?;
        bucket
            .canonical_runs
            .try_reserve(delta.new_canonical_runs.len())
            .map_err(exhausted)?;
        #[cfg(test)]
        if fail_during_shadow_canonical_runs {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }
        Ok(PreparedProjectionFormulaShadowAdmission {
            new_record_bucket,
            delta,
        })
    }

    fn projection_formula_movement_bucket(moved: usize) -> usize {
        (if moved == 0 {
            0
        } else {
            (usize::BITS - moved.leading_zeros()) as usize
        })
        .min(15)
    }

    fn commit_projection_formula_shadow_delta(
        bucket: &mut ProjectionFormulaBucket,
        delta: &mut ProjectionFormulaShadowDelta,
        movement: &mut ProjectionFormulaMovementCensus,
    ) {
        for entry in delta.new_entries.drain(..) {
            let id = ProjectionFormulaEntryId(
                u32::try_from(bucket.entries.len()).expect("PCLF entry id"),
            );
            assert!(bucket.entry_by_clause.insert(entry.clause, id).is_none());
            bucket.entries.push(entry);
        }
        for group in delta.new_support_groups.drain(..) {
            let id = ProjectionSupportGroupId(
                u32::try_from(bucket.support_groups.len()).expect("PCLF support id"),
            );
            let support = group.raw_support;
            assert!(bucket.support_group_by_raw.insert(support, id).is_none());
            bucket.support_groups.push(group);
        }
        for (support_id, entry_id, metadata) in delta.exact_links.drain(..) {
            assert!(
                bucket
                    .exact_links
                    .insert((support_id, entry_id), metadata)
                    .is_none()
            );
        }
        for run_delta in delta.canonical_run_deltas.drain(..) {
            let delta_len = run_delta.entry_count;
            movement.run_delta_count += 1;
            movement.run_delta_entries += delta_len as u64;
            movement.run_delta_max_entries = movement.run_delta_max_entries.max(delta_len);
            movement.run_delta_size_histogram
                [Self::projection_formula_movement_bucket(delta_len)] += 1;
            let run_index = run_delta.existing_run_index;
            let support_id = run_delta.support_id;
            for chunk_delta in run_delta.chunks {
                let output_count = 1 + chunk_delta.new_chunks.len();
                let entries = &bucket.entries;
                let support_groups = &bucket.support_groups;
                let exact_links = &bucket.exact_links;
                let run = &mut bucket.canonical_runs[run_index];
                let compare = |left, right| {
                    canonical_projection_incidence_cmp(
                        reconstructed_projection_clause(
                            entries,
                            support_groups,
                            exact_links,
                            support_id,
                            left,
                        ),
                        left,
                        reconstructed_projection_clause(
                            entries,
                            support_groups,
                            exact_links,
                            support_id,
                            right,
                        ),
                        right,
                    )
                };
                run.chunk_mut_by_pivot(chunk_delta.target_pivot, &compare)
                    .entries = chunk_delta.replacement_entries;
                for new_chunk in chunk_delta.new_chunks {
                    let root = run.chunk_root.take();
                    run.chunk_root = Some(CanonicalProjectionRun::insert_chunk_by(
                        root,
                        new_chunk,
                        &compare,
                    ));
                }
                movement.merge_calls += 1;
                movement.chunk_lookup_comparisons += chunk_delta.lookup_comparisons as u64;
                movement.merge_comparisons += chunk_delta.merge_comparisons as u64;
                movement.merge_scanned_entries += chunk_delta.scanned_existing as u64;
                movement.merge_moved_entries += chunk_delta.moved_entries as u64;
                movement.merge_max_scanned_entries = movement
                    .merge_max_scanned_entries
                    .max(chunk_delta.scanned_existing);
                movement.merge_scan_histogram[Self::projection_formula_movement_bucket(
                    chunk_delta.scanned_existing,
                )] += 1;
                movement.chunk_splits += output_count.saturating_sub(1) as u64;
            }
            bucket.canonical_runs[run_index].entry_len += delta_len;
        }
        if !delta.new_canonical_runs.is_empty() {
            for run in &delta.new_canonical_runs {
                movement.run_delta_count += 1;
                movement.run_delta_entries += run.entry_len as u64;
                movement.run_delta_max_entries =
                    movement.run_delta_max_entries.max(run.entry_len);
                movement.run_delta_size_histogram
                    [Self::projection_formula_movement_bucket(run.entry_len)] += 1;
            }
            let old_len = bucket.canonical_runs.len();
            let new_run_count = delta.new_canonical_runs.len();
            for _ in 0..new_run_count {
                bucket
                    .canonical_runs
                    .push(CanonicalProjectionRun::merge_placeholder());
            }
            let mut old_cursor = old_len;
            let mut new_cursor = new_run_count;
            let mut output_cursor = old_len + new_run_count;
            let mut comparisons = 0usize;
            let mut moved = 0usize;
            while old_cursor > 0 && new_cursor > 0 {
                let old_run = &bucket.canonical_runs[old_cursor - 1];
                let new_run = &delta.new_canonical_runs[new_cursor - 1];
                let old_support =
                    bucket.support_groups[old_run.support_id.0 as usize].raw_support;
                let new_support =
                    bucket.support_groups[new_run.support_id.0 as usize].raw_support;
                comparisons += 1;
                let ordering = old_run
                    .category
                    .cmp(&new_run.category)
                    .then_with(|| projection_support_cmp(old_support, new_support));
                assert_ne!(
                    ordering,
                    std::cmp::Ordering::Equal,
                    "PCLF canonical run key must stay unique",
                );
                output_cursor -= 1;
                if ordering == std::cmp::Ordering::Greater {
                    old_cursor -= 1;
                    let source = old_cursor;
                    let existing = std::mem::replace(
                        &mut bucket.canonical_runs[source],
                        CanonicalProjectionRun::merge_placeholder(),
                    );
                    moved += usize::from(source != output_cursor);
                    bucket.canonical_runs[output_cursor] = existing;
                } else {
                    new_cursor -= 1;
                    moved += 1;
                    bucket.canonical_runs[output_cursor] =
                        std::mem::replace(
                            &mut delta.new_canonical_runs[new_cursor],
                            CanonicalProjectionRun::merge_placeholder(),
                        );
                }
            }
            while new_cursor > 0 {
                new_cursor -= 1;
                output_cursor -= 1;
                moved += 1;
                bucket.canonical_runs[output_cursor] = std::mem::replace(
                    &mut delta.new_canonical_runs[new_cursor],
                    CanonicalProjectionRun::merge_placeholder(),
                );
            }
            debug_assert_eq!(output_cursor, old_cursor);
            movement.new_run_insertions += new_run_count as u64;
            movement.descriptor_comparisons += comparisons as u64;
            movement.descriptor_moved += moved as u64;
            movement.descriptor_max_moved = movement.descriptor_max_moved.max(moved);
            movement.descriptor_move_histogram
                [Self::projection_formula_movement_bucket(moved)] += 1;
            delta.new_canonical_runs.clear();
        }
        for (support_id, match_key) in delta.support_match_key_promotions.drain(..) {
            let group = &mut bucket.support_groups[support_id.0 as usize];
            assert!(group.match_key.is_none());
            group.match_key = Some(match_key);
        }
        for key in delta.normalized_support_keys.drain() {
            assert!(bucket.normalized_support_keys.insert(key));
        }
        for root in delta.attributed_roots.drain(..) {
            assert!(bucket.attributed_roots.insert(root));
        }
        for root in delta.flat_retained_attributed_roots.drain(..) {
            assert!(bucket.flat_retained_attributed_roots.insert(root));
        }
    }

    fn refresh_projection_formula_shadow_match_keys_at_commit(
        &self,
        lower_record: BoundRecordId,
        accepted: &[AcceptedProjectionClauseAdmission],
        shadow: &mut PreparedProjectionFormulaShadowAdmission,
    ) {
        // Legacy resolves normalized support at commit, and a prepared admission may straddle a
        // claim registration/move. The shadow therefore freezes raw incidence metadata during
        // prepare but derives this summary from the same commit-time snapshot as legacy.
        shadow.delta.normalized_support_keys.clear();
        shadow.delta.support_match_key_promotions.clear();
        let existing = self.projection_formula_shadow.by_record.get(&lower_record);
        for (event, &(support_id, _, _)) in accepted.iter().zip(&shadow.delta.exact_links) {
            let support = event.admission.support;
            let Some(match_key) = self.projection_support_match_key(support) else {
                continue;
            };
            let existing_support_len = existing.map_or(0, |bucket| bucket.support_groups.len());
            if (support_id.0 as usize) < existing_support_len {
                let current = existing.unwrap().support_groups[support_id.0 as usize].match_key;
                if let Some(current) = current {
                    assert_eq!(current, match_key);
                } else if !shadow
                    .delta
                    .support_match_key_promotions
                    .iter()
                    .any(|(pending, _)| *pending == support_id)
                {
                    shadow
                        .delta
                        .support_match_key_promotions
                        .push((support_id, match_key));
                }
            } else {
                let group = &mut shadow.delta.new_support_groups
                    [support_id.0 as usize - existing_support_len];
                assert_eq!(group.raw_support, support);
                if let Some(current) = group.match_key {
                    assert_eq!(current, match_key);
                } else {
                    group.match_key = Some(match_key);
                }
            }
            if existing.is_none_or(|bucket| !bucket.normalized_support_keys.contains(&match_key))
                && !shadow.delta.normalized_support_keys.contains(&match_key)
            {
                assert!(shadow.delta.normalized_support_keys.insert(match_key));
            }
        }
    }

    pub(super) fn try_prepare_projection_clause_admission(
        &mut self,
        lower_record: BoundRecordId,
        admissions: &[RecordProofClauseLinkAdmission],
    ) -> Result<Option<PreparedProjectionClauseAdmission>, ProofFailure> {
        let exhausted = |_| ProofFailure::ResourceExhausted {
            operation: ProofOperation::UpdateClaimLifecycle,
        };
        #[cfg(test)]
        if self.take_projection_clause_reservation_failure(
            ProjectionClauseReservationFailurePoint::Initial,
        ) {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }
        let mut accepted = Vec::new();
        accepted.try_reserve(admissions.len()).map_err(exhausted)?;
        let mut pending_clause_keys = FxHashSet::default();
        pending_clause_keys
            .try_reserve(admissions.len())
            .map_err(exhausted)?;
        let mut pending_link_sources = FxHashMap::default();
        pending_link_sources
            .try_reserve(admissions.len())
            .map_err(exhausted)?;
        #[cfg(test)]
        let mut new_clause_keys = Vec::new();
        #[cfg(test)]
        new_clause_keys
            .try_reserve(admissions.len())
            .map_err(exhausted)?;
        #[cfg(test)]
        let mut new_link_keys = Vec::new();
        #[cfg(test)]
        new_link_keys
            .try_reserve(admissions.len())
            .map_err(exhausted)?;
        #[cfg(test)]
        let mut new_projection_attributions = Vec::new();
        #[cfg(test)]
        new_projection_attributions
            .try_reserve(admissions.len())
            .map_err(exhausted)?;
        #[cfg(test)]
        let mut new_flat_retained_projection_attributions = Vec::new();
        #[cfg(test)]
        new_flat_retained_projection_attributions
            .try_reserve(admissions.len())
            .map_err(exhausted)?;
        #[cfg(test)]
        let mut pending_attributed = FxHashSet::default();
        #[cfg(test)]
        pending_attributed
            .try_reserve(admissions.len())
            .map_err(exhausted)?;
        #[cfg(test)]
        let mut pending_flat_retained = FxHashSet::default();
        #[cfg(test)]
        pending_flat_retained
            .try_reserve(admissions.len())
            .map_err(exhausted)?;
        #[cfg(test)]
        let mut new_claimed_link_audit_entries = Vec::new();
        #[cfg(test)]
        new_claimed_link_audit_entries
            .try_reserve(admissions.len())
            .map_err(exhausted)?;

        for &admission in admissions {
            let clause_key = (lower_record, admission.clause);
            let link_key = (lower_record, admission.support, admission.clause);
            let membership = self.projection_clause_membership(
                lower_record,
                admission.support,
                admission.clause,
            );
            if membership.exact_link_registered {
                assert_eq!(
                    self.registered_projection_incidence_claimed_source(
                        lower_record,
                        admission.support,
                        admission.clause,
                    ),
                    admission.claimed_proof_source,
                    "an exact PCLF incidence duplicate must retain one event-local certificate identity",
                );
                continue;
            }
            if let Some(existing_source) = pending_link_sources.get(&link_key) {
                assert_eq!(
                    *existing_source, admission.claimed_proof_source,
                    "a batch-local raw-link duplicate must retain one certificate identity",
                );
                continue;
            }
            assert!(pending_link_sources
                .insert(link_key, admission.claimed_proof_source)
                .is_none());
            let clause_inserted =
                !membership.clause_registered && pending_clause_keys.insert(clause_key);
            #[cfg(test)]
            if clause_inserted {
                new_clause_keys.push(clause_key);
            }
            #[cfg(test)]
            new_link_keys.push(link_key);
            accepted.push(AcceptedProjectionClauseAdmission {
                admission,
                clause_inserted,
            });
            if matches!(
                admission.support,
                SchemeProjectionProofSupport::Claimed(_)
            ) {
                self.claimed_projection_proof(lower_record, admission)?
                    .expect("claimed admission produces exactly one reconstructible certificate");
                #[cfg(test)]
                {
                    let SchemeProjectionProofSupport::Claimed(root) = admission.support else {
                        unreachable!("claimed admission branch must retain its representative")
                    };
                    let proof_source = admission
                        .claimed_proof_source
                        .expect("claimed admission metadata was constructor-validated");
                    new_claimed_link_audit_entries.push((link_key, proof_source));
                    let attribution = (lower_record, root);
                    if !self.projection_attributions.contains(&attribution)
                        && pending_attributed.insert(attribution)
                    {
                        new_projection_attributions.push(attribution);
                    }
                    if admission.claimed_attribution_source
                        == Some(ClaimedAttributionSource::FlatRetained)
                        && !self
                            .flat_retained_projection_attributions
                            .contains(&attribution)
                        && pending_flat_retained.insert(attribution)
                    {
                        new_flat_retained_projection_attributions.push(attribution);
                    }
                }
            }
        }
        if accepted.is_empty() {
            return Ok(None);
        }

        #[cfg(test)]
        let (canonical_formula, formula_support_keys) = {
            let existing_formula = self
                .projection_formulas
                .get(&lower_record)
                .map(Vec::as_slice)
                .unwrap_or_default();
            let mut canonical_formula = Vec::new();
            canonical_formula
                .try_reserve(existing_formula.len().saturating_add(accepted.len()))
                .map_err(exhausted)?;
            canonical_formula.extend_from_slice(existing_formula);
            for event in &accepted {
                Self::insert_projection_clause_canonical(
                    &mut canonical_formula,
                    Self::projection_clause(event.admission),
                );
            }
            let existing_formula_support_keys =
                self.projection_formula_support_keys.get(&lower_record);
            let mut formula_support_keys = FxHashSet::default();
            formula_support_keys
                .try_reserve(
                    existing_formula_support_keys.map_or(0, FxHashSet::len) + accepted.len(),
                )
                .map_err(exhausted)?;
            formula_support_keys.extend(
                existing_formula_support_keys
                    .into_iter()
                    .flatten()
                    .copied(),
            );
            (canonical_formula, formula_support_keys)
        };

        #[cfg(test)]
        {
            self.projection_clause_keys
                .try_reserve(new_clause_keys.len())
                .map_err(exhausted)?;
            self.independent_projection_clause_link_keys
                .try_reserve(
                    new_link_keys
                        .iter()
                        .filter(|(_, support, _)| {
                            matches!(support, SchemeProjectionProofSupport::Independent(_))
                        })
                        .count(),
                )
                .map_err(exhausted)?;
            self.projection_claimed_link_audit
                .try_reserve(new_claimed_link_audit_entries.len())
                .map_err(exhausted)?;
            self.projection_attributions
                .try_reserve(new_projection_attributions.len())
                .map_err(exhausted)?;
            self.flat_retained_projection_attributions
                .try_reserve(new_flat_retained_projection_attributions.len())
                .map_err(exhausted)?;
            if !self.projection_formulas.contains_key(&lower_record) {
                self.projection_formulas.try_reserve(1).map_err(exhausted)?;
            }
            if !self
                .projection_formula_support_keys
                .contains_key(&lower_record)
            {
                self.projection_formula_support_keys
                    .try_reserve(1)
                    .map_err(exhausted)?;
            }
            if self.take_projection_clause_reservation_failure(
                ProjectionClauseReservationFailurePoint::AfterLegacyPreflight,
            ) {
                return Err(ProofFailure::ResourceExhausted {
                    operation: ProofOperation::UpdateClaimLifecycle,
                });
            }
        }
        let shadow =
            self.try_prepare_projection_formula_shadow_admission(lower_record, &accepted)?;

        Ok(Some(PreparedProjectionClauseAdmission {
            lower_record,
            accepted,
            #[cfg(test)]
            new_clause_keys,
            #[cfg(test)]
            new_link_keys,
            #[cfg(test)]
            canonical_formula,
            #[cfg(test)]
            formula_support_keys,
            #[cfg(test)]
            new_claimed_link_audit_entries,
            #[cfg(test)]
            new_projection_attributions,
            #[cfg(test)]
            new_flat_retained_projection_attributions,
            shadow,
        }))
    }

    pub(super) fn commit_projection_clause_admission(
        &mut self,
        prepared: &mut PreparedProjectionClauseAdmission,
    ) {
        // Finalize the commit-snapshot-dependent summary before the authoritative bucket mutates.
        // All sets touched here reserved `accepted.len()` during prepare, so this refresh is
        // bounded and allocation-free even when a claimed support was promoted meanwhile.
        self.refresh_projection_formula_shadow_match_keys_at_commit(
            prepared.lower_record,
            &prepared.accepted,
            &mut prepared.shadow,
        );
        #[cfg(test)]
        {
            for key in prepared.new_clause_keys.drain(..) {
                assert!(self.projection_clause_keys.insert(key));
            }
            for key @ (_, support, _) in prepared.new_link_keys.drain(..) {
                if matches!(support, SchemeProjectionProofSupport::Independent(_)) {
                    assert!(self.independent_projection_clause_link_keys.insert(key));
                }
            }
            for (key, source) in prepared.new_claimed_link_audit_entries.drain(..) {
                assert!(self
                    .projection_claimed_link_audit
                    .insert(key, source)
                    .is_none());
            }
            for attribution in prepared.new_projection_attributions.drain(..) {
                self.projection_attributions.insert(attribution);
            }
            for attribution in prepared.new_flat_retained_projection_attributions.drain(..) {
                self.flat_retained_projection_attributions
                    .insert(attribution);
            }
            for event in &prepared.accepted {
                if let Some(key) = self.projection_support_match_key(event.admission.support) {
                    prepared.formula_support_keys.insert(key);
                }
            }
            let canonical_formula = std::mem::take(&mut prepared.canonical_formula);
            let formula_support_keys = std::mem::take(&mut prepared.formula_support_keys);
            self.projection_formulas
                .insert(prepared.lower_record, canonical_formula);
            self.projection_formula_support_keys
                .insert(prepared.lower_record, formula_support_keys);
        }
        let mut new_bucket = prepared.shadow.new_record_bucket.take();
        let bucket = match new_bucket.as_mut() {
            Some(bucket) => bucket,
            None => self
                .projection_formula_shadow
                .by_record
                .get_mut(&prepared.lower_record)
                .expect("prepared PCLF shadow delta must retain its target bucket"),
        };
        Self::commit_projection_formula_shadow_delta(
            bucket,
            &mut prepared.shadow.delta,
            &mut self.projection_formula_shadow.movement,
        );
        if let Some(bucket) = new_bucket {
            assert!(
                self.projection_formula_shadow
                    .by_record
                    .insert(prepared.lower_record, bucket)
                    .is_none()
            );
        }
        #[cfg(test)]
        self.debug_assert_pclf_a_read_model_matches_legacy();
    }

    pub(super) fn record_projection_clause(
        &mut self,
        lower_record: BoundRecordId,
        admission: RecordProofClauseLinkAdmission,
    ) {
        if let Some(mut prepared) = self
            .try_prepare_projection_clause_admission(lower_record, &[admission])
            .expect("infallible projection-clause admission")
        {
            self.commit_projection_clause_admission(&mut prepared);
        }
    }

    fn projection_clause(admission: RecordProofClauseLinkAdmission) -> ProjectionClause {
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
        match admission.clause {
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
        }
    }

    #[cfg(test)]
    fn insert_projection_clause_canonical(
        formula: &mut Vec<ProjectionClause>,
        clause: ProjectionClause,
    ) {
        // Exact-key uniqueness is established before this writer runs. CPK owns the formula's
        // typed canonical order, including the total order within each formula category.
        if formula
            .last()
            .is_none_or(|last| last.canonical_cmp(clause) != std::cmp::Ordering::Greater)
        {
            formula.push(clause);
        } else {
            let position = formula.partition_point(|existing| {
                existing.canonical_cmp(clause) != std::cmp::Ordering::Greater
            });
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
        let (lower_endpoint, upper_endpoint) =
            self.validate_replay_route_target(view, lower, upper)?;
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
        let prepared = self.compose_prepared_replay_route(
            view,
            lower,
            upper,
            lower_endpoint,
            upper_endpoint,
            lower_block,
            upper_ids,
            &upper_entries,
            incremental_routes,
        )?;
        self.validate_prepared_replay_route(lower, upper, &prepared)?;
        Ok(prepared)
    }

    pub(crate) fn prepare_replay_routes_for_lower<'a>(
        &self,
        view: &impl SemanticFactView,
        lower: BoundRecordId,
        requests: impl IntoIterator<Item = (BoundRecordId, &'a [IncrementalRouteKey])>,
    ) -> Result<Vec<PreparedReplayRoute>, ProofFailure> {
        let requests = requests.into_iter();
        let mut prepared_routes = Vec::new();
        prepared_routes
            .try_reserve(requests.size_hint().0)
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::PrepareReplayRouteBatch,
            })?;
        let mut shared_lower_block: Option<PreparedReplayParentBlock> = None;
        for (upper, incremental_routes) in requests {
            let (lower_endpoint, upper_endpoint) =
                self.validate_replay_route_target(view, lower, upper)?;
            let lower_block = match &shared_lower_block {
                Some(block) => block.clone(),
                None => {
                    let lower_ids = self
                        .claimed_parents_by_lower_record
                        .get(&lower)
                        .map(Vec::as_slice)
                        .unwrap_or(&[]);
                    let block = self.prepare_replay_parent_block(
                        lower,
                        upper,
                        ReplayClaimParentSide::Lower,
                        lower_ids,
                        None,
                    )?;
                    shared_lower_block = Some(block.clone());
                    block
                }
            };
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
            let prepared = self.compose_prepared_replay_route(
                view,
                lower,
                upper,
                lower_endpoint,
                upper_endpoint,
                lower_block,
                upper_ids,
                &upper_entries,
                incremental_routes,
            )?;
            self.validate_prepared_replay_route_payload(lower, upper, &prepared)?;
            prepared_routes.push(prepared);
        }
        Ok(prepared_routes)
    }

    pub(crate) fn prepare_replay_routes_for_upper(
        &self,
        view: &impl SemanticFactView,
        lowers: impl IntoIterator<Item = BoundRecordId>,
        upper: BoundRecordId,
    ) -> Result<Vec<PreparedReplayRoute>, ProofFailure> {
        let lowers = lowers.into_iter();
        let mut prepared_routes = Vec::new();
        prepared_routes
            .try_reserve(lowers.size_hint().0)
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::PrepareReplayRouteBatch,
            })?;
        let upper_ids = self
            .claims_by_upper_record
            .get(&upper)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let mut shared_upper_entries = None;
        let mut shared_upper_variants: [
            Option<(ReplayRouting, Option<PreparedReplayParentBlock>)>;
            2
        ] = [None, None];
        for lower in lowers {
            let (lower_endpoint, upper_endpoint) =
                self.validate_replay_route_target(view, lower, upper)?;
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
            let upper_entries = match &shared_upper_entries {
                Some(entries) => entries,
                None => {
                    let entries = self.prepare_replay_parent_entries(
                        lower,
                        upper,
                        ReplayClaimParentSide::Upper,
                        upper_ids,
                        Some(upper),
                    )?;
                    shared_upper_entries = Some(entries);
                    shared_upper_entries
                        .as_ref()
                        .expect("the shared upper replay entries were just prepared")
                }
            };
            let variant_index = usize::from(view.is_var_pos(lower_endpoint));
            let prepared = match &shared_upper_variants[variant_index] {
                Some((routing, upper_block)) => PreparedReplayRoute {
                    routing: *routing,
                    proof_event: PreparedReplayParents {
                        pair_replay: upper_block.clone().map(|upper| PreparedReplayParentSet {
                            lower: lower_block,
                            upper,
                        }),
                        incremental_replays: Vec::new(),
                    },
                },
                None => {
                    let prepared = self.compose_prepared_replay_route(
                        view,
                        lower,
                        upper,
                        lower_endpoint,
                        upper_endpoint,
                        lower_block,
                        upper_ids,
                        upper_entries,
                        &[],
                    )?;
                    let upper_block = prepared
                        .proof_event
                        .pair_replay
                        .as_ref()
                        .map(|parents| parents.upper.clone());
                    shared_upper_variants[variant_index] =
                        Some((prepared.routing, upper_block));
                    prepared
                }
            };
            self.validate_prepared_replay_route_payload(lower, upper, &prepared)?;
            prepared_routes.push(prepared);
        }
        Ok(prepared_routes)
    }

    fn validate_replay_route_target(
        &self,
        view: &impl SemanticFactView,
        lower: BoundRecordId,
        upper: BoundRecordId,
    ) -> Result<(PosId, NegId), ProofFailure> {
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
        Ok((lower_endpoint, upper_endpoint))
    }

    #[allow(clippy::too_many_arguments)]
    fn compose_prepared_replay_route(
        &self,
        view: &impl SemanticFactView,
        lower: BoundRecordId,
        upper: BoundRecordId,
        lower_endpoint: PosId,
        upper_endpoint: NegId,
        lower_block: PreparedReplayParentBlock,
        upper_ids: &[UpperReplayClaimId],
        upper_entries: &[PreparedReplayParent],
        incremental_routes: &[IncrementalRouteKey],
    ) -> Result<PreparedReplayRoute, ProofFailure> {
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
        for parent in upper_entries {
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

    fn validate_prepared_replay_route_payload(
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

    #[cfg(test)]
    pub(super) fn projection_formula_for_test(
        &self,
        record: BoundRecordId,
    ) -> Option<&[ProjectionClause]> {
        self.projection_formulas.get(&record).map(Vec::as_slice)
    }

    /// GWCB-0 read-side observation only. This deliberately reconstructs the bridge with
    /// linear scans so the red topology fixture can name the exact facts that later slices must
    /// carry transactionally. Production must never call this helper or adopt its scan shape.
    #[cfg(test)]
    pub(super) fn gwcb0_claimed_replay_bridges_for_test(
        &self,
    ) -> Vec<Gwcb0ClaimedReplayBridge> {
        let mut bridges = Vec::new();
        for (bound, clauses) in &self.projection_formulas {
            for clause in clauses {
                let ProjectionClause::ReplayConjunction {
                    support: SchemeProjectionProofSupport::Claimed(representative_claim),
                    carrier,
                    lower,
                    upper,
                    attribution: Some(ProjectionLineage::ReplayConstraint),
                } = *clause
                else {
                    continue;
                };
                let Some(coverage_root) = self.claim_coverage_root(representative_claim) else {
                    continue;
                };
                let Some(original) = self.upper_claims.iter().find(|claim| {
                    claim.coverage_root == coverage_root
                        && claim.lineage == ProjectionLineage::Original
                        && claim.current_record == upper
                }) else {
                    continue;
                };
                for replay in self
                    .replay_finite_map
                    .iter()
                    .filter(|replay| replay.carrier == carrier)
                {
                    bridges.push(Gwcb0ClaimedReplayBridge {
                        bound: *bound,
                        coverage_root,
                        representative_claim,
                        result: replay.result,
                        carrier,
                        lower,
                        upper,
                        producer: original.producer,
                    });
                }
            }
        }
        bridges.sort_unstable_by_key(|bridge| {
            (
                bridge.bound.0,
                bridge.result.0,
                bridge.carrier.pivot.0,
                bridge.lower.0,
                bridge.upper.0,
                bridge.producer.0,
            )
        });
        bridges.dedup();
        bridges
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

    fn project_lower_inner<'a>(
        &'a self,
        view: &'a impl SemanticFactView,
        record: BoundRecordId,
        round: &mut ProjectionEvaluationRound<'a>,
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
        let formula_bucket = self.projection_formula_shadow.by_record.get(&record);
        let has_supports = supports.is_some_and(|supports| !supports.is_empty());
        let has_formula = formula_bucket.is_some_and(|bucket| !bucket.exact_links.is_empty());
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

        let preflight = round
            .preflight
            .get_or_insert_with(|| ProjectionPreflight::new(self, view, record));
        preflight.retarget(record);
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
                    let live_states = self
                        .live_states_by_coverage_root
                        .get(&resolved.coverage_root);
                    #[cfg(test)]
                    debug_assert_eq!(
                        live_states.is_some_and(|states| !states.is_empty()),
                        self.live_coverage
                            .iter()
                            .any(|(root, _)| *root == resolved.coverage_root)
                    );
                    if live_states.is_none_or(FxHashSet::is_empty) {
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
        let evaluation = evaluator.eval_preflighted_record_with_evidence(record)?;
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

        Ok(match evaluation {
            CpkProjectionEvaluation::Excluded => ProjectionDecision::Excluded,
            CpkProjectionEvaluation::Included { evidence } => ProjectionDecision::Included {
                supports: payload,
                evidence,
            },
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

    fn retarget(&mut self, target_record: BoundRecordId) {
        // Successful checks are target-independent. Only failure attribution changes between the
        // top-level records in one immutable query, after the prior traversal has fully unwound.
        debug_assert!(self.visiting_records.is_empty());
        debug_assert!(self.visiting_constraints.is_empty());
        self.target_record = target_record;
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
                    .claims_by_upper_record
                    .get(&record)
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                for claim in claims.iter().copied() {
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
        let formula_bucket = self.store.projection_formula_shadow.by_record.get(&record);
        let has_supports = supports.is_some_and(|supports| !supports.is_empty());
        let has_clauses = formula_bucket.is_some_and(|bucket| !bucket.exact_links.is_empty());
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
        let formula_bucket =
            formula_bucket.expect("non-empty clauses were classified above");
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

        let mut previous_clause = None;
        let mut order_cursor = formula_bucket.canonical_run_cursor();
        while let Some((support_id, entry_id)) = order_cursor.next() {
            let clause = formula_bucket.reconstructed_clause(support_id, entry_id);
            if previous_clause.is_some_and(|previous: ProjectionClause| {
                previous.canonical_cmp(clause) == std::cmp::Ordering::Greater
            }) {
                return Err(ProofFailure::NonCanonicalProjectionOrder { record });
            }
            previous_clause = Some(clause);
        }

        let mut matched = Vec::new();
        matched
            .try_reserve_exact(resolved.len())
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::ProjectLowerPreflight,
            })?;
        matched.resize(resolved.len(), false);
        let mut cursor = formula_bucket.canonical_run_cursor();
        while let Some((support_id, entry_id)) = cursor.next() {
            let clause = formula_bucket.reconstructed_clause(support_id, entry_id);
            let clause_support = self.resolve_support(record, clause.support())?;
            let Ok(index) = resolved
                .binary_search_by(|support| support.cmp(clause_support))
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
        let live_states = self.store.live_states_by_coverage_root.get(&root);
        #[cfg(test)]
        {
            let expected = self
                .store
                .live_coverage
                .iter()
                .filter_map(|(candidate, state)| (*candidate == root).then_some(*state))
                .collect::<FxHashSet<_>>();
            debug_assert_eq!(live_states.cloned().unwrap_or_default(), expected);
        }
        for state in live_states.into_iter().flatten() {
            assert!(
                self.store.live_coverage.contains(&(root, *state)),
                "the live coverage root index must reference a recorded live state"
            );
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
                .replay_indices_by_result
                .get(&constraint)
                .map(Vec::as_slice)
                .unwrap_or(&[])
                .iter()
                .map(|index| {
                    let occurrence = self
                        .store
                        .replay_finite_map
                        .get(*index)
                        .expect("a replay result bucket must reference a recorded replay");
                    assert_eq!(
                        occurrence.result, constraint,
                        "a replay result bucket must reference its own result"
                    );
                    occurrence.carrier
                })
                .collect::<Vec<_>>();
            for replay in replays {
                self.validate_record(replay.lower, owner)?;
                self.validate_record(replay.upper, owner)?;
            }
            let sources = self
                .store
                .dependency_occurrence_indices_by_result
                .get(&constraint)
                .map(Vec::as_slice)
                .unwrap_or(&[])
                .iter()
                .map(|index| {
                    let occurrence = self
                        .store
                        .occurrences
                        .get(*index)
                        .expect("a dependency result bucket must reference a proof occurrence");
                    assert_eq!(
                        occurrence.result,
                        ProofResult::Semantic(SemanticFactRef::Constraint(constraint)),
                        "a dependency result bucket must reference its own result"
                    );
                    match &occurrence.cause {
                        ProofCause::Structural(derivation) => Ok(derivation.parent),
                        ProofCause::ReductionRoute { parent_claim, .. } => Err(*parent_claim),
                        _ => panic!(
                            "a dependency result bucket must reference a structural or reduction-route occurrence"
                        ),
                    }
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
            let root = self.store.root_claim_for_producer(constraint);
            #[cfg(test)]
            {
                let expected = self
                    .store
                    .upper_claims
                    .iter()
                    .filter(|claim| {
                        claim.producer == constraint
                            && claim.lineage == ProjectionLineage::Original
                    })
                    .map(|claim| claim.claim)
                    .collect::<Vec<_>>();
                debug_assert_eq!(root.into_iter().collect::<Vec<_>>(), expected);
            }
            if let Some(root) = root {
                let root_claim = self
                    .store
                    .upper_claim(root)
                    .ok_or_else(|| self.dangling(owner, ProofFactRef::UpperClaim(root)))?;
                assert_eq!(
                    (root_claim.producer, root_claim.lineage),
                    (constraint, ProjectionLineage::Original),
                    "the original claim producer index must reference its own original root"
                );
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
                if self
                    .store
                    .projection_carrier_occurrence(ProjectionProofCarrier::ConstraintOrigin {
                        constraint,
                        origin,
                    })
                    .is_none()
                {
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
                if self
                    .store
                    .projection_carrier_occurrence(
                        ProjectionProofCarrier::StructuralConstraint { result, derivation },
                    )
                    .is_none()
                {
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
                let replay = self
                    .store
                    .replay_finite_map_index
                    .get(&(result, derivation))
                    .and_then(|index| self.store.replay_finite_map.get(*index));
                #[cfg(test)]
                debug_assert_eq!(
                    replay.is_some(),
                    self.store.replay_finite_map.iter().any(|occurrence| {
                        occurrence.result == result && occurrence.carrier == derivation
                    })
                );
                if let Some(replay) = replay {
                    assert_eq!(
                        (replay.result, replay.carrier),
                        (result, derivation),
                        "the replay finite-map index must reference its own key"
                    );
                } else {
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
                if self
                    .store
                    .projection_carrier_occurrence(ProjectionProofCarrier::RowConstraint {
                        result,
                        derivation,
                    })
                    .is_none()
                {
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
                if self
                    .store
                    .projection_carrier_occurrence(
                        ProjectionProofCarrier::SchemeInstantiationConstraint {
                            result,
                            source_witness,
                        },
                    )
                    .is_none()
                {
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
                if self
                    .store
                    .projection_carrier_occurrence(ProjectionProofCarrier::ReplayEvidence(
                        derivation,
                    ))
                    .is_none()
                {
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
        self.store
            .projection_carrier_occurrence(ProjectionProofCarrier::Origin(origin))
            .is_some()
    }

    fn has_row_derivation(&self, derivation: RowDerivationId) -> bool {
        self.store.row_derivation_occurrence(derivation).is_some()
    }

    fn has_generalized_witness(&self, witness: GeneralizedSchemeWitnessId) -> bool {
        self.store
            .projection_carrier_occurrence(ProjectionProofCarrier::SchemeInstantiation(witness))
            .is_some()
    }

    fn dangling(&self, owner: ProofFactRef, target: ProofFactRef) -> ProofFailure {
        ProofFailure::DanglingProofReference { owner, target }
    }
}

impl ProofOccurrenceStore {
    pub(super) fn upper_claim(&self, claim: UpperReplayClaimId) -> Option<&UpperClaimOccurrence> {
        let index = self.upper_claim_index.get(&claim).copied()?;
        self.upper_claims.get(index)
    }

    #[cfg(test)]
    pub(super) fn upper_claims_for_test(&self) -> &[UpperClaimOccurrence] {
        &self.upper_claims
    }

    #[cfg(test)]
    pub(super) fn claims_for_upper_record_for_test(
        &self,
        record: BoundRecordId,
    ) -> &[UpperReplayClaimId] {
        self.claims_by_upper_record
            .get(&record)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    #[cfg(test)]
    pub(super) fn upper_claim_record_entries_for_test(
        &self,
    ) -> impl Iterator<Item = (BoundRecordId, &[UpperReplayClaimId])> {
        self.claims_by_upper_record
            .iter()
            .map(|(record, claims)| (*record, claims.as_slice()))
    }

    #[cfg(test)]
    pub(super) fn live_coverage_states_for_test(
        &self,
        root: UpperReplayClaimId,
    ) -> Option<&FxHashSet<UnweightedRowReductionRecordId>> {
        self.live_states_by_coverage_root.get(&root)
    }

    #[cfg(test)]
    pub(super) fn replay_claim_cycle_coalesces_for_test(&self) -> usize {
        self.replay_claim_cycle_coalesces
    }

    #[cfg(test)]
    pub(super) fn prepared_upper_replay_parents_for_test(
        &self,
        upper: BoundRecordId,
        lower_is_var: bool,
    ) -> Result<Vec<PreparedReplayParent>, ProofFailure> {
        let claims = self
            .claims_by_upper_record
            .get(&upper)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let entries = self.prepare_replay_parent_entries(
            upper,
            upper,
            ReplayClaimParentSide::Upper,
            claims,
            Some(upper),
        )?;
        Ok(entries
            .into_iter()
            .filter(|parent| {
                lower_is_var
                    || self
                        .live_states_by_coverage_root
                        .get(&parent.coverage_root)
                        .is_none_or(FxHashSet::is_empty)
            })
            .collect())
    }
}

pub(super) struct CpkProjectionEvaluator<'a> {
    view: &'a dyn SemanticFactView,
    store: &'a ProofOccurrenceStore,
    states: FxHashMap<ProofEvalNode, ProofEvalState>,
    record_overrides: FxHashMap<BoundRecordId, bool>,
    root_overrides: FxHashMap<UpperReplayClaimId, bool>,
    cycle_cuts: usize,
    preflight_validated_walk: bool,
    #[cfg(test)]
    decisive_certificate_lookups: usize,
    #[cfg(test)]
    decisive_evidence_markers: usize,
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
            preflight_validated_walk: false,
            #[cfg(test)]
            decisive_certificate_lookups: 0,
            #[cfg(test)]
            decisive_evidence_markers: 0,
        }
    }

    pub(super) fn eval_record(&mut self, record: BoundRecordId) -> bool {
        self.eval_record_memo(record).summary.is_included()
    }

    pub(crate) fn eval_record_with_evidence(
        &mut self,
        record: BoundRecordId,
    ) -> Result<CpkProjectionEvaluation, ProofFailure> {
        self.eval_record_with_evidence_mode(record, false)
    }

    fn eval_preflighted_record_with_evidence(
        &mut self,
        record: BoundRecordId,
    ) -> Result<CpkProjectionEvaluation, ProofFailure> {
        self.eval_record_with_evidence_mode(record, true)
    }

    fn eval_record_with_evidence_mode(
        &mut self,
        record: BoundRecordId,
        preflight_validated_walk: bool,
    ) -> Result<CpkProjectionEvaluation, ProofFailure> {
        if let Some(result) = self.record_overrides.get(&record) {
            return Ok(if *result {
                CpkProjectionEvaluation::Included {
                    evidence: ProjectionEvidence::ExactWithoutClaimedArm,
                }
            } else {
                CpkProjectionEvaluation::Excluded
            });
        }

        let previous_preflight_mode =
            std::mem::replace(&mut self.preflight_validated_walk, preflight_validated_walk);
        let memo = self.eval_record_memo(record);
        self.preflight_validated_walk = previous_preflight_mode;

        Ok(match memo.summary {
            CpkProjectionEvaluationSummary::Excluded => CpkProjectionEvaluation::Excluded,
            CpkProjectionEvaluationSummary::IncludedExact
            | CpkProjectionEvaluationSummary::IncludedFailOpen => {
                let evidence = self.resolve_record_evidence(record, memo)?;
                CpkProjectionEvaluation::Included { evidence }
            }
        })
    }

    fn eval_record_memo(&mut self, record: BoundRecordId) -> ProofEvalMemo {
        if let Some(result) = self.record_overrides.get(&record) {
            return if *result {
                ProofEvalMemo {
                    summary: CpkProjectionEvaluationSummary::IncludedExact,
                    evidence: ProofEvalEvidenceMemo::exact_without_claimed_arm(),
                }
            } else {
                ProofEvalMemo {
                    summary: CpkProjectionEvaluationSummary::Excluded,
                    evidence: ProofEvalEvidenceMemo::none(),
                }
            };
        }
        let node = ProofEvalNode::Record(record);
        if let Some(memo) = self.enter(node) {
            return memo;
        }
        let mut decisive_claimed_incidence = None;
        let summary = self.eval_record_uncached(
            record,
            self.preflight_validated_walk,
            Some(&mut decisive_claimed_incidence),
        );
        let evidence = match (summary, decisive_claimed_incidence) {
            (CpkProjectionEvaluationSummary::Excluded, _) => ProofEvalEvidenceMemo::none(),
            (CpkProjectionEvaluationSummary::IncludedFailOpen, _) => {
                ProofEvalEvidenceMemo::fail_open_incomplete()
            }
            (CpkProjectionEvaluationSummary::IncludedExact, Some((support_id, entry_id))) => {
                #[cfg(test)]
                {
                    self.decisive_evidence_markers += 1;
                }
                ProofEvalEvidenceMemo::decisive_claimed_incidence(support_id, entry_id)
            }
            (CpkProjectionEvaluationSummary::IncludedExact, _) => {
                ProofEvalEvidenceMemo::exact_without_claimed_arm()
            }
        };
        self.finish(node, ProofEvalMemo { summary, evidence })
    }

    fn eval_record_summary(&mut self, record: BoundRecordId) -> CpkProjectionEvaluationSummary {
        self.eval_record_memo(record).summary
    }

    fn resolve_record_evidence(
        &mut self,
        record: BoundRecordId,
        memo: ProofEvalMemo,
    ) -> Result<ProjectionEvidence, ProofFailure> {
        Ok(match memo.evidence.decode() {
            DecodedProofEvalEvidenceMemo::DecisiveClaimedIncidence {
                support_id,
                entry_id,
            } => {
                #[cfg(test)]
                {
                    self.decisive_certificate_lookups += 1;
                }
                self.store
                    .decisive_claimed_projection_proof_from_incidence(
                        record,
                        support_id,
                        entry_id,
                    )?
                    .map(ProjectionEvidence::DecisiveClaimedArm)
                    .unwrap_or(ProjectionEvidence::FailOpenIncomplete)
            }
            DecodedProofEvalEvidenceMemo::ExactWithoutClaimedArm => {
                ProjectionEvidence::ExactWithoutClaimedArm
            }
            DecodedProofEvalEvidenceMemo::FailOpenIncomplete => {
                ProjectionEvidence::FailOpenIncomplete
            }
            DecodedProofEvalEvidenceMemo::None => {
                debug_assert!(false, "included record memo must carry evidence");
                ProjectionEvidence::FailOpenIncomplete
            }
        })
    }

    pub(super) fn with_record_result_override(
        mut self,
        record: BoundRecordId,
        result: bool,
    ) -> Self {
        self.record_overrides.insert(record, result);
        self
    }

    pub(super) fn with_root_result_override(
        mut self,
        root: UpperReplayClaimId,
        result: bool,
    ) -> Self {
        self.root_overrides.insert(root, result);
        self
    }

    fn eval_record_uncached(
        &mut self,
        record: BoundRecordId,
        prefer_exact_arm: bool,
        mut decisive_claimed_incidence: Option<
            &mut Option<(ProjectionSupportGroupId, ProjectionFormulaEntryId)>,
        >,
    ) -> CpkProjectionEvaluationSummary {
        let Some(bound) = self.view.bound(record) else {
            debug_assert!(
                false,
                "CPK projection evaluator reached missing machine-issued bound {record:?}"
            );
            return CpkProjectionEvaluationSummary::IncludedFailOpen;
        };
        if bound.state() == BoundRecordState::Tombstone {
            return CpkProjectionEvaluationSummary::IncludedExact;
        }
        if bound.direction() == BoundDirection::Upper {
            let claims = self
                .store
                .claims_by_upper_record
                .get(&record)
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            if claims.is_empty() {
                return CpkProjectionEvaluationSummary::IncludedExact;
            }
            for claim in claims.iter().copied() {
                let result = self.eval_root_coverage(claim);
                if result.is_included() {
                    return result;
                }
            }
            return CpkProjectionEvaluationSummary::Excluded;
        }

        let formula_bucket = self.store.projection_formula_shadow.by_record.get(&record);
        let Some(supports) = self.store.projection_supports.get(&record) else {
            return if self.preflight_validated_walk
                && formula_bucket.is_none_or(|bucket| bucket.exact_links.is_empty())
            {
                CpkProjectionEvaluationSummary::IncludedExact
            } else {
                CpkProjectionEvaluationSummary::IncludedFailOpen
            };
        };
        if supports.is_empty() {
            return if self.preflight_validated_walk
                && formula_bucket.is_none_or(|bucket| bucket.exact_links.is_empty())
            {
                CpkProjectionEvaluationSummary::IncludedExact
            } else {
                CpkProjectionEvaluationSummary::IncludedFailOpen
            };
        }
        let normalized_support_keys = formula_bucket.map(|bucket| &bucket.normalized_support_keys);
        for support in supports.iter().copied() {
            if self.support_evaluation(support).is_included()
                && !self
                    .store
                    .projection_support_match_key(support)
                    .is_some_and(|key| {
                        normalized_support_keys.is_some_and(|keys| keys.contains(&key))
                    })
            {
                return CpkProjectionEvaluationSummary::IncludedFailOpen;
            }
        }
        let Some(formula_bucket) = formula_bucket else {
            return CpkProjectionEvaluationSummary::Excluded;
        };
        let mut incomplete_arm_exists = false;
        let mut cursor = formula_bucket.canonical_run_cursor();
        while let Some((support_id, entry_id)) = cursor.next() {
            let item = formula_bucket.evaluation_item(support_id, entry_id);
            let result = self.eval_formula_item(item);
            match result {
                CpkProjectionEvaluationSummary::IncludedExact => {
                    if matches!(item.raw_support, SchemeProjectionProofSupport::Claimed(_)) {
                        if let Some(found) = decisive_claimed_incidence.as_deref_mut() {
                            let legacy_entry_id = formula_bucket
                                .legacy_decisive_entry_id(item.support_id, item.entry_id)
                                .unwrap_or(item.entry_id);
                            *found = Some((item.support_id, legacy_entry_id));
                        }
                    }
                    return result;
                }
                CpkProjectionEvaluationSummary::IncludedFailOpen if !prefer_exact_arm => {
                    return result;
                }
                CpkProjectionEvaluationSummary::IncludedFailOpen => incomplete_arm_exists = true,
                CpkProjectionEvaluationSummary::Excluded => {}
            }
        }
        if incomplete_arm_exists {
            CpkProjectionEvaluationSummary::IncludedFailOpen
        } else {
            CpkProjectionEvaluationSummary::Excluded
        }
    }

    fn eval_formula_item(
        &mut self,
        item: ProjectionEvaluationItem,
    ) -> CpkProjectionEvaluationSummary {
        match item.clause {
            RecordProofClause::Standalone { .. } => self.support_evaluation(item.raw_support),
            RecordProofClause::DerivedUnary { premise, .. } => self.eval_premise(premise),
            RecordProofClause::ReplayConjunction {
                lower_premise,
                upper_premise,
                ..
            } => {
                let lower = self.eval_record_summary(lower_premise);
                if lower == CpkProjectionEvaluationSummary::Excluded {
                    return CpkProjectionEvaluationSummary::Excluded;
                }
                let upper = self.eval_record_summary(upper_premise);
                if upper == CpkProjectionEvaluationSummary::Excluded {
                    return CpkProjectionEvaluationSummary::Excluded;
                }
                if lower == CpkProjectionEvaluationSummary::IncludedFailOpen
                    || upper == CpkProjectionEvaluationSummary::IncludedFailOpen
                {
                    CpkProjectionEvaluationSummary::IncludedFailOpen
                } else {
                    CpkProjectionEvaluationSummary::IncludedExact
                }
            }
        }
    }

    #[cfg(test)]
    fn eval_clause(&mut self, clause: ProjectionClause) -> CpkProjectionEvaluationSummary {
        match clause {
            ProjectionClause::Standalone { support, .. } => {
                self.support_evaluation(support)
            }
            ProjectionClause::DerivedUnary { premise, .. } => self.eval_premise(premise),
            ProjectionClause::ReplayConjunction { lower, upper, .. } => {
                let lower = self.eval_record_summary(lower);
                if lower == CpkProjectionEvaluationSummary::Excluded {
                    return CpkProjectionEvaluationSummary::Excluded;
                }
                let upper = self.eval_record_summary(upper);
                if upper == CpkProjectionEvaluationSummary::Excluded {
                    return CpkProjectionEvaluationSummary::Excluded;
                }
                if lower == CpkProjectionEvaluationSummary::IncludedFailOpen
                    || upper == CpkProjectionEvaluationSummary::IncludedFailOpen
                {
                    CpkProjectionEvaluationSummary::IncludedFailOpen
                } else {
                    CpkProjectionEvaluationSummary::IncludedExact
                }
            }
        }
    }

    fn eval_premise(&mut self, premise: ProofPremise) -> CpkProjectionEvaluationSummary {
        match premise {
            ProofPremise::Record(record) => self.eval_record_summary(record),
            ProofPremise::Constraint(constraint) => self.eval_constraint(constraint),
            ProofPremise::RootCoverage(root) => self.eval_root_coverage(root),
        }
    }

    fn eval_constraint(
        &mut self,
        constraint: ConstraintRecordId,
    ) -> CpkProjectionEvaluationSummary {
        let node = ProofEvalNode::Constraint(constraint);
        if let Some(memo) = self.enter(node) {
            return memo.summary;
        }
        let result = self.eval_constraint_uncached(constraint);
        self.finish(node, ProofEvalMemo::summary_only(result)).summary
    }

    fn eval_constraint_uncached(
        &mut self,
        constraint: ConstraintRecordId,
    ) -> CpkProjectionEvaluationSummary {
        if self.view.constraint(constraint).is_none() {
            debug_assert!(
                false,
                "CPK projection evaluator reached missing machine-issued constraint {constraint:?}"
            );
            return CpkProjectionEvaluationSummary::IncludedFailOpen;
        }
        let mut has_source = false;
        if let Some(lower_record) = self.view.lower_record_for_constraint(constraint) {
            has_source = true;
            let result = self.eval_record_summary(lower_record);
            if result.is_included() {
                return result;
            }
        }
        let qualified_parents = self
            .store
            .qualified_parents_for_result(constraint)
            .iter()
            .map(|entry| entry.parent)
            .collect::<Vec<_>>();
        for parent in qualified_parents {
            has_source = true;
            let projectable = match parent {
                ClaimQualifiedParent::ReplayConstraint { replay, .. } => {
                    let lower = self.eval_record_summary(replay.lower);
                    if lower == CpkProjectionEvaluationSummary::Excluded {
                        CpkProjectionEvaluationSummary::Excluded
                    } else {
                        let upper = self.eval_record_summary(replay.upper);
                        if upper == CpkProjectionEvaluationSummary::Excluded {
                            CpkProjectionEvaluationSummary::Excluded
                        } else if lower == CpkProjectionEvaluationSummary::IncludedFailOpen
                            || upper == CpkProjectionEvaluationSummary::IncludedFailOpen
                        {
                            CpkProjectionEvaluationSummary::IncludedFailOpen
                        } else {
                            CpkProjectionEvaluationSummary::IncludedExact
                        }
                    }
                }
                ClaimQualifiedParent::StructuralConstraint { derivation, .. } => {
                    self.eval_constraint(derivation.parent)
                }
                ClaimQualifiedParent::ReductionRouteConstraint { parent_claim, .. } => {
                    self.eval_root_coverage(parent_claim)
                }
            };
            if projectable.is_included() {
                return projectable;
            }
        }
        if let Some(root) = self.store.root_claim_for_producer(constraint) {
            has_source = true;
            let result = self.eval_root_coverage(root);
            if result.is_included() {
                return result;
            }
        }
        if has_source {
            CpkProjectionEvaluationSummary::Excluded
        } else {
            CpkProjectionEvaluationSummary::IncludedExact
        }
    }

    fn eval_root_coverage(
        &self,
        claim: UpperReplayClaimId,
    ) -> CpkProjectionEvaluationSummary {
        let Some(root) = self.store.claim_coverage_root(claim) else {
            debug_assert!(
                false,
                "CPK projection evaluator reached missing machine-issued claim/root {claim:?}"
            );
            return CpkProjectionEvaluationSummary::IncludedFailOpen;
        };
        if let Some(result) = self.root_overrides.get(&root) {
            return if *result {
                CpkProjectionEvaluationSummary::IncludedExact
            } else {
                CpkProjectionEvaluationSummary::Excluded
            };
        }
        if self
            .store
            .live_states_by_coverage_root
            .get(&root)
            .is_none_or(FxHashSet::is_empty)
        {
            CpkProjectionEvaluationSummary::IncludedExact
        } else {
            CpkProjectionEvaluationSummary::Excluded
        }
    }

    fn support_evaluation(
        &self,
        support: SchemeProjectionProofSupport,
    ) -> CpkProjectionEvaluationSummary {
        match support {
            SchemeProjectionProofSupport::Independent(_) => {
                CpkProjectionEvaluationSummary::IncludedExact
            }
            SchemeProjectionProofSupport::Claimed(claim) => self.eval_root_coverage(claim),
        }
    }

    fn enter(&mut self, node: ProofEvalNode) -> Option<ProofEvalMemo> {
        match self.states.get(&node).copied() {
            Some(ProofEvalState::Done(memo)) => Some(memo),
            Some(ProofEvalState::Visiting) => {
                self.cycle_cuts += 1;
                Some(ProofEvalMemo::summary_only(
                    CpkProjectionEvaluationSummary::Excluded,
                ))
            }
            None => {
                self.states.insert(node, ProofEvalState::Visiting);
                None
            }
        }
    }

    fn finish(
        &mut self,
        node: ProofEvalNode,
        memo: ProofEvalMemo,
    ) -> ProofEvalMemo {
        self.states.insert(node, ProofEvalState::Done(memo));
        memo
    }

    pub(super) fn cycle_cuts(&self) -> usize {
        self.cycle_cuts
    }

    #[cfg(test)]
    fn decisive_certificate_lookups(&self) -> usize {
        self.decisive_certificate_lookups
    }

    #[cfg(test)]
    fn decisive_evidence_markers(&self) -> usize {
        self.decisive_evidence_markers
    }

    pub(super) fn has_visiting_state(&self) -> bool {
        self.states
            .values()
            .any(|state| *state == ProofEvalState::Visiting)
    }
}

impl ProofOccurrenceStore {
    pub(crate) fn replay_parents_for_occurrence_side<'a>(
        &'a self,
        occurrence: &ReplayProofOccurrence,
        side: ReplayClaimParentSide,
    ) -> impl ExactSizeIterator<Item = ReplayProofParent> + 'a {
        let side_index = match side {
            ReplayClaimParentSide::Lower => occurrence.replay_parent_sides[0],
            ReplayClaimParentSide::Upper => occurrence.replay_parent_sides[1],
        };
        ReplayParentSideCursor::new(&self.replay_parent_chunks, side_index, side)
    }

    fn exact_replay_qualified_parent_is_registered(
        &self,
        result: ConstraintRecordId,
        carrier: BinaryReplayDerivation,
        side: ReplayClaimParentSide,
        root: UpperReplayClaimId,
    ) -> bool {
        let Some(index) = self.replay_finite_map_index.get(&(result, carrier)).copied() else {
            return false;
        };
        let occurrence = &self.replay_finite_map[index];
        debug_assert_eq!((occurrence.result, occurrence.carrier), (result, carrier));
        let side_index = match side {
            ReplayClaimParentSide::Lower => occurrence.replay_parent_sides[0],
            ReplayClaimParentSide::Upper => occurrence.replay_parent_sides[1],
        };
        self.replay_parent_chunks.contains(side_index, root)
    }

    fn qorf_occurrence_first_exact_parent(
        &self,
        occurrence: ReplayFiniteMapEntryId,
    ) -> ExactQualifiedParent {
        qorf_occurrence_first_exact_parent(
            &self.replay_finite_map,
            &self.replay_parent_chunks,
            occurrence,
        )
    }

    fn qorf_exact_parent_for_root_ref(
        &self,
        result: ConstraintRecordId,
        root: UpperReplayClaimId,
        reference: CanonicalQualifiedParentRef,
    ) -> ExactQualifiedParent {
        match reference {
            CanonicalQualifiedParentRef::Replay {
                finite_map_id,
                side,
            } => {
                let occurrence = &self.replay_finite_map[finite_map_id.0 as usize];
                debug_assert_eq!(occurrence.result, result);
                let side_index = match side {
                    ReplayClaimParentSide::Lower => occurrence.replay_parent_sides[0],
                    ReplayClaimParentSide::Upper => occurrence.replay_parent_sides[1],
                };
                let entry = self
                    .replay_parent_chunks
                    .qorf_entry(side_index, root)
                    .expect("QORF root winner replay ref must resolve exactly");
                ExactQualifiedParent {
                    coverage_root: root,
                    parent: ClaimQualifiedParent::ReplayConstraint {
                        parent_claim: entry.representative_claim,
                        parent_side: side,
                        replay: occurrence.carrier,
                    },
                }
            }
            CanonicalQualifiedParentRef::NonReplay { parent_id } => {
                let parent = self.non_replay_qualified_parents.entries[parent_id.0 as usize];
                debug_assert_eq!(parent.coverage_root, root);
                parent
            }
        }
    }

    fn try_prepare_qorf_root_winner_updates(
        &mut self,
        result: ConstraintRecordId,
        mut candidates: Vec<(ExactQualifiedParent, CanonicalQualifiedParentRef)>,
    ) -> Result<Vec<QorfPreparedCanonicalRootWinnerUpdate>, ProofFailure> {
        let exhausted = |_| ProofFailure::ResourceExhausted {
            operation: ProofOperation::UpdateClaimLifecycle,
        };
        candidates.sort_unstable_by(|left, right| {
            left.0
                .coverage_root
                .cmp(&right.0.coverage_root)
                .then_with(|| qualified_parent_entry_cmp(&left.0, &right.0))
        });
        candidates.dedup_by(|left, right| left.0.coverage_root == right.0.coverage_root);
        let mut updates = Vec::new();
        updates
            .try_reserve_exact(candidates.len())
            .map_err(exhausted)?;
        let mut inserted = 0usize;
        for (candidate, reference) in candidates {
            let existing = self
                .canonical_qualified_parent_by_root
                .get(result, candidate.coverage_root);
            if let Some(existing) = existing {
                let current = self.qorf_exact_parent_for_root_ref(
                    result,
                    candidate.coverage_root,
                    existing.winner,
                );
                if !qualified_parent_entry_cmp(&candidate, &current).is_lt() {
                    continue;
                }
            } else {
                inserted += 1;
            }
            updates.push(QorfPreparedCanonicalRootWinnerUpdate {
                result,
                entry: CanonicalQualifiedParentRootEntry {
                    coverage_root: candidate.coverage_root,
                    winner: reference,
                },
                buffers: QorfPreparedChunkBuffers::try_new()?,
            });
        }
        if updates.is_empty() {
            return Ok(updates);
        }
        if !self
            .canonical_qualified_parent_by_root
            .by_result
            .contains_key(&result)
        {
            self.canonical_qualified_parent_by_root
                .by_result
                .try_reserve(1)
                .map_err(exhausted)?;
        }
        let current_len = self
            .canonical_qualified_parent_by_root
            .by_result
            .get(&result)
            .map_or(0, |tree| tree.len);
        let inserted_u32 =
            u32::try_from(inserted).map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            })?;
        current_len
            .checked_add(inserted_u32)
            .ok_or(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            })?;
        self.canonical_qualified_parent_by_root
            .chunks
            .try_reserve(inserted)
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            })?;
        if inserted != 0 {
            let last_new_chunk = self
                .canonical_qualified_parent_by_root
                .chunks
                .len()
                .checked_add(inserted - 1)
                .ok_or(ProofFailure::ResourceExhausted {
                    operation: ProofOperation::UpdateClaimLifecycle,
                })?;
            u32::try_from(last_new_chunk).map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            })?;
        }
        Ok(updates)
    }

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

    pub(super) fn try_prepare_replay_qualified_parent_transaction(
        &mut self,
        result: ConstraintRecordId,
        carrier: BinaryReplayDerivation,
        parents: &[ClaimQualifiedParent],
    ) -> Result<PreparedReplayQualifiedParentTransaction, ProofFailure> {
        let exhausted = |_| ProofFailure::ResourceExhausted {
            operation: ProofOperation::UpdateClaimLifecycle,
        };
        let mut qualified = self.try_prepare_qualified_parent_admission(result, parents)?;
        #[cfg(test)]
        if self.qorf_fail_after(QorfReplayReservationFailurePoint::AfterQualified) {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }
        let mut accepted_parents = Vec::new();
        accepted_parents
            .try_reserve_exact(qualified.accepted.len())
            .map_err(exhausted)?;
        for entry in &qualified.accepted {
            let ClaimQualifiedParent::ReplayConstraint {
                parent_claim,
                parent_side,
                replay,
            } = entry.parent
            else {
                panic!("QORF replay transaction received a non-replay parent");
            };
            assert_eq!(replay, carrier, "QORF replay transaction carrier mismatch");
            let claim = self
                .upper_claim(parent_claim)
                .filter(|claim| claim.claim == parent_claim)
                .expect("qualified replay claims were resolved before QORF preparation");
            accepted_parents.push(ReplayProofParent {
                side: parent_side,
                coverage_root: entry.coverage_root,
                representative_claim: parent_claim,
                lineage: claim.lineage,
            });
        }

        let key = (result, carrier);
        let occurrence_index = self.replay_finite_map_index.get(&key).copied();
        let existing_sides = occurrence_index
            .map(|index| self.replay_finite_map[index].replay_parent_sides)
            .unwrap_or_default();
        let mut lower_entries = Vec::new();
        let mut upper_entries = Vec::new();
        lower_entries
            .try_reserve_exact(accepted_parents.len())
            .map_err(exhausted)?;
        upper_entries
            .try_reserve_exact(accepted_parents.len())
            .map_err(exhausted)?;
        for parent in &accepted_parents {
            let entry = QorfReplayParentEntry {
                coverage_root: parent.coverage_root,
                representative_claim: parent.representative_claim,
                lineage: parent.lineage,
            };
            match parent.side {
                ReplayClaimParentSide::Lower => lower_entries.push(entry),
                ReplayClaimParentSide::Upper => upper_entries.push(entry),
            }
        }
        let arena_base = self.replay_parent_chunks.nodes.len();
        let lower_shadow = try_prepare_qorf_side_delta(
            &self.replay_parent_chunks,
            ReplayClaimParentSide::Lower,
            existing_sides[0],
            lower_entries,
            arena_base,
        )?;
        let upper_base = arena_base
            + lower_shadow
                .as_ref()
                .map_or(0, |delta| delta.new_nodes.len());
        let upper_shadow = try_prepare_qorf_side_delta(
            &self.replay_parent_chunks,
            ReplayClaimParentSide::Upper,
            existing_sides[1],
            upper_entries,
            upper_base,
        )?;
        let new_chunk_count = lower_shadow
            .as_ref()
            .map_or(0, |delta| delta.new_nodes.len())
            + upper_shadow
                .as_ref()
                .map_or(0, |delta| delta.new_nodes.len());
        self.replay_parent_chunks
            .nodes
            .try_reserve(new_chunk_count)
            .map_err(exhausted)?;
        #[cfg(test)]
        if self.qorf_fail_after(QorfReplayReservationFailurePoint::AfterSideChunks) {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }

        let mut new_occurrence = None;
        let mut new_replay_result_indices = None;
        if !accepted_parents.is_empty() {
            if let Some(index) = occurrence_index {
                let lower_count = accepted_parents
                    .iter()
                    .filter(|parent| parent.side == ReplayClaimParentSide::Lower)
                    .count();
                let upper_count = accepted_parents.len() - lower_count;
                self.replay_finite_map[index]
                    .lower_parents
                    .try_reserve(lower_count)
                    .map_err(exhausted)?;
                self.replay_finite_map[index]
                    .upper_parents
                    .try_reserve(upper_count)
                    .map_err(exhausted)?;
            } else {
                self.replay_finite_map.try_reserve(1).map_err(exhausted)?;
                #[cfg(test)]
                if self.qorf_fail_after(QorfReplayReservationFailurePoint::AfterReplayFiniteMap) {
                    return Err(ProofFailure::ResourceExhausted {
                        operation: ProofOperation::UpdateClaimLifecycle,
                    });
                }
                self.replay_finite_map_index
                    .try_reserve(1)
                    .map_err(exhausted)?;
                #[cfg(test)]
                if self
                    .qorf_fail_after(QorfReplayReservationFailurePoint::AfterReplayFiniteMapIndex)
                {
                    return Err(ProofFailure::ResourceExhausted {
                        operation: ProofOperation::UpdateClaimLifecycle,
                    });
                }
                let mut lower_parents = Vec::new();
                let mut upper_parents = Vec::new();
                lower_parents
                    .try_reserve_exact(accepted_parents.len())
                    .map_err(exhausted)?;
                upper_parents
                    .try_reserve_exact(accepted_parents.len())
                    .map_err(exhausted)?;
                for parent in &accepted_parents {
                    match parent.side {
                        ReplayClaimParentSide::Lower => lower_parents.push(*parent),
                        ReplayClaimParentSide::Upper => upper_parents.push(*parent),
                    }
                }
                if let Some(indices) = self.replay_indices_by_result.get_mut(&result) {
                    indices.try_reserve(1).map_err(exhausted)?;
                } else {
                    self.replay_indices_by_result
                        .try_reserve(1)
                        .map_err(exhausted)?;
                    let mut indices = Vec::new();
                    indices.try_reserve_exact(1).map_err(exhausted)?;
                    new_replay_result_indices = Some(indices);
                }
                #[cfg(test)]
                if self.qorf_fail_after(QorfReplayReservationFailurePoint::AfterReplayResultIndex)
                {
                    return Err(ProofFailure::ResourceExhausted {
                        operation: ProofOperation::UpdateClaimLifecycle,
                    });
                }
                new_occurrence = Some(ReplayProofOccurrence {
                    result,
                    carrier,
                    lower_parents,
                    upper_parents,
                    first_event: self.replay_admissions.len(),
                    replay_parent_sides: [ReplayParentSideIndex::default(); 2],
                });
            }
        }
        #[cfg(test)]
        if self.qorf_fail_after(QorfReplayReservationFailurePoint::AfterOccurrence) {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }

        let occurrence_id = occurrence_index
            .map(|index| u32::try_from(index).map(ReplayFiniteMapEntryId))
            .unwrap_or_else(|| {
                u32::try_from(self.replay_finite_map.len()).map(ReplayFiniteMapEntryId)
            })
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            })?;
        let accepted_first = qualified
            .accepted
            .iter()
            .copied()
            .min_by(qualified_parent_entry_cmp);
        let arm_edit = if let Some(accepted_first) = accepted_first {
            let old_first =
                occurrence_index.map(|_| self.qorf_occurrence_first_exact_parent(occurrence_id));
            if old_first.is_none()
                || old_first
                    .is_some_and(|old| qualified_parent_entry_cmp(&accepted_first, &old).is_lt())
            {
                if !self.replay_qualified_arms.by_result.contains_key(&result) {
                    self.replay_qualified_arms
                        .by_result
                        .try_reserve(1)
                        .map_err(exhausted)?;
                }
                let current_len = self
                    .replay_qualified_arms
                    .by_result
                    .get(&result)
                    .map_or(0, |tree| tree.len);
                if old_first.is_none() {
                    current_len
                        .checked_add(1)
                        .ok_or(ProofFailure::ResourceExhausted {
                            operation: ProofOperation::UpdateClaimLifecycle,
                        })?;
                }
                self.replay_qualified_arms
                    .chunks
                    .try_reserve(1)
                    .map_err(exhausted)?;
                u32::try_from(self.replay_qualified_arms.chunks.len()).map_err(|_| {
                    ProofFailure::ResourceExhausted {
                        operation: ProofOperation::UpdateClaimLifecycle,
                    }
                })?;
                Some(QorfPreparedReplayQualifiedArmEdit {
                    result,
                    occurrence: occurrence_id,
                    rekey: old_first.is_some(),
                    buffers: QorfPreparedChunkBuffers::try_new()?,
                })
            } else {
                None
            }
        } else {
            None
        };
        #[cfg(test)]
        if self.qorf_fail_after(QorfReplayReservationFailurePoint::AfterArm) {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }
        let mut replay_root_candidates = Vec::new();
        replay_root_candidates
            .try_reserve_exact(qualified.accepted.len())
            .map_err(exhausted)?;
        for &entry in &qualified.accepted {
            let ClaimQualifiedParent::ReplayConstraint { parent_side, .. } = entry.parent else {
                unreachable!("replay transaction accepted only replay parents")
            };
            replay_root_candidates.push((
                entry,
                CanonicalQualifiedParentRef::Replay {
                    finite_map_id: occurrence_id,
                    side: parent_side,
                },
            ));
        }
        debug_assert!(
            qualified.root_winner_updates.is_empty(),
            "generic qualified-parent preparation excludes replay root candidates",
        );
        // Take ownership of the already fallibly allocated update plan. Extending the empty
        // generic plan here would perform an implicit infallible reservation before the outer
        // replay event can be appended on preparation failure.
        qualified.root_winner_updates =
            self.try_prepare_qorf_root_winner_updates(result, replay_root_candidates)?;
        #[cfg(test)]
        if self.qorf_fail_after(QorfReplayReservationFailurePoint::AfterRootWinner) {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }

        let mut new_first_witnesses = Vec::new();
        let mut pending_witnesses = FxHashSet::default();
        new_first_witnesses
            .try_reserve_exact(accepted_parents.len())
            .map_err(exhausted)?;
        pending_witnesses
            .try_reserve(accepted_parents.len())
            .map_err(exhausted)?;
        for parent in &accepted_parents {
            let witness_key = (result, parent.coverage_root);
            if !self.first_replay_witnesses.contains_key(&witness_key)
                && pending_witnesses.insert(witness_key)
            {
                new_first_witnesses.push((
                    witness_key,
                    ReplayFirstWitness {
                        carrier,
                        side: parent.side,
                        representative_claim: parent.representative_claim,
                    },
                ));
            }
        }
        self.first_replay_witnesses
            .try_reserve(new_first_witnesses.len())
            .map_err(exhausted)?;
        #[cfg(test)]
        if self.qorf_fail_after(QorfReplayReservationFailurePoint::AfterSummary) {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }

        let proof_occurrence = if accepted_parents.is_empty() {
            None
        } else {
            self.occurrences.try_reserve(1).map_err(exhausted)?;
            let mut occurrence_parents = Vec::new();
            occurrence_parents.try_reserve_exact(2).map_err(exhausted)?;
            occurrence_parents.push(ProofParent::Semantic(SemanticFactRef::Bound(carrier.lower)));
            occurrence_parents.push(ProofParent::Semantic(SemanticFactRef::Bound(carrier.upper)));
            Some(ProofOccurrence {
                result: ProofResult::Semantic(SemanticFactRef::Constraint(result)),
                cause: ProofCause::Replay(carrier),
                parents: occurrence_parents,
                event: self.occurrences.len(),
                completeness: ProvenanceCompleteness::Complete,
            })
        };
        #[cfg(test)]
        if self.qorf_fail_after(QorfReplayReservationFailurePoint::AfterProofOccurrence) {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }
        Ok(PreparedReplayQualifiedParentTransaction {
            qualified,
            carrier,
            occurrence_index,
            new_occurrence,
            new_replay_result_indices,
            accepted_parents,
            lower_shadow,
            upper_shadow,
            arm_edit,
            new_first_witnesses,
            proof_occurrence,
        })
    }

    fn commit_replay_parent_side_shadow_delta(
        arena: &mut ReplayParentChunkArena,
        side_index: &mut ReplayParentSideIndex,
        delta: PreparedReplayParentSideShadowDelta,
    ) {
        debug_assert_eq!(arena.nodes.len(), delta.first_new_node_index);
        let new_node_start = arena.nodes.len();
        arena.nodes.extend(delta.new_nodes);
        for (id, entries) in delta.replacements {
            arena.node_mut(id).entries = entries;
        }
        let mut root = delta.new_root.or(side_index.root);
        if delta.new_root.is_none() {
            for index in new_node_start..arena.nodes.len() {
                let id = ReplayParentChunkId(index as u32);
                root = Some(arena.insert_node(root, id));
            }
        }
        side_index.root = root;
        side_index.len = delta.resulting_len;
    }

    #[cfg(test)]
    fn debug_assert_qorf_b_side_shadow_matches_legacy(&self, index: usize) {
        if QORF_C_FULL_STD_PARITY_ACTIVE.with(Cell::get) {
            return;
        }
        let occurrence = &self.replay_finite_map[index];
        for (side, legacy) in [
            (ReplayClaimParentSide::Lower, &occurrence.lower_parents),
            (ReplayClaimParentSide::Upper, &occurrence.upper_parents),
        ] {
            let shadow = self
                .replay_parents_for_occurrence_side(occurrence, side)
                .collect::<Vec<_>>();
            let mut expected = legacy.clone();
            expected.sort_unstable_by_key(|entry| entry.coverage_root);
            assert_eq!(shadow, expected);
            assert_eq!(shadow.len(), expected.len());
            assert!(
                shadow
                    .windows(2)
                    .all(|pair| pair[0].coverage_root < pair[1].coverage_root)
            );
        }
    }

    pub(super) fn commit_replay_qualified_parent_transaction(
        &mut self,
        transaction: &mut PreparedReplayQualifiedParentTransaction,
    ) {
        if transaction.accepted_parents.is_empty() {
            self.commit_qualified_parent_admission(&mut transaction.qualified);
            return;
        }
        let arm_edit = transaction.arm_edit.take();
        let mut recycled_arm_chunk = None;
        if arm_edit.as_ref().is_some_and(|edit| edit.rekey) {
            let edit = arm_edit.as_ref().unwrap();
            let occurrences = &self.replay_finite_map;
            let chunks = &self.replay_parent_chunks;
            let cmp = |left, right| {
                qualified_parent_entry_cmp(
                    &qorf_occurrence_first_exact_parent(occurrences, chunks, left),
                    &qorf_occurrence_first_exact_parent(occurrences, chunks, right),
                )
            };
            recycled_arm_chunk = self
                .replay_qualified_arms
                .remove(edit.result, edit.occurrence, &cmp);
        }
        let is_new_occurrence = transaction.new_occurrence.is_some();
        let index = if let Some(occurrence) = transaction.new_occurrence.take() {
            let index = self.replay_finite_map.len();
            let key = (occurrence.result, occurrence.carrier);
            assert!(self.replay_finite_map_index.insert(key, index).is_none());
            if let Some(indices) = transaction.new_replay_result_indices.take() {
                assert!(
                    self.replay_indices_by_result
                        .insert(occurrence.result, indices)
                        .is_none()
                );
            }
            self.replay_indices_by_result
                .get_mut(&occurrence.result)
                .expect("QORF replay result index capacity was prepared")
                .push(index);
            self.replay_finite_map.push(occurrence);
            index
        } else {
            transaction
                .occurrence_index
                .expect("accepted QORF delta has an existing or prepared occurrence")
        };
        if !is_new_occurrence {
            for parent in &transaction.accepted_parents {
                let target = match parent.side {
                    ReplayClaimParentSide::Lower => {
                        &mut self.replay_finite_map[index].lower_parents
                    }
                    ReplayClaimParentSide::Upper => {
                        &mut self.replay_finite_map[index].upper_parents
                    }
                };
                target.push(*parent);
            }
        }
        if let Some(delta) = transaction.lower_shadow.take() {
            Self::commit_replay_parent_side_shadow_delta(
                &mut self.replay_parent_chunks,
                &mut self.replay_finite_map[index].replay_parent_sides[0],
                delta,
            );
        }
        if let Some(delta) = transaction.upper_shadow.take() {
            Self::commit_replay_parent_side_shadow_delta(
                &mut self.replay_parent_chunks,
                &mut self.replay_finite_map[index].replay_parent_sides[1],
                delta,
            );
        }
        if let Some(edit) = arm_edit {
            let occurrences = &self.replay_finite_map;
            let chunks = &self.replay_parent_chunks;
            let cmp = |left, right| {
                qualified_parent_entry_cmp(
                    &qorf_occurrence_first_exact_parent(occurrences, chunks, left),
                    &qorf_occurrence_first_exact_parent(occurrences, chunks, right),
                )
            };
            self.replay_qualified_arms
                .insert(
                    edit.result,
                    edit.occurrence,
                    recycled_arm_chunk,
                    edit.buffers,
                    &cmp,
                );
        }
        for (key, witness) in transaction.new_first_witnesses.drain(..) {
            self.first_replay_witnesses.entry(key).or_insert(witness);
        }
        self.commit_qualified_parent_admission(&mut transaction.qualified);
        if let Some(occurrence) = transaction.proof_occurrence.take() {
            debug_assert_eq!(occurrence.event, self.occurrences.len());
            self.occurrences.push(occurrence);
        }
        #[cfg(test)]
        {
            self.debug_assert_qorf_b_side_shadow_matches_legacy(index);
            self.debug_assert_qorf_d0_projections_match_legacy(transaction.qualified.result);
        }
    }

    #[cfg(test)]
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
        let mut parents_resolved = Vec::new();
        parents_resolved
            .try_reserve_exact(parents.len())
            .expect("QORF test snapshot parent staging must allocate");
        for parent in parents {
            let claim = self
                .upper_claim(parent.claim)
                .filter(|claim| claim.claim == parent.claim)
                .expect("a CPK replay parent must be admitted before its snapshot");
            parents_resolved.push(ReplayProofParent {
                side: parent.parent_side,
                coverage_root: claim.coverage_root,
                representative_claim: parent.claim,
                lineage: claim.lineage,
            });
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
                    replay_parent_sides: [ReplayParentSideIndex::default(); 2],
                });
                self.replay_finite_map_index.insert(key, index);
                self.replay_indices_by_result
                    .entry(result)
                    .or_default()
                    .push(index);
                index
            });
        let mut accepted_parents = Vec::new();
        accepted_parents
            .try_reserve_exact(parents_resolved.len())
            .expect("QORF test snapshot accepted-parent staging must allocate");
        for parent in parents_resolved {
            let target = match parent.side {
                ReplayClaimParentSide::Lower => &self.replay_finite_map[index].lower_parents,
                ReplayClaimParentSide::Upper => &self.replay_finite_map[index].upper_parents,
            };
            if target
                .iter()
                .any(|entry| entry.coverage_root == parent.coverage_root)
                || accepted_parents.iter().any(|entry: &ReplayProofParent| {
                    entry.side == parent.side && entry.coverage_root == parent.coverage_root
                })
            {
                continue;
            }
            accepted_parents.push(parent);
        }
        if accepted_parents.is_empty() {
            return;
        }

        let existing_sides = self.replay_finite_map[index].replay_parent_sides;
        let mut lower_entries = Vec::new();
        let mut upper_entries = Vec::new();
        lower_entries
            .try_reserve_exact(accepted_parents.len())
            .expect("QORF test lower-side staging must allocate");
        upper_entries
            .try_reserve_exact(accepted_parents.len())
            .expect("QORF test upper-side staging must allocate");
        for parent in &accepted_parents {
            let entry = QorfReplayParentEntry {
                coverage_root: parent.coverage_root,
                representative_claim: parent.representative_claim,
                lineage: parent.lineage,
            };
            match parent.side {
                ReplayClaimParentSide::Lower => lower_entries.push(entry),
                ReplayClaimParentSide::Upper => upper_entries.push(entry),
            }
        }
        let arena_base = self.replay_parent_chunks.nodes.len();
        let lower_shadow = try_prepare_qorf_side_delta(
            &self.replay_parent_chunks,
            ReplayClaimParentSide::Lower,
            existing_sides[0],
            lower_entries,
            arena_base,
        )
        .expect("QORF test lower-side shadow must prepare");
        let upper_base = arena_base
            + lower_shadow
                .as_ref()
                .map_or(0, |delta| delta.new_nodes.len());
        let upper_shadow = try_prepare_qorf_side_delta(
            &self.replay_parent_chunks,
            ReplayClaimParentSide::Upper,
            existing_sides[1],
            upper_entries,
            upper_base,
        )
        .expect("QORF test upper-side shadow must prepare");
        let new_chunk_count = lower_shadow
            .as_ref()
            .map_or(0, |delta| delta.new_nodes.len())
            + upper_shadow
                .as_ref()
                .map_or(0, |delta| delta.new_nodes.len());
        self.replay_parent_chunks
            .nodes
            .try_reserve(new_chunk_count)
            .expect("QORF test side arena must reserve before commit");

        for parent in accepted_parents {
            match parent.side {
                ReplayClaimParentSide::Lower => {
                    self.replay_finite_map[index].lower_parents.push(parent)
                }
                ReplayClaimParentSide::Upper => {
                    self.replay_finite_map[index].upper_parents.push(parent)
                }
            }
            self.first_replay_witnesses
                .entry((result, parent.coverage_root))
                .or_insert(ReplayFirstWitness {
                    carrier,
                    side: parent.side,
                    representative_claim: parent.representative_claim,
                });
        }
        if let Some(delta) = lower_shadow {
            Self::commit_replay_parent_side_shadow_delta(
                &mut self.replay_parent_chunks,
                &mut self.replay_finite_map[index].replay_parent_sides[0],
                delta,
            );
        }
        if let Some(delta) = upper_shadow {
            Self::commit_replay_parent_side_shadow_delta(
                &mut self.replay_parent_chunks,
                &mut self.replay_finite_map[index].replay_parent_sides[1],
                delta,
            );
        }
        self.rebuild_qorf_d0_projections_for_test(result);
        self.debug_assert_qorf_b_side_shadow_matches_legacy(index);
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

    #[cfg(test)]
    fn rebuild_qorf_d0_projections_for_test(&mut self, result: ConstraintRecordId) {
        // This helper exists only for old fixtures that deliberately split qualified admission
        // from their test snapshot writer. Production uses the unified prepared transaction.
        self.replay_qualified_arms.by_result.remove(&result);
        let mut seen = FxHashSet::default();
        let legacy = self
            .qualified_parents_by_result
            .get(&result)
            .cloned()
            .unwrap_or_default();
        for entry in &legacy {
            let ClaimQualifiedParent::ReplayConstraint { replay, .. } = entry.parent else {
                continue;
            };
            let occurrence = self.replay_finite_map_index[&(result, replay)];
            if !seen.insert(occurrence) {
                continue;
            }
            self.replay_qualified_arms.by_result.reserve(1);
            self.replay_qualified_arms.chunks.reserve(1);
            let occurrences = &self.replay_finite_map;
            let chunks = &self.replay_parent_chunks;
            let cmp = |left, right| {
                qualified_parent_entry_cmp(
                    &qorf_occurrence_first_exact_parent(occurrences, chunks, left),
                    &qorf_occurrence_first_exact_parent(occurrences, chunks, right),
                )
            };
            self.replay_qualified_arms.insert(
                result,
                ReplayFiniteMapEntryId(occurrence as u32),
                None,
                QorfPreparedChunkBuffers::try_new().expect("test arm buffers"),
                &cmp,
            );
        }

        self.canonical_qualified_parent_by_root
            .by_result
            .remove(&result);
        let mut previous_root = None;
        for entry in legacy {
            if previous_root == Some(entry.coverage_root) {
                continue;
            }
            previous_root = Some(entry.coverage_root);
            let winner = match entry.parent {
                ClaimQualifiedParent::ReplayConstraint {
                    parent_side,
                    replay,
                    ..
                } => CanonicalQualifiedParentRef::Replay {
                    finite_map_id: ReplayFiniteMapEntryId(
                        self.replay_finite_map_index[&(result, replay)] as u32,
                    ),
                    side: parent_side,
                },
                ClaimQualifiedParent::StructuralConstraint { .. }
                | ClaimQualifiedParent::ReductionRouteConstraint { .. } => {
                    let parent_id = self
                        .non_replay_qualified_parents
                        .by_result
                        .get(&result)
                        .into_iter()
                        .flatten()
                        .copied()
                        .find(|id| {
                            self.non_replay_qualified_parents.entries[id.0 as usize] == entry
                        })
                        .expect(
                            "test compatibility rebuild requires the admitted non-replay parent",
                        );
                    CanonicalQualifiedParentRef::NonReplay { parent_id }
                }
            };
            self.canonical_qualified_parent_by_root.by_result.reserve(1);
            self.canonical_qualified_parent_by_root.chunks.reserve(1);
            self.canonical_qualified_parent_by_root
                .apply(QorfPreparedCanonicalRootWinnerUpdate {
                    result,
                    entry: CanonicalQualifiedParentRootEntry {
                        coverage_root: entry.coverage_root,
                        winner,
                    },
                    buffers: QorfPreparedChunkBuffers::try_new().expect("test root buffers"),
                });
        }
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
        let mut pending_first_source_keys = FxHashSet::default();
        let mut new_first_sources = Vec::new();
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
            let registered = match identity {
                QualifiedParentIdentity::Replay {
                    parent_side,
                    replay,
                } => {
                    let registered = self.exact_replay_qualified_parent_is_registered(
                        result,
                        replay,
                        parent_side,
                        claim.coverage_root,
                    );
                    #[cfg(test)]
                    assert_eq!(
                        registered,
                        self.qualified_parent_keys.contains(&key),
                        "QORF-C side authority must match the legacy replay membership oracle",
                    );
                    registered
                }
                QualifiedParentIdentity::Structural(_)
                | QualifiedParentIdentity::ReductionRoute { .. } => {
                    self.qualified_parent_keys.contains(&key)
                }
            };
            if registered || !pending_keys.insert(key) {
                continue;
            }
            accepted.push(ExactQualifiedParent {
                coverage_root: claim.coverage_root,
                parent,
            });
            let source_key = (result, claim.coverage_root);
            if !self
                .first_qualified_parent_source_by_root
                .contains_key(&source_key)
                && !pending_first_source_keys.contains(&source_key)
            {
                // A parent batch is usually much wider than its new `(result, root)` frontier.
                // Grow the plan-local first-source delta only when that frontier really advances.
                // Both reservations remain fallible and precede even the temporary insertion, so
                // a failure cannot escape preparation or partially commit persistent proof state.
                pending_first_source_keys
                    .try_reserve(1)
                    .map_err(exhausted)?;
                new_first_sources.try_reserve(1).map_err(exhausted)?;
                let inserted = pending_first_source_keys.insert(source_key);
                debug_assert!(inserted);
                let source = match parent {
                    ClaimQualifiedParent::ReplayConstraint { .. } => {
                        FirstQualifiedParentSource::Replay
                    }
                    ClaimQualifiedParent::StructuralConstraint { .. }
                    | ClaimQualifiedParent::ReductionRouteConstraint { .. } => {
                        FirstQualifiedParentSource::NonReplay(parent)
                    }
                };
                new_first_sources.push((source_key, source));
            }
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
        self.first_qualified_parent_source_by_root
            .try_reserve(new_first_sources.len())
            .map_err(exhausted)?;
        #[cfg(test)]
        if self.qorf_fail_after(QorfReplayReservationFailurePoint::AfterQualifiedSourceSummary) {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }
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
        let mut new_non_replay_parents = Vec::new();
        new_non_replay_parents
            .try_reserve_exact(accepted.len())
            .map_err(exhausted)?;
        let mut root_candidates = Vec::new();
        root_candidates
            .try_reserve_exact(accepted.len())
            .map_err(exhausted)?;
        for &entry in &accepted {
            if matches!(entry.parent, ClaimQualifiedParent::ReplayConstraint { .. }) {
                continue;
            }
            let id = u32::try_from(
                self.non_replay_qualified_parents.entries.len() + new_non_replay_parents.len(),
            )
            .map(NonReplayQualifiedParentId)
            .map_err(|_| ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            })?;
            new_non_replay_parents.push(entry);
            root_candidates.push((
                entry,
                CanonicalQualifiedParentRef::NonReplay { parent_id: id },
            ));
        }
        self.non_replay_qualified_parents
            .entries
            .try_reserve(new_non_replay_parents.len())
            .map_err(exhausted)?;
        let new_non_replay_result_entries = if new_non_replay_parents.is_empty() {
            None
        } else {
            let existing = self
                .non_replay_qualified_parents
                .by_result
                .get(&result)
                .map(Vec::as_slice)
                .unwrap_or_default();
            let mut entries = Vec::new();
            entries
                .try_reserve_exact(existing.len() + new_non_replay_parents.len())
                .map_err(exhausted)?;
            entries.extend_from_slice(existing);
            let first_new = self.non_replay_qualified_parents.entries.len();
            for offset in 0..new_non_replay_parents.len() {
                let id = u32::try_from(first_new + offset)
                    .map(NonReplayQualifiedParentId)
                    .map_err(|_| ProofFailure::ResourceExhausted {
                        operation: ProofOperation::UpdateClaimLifecycle,
                    })?;
                entries.push(id);
            }
            entries.sort_unstable_by(|left, right| {
                let resolve = |id: NonReplayQualifiedParentId| {
                    let index = id.0 as usize;
                    if index < first_new {
                        self.non_replay_qualified_parents.entries[index]
                    } else {
                        new_non_replay_parents[index - first_new]
                    }
                };
                qualified_parent_entry_cmp(&resolve(*left), &resolve(*right))
            });
            if !self
                .non_replay_qualified_parents
                .by_result
                .contains_key(&result)
            {
                self.non_replay_qualified_parents
                    .by_result
                    .try_reserve(1)
                    .map_err(exhausted)?;
            }
            Some(entries)
        };
        let root_winner_updates =
            self.try_prepare_qorf_root_winner_updates(result, root_candidates)?;
        #[cfg(test)]
        if !root_winner_updates.is_empty()
            && self.qorf_fail_after(QorfReplayReservationFailurePoint::AfterRootWinner)
        {
            return Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            });
        }
        Ok(PreparedQualifiedParentAdmission {
            result,
            accepted,
            canonical,
            new_result_entries,
            new_first_sources,
            new_non_replay_parents,
            new_non_replay_result_entries,
            root_winner_updates,
            #[cfg(test)]
            pending_first_source_capacity: pending_first_source_keys.capacity(),
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
        for (key, source) in admission.new_first_sources.drain(..) {
            assert!(self
                .first_qualified_parent_source_by_root
                .insert(key, source)
                .is_none());
        }
        self.non_replay_qualified_parents
            .entries
            .extend(admission.new_non_replay_parents.drain(..));
        if let Some(entries) = admission.new_non_replay_result_entries.take() {
            self.non_replay_qualified_parents
                .by_result
                .insert(admission.result, entries);
        }
        for update in admission.root_winner_updates.drain(..) {
            self.canonical_qualified_parent_by_root.apply(update);
        }
        let entries = self
            .qualified_parents_by_result
            .get_mut(&admission.result)
            .expect("qualified-parent result capacity was prepared before commit");
        merge_qualified_parent_entries(entries, &admission.canonical);
        #[cfg(test)]
        if admission
            .accepted
            .iter()
            .all(|entry| !matches!(entry.parent, ClaimQualifiedParent::ReplayConstraint { .. }))
        {
            self.debug_assert_qorf_d0_projections_match_legacy(admission.result);
        }
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

    pub(super) fn qualified_parent_values_for_result(
        &self,
        result: ConstraintRecordId,
    ) -> impl ExactSizeIterator<Item = ClaimQualifiedParent> + '_ {
        self.qualified_parents_for_result(result)
            .iter()
            .map(|entry| entry.parent)
    }

    pub(super) fn qualified_parent_count(&self, result: ConstraintRecordId) -> usize {
        self.qualified_parents_for_result(result).len()
    }

    fn try_exact_qualified_parents(
        &self,
        result: ConstraintRecordId,
    ) -> ProofKernelResult<QorfExactQualifiedParentCursor<'_>> {
        let exhausted = |_| ProofFailure::ResourceExhausted {
            operation: ProofOperation::UpdateClaimLifecycle,
        };
        let replay_indices = self
            .replay_indices_by_result
            .get(&result)
            .map(Vec::as_slice)
            .unwrap_or_default();
        let non_replay_ids = self
            .non_replay_qualified_parents
            .by_result
            .get(&result)
            .map(Vec::as_slice)
            .unwrap_or_default();
        let replay_source_count = replay_indices
            .iter()
            .map(|&index| {
                self.replay_finite_map[index]
                    .replay_parent_sides
                    .iter()
                    .filter(|side| side.len != 0)
                    .count()
            })
            .sum::<usize>();
        let source_count = replay_source_count + usize::from(!non_replay_ids.is_empty());
        let mut sources = Vec::new();
        sources.try_reserve_exact(source_count).map_err(exhausted)?;
        for &index in replay_indices {
            let occurrence = &self.replay_finite_map[index];
            for (side, side_index) in [
                (
                    ReplayClaimParentSide::Lower,
                    occurrence.replay_parent_sides[0],
                ),
                (
                    ReplayClaimParentSide::Upper,
                    occurrence.replay_parent_sides[1],
                ),
            ] {
                if side_index.len == 0 {
                    continue;
                }
                sources.push(QorfExactQualifiedParentSource::Replay {
                    carrier: occurrence.carrier,
                    cursor: ReplayParentSideCursor::new(
                        &self.replay_parent_chunks,
                        side_index,
                        side,
                    ),
                });
            }
        }
        if !non_replay_ids.is_empty() {
            sources.push(QorfExactQualifiedParentSource::NonReplay {
                entries: &self.non_replay_qualified_parents.entries,
                ids: non_replay_ids,
                position: 0,
            });
        }
        debug_assert_eq!(sources.len(), source_count);
        let mut frontier = std::collections::BinaryHeap::new();
        frontier
            .try_reserve_exact(source_count)
            .map_err(exhausted)?;
        for (source, cursor) in sources.iter_mut().enumerate() {
            let parent = cursor
                .next_parent()
                .expect("QORF exact cursor sources must be nonempty");
            frontier.push(QorfExactQualifiedParentHeapEntry { parent, source });
        }
        Ok(QorfExactQualifiedParentCursor { sources, frontier })
    }

    fn try_replay_clause_link_associations(
        &self,
        result: ConstraintRecordId,
    ) -> ProofKernelResult<QorfClauseLinkAssociationCursor<'_>> {
        Ok(QorfClauseLinkAssociationCursor {
            exact: self.try_exact_qualified_parents(result)?,
            previous: None,
        })
    }

    /// Retained QORF-A oracle. Both faces are expanded independently into the exact identity/value
    /// schema from Appendix A; callers compare maps, not hash iteration order or only counts.
    #[cfg(test)]
    fn qorf_a_replay_relation_snapshot(&self) -> QorfReplayRelationSnapshot {
        let mut snapshot = QorfReplayRelationSnapshot::default();
        for (&result, entries) in &self.qualified_parents_by_result {
            for entry in entries {
                let ClaimQualifiedParent::ReplayConstraint {
                    parent_claim,
                    parent_side,
                    replay,
                } = entry.parent
                else {
                    continue;
                };
                let lineage = self
                    .upper_claim(parent_claim)
                    .filter(|claim| claim.claim == parent_claim)
                    .expect("qualified replay parent must resolve through the claim index")
                    .lineage;
                let previous = snapshot.qualified.insert(
                    QorfReplayRelationKey {
                        result,
                        carrier: replay,
                        side: parent_side,
                        coverage_root: entry.coverage_root,
                    },
                    QorfReplayRelationValue {
                        representative_claim: parent_claim,
                        lineage,
                    },
                );
                snapshot.qualified_duplicate_keys += usize::from(previous.is_some());
            }
        }
        for occurrence in &self.replay_finite_map {
            for (expected_side, parents) in [
                (ReplayClaimParentSide::Lower, &occurrence.lower_parents),
                (ReplayClaimParentSide::Upper, &occurrence.upper_parents),
            ] {
                for parent in parents {
                    snapshot.side_container_mismatches += usize::from(parent.side != expected_side);
                    let previous = snapshot.finite_map.insert(
                        QorfReplayRelationKey {
                            result: occurrence.result,
                            carrier: occurrence.carrier,
                            side: expected_side,
                            coverage_root: parent.coverage_root,
                        },
                        QorfReplayRelationValue {
                            representative_claim: parent.representative_claim,
                            lineage: parent.lineage,
                        },
                    );
                    snapshot.finite_map_duplicate_keys += usize::from(previous.is_some());
                }
            }
        }
        snapshot
    }

    #[cfg(test)]
    fn debug_assert_qorf_a_replay_relation_matches(&self) {
        self.qorf_a_replay_relation_snapshot().assert_exact_parity();
    }

    #[cfg(test)]
    fn debug_assert_qorf_d0_projections_match_legacy(&self, result: ConstraintRecordId) {
        if QORF_C_FULL_STD_PARITY_ACTIVE.with(Cell::get) {
            return;
        }
        let Some(legacy) = self.qualified_parents_by_result.get(&result) else {
            return;
        };
        if legacy.iter().any(|entry| {
            let ClaimQualifiedParent::ReplayConstraint { replay, .. } = entry.parent else {
                return false;
            };
            !self.replay_finite_map_index.contains_key(&(result, replay))
        }) {
            // A few old unit-test bypasses admit the qualified face before their test-only
            // snapshot writer creates an occurrence. Production never exposes this midpoint.
            return;
        }

        let mut expected_arms = Vec::new();
        let mut seen = FxHashSet::default();
        for entry in legacy {
            let ClaimQualifiedParent::ReplayConstraint { replay, .. } = entry.parent else {
                continue;
            };
            let occurrence = self.replay_finite_map_index[&(result, replay)];
            if seen.insert(occurrence) {
                expected_arms.push(ReplayFiniteMapEntryId(occurrence as u32));
            }
        }
        assert_eq!(self.replay_qualified_arms.flatten(result), expected_arms);

        let mut expected_winners = Vec::new();
        let mut previous_root = None;
        for &entry in legacy {
            if previous_root == Some(entry.coverage_root) {
                continue;
            }
            previous_root = Some(entry.coverage_root);
            expected_winners.push(entry);
        }
        let actual_winners = self
            .canonical_qualified_parent_by_root
            .flatten(result)
            .into_iter()
            .map(|entry| {
                self.qorf_exact_parent_for_root_ref(result, entry.coverage_root, entry.winner)
            })
            .collect::<Vec<_>>();
        assert_eq!(actual_winners, expected_winners);

        let expected_non_replay = legacy
            .iter()
            .copied()
            .filter(|entry| !matches!(entry.parent, ClaimQualifiedParent::ReplayConstraint { .. }))
            .collect::<Vec<_>>();
        let actual_non_replay = self
            .non_replay_qualified_parents
            .by_result
            .get(&result)
            .into_iter()
            .flatten()
            .map(|id| self.non_replay_qualified_parents.entries[id.0 as usize])
            .collect::<Vec<_>>();
        assert_eq!(actual_non_replay, expected_non_replay);

        let actual_exact = self
            .try_exact_qualified_parents(result)
            .expect("QORF fixture exact cursor construction")
            .collect::<Vec<_>>();
        assert_eq!(actual_exact.as_slice(), legacy.as_slice());

        let mut expected_associations = Vec::new();
        for &entry in legacy {
            let key = (
                entry.coverage_root,
                qualified_parent_projection_carrier(entry.parent),
            );
            if expected_associations
                .last()
                .is_some_and(|previous: &ExactQualifiedParent| {
                    (
                        previous.coverage_root,
                        qualified_parent_projection_carrier(previous.parent),
                    ) == key
                })
            {
                continue;
            }
            expected_associations.push(entry);
        }
        let actual_associations = self
            .try_replay_clause_link_associations(result)
            .expect("QORF fixture association cursor construction")
            .collect::<Vec<_>>();
        assert_eq!(actual_associations, expected_associations);
    }

    /// Exhaustive, allocation-bounded QORF-C authority gate for the repository-std workload.
    ///
    /// This streams the 50M-scale relation instead of constructing the retained QORF-A pair of
    /// full hash maps. Equality of every legacy side with its sorted cursor, exact lookup of every
    /// qualified replay entry and key, and equal cardinalities prove a key/value bijection without
    /// another relation-sized allocation.
    #[cfg(test)]
    fn qorf_c_full_std_parity_report(&self) -> QorfCFullStdParityReport {
        let mut report = QorfCFullStdParityReport {
            occurrences: self.replay_finite_map.len(),
            nonempty_sides: 0,
            side_entries: 0,
            qualified_replay_entries: 0,
            qualified_replay_keys: 0,
            replay_arms: 0,
            root_winners: 0,
            d0_projection_census: QorfD0ProjectionAllocationCensus::default(),
        };
        let mut expected_side = Vec::new();

        for occurrence in &self.replay_finite_map {
            for (side, legacy) in [
                (ReplayClaimParentSide::Lower, &occurrence.lower_parents),
                (ReplayClaimParentSide::Upper, &occurrence.upper_parents),
            ] {
                report.nonempty_sides += usize::from(!legacy.is_empty());
                report.side_entries += legacy.len();
                expected_side.clear();
                expected_side
                    .try_reserve(legacy.len())
                    .expect("QORF-C full-std parity side scratch allocation");
                expected_side.extend_from_slice(legacy);
                expected_side.sort_unstable_by_key(|entry| entry.coverage_root);
                assert!(expected_side
                    .windows(2)
                    .all(|pair| pair[0].coverage_root < pair[1].coverage_root));
                assert!(
                    self.replay_parents_for_occurrence_side(occurrence, side)
                        .eq(expected_side.iter().copied()),
                    "QORF-C full-std side cursor diverged for ({:?}, {:?}, {:?})",
                    occurrence.result,
                    occurrence.carrier,
                    side,
                );
            }
        }

        for (&result, parents) in &self.qualified_parents_by_result {
            assert!(
                self.try_exact_qualified_parents(result)
                    .expect("QORF-D0 full-std exact cursor construction")
                    .eq(parents.iter().copied()),
                "QORF-D0 exact compatibility cursor diverged for {result:?}",
            );
            let mut previous_association = None;
            let expected_associations = parents.iter().copied().filter(|parent| {
                let key = (
                    parent.coverage_root,
                    qualified_parent_projection_carrier(parent.parent),
                );
                if previous_association == Some(key) {
                    return false;
                }
                previous_association = Some(key);
                true
            });
            assert!(
                self.try_replay_clause_link_associations(result)
                    .expect("QORF-D0 full-std association cursor construction")
                    .eq(expected_associations),
                "QORF-D0 clause-link association cursor diverged for {result:?}",
            );
            for parent in parents {
                let ClaimQualifiedParent::ReplayConstraint {
                    parent_claim,
                    parent_side,
                    replay,
                } = parent.parent
                else {
                    continue;
                };
                report.qualified_replay_entries += 1;
                let occurrence_index = self
                    .replay_finite_map_index
                    .get(&(result, replay))
                    .copied()
                    .expect("qualified replay entry must have a finite-map occurrence");
                let occurrence = &self.replay_finite_map[occurrence_index];
                let side_index = match parent_side {
                    ReplayClaimParentSide::Lower => occurrence.replay_parent_sides[0],
                    ReplayClaimParentSide::Upper => occurrence.replay_parent_sides[1],
                };
                let actual = self
                    .replay_parent_chunks
                    .qorf_entry(side_index, parent.coverage_root)
                    .expect("qualified replay entry must have an exact side entry");
                let lineage = self
                    .upper_claim(parent_claim)
                    .filter(|claim| claim.claim == parent_claim)
                    .expect("qualified replay parent must resolve through the claim index")
                    .lineage;
                assert_eq!(
                    actual,
                    QorfReplayParentEntry {
                        coverage_root: parent.coverage_root,
                        representative_claim: parent_claim,
                        lineage,
                    },
                    "QORF-C full-std side value diverged for ({result:?}, {replay:?}, {parent_side:?})",
                );
            }
            let mut expected_arms = Vec::new();
            let mut seen_occurrences = FxHashSet::default();
            let mut expected_winners = Vec::new();
            let mut previous_root = None;
            for &parent in parents {
                if previous_root != Some(parent.coverage_root) {
                    previous_root = Some(parent.coverage_root);
                    expected_winners.push(parent);
                }
                let ClaimQualifiedParent::ReplayConstraint { replay, .. } = parent.parent else {
                    continue;
                };
                let occurrence = self.replay_finite_map_index[&(result, replay)];
                if seen_occurrences.insert(occurrence) {
                    expected_arms.push(ReplayFiniteMapEntryId(occurrence as u32));
                }
            }
            let actual_arms = self.replay_qualified_arms.flatten(result);
            assert_eq!(actual_arms, expected_arms);
            report.replay_arms += actual_arms.len();
            let actual_winners = self
                .canonical_qualified_parent_by_root
                .flatten(result)
                .into_iter()
                .map(|entry| {
                    self.qorf_exact_parent_for_root_ref(result, entry.coverage_root, entry.winner)
                })
                .collect::<Vec<_>>();
            assert_eq!(actual_winners, expected_winners);
            report.root_winners += actual_winners.len();
        }

        for key in &self.qualified_parent_keys {
            let QualifiedParentIdentity::Replay {
                parent_side,
                replay,
            } = key.identity
            else {
                continue;
            };
            report.qualified_replay_keys += 1;
            assert!(
                self.exact_replay_qualified_parent_is_registered(
                    key.result,
                    replay,
                    parent_side,
                    key.coverage_root,
                ),
                "QORF-C full-std side membership missed legacy key {key:?}",
            );
        }

        assert_eq!(report.side_entries, report.qualified_replay_entries);
        assert_eq!(report.side_entries, report.qualified_replay_keys);
        report.d0_projection_census = self.qorf_d0_projection_allocation_census();
        report
    }

    #[cfg(test)]
    fn qorf_d0_projection_allocation_census(&self) -> QorfD0ProjectionAllocationCensus {
        let arm_entries = self
            .replay_qualified_arms
            .chunks
            .iter()
            .map(|chunk| (chunk.entries.len(), chunk.entries.capacity()))
            .fold((0, 0), |total, next| (total.0 + next.0, total.1 + next.1));
        let root_entries = self
            .canonical_qualified_parent_by_root
            .chunks
            .iter()
            .map(|chunk| (chunk.entries.len(), chunk.entries.capacity()))
            .fold((0, 0), |total, next| (total.0 + next.0, total.1 + next.1));
        let non_replay_result_ids = self
            .non_replay_qualified_parents
            .by_result
            .values()
            .map(|ids| (ids.len(), ids.capacity()))
            .fold((0, 0), |total, next| (total.0 + next.0, total.1 + next.1));
        let arm_result_buckets = (
            self.replay_qualified_arms.by_result.len(),
            self.replay_qualified_arms.by_result.capacity(),
        );
        let arm_chunks = (
            self.replay_qualified_arms.chunks.len(),
            self.replay_qualified_arms.chunks.capacity(),
        );
        let root_result_buckets = (
            self.canonical_qualified_parent_by_root.by_result.len(),
            self.canonical_qualified_parent_by_root.by_result.capacity(),
        );
        let root_chunks = (
            self.canonical_qualified_parent_by_root.chunks.len(),
            self.canonical_qualified_parent_by_root.chunks.capacity(),
        );
        let non_replay_entries = (
            self.non_replay_qualified_parents.entries.len(),
            self.non_replay_qualified_parents.entries.capacity(),
        );
        let non_replay_result_buckets = (
            self.non_replay_qualified_parents.by_result.len(),
            self.non_replay_qualified_parents.by_result.capacity(),
        );
        let capacity_inclusive_payload_bytes = arm_result_buckets.1
            * (std::mem::size_of::<ConstraintRecordId>()
                + std::mem::size_of::<ReplayQualifiedArmTree>())
            + arm_chunks.1 * std::mem::size_of::<ReplayQualifiedArmChunkNode>()
            + arm_entries.1 * std::mem::size_of::<ReplayFiniteMapEntryId>()
            + root_result_buckets.1
                * (std::mem::size_of::<ConstraintRecordId>()
                    + std::mem::size_of::<CanonicalQualifiedParentRootTree>())
            + root_chunks.1 * std::mem::size_of::<CanonicalQualifiedParentRootChunkNode>()
            + root_entries.1 * std::mem::size_of::<CanonicalQualifiedParentRootEntry>()
            + non_replay_entries.1 * std::mem::size_of::<ExactQualifiedParent>()
            + non_replay_result_buckets.1
                * (std::mem::size_of::<ConstraintRecordId>()
                    + std::mem::size_of::<Vec<NonReplayQualifiedParentId>>())
            + non_replay_result_ids.1 * std::mem::size_of::<NonReplayQualifiedParentId>();
        QorfD0ProjectionAllocationCensus {
            arm_result_buckets,
            arm_chunks,
            arm_entries,
            root_result_buckets,
            root_chunks,
            root_entries,
            non_replay_entries,
            non_replay_result_buckets,
            non_replay_result_ids,
            capacity_inclusive_payload_bytes,
        }
    }

    pub(super) fn contains_qualified_parent_carrier(
        &self,
        result: ConstraintRecordId,
        carrier: ProjectionProofCarrier,
    ) -> bool {
        self.qualified_parent_values_for_result(result)
            .any(|parent| match (parent, carrier) {
                (
                    ClaimQualifiedParent::ReplayConstraint { replay, .. },
                    ProjectionProofCarrier::ReplayConstraint { derivation, .. },
                ) => replay == derivation,
                (
                    ClaimQualifiedParent::StructuralConstraint { derivation, .. },
                    ProjectionProofCarrier::StructuralConstraint {
                        derivation: candidate,
                        ..
                    },
                ) => derivation == candidate,
                (
                    ClaimQualifiedParent::ReductionRouteConstraint { derivation, .. },
                    ProjectionProofCarrier::RowConstraint {
                        derivation: candidate,
                        ..
                    },
                ) => derivation == candidate,
                _ => false,
            })
    }

    #[cfg(test)]
    pub(super) fn qualified_parent_storage_census(&self) -> (usize, usize, usize, usize) {
        (
            self.qualified_parent_keys.len(),
            self.qualified_parent_keys.capacity(),
            self.qualified_parents_by_result.len(),
            self.qualified_parents_by_result.capacity(),
        )
    }

    pub(super) fn first_qualified_parent_source(
        &self,
        result: ConstraintRecordId,
        root: UpperReplayClaimId,
    ) -> Option<FirstQualifiedParentSource> {
        self.first_qualified_parent_source_by_root
            .get(&(result, root))
            .copied()
    }

    #[cfg(test)]
    pub(super) fn fail_next_qualified_parent_reservation(&mut self) {
        self.fail_next_qualified_parent_reservation = true;
    }

    #[cfg(test)]
    fn fail_qorf_replay_reservation_after(&mut self, point: QorfReplayReservationFailurePoint) {
        self.qorf_replay_reservation_failure_point = Some(point);
    }

    #[cfg(test)]
    fn reset_qorf_replay_side_operation_census(&self) {
        QORF_REPLAY_SIDE_OPERATION_CENSUS.with(|cell| cell.set(Default::default()));
    }

    #[cfg(test)]
    fn qorf_replay_side_operation_census(&self) -> QorfReplaySideOperationCensus {
        QORF_REPLAY_SIDE_OPERATION_CENSUS.with(Cell::get)
    }

    #[cfg(test)]
    fn qorf_replay_side_allocation_census(&self) -> (usize, usize, usize, usize, usize) {
        let side_count = self.replay_finite_map.len() * 2;
        let nonempty_sides = self
            .replay_finite_map
            .iter()
            .flat_map(|occurrence| occurrence.replay_parent_sides)
            .filter(|side| side.root.is_some())
            .count();
        let entry_count = self
            .replay_parent_chunks
            .nodes
            .iter()
            .map(|node| node.entries.len())
            .sum();
        (
            side_count,
            nonempty_sides,
            self.replay_parent_chunks.nodes.len(),
            self.replay_parent_chunks.nodes.capacity(),
            entry_count,
        )
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

    pub(super) fn dependency_entries(
        &self,
    ) -> impl Iterator<Item = (ProofPremise, &FxHashSet<BoundRecordId>)> {
        self.dependent_records_by_premise
            .iter()
            .map(|(premise, dependents)| (*premise, dependents))
    }

    pub(super) fn projection_records(&self) -> impl Iterator<Item = BoundRecordId> + '_ {
        self.projection_supports
            .keys()
            .chain(self.projection_formula_shadow.by_record.keys())
            .copied()
    }

    pub(super) fn projection_supports_for_record(
        &self,
        record: BoundRecordId,
    ) -> &[SchemeProjectionProofSupport] {
        self.projection_supports
            .get(&record)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub(super) fn projection_claims_for_record(
        &self,
        record: BoundRecordId,
    ) -> &[UpperReplayClaimId] {
        self.claimed_parents_by_lower_record
            .get(&record)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub(super) fn has_projection_support_ledger(&self, record: BoundRecordId) -> bool {
        self.projection_supports.contains_key(&record)
    }

    pub(super) fn projection_lower_records_for_root(
        &self,
        root: UpperReplayClaimId,
    ) -> &[BoundRecordId] {
        self.projection_lower_records_by_root
            .get(&root)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub(super) fn projection_owners(
        &self,
        view: &impl SemanticFactView,
    ) -> FxHashSet<TypeVar> {
        self.projection_supports
            .keys()
            .filter_map(|record| view.bound(*record).map(SemanticBoundRecordRef::owner))
            .collect()
    }

    pub(super) fn projection_formula_for_record(
        &self,
        record: BoundRecordId,
    ) -> ProjectionFormulaRecordCursor<'_> {
        self.projection_formula_shadow.by_record.get(&record).map_or(
            ProjectionFormulaRecordCursor {
                cursor: None,
                empty: true,
            },
            ProjectionFormulaBucket::canonical_clause_cursor,
        )
    }

    #[cfg(test)]
    pub(super) fn fail_next_projection_index_reservation(&mut self) {
        self.fail_next_projection_index_reservation = true;
    }

    #[cfg(test)]
    pub(super) fn fail_next_projection_support_reservation(&mut self) {
        self.fail_next_projection_support_reservation = true;
    }

    #[cfg(test)]
    pub(super) fn fail_next_projection_clause_reservation(&mut self) {
        self.projection_clause_reservation_failure_point =
            Some(ProjectionClauseReservationFailurePoint::Initial);
    }

    #[cfg(test)]
    fn fail_projection_clause_reservation_at_for_test(
        &mut self,
        point: ProjectionClauseReservationFailurePoint,
    ) {
        assert!(
            self.projection_clause_reservation_failure_point
                .replace(point)
                .is_none()
        );
    }

    #[cfg(test)]
    fn fail_projection_clause_canonical_run_reservation_after_for_test(
        &mut self,
        completed_run_reservations: usize,
    ) {
        assert!(
            self.projection_clause_canonical_run_reservation_failure_after
                .replace(completed_run_reservations)
                .is_none()
        );
    }

    #[cfg(test)]
    fn take_projection_clause_reservation_failure(
        &mut self,
        point: ProjectionClauseReservationFailurePoint,
    ) -> bool {
        if self.projection_clause_reservation_failure_point == Some(point) {
            self.projection_clause_reservation_failure_point = None;
            true
        } else {
            false
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

fn qorf_occurrence_first_exact_parent(
    occurrences: &[ReplayProofOccurrence],
    chunks: &ReplayParentChunkArena,
    occurrence: ReplayFiniteMapEntryId,
) -> ExactQualifiedParent {
    let occurrence = &occurrences[occurrence.0 as usize];
    [
        (
            ReplayClaimParentSide::Lower,
            occurrence.replay_parent_sides[0],
        ),
        (
            ReplayClaimParentSide::Upper,
            occurrence.replay_parent_sides[1],
        ),
    ]
    .into_iter()
    .filter_map(|(side, index)| {
        let root = index.root?;
        let mut node = root;
        while let Some(left) = chunks.node(node).left {
            node = left;
        }
        let entry = chunks.node(node).entries[0];
        Some(ExactQualifiedParent {
            coverage_root: entry.coverage_root,
            parent: ClaimQualifiedParent::ReplayConstraint {
                parent_claim: entry.representative_claim,
                parent_side: side,
                replay: occurrence.carrier,
            },
        })
    })
    .min_by(qualified_parent_entry_cmp)
    .expect("QORF arm occurrence must have a nonempty side")
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

fn merge_qualified_parent_entries(
    entries: &mut Vec<ExactQualifiedParent>,
    incoming: &[ExactQualifiedParent],
) {
    // Preparation reserves the incoming tail before any proof fact commits. Merge the two strict
    // canonical runs backward so unread existing entries are never overwritten and commit needs
    // neither another allocation nor a full-bucket re-sort.
    debug_assert!(entries.capacity() - entries.len() >= incoming.len());
    debug_assert!(entries
        .windows(2)
        .all(|pair| qualified_parent_entry_cmp(&pair[0], &pair[1]).is_lt()));
    debug_assert!(incoming
        .windows(2)
        .all(|pair| qualified_parent_entry_cmp(&pair[0], &pair[1]).is_lt()));
    if incoming.is_empty() {
        return;
    }

    #[cfg(test)]
    let expected = {
        let mut expected = entries.clone();
        expected.extend_from_slice(incoming);
        expected.sort_unstable_by(qualified_parent_entry_cmp);
        expected
    };

    let existing_len = entries.len();
    entries.extend_from_slice(incoming);
    let mut existing = existing_len;
    let mut added = incoming.len();
    let mut output = entries.len();
    while existing > 0 && added > 0 {
        let existing_entry = entries[existing - 1];
        let added_entry = incoming[added - 1];
        let ordering = qualified_parent_entry_cmp(&existing_entry, &added_entry);
        debug_assert_ne!(
            ordering,
            std::cmp::Ordering::Equal,
            "qualified-parent identity dedup must make canonical entries strictly ordered",
        );
        if ordering.is_gt() {
            entries[output - 1] = existing_entry;
            existing -= 1;
        } else {
            entries[output - 1] = added_entry;
            added -= 1;
        }
        output -= 1;
    }
    if added > 0 {
        entries[..added].copy_from_slice(&incoming[..added]);
    }

    #[cfg(test)]
    debug_assert_eq!(
        *entries, expected,
        "incremental qualified-parent merge must equal a full canonical re-sort",
    );
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
        ProofSoakEventOrigin, capture_proof_soak_test_events,
        with_intentional_proof_soak_test_injection,
    };

    fn cpk_machine() -> ConstraintMachine {
        ConstraintMachine::new()
    }

    #[derive(Debug, Clone)]
    struct QorfModelChunkNode<K> {
        entries: Vec<K>,
        left: Option<usize>,
        right: Option<usize>,
        height: u8,
    }

    /// Test-only executable model for all three QORF chunk-AVL projections. Production does not
    /// call this implementation; later slices must match its flattening and bounded-chunk rules.
    #[derive(Debug, Clone)]
    struct QorfModelChunkAvl<K, const CAPACITY: usize> {
        root: Option<usize>,
        nodes: Vec<QorfModelChunkNode<K>>,
        len: usize,
        max_scanned_existing_per_insert: usize,
        total_scanned_existing: usize,
    }

    impl<K: Copy + Ord + std::fmt::Debug, const CAPACITY: usize> QorfModelChunkAvl<K, CAPACITY> {
        fn new() -> Self {
            assert!(CAPACITY >= 2);
            Self {
                root: None,
                nodes: Vec::new(),
                len: 0,
                max_scanned_existing_per_insert: 0,
                total_scanned_existing: 0,
            }
        }

        fn height(&self, node: Option<usize>) -> u8 {
            node.map_or(0, |id| self.nodes[id].height)
        }

        fn update_height(&mut self, id: usize) {
            self.nodes[id].height = 1 + self
                .height(self.nodes[id].left)
                .max(self.height(self.nodes[id].right));
        }

        fn rotate_left(&mut self, root: usize) -> usize {
            let pivot = self.nodes[root]
                .right
                .expect("left rotation needs a right child");
            let middle = self.nodes[pivot].left;
            self.nodes[root].right = middle;
            self.nodes[pivot].left = Some(root);
            self.update_height(root);
            self.update_height(pivot);
            pivot
        }

        fn rotate_right(&mut self, root: usize) -> usize {
            let pivot = self.nodes[root]
                .left
                .expect("right rotation needs a left child");
            let middle = self.nodes[pivot].right;
            self.nodes[root].left = middle;
            self.nodes[pivot].right = Some(root);
            self.update_height(root);
            self.update_height(pivot);
            pivot
        }

        fn rebalance(&mut self, root: usize) -> usize {
            self.update_height(root);
            let balance = i16::from(self.height(self.nodes[root].left))
                - i16::from(self.height(self.nodes[root].right));
            if balance > 1 {
                let left = self.nodes[root].left.expect("left-heavy node has a child");
                if self.height(self.nodes[left].right) > self.height(self.nodes[left].left) {
                    let rotated = self.rotate_left(left);
                    self.nodes[root].left = Some(rotated);
                }
                return self.rotate_right(root);
            }
            if balance < -1 {
                let right = self.nodes[root]
                    .right
                    .expect("right-heavy node has a child");
                if self.height(self.nodes[right].left) > self.height(self.nodes[right].right) {
                    let rotated = self.rotate_right(right);
                    self.nodes[root].right = Some(rotated);
                }
                return self.rotate_left(root);
            }
            root
        }

        fn insert_chunk_node(&mut self, root: Option<usize>, incoming: usize) -> usize {
            let Some(root) = root else {
                return incoming;
            };
            let incoming_min = self.nodes[incoming].entries[0];
            let root_min = self.nodes[root].entries[0];
            if incoming_min < root_min {
                let child = self.insert_chunk_node(self.nodes[root].left, incoming);
                self.nodes[root].left = Some(child);
            } else {
                let child = self.insert_chunk_node(self.nodes[root].right, incoming);
                self.nodes[root].right = Some(child);
            }
            self.rebalance(root)
        }

        fn target_chunk(&self, key: K) -> Option<usize> {
            let mut current = self.root?;
            loop {
                let node = &self.nodes[current];
                if key < node.entries[0] {
                    if let Some(left) = node.left {
                        current = left;
                        continue;
                    }
                } else if key > *node.entries.last().expect("chunks are nonempty") {
                    if let Some(right) = node.right {
                        current = right;
                        continue;
                    }
                }
                return Some(current);
            }
        }

        fn insert(&mut self, key: K) -> bool {
            let Some(target) = self.target_chunk(key) else {
                self.nodes.push(QorfModelChunkNode {
                    entries: vec![key],
                    left: None,
                    right: None,
                    height: 1,
                });
                self.root = Some(0);
                self.len = 1;
                return true;
            };
            let position = match self.nodes[target].entries.binary_search(&key) {
                Ok(_) => return false,
                Err(position) => position,
            };
            let scanned = self.nodes[target].entries.len();
            self.max_scanned_existing_per_insert =
                self.max_scanned_existing_per_insert.max(scanned);
            self.total_scanned_existing += scanned;
            if scanned < CAPACITY {
                self.nodes[target].entries.insert(position, key);
                self.len += 1;
                return true;
            }
            let mut merged = Vec::with_capacity(CAPACITY + 1);
            merged.extend_from_slice(&self.nodes[target].entries[..position]);
            merged.push(key);
            merged.extend_from_slice(&self.nodes[target].entries[position..]);
            let right_entries = merged.split_off(merged.len() / 2);
            self.nodes[target].entries = merged;
            let incoming = self.nodes.len();
            self.nodes.push(QorfModelChunkNode {
                entries: right_entries,
                left: None,
                right: None,
                height: 1,
            });
            self.root = Some(self.insert_chunk_node(self.root, incoming));
            self.len += 1;
            true
        }

        fn remove_chunk_node(&mut self, root: Option<usize>, minimum: K) -> Option<usize> {
            let root = root?;
            let root_minimum = self.nodes[root].entries[0];
            if minimum < root_minimum {
                self.nodes[root].left = self.remove_chunk_node(self.nodes[root].left, minimum);
                return Some(self.rebalance(root));
            }
            if minimum > root_minimum {
                self.nodes[root].right = self.remove_chunk_node(self.nodes[root].right, minimum);
                return Some(self.rebalance(root));
            }
            match (self.nodes[root].left, self.nodes[root].right) {
                (None, right) => right,
                (left, None) => left,
                (Some(_), Some(right)) => {
                    let mut successor = right;
                    while let Some(left) = self.nodes[successor].left {
                        successor = left;
                    }
                    let successor_minimum = self.nodes[successor].entries[0];
                    self.nodes[root].entries = self.nodes[successor].entries.clone();
                    self.nodes[root].right =
                        self.remove_chunk_node(self.nodes[root].right, successor_minimum);
                    Some(self.rebalance(root))
                }
            }
        }

        fn remove(&mut self, key: K) -> bool {
            let Some(target) = self.target_chunk(key) else {
                return false;
            };
            let Ok(position) = self.nodes[target].entries.binary_search(&key) else {
                return false;
            };
            if self.nodes[target].entries.len() > 1 {
                self.nodes[target].entries.remove(position);
            } else {
                let minimum = self.nodes[target].entries[0];
                self.root = self.remove_chunk_node(self.root, minimum);
            }
            self.len -= 1;
            true
        }

        fn rekey(&mut self, old: K, new: K) -> bool {
            if old == new
                || self
                    .target_chunk(new)
                    .is_some_and(|id| self.nodes[id].entries.binary_search(&new).is_ok())
            {
                return false;
            }
            if !self.remove(old) {
                return false;
            }
            assert!(self.insert(new));
            true
        }

        fn flatten(&self) -> Vec<K> {
            fn append<K: Copy, const CAPACITY: usize>(
                tree: &QorfModelChunkAvl<K, CAPACITY>,
                node: Option<usize>,
                output: &mut Vec<K>,
            ) {
                let Some(node) = node else { return };
                append(tree, tree.nodes[node].left, output);
                output.extend_from_slice(&tree.nodes[node].entries);
                append(tree, tree.nodes[node].right, output);
            }
            let mut output = Vec::with_capacity(self.len);
            append(self, self.root, &mut output);
            output
        }

        fn assert_invariants(&self) {
            fn check<K: Copy + Ord + std::fmt::Debug, const CAPACITY: usize>(
                tree: &QorfModelChunkAvl<K, CAPACITY>,
                node: Option<usize>,
                previous: &mut Option<K>,
            ) -> u8 {
                let Some(node) = node else { return 0 };
                let current = &tree.nodes[node];
                assert!(!current.entries.is_empty());
                assert!(current.entries.len() <= CAPACITY);
                assert!(current.entries.windows(2).all(|pair| pair[0] < pair[1]));
                let left_height = check(tree, current.left, previous);
                for &entry in &current.entries {
                    if let Some(previous) = *previous {
                        assert!(previous < entry, "chunk ranges must be strictly ordered");
                    }
                    *previous = Some(entry);
                }
                let right_height = check(tree, current.right, previous);
                assert!((i16::from(left_height) - i16::from(right_height)).abs() <= 1);
                let expected = 1 + left_height.max(right_height);
                assert_eq!(current.height, expected);
                expected
            }
            let mut previous = None;
            check(self, self.root, &mut previous);
            assert_eq!(self.flatten().len(), self.len);
        }
    }


    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    enum Gwcb0NormalizedClause {
        Standalone {
            embedded_support: ProjectionSupportMatchKey,
        },
        DerivedUnary {
            carrier: DerivedUnaryCarrier,
            premise: ProofPremise,
        },
        ReplayConjunction {
            carrier: BinaryReplayDerivation,
            lower: BoundRecordId,
            upper: BoundRecordId,
        },
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    struct Gwcb0NormalizedClaimedLinkKey {
        record: BoundRecordId,
        support: ProjectionSupportMatchKey,
        clause: Gwcb0NormalizedClause,
    }

    fn gwcb0_normalized_claimed_link_key(
        store: &ProofOccurrenceStore,
        record: BoundRecordId,
        support: SchemeProjectionProofSupport,
        clause: RecordProofClause,
    ) -> Option<Gwcb0NormalizedClaimedLinkKey> {
        let support = store.projection_support_match_key(support)?;
        if !matches!(support, ProjectionSupportMatchKey::Claimed(_)) {
            return None;
        }
        let clause = match clause {
            RecordProofClause::Standalone { support } => Gwcb0NormalizedClause::Standalone {
                embedded_support: store.projection_support_match_key(support)?,
            },
            RecordProofClause::DerivedUnary { carrier, premise } => {
                Gwcb0NormalizedClause::DerivedUnary { carrier, premise }
            }
            RecordProofClause::ReplayConjunction {
                carrier,
                lower_premise,
                upper_premise,
            } => Gwcb0NormalizedClause::ReplayConjunction {
                carrier,
                lower: lower_premise,
                upper: upper_premise,
            },
        };
        Some(Gwcb0NormalizedClaimedLinkKey {
            record,
            support,
            clause,
        })
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Gwcb0WriterCertificateMetadata {
        Original {
            producer: ConstraintRecordId,
        },
        ReplayConstraint {
            result: ConstraintRecordId,
        },
        ReplayEvidence,
        DerivedUnary {
            result: ConstraintRecordId,
            premise: ProofPremise,
        },
    }

    fn gwcb0_test_writer_with_explicit_metadata(
        admission: RecordProofClauseLinkAdmission,
        metadata: Gwcb0WriterCertificateMetadata,
    ) -> (RecordProofClauseLinkAdmission, Gwcb0WriterCertificateMetadata) {
        match (admission.clause, metadata) {
            (
                RecordProofClause::Standalone { .. },
                Gwcb0WriterCertificateMetadata::Original { .. },
            )
            | (
                RecordProofClause::ReplayConjunction { .. },
                Gwcb0WriterCertificateMetadata::ReplayConstraint { .. }
                    | Gwcb0WriterCertificateMetadata::ReplayEvidence,
            ) => {}
            (
                RecordProofClause::DerivedUnary { premise, .. },
                Gwcb0WriterCertificateMetadata::DerivedUnary {
                    premise: supplied, ..
                },
            ) => assert_eq!(premise, supplied, "test metadata must be supplied, not inferred"),
            pair => panic!("clause/metadata mismatch in GWCB-0 test writer: {pair:?}"),
        }
        (admission, metadata)
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Gwcb0RawTrueBranch {
        // Valid recursive base cases, not corruption evidence.
        Tombstone,
        UpperWithoutClaims,
        ConstraintWithoutSource,
        // Inclusion shortcuts that cannot yield an exact top-level clause arm.
        MissingBound,
        MissingSupports,
        EmptySupports,
        QualifyingSupportAbsentFromFormulaMirror,
        MissingConstraint,
        MissingClaimOrCoverageRoot,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Gwcb0EvidenceObservation {
        ExactWithoutClaimedArm,
        FailOpenIncomplete(Gwcb0RawTrueBranch),
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

    fn projection_evidence_for_test(
        machine: &ConstraintMachine,
        record: BoundRecordId,
    ) -> ProjectionEvidence {
        let mut evaluator = CpkProjectionEvaluator::new(machine, &machine.proof_store);
        match evaluator
            .eval_preflighted_record_with_evidence(record)
            .expect("test projection evidence must be available")
        {
            CpkProjectionEvaluation::Included { evidence } => evidence,
            CpkProjectionEvaluation::Excluded => {
                panic!("included test fixture must have projection evidence")
            }
        }
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

    #[test]
    fn cpk_result_bucket_indexes_mirror_replay_and_dependency_raw_facts() {
        let mut machine = cpk_machine();
        let (lower, first_claim) = cpk_7_record_original_claim(&mut machine, 97_100);
        let (upper, second_claim) = cpk_7_record_original_claim(&mut machine, 97_101);
        let result = ConstraintRecordId(97_102);
        let replay = BinaryReplayDerivation {
            pivot: TypeVar(97_103),
            lower,
            upper,
            rule: ReplayRule::LowerBoundAdded,
        };
        machine.proof_store.record_cpk_replay_parent_snapshot(
            result,
            replay,
            &[SideTaggedReplayClaim {
                claim: first_claim,
                parent_side: ReplayClaimParentSide::Lower,
            }],
        );
        machine.proof_store.record_cpk_replay_parent_snapshot(
            result,
            replay,
            &[SideTaggedReplayClaim {
                claim: second_claim,
                parent_side: ReplayClaimParentSide::Upper,
            }],
        );
        let indexes_before_duplicate = machine.proof_store.performance_index_allocation_census();
        machine.proof_store.record_cpk_replay_parent_snapshot(
            result,
            replay,
            &[SideTaggedReplayClaim {
                claim: second_claim,
                parent_side: ReplayClaimParentSide::Upper,
            }],
        );
        assert_eq!(
            machine
                .proof_store
                .performance_index_allocation_census(),
            indexes_before_duplicate,
            "an exact replay-parent duplicate must not grow either result-bucket index",
        );

        let structural = StructuralDerivation {
            parent: ConstraintRecordId(97_104),
            rule: StructuralDerivationRule::FunctionReturn,
        };
        machine.proof_store.record_structural(result, structural);
        machine
            .proof_store
            .record_reduction_route(result, RowDerivationId(97_105), first_claim);
        machine
            .proof_store
            .record_constraint_root(result, OriginId::unknown_internal());

        machine
            .proof_store
            .debug_assert_result_bucket_indexes_match_linear_scans();
        assert_eq!(machine.proof_store.replay_indices_by_result[&result], [0]);
        let dependency_indices =
            &machine.proof_store.dependency_occurrence_indices_by_result[&result];
        assert_eq!(dependency_indices.len(), 2);
        assert!(matches!(
            machine.proof_store.occurrences[dependency_indices[0]].cause,
            ProofCause::Structural(candidate) if candidate == structural
        ));
        assert!(matches!(
            machine.proof_store.occurrences[dependency_indices[1]].cause,
            ProofCause::ReductionRoute {
                derivation: RowDerivationId(97_105),
                parent_claim,
            } if parent_claim == first_claim
        ));
    }

    #[test]
    fn cpk_occurrence_membership_indexes_mirror_carriers_and_row_derivations() {
        let mut store = ProofOccurrenceStore::default();
        let result = ConstraintRecordId(97_106);
        let origin = OriginId(97_107);
        let parent_origin = OriginId(97_108);
        let structural = StructuralDerivation {
            parent: ConstraintRecordId(97_109),
            rule: StructuralDerivationRule::FunctionReturn,
        };
        let row = RowDerivationId(97_110);
        let witness = GeneralizedSchemeWitnessId(97_111);
        let instantiation = SchemeInstantiationDerivation {
            instantiation: SchemeInstantiationId(97_112),
            source_witness: witness,
            path: GeneralizedTypePath::default(),
        };
        let replay = BinaryReplayDerivation {
            pivot: TypeVar(97_113),
            lower: BoundRecordId(97_114),
            upper: BoundRecordId(97_115),
            rule: ReplayRule::LowerBoundAdded,
        };

        store.record_constraint_root(result, origin);
        store.record_structural(result, structural);
        store.record_row_definition(
            row,
            RowDerivation {
                rule: RowDerivationRule::RowItemMatch,
                parents: vec![RowDerivationParent::Origin(parent_origin)],
                retained_items: Vec::new(),
            },
        );
        store.record_row_constraint(result, row);
        store.record_scheme_instantiation_derivation(result, instantiation);
        store.record_replay_evidence(BoundRecordId(97_116), replay);

        store.debug_assert_occurrence_membership_indexes_match_linear_scans();
        for carrier in [
            ProjectionProofCarrier::ConstraintOrigin {
                constraint: result,
                origin,
            },
            ProjectionProofCarrier::StructuralConstraint {
                result,
                derivation: structural,
            },
            ProjectionProofCarrier::RowConstraint {
                result,
                derivation: row,
            },
            ProjectionProofCarrier::SchemeInstantiationConstraint {
                result,
                source_witness: witness,
            },
            ProjectionProofCarrier::Origin(origin),
            ProjectionProofCarrier::Origin(parent_origin),
            ProjectionProofCarrier::ReplayEvidence(replay),
            ProjectionProofCarrier::SchemeInstantiation(witness),
        ] {
            assert!(store.projection_carrier_occurrence(carrier).is_some());
        }
        assert!(store.row_derivation_occurrence(row).is_some());
        assert_eq!(store.projection_carrier_occurrence_index.len(), 8);
        assert_eq!(store.row_derivation_occurrence_index.len(), 1);
    }

    #[test]
    fn pclf_a_per_incidence_sources_are_lossless_across_conflicts_and_permutations() {
        let record = BoundRecordId(97_080);
        let replay = BinaryReplayDerivation {
            pivot: TypeVar(97_081),
            lower: BoundRecordId(97_082),
            upper: BoundRecordId(97_083),
            rule: ReplayRule::LowerBoundAdded,
        };
        let replay_clause = RecordProofClause::ReplayConjunction {
            carrier: replay,
            lower_premise: replay.lower,
            upper_premise: replay.upper,
        };
        let derived_clause = RecordProofClause::DerivedUnary {
            carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                parent: ConstraintRecordId(97_084),
                rule: StructuralDerivationRule::FunctionReturn,
            }),
            premise: ProofPremise::Constraint(ConstraintRecordId(97_084)),
        };
        let claimed = |claim, clause, attribution, source| {
            RecordProofClauseLinkAdmission::claimed(claim, clause, attribution, source)
        };
        let admissions = [
            claimed(
                UpperReplayClaimId(97_085),
                replay_clause,
                ClaimedAttributionSource::CanonicalReplay,
                ClaimedProjectionProofSource::ReplayConstraint {
                    coverage_root: UpperReplayClaimId(97_085),
                    result: ConstraintRecordId(97_090),
                },
            ),
            claimed(
                UpperReplayClaimId(97_086),
                replay_clause,
                ClaimedAttributionSource::FlatRetained,
                ClaimedProjectionProofSource::ReplayEvidence {
                    coverage_root: UpperReplayClaimId(97_086),
                },
            ),
            claimed(
                UpperReplayClaimId(97_087),
                replay_clause,
                ClaimedAttributionSource::CanonicalReplay,
                ClaimedProjectionProofSource::ReplayConstraint {
                    coverage_root: UpperReplayClaimId(97_087),
                    result: ConstraintRecordId(97_091),
                },
            ),
            claimed(
                UpperReplayClaimId(97_088),
                derived_clause,
                ClaimedAttributionSource::FlatRetained,
                ClaimedProjectionProofSource::DerivedUnary {
                    coverage_root: UpperReplayClaimId(97_088),
                    result: ConstraintRecordId(97_092),
                },
            ),
            claimed(
                UpperReplayClaimId(97_089),
                derived_clause,
                ClaimedAttributionSource::FlatRetained,
                ClaimedProjectionProofSource::DerivedUnary {
                    coverage_root: UpperReplayClaimId(97_089),
                    result: ConstraintRecordId(97_093),
                },
            ),
            claimed(
                UpperReplayClaimId(97_094),
                RecordProofClause::Standalone {
                    support: SchemeProjectionProofSupport::Claimed(UpperReplayClaimId(97_094)),
                },
                ClaimedAttributionSource::FlatRetained,
                ClaimedProjectionProofSource::Original {
                    coverage_root: UpperReplayClaimId(97_094),
                    producer: ConstraintRecordId(97_095),
                },
            ),
        ];

        let mut snapshots = Vec::new();
        for order in [
            [0usize, 1, 2, 3, 4, 5],
            [5usize, 4, 3, 2, 1, 0],
            [1usize, 3, 5, 0, 4, 2],
        ] {
            let mut store = ProofOccurrenceStore::default();
            for index in order {
                store.record_projection_clause(record, admissions[index]);
            }
            for admission in admissions {
                assert_eq!(
                    store.projection_clause_link_is_registered(
                        record,
                        admission.support,
                        admission.clause,
                    ),
                    store.legacy_projection_clause_link_is_registered_for_test(
                        record,
                        admission.support,
                        admission.clause,
                    ),
                    "factored membership must preserve every rev.2 source-conflict incidence",
                );
                assert_eq!(
                    store.projection_clause_is_registered(record, admission.clause),
                    store.legacy_projection_clause_is_registered_for_test(
                        record,
                        admission.clause,
                    ),
                );
            }
            store.debug_assert_pclf_a_read_model_matches_legacy();
            let factored = ProjectionFormulaStore::from_legacy(&store);
            let bucket = &factored.by_record[&record];
            assert_eq!(bucket.entries.len(), 3, "clause bodies are stored once");
            assert_eq!(bucket.exact_links.len(), admissions.len());
            assert_eq!(
                bucket
                    .exact_links
                    .values()
                    .filter(|metadata| matches!(
                        metadata,
                        ProjectionIncidenceMetadata::Claimed(
                            ClaimedProjectionSourceTemplate::ReplayConstraint { .. }
                        )
                    ))
                    .count(),
                2,
            );
            assert!(bucket.exact_links.values().any(|metadata| matches!(
                metadata,
                ProjectionIncidenceMetadata::Claimed(
                    ClaimedProjectionSourceTemplate::ReplayEvidence
                )
            )));
            let mut replay_results = bucket
                .exact_links
                .values()
                .filter_map(|metadata| match metadata {
                    ProjectionIncidenceMetadata::Claimed(
                        ClaimedProjectionSourceTemplate::ReplayConstraint { result },
                    ) => Some(*result),
                    _ => None,
                })
                .collect::<Vec<_>>();
            replay_results.sort_unstable_by_key(|result| result.0);
            assert_eq!(
                replay_results,
                vec![ConstraintRecordId(97_090), ConstraintRecordId(97_091)],
            );
            let mut derived_results = bucket
                .exact_links
                .values()
                .filter_map(|metadata| match metadata {
                    ProjectionIncidenceMetadata::Claimed(
                        ClaimedProjectionSourceTemplate::DerivedUnary { result },
                    ) => Some(*result),
                    _ => None,
                })
                .collect::<Vec<_>>();
            derived_results.sort_unstable_by_key(|result| result.0);
            assert_eq!(
                derived_results,
                vec![ConstraintRecordId(97_092), ConstraintRecordId(97_093)],
            );
            snapshots.push(store.legacy_projection_formula_read_model());
        }
        assert_eq!(snapshots[0], snapshots[1]);
        assert_eq!(snapshots[0], snapshots[2]);
    }

    #[test]
    fn pclf_a_exact_and_batch_duplicates_cover_support_clause_delta_matrix() {
        let mut store = ProofOccurrenceStore::default();
        let record = BoundRecordId(97_096);
        let support = |ordinal| {
            SchemeProjectionProofSupport::Independent(ProjectionProofCarrier::Origin(OriginId(
                ordinal,
            )))
        };
        let clause = |ordinal| {
            let carrier = BinaryReplayDerivation {
                pivot: TypeVar(ordinal),
                lower: BoundRecordId(ordinal + 1),
                upper: BoundRecordId(ordinal + 2),
                rule: ReplayRule::LowerBoundAdded,
            };
            RecordProofClause::ReplayConjunction {
                carrier,
                lower_premise: carrier.lower,
                upper_premise: carrier.upper,
            }
        };
        let first = RecordProofClauseLinkAdmission::independent(support(97_100), clause(97_110));
        store.record_projection_clause(record, first);
        let batch = [
            first,
            RecordProofClauseLinkAdmission::independent(support(97_101), clause(97_110)),
            RecordProofClauseLinkAdmission::independent(support(97_100), clause(97_120)),
            RecordProofClauseLinkAdmission::independent(support(97_102), clause(97_130)),
            RecordProofClauseLinkAdmission::independent(support(97_102), clause(97_130)),
        ];
        let mut prepared = store
            .try_prepare_projection_clause_admission(record, &batch)
            .expect("PCLF-A delta matrix must reserve")
            .expect("three exact links are new");
        assert_eq!(prepared.accepted().len(), 3);
        assert_eq!(
            prepared
                .accepted()
                .iter()
                .map(|event| event.admission)
                .collect::<Vec<_>>(),
            vec![batch[1], batch[2], batch[3]],
            "existing and batch-local duplicates must retain their legacy classifications",
        );
        assert_eq!(
            prepared
                .accepted()
                .iter()
                .map(|event| event.clause_inserted)
                .collect::<Vec<_>>(),
            vec![false, true, true],
        );
        store.commit_projection_clause_admission(&mut prepared);
        store.debug_assert_pclf_a_read_model_matches_legacy();
        for admission in [first, batch[1], batch[2], batch[3]] {
            assert_eq!(
                store.projection_clause_link_is_registered(
                    record,
                    admission.support,
                    admission.clause,
                ),
                store.legacy_projection_clause_link_is_registered_for_test(
                    record,
                    admission.support,
                    admission.clause,
                ),
            );
            assert_eq!(
                store.projection_clause_is_registered(record, admission.clause),
                store.legacy_projection_clause_is_registered_for_test(
                    record,
                    admission.clause,
                ),
            );
        }
        assert_eq!(store.projection_formulas[&record].len(), 4);
        assert_eq!(store.projection_clause_keys.len(), 3);
    }

    #[test]
    fn pclf_c_one_membership_probe_answers_exact_and_distinct_queries() {
        const QUERIES: usize = 256;
        let mut store = ProofOccurrenceStore::default();
        let record = BoundRecordId(97_163);
        let target_support = SchemeProjectionProofSupport::Independent(
            ProjectionProofCarrier::Origin(OriginId(97_164)),
        );
        let clause = RecordProofClause::Standalone {
            support: target_support,
        };
        store.record_projection_clause(
            record,
            RecordProofClauseLinkAdmission::independent(target_support, clause),
        );
        store.debug_assert_pclf_a_read_model_matches_legacy();

        store.reset_projection_clause_membership_census_for_test();
        for _ in 0..QUERIES {
            let membership = std::hint::black_box(
                store.projection_clause_membership(record, target_support, clause),
            );
            assert!(membership.exact_link_registered);
            assert!(membership.clause_registered);
        }
        assert_eq!(
            store.projection_clause_membership_census_for_test(),
            ProjectionClauseMembershipCensus {
                membership_queries: QUERIES,
                record_bucket_hash_lookups: QUERIES,
                support_hash_lookups: QUERIES,
                clause_hash_lookups: QUERIES,
                incidence_hash_lookups: QUERIES,
            },
            "one fixed probe sequence must answer both exact-link and distinct-clause membership",
        );
    }

    #[test]
    fn pclf_a_canonical_read_model_preserves_category_and_suffix_order() {
        let mut store = ProofOccurrenceStore::default();
        let record = BoundRecordId(97_140);
        let support = SchemeProjectionProofSupport::Independent(
            ProjectionProofCarrier::Incomplete,
        );
        let replay = BinaryReplayDerivation {
            pivot: TypeVar(97_141),
            lower: BoundRecordId(97_142),
            upper: BoundRecordId(97_143),
            rule: ReplayRule::UpperBoundAdded,
        };
        for admission in [
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::ReplayConjunction {
                    carrier: replay,
                    lower_premise: replay.lower,
                    upper_premise: replay.upper,
                },
            ),
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::ReductionRoute(RowDerivationId(97_144)),
                    premise: ProofPremise::Record(BoundRecordId(97_145)),
                },
            ),
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::Standalone { support },
            ),
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                        parent: ConstraintRecordId(97_146),
                        rule: StructuralDerivationRule::FunctionArgument,
                    }),
                    premise: ProofPremise::Constraint(ConstraintRecordId(97_146)),
                },
            ),
        ] {
            store.record_projection_clause(record, admission);
        }
        store.debug_assert_pclf_a_read_model_matches_legacy();
        let factored = ProjectionFormulaStore::from_legacy(&store);
        assert_eq!(
            factored.by_record[&record].canonical_clauses(),
            store.projection_formulas[&record],
        );
        let bucket = &store.projection_formula_shadow.by_record[&record];
        assert!(bucket.canonical_runs.iter().all(|run| {
            run.entry_len > 0
                && run.chunks_are_nonempty_and_bounded()
                && run.chunk_tree_is_balanced()
        }));
        let run_keys = bucket
            .canonical_runs
            .iter()
            .map(|run| (run.category, run.support_id))
            .collect::<FxHashSet<_>>();
        assert_eq!(run_keys.len(), bucket.canonical_runs.len());
        assert_eq!(
            bucket
                .canonical_runs
                .iter()
                .map(|run| run.entry_len)
                .sum::<usize>(),
            bucket.exact_links.len(),
        );
        assert_eq!(bucket.canonical_runs.len(), 3);
    }

    #[test]
    fn pclf_d1_evaluator_items_match_legacy_clauses_in_canonical_order() {
        let mut store = ProofOccurrenceStore::default();
        let record = BoundRecordId(97_168);
        let support = SchemeProjectionProofSupport::Independent(
            ProjectionProofCarrier::Incomplete,
        );
        let replay = BinaryReplayDerivation {
            pivot: TypeVar(97_169),
            lower: BoundRecordId(97_170),
            upper: BoundRecordId(97_171),
            rule: ReplayRule::UpperBoundAdded,
        };
        for admission in [
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::ReplayConjunction {
                    carrier: replay,
                    lower_premise: replay.lower,
                    upper_premise: replay.upper,
                },
            ),
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::ReductionRoute(RowDerivationId(97_172)),
                    premise: ProofPremise::Record(BoundRecordId(97_173)),
                },
            ),
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::Standalone { support },
            ),
        ] {
            store.record_projection_clause(record, admission);
        }

        let bucket = &store.projection_formula_shadow.by_record[&record];
        let mut cursor = bucket.canonical_run_cursor();
        let mut factored_items = Vec::new();
        while let Some((support_id, entry_id)) = cursor.next() {
            factored_items.push((
                bucket.evaluation_item(support_id, entry_id),
                bucket.reconstructed_clause(support_id, entry_id),
            ));
        }
        assert_eq!(
            factored_items
                .iter()
                .map(|(_, clause)| *clause)
                .collect::<Vec<_>>(),
            store.projection_formulas[&record],
            "the evaluator cursor must expose the byte-identical legacy clause sequence",
        );

        let machine = ConstraintMachine::new();
        for (item, legacy_clause) in factored_items {
            let mut factored = CpkProjectionEvaluator::new(&machine, &store)
                .with_record_result_override(replay.lower, true)
                .with_record_result_override(replay.upper, false)
                .with_record_result_override(BoundRecordId(97_173), true);
            let mut legacy = CpkProjectionEvaluator::new(&machine, &store)
                .with_record_result_override(replay.lower, true)
                .with_record_result_override(replay.upper, false)
                .with_record_result_override(BoundRecordId(97_173), true);
            assert_eq!(
                factored.eval_formula_item(item),
                legacy.eval_clause(legacy_clause),
                "factored evaluator items must preserve legacy per-clause semantics",
            );
        }
    }

    #[test]
    fn pclf_d0_large_single_run_repeated_small_admissions_bounds_writer_cost() {
        const LINKS: u32 = 1_800;
        let mut store = ProofOccurrenceStore::default();
        let record = BoundRecordId(97_170);
        let support = SchemeProjectionProofSupport::Independent(
            ProjectionProofCarrier::Origin(OriginId(97_171)),
        );
        for ordinal in (0..LINKS).rev() {
            let parent = ConstraintRecordId(100_000 + ordinal);
            store.record_projection_clause(
                record,
                RecordProofClauseLinkAdmission::independent(
                    support,
                    RecordProofClause::DerivedUnary {
                        carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                            parent,
                            rule: StructuralDerivationRule::FunctionReturn,
                        }),
                        premise: ProofPremise::Constraint(parent),
                    },
                ),
            );
        }
        store.debug_assert_pclf_a_read_model_matches_legacy();
        let bucket = &store.projection_formula_shadow.by_record[&record];
        assert_eq!(bucket.canonical_runs.len(), 1);
        assert_eq!(bucket.canonical_runs[0].entry_len, LINKS as usize);
        assert!(bucket.canonical_runs[0].chunks_are_nonempty_and_bounded());
        assert!(bucket.canonical_runs[0].chunk_tree_is_balanced());
        assert_eq!(bucket.canonical_clauses(), store.projection_formulas[&record]);
        let movement = store.projection_formula_shadow.movement;
        assert_eq!(movement.merge_calls, u64::from(LINKS - 1));
        assert_eq!(movement.merge_comparisons, 2 * u64::from(LINKS - 1));
        assert_eq!(movement.merge_scanned_entries, 2 * u64::from(LINKS - 1));
        assert!(movement.merge_max_scanned_entries <= PROJECTION_RUN_CHUNK_CAPACITY);
        assert!(
            movement.merge_moved_entries
                <= u64::from(LINKS - 1) * (PROJECTION_RUN_CHUNK_CAPACITY as u64 + 1)
        );
        assert!(movement.chunk_lookup_comparisons < u64::from(LINKS) * 16);
        assert!(movement.chunk_splits > 0);
    }

    #[test]
    fn pclf_d0_full_chunk_middle_singleton_reuses_endpoint_scans() {
        let mut store = ProofOccurrenceStore::default();
        let record = BoundRecordId(97_172);
        let support = SchemeProjectionProofSupport::Independent(
            ProjectionProofCarrier::Origin(OriginId(97_173)),
        );
        let admission = |parent: ConstraintRecordId| {
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                        parent,
                        rule: StructuralDerivationRule::FunctionReturn,
                    }),
                    premise: ProofPremise::Constraint(parent),
                },
            )
        };
        let initial = (0..PROJECTION_RUN_CHUNK_CAPACITY as u32)
            .map(|ordinal| admission(ConstraintRecordId(200_000 + ordinal * 2)))
            .collect::<Vec<_>>();
        let mut prepared = store
            .try_prepare_projection_clause_admission(record, &initial)
            .expect("full-chunk fixture reservation")
            .expect("full-chunk fixture must admit its initial batch");
        store.commit_projection_clause_admission(&mut prepared);
        let bucket = &store.projection_formula_shadow.by_record[&record];
        assert_eq!(bucket.canonical_runs.len(), 1);
        assert_eq!(bucket.canonical_runs[0].chunk_count(), 1);
        assert_eq!(bucket.canonical_runs[0].entry_len, PROJECTION_RUN_CHUNK_CAPACITY);

        let before = store.projection_formula_shadow.movement;
        store.record_projection_clause(record, admission(ConstraintRecordId(200_001)));
        let after = store.projection_formula_shadow.movement;
        assert_eq!(after.merge_calls - before.merge_calls, 1);
        assert_eq!(
            after.merge_scanned_entries - before.merge_scanned_entries,
            PROJECTION_RUN_CHUNK_CAPACITY as u64,
            "the two endpoint probes must be reused by the overlapping fallback merge",
        );
        assert_eq!(
            after.merge_comparisons - before.merge_comparisons,
            PROJECTION_RUN_CHUNK_CAPACITY as u64,
        );
        assert_eq!(after.chunk_splits - before.chunk_splits, 1);
        let bucket = &store.projection_formula_shadow.by_record[&record];
        assert_eq!(bucket.canonical_clauses(), store.projection_formulas[&record]);
        assert!(bucket.canonical_runs[0].chunks_are_nonempty_and_bounded());
        assert!(bucket.canonical_runs[0].chunk_tree_is_balanced());
    }

    #[test]
    fn pclf_b_shadow_admission_is_atomic_and_exact_duplicates_do_not_grow_it() {
        let mut store = ProofOccurrenceStore::default();
        let record = BoundRecordId(97_147);
        let support = SchemeProjectionProofSupport::Independent(ProjectionProofCarrier::Origin(
            OriginId(97_148),
        ));
        let admission = RecordProofClauseLinkAdmission::independent(
            support,
            RecordProofClause::Standalone { support },
        );
        let before = store.clone();
        let prepared = store
            .try_prepare_projection_clause_admission(record, &[admission])
            .unwrap()
            .unwrap();
        drop(prepared);
        assert_eq!(
            store, before,
            "prepare without commit must change neither logical face"
        );
        store.fail_next_projection_clause_reservation();
        assert!(matches!(
            store.try_prepare_projection_clause_admission(record, &[admission]),
            Err(ProofFailure::ResourceExhausted { .. })
        ));
        assert_eq!(store, before);
        store.record_projection_clause(record, admission);
        let after = store.performance_index_allocation_census();
        assert_eq!(after.shadow_projection_formula.bucket_map.0, 1);
        assert_eq!(after.shadow_projection_formula.entry_arena.0, 1);
        assert_eq!(after.shadow_projection_formula.support_group_arena.0, 1);
        assert_eq!(after.shadow_projection_formula.exact_incidence_index.0, 1);
        assert_eq!(after.shadow_projection_formula.canonical_run_table.0, 1);
        assert_eq!(after.shadow_projection_formula.canonical_run_entries.0, 1);
        assert_eq!(after.shadow_projection_formula.nonempty_canonical_runs, 1);
        assert_eq!(after.shadow_projection_formula.empty_canonical_runs, 0);
        assert_eq!(after.shadow_incidence_metadata.0, 1);
        store.record_projection_clause(record, admission);
        assert_eq!(store.performance_index_allocation_census(), after);
        store.debug_assert_pclf_a_read_model_matches_legacy();
    }

    #[test]
    fn pclf_b_each_reservation_failure_keeps_legacy_and_shadow_logically_unchanged() {
        let record = BoundRecordId(97_161);
        let claim = UpperReplayClaimId(0);
        let support = SchemeProjectionProofSupport::Claimed(claim);
        let admission = RecordProofClauseLinkAdmission::claimed(
            claim,
            RecordProofClause::Standalone { support },
            ClaimedAttributionSource::FlatRetained,
            ClaimedProjectionProofSource::Original {
                coverage_root: claim,
                producer: ConstraintRecordId(97_162),
            },
        );

        for point in [
            ProjectionClauseReservationFailurePoint::Initial,
            ProjectionClauseReservationFailurePoint::AfterLegacyPreflight,
            ProjectionClauseReservationFailurePoint::ShadowStructure,
            ProjectionClauseReservationFailurePoint::ShadowCanonicalRuns,
            ProjectionClauseReservationFailurePoint::ShadowNormalizedSupport,
        ] {
            let mut store = ProofOccurrenceStore::default();
            let before = store.clone();
            store.fail_projection_clause_reservation_at_for_test(point);
            assert!(matches!(
                store.try_prepare_projection_clause_admission(record, &[admission]),
                Err(ProofFailure::ResourceExhausted { .. })
            ));
            assert_eq!(
                store, before,
                "reservation failure at {point:?} must not logically mutate either face",
            );
        }
    }

    #[test]
    fn pclf_d0_failure_between_existing_run_reservations_keeps_both_faces_unchanged() {
        let mut store = ProofOccurrenceStore::default();
        let record = BoundRecordId(97_163);
        let left_support = SchemeProjectionProofSupport::Independent(
            ProjectionProofCarrier::Origin(OriginId(97_164)),
        );
        let right_support = SchemeProjectionProofSupport::Independent(
            ProjectionProofCarrier::Origin(OriginId(97_165)),
        );
        for (support, producer) in [
            (left_support, ConstraintRecordId(97_166)),
            (right_support, ConstraintRecordId(97_167)),
        ] {
            store.record_projection_clause(
                record,
                RecordProofClauseLinkAdmission::independent(
                    support,
                    RecordProofClause::DerivedUnary {
                        carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                            parent: producer,
                            rule: StructuralDerivationRule::FunctionArgument,
                        }),
                        premise: ProofPremise::Constraint(producer),
                    },
                ),
            );
        }
        let admissions = [
            RecordProofClauseLinkAdmission::independent(
                left_support,
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                        parent: ConstraintRecordId(97_168),
                        rule: StructuralDerivationRule::FunctionReturn,
                    }),
                    premise: ProofPremise::Constraint(ConstraintRecordId(97_168)),
                },
            ),
            RecordProofClauseLinkAdmission::independent(
                right_support,
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                        parent: ConstraintRecordId(97_169),
                        rule: StructuralDerivationRule::FunctionReturn,
                    }),
                    premise: ProofPremise::Constraint(ConstraintRecordId(97_169)),
                },
            ),
        ];
        let before = store.clone();
        store.fail_projection_clause_canonical_run_reservation_after_for_test(1);
        assert!(matches!(
            store.try_prepare_projection_clause_admission(record, &admissions),
            Err(ProofFailure::ResourceExhausted { .. })
        ));
        assert_eq!(store, before);
        store.debug_assert_pclf_a_read_model_matches_legacy();
    }

    #[test]
    fn pclf_b_shadow_keeps_conflicting_claimed_sources_per_incidence() {
        let mut store = ProofOccurrenceStore::default();
        let record = BoundRecordId(97_149);
        let replay = BinaryReplayDerivation {
            pivot: TypeVar(97_150),
            lower: BoundRecordId(97_151),
            upper: BoundRecordId(97_152),
            rule: ReplayRule::LowerBoundAdded,
        };
        let clause = RecordProofClause::ReplayConjunction {
            carrier: replay,
            lower_premise: replay.lower,
            upper_premise: replay.upper,
        };
        for admission in [
            RecordProofClauseLinkAdmission::claimed(
                UpperReplayClaimId(97_153),
                clause,
                ClaimedAttributionSource::CanonicalReplay,
                ClaimedProjectionProofSource::ReplayConstraint {
                    coverage_root: UpperReplayClaimId(97_153),
                    result: ConstraintRecordId(97_154),
                },
            ),
            RecordProofClauseLinkAdmission::claimed(
                UpperReplayClaimId(97_155),
                clause,
                ClaimedAttributionSource::FlatRetained,
                ClaimedProjectionProofSource::ReplayEvidence {
                    coverage_root: UpperReplayClaimId(97_155),
                },
            ),
        ] {
            store.record_projection_clause(record, admission);
        }
        store.debug_assert_pclf_a_read_model_matches_legacy();
        let bucket = &store.projection_formula_shadow.by_record[&record];
        assert_eq!(
            (
                bucket.entries.len(),
                bucket.support_groups.len(),
                bucket.exact_links.len()
            ),
            (1, 2, 2)
        );
        assert!(bucket.exact_links.values().any(|value| matches!(
            value,
            ProjectionIncidenceMetadata::Claimed(
                ClaimedProjectionSourceTemplate::ReplayConstraint {
                    result: ConstraintRecordId(97_154)
                }
            )
        )));
        assert!(bucket.exact_links.values().any(|value| matches!(
            value,
            ProjectionIncidenceMetadata::Claimed(ClaimedProjectionSourceTemplate::ReplayEvidence)
        )));
    }

    #[test]
    fn pclf_b_shadow_promotes_a_late_normalized_support_key() {
        let mut store = ProofOccurrenceStore::default();
        let record = BoundRecordId(97_156);
        let claim = UpperReplayClaimId(0);
        let support = SchemeProjectionProofSupport::Claimed(claim);
        let admission = RecordProofClauseLinkAdmission::claimed(
            claim,
            RecordProofClause::Standalone { support },
            ClaimedAttributionSource::FlatRetained,
            ClaimedProjectionProofSource::Original {
                coverage_root: claim,
                producer: ConstraintRecordId(97_157),
            },
        );
        // This is the production ordering: the clause is prepared from the old claim snapshot,
        // claim publication happens next, then that same prepared clause is committed.
        let mut prepared = store
            .try_prepare_projection_clause_admission(record, &[admission])
            .expect("the clause transaction must reserve both representations")
            .expect("the claimed exact link must be new");
        let normalized_capacity_before_commit = prepared
            .shadow
            .new_record_bucket
            .as_ref()
            .unwrap()
            .normalized_support_keys
            .capacity();
        assert!(normalized_capacity_before_commit >= 1);
        assert!(
            prepared.shadow.delta.new_support_groups[0]
                .match_key
                .is_none()
        );
        let mut claim_admission = store
            .try_prepare_original_claim_admission(
                BoundRecordId(97_158),
                ConstraintRecordId(97_157),
                UpperReplayClaimKind::Direct,
            )
            .unwrap();
        assert_eq!(claim_admission.occurrence.claim, claim);
        store.commit_original_claim_admission(&mut claim_admission);
        store.commit_projection_clause_admission(&mut prepared);
        assert_eq!(
            store.projection_formula_shadow.by_record[&record].support_groups[0].match_key,
            Some(ProjectionSupportMatchKey::Claimed(claim)),
        );
        assert!(
            store.projection_formula_shadow.by_record[&record]
                .normalized_support_keys
                .contains(&ProjectionSupportMatchKey::Claimed(claim))
        );
        assert_eq!(
            store.projection_formula_shadow.by_record[&record]
                .normalized_support_keys
                .capacity(),
            normalized_capacity_before_commit,
            "commit-time promotion must consume preflighted capacity without allocating",
        );
        assert!(
            store.projection_formula_support_keys[&record]
                .contains(&ProjectionSupportMatchKey::Claimed(claim))
        );
        store.debug_assert_pclf_a_read_model_matches_legacy();
    }

    #[test]
    fn cpk_projection_formula_support_keys_match_linear_formula_scan() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let replacement = add_same_root_replay_claim(
            &mut fixture,
            TypeVar(97_110),
            ConstraintRecordId(97_111),
        );
        let record = cpk_gap_1_projection_record(&mut fixture.machine, 97_112);
        let independent = SchemeProjectionProofSupport::Independent(
            ProjectionProofCarrier::Incomplete,
        );
        for admission in [
            RecordProofClauseLinkAdmission::claimed(
                fixture.coverage_root,
                RecordProofClause::Standalone {
                    support: SchemeProjectionProofSupport::Claimed(fixture.coverage_root),
                },
                ClaimedAttributionSource::FlatRetained,
                ClaimedProjectionProofSource::Original {
                    coverage_root: fixture.coverage_root,
                    producer: ConstraintRecordId(10_000),
                },
            ),
            RecordProofClauseLinkAdmission::claimed(
                replacement,
                RecordProofClause::Standalone {
                    support: SchemeProjectionProofSupport::Claimed(replacement),
                },
                ClaimedAttributionSource::FlatRetained,
                ClaimedProjectionProofSource::Original {
                    coverage_root: fixture.coverage_root,
                    producer: ConstraintRecordId(10_000),
                },
            ),
            RecordProofClauseLinkAdmission::independent(
                independent,
                RecordProofClause::Standalone {
                    support: independent,
                },
            ),
        ] {
            fixture
                .machine
                .proof_store
                .record_projection_clause(record, admission);
        }
        let indexes_before_duplicate = fixture
            .machine
            .proof_store
            .performance_index_allocation_census();
        fixture.machine.proof_store.record_projection_clause(
            record,
            RecordProofClauseLinkAdmission::independent(
                independent,
                RecordProofClause::Standalone {
                    support: independent,
                },
            ),
        );
        assert_eq!(
            fixture
                .machine
                .proof_store
                .performance_index_allocation_census(),
            indexes_before_duplicate,
            "an exact clause-link duplicate must not grow the formula-support mirror",
        );

        fixture
            .machine
            .proof_store
            .debug_assert_projection_formula_support_keys_match_linear_scan();
        fixture
            .machine
            .proof_store
            .debug_assert_claimed_projection_audit_reconstructs();
        fixture
            .machine
            .proof_store
            .debug_assert_pclf_a_read_model_matches_legacy();
        let keys = &fixture.machine.proof_store.projection_formula_support_keys[&record];
        assert_eq!(keys.len(), 2, "same-root representatives share one key");
        assert!(keys.contains(&ProjectionSupportMatchKey::Claimed(
            fixture.coverage_root
        )));
        assert!(keys.contains(&ProjectionSupportMatchKey::Independent(
            ProjectionProofCarrier::Incomplete
        )));
    }

    #[test]
    fn gwcb_a_claimed_audit_reconstruction_is_insertion_order_invariant() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let replacement = add_same_root_replay_claim(
            &mut fixture,
            TypeVar(97_113),
            ConstraintRecordId(97_114),
        );
        let record = BoundRecordId(97_115);
        let root = fixture.coverage_root;
        let source = ClaimedProjectionProofSource::Original {
            coverage_root: root,
            producer: ConstraintRecordId(10_000),
        };
        let baseline = fixture.machine.proof_store.clone();
        let mut snapshots = Vec::new();
        for claims in [[root, replacement], [replacement, root]] {
            let mut store = baseline.clone();
            for claim in claims {
                store.record_projection_clause(
                    record,
                    RecordProofClauseLinkAdmission::claimed(
                        claim,
                        RecordProofClause::Standalone {
                            support: SchemeProjectionProofSupport::Claimed(claim),
                        },
                        ClaimedAttributionSource::FlatRetained,
                        source,
                    ),
                );
            }
            store.debug_assert_claimed_projection_audit_reconstructs();
            let reconstructed = store.claimed_projection_proofs_from_audit_for_test();
            let bucket = reconstructed
                .get(&record)
                .expect("accepted claimed links reconstruct one semantic bucket");
            assert_eq!(
                store
                    .projection_claimed_link_audit
                    .keys()
                    .filter(|(bound, _, _)| *bound == record)
                    .count(),
                2,
                "both exact raw representative links remain auditable",
            );
            assert_eq!(bucket.len(), 1, "same-root raw links share one semantic key");
            assert_eq!(
                *bucket.values().next().unwrap(),
                root.min(replacement),
                "the audit representative is canonical rather than admission-order dependent",
            );
            let decisive = store
                .decisive_claimed_projection_proof(
                    record,
                    store.projection_formulas[&record][0],
                )
                .expect("the canonical raw clause must reconstruct without a scan")
                .expect("the canonical raw clause is claimed");
            assert_eq!(
                decisive.representative_claim(),
                root.min(replacement),
                "lookup-time reconstruction must retain canonical representative stability",
            );
            snapshots.push((bucket.clone(), decisive));
        }
        assert_eq!(snapshots[0], snapshots[1]);
    }

    #[test]
    fn gwcb_a_certificate_allocation_is_zero_for_independent_and_exact_duplicate_links() {
        let mut independent_store = ProofOccurrenceStore::default();
        let record = BoundRecordId(97_116);
        let support = SchemeProjectionProofSupport::Independent(
            ProjectionProofCarrier::Incomplete,
        );
        let before = independent_store.performance_index_allocation_census();
        independent_store.record_projection_clause(
            record,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::Standalone { support },
            ),
        );
        let after = independent_store.performance_index_allocation_census();
        assert!(
            independent_store.projection_formulas.contains_key(&record),
            "the independent-only admission must be accepted before its claimed-link allocation is assessed",
        );
        assert_eq!(after.claimed_projection_audit, before.claimed_projection_audit);
        independent_store.debug_assert_pclf_a_read_model_matches_legacy();

        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let record = BoundRecordId(97_117);
        let claim = fixture.coverage_root;
        let admission = RecordProofClauseLinkAdmission::claimed(
            claim,
            RecordProofClause::Standalone {
                support: SchemeProjectionProofSupport::Claimed(claim),
            },
            ClaimedAttributionSource::FlatRetained,
            ClaimedProjectionProofSource::Original {
                coverage_root: claim,
                producer: ConstraintRecordId(10_000),
            },
        );
        fixture
            .machine
            .proof_store
            .record_projection_clause(record, admission);
        let after_first = fixture
            .machine
            .proof_store
            .performance_index_allocation_census();
        fixture
            .machine
            .proof_store
            .record_projection_clause(record, admission);
        assert_eq!(
            fixture
                .machine
                .proof_store
                .performance_index_allocation_census(),
            after_first,
            "an exact raw-link duplicate must not grow audit or certificate storage",
        );
        fixture
            .machine
            .proof_store
            .debug_assert_claimed_projection_audit_reconstructs();
        fixture
            .machine
            .proof_store
            .debug_assert_pclf_a_read_model_matches_legacy();
    }

    #[test]
    fn gwcb_a_failed_claimed_reservation_keeps_formula_and_certificate_atomic() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let record = BoundRecordId(97_118);
        let claim = fixture.coverage_root;
        let admission = RecordProofClauseLinkAdmission::claimed(
            claim,
            RecordProofClause::Standalone {
                support: SchemeProjectionProofSupport::Claimed(claim),
            },
            ClaimedAttributionSource::FlatRetained,
            ClaimedProjectionProofSource::Original {
                coverage_root: claim,
                producer: ConstraintRecordId(10_000),
            },
        );
        let before = fixture.machine.proof_store.clone();
        fixture
            .machine
            .proof_store
            .fail_next_projection_clause_reservation();
        assert!(matches!(
            fixture
                .machine
                .proof_store
                .try_prepare_projection_clause_admission(record, &[admission]),
            Err(ProofFailure::ResourceExhausted { .. })
        ));
        assert_eq!(fixture.machine.proof_store.projection_formulas, before.projection_formulas);
        assert_eq!(
            fixture.machine.proof_store.projection_claimed_link_audit,
            before.projection_claimed_link_audit,
        );
        fixture
            .machine
            .proof_store
            .record_projection_clause(record, admission);
        fixture
            .machine
            .proof_store
            .debug_assert_claimed_projection_audit_reconstructs();
        fixture
            .machine
            .proof_store
            .debug_assert_pclf_a_read_model_matches_legacy();
        assert_eq!(fixture.machine.proof_store.projection_formulas[&record].len(), 1);
        assert_eq!(
            fixture
                .machine
                .proof_store
                .claimed_projection_proofs_from_audit_for_test()[&record]
                .len(),
            1,
        );
    }

    #[test]
    fn gwcb_a_claimed_audit_prepare_carries_only_the_admission_delta() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let record = BoundRecordId(97_119);
        let first = fixture.coverage_root;
        fixture.machine.proof_store.record_projection_clause(
            record,
            RecordProofClauseLinkAdmission::claimed(
                first,
                RecordProofClause::Standalone {
                    support: SchemeProjectionProofSupport::Claimed(first),
                },
                ClaimedAttributionSource::FlatRetained,
                ClaimedProjectionProofSource::Original {
                    coverage_root: first,
                    producer: ConstraintRecordId(10_000),
                },
            ),
        );

        let second_parent = fixture
            .machine
            .bounds
            .add_upper(
                TypeVar(97_119),
                fixture.machine.constraint_records[fixture.result.0 as usize]
                    .key
                    .upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let second = fixture.machine.original_upper_replay_claim(
            second_parent,
            ConstraintRecordId(10_001),
            UpperReplayClaimKind::Direct,
        );
        fixture
            .machine
            .apply_scheme_projection_mutation(second.scheme_projection_mutation);
        let second_admission = RecordProofClauseLinkAdmission::claimed(
            second.claim,
            RecordProofClause::Standalone {
                support: SchemeProjectionProofSupport::Claimed(second.claim),
            },
            ClaimedAttributionSource::FlatRetained,
            ClaimedProjectionProofSource::Original {
                coverage_root: second.claim,
                producer: ConstraintRecordId(10_001),
            },
        );
        let mut prepared = fixture
            .machine
            .proof_store
            .try_prepare_projection_clause_admission(record, &[second_admission])
            .expect("delta admission must reserve all commit capacity")
            .expect("the distinct claimed link must be admitted");
        assert_eq!(
            fixture
                .machine
                .proof_store
                .projection_claimed_link_audit
                .keys()
                .filter(|(bound, _, _)| *bound == record)
                .count(),
            1,
            "preparation must leave the existing raw audit ledger unchanged",
        );
        assert_eq!(
            prepared.new_claimed_link_audit_entries.len(),
            1,
            "the prepared transaction must carry only the new raw audit fact",
        );
        assert_eq!(
            prepared.new_claimed_link_audit_entries[0],
            (
                (
                    record,
                    SchemeProjectionProofSupport::Claimed(second.claim),
                    RecordProofClause::Standalone {
                        support: SchemeProjectionProofSupport::Claimed(second.claim),
                    },
                ),
                ClaimedProjectionProofSource::Original {
                    coverage_root: second.claim,
                    producer: ConstraintRecordId(10_001),
                },
            ),
        );

        fixture
            .machine
            .proof_store
            .commit_projection_clause_admission(&mut prepared);
        fixture
            .machine
            .proof_store
            .debug_assert_claimed_projection_audit_reconstructs();
        assert_eq!(
            fixture
                .machine
                .proof_store
                .projection_claimed_link_audit
                .keys()
                .filter(|(bound, _, _)| *bound == record)
                .count(),
            2,
        );
    }

    #[test]
    fn gwcb_b_decisive_claimed_arm_is_canonical_memoized_once_and_materialized_lazily() {
        assert_eq!(
            std::mem::size_of::<ProofEvalEvidenceMemo>(),
            8,
            "the evidence memo must retain only a compact support/entry identity",
        );
        assert_eq!(
            std::mem::size_of::<ProofEvalState>(),
            12,
            "the hot round memo must not inline projection clauses or certificates",
        );
        #[allow(dead_code)]
        enum PriorGeneralizationParentLayout {
            Constraint(ConstraintRecordId),
            Bound(BoundRecordId),
            BoundClaim {
                bound: BoundRecordId,
                claim: UpperReplayClaimId,
            },
            BoundProjectionProof {
                bound: BoundRecordId,
                carrier: ProjectionProofCarrier,
            },
        }
        assert_eq!(
            std::mem::size_of::<PriorGeneralizationParentLayout>(),
            28,
            "the comparison layout must continue to model the pre-GWCB parent",
        );
        assert_eq!(
            std::mem::size_of::<GeneralizationParent>(),
            32,
            "the boxed certificate must add only one pointer-sized field to the prior parent layout",
        );
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let second_parent = fixture
            .machine
            .bounds
            .add_upper(
                TypeVar(97_119),
                fixture.machine.constraint_records[fixture.result.0 as usize]
                    .key
                    .upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let second = fixture.machine.original_upper_replay_claim(
            second_parent,
            ConstraintRecordId(10_001),
            UpperReplayClaimKind::Direct,
        );
        fixture
            .machine
            .apply_scheme_projection_mutation(second.scheme_projection_mutation);
        let claims = [fixture.coverage_root, second.claim];
        let record = cpk_gap_1_projection_record(&mut fixture.machine, 97_119);
        let mutation = fixture
            .machine
            .try_prepare_scheme_projection_mutation(record, &claims, &[])
            .expect("multi-arm fixture support mutation must have capacity");
        fixture.machine.apply_scheme_projection_mutation(mutation);
        for (claim, producer) in claims
            .into_iter()
            .zip([ConstraintRecordId(10_000), ConstraintRecordId(10_001)])
            .rev()
        {
            fixture.machine.proof_store.record_projection_clause(
                record,
                RecordProofClauseLinkAdmission::claimed(
                    claim,
                    RecordProofClause::Standalone {
                        support: SchemeProjectionProofSupport::Claimed(claim),
                    },
                    ClaimedAttributionSource::FlatRetained,
                    ClaimedProjectionProofSource::Original {
                        coverage_root: claim,
                        producer,
                    },
                ),
            );
        }
        assert_eq!(
            fixture
                .machine
                .proof_store
                .projection_claimed_link_audit
                .keys()
                .filter(|(bound, _, _)| *bound == record)
                .count(),
            2,
            "the source-of-truth fixture must contain multiple raw claimed arms",
        );

        let mut evaluator =
            CpkProjectionEvaluator::new(&fixture.machine, &fixture.machine.proof_store);
        let evaluation = evaluator
            .eval_record_with_evidence(record)
            .expect("decisive evidence lookup must be fallible without collecting arms");
        let CpkProjectionEvaluation::Included {
            evidence: ProjectionEvidence::DecisiveClaimedArm(proof),
        } = evaluation
        else {
            panic!("the canonical first true claimed clause must be the decisive arm");
        };
        assert_eq!(proof.coverage_root(), claims.into_iter().min().unwrap());
        let ProofEvalState::Done(memo) = evaluator.states[&ProofEvalNode::Record(record)] else {
            panic!("the decisive record must be memoized after its first evaluation");
        };
        let DecodedProofEvalEvidenceMemo::DecisiveClaimedIncidence {
            support_id,
            entry_id,
        } = memo.evidence.decode()
        else {
            panic!("the packed memo must retain the exact decisive PCLF incidence");
        };
        let bucket = &fixture.machine.proof_store.projection_formula_shadow.by_record[&record];
        assert!(matches!(
            bucket.exact_links[&(support_id, entry_id)],
            ProjectionIncidenceMetadata::Claimed(_),
        ));
        let legacy_clause = bucket.reconstructed_clause(support_id, entry_id);
        assert_eq!(
            fixture
                .machine
                .proof_store
                .decisive_claimed_projection_proof(record, legacy_clause)
                .expect("legacy decisive source oracle"),
            Some(proof),
        );
        assert_eq!(
            evaluator
                .eval_record_with_evidence(record)
                .expect("the same immutable-round evidence must be memoized"),
            evaluation,
        );
        assert_eq!(
            evaluator.decisive_certificate_lookups(),
            2,
            "the full certificate is materialized lazily only when each caller requests evidence",
        );
        assert_eq!(
            evaluator.decisive_evidence_markers(),
            1,
            "the compact decisive-clause marker is computed once with the memoized boolean result",
        );
    }

    #[test]
    fn pclf_d1_standalone_ties_preserve_legacy_decisive_claimed_source() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let record = cpk_gap_1_projection_record(&mut fixture.machine, 97_174);
        let claim = fixture.coverage_root;
        let outer_support = SchemeProjectionProofSupport::Claimed(claim);
        let mutation = fixture
            .machine
            .try_prepare_scheme_projection_mutation(record, &[claim], &[])
            .expect("standalone tie fixture support mutation");
        fixture.machine.apply_scheme_projection_mutation(mutation);

        let mismatched_clause = RecordProofClause::Standalone {
            support: SchemeProjectionProofSupport::Independent(
                ProjectionProofCarrier::Incomplete,
            ),
        };
        let legacy_matching_clause = RecordProofClause::Standalone {
            support: outer_support,
        };
        for (clause, producer) in [
            (mismatched_clause, ConstraintRecordId(97_175)),
            (legacy_matching_clause, ConstraintRecordId(97_176)),
        ] {
            fixture.machine.proof_store.record_projection_clause(
                record,
                RecordProofClauseLinkAdmission::claimed(
                    claim,
                    clause,
                    ClaimedAttributionSource::FlatRetained,
                    ClaimedProjectionProofSource::Original {
                        coverage_root: claim,
                        producer,
                    },
                ),
            );
        }

        let legacy_formula = &fixture.machine.proof_store.projection_formulas[&record];
        assert_eq!(legacy_formula.len(), 2);
        assert_eq!(legacy_formula[0], legacy_formula[1]);
        let legacy_proof = fixture
            .machine
            .proof_store
            .decisive_claimed_projection_proof(record, legacy_formula[0])
            .expect("legacy decisive lookup")
            .expect("the embedded-outer incidence is legacy's decisive source");
        let mut evaluator =
            CpkProjectionEvaluator::new(&fixture.machine, &fixture.machine.proof_store);
        let CpkProjectionEvaluation::Included {
            evidence: ProjectionEvidence::DecisiveClaimedArm(factored_proof),
        } = evaluator
            .eval_record_with_evidence(record)
            .expect("factored decisive lookup")
        else {
            panic!("the tied standalone fixture must include through a claimed arm");
        };
        assert_eq!(factored_proof, legacy_proof);
        let ProofEvalState::Done(memo) = evaluator.states[&ProofEvalNode::Record(record)] else {
            panic!("the decisive record must be memoized");
        };
        let DecodedProofEvalEvidenceMemo::DecisiveClaimedIncidence {
            support_id,
            entry_id,
        } = memo.evidence.decode()
        else {
            panic!("the packed memo must retain legacy's decisive incidence");
        };
        let bucket = &fixture.machine.proof_store.projection_formula_shadow.by_record[&record];
        assert_eq!(
            entry_id,
            bucket.entry_by_clause[&legacy_matching_clause],
            "legacy resolves the collapsed Standalone clause through the embedded-outer audit identity",
        );
        assert!(bucket.exact_links.contains_key(&(support_id, entry_id)));
    }

    #[test]
    fn pclf_d1_standalone_ties_split_chunks_without_equal_pivots() {
        let mut store = ProofOccurrenceStore::default();
        let record = BoundRecordId(97_177);
        let outer_support = SchemeProjectionProofSupport::Independent(
            ProjectionProofCarrier::Incomplete,
        );
        let admission = |ordinal: u32| {
            RecordProofClauseLinkAdmission::independent(
                outer_support,
                RecordProofClause::Standalone {
                    support: SchemeProjectionProofSupport::Independent(
                        ProjectionProofCarrier::Origin(OriginId(210_000 + ordinal)),
                    ),
                },
            )
        };
        let initial = (0..PROJECTION_RUN_CHUNK_CAPACITY as u32)
            .map(admission)
            .collect::<Vec<_>>();
        let mut prepared = store
            .try_prepare_projection_clause_admission(record, &initial)
            .expect("tied standalone initial reservation")
            .expect("tied standalone initial admission");
        store.commit_projection_clause_admission(&mut prepared);
        store.record_projection_clause(
            record,
            admission(PROJECTION_RUN_CHUNK_CAPACITY as u32),
        );

        let bucket = &store.projection_formula_shadow.by_record[&record];
        assert_eq!(bucket.canonical_runs.len(), 1);
        assert_eq!(bucket.canonical_runs[0].entry_len, 129);
        assert!(bucket.canonical_runs[0].chunks_are_nonempty_and_bounded());
        assert!(bucket.canonical_runs[0].chunk_tree_is_balanced());
        assert_eq!(bucket.canonical_clauses(), store.projection_formulas[&record]);
    }

    #[test]
    fn pclf_d1_packed_evidence_memo_round_trips_all_states_and_rejects_reserved_ids() {
        assert_eq!(std::mem::size_of::<ProofEvalEvidenceMemo>(), 8);
        assert_eq!(std::mem::size_of::<ProofEvalState>(), 12);
        assert_eq!(
            ProofEvalEvidenceMemo::none().decode(),
            DecodedProofEvalEvidenceMemo::None,
        );
        assert_eq!(
            ProofEvalEvidenceMemo::exact_without_claimed_arm().decode(),
            DecodedProofEvalEvidenceMemo::ExactWithoutClaimedArm,
        );
        assert_eq!(
            ProofEvalEvidenceMemo::fail_open_incomplete().decode(),
            DecodedProofEvalEvidenceMemo::FailOpenIncomplete,
        );
        let support_id = ProjectionSupportGroupId(17);
        let entry_id = ProjectionFormulaEntryId(23);
        assert_eq!(
            ProofEvalEvidenceMemo::decisive_claimed_incidence(support_id, entry_id).decode(),
            DecodedProofEvalEvidenceMemo::DecisiveClaimedIncidence {
                support_id,
                entry_id,
            },
        );
        assert!(std::panic::catch_unwind(|| {
            ProofEvalEvidenceMemo::decisive_claimed_incidence(
                ProjectionSupportGroupId(u32::MAX),
                entry_id,
            )
        })
        .is_err());
        assert_eq!(
            try_projection_support_group_id(u32::MAX as usize - 1),
            Ok(ProjectionSupportGroupId(u32::MAX - 1)),
        );
        assert!(matches!(
            try_projection_support_group_id(u32::MAX as usize),
            Err(ProofFailure::ResourceExhausted {
                operation: ProofOperation::UpdateClaimLifecycle,
            }),
        ));
    }

    #[test]
    fn gwcb_0_raw_claimed_links_map_totally_to_distinct_normalized_keys() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let replacement = add_same_root_replay_claim(
            &mut fixture,
            TypeVar(97_120),
            ConstraintRecordId(97_121),
        );
        let record = cpk_gap_1_projection_record(&mut fixture.machine, 97_122);
        for claim in [fixture.coverage_root, replacement] {
            fixture.machine.proof_store.record_projection_clause(
                record,
                RecordProofClauseLinkAdmission::claimed(
                    claim,
                    RecordProofClause::Standalone {
                        support: SchemeProjectionProofSupport::Claimed(claim),
                    },
                    ClaimedAttributionSource::FlatRetained,
                    ClaimedProjectionProofSource::Original {
                        coverage_root: fixture.coverage_root,
                        producer: ConstraintRecordId(10_000),
                    },
                ),
            );
        }

        let raw = fixture
            .machine
            .proof_store
            .projection_clause_links_for_test(record)
            .into_iter()
            .filter(|(support, _)| matches!(support, SchemeProjectionProofSupport::Claimed(_)))
            .collect::<Vec<_>>();
        let normalized = raw
            .iter()
            .map(|(support, clause)| {
                gwcb0_normalized_claimed_link_key(
                    &fixture.machine.proof_store,
                    record,
                    *support,
                    *clause,
                )
                .expect("every admitted claimed link has a resolvable normalized key")
            })
            .collect::<FxHashSet<_>>();
        assert_eq!(raw.len(), 2, "the audit ledger retains both raw representatives");
        assert_eq!(
            normalized.len(),
            1,
            "same-root outer and embedded claimed supports collapse to one semantic certificate",
        );
    }

    #[test]
    fn gwcb_0_generic_test_writers_can_supply_exact_certificate_metadata() {
        let root = UpperReplayClaimId(97_130);
        let lower = BoundRecordId(97_131);
        let upper = BoundRecordId(97_132);
        let result = ConstraintRecordId(97_133);
        let producer = ConstraintRecordId(97_134);
        let replay = BinaryReplayDerivation {
            pivot: TypeVar(97_135),
            lower,
            upper,
            rule: ReplayRule::UpperBoundAdded,
        };
        let replay_clause = RecordProofClause::ReplayConjunction {
            carrier: replay,
            lower_premise: lower,
            upper_premise: upper,
        };
        let structural_premise = ProofPremise::Constraint(ConstraintRecordId(97_136));
        let reduction_premise = ProofPremise::RootCoverage(root);
        let observations = [
            gwcb0_test_writer_with_explicit_metadata(
                RecordProofClauseLinkAdmission::claimed(
                    root,
                    RecordProofClause::Standalone {
                        support: SchemeProjectionProofSupport::Claimed(root),
                    },
                    ClaimedAttributionSource::FlatRetained,
                    ClaimedProjectionProofSource::Original {
                        coverage_root: root,
                        producer,
                    },
                ),
                Gwcb0WriterCertificateMetadata::Original { producer },
            ),
            gwcb0_test_writer_with_explicit_metadata(
                RecordProofClauseLinkAdmission::claimed(
                    root,
                    replay_clause,
                    ClaimedAttributionSource::CanonicalReplay,
                    ClaimedProjectionProofSource::ReplayConstraint {
                        coverage_root: root,
                        result,
                    },
                ),
                Gwcb0WriterCertificateMetadata::ReplayConstraint { result },
            ),
            gwcb0_test_writer_with_explicit_metadata(
                RecordProofClauseLinkAdmission::claimed(
                    root,
                    replay_clause,
                    ClaimedAttributionSource::FlatRetained,
                    ClaimedProjectionProofSource::ReplayEvidence {
                        coverage_root: root,
                    },
                ),
                Gwcb0WriterCertificateMetadata::ReplayEvidence,
            ),
            gwcb0_test_writer_with_explicit_metadata(
                RecordProofClauseLinkAdmission::claimed(
                    root,
                    RecordProofClause::DerivedUnary {
                        carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                            parent: ConstraintRecordId(97_136),
                            rule: StructuralDerivationRule::FunctionReturn,
                        }),
                        premise: structural_premise,
                    },
                    ClaimedAttributionSource::FlatRetained,
                    ClaimedProjectionProofSource::DerivedUnary {
                        coverage_root: root,
                        result,
                    },
                ),
                Gwcb0WriterCertificateMetadata::DerivedUnary {
                    result,
                    premise: structural_premise,
                },
            ),
            gwcb0_test_writer_with_explicit_metadata(
                RecordProofClauseLinkAdmission::claimed(
                    root,
                    RecordProofClause::DerivedUnary {
                        carrier: DerivedUnaryCarrier::ReductionRoute(RowDerivationId(97_137)),
                        premise: reduction_premise,
                    },
                    ClaimedAttributionSource::FlatRetained,
                    ClaimedProjectionProofSource::DerivedUnary {
                        coverage_root: root,
                        result,
                    },
                ),
                Gwcb0WriterCertificateMetadata::DerivedUnary {
                    result,
                    premise: reduction_premise,
                },
            ),
        ];
        assert_eq!(observations.len(), 5);
        assert!(matches!(
            observations[0].1,
            Gwcb0WriterCertificateMetadata::Original { producer: found } if found == producer
        ));
        assert!(matches!(
            observations[1].1,
            Gwcb0WriterCertificateMetadata::ReplayConstraint { result: found } if found == result
        ));
    }

    #[test]
    fn gwcb_0_replay_carrier_can_have_multiple_results_but_writer_has_result() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let other_result =
            cpk_7_admit_inert_constraint(&mut fixture.machine, 97_140, "gwcb-other-result");
        let parent = SideTaggedReplayClaim {
            claim: fixture.coverage_root,
            parent_side: ReplayClaimParentSide::Upper,
        };
        for result in [fixture.result, other_result] {
            fixture
                .machine
                .proof_store
                .record_cpk_replay_parent_snapshot(result, fixture.carrier, &[parent]);
        }
        let results = fixture
            .machine
            .proof_store
            .replay_finite_map
            .iter()
            .filter(|replay| replay.carrier == fixture.carrier)
            .map(|replay| replay.result)
            .collect::<FxHashSet<_>>();
        assert_eq!(results, FxHashSet::from_iter([fixture.result, other_result]));
        assert!(fixture
            .machine
            .proof_store
            .replay_finite_map_index
            .contains_key(&(fixture.result, fixture.carrier)));
        assert!(fixture
            .machine
            .proof_store
            .replay_finite_map_index
            .contains_key(&(other_result, fixture.carrier)));
    }

    #[test]
    fn gwcb_0_raw_true_branches_distinguish_exact_empty_from_fail_open() {
        let enumerated = [
            Gwcb0RawTrueBranch::Tombstone,
            Gwcb0RawTrueBranch::UpperWithoutClaims,
            Gwcb0RawTrueBranch::ConstraintWithoutSource,
            Gwcb0RawTrueBranch::MissingBound,
            Gwcb0RawTrueBranch::MissingSupports,
            Gwcb0RawTrueBranch::EmptySupports,
            Gwcb0RawTrueBranch::QualifyingSupportAbsentFromFormulaMirror,
            Gwcb0RawTrueBranch::MissingConstraint,
            Gwcb0RawTrueBranch::MissingClaimOrCoverageRoot,
        ];
        assert_eq!(enumerated.len(), 9, "keep this census aligned with raw evaluator true exits");
        let fail_open = [
            Gwcb0RawTrueBranch::MissingBound,
            Gwcb0RawTrueBranch::MissingSupports,
            Gwcb0RawTrueBranch::EmptySupports,
            Gwcb0RawTrueBranch::QualifyingSupportAbsentFromFormulaMirror,
            Gwcb0RawTrueBranch::MissingConstraint,
            Gwcb0RawTrueBranch::MissingClaimOrCoverageRoot,
        ];
        let fail_open_observations = fail_open.map(Gwcb0EvidenceObservation::FailOpenIncomplete);
        assert!(fail_open_observations.iter().all(|observation| matches!(
            observation,
            Gwcb0EvidenceObservation::FailOpenIncomplete(_)
        )));

        let mut exact = cpk_machine();
        let exact_record = cpk_gap_1_projection_record(&mut exact, 97_150);
        let carrier = ProjectionProofCarrier::Incomplete;
        let support = cpk_4_add_independent_support(&mut exact, exact_record, carrier);
        exact.register_cpk_projection_clause_for_test(
            exact_record,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::Standalone { support },
            ),
        );
        assert!(matches!(
            project_lower_for_test(&exact, exact_record).0,
            Ok(ProjectionDecision::Included {
                supports: ProjectionSupportSet {
                    ref uncovered_claims,
                    ..
                },
                ..
            }) if uncovered_claims.is_empty()
        ));
        assert_eq!(
            projection_evidence_for_test(&exact, exact_record),
            ProjectionEvidence::ExactWithoutClaimedArm,
        );
        let exact_observation = Gwcb0EvidenceObservation::ExactWithoutClaimedArm;

        let mut missing_supports = cpk_machine();
        let missing_supports_record =
            cpk_gap_1_projection_record(&mut missing_supports, 97_152);
        let mut raw =
            CpkProjectionEvaluator::new(&missing_supports, &missing_supports.proof_store);
        assert!(raw.eval_record(missing_supports_record));
        assert_eq!(
            raw.eval_record_with_evidence(missing_supports_record),
            Ok(CpkProjectionEvaluation::Included {
                evidence: ProjectionEvidence::FailOpenIncomplete,
            }),
        );
        let missing_observation = Gwcb0EvidenceObservation::FailOpenIncomplete(
            Gwcb0RawTrueBranch::MissingSupports,
        );

        let mut empty_supports = cpk_machine();
        let empty_supports_record = cpk_gap_1_projection_record(&mut empty_supports, 97_153);
        empty_supports
            .proof_store
            .projection_supports
            .insert(empty_supports_record, Vec::new());
        let mut raw = CpkProjectionEvaluator::new(&empty_supports, &empty_supports.proof_store);
        assert!(raw.eval_record(empty_supports_record));
        assert_eq!(
            raw.eval_record_with_evidence(empty_supports_record),
            Ok(CpkProjectionEvaluation::Included {
                evidence: ProjectionEvidence::FailOpenIncomplete,
            }),
        );
        let empty_observation =
            Gwcb0EvidenceObservation::FailOpenIncomplete(Gwcb0RawTrueBranch::EmptySupports);

        let mut incomplete = cpk_machine();
        let incomplete_record = cpk_gap_1_projection_record(&mut incomplete, 97_151);
        cpk_4_add_independent_support(&mut incomplete, incomplete_record, carrier);
        let mut raw = CpkProjectionEvaluator::new(&incomplete, &incomplete.proof_store);
        assert!(raw.eval_record(incomplete_record), "the direct raw path currently fail-opens");
        assert_eq!(
            raw.eval_record_with_evidence(incomplete_record),
            Ok(CpkProjectionEvaluation::Included {
                evidence: ProjectionEvidence::FailOpenIncomplete,
            }),
        );
        assert!(matches!(
            project_lower_for_test(&incomplete, incomplete_record).0,
            Err(ProofFailure::MissingProofFact {
                fact: ProofFactRef::ProjectionFormula(found),
            }) if found == incomplete_record
        ));
        let incomplete_observation = Gwcb0EvidenceObservation::FailOpenIncomplete(
            Gwcb0RawTrueBranch::QualifyingSupportAbsentFromFormulaMirror,
        );

        assert_ne!(exact_observation, missing_observation);
        assert_ne!(exact_observation, empty_observation);
        assert_ne!(exact_observation, incomplete_observation);
    }

    #[test]
    fn gwcb_0_mixed_bound_filtered_certificate_excludes_raw_sibling_arms() {
        let (mut machine, endpoint, owner, _) =
            ConstraintMachine::compact_scheme_projection_unmatched_route_fixture(true);
        let record = machine
            .bounds()
            .of(owner)
            .expect("mixed fixture owner")
            .generalized_projection_lowers()
            .find_map(|(record, bound)| {
                matches!(machine.types().pos(bound.pos), Pos::Var(found) if *found == endpoint)
                    .then_some(record)
            })
            .expect("mixed fixture target");
        let independent = SchemeProjectionProofSupport::Independent(
            ProjectionProofCarrier::Incomplete,
        );
        let mutation = machine
            .try_prepare_scheme_projection_mutation(
                record,
                &[],
                &[ProjectionProofCarrier::Incomplete],
            )
            .expect("test projection support mutation must have capacity");
        machine.apply_scheme_projection_mutation(mutation);
        machine.register_cpk_projection_clause_for_test(
            record,
            RecordProofClauseLinkAdmission::independent(
                independent,
                RecordProofClause::Standalone {
                    support: independent,
                },
            ),
        );

        let formula = &machine.proof_store.projection_formulas[&record];
        let filtered = formula
            .iter()
            .copied()
            .find(|clause| matches!(clause.support(), SchemeProjectionProofSupport::Claimed(_)))
            .expect("mixed fixture retains one claimed certificate arm");
        assert!(formula.len() > 1, "raw record contains sibling formula arms");
        assert!(formula.iter().any(|clause| *clause != filtered));
        assert!(formula.iter().any(|clause| clause.support() == independent));

        let filtered_view = [filtered];
        assert_eq!(filtered_view.len(), 1);
        assert!(!filtered_view.iter().any(|clause| clause.support() == independent));
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
    fn cpk_replay_route_batches_match_pairwise_preparation() {
        let mut machine = cpk_machine();
        let owner = TypeVar(72_000);
        let concrete_lower_endpoint =
            machine.alloc_pos(Pos::Con(vec!["cpk-batch-concrete".into()], Vec::new()));
        let variable_lower_endpoint = machine.alloc_pos(Pos::Var(TypeVar(72_001)));
        let concrete_lower = machine
            .bounds
            .add_lower(
                owner,
                concrete_lower_endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let variable_lower = machine
            .bounds
            .add_lower(
                owner,
                variable_lower_endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let first_upper_endpoint =
            machine.alloc_neg(Neg::Con(vec!["cpk-batch-first".into()], Vec::new()));
        let second_upper_endpoint =
            machine.alloc_neg(Neg::Con(vec!["cpk-batch-second".into()], Vec::new()));
        let first_upper = machine
            .bounds
            .add_upper(
                owner,
                first_upper_endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let second_upper = machine
            .bounds
            .add_upper(
                owner,
                second_upper_endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let first_claim = machine
            .original_upper_replay_claim(
                first_upper,
                ConstraintRecordId(92_000),
                UpperReplayClaimKind::Direct,
            )
            .claim;
        machine.original_upper_replay_claim(
            second_upper,
            ConstraintRecordId(92_001),
            UpperReplayClaimKind::Direct,
        );
        machine.proof_store.record_live_coverage(
            first_claim,
            UnweightedRowReductionRecordId(72_000),
            true,
        );
        let incremental = IncrementalRouteKey {
            upper: machine.alloc_neg(Neg::Con(
                vec!["cpk-batch-incremental".into()],
                Vec::new(),
            )),
            upper_record: first_upper,
            provenance: RowDerivationId(72_000),
            claim: None,
        };

        let expected_lower = vec![
            machine
                .proof_store
                .prepare_replay_route(&machine, concrete_lower, first_upper, &[incremental])
                .expect("first pairwise lower-added route"),
            machine
                .proof_store
                .prepare_replay_route(&machine, concrete_lower, second_upper, &[])
                .expect("second pairwise lower-added route"),
        ];
        let incremental_routes = [incremental];
        let lower_batch = machine
            .proof_store
            .prepare_replay_routes_for_lower(
                &machine,
                concrete_lower,
                [
                    (first_upper, incremental_routes.as_slice()),
                    (second_upper, &[]),
                ],
            )
            .expect("lower-added replay batch");
        assert_eq!(lower_batch, expected_lower);

        let expected_upper = vec![
            machine
                .proof_store
                .prepare_replay_route(&machine, concrete_lower, first_upper, &[])
                .expect("concrete pairwise upper-added route"),
            machine
                .proof_store
                .prepare_replay_route(&machine, variable_lower, first_upper, &[])
                .expect("variable pairwise upper-added route"),
        ];
        let upper_batch = machine
            .proof_store
            .prepare_replay_routes_for_upper(
                &machine,
                [concrete_lower, variable_lower],
                first_upper,
            )
            .expect("upper-added replay batch");
        assert_eq!(upper_batch, expected_upper);
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
        machine
            .proof_store
            .record_projection_supports(lower_record, &proofs);
        let second_lower_record = BoundRecordId(70_001);
        let second_proofs = [SchemeProjectionProof {
            lower_record: second_lower_record,
            support: SchemeProjectionProofSupport::Claimed(claim),
        }];
        machine
            .proof_store
            .record_projection_supports(second_lower_record, &second_proofs);
        assert_eq!(
            machine
                .proof_store
                .projection_lower_records_for_root(claim),
            &[lower_record, second_lower_record],
            "the CPK reverse membership is first-insertion ordered and idempotent",
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
    fn cpk_8b_original_claim_commit_uses_the_allocation_snapshot() {
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
        let mut admission = machine
            .proof_store
            .try_prepare_original_claim_admission(record, producer, UpperReplayClaimKind::Direct)
            .expect("the CPK original-claim transaction has capacity");
        let expected = admission.occurrence.clone();
        machine
            .proof_store
            .commit_original_claim_admission(&mut admission);

        assert_eq!(
            machine.proof_store.upper_claims,
            vec![expected],
            "the CPK claim commit must consume its allocation-time prepared occurrence",
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

    fn cpk_gap_1_set_supports_and_admit_independent_formula(
        machine: &mut ConstraintMachine,
        record: BoundRecordId,
        supports: Vec<SchemeProjectionProofSupport>,
        clauses: Vec<ProjectionClause>,
    ) {
        machine
            .proof_store
            .projection_supports
            .insert(record, supports);
        for clause in clauses {
            assert_eq!(projection_lineage_rank(match clause {
                ProjectionClause::Standalone { attribution, .. }
                | ProjectionClause::DerivedUnary { attribution, .. }
                | ProjectionClause::ReplayConjunction { attribution, .. } => attribution,
            }), 0);
            let support = clause.support();
            machine.proof_store.record_projection_clause(
                record,
                RecordProofClauseLinkAdmission::independent(support, clause.record_clause()),
            );
        }
    }

    #[test]
    fn cpk_preflight_checked_state_is_shared_across_round_targets() {
        let mut machine = cpk_machine();
        let records = [
            cpk_gap_1_projection_record(&mut machine, 200),
            cpk_gap_1_projection_record(&mut machine, 201),
        ];
        let support = SchemeProjectionProofSupport::Independent(
            ProjectionProofCarrier::Incomplete,
        );
        for record in records {
            cpk_gap_1_set_supports_and_admit_independent_formula(
                &mut machine,
                record,
                vec![support],
                vec![ProjectionClause::Standalone {
                    support,
                    attribution: None,
                }],
            );
        }

        let mut round = ProjectionEvaluationRound::new();
        for (index, record) in records.into_iter().enumerate() {
            let owner = machine
                .bounds
                .record(record)
                .expect("projection target remains registered")
                .owner();
            let lowers = machine.scheme_projectable_lowers_in_round(owner, &mut round);
            assert_eq!(lowers.len(), 1);
            assert_eq!(lowers[0].record, record);
            let preflight = round
                .preflight
                .as_ref()
                .expect("the first claimed target creates one query preflight");
            assert_eq!(preflight.target_record, record);
            assert_eq!(
                preflight.checked_records.len(),
                index + 1,
                "successful record checks remain available to later targets",
            );
            assert!(records[..=index].iter().all(|record| {
                preflight.checked_records.contains(record)
            }));
        }
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

    #[cfg(debug_assertions)]
    #[test]
    fn cpk_8g_4b_evaluator_traps_missing_machine_issued_references() {
        let traps = |evaluation: Box<dyn FnOnce()>| {
            assert!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(evaluation)).is_err(),
                "a raw CPK referential-integrity violation must trip its debug assertion",
            );
        };

        traps(Box::new(|| {
            let machine = cpk_machine();
            let mut evaluator = CpkProjectionEvaluator::new(&machine, &machine.proof_store);
            evaluator.eval_record(BoundRecordId(u32::MAX));
        }));

        traps(Box::new(|| {
            let mut machine = cpk_machine();
            let record = cpk_gap_1_projection_record(&mut machine, 102);
            let support = SchemeProjectionProofSupport::Independent(
                ProjectionProofCarrier::Incomplete,
            );
            cpk_gap_1_set_supports_and_admit_independent_formula(
                &mut machine,
                record,
                vec![support],
                vec![ProjectionClause::DerivedUnary {
                    support,
                    carrier: DerivedUnaryCarrier::ReductionRoute(RowDerivationId(50_102)),
                    premise: ProofPremise::Constraint(ConstraintRecordId(u32::MAX)),
                    attribution: None,
                }],
            );
            let mut evaluator = CpkProjectionEvaluator::new(&machine, &machine.proof_store);
            evaluator.eval_record(record);
        }));

        traps(Box::new(|| {
            let mut machine = cpk_machine();
            let record = cpk_gap_1_projection_record(&mut machine, 103);
            let claim = UpperReplayClaimId(u32::MAX);
            let support = SchemeProjectionProofSupport::Claimed(claim);
            machine
                .proof_store
                .projection_supports
                .insert(record, vec![support]);
            machine.proof_store.record_projection_clause(
                record,
                RecordProofClauseLinkAdmission::claimed(
                    claim,
                    RecordProofClause::Standalone { support },
                    ClaimedAttributionSource::FlatRetained,
                    ClaimedProjectionProofSource::Original {
                        coverage_root: claim,
                        producer: ConstraintRecordId(u32::MAX),
                    },
                ),
            );
            let mut evaluator = CpkProjectionEvaluator::new(&machine, &machine.proof_store);
            evaluator.eval_record(record);
        }));
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
        let mut mutation = machine
            .try_prepare_scheme_projection_mutation(record, &[], &[admitted])
            .expect("test projection support mutation must have capacity");

        let later = ProjectionProofCarrier::Origin(OriginId(70_103));
        let _later_mutation = machine
            .try_prepare_scheme_projection_mutation(record, &[], &[later])
            .expect("test projection support mutation must have capacity");
        machine.commit_scheme_projection_mutation(&mut mutation);

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
    fn cpk_projection_support_duplicate_preflight_skips_bucket_snapshot_copy() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 104);
        let carrier = ProjectionProofCarrier::Origin(OriginId(70_104));
        cpk_4_add_independent_support(&mut machine, record, carrier);
        PROJECTION_SUPPORT_PREPARE_COPIED_ENTRIES.with(|cell| cell.set(0));

        let mutation = machine
            .try_prepare_scheme_projection_mutation(record, &[], &[carrier])
            .expect("duplicate support preflight must remain infallible");
        machine.apply_scheme_projection_mutation(mutation);

        assert_eq!(
            PROJECTION_SUPPORT_PREPARE_COPIED_ENTRIES.with(Cell::get),
            0,
            "an immutable duplicate check must return before copying either support bucket",
        );
        assert_eq!(
            machine.proof_store.projection_supports[&record],
            vec![SchemeProjectionProofSupport::Independent(carrier)],
        );

        let (_, claim) = cpk_7_record_original_claim(&mut machine, 105);
        let mutation = machine
            .try_prepare_scheme_projection_mutation(record, &[claim], &[])
            .expect("new claimed support preflight must have capacity");
        machine.apply_scheme_projection_mutation(mutation);
        PROJECTION_SUPPORT_PREPARE_COPIED_ENTRIES.with(|cell| cell.set(0));
        let mutation = machine
            .try_prepare_scheme_projection_mutation(record, &[claim], &[])
            .expect("duplicate claimed support preflight must remain infallible");
        machine.apply_scheme_projection_mutation(mutation);
        assert_eq!(
            PROJECTION_SUPPORT_PREPARE_COPIED_ENTRIES.with(Cell::get),
            0,
            "an unchanged claimed representative must also return before copying either bucket",
        );
    }

    #[test]
    fn cpk_projection_support_preflight_failure_is_atomic() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 102);
        machine
            .proof_store
            .record_projection_supports(record, &[]);
        let supports_before = machine.proof_store.projection_supports.clone();
        let claims_before = machine
            .proof_store
            .claimed_parents_by_lower_record
            .clone();
        let records_before = machine
            .proof_store
            .projection_lower_records_by_root
            .clone();
        let memberships_before = machine
            .proof_store
            .projection_lower_record_memberships
            .clone();
        machine
            .proof_store
            .fail_next_projection_support_reservation();

        let failure = machine
            .try_prepare_scheme_projection_mutation(
                record,
                &[],
                &[ProjectionProofCarrier::Incomplete],
            )
            .expect_err("injected support preflight must fail");
        assert!(matches!(failure, ProofFailure::ResourceExhausted { .. }));
        assert_eq!(machine.proof_store.projection_supports, supports_before);
        assert_eq!(
            machine.proof_store.claimed_parents_by_lower_record,
            claims_before
        );
        assert_eq!(
            machine.proof_store.projection_lower_records_by_root,
            records_before
        );
        assert_eq!(
            machine.proof_store.projection_lower_record_memberships,
            memberships_before
        );

        let mutation = machine
            .try_prepare_scheme_projection_mutation(
                record,
                &[],
                &[ProjectionProofCarrier::Incomplete],
            )
            .expect("the next transaction must reuse the unchanged state");
        machine.apply_scheme_projection_mutation(mutation);
        assert_eq!(
            machine.proof_store.projection_supports[&record],
            vec![SchemeProjectionProofSupport::Independent(
                ProjectionProofCarrier::Incomplete
            )]
        );
    }

    #[test]
    fn cpk_projection_clause_preflight_failure_is_atomic() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 103);
        let support = SchemeProjectionProofSupport::Independent(ProjectionProofCarrier::Incomplete);
        let admission = RecordProofClauseLinkAdmission::independent(
            support,
            RecordProofClause::Standalone { support },
        );
        machine
            .proof_store
            .fail_next_projection_clause_reservation();

        let failure = machine
            .proof_store
            .try_prepare_projection_clause_admission(record, &[admission])
            .expect_err("injected clause preflight must fail");
        assert!(matches!(failure, ProofFailure::ResourceExhausted { .. }));
        assert!(machine.proof_store.projection_clause_keys.is_empty());
        assert!(machine
            .proof_store
            .independent_projection_clause_link_keys
            .is_empty());
        assert!(machine.proof_store.projection_formulas.is_empty());
        assert!(
            machine
                .proof_store
                .projection_formula_support_keys
                .is_empty()
        );
        assert!(machine.proof_store.projection_attributions.is_empty());
        assert!(
            machine
                .proof_store
                .flat_retained_projection_attributions
                .is_empty()
        );

        let mut prepared = machine
            .proof_store
            .try_prepare_projection_clause_admission(record, &[admission])
            .expect("the next transaction must reuse the unchanged state")
            .expect("the clause must still be new");
        machine
            .proof_store
            .commit_projection_clause_admission(&mut prepared);
        assert!(machine.proof_store.projection_clause_link_is_registered(
            record,
            support,
            admission.clause,
        ));
        machine
            .proof_store
            .debug_assert_projection_formula_support_keys_match_linear_scan();
    }

    #[test]
    fn cpk_gap_1_project_lower_rejects_orphan_formula() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 1);
        let support = SchemeProjectionProofSupport::Independent(ProjectionProofCarrier::Incomplete);
        machine.proof_store.record_projection_clause(
            record,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::Standalone { support },
            ),
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
        machine
            .proof_store
            .projection_supports
            .insert(record, vec![support]);
        machine.proof_store.record_projection_clause(
            record,
            RecordProofClauseLinkAdmission::claimed(
                claim,
                RecordProofClause::Standalone { support },
                ClaimedAttributionSource::FlatRetained,
                ClaimedProjectionProofSource::Original {
                    coverage_root: claim,
                    producer: ConstraintRecordId(50_003),
                },
            ),
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
        machine
            .proof_store
            .projection_supports
            .insert(record, supports.clone());
        for (claim, support) in [root, representative].into_iter().zip(supports) {
            machine.proof_store.record_projection_clause(
                record,
                RecordProofClauseLinkAdmission::claimed(
                    claim,
                    RecordProofClause::Standalone { support },
                    ClaimedAttributionSource::FlatRetained,
                    ClaimedProjectionProofSource::Original {
                        coverage_root: root,
                        producer: ConstraintRecordId(50_004),
                    },
                ),
            );
        }
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
        machine.proof_store.record_projection_supports(
            record,
            &[SchemeProjectionProof {
                lower_record: record,
                support: stored_support,
            }],
        );
        machine.proof_store.record_projection_clause(
            record,
            RecordProofClauseLinkAdmission::claimed(
                root,
                RecordProofClause::Standalone {
                    support: formula_support,
                },
                ClaimedAttributionSource::FlatRetained,
                ClaimedProjectionProofSource::Original {
                    coverage_root: root,
                    producer: ConstraintRecordId(50_009),
                },
            ),
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
                evidence: projection_evidence_for_test(&machine, record),
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
        let clauses: Vec<_> = supports
            .iter()
            .copied()
            .map(|support| ProjectionClause::Standalone {
                support,
                attribution: None,
            })
            .collect();
        cpk_gap_1_set_supports_and_admit_independent_formula(
            &mut machine,
            record,
            supports,
            clauses.clone(),
        );
        machine
            .proof_store
            .force_noncanonical_projection_formula_order_for_test(record, clauses);
        let (actual, _) = project_lower_for_test(&machine, record);
        assert_eq!(
            actual,
            Err(ProofFailure::NonCanonicalProjectionOrder { record })
        );
    }

    #[test]
    fn cpk_gap_1_noncanonical_formula_precedes_dangling_clause_failure() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 205);
        let origins = [OriginId(98_000), OriginId(98_001), OriginId(98_002)];
        for origin in origins {
            machine.proof_store.record_occurrence(
                ProofResult::Semantic(SemanticFactRef::Constraint(ConstraintRecordId(origin.0))),
                ProofCause::Root(origin),
                vec![ProofParent::Origin(origin)],
                ProvenanceCompleteness::Complete,
            );
        }
        let supports = origins.map(|origin| {
            SchemeProjectionProofSupport::Independent(ProjectionProofCarrier::Origin(origin))
        });
        let clauses = supports
            .into_iter()
            .enumerate()
            .map(|(index, support)| {
                let dangling = ConstraintRecordId(220_000 + index as u32);
                ProjectionClause::DerivedUnary {
                    support,
                    carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                        parent: dangling,
                        rule: StructuralDerivationRule::FunctionReturn,
                    }),
                    premise: ProofPremise::Constraint(dangling),
                    attribution: None,
                }
            })
            .collect::<Vec<_>>();
        cpk_gap_1_set_supports_and_admit_independent_formula(
            &mut machine,
            record,
            supports.to_vec(),
            clauses.clone(),
        );
        machine
            .proof_store
            .force_noncanonical_projection_formula_order_for_test(
                record,
                vec![clauses[0], clauses[2], clauses[1]],
            );

        let (actual, _) = project_lower_for_test(&machine, record);
        assert_eq!(
            actual,
            Err(ProofFailure::NonCanonicalProjectionOrder { record }),
            "the complete order-only pass must precede allocation and dangling-clause validation",
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
        cpk_gap_1_set_supports_and_admit_independent_formula(
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
    fn cpk_8g_4b_formula_writer_canonicalizes_category_and_same_category_order() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 60);
        let other = cpk_gap_1_projection_record(&mut machine, 61);
        let low_carrier = ProjectionProofCarrier::Origin(OriginId(60_001));
        let high_carrier = ProjectionProofCarrier::Origin(OriginId(60_002));
        record_test_origin(&mut machine, record, OriginId(60_001));
        record_test_origin(&mut machine, record, OriginId(60_002));
        let low_parent = cpk_7_admit_inert_constraint(&mut machine, 60_101, "formula-low");
        let high_parent = cpk_7_admit_inert_constraint(&mut machine, 60_102, "formula-high");
        let low_support = SchemeProjectionProofSupport::Independent(low_carrier);
        let high_support = SchemeProjectionProofSupport::Independent(high_carrier);
        machine.proof_store.record_projection_supports(
            record,
            &[
                SchemeProjectionProof {
                    lower_record: record,
                    support: low_support,
                },
                SchemeProjectionProof {
                    lower_record: record,
                    support: high_support,
                },
            ],
        );

        let derived = |support, parent| {
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                        parent,
                        rule: StructuralDerivationRule::FunctionReturn,
                    }),
                    premise: ProofPremise::Record(other),
                },
            )
        };
        machine
            .proof_store
            .record_projection_clause(record, derived(high_support, high_parent));
        machine.proof_store.record_projection_clause(
            record,
            RecordProofClauseLinkAdmission::independent(
                low_support,
                RecordProofClause::Standalone {
                    support: low_support,
                },
            ),
        );
        machine
            .proof_store
            .record_projection_clause(record, derived(low_support, low_parent));

        let formula = &machine.proof_store.projection_formulas[&record];
        assert!(matches!(formula[0], ProjectionClause::Standalone { .. }));
        assert!(matches!(
            formula[1],
            ProjectionClause::DerivedUnary {
                support,
                ..
            } if support == low_support
        ));
        assert!(matches!(
            formula[2],
            ProjectionClause::DerivedUnary {
                support,
                ..
            } if support == high_support
        ));
        assert_eq!(formula.len(), 3);

        let (decision, round) = project_lower_for_test(&machine, record);
        assert!(matches!(decision, Ok(ProjectionDecision::Included { .. })));
        assert_eq!(round.cycle_cuts(), 0);
        assert!(!round.memo_sharing_disabled);
    }

    #[test]
    fn cpk_gap_1_incomplete_is_a_normal_independent_support() {
        let mut machine = cpk_machine();
        let record = cpk_gap_1_projection_record(&mut machine, 8);
        let carrier = ProjectionProofCarrier::Incomplete;
        let support = SchemeProjectionProofSupport::Independent(carrier);
        cpk_gap_1_set_supports_and_admit_independent_formula(
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
                evidence: projection_evidence_for_test(&machine, record),
            })
        );
    }

    #[test]
    fn cpk_original_standalone_writer_publishes_mixed_projection_contract() {
        let (machine, endpoint, owner, covered_root) =
            ConstraintMachine::compact_scheme_projection_unmatched_route_fixture(true);
        machine
            .proof_store
            .debug_assert_claimed_projection_audit_reconstructs();
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
                    .proof_store
                    .projection_clause_link_is_registered(record, *support, *clause),
                "each CPK formula entry must retain its exact typed clause link",
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
                evidence: projection_evidence_for_test(&machine, record),
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
            .try_prepare_scheme_projection_mutation(mixed_record, &[], &[independent])
            .expect("test projection support mutation must have capacity");
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
                    ProjectionDecision::Included { supports, .. } => Some((
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
        let ProjectionDecision::Included { supports, evidence } =
            decision.expect("complete CPK decision")
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
        let mut expected_parents = Vec::new();
        if let ProjectionEvidence::DecisiveClaimedArm(proof) = evidence {
            expected_parents.push(GeneralizationParent::BoundClaimProjectionProof {
                bound: *record,
                coverage_root: proof.coverage_root(),
                representative_claim: proof.representative_claim(),
                proof: Box::new(proof),
            });
        }
        expected_parents.extend(supports.independent_supports.iter().map(|carrier| {
                GeneralizationParent::BoundProjectionProof {
                    bound: *record,
                    carrier: *carrier,
                }
            }));
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
                .cloned()
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
                evidence: projection_evidence_for_test(&included, included_record),
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
                    .cloned()
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let expected_parents = match expected {
            ProjectionDecision::Excluded => Vec::new(),
            ProjectionDecision::Unclaimed => vec![GeneralizationParent::Bound(record)],
            ProjectionDecision::Included { supports, evidence } => {
                let mut parents = Vec::new();
                if let ProjectionEvidence::DecisiveClaimedArm(proof) = evidence {
                    parents.push(GeneralizationParent::BoundClaimProjectionProof {
                        bound: record,
                        coverage_root: proof.coverage_root(),
                        representative_claim: proof.representative_claim(),
                        proof: Box::new(proof),
                    });
                }
                parents.extend(supports.independent_supports.into_iter().map(|carrier| {
                    GeneralizationParent::BoundProjectionProof {
                        bound: record,
                        carrier,
                    }
                }));
                parents
            }
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
            no_ledger
                .proof_store
                .projection_formula_support_keys
                .len(),
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
                no_ledger
                    .proof_store
                    .projection_formula_support_keys
                    .len(),
            ),
            "the no-claim query must allocate no persistent proof state",
        );

        no_ledger
            .proof_store
            .projection_supports
            .insert(no_ledger_record, Vec::new());
        no_ledger
            .proof_store
            .force_present_empty_projection_formula_for_test(no_ledger_record);
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
                evidence: projection_evidence_for_test(&standalone, standalone_record),
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
                evidence: projection_evidence_for_test(&derived, derived_record),
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
                evidence: projection_evidence_for_test(&incomplete, incomplete_record),
            },
        );
    }

    #[test]
    fn cpk_gap_1_included_empty_keeps_its_decisive_claimed_parent() {
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
        let ProjectionDecision::Included { supports, .. } =
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
                ClaimedProjectionProofSource::DerivedUnary {
                    coverage_root: uncovered.coverage_root,
                    result: ConstraintRecordId(0),
                },
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
        let evidence = projection_evidence_for_test(&machine, record);
        let ProjectionEvidence::DecisiveClaimedArm(proof) = evidence else {
            panic!("the exact derived-unary clause must be the decisive claimed arm");
        };
        let ClaimedProjectionProofKind::DerivedUnary {
            result: decisive_result,
            ..
        } = proof.kind()
        else {
            panic!("the fixture must retain its derived-unary decisive arm");
        };
        assert_eq!(
            project_lower_for_test(&machine, record).0,
            Ok(ProjectionDecision::Included {
                supports: ProjectionSupportSet::default(),
                evidence,
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
        let exact_parent = GeneralizationParent::BoundClaimProjectionProof {
            bound: record,
            coverage_root: proof.coverage_root(),
            representative_claim: proof.representative_claim(),
            proof: Box::new(proof),
        };
        assert!(
            drafts
                .iter()
                .flat_map(|draft| &draft.incoming)
                .flat_map(|edge| &edge.parents)
                .any(|parent| *parent == exact_parent),
            "Included(empty) must retain the exact clause that established inclusion",
        );

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
                .any(|parent| matches!(
                    parent,
                    crate::constraints::logical_proof_snapshot::CanonicalGeneralizationParent::BoundClaimProjectionProof {
                        bound: found,
                        ..
                    } if *found == record.0 as usize
                )),
            "logical proof snapshots must retain the decisive certificate parent",
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
        let result_root = snapshot
            .portable
            .roots
            .iter()
            .position(|root| {
                matches!(
                    root,
                    crate::constraints::logical_proof_snapshot::CanonicalPortableRoot::Constraint(
                        found
                    ) if *found == decisive_result.0 as usize
                )
            })
            .expect("portable decisive-result root");
        let result_anchor = snapshot.portable.root_anchors[result_root]
            .expect("portable decisive-result anchor");
        let result_node = snapshot.portable.snapshot.anchors()[result_anchor].node;
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
        let edges = snapshot.portable.snapshot.edges();
        assert!(edges.iter().any(|edge| {
            witness_nodes.contains(&edge.child)
                && edge.parents.contains(&target_node)
                && matches!(
                    edge.kind,
                    poly::provenance::PortableProvenanceEdgeKind::Generalization(_)
                )
        }), "portable generalized witnesses must retain the qualified bound node as the filtered-view parent");
        assert!(edges.iter().any(|edge| {
            edge.child == target_node
                && edge.parents.as_slice() == [result_node]
                && edge.kind
                    == poly::provenance::PortableProvenanceEdgeKind::Bound(
                        poly::provenance::PortableBoundDerivationKind::Constraint,
                    )
        }), "the filtered qualified-bound view must expose the exact decisive result");
        assert!(edges.iter().all(|edge| {
            !witness_nodes.contains(&edge.child) || !edge.parents.contains(&result_node)
        }), "the decisive result must be reached through the filtered bound, not a producer shortcut");
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
            machine
                .proof_store
                .force_projection_clause_lineage_for_test(record, lineage);
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
                    evidence: projection_evidence_for_test(&machine, record),
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
                ClaimedProjectionProofSource::Original {
                    coverage_root: fixture.coverage_root,
                    producer: ConstraintRecordId(10_000),
                },
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
        let mutation = fixture.machine.try_prepare_scheme_projection_mutation(
            record,
            &[fixture.coverage_root],
            &[],
        ).expect("test projection support mutation must have capacity");
        fixture.machine.apply_scheme_projection_mutation(mutation);
        fixture.machine.register_cpk_projection_clause_for_test(
            record,
            RecordProofClauseLinkAdmission::claimed(
                fixture.coverage_root,
                RecordProofClause::Standalone {
                    support: SchemeProjectionProofSupport::Claimed(fixture.coverage_root),
                },
                ClaimedAttributionSource::FlatRetained,
                ClaimedProjectionProofSource::Original {
                    coverage_root: fixture.coverage_root,
                    producer: ConstraintRecordId(10_000),
                },
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
                evidence: projection_evidence_for_test(&fixture.machine, record),
            },
        );
        let ProjectionDecision::Included { supports, .. } = before else {
            panic!("same-root fixture must be included");
        };
        let before_representative = supports
            .uncovered_claims
            .iter()
            .find(|support| support.coverage_root == fixture.coverage_root)
            .expect("same-root support")
            .representative_claim;
        let mutation = fixture.machine.try_prepare_scheme_projection_mutation(
            record,
            &[replacement_claim],
            &[],
        ).expect("test projection support mutation must have capacity");
        fixture.machine.apply_scheme_projection_mutation(mutation);
        let expected = ProjectionDecision::Included {
            supports: ProjectionSupportSet {
                uncovered_claims: vec![ProjectionClaimSupport {
                    coverage_root: fixture.coverage_root,
                    representative_claim: replacement_claim,
                }],
                independent_supports: Vec::new(),
            },
            evidence: projection_evidence_for_test(&fixture.machine, record),
        };
        let ProjectionDecision::Included { supports, .. } = &expected else {
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
                evidence: projection_evidence_for_test(&fixture.machine, record),
            };
            let (actual, _) = project_lower_for_test(&fixture.machine, record);
            assert_eq!(actual, Ok(expected.clone()), "arrival order {order:?}");
            assert_single_lower_matches_all_four_cpk_consumers(
                &fixture.machine,
                owner,
                record,
                expected.clone(),
            );
            let ProjectionDecision::Included { supports, evidence } = expected else {
                panic!("permutation fixture must be included");
            };
            let representative = supports
                .uncovered_claims
                .iter()
                .find(|support| support.coverage_root == fixture.coverage_root)
                .expect("same-root permutation support");
            assert_eq!(representative.coverage_root, fixture.coverage_root);
            let decision = ProjectionDecision::Included { supports, evidence };
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
            .proof_store
            .record_projection_supports(record, &[]);
        let mutation = machine
            .try_prepare_scheme_projection_mutation(record, &[], &[carrier])
            .expect("test projection support mutation must have capacity");
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

    fn cpk_3_cpk_only_replay_admission_fixture() -> CpkReplayAdmissionFixture {
        let mut machine = cpk_machine();
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

    fn cpk_3_replay_fixture() -> ConstraintMachine {
        let mut machine = cpk_machine();
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

        let replay = machine.proof_store.replay_finite_map[0].carrier;
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

    fn assert_cpk_claim_payload_matches_semantic_snapshot(
        machine: &ConstraintMachine,
        actual: &UpperClaimOccurrence,
    ) {
        let record = machine
            .bounds
            .record(actual.current_record)
            .expect("CPK claim's semantic BoundRecord remains present");
        let BoundEndpoint::Upper(endpoint) = record.endpoint() else {
            panic!("CPK upper claim must point at an upper BoundRecord")
        };
        assert_eq!(actual.lineage, actual.full_lineage.projection_lineage());
        assert_eq!(
            machine.proof_store.upper_claim(actual.claim),
            Some(actual),
            "the dense CPK ID resolves to the complete accepted occurrence",
        );
        assert_eq!(record.owner(), machine.bounds.record(actual.current_record).unwrap().owner());
        assert_eq!(
            record.weights(),
            machine.bounds.record(actual.current_record).unwrap().weights()
        );
        assert_eq!(BoundEndpoint::Upper(endpoint), record.endpoint());
    }

    #[test]
    fn cpk_claim_payload_covers_five_lineages_and_move_from_semantic_records() {
        let mut machine = cpk_3_replay_fixture();
        cpk_record_original_claim_with_kind(
            &mut machine,
            100,
            UpperReplayClaimKind::Reduced(UnweightedRowReductionRecordId(0)),
        );
        let cpk_claims = machine.proof_store.upper_claims.clone();
        assert_eq!(cpk_claims.len(), machine.proof_store.upper_claim_index.len());

        for actual in &cpk_claims {
            assert_eq!(
                actual.claim.0 as usize,
                machine.proof_store.upper_claim_index[&actual.claim]
            );
            assert_cpk_claim_payload_matches_semantic_snapshot(&machine, actual);
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
        let reduction_claim = machine
            .proof_store
            .reduction_claim(UnweightedRowReductionRecordId(0))
            .expect("CPK reduction-state index retains its canonical claim");
        assert_eq!(
            machine.proof_store.upper_claim(reduction_claim).unwrap().claim,
            reduction_claim,
            "the CPK reduction-state index remains referentially closed"
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

        let actual_after_move = &machine.proof_store.upper_claims[moved_index];
        assert_cpk_claim_payload_matches_semantic_snapshot(&machine, actual_after_move);
        assert_eq!(actual_after_move.current_record, moved_record);
        assert_eq!(actual_after_move.kind, before_move.kind);
        assert_eq!(actual_after_move.full_lineage, before_move.full_lineage);
        assert_eq!(machine.proof_store.derived_claim(moved_record, actual_after_move.coverage_root),
            Some(moved_claim), "the moved derived lineage remains indexed by CPK");
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
        machine.admit_projection_target_for_test(
            ProjectionTarget::Constraint(producer),
            lower_record,
        );
        let cpk_before = (
            machine.proof_store.upper_claims.len(),
            machine.proof_store.upper_claim_index.len(),
            machine.proof_store.original_claim_by_record_and_producer.len(),
            machine.proof_store.root_claim_by_producer_constraint.len(),
            machine.proof_store.claims_by_upper_record.len(),
            machine.proof_store.projection_supports.len(),
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

        let registration = machine
            .try_original_upper_replay_claim(
                upper_record,
                producer,
                UpperReplayClaimKind::Direct,
            )
            .expect("the failed preflight leaves its dense ID unconsumed");
        assert_eq!(registration.claim, next_id);
        assert_eq!(machine.proof_store.upper_claims[next_id.0 as usize].claim, next_id);
        assert_eq!(
            machine.proof_store.original_claim(upper_record, producer),
            Some(next_id)
        );
        assert_eq!(
            machine.proof_store.root_claim_by_producer_constraint[&producer],
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
        assert_eq!(machine.proof_store.upper_claims[first.0 as usize].coverage_root, root);
        assert_eq!(machine.proof_store.upper_claims[second.0 as usize].coverage_root, root);
        assert_eq!(machine.proof_store.upper_claims[first.0 as usize].full_lineage.depth(), 1);
        assert_eq!(machine.proof_store.upper_claims[second.0 as usize].full_lineage.depth(), 2);
        for claim in [root, first, second] {
            assert_cpk_claim_payload_matches_semantic_snapshot(
                &machine,
                &machine.proof_store.upper_claims[claim.0 as usize],
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
            ),
            before,
            "a failed move preflight commits no partial CPK state",
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
        assert!(machine.proof_store.live_coverage.contains(&(first, first_state)));
        assert!(machine.proof_store.live_coverage.contains(&(second, second_state)));
        assert_eq!(machine.proof_store.live_coverage_states_for_test(first),
            Some(&FxHashSet::from_iter([first_state])),
            "root liveness follows stable claim identity and is not reassigned by a move");
        assert_eq!(machine.proof_store.live_coverage_states_for_test(second),
            Some(&FxHashSet::from_iter([second_state])));
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
            machine
                .proof_store
                .first_qualified_parent_source_by_root
                .clone(),
        );
        machine
            .proof_store
            .fail_next_qualified_parent_reservation();
        machine.admit_claim_qualified_parents(result, &parents);
        assert_eq!(
            (
                machine.proof_store.qualified_parent_keys.clone(),
                machine.proof_store.qualified_parents_by_result.clone(),
                machine
                    .proof_store
                    .first_qualified_parent_source_by_root
                    .clone(),
            ),
            cpk_before,
            "a failed CPK preflight commits no key, first-source, or result-local order state",
        );
        machine.admit_claim_qualified_parents(result, &parents[..2]);
        // Exercise the non-empty incremental merge. In test builds the merge helper compares
        // this result against a full re-sort of the same existing and newly accepted entries.
        machine.admit_claim_qualified_parents(result, &parents[2..]);
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
            machine
                .proof_store
                .first_qualified_parent_source(result, first),
            Some(FirstQualifiedParentSource::Replay),
            "the event-local first accepted parent wins independently of canonical storage order",
        );
    }

    #[test]
    fn cpk_qualified_parent_first_source_capacity_tracks_the_source_delta() {
        let mut machine = cpk_machine();
        let (record, claim) = cpk_7_record_original_claim(&mut machine, 987);
        let result = ConstraintRecordId(96_988);
        let parents = (0..64)
            .map(|index| ClaimQualifiedParent::ReplayConstraint {
                parent_claim: claim,
                parent_side: ReplayClaimParentSide::Lower,
                replay: BinaryReplayDerivation {
                    pivot: TypeVar(97_000 + index),
                    lower: record,
                    upper: record,
                    rule: ReplayRule::LowerBoundAdded,
                },
            })
            .collect::<Vec<_>>();

        let mut admission = machine
            .proof_store
            .try_prepare_qualified_parent_admission(result, &parents)
            .expect("the representative first-source capacity fixture must prepare");
        assert_eq!(admission.accepted.len(), parents.len());
        assert_eq!(admission.new_first_sources.len(), 1);
        assert!(
            admission.pending_first_source_capacity <= 4,
            "the pending set must grow with the one real source, not all input parents: {:?}",
            admission.pending_first_source_capacity,
        );
        assert!(
            admission.new_first_sources.capacity() <= 4,
            "the source delta must grow with the one real source, not all input parents: {:?}",
            admission.new_first_sources.capacity(),
        );

        machine
            .proof_store
            .commit_qualified_parent_admission(&mut admission);
        assert_eq!(
            machine
                .proof_store
                .first_qualified_parent_source(result, claim),
            Some(FirstQualifiedParentSource::Replay),
        );
        assert_eq!(
            machine
                .proof_store
                .qualified_parents_for_result(result)
                .len(),
            parents.len(),
        );
    }

    #[test]
    fn qorf_a_exact_replay_relation_oracle_covers_new_and_late_occurrence_parents() {
        let mut machine = cpk_machine();
        let (lower_record, smaller_root) = cpk_7_record_original_claim(&mut machine, 98_100);
        let (upper_record, larger_root) = cpk_7_record_original_claim(&mut machine, 98_101);
        let result = ConstraintRecordId(98_102);
        let carrier = BinaryReplayDerivation {
            pivot: TypeVar(98_103),
            lower: lower_record,
            upper: upper_record,
            rule: ReplayRule::LowerBoundAdded,
        };
        let admit = |machine: &mut ConstraintMachine, claim, parent_side: ReplayClaimParentSide| {
            machine.admit_claim_qualified_parents(
                result,
                &[ClaimQualifiedParent::ReplayConstraint {
                    parent_claim: claim,
                    parent_side,
                    replay: carrier,
                }],
            );
            machine.proof_store.record_cpk_replay_parent_snapshot(
                result,
                carrier,
                &[SideTaggedReplayClaim { claim, parent_side }],
            );
            machine
                .proof_store
                .debug_assert_qorf_a_replay_relation_matches();
        };

        // Admit the larger root first, then extend both sides with an earlier canonical root. The
        // future arm projection must rekey, while the exact relation remains byte-for-byte equal.
        admit(&mut machine, larger_root, ReplayClaimParentSide::Upper);
        admit(&mut machine, smaller_root, ReplayClaimParentSide::Lower);
        admit(&mut machine, smaller_root, ReplayClaimParentSide::Upper);
        let snapshot = machine.proof_store.qorf_a_replay_relation_snapshot();
        snapshot.assert_exact_parity();
        assert_eq!(snapshot.qualified.len(), 3);

        // Persistent duplicates on both writers retain the first exact metadata and add nothing.
        admit(&mut machine, smaller_root, ReplayClaimParentSide::Lower);
        assert_eq!(
            machine
                .proof_store
                .qorf_a_replay_relation_snapshot()
                .qualified
                .len(),
            3,
        );
    }

    #[test]
    fn qorf_a_side_chunk_boundaries_and_middle_split_match_sorted_model() {
        let mut tree = QorfModelChunkAvl::<(u8, u16), QORF_REPLAY_PARENT_CHUNK_CAPACITY>::new();
        let mut expected = std::collections::BTreeSet::new();
        for suffix in (0..256).step_by(2) {
            assert!(tree.insert((7, suffix)));
            expected.insert((7, suffix));
        }
        assert_eq!(tree.len, 128);
        assert!(
            tree.insert((7, 127)),
            "full-chunk middle insertion must split"
        );
        expected.insert((7, 127));
        tree.assert_invariants();
        assert_eq!(tree.flatten(), expected.iter().copied().collect::<Vec<_>>());
        assert_eq!(tree.max_scanned_existing_per_insert, 128);

        for suffix in 256..520 {
            assert!(tree.insert((7, suffix)));
            expected.insert((7, suffix));
        }
        tree.assert_invariants();
        assert_eq!(tree.flatten(), expected.iter().copied().collect::<Vec<_>>());
        assert!(
            tree.nodes
                .iter()
                .all(|node| !node.entries.is_empty() && node.entries.len() <= 128)
        );
        assert!(tree.nodes.len() >= 3, "fixture must cross multiple chunks");
    }

    #[test]
    fn qorf_a_outer_replay_event_survives_inner_parent_reservation_failure() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let events_before = fixture.machine.proof_store.replay_admissions.len();
        let relation_before = fixture
            .machine
            .proof_store
            .qorf_a_replay_relation_snapshot();
        let occurrences_before = fixture.machine.proof_store.replay_finite_map.len();
        fixture
            .machine
            .proof_store
            .fail_next_qualified_parent_reservation();

        fixture.machine.apply_cpk_replay_parent_arrival_for_test(
            fixture.result,
            fixture.carrier,
            fixture.coverage_root,
        );

        assert_eq!(
            fixture.machine.proof_store.replay_admissions.len(),
            events_before + 1
        );
        assert_eq!(
            fixture
                .machine
                .proof_store
                .qorf_a_replay_relation_snapshot(),
            relation_before,
            "inner reservation failure must leave both exact-parent faces unchanged",
        );
        assert_eq!(
            fixture.machine.proof_store.replay_finite_map.len(),
            occurrences_before
        );
        assert!(fixture.machine.proof_terminal_failure().is_some());
    }

    #[test]
    fn qorf_b_every_inner_reservation_failure_keeps_only_the_outer_event() {
        for point in [
            QorfReplayReservationFailurePoint::AfterQualifiedSourceSummary,
            QorfReplayReservationFailurePoint::AfterQualified,
            QorfReplayReservationFailurePoint::AfterSideChunks,
            QorfReplayReservationFailurePoint::AfterReplayFiniteMap,
            QorfReplayReservationFailurePoint::AfterReplayFiniteMapIndex,
            QorfReplayReservationFailurePoint::AfterReplayResultIndex,
            QorfReplayReservationFailurePoint::AfterOccurrence,
            QorfReplayReservationFailurePoint::AfterArm,
            QorfReplayReservationFailurePoint::AfterRootWinner,
            QorfReplayReservationFailurePoint::AfterSummary,
            QorfReplayReservationFailurePoint::AfterProofOccurrence,
        ] {
            let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
            let events_before = fixture.machine.proof_store.replay_admissions.len();
            let inner_before = (
                fixture.machine.proof_store.qualified_parent_keys.clone(),
                fixture
                    .machine
                    .proof_store
                    .qualified_parents_by_result
                    .clone(),
                fixture
                    .machine
                    .proof_store
                    .first_qualified_parent_source_by_root
                    .clone(),
                fixture.machine.proof_store.replay_finite_map.clone(),
                fixture.machine.proof_store.replay_finite_map_index.clone(),
                fixture.machine.proof_store.replay_indices_by_result.clone(),
                fixture.machine.proof_store.replay_parent_chunks.clone(),
                fixture.machine.proof_store.replay_qualified_arms.clone(),
                fixture
                    .machine
                    .proof_store
                    .canonical_qualified_parent_by_root
                    .clone(),
                fixture
                    .machine
                    .proof_store
                    .non_replay_qualified_parents
                    .clone(),
                fixture.machine.proof_store.first_replay_witnesses.clone(),
                fixture.machine.proof_store.occurrences.clone(),
            );
            fixture
                .machine
                .proof_store
                .fail_qorf_replay_reservation_after(point);
            fixture.machine.apply_cpk_replay_parent_arrival_for_test(
                fixture.result,
                fixture.carrier,
                fixture.coverage_root,
            );
            assert_eq!(
                fixture.machine.proof_store.replay_admissions.len(),
                events_before + 1
            );
            assert_eq!(
                (
                    fixture.machine.proof_store.qualified_parent_keys.clone(),
                    fixture
                        .machine
                        .proof_store
                        .qualified_parents_by_result
                        .clone(),
                    fixture
                        .machine
                        .proof_store
                        .first_qualified_parent_source_by_root
                        .clone(),
                    fixture.machine.proof_store.replay_finite_map.clone(),
                    fixture.machine.proof_store.replay_finite_map_index.clone(),
                    fixture.machine.proof_store.replay_indices_by_result.clone(),
                    fixture.machine.proof_store.replay_parent_chunks.clone(),
                    fixture.machine.proof_store.replay_qualified_arms.clone(),
                    fixture
                        .machine
                        .proof_store
                        .canonical_qualified_parent_by_root
                        .clone(),
                    fixture
                        .machine
                        .proof_store
                        .non_replay_qualified_parents
                        .clone(),
                    fixture.machine.proof_store.first_replay_witnesses.clone(),
                    fixture.machine.proof_store.occurrences.clone(),
                ),
                inner_before,
                "QORF inner reservation failure at {point:?} must commit no inner face",
            );
        }
    }

    #[test]
    fn qorf_c_side_membership_and_cursor_match_the_legacy_oracle() {
        let mut machine = cpk_machine();
        let (lower, lower_claim) = cpk_7_record_original_claim(&mut machine, 109_900);
        let (upper, upper_claim) = cpk_7_record_original_claim(&mut machine, 109_901);
        let result = ConstraintRecordId(109_902);
        let carrier = BinaryReplayDerivation {
            pivot: TypeVar(109_903),
            lower,
            upper,
            rule: ReplayRule::LowerBoundAdded,
        };
        for (claim, side) in [
            (upper_claim, ReplayClaimParentSide::Upper),
            (lower_claim, ReplayClaimParentSide::Lower),
        ] {
            let parent = ClaimQualifiedParent::ReplayConstraint {
                parent_claim: claim,
                parent_side: side,
                replay: carrier,
            };
            let mut transaction = machine
                .proof_store
                .try_prepare_replay_qualified_parent_transaction(result, carrier, &[parent])
                .expect("QORF-C exact parent must prepare");
            assert_eq!(transaction.accepted().len(), 1);
            machine
                .proof_store
                .commit_replay_qualified_parent_transaction(&mut transaction);
            machine.proof_store.record_replay_admission(
                Some(result),
                carrier,
                ReplayAdmissionDisposition::ExactDuplicate,
            );
        }

        let lower_root = machine.proof_store.claim_coverage_root(lower_claim).unwrap();
        let upper_root = machine.proof_store.claim_coverage_root(upper_claim).unwrap();
        assert!(machine.proof_store.exact_replay_qualified_parent_is_registered(
            result,
            carrier,
            ReplayClaimParentSide::Lower,
            lower_root,
        ));
        assert!(machine.proof_store.exact_replay_qualified_parent_is_registered(
            result,
            carrier,
            ReplayClaimParentSide::Upper,
            upper_root,
        ));
        assert!(!machine.proof_store.exact_replay_qualified_parent_is_registered(
            result,
            carrier,
            ReplayClaimParentSide::Lower,
            upper_root,
        ));
        assert!(!machine.proof_store.exact_replay_qualified_parent_is_registered(
            result,
            carrier,
            ReplayClaimParentSide::Upper,
            lower_root,
        ));

        let occurrence = &machine.proof_store.replay_finite_map[0];
        for (side, legacy) in [
            (ReplayClaimParentSide::Lower, &occurrence.lower_parents),
            (ReplayClaimParentSide::Upper, &occurrence.upper_parents),
        ] {
            let actual = machine
                .proof_store
                .replay_parents_for_occurrence_side(occurrence, side)
                .collect::<Vec<_>>();
            let mut expected = legacy.clone();
            expected.sort_unstable_by_key(|entry| entry.coverage_root);
            assert_eq!(actual, expected);
        }

        let duplicate = ClaimQualifiedParent::ReplayConstraint {
            parent_claim: lower_claim,
            parent_side: ReplayClaimParentSide::Lower,
            replay: carrier,
        };
        let duplicate_transaction = machine
            .proof_store
            .try_prepare_replay_qualified_parent_transaction(result, carrier, &[duplicate])
            .expect("QORF-C persistent duplicate must prepare as a no-op");
        assert!(duplicate_transaction.accepted().is_empty());
    }

    #[test]
    fn qorf_d0_rekeys_one_arm_and_replaces_replay_root_winner_with_structural() {
        let mut machine = cpk_machine();
        let (lower, lower_claim) = cpk_7_record_original_claim(&mut machine, 120_900);
        let (upper, upper_claim) = cpk_7_record_original_claim(&mut machine, 120_901);
        let result = ConstraintRecordId(120_902);
        let carrier = BinaryReplayDerivation {
            pivot: TypeVar(120_903),
            lower,
            upper,
            rule: ReplayRule::LowerBoundAdded,
        };
        for (claim, side) in [
            (upper_claim, ReplayClaimParentSide::Upper),
            (lower_claim, ReplayClaimParentSide::Lower),
        ] {
            let mut transaction = machine
                .proof_store
                .try_prepare_replay_qualified_parent_transaction(
                    result,
                    carrier,
                    &[ClaimQualifiedParent::ReplayConstraint {
                        parent_claim: claim,
                        parent_side: side,
                        replay: carrier,
                    }],
                )
                .expect("QORF-D0 replay arm admission");
            machine
                .proof_store
                .commit_replay_qualified_parent_transaction(&mut transaction);
        }
        assert_eq!(
            machine.proof_store.replay_qualified_arms.flatten(result),
            vec![ReplayFiniteMapEntryId(0)],
            "late smaller-side extension rekeys rather than duplicating the occurrence arm",
        );
        assert_eq!(
            machine
                .proof_store
                .canonical_qualified_parent_by_root
                .flatten(result)
                .len(),
            2,
        );

        let lower_root = machine
            .proof_store
            .claim_coverage_root(lower_claim)
            .unwrap();
        assert_eq!(
            machine
                .proof_store
                .first_qualified_parent_source(result, lower_root),
            Some(FirstQualifiedParentSource::Replay),
        );
        let structural = ClaimQualifiedParent::StructuralConstraint {
            parent_claim: lower_claim,
            derivation: StructuralDerivation {
                parent: ConstraintRecordId(120_904),
                rule: StructuralDerivationRule::FunctionReturn,
            },
        };
        let mut admission = machine
            .proof_store
            .try_prepare_qualified_parent_admission(result, &[structural])
            .expect("QORF-D0 structural root winner replacement");
        machine
            .proof_store
            .commit_qualified_parent_admission(&mut admission);
        let winner = machine
            .proof_store
            .canonical_qualified_parent_by_root
            .get(result, lower_root)
            .expect("root winner remains present");
        assert!(matches!(
            winner.winner,
            CanonicalQualifiedParentRef::NonReplay { .. }
        ));
        assert_eq!(
            machine
                .proof_store
                .first_qualified_parent_source(result, lower_root),
            Some(FirstQualifiedParentSource::Replay),
            "canonical winner replacement must not rewrite historical first-source state",
        );
        machine
            .proof_store
            .debug_assert_qorf_d0_projections_match_legacy(result);
    }

    #[test]
    fn qorf_d0_root_winner_writer_order_matrix_matches_legacy() {
        #[derive(Clone, Copy)]
        enum Event {
            Replay,
            Structural,
            Reduction,
        }

        fn assert_root_winner_matches_legacy(
            fixture: &CpkReplayAdmissionFixture,
            root: UpperReplayClaimId,
        ) {
            let expected = fixture
                .machine
                .proof_store
                .qualified_parents_for_result(fixture.result)
                .iter()
                .copied()
                .find(|entry| entry.coverage_root == root)
                .expect("writer-order fixture has a root-qualified parent");
            let winner = fixture
                .machine
                .proof_store
                .canonical_qualified_parent_by_root
                .get(fixture.result, root)
                .expect("writer-order fixture has a projected root winner");
            let actual = fixture.machine.proof_store.qorf_exact_parent_for_root_ref(
                fixture.result,
                root,
                winner.winner,
            );
            assert_eq!(actual, expected);
            fixture
                .machine
                .proof_store
                .debug_assert_qorf_d0_projections_match_legacy(fixture.result);
        }

        for order in [
            &[Event::Structural, Event::Replay][..],
            &[Event::Replay, Event::Structural],
            &[Event::Reduction, Event::Replay],
            &[Event::Replay, Event::Reduction],
            &[Event::Replay, Event::Reduction, Event::Structural],
            &[Event::Structural, Event::Replay, Event::Reduction],
        ] {
            let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
            let root = fixture.coverage_root;
            let structural = StructuralDerivation {
                parent: ConstraintRecordId(120_970),
                rule: StructuralDerivationRule::FunctionReturn,
            };
            let row = fixture.machine.intern_row_derivation(
                RowDerivationRule::UnweightedReduction,
                vec![RowDerivationParent::Constraint(fixture.result)],
                Vec::new(),
            );
            let key = fixture.machine.constraint_records[fixture.result.0 as usize]
                .key
                .clone();
            assert!(!fixture.machine.enqueue_row_derived_subtype(
                key.lower,
                key.weights,
                key.upper,
                row,
            ));

            for event in order.iter().copied() {
                match event {
                    Event::Replay => {
                        fixture.machine.apply_cpk_replay_parent_arrival_for_test(
                            fixture.result,
                            fixture.carrier,
                            root,
                        );
                    }
                    Event::Structural => {
                        let parent = ClaimQualifiedParent::StructuralConstraint {
                            parent_claim: root,
                            derivation: structural,
                        };
                        assert!(fixture.machine.register_structural_claim_parent_admission(
                            fixture.result,
                            &[parent],
                            structural,
                            false,
                        ));
                    }
                    Event::Reduction => fixture
                        .machine
                        .register_reduction_route_claim_parent(fixture.result, row, root),
                }
                assert_root_winner_matches_legacy(&fixture, root);
            }
        }

        // Exercise the comparator's side and representative-claim tie fields through the real
        // prepared replay writer, in both arrival orders, rather than only in comparator tests.
        for upper_first in [false, true] {
            let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
            let root = fixture.coverage_root;
            let same_root = add_same_root_replay_claim(
                &mut fixture,
                TypeVar(120_980),
                ConstraintRecordId(120_981),
            );
            let ordered = if upper_first {
                [
                    (same_root, ReplayClaimParentSide::Upper),
                    (root, ReplayClaimParentSide::Lower),
                ]
            } else {
                [
                    (root, ReplayClaimParentSide::Lower),
                    (same_root, ReplayClaimParentSide::Upper),
                ]
            };
            for (claim, side) in ordered {
                let parent = ClaimQualifiedParent::ReplayConstraint {
                    parent_claim: claim,
                    parent_side: side,
                    replay: fixture.carrier,
                };
                let mut transaction = fixture
                    .machine
                    .proof_store
                    .try_prepare_replay_qualified_parent_transaction(
                        fixture.result,
                        fixture.carrier,
                        &[parent],
                    )
                    .expect("tie-field replay admission prepares");
                fixture
                    .machine
                    .proof_store
                    .commit_replay_qualified_parent_transaction(&mut transaction);
                assert_root_winner_matches_legacy(&fixture, root);
            }
        }
    }

    #[test]
    fn qorf_d0_compatibility_snapshot_preserves_existing_non_replay_winner() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let structural = StructuralDerivation {
            parent: ConstraintRecordId(120_990),
            rule: StructuralDerivationRule::FunctionReturn,
        };
        fixture.machine.admit_claim_qualified_parent(
            fixture.result,
            ClaimQualifiedParent::StructuralConstraint {
                parent_claim: fixture.coverage_root,
                derivation: structural,
            },
        );
        fixture.machine.admit_claim_qualified_parent(
            fixture.result,
            ClaimQualifiedParent::ReplayConstraint {
                parent_claim: fixture.coverage_root,
                parent_side: ReplayClaimParentSide::Lower,
                replay: fixture.carrier,
            },
        );
        fixture.machine.proof_store.record_cpk_replay_parent_snapshot(
            fixture.result,
            fixture.carrier,
            &[SideTaggedReplayClaim {
                claim: fixture.coverage_root,
                parent_side: ReplayClaimParentSide::Lower,
            }],
        );

        let winner = fixture
            .machine
            .proof_store
            .canonical_qualified_parent_by_root
            .get(fixture.result, fixture.coverage_root)
            .expect("compatibility rebuild preserves the structural root winner");
        assert!(matches!(
            winner.winner,
            CanonicalQualifiedParentRef::NonReplay { .. }
        ));
        fixture
            .machine
            .proof_store
            .debug_assert_qorf_d0_projections_match_legacy(fixture.result);
    }

    #[test]
    fn qorf_d0_non_replay_root_reservation_failure_commits_no_inner_state_or_event() {
        let mut machine = cpk_machine();
        let (_, parent_claim) = cpk_7_record_original_claim(&mut machine, 120_950);
        let result = ConstraintRecordId(120_951);
        let parent = ClaimQualifiedParent::StructuralConstraint {
            parent_claim,
            derivation: StructuralDerivation {
                parent: ConstraintRecordId(120_952),
                rule: StructuralDerivationRule::FunctionReturn,
            },
        };
        let before = (
            machine.proof_store.qualified_parent_keys.clone(),
            machine.proof_store.qualified_parents_by_result.clone(),
            machine
                .proof_store
                .first_qualified_parent_source_by_root
                .clone(),
            machine
                .proof_store
                .canonical_qualified_parent_by_root
                .clone(),
            machine.proof_store.non_replay_qualified_parents.clone(),
            machine.proof_store.replay_admissions.clone(),
        );
        machine
            .proof_store
            .fail_qorf_replay_reservation_after(QorfReplayReservationFailurePoint::AfterRootWinner);
        let failure = machine
            .proof_store
            .try_prepare_qualified_parent_admission(result, &[parent])
            .expect_err("injected non-replay root reservation failure");
        assert!(matches!(failure, ProofFailure::ResourceExhausted { .. }));
        assert_eq!(
            (
                machine.proof_store.qualified_parent_keys.clone(),
                machine.proof_store.qualified_parents_by_result.clone(),
                machine
                    .proof_store
                    .first_qualified_parent_source_by_root
                    .clone(),
                machine
                    .proof_store
                    .canonical_qualified_parent_by_root
                    .clone(),
                machine.proof_store.non_replay_qualified_parents.clone(),
                machine.proof_store.replay_admissions.clone(),
            ),
            before,
        );
    }

    /// Reproducible QORF-C cutover gate from design §8. This is intentionally excluded from the
    /// fast suite: it lowers the complete repository std graph and then streams every legacy
    /// qualified replay key/value and every occurrence side through the authoritative side AVL.
    ///
    /// Run with:
    /// `YULANG_QORF_C_FULL_STD_PARITY=1 cargo test -p infer --release \
    ///   constraints::proof::tests::qorf_c_full_std_exhaustive_side_authority_parity \
    ///   -- --ignored --exact --nocapture`
    #[test]
    #[ignore = "full repository-std QORF-C exhaustive parity gate"]
    fn qorf_c_full_std_exhaustive_side_authority_parity() {
        assert_eq!(
            std::env::var("YULANG_QORF_C_FULL_STD_PARITY").as_deref(),
            Ok("1"),
            "set YULANG_QORF_C_FULL_STD_PARITY=1 to acknowledge the heavy full-std gate",
        );
        struct ActiveGuard;
        impl Drop for ActiveGuard {
            fn drop(&mut self) {
                QORF_C_FULL_STD_PARITY_ACTIVE.with(|active| active.set(false));
            }
        }
        QORF_C_FULL_STD_PARITY_ACTIVE.with(|active| {
            assert!(!active.replace(true), "QORF-C full-std gate cannot nest");
        });
        let _active = ActiveGuard;

        let loaded = qorf_c_repository_std_loaded("use std::prelude::*\nmod std;\n");
        let output = crate::lowering::lower_loaded_files(&loaded)
            .expect("lower complete repository std for QORF-C parity");
        let report = output
            .session
            .infer
            .constraints()
            .proof_store
            .qorf_c_full_std_parity_report();
        assert!(report.occurrences > 0);
        assert!(report.side_entries > 0);
        assert_eq!(
            report.d0_projection_census.arm_entries.0,
            report.occurrences
        );
        assert_eq!(
            report.d0_projection_census.root_entries.0,
            report.root_winners,
        );
        assert!(
            report.d0_projection_census.arm_entries.0 < report.side_entries
                && report.d0_projection_census.root_entries.0 < report.side_entries,
            "QORF-D0 compact projections must not reproduce exact-parent cardinality",
        );
        eprintln!(
            "QORF_C_FULL_STD_PARITY occurrences={} nonempty_sides={} side_entries={} qualified_replay_entries={} qualified_replay_keys={} replay_arms={} root_winners={} d0_census={:?} mismatches=0",
            report.occurrences,
            report.nonempty_sides,
            report.side_entries,
            report.qualified_replay_entries,
            report.qualified_replay_keys,
            report.replay_arms,
            report.root_winners,
            report.d0_projection_census,
        );
    }

    fn qorf_c_repository_std_loaded(root_source: &str) -> Vec<sources::LoadedFile> {
        let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .expect("canonical repository root");
        let lib = repository.join("lib");
        let mut paths = vec![lib.join("std.yu")];
        qorf_c_collect_yu_files(&lib.join("std"), &mut paths);
        paths.sort();

        let mut files = vec![qorf_c_source_file(&[], root_source)];
        files.extend(paths.into_iter().map(|path| {
            let relative = path.strip_prefix(&lib).expect("std path below lib");
            let mut module = relative.to_path_buf();
            module.set_extension("");
            let segments = module
                .components()
                .map(|component| {
                    let std::path::Component::Normal(segment) = component else {
                        panic!("normal std module path component")
                    };
                    segment.to_str().expect("utf-8 std path")
                })
                .collect::<Vec<_>>();
            qorf_c_source_file(
                &segments,
                &std::fs::read_to_string(path).expect("read std source"),
            )
        }));
        sources::load(files)
    }

    fn qorf_c_collect_yu_files(directory: &std::path::Path, files: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(directory).expect("read repository std directory") {
            let path = entry.expect("read repository std entry").path();
            if path.is_dir() {
                qorf_c_collect_yu_files(&path, files);
            } else if path.extension().and_then(|extension| extension.to_str()) == Some("yu") {
                files.push(path);
            }
        }
    }

    fn qorf_c_source_file(path: &[&str], source: &str) -> sources::SourceFile {
        sources::SourceFile {
            module_path: sources::Path {
                segments: path
                    .iter()
                    .map(|segment| sources::Name((*segment).to_string()))
                    .collect(),
            },
            source: source.to_string(),
        }
    }

    #[test]
    fn qorf_b_real_writer_descending_singletons_keep_side_payload_work_chunk_bounded() {
        let mut machine = cpk_machine();
        let (lower, _) = cpk_7_record_original_claim(&mut machine, 110_000);
        let (upper, _) = cpk_7_record_original_claim(&mut machine, 110_001);
        let result = ConstraintRecordId(110_002);
        let carrier = BinaryReplayDerivation {
            pivot: TypeVar(110_003),
            lower,
            upper,
            rule: ReplayRule::LowerBoundAdded,
        };
        let mut claims = Vec::new();
        claims.reserve(1_800);
        for ordinal in 0..1_800 {
            claims.push(cpk_7_record_original_claim(&mut machine, 111_000 + ordinal).1);
        }
        machine
            .proof_store
            .reset_qorf_replay_side_operation_census();
        for claim in claims.into_iter().rev() {
            let parent = ClaimQualifiedParent::ReplayConstraint {
                parent_claim: claim,
                parent_side: ReplayClaimParentSide::Lower,
                replay: carrier,
            };
            let mut transaction = machine
                .proof_store
                .try_prepare_replay_qualified_parent_transaction(result, carrier, &[parent])
                .expect("QORF real-writer singleton must prepare");
            machine
                .proof_store
                .commit_replay_qualified_parent_transaction(&mut transaction);
            machine.proof_store.record_replay_admission(
                Some(result),
                carrier,
                ReplayAdmissionDisposition::ExactDuplicate,
            );
        }
        let census = machine.proof_store.qorf_replay_side_operation_census();
        assert_eq!(census.accepted_parents, 1_800);
        assert!(census.max_scanned_existing <= QORF_REPLAY_PARENT_CHUNK_CAPACITY);
        assert!(census.scanned_existing < 1_800 * 1_799 / 2);
        assert_eq!(census.snapshot_duplicate_comparisons, 0);
        let (_, nonempty_sides, _, _, entries) =
            machine.proof_store.qorf_replay_side_allocation_census();
        assert_eq!(nonempty_sides, 1);
        assert_eq!(entries, 1_800);
        assert_eq!(
            machine.proof_store.replay_qualified_arms.flatten(result),
            vec![ReplayFiniteMapEntryId(0)],
        );
        assert_eq!(
            machine.proof_store.replay_qualified_arms.chunks.len(),
            1,
            "1,800 minimum-arm rekeys must recycle one physical arena slot",
        );
        machine
            .proof_store
            .debug_assert_qorf_b_side_shadow_matches_legacy(0);
    }

    #[test]
    fn qorf_a_zero_accepted_duplicate_keeps_event_and_preappend_first_event_index() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        let first_event = fixture.machine.proof_store.replay_admissions.len();
        fixture.machine.apply_cpk_replay_parent_arrival_for_test(
            fixture.result,
            fixture.carrier,
            fixture.coverage_root,
        );
        assert_eq!(
            fixture.machine.proof_store.replay_admissions.len(),
            first_event + 1
        );
        assert_eq!(fixture.machine.proof_store.replay_finite_map.len(), 1);
        assert_eq!(
            fixture.machine.proof_store.replay_finite_map[0].first_event,
            first_event
        );
        fixture
            .machine
            .proof_store
            .debug_assert_qorf_a_replay_relation_matches();

        let parent_faces_before = (
            fixture.machine.proof_store.qualified_parent_keys.clone(),
            fixture
                .machine
                .proof_store
                .qualified_parents_by_result
                .clone(),
            fixture.machine.proof_store.replay_finite_map.clone(),
            fixture.machine.proof_store.occurrences.clone(),
        );
        fixture.machine.apply_cpk_replay_parent_arrival_for_test(
            fixture.result,
            fixture.carrier,
            fixture.coverage_root,
        );
        assert_eq!(
            fixture.machine.proof_store.replay_admissions.len(),
            first_event + 2
        );
        assert_eq!(
            (
                fixture.machine.proof_store.qualified_parent_keys.clone(),
                fixture
                    .machine
                    .proof_store
                    .qualified_parents_by_result
                    .clone(),
                fixture.machine.proof_store.replay_finite_map.clone(),
                fixture.machine.proof_store.occurrences.clone(),
            ),
            parent_faces_before,
            "zero-accepted exact duplicate appends only its required replay event",
        );
    }

    #[test]
    fn qorf_a_duplicate_metadata_is_silent_first_wins_on_both_current_faces() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
        fixture
            .machine
            .apply_cpk_replay_parent_arrival_without_materialization_for_test(
                fixture.result,
                fixture.carrier,
                fixture.coverage_root,
            );
        let later_claim =
            add_same_root_replay_claim(&mut fixture, TypeVar(98_300), ConstraintRecordId(98_301));
        assert_ne!(later_claim, fixture.coverage_root);
        fixture
            .machine
            .apply_cpk_replay_parent_arrival_without_materialization_for_test(
                fixture.result,
                fixture.carrier,
                later_claim,
            );
        let snapshot = fixture
            .machine
            .proof_store
            .qorf_a_replay_relation_snapshot();
        snapshot.assert_exact_parity();
        assert_eq!(snapshot.qualified.len(), 1);
        assert_eq!(
            snapshot
                .qualified
                .values()
                .next()
                .unwrap()
                .representative_claim,
            fixture.coverage_root,
            "later conflicting metadata is silently dropped instead of becoming a new error",
        );
    }

    #[test]
    fn qorf_a_descending_singleton_events_have_chunk_bounded_payload_work() {
        let mut tree = QorfModelChunkAvl::<u32, QORF_REPLAY_PARENT_CHUNK_CAPACITY>::new();
        for key in (0..1_800).rev() {
            assert!(tree.insert(key));
        }
        tree.assert_invariants();
        assert_eq!(tree.flatten(), (0..1_800).collect::<Vec<_>>());
        assert!(tree.max_scanned_existing_per_insert <= QORF_REPLAY_PARENT_CHUNK_CAPACITY);
        assert!(
            tree.total_scanned_existing < 1_800 * 1_799 / 2,
            "fixed chunks must not reproduce the flat-Vec N(N-1)/2 scan",
        );
    }

    #[test]
    fn qorf_a_chunk_avl_insert_remove_rekey_matches_finite_btree_model() {
        fn permutations(values: &mut [u8], start: usize, output: &mut Vec<Vec<u8>>) {
            if start == values.len() {
                output.push(values.to_vec());
                return;
            }
            for index in start..values.len() {
                values.swap(start, index);
                permutations(values, start + 1, output);
                values.swap(start, index);
            }
        }

        let mut orders = Vec::new();
        permutations(&mut [0, 1, 2, 3, 4, 5], 0, &mut orders);
        for order in orders {
            let mut tree = QorfModelChunkAvl::<u8, 4>::new();
            let mut model = std::collections::BTreeSet::new();
            for &key in &order {
                assert_eq!(tree.insert(key), model.insert(key));
                tree.assert_invariants();
                assert_eq!(tree.flatten(), model.iter().copied().collect::<Vec<_>>());
            }
            assert!(!tree.insert(order[0]), "exact insert is silent first-wins");
            let old = order[1];
            assert!(tree.rekey(old, 9));
            model.remove(&old);
            model.insert(9);
            tree.assert_invariants();
            assert_eq!(tree.flatten(), model.iter().copied().collect::<Vec<_>>());
            for &key in order.iter().rev().filter(|key| **key != old) {
                assert_eq!(tree.remove(key), model.remove(&key));
                tree.assert_invariants();
                assert_eq!(tree.flatten(), model.iter().copied().collect::<Vec<_>>());
            }
            assert!(tree.remove(9));
            assert!(tree.flatten().is_empty());
        }
    }

    #[test]
    fn qorf_a_root_winner_uses_canonical_minimum_not_historical_first_source() {
        let result = ConstraintRecordId(98_200);
        let root = UpperReplayClaimId(98_201);
        let replay = ExactQualifiedParent {
            coverage_root: root,
            parent: ClaimQualifiedParent::ReplayConstraint {
                parent_claim: UpperReplayClaimId(98_203),
                parent_side: ReplayClaimParentSide::Upper,
                replay: BinaryReplayDerivation {
                    pivot: TypeVar(98_204),
                    lower: BoundRecordId(98_205),
                    upper: BoundRecordId(98_206),
                    rule: ReplayRule::UpperBoundAdded,
                },
            },
        };
        let structural = ExactQualifiedParent {
            coverage_root: root,
            parent: ClaimQualifiedParent::StructuralConstraint {
                parent_claim: UpperReplayClaimId(98_202),
                derivation: StructuralDerivation {
                    parent: result,
                    rule: StructuralDerivationRule::FunctionReturn,
                },
            },
        };
        assert!(qualified_parent_entry_cmp(&structural, &replay).is_lt());
        let historical_first = replay;
        let canonical_winner = [historical_first, structural]
            .into_iter()
            .min_by(qualified_parent_entry_cmp)
            .expect("root winner fixture is nonempty");
        assert_eq!(canonical_winner, structural);
        assert_eq!(
            historical_first, replay,
            "historical first-wins remains independent"
        );
    }

    #[test]
    fn qorf_a_arm_stable_first_and_exact_clause_associations_match_legacy_order() {
        let mut machine = cpk_machine();
        let (lower, first_root) = cpk_7_record_original_claim(&mut machine, 98_400);
        let (upper, second_root) = cpk_7_record_original_claim(&mut machine, 98_401);
        let result = ConstraintRecordId(98_402);
        let carriers = [ReplayRule::UpperBoundAdded, ReplayRule::LowerBoundAdded].map(|rule| {
            BinaryReplayDerivation {
                pivot: TypeVar(98_403),
                lower,
                upper,
                rule,
            }
        });
        for (carrier, roots) in [
            (carriers[0], [second_root, first_root]),
            (carriers[1], [first_root, second_root]),
        ] {
            for (index, root) in roots.into_iter().enumerate() {
                let side = if index == 0 {
                    ReplayClaimParentSide::Upper
                } else {
                    ReplayClaimParentSide::Lower
                };
                machine.admit_claim_qualified_parents(
                    result,
                    &[ClaimQualifiedParent::ReplayConstraint {
                        parent_claim: root,
                        parent_side: side,
                        replay: carrier,
                    }],
                );
                machine.proof_store.record_cpk_replay_parent_snapshot(
                    result,
                    carrier,
                    &[SideTaggedReplayClaim {
                        claim: root,
                        parent_side: side,
                    }],
                );
            }
        }
        machine
            .proof_store
            .debug_assert_qorf_a_replay_relation_matches();

        let mut seen = FxHashSet::default();
        let legacy_stable_first = machine
            .proof_store
            .qualified_parents_for_result(result)
            .iter()
            .filter_map(|entry| match entry.parent {
                ClaimQualifiedParent::ReplayConstraint { replay, .. }
                    if seen.insert(replay) => Some(replay),
                _ => None,
            })
            .collect::<Vec<_>>();
        let mut occurrence_minima = machine.proof_store.replay_finite_map
            .iter()
            .map(|occurrence| {
                [
                    occurrence.lower_parents.as_slice(),
                    occurrence.upper_parents.as_slice(),
                ]
                .into_iter()
                .flatten()
                .map(|parent| ExactQualifiedParent {
                    coverage_root: parent.coverage_root,
                    parent: ClaimQualifiedParent::ReplayConstraint {
                        parent_claim: parent.representative_claim,
                        parent_side: parent.side,
                        replay: occurrence.carrier,
                    },
                })
                .min_by(qualified_parent_entry_cmp)
                .expect("QORF occurrences are nonempty")
            })
            .collect::<Vec<_>>();
        occurrence_minima.sort_unstable_by(qualified_parent_entry_cmp);
        assert_eq!(
            occurrence_minima
                .iter()
                .map(|entry| qualified_parent_projection_carrier(entry.parent))
                .collect::<Vec<_>>(),
            legacy_stable_first
                .iter()
                .map(|replay| ProjectionProofCarrier::ReplayConstraint {
                    result: ConstraintRecordId(0),
                    derivation: *replay,
                })
                .collect::<Vec<_>>(),
        );

        let exact = machine.proof_store.qorf_a_replay_relation_snapshot();
        let shared_root_carriers = exact
            .finite_map
            .keys()
            .filter(|key| key.coverage_root == first_root)
            .map(|key| key.carrier)
            .collect::<FxHashSet<_>>();
        assert_eq!(
            shared_root_carriers.len(),
            2,
            "clause-association cursor must retain every exact carrier for one root",
        );
    }

    #[test]
    fn qorf_a_parent_validation_preserves_lineage_before_later_order_error() {
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
        let mut malformed_second = make_parent(second_claim);
        malformed_second.lineage = ProjectionLineage::ReplayEvidence;
        let combined_fault = PreparedReplayRoute {
            routing: ReplayRouting::Generic,
            proof_event: PreparedReplayParents {
                pair_replay: Some(PreparedReplayParentSet {
                    lower: PreparedReplayParentBlock::Empty,
                    // second > first is noncanonical, but current validation resolves and checks
                    // each payload before comparing it with its successor.
                    upper: PreparedReplayParentBlock::Shared(Arc::from(vec![
                        malformed_second,
                        first,
                    ])),
                }),
                incremental_replays: Vec::new(),
            },
        };
        assert!(matches!(
            fixture.machine.proof_store.validate_prepared_replay_route(
                fixture.lower,
                fixture.upper,
                &combined_fault,
            ),
            Err(ProofFailure::IncompleteMandatoryData {
                field: MandatoryProofField::ReplayParentLineage,
                ..
            })
        ));
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
            cpk_3_replay_fixture()
        });
        let active = with_semantic_execution_snapshot_capture_for_new_machines(|| {
            cpk_3_replay_fixture()
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
                    replay_parent_sides: [
                        ReplayParentSideIndex {
                            root: Some(ReplayParentChunkId(0)),
                            len: 1
                        },
                        ReplayParentSideIndex {
                            root: Some(ReplayParentChunkId(1)),
                            len: 1
                        },
                    ],
                },
                ReplayProofOccurrence {
                    result: ConstraintRecordId(2),
                    carrier: second_carrier,
                    lower_parents: vec![parent(ReplayClaimParentSide::Lower, 4, 4)],
                    upper_parents: vec![parent(ReplayClaimParentSide::Upper, 5, 5)],
                    first_event: 1,
                    replay_parent_sides: [
                        ReplayParentSideIndex {
                            root: Some(ReplayParentChunkId(2)),
                            len: 1
                        },
                        ReplayParentSideIndex {
                            root: Some(ReplayParentChunkId(3)),
                            len: 1
                        },
                    ],
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
        let claim = machine.proof_store.reduction_claim(state).expect("CPK reduction claim");
        let record_before_move =
            machine.proof_store.upper_claim(claim).expect("CPK claim").current_record;

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
        let upper_record = fixture.machine.proof_store.upper_claim(fixture.claim)
            .expect("CPK claim").current_record;
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
            fixture.machine.proof_store.upper_claim(fixture.claim).expect("CPK claim").current_record,
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
        let mut machine = cpk_3_replay_fixture();
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
            claim: Some(machine.proof_store.reduction_claim(state).expect("CPK reduction claim")),
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
                machine.proof_store.root_claim_for_producer(producer).expect("CPK root claim")
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
                machine.proof_store.root_claim_for_producer(producer).expect("CPK root claim")
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
            let mut machine = cpk_3_replay_fixture();
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
        let machine = cpk_3_replay_fixture();
        let snapshot = machine.proof_store.clone();
        snapshot.debug_assert_claimed_projection_audit_reconstructs();
        snapshot.debug_assert_pclf_a_read_model_matches_legacy();
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

        let included = |record, supports: Vec<(u32, u32)>| ProjectionDecision::Included {
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
            evidence: projection_evidence_for_test(&machine, record),
        };
        for (record, owner, decision) in [
            (
                BoundRecordId(0),
                TypeVar(31),
                included(BoundRecordId(0), vec![(0, 0)]),
            ),
            (BoundRecordId(2), TypeVar(34), ProjectionDecision::Excluded),
            (
                BoundRecordId(4),
                TypeVar(34),
                included(BoundRecordId(4), vec![(0, 2), (4, 6), (5, 7)]),
            ),
            (
                BoundRecordId(6),
                TypeVar(32),
                included(BoundRecordId(6), vec![(4, 4)]),
            ),
            (
                BoundRecordId(8),
                TypeVar(34),
                included(BoundRecordId(8), vec![(5, 5)]),
            ),
            (
                BoundRecordId(10),
                TypeVar(36),
                included(BoundRecordId(10), vec![(8, 8)]),
            ),
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
            ProjectionDecision::Included { supports, .. } => assert_eq!(
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
                evidence: projection_evidence_for_test(&machine, record),
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
        let indexes_before = machine
            .proof_store
            .performance_index_allocation_census();

        assert!(!machine.proof_store.projection_supports.contains_key(&record));
        assert!(!machine.proof_store.projection_formulas.contains_key(&record));
        assert!(
            !machine
                .proof_store
                .projection_formula_support_keys
                .contains_key(&record)
        );
        let (decision, round) = project_lower_for_test(&machine, record);
        assert_eq!(decision, Ok(ProjectionDecision::Unclaimed));
        assert!(
            round.preflight.is_none(),
            "an unclaimed record must not allocate query-local preflight state",
        );
        drop(round);
        assert_cpk_projection_decision_and_consumer(
            &machine,
            owner,
            record,
            ProjectionDecision::Unclaimed,
        );
        assert_eq!(
            machine
                .proof_store
                .performance_index_allocation_census(),
            indexes_before,
            "a no-claim query must not grow any CPK performance mirror",
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
        assert_eq!(
            machine
                .proof_store
                .performance_index_allocation_census(),
            PerformanceIndexAllocationCensus {
                dependency_result_buckets: (0, 0, 0, 0),
                projection_carrier_occurrences: (0, 0),
                row_derivation_occurrences: (0, 0),
                replay_result_buckets: (0, 0, 0, 0),
                formula_support_buckets: (0, 0, 0, 0),
                claimed_projection_audit: (0, 0),
                legacy_projection_formula: ProjectionFormulaAllocationCensus::default(),
                shadow_projection_formula: ProjectionFormulaAllocationCensus::default(),
                shadow_incidence_metadata: (
                    0,
                    0,
                    std::mem::size_of::<ProjectionIncidenceMetadata>(),
                ),
                shadow_movement: ProjectionFormulaMovementCensus::default(),
            },
        );

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
        let indexes = machine
            .proof_store
            .performance_index_allocation_census();
        assert_eq!(indexes.dependency_result_buckets, (0, 0, 0, 0));
        assert_eq!(indexes.row_derivation_occurrences, (0, 0));
        assert_eq!(indexes.replay_result_buckets, (0, 0, 0, 0));
        assert_eq!(indexes.formula_support_buckets, (0, 0, 0, 0));
        assert_eq!(indexes.claimed_projection_audit, (0, 0));
        assert_eq!(indexes.projection_carrier_occurrences.0, 1);
        assert!(
            indexes.projection_carrier_occurrences.1 > 0,
            "the ordinary bound's Origin occurrence is intentionally indexed as a projection carrier",
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
                    ClaimedProjectionProofSource::Original {
                        coverage_root: UpperReplayClaimId(0),
                        producer: ConstraintRecordId(40_000),
                    },
                ),
                RecordProofClauseLinkAdmission::claimed(
                    UpperReplayClaimId(1),
                    RecordProofClause::ReplayConjunction {
                        carrier: replay,
                        lower_premise: replay.lower,
                        upper_premise: replay.upper,
                    },
                    ClaimedAttributionSource::CanonicalReplay,
                    ClaimedProjectionProofSource::ReplayConstraint {
                        coverage_root: UpperReplayClaimId(1),
                        result: ConstraintRecordId(40_001),
                    },
                ),
                RecordProofClauseLinkAdmission::claimed(
                    UpperReplayClaimId(2),
                    RecordProofClause::ReplayConjunction {
                        carrier: replay,
                        lower_premise: replay.lower,
                        upper_premise: replay.upper,
                    },
                    ClaimedAttributionSource::FlatRetained,
                    ClaimedProjectionProofSource::ReplayEvidence {
                        coverage_root: UpperReplayClaimId(2),
                    },
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
                    ClaimedProjectionProofSource::DerivedUnary {
                        coverage_root: UpperReplayClaimId(3),
                        result: ConstraintRecordId(40_003),
                    },
                ),
                RecordProofClauseLinkAdmission::claimed(
                    UpperReplayClaimId(4),
                    RecordProofClause::DerivedUnary {
                        carrier: DerivedUnaryCarrier::ReductionRoute(RowDerivationId(40_004)),
                        premise: ProofPremise::RootCoverage(UpperReplayClaimId(4)),
                    },
                    ClaimedAttributionSource::FlatRetained,
                    ClaimedProjectionProofSource::DerivedUnary {
                        coverage_root: UpperReplayClaimId(4),
                        result: ConstraintRecordId(40_004),
                    },
                ),
            ];
            for (index, admission) in entries.into_iter().enumerate() {
                machine
                    .proof_store
                    .record_projection_clause(BoundRecordId(index as u32), admission);
            }
        let snapshot = machine.proof_store.clone();
        snapshot.debug_assert_claimed_projection_audit_reconstructs();
        snapshot.debug_assert_pclf_a_read_model_matches_legacy();
        assert_eq!(snapshot.projection_claimed_link_audit.len(), 5);
        assert_eq!(
            snapshot
                .claimed_projection_proofs_from_audit_for_test()
                .values()
                .map(FxHashMap::len)
                .sum::<usize>(),
            5,
        );

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

        collect(&cpk_3_replay_fixture());

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
            machine.proof_store.root_claim_for_producer(producer).expect("CPK root claim")
        });
        roots.sort();
        let upper_records = roots.map(|root| {
            let claim = machine.proof_store.upper_claim(root).expect("CPK root claim");
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
        let root = machine.proof_store.root_claim_for_producer(producer).expect("CPK root claim");

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

        let parents_before = machine
            .proof_store
            .qualified_parents_for_result(result)
            .to_vec();
        machine.register_reduction_route_claim_parent(result, derivation, root);

        assert_eq!(
            occurrence_count(&machine),
            1,
            "CPK exact dedup must not depend on the corrupted Legacy mirror",
        );
        assert_eq!(
            machine.proof_store.qualified_parents_for_result(result),
            parents_before,
            "a CPK duplicate must not change the result-local exact-parent view",
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
        let root = machine.proof_store.root_claim_for_producer(producer).expect("CPK root claim");
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
                evidence: projection_evidence_for_test(&machine, lower_record),
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
        let lower_record = machine
            .proof_store
            .projection_lower_record_for_constraint(result)
            .expect("CPK projection target");

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
        let root = machine.proof_store.root_claim_for_producer(producer).expect("CPK root claim");

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
        let lower_record = machine
            .proof_store
            .projection_lower_record_for_constraint(result)
            .expect("CPK projection target");

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
    fn cpk_7_cpk_authority_preflight_rejects_claim_index_corruption() {
        let mut fixture = cpk_3_cpk_only_replay_admission_fixture();
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

        let ((), telemetry) = capture_proof_soak_test_events(|| {
            cpk_5_trigger_lower_route(&mut fixture, false);
            cpk_5_trigger_lower_route(&mut fixture, true);
        });

        assert!(matches!(
            fixture.machine.proof_terminal_failure(),
            Some(ProofFailure::DanglingProofReference { .. }),
        ));
        assert_eq!(
            telemetry.proof_terminal_failures(
                ProofSoakEventOrigin::Organic,
                ProofOperation::PrepareReplayRouteBatch,
            ),
            1,
            "the sticky terminal failure must be counted only once",
        );
        assert_eq!(
            telemetry.proof_terminal_failures(
                ProofSoakEventOrigin::IntentionalTestInjection,
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

        with_intentional_proof_soak_test_injection(|| fixture.machine.drain());

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
        let ((), telemetry) = capture_proof_soak_test_events(|| {
            cpk_5_trigger_lower_route(&mut fixture, false);
        });

        assert_eq!(
            telemetry.total_for_origin(ProofSoakEventOrigin::Organic),
            0,
            "a normal successful CPK route must not resemble an organic soak failure",
        );
        assert_eq!(
            telemetry.total_for_origin(ProofSoakEventOrigin::IntentionalTestInjection),
            0,
        );
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
            let indexes_before_structural_duplicate = machine
                .proof_store
                .performance_index_allocation_census();
            assert!(!machine.enqueue_derived_subtype(
                structural_lower,
                ConstraintWeights::empty(),
                structural_upper,
                parent,
                StructuralDerivationRule::FunctionReturn,
            ));
            assert_eq!(
                machine
                    .proof_store
                    .performance_index_allocation_census(),
                indexes_before_structural_duplicate,
                "an exact structural duplicate must not grow dependency or carrier indexes",
            );

            let row = machine.intern_row_derivation(
                RowDerivationRule::RowItemMatch,
                vec![RowDerivationParent::Constraint(parent)],
                Vec::new(),
            );
            let indexes_before_row_duplicate = machine
                .proof_store
                .performance_index_allocation_census();
            assert_eq!(
                machine.intern_row_derivation(
                    RowDerivationRule::RowItemMatch,
                    vec![RowDerivationParent::Constraint(parent)],
                    Vec::new(),
                ),
                row,
            );
            assert_eq!(
                machine
                    .proof_store
                    .performance_index_allocation_census(),
                indexes_before_row_duplicate,
                "an exact row-derivation duplicate must not grow the row membership index",
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
            let indexes_before_duplicate = machine
                .proof_store
                .performance_index_allocation_census();
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
            assert_eq!(
                machine
                    .proof_store
                    .performance_index_allocation_census(),
                indexes_before_duplicate,
                "an exact occurrence duplicate must not grow any occurrence membership index",
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
    fn cpk_1_semantic_view_matches_embedded_records() {
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
