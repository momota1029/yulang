//! Constraint Proof Kernel boundary.
//!
//! CPK-1 defines read-only adapters over current semantic records and their legacy proof payloads.
//! CPK-2 adds a test-only occurrence shadow below that seam. It does not own production state,
//! receive replay occurrences, or influence worklist identity and ordering.

use super::*;

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

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofOccurrence {
    pub(crate) result: ProofResult,
    pub(crate) cause: ProofCause,
    pub(crate) parents: Vec<ProofParent>,
    pub(crate) event: usize,
    pub(crate) completeness: ProvenanceCompleteness,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ProofResult {
    Semantic(SemanticFactRef),
    TrivialReplay(ReplayDropRecordId),
    EvidenceBound(BoundRecordId),
    /// Some rejected/equivalent admissions have no newly persisted semantic bound.
    BoundDisposition(BoundDispositionRecordId),
}

#[cfg(test)]
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

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ProjectionLineage {
    Original,
    ReplayConstraint,
    ReplayEvidence,
    StructuralConstraint,
    ReductionRouteConstraint,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ReplayProofParent {
    pub(crate) side: ReplayClaimParentSide,
    pub(crate) coverage_root: UpperReplayClaimId,
    pub(crate) representative_claim: UpperReplayClaimId,
    pub(crate) lineage: ProjectionLineage,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReplayProofOccurrence {
    pub(crate) result: ConstraintRecordId,
    pub(crate) carrier: BinaryReplayDerivation,
    pub(crate) lower_parents: Vec<ReplayProofParent>,
    pub(crate) upper_parents: Vec<ReplayProofParent>,
    pub(crate) first_event: usize,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplayAdmissionDisposition {
    NewSemantic,
    CanonicalDuplicate,
    ExactDuplicate,
    Trivial,
    EvidenceOnly,
    Incomplete,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ReplayAdmissionEvent {
    pub(crate) result: Option<ConstraintRecordId>,
    pub(crate) carrier: BinaryReplayDerivation,
    pub(crate) disposition: ReplayAdmissionDisposition,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ReplayFirstWitness {
    pub(crate) carrier: BinaryReplayDerivation,
    pub(crate) side: ReplayClaimParentSide,
    pub(crate) representative_claim: UpperReplayClaimId,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UpperClaimOccurrence {
    pub(crate) claim: UpperReplayClaimId,
    pub(crate) coverage_root: UpperReplayClaimId,
    pub(crate) lineage: ProjectionLineage,
    pub(crate) producer: ConstraintRecordId,
    pub(crate) current_record: BoundRecordId,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ShadowProjectionClause {
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

#[cfg(test)]
impl ShadowProjectionClause {
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
pub(crate) struct RowReductionOccurrence {
    pub(crate) state: UnweightedRowReductionRecordId,
    pub(crate) root_claim: Option<UpperReplayClaimId>,
    pub(crate) provenance: RowDerivationId,
    pub(crate) current_record: BoundRecordId,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ProofParent {
    Semantic(SemanticFactRef),
    Origin(OriginId),
    LowerFilter(LowerFilterRecordId),
    GeneralizedWitness(GeneralizedSchemeWitnessId),
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofOccurrenceStoreSnapshot {
    pub(crate) occurrences: Vec<ProofOccurrence>,
    pub(crate) replay_finite_map: Vec<ReplayProofOccurrence>,
    pub(crate) replay_admissions: Vec<ReplayAdmissionEvent>,
    pub(crate) first_replay_witnesses:
        FxHashMap<(ConstraintRecordId, UpperReplayClaimId), ReplayFirstWitness>,
    pub(crate) upper_claims: Vec<UpperClaimOccurrence>,
    pub(crate) row_reductions: Vec<RowReductionOccurrence>,
    pub(crate) live_coverage: FxHashSet<(UpperReplayClaimId, UnweightedRowReductionRecordId)>,
    pub(crate) replay_coverage_connected: bool,
    projection_supports: FxHashMap<BoundRecordId, Vec<SchemeProjectionProofSupport>>,
    projection_formulas: FxHashMap<BoundRecordId, Vec<ShadowProjectionClause>>,
    projectability_observations: Vec<ShadowProjectabilityObservation>,
}

#[cfg(test)]
impl Default for ProofOccurrenceStoreSnapshot {
    fn default() -> Self {
        Self {
            occurrences: Vec::new(),
            replay_finite_map: Vec::new(),
            replay_admissions: Vec::new(),
            first_replay_witnesses: FxHashMap::default(),
            upper_claims: Vec::new(),
            row_reductions: Vec::new(),
            live_coverage: FxHashSet::default(),
            replay_coverage_connected: true,
            projection_supports: FxHashMap::default(),
            projection_formulas: FxHashMap::default(),
            projectability_observations: Vec::new(),
        }
    }
}

#[cfg(test)]
thread_local! {
    static SHADOW_CAPTURE_DEPTH: Cell<usize> = const { Cell::new(0) };
    static SHADOW_STORE: RefCell<ProofOccurrenceStoreSnapshot> = RefCell::default();
}

#[cfg(test)]
pub(crate) fn capture_proof_occurrence_shadow<R>(
    f: impl FnOnce() -> R,
) -> (R, ProofOccurrenceStoreSnapshot) {
    struct Reset(usize);
    impl Drop for Reset {
        fn drop(&mut self) {
            SHADOW_CAPTURE_DEPTH.set(self.0);
        }
    }

    let previous = SHADOW_CAPTURE_DEPTH.get();
    assert_eq!(previous, 0, "CPK proof shadow capture is not nestable");
    SHADOW_STORE.with(|store| *store.borrow_mut() = ProofOccurrenceStoreSnapshot::default());
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
        let mut store = store.borrow_mut();
        let event = store.occurrences.len();
        store.occurrences.push(ProofOccurrence {
            result,
            cause,
            parents,
            event,
            completeness,
        });
    });
}

#[cfg(test)]
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
    SHADOW_STORE.with(|store| {
        store.borrow_mut().upper_claims.push(UpperClaimOccurrence {
            claim: claim.id,
            coverage_root: claim.coverage_root,
            lineage: projection_lineage(claim.lineage),
            producer: claim.producer_constraint,
            current_record: claim.current_record,
        });
    });
}

#[cfg(test)]
pub(super) fn update_upper_claim_shadow(claim: &UpperReplayClaim) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| {
        let mut store = store.borrow_mut();
        let Some(existing) = store
            .upper_claims
            .iter_mut()
            .find(|existing| existing.claim == claim.id)
        else {
            return;
        };
        existing.current_record = claim.current_record;
    });
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
        store.borrow_mut().projection_supports.insert(
            lower_record,
            proofs.iter().map(|proof| proof.support).collect(),
        );
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
        RecordProofClause::Standalone { .. } => ShadowProjectionClause::Standalone {
            support: admission.support,
            attribution,
        },
        RecordProofClause::DerivedUnary { carrier, premise } => {
            ShadowProjectionClause::DerivedUnary {
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
        } => ShadowProjectionClause::ReplayConjunction {
            support: admission.support,
            carrier,
            lower: lower_premise,
            upper: upper_premise,
            attribution,
        },
    };
    SHADOW_STORE.with(|store| {
        let mut store = store.borrow_mut();
        let formula = store.projection_formulas.entry(lower_record).or_default();
        if !formula.contains(&clause) {
            formula.push(clause);
            formula.sort_by_key(|clause| clause.category_rank());
        }
    });
}

#[cfg(test)]
struct ShadowProjectionEvaluator<'a> {
    machine: &'a ConstraintMachine,
    store: &'a ProofOccurrenceStoreSnapshot,
    states: FxHashMap<ProofEvalNode, ProofEvalState>,
    record_overrides: FxHashMap<BoundRecordId, bool>,
    root_overrides: FxHashMap<UpperReplayClaimId, bool>,
    cycle_cuts: usize,
}

#[cfg(test)]
impl<'a> ShadowProjectionEvaluator<'a> {
    fn new(machine: &'a ConstraintMachine, store: &'a ProofOccurrenceStoreSnapshot) -> Self {
        Self {
            machine,
            store,
            states: FxHashMap::default(),
            record_overrides: FxHashMap::default(),
            root_overrides: FxHashMap::default(),
            cycle_cuts: 0,
        }
    }

    fn eval_record(&mut self, record: BoundRecordId) -> bool {
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
        let Some(bound) = self.machine.bounds.record(record) else {
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

    fn eval_clause(&mut self, clause: ShadowProjectionClause) -> bool {
        match clause {
            ShadowProjectionClause::Standalone { support, .. } => {
                self.support_is_qualifying(support)
            }
            ShadowProjectionClause::DerivedUnary { premise, .. } => self.eval_premise(premise),
            ShadowProjectionClause::ReplayConjunction { lower, upper, .. } => {
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
        if self
            .machine
            .constraint_records
            .get(constraint.0 as usize)
            .is_none()
        {
            return true;
        }
        let mut has_source = false;
        if let Some(lower_record) = self.machine.lower_record_for_constraint(constraint) {
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
}

#[cfg(test)]
pub(super) fn compare_projection_record_shadow(
    machine: &ConstraintMachine,
    record: BoundRecordId,
    legacy_result: bool,
    legacy_cycle_cuts: usize,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    let snapshot = SHADOW_STORE.with(|store| store.borrow().clone());
    if machine
        .bounds
        .projection_proofs_by_lower_record
        .contains_key(&record)
        && !snapshot.projection_supports.contains_key(&record)
    {
        // Capture began after this record's writer events; it is not a complete shadow view.
        return;
    }
    let mut evaluator = ShadowProjectionEvaluator::new(machine, &snapshot);
    let shadow_result = evaluator.eval_record(record);
    let observation = ShadowProjectabilityObservation {
        record,
        legacy: legacy_result,
        shadow: shadow_result,
        legacy_cycle_cut: legacy_cycle_cuts != 0,
        shadow_cycle_cut: evaluator.cycle_cuts != 0,
    };
    assert_eq!(shadow_result, legacy_result, "CPK-4 projectability diverged");
    assert_eq!(
        observation.shadow_cycle_cut, observation.legacy_cycle_cut,
        "CPK-4 cycle-cut behavior diverged"
    );
    SHADOW_STORE.with(|store| {
        store
            .borrow_mut()
            .projectability_observations
            .push(observation);
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
        store.borrow_mut().replay_admissions.push(ReplayAdmissionEvent {
            result,
            carrier,
            disposition,
        });
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
        let mut store = store.borrow_mut();
        let index = store
            .replay_finite_map
            .iter()
            .position(|entry| entry.result == result && entry.carrier == carrier)
            .unwrap_or_else(|| {
                let index = store.replay_finite_map.len();
                let first_event = store.replay_admissions.len();
                store.replay_finite_map.push(ReplayProofOccurrence {
                    result,
                    carrier,
                    lower_parents: Vec::new(),
                    upper_parents: Vec::new(),
                    first_event,
                });
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
                    &mut store.replay_finite_map[index].lower_parents
                }
                ReplayClaimParentSide::Upper => {
                    &mut store.replay_finite_map[index].upper_parents
                }
            };
            if !target.iter().any(|entry| entry.coverage_root == claim.coverage_root) {
                target.push(proof_parent);
            }
            store
                .first_replay_witnesses
                .entry((result, claim.coverage_root))
                .or_insert(ReplayFirstWitness {
                    carrier,
                    side: parent_side,
                    representative_claim: parent_claim,
                });
        }
    });
    record_shadow_occurrence(
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
pub(super) fn record_replay_evidence_shadow(
    result: BoundRecordId,
    carrier: BinaryReplayDerivation,
) {
    record_shadow_occurrence(
        ProofResult::EvidenceBound(result),
        ProofCause::ReplayEvidence(carrier),
        vec![
            ProofParent::Semantic(SemanticFactRef::Bound(carrier.lower)),
            ProofParent::Semantic(SemanticFactRef::Bound(carrier.upper)),
        ],
        ProvenanceCompleteness::Complete,
    );
}

#[cfg(test)]
pub(super) fn record_replay_drop_shadow(id: ReplayDropRecordId, record: ReplayDropRecord) {
    record_shadow_occurrence(
        ProofResult::TrivialReplay(id),
        ProofCause::ReplayDrop(record),
        Vec::new(),
        ProvenanceCompleteness::Complete,
    );
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
        store.borrow_mut().row_reductions.push(RowReductionOccurrence {
            state,
            root_claim,
            provenance: record.provenance_head,
            current_record: record.current_reduced_upper.record,
        });
    });
    record_shadow_occurrence(
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

#[cfg(test)]
pub(super) fn record_live_coverage_shadow(
    root: UpperReplayClaimId,
    state: UnweightedRowReductionRecordId,
    active: bool,
) {
    if !proof_occurrence_shadow_is_active() {
        return;
    }
    SHADOW_STORE.with(|store| {
        let mut store = store.borrow_mut();
        if active {
            store.live_coverage.insert((root, state));
        } else {
            store.live_coverage.remove(&(root, state));
        }
    });
}

#[cfg(test)]
pub(super) fn record_reduction_route_shadow(
    result: ConstraintRecordId,
    derivation: RowDerivationId,
    parent_claim: UpperReplayClaimId,
) {
    record_shadow_occurrence(
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

#[cfg(test)]
pub(crate) fn record_constraint_root_shadow(result: ConstraintRecordId, origin: OriginId) {
    record_shadow_occurrence(
        ProofResult::Semantic(SemanticFactRef::Constraint(result)),
        ProofCause::Root(origin),
        vec![ProofParent::Origin(origin)],
        ProvenanceCompleteness::Complete,
    );
}

#[cfg(test)]
pub(crate) fn record_structural_shadow(
    result: ConstraintRecordId,
    derivation: StructuralDerivation,
) {
    record_shadow_occurrence(
        ProofResult::Semantic(SemanticFactRef::Constraint(result)),
        ProofCause::Structural(derivation),
        vec![ProofParent::Semantic(SemanticFactRef::Constraint(
            derivation.parent,
        ))],
        ProvenanceCompleteness::Complete,
    );
}

#[cfg(test)]
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
    let parents = derivation.parents.iter().copied().map(row_parent).collect();
    record_shadow_occurrence(
        ProofResult::Semantic(SemanticFactRef::RowDerivation(id)),
        ProofCause::RowDefinition(derivation),
        parents,
        ProvenanceCompleteness::Complete,
    );
}

#[cfg(test)]
pub(crate) fn record_row_constraint_shadow(
    result: ConstraintRecordId,
    derivation: RowDerivationId,
) {
    record_shadow_occurrence(
        ProofResult::Semantic(SemanticFactRef::Constraint(result)),
        ProofCause::RowConstraint(derivation),
        vec![ProofParent::Semantic(SemanticFactRef::RowDerivation(
            derivation,
        ))],
        ProvenanceCompleteness::Complete,
    );
}

#[cfg(test)]
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

#[cfg(test)]
pub(crate) fn record_bound_shadow(result: BoundRecordId, derivation: BoundDerivation) {
    if matches!(
        derivation,
        BoundDerivation::ReplayEvidence(_) | BoundDerivation::IncompleteReplay
    ) {
        // Replay occurrences, including evidence-only replay bounds, start in CPK-3.
        return;
    }
    let parents = bound_derivation_parents(&derivation);
    record_shadow_occurrence(
        ProofResult::Semantic(SemanticFactRef::Bound(result)),
        ProofCause::Bound(derivation),
        parents,
        ProvenanceCompleteness::Complete,
    );
}

#[cfg(test)]
pub(crate) fn record_bound_disposition_shadow(
    id: BoundDispositionRecordId,
    result: Option<BoundRecordId>,
    disposition: BoundDispositionRecord,
) {
    record_shadow_occurrence(
        result.map_or(ProofResult::BoundDisposition(id), |result| {
            ProofResult::Semantic(SemanticFactRef::Bound(result))
        }),
        ProofCause::BoundDisposition(disposition),
        Vec::new(),
        ProvenanceCompleteness::Complete,
    );
}

#[cfg(test)]
pub(crate) fn record_subtract_shadow(
    result: SubtractFactRecordId,
    derivation: SubtractFactDerivation,
) {
    let origin = match derivation {
        SubtractFactDerivation::Declaration(origin)
        | SubtractFactDerivation::Import(origin)
        | SubtractFactDerivation::Internal(origin) => origin,
    };
    record_shadow_occurrence(
        ProofResult::Semantic(SemanticFactRef::Subtract(result)),
        ProofCause::Subtract(derivation),
        vec![ProofParent::Origin(origin)],
        ProvenanceCompleteness::Complete,
    );
}

#[cfg(test)]
pub(crate) fn record_scheme_instantiation_record_shadow(
    result: SchemeInstantiationId,
    record: SchemeInstantiationRecord,
) {
    record_shadow_occurrence(
        ProofResult::Semantic(SemanticFactRef::SchemeInstantiation(result)),
        ProofCause::SchemeInstantiationRecord(record.clone()),
        Vec::new(),
        record.completeness,
    );
}

#[cfg(test)]
pub(crate) fn record_scheme_instantiation_derivation_shadow(
    result: ConstraintRecordId,
    derivation: SchemeInstantiationDerivation,
) {
    record_shadow_occurrence(
        ProofResult::Semantic(SemanticFactRef::Constraint(result)),
        ProofCause::SchemeInstantiationDerivation(derivation.clone()),
        vec![
            ProofParent::Semantic(SemanticFactRef::SchemeInstantiation(
                derivation.instantiation,
            )),
            ProofParent::GeneralizedWitness(derivation.source_witness),
        ],
        ProvenanceCompleteness::Complete,
    );
}

#[cfg(test)]
pub(crate) fn record_scheme_instantiation_route_shadow(
    result: ConstraintRecordId,
    route: SchemeInstantiationRoute,
) {
    record_shadow_occurrence(
        ProofResult::Semantic(SemanticFactRef::Constraint(result)),
        ProofCause::SchemeInstantiationRoute(route.clone()),
        vec![
            ProofParent::Semantic(SemanticFactRef::SchemeInstantiation(
                route.derivation.instantiation,
            )),
            ProofParent::GeneralizedWitness(route.derivation.source_witness),
        ],
        ProvenanceCompleteness::Complete,
    );
}

#[cfg(test)]
pub(crate) fn record_constraint_disposition_shadow(
    result: ConstraintRecordId,
    disposition: ConstraintCanonicalizationDisposition,
) {
    record_shadow_occurrence(
        ProofResult::Semantic(SemanticFactRef::Constraint(result)),
        ProofCause::ConstraintDisposition(disposition),
        Vec::new(),
        ProvenanceCompleteness::Complete,
    );
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
    snapshot: &ProofOccurrenceStoreSnapshot,
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
    snapshot: &ProofOccurrenceStoreSnapshot,
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

    struct CpkReplayAdmissionFixture {
        machine: ConstraintMachine,
        result: ConstraintRecordId,
        carrier: BinaryReplayDerivation,
        coverage_root: UpperReplayClaimId,
    }

    fn cpk_3_replay_admission_fixture() -> CpkReplayAdmissionFixture {
        let mut machine = ConstraintMachine::new();
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
        fixture
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
            })
            .claim
    }

    fn cpk_3_replay_fixture() -> ConstraintMachine {
        let mut machine = ConstraintMachine::new();
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
            let _ = machine.bounds.derived_upper_replay_claim(
                insertion.id,
                root_claim,
                producer,
                |_| lineage,
            );
        }
        machine
    }

    #[test]
    fn cpk_3_exact_replay_and_first_witness_match_factored_oracle() {
        let inactive =
            with_semantic_execution_snapshot_capture_for_new_machines(cpk_3_replay_fixture);
        let (active, snapshot) = with_semantic_execution_snapshot_capture_for_new_machines(|| {
            capture_proof_occurrence_shadow(cpk_3_replay_fixture)
        });

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
        let ((machine, expected_drop), snapshot) = capture_proof_occurrence_shadow(|| {
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
            (fixture.machine, expected_drop)
        });

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
        let ((machine, carrier), snapshot) = capture_proof_occurrence_shadow(|| {
            let mut fixture = cpk_3_replay_admission_fixture();
            let constraint = SubtypeConstraintKey {
                lower: fixture.machine.alloc_pos(Pos::Var(TypeVar(10))),
                upper: fixture.machine.alloc_neg(Neg::Var(TypeVar(11))),
                weights: ConstraintWeights::empty(),
            };
            fixture
                .machine
                .apply_cpk_evidence_only_replay_for_test(constraint, fixture.carrier);
            (fixture.machine, fixture.carrier)
        });

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
            let ((machine, result, root, claims), snapshot) =
                capture_proof_occurrence_shadow(|| {
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
                    (
                        fixture.machine,
                        fixture.result,
                        fixture.coverage_root,
                        claims,
                    )
                });

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
        let (machine, snapshot) = capture_proof_occurrence_shadow(cpk_3_replay_fixture);

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
                .any(|clause| matches!(clause, ShadowProjectionClause::ReplayConjunction { .. })),
            "the representative fixture must exercise replay-conjunction support",
        );
        assert!(
            !snapshot.projectability_observations.is_empty(),
            "legacy production evaluation must invoke the CPK-4 shadow oracle",
        );
        assert!(snapshot.projectability_observations.iter().all(|observation| {
            observation.legacy == observation.shadow
                && observation.legacy_cycle_cut == observation.shadow_cycle_cut
        }));
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

        let (machine, snapshot) = capture_proof_occurrence_shadow(|| {
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
            let before_duplicate = proof_occurrence_shadow_len();
            assert!(!machine.attach_root_origin_to_existing_subtype(
                lower,
                upper,
                alternate.origin,
            ));
            assert_eq!(
                proof_occurrence_shadow_len(),
                before_duplicate,
                "an exact metadata duplicate must not create an occurrence",
            );
            machine
        });

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
