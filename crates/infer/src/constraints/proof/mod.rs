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
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ProofOccurrenceStoreSnapshot {
    pub(crate) occurrences: Vec<ProofOccurrence>,
    /// Replay is intentionally deferred to CPK-3; consumers must not infer coverage from absence.
    pub(crate) replay_coverage_connected: bool,
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
    assert!(!snapshot.replay_coverage_connected, "replay belongs to CPK-3");
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
mod tests {
    use super::*;

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
        assert!(!snapshot.replay_coverage_connected);
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
