//! Exact structural context relation authority for the private candidate.
//! Derivations are a separate fiber: retaining another origin does not create
//! another semantic task or unfold a recursive identity derivation.
use crate::candidate_effect::BoundKey;
use crate::*;
use yu_hir::shadow::{SourceEffectId, SourceNodeKey};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct RelationId(pub u32);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct ReplayOperationId(usize);
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ReplayChildAck {
    pub operation: ReplayOperationId,
    pub index: usize,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ReplayChildWait {
    Idle,
    Running { ack: ReplayChildAck, drain_index: usize },
    Ready { ack: ReplayChildAck, drain_index: usize, completion: DrainCompletion },
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ReplayChildStep { More, Delivered, NoChild }
// Queue transfer and child completion are distinct replay frontiers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ReplayDriveOutcome { Complete, Queued }
// This stack owns the inner synchronous driver's continuation data. Lifecycle
// suspension and the source/extrusion frames are separate, still-disabled gates.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TypedDrainStage { Transport, Context, Dispatch, FunctionAdmission, FunctionEnqueue, Diagnostics, Acknowledgements, ReturnReady }
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct FunctionDispatch {
    pub children: [(FunctionField, TypedPairKey); 4],
    pub next: usize,
    pub pending: Option<TypedWorkItem>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct TypedDrainFrame {
    pub initial: LiveConstraintTask,
    pub occurrence: ConstraintOccurrenceId,
    pub cause: CauseId,
    pub previous_processing: Option<TypedPairKey>,
    pub previous_relation: Option<RelationId>,
    pub current: Option<TypedWorkItem>,
    pub stage: TypedDrainStage,
    pub context_consumed: Option<bool>,
    pub transitions: usize,
    pub replay_acks: Vec<ReplayChildAck>,
    pub completed_acks: usize,
    pub prepared_acks: usize,
    pub terminal_prepared: bool,
    pub function: Option<FunctionDispatch>,
    pub replay_destination: Option<ReplayChildAck>,
}
#[derive(Debug)]
struct TypedDrainUndo {
    index: usize,
    frame: TypedDrainFrame,
}
#[derive(Clone, Debug, Eq, PartialEq)]
struct ReplayOperation {
    task: LiveConstraintTask,
    // Generation and child completion are deliberately separate frontiers.
    #[allow(dead_code, reason = "retained frozen generation evidence for the private continuation")]
    inputs: (BoundKey, BoundKey),
    #[allow(dead_code, reason = "retained frozen generation evidence for the private continuation")]
    heads: (Option<usize>, Option<usize>),
    #[allow(dead_code, reason = "retained frozen generation evidence for the private continuation")]
    prior: (Option<usize>, Option<usize>),
    #[allow(dead_code, reason = "retained incoming-use replay ownership for the private continuation")]
    incoming_use: bool,
    children: Vec<RelationId>,
    queued: usize,
    consumed: usize,
    retired: bool,
    restoration: Option<ReplayOperationId>,
    waiting_child: ReplayChildWait,
}
#[derive(Clone, Copy, Debug)]
struct ReplayOperationUndo {
    id: ReplayOperationId,
    waiting_child: ReplayChildWait,
    queued: usize,
    consumed: usize,
    retired: bool,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct BoundRestoration {
    pub owner: ExtrusionEndpoint,
    pub polarity: Polarity,
    pub bound: ExtrusionEndpoint,
    pub emission: BoundEmissionId,
    pub opposite_count: usize,
    pub next_opposite: usize,
    pub replay: Option<ReplayOperationId>,
    pub occurrence: ConstraintOccurrenceId,
    pub cause: CauseId,
    retired: bool,
}
#[derive(Clone, Copy, Debug)]
struct BoundRestorationUndo {
    id: ReplayOperationId,
    next_opposite: usize,
    replay: Option<ReplayOperationId>,
    retired: bool,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct ContextId(u32);
const IDENTITY: ContextId = ContextId(0);
// A payload handle is independent of nominal members and boundary identities.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct LocalWeightId(u32);
#[derive(Debug)]
pub(super) struct LocalWeight {
    pub(super) left_word: [(); 0],
    pub(super) allowed: Vec<SourceEffectId>,
    pub(super) right_pops: [(); 0],
    pub(super) boundary: u32,
    pub(super) owner: SourceRootId,
    pub(super) position: SourceNodeKey,
    pub(super) attachment: Option<AttachmentSet>,
}
// The payload ID is the set identity; ordinals index its resolved allowed operands.
#[derive(Debug)]
pub(super) struct AttachmentSet {
    pub(super) composed_polarity: Polarity,
    pub(super) lexical_scope: candidate_effect::AnnotationScope,
    pub(super) member_ordinals: Vec<usize>,
    // Dormant source preparation only. The owning weight already retains the
    // exact resolved members; live zero-word/filter execution never reads this.
    pub(super) unit_push: Option<SourceUnitPush>,
}
#[derive(Debug)]
pub(super) struct SourceUnitPush;
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct AttachmentSource {
    pub composed_polarity: Polarity,
    pub lexical_scope: candidate_effect::AnnotationScope,
}
// These identities retain source construction only. They never enter a
// RelationKey, ContextExpr, executable View, or endpoint comparison.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct AttachmentBundleId(pub usize);
#[derive(Clone, Debug)]
#[cfg_attr(not(test), allow(dead_code, reason = "inert source provenance has no executable attachment consumer"))]
pub(super) struct EmptyAttachmentSet {
    pub owner: SourceRootId,
    pub position: SourceNodeKey,
    pub source: AttachmentSource,
}
#[derive(Clone, Debug)]
pub(super) struct AttachmentBundle {
    pub occurrence: ConstraintOccurrenceId,
    pub sets: Vec<EmptyAttachmentSet>,
}
// Inert construction evidence, deliberately distinct from EntryCertificateId.
// Only admit_lambda_fact retains these records; they authorize no context operation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct InferredEntryOriginId(usize);
#[derive(Clone, Debug, Eq, PartialEq)]
#[cfg_attr(not(test), allow(dead_code, reason = "inferred-entry evidence has no authorization consumer yet"))]
pub(super) struct InferredEntryOrigin {
    pub id: InferredEntryOriginId,
    pub lambda: HirOccurrenceId,
    pub entry: EffectEndpointKey,
    pub returned: EffectEndpointKey,
    pub occurrence: ConstraintOccurrenceId,
    pub cause: CauseId,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct EntryCertificateId(u32);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(
    not(test),
    allow(dead_code, reason = "context propagation is a later gate")
)]
pub(super) enum ContextExpr {
    PrefixLeft {
        weight: LocalWeightId,
        input: ContextId,
    },
    SuffixRightPops {
        input: ContextId,
        weight: LocalWeightId,
    },
    Swap {
        input: ContextId,
    },
    BothFromRight {
        input: ContextId,
        certificate: EntryCertificateId,
    },
    Replay {
        lower: ContextId,
        upper: ContextId,
    },
    WithoutLeftFilter {
        input: ContextId,
    },
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct ScopedDemand {
    pub original_call: usize,
    pub use_instance: usize,
    pub root: Term,
    pub output_scope: candidate_scope::EffectScopeId,
    pub input: candidate_scope::InputRouteId,
}
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub(super) struct ScopedFlow {
    pub transformer: usize,
    pub demand: Option<ScopedDemand>,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct ScopedObservation {
    pub relation: RelationId,
    pub operand: EffectEndpointKey,
}
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub(super) struct ScopedFlowId(usize);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct RelationKey {
    pub(super) pair: TypedPairKey,
    pub(super) context: ContextId,
    pub(super) sources: Option<usize>,
    pub(super) scoped: ScopedFlowId,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct Relation {
    pub(super) key: RelationKey,
    pub(super) previous_on_pair: Option<RelationId>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ReplayDemandRow {
    pub call: usize,
    pub child: RelationId,
    pub lower: RelationId,
    pub upper: RelationId,
    pub lower_input: BoundKey,
    pub upper_input: BoundKey,
    pub demand: ScopedDemand,
    pub lower_matches: bool,
    pub upper_matches: bool,
}
// Operation incidence is inert: child admission still reconstructs its own
// executable context. In particular this never constructs a structural Swap(I).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum FunctionPortOperation {
    Swap,
    Preserve,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum TransportReason {
    Extrusion { operation: ExtrusionEndpoint, polarity: Polarity, target_level: u32 },
    ParentCopy { parent_index: usize },
    EqualityCanonicalization,
    FreshUse,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct TransportWitness {
    pub from: BoundKey,
    pub to: BoundKey,
    pub reason: TransportReason,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Dependency {
    Derived {
        child: RelationId,
        parent: RelationId,
    },
    FunctionPort {
        child: RelationId,
        parent: RelationId,
        field: FunctionField,
        operation: FunctionPortOperation,
    },
    // Parent order is lower then upper, independently of insertion direction.
    Replay {
        child: RelationId,
        lower: RelationId,
        upper: RelationId,
        lower_input: BoundKey,
        upper_input: BoundKey,
    },
    Transport {
        child: RelationId,
        parent: RelationId,
        use_origin: usize,
        witness: Option<TransportWitness>,
    },
}
#[derive(Debug)]
#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "source origin certificates are retained independently of semantic conflict traversal"
    )
)]
pub(super) struct Origin {
    pub(super) relation: RelationId,
    pub(super) occurrence: ConstraintOccurrenceId,
    pub(super) inferred_entry: Option<InferredEntryOriginId>,
    pub(super) formal: Option<FormalConstruction>,
}
// An owning Lambda construction, never a callback contract or runtime receipt.
#[derive(Debug)]
#[cfg_attr(not(test), allow(dead_code, reason = "formal construction evidence has no semantic consumer"))]
pub(super) struct FormalConstruction {
    pub source: Arc<candidate_source::OmittedFormal>,
    pub domain: ValueEndpointKey,
    pub domain_child: Term,
    pub function: ValueEndpointKey,
}
#[derive(Debug)]
#[allow(dead_code, reason = "structural source evidence is not an effect consumer")]
pub(super) struct FormalArgumentIncidence<'a> {
    pub construction: &'a FormalConstruction,
    pub source_relation: RelationId,
    pub transport_relation: RelationId,
    pub name_handoff: Option<RelationId>,
    pub name_link: Option<RelationId>,
    pub comparison: RelationId,
    pub argument: RelationId,
    pub use_origin: usize,
    pub domain: ValueEndpointKey,
    pub actual: ValueEndpointKey,
}

impl InferenceSession {
    // Bounded, inert inspection of a captured Function bound, optionally through
    // the one source Name handoff. Earlier extrusion/derived routes are excluded.
    #[allow(dead_code, reason = "structural source evidence is not an effect consumer")]
    pub(super) fn candidate_formal_argument_incidence(&self, argument: RelationId) -> Option<FormalArgumentIncidence<'_>> {
        let state = &self.candidate_graph.as_ref()?.intrusion.effect_algebra.context;
        let TypedPairKey::Value(argument_pair) = state.relations.get(argument.0 as usize)?.key.pair else { return None; };
        for dependency in &state.dependencies {
            let Dependency::FunctionPort { child, parent: comparison, field: FunctionField::Argument, operation: FunctionPortOperation::Swap } = *dependency else { continue; };
            if child != argument { continue; }
            let TypedPairKey::Value(parent_pair) = state.relations.get(comparison.0 as usize)?.key.pair else { continue; };
            let Some((domain, _, _, _)) = Self::positive_function_children(&self.store, parent_pair.lower) else { continue; };
            // The dependency authenticates the child. Equality only reconciles
            // its retained endpoint with the current representative; it cannot
            // select a source construction or create an incidence.
            if self.value_endpoint(domain, Polarity::Negative) != self.canonical_value(argument_pair.upper) { continue; }
            for replay in &state.dependencies {
                let Dependency::Replay { child, lower, upper, lower_input, upper_input } = *replay else { continue; };
                if child != comparison { continue; }
                if state.relations.get(lower.0 as usize)?.key.pair != bound_pair(lower_input)
                    || state.relations.get(upper.0 as usize)?.key.pair != bound_pair(upper_input)
                    || lower_input.0 != upper_input.0 || lower_input.1 != Polarity::Positive
                    || upper_input.1 != Polarity::Negative
                    || lower_input.2 != ExtrusionEndpoint::Value(parent_pair.lower)
                    || upper_input.2 != ExtrusionEndpoint::Value(parent_pair.upper) { continue; }
                for transport in &state.dependencies {
                    let Dependency::Transport { child: fresh, parent, use_origin, witness: Some(TransportWitness { from, to, reason: TransportReason::FreshUse }) } = *transport else { continue; };
                    if to.1 != Polarity::Positive
                        || to.2 != ExtrusionEndpoint::Value(parent_pair.lower) { continue; }
                    let (name_handoff, name_link) = if fresh == lower && to == lower_input {
                        (None, None)
                    } else {
                        let Some((handoff, link)) = self.candidate_formal_name_handoff(state, fresh, to, lower, lower_input) else { continue; };
                        (Some(handoff), Some(link))
                    };
                    for origin in &state.origins {
                        let Some(construction) = &origin.formal else { continue; };
                        if origin.relation != parent || from.1 != Polarity::Positive
                            || from.2 != ExtrusionEndpoint::Value(construction.function) { continue; }
                        let Some((original_domain, _, _, _)) = Self::positive_function_children(&self.store, construction.function) else { continue; };
                        if original_domain != construction.domain_child { continue; }
                        let Ok(TermView::LiveVariable(view)) = self.store.term_view(original_domain) else { continue; };
                        if view.kind() != ComponentKind::Value || view.polarity() != Polarity::Negative
                            || construction.domain != ValueEndpointKey::ValueRow(view.ordinal()) { continue; }
                        return Some(FormalArgumentIncidence {
                            construction, source_relation: parent, transport_relation: fresh, name_handoff, name_link,
                            comparison, argument, use_origin, domain: argument_pair.upper, actual: argument_pair.lower,
                        });
                    }
                }
            }
        }
        None
    }

    // Recognize only the source local-use publication seam. All participating
    // relations and both replay bounds are retained construction inputs.
    fn candidate_formal_name_handoff(&self, state: &State, fresh: RelationId, to: BoundKey,
        name_bound: RelationId, name_input: BoundKey) -> Option<(RelationId, RelationId)> {
        if state.relations.get(fresh.0 as usize)?.key.pair != bound_pair(to)
            || name_input.1 != Polarity::Positive || name_input.2 != to.2 { return None; }
        for dependency in &state.dependencies {
            let Dependency::Derived { child, parent: handoff } = *dependency else { continue; };
            if child != name_bound { continue; }
            if state.relations.get(handoff.0 as usize)?.key.pair != bound_pair(name_input) { continue; }
            for replay in &state.dependencies {
                let Dependency::Replay { child, lower, upper: link, lower_input, upper_input } = *replay else { continue; };
                if child != handoff || lower != fresh || lower_input != to
                    || upper_input != BoundKey(to.0, Polarity::Negative, name_input.0)
                    || state.relations.get(link.0 as usize)?.key.pair != bound_pair(upper_input) { continue; }
                // This is the actual source Name's local-use admission, not an
                // arbitrary equal-row upper bound or an ancestor search.
                let named = state.origins.iter().filter(|origin| origin.relation == link && origin.occurrence.local_slot() == 0)
                    .any(|origin| self.batch.candidate_source.schedules.values().flatten().chain(self.batch.candidate_source.loose.iter())
                        .any(|action| matches!(action, candidate_source::Action::Local { occurrence, .. }
                            if occurrence == origin.occurrence.occurrence())));
                if named { return Some((handoff, link)); }
            }
        }
        None
    }
}
#[derive(Clone, Copy, Debug)]
pub(super) struct BundleIncidence {
    pub(super) relation: RelationId,
    pub(super) bundle: AttachmentBundleId,
    pub(super) previous_on_relation: Option<usize>,
}
#[derive(Debug, Default)]
struct BundleTransports {
    heads: HashMap<RelationId, usize>,
    log: Vec<(RelationId, RelationId, Option<usize>)>,
}
impl BundleTransports {
    fn insert(&mut self, parent: RelationId, child: RelationId) -> Result<(), SolveAvailabilityError> {
        self.heads.try_reserve(1).map_err(|_| exhausted())?;
        self.log.try_reserve(1).map_err(|_| exhausted())?;
        let previous = self.heads.insert(parent, self.log.len());
        self.log.push((parent, child, previous));
        Ok(())
    }
    fn rollback(&mut self, length: usize) {
        for (parent, _, previous) in self.log.drain(length..).rev() {
            if let Some(previous) = previous { self.heads.insert(parent, previous); }
            else { self.heads.remove(&parent); }
        }
    }
    fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        self.heads.capacity().checked_mul(std::mem::size_of::<(RelationId, usize)>())
            .and_then(|n| n.checked_add(self.log.capacity().checked_mul(std::mem::size_of::<(RelationId, RelationId, Option<usize>)>())?)).ok_or_else(exhausted)
    }
}
// Inert producer retention. IDs name construction records, never authorization.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct BoundAdmissionId(pub usize);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct BoundEmissionId(pub usize);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct BoundEvidenceGroupId(usize);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct EvidenceSnapshotId(pub usize);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ReplayRecipeId(usize);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum CoverageGap {
    MissingBoundRelation, MissingBoundGroup, MissingPhysicalEmission, MissingAntecedent,
    ProcessingAntecedentsUnavailable, OrdinarySeedAuthenticationUnavailable,
    ReplayUseAntecedentsNotRetained, MissingOriginAssociation,
}
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub(super) struct EvidenceCoverage { gaps: u8 }
impl EvidenceCoverage {
    fn add(&mut self, gap: CoverageGap) {
        assert!((gap as u8) < u8::BITS as u8);
        self.gaps |= 1 << gap as u8;
    }
    #[cfg(test)]
    fn contains(self, gap: CoverageGap) -> bool { self.gaps & (1 << gap as u8) != 0 }
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum BoundLane {
    ValueLowerRow, ValueUpperRow, ValueLowerAtom, ValueUpperAtom,
    EffectLowerRow, EffectUpperRow, EffectLowerAtom, EffectUpperAtom,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct PhysicalBoundSlot { pub owner: candidate_scheme::RowKey, pub lane: BoundLane, pub index: usize }
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum PhysicalReadbackPhase { ConstructorAfterAppend }
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct PhysicalBoundReadback {
    pub slot: PhysicalBoundSlot,
    pub bound: BoundKey,
    pub phase: PhysicalReadbackPhase,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum BoundConstructionPurpose { Ordinary, ExtrusionLink }
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum BoundAdmissionCause {
    OwnerEmission { processing: Option<RelationId> },
    ExtrusionLink { processing: Option<RelationId> },
    FreshUse { antecedent: EvidenceSnapshotId, use_origin: usize, source_bound: BoundKey, mapped_relation: Option<RelationId> },
    BoundTransport { antecedent: EvidenceSnapshotId, through: TransportReason },
}
#[derive(Clone, Copy, Debug)]
#[cfg_attr(not(test), allow(dead_code, reason = "inert producer evidence has no authorization consumer"))]
pub(super) struct BoundAdmission {
    pub bound: BoundKey, pub origin: TypedPairKey, pub relation: Option<RelationId>,
    group: BoundEvidenceGroupId, pub cause: BoundAdmissionCause, pub coverage: EvidenceCoverage,
    previous_on_group: Option<BoundAdmissionId>,
}
#[derive(Clone, Copy, Debug)]
#[cfg_attr(not(test), allow(dead_code, reason = "inert physical emission evidence"))]
pub(super) struct BoundEmission {
    pub admission: BoundAdmissionId, pub bound: BoundKey, pub physical: PhysicalBoundSlot,
    pub readback: PhysicalBoundReadback,
    previous_on_group: Option<BoundEmissionId>,
}
#[derive(Clone, Copy, Debug)]
struct BoundEvidenceGroup {
    admission_head: Option<BoundAdmissionId>, emission_head: Option<BoundEmissionId>,
    coverage: EvidenceCoverage,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct EvidenceSnapshot {
    pub source_bound: BoundKey, pub relation: Option<RelationId>,
    admission_head: Option<BoundAdmissionId>, emission_head: Option<BoundEmissionId>,
    pub coverage: EvidenceCoverage,
}
impl EvidenceSnapshot {
    pub(super) fn with_gap(mut self, gap: CoverageGap) -> Self { self.coverage.add(gap); self }
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct FiberTransformId(usize);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct FiberTransform {
    antecedent: EvidenceSnapshotId, from: BoundKey, to: BoundKey,
    source_relation: RelationId, child_relation: RelationId, reason: TransportReason,
    coverage: EvidenceCoverage,
}
// Borrowed only in the owning live State/route. Bare IDs do not authenticate
// cross-State or rollback-retired records, nor destination admissions/emissions.
#[allow(dead_code, reason = "inert direct association has no authorization consumer")]
struct DirectTransportAdmissions<'a> {
    admissions: &'a [BoundAdmission], transform: &'a FiberTransform,
    group: Option<BoundEvidenceGroupId>, next: Option<BoundAdmissionId>,
}
impl<'a> Iterator for DirectTransportAdmissions<'a> {
    type Item = Result<(BoundAdmissionId, &'a BoundAdmission, &'a FiberTransform), InputGap>;
    fn next(&mut self) -> Option<Self::Item> {
        let id = self.next.take()?;
        let Some(record) = self.admissions.get(id.0) else { return Some(Err(InputGap::MissingReference)); };
        if record.bound != self.transform.from || record.relation != Some(self.transform.source_relation)
            || Some(record.group) != self.group
            || record.previous_on_group.is_some_and(|previous| previous.0 >= id.0) {
            return Some(Err(InputGap::InconsistentReference));
        }
        self.next = record.previous_on_group;
        Some(Ok((id, record, self.transform)))
    }
}
#[derive(Clone, Copy, Debug)]
#[cfg_attr(not(test), allow(dead_code, reason = "typed inert reverse incidence has no authorization consumer"))]
enum EvidenceDependent { Admission(BoundAdmissionId), FiberTransform(FiberTransformId) }
#[derive(Clone, Copy, Debug)]
#[cfg_attr(not(test), allow(dead_code, reason = "structural replay evidence has no authorization consumer"))]
struct ReplayRecipe { dependency: Dependency, coverage: EvidenceCoverage }
#[derive(Clone, Copy, Debug)]
#[cfg_attr(not(test), allow(dead_code, reason = "inert reverse construction incidence"))]
struct EvidenceReverseEdge { antecedent: EvidenceSnapshotId, dependent: EvidenceDependent, previous: Option<usize> }
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct EvidenceCounters {
    attempts: usize, duplicate_admissions: usize, snapshot_hits: usize,
    fresh_uses: usize, transports: usize, replay_visits: usize, recipe_hits: usize,
    admission_samples: usize, emission_samples: usize, witness_attempts: usize, transform_hits: usize,
}
#[derive(Debug, Default)]
struct BoundEvidence {
    admissions: Vec<BoundAdmission>, emissions: Vec<BoundEmission>,
    groups: Vec<BoundEvidenceGroup>, group_keys: HashMap<(BoundKey, Option<RelationId>), BoundEvidenceGroupId>,
    group_log: Vec<(BoundEvidenceGroupId, BoundEvidenceGroup)>,
    snapshots: Vec<EvidenceSnapshot>, snapshot_keys: HashMap<EvidenceSnapshot, EvidenceSnapshotId>,
    recipes: Vec<ReplayRecipe>, recipe_keys: HashMap<Dependency, ReplayRecipeId>,
    reverse: Vec<EvidenceReverseEdge>, reverse_heads: HashMap<EvidenceSnapshotId, usize>,
    transforms: Vec<FiberTransform>, transform_keys: HashMap<FiberTransform, FiberTransformId>,
    transform_children: HashMap<RelationId, FiberTransformId>,
    transform_child_log: Vec<(RelationId, FiberTransformId, Option<FiberTransformId>)>,
    counters: EvidenceCounters,
    #[cfg(test)]
    failed_attempts: usize,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct EvidenceCheckpoint {
    admissions: usize, emissions: usize, groups: usize, group_log: usize,
    snapshots: usize, recipes: usize, reverse: usize, transforms: usize, transform_children: usize, counters: EvidenceCounters,
}
impl BoundEvidence {
    fn checkpoint(&self) -> EvidenceCheckpoint {
        EvidenceCheckpoint { admissions: self.admissions.len(), emissions: self.emissions.len(),
            groups: self.groups.len(), group_log: self.group_log.len(), snapshots: self.snapshots.len(),
            recipes: self.recipes.len(), reverse: self.reverse.len(), transforms: self.transforms.len(),
            transform_children: self.transform_child_log.len(), counters: self.counters }
    }
    fn rollback(&mut self, checkpoint: EvidenceCheckpoint) {
        #[cfg(test)]
        { self.failed_attempts += self.counters.attempts - checkpoint.counters.attempts; }
        for edge in self.reverse.drain(checkpoint.reverse..).rev() {
            if let Some(previous) = edge.previous { self.reverse_heads.insert(edge.antecedent, previous); }
            else { self.reverse_heads.remove(&edge.antecedent); }
        }
        for (child, _, previous) in self.transform_child_log.drain(checkpoint.transform_children..).rev() {
            if let Some(previous) = previous { self.transform_children.insert(child, previous); }
            else { self.transform_children.remove(&child); }
        }
        for transform in self.transforms.drain(checkpoint.transforms..) { self.transform_keys.remove(&transform); }
        for (group, old) in self.group_log.drain(checkpoint.group_log..).rev() { self.groups[group.0] = old; }
        // Every new group has an admission whose immutable key owns its map entry.
        for admission in &self.admissions[checkpoint.admissions..] {
            if admission.group.0 >= checkpoint.groups { self.group_keys.remove(&(admission.bound, admission.relation)); }
        }
        for snapshot in self.snapshots.drain(checkpoint.snapshots..) { self.snapshot_keys.remove(&snapshot); }
        for recipe in self.recipes.drain(checkpoint.recipes..) { self.recipe_keys.remove(&recipe.dependency); }
        self.admissions.truncate(checkpoint.admissions);
        self.emissions.truncate(checkpoint.emissions);
        self.groups.truncate(checkpoint.groups);
        self.counters = checkpoint.counters;
    }
    fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        let parts = [
            Some(std::mem::size_of::<EvidenceCounters>() + if cfg!(test) { std::mem::size_of::<usize>() } else { 0 }),
            self.admissions.capacity().checked_mul(std::mem::size_of::<BoundAdmission>()),
            self.emissions.capacity().checked_mul(std::mem::size_of::<BoundEmission>()),
            self.groups.capacity().checked_mul(std::mem::size_of::<BoundEvidenceGroup>()),
            self.group_keys.capacity().checked_mul(std::mem::size_of::<((BoundKey, Option<RelationId>), BoundEvidenceGroupId)>()),
            self.group_log.capacity().checked_mul(std::mem::size_of::<(BoundEvidenceGroupId, BoundEvidenceGroup)>()),
            self.snapshots.capacity().checked_mul(std::mem::size_of::<EvidenceSnapshot>()),
            self.snapshot_keys.capacity().checked_mul(std::mem::size_of::<(EvidenceSnapshot, EvidenceSnapshotId)>()),
            self.recipes.capacity().checked_mul(std::mem::size_of::<ReplayRecipe>()),
            self.recipe_keys.capacity().checked_mul(std::mem::size_of::<(Dependency, ReplayRecipeId)>()),
            self.transforms.capacity().checked_mul(std::mem::size_of::<FiberTransform>()),
            self.transform_keys.capacity().checked_mul(std::mem::size_of::<(FiberTransform, FiberTransformId)>()),
            self.transform_children.capacity().checked_mul(std::mem::size_of::<(RelationId, FiberTransformId)>()),
            self.transform_child_log.capacity().checked_mul(std::mem::size_of::<(RelationId, FiberTransformId, Option<FiberTransformId>)>()),
            self.reverse.capacity().checked_mul(std::mem::size_of::<EvidenceReverseEdge>()),
            self.reverse_heads.capacity().checked_mul(std::mem::size_of::<(EvidenceSnapshotId, usize)>()),
        ];
        parts.into_iter().try_fold(0usize, |n, part| n.checked_add(part.ok_or_else(exhausted)?).ok_or_else(exhausted))
    }
    #[cfg(test)]
    fn enumerated_bytes(&self) -> usize {
        assert_eq!(self.group_keys.len(), self.groups.len());
        assert_eq!(self.snapshot_keys.len(), self.snapshots.len());
        assert_eq!(self.recipe_keys.len(), self.recipes.len());
        for (&snapshot, &id) in &self.snapshot_keys { assert_eq!(self.snapshots[id.0], snapshot); }
        for (&dependency, &id) in &self.recipe_keys { assert_eq!(self.recipes[id.0].dependency, dependency); }
        for edge in &self.reverse {
            match edge.dependent {
                EvidenceDependent::Admission(id) => assert!(id.0 < self.admissions.len()),
                EvidenceDependent::FiberTransform(id) => assert!(id.0 < self.transforms.len()),
            }
            assert!(edge.antecedent.0 < self.snapshots.len());
        }
        assert_eq!(self.transforms.len(), self.transform_keys.len());
        for (&transform, &id) in &self.transform_keys { assert_eq!(self.transforms[id.0], transform); }
        for (index, admission) in self.admissions.iter().enumerate() {
            let _ = admission.origin;
            if let Some(previous) = admission.previous_on_group {
                assert!(previous.0 < index);
                assert_eq!(self.admissions[previous.0].group, admission.group);
            }
        }
        for emission in &self.emissions {
            assert_eq!(emission.bound, self.admissions[emission.admission.0].bound);
            if let Some(previous) = emission.previous_on_group { assert!(previous.0 < self.emissions.len()); }
        }
        std::mem::size_of::<EvidenceCounters>() + std::mem::size_of::<usize>()
            + self.admissions.capacity() * std::mem::size_of::<BoundAdmission>()
            + self.emissions.capacity() * std::mem::size_of::<BoundEmission>()
            + self.groups.capacity() * std::mem::size_of::<BoundEvidenceGroup>()
            + self.group_keys.capacity() * std::mem::size_of::<((BoundKey, Option<RelationId>), BoundEvidenceGroupId)>()
            + self.group_log.capacity() * std::mem::size_of::<(BoundEvidenceGroupId, BoundEvidenceGroup)>()
            + self.snapshots.capacity() * std::mem::size_of::<EvidenceSnapshot>()
            + self.snapshot_keys.capacity() * std::mem::size_of::<(EvidenceSnapshot, EvidenceSnapshotId)>()
            + self.recipes.capacity() * std::mem::size_of::<ReplayRecipe>()
            + self.recipe_keys.capacity() * std::mem::size_of::<(Dependency, ReplayRecipeId)>()
            + self.transforms.capacity() * std::mem::size_of::<FiberTransform>()
            + self.transform_keys.capacity() * std::mem::size_of::<(FiberTransform, FiberTransformId)>()
            + self.transform_children.capacity() * std::mem::size_of::<(RelationId, FiberTransformId)>()
            + self.transform_child_log.capacity() * std::mem::size_of::<(RelationId, FiberTransformId, Option<FiberTransformId>)>()
            + self.reverse.capacity() * std::mem::size_of::<EvidenceReverseEdge>()
            + self.reverse_heads.capacity() * std::mem::size_of::<(EvidenceSnapshotId, usize)>()
    }
    fn snapshot(&self, source_bound: BoundKey, relation: Option<RelationId>) -> EvidenceSnapshot {
        let mut coverage = EvidenceCoverage::default();
        if relation.is_none() { coverage.add(CoverageGap::MissingBoundRelation); }
        let group = self.group_keys.get(&(source_bound, relation))
            .map(|id| self.groups[id.0]);
        let (admission_head, emission_head) = if let Some(group) = group {
            coverage.gaps |= group.coverage.gaps;
            (group.admission_head, group.emission_head)
        } else { coverage.add(CoverageGap::MissingBoundGroup); (None, None) };
        if admission_head.is_none() { coverage.add(CoverageGap::MissingAntecedent); }
        if emission_head.is_none() { coverage.add(CoverageGap::MissingPhysicalEmission); }
        EvidenceSnapshot { source_bound, relation, admission_head, emission_head, coverage }
    }
    fn intern_snapshot(&mut self, snapshot: EvidenceSnapshot) -> Result<EvidenceSnapshotId, SolveAvailabilityError> {
        if let Some(&id) = self.snapshot_keys.get(&snapshot) { self.counters.snapshot_hits += 1; return Ok(id); }
        self.snapshots.try_reserve(1).map_err(|_| exhausted())?;
        self.snapshot_keys.try_reserve(1).map_err(|_| exhausted())?;
        let id = EvidenceSnapshotId(self.snapshots.len());
        self.snapshots.push(snapshot);
        self.snapshot_keys.insert(snapshot, id);
        Ok(id)
    }
    fn admit(&mut self, bound: BoundKey, origin: TypedPairKey, relation: Option<RelationId>,
        cause: BoundAdmissionCause, duplicate: bool) -> Result<BoundAdmissionId, SolveAvailabilityError> {
        let mut coverage = EvidenceCoverage::default();
        let antecedent = match cause {
            BoundAdmissionCause::OwnerEmission { .. } | BoundAdmissionCause::ExtrusionLink { .. } => {
                coverage.add(CoverageGap::ProcessingAntecedentsUnavailable);
                coverage.add(CoverageGap::OrdinarySeedAuthenticationUnavailable);
                coverage.add(CoverageGap::MissingAntecedent);
                None
            }
            BoundAdmissionCause::FreshUse { antecedent, .. } | BoundAdmissionCause::BoundTransport { antecedent, .. } => {
                coverage = self.snapshots.get(antecedent.0).ok_or_else(exhausted)?.coverage;
                Some(antecedent)
            }
        };
        if relation.is_none() {
            coverage.add(CoverageGap::MissingBoundRelation);
            coverage.add(CoverageGap::MissingOriginAssociation);
        }
        if matches!(cause, BoundAdmissionCause::FreshUse { .. }) { coverage.add(CoverageGap::ReplayUseAntecedentsNotRetained); }
        self.admissions.try_reserve(1).map_err(|_| exhausted())?;
        self.groups.try_reserve(1).map_err(|_| exhausted())?;
        self.group_keys.try_reserve(1).map_err(|_| exhausted())?;
        self.group_log.try_reserve(1).map_err(|_| exhausted())?;
        if antecedent.is_some() {
            self.reverse.try_reserve(1).map_err(|_| exhausted())?;
            self.reverse_heads.try_reserve(1).map_err(|_| exhausted())?;
        }
        let group = if let Some(&group) = self.group_keys.get(&(bound, relation)) { group } else {
            let group = BoundEvidenceGroupId(self.groups.len());
            self.groups.push(BoundEvidenceGroup { admission_head: None, emission_head: None, coverage: EvidenceCoverage::default() });
            self.group_keys.insert((bound, relation), group);
            group
        };
        let old = self.groups[group.0];
        self.group_log.push((group, old));
        let id = BoundAdmissionId(self.admissions.len());
        self.admissions.push(BoundAdmission { bound, origin, relation, group, cause, coverage, previous_on_group: old.admission_head });
        self.groups[group.0].admission_head = Some(id);
        self.groups[group.0].coverage.gaps |= coverage.gaps;
        if let Some(antecedent) = antecedent {
            let previous = self.reverse_heads.insert(antecedent, self.reverse.len());
            self.reverse.push(EvidenceReverseEdge { antecedent, dependent: EvidenceDependent::Admission(id), previous });
        }
        self.counters.duplicate_admissions += usize::from(duplicate);
        self.counters.fresh_uses += usize::from(matches!(cause, BoundAdmissionCause::FreshUse { .. }));
        self.counters.transports += usize::from(matches!(cause, BoundAdmissionCause::BoundTransport { .. }));
        Ok(id)
    }
    fn reserve_emission(&mut self) -> Result<(), SolveAvailabilityError> {
        self.emissions.try_reserve(1).map_err(|_| exhausted())?;
        self.group_log.try_reserve(1).map_err(|_| exhausted())?;
        Ok(())
    }
    fn emit(&mut self, admission: BoundAdmissionId, physical: PhysicalBoundSlot,
        readback: PhysicalBoundReadback) -> BoundEmissionId {
        let record = self.admissions[admission.0];
        let old = self.groups[record.group.0];
        self.group_log.push((record.group, old));
        let id = BoundEmissionId(self.emissions.len());
        self.emissions.push(BoundEmission { admission, bound: record.bound, physical, readback,
            previous_on_group: old.emission_head });
        self.groups[record.group.0].emission_head = Some(id);
        id
    }
    fn direct_admission_head(&self, snapshot: &EvidenceSnapshot, from: BoundKey,
        source_relation: RelationId) -> Result<Option<BoundAdmissionId>, InputGap> {
        if snapshot.source_bound != from || snapshot.relation != Some(source_relation) {
            return Err(InputGap::InconsistentReference);
        }
        let Some(head) = snapshot.admission_head else { return Ok(None); };
        let record = self.admissions.get(head.0).ok_or(InputGap::MissingReference)?;
        if record.bound != from || record.relation != Some(source_relation)
            || record.previous_on_group.is_some_and(|previous| previous.0 >= head.0) {
            return Err(InputGap::InconsistentReference);
        }
        Ok(Some(head))
    }
    #[allow(dead_code, reason = "inert direct association has no authorization consumer")]
    fn direct_transport_admissions(&self, id: FiberTransformId) -> Result<DirectTransportAdmissions<'_>, InputGap> {
        let transform = self.transforms.get(id.0).ok_or(InputGap::MissingReference)?;
        let snapshot = self.snapshots.get(transform.antecedent.0).ok_or(InputGap::MissingReference)?;
        let next = self.direct_admission_head(snapshot, transform.from, transform.source_relation)?;
        let group = next.map(|head| self.admissions[head.0].group);
        Ok(DirectTransportAdmissions { admissions: &self.admissions, transform, group, next })
    }
    fn transform(&mut self, antecedent: EvidenceSnapshotId, witness: TransportWitness,
        source_relation: RelationId, child_relation: RelationId) -> Result<FiberTransformId, SolveAvailabilityError> {
        self.counters.witness_attempts += 1;
        let snapshot = self.snapshots.get(antecedent.0).ok_or_else(exhausted)?;
        let mut coverage = snapshot.coverage;
        // The frozen exact source prefix supplies direct admission association.
        // Inherited gaps and the ambiguous operational origin fallback stay intact.
        if !matches!(self.direct_admission_head(snapshot, witness.from, source_relation), Ok(Some(_))) {
            coverage.add(CoverageGap::MissingOriginAssociation);
        }
        let transform = FiberTransform { antecedent, from: witness.from, to: witness.to,
            source_relation, child_relation, reason: witness.reason, coverage };
        if let Some(&id) = self.transform_keys.get(&transform) { self.counters.transform_hits += 1; return Ok(id); }
        self.transforms.try_reserve(1).map_err(|_| exhausted())?;
        self.transform_keys.try_reserve(1).map_err(|_| exhausted())?;
        self.transform_children.try_reserve(1).map_err(|_| exhausted())?;
        self.transform_child_log.try_reserve(1).map_err(|_| exhausted())?;
        self.reverse.try_reserve(1).map_err(|_| exhausted())?;
        self.reverse_heads.try_reserve(1).map_err(|_| exhausted())?;
        let id = FiberTransformId(self.transforms.len());
        self.transforms.push(transform);
        self.transform_keys.insert(transform, id);
        let previous = self.transform_children.insert(child_relation, id);
        self.transform_child_log.push((child_relation, id, previous));
        let previous = self.reverse_heads.insert(antecedent, self.reverse.len());
        self.reverse.push(EvidenceReverseEdge { antecedent, dependent: EvidenceDependent::FiberTransform(id), previous });
        Ok(id)
    }
    fn recipe(&mut self, dependency: Dependency) -> Result<(), SolveAvailabilityError> {
        self.counters.replay_visits += 1;
        if self.recipe_keys.contains_key(&dependency) { self.counters.recipe_hits += 1; return Ok(()); }
        self.recipes.try_reserve(1).map_err(|_| exhausted())?;
        self.recipe_keys.try_reserve(1).map_err(|_| exhausted())?;
        let mut coverage = EvidenceCoverage::default();
        coverage.add(CoverageGap::ReplayUseAntecedentsNotRetained);
        self.recipe_keys.insert(dependency, ReplayRecipeId(self.recipes.len()));
        self.recipes.push(ReplayRecipe { dependency, coverage });
        Ok(())
    }
}
// Private synthetic source support only; this is never an entry certificate.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct SourceSupportId(usize);
#[derive(Debug)]
struct SourceSupportRegistration {
    watched: Vec<RelationId>,
    generation: u64,
    valid: bool,
}
#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceSupportFailure { Registration, DependencyPublication, AfterInvalidation }
#[derive(Debug, Default)]
pub(super) struct State {
    pub(super) scoped_enabled: bool,
    pub(super) scope_inventory: candidate_source::ScopeInventory,
    scope_transformers: Vec<(candidate_scope::ScopeTransformer, Option<usize>, usize)>,
    scope_transformer_heap: usize,
    scope_flows: Vec<ScopedFlow>,
    scope_flow_keys: HashMap<ScopedFlow, ScopedFlowId>,
    scope_observation_keys: HashSet<ScopedObservation>,
    scope_heads: HashMap<u64, usize>,
    pub(super) scope_observations: Vec<ScopedObservation>,
    // This first producer hook covers exact FunctionPort admission only.
    // It is independent of equality generation and cannot authorize a
    // certificate until the remaining producers and observation owners exist.
    pub(super) lifecycle_generation: u64,
    source_support: HashMap<SourceSupportId, SourceSupportRegistration>,
    source_support_log: Vec<SourceSupportId>,
    source_support_undo: Vec<SourceSupportId>,
    // Deliberately not rewound: a rolled-back ID must never name a retry.
    #[cfg_attr(not(test), allow(dead_code, reason = "only the synthetic test supplier allocates support IDs"))]
    next_source_support: usize,
    #[cfg(test)]
    source_support_failure: Option<SourceSupportFailure>,
    evidence: BoundEvidence,
    pub inferred_entries: Vec<InferredEntryOrigin>,
    pub bundles: Vec<AttachmentBundle>,
    bundle_bytes: usize,
    source_bundles: HashMap<ConstraintOccurrenceId, AttachmentBundleId>,
    source_bundle_log: Vec<ConstraintOccurrenceId>,
    bundle_incidence: HashSet<(RelationId, AttachmentBundleId)>,
    bundle_incidence_log: Vec<BundleIncidence>,
    bundle_incidence_heads: HashMap<RelationId, usize>,
    bundle_transports: Option<BundleTransports>,
    #[cfg(test)]
    bundle_visits: usize,
    weights: Vec<LocalWeight>,
    weight_bytes: usize,
    contexts: Vec<ContextExpr>,
    context_keys: HashMap<ContextExpr, ContextId>,
    source_sets: Vec<Vec<usize>>,
    source_set_bytes: usize,
    source_set_keys: HashMap<Vec<usize>, usize>,
    relations: Vec<Relation>,
    keys: HashMap<RelationKey, RelationId>,
    pair_heads: HashMap<TypedPairKey, RelationId>,
    dependencies: Vec<Dependency>,
    dependency_keys: HashSet<Dependency>,
    pub(super) origins: Vec<Origin>,
    bounds: HashMap<BoundKey, usize>,
    bound_keys: Vec<(BoundKey, RelationId, Option<usize>)>,
    replay_heads: HashMap<(BoundKey, BoundKey), (Option<usize>, Option<usize>)>,
    replay_log: Vec<((BoundKey, BoundKey), Option<(Option<usize>, Option<usize>)>)>,
    replay_operations: HashMap<ReplayOperationId, ReplayOperation>,
    next_replay_operation: usize,
    replay_operation_undo: Vec<ReplayOperationUndo>,
    replay_child_bytes: usize,
    pub(super) typed_drains: Vec<TypedDrainFrame>,
    typed_drain_undo: Vec<TypedDrainUndo>,
    #[cfg(test)]
    fail_replay_completion_undo_reserve: bool,
    #[cfg(test)]
    fail_replay_completion_after: Option<usize>,
    #[cfg(test)]
    failed_replay_completion_bytes: Option<(usize, usize)>,
    #[cfg(test)]
    operation_frontier_visits: usize,
    restorations: HashMap<ReplayOperationId, BoundRestoration>,
    restoration_undo: Vec<BoundRestorationUndo>,
    uses: usize,
    edges: HashMap<RelationId, Vec<RelationId>>,
    edge_keys: HashSet<(RelationId, RelationId)>,
    edge_log: Vec<(RelationId, RelationId)>,
    edge_bytes: usize,
    pub processing: Option<RelationId>,
    discharged: HashSet<RelationId>,
    discharge_residuals: HashMap<RelationId, ContextId>,
    discharge_log: Vec<RelationId>,
    // Synchronous validation scratch only; never captured or checkpointed.
    checking_filters: Option<(RelationId, HashSet<LocalWeightId>)>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Checkpoint {
    scope_observations: usize,
    lifecycle_generation: u64,
    source_support: usize,
    source_support_undo: usize,
    evidence: EvidenceCheckpoint,
    inferred_entries: usize,
    bundles: usize,
    source_bundles: usize,
    bundle_incidence: usize,
    bundle_transports: Option<usize>,
    weights: usize,
    contexts: usize,
    source_sets: usize,
    relations: usize,
    dependencies: usize,
    origins: usize,
    bounds: usize,
    uses: usize,
    replay_log: usize,
    next_replay_operation: usize,
    replay_operation_undo: usize,
    restoration_undo: usize,
    typed_drains: usize,
    typed_drain_undo: usize,
    edges: usize,
    processing: Option<RelationId>,
    discharges: usize,
}

/// Borrowed construction evidence. This never authorizes a context operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum InputGap {
    MissingReference,
    InconsistentReference,
    MissingTransportWitness,
    TransportAuthenticationUnavailable,
    InertOperation,
    FilterObligationsUnavailable,
    ProducerReadinessUnavailable,
    DependentObservationsUnavailable,
}
#[derive(Debug, Eq, PartialEq)]
pub(super) enum InputCompleteness {
    Incomplete(Vec<InputGap>),
    #[allow(dead_code, reason = "Packet 1 has no producer readiness or observation witness") ]
    Complete,
}
#[allow(dead_code, reason = "retained completeness fields are consumed by the next circuit packet")]
pub(super) struct RetainedInput<'a> {
    pub roots: &'a [RelationId],
    pub evidence: CircuitEvidence<'a>,
    pub completeness: InputCompleteness,
}
pub(super) struct CircuitEvidence<'a> {
    state: &'a State,
    pub views: &'a [candidate_effect::View],
    #[allow(dead_code, reason = "retained parent evidence is consumed by the next circuit packet")]
    pub parents: &'a [candidate_intrusion::Parent],
    relations: Vec<u8>,
    contexts: Vec<u8>,
    weights: Vec<u8>,
    selected_views: Vec<u8>,
}
#[allow(dead_code, reason = "borrowed evidence accessors are consumed by Packet 2")]
impl CircuitEvidence<'_> {
    pub fn relations(&self) -> impl Iterator<Item = (RelationId, &Relation)> {
        self.state.relations.iter().enumerate().filter(|(i, _)| self.relations[*i] != 0)
            .map(|(i, r)| (RelationId(i as u32), r))
    }
    pub fn dependencies(&self) -> impl Iterator<Item = &Dependency> {
        self.state.dependencies.iter().filter(|d| dependency_relations(**d).into_iter().flatten()
            .any(|id| self.includes(id)))
    }
    pub fn origins(&self) -> impl Iterator<Item = &Origin> {
        self.state.origins.iter().filter(|o| self.includes(o.relation))
    }
    pub fn inferred_entries(&self) -> impl Iterator<Item = &InferredEntryOrigin> {
        self.state.inferred_entries.iter().filter(|e| self.origins().any(|o| o.inferred_entry == Some(e.id)))
    }
    pub fn bounds(&self) -> impl Iterator<Item = (BoundKey, RelationId)> + '_ {
        self.state.bound_keys.iter().filter(|(_, r, _)| self.includes(*r)).map(|(k, r, _)| (*k, *r))
    }
    pub fn bundles(&self) -> impl Iterator<Item = (AttachmentBundleId, &AttachmentBundle)> {
        self.state.bundles.iter().enumerate().filter(|(i, _)| self.bundle_incidences().any(|b| b.bundle.0 == *i))
            .map(|(i, b)| (AttachmentBundleId(i), b))
    }
    pub fn bundle_incidences(&self) -> impl Iterator<Item = &BundleIncidence> {
        self.state.bundle_incidence_log.iter().filter(|b| self.includes(b.relation))
    }
    pub fn contexts(&self) -> impl Iterator<Item = (ContextId, &ContextExpr)> {
        self.state.contexts.iter().enumerate().filter(|(i, _)| self.contexts[*i] != 0)
            .map(|(i, c)| (ContextId(i as u32 + 1), c))
    }
    pub fn weights(&self) -> impl Iterator<Item = (LocalWeightId, &LocalWeight)> {
        self.state.weights.iter().enumerate().filter(|(i, _)| self.weights[*i] != 0)
            .map(|(i, w)| (LocalWeightId(i as u32), w))
    }
    pub fn filter_views(&self) -> impl Iterator<Item = (u32, &candidate_effect::View)> {
        self.views.iter().enumerate().filter(|(i, _)| self.selected_views[*i] != 0).map(|(i, v)| (i as u32, v))
    }
    pub fn includes(&self, id: RelationId) -> bool { self.relations.get(id.0 as usize) == Some(&1) }
}
#[allow(dead_code, reason = "retained input accounting is consumed by the next circuit packet")]
impl RetainedInput<'_> {
    /// Input-owned masks and gap storage; canonical retained payloads stay borrowed.
    pub fn owned_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        let e = &self.evidence;
        [e.relations.capacity(), e.contexts.capacity(), e.weights.capacity(), e.selected_views.capacity(),
            match &self.completeness { InputCompleteness::Incomplete(gaps) => gaps.capacity().checked_mul(std::mem::size_of::<InputGap>()).ok_or_else(exhausted)?, InputCompleteness::Complete => 0 }]
            .into_iter().try_fold(0usize, |n, part| n.checked_add(part).ok_or_else(exhausted))
    }
}
fn dependency_relations(d: Dependency) -> [Option<RelationId>; 3] {
    match d {
        Dependency::Derived { parent, child } | Dependency::FunctionPort { parent, child, .. }
        | Dependency::Transport { parent, child, .. } => [Some(parent), Some(child), None],
        Dependency::Replay { lower, upper, child, .. } => [Some(lower), Some(upper), Some(child)],
    }
}
fn input_mask(length: usize) -> Result<Vec<u8>, SolveAvailabilityError> {
    let mut mask = Vec::new();
    mask.try_reserve_exact(length).map_err(|_| exhausted())?;
    mask.resize(length, 0);
    Ok(mask)
}
fn select(mask: &mut [u8], index: usize, missing: &mut bool) -> bool {
    match mask.get_mut(index) {
        Some(slot) => { let changed = *slot == 0; *slot = 1; changed }
        None => { *missing = true; false }
    }
}
fn endpoint_view(endpoint: ExtrusionEndpoint) -> Option<usize> {
    match endpoint {
        ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(v) | EffectEndpointKey::Support(v) | EffectEndpointKey::AnnotationMember(v, _)) => Some(v as usize),
        _ => None,
    }
}
fn pair_endpoints(pair: TypedPairKey) -> [ExtrusionEndpoint; 2] {
    match pair {
        TypedPairKey::Value(pair) => [ExtrusionEndpoint::Value(pair.lower), ExtrusionEndpoint::Value(pair.upper)],
        TypedPairKey::Effect { lower, upper } => [ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(upper)],
    }
}
fn row_endpoint(row: candidate_scheme::RowKey) -> ExtrusionEndpoint {
    match row {
        candidate_scheme::RowKey::Value(id) => ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(id)),
        candidate_scheme::RowKey::Effect(id) => ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(id)),
    }
}
fn select_endpoint(endpoint: ExtrusionEndpoint, selected: &mut [u8], views: &[candidate_effect::View],
    missing: &mut bool, inconsistent: &mut bool,
) -> bool {
    let Some(view) = endpoint_view(endpoint) else { return false; };
    if let ExtrusionEndpoint::Effect(EffectEndpointKey::AnnotationMember(_, ordinal)) = endpoint {
        match views.get(view) {
            Some(view) => *inconsistent |= ordinal as usize >= view.allowed.len(),
            None => *missing = true,
        }
    }
    select(selected, view, missing)
}
impl State {
    #[cfg_attr(not(test), allow(dead_code, reason = "certificate input consumer is a later packet"))]
    pub(super) fn retained_input<'a>(
        &'a self, roots: &'a [RelationId], views: &'a [candidate_effect::View],
        parents: &'a [candidate_intrusion::Parent],
    ) -> Result<RetainedInput<'a>, SolveAvailabilityError> {
        let mut evidence = CircuitEvidence { state: self, views, parents,
            relations: input_mask(self.relations.len())?, contexts: input_mask(self.contexts.len())?,
            weights: input_mask(self.weights.len())?, selected_views: input_mask(views.len())? };
        let mut missing = false;
        let mut inconsistent = false;
        let mut missing_transport = false;
        let mut inert = false;
        let mut transport_authentication = false;
        for root in roots { select(&mut evidence.relations, root.0 as usize, &mut missing); }
        // Relations, bound registrations, source operands and shared context
        // children form one evidence closure, independent of solver/SCC edges.
        loop {
            let mut changed = false;
            for (index, relation) in self.relations.iter().enumerate() {
                if evidence.relations[index] == 0 { continue; }
                let context = relation.key.context;
                if context != IDENTITY { changed |= select(&mut evidence.contexts, context.0 as usize - 1, &mut missing); }
                for endpoint in pair_endpoints(relation.key.pair) {
                    changed |= select_endpoint(endpoint, &mut evidence.selected_views, views, &mut missing, &mut inconsistent);
                }
            }
            // Children precede parents in the canonical DAG. Reverse traversal
            // visits every shared child once in this expansion pass.
            for index in (0..self.contexts.len()).rev() {
                if evidence.contexts[index] == 0 { continue; }
                let (children, weight) = match self.contexts[index] {
                    ContextExpr::PrefixLeft { input, weight } => ([Some(input), None], Some(weight)),
                    ContextExpr::SuffixRightPops { input, weight } => { inert = true; ([Some(input), None], Some(weight)) },
                    ContextExpr::Replay { lower, upper } => { inert = true; ([Some(lower), Some(upper)], None) },
                    ContextExpr::Swap { input } | ContextExpr::BothFromRight { input, .. } | ContextExpr::WithoutLeftFilter { input } => { inert = true; ([Some(input), None], None) },
                };
                for child in children.into_iter().flatten() {
                    if child == IDENTITY { continue; }
                    if child.0 as usize > index { inconsistent = true; }
                    changed |= select(&mut evidence.contexts, child.0 as usize - 1, &mut missing);
                }
                if let Some(weight) = weight { changed |= select(&mut evidence.weights, weight.0 as usize, &mut missing); }
            }
            for i in 0..self.weights.len() {
                if evidence.weights[i] != 0 { changed |= select(&mut evidence.selected_views, self.weights[i].boundary as usize, &mut missing); }
            }
            for i in 0..views.len() {
                if evidence.selected_views[i] == 0 { continue; }
                for weight in [views[i].source_weight, views[i].closed_weight].into_iter().flatten() {
                    changed |= select(&mut evidence.weights, weight.0 as usize, &mut missing);
                }
            }
            for dependency in &self.dependencies {
                let ids = dependency_relations(*dependency);
                if !ids.into_iter().flatten().any(|id| evidence.includes(id)) { continue; }
                for id in ids.into_iter().flatten() { changed |= select(&mut evidence.relations, id.0 as usize, &mut missing); }
                let keys = match dependency {
                    Dependency::Replay { lower_input, upper_input, .. } => [Some(*lower_input), Some(*upper_input)],
                    Dependency::Transport { witness: Some(w), .. } => [Some(w.from), Some(w.to)],
                    _ => [None, None],
                };
                for key in keys.into_iter().flatten() {
                    missing |= !self.bounds.contains_key(&key);
                    for endpoint in [key.0, key.2] {
                        changed |= select_endpoint(endpoint, &mut evidence.selected_views, views, &mut missing, &mut inconsistent);
                    }
                    for id in self.bound_relations(key) { changed |= select(&mut evidence.relations, id.0 as usize, &mut missing); }
                }
            }
            for (key, id, _) in &self.bound_keys {
                let touches_view = [key.0, key.2].into_iter().filter_map(endpoint_view)
                    .any(|view| evidence.selected_views.get(view) == Some(&1));
                if !evidence.includes(*id) && !touches_view { continue; }
                for relation in self.bound_relations(*key) { changed |= select(&mut evidence.relations, relation.0 as usize, &mut missing); }
                for endpoint in [key.0, key.2] {
                    changed |= select_endpoint(endpoint, &mut evidence.selected_views, views, &mut missing, &mut inconsistent);
                }
            }
            if !changed { break; }
        }
        for (_, weight) in evidence.weights() {
            if let Some(set) = &weight.attachment {
                inert |= set.unit_push.is_some();
                inconsistent |= set.member_ordinals.len() != weight.allowed.len()
                    || set.member_ordinals.iter().any(|ordinal| *ordinal >= weight.allowed.len());
            }
            match views.get(weight.boundary as usize) {
                Some(view) => inconsistent |= view.owner != weight.owner || view.position != weight.position || view.allowed != weight.allowed,
                None => missing = true,
            }
        }
        for origin in evidence.origins() {
            if let Some(id) = origin.inferred_entry {
                match self.inferred_entries.get(id.0) {
                    Some(entry) => inconsistent |= entry.id != id || entry.occurrence != origin.occurrence,
                    None => missing = true,
                }
            }
        }
        for bundle in evidence.bundle_incidences() { missing |= self.bundles.get(bundle.bundle.0).is_none(); }
        for dependency in evidence.dependencies() {
            match dependency {
                Dependency::FunctionPort { .. } => inert = true,
                Dependency::Replay { lower, upper, lower_input, upper_input, .. } => {
                    inconsistent |= !self.bound_relations(*lower_input).any(|id| id == *lower)
                        || !self.bound_relations(*upper_input).any(|id| id == *upper);
                }
                Dependency::Transport { parent, child, witness, use_origin } => match witness {
                    None => missing_transport = true,
                    Some(w) => {
                        inconsistent |= !self.bound_relations(w.from).any(|id| id == *parent)
                            || !self.bound_relations(w.to).any(|id| id == *child);
                        for (key, id) in [(w.from, *parent), (w.to, *child)] {
                            match self.relations.get(id.0 as usize) {
                                Some(relation) => transport_authentication |= relation.key.pair != bound_pair(key),
                                None => missing = true,
                            }
                        }
                        match w.reason {
                            TransportReason::ParentCopy { parent_index } => match parents.get(parent_index) {
                                None => missing = true,
                                Some(record) => {
                                    let copy = row_endpoint(record.copy);
                                    let original = row_endpoint(record.parent);
                                    // Recorded original rows remain authentic after representative
                                    // changes; authenticating aliases needs the row-map owner.
                                    transport_authentication |= w.from.0 != copy || w.to.0 != original;
                                    inconsistent |= record.copy.kind() != record.parent.kind() || w.from.1 != w.to.1;
                                }
                            },
                            TransportReason::FreshUse => inconsistent |= *use_origin == 0,
                            // Exact keys are retained here; row-map/equality qualification
                            // remains evidence from its lifecycle owner, not endpoint inference.
                            TransportReason::Extrusion { .. } | TransportReason::EqualityCanonicalization => transport_authentication = true,
                        }
                    }
                },
                _ => {},
            }
        }
        let mut reasons = Vec::new();
        reasons.try_reserve_exact(8).map_err(|_| exhausted())?;
        if missing { reasons.push(InputGap::MissingReference); }
        if inconsistent { reasons.push(InputGap::InconsistentReference); }
        if missing_transport { reasons.push(InputGap::MissingTransportWitness); }
        if transport_authentication { reasons.push(InputGap::TransportAuthenticationUnavailable); }
        if inert { reasons.push(InputGap::InertOperation); }
        reasons.push(InputGap::FilterObligationsUnavailable);
        reasons.push(InputGap::ProducerReadinessUnavailable);
        reasons.push(InputGap::DependentObservationsUnavailable);
        Ok(RetainedInput { roots, evidence, completeness: InputCompleteness::Incomplete(reasons) })
    }
}
fn exhausted() -> SolveAvailabilityError {
    SolveAvailabilityError::IdentityExhausted
}
// Source correspondence: frozen constraints/directed_weight.rs and
// constraints/mod.rs:3566–3612, as mapped by the contextual-effect source note.
// Detached finite atom-set algebra: no source admission, parameterized/cofinite
// families, certificate authorization, residual construction, or filter discharge.
#[derive(Debug, Default, Eq, PartialEq)]
struct ExactCount(Vec<u32>);
impl ExactCount {
    fn from_u32(value: u32) -> Result<Self, SolveAvailabilityError> {
        let mut out = Self::default();
        if value != 0 { out.0.try_reserve(1).map_err(|_| exhausted())?; out.0.push(value); }
        Ok(out)
    }
    fn copy(&self) -> Result<Self, SolveAvailabilityError> {
        let mut out = Self::default();
        out.0.try_reserve(self.0.len()).map_err(|_| exhausted())?;
        out.0.extend_from_slice(&self.0);
        Ok(out)
    }
    fn is_zero(&self) -> bool { self.0.is_empty() }
    fn compare(&self, other: &Self) -> std::cmp::Ordering {
        self.0.len().cmp(&other.0.len()).then_with(|| self.0.iter().rev().cmp(other.0.iter().rev()))
    }
    fn add(&self, other: &Self) -> Result<Self, SolveAvailabilityError> {
        let length = self.0.len().max(other.0.len());
        let mut out = Self::default();
        out.0.try_reserve(length.checked_add(1).ok_or_else(exhausted)?).map_err(|_| exhausted())?;
        let mut carry = 0u64;
        for i in 0..length {
            let sum = self.0.get(i).copied().unwrap_or(0) as u64
                + other.0.get(i).copied().unwrap_or(0) as u64 + carry;
            out.0.push(sum as u32); carry = sum >> 32;
        }
        if carry != 0 { out.0.push(carry as u32); }
        Ok(out)
    }
    fn subtract(&self, other: &Self) -> Result<Self, SolveAvailabilityError> {
        if self.compare(other).is_lt() { return Err(exhausted()); }
        let mut out = self.copy()?;
        let mut borrow = 0u64;
        for (i, limb) in out.0.iter_mut().enumerate() {
            let sub = other.0.get(i).copied().unwrap_or(0) as u64 + borrow;
            let original = *limb as u64;
            *limb = if original < sub { original + (1u64 << 32) - sub } else { original - sub } as u32;
            borrow = u64::from(original < sub);
        }
        while out.0.last() == Some(&0) { out.0.pop(); }
        Ok(out)
    }
}
// PUSH payloads have finite resolved families. All belongs only to filters.
#[derive(Debug)]
struct DetachedPushFamily(Vec<SourceEffectId>);
impl PartialEq for DetachedPushFamily {
    fn eq(&self, other: &Self) -> bool {
        self.0.iter().all(|x| other.0.contains(x)) && other.0.iter().all(|x| self.0.contains(x))
    }
}
impl Eq for DetachedPushFamily {}
impl DetachedPushFamily {
    fn copy(&self) -> Result<Self, SolveAvailabilityError> {
        let mut out = Vec::new();
        out.try_reserve(self.0.len()).map_err(|_| exhausted())?;
        out.extend(self.0.iter().cloned());
        Ok(Self(out))
    }
}
#[derive(Debug)]
enum DetachedFilter { All, Finite(Vec<SourceEffectId>) }
impl PartialEq for DetachedFilter {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::All, Self::All) => true,
            (Self::Finite(a), Self::Finite(b)) => a.iter().all(|x| b.contains(x)) && b.iter().all(|x| a.contains(x)),
            _ => false,
        }
    }
}
impl Eq for DetachedFilter {}
impl DetachedFilter {
    fn copy(&self) -> Result<Self, SolveAvailabilityError> {
        match self {
            Self::All => Ok(Self::All),
            Self::Finite(atoms) => {
                let mut out = Vec::new(); out.try_reserve(atoms.len()).map_err(|_| exhausted())?;
                out.extend(atoms.iter().cloned()); Ok(Self::Finite(out))
            }
        }
    }
    fn intersect(&self, other: &Self) -> Result<Self, SolveAvailabilityError> {
        match (self, other) {
            (Self::All, family) | (family, Self::All) => family.copy(),
            (Self::Finite(a), Self::Finite(b)) => {
                let mut out = Vec::new(); out.try_reserve(a.len().min(b.len())).map_err(|_| exhausted())?;
                for atom in a { if b.contains(atom) && !out.contains(atom) { out.push(atom.clone()); } }
                Ok(Self::Finite(out))
            }
        }
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DetachedAttachmentId(u32);
#[derive(Debug, Eq, PartialEq)]
struct DetachedLeftEntry {
    id: DetachedAttachmentId,
    pops: ExactCount,
    pushes: ExactCount,
    family: Option<DetachedPushFamily>,
}
impl DetachedLeftEntry {
    fn copy(&self) -> Result<Self, SolveAvailabilityError> {
        Ok(Self { id: self.id, pops: self.pops.copy()?, pushes: self.pushes.copy()?,
            family: self.family.as_ref().map(DetachedPushFamily::copy).transpose()? })
    }
}
#[derive(Debug, Eq, PartialEq)]
struct DetachedRightEntry { id: DetachedAttachmentId, pops: ExactCount }
#[derive(Debug, Eq, PartialEq)]
struct DetachedWeight {
    left: Vec<DetachedLeftEntry>,
    filter: DetachedFilter,
    right: Vec<DetachedRightEntry>,
}
impl DetachedWeight {
    fn identity() -> Self { Self { left: Vec::new(), filter: DetachedFilter::All, right: Vec::new() } }
    fn copy(&self) -> Result<Self, SolveAvailabilityError> {
        let mut out = Self::identity(); out.filter = self.filter.copy()?;
        out.left.try_reserve(self.left.len()).map_err(|_| exhausted())?;
        for entry in &self.left { out.left.push(entry.copy()?); }
        out.append_right(&self.right)?;
        Ok(out)
    }
    fn append_left(&mut self, entries: &[DetachedLeftEntry]) -> Result<(), SolveAvailabilityError> {
        for incoming in entries {
            if incoming.pushes.is_zero() != incoming.family.is_none() { return Err(exhausted()); }
            let Some(index) = self.left.iter().position(|entry| entry.id == incoming.id) else {
                if !incoming.pops.is_zero() || !incoming.pushes.is_zero() {
                    self.left.try_reserve(1).map_err(|_| exhausted())?;
                    self.left.push(incoming.copy()?); self.left.sort_unstable_by_key(|entry| entry.id.0);
                }
                continue;
            };
            let current = &self.left[index];
            if let (Some(a), Some(b)) = (&current.family, &incoming.family) {
                if a != b { return Err(exhausted()); }
            }
            let (pops, pushes) = if incoming.pops.compare(&current.pushes).is_le() {
                (current.pops.copy()?, current.pushes.subtract(&incoming.pops)?.add(&incoming.pushes)?)
            } else {
                (current.pops.add(&incoming.pops.subtract(&current.pushes)?)?, incoming.pushes.copy()?)
            };
            let family = if pushes.is_zero() { None } else {
                Some(current.family.as_ref().or(incoming.family.as_ref()).ok_or_else(exhausted)?.copy()?)
            };
            if pops.is_zero() && pushes.is_zero() { self.left.remove(index); }
            else { self.left[index] = DetachedLeftEntry { id: incoming.id, pops, pushes, family }; }
        }
        Ok(())
    }
    fn append_right(&mut self, entries: &[DetachedRightEntry]) -> Result<(), SolveAvailabilityError> {
        for incoming in entries {
            if incoming.pops.is_zero() { continue; }
            if let Some(current) = self.right.iter_mut().find(|entry| entry.id == incoming.id) {
                current.pops = current.pops.add(&incoming.pops)?;
            } else {
                self.right.try_reserve(1).map_err(|_| exhausted())?;
                self.right.push(DetachedRightEntry { id: incoming.id, pops: incoming.pops.copy()? });
                self.right.sort_unstable_by_key(|entry| entry.id.0);
            }
        }
        Ok(())
    }
    fn right_to_left(&mut self, entries: &[DetachedRightEntry]) -> Result<(), SolveAvailabilityError> {
        for entry in entries {
            self.append_left(&[DetachedLeftEntry { id: entry.id, pops: entry.pops.copy()?, pushes: ExactCount::default(), family: None }])?;
        }
        Ok(())
    }
    fn mix(mut self) -> Result<Self, SolveAvailabilityError> {
        if self.left.is_empty() || self.right.is_empty() { return Ok(self); }
        let right = std::mem::take(&mut self.right);
        for entry in right {
            let id = entry.id;
            self.right_to_left(&[entry])?;
            if let Some(index) = self.left.iter().position(|left| left.id == id) {
                if self.left[index].pushes.is_zero() {
                    let left = self.left.remove(index);
                    self.append_right(&[DetachedRightEntry { id, pops: left.pops }])?;
                }
            }
        }
        Ok(self)
    }
}
#[derive(Debug)]
#[cfg_attr(not(test), allow(dead_code, reason = "detached result has no live source consumer"))]
struct DetachedEvaluation {
    value: DetachedWeight,
    // One exact record per reachable node retains weight/certificate tokens.
    // Numeric equality never interns or rewrites construction records.
    nodes: Vec<(ContextId, Option<ContextExpr>)>,
}
fn reserve_rename_scratch<T>(
    storage: &mut Vec<T>, additional: usize, scratch_bytes: &mut usize, charge: &mut usize,
) -> Result<(), SolveAvailabilityError> {
    let before = storage.capacity();
    storage.try_reserve(additional).map_err(|_| exhausted())?;
    let growth = (storage.capacity() - before).checked_mul(std::mem::size_of::<T>()).ok_or_else(exhausted)?;
    let next_charge = charge.checked_add(growth).ok_or_else(exhausted)?;
    let next_scratch = scratch_bytes.checked_add(growth).ok_or_else(exhausted)?;
    *charge = next_charge;
    *scratch_bytes = next_scratch;
    Ok(())
}
impl State {
    pub(super) fn retain_inferred_entry(
        &mut self, lambda: &HirOccurrenceId, entry: u32, returned: u32,
        occurrence: &ConstraintOccurrenceId, cause: &CauseId,
    ) -> Result<InferredEntryOriginId, SolveAvailabilityError> {
        let id = InferredEntryOriginId(self.inferred_entries.len());
        self.inferred_entries.try_reserve(1).map_err(|_| exhausted())?;
        self.inferred_entries.push(InferredEntryOrigin {
            id, lambda: lambda.clone(), entry: EffectEndpointKey::EffectRow(entry),
            returned: EffectEndpointKey::EffectRow(returned),
            occurrence: occurrence.clone(), cause: cause.clone(),
        });
        Ok(id)
    }

    // Detached per-use construction rename. Substitutions and the reusable map
    // belong to the caller's scratch lease; only traversal/journal storage is
    // charged here. Reuse the map only with unchanged substitutions and retained
    // nodes from this route/use; invalidate it when an outer route rolls back.
    // Certificates are opaque tokens, never entry authorization.
    #[cfg_attr(not(test), allow(dead_code, reason = "detached transport preparation has no live consumer"))]
    fn rename_contexts(
        &mut self,
        roots: &[ContextId],
        weights: &HashMap<LocalWeightId, LocalWeightId>,
        certificates: &HashMap<EntryCertificateId, EntryCertificateId>,
        remap: &mut HashMap<ContextId, ContextId>,
        scratch_bytes: &mut usize,
    ) -> Result<(), SolveAvailabilityError> {
        self.rename_contexts_impl(roots, weights, certificates, remap, scratch_bytes, false, &mut 0)
    }
    fn rename_contexts_impl(
        &mut self, roots: &[ContextId], weights: &HashMap<LocalWeightId, LocalWeightId>,
        certificates: &HashMap<EntryCertificateId, EntryCertificateId>,
        remap: &mut HashMap<ContextId, ContextId>, scratch_bytes: &mut usize,
        charge_map: bool, peak_bytes: &mut usize,
    ) -> Result<(), SolveAvailabilityError> {
        let checkpoint = self.checkpoint();
        let map_was_empty = remap.is_empty();
        let mut pending = Vec::<(ContextId, bool)>::new();
        let mut inserted = Vec::<ContextId>::new();
        let mut verified = HashSet::<ContextId>::new();
        let mut charge = 0usize;
        let result = (|| {
            for &root in roots {
                reserve_rename_scratch(&mut pending, 1, scratch_bytes, &mut charge)?;
                *peak_bytes = (*peak_bytes).max(*scratch_bytes);
                pending.push((root, false));
                while let Some((id, ready)) = pending.pop() {
                    if verified.contains(&id) { continue; }
                    // Newly interned outputs cannot make a malformed source
                    // handle valid partway through this rename.
                    if id.0 as usize > checkpoint.contexts { return Err(exhausted()); }
                    let expression = if id == IDENTITY { None } else {
                        Some(*self.contexts.get(id.0 as usize - 1).ok_or_else(exhausted)?)
                    };
                    let (children, count) = match expression {
                        None => ([IDENTITY, IDENTITY], 0),
                        Some(ContextExpr::Replay { lower, upper }) => ([lower, upper], 2),
                        Some(ContextExpr::PrefixLeft { input, .. }
                            | ContextExpr::SuffixRightPops { input, .. }
                            | ContextExpr::Swap { input }
                            | ContextExpr::BothFromRight { input, .. }
                            | ContextExpr::WithoutLeftFilter { input }) => ([input, IDENTITY], 1),
                    };
                    if children[..count].iter().any(|child| child.0 >= id.0) {
                        return Err(exhausted());
                    }
                    if !ready && count > 0 {
                        reserve_rename_scratch(&mut pending, count + 1, scratch_bytes, &mut charge)?;
                        *peak_bytes = (*peak_bytes).max(*scratch_bytes);
                        pending.push((id, true));
                        for &child in children[..count].iter().rev() {
                            if !verified.contains(&child) { pending.push((child, false)); }
                        }
                        continue;
                    }
                    let child = |input| remap.get(&input).copied().ok_or_else(exhausted);
                    let weight = |input: LocalWeightId| {
                        self.weights.get(input.0 as usize).ok_or_else(exhausted)?;
                        let copy = weights.get(&input).copied().ok_or_else(exhausted)?;
                        self.weights.get(copy.0 as usize).ok_or_else(exhausted)?;
                        Ok::<_, SolveAvailabilityError>(copy)
                    };
                    let renamed = match expression {
                        None => None,
                        Some(ContextExpr::PrefixLeft { weight: token, input }) =>
                            Some(ContextExpr::PrefixLeft { weight: weight(token)?, input: child(input)? }),
                        Some(ContextExpr::SuffixRightPops { input, weight: token }) =>
                            Some(ContextExpr::SuffixRightPops { input: child(input)?, weight: weight(token)? }),
                        Some(ContextExpr::Swap { input }) => Some(ContextExpr::Swap { input: child(input)? }),
                        Some(ContextExpr::BothFromRight { input, certificate }) => Some(ContextExpr::BothFromRight {
                            input: child(input)?, certificate: certificates.get(&certificate).copied().ok_or_else(exhausted)?,
                        }),
                        Some(ContextExpr::Replay { lower, upper }) =>
                            Some(ContextExpr::Replay { lower: child(lower)?, upper: child(upper)? }),
                        Some(ContextExpr::WithoutLeftFilter { input }) =>
                            Some(ContextExpr::WithoutLeftFilter { input: child(input)? }),
                    };
                    let old_capacity = verified.capacity();
                    verified.try_reserve(1).map_err(|_| exhausted())?;
                    let growth = (verified.capacity() - old_capacity).checked_mul(std::mem::size_of::<ContextId>()).ok_or_else(exhausted)?;
                    let next_charge = charge.checked_add(growth).ok_or_else(exhausted)?;
                    let next_scratch = scratch_bytes.checked_add(growth).ok_or_else(exhausted)?;
                    charge = next_charge;
                    *scratch_bytes = next_scratch;
                    *peak_bytes = (*peak_bytes).max(*scratch_bytes);
                    if let Some(&copy) = remap.get(&id) {
                        // Caller-seeded mappings are suggestions. Validate the
                        // exact reconstructed constructor before accepting one.
                        let actual = if copy == IDENTITY { None } else {
                            if copy.0 as usize > checkpoint.contexts { return Err(exhausted()); }
                            Some(*self.contexts.get(copy.0 as usize - 1).ok_or_else(exhausted)?)
                        };
                        if actual != renamed { return Err(exhausted()); }
                    } else {
                        // Reserve rollback storage before interning/publication.
                        reserve_rename_scratch(&mut inserted, 1, scratch_bytes, &mut charge)?;
                        let before = remap.capacity();
                        remap.try_reserve(1).map_err(|_| exhausted())?;
                        if charge_map {
                            // The caller retains this charge until its map drops,
                            // including a failed rename with retained capacity.
                            let growth = (remap.capacity() - before).checked_mul(std::mem::size_of::<(ContextId, ContextId)>()).ok_or_else(exhausted)?;
                            *scratch_bytes = scratch_bytes.checked_add(growth).ok_or_else(exhausted)?;
                        }
                        *peak_bytes = (*peak_bytes).max(*scratch_bytes);
                        let copy = match renamed { Some(node) => self.context(node)?, None => IDENTITY };
                        remap.insert(id, copy);
                        inserted.push(id);
                    }
                    verified.insert(id);
                }
            }
            Ok(())
        })();
        if result.is_err() {
            // A fresh-use map starts empty. Clear its deletion markers while
            // retaining the charged allocation for a supported retry.
            if charge_map && map_was_empty { remap.clear(); }
            else { for &id in &inserted { remap.remove(&id); } }
            self.rollback(checkpoint);
        }
        drop(pending);
        drop(inserted);
        drop(verified);
        *scratch_bytes -= charge;
        result
    }
    pub(super) fn rename_fresh_contexts(
        &mut self, roots: &[ContextId], weights: &HashMap<LocalWeightId, LocalWeightId>,
        remap: &mut HashMap<ContextId, ContextId>, scratch_bytes: &mut usize,
        peak_bytes: &mut usize,
    ) -> Result<(), SolveAvailabilityError> {
        self.rename_contexts_impl(roots, weights, &HashMap::new(), remap, scratch_bytes, true, peak_bytes)
    }
    pub(super) fn relation_context(&self, relation: RelationId) -> Result<ContextId, SolveAvailabilityError> {
        self.relations.get(relation.0 as usize).ok_or_else(exhausted)?;
        Ok(self.post_check_context(relation))
    }
    // Discovery follows construction edges once across all captured fibers.
    pub(super) fn context_payloads(
        &self, root: ContextId, visited: &mut HashSet<ContextId>,
        pending: &mut Vec<ContextId>, weights: &mut Vec<LocalWeightId>,
    ) -> Result<(), SolveAvailabilityError> {
        pending.try_reserve(1).map_err(|_| exhausted())?;
        pending.push(root);
        while let Some(id) = pending.pop() {
            if visited.contains(&id) { continue; }
            visited.try_reserve(1).map_err(|_| exhausted())?;
            visited.insert(id);
            if id == IDENTITY { continue; }
            let expression = *self.contexts.get(id.0 as usize - 1).ok_or_else(exhausted)?;
            let (children, count, weight) = match expression {
                ContextExpr::PrefixLeft { input, weight } | ContextExpr::SuffixRightPops { input, weight } => ([input, IDENTITY], 1, Some(weight)),
                ContextExpr::Replay { lower, upper } => ([lower, upper], 2, None),
                ContextExpr::Swap { input } | ContextExpr::WithoutLeftFilter { input } => ([input, IDENTITY], 1, None),
                // Fresh-use certificates require an authentic retained owner.
                ContextExpr::BothFromRight { .. } => return Err(exhausted()),
            };
            if children[..count].iter().any(|child| child.0 >= id.0) { return Err(exhausted()); }
            pending.try_reserve(count).map_err(|_| exhausted())?;
            pending.extend_from_slice(&children[..count]);
            if let Some(weight) = weight {
                self.weights.get(weight.0 as usize).ok_or_else(exhausted)?;
                weights.try_reserve(1).map_err(|_| exhausted())?;
                weights.push(weight);
            }
        }
        Ok(())
    }
    pub(super) fn payload_view(&self, weight: LocalWeightId) -> Result<u32, SolveAvailabilityError> {
        Ok(self.weights.get(weight.0 as usize).ok_or_else(exhausted)?.boundary)
    }
    pub(super) fn validate_payload_view(&self, weight: LocalWeightId, id: u32, view: &candidate_effect::View) -> Result<(), SolveAvailabilityError> {
        let payload = self.weights.get(weight.0 as usize).ok_or_else(exhausted)?;
        if payload.boundary != id || payload.owner != view.owner || payload.position != view.position
            || payload.allowed != view.allowed || view.source_weight != Some(weight)
            || view.closed_weight != view.tail.is_none().then_some(weight) { return Err(exhausted()); }
        Ok(())
    }
    // Detached postorder fold: the callback sees the exact construction token
    // and ordered children. No relation, source task, or certificate is consumed.
    #[cfg_attr(not(test), allow(dead_code, reason = "detached contextual evaluation gate"))]
    fn fold_context<T>(
        &self,
        root: ContextId,
        mut evaluate: impl FnMut(ContextId, Option<ContextExpr>, &[&T]) -> Result<T, SolveAvailabilityError>,
    ) -> Result<T, SolveAvailabilityError> {
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| exhausted())?;
        pending.push((root, false));
        let mut results = HashMap::new();
        while let Some((id, ready)) = pending.pop() {
            if results.contains_key(&id) { continue; }
            let expression = if id == IDENTITY { None } else {
                Some(*self.contexts.get(id.0 as usize - 1).ok_or_else(exhausted)?)
            };
            let (children, count) = match expression {
                None => ([IDENTITY, IDENTITY], 0),
                Some(ContextExpr::Replay { lower, upper }) => ([lower, upper], 2),
                Some(ContextExpr::PrefixLeft { input, .. }
                    | ContextExpr::SuffixRightPops { input, .. }
                    | ContextExpr::Swap { input }
                    | ContextExpr::BothFromRight { input, .. }
                    | ContextExpr::WithoutLeftFilter { input }) => ([input, IDENTITY], 1),
            };
            // Construction only references already retained nodes. Validate
            // this invariant before descending, including malformed handles.
            if children[..count].iter().any(|child| child.0 >= id.0) {
                return Err(exhausted());
            }
            if !ready && count > 0 {
                pending.try_reserve(count + 1).map_err(|_| exhausted())?;
                pending.push((id, true));
                for &child in children[..count].iter().rev() {
                    if !results.contains_key(&child) { pending.push((child, false)); }
                }
                continue;
            }
            let result = match count {
                0 => evaluate(id, expression, &[])?,
                1 => evaluate(id, expression, &[&results[&children[0]]])?,
                2 => evaluate(id, expression, &[&results[&children[0]], &results[&children[1]]])?,
                _ => unreachable!(),
            };
            results.try_reserve(1).map_err(|_| exhausted())?;
            results.insert(id, result);
        }
        results.remove(&root).ok_or_else(exhausted)
    }
    #[cfg_attr(not(test), allow(dead_code, reason = "detached algebra has no source consumer"))]
    fn evaluate_context(&self, root: ContextId, weights: &[DetachedWeight]) -> Result<DetachedEvaluation, SolveAvailabilityError> {
        let mut nodes = Vec::new();
        let value = self.fold_context(root, |id, expression, children: &[&DetachedWeight]| {
            let value = match expression {
                None => DetachedWeight::identity(),
                Some(ContextExpr::PrefixLeft { weight, .. }) => {
                    let prefix = weights.get(weight.0 as usize).ok_or_else(exhausted)?;
                    let mut out = DetachedWeight::identity();
                    out.append_left(&prefix.left)?; out.append_left(&children[0].left)?;
                    out.filter = prefix.filter.intersect(&children[0].filter)?;
                    out.append_right(&children[0].right)?; out
                }
                Some(ContextExpr::SuffixRightPops { weight, .. }) => {
                    let suffix = weights.get(weight.0 as usize).ok_or_else(exhausted)?;
                    let mut out = children[0].copy()?;
                    out.right.clear();
                    // Oracle suffix uses only leading POPs of the wrapper.
                    for entry in &suffix.left {
                        out.append_right(&[DetachedRightEntry { id: entry.id, pops: entry.pops.copy()? }])?;
                    }
                    out.append_right(&children[0].right)?; out
                }
                Some(ContextExpr::Swap { .. }) => {
                    let mut out = DetachedWeight::identity(); out.right_to_left(&children[0].right)?;
                    for entry in &children[0].left {
                        out.append_right(&[DetachedRightEntry { id: entry.id, pops: entry.pops.copy()? }])?;
                    }
                    out
                }
                Some(ContextExpr::BothFromRight { .. }) => {
                    let mut out = DetachedWeight::identity(); out.right_to_left(&children[0].right)?;
                    out.append_right(&children[0].right)?; out
                }
                Some(ContextExpr::WithoutLeftFilter { .. }) => {
                    let mut out = children[0].copy()?; out.filter = DetachedFilter::All; out
                }
                Some(ContextExpr::Replay { .. }) => {
                    let mut out = children[0].copy()?; out.append_left(&children[1].left)?;
                    out.filter = children[0].filter.intersect(&children[1].filter)?;
                    out.right.clear(); out.append_right(&children[1].right)?;
                    out.append_right(&children[0].right)?; out.mix()?
                }
            };
            nodes.try_reserve(1).map_err(|_| exhausted())?; nodes.push((id, expression));
            Ok(value)
        })?;
        Ok(DetachedEvaluation { value, nodes })
    }
    pub(super) fn evidence_snapshot(&self, bound: BoundKey, relation: Option<RelationId>) -> EvidenceSnapshot {
        self.evidence.snapshot(bound, relation)
    }
    pub(super) fn import_evidence(&mut self, snapshot: EvidenceSnapshot) -> Result<EvidenceSnapshotId, SolveAvailabilityError> {
        self.evidence.intern_snapshot(snapshot)
    }
    /// Check the already captured/imported snapshot pair. This deliberately
    /// compares the source snapshot retained by the route; it must not sample
    /// the current evidence head, which may include later admissions.
    pub(super) fn captured_snapshot_was_imported(
        &self, captured: EvidenceSnapshot, imported: EvidenceSnapshotId,
    ) -> bool {
        self.evidence.snapshots.get(imported.0).copied() == Some(captured)
    }
    /// Authenticate the concrete FreshUse admission and the emitted physical
    /// fiber that consumed its imported antecedent. No tuple-only lookup can
    /// manufacture this link: the immutable admission names both the captured
    /// bound and mapped relation, and the emission names that admission.
    pub(super) fn fresh_use_fiber_emission(
        &self, antecedent: EvidenceSnapshotId, source_bound: BoundKey,
        use_origin: usize, mapped_relation: RelationId, target_bound: BoundKey,
    ) -> Option<(BoundAdmissionId, RelationId, BoundEmissionId, PhysicalBoundSlot, PhysicalBoundReadback)> {
        let mut found = None;
        let snapshot_coverage = self.evidence.snapshots.get(antecedent.0)?.coverage;
        let mut expected_coverage = snapshot_coverage;
        expected_coverage.add(CoverageGap::ReplayUseAntecedentsNotRetained);
        for (index, admission) in self.evidence.admissions.iter().enumerate() {
            if admission.bound != target_bound || admission.relation != Some(mapped_relation)
                || admission.cause != (BoundAdmissionCause::FreshUse {
                    antecedent, use_origin, source_bound, mapped_relation: Some(mapped_relation),
                }) {
                continue;
            }
            if admission.coverage != expected_coverage { return None; }
            let id = BoundAdmissionId(index);
            let relation = admission.relation?;
            let mut emissions = self.evidence.emissions.iter().enumerate().filter(|(_, emission)|
                emission.admission == id && emission.bound == target_bound);
            let (emission_index, emission) = emissions.next()?;
            if emissions.next().is_some() { return None; }
            if emission.readback.bound != target_bound
                || emission.readback.slot != emission.physical
                || emission.readback.phase != PhysicalReadbackPhase::ConstructorAfterAppend
            { return None; }
            let evidence = (id, relation, BoundEmissionId(emission_index), emission.physical, emission.readback);
            if found.replace(evidence).is_some() { return None; }
        }
        found
    }
    #[cfg(test)]
    pub(super) fn test_emission_record(&self, id: BoundEmissionId) -> Option<(PhysicalBoundSlot, PhysicalBoundReadback)> {
        self.evidence.emissions.get(id.0).map(|emission| (emission.physical, emission.readback))
    }
    #[cfg(test)]
    pub(super) fn test_emission_contents(&self, id: BoundEmissionId) -> Option<(BoundAdmissionId, BoundKey, PhysicalBoundSlot, PhysicalBoundReadback)> {
        self.evidence.emissions.get(id.0).map(|emission|
            (emission.admission, emission.bound, emission.physical, emission.readback))
    }
    #[cfg(test)]
    pub(super) fn test_replace_emission_contents(
        &mut self, id: BoundEmissionId,
        contents: (BoundAdmissionId, BoundKey, PhysicalBoundSlot, PhysicalBoundReadback),
    ) {
        let emission = &mut self.evidence.emissions[id.0];
        emission.admission = contents.0;
        emission.bound = contents.1;
        emission.physical = contents.2;
        emission.readback = contents.3;
    }
    #[cfg(test)]
    pub(super) fn test_replace_emission_slot(&mut self, id: BoundEmissionId, slot: PhysicalBoundSlot) {
        self.evidence.emissions[id.0].physical = slot;
    }
    #[cfg(test)]
    pub(super) fn test_replace_emission_readback(&mut self, id: BoundEmissionId, readback: PhysicalBoundReadback) {
        self.evidence.emissions[id.0].readback = readback;
    }
    #[cfg(test)]
    pub(super) fn test_orphan_emission(&mut self, id: BoundEmissionId) -> BoundAdmissionId {
        let original = self.evidence.emissions[id.0].admission;
        self.evidence.emissions[id.0].admission = BoundAdmissionId(usize::MAX);
        original
    }
    #[cfg(test)]
    pub(super) fn test_restore_emission_admission(&mut self, id: BoundEmissionId, admission: BoundAdmissionId) {
        self.evidence.emissions[id.0].admission = admission;
    }
    #[cfg(test)]
    pub(super) fn test_replace_dependency(&mut self, original: Dependency, replacement: Dependency) {
        let index = self.dependencies.iter().position(|dependency| *dependency == original).expect("actual dependency retained");
        self.dependency_keys.remove(&original);
        self.dependencies[index] = replacement;
        self.dependency_keys.insert(replacement);
    }
    #[cfg(test)]
    pub(super) fn test_replace_relation_scoped(&mut self, id: RelationId, scoped: usize) -> usize {
        let relation = &mut self.relations[id.0 as usize];
        let original = relation.key.scoped;
        relation.key.scoped = ScopedFlowId(scoped);
        original.0
    }
    #[cfg(test)]
    pub(super) fn test_replace_scoped_flow(&mut self, relation: RelationId, flow: ScopedFlow) -> Option<ScopedFlow> {
        let id = self.relations.get(relation.0 as usize)?.key.scoped;
        if id.0 == 0 { return None; }
        let slot = self.scope_flows.get_mut(id.0 - 1)?;
        let original = *slot;
        *slot = flow;
        Some(original)
    }
    #[cfg(test)]
    pub(super) fn test_remove_bound_member(&mut self, key: BoundKey, relation: RelationId)
        -> Option<(usize, Option<usize>, Option<usize>)> {
        let mut previous = None;
        let mut cursor = *self.bounds.get(&key)?;
        loop {
            let (entry_key, entry_relation, next) = *self.bound_keys.get(cursor)?;
            if entry_key == key && entry_relation == relation {
                if let Some(previous) = previous {
                    self.bound_keys[previous].2 = next;
                } else if let Some(next) = next {
                    self.bounds.insert(key, next);
                } else {
                    self.bounds.remove(&key);
                }
                return Some((cursor, previous, next));
            }
            previous = Some(cursor);
            cursor = next?;
        }
    }
    #[cfg(test)]
    pub(super) fn test_restore_bound_member(
        &mut self, key: BoundKey, token: (usize, Option<usize>, Option<usize>),
    ) {
        let (index, previous, next) = token;
        self.bound_keys[index].2 = next;
        if let Some(previous) = previous {
            self.bound_keys[previous].2 = Some(index);
        } else {
            self.bounds.insert(key, index);
        }
    }
    pub(super) fn replay_recipe_is_retained(&self, dependency: Dependency) -> bool {
        self.evidence.recipe_keys.get(&dependency).is_some_and(|id|
            self.evidence.recipes.get(id.0).is_some_and(|recipe| {
                let mut expected = EvidenceCoverage::default();
                expected.add(CoverageGap::ReplayUseAntecedentsNotRetained);
                recipe.dependency == dependency && recipe.coverage == expected
            }))
    }
    pub(super) fn evidence_admit(&mut self, bound: BoundKey, origin: TypedPairKey, relation: Option<RelationId>,
        cause: BoundAdmissionCause, duplicate: bool) -> Result<BoundAdmissionId, SolveAvailabilityError> {
        self.evidence.admit(bound, origin, relation, cause, duplicate)
    }
    pub(super) fn evidence_attempt(&mut self) { self.evidence.counters.attempts += 1; }
    pub(super) fn evidence_admission_sample(&mut self) { self.evidence.counters.admission_samples += 1; }
    pub(super) fn reserve_evidence_emission(&mut self) -> Result<(), SolveAvailabilityError> { self.evidence.reserve_emission() }
    pub(super) fn evidence_emit(&mut self, admission: BoundAdmissionId, slot: PhysicalBoundSlot,
        readback: PhysicalBoundReadback) -> BoundEmissionId {
        self.evidence.counters.emission_samples += 1;
        self.evidence.emit(admission, slot, readback)
    }
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            scope_observations: self.scope_observations.len(),
            lifecycle_generation: self.lifecycle_generation,
            source_support: self.source_support_log.len(),
            source_support_undo: self.source_support_undo.len(),
            evidence: self.evidence.checkpoint(),
            inferred_entries: self.inferred_entries.len(),
            bundles: self.bundles.len(),
            source_bundles: self.source_bundle_log.len(),
            bundle_incidence: self.bundle_incidence_log.len(),
            bundle_transports: self.bundle_transports.as_ref().map(|index| index.log.len()),
            weights: self.weights.len(),
            contexts: self.contexts.len(),
            source_sets: self.source_sets.len(),
            relations: self.relations.len(),
            dependencies: self.dependencies.len(),
            origins: self.origins.len(),
            bounds: self.bound_keys.len(),
            uses: self.uses,
            replay_log: self.replay_log.len(),
            next_replay_operation: self.next_replay_operation,
            replay_operation_undo: self.replay_operation_undo.len(),
            restoration_undo: self.restoration_undo.len(),
            typed_drains: self.typed_drains.len(),
            typed_drain_undo: self.typed_drain_undo.len(),
            edges: self.edge_log.len(),
            processing: self.processing,
            discharges: self.discharge_log.len(),
        }
    }
    pub fn rollback(&mut self, checkpoint: Checkpoint) {
        for observation in self.scope_observations.drain(checkpoint.scope_observations..) { self.scope_observation_keys.remove(&observation); }
        for id in self.source_support_undo.drain(checkpoint.source_support_undo..).rev() {
            self.source_support.get_mut(&id).expect("registered support retained until rollback").valid = true;
        }
        for id in self.source_support_log.drain(checkpoint.source_support..) {
            self.source_support.remove(&id);
        }
        for undo in self.typed_drain_undo.drain(checkpoint.typed_drain_undo..).rev() {
            if undo.index >= checkpoint.typed_drains { continue; }
            if undo.index < self.typed_drains.len() { self.typed_drains[undo.index] = undo.frame; }
            else {
                assert_eq!(undo.index, self.typed_drains.len());
                // Removal never shrinks the stack's already reserved capacity.
                self.typed_drains.push(undo.frame);
            }
        }
        self.typed_drains.truncate(checkpoint.typed_drains);
        for undo in self.restoration_undo.drain(checkpoint.restoration_undo..).rev() {
            let operation = self.restorations.get_mut(&undo.id).expect("restoration retirement waits for route commit");
            operation.next_opposite = undo.next_opposite;
            operation.replay = undo.replay;
            operation.retired = undo.retired;
        }
        for undo in self.replay_operation_undo.drain(checkpoint.replay_operation_undo..).rev() {
            let operation = self.replay_operations.get_mut(&undo.id).expect("retirement waits for route commit");
            operation.waiting_child = undo.waiting_child;
            operation.queued = undo.queued;
            operation.consumed = undo.consumed;
            operation.retired = undo.retired;
        }
        for index in checkpoint.next_replay_operation..self.next_replay_operation {
            #[cfg(test)]
            { self.operation_frontier_visits += 1; }
            let id = ReplayOperationId(index);
            self.remove_replay_operation(id);
            self.restorations.remove(&id);
        }
        self.next_replay_operation = checkpoint.next_replay_operation;
        self.evidence.rollback(checkpoint.evidence);
        self.inferred_entries.truncate(checkpoint.inferred_entries);
        for bundle in self.bundles.drain(checkpoint.bundles..) {
            self.bundle_bytes -= bundle.sets.capacity() * std::mem::size_of::<EmptyAttachmentSet>();
        }
        for origin in self.source_bundle_log.drain(checkpoint.source_bundles..) { self.source_bundles.remove(&origin); }
        for incidence in self.bundle_incidence_log.drain(checkpoint.bundle_incidence..).rev() {
            self.bundle_incidence.remove(&(incidence.relation, incidence.bundle));
            if let Some(previous) = incidence.previous_on_relation { self.bundle_incidence_heads.insert(incidence.relation, previous); }
            else { self.bundle_incidence_heads.remove(&incidence.relation); }
        }
        if let Some(length) = checkpoint.bundle_transports { self.bundle_transports.as_mut().unwrap().rollback(length); }
        else { self.bundle_transports = None; }
        for weight in self.weights.drain(checkpoint.weights..) {
            self.weight_bytes -= weight.allowed.capacity() * std::mem::size_of::<SourceEffectId>()
                + weight.attachment.as_ref().map_or(0, |set| set.member_ordinals.capacity() * std::mem::size_of::<usize>());
        }
        for (key, previous) in self.replay_log.drain(checkpoint.replay_log..).rev() {
            if let Some(previous) = previous { self.replay_heads.insert(key, previous); }
            else { self.replay_heads.remove(&key); }
        }
        for relation in self.discharge_log.drain(checkpoint.discharges..) {
            self.discharged.remove(&relation);
            self.discharge_residuals.remove(&relation);
        }
        for context in self.contexts.drain(checkpoint.contexts..) {
            self.context_keys.remove(&context);
        }
        for sources in self.source_sets.drain(checkpoint.source_sets..) {
            let key = self.source_set_keys.remove_entry(&sources).expect("interned sources").0;
            self.source_set_bytes -= (sources.capacity() + key.capacity()) * std::mem::size_of::<usize>();
        }
        for relation in self.relations.drain(checkpoint.relations..).rev() {
            self.keys.remove(&relation.key);
            if let Some(previous) = relation.previous_on_pair {
                self.pair_heads.insert(relation.key.pair, previous);
            } else {
                self.pair_heads.remove(&relation.key.pair);
            }
        }
        for dependency in self.dependencies.drain(checkpoint.dependencies..) {
            self.dependency_keys.remove(&dependency);
        }
        self.lifecycle_generation = checkpoint.lifecycle_generation;
        for (bound, _, previous) in self.bound_keys.drain(checkpoint.bounds..).rev() {
            if let Some(previous) = previous { self.bounds.insert(bound, previous); }
            else { self.bounds.remove(&bound); }
        }
        self.origins.truncate(checkpoint.origins);
        self.uses = checkpoint.uses;
        self.processing = checkpoint.processing;
        for (parent, child) in self.edge_log.drain(checkpoint.edges..).rev() {
            self.edge_keys.remove(&(parent, child));
            let entries = self.edges.get_mut(&parent).unwrap();
            assert_eq!(entries.pop(), Some(child));
            if entries.is_empty() {
                self.edge_bytes -= self.edges.remove(&parent).unwrap().capacity()
                    * std::mem::size_of::<RelationId>();
            }
        }
    }
    fn remove_replay_operation(&mut self, id: ReplayOperationId) {
        if let Some(operation) = self.replay_operations.remove(&id) {
            self.replay_child_bytes -= operation.children.capacity() * std::mem::size_of::<RelationId>();
        }
    }
    fn retire_replay_candidate(&mut self, id: ReplayOperationId) {
        #[cfg(test)]
        { self.operation_frontier_visits += 1; }
        let reclaim = self.replay_operations.get(&id).is_some_and(|operation| operation.retired
            && operation.waiting_child == ReplayChildWait::Idle
            && !operation.restoration.is_some_and(|parent| self.restorations.get(&parent)
                .is_some_and(|restoration| !restoration.retired && restoration.replay == Some(id))));
        if reclaim { self.remove_replay_operation(id); }
    }
    fn retire_restoration_candidate(&mut self, id: ReplayOperationId) {
        #[cfg(test)]
        { self.operation_frontier_visits += 1; }
        if self.restorations.get(&id).is_some_and(|operation| operation.retired) { self.restorations.remove(&id); }
    }
    pub(super) fn commit_replay_operations(&mut self, checkpoint: Checkpoint) {
        self.source_support_undo.truncate(checkpoint.source_support_undo);
        self.typed_drain_undo.truncate(checkpoint.typed_drain_undo);
        for frame in &mut self.typed_drains {
            // A committed continuation must preflight its remaining children
            // against the next route's journal before terminal consumption.
            frame.prepared_acks = frame.completed_acks;
            frame.terminal_prepared = false;
        }
        // Candidate visits depend on this route's creations and mutations,
        // never on historical map capacity. Repeated IDs need no dedup storage.
        for index in checkpoint.next_replay_operation..self.next_replay_operation {
            let id = ReplayOperationId(index);
            self.retire_replay_candidate(id);
            if let Some(replay) = self.restorations.get(&id).and_then(|operation| operation.replay) {
                self.retire_replay_candidate(replay);
            }
        }
        for index in checkpoint.replay_operation_undo..self.replay_operation_undo.len() {
            self.retire_replay_candidate(self.replay_operation_undo[index].id);
        }
        for index in checkpoint.restoration_undo..self.restoration_undo.len() {
            let undo = self.restoration_undo[index];
            // A previous route can have retained a completed replay through
            // this pointer. Advancing the restoration releases that ownership.
            if let Some(replay) = undo.replay { self.retire_replay_candidate(replay); }
            if let Some(replay) = self.restorations.get(&undo.id).and_then(|operation| operation.replay) {
                self.retire_replay_candidate(replay);
            }
        }
        // Replays read their owner's final state before owners are reclaimed.
        for index in checkpoint.next_replay_operation..self.next_replay_operation {
            self.retire_restoration_candidate(ReplayOperationId(index));
        }
        for index in checkpoint.restoration_undo..self.restoration_undo.len() {
            self.retire_restoration_candidate(self.restoration_undo[index].id);
        }
        self.replay_operation_undo.truncate(checkpoint.replay_operation_undo);
        self.restoration_undo.truncate(checkpoint.restoration_undo);
    }
    pub(super) fn begin_typed_drain(&mut self, initial: LiveConstraintTask,
        occurrence: &ConstraintOccurrenceId, cause: &CauseId,
        previous_processing: Option<TypedPairKey>, previous_relation: Option<RelationId>,
    ) -> Result<usize, SolveAvailabilityError> {
        self.typed_drains.try_reserve(1).map_err(|_| exhausted())?;
        let index = self.typed_drains.len();
        self.typed_drains.push(TypedDrainFrame { initial, occurrence: occurrence.clone(), cause: cause.clone(),
            previous_processing, previous_relation, current: None, stage: TypedDrainStage::Transport,
            context_consumed: None, transitions: 0, replay_acks: Vec::new(), completed_acks: 0, prepared_acks: 0, terminal_prepared: false, function: None, replay_destination: None });
        Ok(index)
    }
    // Keep the original allocation owned by undo, so rollback restores the
    // exact frame and acknowledgement capacity even after terminal removal.
    pub(super) fn prepare_typed_drain_update(&mut self, index: usize, transactional: bool) -> Result<(), SolveAvailabilityError> {
        if !transactional || self.typed_drain_undo.iter().any(|undo| undo.index == index) { return Ok(()); }
        self.typed_drain_undo.try_reserve(1).map_err(|_| exhausted())?;
        let frame = self.typed_drains.get(index).ok_or_else(exhausted)?;
        let mut replay_acks = Vec::new();
        replay_acks.try_reserve_exact(frame.replay_acks.capacity()).map_err(|_| exhausted())?;
        replay_acks.extend_from_slice(&frame.replay_acks);
        let replacement = TypedDrainFrame { initial: frame.initial, occurrence: frame.occurrence.clone(), cause: frame.cause.clone(),
            previous_processing: frame.previous_processing, previous_relation: frame.previous_relation,
            current: frame.current, stage: frame.stage, context_consumed: frame.context_consumed,
            transitions: frame.transitions, replay_acks, completed_acks: frame.completed_acks,
            prepared_acks: frame.prepared_acks, terminal_prepared: frame.terminal_prepared, function: frame.function.clone(), replay_destination: frame.replay_destination };
        let frame = std::mem::replace(&mut self.typed_drains[index], replacement);
        self.typed_drain_undo.push(TypedDrainUndo { index, frame });
        Ok(())
    }
    pub(super) fn replay_operation_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        let mut bytes = self.replay_operations.capacity().checked_mul(std::mem::size_of::<(ReplayOperationId, ReplayOperation)>())
            .and_then(|bytes| self.replay_operation_undo.capacity().checked_mul(std::mem::size_of::<ReplayOperationUndo>())
                .and_then(|undo| bytes.checked_add(undo))).ok_or_else(exhausted)?;
        bytes = bytes.checked_add(self.replay_child_bytes).ok_or_else(exhausted)?;
        bytes = bytes.checked_add(self.typed_drains.capacity().checked_mul(std::mem::size_of::<TypedDrainFrame>()).ok_or_else(exhausted)?)
            .ok_or_else(exhausted)?;
        bytes = bytes.checked_add(self.typed_drain_undo.capacity().checked_mul(std::mem::size_of::<TypedDrainUndo>()).ok_or_else(exhausted)?).ok_or_else(exhausted)?;
        for frame in self.typed_drains.iter().chain(self.typed_drain_undo.iter().map(|undo| &undo.frame)) {
            bytes = bytes.checked_add(frame.replay_acks.capacity().checked_mul(std::mem::size_of::<ReplayChildAck>()).ok_or_else(exhausted)?)
                .ok_or_else(exhausted)?;
        }
        bytes = bytes.checked_add(self.restorations.capacity().checked_mul(std::mem::size_of::<(ReplayOperationId, BoundRestoration)>()).ok_or_else(exhausted)?)
            .and_then(|bytes| self.restoration_undo.capacity().checked_mul(std::mem::size_of::<BoundRestorationUndo>()).and_then(|undo| bytes.checked_add(undo)))
            .ok_or_else(exhausted)?;
        Ok(bytes)
    }
    pub(super) fn reserve_restoration(&mut self) -> Result<(), SolveAvailabilityError> {
        self.next_replay_operation.checked_add(1).ok_or_else(exhausted)?;
        self.restorations.try_reserve(1).map_err(|_| exhausted())
    }
    pub(super) fn retain_restoration(&mut self, owner: ExtrusionEndpoint, polarity: Polarity, bound: ExtrusionEndpoint,
        emission: BoundEmissionId, opposite_count: usize, occurrence: ConstraintOccurrenceId, cause: CauseId,
    ) -> ReplayOperationId {
        let id = ReplayOperationId(self.next_replay_operation);
        self.next_replay_operation += 1;
        self.restorations.insert(id, BoundRestoration { owner, polarity, bound, emission, opposite_count,
            next_opposite: 0, replay: None, occurrence, cause, retired: false });
        id
    }
    pub(super) fn restoration(&self, id: ReplayOperationId) -> Result<&BoundRestoration, SolveAvailabilityError> {
        self.restorations.get(&id).ok_or_else(exhausted)
    }
    pub(super) fn validate_restoration_replay(&self, restoration: ReplayOperationId, replay: ReplayOperationId) -> Result<(), SolveAvailabilityError> {
        if self.restoration(restoration)?.replay != Some(replay)
            || self.replay_operations.get(&replay).ok_or_else(exhausted)?.restoration != Some(restoration) {
            return Err(exhausted());
        }
        Ok(())
    }
    pub(super) fn prepare_restoration_update(&mut self, id: ReplayOperationId, transactional: bool) -> Result<bool, SolveAvailabilityError> {
        let operation = self.restorations.get(&id).ok_or_else(exhausted)?;
        let before = self.restoration_undo.capacity();
        if transactional {
            self.restoration_undo.try_reserve(1).map_err(|_| exhausted())?;
            self.restoration_undo.push(BoundRestorationUndo { id, next_opposite: operation.next_opposite,
                replay: operation.replay, retired: operation.retired });
        }
        Ok(self.restoration_undo.capacity() != before)
    }
    pub(super) fn set_restoration_replay(&mut self, id: ReplayOperationId, replay: ReplayOperationId) {
        self.replay_operations.get_mut(&replay).expect("new retained replay operation").restoration = Some(id);
        self.restorations.get_mut(&id).expect("prepared restoration update").replay = Some(replay);
    }
    pub(super) fn advance_restoration(&mut self, id: ReplayOperationId, transactional: bool) {
        let operation = self.restorations.get_mut(&id).expect("prepared restoration update");
        let replay = operation.replay.take();
        operation.next_opposite += 1;
        if !transactional {
            if let Some(replay) = replay { self.retire_replay_candidate(replay); }
        }
    }
    pub(super) fn retire_restoration(&mut self, id: ReplayOperationId, transactional: bool) {
        self.restorations.get_mut(&id).expect("prepared restoration retirement").retired = true;
        if !transactional { self.restorations.remove(&id); }
    }
    #[cfg(test)]
    pub(super) fn replay_operation_next(&self, id: ReplayOperationId) -> Result<Option<TypedWorkItem>, SolveAvailabilityError> {
        let operation = self.replay_operations.get(&id).ok_or_else(exhausted)?;
        if operation.retired { return Ok(None); }
        Ok(operation.children.get(operation.consumed).copied().map(|relation|
            TypedWorkItem { task: operation.task, relation: Some(relation), replay_ack: Some(ReplayChildAck { operation: id, index: operation.consumed }) }))
    }
    fn replay_operation_queue_next(&self, id: ReplayOperationId) -> Result<Option<TypedWorkItem>, SolveAvailabilityError> {
        let operation = self.replay_operations.get(&id).ok_or_else(exhausted)?;
        if operation.retired { return Ok(None); }
        Ok(operation.children.get(operation.queued).copied().map(|relation|
            TypedWorkItem { task: operation.task, relation: Some(relation), replay_ack: Some(ReplayChildAck { operation: id, index: operation.queued }) }))
    }
    // Reserve the acknowledgement before running a child with side effects.
    fn prepare_replay_ack(&mut self, id: ReplayOperationId, transactional: bool) -> Result<(), SolveAvailabilityError> {
        let operation = self.replay_operations.get(&id).ok_or_else(exhausted)?;
        if transactional {
            self.replay_operation_undo.try_reserve(1).map_err(|_| exhausted())?;
            self.replay_operation_undo.push(ReplayOperationUndo { id, waiting_child: operation.waiting_child, queued: operation.queued, consumed: operation.consumed, retired: operation.retired });
        }
        Ok(())
    }
    pub(super) fn transfer_replay_child(&mut self, ack: ReplayChildAck, transactional: bool) -> Result<(), SolveAvailabilityError> {
        let operation = self.replay_operations.get(&ack.operation).ok_or_else(exhausted)?;
        if operation.waiting_child != ReplayChildWait::Idle || operation.retired || ack.index >= operation.children.len() || ack.index < operation.consumed || ack.index > operation.queued {
            return Err(exhausted());
        }
        if ack.index == operation.queued {
            self.prepare_replay_ack(ack.operation, transactional)?;
            self.replay_operations.get_mut(&ack.operation).unwrap().queued += 1;
        }
        // An already queued item can enter a synchronous drain as its initial
        // item without recording a second transfer.
        Ok(())
    }
    fn acknowledge_replay(&mut self, id: ReplayOperationId, transactional: bool) {
        let operation = self.replay_operations.get_mut(&id).expect("prepared replay acknowledgement");
        if operation.consumed < operation.children.len() { operation.consumed += 1; }
        if operation.consumed == operation.children.len() {
            operation.retired = true;
            if !transactional { self.retire_replay_candidate(id); }
        }
    }
    pub(super) fn prepare_replay_child_completion(&mut self, ack: ReplayChildAck, transactional: bool) -> Result<(), SolveAvailabilityError> {
        let operation = self.replay_operations.get(&ack.operation).ok_or_else(exhausted)?;
        if ack.index >= operation.queued || ack.index < operation.consumed { return Err(exhausted()); }
        if let ReplayChildWait::Running { ack: expected, .. } = operation.waiting_child {
            if expected != ack || operation.queued != ack.index.checked_add(1).ok_or_else(exhausted)? { return Err(exhausted()); }
        } else if operation.waiting_child != ReplayChildWait::Idle { return Err(exhausted()); }
        #[cfg(test)]
        let counted_failure = if transactional {
            match self.fail_replay_completion_after {
                Some(0) => { self.fail_replay_completion_after = None; true }
                Some(remaining) => { self.fail_replay_completion_after = Some(remaining - 1); false }
                None => false,
            }
        } else { false };
        #[cfg(test)]
        if transactional && (std::mem::take(&mut self.fail_replay_completion_undo_reserve) || counted_failure) {
            let ack_bytes = self.typed_drains.last().unwrap().replay_acks.capacity()
                * std::mem::size_of::<ReplayChildAck>();
            self.failed_replay_completion_bytes = Some((self.bytes()?, ack_bytes));
            return Err(exhausted());
        }
        self.prepare_replay_ack(ack.operation, transactional)
    }
    pub(super) fn terminal_storage(&self) -> (usize, usize, usize) {
        (self.typed_drain_undo.capacity(), self.replay_operation_undo.capacity(), self.typed_drain_undo.len())
    }
    pub(super) fn prepare_replay_return(&mut self, ack: ReplayChildAck, index: usize, transactional: bool) -> Result<(), SolveAvailabilityError> {
        let operation = self.replay_operations.get(&ack.operation).ok_or_else(exhausted)?;
        let next = ack.index.checked_add(1).ok_or_else(exhausted)?;
        if operation.waiting_child != (ReplayChildWait::Running { ack, drain_index: index })
            || operation.consumed != next || operation.queued != next {
            return Err(exhausted());
        }
        self.prepare_replay_ack(ack.operation, transactional)
    }
    pub(super) fn retain_replay_return(&mut self, ack: ReplayChildAck, index: usize, completion: DrainCompletion) {
        self.replay_operations.get_mut(&ack.operation).expect("prepared exact replay return").waiting_child =
            ReplayChildWait::Ready { ack, drain_index: index, completion };
    }
    pub(super) fn complete_replay_child(&mut self, ack: ReplayChildAck, transactional: bool) -> Result<(), SolveAvailabilityError> {
        let operation = self.replay_operations.get(&ack.operation).ok_or_else(exhausted)?;
        if operation.consumed != ack.index { return Err(exhausted()); }
        if let ReplayChildWait::Running { ack: expected, .. } = operation.waiting_child {
            if expected != ack || operation.queued != ack.index.checked_add(1).ok_or_else(exhausted)? { return Err(exhausted()); }
        } else if operation.waiting_child != ReplayChildWait::Idle { return Err(exhausted()); }
        self.acknowledge_replay(ack.operation, transactional);
        Ok(())
    }
    pub fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        let parts = [
            Some(std::mem::size_of::<u64>() + std::mem::size_of::<usize>()),
            self.source_support.capacity().checked_mul(std::mem::size_of::<(SourceSupportId, SourceSupportRegistration)>()),
            self.source_support_log.capacity().checked_mul(std::mem::size_of::<SourceSupportId>()),
            Some(self.scope_inventory.bytes()?),
            self.scope_transformers.capacity().checked_mul(std::mem::size_of::<(candidate_scope::ScopeTransformer, Option<usize>, usize)>()),
            self.scope_heads.capacity().checked_mul(std::mem::size_of::<(u64, usize)>()),
            Some(self.scope_transformer_heap),
            self.scope_flows.capacity().checked_mul(std::mem::size_of::<ScopedFlow>()),
            self.scope_flow_keys.capacity().checked_mul(std::mem::size_of::<(ScopedFlow, ScopedFlowId)>()),
            self.scope_observations.capacity().checked_mul(std::mem::size_of::<ScopedObservation>()),
            self.scope_observation_keys.capacity().checked_mul(std::mem::size_of::<ScopedObservation>()),
            self.source_support_undo.capacity().checked_mul(std::mem::size_of::<SourceSupportId>()),
            Some(self.source_support.values().try_fold(0usize, |bytes, registration| {
                bytes.checked_add(registration.watched.capacity().checked_mul(std::mem::size_of::<RelationId>()).ok_or_else(exhausted)?).ok_or_else(exhausted)
            })?),
            Some(self.replay_operation_bytes()?),
            Some(self.evidence.bytes()?),
            self.inferred_entries.capacity().checked_mul(std::mem::size_of::<InferredEntryOrigin>()),
            Some(self.bundle_bytes),
            self.bundles.capacity().checked_mul(std::mem::size_of::<AttachmentBundle>()),
            self.source_bundles.capacity().checked_mul(std::mem::size_of::<(ConstraintOccurrenceId, AttachmentBundleId)>()),
            self.source_bundle_log.capacity().checked_mul(std::mem::size_of::<ConstraintOccurrenceId>()),
            self.bundle_incidence.capacity().checked_mul(std::mem::size_of::<(RelationId, AttachmentBundleId)>()),
            self.bundle_incidence_log.capacity().checked_mul(std::mem::size_of::<BundleIncidence>()),
            self.bundle_incidence_heads.capacity().checked_mul(std::mem::size_of::<(RelationId, usize)>()),
            Some(self.bundle_transports.as_ref().map_or(Ok(0), BundleTransports::bytes)?),
            Some(self.weight_bytes),
            self.weights.capacity().checked_mul(std::mem::size_of::<LocalWeight>()),
            self.replay_heads.capacity().checked_mul(std::mem::size_of::<((BoundKey, BoundKey), (Option<usize>, Option<usize>))>()),
            self.replay_log.capacity().checked_mul(std::mem::size_of::<((BoundKey, BoundKey), Option<(Option<usize>, Option<usize>)>)>()),
            self.discharged.capacity().checked_mul(std::mem::size_of::<RelationId>()),
            self.discharge_residuals.capacity().checked_mul(std::mem::size_of::<(RelationId, ContextId)>()),
            self.discharge_log.capacity().checked_mul(std::mem::size_of::<RelationId>()),
            self.contexts
                .capacity()
                .checked_mul(std::mem::size_of::<ContextExpr>()),
            self.context_keys
                .capacity()
                .checked_mul(std::mem::size_of::<(ContextExpr, ContextId)>()),
            self.source_sets.capacity().checked_mul(std::mem::size_of::<Vec<usize>>()),
            self.source_set_keys.capacity().checked_mul(std::mem::size_of::<(Vec<usize>, usize)>()),
            Some(self.source_set_bytes),
            self.relations
                .capacity()
                .checked_mul(std::mem::size_of::<Relation>()),
            self.keys
                .capacity()
                .checked_mul(std::mem::size_of::<(RelationKey, RelationId)>()),
            self.pair_heads
                .capacity()
                .checked_mul(std::mem::size_of::<(TypedPairKey, RelationId)>()),
            self.dependencies
                .capacity()
                .checked_mul(std::mem::size_of::<Dependency>()),
            self.dependency_keys
                .capacity()
                .checked_mul(std::mem::size_of::<Dependency>()),
            self.origins
                .capacity()
                .checked_mul(std::mem::size_of::<Origin>()),
            self.bounds
                .capacity()
                .checked_mul(std::mem::size_of::<(BoundKey, usize)>()),
            self.bound_keys
                .capacity()
                .checked_mul(std::mem::size_of::<(BoundKey, RelationId, Option<usize>)>()),
        ];
        let owned = parts.into_iter().try_fold(0usize, |n, part| {
            n.checked_add(part.ok_or_else(exhausted)?)
                .ok_or_else(exhausted)
        })?;
        owned
            .checked_add(
                self.edges
                    .capacity()
                    .checked_mul(std::mem::size_of::<(RelationId, Vec<RelationId>)>())
                    .ok_or_else(exhausted)?,
            )
            .and_then(|n| {
                n.checked_add(
                    self.edge_keys
                        .capacity()
                        .checked_mul(std::mem::size_of::<(RelationId, RelationId)>())?,
                )
            })
            .and_then(|n| {
                n.checked_add(
                    self.edge_log
                        .capacity()
                        .checked_mul(std::mem::size_of::<(RelationId, RelationId)>())?,
                )
            })
            .and_then(|n| n.checked_add(self.edge_bytes))
            .ok_or_else(exhausted)
    }
    #[cfg(test)]
    pub fn enumerated_bytes(&self) -> usize {
        let scoped_bytes = self.scope_inventory.enumerated_bytes().expect("accounted source inventory")
            + self.scope_transformers.capacity() * std::mem::size_of::<(candidate_scope::ScopeTransformer, Option<usize>, usize)>()
            + self.scope_heads.capacity() * std::mem::size_of::<(u64, usize)>()
            + self.scope_transformers.iter().map(|(t, _, _)| t.checked_retained_bytes().expect("accounted transformer")).sum::<usize>()
            + self.scope_flows.capacity() * std::mem::size_of::<ScopedFlow>()
            + self.scope_flow_keys.capacity() * std::mem::size_of::<(ScopedFlow, ScopedFlowId)>()
            + self.scope_observations.capacity() * std::mem::size_of::<ScopedObservation>()
            + self.scope_observation_keys.capacity() * std::mem::size_of::<ScopedObservation>();
        let replay_children = self.replay_operations.values().map(|operation|
            operation.children.capacity() * std::mem::size_of::<RelationId>()).sum::<usize>();
        assert_eq!(self.replay_child_bytes, replay_children);
        let adjacency_bytes = self
            .edges
            .values()
            .map(|entries| entries.capacity() * std::mem::size_of::<RelationId>())
            .sum::<usize>();
        assert_eq!(self.edge_bytes, adjacency_bytes);
        scoped_bytes + std::mem::size_of::<u64>() + std::mem::size_of::<usize>()
            + self.source_support.capacity() * std::mem::size_of::<(SourceSupportId, SourceSupportRegistration)>()
            + self.source_support_log.capacity() * std::mem::size_of::<SourceSupportId>()
            + self.source_support_undo.capacity() * std::mem::size_of::<SourceSupportId>()
            + self.source_support.values().map(|registration| registration.watched.capacity() * std::mem::size_of::<RelationId>()).sum::<usize>()
            + self.evidence.enumerated_bytes()
            + self.replay_operations.capacity() * std::mem::size_of::<(ReplayOperationId, ReplayOperation)>()
            + self.replay_operation_undo.capacity() * std::mem::size_of::<ReplayOperationUndo>()
            + self.restorations.capacity() * std::mem::size_of::<(ReplayOperationId, BoundRestoration)>()
            + self.restoration_undo.capacity() * std::mem::size_of::<BoundRestorationUndo>()
            + replay_children
            + self.typed_drains.capacity() * std::mem::size_of::<TypedDrainFrame>()
            + self.typed_drain_undo.capacity() * std::mem::size_of::<TypedDrainUndo>()
            + self.typed_drains.iter().chain(self.typed_drain_undo.iter().map(|undo| &undo.frame))
                .map(|frame| frame.replay_acks.capacity() * std::mem::size_of::<ReplayChildAck>()).sum::<usize>()
            + self.inferred_entries.capacity() * std::mem::size_of::<InferredEntryOrigin>()
            + self.bundles.capacity() * std::mem::size_of::<AttachmentBundle>()
            + self.bundles.iter().map(|bundle| bundle.sets.capacity() * std::mem::size_of::<EmptyAttachmentSet>()).sum::<usize>()
            + self.source_bundles.capacity() * std::mem::size_of::<(ConstraintOccurrenceId, AttachmentBundleId)>()
            + self.source_bundle_log.capacity() * std::mem::size_of::<ConstraintOccurrenceId>()
            + self.bundle_incidence.capacity() * std::mem::size_of::<(RelationId, AttachmentBundleId)>()
            + self.bundle_incidence_log.capacity() * std::mem::size_of::<BundleIncidence>()
            + self.bundle_incidence_heads.capacity() * std::mem::size_of::<(RelationId, usize)>()
            + self.bundle_transports.as_ref().map_or(0, |index| index.heads.capacity() * std::mem::size_of::<(RelationId, usize)>()
                + index.log.capacity() * std::mem::size_of::<(RelationId, RelationId, Option<usize>)>())
            + self.weights.capacity() * std::mem::size_of::<LocalWeight>()
            + self.weights.iter().map(|w| w.allowed.capacity() * std::mem::size_of::<SourceEffectId>()
                + w.attachment.as_ref().map_or(0, |set| set.member_ordinals.capacity() * std::mem::size_of::<usize>())).sum::<usize>()
            + self.replay_heads.capacity() * std::mem::size_of::<((BoundKey, BoundKey), (Option<usize>, Option<usize>))>()
            + self.replay_log.capacity() * std::mem::size_of::<((BoundKey, BoundKey), Option<(Option<usize>, Option<usize>)>)>()
            + self.discharged.capacity() * std::mem::size_of::<RelationId>()
            + self.discharge_residuals.capacity() * std::mem::size_of::<(RelationId, ContextId)>()
            + self.discharge_log.capacity() * std::mem::size_of::<RelationId>()
            + self.contexts.capacity() * std::mem::size_of::<ContextExpr>()
            + self.context_keys.capacity() * std::mem::size_of::<(ContextExpr, ContextId)>()
            + self.source_sets.capacity() * std::mem::size_of::<Vec<usize>>()
            + self.source_set_keys.capacity() * std::mem::size_of::<(Vec<usize>, usize)>()
            + self.source_sets.iter().map(|set| set.capacity() * std::mem::size_of::<usize>()).sum::<usize>()
            + self.source_set_keys.keys().map(|set| set.capacity() * std::mem::size_of::<usize>()).sum::<usize>()
            + self.relations.capacity() * std::mem::size_of::<Relation>()
            + self.keys.capacity() * std::mem::size_of::<(RelationKey, RelationId)>()
            + self.pair_heads.capacity() * std::mem::size_of::<(TypedPairKey, RelationId)>()
            + self.dependencies.capacity() * std::mem::size_of::<Dependency>()
            + self.dependency_keys.capacity() * std::mem::size_of::<Dependency>()
            + self.origins.capacity() * std::mem::size_of::<Origin>()
            + self.bounds.capacity() * std::mem::size_of::<(BoundKey, usize)>()
            + self.bound_keys.capacity() * std::mem::size_of::<(BoundKey, RelationId, Option<usize>)>()
            + self.edges.capacity() * std::mem::size_of::<(RelationId, Vec<RelationId>)>()
            + self.edge_keys.capacity() * std::mem::size_of::<(RelationId, RelationId)>()
            + self.edge_log.capacity() * std::mem::size_of::<(RelationId, RelationId)>()
            + adjacency_bytes
    }
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "context propagation is a later gate")
    )]
    fn context(&mut self, expression: ContextExpr) -> Result<ContextId, SolveAvailabilityError> {
        match expression {
            ContextExpr::PrefixLeft { input, .. }
            | ContextExpr::SuffixRightPops { input, .. }
            | ContextExpr::Swap { input }
            | ContextExpr::BothFromRight { input, .. }
            | ContextExpr::WithoutLeftFilter { input } => self.assert_context(input),
            ContextExpr::Replay { lower, upper } => {
                self.assert_context(lower);
                self.assert_context(upper);
            }
        }
        if let Some(&id) = self.context_keys.get(&expression) {
            return Ok(id);
        }
        let id = ContextId(
            u32::try_from(self.contexts.len())
                .map_err(|_| exhausted())?
                .checked_add(1)
                .ok_or_else(exhausted)?,
        );
        self.contexts.try_reserve(1).map_err(|_| exhausted())?;
        self.context_keys.try_reserve(1).map_err(|_| exhausted())?;
        self.contexts.push(expression);
        self.context_keys.insert(expression, id);
        Ok(id)
    }
    pub fn retain_bundle(&mut self, bundle: AttachmentBundle, source: bool) -> Result<AttachmentBundleId, SolveAvailabilityError> {
        let identity = AttachmentBundleId(self.bundles.len());
        let bytes = bundle.sets.capacity().checked_mul(std::mem::size_of::<EmptyAttachmentSet>()).ok_or_else(exhausted)?;
        let total = self.bundle_bytes.checked_add(bytes).ok_or_else(exhausted)?;
        self.bundles.try_reserve(1).map_err(|_| exhausted())?;
        if source {
            assert!(!self.source_bundles.contains_key(&bundle.occurrence));
            self.source_bundles.try_reserve(1).map_err(|_| exhausted())?;
            self.source_bundle_log.try_reserve(1).map_err(|_| exhausted())?;
            self.source_bundles.insert(bundle.occurrence.clone(), identity);
            self.source_bundle_log.push(bundle.occurrence.clone());
        }
        self.bundles.push(bundle);
        self.bundle_bytes = total;
        Ok(identity)
    }
    pub fn relation_bundles(&self, relation: RelationId) -> impl Iterator<Item = AttachmentBundleId> + '_ {
        std::iter::successors(self.bundle_incidence_heads.get(&relation).copied(), |&index| {
            self.bundle_incidence_log[index].previous_on_relation
        }).map(|index| self.bundle_incidence_log[index].bundle)
    }
    fn activate_bundle_transports(&mut self) -> Result<(), SolveAvailabilityError> {
        if self.bundle_transports.is_some() { return Ok(()); }
        // This one scan is paid only by sessions using bundle provenance.
        let mut index = BundleTransports::default();
        for dependency in &self.dependencies {
            if let Dependency::Transport { parent, child, witness: Some(TransportWitness { reason: TransportReason::Extrusion { .. } | TransportReason::ParentCopy { .. } | TransportReason::EqualityCanonicalization, .. }), .. } = *dependency { index.insert(parent, child)?; }
        }
        self.bundle_transports = Some(index);
        Ok(())
    }
    fn bundle_incidence_insert(&mut self, relation: RelationId, bundle: AttachmentBundleId) -> Result<(), SolveAvailabilityError> {
        if self.bundle_incidence.contains(&(relation, bundle)) { return Ok(()); }
        self.bundle_incidence.try_reserve(1).map_err(|_| exhausted())?;
        self.bundle_incidence_log.try_reserve(1).map_err(|_| exhausted())?;
        self.bundle_incidence_heads.try_reserve(1).map_err(|_| exhausted())?;
        let previous_on_relation = self.bundle_incidence_heads.insert(relation, self.bundle_incidence_log.len());
        self.bundle_incidence.insert((relation, bundle));
        self.bundle_incidence_log.push(BundleIncidence { relation, bundle, previous_on_relation });
        Ok(())
    }
    fn bundle_link(&mut self, relation: RelationId, bundle: AttachmentBundleId) -> Result<(), SolveAvailabilityError> {
        if self.bundle_incidence.contains(&(relation, bundle)) { return Ok(()); }
        self.activate_bundle_transports()?;
        let mut cursor = self.bundle_incidence_log.len();
        self.bundle_incidence_insert(relation, bundle)?;
        // The append log is an iterative queue. Each new incidence visits only
        // diagnostic successors and the sparse zero-use transport chain.
        while cursor < self.bundle_incidence_log.len() {
            let BundleIncidence { relation: parent, bundle, .. } = self.bundle_incidence_log[cursor];
            cursor += 1;
            let count = self.edges.get(&parent).map_or(0, Vec::len);
            for index in 0..count {
                let child = self.edges[&parent][index];
                #[cfg(test)] { self.bundle_visits += 1; }
                self.bundle_incidence_insert(child, bundle)?;
            }
            let mut next = self.bundle_transports.as_ref().unwrap().heads.get(&parent).copied();
            while let Some(index) = next {
                let (_, child, previous) = self.bundle_transports.as_ref().unwrap().log[index];
                next = previous;
                #[cfg(test)] { self.bundle_visits += 1; }
                self.bundle_incidence_insert(child, bundle)?;
            }
        }
        Ok(())
    }
    fn bundle_edge(&mut self, parent: RelationId, child: RelationId) -> Result<(), SolveAvailabilityError> {
        let mut next = self.bundle_incidence_heads.get(&parent).copied();
        while let Some(index) = next {
            let incidence = self.bundle_incidence_log[index];
            next = incidence.previous_on_relation;
            #[cfg(test)] { self.bundle_visits += 1; }
            self.bundle_link(child, incidence.bundle)?;
        }
        Ok(())
    }
    pub fn source_weight(&mut self, boundary: u32, owner: &SourceRootId, position: &SourceNodeKey, allowed: &[SourceEffectId], source: Option<AttachmentSource>) -> Result<LocalWeightId, SolveAvailabilityError> {
        let id = LocalWeightId(u32::try_from(self.weights.len()).map_err(|_| exhausted())?);
        let mut members = Vec::new();
        members.try_reserve_exact(allowed.len()).map_err(|_| exhausted())?;
        members.extend_from_slice(allowed);
        let attachment = source.map(|source| {
            let mut member_ordinals = Vec::new();
            member_ordinals.try_reserve_exact(allowed.len()).map_err(|_| exhausted())?;
            member_ordinals.extend(0..allowed.len());
            Ok::<_, SolveAvailabilityError>(AttachmentSet {
                composed_polarity: source.composed_polarity,
                lexical_scope: source.lexical_scope,
                member_ordinals,
                unit_push: (source.composed_polarity == Polarity::Positive && !allowed.is_empty()).then_some(SourceUnitPush),
            })
        }).transpose()?;
        let ordinal_bytes = attachment.as_ref().map_or(Some(0), |set| set.member_ordinals.capacity().checked_mul(std::mem::size_of::<usize>())).ok_or_else(exhausted)?;
        let weight_bytes = self.weight_bytes.checked_add(ordinal_bytes).and_then(|n| n.checked_add(members.capacity().checked_mul(std::mem::size_of::<SourceEffectId>())?)).ok_or_else(exhausted)?;
        self.weights.try_reserve(1).map_err(|_| exhausted())?;
        self.weights.push(LocalWeight { left_word: [], allowed: members, right_pops: [], boundary, owner: owner.clone(), position: position.clone(), attachment });
        self.weight_bytes = weight_bytes;
        Ok(id)
    }
    // The adapter is private and detached. It does not produce a live
    // ContextExpr, relation, bound, registration, or executable local word.
    #[cfg_attr(not(test), allow(dead_code, reason = "source PUSH preparation has no live consumer"))]
    fn materialize_unit_push(&self, weight: LocalWeightId) -> Result<Option<DetachedWeight>, SolveAvailabilityError> {
        let payload = self.weights.get(weight.0 as usize).ok_or_else(exhausted)?;
        let Some(set) = &payload.attachment else { return Ok(None); };
        if set.unit_push.is_none() { return Ok(None); }
        let mut atoms = Vec::new();
        atoms.try_reserve_exact(payload.allowed.len()).map_err(|_| exhausted())?;
        atoms.extend(payload.allowed.iter().cloned());
        let mut out = DetachedWeight::identity();
        out.left.try_reserve_exact(1).map_err(|_| exhausted())?;
        out.left.push(DetachedLeftEntry {
            id: DetachedAttachmentId(weight.0),
            pops: ExactCount::default(),
            pushes: ExactCount::from_u32(1)?,
            family: Some(DetachedPushFamily(atoms)),
        });
        Ok(Some(out))
    }
    pub fn attachment_source(&self, weight: LocalWeightId) -> Option<AttachmentSource> {
        self.weights[weight.0 as usize].attachment.as_ref().map(|set| AttachmentSource {
            composed_polarity: set.composed_polarity,
            lexical_scope: set.lexical_scope.clone(),
        })
    }
    pub fn allowed(&self, weight: LocalWeightId) -> &[SourceEffectId] {
        &self.weights[weight.0 as usize].allowed
    }
    fn assert_context(&self, context: ContextId) {
        assert!(
            context == IDENTITY || context.0 as usize <= self.contexts.len(),
            "context must be identity or an already interned node"
        );
    }
    pub(super) fn scope_transformer(&self, id: usize) -> Result<&candidate_scope::ScopeTransformer, SolveAvailabilityError> {
        self.scope_transformers.get(id.checked_sub(1).ok_or_else(exhausted)?).map(|entry| &entry.0).ok_or_else(exhausted)
    }
    pub(super) fn intern_scope(&mut self, transformer: candidate_scope::ScopeTransformer) -> Result<usize, SolveAvailabilityError> {
        use std::hash::{Hash, Hasher};
        if transformer == candidate_scope::ScopeTransformer::identity() { return Ok(0); }
        let mut hasher = std::collections::hash_map::DefaultHasher::new(); transformer.hash(&mut hasher);
        let hash = hasher.finish();
        let mut cursor = self.scope_heads.get(&hash).copied();
        while let Some(id) = cursor {
            let entry = &self.scope_transformers[id - 1];
            if entry.0 == transformer { return Ok(id); }
            cursor = entry.1;
        }
        if self.scope_transformers.len() >= candidate_source::SCOPED_RECORD_LIMIT { return Err(exhausted()); }
        let heap = transformer.checked_retained_bytes()?;
        self.scope_inventory.charge(heap.checked_div(std::mem::size_of::<usize>()).unwrap_or(0).checked_add(1).ok_or_else(exhausted)?)?;
        self.scope_transformers.try_reserve(1).map_err(|_| exhausted())?;
        self.scope_heads.try_reserve(1).map_err(|_| exhausted())?;
        let id = self.scope_transformers.len().checked_add(1).ok_or_else(exhausted)?;
        self.scope_transformer_heap = self.scope_transformer_heap.checked_add(heap).ok_or_else(exhausted)?;
        self.scope_transformers.push((transformer, self.scope_heads.insert(hash, id), heap));
        Ok(id)
    }
    fn compose_scopes(&mut self, first: usize, second: usize) -> Result<usize, SolveAvailabilityError> {
        if first == 0 { return Ok(second); } if second == 0 { return Ok(first); }
        let support_bytes = self.scope_transformers[first - 1].2.checked_add(self.scope_transformers[second - 1].2).ok_or_else(exhausted)?;
        self.scope_inventory.charge(support_bytes.checked_div(std::mem::size_of::<usize>()).unwrap_or(0).checked_add(1).ok_or_else(exhausted)?)?;
        // Kernel then performs a fixed number of linear merge/copy stages.
        // Include small-vector reserve floors in this conservative envelope.
        self.scope_inventory.note_scratch(support_bytes.checked_add(256).and_then(|n| n.checked_mul(16)).ok_or_else(exhausted)?);
        let result = self.scope_transformer(first)?.then(self.scope_transformer(second)?)?;
        self.intern_scope(result)
    }
    pub(super) fn prepare_scope_remap(&mut self, transformer: usize) -> Result<(), SolveAvailabilityError> {
        let bytes = self.scope_transformers.get(transformer.checked_sub(1).ok_or_else(exhausted)?).ok_or_else(exhausted)?.2;
        self.scope_inventory.charge(bytes.checked_div(std::mem::size_of::<usize>()).unwrap_or(0).checked_add(1).ok_or_else(exhausted)?)?;
        self.scope_inventory.note_scratch(bytes.checked_add(256).and_then(|n| n.checked_mul(16)).ok_or_else(exhausted)?);
        Ok(())
    }
    pub(super) fn observed_relations(&self) -> impl Iterator<Item = (usize, &TypedPairKey, ScopedFlow)> {
        self.relations.iter().enumerate().map(|(index, relation)| {
            let flow = if relation.key.scoped.0 == 0 { ScopedFlow::default() } else { self.scope_flows[relation.key.scoped.0 - 1] };
            (index, &relation.key.pair, flow)
        })
    }
    pub(super) fn observed_dependencies(&self) -> impl Iterator<Item = &Dependency> { self.dependencies.iter() }
    pub(super) fn observed_pair(&self, relation: RelationId) -> Result<TypedPairKey, SolveAvailabilityError> {
        Ok(self.relations.get(relation.0 as usize).ok_or_else(exhausted)?.key.pair)
    }
    pub(super) fn evaluate_observation(&self, relation: RelationId) -> Result<(usize, candidate_scope::ScopeState), SolveAvailabilityError> {
        let id = self.scoped_flow(relation)?.transformer;
        let state = if id == 0 { candidate_scope::ScopeTransformer::identity().evaluate(&[], &[])? }
            else { self.scope_transformer(id)?.evaluate(&[], &[])? };
        Ok((id, state))
    }
    fn transported_scoped(&self, parent: RelationId, witness: TransportWitness) -> Result<ScopedFlow, SolveAvailabilityError> {
        let mut flow = self.scoped_flow(parent)?;
        if let Some(demand) = &mut flow.demand {
            for (from, to) in [(witness.from.0, witness.to.0), (witness.from.2, witness.to.2)] {
                if from == ExtrusionEndpoint::Value(ValueEndpointKey::NegativeFunction(demand.root)) {
                    let ExtrusionEndpoint::Value(ValueEndpointKey::NegativeFunction(root)) = to else { return Err(SolveAvailabilityError::ReceiptMismatch); };
                    demand.root = root;
                    break;
                }
            }
        }
        Ok(flow)
    }
    pub(super) fn scoped_flow(&self, id: RelationId) -> Result<ScopedFlow, SolveAvailabilityError> {
        let flow = self.relations.get(id.0 as usize).ok_or_else(exhausted)?.key.scoped;
        if flow.0 == 0 { Ok(ScopedFlow::default()) } else { self.scope_flows.get(flow.0 - 1).copied().ok_or_else(exhausted) }
    }
    pub(super) fn relation_pair(&self, id: RelationId) -> Option<TypedPairKey> {
        self.relations.get(id.0 as usize).map(|relation| relation.key.pair)
    }
    /// Allocation-free source of exact Replay/demand rows for the private
    /// diagnostic observer. Each dependency is preserved independently.
    pub(super) fn replay_demand_rows(&self) -> impl Iterator<Item = ReplayDemandRow> + '_ {
        self.dependencies.iter().filter_map(|dependency| {
            let Dependency::Replay { child, lower, upper, lower_input, upper_input } = *dependency else { return None; };
            let demand = self.scoped_flow(child).ok()?.demand?;
            let lower_matches = self.relations.get(lower.0 as usize)
                .is_some_and(|relation| relation.key.pair == bound_pair(lower_input));
            let upper_matches = self.relations.get(upper.0 as usize)
                .is_some_and(|relation| relation.key.pair == bound_pair(upper_input));
            Some(ReplayDemandRow { call: demand.original_call, child, lower, upper, lower_input, upper_input, demand, lower_matches, upper_matches })
        })
    }
    pub(super) fn fresh_use_witness(&self, source: RelationId, demand: ScopedDemand)
        -> Option<(RelationId, BoundKey, BoundKey)> {
        let mut found = None;
        for dependency in &self.dependencies {
            if let Dependency::Transport { child, parent, use_origin,
                witness: Some(TransportWitness { from, to, reason: TransportReason::FreshUse }) } = *dependency
            {
                if parent == source && use_origin == demand.use_instance
                    && self.scoped_flow(child).ok().and_then(|flow| flow.demand) == Some(demand)
                {
                    if found.replace((child, from, to)).is_some() { return None; }
                }
            }
        }
        found
    }
    /// Fail-closed authentication of independently retained FreshUse and Replay
    /// constructors. `fresh_relation` is p1, the FreshUse child and Replay
    /// upper h; `copied` is q, the Replay child. Do not infer either incidence
    /// from an incoming-edge count or from equal terms.
    pub(super) fn authenticate_replay_ancestry(
        &self, row: ReplayDemandRow, source: RelationId, fresh_relation: RelationId,
        copied: RelationId,
        from: BoundKey, to: BoundKey,
    ) -> Option<(RelationId, [RelationId; 4], [usize; 4], Term, Term)> {
        let ordered_replay_pair = match (row.lower_input.2, row.upper_input.2) {
            (ExtrusionEndpoint::Value(lower), ExtrusionEndpoint::Value(upper)) =>
                TypedPairKey::Value(CanonicalValuePairKey { lower, upper }),
            (ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(upper)) =>
                TypedPairKey::Effect { lower, upper },
            _ => return None,
        };
        if !row.lower_matches || !row.upper_matches
            || row.upper != fresh_relation
            || row.upper_input != to
            || !self.bound_relations(to).any(|relation| relation == fresh_relation)
            || self.bound_relations(row.lower_input).next().is_none()
            || !self.bound_relations(row.lower_input).any(|relation| relation == row.lower)
            || self.relations.get(source.0 as usize)?.key.pair != bound_pair(from)
            || self.relations.get(fresh_relation.0 as usize)?.key.pair != bound_pair(to)
            || self.relations.get(copied.0 as usize)?.key.pair != ordered_replay_pair
            || self.relations.get(row.lower.0 as usize)?.key.pair != bound_pair(row.lower_input)
            || self.relations.get(row.upper.0 as usize)?.key.pair != bound_pair(row.upper_input)
            || row.lower_input.0 != row.upper_input.0
            || row.lower_input.1 != Polarity::Positive || row.upper_input.1 != Polarity::Negative
        { return None; }
        let replay = self.dependencies.iter().filter(|edge| matches!(**edge,
            Dependency::Replay { child, lower, upper, lower_input, upper_input }
            if child == row.child && lower == row.lower && upper == row.upper
                && lower_input == row.lower_input && upper_input == row.upper_input)).count();
        if replay != 1 { return None; }

        let fresh = self.dependencies.iter().filter(|edge| matches!(**edge,
            Dependency::Transport { child, parent, use_origin, witness: Some(TransportWitness { from: witness_from, to: witness_to, reason: TransportReason::FreshUse }) }
            if child == fresh_relation && parent == source && use_origin == row.demand.use_instance
                && witness_from == from && witness_to == to)).count();
        if fresh != 1 { return None; }

        let source_root = relation_negative_function_root(self.relations.get(source.0 as usize)?.key.pair)?;
        let fresh_root = relation_negative_function_root(self.relations.get(fresh_relation.0 as usize)?.key.pair)?;
        let ExtrusionEndpoint::Value(ValueEndpointKey::NegativeFunction(source_endpoint_root)) = from.2 else { return None; };
        if source_root != source_endpoint_root || fresh_root != row.demand.root
            || self.scoped_flow(fresh_relation).ok()?.demand != Some(row.demand)
        { return None; }
        let upper_pair = self.relations.get(row.upper.0 as usize)?.key.pair;
        let upper_root = relation_negative_function_root(upper_pair)?;
        let child_root = relation_negative_function_root(self.relations.get(row.child.0 as usize)?.key.pair)?;
        if row.upper_input.2 != ExtrusionEndpoint::Value(ValueEndpointKey::NegativeFunction(upper_root))
            || child_root != row.demand.root
        { return None; }
        let lower_flow = self.scoped_flow(row.lower).ok()?;
        let upper_flow = self.scoped_flow(row.upper).ok()?;
        let child_flow = self.scoped_flow(row.child).ok()?;
        if lower_flow.demand.is_some() || upper_flow.demand != Some(row.demand)
            || child_flow.demand != Some(row.demand)
            || lower_flow.transformer != 0 || upper_flow.transformer != 0 || child_flow.transformer != 0
        { return None; }

        let fields = [FunctionField::Argument, FunctionField::ArgumentEffect, FunctionField::ResultEffect, FunctionField::Result];
        let operations = [FunctionPortOperation::Swap, FunctionPortOperation::Swap, FunctionPortOperation::Preserve, FunctionPortOperation::Preserve];
        let mut children = [RelationId(0); 4];
        let mut transformers = [0usize; 4];
        for index in 0..4 {
            let mut matches = self.dependencies.iter().filter_map(|edge| match *edge {
                Dependency::FunctionPort { child, parent, field, operation }
                    if parent == row.child && field == fields[index] && operation == operations[index] => Some(child),
                _ => None,
            });
            let child = matches.next()?;
            let child_pair = self.relations.get(child.0 as usize)?.key.pair;
            let correct_kind = match fields[index] {
                FunctionField::Argument | FunctionField::Result => matches!(child_pair, TypedPairKey::Value(_)),
                FunctionField::ArgumentEffect | FunctionField::ResultEffect => matches!(child_pair, TypedPairKey::Effect { .. }),
            };
            if matches.next().is_some() || !correct_kind { return None; }
            let flow = self.scoped_flow(child).ok()?;
            if flow.demand.is_some() { return None; }
            let transformer_matches = match fields[index] {
                FunctionField::Argument | FunctionField::Result => flow.transformer == 0,
                FunctionField::ArgumentEffect => {
                    let expected = candidate_scope::ScopeTransformer::stamp_input(row.demand.input).ok()?;
                    self.scope_transformer(flow.transformer).is_ok_and(|actual| actual == &expected)
                }
                FunctionField::ResultEffect => {
                    let expected = candidate_scope::ScopeTransformer::protect_body(
                        row.demand.output_scope, row.demand.input).ok()?;
                    self.scope_transformer(flow.transformer).is_ok_and(|actual| actual == &expected)
                }
            };
            if !transformer_matches { return None; }
            transformers[index] = flow.transformer;
            children[index] = child;
        }
        if (0..4).any(|i| (0..i).any(|j| children[i] == children[j])) { return None; }
        // `q -> C` is the separately checked consumer spine. This fixture's
        // dispatch consumes q directly; its zero-step case is an identity
        // check, not an inferred adjacency. Any rewritten consumer must retain
        // a separate producer edge before it can be accepted here.
        let consumer = row.child;
        let consumer_root = relation_negative_function_root(self.relations.get(consumer.0 as usize)?.key.pair)?;
        if consumer != row.child || consumer_root != child_root {
            return None;
        }
        Some((consumer, children, transformers, upper_root, child_root))
    }
    fn relation(
        &mut self,
        pair: TypedPairKey,
        context: ContextId,
    ) -> Result<RelationId, SolveAvailabilityError> {
        let sources = self.processing.and_then(|id| self.relations[id.0 as usize].key.sources);
        self.relation_with_sources(pair, context, sources)
    }
    fn relation_with_sources(&mut self, pair: TypedPairKey, context: ContextId, sources: Option<usize>) -> Result<RelationId, SolveAvailabilityError> {
        let scoped = self.processing.map(|id| self.scoped_flow(id)).transpose()?.unwrap_or_default();
        self.relation_with_scoped(pair, context, sources, scoped)
    }
    // Structural bound emission is not Function-port projection. Keep deferred
    // Value demands on Value links and executable transforms on Effect links.
    #[cfg(test)]
    fn bound_scoped_payload(&self, parent: RelationId, pair: TypedPairKey) -> Result<ScopedFlow, SolveAvailabilityError> {
        self.bound_scoped_payload_for(parent, pair, BoundConstructionPurpose::Ordinary)
    }
    fn bound_scoped_payload_for(&self, parent: RelationId, pair: TypedPairKey, purpose: BoundConstructionPurpose) -> Result<ScopedFlow, SolveAvailabilityError> {
        let parent_pair = self.relations.get(parent.0 as usize).ok_or_else(exhausted)?.key.pair;
        let flow = self.scoped_flow(parent)?;
        match parent_pair {
            TypedPairKey::Value(_) if flow.transformer != 0 => return Err(SolveAvailabilityError::ReceiptMismatch),
            TypedPairKey::Effect { .. } if flow.demand.is_some() => return Err(SolveAvailabilityError::ReceiptMismatch),
            _ => {}
        }
        if !self.scoped_enabled && flow == ScopedFlow::default() { return Ok(flow); }
        if purpose == BoundConstructionPurpose::ExtrusionLink && matches!(parent_pair, TypedPairKey::Value(_)) {
            return Ok(ScopedFlow::default());
        }
        match (parent_pair, pair) {
            (TypedPairKey::Value(_), TypedPairKey::Value(_))
            | (TypedPairKey::Effect { .. }, TypedPairKey::Effect { .. }) => Ok(flow),
            (TypedPairKey::Value(_), TypedPairKey::Effect { .. }) => Ok(ScopedFlow::default()),
            (TypedPairKey::Effect { .. }, TypedPairKey::Value(_)) => Err(SolveAvailabilityError::ReceiptMismatch),
        }
    }
    pub(super) fn relation_with_scoped(&mut self, pair: TypedPairKey, context: ContextId, sources: Option<usize>, scoped: ScopedFlow) -> Result<RelationId, SolveAvailabilityError> {
        self.assert_context(context);
        // A nonidentity scoped self-relation needs transport semantics that
        // this bounded experiment has not established. Defer it before it can
        // become a dormant bound or disappear in endpoint memoization.
        if scoped.transformer != 0 && matches!(pair, TypedPairKey::Effect { lower, upper } if lower == upper) {
            return Err(exhausted());
        }
        if matches!(pair, TypedPairKey::Value(_)) && scoped.transformer != 0 { return Err(SolveAvailabilityError::ReceiptMismatch); }
        if matches!(pair, TypedPairKey::Effect { .. }) && scoped.demand.is_some() { return Err(SolveAvailabilityError::ReceiptMismatch); }
        let scoped = if scoped == ScopedFlow::default() { ScopedFlowId(0) }
            else if let Some(&id) = self.scope_flow_keys.get(&scoped) { id }
            else {
                if !self.scoped_enabled || self.scope_flows.len() >= candidate_source::SCOPED_RECORD_LIMIT { return Err(exhausted()); }
                self.scope_inventory.charge(1)?;
                self.scope_flows.try_reserve(1).map_err(|_| exhausted())?;
                self.scope_flow_keys.try_reserve(1).map_err(|_| exhausted())?;
                let id = ScopedFlowId(self.scope_flows.len().checked_add(1).ok_or_else(exhausted)?);
                self.scope_flows.push(scoped); self.scope_flow_keys.insert(scoped, id); id
            };
        let key = RelationKey { pair, context, sources, scoped };
        if let Some(&id) = self.keys.get(&key) {
            return Ok(id);
        }
        let id = RelationId(u32::try_from(self.relations.len()).map_err(|_| exhausted())?);
        self.relations.try_reserve(1).map_err(|_| exhausted())?;
        self.keys.try_reserve(1).map_err(|_| exhausted())?;
        self.pair_heads.try_reserve(1).map_err(|_| exhausted())?;
        let previous_on_pair = self.pair_heads.insert(pair, id);
        self.relations.push(Relation { key, previous_on_pair });
        self.keys.insert(key, id);
        Ok(id)
    }
    fn intern_sources(&mut self, mut sources: Vec<usize>) -> Result<Option<usize>, SolveAvailabilityError> {
        sources.sort_unstable(); sources.dedup();
        if sources.is_empty() { return Ok(None); }
        if let Some(&id) = self.source_set_keys.get(&sources) { return Ok(Some(id)); }
        self.source_sets.try_reserve(1).map_err(|_| exhausted())?;
        self.source_set_keys.try_reserve(1).map_err(|_| exhausted())?;
        let mut retained = Vec::new(); retained.try_reserve_exact(sources.len()).map_err(|_| exhausted())?;
        retained.extend_from_slice(&sources);
        self.source_set_bytes = self.source_set_bytes.checked_add(
            sources.capacity().checked_add(retained.capacity()).and_then(|capacity| capacity.checked_mul(std::mem::size_of::<usize>())).ok_or_else(exhausted)?
        ).ok_or_else(exhausted)?;
        let id = self.source_sets.len(); self.source_sets.push(retained); self.source_set_keys.insert(sources, id); Ok(Some(id))
    }
    fn union_sources(&mut self, lower: RelationId, upper: RelationId) -> Result<Option<usize>, SolveAvailabilityError> {
        let a = self.relations[lower.0 as usize].key.sources;
        let b = self.relations[upper.0 as usize].key.sources;
        if a == b || b.is_none() { return Ok(a); } if a.is_none() { return Ok(b); }
        let a = &self.source_sets[a.unwrap()]; let b = &self.source_sets[b.unwrap()];
        let mut sources = Vec::new(); sources.try_reserve_exact(a.len() + b.len()).map_err(|_| exhausted())?;
        sources.extend_from_slice(a); sources.extend_from_slice(b); self.intern_sources(sources)
    }
    pub(super) fn extrusion_sources(&self) -> Option<usize> {
        self.processing.and_then(|id| self.relations[id.0 as usize].key.sources)
    }
    pub(super) fn source_events(&self, sources: usize) -> &[usize] { &self.source_sets[sources] }
    pub fn begin_use(&mut self) -> Result<usize, SolveAvailabilityError> {
        self.uses = self.uses.checked_add(1).ok_or_else(exhausted)?;
        Ok(self.uses)
    }
    #[cfg(test)]
    pub fn contains(&self, pair: TypedPairKey) -> bool {
        self.pair_heads.contains_key(&pair)
    }
    #[cfg(test)]
    pub(super) fn synthetic_source_support(&mut self, watched: &[RelationId]) -> Result<SourceSupportId, SolveAvailabilityError> {
        if watched.iter().any(|id| self.relations.get(id.0 as usize).is_none()) { return Err(exhausted()); }
        let next = self.next_source_support.checked_add(1).ok_or_else(exhausted)?;
        let mut footprint = Vec::new();
        footprint.try_reserve(watched.len()).map_err(|_| exhausted())?;
        self.source_support.try_reserve(1).map_err(|_| exhausted())?;
        self.source_support_log.try_reserve(1).map_err(|_| exhausted())?;
        self.source_support_fail(SourceSupportFailure::Registration)?;
        footprint.extend_from_slice(watched);
        let id = SourceSupportId(self.next_source_support);
        self.source_support.insert(id, SourceSupportRegistration { watched: footprint, generation: self.lifecycle_generation, valid: true });
        self.source_support_log.push(id);
        self.next_source_support = next;
        Ok(id)
    }
    pub(super) fn source_support_wait(&self, id: SourceSupportId) -> Result<Option<candidate_source::Wait>, SolveAvailabilityError> {
        let registration = self.source_support.get(&id).ok_or_else(exhausted)?;
        Ok((!registration.valid).then_some(candidate_source::Wait { generation: registration.generation, dependency: id.0 }))
    }
    #[cfg(test)]
    fn source_support_fail(&mut self, point: SourceSupportFailure) -> Result<(), SolveAvailabilityError> {
        if self.source_support_failure == Some(point) { self.source_support_failure = None; return Err(exhausted()); }
        Ok(())
    }
    fn dependency(&mut self, dependency: Dependency) -> Result<(), SolveAvailabilityError> {
        if self.dependency_keys.contains(&dependency) {
            return Ok(());
        }
        // Check identity exhaustion before any reservation or edge mutation.
        // Exact incidence is already retained in `dependencies`; do not
        // reconstruct a lifecycle mutation from diagnostic reachability.
        let next_generation = if matches!(dependency, Dependency::FunctionPort { .. }) {
            self.lifecycle_generation.checked_add(1).ok_or_else(exhausted)?
        } else { self.lifecycle_generation };
        let invalidations = if let Dependency::FunctionPort { parent, child, .. } = dependency {
            self.source_support.values().filter(|registration| registration.valid
                && (registration.watched.contains(&parent) || registration.watched.contains(&child))).count()
        } else { 0 };
        self.source_support_undo.try_reserve(invalidations).map_err(|_| exhausted())?;
        self.dependencies.try_reserve(1).map_err(|_| exhausted())?;
        self.dependency_keys
            .try_reserve(1)
            .map_err(|_| exhausted())?;
        #[cfg(test)]
        self.source_support_fail(SourceSupportFailure::DependencyPublication)?;
        match dependency {
            Dependency::Derived { child, parent } | Dependency::FunctionPort { child, parent, .. } => self.edge(parent, child)?,
            // Transport retains provenance across instantiation and row
            // lifecycle changes; it is not a constraint from the template to
            // a fresh use and must not replay that use's conflicts upstream.
            Dependency::Transport { .. } => {}
            Dependency::Replay {
                child,
                lower,
                upper,
                ..
            } => {
                self.edge(lower, child)?;
                self.edge(upper, child)?;
            }
        }
        if let Dependency::Transport { child, parent, witness: Some(TransportWitness { reason: TransportReason::Extrusion { .. } | TransportReason::ParentCopy { .. } | TransportReason::EqualityCanonicalization, .. }), .. } = dependency {
            if let Some(index) = &mut self.bundle_transports {
                index.insert(parent, child)?;
                self.bundle_edge(parent, child)?;
            }
        }
        if let Dependency::FunctionPort { parent, child, .. } = dependency {
            for (&id, registration) in &mut self.source_support {
                if registration.valid && (registration.watched.contains(&parent) || registration.watched.contains(&child)) {
                    self.source_support_undo.push(id);
                    registration.valid = false;
                }
            }
        }
        #[cfg(test)]
        self.source_support_fail(SourceSupportFailure::AfterInvalidation)?;
        self.dependencies.push(dependency);
        self.dependency_keys.insert(dependency);
        self.lifecycle_generation = next_generation;
        Ok(())
    }
    fn edge(
        &mut self,
        parent: RelationId,
        child: RelationId,
    ) -> Result<(), SolveAvailabilityError> {
        if self.edge_keys.contains(&(parent, child)) {
            return Ok(());
        }
        self.edges.try_reserve(1).map_err(|_| exhausted())?;
        self.edge_keys.try_reserve(1).map_err(|_| exhausted())?;
        self.edge_log.try_reserve(1).map_err(|_| exhausted())?;
        let new = !self.edges.contains_key(&parent);
        let mut fresh = Vec::new();
        let entries = if new {
            &mut fresh
        } else {
            self.edges.get_mut(&parent).unwrap()
        };
        let old = entries.capacity();
        entries.try_reserve(1).map_err(|_| exhausted())?;
        self.edge_bytes = self
            .edge_bytes
            .checked_add(
                (entries.capacity() - old)
                    .checked_mul(std::mem::size_of::<RelationId>())
                    .ok_or_else(exhausted)?,
            )
            .ok_or_else(exhausted)?;
        entries.push(child);
        if new {
            self.edges.insert(parent, fresh);
        }
        self.edge_keys.insert((parent, child));
        self.edge_log.push((parent, child));
        self.bundle_edge(parent, child)
    }
    pub fn children(&self, pair: TypedPairKey) -> impl Iterator<Item = TypedPairKey> + '_ {
        std::iter::successors(self.pair_heads.get(&pair).copied(), |id| {
            self.relations[id.0 as usize].previous_on_pair
        })
        .filter_map(|id| self.edges.get(&id))
        .flatten()
        .map(|id| self.relations[id.0 as usize].key.pair)
    }
    #[cfg(test)]
    pub fn bound(&self, key: BoundKey) -> Option<RelationId> {
        self.bound_relations(key).next()
    }
    pub fn bound_relations(&self, key: BoundKey) -> impl Iterator<Item = RelationId> + '_ {
        std::iter::successors(self.bounds.get(&key).copied(), |&index| {
            self.bound_keys[index].2
        }).map(|index| self.bound_keys[index].1)
    }
    pub fn bound_cursor(&self, key: BoundKey) -> Option<usize> {
        self.bounds.get(&key).copied()
    }
    pub fn bound_entry(&self, index: usize) -> (RelationId, Option<usize>) {
        let (_, relation, next) = self.bound_keys[index];
        (relation, next)
    }
    fn replay_progress(&mut self, key: (BoundKey, BoundKey), heads: (Option<usize>, Option<usize>)) -> Result<(), SolveAvailabilityError> {
        self.replay_heads.try_reserve(1).map_err(|_| exhausted())?;
        self.replay_log.try_reserve(1).map_err(|_| exhausted())?;
        let previous = self.replay_heads.insert(key, heads);
        self.replay_log.push((key, previous));
        Ok(())
    }
    fn attach(
        &mut self,
        key: BoundKey,
        relation: RelationId,
    ) -> Result<(), SolveAvailabilityError> {
        if self.bound_relations(key).any(|existing| existing == relation) {
            return Ok(());
        }
        self.bounds.try_reserve(1).map_err(|_| exhausted())?;
        self.bound_keys.try_reserve(1).map_err(|_| exhausted())?;
        let previous = self.bounds.insert(key, self.bound_keys.len());
        self.bound_keys.push((key, relation, previous));
        Ok(())
    }
    fn post_check_context(&self, relation: RelationId) -> ContextId {
        let context = self.relations[relation.0 as usize].key.context;
        if self.discharged.contains(&relation) {
            self.discharge_residuals.get(&relation).copied().unwrap_or(IDENTITY)
        } else { context }
    }

}
pub(super) fn task_pair(task: LiveConstraintTask) -> TypedPairKey {
    match task {
        LiveConstraintTask::Value(pair) => TypedPairKey::Value(pair),
        LiveConstraintTask::Effect(lower, upper) => TypedPairKey::Effect { lower, upper },
    }
}
pub(super) fn bound_pair(BoundKey(owner, side, item): BoundKey) -> TypedPairKey {
    let (lower, upper) = if side == Polarity::Positive {
        (item, owner)
    } else {
        (owner, item)
    };
    match (lower, upper) {
        (ExtrusionEndpoint::Value(lower), ExtrusionEndpoint::Value(upper)) => {
            TypedPairKey::Value(CanonicalValuePairKey { lower, upper })
        }
        (ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(upper)) => {
            TypedPairKey::Effect { lower, upper }
        }
        _ => unreachable!("bound component kind"),
    }
}
fn relation_negative_function_root(pair: TypedPairKey) -> Option<Term> {
    let TypedPairKey::Value(pair) = pair else { return None; };
    match pair.upper { ValueEndpointKey::NegativeFunction(root) => Some(root), _ => None }
}
#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum EvidenceFailurePoint { Admission, Emission, ImportReserve, ImportedSnapshot, Transport, Recipe, CaptureScratch }
impl InferenceSession {
    #[cfg(test)]
    pub(super) fn candidate_evidence_failure(&mut self, point: EvidenceFailurePoint) -> Result<(), SolveAvailabilityError> {
        let graph = self.candidate_graph.as_mut().unwrap();
        if graph.evidence_failure != Some(point) { return Ok(()); }
        graph.evidence_failure = None;
        graph.failed_evidence_point = Some(point);
        // Fault injection follows a charged sample, including transient growth.
        let scratch = graph.scratch_bytes;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        let total = self.resource_ledger.inference_session_retained_bytes;
        self.candidate_graph.as_mut().unwrap().failed_evidence_sample = Some((point, scratch, total));
        Err(exhausted())
    }

    pub(super) fn candidate_context_pair(&self, pair: TypedPairKey) -> TypedPairKey {
        match pair {
            TypedPairKey::Value(pair) => TypedPairKey::Value(CanonicalValuePairKey {
                lower: self.canonical_value(pair.lower),
                upper: self.canonical_value(pair.upper),
            }),
            TypedPairKey::Effect { lower, upper } => TypedPairKey::Effect {
                lower: self.canonical_effect(lower),
                upper: self.canonical_effect(upper),
            },
        }
    }
    fn candidate_closed_allowance(&self, pair: TypedPairKey) -> Option<LocalWeightId> {
        let TypedPairKey::Effect { upper: EffectEndpointKey::Allowance(view), .. } = pair else { return None; };
        let view_data = &self.candidate_graph.as_ref()?.intrusion.effect_algebra.views[view as usize];
        view_data.closed_weight
    }
    fn candidate_context_source(&mut self, pair: TypedPairKey) -> Result<ContextId, SolveAvailabilityError> {
        let weight = self.candidate_closed_allowance(pair);
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        match weight {
            Some(weight) => state.context(ContextExpr::PrefixLeft { weight, input: IDENTITY }),
            None => Ok(IDENTITY),
        }
    }
    pub(super) fn candidate_context_seed(
        &mut self,
        task: LiveConstraintTask,
        occurrence: &ConstraintOccurrenceId,
        inferred_entry: Option<InferredEntryOriginId>,
    ) -> Result<Option<RelationId>, SolveAvailabilityError> {
        if self.candidate_graph.is_none() {
            return Ok(None);
        }
        let source = self.batch.candidate_source.references.checking.get(occurrence).copied();
        let pair = self.candidate_context_pair(task_pair(task));
        let context = self.candidate_context_source(pair)?;
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let sources = match source { Some(source) => { let mut singleton = Vec::new(); singleton.try_reserve_exact(1).map_err(|_| exhausted())?; singleton.push(source); state.intern_sources(singleton)? }, None => None };
        let mut scoped = ScopedFlow::default();
        if state.scoped_enabled {
            if let Some(&call_index) = self.batch.candidate_calls.by_occurrence.get(occurrence.occurrence()) {
                let call = &self.batch.candidate_calls.calls[call_index];
                match occurrence.local_slot() {
                    0 => {
                        if let Some(introduction) = &call.introduction {
                            scoped.demand = Some(ScopedDemand {
                                original_call: call_index, use_instance: 0, root: introduction.demand,
                                output_scope: self.batch.candidate_source.computation_scopes[occurrence.occurrence()],
                                input: candidate_scope::InputRouteId(u32::try_from(call_index).map_err(|_| exhausted())?),
                            });
                        }
                    }
                    2 => {
                        let source = self.batch.hir.local_source_for(&call.owner).map_err(|_| exhausted())?.ok_or_else(exhausted)?;
                        let argument = source.expression(&call.argument).ok_or_else(exhausted)?;
                        let scope = self.batch.candidate_source.computation_scopes.get(&argument.occurrence).copied().ok_or_else(exhausted)?;
                        scoped.transformer = state.intern_scope(candidate_scope::ScopeTransformer::release(scope)?)?;
                    }
                    _ => {}
                }
            }
        }
        let relation = state.relation_with_scoped(pair, context, sources, scoped)?;
        let bundle_slot = match occurrence.local_slot() {
            40 | 41 => Some(41),
            45 | 46 => Some(46),
            _ => None,
        };
        if let Some(slot) = bundle_slot {
            let anchor = ConstraintOccurrenceId::new(occurrence.occurrence().clone(), slot);
            if let Some(&bundle) = state.source_bundles.get(&anchor) { state.bundle_link(relation, bundle)?; }
        }
        state.origins.try_reserve(1).map_err(|_| exhausted())?;
        // The Lambda owner supplies its exact retained handle directly. All
        // other source admissions take the bounded no-handle path.
        state.origins.push(Origin {
            relation,
            occurrence: occurrence.clone(),
            inferred_entry,
            formal: None,
        });
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(Some(relation))
    }
    // One owning seed carries both independent construction facts. Existing
    // inferred-entry attachment is retained even when a formal is also supplied.
    pub(super) fn candidate_context_seed_with_formal(
        &mut self, task: LiveConstraintTask, occurrence: &ConstraintOccurrenceId,
        inferred_entry: Option<InferredEntryOriginId>, formal: Option<FormalConstruction>,
    ) -> Result<Option<RelationId>, SolveAvailabilityError> {
        let relation = self.candidate_context_seed(task, occurrence, inferred_entry)?;
        if let Some(formal) = formal {
            let state = &mut self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion.effect_algebra.context;
            let origin = state.origins.last_mut().ok_or_else(exhausted)?;
            debug_assert_eq!(Some(origin.relation), relation);
            debug_assert_eq!(&origin.occurrence, occurrence);
            origin.formal = Some(formal);
        }
        Ok(relation)
    }
    pub(super) fn candidate_context_admit(
        &mut self,
        task: LiveConstraintTask,
    ) -> Result<Option<RelationId>, SolveAvailabilityError> {
        let Some(graph) = &self.candidate_graph else { return Ok(None); };
        let retained_parent = graph.intrusion.effect_algebra.context.processing;
        let parent = graph.intrusion.effect_algebra.processing
            .map(|p| self.candidate_context_pair(p));
        let pair = self.candidate_context_pair(task_pair(task));
        let context = self.candidate_context_source(pair)?;
        let parent_context = parent.map(|pair| self.candidate_context_source(pair)).transpose()?;
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let child = state.relation(pair, context)?;
        if let Some(parent) = parent {
            let parent = match retained_parent {
                Some(id) if state.relations[id.0 as usize].key.pair == parent => id,
                _ => state.relation(parent, parent_context.unwrap())?,
            };
            state.dependency(Dependency::Derived { child, parent })?;
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(Some(child))
    }
    /// The caller supplies the actual whole-Value extrusion rewrite. Its demand
    /// root follows that copied upper Function, never a later consumer's shape.
    pub(super) fn candidate_context_value_rewrite(&mut self, original: CanonicalValuePairKey, rewritten: CanonicalValuePairKey) -> Result<Option<RelationId>, SolveAvailabilityError> {
        let Some(graph) = &self.candidate_graph else { return Ok(None); };
        let parent = graph.intrusion.effect_algebra.context.processing.ok_or_else(exhausted)?;
        let original_pair = self.candidate_context_pair(TypedPairKey::Value(original));
        let pair = self.candidate_context_pair(TypedPairKey::Value(rewritten));
        let context = self.candidate_context_source(pair)?;
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        if state.relations[parent.0 as usize].key.pair != original_pair { return Err(SolveAvailabilityError::ReceiptMismatch); }
        let mut flow = state.scoped_flow(parent)?;
        if flow.transformer != 0 { return Err(SolveAvailabilityError::ReceiptMismatch); }
        if let Some(demand) = &mut flow.demand {
            if original.upper != ValueEndpointKey::NegativeFunction(demand.root) { return Err(SolveAvailabilityError::ReceiptMismatch); }
            if original.upper != rewritten.upper {
                let ValueEndpointKey::NegativeFunction(root) = rewritten.upper else { return Err(SolveAvailabilityError::ReceiptMismatch); };
                demand.root = root;
            }
        }
        let child = state.relation_with_scoped(pair, context, state.relations[parent.0 as usize].key.sources, flow)?;
        state.dependency(Dependency::Derived { child, parent })?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(Some(child))
    }
    pub(super) fn candidate_function_port_admit(
        &mut self,
        task: LiveConstraintTask,
        field: FunctionField,
    ) -> Result<Option<RelationId>, SolveAvailabilityError> {
        let Some(graph) = &self.candidate_graph else {
            return Ok(None);
        };
        let parent = graph.intrusion.effect_algebra.context.processing.ok_or_else(exhausted)?;
        let derived = graph.intrusion.effect_algebra.processing.is_some();
        let pair = self.candidate_context_pair(task_pair(task));
        let local = self.candidate_context_source(pair)?;
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let operation = match field {
            FunctionField::Argument | FunctionField::ArgumentEffect => FunctionPortOperation::Swap,
            FunctionField::ResultEffect | FunctionField::Result => FunctionPortOperation::Preserve,
        };
        // The retained parent owns the post-check context. Child-local wrapper
        // authority prefixes the inherited Function operation in source order.
        let inherited = state.post_check_context(parent);
        let inherited = match operation {
            FunctionPortOperation::Swap if inherited != IDENTITY =>
                state.context(ContextExpr::Swap { input: inherited })?,
            _ => inherited,
        };
        let context = if local == IDENTITY {
            inherited
        } else {
            match state.contexts.get(local.0 as usize - 1).copied() {
                Some(ContextExpr::PrefixLeft { weight, input: IDENTITY }) =>
                    state.context(ContextExpr::PrefixLeft { weight, input: inherited })?,
                _ => return Err(exhausted()),
            }
        };
        let mut scoped = state.scoped_flow(parent)?;
        if scoped.transformer != 0 { return Err(SolveAvailabilityError::ReceiptMismatch); }
        if let Some(demand) = scoped.demand {
            let authentic = matches!(state.relations[parent.0 as usize].key.pair,
                TypedPairKey::Value(CanonicalValuePairKey { upper: ValueEndpointKey::NegativeFunction(root), .. }) if root == demand.root);
            if !authentic { return Err(SolveAvailabilityError::ReceiptMismatch); }
            scoped.demand = None;
            scoped.transformer = match field {
                FunctionField::ArgumentEffect => state.intern_scope(candidate_scope::ScopeTransformer::stamp_input(demand.input)?)?,
                FunctionField::ResultEffect => state.intern_scope(candidate_scope::ScopeTransformer::protect_body(demand.output_scope, demand.input)?)?,
                FunctionField::Argument | FunctionField::Result => 0,
            };
        }
        let child = state.relation_with_scoped(pair, context, state.relations[parent.0 as usize].key.sources, scoped)?;
        if derived {
            state.dependency(Dependency::Derived { child, parent })?;
        }
        state.dependency(Dependency::FunctionPort {
            child,
            parent,
            field,
            operation,
        })?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(Some(child))
    }
    // Validate the whole live fragment before publishing any of its checks.
    // Keep the validated ID set live through synchronous bound callbacks;
    // nested consumers restore the enclosing scope on both success and error.
    fn candidate_zero_word_filters<T>(
        &mut self, relation: RelationId, root: ContextId,
        consume: impl FnOnce(&mut Self, &[LocalWeightId], ContextId) -> Result<T, SolveAvailabilityError>,
    ) -> Result<T, SolveAvailabilityError> {
        let mut pending = Vec::new();
        let mut visited = HashSet::new();
        let mut filters = Vec::new();
        let mut weights = HashSet::new();
        let mut replay_filters = false;
        let mut directed_residual = false;
        let mut replay_residual = false;
        let mut residual = root;
        let mut charge = 0;
        let result = (|| {
            let before = pending.capacity();
            pending.try_reserve(1).map_err(|_| exhausted())?;
            self.candidate_scratch_growth(&mut charge, (pending.capacity() - before)
                .checked_mul(std::mem::size_of::<(ContextId, u8)>()).ok_or_else(exhausted)?)?;
            // 0: outer prefix spine; 1: replay-only filter fragment;
            // 2: payload-free directed residual.
            pending.push((root, 0_u8));
            while let Some((id, mode)) = pending.pop() {
                if id == IDENTITY || visited.contains(&(id, mode)) { continue; }
                let before = visited.capacity();
                visited.try_reserve(1).map_err(|_| exhausted())?;
                self.candidate_scratch_growth(&mut charge, (visited.capacity() - before)
                    .checked_mul(std::mem::size_of::<(ContextId, u8)>()).ok_or_else(exhausted)?)?;
                visited.insert((id, mode));
                let state = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
                let node = *state.context.contexts.get(id.0 as usize - 1).ok_or_else(exhausted)?;
                match node {
                    ContextExpr::PrefixLeft { weight, input } if mode == 0 || (mode == 1 && input == IDENTITY) => {
                        if input.0 >= id.0 { return Err(exhausted()); }
                        if mode == 0 { residual = input; } else { replay_filters = true; }
                        // The spine is linear; its popped slot is reusable.
                        pending.push((input, mode));
                        let payload = state.context.weights.get(weight.0 as usize).ok_or_else(exhausted)?;
                        let boundary = state.views.get(payload.boundary as usize).ok_or_else(exhausted)?;
                        if !payload.left_word.is_empty() || !payload.right_pops.is_empty()
                            || payload.owner != boundary.owner || payload.position != boundary.position
                            || boundary.closed_weight != Some(weight) {
                            return Err(exhausted());
                        }
                        if weights.contains(&weight) { continue; }
                        let before = weights.capacity();
                        weights.try_reserve(1).map_err(|_| exhausted())?;
                        self.candidate_scratch_growth(&mut charge, (weights.capacity() - before)
                            .checked_mul(std::mem::size_of::<LocalWeightId>()).ok_or_else(exhausted)?)?;
                        weights.insert(weight);
                        let before = filters.capacity();
                        filters.try_reserve(1).map_err(|_| exhausted())?;
                        self.candidate_scratch_growth(&mut charge, (filters.capacity() - before)
                            .checked_mul(std::mem::size_of::<LocalWeightId>()).ok_or_else(exhausted)?)?;
                        filters.push(weight);
                    }
                    ContextExpr::Replay { lower, upper } => {
                        if mode == 0 { replay_residual = true; }
                        let child_mode = if mode == 2 { 2 } else { 1 };
                        if lower.0 >= id.0 || upper.0 >= id.0 { return Err(exhausted()); }
                        let before = pending.capacity();
                        pending.try_reserve(2).map_err(|_| exhausted())?;
                        self.candidate_scratch_growth(&mut charge, (pending.capacity() - before)
                            .checked_mul(std::mem::size_of::<(ContextId, u8)>()).ok_or_else(exhausted)?)?;
                        pending.push((upper, child_mode));
                        pending.push((lower, child_mode));
                    }
                    ContextExpr::Swap { input } | ContextExpr::WithoutLeftFilter { input } => {
                        if input.0 >= id.0 { return Err(exhausted()); }
                        directed_residual = true;
                        let before = pending.capacity();
                        pending.try_reserve(1).map_err(|_| exhausted())?;
                        self.candidate_scratch_growth(&mut charge, (pending.capacity() - before)
                            .checked_mul(std::mem::size_of::<(ContextId, u8)>()).ok_or_else(exhausted)?)?;
                        pending.push((input, 2));
                    }
                    _ => return Err(exhausted()),
                }
            }
            // Replay-only zero-word filters discharge together. Directed residuals
            // retain their exact operations and cannot contain buried filters.
            if replay_filters && directed_residual { return Err(exhausted()); }
            if replay_residual && !directed_residual { residual = IDENTITY; }
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            let prior = self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context
                .checking_filters.replace((relation, std::mem::take(&mut weights)));
            let consumed = consume(self, &filters, residual);
            let active = std::mem::replace(&mut self.candidate_graph.as_mut().unwrap()
                .intrusion.effect_algebra.context.checking_filters, prior);
            drop(active);
            consumed
        })();
        drop(weights);
        drop(pending);
        drop(visited);
        drop(filters);
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= charge;
        result
    }
    pub(super) fn candidate_context_transport_task(
        &mut self,
        task: LiveConstraintTask,
        relation: Option<RelationId>,
    ) -> Result<Option<RelationId>, SolveAvailabilityError> {
        let Some(parent) = relation else { return Ok(None); };
        let pair = self.candidate_context_pair(task_pair(task));
        let key = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context
            .relations[parent.0 as usize].key;
        assert_eq!(self.candidate_context_pair(key.pair), pair, "task retains its relation endpoints");
        if key.pair == pair { return Ok(Some(parent)); }
        // Equality changes execution identity, while the original relation and
        // raw task remain available for occurrence diagnostics and rollback.
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let child = state.relation_with_scoped(pair, state.post_check_context(parent), state.relations[parent.0 as usize].key.sources, state.scoped_flow(parent)?)?;
        state.dependency(Dependency::Derived { parent, child })?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(Some(child))
    }
    // Admission checks precede endpoint memoization and equality handling.
    // Exact Allowance endpoints are handled by their retained registrations;
    // other endpoint pairs still propagate normally after filter discharge.
    pub(super) fn candidate_context_execute(
        &mut self,
        task: LiveConstraintTask,
        relation: Option<RelationId>,
    ) -> Result<bool, SolveAvailabilityError> {
        let Some(relation) = self.candidate_context_transport_task(task, relation)? else { return Ok(false); };
        let previous = self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing.replace(relation);
        let result = self.candidate_context_execute_relation(task, relation);
        self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = previous;
        result
    }
    fn candidate_context_execute_relation(
        &mut self,
        task: LiveConstraintTask,
        relation: RelationId,
    ) -> Result<bool, SolveAvailabilityError> {
        let state = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        let key = state.relations[relation.0 as usize].key;
        assert_eq!(key.pair, self.candidate_context_pair(task_pair(task)), "task retains its relation endpoints");
        if state.scoped_flow(relation)?.transformer != 0
            && matches!(key.pair, TypedPairKey::Effect { lower, upper } if lower == upper) {
            return Err(exhausted());
        }
        if self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.scoped_enabled {
            if let LiveConstraintTask::Effect(operand @ (EffectEndpointKey::Support(_) | EffectEndpointKey::Contribution(_) | EffectEndpointKey::AnnotationMember(_, _)), _) = task {
                let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                let observation = ScopedObservation { relation, operand };
                if !state.scope_observation_keys.contains(&observation) {
                    if state.scope_observations.len() >= candidate_source::SCOPED_RECORD_LIMIT { return Err(exhausted()); }
                    state.scope_inventory.charge(1)?;
                    state.scope_observations.try_reserve(1).map_err(|_| exhausted())?;
                    state.scope_observation_keys.try_reserve(1).map_err(|_| exhausted())?;
                    state.scope_observation_keys.insert(observation);
                    state.scope_observations.push(observation);
                }
            }
        }
        if key.context == IDENTITY { return Ok(false); }
        self.candidate_zero_word_filters(relation, key.context, |session, filters, residual| {
            // Unrestricted operations have no receiver check to discharge. Keep
            // their exact construction for Function ports, bounds and replay.
            if filters.is_empty() { return Ok(false); }
            let lower = match task {
                LiveConstraintTask::Effect(lower, _) => lower,
                LiveConstraintTask::Value(_) => return Err(exhausted()),
            };
            let consumed_endpoint = match key.pair {
                TypedPairKey::Effect { upper: EffectEndpointKey::Allowance(view), .. } =>
                    filters.iter().any(|weight| session.candidate_graph.as_ref().unwrap()
                        .intrusion.effect_algebra.context.weights[weight.0 as usize].boundary == view),
                _ => false,
            };
            if session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context
                .discharged.contains(&relation) { return Ok(consumed_endpoint); }
            for &weight in filters {
                let view = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.weights[weight.0 as usize].boundary;
                let upper = EffectEndpointKey::Allowance(view);
                let registered = match session.canonical_effect(lower) {
                    EffectEndpointKey::EffectRow(row) => session.effect_bounds[row as usize].exact_non_variable_uppers.contains(&upper),
                    _ => false,
                };
                if registered {
                    // The allowance already owns its executable bound, but this
                    // source occurrence still needs an edge to that bound. Otherwise
                    // a conflict recorded before this relation was admitted cannot
                    // be replayed at this occurrence.
                    let EffectEndpointKey::EffectRow(row) = session.canonical_effect(lower) else { unreachable!() };
                    session.candidate_bound_origin(
                        BoundKey(
                            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row)),
                            Polarity::Negative,
                            ExtrusionEndpoint::Effect(upper),
                        ),
                        Some(task_pair(task)),
                    )?;
                    session.candidate_replay_bound(
                        ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row)),
                        Polarity::Negative,
                        ExtrusionEndpoint::Effect(upper),
                        None,
                    )?;
                } else {
                    session.candidate_apply_effect(lower, upper)?;
                }
            }
            let state = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
            // Reserve all retained discharge state before publishing any entry.
            state.discharged.try_reserve(1).map_err(|_| exhausted())?;
            state.discharge_log.try_reserve(1).map_err(|_| exhausted())?;
            if residual != IDENTITY {
                state.discharge_residuals.try_reserve(1).map_err(|_| exhausted())?;
                state.discharge_residuals.insert(relation, residual);
            }
            state.discharged.insert(relation);
            state.discharge_log.push(relation);
            session.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            Ok(consumed_endpoint)
        })
    }
    pub(super) fn candidate_context_bound(
        &mut self,
        bound: BoundKey,
        origin: TypedPairKey,
    ) -> Result<RelationId, SolveAvailabilityError> {
        self.candidate_context_bound_for(bound, origin, BoundConstructionPurpose::Ordinary)
    }
    pub(super) fn candidate_context_extrusion_link(&mut self, bound: BoundKey, origin: TypedPairKey) -> Result<RelationId, SolveAvailabilityError> {
        self.candidate_context_bound_for(bound, origin, BoundConstructionPurpose::ExtrusionLink)
    }
    fn candidate_context_bound_for(&mut self, bound: BoundKey, origin: TypedPairKey, purpose: BoundConstructionPurpose) -> Result<RelationId, SolveAvailabilityError> {
        let pair = self.candidate_context_pair(bound_pair(bound));
        let origin = self.candidate_context_pair(origin);
        let origin_context = self.candidate_context_source(origin)?;
        let retained_parent = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.processing;
        let algebra = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        let checked_boundary = match (bound, retained_parent, &algebra.context.checking_filters) {
            (BoundKey(ExtrusionEndpoint::Effect(owner), Polarity::Negative,
                ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(view))),
                Some(parent), Some((checked_parent, weights)))
                if parent == *checked_parent
                    && algebra.context.relations[parent.0 as usize].key.pair == origin
                    && matches!(origin, TypedPairKey::Effect { lower, .. }
                        if self.canonical_effect(lower) == self.canonical_effect(owner)) => {
                algebra.views.get(view as usize).and_then(|view| view.closed_weight)
                    .is_some_and(|weight| weights.contains(&weight)
                        && algebra.context.weights[weight.0 as usize].boundary == view)
            }
            _ => false,
        };
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let parent = match retained_parent {
            Some(id) if state.relations[id.0 as usize].key.pair == origin => id,
            _ => state.relation(origin, origin_context)?,
        };
        // The exact allowance bound retains this boundary's executable check;
        // its derivation still points to the complete, undischarged parent DAG.
        let context = if checked_boundary { IDENTITY } else { state.post_check_context(parent) };
        let scoped = state.bound_scoped_payload_for(parent, pair, purpose)?;
        let child = state.relation_with_scoped(pair, context, state.relations[parent.0 as usize].key.sources, scoped)?;
        state.dependency(Dependency::Derived { child, parent })?;
        state.attach(bound, child)?;
        Ok(child)
    }
    #[cfg(test)]
    pub(super) fn candidate_context_replay<T>(
        &mut self,
        lower_input: BoundKey,
        upper_input: BoundKey,
        task: LiveConstraintTask,
        publish: impl FnOnce(&mut Self, &[RelationId]) -> Result<T, SolveAvailabilityError>,
    ) -> Result<T, SolveAvailabilityError> {
        self.candidate_context_replay_impl(lower_input, upper_input, task, false, publish)
    }
    #[cfg(test)]
    pub(super) fn candidate_context_restore_replay<T>(
        &mut self,
        lower_input: BoundKey,
        upper_input: BoundKey,
        task: LiveConstraintTask,
        publish: impl FnOnce(&mut Self, &[RelationId]) -> Result<T, SolveAvailabilityError>,
    ) -> Result<T, SolveAvailabilityError> {
        self.candidate_context_replay_impl(lower_input, upper_input, task, true, publish)
    }
    #[cfg(test)]
    fn candidate_context_replay_impl<T>(
        &mut self,
        lower_input: BoundKey,
        upper_input: BoundKey,
        task: LiveConstraintTask,
        incoming_use: bool,
        publish: impl FnOnce(&mut Self, &[RelationId]) -> Result<T, SolveAvailabilityError>,
    ) -> Result<T, SolveAvailabilityError> {
        let id = self.candidate_context_begin_replay(lower_input, upper_input, task, incoming_use)?;
        // Compatibility harness only: production consumes the owned batch by
        // operation identity without lending a local vector to a closure.
        let children = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.replay_operations[&id].children;
        let mut replay = Vec::new();
        replay.try_reserve(children.len()).map_err(|_| exhausted())?;
        replay.extend_from_slice(children);
        let mut charge = 0;
        self.candidate_scratch_growth(&mut charge, replay.capacity().checked_mul(std::mem::size_of::<RelationId>()).ok_or_else(exhausted)?)?;
        let result = publish(self, &replay);
        drop(replay);
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= charge;
        if result.is_ok() {
            loop {
                let pending = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.replay_operation_next(id)?.is_some();
                let transactional = self.route_journal.is_some();
                let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                state.prepare_replay_ack(id, transactional)?;
                if pending { state.replay_operations.get_mut(&id).unwrap().queued += 1; }
                state.acknowledge_replay(id, transactional);
                if !pending || state.replay_operations.get(&id).is_none_or(|operation| operation.retired) { break; }
            }
        }
        result
    }
    pub(super) fn candidate_context_begin_replay(
        &mut self,
        lower_input: BoundKey,
        upper_input: BoundKey,
        task: LiveConstraintTask,
        incoming_use: bool,
    ) -> Result<ReplayOperationId, SolveAvailabilityError> {
        {
            let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
            state.next_replay_operation.checked_add(1).ok_or_else(exhausted)?;
            state.replay_operations.try_reserve(1).map_err(|_| exhausted())?;
        }
        let pair = self.candidate_context_pair(task_pair(task));
        let mut replay = Vec::new();
        let mut charge = 0;
        let result = (|| {
            let state = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
            let heads = (state.bound_cursor(lower_input), state.bound_cursor(upper_input));
            let recorded = state.replay_heads.get(&(lower_input, upper_input)).copied().unwrap_or((None, None));
            // Every incoming scheme use owns diagnostic replay, even when
            // ordinary propagation already admitted these exact dependencies.
            let old = if incoming_use { (None, None) } else { recorded };
            // Each newly retained fiber meets the opposite fibers once. Older
            // lower fibers meet only new uppers; the new/new quadrant is owned
            // by the first loop.
            for (start, stop, upper_start, upper_stop) in [
                (heads.0, old.0, heads.1, None),
                (old.0, None, heads.1, old.1),
            ] {
                if upper_start == upper_stop { continue; }
                let mut lower_cursor = start;
                while lower_cursor != stop {
                    let Some(index) = lower_cursor else { break; };
                    let (lower, next) = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_entry(index);
                    lower_cursor = next;
                    let mut upper_cursor = upper_start;
                    while upper_cursor != upper_stop {
                        let Some(index) = upper_cursor else { break; };
                        let (upper, next) = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_entry(index);
                        upper_cursor = next;
                        let old_capacity = replay.capacity();
                        replay.try_reserve(1).map_err(|_| exhausted())?;
                        self.candidate_scratch_growth(&mut charge,
                            (replay.capacity() - old_capacity).checked_mul(std::mem::size_of::<RelationId>()).ok_or_else(exhausted)?)?;
                        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                        let lower_context = state.relations[lower.0 as usize].key.context;
                        let upper_context = state.relations[upper.0 as usize].key.context;
                        // Empty-weight directed mix is identity; its ordered
                        // derivation remains in the dependency certificate.
                        let context = if lower_context == IDENTITY && upper_context == IDENTITY { IDENTITY }
                            else { state.context(ContextExpr::Replay { lower: lower_context, upper: upper_context })? };
                        let sources = state.union_sources(lower, upper)?;
                        let lower_scoped = state.scoped_flow(lower)?;
                        let upper_scoped = state.scoped_flow(upper)?;
                        if lower_scoped.demand.is_some() { return Err(SolveAvailabilityError::ReceiptMismatch); }
                        let scoped = ScopedFlow { transformer: state.compose_scopes(lower_scoped.transformer, upper_scoped.transformer)?, demand: upper_scoped.demand };
                        let child = state.relation_with_scoped(pair, context, sources, scoped)?;
                        let dependency = Dependency::Replay { child, lower, upper, lower_input, upper_input };
                        state.evidence.recipe(dependency)?;
                        #[cfg(test)]
                        self.candidate_evidence_failure(EvidenceFailurePoint::Recipe)?;
                        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                        if !incoming_use && state.dependency_keys.contains(&dependency) { continue; }
                        state.dependency(dependency)?;
                        replay.push(child);
                    }
                }
            }
            if heads != recorded {
                self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.replay_progress((lower_input, upper_input), heads)?;
            }
            let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
            let child_bytes = state.replay_child_bytes.checked_add(charge).ok_or_else(exhausted)?;
            let id = ReplayOperationId(state.next_replay_operation);
            state.next_replay_operation += 1;
            state.replay_operations.insert(id, ReplayOperation { task, inputs: (lower_input, upper_input), heads,
                prior: old, incoming_use, children: std::mem::take(&mut replay), queued: 0, consumed: 0, retired: false, restoration: None, waiting_child: ReplayChildWait::Idle });
            state.replay_child_bytes = child_bytes;
            // Ownership moved from generation scratch to retained operation storage.
            self.candidate_graph.as_mut().unwrap().scratch_bytes -= charge;
            charge = 0;
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            Ok(id)
        })();
        drop(replay);
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= charge;
        result
    }
    // ReturnReady owns the receipt. The ordered replay parent releases that
    // barrier without acknowledging the same child a second time.
    fn candidate_prepare_replay_wait(&mut self, id: ReplayOperationId) -> Result<(), SolveAvailabilityError> {
        let transactional = self.route_journal.is_some();
        let context = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let before = context.replay_operation_undo.capacity();
        context.prepare_replay_ack(id, transactional)?;
        if context.replay_operation_undo.capacity() != before {
            if self.incoming_route_accounting_active { self.observe_typed_route_capacity(true)?; }
            else {
                #[cfg(test)]
                incoming_sample_trace::reason("candidate_prepare_replay_wait-replay-operation-undo-growth");
                self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            }
        }
        Ok(())
    }
    pub(super) fn candidate_context_step_replay_child(
        &mut self, id: ReplayOperationId, occurrence: &ConstraintOccurrenceId, cause: &CauseId,
    ) -> Result<ReplayChildStep, SolveAvailabilityError> {
        let transactional = self.route_journal.is_some();
        let operation = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.replay_operations.get(&id).ok_or_else(exhausted)?;
        match operation.waiting_child {
            ReplayChildWait::Idle => {
                if operation.queued != operation.consumed { return Err(exhausted()); }
                let item = operation.children.get(operation.consumed).copied().map(|relation| TypedWorkItem {
                    task: operation.task, relation: Some(relation),
                    replay_ack: Some(ReplayChildAck { operation: id, index: operation.consumed }),
                });
                if !self.typed_worklist.is_empty() { return Err(exhausted()); }
                self.candidate_prepare_replay_wait(id)?;
                let Some(item) = item else {
                    self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.acknowledge_replay(id, transactional);
                    return Ok(ReplayChildStep::NoChild);
                };
                let ack = item.replay_ack.unwrap();
                let index = self.start_typed_drain(item, occurrence, cause, None, None)?;
                let context = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                context.typed_drains[index].replay_destination = Some(ack);
                context.replay_operations.get_mut(&id).unwrap().waiting_child = ReplayChildWait::Running { ack, drain_index: index };
                Ok(ReplayChildStep::More)
            }
            ReplayChildWait::Running { ack, drain_index } => {
                let next = ack.index.checked_add(1).ok_or_else(exhausted)?;
                if ack.operation != id || operation.queued != next
                    || (operation.consumed != ack.index && operation.consumed != next) { return Err(exhausted()); }
                let frame = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.typed_drains.get(drain_index).ok_or_else(exhausted)?;
                if frame.replay_destination != Some(ack) || &frame.occurrence != occurrence || &frame.cause != cause { return Err(exhausted()); }
                // The terminal owner publishes Ready before removing F.
                let _ = self.step_typed_drain(drain_index)?;
                Ok(ReplayChildStep::More)
            }
            ReplayChildWait::Ready { ack, drain_index, completion: _ } => {
                let next = ack.index.checked_add(1).ok_or_else(exhausted)?;
                if ack.operation != id || operation.consumed != next || operation.queued != next
                    || self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.typed_drains.len() != drain_index {
                    return Err(exhausted());
                }
                self.candidate_prepare_replay_wait(id)?;
                let context = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                context.replay_operations.get_mut(&id).unwrap().waiting_child = ReplayChildWait::Idle;
                if !transactional { context.retire_replay_candidate(id); }
                Ok(ReplayChildStep::Delivered)
            }
        }
    }
    pub(super) fn candidate_context_consume_replay_child(
        &mut self, id: ReplayOperationId,
        provenance: Option<(&ConstraintOccurrenceId, &CauseId)>,
    ) -> Result<bool, SolveAvailabilityError> {
        if let Some((occurrence, cause)) = provenance {
            let graph = self.candidate_graph.as_ref().unwrap();
            let frame_count = graph.intrusion.effect_algebra.context.typed_drains.len();
            let previous_processing = graph.intrusion.effect_algebra.processing;
            let previous_relation = graph.intrusion.effect_algebra.context.processing;
            let result = (|| {
                loop {
                    match self.candidate_context_step_replay_child(id, occurrence, cause)? {
                        ReplayChildStep::More => {}
                        ReplayChildStep::Delivered => return Ok(true),
                        ReplayChildStep::NoChild => return Ok(false),
                    }
                }
            })();
            if result.is_err() {
                let context = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                if context.typed_drains.len() > frame_count {
                    context.typed_drains.truncate(frame_count);
                    context.replay_operations.get_mut(&id).ok_or_else(exhausted)?.waiting_child = ReplayChildWait::Idle;
                }
                self.candidate_processing(previous_processing);
                self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = previous_relation;
            }
            return result;
        }
        let state = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        let operation = state.replay_operations.get(&id).ok_or_else(exhausted)?;
        if operation.waiting_child != ReplayChildWait::Idle { return Err(exhausted()); }
        let item = state.replay_operation_queue_next(id)?;
        let transactional = self.route_journal.is_some();
        if item.is_none() && operation.consumed < operation.children.len() {
            // Every child is queued, but its typed drain still owns completion.
            return Ok(false);
        }
        if let Some(item) = item {
            self.enqueue_item(item, false)?;
        } else {
            self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.prepare_replay_ack(id, transactional)?;
            self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.acknowledge_replay(id, transactional);
        }
        Ok(item.is_some())
    }
    pub(super) fn candidate_context_replay_returned(&self, id: ReplayOperationId) -> Result<bool, SolveAvailabilityError> {
        let operation = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.replay_operations.get(&id).ok_or_else(exhausted)?;
        Ok(operation.waiting_child == ReplayChildWait::Idle && operation.retired)
    }
    pub(super) fn candidate_context_drive_replay(
        &mut self, id: ReplayOperationId,
        provenance: Option<(&ConstraintOccurrenceId, &CauseId)>,
    ) -> Result<ReplayDriveOutcome, SolveAvailabilityError> {
        loop {
            let transferred = self.candidate_context_consume_replay_child(id, provenance)?;
            let operation = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.replay_operations.get(&id);
            if operation.is_none_or(|operation| operation.retired && operation.waiting_child == ReplayChildWait::Idle) { return Ok(ReplayDriveOutcome::Complete); }
            if !transferred {
                // Only the outer worklist consumer can complete queued children.
                if provenance.is_some() { return Err(exhausted()); }
                return Ok(ReplayDriveOutcome::Queued);
            }
        }
    }
    pub(super) fn candidate_context_canonicalize_bounds(&mut self) -> Result<(), SolveAvailabilityError> {
        // Representative changes affect third-owner incidence as well as the
        // merged row's outgoing bounds. Preserve the original fiber/provenance
        // and transport it to the canonical bound key before any replay.
        let count = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_keys.len();
        for index in 0..count {
            let (from, parent, _) = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_keys[index];
            let to = BoundKey(self.canonical_extrusion(from.0), from.1, self.canonical_extrusion(from.2));
            if to != from {
                self.candidate_context_transport_witness(parent, to, 0, Some(TransportWitness { from, to, reason: TransportReason::EqualityCanonicalization }))?;
                let pair = self.candidate_context_pair(bound_pair(to));
                let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                let child = state.relation_with_scoped(pair, state.post_check_context(parent), state.relations[parent.0 as usize].key.sources, state.scoped_flow(parent)?)?;
                // Equality transport remains within this owner, unlike fresh
                // scheme uses: conflicts must retain the original derivation.
                state.dependency(Dependency::Derived { child, parent })?;
            }
        }
        Ok(())
    }
    #[cfg(test)]
    pub(super) fn candidate_context_fresh_transport(
        &mut self, parent: RelationId, to: BoundKey, use_origin: usize,
        context: ContextId, from: BoundKey,
    ) -> Result<RelationId, SolveAvailabilityError> {
        self.candidate_context_fresh_transport_scoped(parent, to, use_origin, context, from, None)
    }
    pub(super) fn candidate_context_reuse_fresh_relation(
        &self, bound: BoundKey, antecedent: EvidenceSnapshotId, source_bound: BoundKey,
        use_origin: usize, relation: RelationId,
    ) -> Result<RelationId, SolveAvailabilityError> {
        let pair = self.candidate_context_pair(bound_pair(bound));
        let state = &self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.effect_algebra.context;
        let snapshot = state.evidence.snapshots.get(antecedent.0).ok_or_else(exhausted)?;
        let parent = snapshot.relation.ok_or(SolveAvailabilityError::ReceiptMismatch)?;
        let retained = state.relations.get(relation.0 as usize).ok_or_else(exhausted)?;
        if snapshot.source_bound != source_bound || self.candidate_context_pair(retained.key.pair) != pair
            || use_origin == 0
            || !state.dependency_keys.contains(&Dependency::Transport {
                child: relation, parent, use_origin,
                witness: Some(TransportWitness { from: source_bound, to: bound, reason: TransportReason::FreshUse }),
            }) {
            return Err(SolveAvailabilityError::ReceiptMismatch);
        }
        Ok(relation)
    }
    pub(super) fn candidate_context_fresh_transport_scoped(
        &mut self, parent: RelationId, to: BoundKey, use_origin: usize,
        context: ContextId, from: BoundKey, scoped: Option<ScopedFlow>,
    ) -> Result<RelationId, SolveAvailabilityError> {
        let scoped_enabled = self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.effect_algebra.context.scoped_enabled;
        let to = if scoped_enabled { BoundKey(self.canonical_extrusion(to.0), to.1, self.canonical_extrusion(to.2)) } else { to };
        let pair = self.candidate_context_pair(bound_pair(to));
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let flow = if state.scoped_enabled { scoped.ok_or(SolveAvailabilityError::ReceiptMismatch)? } else { ScopedFlow::default() };
        let child = state.relation_with_scoped(pair, context, state.relations[parent.0 as usize].key.sources, flow)?;
        state.dependency(Dependency::Transport { child, parent, use_origin, witness: Some(TransportWitness { from, to, reason: TransportReason::FreshUse }) })?;
        state.attach(to, child)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(child)
    }
    pub(super) fn candidate_context_fresh_bundle(
        &mut self, child: RelationId, bundle: AttachmentBundleId,
    ) -> Result<(), SolveAvailabilityError> {
        self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.bundle_link(child, bundle)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
    #[allow(dead_code, reason = "equality bundle transport is distinct from fresh-use reconstruction")]
    pub(super) fn candidate_context_transport_bundle(
        &mut self, parent: RelationId, to: BoundKey, bundle: AttachmentBundleId,
    ) -> Result<(), SolveAvailabilityError> {
        let pair = self.candidate_context_pair(bound_pair(to));
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let child = state.relation_with_scoped(pair, state.post_check_context(parent), state.relations[parent.0 as usize].key.sources, state.scoped_flow(parent)?)?;
        state.bundle_link(child, bundle)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
    #[cfg(test)]
    pub(super) fn candidate_context_transport(
        &mut self,
        parent: RelationId,
        to: BoundKey,
        use_origin: usize,
    ) -> Result<(), SolveAvailabilityError> {
        self.candidate_context_transport_witness(parent, to, use_origin, None)
    }
    pub(super) fn candidate_context_transport_witness_with_evidence(
        &mut self, parent: RelationId, to: BoundKey, use_origin: usize, witness: TransportWitness,
    ) -> Result<(RelationId, FiberTransformId), SolveAvailabilityError> {
        if to != witness.to { return Err(exhausted()); }
        let pair = self.candidate_context_pair(bound_pair(to));
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let snapshot = state.evidence.snapshot(witness.from, Some(parent));
        let antecedent = state.evidence.intern_snapshot(snapshot)?;
        let scoped = state.transported_scoped(parent, witness)?;
        let child = state.relation_with_scoped(pair, state.post_check_context(parent), state.relations[parent.0 as usize].key.sources, scoped)?;
        state.dependency(Dependency::Transport { child, parent, use_origin, witness: Some(witness) })?;
        let transform = state.evidence.transform(antecedent, witness, parent, child)?;
        state.attach(to, child)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok((child, transform))
    }
    pub(super) fn candidate_context_transport_witness(
        &mut self, parent: RelationId, to: BoundKey, use_origin: usize,
        witness: Option<TransportWitness>,
    ) -> Result<(), SolveAvailabilityError> {
        if let Some(witness) = witness {
            return self.candidate_context_transport_witness_with_evidence(parent, to, use_origin, witness).map(|_| ());
        }
        let pair = self.candidate_context_pair(bound_pair(to));
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let child = state.relation_with_scoped(pair, state.post_check_context(parent), state.relations[parent.0 as usize].key.sources, state.scoped_flow(parent)?)?;
        state.dependency(Dependency::Transport {
            child,
            parent,
            use_origin,
            witness,
        })?;
        state.attach(to, child)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
}
#[cfg(test)]
#[path = "candidate_context_tests.rs"]
mod tests;
