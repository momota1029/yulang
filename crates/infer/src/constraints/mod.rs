//! subtype constraint を即時伝播する machine。
//!
//! lowering は `PosId <: NegId` を machine に渡すだけで、上下界 table の更新と再伝播はここが持つ。
//! 伝播で増えた下界・上界は event として外へ出し、selection や SCC の別 machine が反応できる。
//!
//! effect row の subtraction は `stack(T, @S)` と weighted edge として表す。
//! subtract fact table は注釈・データ宣言由来の stack id を記録し、generalize の pruning 入力にする。

mod directed_weight;
#[allow(dead_code)]
pub(crate) mod explain;
#[cfg(test)]
mod logical_proof_snapshot;
mod machine;
pub(crate) mod mutation;
pub(crate) mod ocast_eligibility;
mod portable_explain;
#[allow(
    dead_code,
    reason = "CPK-1 establishes the proof seam before CPK-2 connects production events"
)]
pub(crate) mod proof;
#[cfg(test)]
mod proof_inventory;
mod replay_soak;
mod row_effect;
#[cfg(test)]
mod semantic_execution_snapshot;
#[cfg(test)]
mod tests;
mod timing;
mod trace;

#[cfg(test)]
use std::cell::Cell;
use std::cell::RefCell;
use std::collections::{VecDeque, hash_map::Entry};

use directed_weight::{
    DirectedWeights, LeftConstraintWeight as DirectedLeftConstraintWeight, RightStackWeight,
};
use poly::expr::DefId;
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, StackWeight, SubtractId, Subtractability,
    TypeArena, TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};

pub(crate) use proof::ProofFailure;
use replay_soak::ensure_replay_soak_telemetry_header;
pub(crate) use replay_soak::{
    record_proof_terminal_failure,
};
#[cfg(test)]
pub(crate) use replay_soak::{
    ReplaySoakEventOrigin, capture_replay_soak_test_events,
    with_intentional_replay_soak_test_injection,
};

#[cfg(test)]
pub(crate) use mutation::MethodRoleMutation;
pub(crate) use mutation::{
    DependencyKey, InvalidateAllReason, MethodRoleMutationActivation, MethodRoleMutationOutbox,
    MethodRoleMutationSubscriptions, MutationGeneration,
};

pub use portable_explain::{
    DiagnosticExplanationCompleteness, DiagnosticExplanationTruncationReason,
    DiagnosticSubtypeExplanation, DiagnosticTypeCause, DiagnosticTypeCauseRole,
    PortableExplanationBudget, explain_portable_subtype,
};
pub use timing::{
    BodyRequirementOriginCoverage, BoundDispositionCoverage, ConstraintOriginCoverage,
    ConstraintTiming, GeneralizedSchemeCoverage, ReplayDerivationCoverage,
    ReplayDerivationStorageMetrics, ReplayDuplicateProfile, ReplayFrontierShadowMetrics,
    ReplayRoutingShadowMetrics, ReplayWeightedRoutingShadowMetrics, RowDerivationCoverage,
    SchemeInstantiationCoverage, StableRecordCoverage, StructuralDerivationCoverage,
};
use trace::{
    ConstraintDrainTrace, trace_bound_replay_progress, trace_bound_replay_start, trace_var_bounds,
};

#[cfg(test)]
#[allow(
    unused_imports,
    reason = "CPK-0b fixtures consume this shared snapshot type incrementally"
)]
pub(crate) use logical_proof_snapshot::LogicalProofSnapshot;
#[cfg(test)]
pub(crate) use machine::global_alpha_census::{
    GlobalAlphaConsequenceCensusSnapshot, capture_global_alpha_consequence_census,
};
#[cfg(test)]
#[allow(
    unused_imports,
    reason = "CPK-0a exposes one shared baseline vocabulary to later fixture slices"
)]
pub(crate) use semantic_execution_snapshot::{
    SccExecutionSnapshot, SemanticExecutionSnapshot, SemanticOutputSnapshot,
    with_semantic_execution_snapshot_capture_for_new_machines,
};

/// subtype constraint の伝播 machine。
///
/// `TypeArena`、未処理 queue、変数ごとの上下界、subtract fact、outbox event をまとめて所有する。
/// public entrypoint は work を queue に積んだあと `drain()` する。将来 lowering と並列化する場合も、
/// この queue / event 境界を通信点にできる。
pub struct ConstraintMachine {
    types: TypeArena,
    queue: VecDeque<ConstraintWork>,
    bounds: TypeBounds,
    #[allow(dead_code, reason = "CPK-6a promotes storage before writer cutover")]
    proof_store: proof::ProofOccurrenceStore,
    proof_terminal_failure: RefCell<Option<proof::ProofFailure>>,
    var_adjacency: FxHashMap<TypeVar, FxHashMap<TypeVar, usize>>,
    subtracts: SubtractTable,
    levels: TypeLevels,
    next_internal_type_var: u32,
    row_residuals: FxHashMap<RowResidualKey, TypeVar>,
    row_residual_record_ids: FxHashMap<RowResidualKey, RowResidualRecordId>,
    row_residual_records: Vec<RowResidualRecord>,
    unweighted_row_reductions_by_source: FxHashMap<TypeVar, Vec<UnweightedRowReductionRecordId>>,
    unweighted_row_reduction_owners_by_upper:
        FxHashMap<BoundRecordId, Vec<UnweightedRowReductionOwner>>,
    unweighted_row_reduction_records: Vec<UnweightedRowReductionRecord>,
    row_derivations: Vec<RowDerivation>,
    row_derivation_index: FxHashMap<RowDerivation, RowDerivationId>,
    bound_dispositions: Vec<BoundDispositionRecord>,
    declared_subtracts: FxHashMap<SubtractId, Vec<OriginId>>,
    effect_family_paths: FxHashSet<Vec<String>>,
    row_tail_vars: FxHashSet<TypeVar>,
    pre_pop_effect_families: FxHashMap<TypeVar, Vec<ConstraintEffectFamily>>,
    lower_filters: FxHashMap<TypeVar, FxHashSet<Subtractability>>,
    lower_filter_record_ids: FxHashMap<(TypeVar, Subtractability), LowerFilterRecordId>,
    lower_filter_records: Vec<LowerFilterRecord>,
    effect_filter_violations: FxHashSet<EffectFilterViolationKey>,
    canonical_constraints: FxHashMap<SubtypeConstraintKey, ConstraintRecordId>,
    constraint_records: Vec<ConstraintRecord>,
    replay_drop_records: Vec<ReplayDropRecord>,
    replay_drop_index: FxHashMap<ReplayDropRecord, ReplayDropRecordId>,
    replay_derivation_budget: ReplayDerivationBudget,
    replay_derivation_storage: ReplayDerivationStorage,
    origins: Vec<OriginRecord>,
    source_boundaries: Vec<SourceBoundaryRecord>,
    generalized_schemes: Vec<GeneralizedSchemeRecord>,
    generalized_witnesses: Vec<GeneralizedSchemeWitness>,
    scheme_instantiations: Vec<SchemeInstantiationRecord>,
    scheme_instantiation_index: FxHashMap<SchemeInstantiationKey, SchemeInstantiationId>,
    events: Vec<ConstraintEvent>,
    method_role_mutations: MethodRoleMutationOutbox,
    timing: ConstraintTiming,
    epoch: ConstraintEpoch,
    provenance_epoch: ProvenanceEpoch,
    role_solve_supplemental_epoch: RoleSolveSupplementalEpoch,
    replay_frontier_shadow: Option<ReplayFrontierShadow>,
    replay_routing_shadow: Option<RefCell<ReplayRoutingShadow>>,
    #[cfg(test)]
    cdm_lower_delta_census: CdmLowerDeltaCensus,
    #[cfg(test)]
    semantic_execution_trace: Option<RefCell<semantic_execution_snapshot::SemanticExecutionTrace>>,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct CdmLowerDeltaCensus {
    bootstrap_scans: usize,
    bulk_scans: usize,
    parent_batches: usize,
    constraint_bound_events: usize,
    other_bound_events: usize,
    replay_carrier_events: usize,
    structural_carrier_events: usize,
    row_carrier_events: usize,
    evidence_carrier_events: usize,
    other_carrier_events: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintEpoch(u64);

impl ConstraintEpoch {
    pub fn as_u64(self) -> u64 {
        self.0
    }

    /// Whether equality with this value can prove that no observed mutation occurred.
    ///
    /// The counter saturates instead of wrapping. Once saturated, later mutations cannot be
    /// distinguished, so correctness-sensitive reuse must treat the epoch as unavailable.
    pub fn can_witness_unchanged_state(self) -> bool {
        self.0 != u64::MAX
    }

    fn bump(&mut self) {
        self.0 = self.0.saturating_add(1);
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProvenanceEpoch(u64);

impl ProvenanceEpoch {
    pub fn as_u64(self) -> u64 {
        self.0
    }

    pub fn can_witness_unchanged_state(self) -> bool {
        self.0 != u64::MAX
    }

    fn bump(&mut self) {
        self.0 = self.0.saturating_add(1);
    }
}

/// Supplemental witness for role-solver inputs intentionally omitted from `ConstraintEpoch`.
///
/// This counter has no replay, lifecycle-audit, or cache semantics. A role-solve snapshot must
/// compare it together with `ConstraintEpoch`; neither counter is complete by itself.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RoleSolveSupplementalEpoch(u64);

impl RoleSolveSupplementalEpoch {
    pub fn as_u64(self) -> u64 {
        self.0
    }

    pub fn can_witness_unchanged_state(self) -> bool {
        self.0 != u64::MAX
    }

    fn bump(&mut self) {
        self.0 = self.0.saturating_add(1);
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// let / lambda nesting の深さ。
///
/// root level より深い変数が浅い変数の bound に入ると、bound 登録前の extrusion で浅い level へ
/// 老化させる。未登録の手書き `TypeVar` は root として扱う。
pub struct TypeLevel(u32);

impl TypeLevel {
    pub fn root() -> Self {
        Self(0)
    }

    pub fn secondary() -> Self {
        Self(u32::MAX)
    }

    pub fn child(self) -> Self {
        Self(self.0.saturating_add(1))
    }

    pub fn depth(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct TypeLevels {
    vars: Vec<Option<TypeLevel>>,
    births: Vec<Option<TypeLevel>>,
}

impl TypeLevels {
    fn new() -> Self {
        Self::default()
    }

    fn register_recording_change(&mut self, var: TypeVar, level: TypeLevel) -> bool {
        let index = var.0 as usize;
        ensure_slot(&mut self.vars, index);
        ensure_slot(&mut self.births, index);
        let current_inserted = self.vars[index].is_none();
        let birth_inserted = self.births[index].is_none();
        self.vars[index].get_or_insert(level);
        self.births[index].get_or_insert(level);
        current_inserted || birth_inserted
    }

    fn level_of(&self, var: TypeVar) -> TypeLevel {
        self.vars
            .get(var.0 as usize)
            .and_then(|level| *level)
            .unwrap_or_else(TypeLevel::root)
    }

    fn birth_level_of(&self, var: TypeVar) -> TypeLevel {
        self.births
            .get(var.0 as usize)
            .and_then(|level| *level)
            .unwrap_or_else(TypeLevel::root)
    }

    fn lower_to(&mut self, var: TypeVar, target: TypeLevel) -> bool {
        let index = var.0 as usize;
        ensure_slot(&mut self.vars, index);
        let level = self.vars[index].get_or_insert_with(TypeLevel::root);
        if target < *level {
            *level = target;
            return true;
        }
        false
    }
}

#[derive(Debug)]
struct ExtrudeCtx {
    target: TypeLevel,
    visited: FxHashSet<TypeVar>,
    visited_pos: FxHashSet<PosId>,
    visited_neg: FxHashSet<NegId>,
    visited_neu: FxHashSet<NeuId>,
}

impl ExtrudeCtx {
    fn new(target: TypeLevel) -> Self {
        Self {
            target,
            visited: FxHashSet::default(),
            visited_pos: FxHashSet::default(),
            visited_neg: FxHashSet::default(),
            visited_neu: FxHashSet::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// constraint machine から外側へ出る通知。
///
/// selection は lower bound の追加を見て pending site を起こす。SCC や diagnostics も、
/// constraint core に直接入り込まず event を介して反応する。
pub enum ConstraintEvent {
    LowerBoundAdded {
        record: BoundRecordId,
        producer: Option<ConstraintRecordId>,
        var: TypeVar,
        bound: PosId,
        weights: ConstraintWeights,
    },
    UpperBoundAdded {
        record: BoundRecordId,
        producer: Option<ConstraintRecordId>,
        var: TypeVar,
        bound: NegId,
        weights: ConstraintWeights,
    },
    SubtractFactAdded {
        record: SubtractFactRecordId,
        effect: TypeVar,
        id: SubtractId,
    },
    NominalCastNeeded {
        producer: ConstraintRecordId,
        lower: PosId,
        upper: NegId,
        source: Vec<String>,
        target: Vec<String>,
        weights: ConstraintWeights,
    },
    EffectFilterViolation {
        effect: Option<Vec<String>>,
        filter: Subtractability,
    },
    /// A nominal constructor must be checked against struct projection metadata outside the
    /// constraint core.
    NominalRecordShapeObligation(NominalRecordShapeObligation),
    /// A fixed concrete-head relation that cannot satisfy the subtype matrix.
    ///
    /// STF-C only defines this event contract. `step_subtype` starts producing it in STF-D/E.
    UnsatisfiedSubtypeShape(UnsatisfiedSubtypeShapeEvent),
}

/// Structured summary of a fixed concrete subtype head.
///
/// Field and tag vectors carry names only; nested mismatches remain ordinary subtype obligations.
/// This data stays presentation-neutral so the constraint machine never constructs formatter text.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConcreteSubtypeHead {
    Constructor(Vec<String>),
    Function,
    Tuple(usize),
    Record(Vec<String>),
    PolyVariant(Vec<String>),
    EffectRow,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsatisfiedSubtypeShapeEvent {
    pub actual: ConcreteSubtypeHead,
    pub expected: ConcreteSubtypeHead,
    pub producer: ConstraintRecordId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NominalRecordShapeObligation {
    pub producer: ConstraintRecordId,
    pub lower: PosId,
    pub upper: NegId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ConstraintWork {
    Subtype(ConstraintRecordId),
    SubtractFact(QueuedSubtractFact),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EnqueueSubtypeResult {
    Enqueued,
    Duplicate,
    Trivial,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct QueuedSubtractFact {
    effect: TypeVar,
    fact: SubtractFact,
    derivation: SubtractFactDerivation,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RowResidualKey {
    source: TypeVar,
    retained_families: Vec<EffectFamily>,
    weight: LeftConstraintWeight,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct UnweightedRowReductionRecordId(u32);

#[derive(Debug, Clone, PartialEq, Eq)]
struct UnweightedRowReductionRecord {
    source: TypeVar,
    producer_constraint: Option<ConstraintRecordId>,
    original_items: Vec<NegId>,
    original_tail: NegId,
    original_upper: NegId,
    consumed_items: Vec<NegId>,
    remaining_items: Vec<NegId>,
    current_reduced_upper: UnweightedRowReductionMaterialization,
    processed_lower_records: FxHashSet<BoundRecordId>,
    provenance_head: RowDerivationId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct UnweightedRowReductionMaterialization {
    endpoint: NegId,
    record: BoundRecordId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct UnweightedRowReductionOwner {
    state: UnweightedRowReductionRecordId,
    derivation: BoundDerivation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct UnweightedRowReductionReplayRoute {
    upper: NegId,
    upper_record: BoundRecordId,
    provenance: RowDerivationId,
    claim: Option<UpperReplayClaimId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct UnweightedRowReductionRegistration {
    state: UnweightedRowReductionRecordId,
    root_claim: Option<UpperReplayClaimId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UpperReplayClaimId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UpperReplayClaimKind {
    Direct,
    Reduced(UnweightedRowReductionRecordId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UpperReplayClaimLineage {
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

impl UpperReplayClaimLineage {
    fn depth(self) -> u32 {
        match self {
            Self::Original => 0,
            Self::ReplayConstraint { depth, .. }
            | Self::ReplayEvidence { depth, .. }
            | Self::StructuralConstraint { depth, .. }
            | Self::ReductionRouteConstraint { depth, .. } => depth,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct UpperReplayClaimRegistration {
    claim: UpperReplayClaimId,
    scheme_projection_mutation: SchemeProjectionMutation,
}

impl UpperReplayClaimRegistration {
    fn new(claim: UpperReplayClaimId) -> Self {
        Self {
            claim,
            scheme_projection_mutation: SchemeProjectionMutation::None,
        }
    }
}

/// A CPK-decided projection support transaction and its publication target.
#[derive(Debug, Clone, PartialEq, Eq)]
enum SchemeProjectionMutation {
    None,
    ProofsChanged {
        lower_record: BoundRecordId,
        prepared: proof::PreparedProjectionSupportMutation,
    },
}

enum SchemeProjectionPublicationIntent {
    None,
    MetadataOnly,
    OwnersChanged(FxHashSet<TypeVar>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ReplayClaimParentSide {
    Lower,
    Upper,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct SideTaggedReplayClaim {
    claim: UpperReplayClaimId,
    parent_side: ReplayClaimParentSide,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ClaimQualifiedParent {
    ReplayConstraint {
        parent_claim: UpperReplayClaimId,
        parent_side: ReplayClaimParentSide,
        replay: BinaryReplayDerivation,
    },
    StructuralConstraint {
        parent_claim: UpperReplayClaimId,
        derivation: StructuralDerivation,
    },
    ReductionRouteConstraint {
        parent_claim: UpperReplayClaimId,
        derivation: RowDerivationId,
    },
}

impl ClaimQualifiedParent {
    fn parent_claim(self) -> UpperReplayClaimId {
        match self {
            Self::ReplayConstraint { parent_claim, .. }
            | Self::StructuralConstraint { parent_claim, .. }
            | Self::ReductionRouteConstraint { parent_claim, .. } => parent_claim,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProjectionProofCarrier {
    ConstraintOrigin {
        constraint: ConstraintRecordId,
        origin: OriginId,
    },
    StructuralConstraint {
        result: ConstraintRecordId,
        derivation: StructuralDerivation,
    },
    ReplayConstraint {
        result: ConstraintRecordId,
        derivation: BinaryReplayDerivation,
    },
    RowConstraint {
        result: ConstraintRecordId,
        derivation: RowDerivationId,
    },
    SchemeInstantiationConstraint {
        result: ConstraintRecordId,
        source_witness: GeneralizedSchemeWitnessId,
    },
    Origin(OriginId),
    ReplayEvidence(BinaryReplayDerivation),
    Row(RowDerivationId),
    SchemeInstantiation(GeneralizedSchemeWitnessId),
    Incomplete,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum SchemeProjectionProofSupport {
    Claimed(UpperReplayClaimId),
    Independent(ProjectionProofCarrier),
}

#[allow(dead_code, reason = "RCPF-D3b-0b wires the permutation oracle")]
#[rustfmt::skip]
mod canonical_projection_key {
    use super::*;
    use std::cmp::Ordering;

    type CarrierKey = (u8, [u32; 6]);

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(super) enum Key {
        Claimed(UpperReplayClaimId),
        Independent(ProjectionProofCarrier),
    }

    pub(super) fn carrier_cmp(
        left: &ProjectionProofCarrier,
        right: &ProjectionProofCarrier,
    ) -> Ordering {
        carrier_key(*left).cmp(&carrier_key(*right))
    }

    pub(super) fn cmp(left: &Key, right: &Key) -> Ordering {
        match (left, right) {
            (Key::Claimed(left), Key::Claimed(right)) => left.cmp(right),
            (Key::Claimed(_), Key::Independent(_)) => Ordering::Less,
            (Key::Independent(_), Key::Claimed(_)) => Ordering::Greater,
            (Key::Independent(left), Key::Independent(right)) => carrier_cmp(left, right),
        }
    }

    pub(super) fn normalize_clone(keys: &[Key]) -> Vec<Key> {
        let mut normalized = keys.to_vec();
        normalized.sort_by(cmp);
        normalized
    }

    fn carrier_key(carrier: ProjectionProofCarrier) -> CarrierKey {
        match carrier {
            ProjectionProofCarrier::ConstraintOrigin { constraint, origin } => (0, [constraint.0, origin.0, 0, 0, 0, 0]),
            ProjectionProofCarrier::StructuralConstraint { result, derivation } => {
                let rule = structural_rule_key(derivation.rule);
                (1, [result.0, derivation.parent.0, rule[0], rule[1], rule[2], rule[3]])
            }
            ProjectionProofCarrier::ReplayConstraint { result, derivation } => (2, [result.0, derivation.pivot.0, derivation.lower.0, derivation.upper.0, replay_rule_rank(derivation.rule), 0]),
            ProjectionProofCarrier::RowConstraint { result, derivation } => (3, [result.0, derivation.0, 0, 0, 0, 0]),
            ProjectionProofCarrier::SchemeInstantiationConstraint { result, source_witness } => (4, [result.0, source_witness.0, 0, 0, 0, 0]),
            ProjectionProofCarrier::Origin(origin) => (5, [origin.0, 0, 0, 0, 0, 0]),
            ProjectionProofCarrier::ReplayEvidence(derivation) => (6, [derivation.pivot.0, derivation.lower.0, derivation.upper.0, replay_rule_rank(derivation.rule), 0, 0]),
            ProjectionProofCarrier::Row(derivation) => (7, [derivation.0, 0, 0, 0, 0, 0]),
            ProjectionProofCarrier::SchemeInstantiation(source_witness) => (8, [source_witness.0, 0, 0, 0, 0, 0]),
            ProjectionProofCarrier::Incomplete => (9, [0; 6]),
        }
    }

    fn structural_rule_key(rule: StructuralDerivationRule) -> [u32; 4] {
        use StructuralDerivationRule::*;
        match rule {
            LowerStackNormalization => [0, 0, 0, 0],
            LowerNonSubtractNormalization => [1, 0, 0, 0],
            UpperStackNormalization => [2, 0, 0, 0],
            UnionBranch { branch } => [3, branch.0, 0, 0],
            IntersectionBranch { branch } => [4, branch.0, 0, 0],
            FunctionArgument => [5, 0, 0, 0],
            FunctionArgumentEffect { pure_passthrough } => [6, pure_passthrough as u32, 0, 0],
            FunctionReturnEffect => [7, 0, 0, 0],
            FunctionReturn => [8, 0, 0, 0],
            ConstructorArgument { index, direction } => [9, index.0, direction_rank(direction), 0],
            TupleElement { index } => [10, index.0, 0, 0],
            RecordField { index } => [11, index.0, 0, 0],
            RecordSpreadField { spread, index } => [12, spread_rank(spread), index.0, 0],
            RecordSpreadTail { spread, index } => [13, spread_rank(spread), index.0, 0],
            VariantPayload { variant_index, payload_index } => [14, variant_index.0, payload_index.0, 0],
            RowItem { index, route } => [15, index.0, row_route_rank(route), 0],
            RowItemArgument { item_index, argument_index, direction } => [16, item_index.0, argument_index.0, direction_rank(direction)],
        }
    }

    fn replay_rule_rank(rule: ReplayRule) -> u32 {
        match rule { ReplayRule::LowerBoundAdded => 0, ReplayRule::UpperBoundAdded => 1 }
    }

    fn direction_rank(direction: InvariantDirection) -> u32 {
        match direction { InvariantDirection::LowerToUpper => 0, InvariantDirection::UpperToLower => 1 }
    }

    fn spread_rank(spread: RecordSpreadKind) -> u32 {
        match spread { RecordSpreadKind::Head => 0, RecordSpreadKind::Tail => 1 }
    }

    fn row_route_rank(route: RowItemRoute) -> u32 {
        match route {
            RowItemRoute::Matched => 0,
            RowItemRoute::DirectToUpperTail => 1,
            RowItemRoute::MarkerAggregateToUpperTail => 2,
            RowItemRoute::VariableToRemainingRow => 3,
            RowItemRoute::UpperTailToMarkerItems => 4,
            RowItemRoute::UpperTailToDirectItems => 5,
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        fn carriers() -> [ProjectionProofCarrier; 10] {
            let replay = |seed| BinaryReplayDerivation {
                pivot: TypeVar(seed), lower: BoundRecordId(seed + 1), upper: BoundRecordId(seed + 2),
                rule: ReplayRule::LowerBoundAdded,
            };
            [
                ProjectionProofCarrier::ConstraintOrigin { constraint: ConstraintRecordId(1), origin: OriginId(2) },
                ProjectionProofCarrier::StructuralConstraint {
                    result: ConstraintRecordId(3), derivation: StructuralDerivation {
                        parent: ConstraintRecordId(4), rule: StructuralDerivationRule::FunctionArgument,
                    }
                },
                ProjectionProofCarrier::ReplayConstraint { result: ConstraintRecordId(5), derivation: replay(6) },
                ProjectionProofCarrier::RowConstraint { result: ConstraintRecordId(9), derivation: RowDerivationId(10) },
                ProjectionProofCarrier::SchemeInstantiationConstraint { result: ConstraintRecordId(11), source_witness: GeneralizedSchemeWitnessId(12) },
                ProjectionProofCarrier::Origin(OriginId(13)),
                ProjectionProofCarrier::ReplayEvidence(replay(14)),
                ProjectionProofCarrier::Row(RowDerivationId(17)),
                ProjectionProofCarrier::SchemeInstantiation(GeneralizedSchemeWitnessId(18)),
                ProjectionProofCarrier::Incomplete,
            ]
        }

        #[test]
        fn canonical_cmp_is_equal_exactly_for_equal_keys() {
            let same_root = Key::Claimed(UpperReplayClaimId(7));
            let same_root_again = Key::Claimed(UpperReplayClaimId(7));
            let same_carrier = Key::Independent(carriers()[0]);
            let same_carrier_again = Key::Independent(carriers()[0]);
            assert_eq!(cmp(&same_root, &same_root_again), Ordering::Equal);
            assert_eq!(cmp(&same_carrier, &same_carrier_again), Ordering::Equal);
            let keys = [vec![Key::Claimed(UpperReplayClaimId(6)), same_root],
                carriers().into_iter().map(Key::Independent).collect()].concat();
            for left in &keys {
                for right in &keys {
                    assert_eq!(cmp(left, right) == Ordering::Equal, left == right);
                }
            }
        }

        #[test]
        fn canonical_cmp_is_transitive_across_categories_and_ranks() {
            let keys = [vec![Key::Claimed(UpperReplayClaimId(1)), Key::Claimed(UpperReplayClaimId(2))],
                carriers().into_iter().map(Key::Independent).collect()].concat();
            for left in &keys {
                for middle in &keys {
                    for right in &keys {
                        if cmp(left, middle) != Ordering::Greater && cmp(middle, right) != Ordering::Greater {
                            assert_ne!(cmp(left, right), Ordering::Greater);
                        }
                        assert_eq!(cmp(left, middle), cmp(middle, left).reverse());
                    }
                }
            }
        }

        #[test]
        fn every_claimed_root_sorts_before_every_independent_carrier() {
            for root in [UpperReplayClaimId(0), UpperReplayClaimId(u32::MAX)] {
                for carrier in carriers() {
                    assert_eq!(cmp(&Key::Claimed(root), &Key::Independent(carrier)), Ordering::Less);
                }
            }
        }

        #[test]
        fn carrier_rank_table_and_clone_normalizer_are_canonical() {
            let carriers = carriers();
            for (lower_rank, lower) in carriers.iter().enumerate() {
                for (higher_rank, higher) in carriers.iter().enumerate().skip(lower_rank + 1) {
                    assert_eq!(carrier_cmp(lower, higher), Ordering::Less, "rank {lower_rank} < {higher_rank}");
                }
            }
            let expected = carriers.map(Key::Independent).to_vec();
            let input = expected.iter().copied().rev().collect::<Vec<_>>();
            assert_eq!(normalize_clone(&input), expected);
            assert_ne!(input, expected, "normalization must leave its input clone untouched");
        }

        #[test]
        fn structural_rule_key_distinguishes_every_payload_kind() {
            use InvariantDirection::*;
            use RecordSpreadKind::*;
            use RowItemRoute::*;
            use StructuralDerivationRule::*;
            let rules = [
                (UnionBranch { branch: StructuralIndex(2) }, [3, 2, 0, 0]),
                (FunctionArgumentEffect { pure_passthrough: true }, [6, 1, 0, 0]),
                (ConstructorArgument { index: StructuralIndex(3), direction: UpperToLower }, [9, 3, 1, 0]),
                (RecordSpreadField { spread: Tail, index: StructuralIndex(4) }, [12, 1, 4, 0]),
                (VariantPayload { variant_index: StructuralIndex(5), payload_index: StructuralIndex(6) }, [14, 5, 6, 0]),
                (RowItem { index: StructuralIndex(7), route: UpperTailToDirectItems }, [15, 7, 5, 0]),
                (RowItemArgument { item_index: StructuralIndex(8), argument_index: StructuralIndex(9), direction: UpperToLower }, [16, 8, 9, 1]),
            ];
            for (rule, expected) in rules { assert_eq!(structural_rule_key(rule), expected); }
            let carrier = |rule| ProjectionProofCarrier::StructuralConstraint {
                result: ConstraintRecordId(20),
                derivation: StructuralDerivation { parent: ConstraintRecordId(21), rule },
            };
            let left = carrier(RowItem { index: StructuralIndex(7), route: Matched });
            let right = carrier(RowItem { index: StructuralIndex(7), route: UpperTailToDirectItems });
            assert_ne!(carrier_cmp(&left, &right), Ordering::Equal);
            assert_eq!(carrier_cmp(&left, &right), carrier_cmp(&right, &left).reverse());
        }
    }
}

mod canonical_upper_claim_key {
    use super::UpperReplayClaimId;
    use std::cmp::Ordering;

    pub(super) fn cmp(left: UpperReplayClaimId, right: UpperReplayClaimId) -> Ordering {
        left.cmp(&right)
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        const ROOTS: [UpperReplayClaimId; 5] = [
            UpperReplayClaimId(0),
            UpperReplayClaimId(1),
            UpperReplayClaimId(7),
            UpperReplayClaimId(u32::MAX - 1),
            UpperReplayClaimId(u32::MAX),
        ];

        #[test]
        fn canonical_upper_claim_cmp_is_reflexive() {
            for root in ROOTS {
                assert_eq!(cmp(root, root), Ordering::Equal);
            }
        }

        #[test]
        fn canonical_upper_claim_cmp_is_antisymmetric_and_identity_exact() {
            for left in ROOTS {
                for right in ROOTS {
                    assert_eq!(cmp(left, right), cmp(right, left).reverse());
                    assert_eq!(cmp(left, right) == Ordering::Equal, left == right);
                }
            }
        }

        #[test]
        fn canonical_upper_claim_cmp_is_transitive() {
            for left in ROOTS {
                for middle in ROOTS {
                    for right in ROOTS {
                        if cmp(left, middle) != Ordering::Greater
                            && cmp(middle, right) != Ordering::Greater
                        {
                            assert_ne!(cmp(left, right), Ordering::Greater);
                        }
                    }
                }
            }
        }

        #[test]
        fn canonical_upper_claim_cmp_is_the_total_ascending_root_order() {
            for (lower_index, lower) in ROOTS.into_iter().enumerate() {
                for higher in ROOTS.into_iter().skip(lower_index + 1) {
                    assert_eq!(cmp(lower, higher), Ordering::Less);
                    assert_eq!(cmp(higher, lower), Ordering::Greater);
                }
            }
        }
    }
}

#[cfg(test)]
std::thread_local! {
    static CANONICAL_PROJECTION_INSERTION_CENSUS: std::cell::Cell<(usize, usize)> =
        const { std::cell::Cell::new((0, 0)) };
    static CANONICAL_UPPER_CLAIM_INSERTION_CENSUS: std::cell::Cell<(usize, usize)> =
        const { std::cell::Cell::new((0, 0)) };
}

#[cfg(test)]
pub(crate) fn reset_canonical_projection_insertion_census() {
    CANONICAL_PROJECTION_INSERTION_CENSUS.set((0, 0));
}

#[cfg(test)]
pub(crate) fn canonical_projection_insertion_census() -> (usize, usize) {
    CANONICAL_PROJECTION_INSERTION_CENSUS.get()
}

#[cfg(test)]
fn record_canonical_projection_insertion_moves(moves: usize) {
    CANONICAL_PROJECTION_INSERTION_CENSUS.with(|census| {
        let (total, maximum) = census.get();
        census.set((total + moves, maximum.max(moves)));
    });
}

#[cfg(test)]
pub(crate) fn reset_canonical_upper_claim_insertion_census() {
    CANONICAL_UPPER_CLAIM_INSERTION_CENSUS.set((0, 0));
}

#[cfg(test)]
pub(crate) fn canonical_upper_claim_insertion_census() -> (usize, usize) {
    CANONICAL_UPPER_CLAIM_INSERTION_CENSUS.get()
}

#[cfg(test)]
fn record_canonical_upper_claim_insertion_moves(moves: usize) {
    CANONICAL_UPPER_CLAIM_INSERTION_CENSUS.with(|census| {
        let (total, maximum) = census.get();
        census.set((total + moves, maximum.max(moves)));
    });
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// A lazily evaluated proof input. DPN-A records these nodes; DPN-B will evaluate them.
pub(crate) enum ProofPremise {
    Record(BoundRecordId),
    Constraint(ConstraintRecordId),
    RootCoverage(UpperReplayClaimId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum DerivedUnaryCarrier {
    Structural(StructuralDerivation),
    ReductionRoute(RowDerivationId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// One OR-arm in a lower record's proof-composition ledger.
pub(crate) enum RecordProofClause {
    Standalone {
        support: SchemeProjectionProofSupport,
    },
    DerivedUnary {
        carrier: DerivedUnaryCarrier,
        premise: ProofPremise,
    },
    ReplayConjunction {
        carrier: BinaryReplayDerivation,
        lower_premise: BoundRecordId,
        upper_premise: BoundRecordId,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClaimedAttributionSource {
    CanonicalReplay,
    FlatRetained,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RecordProofClauseLinkAdmission {
    support: SchemeProjectionProofSupport,
    clause: RecordProofClause,
    claimed_attribution_source: Option<ClaimedAttributionSource>,
}

impl RecordProofClauseLinkAdmission {
    fn claimed(
        root: UpperReplayClaimId,
        clause: RecordProofClause,
        source: ClaimedAttributionSource,
    ) -> Self {
        Self {
            support: SchemeProjectionProofSupport::Claimed(root),
            clause,
            claimed_attribution_source: Some(source),
        }
    }

    fn independent(support: SchemeProjectionProofSupport, clause: RecordProofClause) -> Self {
        assert!(matches!(
            support,
            SchemeProjectionProofSupport::Independent(_)
        ));
        Self {
            support,
            clause,
            claimed_attribution_source: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct SchemeProjectionProof {
    pub(crate) lower_record: BoundRecordId,
    pub(crate) support: SchemeProjectionProofSupport,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SchemeProjectableLowerReason {
    Unclaimed,
    Qualified {
        uncovered_claims: Vec<UpperReplayClaimId>,
        independent_supports: Vec<ProjectionProofCarrier>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SchemeProjectableLower<'a> {
    pub(crate) record: BoundRecordId,
    pub(crate) bound: &'a WeightedLowerBound,
    pub(crate) reason: SchemeProjectableLowerReason,
}

/// Shares acyclic projection results across top-level queries over one fixed view.
///
/// A cycle cut can leave root-dependent `Done` results in the shared evaluator. Once a query cuts
/// a cycle, that evaluator is discarded and every remaining query uses its own fresh evaluator.
#[cfg(test)]
struct CpkTestProjectionEvaluationRound<'a> {
    machine: &'a ConstraintMachine,
    record_result_override: Option<(BoundRecordId, bool)>,
    shared: Option<proof::CpkProjectionEvaluator<'a>>,
    sharing_disabled: bool,
}

#[cfg(test)]
impl<'a> CpkTestProjectionEvaluationRound<'a> {
    fn new(machine: &'a ConstraintMachine) -> Self {
        Self::new_with_record_result_override(machine, None)
    }

    fn with_record_result_override(
        machine: &'a ConstraintMachine,
        record: BoundRecordId,
        result: bool,
    ) -> Self {
        Self::new_with_record_result_override(machine, Some((record, result)))
    }

    fn new_with_record_result_override(
        machine: &'a ConstraintMachine,
        record_result_override: Option<(BoundRecordId, bool)>,
    ) -> Self {
        Self {
            machine,
            record_result_override,
            shared: Some(Self::new_evaluator(machine, record_result_override)),
            sharing_disabled: false,
        }
    }

    fn eval_record(&mut self, record: BoundRecordId) -> bool {
        if self.sharing_disabled {
            return Self::new_evaluator(self.machine, self.record_result_override)
                .eval_record(record);
        }

        let shared = self
            .shared
            .as_mut()
            .expect("sharing remains available until a cycle cut disables it");
        let cuts_before = shared.cycle_cuts();
        let result = shared.eval_record(record);
        assert!(!shared.has_visiting_state(),
            "projection evaluation left a Visiting node after a top-level query");
        let cycle_was_cut = shared.cycle_cuts() != cuts_before;

        if cycle_was_cut {
            self.shared = None;
            self.sharing_disabled = true;
        }

        result
    }

    fn new_evaluator(
        machine: &'a ConstraintMachine,
        record_result_override: Option<(BoundRecordId, bool)>,
    ) -> proof::CpkProjectionEvaluator<'a> {
        let evaluator = proof::CpkProjectionEvaluator::new(machine, &machine.proof_store);
        let Some((record, result)) = record_result_override else {
            return evaluator;
        };
        evaluator.with_record_result_override(record, result)
    }
}

/// Publication-time projection evaluation over the CPK-authoritative snapshot.
///
/// RCPF's factored stores remain available to their direct structure tests, but publication
/// decisions and test evaluation rounds use the CPK-authoritative evaluator below.
struct CpkPublicationEvaluationRound<'a> {
    machine: &'a ConstraintMachine,
    record_result_override: Option<(BoundRecordId, bool)>,
    root_result_override: Option<(UpperReplayClaimId, bool)>,
    shared: Option<proof::CpkProjectionEvaluator<'a>>,
    sharing_disabled: bool,
}

impl<'a> CpkPublicationEvaluationRound<'a> {
    fn new(machine: &'a ConstraintMachine) -> Self {
        Self::new_with_overrides(machine, None, None)
    }

    fn with_record_result_override(
        machine: &'a ConstraintMachine,
        record: BoundRecordId,
        result: bool,
    ) -> Self {
        Self::new_with_overrides(machine, Some((record, result)), None)
    }

    fn with_root_result_override(
        machine: &'a ConstraintMachine,
        root: UpperReplayClaimId,
        result: bool,
    ) -> Self {
        Self::new_with_overrides(machine, None, Some((root, result)))
    }

    fn new_with_overrides(
        machine: &'a ConstraintMachine,
        record_result_override: Option<(BoundRecordId, bool)>,
        root_result_override: Option<(UpperReplayClaimId, bool)>,
    ) -> Self {
        Self {
            machine,
            record_result_override,
            root_result_override,
            shared: Some(Self::new_evaluator(
                machine,
                record_result_override,
                root_result_override,
            )),
            sharing_disabled: false,
        }
    }

    fn eval_record(&mut self, record: BoundRecordId) -> bool {
        if self.sharing_disabled {
            return Self::new_evaluator(
                self.machine,
                self.record_result_override,
                self.root_result_override,
            )
            .eval_record(record);
        }

        let shared = self
            .shared
            .as_mut()
            .expect("sharing remains available until a CPK cycle cut disables it");
        let cuts_before = shared.cycle_cuts();
        let result = shared.eval_record(record);
        assert!(
            !shared.has_visiting_state(),
            "CPK projection evaluation left a Visiting node after a top-level query"
        );
        if shared.cycle_cuts() != cuts_before {
            self.shared = None;
            self.sharing_disabled = true;
        }
        result
    }

    fn new_evaluator(
        machine: &'a ConstraintMachine,
        record_result_override: Option<(BoundRecordId, bool)>,
        root_result_override: Option<(UpperReplayClaimId, bool)>,
    ) -> proof::CpkProjectionEvaluator<'a> {
        let mut evaluator = proof::CpkProjectionEvaluator::new(machine, &machine.proof_store);
        if let Some((record, result)) = record_result_override {
            evaluator = evaluator.with_record_result_override(record, result);
        }
        if let Some((root, result)) = root_result_override {
            evaluator = evaluator.with_root_result_override(root, result);
        }
        evaluator
    }
}

impl ConstraintMachine {
    /// Return the active lower relations that may contribute to a generalized scheme.
    ///
    /// Raw bounds remain the audit source of truth. Claim coverage is deliberately resolved here,
    /// at projection time, so a relation becomes visible again when its last live coverage state
    /// leaves the compressed root.
    pub(crate) fn scheme_projectable_lowers(
        &self,
        var: TypeVar,
    ) -> impl Iterator<Item = SchemeProjectableLower<'_>> {
        self.cpk_scheme_projectable_lowers(var).into_iter()
    }

    fn cpk_scheme_projectable_lowers(&self, var: TypeVar) -> Vec<SchemeProjectableLower<'_>> {
        if self.proof_terminal_failure().is_some() {
            return Vec::new();
        }
        let records = self
            .bounds
            .vars
            .get(var.0 as usize)
            .and_then(Option::as_ref)
            .into_iter()
            .flat_map(VarBounds::projection_lower_records);
        let mut round = proof::ProjectionEvaluationRound::new();
        let mut lowers = Vec::new();
        for (record, bound) in records {
            let decision = match self.proof_store.project_lower(self, record, &mut round) {
                Ok(decision) => decision,
                Err(failure) => {
                    lowers.clear();
                    self.mark_proof_terminal_failure(
                        proof::ProofOperation::ProjectLowerEvaluation,
                        failure,
                    );
                    break;
                }
            };
            let reason = match decision {
                proof::ProjectionDecision::Excluded => continue,
                proof::ProjectionDecision::Unclaimed => SchemeProjectableLowerReason::Unclaimed,
                proof::ProjectionDecision::Included { supports } => {
                    SchemeProjectableLowerReason::Qualified {
                        uncovered_claims: supports
                            .uncovered_claims
                            .into_iter()
                            .map(|support| support.representative_claim)
                            .collect(),
                        independent_supports: supports.independent_supports,
                    }
                }
            };
            lowers.push(SchemeProjectableLower {
                record,
                bound,
                reason,
            });
        }
        lowers
    }

    /// Remove one state from the live coverage index without defining a new expiry policy.
    ///
    /// This is the lifecycle primitive needed by projection-time liveness. No production caller
    /// is wired in URR-H1; tests use it to exercise the empty/non-empty transition directly.
    #[allow(dead_code)]
    fn remove_scheme_projection_live_coverage_state(
        &mut self,
        root: UpperReplayClaimId,
        state: UnweightedRowReductionRecordId,
    ) -> bool {
        let transition = match self.try_update_scheme_projection_live_coverage(root, state, false) {
            Ok(transition) => transition,
            Err(failure) => {
                self.mark_proof_terminal_failure(
                    proof::ProofOperation::UpdateClaimLifecycle,
                    failure,
                );
                return false;
            }
        };
        let proof::PreparedLiveCoverageTransition::Changed {
            was_empty,
            is_empty,
            ..
        } = transition
        else {
            return false;
        };
        self.record_scheme_projection_liveness_mutation(root, was_empty, is_empty);
        true
    }

    fn insert_scheme_projection_live_coverage_state(
        &mut self,
        root: UpperReplayClaimId,
        state: UnweightedRowReductionRecordId,
    ) -> bool {
        let transition = match self.try_update_scheme_projection_live_coverage(root, state, true) {
            Ok(transition) => transition,
            Err(failure) => {
                self.mark_proof_terminal_failure(
                    proof::ProofOperation::UpdateClaimLifecycle,
                    failure,
                );
                return false;
            }
        };
        let proof::PreparedLiveCoverageTransition::Changed {
            was_empty,
            is_empty,
            ..
        } = transition
        else {
            return false;
        };
        self.record_scheme_projection_liveness_mutation(root, was_empty, is_empty);
        true
    }

    fn try_update_scheme_projection_live_coverage(
        &mut self,
        root: UpperReplayClaimId,
        state: UnweightedRowReductionRecordId,
        active: bool,
    ) -> Result<proof::PreparedLiveCoverageTransition, proof::ProofFailure> {
        let mut mutation = self
            .proof_store
            .try_prepare_live_coverage_mutation(root, state, active)?;
        self.proof_store
            .commit_live_coverage_mutation(&mut mutation);
        Ok(mutation.transition)
    }

    fn record_scheme_projection_liveness_mutation(
        &mut self,
        root: UpperReplayClaimId,
        was_empty: bool,
        is_empty: bool,
    ) {
        if was_empty == is_empty {
            self.bump_provenance_epoch();
            return;
        }
        let Some(root) = self.proof_store.claim_coverage_root(root) else {
            self.bump_provenance_epoch();
            return;
        };
        let mut affected_records = self
            .proof_store
            .projection_lower_records_for_root(root)
            .iter()
            .copied()
            .collect::<FxHashSet<_>>();
        affected_records.extend(
            self.proof_store
                .dependent_records(ProofPremise::RootCoverage(root))
                .into_iter()
                .flatten()
                .copied(),
        );
        self.extend_with_record_dependents(&mut affected_records);

        let mut before_round =
            CpkPublicationEvaluationRound::with_root_result_override(self, root, was_empty);
        let mut after_round = CpkPublicationEvaluationRound::new(self);
        let affected_owners = affected_records
            .into_iter()
            .filter(|record| before_round.eval_record(*record) != after_round.eval_record(*record))
            .filter_map(|record| self.active_projection_record_owner(record))
            .collect::<FxHashSet<_>>();
        self.record_scheme_projection_mutation(affected_owners);
    }

    fn apply_scheme_projection_mutation(&mut self, mut mutation: SchemeProjectionMutation) {
        let inclusion_before = self.cpk_projection_mutation_inclusion_before(&mutation);
        self.commit_scheme_projection_mutation(&mut mutation);
        let intent = self.evaluate_cpk_scheme_projection_mutation(mutation, inclusion_before);
        self.publish_scheme_projection_intent(intent);
    }

    fn cpk_projection_mutation_inclusion_before(
        &self,
        mutation: &SchemeProjectionMutation,
    ) -> Option<bool> {
        let SchemeProjectionMutation::ProofsChanged { lower_record, .. } = mutation else {
            return None;
        };
        Some(self.scheme_projection_record_is_included(*lower_record))
    }

    fn evaluate_cpk_scheme_projection_mutation(
        &self,
        mutation: SchemeProjectionMutation,
        inclusion_before: Option<bool>,
    ) -> SchemeProjectionPublicationIntent {
        match mutation {
            SchemeProjectionMutation::None => SchemeProjectionPublicationIntent::None,
            SchemeProjectionMutation::ProofsChanged { lower_record, .. } => {
                let was_included = inclusion_before
                    .expect("a proof mutation captures its CPK before view before commit");
                let is_included = self.scheme_projection_record_is_included(lower_record);
                self.evaluate_record_inclusion_publication(
                    lower_record,
                    was_included,
                    is_included,
                    true,
                )
            }
        }
    }

    pub(in crate::constraints) fn try_original_upper_replay_claim(
        &mut self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        kind: UpperReplayClaimKind,
    ) -> Result<UpperReplayClaimRegistration, proof::ProofFailure> {
        self.try_original_upper_replay_claim_transaction(record, producer, kind, None)
    }

    fn try_original_upper_replay_claim_transaction(
        &mut self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        kind: UpperReplayClaimKind,
        reduction_state: Option<UnweightedRowReductionRecordId>,
    ) -> Result<UpperReplayClaimRegistration, proof::ProofFailure> {
        if reduction_state.is_some() {
            let exhausted = |_| proof::ProofFailure::ResourceExhausted {
                operation: proof::ProofOperation::AdmitOriginalClaim,
            };
            self.proof_store
                .try_reserve_reduction_claim_index()
                .map_err(exhausted)?;
        }
        if let Some(claim) = self.proof_store.original_claim(record, producer) {
            if let Some(state) = reduction_state {
                self.proof_store.commit_reduction_claim_index(state, claim);
            }
            let lower_record = self.lower_record_for_constraint(producer);
            let mut clause_admission = match lower_record {
                Some(lower_record) => self.proof_store.try_prepare_projection_clause_admission(
                    lower_record,
                    &[RecordProofClauseLinkAdmission::claimed(
                        claim,
                        RecordProofClause::Standalone {
                            support: SchemeProjectionProofSupport::Claimed(claim),
                        },
                        ClaimedAttributionSource::FlatRetained,
                    )],
                )?,
                None => None,
            };
            if let Some(prepared) = clause_admission.as_mut() {
                self.proof_store
                    .commit_projection_clause_admission(prepared);
            }
            let mut registration = UpperReplayClaimRegistration::new(claim);
            if let Some(lower_record) = lower_record {
                registration.scheme_projection_mutation =
                    self.try_prepare_scheme_projection_mutation(lower_record, &[claim], &[])?;
            }
            return Ok(registration);
        }
        let mut admission = self
            .proof_store
            .try_prepare_original_claim_admission(record, producer, kind)?;
        let issued = admission.occurrence.claim;
        let lower_record = self.lower_record_for_constraint(producer);
        let mut clause_admission = match lower_record {
            Some(lower_record) => self.proof_store.try_prepare_projection_clause_admission(
                lower_record,
                &[RecordProofClauseLinkAdmission::claimed(
                    issued,
                    RecordProofClause::Standalone {
                        support: SchemeProjectionProofSupport::Claimed(issued),
                    },
                    ClaimedAttributionSource::FlatRetained,
                )],
            )?,
            None => None,
        };
        #[cfg(test)]
        self.record_cpk_upper_claim_insertion_census(record, issued);
        self.proof_store
            .commit_original_claim_admission(&mut admission);
        if let Some(prepared) = clause_admission.as_mut() {
            self.proof_store
                .commit_projection_clause_admission(prepared);
        }
        let mut registration = UpperReplayClaimRegistration::new(issued);
        if let Some(lower_record) = lower_record {
            registration.scheme_projection_mutation =
                self.try_prepare_scheme_projection_mutation(lower_record, &[issued], &[])?;
        }
        if let Some(state) = reduction_state {
            self.proof_store.commit_reduction_claim_index(state, issued);
        }
        Ok(registration)
    }

    fn admit_original_upper_replay_claim(
        &mut self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        kind: UpperReplayClaimKind,
    ) -> Option<UpperReplayClaimRegistration> {
        match self.try_original_upper_replay_claim(record, producer, kind) {
            Ok(registration) => Some(registration),
            Err(failure) => {
                self.mark_proof_terminal_failure(
                    proof::ProofOperation::AdmitOriginalClaim,
                    failure,
                );
                None
            }
        }
    }

    #[cfg(test)]
    pub(in crate::constraints) fn original_upper_replay_claim(
        &mut self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        kind: UpperReplayClaimKind,
    ) -> UpperReplayClaimRegistration {
        self.try_original_upper_replay_claim(record, producer, kind)
            .expect("test original claim admission must have capacity")
    }

    pub(in crate::constraints) fn try_derived_upper_replay_claim(
        &mut self,
        record: BoundRecordId,
        parent_claim: UpperReplayClaimId,
        producer: ConstraintRecordId,
        lineage: impl FnOnce(u32) -> UpperReplayClaimLineage,
    ) -> Result<UpperReplayClaimRegistration, proof::ProofFailure> {
        let depth = self.proof_store.next_derived_claim_depth(parent_claim);
        let lineage = lineage(depth);
        let mut decision = self.proof_store.try_prepare_derived_claim_admission(
            record,
            parent_claim,
            producer,
            lineage,
        )?;
        let lower_record = match lineage {
            UpperReplayClaimLineage::Original => self.lower_record_for_constraint(producer),
            UpperReplayClaimLineage::ReplayConstraint { result, .. }
            | UpperReplayClaimLineage::StructuralConstraint { result, .. }
            | UpperReplayClaimLineage::ReductionRouteConstraint { result, .. } => {
                self.lower_record_for_constraint(result)
            }
            UpperReplayClaimLineage::ReplayEvidence { replay, .. } => self
                .proof_store
                .projection_lower_record_for_replay(replay),
        };
        match &decision {
            proof::PreparedDerivedClaimDecision::Coalesced { claim, .. } => {
                let claim = *claim;
                self.proof_store
                    .commit_derived_claim_decision(&mut decision);
                let mut registration = UpperReplayClaimRegistration::new(claim);
                if let Some(lower_record) = lower_record {
                    registration.scheme_projection_mutation =
                        self.try_prepare_scheme_projection_mutation(lower_record, &[claim], &[])?;
                }
                Ok(registration)
            }
            proof::PreparedDerivedClaimDecision::New(_) => {
                #[cfg(test)]
                if let proof::PreparedDerivedClaimDecision::New(admission) = &decision {
                    self.record_cpk_upper_claim_insertion_census(
                        admission.occurrence.current_record,
                        admission.occurrence.coverage_root,
                    );
                }
                self.proof_store
                    .commit_derived_claim_decision(&mut decision);
                let proof::PreparedDerivedClaimDecision::New(admission) = &decision else {
                    unreachable!("prepared derived decision changed variant")
                };
                let mut registration =
                    UpperReplayClaimRegistration::new(admission.occurrence.claim);
                if let Some(lower_record) = lower_record {
                    registration.scheme_projection_mutation = self
                        .try_prepare_scheme_projection_mutation(
                            lower_record,
                            &[admission.occurrence.claim],
                            &[],
                        )?;
                }
                Ok(registration)
            }
        }
    }

    fn admit_derived_upper_replay_claim(
        &mut self,
        record: BoundRecordId,
        parent_claim: UpperReplayClaimId,
        producer: ConstraintRecordId,
        lineage: impl FnOnce(u32) -> UpperReplayClaimLineage,
    ) -> Option<UpperReplayClaimRegistration> {
        match self.try_derived_upper_replay_claim(record, parent_claim, producer, lineage) {
            Ok(registration) => Some(registration),
            Err(failure) => {
                self.mark_proof_terminal_failure(proof::ProofOperation::AdmitDerivedClaim, failure);
                None
            }
        }
    }

    #[cfg(test)]
    fn derived_upper_replay_claim(
        &mut self,
        record: BoundRecordId,
        parent_claim: UpperReplayClaimId,
        producer: ConstraintRecordId,
        lineage: impl FnOnce(u32) -> UpperReplayClaimLineage,
    ) -> UpperReplayClaimRegistration {
        self.try_derived_upper_replay_claim(record, parent_claim, producer, lineage)
            .expect("test derived claim admission must have capacity")
    }

    fn try_move_upper_replay_claim(
        &mut self,
        claim: UpperReplayClaimId,
        current_record: BoundRecordId,
    ) -> Result<(), proof::ProofFailure> {
        let mut mutation = self
            .proof_store
            .try_prepare_upper_claim_move(claim, current_record)?;
        #[cfg(test)]
        if mutation.previous_record != mutation.current_record {
            self.record_cpk_upper_claim_insertion_census(
                mutation.current_record,
                mutation.coverage_root,
            );
        }
        self.proof_store.commit_upper_claim_move(&mut mutation);
        Ok(())
    }

    #[cfg(test)]
    fn record_cpk_upper_claim_insertion_census(
        &self,
        record: BoundRecordId,
        coverage_root: UpperReplayClaimId,
    ) {
        let moves = self
            .proof_store
            .claims_for_upper_record_for_test(record)
            .iter()
            .filter_map(|claim| self.proof_store.claim_coverage_root(*claim))
            .filter(|root| *root > coverage_root)
            .count();
        record_canonical_upper_claim_insertion_moves(moves);
    }

    #[cfg(test)]
    fn move_upper_replay_claim(
        &mut self,
        claim: UpperReplayClaimId,
        current_record: BoundRecordId,
    ) {
        self.try_move_upper_replay_claim(claim, current_record)
            .expect("test claim move must have capacity");
    }

    fn try_prepare_scheme_projection_mutation(
        &mut self,
        lower_record: BoundRecordId,
        claims_to_link: &[UpperReplayClaimId],
        independent_supports: &[ProjectionProofCarrier],
    ) -> Result<SchemeProjectionMutation, proof::ProofFailure> {
        if self.bounds.record(lower_record).is_none() {
            return Ok(SchemeProjectionMutation::None);
        }
        let Some(prepared) = self.proof_store.try_prepare_projection_support_mutation(
            lower_record,
            claims_to_link,
            independent_supports,
        )?
        else {
            return Ok(SchemeProjectionMutation::None);
        };
        Ok(SchemeProjectionMutation::ProofsChanged {
            lower_record,
            prepared,
        })
    }

    fn commit_scheme_projection_mutation(&mut self, mutation: &mut SchemeProjectionMutation) {
        let SchemeProjectionMutation::ProofsChanged { prepared, .. } = mutation else {
            return;
        };
        self.proof_store
            .commit_projection_support_mutation(prepared);
    }

    #[cfg(test)]
    fn try_evaluate_record_inclusion_publication(
        &self,
        lower_record: BoundRecordId,
        was_included: bool,
        is_included: bool,
        metadata_changed: bool,
    ) -> proof::ProofKernelResult<SchemeProjectionPublicationIntent> {
        if was_included == is_included {
            let intent = if metadata_changed {
                SchemeProjectionPublicationIntent::MetadataOnly
            } else {
                SchemeProjectionPublicationIntent::None
            };
            return Ok(intent);
        }
        let mut affected_records = self
            .proof_store
            .dependent_records(ProofPremise::Record(lower_record))
            .cloned()
            .unwrap_or_default();
        self.extend_with_record_dependents(&mut affected_records);
        let mut before_round = CpkTestProjectionEvaluationRound::with_record_result_override(
            self,
            lower_record,
            was_included,
        );
        let mut after_round = CpkTestProjectionEvaluationRound::new(self);
        let mut affected_owners = FxHashSet::default();
        for record in affected_records {
            if before_round.eval_record(record) != after_round.eval_record(record)
                && let Some(owner) = self.active_projection_record_owner(record)
            {
                affected_owners.insert(owner);
            }
        }
        #[cfg(test)]
        self.record_semantic_projectability_transition(lower_record, was_included, is_included);
        if let Some(owner) = self.active_projection_record_owner(lower_record) {
            affected_owners.insert(owner);
        }
        let intent = if affected_owners.is_empty() {
            SchemeProjectionPublicationIntent::MetadataOnly
        } else {
            SchemeProjectionPublicationIntent::OwnersChanged(affected_owners)
        };
        Ok(intent)
    }

    fn evaluate_record_inclusion_publication(
        &self,
        lower_record: BoundRecordId,
        was_included: bool,
        is_included: bool,
        metadata_changed: bool,
    ) -> SchemeProjectionPublicationIntent {
        if was_included == is_included {
            return if metadata_changed {
                SchemeProjectionPublicationIntent::MetadataOnly
            } else {
                SchemeProjectionPublicationIntent::None
            };
        }
        let mut affected_records = self
            .proof_store
            .dependent_records(ProofPremise::Record(lower_record))
            .cloned()
            .unwrap_or_default();
        self.extend_with_record_dependents(&mut affected_records);
        let mut before_round = CpkPublicationEvaluationRound::with_record_result_override(
            self,
            lower_record,
            was_included,
        );
        let mut after_round = CpkPublicationEvaluationRound::new(self);
        let mut affected_owners = FxHashSet::default();
        for record in affected_records {
            if before_round.eval_record(record) != after_round.eval_record(record)
                && let Some(owner) = self.active_projection_record_owner(record)
            {
                affected_owners.insert(owner);
            }
        }
        #[cfg(test)]
        self.record_semantic_projectability_transition(lower_record, was_included, is_included);
        if let Some(owner) = self.active_projection_record_owner(lower_record) {
            affected_owners.insert(owner);
        }
        if affected_owners.is_empty() {
            SchemeProjectionPublicationIntent::MetadataOnly
        } else {
            SchemeProjectionPublicationIntent::OwnersChanged(affected_owners)
        }
    }

    fn try_evaluate_projection_inclusion_snapshot(
        &self,
        before: &FxHashMap<BoundRecordId, bool>,
    ) -> proof::ProofKernelResult<SchemeProjectionPublicationIntent> {
        let mut after_round = CpkPublicationEvaluationRound::new(self);
        let mut affected_owners = FxHashSet::default();
        #[cfg(test)]
        let mut semantic_transitions = Vec::new();
        for (record, was_included) in before {
            let is_included = after_round.eval_record(*record);
            if *was_included != is_included {
                #[cfg(test)]
                semantic_transitions.push((*record, *was_included, is_included));
                if let Some(owner) = self.active_projection_record_owner(*record) {
                    affected_owners.insert(owner);
                }
            }
        }
        #[cfg(test)]
        for (record, was_included, is_included) in semantic_transitions {
            self.record_semantic_projectability_transition(record, was_included, is_included);
        }
        Ok(if affected_owners.is_empty() {
            SchemeProjectionPublicationIntent::None
        } else {
            SchemeProjectionPublicationIntent::OwnersChanged(affected_owners)
        })
    }

    fn publish_scheme_projection_intent(&mut self, intent: SchemeProjectionPublicationIntent) {
        match intent {
            SchemeProjectionPublicationIntent::None => {}
            SchemeProjectionPublicationIntent::MetadataOnly => {
                self.bump_provenance_epoch();
            }
            SchemeProjectionPublicationIntent::OwnersChanged(owners) => {
                self.record_scheme_projection_mutation(owners);
            }
        }
    }

    fn scheme_projection_record_is_included(&self, lower_record: BoundRecordId) -> bool {
        CpkPublicationEvaluationRound::new(self).eval_record(lower_record)
    }

    #[cfg(test)]
    fn scheme_projection_cycle_guard_snapshot(&self, lower_record: BoundRecordId) -> (bool, usize) {
        let mut evaluator = proof::CpkProjectionEvaluator::new(self, &self.proof_store);
        let projectable = evaluator.eval_record(lower_record);
        (projectable, evaluator.cycle_cuts())
    }

    fn projection_inclusion_snapshot(
        &self,
        premise: ProofPremise,
    ) -> FxHashMap<BoundRecordId, bool> {
        let mut records = self
            .proof_store
            .dependent_records(premise)
            .cloned()
            .unwrap_or_default();
        self.extend_with_record_dependents(&mut records);
        let mut round = CpkPublicationEvaluationRound::new(self);
        records
            .into_iter()
            .map(|record| (record, round.eval_record(record)))
            .collect()
    }

    fn publish_projection_inclusion_snapshot(&mut self, before: FxHashMap<BoundRecordId, bool>) {
        if before.is_empty() {
            return;
        }
        let mut affected_owners = FxHashSet::default();
        for (record, was_included) in before {
            let is_included = self.scheme_projection_record_is_included(record);
            if was_included != is_included {
                #[cfg(test)]
                self.record_semantic_projectability_transition(record, was_included, is_included);
                if let Some(owner) = self.active_projection_record_owner(record) {
                    affected_owners.insert(owner);
                }
            }
        }
        if !affected_owners.is_empty() {
            self.record_scheme_projection_mutation(affected_owners);
        }
    }

    fn extend_with_record_dependents(&self, records: &mut FxHashSet<BoundRecordId>) {
        let mut queue = records.iter().copied().collect::<VecDeque<_>>();
        while let Some(record) = queue.pop_front() {
            let Some(dependents) = self
                .proof_store
                .dependent_records(ProofPremise::Record(record))
            else {
                continue;
            };
            for dependent in dependents {
                if records.insert(*dependent) {
                    queue.push_back(*dependent);
                }
            }
        }
    }

    fn active_projection_record_owner(&self, record: BoundRecordId) -> Option<TypeVar> {
        self.bounds
            .record(record)
            .filter(|record| record.state() != BoundRecordState::Tombstone)
            .map(BoundRecord::owner)
    }

    fn record_scheme_projection_mutation(&mut self, owners: FxHashSet<TypeVar>) {
        #[cfg(test)]
        let semantic_owner_order = owners.iter().copied().collect::<Vec<_>>();
        #[cfg(test)]
        let semantic_before_epoch = self.epoch;
        for owner in &owners {
            if self.method_role_mutations.is_active() {
                self.method_role_mutations
                    .record(DependencyKey::ConstraintBounds(*owner));
            }
        }
        if owners.is_empty() {
            self.bump_provenance_epoch();
            return;
        }
        let epoch = self.bump_epoch();
        for owner in owners {
            self.bounds.record_var_epoch(owner, epoch);
        }
        self.bump_provenance_epoch();
        #[cfg(test)]
        self.record_semantic_owner_invalidations(
            &semantic_owner_order,
            semantic_before_epoch,
            epoch,
        );
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
/// 型変数ごとの weighted lower / upper bounds。
///
/// 新しい lower が入ると既存 upper へ、新しい upper が入ると既存 lower へ subtype を再投入する。
/// 同じ型境界でも重みが違えば別の不等式なので、bounds 側では合成せず exact dedup だけを行う。
pub struct TypeBounds {
    vars: Vec<Option<VarBounds>>,
    canonical: FxHashMap<BoundSemanticKey, BoundRecordId>,
    records: Vec<BoundRecord>,
}

impl TypeBounds {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn of(&self, var: TypeVar) -> Option<&VarBounds> {
        #[cfg(test)]
        crate::analysis::record_owner_bound_read(var);
        self.vars
            .get(var.0 as usize)
            .and_then(|bounds| bounds.as_ref())
    }

    pub fn record(&self, id: BoundRecordId) -> Option<&BoundRecord> {
        self.records.get(id.0 as usize)
    }

    fn contains_derivation(&self, key: &BoundSemanticKey, derivation: &BoundDerivation) -> bool {
        self.canonical
            .get(key)
            .and_then(|id| self.record(*id))
            .is_some_and(|record| record.derivations.contains(derivation))
    }

    fn add_lower(
        &mut self,
        var: TypeVar,
        pos: PosId,
        weights: ConstraintWeights,
        derivation: BoundDerivation,
    ) -> BoundInsertResult {
        let insertion = self.add_bound(
            BoundSemanticKey::Lower {
                owner: var,
                endpoint: pos,
                weights: weights.clone(),
            },
            BoundDirection::Lower,
            var,
            BoundEndpoint::Lower(pos),
            weights,
            BoundRecordState::Ordinary,
            derivation,
        );
        insertion
    }

    fn add_upper(
        &mut self,
        var: TypeVar,
        neg: NegId,
        weights: ConstraintWeights,
        derivation: BoundDerivation,
    ) -> BoundInsertResult {
        self.add_bound(
            BoundSemanticKey::Upper {
                owner: var,
                endpoint: neg,
                weights: weights.clone(),
            },
            BoundDirection::Upper,
            var,
            BoundEndpoint::Upper(neg),
            weights,
            BoundRecordState::Ordinary,
            derivation,
        )
    }

    fn add_evidence_lower(
        &mut self,
        var: TypeVar,
        pos: PosId,
        weights: ConstraintWeights,
        derivation: BoundDerivation,
    ) -> BoundInsertResult {
        let insertion = self.add_bound(
            BoundSemanticKey::Lower {
                owner: var,
                endpoint: pos,
                weights: weights.clone(),
            },
            BoundDirection::Lower,
            var,
            BoundEndpoint::Lower(pos),
            weights,
            BoundRecordState::Evidence,
            derivation,
        );
        insertion
    }

    fn add_evidence_upper(
        &mut self,
        var: TypeVar,
        neg: NegId,
        weights: ConstraintWeights,
        derivation: BoundDerivation,
    ) -> BoundInsertResult {
        self.add_bound(
            BoundSemanticKey::Upper {
                owner: var,
                endpoint: neg,
                weights: weights.clone(),
            },
            BoundDirection::Upper,
            var,
            BoundEndpoint::Upper(neg),
            weights,
            BoundRecordState::Evidence,
            derivation,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn add_bound(
        &mut self,
        key: BoundSemanticKey,
        direction: BoundDirection,
        owner: TypeVar,
        endpoint: BoundEndpoint,
        weights: ConstraintWeights,
        requested_state: BoundRecordState,
        derivation: BoundDerivation,
    ) -> BoundInsertResult {
        if let Some(id) = self.canonical.get(&key).copied() {
            let record = &mut self.records[id.0 as usize];
            let provenance_changed = if record.derivations.contains(&derivation) {
                false
            } else {
                record.derivations.push(derivation);
                true
            };
            let promoted = requested_state == BoundRecordState::Ordinary
                && record.state == BoundRecordState::Evidence;
            if promoted {
                record.state = BoundRecordState::Ordinary;
                let bounds = self.bounds_mut(owner);
                match endpoint {
                    BoundEndpoint::Lower(pos) => {
                        let bound = WeightedLowerBound { pos, weights };
                        bounds
                            .evidence_lower_ids
                            .retain(|candidate| *candidate != id);
                        bounds
                            .evidence_lowers
                            .retain(|candidate| candidate != &bound);
                        bounds.lower_ids.push(id);
                        bounds.lowers.push(bound);
                    }
                    BoundEndpoint::Upper(neg) => {
                        let bound = WeightedUpperBound { neg, weights };
                        bounds
                            .evidence_upper_ids
                            .retain(|candidate| *candidate != id);
                        bounds
                            .evidence_uppers
                            .retain(|candidate| candidate != &bound);
                        bounds.upper_ids.push(id);
                        bounds.uppers.push(bound);
                    }
                }
            }
            return BoundInsertResult {
                id,
                semantic_changed: promoted,
                provenance_changed,
                promoted,
            };
        }

        let id = BoundRecordId(self.records.len() as u32);
        self.canonical.insert(key, id);
        self.records.push(BoundRecord {
            direction,
            owner,
            endpoint,
            weights: weights.clone(),
            state: requested_state,
            derivations: vec![derivation],
            disposition: None,
        });
        let bounds = self.bounds_mut(owner);
        match (endpoint, requested_state) {
            (BoundEndpoint::Lower(pos), BoundRecordState::Ordinary) => {
                bounds.lower_ids.push(id);
                bounds.lowers.push(WeightedLowerBound { pos, weights });
            }
            (BoundEndpoint::Upper(neg), BoundRecordState::Ordinary) => {
                bounds.upper_ids.push(id);
                bounds.uppers.push(WeightedUpperBound { neg, weights });
            }
            (BoundEndpoint::Lower(pos), BoundRecordState::Evidence) => {
                bounds.evidence_lower_ids.push(id);
                bounds
                    .evidence_lowers
                    .push(WeightedLowerBound { pos, weights });
            }
            (BoundEndpoint::Upper(neg), BoundRecordState::Evidence) => {
                bounds.evidence_upper_ids.push(id);
                bounds
                    .evidence_uppers
                    .push(WeightedUpperBound { neg, weights });
            }
            (_, BoundRecordState::Tombstone) => unreachable!("new bounds are active"),
        }
        BoundInsertResult {
            id,
            semantic_changed: true,
            provenance_changed: true,
            promoted: false,
        }
    }

    fn bounds_mut(&mut self, var: TypeVar) -> &mut VarBounds {
        let index = var.0 as usize;
        ensure_slot(&mut self.vars, index);
        self.vars[index].get_or_insert_with(VarBounds::default)
    }

    fn record_var_epoch(&mut self, var: TypeVar, epoch: ConstraintEpoch) {
        self.bounds_mut(var).epoch = epoch;
    }

}

fn ensure_slot<T>(items: &mut Vec<Option<T>>, index: usize) {
    if items.len() <= index {
        items.resize_with(index + 1, || None);
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
/// 1つの型変数に蓄積された上下界。
///
/// bounds は追加順の Vec で持つ。現段階では探索や差分削除よりも、イベント順と単純な再伝播を優先する。
pub struct VarBounds {
    epoch: ConstraintEpoch,
    lowers: Vec<WeightedLowerBound>,
    uppers: Vec<WeightedUpperBound>,
    evidence_lowers: Vec<WeightedLowerBound>,
    evidence_uppers: Vec<WeightedUpperBound>,
    lower_ids: Vec<BoundRecordId>,
    upper_ids: Vec<BoundRecordId>,
    evidence_lower_ids: Vec<BoundRecordId>,
    evidence_upper_ids: Vec<BoundRecordId>,
}

impl VarBounds {
    pub fn epoch(&self) -> ConstraintEpoch {
        self.epoch
    }

    pub fn lowers(&self) -> &[WeightedLowerBound] {
        &self.lowers
    }

    pub fn uppers(&self) -> &[WeightedUpperBound] {
        &self.uppers
    }

    pub fn projection_lowers(&self) -> impl Iterator<Item = &WeightedLowerBound> {
        self.evidence_lowers.iter().chain(self.lowers.iter())
    }

    pub fn projection_uppers(&self) -> impl Iterator<Item = &WeightedUpperBound> {
        self.evidence_uppers.iter().chain(self.uppers.iter())
    }

    fn projection_lower_records(
        &self,
    ) -> impl Iterator<Item = (BoundRecordId, &WeightedLowerBound)> {
        self.evidence_lower_ids
            .iter()
            .copied()
            .zip(self.evidence_lowers.iter())
            .chain(self.lower_ids.iter().copied().zip(self.lowers.iter()))
    }

    pub(crate) fn generalized_projection_lowers(
        &self,
    ) -> impl Iterator<Item = (BoundRecordId, &WeightedLowerBound)> {
        self.projection_lower_records()
    }

    fn projection_upper_records(
        &self,
    ) -> impl Iterator<Item = (BoundRecordId, &WeightedUpperBound)> {
        self.evidence_upper_ids
            .iter()
            .copied()
            .zip(self.evidence_uppers.iter())
            .chain(self.upper_ids.iter().copied().zip(self.uppers.iter()))
    }

    pub(crate) fn generalized_projection_uppers(
        &self,
    ) -> impl Iterator<Item = (BoundRecordId, &WeightedUpperBound)> {
        self.projection_upper_records()
    }

    pub fn evidence_lower_count(&self) -> usize {
        self.evidence_lowers.len()
    }

    pub fn evidence_upper_count(&self) -> usize {
        self.evidence_uppers.len()
    }

    pub fn lower_record_ids(&self) -> &[BoundRecordId] {
        &self.lower_ids
    }

    pub fn upper_record_ids(&self) -> &[BoundRecordId] {
        &self.upper_ids
    }

    pub fn evidence_lower_record_ids(&self) -> &[BoundRecordId] {
        &self.evidence_lower_ids
    }

    pub fn evidence_upper_record_ids(&self) -> &[BoundRecordId] {
        &self.evidence_upper_ids
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// lower bound と、その bound へ到達するまでに通った subtract weight。
pub struct WeightedLowerBound {
    pub pos: PosId,
    pub weights: ConstraintWeights,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// upper bound と、その bound へ到達するまでに通った subtract weight。
pub struct WeightedUpperBound {
    pub neg: NegId,
    pub weights: ConstraintWeights,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundRecordId(u32);

pub use poly::provenance::{
    OccurrenceProvenance, TypeOccurrenceKey, TypeOccurrenceOwner, TypeOccurrenceRole,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum OccurrenceProvenanceRoot {
    Constraint(ConstraintRecordId),
    Bound(BoundRecordId),
    Origin(OriginId),
    RowDerivation(RowDerivationId),
    GeneralizedWitness(GeneralizedSchemeWitnessId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PendingOccurrenceProvenance {
    pub(crate) roots: Vec<OccurrenceProvenanceRoot>,
    pub(crate) completeness: ProvenanceCompleteness,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GeneralizedSchemeRecordId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GeneralizedSchemeWitnessId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SchemeInstantiationId(u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct GeneralizedTypePath(pub Vec<GeneralizedTypePathStep>);

impl GeneralizedTypePath {
    pub(crate) fn push(&mut self, step: GeneralizedTypePathStep) {
        self.0.push(step);
    }

    pub fn depth(&self) -> usize {
        self.0.len()
    }

    fn without_first(&self) -> Self {
        Self(self.0.iter().skip(1).copied().collect())
    }

    pub fn to_type_position_path(&self) -> poly::provenance::TypePositionPath {
        poly::provenance::TypePositionPath(
            self.0
                .iter()
                .copied()
                .map(GeneralizedTypePathStep::to_type_position_step)
                .collect(),
        )
    }

    pub fn from_type_position_path(path: &poly::provenance::TypePositionPath) -> Self {
        Self(
            path.0
                .iter()
                .copied()
                .map(GeneralizedTypePathStep::from_type_position_step)
                .collect(),
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GeneralizedTypePathStep {
    FunctionArgument,
    FunctionArgumentEffect,
    FunctionReturnEffect,
    FunctionReturn,
    ConstructorArgument {
        alternative: StructuralIndex,
        argument: StructuralIndex,
    },
    TupleElement(StructuralIndex),
    RecordField {
        alternative: StructuralIndex,
        field: StructuralIndex,
    },
    VariantPayload {
        alternative: StructuralIndex,
        item: StructuralIndex,
        payload: StructuralIndex,
    },
    RowItemArgument {
        item: StructuralIndex,
        argument: StructuralIndex,
    },
    RowTail,
    RecursiveBound(StructuralIndex),
}

impl GeneralizedTypePathStep {
    fn to_type_position_step(self) -> poly::provenance::TypePositionStep {
        use poly::provenance::{TypePositionIndex, TypePositionStep};
        let index = |value: StructuralIndex| TypePositionIndex::from_usize(value.0 as usize);
        match self {
            Self::FunctionArgument => TypePositionStep::FunctionArgument,
            Self::FunctionArgumentEffect => TypePositionStep::FunctionArgumentEffect,
            Self::FunctionReturnEffect => TypePositionStep::FunctionReturnEffect,
            Self::FunctionReturn => TypePositionStep::FunctionReturn,
            Self::ConstructorArgument {
                alternative,
                argument,
            } => TypePositionStep::ConstructorArgument {
                alternative: index(alternative),
                argument: index(argument),
            },
            Self::TupleElement(value) => TypePositionStep::TupleElement(index(value)),
            Self::RecordField { alternative, field } => TypePositionStep::RecordField {
                alternative: index(alternative),
                field: index(field),
            },
            Self::VariantPayload {
                alternative,
                item,
                payload,
            } => TypePositionStep::VariantPayload {
                alternative: index(alternative),
                item: index(item),
                payload: index(payload),
            },
            Self::RowItemArgument { item, argument } => TypePositionStep::RowItemArgument {
                item: index(item),
                argument: index(argument),
            },
            Self::RowTail => TypePositionStep::RowTail,
            Self::RecursiveBound(value) => TypePositionStep::RecursiveBound(index(value)),
        }
    }

    fn from_type_position_step(step: poly::provenance::TypePositionStep) -> Self {
        use poly::provenance::TypePositionStep;
        let index =
            |value: poly::provenance::TypePositionIndex| StructuralIndex::from_usize(value.index());
        match step {
            TypePositionStep::FunctionArgument => Self::FunctionArgument,
            TypePositionStep::FunctionArgumentEffect => Self::FunctionArgumentEffect,
            TypePositionStep::FunctionReturnEffect => Self::FunctionReturnEffect,
            TypePositionStep::FunctionReturn => Self::FunctionReturn,
            TypePositionStep::ConstructorArgument {
                alternative,
                argument,
            } => Self::ConstructorArgument {
                alternative: index(alternative),
                argument: index(argument),
            },
            TypePositionStep::TupleElement(value) => Self::TupleElement(index(value)),
            TypePositionStep::RecordField { alternative, field } => Self::RecordField {
                alternative: index(alternative),
                field: index(field),
            },
            TypePositionStep::VariantPayload {
                alternative,
                item,
                payload,
            } => Self::VariantPayload {
                alternative: index(alternative),
                item: index(item),
                payload: index(payload),
            },
            TypePositionStep::RowItemArgument { item, argument } => Self::RowItemArgument {
                item: index(item),
                argument: index(argument),
            },
            TypePositionStep::RowTail => Self::RowTail,
            TypePositionStep::RecursiveBound(value) => Self::RecursiveBound(index(value)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GeneralizedWitnessRole {
    ConstraintRelation,
    LowerBound,
    UpperBound,
    RecursiveLowerBound,
    RecursiveUpperBound,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GeneralizationParent {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GeneralizationParentCarriers {
    Constraint(ConstraintRecordId),
    Bound(BoundRecordId),
    ReplayEvidence {
        lower: BoundRecordId,
        upper: BoundRecordId,
    },
    Origin(OriginId),
    RowDerivation(RowDerivationId),
    GeneralizedWitness(GeneralizedSchemeWitnessId),
}

impl ConstraintMachine {
    /// Resolve a generalized parent to the exact records that carry its explanation.
    ///
    /// A claim-qualified parent keeps `bound` as its audit link, but deliberately does not
    /// expand that mixed record: only the selected claim's own lineage is semantic provenance.
    pub(crate) fn generalization_parent_carriers(
        &self,
        parent: GeneralizationParent,
    ) -> Option<GeneralizationParentCarriers> {
        let GeneralizationParent::BoundClaim { bound, claim } = parent else {
            if let GeneralizationParent::BoundProjectionProof { bound, carrier } = parent {
                let linked = self
                    .proof_store
                    .projection_supports_for_record(bound)
                    .contains(&SchemeProjectionProofSupport::Independent(carrier));
                debug_assert!(
                    linked,
                    "independent projection parent must be ledger-backed"
                );
                if !linked {
                    return None;
                }
                return Some(match carrier {
                    ProjectionProofCarrier::ConstraintOrigin { origin, .. }
                    | ProjectionProofCarrier::Origin(origin) => {
                        GeneralizationParentCarriers::Origin(origin)
                    }
                    ProjectionProofCarrier::StructuralConstraint { derivation, .. } => {
                        GeneralizationParentCarriers::Constraint(derivation.parent)
                    }
                    ProjectionProofCarrier::ReplayConstraint { derivation, .. }
                    | ProjectionProofCarrier::ReplayEvidence(derivation) => {
                        GeneralizationParentCarriers::ReplayEvidence {
                            lower: derivation.lower,
                            upper: derivation.upper,
                        }
                    }
                    ProjectionProofCarrier::RowConstraint { derivation, .. }
                    | ProjectionProofCarrier::Row(derivation) => {
                        GeneralizationParentCarriers::RowDerivation(derivation)
                    }
                    ProjectionProofCarrier::SchemeInstantiationConstraint {
                        source_witness,
                        ..
                    }
                    | ProjectionProofCarrier::SchemeInstantiation(source_witness) => {
                        GeneralizationParentCarriers::GeneralizedWitness(source_witness)
                    }
                    ProjectionProofCarrier::Incomplete => return None,
                });
            }
            return Some(match parent {
                GeneralizationParent::Constraint(record) => {
                    GeneralizationParentCarriers::Constraint(record)
                }
                GeneralizationParent::Bound(record) => GeneralizationParentCarriers::Bound(record),
                GeneralizationParent::BoundClaim { .. } => unreachable!(),
                GeneralizationParent::BoundProjectionProof { .. } => unreachable!(),
            });
        };
        let claim_record = self.proof_store.upper_claim(claim);
        let claim_root = claim_record.map(|claim| claim.coverage_root);
        let linked = self.bounds.record(bound).is_some()
            && claim_record.is_some()
            && self
                .proof_store
                .projection_claims_for_record(bound)
                .iter()
                .any(|linked| {
                    *linked == claim
                        || self.proof_store.upper_claim(*linked).is_some_and(|linked| {
                            linked.coverage_root == claim_root.expect("checked claim")
                        })
                });
        debug_assert!(
            linked,
            "claim-qualified generalization parent must link claim {claim:?} to bound {bound:?}"
        );
        let claim_record = claim_record.filter(|_| linked)?;
        Some(match claim_record.full_lineage {
            proof::UpperClaimLineage::Original => {
                GeneralizationParentCarriers::Constraint(claim_record.producer)
            }
            proof::UpperClaimLineage::ReplayConstraint { result, .. }
            | proof::UpperClaimLineage::StructuralConstraint { result, .. }
            | proof::UpperClaimLineage::ReductionRouteConstraint { result, .. } => {
                GeneralizationParentCarriers::Constraint(result)
            }
            proof::UpperClaimLineage::ReplayEvidence { replay, .. } => {
                GeneralizationParentCarriers::ReplayEvidence {
                    lower: replay.lower,
                    upper: replay.upper,
                }
            }
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GeneralizationDerivationRule {
    BoundCollection,
    StructuralProjection,
    VariableSubstitution,
    SandwichSimplification,
    RecursiveBoundExtraction,
    Finalization,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GeneralizationDerivation {
    pub rule: GeneralizationDerivationRule,
    pub parents: Vec<GeneralizationParent>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneralizedSchemeRecord {
    pub owner: DefId,
    pub generation: u32,
    pub witnesses: Vec<GeneralizedSchemeWitnessId>,
    pub completeness: ProvenanceCompleteness,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneralizedSchemeWitness {
    pub scheme: GeneralizedSchemeRecordId,
    pub path: GeneralizedTypePath,
    pub role: GeneralizedWitnessRole,
    pub incoming: Vec<GeneralizationDerivation>,
    pub completeness: ProvenanceCompleteness,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchemeInstantiationRecord {
    pub source: GeneralizedSchemeRecordId,
    pub owner: DefId,
    pub target: DefId,
    pub use_value: TypeVar,
    pub completeness: ProvenanceCompleteness,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SchemeInstantiationDerivation {
    pub instantiation: SchemeInstantiationId,
    pub source_witness: GeneralizedSchemeWitnessId,
    pub path: GeneralizedTypePath,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct SchemeInstantiationKey {
    source: GeneralizedSchemeRecordId,
    owner: DefId,
    target: DefId,
    use_value: TypeVar,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct SchemeInstantiationRoute {
    pub derivation: SchemeInstantiationDerivation,
    pub remaining: GeneralizedTypePath,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GeneralizedWitnessDraft {
    pub path: GeneralizedTypePath,
    pub role: GeneralizedWitnessRole,
    pub incoming: Vec<GeneralizationDerivation>,
    pub completeness: ProvenanceCompleteness,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundDispositionRecordId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundDirection {
    Lower,
    Upper,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundEndpoint {
    Lower(PosId),
    Upper(NegId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundRecordState {
    Evidence,
    Ordinary,
    Tombstone,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundTrivialReason {
    TerminalWeightErasure,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstraintCanonicalizationDisposition {
    TerminalWeightErasure {
        attempted_weights: ConstraintWeights,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundDisposition {
    Inserted(BoundRecordId),
    EquivalentTo(BoundRecordId),
    SubsumedBy(BoundRecordId),
    Trivial(BoundTrivialReason),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundDispositionRecord {
    direction: BoundDirection,
    owner: TypeVar,
    endpoint: BoundEndpoint,
    weights: ConstraintWeights,
    derivation: Option<BoundDerivation>,
    disposition: BoundDisposition,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BoundDerivation {
    Constraint(ConstraintRecordId),
    Origin(OriginId),
    ReplayEvidence(BinaryReplayDerivation),
    Row(RowDerivationId),
    SchemeInstantiation(SchemeInstantiationDerivation),
    IncompleteReplay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReplayRule {
    LowerBoundAdded,
    UpperBoundAdded,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BinaryReplayDerivation {
    pub pivot: TypeVar,
    pub lower: BoundRecordId,
    pub upper: BoundRecordId,
    pub rule: ReplayRule,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReplayDerivationEdge {
    pub result: ConstraintRecordId,
    pub derivation: BinaryReplayDerivation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReplayDropRecordId(u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ReplayDropRecord {
    attempted: SubtypeConstraintKey,
    derivation: BinaryReplayDerivation,
}

// Section 9 of the provenance redesign spec records the measurements and safety factors behind
// these limits. The byte limit is a stable logical-allocation proxy, not allocator-reported RSS.
const DEFAULT_REPLAY_DERIVATION_BYTES: usize = 64 * 1024 * 1024;
const DEFAULT_REPLAY_DERIVATIONS_PER_RECORD: usize = 4_096;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProvenanceCompleteness {
    Complete,
    Incomplete,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ReplayDerivationBudget {
    max_bytes_proxy: usize,
    max_incoming_per_record: usize,
}

impl Default for ReplayDerivationBudget {
    fn default() -> Self {
        Self {
            max_bytes_proxy: DEFAULT_REPLAY_DERIVATION_BYTES,
            max_incoming_per_record: DEFAULT_REPLAY_DERIVATIONS_PER_RECORD,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ReplayDerivationStorage {
    bytes_proxy: usize,
    max_incoming_per_record: usize,
    incomplete_records: usize,
    completeness: ProvenanceCompleteness,
}

impl Default for ReplayDerivationStorage {
    fn default() -> Self {
        Self {
            bytes_proxy: 0,
            max_incoming_per_record: 0,
            incomplete_records: 0,
            completeness: ProvenanceCompleteness::Complete,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReplayDerivationInsert {
    Inserted,
    Duplicate,
    Incomplete,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundRecord {
    direction: BoundDirection,
    owner: TypeVar,
    endpoint: BoundEndpoint,
    weights: ConstraintWeights,
    state: BoundRecordState,
    derivations: Vec<BoundDerivation>,
    disposition: Option<BoundDispositionRecordId>,
}

impl BoundRecord {
    pub fn direction(&self) -> BoundDirection {
        self.direction
    }

    pub fn owner(&self) -> TypeVar {
        self.owner
    }

    pub fn endpoint(&self) -> BoundEndpoint {
        self.endpoint
    }

    pub fn weights(&self) -> &ConstraintWeights {
        &self.weights
    }

    pub fn state(&self) -> BoundRecordState {
        self.state
    }

    pub fn derivations(&self) -> &[BoundDerivation] {
        &self.derivations
    }

    pub fn disposition(&self) -> Option<BoundDispositionRecordId> {
        self.disposition
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum BoundSemanticKey {
    Lower {
        owner: TypeVar,
        endpoint: PosId,
        weights: ConstraintWeights,
    },
    Upper {
        owner: TypeVar,
        endpoint: NegId,
        weights: ConstraintWeights,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BoundInsertResult {
    id: BoundRecordId,
    semantic_changed: bool,
    provenance_changed: bool,
    promoted: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
/// effect 変数ごとの `S-subtract` fact。
///
/// これは subtype bound ではない。effect row から何を引けるかという事実を独立に持ち、
/// scheme 化や subtract 解釈の段階で読む。
pub struct SubtractTable {
    facts: FxHashMap<TypeVar, Vec<SubtractFact>>,
    fact_ids: FxHashMap<TypeVar, Vec<SubtractFactRecordId>>,
    record_ids_by_subtract: FxHashMap<SubtractId, Vec<SubtractFactRecordId>>,
    canonical: FxHashMap<SubtractFactKey, SubtractFactRecordId>,
    records: Vec<SubtractFactRecord>,
}

impl SubtractTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn facts(&self, effect: TypeVar) -> &[SubtractFact] {
        #[cfg(test)]
        crate::analysis::record_owner_subtract_read(effect);
        self.facts.get(&effect).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn record_ids(&self, effect: TypeVar) -> &[SubtractFactRecordId] {
        self.fact_ids.get(&effect).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn fact_by_id(&self, id: SubtractId) -> Option<&SubtractFact> {
        self.facts
            .values()
            .flat_map(|facts| facts.iter())
            .find(|fact| fact.id == id)
    }

    pub fn record(&self, id: SubtractFactRecordId) -> Option<&SubtractFactRecord> {
        self.records.get(id.0 as usize)
    }

    #[cfg(test)]
    fn record_id(&self, effect: TypeVar, fact: &SubtractFact) -> Option<SubtractFactRecordId> {
        self.canonical
            .get(&SubtractFactKey {
                effect,
                fact: fact.clone(),
            })
            .copied()
    }

    fn insert(
        &mut self,
        effect: TypeVar,
        fact: SubtractFact,
        derivation: SubtractFactDerivation,
    ) -> SubtractFactInsertResult {
        let key = SubtractFactKey {
            effect,
            fact: fact.clone(),
        };
        if let Some(id) = self.canonical.get(&key).copied() {
            let record = &mut self.records[id.0 as usize];
            let provenance_changed = if record.derivations.contains(&derivation) {
                false
            } else {
                record.derivations.push(derivation);
                true
            };
            return SubtractFactInsertResult {
                id,
                semantic_changed: false,
                provenance_changed,
            };
        }
        let id = SubtractFactRecordId(self.records.len() as u32);
        self.canonical.insert(key.clone(), id);
        self.records.push(SubtractFactRecord {
            key,
            active: true,
            derivations: vec![derivation],
            uses: Vec::new(),
        });
        self.fact_ids.entry(effect).or_default().push(id);
        self.record_ids_by_subtract
            .entry(fact.id)
            .or_default()
            .push(id);
        self.facts.entry(effect).or_default().push(fact);
        SubtractFactInsertResult {
            id,
            semantic_changed: true,
            provenance_changed: true,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SubtractFactRecordId(u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SubtractFactKey {
    effect: TypeVar,
    fact: SubtractFact,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SubtractFactDerivation {
    Declaration(OriginId),
    Import(OriginId),
    Internal(OriginId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SubtractFactUseRule {
    Weight,
    Filter,
    RowReduction,
    PayloadInvariant,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SubtractFactUse {
    rule: SubtractFactUseRule,
    consumer: Option<ConstraintRecordId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubtractFactRecord {
    key: SubtractFactKey,
    active: bool,
    derivations: Vec<SubtractFactDerivation>,
    uses: Vec<SubtractFactUse>,
}

impl SubtractFactRecord {
    pub fn effect(&self) -> TypeVar {
        self.key.effect
    }

    pub fn fact(&self) -> &SubtractFact {
        &self.key.fact
    }

    pub fn is_active(&self) -> bool {
        self.active
    }

    pub fn derivations(&self) -> &[SubtractFactDerivation] {
        &self.derivations
    }

    pub fn uses(&self) -> &[SubtractFactUse] {
        &self.uses
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SubtractFactInsertResult {
    id: SubtractFactRecordId,
    semantic_changed: bool,
    provenance_changed: bool,
}

/// subtype edge の片側に載る stack weight。
pub type ConstraintWeight = StackWeight;
pub type LeftConstraintWeight = DirectedLeftConstraintWeight;
pub type RightConstraintWeight = RightStackWeight;

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
/// subtype edge の左右に載る subtract weight。
///
/// 関数引数のように polarity が反転する場所では `swapped()` で左右を入れ替える。
/// bounds の再伝播では `compose_for_replay()` し、経路の情報をまとめる。
/// W-Mix は意味論側の directed projection だが、その後の pop cap は
/// worklist 停止性のための実装ガードであり、型等式としては使わない。
pub struct ConstraintWeights {
    pub left: LeftConstraintWeight,
    pub right: RightConstraintWeight,
}

impl ConstraintWeights {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.left.is_empty() && self.right.is_empty()
    }

    pub fn swapped(&self) -> Self {
        Self {
            left: LeftConstraintWeight::from_right_weight(&self.right),
            right: RightConstraintWeight::from_stack_weight_pops(&self.left.to_stack_weight()),
        }
    }

    pub fn with_left(&self, id: SubtractId) -> Self {
        self.with_left_prefix(StackWeight::pop(id))
    }

    pub fn with_left_prefix(&self, weight: StackWeight) -> Self {
        Self {
            left: LeftConstraintWeight::from_stack_weight(&weight).compose(&self.left),
            right: self.right.clone(),
        }
    }

    pub fn with_right_suffix(&self, weight: StackWeight) -> Self {
        Self {
            left: self.left.clone(),
            right: RightConstraintWeight::from_stack_weight_pops(&weight).compose(&self.right),
        }
    }

    pub fn both_from_right(&self) -> Self {
        Self {
            left: LeftConstraintWeight::from_right_weight(&self.right),
            right: self.right.clone(),
        }
    }

    pub fn compose_for_replay(&self, other: &Self) -> Self {
        // Left weights follow the lower-to-upper path order. Right weights describe upper-side
        // stack wrappers, so replaying through a later upper bound nests that bound outside the
        // earlier one; its weight must be prepended.
        Self {
            left: self.left.compose(&other.left),
            right: other.right.compose(&self.right),
        }
        .normalize_directed_mix()
    }

    pub fn normalize_for_var_var_replay_key(&self) -> Self {
        self.clone().normalize_directed_mix()
    }

    pub fn left_filter_set(&self) -> &Subtractability {
        self.left.filter_set()
    }

    pub fn without_left_filter(&self) -> Self {
        Self {
            left: self.left.without_filter(),
            right: self.right.clone(),
        }
    }

    fn normalize_directed_mix(self) -> Self {
        if self.right.is_empty() {
            return self;
        }

        let mixed = DirectedWeights {
            left: self.left.directed().clone(),
            right: self.right,
        }
        .mix();
        Self {
            left: self.left.with_directed_weight(mixed.left),
            right: mixed.right,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// 1本の canonical weighted subtype constraint の semantic key。
///
/// `lower <: upper` という直接の要求と、その要求が通ってきた subtract weight を一体で持つ。
pub struct SubtypeConstraintKey {
    pub lower: PosId,
    pub upper: NegId,
    pub weights: ConstraintWeights,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// 1 inference session 内の canonical subtype constraint record ID。
pub struct ConstraintRecordId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RowDerivationId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RowResidualRecordId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LowerFilterRecordId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RowDerivationParent {
    Constraint(ConstraintRecordId),
    Bound(BoundRecordId),
    SubtractFact(SubtractFactRecordId),
    RowDerivation(RowDerivationId),
    LowerFilter(LowerFilterRecordId),
    Origin(OriginId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RowDerivationRule {
    WeightedResidual,
    UnweightedReduction,
    RowItemMatch,
    FilterInvariant,
    PayloadInvariant,
    SubtractFactTransformation,
    StoreUpperWithoutReplay,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RowDerivation {
    rule: RowDerivationRule,
    parents: Vec<RowDerivationParent>,
    retained_items: Vec<NegId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RowResidualRecord {
    key: RowResidualKey,
    gamma: TypeVar,
    derivations: Vec<RowDerivationId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LowerFilterRecord {
    var: TypeVar,
    filter: Subtractability,
    derivations: Vec<LowerFilterDerivation>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct LowerFilterDerivation {
    parents: Vec<RowDerivationParent>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructuralIndex(u32);

impl StructuralIndex {
    pub(crate) fn from_usize(index: usize) -> Self {
        Self(u32::try_from(index).expect("structural index fits in u32"))
    }

    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InvariantDirection {
    LowerToUpper,
    UpperToLower,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RecordSpreadKind {
    Head,
    Tail,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RowItemRoute {
    Matched,
    DirectToUpperTail,
    MarkerAggregateToUpperTail,
    VariableToRemainingRow,
    UpperTailToMarkerItems,
    UpperTailToDirectItems,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StructuralDerivationRule {
    LowerStackNormalization,
    LowerNonSubtractNormalization,
    UpperStackNormalization,
    UnionBranch {
        branch: StructuralIndex,
    },
    IntersectionBranch {
        branch: StructuralIndex,
    },
    FunctionArgument,
    FunctionArgumentEffect {
        pure_passthrough: bool,
    },
    FunctionReturnEffect,
    FunctionReturn,
    ConstructorArgument {
        index: StructuralIndex,
        direction: InvariantDirection,
    },
    TupleElement {
        index: StructuralIndex,
    },
    RecordField {
        index: StructuralIndex,
    },
    RecordSpreadField {
        spread: RecordSpreadKind,
        index: StructuralIndex,
    },
    RecordSpreadTail {
        spread: RecordSpreadKind,
        index: StructuralIndex,
    },
    VariantPayload {
        variant_index: StructuralIndex,
        payload_index: StructuralIndex,
    },
    RowItem {
        index: StructuralIndex,
        route: RowItemRoute,
    },
    RowItemArgument {
        item_index: StructuralIndex,
        argument_index: StructuralIndex,
        direction: InvariantDirection,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructuralDerivation {
    parent: ConstraintRecordId,
    rule: StructuralDerivationRule,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// 1 inference session 内の source boundary ID。
pub struct SourceBoundaryId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// 1 inference session 内の root constraint origin ID。
pub struct OriginId(u32);

impl OriginId {
    const INTERNAL: Self = Self(0);
    const UNKNOWN_INTERNAL: Self = Self(1);

    pub fn internal() -> Self {
        Self::INTERNAL
    }

    pub fn unknown_internal() -> Self {
        Self::UNKNOWN_INTERNAL
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConstraintOriginKind {
    ApplicationArgument,
    Pattern,
    Annotation,
    Return,
    Field,
    Assignment,
    BodyRequirement(BodyRequirementKind),
    Internal,
    UnknownInternal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BodyRequirementKind {
    BooleanCondition,
    OperatorOperand { operand: StructuralIndex },
    PatternGuard,
    CalleeArgument { argument: StructuralIndex },
}

impl ConstraintOriginKind {
    fn is_source(self) -> bool {
        matches!(
            self,
            Self::ApplicationArgument
                | Self::Pattern
                | Self::Annotation
                | Self::Return
                | Self::Field
                | Self::Assignment
                | Self::BodyRequirement(_)
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceBoundaryOrigin {
    boundary: SourceBoundaryId,
    origin: OriginId,
}

impl SourceBoundaryOrigin {
    pub fn boundary(self) -> SourceBoundaryId {
        self.boundary
    }

    pub fn origin(self) -> OriginId {
        self.origin
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ConstraintRecord {
    key: SubtypeConstraintKey,
    /// Root leaves are additive metadata and never participate in semantic equality or queueing.
    root_origins: Vec<OriginId>,
    structural_derivations: Vec<StructuralDerivation>,
    row_derivations: Vec<RowDerivationId>,
    replay_derivations: Vec<BinaryReplayDerivation>,
    scheme_instantiation_derivations: Vec<SchemeInstantiationDerivation>,
    scheme_instantiation_routes: Vec<SchemeInstantiationRoute>,
    canonicalization_dispositions: Vec<ConstraintCanonicalizationDisposition>,
    replay_provenance: ProvenanceCompleteness,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct OriginRecord {
    kind: ConstraintOriginKind,
    source_boundary: Option<SourceBoundaryId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SourceBoundaryRecord {
    origin: OriginId,
    location_recorded: bool,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DebugConstraintTraceNode {
    pub(crate) record: ConstraintRecordId,
    pub(crate) key: SubtypeConstraintKey,
    pub(crate) root_origins: Vec<OriginId>,
    pub(crate) structural_derivations: Vec<StructuralDerivation>,
    pub(crate) row_derivations: Vec<RowDerivationId>,
    pub(crate) replay_derivations: Vec<BinaryReplayDerivation>,
    pub(crate) canonicalization_dispositions: Vec<ConstraintCanonicalizationDisposition>,
    pub(crate) replay_provenance: ProvenanceCompleteness,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DebugReplayParentTrace {
    pub(crate) bound: BoundRecordId,
    pub(crate) owner: TypeVar,
    pub(crate) endpoint: BoundEndpoint,
    pub(crate) derivations: Vec<BoundDerivation>,
    pub(crate) origins: Vec<OriginId>,
    pub(crate) source_origins: Vec<OriginId>,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DebugReplayWitness {
    pub(crate) edge: ReplayDerivationEdge,
    pub(crate) lower: DebugReplayParentTrace,
    pub(crate) upper: DebugReplayParentTrace,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// 1つの `S-subtract` fact。
///
/// `id` は weight として subtype edge に載る識別子、`subtractability` はその ID が表す引き算の内容。
pub struct SubtractFact {
    pub id: SubtractId,
    pub subtractability: Subtractability,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ConstraintEffectFamily {
    pub(crate) path: Vec<String>,
    pub(crate) args: Vec<NeuId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct EffectFamily {
    path: Vec<String>,
    args: Vec<NeuId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct EffectFilterViolationKey {
    effect: Option<Vec<String>>,
    filter: Subtractability,
}

#[derive(Debug, Default)]
struct ReplayFrontierShadow {
    lower_var_var_seen: FxHashSet<ReplayFrontierVarVarBoundKey>,
    upper_var_var_seen: FxHashSet<ReplayFrontierVarVarBoundKey>,
    lower_var_var: ReplayFrontierShadowMetrics,
    upper_var_var: ReplayFrontierShadowMetrics,
}

impl ReplayFrontierShadow {
    fn from_env() -> Option<Self> {
        std::env::var("YULANG_REPLAY_FRONTIER_SHADOW")
            .is_ok_and(|value| !value.is_empty() && value != "0")
            .then(Self::default)
    }

    fn observe_lower_var_var(
        &mut self,
        pivot: TypeVar,
        endpoint: TypeVar,
        weights: &ConstraintWeights,
    ) -> ReplayFrontierShadowObservation {
        observe_var_var_frontier(
            &mut self.lower_var_var_seen,
            &mut self.lower_var_var,
            pivot,
            endpoint,
            weights,
        )
    }

    fn observe_upper_var_var(
        &mut self,
        pivot: TypeVar,
        endpoint: TypeVar,
        weights: &ConstraintWeights,
    ) -> ReplayFrontierShadowObservation {
        observe_var_var_frontier(
            &mut self.upper_var_var_seen,
            &mut self.upper_var_var,
            pivot,
            endpoint,
            weights,
        )
    }

    fn record_lower_result(
        &mut self,
        observation: ReplayFrontierShadowObservation,
        accepted: usize,
    ) {
        record_var_var_frontier_result(&mut self.lower_var_var, observation, accepted);
    }

    fn record_upper_result(
        &mut self,
        observation: ReplayFrontierShadowObservation,
        accepted: usize,
    ) {
        record_var_var_frontier_result(&mut self.upper_var_var, observation, accepted);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ReplayFrontierVarVarBoundKey {
    pivot: TypeVar,
    endpoint: TypeVar,
    weights: ConstraintWeights,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReplayFrontierShadowObservation {
    NotCandidate,
    New,
    Hit,
}

fn observe_var_var_frontier(
    seen: &mut FxHashSet<ReplayFrontierVarVarBoundKey>,
    metrics: &mut ReplayFrontierShadowMetrics,
    pivot: TypeVar,
    endpoint: TypeVar,
    weights: &ConstraintWeights,
) -> ReplayFrontierShadowObservation {
    metrics.candidates += 1;
    let key = ReplayFrontierVarVarBoundKey {
        pivot,
        endpoint,
        weights: weights.normalize_for_var_var_replay_key(),
    };
    if seen.insert(key) {
        ReplayFrontierShadowObservation::New
    } else {
        metrics.hits += 1;
        ReplayFrontierShadowObservation::Hit
    }
}

fn record_var_var_frontier_result(
    metrics: &mut ReplayFrontierShadowMetrics,
    observation: ReplayFrontierShadowObservation,
    accepted: usize,
) {
    if observation != ReplayFrontierShadowObservation::Hit {
        return;
    }
    if accepted == 0 {
        metrics.safe_hits += 1;
    } else {
        metrics.unsafe_hits += 1;
        metrics.unsafe_accepted += accepted;
    }
}

#[derive(Debug, Default)]
struct ReplayRoutingShadow {
    unweighted_enabled: bool,
    graph: FxHashMap<TypeVar, FxHashSet<TypeVar>>,
    nodes: FxHashSet<TypeVar>,
    endpoint_seen: FxHashSet<(TypeVar, TypeVar)>,
    metrics: ReplayRoutingShadowMetrics,
    weighted: Option<ReplayWeightedRoutingShadow>,
}

impl ReplayRoutingShadow {
    fn from_env() -> Option<Self> {
        let unweighted = std::env::var("YULANG_REPLAY_ROUTING_SHADOW")
            .is_ok_and(|value| !value.is_empty() && value != "0");
        let weighted = ReplayWeightedRoutingShadow::from_env();
        (unweighted || weighted.is_some()).then(|| Self {
            unweighted_enabled: unweighted,
            weighted,
            ..Self::default()
        })
    }

    fn observe_var_var_edge(
        &mut self,
        source: TypeVar,
        target: TypeVar,
        weights: &ConstraintWeights,
    ) {
        if source == target {
            return;
        }
        if let Some(weighted) = &mut self.weighted {
            weighted.observe_edge(source, target, weights);
        }
        if !self.unweighted_enabled {
            return;
        }
        self.metrics.accepted_edges += 1;
        if !self.endpoint_seen.insert((source, target)) {
            self.metrics.repeated_endpoint_edges += 1;
        }
        if self.reaches(source, target) {
            self.metrics.reachable_before_edges += 1;
        }
        self.nodes.insert(source);
        self.nodes.insert(target);
        if self.graph.entry(source).or_default().insert(target) {
            self.metrics.graph_edges += 1;
        }
        self.metrics.graph_nodes = self.nodes.len();
    }

    fn observe_var_var_consequence(
        &mut self,
        source: TypeVar,
        target: TypeVar,
        weights: &ConstraintWeights,
        seen_before: bool,
    ) {
        if source == target {
            return;
        }
        if let Some(weighted) = &mut self.weighted {
            weighted.observe_consequence(source, target, weights, seen_before);
        }
    }

    fn has_weighted_frontier_path(
        &mut self,
        source: TypeVar,
        target: TypeVar,
        weights: &ConstraintWeights,
    ) -> bool {
        self.weighted
            .as_mut()
            .is_some_and(|weighted| weighted.has_frontier_path(source, target, weights))
    }

    fn reaches(&self, source: TypeVar, target: TypeVar) -> bool {
        let mut stack = vec![source];
        let mut visited = FxHashSet::default();
        while let Some(var) = stack.pop() {
            if !visited.insert(var) {
                continue;
            }
            let Some(next) = self.graph.get(&var) else {
                continue;
            };
            if next.contains(&target) {
                return true;
            }
            stack.extend(next.iter().copied());
        }
        false
    }
}

#[derive(Debug)]
struct ReplayWeightedRoutingShadow {
    graph: FxHashMap<TypeVar, Vec<ReplayWeightedRouteEdge>>,
    frontier_graph: FxHashMap<TypeVar, Vec<ReplayWeightedRouteEdge>>,
    nodes: FxHashSet<TypeVar>,
    frontier_nodes: FxHashSet<TypeVar>,
    positive_paths: FxHashSet<ReplayWeightedPathKey>,
    frontier_positive_paths: FxHashSet<ReplayWeightedPathKey>,
    summary: Option<ReplayWeightedPathSummary>,
    weights: ReplayWeightInterner,
    metrics: ReplayWeightedRoutingShadowMetrics,
    search_limit: usize,
    all_edge_search_enabled: bool,
    frontier_search_enabled: bool,
}

impl ReplayWeightedRoutingShadow {
    fn from_env() -> Option<Self> {
        let weighted = std::env::var("YULANG_REPLAY_WEIGHTED_ROUTING_SHADOW")
            .is_ok_and(|value| !value.is_empty() && value != "0");
        let evidence_skip = evidence_only_replay_skip_enabled();
        let summary = ReplayWeightedPathSummary::from_env();
        let search_limit = if weighted {
            replay_weighted_routing_shadow_limit()
        } else {
            replay_evidence_only_skip_limit()
        };
        (weighted || evidence_skip || summary.is_some()).then(|| Self {
            graph: FxHashMap::default(),
            frontier_graph: FxHashMap::default(),
            nodes: FxHashSet::default(),
            frontier_nodes: FxHashSet::default(),
            positive_paths: FxHashSet::default(),
            frontier_positive_paths: FxHashSet::default(),
            summary,
            weights: ReplayWeightInterner::default(),
            metrics: ReplayWeightedRoutingShadowMetrics::default(),
            search_limit,
            all_edge_search_enabled: weighted,
            frontier_search_enabled: weighted || evidence_skip,
        })
    }

    fn observe_edge(&mut self, source: TypeVar, target: TypeVar, weights: &ConstraintWeights) {
        if source == target {
            return;
        }
        self.metrics.accepted_edges += 1;
        let weight = self.weights.intern(weights.clone());
        if let Some(summary) = &mut self.summary {
            summary.observe_edge(source, target, weight, &mut self.weights);
            self.metrics.summary_observed_edges = summary.metrics.observed_edges;
            self.metrics.summary_known_edges = summary.metrics.known_edges;
            self.metrics.summary_new_edges = summary.metrics.new_edges;
            self.metrics.summary_inserted_paths = summary.metrics.inserted_paths;
            self.metrics.summary_duplicate_paths = summary.metrics.duplicate_paths;
            self.metrics.summary_capped_insertions = summary.metrics.capped_insertions;
            self.metrics.summary_max_queue = summary.metrics.max_queue;
            self.metrics.summary_paths = summary.paths.len();
            self.metrics.summary_outgoing_nodes = summary.outgoing.len();
            self.metrics.summary_incoming_nodes = summary.incoming.len();
        }
        if !self.all_edge_search_enabled && !self.frontier_search_enabled {
            self.metrics.weight_count = self.weights.len();
            self.metrics.compose_cache_hits = self.weights.compose_hits;
            self.metrics.compose_cache_misses = self.weights.compose_misses;
            return;
        }

        if self.all_edge_search_enabled {
            let search = search_exact_weighted_route(
                &self.graph,
                &mut self.positive_paths,
                &mut self.weights,
                self.search_limit,
                source,
                target,
                weight,
            );
            if search.cache_hit {
                self.metrics.route_cache_hits += 1;
            }
            self.metrics.search_states += search.states;
            self.metrics.max_search_states = self.metrics.max_search_states.max(search.states);
            if search.capped {
                self.metrics.capped_searches += 1;
            }
            if search.found {
                self.metrics.reachable_before_edges += 1;
            }
        }

        if self.frontier_search_enabled {
            let frontier_search = search_exact_weighted_route(
                &self.frontier_graph,
                &mut self.frontier_positive_paths,
                &mut self.weights,
                self.search_limit,
                source,
                target,
                weight,
            );
            if frontier_search.cache_hit {
                self.metrics.frontier_route_cache_hits += 1;
            }
            self.metrics.frontier_search_states += frontier_search.states;
            self.metrics.frontier_max_search_states = self
                .metrics
                .frontier_max_search_states
                .max(frontier_search.states);
            if frontier_search.capped {
                self.metrics.frontier_capped_searches += 1;
            }
            if frontier_search.found {
                self.metrics.frontier_skipped_edges += 1;
            } else {
                self.frontier_nodes.insert(source);
                self.frontier_nodes.insert(target);
                self.frontier_graph
                    .entry(source)
                    .or_default()
                    .push(ReplayWeightedRouteEdge { target, weight });
                self.frontier_positive_paths
                    .insert(ReplayWeightedPathKey::new(source, target, weight));
                self.metrics.frontier_inserted_edges += 1;
                self.metrics.frontier_graph_nodes = self.frontier_nodes.len();
                self.metrics.frontier_graph_edges += 1;
            }
        }

        if self.all_edge_search_enabled {
            self.nodes.insert(source);
            self.nodes.insert(target);
            self.graph
                .entry(source)
                .or_default()
                .push(ReplayWeightedRouteEdge { target, weight });
            self.positive_paths
                .insert(ReplayWeightedPathKey::new(source, target, weight));
            self.metrics.graph_nodes = self.nodes.len();
            self.metrics.graph_edges += 1;
        }
        self.metrics.route_cache_entries = self.positive_paths.len();
        self.metrics.frontier_route_cache_entries = self.frontier_positive_paths.len();
        self.metrics.weight_count = self.weights.len();
        self.metrics.compose_cache_hits = self.weights.compose_hits;
        self.metrics.compose_cache_misses = self.weights.compose_misses;
    }

    fn has_frontier_path(
        &mut self,
        source: TypeVar,
        target: TypeVar,
        weights: &ConstraintWeights,
    ) -> bool {
        if source == target {
            return false;
        }
        let weight = self.weights.intern(weights.clone());
        let search = search_exact_weighted_route(
            &self.frontier_graph,
            &mut self.frontier_positive_paths,
            &mut self.weights,
            self.search_limit,
            source,
            target,
            weight,
        );
        if search.cache_hit {
            self.metrics.frontier_route_cache_hits += 1;
        }
        if search.capped {
            self.metrics.frontier_capped_searches += 1;
        }
        self.metrics.frontier_search_states += search.states;
        self.metrics.frontier_max_search_states =
            self.metrics.frontier_max_search_states.max(search.states);
        self.metrics.weight_count = self.weights.len();
        self.metrics.compose_cache_hits = self.weights.compose_hits;
        self.metrics.compose_cache_misses = self.weights.compose_misses;
        search.found
    }

    fn observe_consequence(
        &mut self,
        source: TypeVar,
        target: TypeVar,
        weights: &ConstraintWeights,
        seen_before: bool,
    ) {
        if !self.all_edge_search_enabled {
            return;
        }
        self.metrics.consequence_queries += 1;
        let weight = self.weights.intern(weights.clone());
        let search = search_exact_weighted_route(
            &self.graph,
            &mut self.positive_paths,
            &mut self.weights,
            self.search_limit,
            source,
            target,
            weight,
        );
        if search.cache_hit {
            self.metrics.route_cache_hits += 1;
        }
        self.metrics.consequence_search_states += search.states;
        self.metrics.consequence_max_search_states = self
            .metrics
            .consequence_max_search_states
            .max(search.states);
        if search.capped {
            self.metrics.consequence_capped_searches += 1;
        }
        if search.found {
            self.metrics.consequence_known += 1;
            if !seen_before {
                self.metrics.consequence_known_unseen += 1;
            }
        } else {
            self.metrics.consequence_unknown += 1;
            if seen_before {
                self.metrics.consequence_unknown_seen += 1;
            }
        }

        let frontier_search = search_exact_weighted_route(
            &self.frontier_graph,
            &mut self.frontier_positive_paths,
            &mut self.weights,
            self.search_limit,
            source,
            target,
            weight,
        );
        if frontier_search.cache_hit {
            self.metrics.frontier_route_cache_hits += 1;
        }
        self.metrics.consequence_frontier_search_states += frontier_search.states;
        self.metrics.consequence_frontier_max_search_states = self
            .metrics
            .consequence_frontier_max_search_states
            .max(frontier_search.states);
        if frontier_search.capped {
            self.metrics.consequence_frontier_capped_searches += 1;
        }
        if frontier_search.found {
            self.metrics.consequence_frontier_known += 1;
            if !seen_before {
                self.metrics.consequence_frontier_known_unseen += 1;
            }
        } else {
            self.metrics.consequence_frontier_unknown += 1;
            if seen_before {
                self.metrics.consequence_frontier_unknown_seen += 1;
            }
        }
        self.metrics.route_cache_entries = self.positive_paths.len();
        self.metrics.frontier_route_cache_entries = self.frontier_positive_paths.len();
        self.metrics.weight_count = self.weights.len();
        self.metrics.compose_cache_hits = self.weights.compose_hits;
        self.metrics.compose_cache_misses = self.weights.compose_misses;
    }
}

fn search_exact_weighted_route(
    graph: &FxHashMap<TypeVar, Vec<ReplayWeightedRouteEdge>>,
    positive_paths: &mut FxHashSet<ReplayWeightedPathKey>,
    weights: &mut ReplayWeightInterner,
    search_limit: usize,
    source: TypeVar,
    target: TypeVar,
    target_weight: ReplayWeightId,
) -> ReplayWeightedRouteSearch {
    let key = ReplayWeightedPathKey::new(source, target, target_weight);
    if positive_paths.contains(&key) {
        return ReplayWeightedRouteSearch {
            found: true,
            capped: false,
            cache_hit: true,
            states: 0,
        };
    }
    let empty = weights.empty();
    let mut stack = vec![ReplayWeightedRouteState {
        var: source,
        weight: empty,
    }];
    let mut visited = FxHashSet::default();
    let mut local_states = 0usize;
    while let Some(state) = stack.pop() {
        if !visited.insert(state) {
            continue;
        }
        let edges = graph.get(&state.var).cloned().unwrap_or_default();
        for edge in edges {
            local_states += 1;
            if local_states > search_limit {
                return ReplayWeightedRouteSearch {
                    found: false,
                    capped: true,
                    cache_hit: false,
                    states: local_states,
                };
            }
            let next_weight = weights.compose_for_replay(state.weight, edge.weight);
            if edge.target == target && next_weight == target_weight {
                positive_paths.insert(key);
                return ReplayWeightedRouteSearch {
                    found: true,
                    capped: false,
                    cache_hit: false,
                    states: local_states,
                };
            }
            stack.push(ReplayWeightedRouteState {
                var: edge.target,
                weight: next_weight,
            });
        }
    }
    ReplayWeightedRouteSearch {
        found: false,
        capped: false,
        cache_hit: false,
        states: local_states,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ReplayWeightedRouteSearch {
    found: bool,
    capped: bool,
    cache_hit: bool,
    states: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ReplayWeightedRouteEdge {
    target: TypeVar,
    weight: ReplayWeightId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayWeightedRouteState {
    var: TypeVar,
    weight: ReplayWeightId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayWeightedPathKey {
    source: TypeVar,
    target: TypeVar,
    weight: ReplayWeightId,
}

impl ReplayWeightedPathKey {
    fn new(source: TypeVar, target: TypeVar, weight: ReplayWeightId) -> Self {
        Self {
            source,
            target,
            weight,
        }
    }
}

#[derive(Debug)]
struct ReplayWeightedPathSummary {
    paths: FxHashSet<ReplayWeightedPathKey>,
    outgoing: FxHashMap<TypeVar, Vec<ReplayWeightedPathSummaryEdge>>,
    incoming: FxHashMap<TypeVar, Vec<ReplayWeightedPathSummaryEdge>>,
    queue: VecDeque<ReplayWeightedPathKey>,
    metrics: ReplayWeightedPathSummaryMetrics,
    limit: usize,
    capped: bool,
}

impl ReplayWeightedPathSummary {
    fn from_env() -> Option<Self> {
        std::env::var("YULANG_REPLAY_WEIGHTED_ROUTING_SUMMARY_SHADOW")
            .is_ok_and(|value| !value.is_empty() && value != "0")
            .then(|| Self {
                paths: FxHashSet::default(),
                outgoing: FxHashMap::default(),
                incoming: FxHashMap::default(),
                queue: VecDeque::new(),
                metrics: ReplayWeightedPathSummaryMetrics::default(),
                limit: replay_weighted_routing_summary_shadow_limit(),
                capped: false,
            })
    }

    fn observe_edge(
        &mut self,
        source: TypeVar,
        target: TypeVar,
        weight: ReplayWeightId,
        weights: &mut ReplayWeightInterner,
    ) {
        self.metrics.observed_edges += 1;
        if self.capped {
            self.metrics.capped_insertions += 1;
            return;
        }
        if self
            .paths
            .contains(&ReplayWeightedPathKey::new(source, target, weight))
        {
            self.metrics.known_edges += 1;
            return;
        }
        self.metrics.new_edges += 1;
        self.insert_path(source, target, weight);
        self.close_from_queue(weights);
    }

    fn close_from_queue(&mut self, weights: &mut ReplayWeightInterner) {
        if self.capped {
            return;
        }
        while let Some(path) = self.queue.pop_front() {
            let mut prefixes = self.incoming.get(&path.source).cloned().unwrap_or_default();
            prefixes.push(ReplayWeightedPathSummaryEdge {
                var: path.source,
                weight: weights.empty(),
            });

            let mut suffixes = self.outgoing.get(&path.target).cloned().unwrap_or_default();
            suffixes.push(ReplayWeightedPathSummaryEdge {
                var: path.target,
                weight: weights.empty(),
            });

            for prefix in &prefixes {
                let prefix_weight = weights.compose_for_replay(prefix.weight, path.weight);
                for suffix in &suffixes {
                    if self.capped {
                        self.metrics.capped_insertions += 1;
                        return;
                    }
                    let weight = weights.compose_for_replay(prefix_weight, suffix.weight);
                    self.insert_path(prefix.var, suffix.var, weight);
                }
            }
            self.metrics.max_queue = self.metrics.max_queue.max(self.queue.len());
        }
    }

    fn insert_path(&mut self, source: TypeVar, target: TypeVar, weight: ReplayWeightId) {
        let key = ReplayWeightedPathKey::new(source, target, weight);
        if !self.paths.insert(key) {
            self.metrics.duplicate_paths += 1;
            return;
        }
        if self.paths.len() > self.limit {
            self.capped = true;
            self.metrics.capped_insertions += 1;
            self.paths.remove(&key);
            self.queue.clear();
            return;
        }
        self.metrics.inserted_paths += 1;
        self.outgoing
            .entry(source)
            .or_default()
            .push(ReplayWeightedPathSummaryEdge {
                var: target,
                weight,
            });
        self.incoming
            .entry(target)
            .or_default()
            .push(ReplayWeightedPathSummaryEdge {
                var: source,
                weight,
            });
        self.queue.push_back(key);
        self.metrics.max_queue = self.metrics.max_queue.max(self.queue.len());
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct ReplayWeightedPathSummaryMetrics {
    observed_edges: usize,
    known_edges: usize,
    new_edges: usize,
    inserted_paths: usize,
    duplicate_paths: usize,
    capped_insertions: usize,
    max_queue: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ReplayWeightedPathSummaryEdge {
    var: TypeVar,
    weight: ReplayWeightId,
}

#[derive(Debug, Default)]
struct ReplayWeightInterner {
    weights: Vec<ConstraintWeights>,
    ids: FxHashMap<ConstraintWeights, ReplayWeightId>,
    compose_cache: FxHashMap<(ReplayWeightId, ReplayWeightId), ReplayWeightId>,
    empty: Option<ReplayWeightId>,
    compose_hits: usize,
    compose_misses: usize,
}

impl ReplayWeightInterner {
    fn empty(&mut self) -> ReplayWeightId {
        if let Some(id) = self.empty {
            return id;
        }
        let id = self.intern(ConstraintWeights::empty());
        self.empty = Some(id);
        id
    }

    fn intern(&mut self, weights: ConstraintWeights) -> ReplayWeightId {
        if let Some(id) = self.ids.get(&weights) {
            return *id;
        }
        let id = ReplayWeightId(self.weights.len() as u32);
        self.weights.push(weights.clone());
        self.ids.insert(weights, id);
        id
    }

    fn compose_for_replay(
        &mut self,
        left: ReplayWeightId,
        right: ReplayWeightId,
    ) -> ReplayWeightId {
        let key = (left, right);
        if let Some(id) = self.compose_cache.get(&key) {
            self.compose_hits += 1;
            return *id;
        }
        self.compose_misses += 1;
        let left_weight = self.weights[left.0 as usize].clone();
        let right_weight = self.weights[right.0 as usize].clone();
        let composed = left_weight
            .compose_for_replay(&right_weight)
            .normalize_for_var_var_replay_key();
        let id = self.intern(composed);
        self.compose_cache.insert(key, id);
        id
    }

    fn len(&self) -> usize {
        self.weights.len()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayWeightId(u32);

fn replay_weighted_routing_shadow_limit() -> usize {
    std::env::var("YULANG_REPLAY_WEIGHTED_ROUTING_SHADOW_LIMIT")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|limit| *limit > 0)
        .unwrap_or(4096)
}

fn replay_weighted_routing_summary_shadow_limit() -> usize {
    std::env::var("YULANG_REPLAY_WEIGHTED_ROUTING_SUMMARY_LIMIT")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|limit| *limit > 0)
        .unwrap_or(200_000)
}

fn evidence_only_replay_skip_enabled() -> bool {
    std::env::var("YULANG_REPLAY_EVIDENCE_ONLY_SKIP")
        .is_ok_and(|value| !value.is_empty() && value != "0")
}

fn replay_evidence_only_skip_limit() -> usize {
    std::env::var("YULANG_REPLAY_EVIDENCE_ONLY_SKIP_LIMIT")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|limit| *limit > 0)
        .unwrap_or(16)
}

fn intersect_subtractability(lhs: Subtractability, rhs: Subtractability) -> Subtractability {
    lhs.intersect(rhs)
}

fn sorted_effect_families(mut families: Vec<EffectFamily>) -> Vec<EffectFamily> {
    families.sort_by(|left, right| left.path.cmp(&right.path));
    families
}

fn find_removed_family<'a>(
    family: &EffectFamily,
    removed: &'a [EffectFamily],
) -> Option<&'a EffectFamily> {
    removed.iter().find(|removed| removed.path == family.path)
}

fn families_from_pairs(families: Vec<(Vec<String>, Vec<NeuId>)>) -> Vec<EffectFamily> {
    families
        .into_iter()
        .map(|(path, args)| EffectFamily { path, args })
        .collect()
}

fn subtractability_families(subtractability: &Subtractability) -> Vec<EffectFamily> {
    match subtractability {
        Subtractability::Empty | Subtractability::All => Vec::new(),
        Subtractability::Set(path, args) | Subtractability::AllExcept(path, args) => {
            vec![EffectFamily {
                path: path.clone(),
                args: args.clone(),
            }]
        }
        Subtractability::SetMany(families) | Subtractability::AllExceptMany(families) => families
            .iter()
            .map(|(path, args)| EffectFamily {
                path: path.clone(),
                args: args.clone(),
            })
            .collect(),
    }
}

#[derive(Default)]
struct EffectFamilyMap {
    by_path: FxHashMap<Vec<String>, usize>,
    entries: Vec<EffectFamily>,
}

enum EffectFamilyInsert {
    Inserted,
    Duplicate {
        existing_args: Vec<NeuId>,
        duplicate_args: Vec<NeuId>,
    },
}

impl EffectFamilyMap {
    fn insert(&mut self, family: EffectFamily) -> EffectFamilyInsert {
        if let Some(index) = self.by_path.get(&family.path).copied() {
            return EffectFamilyInsert::Duplicate {
                existing_args: self.entries[index].args.clone(),
                duplicate_args: family.args,
            };
        }
        self.insert_new(family);
        EffectFamilyInsert::Inserted
    }

    fn insert_first(&mut self, family: EffectFamily) {
        if !self.by_path.contains_key(&family.path) {
            self.insert_new(family);
        }
    }

    fn insert_new(&mut self, family: EffectFamily) {
        let index = self.entries.len();
        self.by_path.insert(family.path.clone(), index);
        self.entries.push(family);
    }

    fn into_entries(self) -> Vec<EffectFamily> {
        self.entries
    }
}

fn find_record_field<'a, T>(
    fields: &'a [RecordField<T>],
    name: &str,
) -> Option<&'a RecordField<T>> {
    fields.iter().find(|field| field.name == name)
}

fn optionalized_neg_field(field: RecordField<NegId>) -> RecordField<NegId> {
    RecordField {
        name: field.name,
        value: field.value,
        optional: true,
    }
}
