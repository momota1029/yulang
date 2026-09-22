//! Ordered directed-subtyping collection and deterministic reference solving.

use std::{
    collections::{HashMap, HashSet, VecDeque, hash_map::Entry},
    hash::{Hash, Hasher},
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

/// Every fallible F5b growth goes through this small seam.  Besides keeping
/// allocation failure at the existing availability boundary, it makes the
/// otherwise non-deterministic allocator failure path observable by the
/// private lane-by-lane tests.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum F5bCapacityLane {
    LiveComponents,
    ValueBounds,
    EffectBounds,
    ValueLevels,
    EffectLevels,
    ValueMetadata,
    EffectMetadata,
    ExtrusionStack,
    ExtrusionValueMarks,
    ExtrusionEffectMarks,
    TypedPairs,
    TypedWorklist,
    DiagnosticDelta,
    DiagnosticDeltaIndices,
    DiagnosticReverseOffsets,
    DiagnosticReverseEdges,
    DiagnosticReverseCursors,
    DiagnosticDfsStack,
    DiagnosticFinishOrder,
    DiagnosticSccIndices,
    DiagnosticSccNodes,
    DiagnosticSccOffsets,
    DiagnosticSccPendingChildren,
    DiagnosticSccWorklist,
    DiagnosticBucketHeads,
    DiagnosticBucketTails,
    DiagnosticBucketCandidates,
    DiagnosticNodeWitnesses,
    ValueDirectLower,
    ValueDirectUpper,
    ValueExactLower,
    ValueExactUpper,
    EffectDirectLower,
    EffectDirectUpper,
    EffectExactLower,
    EffectExactUpper,
    DiagnosticEdges,
    Errors,
    ReportedErrors,
    CrossKindComponents,
    RoutedUses,
    RoutedUsePositions,
    Schemes,
    Drafts,
    TermPages,
    TermPagePositions,
    TermInterner,
}

pub(crate) trait F5bReservable {
    fn reserve_f5b(&mut self, additional: usize) -> Result<(), ()>;
}
impl<T> F5bReservable for Vec<T> {
    fn reserve_f5b(&mut self, additional: usize) -> Result<(), ()> {
        self.try_reserve(additional).map_err(|_| ())
    }
}
impl<T> F5bReservable for VecDeque<T> {
    fn reserve_f5b(&mut self, additional: usize) -> Result<(), ()> {
        self.try_reserve(additional).map_err(|_| ())
    }
}
impl<K: Eq + Hash, V, S: std::hash::BuildHasher> F5bReservable for HashMap<K, V, S> {
    fn reserve_f5b(&mut self, additional: usize) -> Result<(), ()> {
        self.try_reserve(additional).map_err(|_| ())
    }
}
impl<T: Eq + Hash, S: std::hash::BuildHasher> F5bReservable for HashSet<T, S> {
    fn reserve_f5b(&mut self, additional: usize) -> Result<(), ()> {
        self.try_reserve(additional).map_err(|_| ())
    }
}

#[cfg(test)]
thread_local! {
    static F5B_INJECTED_RESERVE_FAILURE: std::cell::Cell<Option<F5bCapacityLane>> = const { std::cell::Cell::new(None) };
}

pub(crate) fn reserve_f5b<T: F5bReservable>(
    target: &mut T,
    additional: usize,
    lane: F5bCapacityLane,
) -> Result<(), ConstraintError> {
    #[cfg(not(test))]
    let _ = lane;
    #[cfg(test)]
    if F5B_INJECTED_RESERVE_FAILURE.with(|injected| injected.get() == Some(lane)) {
        F5B_INJECTED_RESERVE_FAILURE.with(|injected| injected.set(None));
        return Err(ConstraintError::IdentityExhausted);
    }
    target
        .reserve_f5b(additional)
        .map_err(|_| ConstraintError::IdentityExhausted)
}

#[cfg(test)]
fn inject_next_f5b_reserve_failure(lane: F5bCapacityLane) {
    F5B_INJECTED_RESERVE_FAILURE.with(|injected| injected.set(Some(lane)));
}

use yu_hir::{
    DefId, DefinitionRootId, HirItem, HirModule, HirOccurrenceId, NameResolution, ResolvedExpr,
};
use yu_types::{
    ClosedSchemeFinalization, ClosedTypeArena, ClosedTypeFinalizationSession,
    ClosedTypeFinalizeError, ClosedTypeFinalizer, ClosedValueScheme, ComponentKind,
    DraftNegativeValueId, DraftPositiveValueId, Leaf, NegativeValueView, NeutralValueView,
    PositiveValueView,
};

mod scc;
use scc::{SccComponentId, SccPlan};
mod term;
#[cfg(test)]
use term::TERM_PAGE_SLOTS;
use term::{BranchTermArena, TermBuilder, TermLineage, TermNode, kind_prefix, view_prefix};
pub use term::{LiveVariableView, Polarity, Term, TermLookupError, TermView};

/// Resource counters use the documented logical `capacity * size_of::<slot>()`
/// model.  Overflow is an invariant violation, never a wrapped measurement.
fn checked_capacity_bytes<T>(capacity: usize, label: &'static str) -> usize {
    capacity
        .checked_mul(std::mem::size_of::<T>())
        .unwrap_or_else(|| panic!("{label}: capacity byte accounting fits usize"))
}

fn checked_usize_sum(lanes: impl IntoIterator<Item = usize>, label: &'static str) -> usize {
    lanes
        .into_iter()
        .try_fold(0usize, |total, lane| total.checked_add(lane))
        .unwrap_or_else(|| panic!("{label}: aggregate accounting fits usize"))
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ComponentId {
    Occurrence {
        occurrence: HirOccurrenceId,
        kind: ComponentKind,
    },
    /// Definition roots are value-only: an effect variant cannot be formed.
    DefinitionValue { root: DefinitionRootId },
}
impl ComponentId {
    pub fn occurrence(&self) -> Option<&HirOccurrenceId> {
        match self {
            Self::Occurrence { occurrence, .. } => Some(occurrence),
            Self::DefinitionValue { .. } => None,
        }
    }
    pub fn definition_root(&self) -> Option<&DefinitionRootId> {
        match self {
            Self::Occurrence { .. } => None,
            Self::DefinitionValue { root } => Some(root),
        }
    }
    pub const fn kind(&self) -> ComponentKind {
        match self {
            Self::Occurrence { kind, .. } => *kind,
            Self::DefinitionValue { .. } => ComponentKind::Value,
        }
    }
}

/// Artifact-branded append-only ordered relation identity.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ConstraintOccurrenceId {
    occurrence: HirOccurrenceId,
    local_slot: u8,
}
impl ConstraintOccurrenceId {
    fn new(occurrence: HirOccurrenceId, local_slot: u8) -> Self {
        Self {
            occurrence,
            local_slot,
        }
    }
    pub fn occurrence(&self) -> &HirOccurrenceId {
        &self.occurrence
    }
    pub const fn source_ordinal(&self) -> u32 {
        self.occurrence.ordinal()
    }
    pub const fn local_slot(&self) -> u8 {
        self.local_slot
    }
}

/// Artifact-branded cause identity, deliberately excluded from semantic keys.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CauseId {
    occurrence: ConstraintOccurrenceId,
}
impl CauseId {
    fn for_occurrence(occurrence: ConstraintOccurrenceId) -> Self {
        Self { occurrence }
    }
    pub fn occurrence(&self) -> &ConstraintOccurrenceId {
        &self.occurrence
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConstraintOccurrence {
    id: ConstraintOccurrenceId,
    lower: Term,
    upper: Term,
    cause: CauseId,
}
impl ConstraintOccurrence {
    pub fn id(&self) -> &ConstraintOccurrenceId {
        &self.id
    }
    pub const fn lower(&self) -> Term {
        self.lower
    }
    pub const fn upper(&self) -> Term {
        self.upper
    }
    pub fn cause(&self) -> &CauseId {
        &self.cause
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Components {
    value: ComponentId,
    effect: ComponentId,
}

/// A deterministic definition key, meaningful only within one collected batch.
///
/// Its ordinal is allocated from admitted-binding HIR order.  It deliberately
/// carries no spelling, range, module-path, or hash-iteration information.
#[derive(Clone)]
pub(crate) struct DefinitionOrderId {
    artifact: Arc<CollectionArtifactToken>,
    ordinal: u32,
}
impl DefinitionOrderId {
    fn new(artifact: Arc<CollectionArtifactToken>, ordinal: u32) -> Self {
        Self { artifact, ordinal }
    }
    pub(crate) const fn ordinal(&self) -> u32 {
        self.ordinal
    }
}
impl std::fmt::Debug for DefinitionOrderId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("DefinitionOrderId")
            .field("ordinal", &self.ordinal)
            .finish_non_exhaustive()
    }
}
impl PartialEq for DefinitionOrderId {
    fn eq(&self, other: &Self) -> bool {
        self.ordinal == other.ordinal && Arc::ptr_eq(&self.artifact, &other.artifact)
    }
}
impl Eq for DefinitionOrderId {}
impl Hash for DefinitionOrderId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.artifact).hash(state);
        self.ordinal.hash(state);
    }
}

/// A completed body remains present even when lowering produced an error body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CollectedBodyStatus {
    Complete,
    Error,
}

/// Immutable F0 record for one admitted binding and its pre-existing facts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CollectedDefinition {
    definition: DefinitionOrderId,
    root: DefinitionRootId,
    body_fact_range: std::ops::Range<usize>,
    body_status: CollectedBodyStatus,
}
#[cfg_attr(
    not(test),
    allow(dead_code, reason = "F0 records become the direct F1 SCC-plan input")
)]
impl CollectedDefinition {
    pub(crate) fn definition(&self) -> &DefinitionOrderId {
        &self.definition
    }
    pub(crate) fn body_fact_range(&self) -> &std::ops::Range<usize> {
        &self.body_fact_range
    }
    pub(crate) const fn body_status(&self) -> CollectedBodyStatus {
        self.body_status
    }
}

/// A dependency-use key branded by its immutable collected batch.
#[derive(Clone)]
pub(crate) struct DefinitionUseId {
    artifact: Arc<CollectionArtifactToken>,
    occurrence: HirOccurrenceId,
}
#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "F0 use identities become the direct F1 graph payload"
    )
)]
impl DefinitionUseId {
    fn new(artifact: Arc<CollectionArtifactToken>, occurrence: HirOccurrenceId) -> Self {
        Self {
            artifact,
            occurrence,
        }
    }
    pub(crate) fn occurrence(&self) -> &HirOccurrenceId {
        &self.occurrence
    }
}
impl std::fmt::Debug for DefinitionUseId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("DefinitionUseId")
            .finish_non_exhaustive()
    }
}
impl PartialEq for DefinitionUseId {
    fn eq(&self, other: &Self) -> bool {
        self.occurrence == other.occurrence && Arc::ptr_eq(&self.artifact, &other.artifact)
    }
}
impl Eq for DefinitionUseId {}
impl Hash for DefinitionUseId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.artifact).hash(state);
        self.occurrence.hash(state);
    }
}

/// Provenance for a dependency occurrence. It is not a type fact or component.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct DefinitionUseCause {
    id: DefinitionUseId,
}
#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "F0 provenance becomes the direct F1 graph payload"
    )
)]
impl DefinitionUseCause {
    fn for_use(id: DefinitionUseId) -> Self {
        Self { id }
    }
    pub(crate) fn id(&self) -> &DefinitionUseId {
        &self.id
    }
}

/// One resolved use from an admitted binding body to another definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DefinitionUse {
    id: DefinitionUseId,
    parent: DefinitionOrderId,
    target: DefinitionOrderId,
    occurrence: HirOccurrenceId,
    cause: DefinitionUseCause,
    /// The consuming definition body's level is frozen during collection.
    /// F5c incoming instantiation consumes this recipe without inspecting HIR.
    use_level: u32,
    /// Component-array positions are frozen with the route record.  They are
    /// used only to reconstruct the existing public/store terms; execution
    /// never re-queries source-bearing component maps.
    use_value_component: usize,
    target_root_component: usize,
}
#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "F0 dependency records become the direct F1 SCC-plan input"
    )
)]
impl DefinitionUse {
    pub(crate) fn id(&self) -> &DefinitionUseId {
        &self.id
    }
    pub(crate) fn parent(&self) -> &DefinitionOrderId {
        &self.parent
    }
    pub(crate) fn target(&self) -> &DefinitionOrderId {
        &self.target
    }
    pub(crate) fn occurrence(&self) -> &HirOccurrenceId {
        &self.occurrence
    }
    pub(crate) fn cause(&self) -> &DefinitionUseCause {
        &self.cause
    }
}

#[cfg_attr(
    not(test),
    allow(dead_code, reason = "F0 crate-private queries become F1 plan queries")
)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CollectionLookupError {
    ArtifactMismatch,
    MissingIdentity,
}

#[derive(Debug)]
struct CollectionArtifactToken;

struct PendingDefinitionUse<'hir> {
    parent_ordinal: u32,
    target: &'hir DefId,
    occurrence: HirOccurrenceId,
}

/// Collection failures are structural availability failures, never local type
/// results.  Their variants deliberately carry no source spelling or payload.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CollectionAvailabilityError {
    DefinitionIdentityExhausted,
    DefinitionUseIdentityExhausted,
    DuplicateDefinitionId,
    DuplicateDefinitionOrderId,
    DuplicateDefinitionUseId,
    MissingDefinitionEndpoint,
    NonTotalDefinitionMap,
    NonTotalDefinitionUseMap,
    GraphIdentityExhausted,
    ComponentIdentityExhausted,
    NonTotalSccMembershipMap,
    NonTotalSccComponentMap,
}
impl Components {
    pub fn value(&self) -> &ComponentId {
        &self.value
    }
    pub fn effect(&self) -> &ComponentId {
        &self.effect
    }
}
#[derive(Clone, Copy, Debug)]
struct ComponentPositions {
    value: usize,
    effect: usize,
}

#[derive(Clone, Copy, Debug)]
struct RootComponentPositions {
    component: usize,
}

#[allow(
    dead_code,
    reason = "Bottom/Top are F5b live algebra endpoints; source construction is deferred to F5d"
)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ValueEndpointKey {
    BottomPositive,
    BottomNegative,
    TopNegative,
    IntPositive,
    IntNegative,
    /// This ordinal is allocated by `InferenceSession`, never by collection.
    ValueRow(u32),
    PositiveFunction(Term),
    NegativeFunction(Term),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct CanonicalValuePairKey {
    lower: ValueEndpointKey,
    upper: ValueEndpointKey,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum EffectEndpointKey {
    BottomPositive,
    EmptyNegative,
    /// This ordinal is allocated by `InferenceSession`, never by collection.
    EffectRow(u32),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum TypedPairKey {
    Value(CanonicalValuePairKey),
    Effect {
        lower: EffectEndpointKey,
        upper: EffectEndpointKey,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LiveComponentEndpoint {
    kind: ComponentKind,
    ordinal: u32,
}

/// Session-local eligibility metadata is allocated with every dense live row.
/// Source handles select an initial recipe only; they never become this
/// identity or its origin.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LiveVariableOrigin {
    Collected,
    Fresh,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LiveVariableMetadata {
    origin: LiveVariableOrigin,
    non_generic: bool,
}

/// Ordered source occurrences and compact component indexes, never semantic facts.
#[derive(Clone, Debug)]
pub struct ConstraintBatch {
    hir: Arc<HirModule>,
    collection_artifact: Arc<CollectionArtifactToken>,
    projection_order: Vec<HirOccurrenceId>,
    root_order: Vec<DefinitionRootId>,
    definitions: Vec<CollectedDefinition>,
    definition_positions: HashMap<DefinitionOrderId, usize>,
    definition_uses: Vec<DefinitionUse>,
    definition_use_positions: HashMap<DefinitionUseId, usize>,
    /// Frozen once, after F0 endpoint resolution and both total-map checks.
    scc_plan: Option<SccPlan>,
    components: Vec<ComponentId>,
    /// Exact collected handles parallel to `components`; route recipes retain
    /// these identities instead of reconstructing endpoint terms at solve.
    component_terms: Vec<Term>,
    /// Frozen recipe lookup only: collected terms select their session-local
    /// live endpoint during one startup translation.  It is never a live
    /// variable identity or a solve-time bound table.
    component_term_positions: HashMap<Term, usize>,
    leaf_terms: HashMap<Leaf, Term>,
    term_builder: Option<TermBuilder>,
    term_arena: Option<Arc<TermLineage>>,
    #[cfg(test)]
    /// Synthetic F4 scale witnesses extend their own unobservable batch after
    /// collection. Production drops the builder at seal.
    test_term_builder: Option<TermBuilder>,
    #[cfg(test)]
    test_term_arena_dirty: bool,
    occurrence_component_positions: HashMap<HirOccurrenceId, ComponentPositions>,
    root_component_positions: HashMap<DefinitionRootId, RootComponentPositions>,
    /// The F4 scheme slot key.  The ordinal is scheduling storage only; the
    /// semantic key remains the artifact-branded definition root.
    root_definition_positions: HashMap<DefinitionRootId, usize>,
    /// Dynamic identity bytes retained beside the dense scheme position.  A
    /// successful public root query charges this exact key payload, while
    /// execution itself never hashes source-bearing roots.
    root_scheme_identity_payload_bytes: Vec<usize>,
    occurrences: Vec<ConstraintOccurrence>,
    #[cfg(test)]
    synthetic_seed_value_pair_probes: usize,
    counters: ProductionCounters,
    definition_query_probes: Arc<AtomicUsize>,
    definition_use_query_probes: Arc<AtomicUsize>,
    scc_component_for_definition_query_probes: Arc<AtomicUsize>,
    scc_component_members_query_probes: Arc<AtomicUsize>,
    scc_component_internal_uses_query_probes: Arc<AtomicUsize>,
    scc_component_incoming_uses_query_probes: Arc<AtomicUsize>,
    occurrence_component_query_probes: Arc<AtomicUsize>,
    root_component_query_probes: Arc<AtomicUsize>,
}
impl ConstraintBatch {
    pub fn collect(hir: Arc<HirModule>) -> Result<Self, CollectionAvailabilityError> {
        let hir_definition_root_allocation_bytes = hir.definition_root_allocation_bytes();
        let definition_root_def_id_clone_bytes = hir.definition_root_def_id_clone_bytes();
        let mut batch = Self {
            hir,
            collection_artifact: Arc::new(CollectionArtifactToken),
            projection_order: Vec::new(),
            root_order: Vec::new(),
            definitions: Vec::new(),
            definition_positions: HashMap::new(),
            definition_uses: Vec::new(),
            definition_use_positions: HashMap::new(),
            scc_plan: None,
            components: Vec::new(),
            component_terms: Vec::new(),
            component_term_positions: HashMap::new(),
            leaf_terms: HashMap::new(),
            term_builder: Some(TermBuilder::new()?),
            term_arena: None,
            #[cfg(test)]
            test_term_builder: None,
            #[cfg(test)]
            test_term_arena_dirty: false,
            occurrence_component_positions: HashMap::new(),
            root_component_positions: HashMap::new(),
            root_definition_positions: HashMap::new(),
            root_scheme_identity_payload_bytes: Vec::new(),
            occurrences: Vec::new(),
            #[cfg(test)]
            synthetic_seed_value_pair_probes: 0,
            definition_query_probes: Arc::new(AtomicUsize::new(0)),
            definition_use_query_probes: Arc::new(AtomicUsize::new(0)),
            scc_component_for_definition_query_probes: Arc::new(AtomicUsize::new(0)),
            scc_component_members_query_probes: Arc::new(AtomicUsize::new(0)),
            scc_component_internal_uses_query_probes: Arc::new(AtomicUsize::new(0)),
            scc_component_incoming_uses_query_probes: Arc::new(AtomicUsize::new(0)),
            occurrence_component_query_probes: Arc::new(AtomicUsize::new(0)),
            root_component_query_probes: Arc::new(AtomicUsize::new(0)),
            counters: ProductionCounters {
                hir_traversals: 1,
                hir_definition_root_allocation_bytes,
                definition_root_def_id_clone_bytes,
                ..ProductionCounters::default()
            },
        };
        let hir = batch.hir.clone();
        #[cfg(test)]
        for leaf in [
            Leaf::IntPositive,
            Leaf::IntNegative,
            Leaf::EffectBottomPositive,
            Leaf::EmptyEffectNegative,
        ] {
            batch.term_for_leaf(leaf)?;
        }
        // This spelling-bearing index borrows HIR and is discarded after the
        // endpoint pass; the immutable batch retains only order identities.
        let mut definition_by_hir_id = HashMap::<&DefId, DefinitionOrderId>::new();
        let mut pending_uses = Vec::new();
        for item in hir.items() {
            batch.counters.body_pass_visits += 1;
            let (expression, definition_root, definition) = match item {
                HirItem::Expression(expression) => (expression, None, None),
                HirItem::Binding(binding) => {
                    let ordinal = u32::try_from(batch.definitions.len())
                        .map_err(|_| CollectionAvailabilityError::DefinitionIdentityExhausted)?;
                    let definition =
                        DefinitionOrderId::new(batch.collection_artifact.clone(), ordinal);
                    let fact_start = batch.occurrences.len();
                    batch.add_definition_root(binding.definition_root().clone())?;
                    let endpoint_identity_payload_bytes = binding.id().hash_eq_payload_bytes();
                    let old_capacity = definition_by_hir_id.capacity();
                    let Entry::Vacant(entry) = definition_by_hir_id.entry(binding.id()) else {
                        return Err(CollectionAvailabilityError::DuplicateDefinitionId);
                    };
                    entry.insert(definition.clone());
                    batch.counters.definition_endpoint_index_inserts += 1;
                    batch
                        .counters
                        .definition_endpoint_identity_hash_byte_incidences +=
                        endpoint_identity_payload_bytes;
                    if definition_by_hir_id.capacity() != old_capacity {
                        batch.counters.definition_endpoint_index_capacity_growths += 1;
                        batch.counters.index_rebuilds += 1;
                    }
                    let definition_position = batch.definitions.len();
                    let old_capacity = batch.definition_positions.capacity();
                    let Entry::Vacant(entry) = batch.definition_positions.entry(definition.clone())
                    else {
                        return Err(CollectionAvailabilityError::DuplicateDefinitionOrderId);
                    };
                    entry.insert(definition_position);
                    batch.counters.definition_record_index_inserts += 1;
                    if batch.definition_positions.capacity() != old_capacity {
                        batch.counters.index_rebuilds += 1;
                    }
                    let body_status = match binding.value() {
                        ResolvedExpr::Integer { .. }
                        | ResolvedExpr::Name {
                            resolution: NameResolution::Resolved(_),
                            ..
                        } => CollectedBodyStatus::Complete,
                        ResolvedExpr::Name {
                            resolution: NameResolution::Ambiguous,
                            ..
                        } => {
                            batch.counters.collected_ambiguous_name_bodies += 1;
                            CollectedBodyStatus::Error
                        }
                        ResolvedExpr::Name {
                            resolution: NameResolution::Unresolved,
                            ..
                        } => {
                            batch.counters.collected_unresolved_name_bodies += 1;
                            CollectedBodyStatus::Error
                        }
                        ResolvedExpr::Name {
                            resolution: NameResolution::Parameter(_),
                            ..
                        } => CollectedBodyStatus::Error,
                        // F5a retains the source Lambda in HIR, but Function
                        // facts remain deliberately deferred to F5d. Its
                        // owned body still determines the existing complete
                        // versus error collection disposition.
                        ResolvedExpr::Lambda { body, .. } => match body.as_ref() {
                            ResolvedExpr::Integer { .. }
                            | ResolvedExpr::Name {
                                resolution:
                                    NameResolution::Resolved(_) | NameResolution::Parameter(_),
                                ..
                            } => CollectedBodyStatus::Complete,
                            ResolvedExpr::Name {
                                resolution: NameResolution::Ambiguous,
                                ..
                            } => {
                                batch.counters.collected_ambiguous_name_bodies += 1;
                                CollectedBodyStatus::Error
                            }
                            ResolvedExpr::Name {
                                resolution: NameResolution::Unresolved,
                                ..
                            } => {
                                batch.counters.collected_unresolved_name_bodies += 1;
                                CollectedBodyStatus::Error
                            }
                            ResolvedExpr::Lambda { .. } | ResolvedExpr::Error { .. } => {
                                CollectedBodyStatus::Error
                            }
                        },
                        ResolvedExpr::Error { .. } => CollectedBodyStatus::Error,
                    };
                    match body_status {
                        CollectedBodyStatus::Complete => {
                            batch.counters.collected_complete_bodies += 1
                        }
                        CollectedBodyStatus::Error => batch.counters.collected_error_bodies += 1,
                    }
                    batch.definitions.push(CollectedDefinition {
                        definition: definition.clone(),
                        root: binding.definition_root().clone(),
                        body_fact_range: fact_start..fact_start,
                        body_status,
                    });
                    let old_capacity = batch.root_definition_positions.capacity();
                    if batch
                        .root_definition_positions
                        .insert(binding.definition_root().clone(), definition_position)
                        .is_some()
                    {
                        return Err(CollectionAvailabilityError::DuplicateDefinitionId);
                    }
                    if batch.root_definition_positions.capacity() != old_capacity {
                        batch.counters.scheme_root_index_growths += 1;
                        batch.counters.scheme_root_index_rebuilds += 1;
                    }
                    batch
                        .root_scheme_identity_payload_bytes
                        .push(binding.id().hash_eq_payload_bytes());
                    batch.counters.definition_registration_visits += 1;
                    batch.counters.collected_definitions += 1;
                    (
                        binding.value(),
                        Some(binding.definition_root()),
                        Some(definition),
                    )
                }
                HirItem::Error { .. } => continue,
            };
            batch.projection_order.push(expression.occurrence().clone());
            batch.counters.occurrence_allocations += 1;
            if matches!(expression, ResolvedExpr::Integer { .. }) {
                batch.emit_integer(expression.occurrence().clone(), definition_root.cloned())?;
            }
            if let (
                Some(parent),
                Some(root),
                ResolvedExpr::Name {
                    occurrence,
                    resolution: NameResolution::Resolved(target),
                    ..
                },
            ) = (definition.as_ref(), definition_root.as_ref(), expression)
            {
                batch.emit_resolved_binding_name(occurrence.clone(), (*root).clone())?;
                let old_capacity = pending_uses.capacity();
                pending_uses.push(PendingDefinitionUse {
                    parent_ordinal: parent.ordinal(),
                    target,
                    occurrence: occurrence.clone(),
                });
                let capacity = pending_uses.capacity();
                batch
                    .counters
                    .definition_use_endpoint_workspace_peak_capacity = batch
                    .counters
                    .definition_use_endpoint_workspace_peak_capacity
                    .max(capacity);
                if capacity != old_capacity {
                    batch
                        .counters
                        .definition_use_endpoint_workspace_capacity_growths += 1;
                }
            }
            if let Some(definition) = definition {
                let record = batch
                    .definitions
                    .get_mut(definition.ordinal() as usize)
                    .ok_or(CollectionAvailabilityError::NonTotalDefinitionMap)?;
                debug_assert_eq!(record.definition, definition);
                record.body_fact_range.end = batch.occurrences.len();
            }
        }
        batch.ensure_total_definition_maps(&definition_by_hir_id)?;
        batch.counters.definition_endpoint_index_peak_capacity = definition_by_hir_id.capacity();
        for pending in &pending_uses {
            batch.counters.definition_use_endpoint_pass_visits += 1;
            batch.counters.definition_endpoint_index_probes += 1;
            batch
                .counters
                .definition_endpoint_identity_hash_byte_incidences +=
                pending.target.hash_eq_payload_bytes();
            let target = definition_by_hir_id
                .get(&pending.target)
                .ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?
                .clone();
            batch
                .counters
                .definition_endpoint_logical_successful_equality_byte_incidences +=
                pending.target.hash_eq_payload_bytes();
            let parent = batch
                .definitions
                .get(pending.parent_ordinal as usize)
                .ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?
                .definition
                .clone();
            u32::try_from(batch.definition_uses.len())
                .map_err(|_| CollectionAvailabilityError::DefinitionUseIdentityExhausted)?;
            let id = DefinitionUseId::new(
                batch.collection_artifact.clone(),
                pending.occurrence.clone(),
            );
            let target_root_component = batch
                .root_component_positions
                .get(&batch.definitions[target.ordinal() as usize].root)
                .expect("target root has frozen component position")
                .component;
            let use_value_component = batch
                .occurrence_component_positions
                .get(&pending.occurrence)
                .expect("resolved use has frozen component positions")
                .value;
            let position = batch.definition_uses.len();
            batch.definition_uses.push(DefinitionUse {
                cause: DefinitionUseCause::for_use(id.clone()),
                id: id.clone(),
                parent,
                target,
                occurrence: pending.occurrence.clone(),
                use_level: 1,
                use_value_component,
                target_root_component,
            });
            let old_capacity = batch.definition_use_positions.capacity();
            let Entry::Vacant(entry) = batch.definition_use_positions.entry(id) else {
                return Err(CollectionAvailabilityError::DuplicateDefinitionUseId);
            };
            entry.insert(position);
            batch.counters.definition_use_index_inserts += 1;
            if batch.definition_use_positions.capacity() != old_capacity {
                batch.counters.index_rebuilds += 1;
            }
            batch.counters.retained_definition_uses += 1;
        }
        batch.ensure_total_definition_use_map()?;
        // Alignment belongs to collection: a failed seal returns no partially
        // observable batch and maps through the established component category.
        let builder = batch
            .term_builder
            .take()
            .expect("term collection builder remains live until seal");
        #[cfg(test)]
        let test_term_builder = builder.clone();
        batch.term_arena = Some(builder.seal()?);
        #[cfg(test)]
        {
            batch.test_term_builder = Some(test_term_builder);
        }
        batch.counters.occurrence_retained_bytes = checked_capacity_bytes::<HirOccurrenceId>(
            batch.projection_order.capacity(),
            "F0 projection order",
        );
        batch.counters.component_retained_bytes =
            checked_capacity_bytes::<ComponentId>(batch.components.capacity(), "F0 components");
        batch.counters.occurrence_record_retained_bytes =
            checked_capacity_bytes::<ConstraintOccurrence>(
                batch.occurrences.capacity(),
                "F0 occurrence records",
            );
        batch.counters.root_retained_bytes = checked_capacity_bytes::<DefinitionRootId>(
            batch.root_order.capacity(),
            "F0 root order",
        );
        batch.counters.occurrence_component_index_capacity =
            batch.occurrence_component_positions.capacity();
        batch.counters.occurrence_component_index_retained_bytes =
            checked_capacity_bytes::<(HirOccurrenceId, ComponentPositions)>(
                batch.occurrence_component_positions.capacity(),
                "F0 occurrence component index",
            );
        batch.counters.root_component_index_capacity = batch.root_component_positions.capacity();
        batch.counters.root_component_index_retained_bytes =
            checked_capacity_bytes::<(DefinitionRootId, RootComponentPositions)>(
                batch.root_component_positions.capacity(),
                "F0 root component index",
            );
        batch.counters.index_capacity = batch.occurrence_component_positions.capacity()
            + batch.root_component_positions.capacity();
        batch.counters.definition_record_index_capacity = batch.definition_positions.capacity();
        batch.counters.definition_record_index_retained_bytes =
            checked_capacity_bytes::<(DefinitionOrderId, usize)>(
                batch.definition_positions.capacity(),
                "F0 definition record index",
            );
        batch.counters.definition_record_retained_bytes =
            checked_capacity_bytes::<CollectedDefinition>(
                batch.definitions.capacity(),
                "F0 definition records",
            );
        batch.counters.definition_use_retained_bytes = checked_capacity_bytes::<DefinitionUse>(
            batch.definition_uses.capacity(),
            "F0 definition uses",
        );
        batch.counters.definition_use_index_capacity = batch.definition_use_positions.capacity();
        batch.counters.definition_use_index_retained_bytes =
            checked_capacity_bytes::<(DefinitionUseId, usize)>(
                batch.definition_use_positions.capacity(),
                "F0 definition-use index",
            );
        let definition_endpoint_index_capacity = definition_by_hir_id.capacity();
        let pending_endpoint_capacity = pending_uses.capacity();
        batch.finish_collection_accounting(
            definition_endpoint_index_capacity,
            pending_endpoint_capacity,
        );
        // Endpoint resolution has completed. These F0-only borrowed/index
        // workspaces cannot co-reside with F2 graph construction.
        drop(pending_uses);
        drop(definition_by_hir_id);
        // F2 freezes exactly one plan from the sealed F0 records.  The plan
        // borrows their identities during construction; it never needs a
        // second definition-ID vector or another HIR traversal.
        batch.scc_plan = Some(SccPlan::build(
            &batch.collection_artifact,
            &batch.definitions,
            &batch.definition_uses,
            &mut batch.counters,
        )?);
        batch.finish_scc_plan_accounting();
        Ok(batch)
    }
    pub fn hir(&self) -> &Arc<HirModule> {
        &self.hir
    }
    pub fn occurrences(&self) -> &[ConstraintOccurrence] {
        &self.occurrences
    }
    pub fn term_view(&self, term: Term) -> Result<TermView<'_>, TermLookupError> {
        view_prefix(
            self.term_arena
                .as_deref()
                .expect("observable batch has a sealed term arena"),
            term,
        )
    }
    pub fn term_kind(&self, term: Term) -> Result<ComponentKind, TermLookupError> {
        kind_prefix(
            self.term_arena
                .as_deref()
                .expect("observable batch has a sealed term arena"),
            term,
        )
    }
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "F0 records become the direct F1 SCC-plan input")
    )]
    pub(crate) fn definitions(&self) -> &[CollectedDefinition] {
        &self.definitions
    }
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "F0 uses become the direct F1 graph input")
    )]
    pub(crate) fn definition_uses(&self) -> &[DefinitionUse] {
        &self.definition_uses
    }
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "F0 identity query becomes an F1 plan query")
    )]
    pub(crate) fn definition(
        &self,
        definition: &DefinitionOrderId,
    ) -> Result<&CollectedDefinition, CollectionLookupError> {
        self.require_owned_definition(definition)?;
        self.definition_query_probes.fetch_add(1, Ordering::Relaxed);
        self.definition_positions
            .get(definition)
            .and_then(|&position| self.definitions.get(position))
            .ok_or(CollectionLookupError::MissingIdentity)
    }
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "F0 use query becomes an F1 plan query")
    )]
    pub(crate) fn definition_use(
        &self,
        id: &DefinitionUseId,
    ) -> Result<&DefinitionUse, CollectionLookupError> {
        self.require_owned_definition_use(id)?;
        self.definition_use_query_probes
            .fetch_add(1, Ordering::Relaxed);
        self.definition_use_positions
            .get(id)
            .and_then(|&position| self.definition_uses.get(position))
            .ok_or(CollectionLookupError::MissingIdentity)
    }
    /// Canonical component identities in dependency-sink-first order.
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    pub(crate) fn scc_components_in_dependency_first_order(
        &self,
    ) -> impl Iterator<Item = &SccComponentId> {
        self.scc_plan().components_in_dependency_first_order()
    }
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    pub(crate) fn scc_component_for_definition(
        &self,
        definition: &DefinitionOrderId,
    ) -> Result<&SccComponentId, CollectionLookupError> {
        self.require_owned_definition(definition)?;
        self.scc_component_for_definition_query_probes
            .fetch_add(1, Ordering::Relaxed);
        self.scc_plan().component_for_definition(definition)
    }
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    pub(crate) fn scc_component_members(
        &self,
        component: &SccComponentId,
    ) -> Result<&[DefinitionOrderId], CollectionLookupError> {
        self.require_owned_scc_component(component)?;
        self.scc_component_members_query_probes
            .fetch_add(1, Ordering::Relaxed);
        self.scc_plan().members(component)
    }
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    pub(crate) fn scc_component_internal_uses(
        &self,
        component: &SccComponentId,
    ) -> Result<&[DefinitionUseId], CollectionLookupError> {
        self.require_owned_scc_component(component)?;
        self.scc_component_internal_uses_query_probes
            .fetch_add(1, Ordering::Relaxed);
        self.scc_plan().internal_uses(component)
    }
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    pub(crate) fn scc_component_incoming_uses(
        &self,
        component: &SccComponentId,
    ) -> Result<&[DefinitionUseId], CollectionLookupError> {
        self.require_owned_scc_component(component)?;
        self.scc_component_incoming_uses_query_probes
            .fetch_add(1, Ordering::Relaxed);
        self.scc_plan().incoming_uses(component)
    }
    pub fn counters(&self) -> ProductionCounters {
        let mut counters = self.counters.clone();
        counters.definition_query_probes = self.definition_query_probes.load(Ordering::Relaxed);
        counters.definition_use_query_probes =
            self.definition_use_query_probes.load(Ordering::Relaxed);
        counters.scc_component_for_definition_query_probes = self
            .scc_component_for_definition_query_probes
            .load(Ordering::Relaxed);
        counters.scc_component_members_query_probes = self
            .scc_component_members_query_probes
            .load(Ordering::Relaxed);
        counters.scc_component_internal_uses_query_probes = self
            .scc_component_internal_uses_query_probes
            .load(Ordering::Relaxed);
        counters.scc_component_incoming_uses_query_probes = self
            .scc_component_incoming_uses_query_probes
            .load(Ordering::Relaxed);
        counters.occurrence_component_query_probes = self
            .occurrence_component_query_probes
            .load(Ordering::Relaxed);
        counters.root_component_query_probes =
            self.root_component_query_probes.load(Ordering::Relaxed);
        counters
    }
    pub fn components_for(
        &self,
        occurrence: &HirOccurrenceId,
    ) -> Result<Option<Components>, ArtifactMismatch> {
        self.require_owned(occurrence)?;
        self.occurrence_component_query_probes
            .fetch_add(1, Ordering::Relaxed);
        Ok(self
            .occurrence_component_positions
            .get(occurrence)
            .map(|positions| Components {
                value: self.components[positions.value].clone(),
                effect: self.components[positions.effect].clone(),
            }))
    }
    pub fn root_value_component(
        &self,
        root: &DefinitionRootId,
    ) -> Result<ComponentId, ArtifactMismatch> {
        self.require_owned_root(root)?;
        self.root_component_query_probes
            .fetch_add(1, Ordering::Relaxed);
        let position = self
            .root_component_positions
            .get(root)
            .copied()
            .ok_or(ArtifactMismatch)?;
        Ok(self.components[position.component].clone())
    }
    fn add_definition_root(
        &mut self,
        root: DefinitionRootId,
    ) -> Result<(), CollectionAvailabilityError> {
        if self.root_component_positions.contains_key(&root) {
            return Err(CollectionAvailabilityError::DuplicateDefinitionId);
        }
        self.root_order.push(root.clone());
        self.counters.root_allocations += 1;
        let value = self.definition_value_component(root.clone())?;
        let old_capacity = self.root_component_positions.capacity();
        self.root_component_positions.insert(
            root,
            RootComponentPositions {
                component: self.components.len() - 1,
            },
        );
        if self.root_component_positions.capacity() != old_capacity {
            self.counters.index_rebuilds += 1;
        }
        debug_assert!(matches!(value, ComponentId::DefinitionValue { .. }));
        Ok(())
    }
    fn emit_integer(
        &mut self,
        occurrence: HirOccurrenceId,
        definition_root: Option<DefinitionRootId>,
    ) -> Result<(), CollectionAvailabilityError> {
        let value = self.occurrence_component(occurrence.clone(), ComponentKind::Value)?;
        let effect = self.occurrence_component(occurrence.clone(), ComponentKind::Effect)?;
        let positions = ComponentPositions {
            value: self.components.len() - 2,
            effect: self.components.len() - 1,
        };
        let old_capacity = self.occurrence_component_positions.capacity();
        self.occurrence_component_positions
            .insert(occurrence.clone(), positions);
        if self.occurrence_component_positions.capacity() != old_capacity {
            self.counters.index_rebuilds += 1;
        }
        let int_positive = self.term_for_leaf(Leaf::IntPositive)?;
        let int_negative = self.term_for_leaf(Leaf::IntNegative)?;
        let effect_bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
        let effect_empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
        self.emit(
            occurrence.clone(),
            0,
            int_positive,
            self.term_for_component(&value),
        )?;
        self.emit(
            occurrence.clone(),
            1,
            self.term_for_component(&value),
            int_negative,
        )?;
        self.emit(
            occurrence.clone(),
            2,
            effect_bottom,
            self.term_for_component(&effect),
        )?;
        self.emit(
            occurrence.clone(),
            3,
            self.term_for_component(&effect),
            effect_empty,
        )?;
        if let Some(root) = definition_root {
            let definition_value = self.root_value_component_for_collect(&root)?;
            self.emit(
                occurrence,
                4,
                self.term_for_component(&value),
                self.term_for_component(&definition_value),
            )?;
        }
        Ok(())
    }
    /// F4's resolved binding-body name surface has the occurrence itself as
    /// the whole body result.  The dependency relation (slot 0) is admitted
    /// only by SCC execution, because its endpoint is open or closed then.
    fn emit_resolved_binding_name(
        &mut self,
        occurrence: HirOccurrenceId,
        definition_root: DefinitionRootId,
    ) -> Result<(), CollectionAvailabilityError> {
        let value = self.occurrence_component(occurrence.clone(), ComponentKind::Value)?;
        let effect = self.occurrence_component(occurrence.clone(), ComponentKind::Effect)?;
        let positions = ComponentPositions {
            value: self.components.len() - 2,
            effect: self.components.len() - 1,
        };
        if self
            .occurrence_component_positions
            .insert(occurrence.clone(), positions)
            .is_some()
        {
            return Err(CollectionAvailabilityError::DuplicateDefinitionUseId);
        }
        let root = self.root_value_component_for_collect(&definition_root)?;
        let effect_bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
        let effect_empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
        self.emit(
            occurrence.clone(),
            1,
            effect_bottom,
            self.term_for_component(&effect),
        )?;
        self.emit(
            occurrence.clone(),
            2,
            self.term_for_component(&effect),
            effect_empty,
        )?;
        self.emit(
            occurrence,
            3,
            self.term_for_component(&value),
            self.term_for_component(&root),
        )?;
        Ok(())
    }
    fn occurrence_component(
        &mut self,
        occurrence: HirOccurrenceId,
        kind: ComponentKind,
    ) -> Result<ComponentId, CollectionAvailabilityError> {
        let component = ComponentId::Occurrence { occurrence, kind };
        self.components.push(component.clone());
        #[cfg(test)]
        if self.term_builder.is_none() {
            self.test_term_arena_dirty = true;
        }
        let term = self
            .active_term_builder()
            .intern(TermNode::Component(component.clone()))?;
        let position = self.component_terms.len();
        self.component_terms.push(term);
        debug_assert!(
            self.component_term_positions
                .insert(term, position)
                .is_none()
        );
        self.counters.component_allocations += 1;
        Ok(component)
    }
    fn definition_value_component(
        &mut self,
        root: DefinitionRootId,
    ) -> Result<ComponentId, CollectionAvailabilityError> {
        let component = ComponentId::DefinitionValue { root };
        self.components.push(component.clone());
        #[cfg(test)]
        if self.term_builder.is_none() {
            self.test_term_arena_dirty = true;
        }
        let term = self
            .active_term_builder()
            .intern(TermNode::Component(component.clone()))?;
        let position = self.component_terms.len();
        self.component_terms.push(term);
        debug_assert!(
            self.component_term_positions
                .insert(term, position)
                .is_none()
        );
        self.counters.component_allocations += 1;
        Ok(component)
    }
    fn term_for_component(&self, component: &ComponentId) -> Term {
        let position = match component {
            ComponentId::Occurrence { occurrence, kind } => {
                let positions = self
                    .occurrence_component_positions
                    .get(occurrence)
                    .expect("every collected occurrence component has frozen positions");
                match kind {
                    ComponentKind::Value => positions.value,
                    ComponentKind::Effect => positions.effect,
                }
            }
            ComponentId::DefinitionValue { root } => {
                self.root_component_positions
                    .get(root)
                    .expect("every collected definition component has a frozen position")
                    .component
            }
        };
        self.component_term_at(position)
    }
    fn component_term_at(&self, position: usize) -> Term {
        self.component_terms[position]
    }
    fn collected_leaf_term(&self, leaf: Leaf) -> Term {
        *self
            .leaf_terms
            .get(&leaf)
            .expect("every F4 route leaf was interned during collection")
    }
    fn term_lineage(&self) -> Arc<TermLineage> {
        #[cfg(test)]
        if self.test_term_arena_dirty {
            let builder = self
                .test_term_builder
                .as_ref()
                .expect("only synthetic test batches extend a sealed prefix");
            return builder
                .clone()
                .seal()
                .expect("synthetic test collection term identities remain representable");
        }
        self.term_arena
            .as_ref()
            .expect("observable batch has a sealed term arena")
            .clone()
    }
    fn term_for_leaf(&mut self, leaf: Leaf) -> Result<Term, CollectionAvailabilityError> {
        if let Some(term) = self.leaf_terms.get(&leaf).copied() {
            return Ok(term);
        }
        #[cfg(test)]
        if self.term_builder.is_none() {
            self.test_term_arena_dirty = true;
        }
        let term = self.active_term_builder().intern(TermNode::Leaf(leaf))?;
        self.leaf_terms.insert(leaf, term);
        Ok(term)
    }
    fn active_term_builder(&mut self) -> &mut TermBuilder {
        if let Some(builder) = &mut self.term_builder {
            return builder;
        }
        #[cfg(test)]
        if let Some(builder) = &mut self.test_term_builder {
            return builder;
        }
        panic!("production collection builder is sealed before batch observation")
    }
    fn emit(
        &mut self,
        occurrence: HirOccurrenceId,
        local_slot: u8,
        lower: Term,
        upper: Term,
    ) -> Result<(), CollectionAvailabilityError> {
        let id = ConstraintOccurrenceId::new(occurrence, local_slot);
        self.occurrences.push(ConstraintOccurrence {
            cause: CauseId::for_occurrence(id.clone()),
            id,
            lower,
            upper,
        });
        self.counters.emitted_facts += 1;
        self.counters.generated_work_items += 1;
        Ok(())
    }
    fn require_owned(&self, occurrence: &HirOccurrenceId) -> Result<(), ArtifactMismatch> {
        self.hir
            .owns_occurrence(occurrence)
            .then_some(())
            .ok_or(ArtifactMismatch)
    }
    fn require_owned_root(&self, root: &DefinitionRootId) -> Result<(), ArtifactMismatch> {
        self.hir
            .owns_definition_root(root)
            .then_some(())
            .ok_or(ArtifactMismatch)
    }
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "F0 identity query becomes an F1 plan query")
    )]
    fn require_owned_definition(
        &self,
        definition: &DefinitionOrderId,
    ) -> Result<(), CollectionLookupError> {
        Arc::ptr_eq(&self.collection_artifact, &definition.artifact)
            .then_some(())
            .ok_or(CollectionLookupError::ArtifactMismatch)
    }
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "F0 use query becomes an F1 plan query")
    )]
    fn require_owned_definition_use(
        &self,
        id: &DefinitionUseId,
    ) -> Result<(), CollectionLookupError> {
        Arc::ptr_eq(&self.collection_artifact, &id.artifact)
            .then_some(())
            .ok_or(CollectionLookupError::ArtifactMismatch)
    }
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    fn require_owned_scc_component(
        &self,
        component: &SccComponentId,
    ) -> Result<(), CollectionLookupError> {
        self.require_owned_definition(component.canonical_definition())
    }
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "F2 read-only plan query surface awaits the later execution gate"
        )
    )]
    fn scc_plan(&self) -> &SccPlan {
        self.scc_plan
            .as_ref()
            .expect("complete F0 collection always freezes one SCC plan")
    }
    fn root_value_component_for_collect(
        &mut self,
        root: &DefinitionRootId,
    ) -> Result<ComponentId, CollectionAvailabilityError> {
        self.counters.root_component_index_probes += 1;
        let position = self
            .root_component_positions
            .get(root)
            .ok_or(CollectionAvailabilityError::NonTotalDefinitionMap)?
            .component;
        self.components
            .get(position)
            .cloned()
            .ok_or(CollectionAvailabilityError::NonTotalDefinitionMap)
    }
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "test-only scale builder reconstructs a real source term"
        )
    )]
    fn root_value_component_for_session(&self, root: &DefinitionRootId) -> ComponentId {
        let position = self
            .root_component_positions
            .get(root)
            .expect("total definition root component map")
            .component;
        self.components
            .get(position)
            .cloned()
            .expect("root component position")
    }
    fn ensure_total_definition_maps(
        &self,
        definition_by_hir_id: &HashMap<&DefId, DefinitionOrderId>,
    ) -> Result<(), CollectionAvailabilityError> {
        ((self.definitions.len() == self.definition_positions.len()
            && self.definitions.len() == definition_by_hir_id.len())
            && self.definitions.len() == self.root_definition_positions.len()
            && self.definitions.len() == self.root_scheme_identity_payload_bytes.len()
            && self
                .definitions
                .iter()
                .enumerate()
                .all(|(position, definition)| {
                    self.root_definition_positions.get(&definition.root) == Some(&position)
                }))
        .then_some(())
        .ok_or(CollectionAvailabilityError::NonTotalDefinitionMap)
    }
    fn ensure_total_definition_use_map(&self) -> Result<(), CollectionAvailabilityError> {
        (self.definition_uses.len() == self.definition_use_positions.len())
            .then_some(())
            .ok_or(CollectionAvailabilityError::NonTotalDefinitionUseMap)
    }
    fn finish_collection_accounting(
        &mut self,
        definition_endpoint_index_capacity: usize,
        pending_endpoint_capacity: usize,
    ) {
        self.counters.definition_endpoint_index_peak_bytes =
            checked_capacity_bytes::<(&DefId, DefinitionOrderId)>(
                definition_endpoint_index_capacity,
                "F0 definition endpoint index",
            );
        self.counters.definition_use_endpoint_workspace_peak_bytes =
            checked_capacity_bytes::<PendingDefinitionUse<'_>>(
                pending_endpoint_capacity,
                "F0 pending definition uses",
            );
        self.counters.f0_collection_retained_bytes = checked_usize_sum(
            [
                self.counters.occurrence_retained_bytes,
                self.counters.root_retained_bytes,
                self.counters.definition_record_retained_bytes,
                self.counters.definition_record_index_retained_bytes,
                self.counters.definition_use_retained_bytes,
                self.counters.definition_use_index_retained_bytes,
                self.counters.component_retained_bytes,
                checked_capacity_bytes::<(Term, usize)>(
                    self.component_term_positions.capacity(),
                    "F5b collected component-term recipe index",
                ),
                self.counters.occurrence_component_index_retained_bytes,
                self.counters.root_component_index_retained_bytes,
                checked_capacity_bytes::<(DefinitionRootId, usize)>(
                    self.root_definition_positions.capacity(),
                    "F0 scheme-root positions",
                ),
                checked_capacity_bytes::<usize>(
                    self.root_scheme_identity_payload_bytes.capacity(),
                    "F0 scheme-root identity payload",
                ),
                self.counters.occurrence_record_retained_bytes,
            ],
            "F0 collection retained bytes",
        );
        self.counters.f0_collection_peak_bytes = checked_usize_sum(
            [
                self.counters.f0_collection_retained_bytes,
                self.counters.definition_endpoint_index_peak_bytes,
                self.counters.definition_use_endpoint_workspace_peak_bytes,
            ],
            "F0 collection peak bytes",
        );
    }
    fn finish_scc_plan_accounting(&mut self) {
        let f1_input_bytes = scc::f1_input_retained_bytes(&self.definitions, &self.definition_uses);
        let scc_temporary_or_plan_bytes = self
            .counters
            .scc_f1_graph_input_plan_peak_known_bytes
            .saturating_sub(f1_input_bytes);
        self.counters.f2_batch_retained_bytes = checked_usize_sum(
            [
                self.counters.f0_collection_retained_bytes,
                self.counters.scc_plan_retained_payload_bytes,
            ],
            "F2 batch retained bytes",
        );
        // The endpoint workspaces peak before the retained plan exists.  SCC
        // construction instead co-resides with the retained F0 batch, so add
        // only its non-input workspace to avoid charging F0 records twice.
        self.counters.f2_batch_plan_peak_bytes =
            self.counters
                .f0_collection_peak_bytes
                .max(checked_usize_sum(
                    [
                        self.counters.f0_collection_retained_bytes,
                        scc_temporary_or_plan_bytes,
                    ],
                    "F2 batch-plan peak bytes",
                ));
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ArtifactMismatch;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
/// Capacity and retained-byte fields model `capacity * size_of::<slot>()`.
/// They exclude allocator metadata, bucket control bytes, and fragmentation;
/// the paired capacity fields report the exact container capacities observed.
pub struct ProductionCounters {
    hir_traversals: usize,
    /// One physical visit per HIR item during F0 collection.
    body_pass_visits: usize,
    /// Admitted definitions registered during the one physical HIR pass.
    definition_registration_visits: usize,
    /// Completed non-error bodies retained by F0.
    collected_complete_bodies: usize,
    /// Error bodies retained by F0 rather than dropped from the definition table.
    collected_error_bodies: usize,
    /// Error-status binding bodies whose HIR name resolution was ambiguous.
    collected_ambiguous_name_bodies: usize,
    /// Error-status binding bodies whose HIR name resolution was unresolved.
    collected_unresolved_name_bodies: usize,
    collected_definitions: usize,
    /// One logical endpoint-resolution visit per collected binding-body name use.
    definition_use_endpoint_pass_visits: usize,
    /// Greatest pending-endpoint vector capacity while collection owns it.
    definition_use_endpoint_workspace_peak_capacity: usize,
    /// Pending-endpoint vector capacity growths, including initial allocation.
    definition_use_endpoint_workspace_capacity_growths: usize,
    /// Byte model for the temporary pending-endpoint vector at its greatest capacity.
    definition_use_endpoint_workspace_peak_bytes: usize,
    /// One insert into the temporary borrowed `DefId -> DefinitionOrderId` index.
    definition_endpoint_index_inserts: usize,
    /// One lookup in that index for each pending resolved endpoint.
    definition_endpoint_index_probes: usize,
    /// Dynamic `DefId` payload bytes presented to the endpoint index's derived
    /// hash: once for each successful definition insert and every use lookup.
    /// This counts spelling plus module file-key realm/path payload only; it is
    /// not allocator, timing, or bucket-control accounting.
    definition_endpoint_identity_hash_byte_incidences: usize,
    /// Conservative logical `DefId` equality-payload bytes for successful
    /// endpoint lookups. This assigns one full matching identity payload per
    /// successful lookup; it does not claim to observe the `HashMap`'s actual
    /// collision comparisons or their byte scans.
    definition_endpoint_logical_successful_equality_byte_incidences: usize,
    /// Greatest capacity of the temporary borrowed endpoint index.
    definition_endpoint_index_peak_capacity: usize,
    /// Endpoint-index capacity growths, including initial allocation.
    definition_endpoint_index_capacity_growths: usize,
    /// Byte model for the temporary endpoint index at its greatest capacity.
    definition_endpoint_index_peak_bytes: usize,
    /// One insert into the retained opaque definition-order index.
    definition_record_index_inserts: usize,
    /// One insert into the retained definition-use index.
    definition_use_index_inserts: usize,
    /// Sum of the retained F0 batch containers after temporary endpoint workspace drops.
    f0_collection_retained_bytes: usize,
    /// Retained F0 bytes plus both temporary endpoint workspaces at their co-resident peak.
    f0_collection_peak_bytes: usize,
    /// Retained F0 batch storage plus its one immutable F2 SCC plan.
    f2_batch_retained_bytes: usize,
    /// Peak of endpoint resolution, or F2 SCC construction after its two
    /// F0-only endpoint workspaces have dropped. The latter adds only F1's
    /// non-input workspace to the already-retained F0 batch.
    f2_batch_plan_peak_bytes: usize,
    retained_definition_uses: usize,
    definition_record_index_capacity: usize,
    definition_record_index_retained_bytes: usize,
    definition_record_retained_bytes: usize,
    definition_use_retained_bytes: usize,
    definition_use_index_capacity: usize,
    definition_use_index_retained_bytes: usize,
    definition_query_probes: usize,
    definition_use_query_probes: usize,
    scc_component_for_definition_query_probes: usize,
    scc_component_members_query_probes: usize,
    scc_component_internal_uses_query_probes: usize,
    scc_component_incoming_uses_query_probes: usize,
    /// F1's standalone static directed graph and frozen-plan accounting.
    /// Byte fields use the established logical `capacity * size_of::<slot>()`
    /// model for `Vec`, `HashMap`, and `HashSet` storage. They exclude allocator
    /// metadata, hash control bytes, fragmentation, allocation timing, and
    /// referent payloads behind stable IDs; capacity counters expose the same
    /// containers independently.
    scc_distinct_arcs: usize,
    scc_retained_occurrence_payloads: usize,
    scc_forward_adjacency_entries: usize,
    scc_forward_payload_lengths: usize,
    scc_forward_adjacency_capacity: usize,
    scc_forward_payload_capacity: usize,
    scc_reverse_adjacency_entries: usize,
    scc_reverse_adjacency_capacity: usize,
    scc_definition_index_probes: usize,
    scc_definition_index_capacity: usize,
    scc_seen_use_set_probes: usize,
    scc_seen_use_set_capacity: usize,
    scc_condensation_set_probes: usize,
    scc_condensation_set_capacity: usize,
    scc_plan_component_index_probes: usize,
    scc_plan_component_index_capacity: usize,
    scc_plan_definition_index_probes: usize,
    scc_plan_definition_index_capacity: usize,
    scc_map_set_rebuilds: usize,
    /// Logical clone operations for F1's artifact-branded stable IDs.
    scc_stable_id_clone_count: usize,
    /// `size_of::<DefinitionOrderId/DefinitionUseId>()` per logical clone;
    /// this is payload copying, not an allocator or `Arc`-control-block claim.
    scc_stable_id_clone_payload_bytes: usize,
    scc_node_visits: usize,
    scc_edge_visits: usize,
    scc_stack_pushes: usize,
    scc_lowlink_writes: usize,
    scc_component_writes: usize,
    scc_peak_stack_bytes: usize,
    scc_peak_temporary_set_bytes: usize,
    /// Co-resident Kosaraju phase: then-live F1 input/graph/index baseline plus
    /// visited/assigned, finish order, DFS stacks, and discovered components.
    scc_kosaraju_workspace_peak_bytes: usize,
    /// Co-resident partition transfer: source SCC/arc payloads and growing
    /// destination components with all then-live graph/index baselines.
    scc_partition_workspace_peak_bytes: usize,
    /// Co-resident scheduler phase: all still-live graph/index/condensation
    /// baselines plus predecessors, dependency counts, ready heap, and output.
    scc_scheduler_workspace_peak_bytes: usize,
    /// Co-resident freeze transition: remaining source component slots,
    /// growing ordered plan components, both plan maps, and live graph/index
    /// baselines after scheduler worklists have dropped.
    scc_freeze_transition_peak_bytes: usize,
    scc_maximum_component_size: usize,
    scc_internal_use_count: usize,
    scc_incoming_use_count: usize,
    scc_condensation_node_visits: usize,
    scc_condensation_edge_visits: usize,
    scc_ready_queue_operations: usize,
    scc_ready_queue_comparisons: usize,
    scc_ready_queue_maximum_size: usize,
    scc_sort_count: usize,
    scc_sort_comparisons: usize,
    scc_sort_elements: usize,
    scc_plan_component_capacity: usize,
    scc_plan_member_capacity: usize,
    scc_plan_internal_use_capacity: usize,
    scc_plan_incoming_use_capacity: usize,
    /// Frozen retained plan: component/member/use vectors and both plan maps.
    scc_plan_retained_payload_bytes: usize,
    /// Allocation-free ordered-use sorting and graph construction with then-live input,
    /// vector, map, and set logical bytes.
    scc_graph_workspace_peak_known_bytes: usize,
    /// Maximum sampled co-resident F1 phase (graph, Kosaraju, partition,
    /// scheduler, freeze transition, or retained plan). It is deliberately
    /// F1-only, not a claim about `ConstraintBatch` integration.
    scc_f1_graph_input_plan_peak_known_bytes: usize,
    cst_traversals: usize,
    cst_rescans: usize,
    hir_clone_count: usize,
    typed_tree_copies: usize,
    copied_spelling_bytes: usize,
    emitted_facts: usize,
    admitted_facts: usize,
    duplicate_facts: usize,
    canonical_map_probes: usize,
    canonical_map_rebuilds: usize,
    canonical_map_capacity: usize,
    canonical_map_retained_bytes: usize,
    occurrence_component_index_probes: usize,
    occurrence_component_index_capacity: usize,
    occurrence_component_index_retained_bytes: usize,
    occurrence_component_query_probes: usize,
    root_component_index_probes: usize,
    root_component_index_capacity: usize,
    root_component_index_retained_bytes: usize,
    root_component_query_probes: usize,
    consumed_receipt_index_probes: usize,
    consumed_receipt_index_capacity: usize,
    consumed_receipt_index_retained_bytes: usize,
    solved_root_index_probes: usize,
    solved_root_index_capacity: usize,
    solved_root_index_retained_bytes: usize,
    solved_root_query_probes: usize,
    generated_work_items: usize,
    accepted_work_items: usize,
    duplicate_work_items: usize,
    /// Logical semantic endpoint incidences; no per-component adjacency lists
    /// are retained by this reference solver.
    adjacency_appends: usize,
    adjacency_visits: usize,
    component_allocations: usize,
    component_retained_bytes: usize,
    fact_allocations: usize,
    fact_retained_bytes: usize,
    occurrence_allocations: usize,
    occurrence_retained_bytes: usize,
    occurrence_record_retained_bytes: usize,
    root_allocations: usize,
    root_retained_bytes: usize,
    hir_definition_root_allocation_bytes: usize,
    definition_root_def_id_clone_bytes: usize,
    index_rebuilds: usize,
    index_capacity: usize,
    provenance_edges: usize,
    provenance_retained_bytes: usize,
    solved_projection_retained_bytes: usize,
    solver_workspace_retained_bytes: usize,
    bounds_workspace_capacity: usize,
    bounds_workspace_retained_bytes: usize,
    fanout_index_capacity: usize,
    fanout_index_retained_bytes: usize,
    failed_component_workspace_capacity: usize,
    failed_component_workspace_retained_bytes: usize,
    solver_error_workspace_capacity: usize,
    solver_error_workspace_retained_bytes: usize,
    eager_explanation_builds: usize,
    scc_execution_component_visits: usize,
    scc_execution_internal_use_connections: usize,
    scc_execution_draft_members: usize,
    scc_execution_drafts_visible_barriers: usize,
    scc_execution_finalized_members: usize,
    scc_execution_installed_members: usize,
    scc_execution_incoming_instantiations: usize,
    scc_execution_int_instantiation_facts: usize,
    scc_execution_bottom_trivial_instantiations: usize,
    scc_execution_draft_lookups: usize,
    scc_execution_cross_draft_visits: usize,
    constraint_pair_admissions: usize,
    constraint_pair_duplicates: usize,
    lower_bound_insertions: usize,
    upper_bound_insertions: usize,
    lower_bound_replays: usize,
    upper_bound_replays: usize,
    scheme_table_len: usize,
    scheme_table_capacity: usize,
    scheme_table_retained_bytes: usize,
    scheme_table_rebuilds: usize,
    scheme_root_query_probes: usize,
    scheme_root_index_capacity: usize,
    scheme_root_index_retained_bytes: usize,
    scheme_root_index_growths: usize,
    scheme_root_index_rebuilds: usize,
    scheme_root_query_identity_hash_byte_incidences: usize,
    scheme_root_query_logical_successful_equality_byte_incidences: usize,
    draft_scratch_max_len: usize,
    draft_scratch_capacity: usize,
    draft_scratch_retained_bytes: usize,
    draft_scratch_growths: usize,
    bound_table_retained_bytes: usize,
    bound_table_capacity: usize,
    bound_table_growths: usize,
    bound_table_rebuilds: usize,
    bound_table_peak_bytes: usize,
    constraint_pair_cache_retained_bytes: usize,
    constraint_pair_cache_capacity: usize,
    constraint_pair_cache_growths: usize,
    constraint_pair_cache_rebuilds: usize,
    constraint_pair_cache_peak_bytes: usize,
    semantic_arena_retained_bytes: usize,
    semantic_arena_peak_bytes: usize,
    routed_use_provenance_len: usize,
    routed_use_provenance_capacity: usize,
    routed_use_provenance_retained_bytes: usize,
    routed_use_provenance_growths: usize,
    occurrence_bound_state_retained_bytes: usize,
    occurrence_bound_state_len: usize,
    occurrence_bound_state_capacity: usize,
    occurrence_bound_state_growths: usize,
    finish_projection_visits: usize,
    inference_session_retained_bytes: usize,
    inference_session_peak_bytes: usize,
    constraint_store_requested_capacity: usize,
    constraint_store_actual_capacity: usize,
    constraint_store_growths: usize,
    constraint_store_rebuilds: usize,
    fact_store_requested_capacity: usize,
    fact_store_actual_capacity: usize,
    fact_store_growths: usize,
    fact_store_rebuilds: usize,
    canonical_map_requested_capacity: usize,
    canonical_map_actual_capacity: usize,
    canonical_map_growths: usize,
    provenance_requested_capacity: usize,
    provenance_actual_capacity: usize,
    provenance_growths: usize,
    provenance_rebuilds: usize,
    consumed_receipt_requested_capacity: usize,
    consumed_receipt_actual_capacity: usize,
    consumed_receipt_growths: usize,
    consumed_receipt_rebuilds: usize,
    scc_count: usize,
}
macro_rules! access { ($($field:ident),+ $(,)?) => {$(pub const fn $field(&self) -> usize { self.$field })+}; }
impl ProductionCounters {
    access!(
        hir_traversals,
        body_pass_visits,
        definition_registration_visits,
        collected_complete_bodies,
        collected_error_bodies,
        collected_ambiguous_name_bodies,
        collected_unresolved_name_bodies,
        collected_definitions,
        definition_use_endpoint_pass_visits,
        definition_use_endpoint_workspace_peak_capacity,
        definition_use_endpoint_workspace_capacity_growths,
        definition_use_endpoint_workspace_peak_bytes,
        definition_endpoint_index_inserts,
        definition_endpoint_index_probes,
        definition_endpoint_identity_hash_byte_incidences,
        definition_endpoint_logical_successful_equality_byte_incidences,
        definition_endpoint_index_peak_capacity,
        definition_endpoint_index_capacity_growths,
        definition_endpoint_index_peak_bytes,
        definition_record_index_inserts,
        definition_use_index_inserts,
        f0_collection_retained_bytes,
        f0_collection_peak_bytes,
        f2_batch_retained_bytes,
        f2_batch_plan_peak_bytes,
        retained_definition_uses,
        definition_record_index_capacity,
        definition_record_index_retained_bytes,
        definition_record_retained_bytes,
        definition_use_retained_bytes,
        definition_use_index_capacity,
        definition_use_index_retained_bytes,
        definition_query_probes,
        definition_use_query_probes,
        scc_component_for_definition_query_probes,
        scc_component_members_query_probes,
        scc_component_internal_uses_query_probes,
        scc_component_incoming_uses_query_probes,
        scc_distinct_arcs,
        scc_retained_occurrence_payloads,
        scc_forward_adjacency_entries,
        scc_forward_payload_lengths,
        scc_forward_adjacency_capacity,
        scc_forward_payload_capacity,
        scc_reverse_adjacency_entries,
        scc_reverse_adjacency_capacity,
        scc_definition_index_probes,
        scc_definition_index_capacity,
        scc_seen_use_set_probes,
        scc_seen_use_set_capacity,
        scc_condensation_set_probes,
        scc_condensation_set_capacity,
        scc_plan_component_index_probes,
        scc_plan_component_index_capacity,
        scc_plan_definition_index_probes,
        scc_plan_definition_index_capacity,
        scc_map_set_rebuilds,
        scc_stable_id_clone_count,
        scc_stable_id_clone_payload_bytes,
        scc_node_visits,
        scc_edge_visits,
        scc_stack_pushes,
        scc_lowlink_writes,
        scc_component_writes,
        scc_peak_stack_bytes,
        scc_peak_temporary_set_bytes,
        scc_kosaraju_workspace_peak_bytes,
        scc_partition_workspace_peak_bytes,
        scc_scheduler_workspace_peak_bytes,
        scc_freeze_transition_peak_bytes,
        scc_maximum_component_size,
        scc_internal_use_count,
        scc_incoming_use_count,
        scc_condensation_node_visits,
        scc_condensation_edge_visits,
        scc_ready_queue_operations,
        scc_ready_queue_comparisons,
        scc_ready_queue_maximum_size,
        scc_sort_count,
        scc_sort_comparisons,
        scc_sort_elements,
        scc_plan_component_capacity,
        scc_plan_member_capacity,
        scc_plan_internal_use_capacity,
        scc_plan_incoming_use_capacity,
        scc_plan_retained_payload_bytes,
        scc_graph_workspace_peak_known_bytes,
        scc_f1_graph_input_plan_peak_known_bytes,
        cst_traversals,
        cst_rescans,
        hir_clone_count,
        typed_tree_copies,
        copied_spelling_bytes,
        emitted_facts,
        admitted_facts,
        duplicate_facts,
        canonical_map_probes,
        canonical_map_rebuilds,
        canonical_map_capacity,
        canonical_map_retained_bytes,
        occurrence_component_index_probes,
        occurrence_component_index_capacity,
        occurrence_component_index_retained_bytes,
        occurrence_component_query_probes,
        root_component_index_probes,
        root_component_index_capacity,
        root_component_index_retained_bytes,
        root_component_query_probes,
        consumed_receipt_index_probes,
        consumed_receipt_index_capacity,
        consumed_receipt_index_retained_bytes,
        solved_root_query_probes,
        generated_work_items,
        accepted_work_items,
        duplicate_work_items,
        component_allocations,
        component_retained_bytes,
        fact_allocations,
        fact_retained_bytes,
        occurrence_allocations,
        occurrence_retained_bytes,
        occurrence_record_retained_bytes,
        root_allocations,
        root_retained_bytes,
        hir_definition_root_allocation_bytes,
        definition_root_def_id_clone_bytes,
        index_rebuilds,
        index_capacity,
        provenance_edges,
        provenance_retained_bytes,
        solved_projection_retained_bytes,
        solver_error_workspace_capacity,
        solver_error_workspace_retained_bytes,
        eager_explanation_builds,
        scc_execution_component_visits,
        scc_execution_internal_use_connections,
        scc_execution_draft_members,
        scc_execution_drafts_visible_barriers,
        scc_execution_finalized_members,
        scc_execution_installed_members,
        scc_execution_incoming_instantiations,
        scc_execution_int_instantiation_facts,
        scc_execution_bottom_trivial_instantiations,
        scc_execution_draft_lookups,
        scc_execution_cross_draft_visits,
        constraint_pair_admissions,
        constraint_pair_duplicates,
        lower_bound_insertions,
        upper_bound_insertions,
        lower_bound_replays,
        upper_bound_replays,
        scheme_table_len,
        scheme_table_capacity,
        scheme_table_retained_bytes,
        scheme_table_rebuilds,
        scheme_root_query_probes,
        scheme_root_index_capacity,
        scheme_root_index_retained_bytes,
        scheme_root_index_growths,
        scheme_root_index_rebuilds,
        scheme_root_query_identity_hash_byte_incidences,
        scheme_root_query_logical_successful_equality_byte_incidences,
        draft_scratch_max_len,
        draft_scratch_capacity,
        draft_scratch_retained_bytes,
        draft_scratch_growths,
        bound_table_retained_bytes,
        bound_table_capacity,
        bound_table_growths,
        bound_table_rebuilds,
        bound_table_peak_bytes,
        constraint_pair_cache_retained_bytes,
        constraint_pair_cache_capacity,
        constraint_pair_cache_growths,
        constraint_pair_cache_rebuilds,
        constraint_pair_cache_peak_bytes,
        semantic_arena_retained_bytes,
        semantic_arena_peak_bytes,
        routed_use_provenance_len,
        routed_use_provenance_capacity,
        routed_use_provenance_retained_bytes,
        routed_use_provenance_growths,
        occurrence_bound_state_retained_bytes,
        occurrence_bound_state_len,
        occurrence_bound_state_capacity,
        occurrence_bound_state_growths,
        finish_projection_visits,
        inference_session_retained_bytes,
        inference_session_peak_bytes,
        constraint_store_requested_capacity,
        constraint_store_actual_capacity,
        constraint_store_growths,
        constraint_store_rebuilds,
        fact_store_requested_capacity,
        fact_store_actual_capacity,
        fact_store_growths,
        canonical_map_requested_capacity,
        canonical_map_actual_capacity,
        canonical_map_growths,
        provenance_requested_capacity,
        provenance_actual_capacity,
        provenance_growths,
        provenance_rebuilds,
        consumed_receipt_requested_capacity,
        consumed_receipt_actual_capacity,
        consumed_receipt_growths,
        consumed_receipt_rebuilds,
        scc_count
    );
    #[deprecated(
        note = "F4 removed the finish-time adjacency projector; retained for compatibility"
    )]
    pub const fn adjacency_appends(&self) -> usize {
        0
    }
    #[deprecated(
        note = "F4 removed the finish-time adjacency projector; retained for compatibility"
    )]
    pub const fn adjacency_visits(&self) -> usize {
        0
    }
    #[deprecated(note = "F4 removed the finish-time fanout index; retained for compatibility")]
    pub const fn maximum_fan_out(&self) -> usize {
        0
    }
    #[deprecated(note = "F4 removed the solved-root result map; retained for compatibility")]
    pub const fn solved_root_index_probes(&self) -> usize {
        0
    }
    #[deprecated(note = "F4 removed the solved-root result map; retained for compatibility")]
    pub const fn solved_root_index_capacity(&self) -> usize {
        0
    }
    #[deprecated(note = "F4 removed the solved-root result map; retained for compatibility")]
    pub const fn solved_root_index_retained_bytes(&self) -> usize {
        0
    }
    #[deprecated(note = "F4 removed the finish-time bounds workspace; retained for compatibility")]
    pub const fn bounds_workspace_capacity(&self) -> usize {
        0
    }
    #[deprecated(note = "F4 removed the finish-time bounds workspace; retained for compatibility")]
    pub const fn bounds_workspace_retained_bytes(&self) -> usize {
        0
    }
    #[deprecated(note = "F4 removed the finish-time fanout index; retained for compatibility")]
    pub const fn fanout_index_capacity(&self) -> usize {
        0
    }
    #[deprecated(note = "F4 removed the finish-time fanout index; retained for compatibility")]
    pub const fn fanout_index_retained_bytes(&self) -> usize {
        0
    }
    #[deprecated(note = "F4 removed the finish-time solver workspace; retained for compatibility")]
    pub const fn solver_workspace_retained_bytes(&self) -> usize {
        0
    }
    #[deprecated(
        note = "F4 removed the finish-time cross-kind workspace; retained for compatibility"
    )]
    pub const fn failed_component_workspace_capacity(&self) -> usize {
        0
    }
    #[deprecated(
        note = "F4 removed the finish-time cross-kind workspace; retained for compatibility"
    )]
    pub const fn failed_component_workspace_retained_bytes(&self) -> usize {
        0
    }
    fn combine(&mut self, other: &Self) {
        macro_rules! add { ($($field:ident),+) => {$(self.$field += other.$field;)+}; }
        add!(
            hir_traversals,
            body_pass_visits,
            definition_registration_visits,
            collected_complete_bodies,
            collected_error_bodies,
            collected_ambiguous_name_bodies,
            collected_unresolved_name_bodies,
            collected_definitions,
            definition_use_endpoint_pass_visits,
            definition_use_endpoint_workspace_peak_capacity,
            definition_use_endpoint_workspace_capacity_growths,
            definition_use_endpoint_workspace_peak_bytes,
            definition_endpoint_index_inserts,
            definition_endpoint_index_probes,
            definition_endpoint_identity_hash_byte_incidences,
            definition_endpoint_logical_successful_equality_byte_incidences,
            definition_endpoint_index_peak_capacity,
            definition_endpoint_index_capacity_growths,
            definition_endpoint_index_peak_bytes,
            definition_record_index_inserts,
            definition_use_index_inserts,
            f0_collection_retained_bytes,
            f0_collection_peak_bytes,
            f2_batch_retained_bytes,
            f2_batch_plan_peak_bytes,
            retained_definition_uses,
            definition_record_index_capacity,
            definition_record_index_retained_bytes,
            definition_record_retained_bytes,
            definition_use_retained_bytes,
            definition_use_index_capacity,
            definition_use_index_retained_bytes,
            definition_query_probes,
            definition_use_query_probes,
            scc_component_for_definition_query_probes,
            scc_component_members_query_probes,
            scc_component_internal_uses_query_probes,
            scc_component_incoming_uses_query_probes,
            scc_distinct_arcs,
            scc_retained_occurrence_payloads,
            scc_forward_adjacency_entries,
            scc_forward_payload_lengths,
            scc_forward_adjacency_capacity,
            scc_forward_payload_capacity,
            scc_reverse_adjacency_entries,
            scc_reverse_adjacency_capacity,
            scc_definition_index_probes,
            scc_definition_index_capacity,
            scc_seen_use_set_probes,
            scc_seen_use_set_capacity,
            scc_condensation_set_probes,
            scc_condensation_set_capacity,
            scc_plan_component_index_probes,
            scc_plan_component_index_capacity,
            scc_plan_definition_index_probes,
            scc_plan_definition_index_capacity,
            scc_map_set_rebuilds,
            scc_stable_id_clone_count,
            scc_stable_id_clone_payload_bytes,
            scc_node_visits,
            scc_edge_visits,
            scc_stack_pushes,
            scc_lowlink_writes,
            scc_component_writes,
            scc_peak_stack_bytes,
            scc_peak_temporary_set_bytes,
            scc_kosaraju_workspace_peak_bytes,
            scc_partition_workspace_peak_bytes,
            scc_scheduler_workspace_peak_bytes,
            scc_freeze_transition_peak_bytes,
            scc_maximum_component_size,
            scc_internal_use_count,
            scc_incoming_use_count,
            scc_condensation_node_visits,
            scc_condensation_edge_visits,
            scc_ready_queue_operations,
            scc_ready_queue_comparisons,
            scc_ready_queue_maximum_size,
            scc_sort_count,
            scc_sort_comparisons,
            scc_sort_elements,
            scc_plan_component_capacity,
            scc_plan_member_capacity,
            scc_plan_internal_use_capacity,
            scc_plan_incoming_use_capacity,
            scc_plan_retained_payload_bytes,
            scc_graph_workspace_peak_known_bytes,
            scc_f1_graph_input_plan_peak_known_bytes,
            cst_traversals,
            cst_rescans,
            hir_clone_count,
            typed_tree_copies,
            copied_spelling_bytes,
            emitted_facts,
            admitted_facts,
            duplicate_facts,
            canonical_map_probes,
            canonical_map_rebuilds,
            canonical_map_capacity,
            canonical_map_retained_bytes,
            occurrence_component_index_probes,
            occurrence_component_index_capacity,
            occurrence_component_index_retained_bytes,
            occurrence_component_query_probes,
            root_component_index_probes,
            root_component_index_capacity,
            root_component_index_retained_bytes,
            root_component_query_probes,
            consumed_receipt_index_probes,
            consumed_receipt_index_capacity,
            consumed_receipt_index_retained_bytes,
            solved_root_index_probes,
            solved_root_index_capacity,
            solved_root_index_retained_bytes,
            solved_root_query_probes,
            generated_work_items,
            accepted_work_items,
            duplicate_work_items,
            adjacency_appends,
            adjacency_visits,
            component_allocations,
            component_retained_bytes,
            fact_allocations,
            fact_retained_bytes,
            occurrence_allocations,
            occurrence_retained_bytes,
            occurrence_record_retained_bytes,
            root_allocations,
            root_retained_bytes,
            hir_definition_root_allocation_bytes,
            definition_root_def_id_clone_bytes,
            index_rebuilds,
            index_capacity,
            provenance_edges,
            provenance_retained_bytes,
            solved_projection_retained_bytes,
            solver_workspace_retained_bytes,
            bounds_workspace_capacity,
            bounds_workspace_retained_bytes,
            fanout_index_capacity,
            fanout_index_retained_bytes,
            failed_component_workspace_capacity,
            failed_component_workspace_retained_bytes,
            solver_error_workspace_capacity,
            solver_error_workspace_retained_bytes,
            eager_explanation_builds,
            scc_execution_component_visits,
            scc_execution_internal_use_connections,
            scc_execution_draft_members,
            scc_execution_drafts_visible_barriers,
            scc_execution_finalized_members,
            scc_execution_installed_members,
            scc_execution_incoming_instantiations,
            scc_execution_int_instantiation_facts,
            scc_execution_bottom_trivial_instantiations,
            scc_execution_draft_lookups,
            scc_execution_cross_draft_visits,
            constraint_pair_admissions,
            constraint_pair_duplicates,
            lower_bound_insertions,
            upper_bound_insertions,
            lower_bound_replays,
            upper_bound_replays,
            scheme_table_len,
            scheme_table_capacity,
            scheme_table_retained_bytes,
            scheme_table_rebuilds,
            scheme_root_query_probes,
            scheme_root_index_capacity,
            scheme_root_index_retained_bytes,
            scheme_root_index_growths,
            scheme_root_index_rebuilds,
            scheme_root_query_identity_hash_byte_incidences,
            scheme_root_query_logical_successful_equality_byte_incidences,
            draft_scratch_max_len,
            draft_scratch_capacity,
            draft_scratch_retained_bytes,
            draft_scratch_growths,
            bound_table_retained_bytes,
            bound_table_capacity,
            bound_table_growths,
            bound_table_rebuilds,
            bound_table_peak_bytes,
            constraint_pair_cache_retained_bytes,
            constraint_pair_cache_capacity,
            constraint_pair_cache_growths,
            constraint_pair_cache_rebuilds,
            constraint_pair_cache_peak_bytes,
            semantic_arena_retained_bytes,
            semantic_arena_peak_bytes,
            routed_use_provenance_len,
            routed_use_provenance_capacity,
            routed_use_provenance_retained_bytes,
            routed_use_provenance_growths,
            occurrence_bound_state_retained_bytes,
            occurrence_bound_state_len,
            occurrence_bound_state_capacity,
            occurrence_bound_state_growths,
            finish_projection_visits,
            inference_session_retained_bytes,
            inference_session_peak_bytes,
            constraint_store_requested_capacity,
            constraint_store_actual_capacity,
            constraint_store_growths,
            constraint_store_rebuilds,
            fact_store_requested_capacity,
            fact_store_actual_capacity,
            fact_store_growths,
            fact_store_rebuilds,
            canonical_map_requested_capacity,
            canonical_map_actual_capacity,
            canonical_map_growths,
            provenance_requested_capacity,
            provenance_actual_capacity,
            provenance_growths,
            provenance_rebuilds,
            consumed_receipt_requested_capacity,
            consumed_receipt_actual_capacity,
            consumed_receipt_growths,
            consumed_receipt_rebuilds,
            scc_count
        );
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct FactId(u32);
impl FactId {
    pub const fn index(self) -> u32 {
        self.0
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AdmissionDelta {
    Accepted,
    Duplicate,
}
#[derive(Debug)]
struct StoreReceiptToken;

/// A receipt can be consumed only by the exact store transaction that minted it.
#[derive(Clone, Debug)]
pub struct AdmissionReceipt {
    store_token: Arc<StoreReceiptToken>,
    serial: u64,
    occurrence: ConstraintOccurrenceId,
    cause: CauseId,
    fact: FactId,
    delta: AdmissionDelta,
}
impl AdmissionReceipt {
    pub fn occurrence(&self) -> &ConstraintOccurrenceId {
        &self.occurrence
    }
    pub fn cause(&self) -> &CauseId {
        &self.cause
    }
    pub const fn fact(&self) -> FactId {
        self.fact
    }
    pub const fn delta(&self) -> AdmissionDelta {
        self.delta
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProvenanceEdge {
    cause: CauseId,
    fact: FactId,
}
impl ProvenanceEdge {
    pub fn cause(&self) -> &CauseId {
        &self.cause
    }
    pub const fn fact(&self) -> FactId {
        self.fact
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticFact {
    id: FactId,
    lower: Term,
    upper: Term,
}
impl SemanticFact {
    pub const fn id(&self) -> FactId {
        self.id
    }
    pub const fn lower(&self) -> Term {
        self.lower
    }
    pub const fn upper(&self) -> Term {
        self.upper
    }
}

/// The artifact-bound semantic authority. The transaction emits receipts;
/// only `record_provenance` consumes them into the separate provenance log.
#[derive(Debug)]
pub struct ConstraintStore {
    hir: Arc<HirModule>,
    terms: BranchTermArena,
    receipt_token: Arc<StoreReceiptToken>,
    next_receipt: u64,
    consumed_receipts: HashSet<u64>,
    facts: Vec<SemanticFact>,
    canonical: HashMap<FactKey, FactId>,
    provenance: Vec<ProvenanceEdge>,
    comparisons: Arc<AtomicUsize>,
    counters: ProductionCounters,
    #[cfg(test)]
    injected_admission_failure: Option<ConstraintError>,
    #[cfg(test)]
    injected_provenance_failure: Option<ConstraintError>,
}
impl ConstraintStore {
    pub fn from_batch(batch: ConstraintBatch) -> Self {
        let lineage = batch.term_lineage();
        Self::with_capacity(batch.hir, lineage, 0)
    }
    /// F4 reserves every store lane before initial admission; the public
    /// batch-transfer constructor deliberately requests zero fact capacity.
    fn with_capacity(
        hir: Arc<HirModule>,
        lineage: Arc<TermLineage>,
        requested_capacity: usize,
    ) -> Self {
        let facts = Vec::with_capacity(requested_capacity);
        let canonical = HashMap::with_capacity(requested_capacity);
        let provenance = Vec::with_capacity(requested_capacity);
        let consumed_receipts = HashSet::with_capacity(requested_capacity);
        Self {
            hir,
            terms: BranchTermArena::new(lineage),
            receipt_token: Arc::new(StoreReceiptToken),
            next_receipt: 0,
            consumed_receipts,
            facts,
            canonical,
            provenance,
            comparisons: Arc::new(AtomicUsize::new(0)),
            counters: ProductionCounters {
                fact_store_requested_capacity: requested_capacity,
                canonical_map_requested_capacity: requested_capacity,
                provenance_requested_capacity: requested_capacity,
                consumed_receipt_requested_capacity: requested_capacity,
                ..ProductionCounters::default()
            },
            #[cfg(test)]
            injected_admission_failure: None,
            #[cfg(test)]
            injected_provenance_failure: None,
        }
    }
    pub fn transaction(&mut self) -> ConstraintTransaction<'_> {
        ConstraintTransaction { store: self }
    }
    pub fn term_view(&self, term: Term) -> Result<TermView<'_>, TermLookupError> {
        self.terms.term_view(term)
    }
    pub fn term_kind(&self, term: Term) -> Result<ComponentKind, TermLookupError> {
        self.terms.term_kind(term)
    }
    fn inference_term_retained_bytes(&self) -> usize {
        self.terms.retained_bytes()
    }
    #[cfg(test)]
    fn independent_inference_term_retained_bytes(&self) -> usize {
        self.terms.independent_retained_bytes()
    }
    #[cfg(test)]
    fn push_test_branch_term(&mut self, node: TermNode) -> Term {
        self.terms
            .push(node)
            .expect("private term-arena evidence has available identity")
    }
    #[cfg(test)]
    fn term_page_observations(&self) -> term::TermPageObservations {
        self.terms.observations()
    }
    pub fn record_provenance(&mut self, receipt: AdmissionReceipt) -> Result<(), ConstraintError> {
        if !Arc::ptr_eq(&self.receipt_token, &receipt.store_token) {
            return Err(ConstraintError::AlienReceipt);
        }
        self.require_owned(receipt.occurrence.occurrence())?;
        if receipt.cause.occurrence != receipt.occurrence
            || self
                .facts
                .get(receipt.fact.index() as usize)
                .map(SemanticFact::id)
                != Some(receipt.fact)
        {
            return Err(ConstraintError::ReceiptMismatch);
        }
        #[cfg(test)]
        if let Some(error) = self.injected_provenance_failure.take() {
            return Err(error);
        }
        self.counters.consumed_receipt_index_probes += 1;
        let old_capacity = self.consumed_receipts.capacity();
        if !self.consumed_receipts.insert(receipt.serial) {
            return Err(ConstraintError::ReceiptConsumed);
        }
        if self.consumed_receipts.capacity() != old_capacity {
            self.counters.consumed_receipt_growths += 1;
            self.counters.consumed_receipt_rebuilds += 1;
        }
        let old_capacity = self.provenance.capacity();
        self.provenance.push(ProvenanceEdge {
            cause: receipt.cause,
            fact: receipt.fact,
        });
        if self.provenance.capacity() != old_capacity {
            self.counters.provenance_growths += 1;
            self.counters.provenance_rebuilds += 1;
        }
        self.counters.provenance_edges += 1;
        self.counters.provenance_retained_bytes = checked_capacity_bytes::<ProvenanceEdge>(
            self.provenance.capacity(),
            "constraint-store provenance",
        );
        Ok(())
    }
    pub fn facts(&self) -> &[SemanticFact] {
        &self.facts
    }
    pub fn provenance(&self) -> &[ProvenanceEdge] {
        &self.provenance
    }
    pub fn counters(&self) -> &ProductionCounters {
        &self.counters
    }
    fn require_owned(&self, occurrence: &HirOccurrenceId) -> Result<(), ConstraintError> {
        self.hir
            .owns_occurrence(occurrence)
            .then_some(())
            .ok_or(ConstraintError::ArtifactMismatch)
    }
    fn finish_accounting(&mut self) {
        self.counters.fact_retained_bytes =
            checked_capacity_bytes::<SemanticFact>(self.facts.capacity(), "constraint-store facts");
        self.counters.fact_store_actual_capacity = self.facts.capacity();
        self.counters.canonical_map_capacity = self.canonical.capacity();
        self.counters.canonical_map_actual_capacity = self.canonical.capacity();
        self.counters.canonical_map_retained_bytes = checked_capacity_bytes::<(FactKey, FactId)>(
            self.canonical.capacity(),
            "constraint-store canonical map",
        );
        self.counters.canonical_map_probes = self.comparisons.load(Ordering::Relaxed);
        self.counters.consumed_receipt_index_capacity = self.consumed_receipts.capacity();
        self.counters.consumed_receipt_actual_capacity = self.consumed_receipts.capacity();
        self.counters.provenance_actual_capacity = self.provenance.capacity();
        self.counters.constraint_store_requested_capacity = checked_usize_sum(
            [
                self.counters.fact_store_requested_capacity,
                self.counters.canonical_map_requested_capacity,
                self.counters.provenance_requested_capacity,
                self.counters.consumed_receipt_requested_capacity,
            ],
            "constraint-store requested capacity",
        );
        self.counters.constraint_store_actual_capacity = checked_usize_sum(
            [
                self.counters.fact_store_actual_capacity,
                self.counters.canonical_map_actual_capacity,
                self.counters.provenance_actual_capacity,
                self.counters.consumed_receipt_actual_capacity,
            ],
            "constraint-store actual capacity",
        );
        self.counters.constraint_store_growths = checked_usize_sum(
            [
                self.counters.fact_store_growths,
                self.counters.canonical_map_growths,
                self.counters.provenance_growths,
                self.counters.consumed_receipt_growths,
            ],
            "constraint-store growth",
        );
        self.counters.constraint_store_rebuilds = checked_usize_sum(
            [
                self.counters.fact_store_rebuilds,
                self.counters.canonical_map_rebuilds,
                self.counters.provenance_rebuilds,
                self.counters.consumed_receipt_rebuilds,
            ],
            "constraint-store rebuild",
        );
        self.counters.consumed_receipt_index_retained_bytes = checked_capacity_bytes::<u64>(
            self.consumed_receipts.capacity(),
            "constraint-store consumed receipts",
        );
    }
}
pub struct ConstraintTransaction<'a> {
    store: &'a mut ConstraintStore,
}
impl ConstraintTransaction<'_> {
    pub fn admit(
        &mut self,
        occurrence: &ConstraintOccurrence,
    ) -> Result<AdmissionReceipt, ConstraintError> {
        let lower_kind = self.validate_term(occurrence.lower)?;
        let upper_kind = self.validate_term(occurrence.upper)?;
        self.store.require_owned(occurrence.id.occurrence())?;
        if occurrence.cause.occurrence != occurrence.id {
            return Err(ConstraintError::CauseMismatch);
        }
        if lower_kind != upper_kind {
            return Err(ConstraintError::CrossKind {
                lower: lower_kind,
                upper: upper_kind,
            });
        }
        #[cfg(test)]
        if let Some(error) = self.store.injected_admission_failure.take() {
            return Err(error);
        }
        let key = FactKey::new(
            occurrence.lower.clone(),
            occurrence.upper.clone(),
            self.store.comparisons.clone(),
        );
        let (fact, delta) = if let Some(fact) = self.store.canonical.get(&key).copied() {
            self.store.counters.duplicate_facts += 1;
            self.store.counters.duplicate_work_items += 1;
            (fact, AdmissionDelta::Duplicate)
        } else {
            let fact = FactId(
                u32::try_from(self.store.facts.len())
                    .map_err(|_| ConstraintError::IdentityExhausted)?,
            );
            let old_fact_capacity = self.store.facts.capacity();
            self.store.facts.push(SemanticFact {
                id: fact,
                lower: occurrence.lower.clone(),
                upper: occurrence.upper.clone(),
            });
            if self.store.facts.capacity() != old_fact_capacity {
                self.store.counters.fact_store_growths += 1;
                self.store.counters.fact_store_rebuilds += 1;
            }
            let old_capacity = self.store.canonical.capacity();
            self.store.canonical.insert(key, fact);
            if self.store.canonical.capacity() != old_capacity {
                self.store.counters.canonical_map_rebuilds += 1;
                self.store.counters.canonical_map_growths += 1;
            }
            self.store.counters.admitted_facts += 1;
            self.store.counters.accepted_work_items += 1;
            self.store.counters.fact_allocations += 1;
            (fact, AdmissionDelta::Accepted)
        };
        let serial = self.store.next_receipt;
        self.store.next_receipt = self
            .store
            .next_receipt
            .checked_add(1)
            .ok_or(ConstraintError::IdentityExhausted)?;
        Ok(AdmissionReceipt {
            store_token: self.store.receipt_token.clone(),
            serial,
            occurrence: occurrence.id.clone(),
            cause: occurrence.cause.clone(),
            fact,
            delta,
        })
    }
    fn validate_term(&self, term: Term) -> Result<ComponentKind, ConstraintError> {
        match self.store.term_kind(term) {
            Ok(kind) => Ok(kind),
            Err(TermLookupError::ArenaMismatch) => Err(ConstraintError::ArtifactMismatch),
            Err(TermLookupError::InvalidHandle) => {
                panic!("same-lineage term missing from this store branch before admission")
            }
        }
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstraintError {
    CrossKind {
        lower: ComponentKind,
        upper: ComponentKind,
    },
    ArtifactMismatch,
    CauseMismatch,
    ReceiptMismatch,
    AlienReceipt,
    ReceiptConsumed,
    IdentityExhausted,
}
#[derive(Clone, Debug)]
struct FactKey {
    lower: Term,
    upper: Term,
    comparisons: Arc<AtomicUsize>,
}
impl FactKey {
    fn new(lower: Term, upper: Term, comparisons: Arc<AtomicUsize>) -> Self {
        Self {
            lower,
            upper,
            comparisons,
        }
    }
}
impl PartialEq for FactKey {
    fn eq(&self, other: &Self) -> bool {
        self.comparisons.fetch_add(1, Ordering::Relaxed);
        self.lower == other.lower && self.upper == other.upper
    }
}
impl Eq for FactKey {}
impl Hash for FactKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.lower.hash(state);
        self.upper.hash(state);
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SolvedValue {
    Int,
    Unknown,
    Never,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SolvedEffect {
    Empty,
    Unknown,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SolvedProjection {
    value: SolvedValue,
    effect: SolvedEffect,
}
impl SolvedProjection {
    pub const fn value(self) -> SolvedValue {
        self.value
    }
    pub const fn effect(self) -> SolvedEffect {
        self.effect
    }
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SolverErrorKind {
    CrossKind {
        lower: ComponentKind,
        upper: ComponentKind,
    },
    IncompatibleValue {
        lower: ValueShape,
        upper: ValueShape,
    },
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ValueShape {
    Bottom,
    Int,
    Function,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SolverError {
    occurrence: ConstraintOccurrenceId,
    cause: CauseId,
    kind: SolverErrorKind,
}
impl SolverError {
    pub fn occurrence(&self) -> &ConstraintOccurrenceId {
        &self.occurrence
    }
    pub fn cause(&self) -> &CauseId {
        &self.cause
    }
    pub const fn kind(&self) -> SolverErrorKind {
        self.kind
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SolveAvailabilityError {
    ArtifactMismatch,
    CauseMismatch,
    ReceiptMismatch,
    IdentityExhausted,
}
impl From<ConstraintError> for SolveAvailabilityError {
    fn from(value: ConstraintError) -> Self {
        match value {
            ConstraintError::ArtifactMismatch => Self::ArtifactMismatch,
            ConstraintError::CauseMismatch => Self::CauseMismatch,
            ConstraintError::ReceiptMismatch => Self::ReceiptMismatch,
            ConstraintError::AlienReceipt | ConstraintError::ReceiptConsumed => {
                Self::ReceiptMismatch
            }
            ConstraintError::IdentityExhausted => Self::IdentityExhausted,
            ConstraintError::CrossKind { .. } => unreachable!("local error"),
        }
    }
}
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct VariableBounds {
    /// The two row lists are the paired physical representation of one direct
    /// variable edge.  They deliberately do not encode transitive reachability.
    direct_lower_rows: Vec<u32>,
    direct_upper_rows: Vec<u32>,
    exact_non_variable_lowers: Vec<ValueEndpointKey>,
    exact_non_variable_uppers: Vec<ValueEndpointKey>,
    has_int_positive_lower: bool,
}

#[derive(Clone, Default)]
struct EffectBounds {
    direct_lower_rows: Vec<u32>,
    direct_upper_rows: Vec<u32>,
    exact_non_variable_lowers: Vec<EffectEndpointKey>,
    exact_non_variable_uppers: Vec<EffectEndpointKey>,
    has_bottom_lower: bool,
    has_empty_upper: bool,
}

#[derive(Clone, Copy)]
enum LiveConstraintTask {
    Value(CanonicalValuePairKey),
    Effect(EffectEndpointKey, EffectEndpointKey),
}

struct TypedWorkItem {
    task: LiveConstraintTask,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DiagnosticWitness {
    terminal: CanonicalValuePairKey,
    kind: SolverErrorKind,
    distance: u32,
    first_field: Option<FunctionField>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DiagnosticEdge {
    child: CanonicalValuePairKey,
    field: Option<FunctionField>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DiagnosticReverseEdge {
    parent: usize,
    field: Option<FunctionField>,
}

/// One call-local FIFO link.  Pair memo entries deliberately never retain
/// completion routing state: these nodes exist only while one §39 delta is
/// being condensed and settled.
#[derive(Clone, Copy, Debug)]
struct DiagnosticBucketCandidate {
    node: usize,
    witness: DiagnosticWitness,
    next: Option<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DiagnosticCompletion {
    Pending,
    Complete(Option<DiagnosticWitness>),
}

/// The session-wide typed memo is the sole semantic pair authority.  A value
/// pair retains only one finite canonical witness; diagnostics never retain a
/// descendant list, route, or per-cause waiter state.
#[derive(Clone)]
enum TypedPairMemo {
    Effect,
    Value {
        children: Vec<DiagnosticEdge>,
        /// A direct incompatibility is a completion seed, not a completed
        /// summary.  The call-local SCC pass is the only place that changes a
        /// Pending entry into Complete.
        direct_witness: Option<DiagnosticWitness>,
        completion: DiagnosticCompletion,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FunctionField {
    Argument,
    ArgumentEffect,
    ResultEffect,
    Result,
}

#[derive(Clone, Copy)]
enum ExtrusionEndpoint {
    Value(ValueEndpointKey),
    Effect(EffectEndpointKey),
}

#[derive(Clone, Copy, Default)]
#[allow(
    dead_code,
    reason = "deprecated F4 occurrence-bound compatibility fields remain zero; live rows own semantics"
)]
struct OccurrenceExactBounds {
    value_lower_int: bool,
    value_upper_int: bool,
    effect_lower_bottom: bool,
    effect_upper_empty: bool,
}

#[derive(Clone)]
struct DraftScheme(ClosedValueScheme);

#[derive(Clone, Debug, Eq, PartialEq)]
enum F5cPositive {
    Bottom,
    Int,
    Variable(u32),
    Quantified(u32),
    Recursive(u32),
    Union(Vec<F5cPositive>),
    Function {
        argument: Box<F5cNegative>,
        argument_effect: F5cNegativeEffect,
        result_effect: F5cPositiveEffect,
        result: Box<F5cPositive>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum F5cPositiveEffect {
    Bottom,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum F5cNegativeEffect {
    Empty,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum F5cNegative {
    Top,
    Bottom,
    Int,
    Variable(u32),
    Quantified(u32),
    Recursive(u32),
    Intersection(Vec<F5cNegative>),
    Function {
        argument: Box<F5cPositive>,
        argument_effect: F5cPositiveEffect,
        result_effect: F5cNegativeEffect,
        result: Box<F5cNegative>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct F5cRecursiveBound {
    ordinal: u32,
    lower: F5cPositive,
    upper: F5cNegative,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct GeneralizationDraft {
    quantifier_count: u32,
    recursive_bounds: Vec<F5cRecursiveBound>,
    predicate: F5cPositive,
}

/// Root-local F5c expansion state.  Collected rows remain immutable recipes;
/// this walker is the sole owner of polarity incidence, active-path re-entry,
/// and the Q/R decision for one draft.
struct F5cGeneralizer<'a> {
    session: &'a InferenceSession,
    active: Vec<(u32, Polarity)>,
    active_set: HashSet<(u32, Polarity)>,
    function_depth: usize,
    /// Completed acyclic row expansions are reused within one root draft.
    /// Active re-entries deliberately bypass these maps so guarded paths keep
    /// their owner-local R witness.
    positive_cache: HashMap<u32, F5cPositive>,
    negative_cache: HashMap<u32, F5cNegative>,
    positive_seen: HashSet<u32>,
    negative_seen: HashSet<u32>,
    order: Vec<u32>,
    order_seen: HashSet<u32>,
    reentries: Vec<u32>,
    reentry_set: HashSet<u32>,
    invalid_effects: bool,
}

impl<'a> F5cGeneralizer<'a> {
    fn new(session: &'a InferenceSession) -> Self {
        Self {
            session,
            active: Vec::new(),
            active_set: HashSet::new(),
            function_depth: 0,
            positive_cache: HashMap::new(),
            negative_cache: HashMap::new(),
            positive_seen: HashSet::new(),
            negative_seen: HashSet::new(),
            order: Vec::new(),
            order_seen: HashSet::new(),
            reentries: Vec::new(),
            reentry_set: HashSet::new(),
            invalid_effects: false,
        }
    }

    fn mark(&mut self, ordinal: u32, polarity: Polarity) {
        let seen = match polarity {
            Polarity::Positive => &mut self.positive_seen,
            Polarity::Negative => &mut self.negative_seen,
        };
        if seen.insert(ordinal) && self.order_seen.insert(ordinal) {
            self.order.push(ordinal);
        }
    }

    fn active(&self, ordinal: u32, polarity: Polarity) -> bool {
        self.active_set.contains(&(ordinal, polarity))
    }

    fn active_any(&self, ordinal: u32) -> bool {
        self.active_set.contains(&(ordinal, Polarity::Positive))
            || self.active_set.contains(&(ordinal, Polarity::Negative))
    }

    fn cacheable_positive(value: &F5cPositive) -> bool {
        match value {
            F5cPositive::Variable(_) => false,
            F5cPositive::Function {
                argument, result, ..
            } => Self::cacheable_negative(argument) && Self::cacheable_positive(result),
            F5cPositive::Union(values) => values.iter().all(Self::cacheable_positive),
            _ => true,
        }
    }

    fn cacheable_negative(value: &F5cNegative) -> bool {
        match value {
            F5cNegative::Variable(_) => false,
            F5cNegative::Function {
                argument, result, ..
            } => Self::cacheable_positive(argument) && Self::cacheable_negative(result),
            F5cNegative::Intersection(values) => values.iter().all(Self::cacheable_negative),
            _ => true,
        }
    }

    fn positive_row(&mut self, ordinal: u32, root: bool) -> F5cPositive {
        if self.active(ordinal, Polarity::Positive) {
            if self.function_depth > 0 && self.reentry_set.insert(ordinal) {
                self.reentries.push(ordinal);
            }
            self.mark(ordinal, Polarity::Positive);
            return F5cPositive::Variable(ordinal);
        }
        if self.function_depth > 0 && self.active_any(ordinal) && self.reentry_set.insert(ordinal) {
            self.reentries.push(ordinal);
        }
        if !root {
            if let Some(value) = self.positive_cache.get(&ordinal).cloned() {
                self.mark(ordinal, Polarity::Positive);
                return value;
            }
        }
        self.mark(ordinal, Polarity::Positive);
        self.active.push((ordinal, Polarity::Positive));
        self.active_set.insert((ordinal, Polarity::Positive));
        let bounds = self
            .session
            .bounds
            .get(ordinal as usize)
            .cloned()
            .unwrap_or_default();
        let mut members = Vec::new();
        for endpoint in bounds.exact_non_variable_lowers {
            let member = self.positive_endpoint(endpoint);
            if !members.contains(&member) {
                members.push(member);
            }
        }
        // Exact propagation already carries every structural lower reachable
        // through a direct row.  Only an otherwise open non-root variable
        // needs the row census; an open root is the normative Bottom case.
        if members.is_empty() && !root {
            let mut work = bounds.direct_lower_rows.clone();
            let mut visited = HashSet::new();
            while let Some(lower) = work.pop() {
                if !visited.insert(lower) {
                    continue;
                }
                let member = self.positive_row(lower, false);
                if !members.contains(&member) {
                    members.push(member);
                }
            }
        }
        let value = match members.len() {
            0 if root => F5cPositive::Bottom,
            0 => F5cPositive::Variable(ordinal),
            1 => members.pop().expect("one lower member"),
            _ => F5cPositive::Union(members),
        };
        self.active.pop();
        self.active_set.remove(&(ordinal, Polarity::Positive));
        if !root && Self::cacheable_positive(&value) {
            self.positive_cache.insert(ordinal, value.clone());
        }
        value
    }

    fn negative_row(&mut self, ordinal: u32) -> F5cNegative {
        if self.active(ordinal, Polarity::Negative) {
            if self.function_depth > 0 && self.reentry_set.insert(ordinal) {
                self.reentries.push(ordinal);
            }
            self.mark(ordinal, Polarity::Negative);
            return F5cNegative::Variable(ordinal);
        }
        if self.function_depth > 0 && self.active_any(ordinal) && self.reentry_set.insert(ordinal) {
            self.reentries.push(ordinal);
        }
        if let Some(value) = self.negative_cache.get(&ordinal).cloned() {
            self.mark(ordinal, Polarity::Negative);
            return value;
        }
        self.mark(ordinal, Polarity::Negative);
        self.active.push((ordinal, Polarity::Negative));
        self.active_set.insert((ordinal, Polarity::Negative));
        let bounds = self
            .session
            .bounds
            .get(ordinal as usize)
            .cloned()
            .unwrap_or_default();
        let mut members = Vec::new();
        for endpoint in bounds.exact_non_variable_uppers {
            let member = self.negative_endpoint(endpoint);
            if !members.contains(&member) {
                members.push(member);
            }
        }
        if members.is_empty() {
            let mut work = bounds.direct_upper_rows.clone();
            let mut visited = HashSet::new();
            while let Some(upper) = work.pop() {
                if !visited.insert(upper) {
                    continue;
                }
                let member = self.negative_row(upper);
                if !members.contains(&member) {
                    members.push(member);
                }
            }
        }
        let value = match members.len() {
            0 => F5cNegative::Variable(ordinal),
            1 => members.pop().expect("one upper member"),
            _ => F5cNegative::Intersection(members),
        };
        self.active.pop();
        self.active_set.remove(&(ordinal, Polarity::Negative));
        if Self::cacheable_negative(&value) {
            self.negative_cache.insert(ordinal, value.clone());
        }
        value
    }

    fn positive_endpoint(&mut self, endpoint: ValueEndpointKey) -> F5cPositive {
        match endpoint {
            ValueEndpointKey::IntPositive => F5cPositive::Int,
            ValueEndpointKey::BottomPositive => F5cPositive::Bottom,
            ValueEndpointKey::ValueRow(ordinal) => self.positive_row(ordinal, false),
            ValueEndpointKey::PositiveFunction(term) => self.positive_term(term),
            _ => F5cPositive::Bottom,
        }
    }

    fn negative_endpoint(&mut self, endpoint: ValueEndpointKey) -> F5cNegative {
        match endpoint {
            ValueEndpointKey::IntNegative => F5cNegative::Int,
            ValueEndpointKey::TopNegative => F5cNegative::Top,
            ValueEndpointKey::BottomNegative => F5cNegative::Bottom,
            ValueEndpointKey::ValueRow(ordinal) => self.negative_row(ordinal),
            ValueEndpointKey::NegativeFunction(term) => self.negative_term(term),
            _ => F5cNegative::Top,
        }
    }

    fn positive_term(&mut self, term: Term) -> F5cPositive {
        match self
            .session
            .store
            .term_view(term)
            .expect("F5c term remains owned")
        {
            TermView::Leaf(Leaf::IntPositive) => F5cPositive::Int,
            TermView::LiveVariable(view) => {
                debug_assert_eq!(view.polarity(), Polarity::Positive);
                self.positive_row(view.ordinal(), false)
            }
            TermView::PositiveBottom => F5cPositive::Bottom,
            TermView::PositiveFunction {
                argument,
                argument_effect,
                result_effect,
                result,
            } => {
                // F5c closes the pure subset authorized by the current closed
                // effect algebra.  A non-extreme live effect cannot be erased.
                if !matches!(
                    self.session.store.term_view(argument_effect),
                    Ok(TermView::Leaf(Leaf::EmptyEffectNegative))
                ) || !matches!(
                    self.session.store.term_view(result_effect),
                    Ok(TermView::Leaf(Leaf::EffectBottomPositive))
                ) {
                    self.invalid_effects = true;
                }
                self.function_depth += 1;
                let value = F5cPositive::Function {
                    argument: Box::new(self.negative_term(argument)),
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result: Box::new(self.positive_term(result)),
                };
                self.function_depth -= 1;
                value
            }
            TermView::Leaf(_)
            | TermView::Component(_)
            | TermView::NegativeTop
            | TermView::NegativeBottom
            | TermView::NegativeFunction { .. } => F5cPositive::Bottom,
        }
    }

    fn negative_term(&mut self, term: Term) -> F5cNegative {
        match self
            .session
            .store
            .term_view(term)
            .expect("F5c term remains owned")
        {
            TermView::Leaf(Leaf::IntNegative) => F5cNegative::Int,
            TermView::LiveVariable(view) => {
                debug_assert_eq!(view.polarity(), Polarity::Negative);
                self.negative_row(view.ordinal())
            }
            TermView::NegativeTop => F5cNegative::Top,
            TermView::NegativeBottom => F5cNegative::Bottom,
            TermView::NegativeFunction {
                argument,
                argument_effect,
                result_effect,
                result,
            } => {
                if !matches!(
                    self.session.store.term_view(argument_effect),
                    Ok(TermView::Leaf(Leaf::EffectBottomPositive))
                ) || !matches!(
                    self.session.store.term_view(result_effect),
                    Ok(TermView::Leaf(Leaf::EmptyEffectNegative))
                ) {
                    self.invalid_effects = true;
                }
                self.function_depth += 1;
                let value = F5cNegative::Function {
                    argument: Box::new(self.positive_term(argument)),
                    argument_effect: F5cPositiveEffect::Bottom,
                    result_effect: F5cNegativeEffect::Empty,
                    result: Box::new(self.negative_term(result)),
                };
                self.function_depth -= 1;
                value
            }
            TermView::Leaf(_)
            | TermView::Component(_)
            | TermView::PositiveBottom
            | TermView::PositiveFunction { .. } => F5cNegative::Top,
        }
    }

    fn build(mut self, root: u32) -> Result<GeneralizationDraft, SolveAvailabilityError> {
        let predicate = self.positive_row(root, true);
        if self.invalid_effects {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let mut recursive_owners = self.reentries.clone();
        let order_positions = self
            .order
            .iter()
            .enumerate()
            .map(|(position, ordinal)| (*ordinal, position))
            .collect::<HashMap<_, _>>();
        recursive_owners.sort_unstable_by_key(|ordinal| {
            order_positions.get(ordinal).copied().unwrap_or(usize::MAX)
        });
        recursive_owners.dedup();
        let recursive_set = recursive_owners.iter().copied().collect::<HashSet<_>>();
        let mut q = HashMap::new();
        for ordinal in &self.order {
            let eligible = self
                .session
                .value_levels
                .get(*ordinal as usize)
                .is_some_and(|level| *level > 0)
                && !self
                    .session
                    .value_metadata
                    .get(*ordinal as usize)
                    .is_some_and(|metadata| metadata.non_generic);
            if !recursive_set.contains(ordinal)
                && self.positive_seen.contains(ordinal)
                && self.negative_seen.contains(ordinal)
                && eligible
            {
                let next = q.len() as u32;
                q.insert(*ordinal, next);
            }
        }
        let q_count = q.len() as u32;
        let r = recursive_owners
            .iter()
            .enumerate()
            .map(|(index, ordinal)| (*ordinal, q_count + index as u32))
            .collect::<HashMap<_, _>>();
        for ordinal in &self.order {
            let eligible_for_elimination =
                self.session.value_levels.get(*ordinal as usize).is_some()
                    && !self
                        .session
                        .value_metadata
                        .get(*ordinal as usize)
                        .is_some_and(|metadata| metadata.non_generic);
            if !eligible_for_elimination
                && !recursive_set.contains(ordinal)
                && !q.contains_key(ordinal)
            {
                panic!("F5c draft retains an unclosed non-generic live variable");
            }
        }
        fn positive(
            value: F5cPositive,
            q: &HashMap<u32, u32>,
            r: &HashMap<u32, u32>,
        ) -> F5cPositive {
            match value {
                F5cPositive::Variable(ordinal) => r
                    .get(&ordinal)
                    .copied()
                    .map(F5cPositive::Recursive)
                    .or_else(|| q.get(&ordinal).copied().map(F5cPositive::Quantified))
                    .unwrap_or(F5cPositive::Bottom),
                F5cPositive::Function {
                    argument, result, ..
                } => F5cPositive::Function {
                    argument: Box::new(negative(*argument, q, r)),
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result: Box::new(positive(*result, q, r)),
                },
                F5cPositive::Union(values) => F5cPositive::Union(
                    values
                        .into_iter()
                        .map(|value| positive(value, q, r))
                        .collect(),
                ),
                other => other,
            }
        }
        fn negative(
            value: F5cNegative,
            q: &HashMap<u32, u32>,
            r: &HashMap<u32, u32>,
        ) -> F5cNegative {
            match value {
                F5cNegative::Variable(ordinal) => r
                    .get(&ordinal)
                    .copied()
                    .map(F5cNegative::Recursive)
                    .or_else(|| q.get(&ordinal).copied().map(F5cNegative::Quantified))
                    .unwrap_or(F5cNegative::Top),
                F5cNegative::Function {
                    argument, result, ..
                } => F5cNegative::Function {
                    argument: Box::new(positive(*argument, q, r)),
                    argument_effect: F5cPositiveEffect::Bottom,
                    result_effect: F5cNegativeEffect::Empty,
                    result: Box::new(negative(*result, q, r)),
                },
                F5cNegative::Intersection(values) => F5cNegative::Intersection(
                    values
                        .into_iter()
                        .map(|value| negative(value, q, r))
                        .collect(),
                ),
                other => other,
            }
        }
        let predicate = positive(predicate, &q, &r);
        let recursive_bounds = recursive_owners
            .iter()
            .filter_map(|ordinal| {
                r.get(ordinal).copied().map(|binder| F5cRecursiveBound {
                    ordinal: binder,
                    lower: if self
                        .session
                        .bounds
                        .get(*ordinal as usize)
                        .is_some_and(|bounds| {
                            bounds.exact_non_variable_lowers.is_empty()
                                && bounds.direct_lower_rows.is_empty()
                        }) {
                        F5cPositive::Bottom
                    } else {
                        positive(self.positive_row(*ordinal, false), &q, &r)
                    },
                    upper: if self
                        .session
                        .bounds
                        .get(*ordinal as usize)
                        .is_some_and(|bounds| {
                            bounds.exact_non_variable_uppers.is_empty()
                                && bounds.direct_upper_rows.is_empty()
                        }) {
                        F5cNegative::Top
                    } else {
                        negative(self.negative_row(*ordinal), &q, &r)
                    },
                })
            })
            .collect();
        Ok(GeneralizationDraft {
            quantifier_count: q_count,
            recursive_bounds,
            predicate,
        })
    }
}

struct VerifiedSchemeDefinition<'a> {
    record: &'a CollectedDefinition,
    position: usize,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum F4SchemeBody {
    Bottom,
    Int,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RoutedUseKind {
    Internal,
    IncomingInt,
    IncomingBottomTrivial,
    IncomingStructured,
}

#[allow(
    dead_code,
    reason = "F4 retains exact private route provenance without a public query"
)]
#[derive(Debug)]
struct RoutedUseProvenance {
    use_id: DefinitionUseId,
    fact: Option<FactId>,
    kind: RoutedUseKind,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ObservedIncomingKind {
    Int,
    BottomTrivial,
    Structured,
}

#[cfg(test)]
#[derive(Clone, Debug, Eq, PartialEq)]
enum ExecutionEvent {
    InternalUse(DefinitionUseId),
    Drafted(DefinitionOrderId),
    DraftsVisible(SccComponentId, usize),
    Installed(DefinitionRootId),
    IncomingUse(DefinitionUseId, ObservedIncomingKind),
}

#[cfg(test)]
#[derive(Debug)]
struct OrderingObserver {
    capacity: usize,
    events: Vec<ExecutionEvent>,
    omitted: usize,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SummaryObservation {
    ordinary_initial_value_pair_probes: usize,
    synthetic_seed_value_pair_probes: usize,
    reads: usize,
    false_to_true_transitions: usize,
    frontier_pushes: usize,
    frontier_pops: usize,
    frontier_maximum_live: usize,
    frontier_capacity: usize,
    frontier_capacity_growths: usize,
    frontier_retained_bytes: usize,
    frontier_peak_bytes: usize,
    direct_edges: usize,
    exact_lower_memberships: usize,
    exact_upper_memberships: usize,
    transmission_attempts: usize,
    same_row_atom_intersections: usize,
    semantic_arena_retained_bytes: usize,
    semantic_arena_peak_bytes: usize,
    inference_session_retained_bytes: usize,
    inference_session_peak_bytes: usize,
    resource_boundary_samples: usize,
    resource_boundary_coverage: usize,
    independent_queue_retained_bytes: usize,
    independent_finish_output_retained_bytes: usize,
    independent_semantic_arena_retained_bytes: usize,
    independent_inference_session_retained_bytes: usize,
    independent_semantic_arena_peak_bytes: usize,
    independent_inference_session_peak_bytes: usize,
}

#[allow(
    dead_code,
    reason = "the named boundary ledger is cfg(test); production keeps the same sampling call sites"
)]
#[derive(Clone, Copy, Debug)]
enum ResourceBoundary {
    InitialReservation,
    InitialAdmission,
    CrossKind,
    InternalRoute,
    DraftScratchClear,
    DraftMember,
    SchemeInstall,
    IncomingRoute,
    StoreAccounting,
    FinishOutputWithStaging,
    FinishOutput,
}

#[cfg(test)]
#[derive(Debug, Default)]
struct IndependentResourceLedger {
    coverage: u16,
    samples: usize,
    queue_retained_bytes: usize,
    semantic_arena_retained_bytes: usize,
    inference_session_retained_bytes: usize,
    finish_output_retained_bytes: usize,
    semantic_arena_peak_bytes: usize,
    inference_session_peak_bytes: usize,
}

#[cfg(test)]
#[derive(Debug, Default)]
struct IndependentNestedCapacityLedger {
    value_direct_lower: usize,
    value_direct_upper: usize,
    value_exact_lower: usize,
    value_exact_upper: usize,
    effect_direct_lower: usize,
    effect_direct_upper: usize,
    effect_exact_lower: usize,
    effect_exact_upper: usize,
    diagnostic_edges: usize,
}

#[cfg(test)]
impl IndependentNestedCapacityLedger {
    fn total_bound_bytes(&self) -> usize {
        checked_usize_sum(
            [
                self.value_direct_lower,
                self.value_direct_upper,
                self.value_exact_lower,
                self.value_exact_upper,
                self.effect_direct_lower,
                self.effect_direct_upper,
                self.effect_exact_lower,
                self.effect_exact_upper,
            ],
            "independent nested bound lanes",
        )
    }
}

#[cfg(test)]
impl IndependentResourceLedger {
    fn record(
        &mut self,
        boundary: ResourceBoundary,
        store: &ConstraintStore,
        errors: &Vec<SolverError>,
        reported_errors: &HashSet<(ConstraintOccurrenceId, SolverErrorKind)>,
        cross_kind_components: &HashSet<ComponentId>,
        live_components: &Vec<LiveComponentEndpoint>,
        bounds: &Vec<VariableBounds>,
        effect_bounds: &Vec<EffectBounds>,
        value_levels: &Vec<u32>,
        effect_levels: &Vec<u32>,
        value_metadata: &Vec<LiveVariableMetadata>,
        effect_metadata: &Vec<LiveVariableMetadata>,
        extrusion_stack: &Vec<ExtrusionEndpoint>,
        extrusion_value_marks: &Vec<u32>,
        extrusion_effect_marks: &Vec<u32>,
        occurrence_exact_bounds: &Vec<OccurrenceExactBounds>,
        typed_pairs: &HashMap<TypedPairKey, TypedPairMemo>,
        typed_worklist: &VecDeque<TypedWorkItem>,
        diagnostic_delta: &Vec<CanonicalValuePairKey>,
        diagnostic_delta_indices: &HashMap<CanonicalValuePairKey, usize>,
        diagnostic_reverse_offsets: &Vec<usize>,
        diagnostic_reverse_edges: &Vec<DiagnosticReverseEdge>,
        diagnostic_reverse_cursors: &Vec<usize>,
        diagnostic_dfs_stack: &Vec<(usize, usize)>,
        diagnostic_finish_order: &Vec<usize>,
        diagnostic_scc_indices: &Vec<usize>,
        diagnostic_scc_nodes: &Vec<usize>,
        diagnostic_scc_offsets: &Vec<usize>,
        diagnostic_scc_pending_children: &Vec<usize>,
        diagnostic_scc_worklist: &VecDeque<usize>,
        diagnostic_bucket_heads: &Vec<Option<usize>>,
        diagnostic_bucket_tails: &Vec<Option<usize>>,
        diagnostic_bucket_candidates: &Vec<DiagnosticBucketCandidate>,
        diagnostic_node_witnesses: &Vec<Option<DiagnosticWitness>>,
        routed_uses: &Vec<RoutedUseProvenance>,
        routed_use_positions: &HashSet<DefinitionUseId>,
        schemes: &Vec<Option<ClosedValueScheme>>,
        drafts: &Vec<DraftScheme>,
        closed_type_retained_bytes: usize,
        f2_batch_retained_bytes: usize,
        component_term_positions_capacity: usize,
        finish_output_retained_bytes: usize,
        nested_capacities: &IndependentNestedCapacityLedger,
    ) {
        self.coverage |= 1 << (boundary as u8);
        self.samples += 1;
        let queue_bytes = checked_capacity_bytes::<TypedWorkItem>(
            typed_worklist.capacity(),
            "F5b independent typed frontier queue",
        );
        let semantic = checked_usize_sum(
            [
                checked_usize_sum(
                    [
                        checked_capacity_bytes::<LiveComponentEndpoint>(
                            live_components.capacity(),
                            "F5b independent live translation",
                        ),
                        checked_capacity_bytes::<VariableBounds>(
                            bounds.capacity(),
                            "F5b independent value rows",
                        ),
                        checked_capacity_bytes::<EffectBounds>(
                            effect_bounds.capacity(),
                            "F5b independent effect rows",
                        ),
                        checked_capacity_bytes::<u32>(
                            value_levels.capacity(),
                            "F5b independent value levels",
                        ),
                        checked_capacity_bytes::<u32>(
                            effect_levels.capacity(),
                            "F5b independent effect levels",
                        ),
                        checked_capacity_bytes::<LiveVariableMetadata>(
                            value_metadata.capacity(),
                            "F5b independent value metadata",
                        ),
                        checked_capacity_bytes::<LiveVariableMetadata>(
                            effect_metadata.capacity(),
                            "F5b independent effect metadata",
                        ),
                        checked_capacity_bytes::<ExtrusionEndpoint>(
                            extrusion_stack.capacity(),
                            "F5b independent extrusion stack",
                        ),
                        checked_capacity_bytes::<u32>(
                            extrusion_value_marks.capacity(),
                            "F5b independent extrusion value marks",
                        ),
                        checked_capacity_bytes::<u32>(
                            extrusion_effect_marks.capacity(),
                            "F5b independent extrusion effect marks",
                        ),
                        nested_capacities.total_bound_bytes(),
                    ],
                    "F5b independent bounds",
                ),
                checked_usize_sum(
                    [
                        checked_capacity_bytes::<(TypedPairKey, TypedPairMemo)>(
                            typed_pairs.capacity(),
                            "F5b independent typed pair memo",
                        ),
                        nested_capacities.diagnostic_edges,
                    ],
                    "F5b independent typed pair memo including diagnostic edges",
                ),
                queue_bytes,
                checked_usize_sum(
                    [
                        checked_capacity_bytes::<CanonicalValuePairKey>(
                            diagnostic_delta.capacity(),
                            "F5b independent diagnostic delta",
                        ),
                        checked_capacity_bytes::<(CanonicalValuePairKey, usize)>(
                            diagnostic_delta_indices.capacity(),
                            "F5b independent diagnostic delta index",
                        ),
                        checked_capacity_bytes::<usize>(
                            diagnostic_reverse_offsets.capacity(),
                            "F5b independent reverse offsets",
                        ),
                        checked_capacity_bytes::<DiagnosticReverseEdge>(
                            diagnostic_reverse_edges.capacity(),
                            "F5b independent reverse edges",
                        ),
                        checked_capacity_bytes::<usize>(
                            diagnostic_reverse_cursors.capacity(),
                            "F5b independent reverse cursors",
                        ),
                        checked_capacity_bytes::<(usize, usize)>(
                            diagnostic_dfs_stack.capacity(),
                            "F5b independent DFS",
                        ),
                        checked_capacity_bytes::<usize>(
                            diagnostic_finish_order.capacity(),
                            "F5b independent finish order",
                        ),
                        checked_capacity_bytes::<usize>(
                            diagnostic_scc_indices.capacity(),
                            "F5b independent SCC indices",
                        ),
                        checked_capacity_bytes::<usize>(
                            diagnostic_scc_nodes.capacity(),
                            "F5b independent SCC nodes",
                        ),
                        checked_capacity_bytes::<usize>(
                            diagnostic_scc_offsets.capacity(),
                            "F5b independent SCC offsets",
                        ),
                        checked_capacity_bytes::<usize>(
                            diagnostic_scc_pending_children.capacity(),
                            "F5b independent SCC pending",
                        ),
                        checked_capacity_bytes::<usize>(
                            diagnostic_scc_worklist.capacity(),
                            "F5b independent SCC worklist",
                        ),
                        checked_capacity_bytes::<Option<usize>>(
                            diagnostic_bucket_heads.capacity(),
                            "F5b independent bucket heads",
                        ),
                        checked_capacity_bytes::<Option<usize>>(
                            diagnostic_bucket_tails.capacity(),
                            "F5b independent bucket tails",
                        ),
                        checked_capacity_bytes::<DiagnosticBucketCandidate>(
                            diagnostic_bucket_candidates.capacity(),
                            "F5b independent bucket candidates",
                        ),
                        checked_capacity_bytes::<Option<DiagnosticWitness>>(
                            diagnostic_node_witnesses.capacity(),
                            "F5b independent node witnesses",
                        ),
                    ],
                    "F5b independent diagnostic scratch",
                ),
                checked_capacity_bytes::<Option<ClosedValueScheme>>(
                    schemes.capacity(),
                    "F4 independent scheme table",
                ),
                checked_capacity_bytes::<RoutedUseProvenance>(
                    routed_uses.capacity(),
                    "F4 independent routed-use provenance",
                ),
                checked_capacity_bytes::<DraftScheme>(
                    drafts.capacity(),
                    "F4 independent draft scratch",
                ),
                closed_type_retained_bytes,
                checked_capacity_bytes::<OccurrenceExactBounds>(
                    occurrence_exact_bounds.capacity(),
                    "F4 independent occurrence bounds",
                ),
                store.independent_inference_term_retained_bytes(),
            ],
            "F4 independent semantic ledger",
        );
        let component_term_position_bytes = checked_capacity_bytes::<(Term, usize)>(
            component_term_positions_capacity,
            "F5b independent collected component-term recipe index",
        );
        let f2_batch_without_component_term_positions = f2_batch_retained_bytes
            .checked_sub(component_term_position_bytes)
            .expect("F5b component-term recipe index is included once in the F2 batch total");
        let session = checked_usize_sum(
            [
                semantic,
                checked_capacity_bytes::<SemanticFact>(
                    store.facts.capacity(),
                    "F4 independent facts",
                ),
                checked_capacity_bytes::<(FactKey, FactId)>(
                    store.canonical.capacity(),
                    "F4 independent canonical map",
                ),
                checked_capacity_bytes::<ProvenanceEdge>(
                    store.provenance.capacity(),
                    "F4 independent provenance",
                ),
                checked_capacity_bytes::<u64>(
                    store.consumed_receipts.capacity(),
                    "F4 independent consumed receipts",
                ),
                checked_capacity_bytes::<SolverError>(errors.capacity(), "F4 independent errors"),
                checked_capacity_bytes::<(ConstraintOccurrenceId, SolverErrorKind)>(
                    reported_errors.capacity(),
                    "F5b independent reported-error index",
                ),
                checked_capacity_bytes::<ComponentId>(
                    cross_kind_components.capacity(),
                    "F4 independent cross-kind components",
                ),
                checked_capacity_bytes::<DefinitionUseId>(
                    routed_use_positions.capacity(),
                    "F4 independent routed-use index",
                ),
                f2_batch_without_component_term_positions,
                component_term_position_bytes,
            ],
            "F4 independent session ledger",
        );
        let full_session = session
            .checked_add(finish_output_retained_bytes)
            .expect("independent finish-output session ledger fits usize");
        self.queue_retained_bytes = queue_bytes;
        self.semantic_arena_retained_bytes = semantic;
        self.inference_session_retained_bytes = session;
        self.finish_output_retained_bytes = finish_output_retained_bytes;
        self.semantic_arena_peak_bytes = self.semantic_arena_peak_bytes.max(semantic);
        self.inference_session_peak_bytes = self.inference_session_peak_bytes.max(full_session);
    }
}

#[cfg(test)]
impl OrderingObserver {
    fn new(capacity: usize) -> Self {
        Self {
            capacity,
            events: Vec::with_capacity(capacity),
            omitted: 0,
        }
    }

    fn has_capacity(&self) -> bool {
        self.events.len() < self.capacity
    }

    fn omit(&mut self) {
        self.omitted += 1;
    }

    fn record(&mut self, event: impl FnOnce() -> ExecutionEvent) {
        if !self.has_capacity() {
            self.omit();
            return;
        }
        self.events.push(event());
    }
}

/// A total artifact-bound frozen solve result. Local relation errors do not
/// prevent later independent components from solving.
#[derive(Debug)]
pub struct SolvedModule {
    hir: Arc<HirModule>,
    projection_order: Vec<HirOccurrenceId>,
    projections: HashMap<HirOccurrenceId, SolvedProjection>,
    root_scheme_positions: HashMap<DefinitionRootId, usize>,
    root_scheme_identity_payload_bytes: Vec<usize>,
    schemes: Vec<Option<ClosedValueScheme>>,
    closed_types: ClosedTypeArena,
    #[allow(
        dead_code,
        reason = "F4 retains exact route provenance for future explanation without adding a public lifecycle query"
    )]
    routed_uses: Vec<RoutedUseProvenance>,
    errors: Vec<SolverError>,
    store: ConstraintStore,
    counters: ProductionCounters,
    solved_root_query_probes: AtomicUsize,
    scheme_root_query_probes: AtomicUsize,
    scheme_root_query_identity_hash_byte_incidences: AtomicUsize,
    scheme_root_query_logical_successful_equality_byte_incidences: AtomicUsize,
    #[cfg(test)]
    resource_boundary_samples: usize,
    #[cfg(test)]
    resource_ledger: IndependentResourceLedger,
}

/// Private owner for one concrete inference attempt.
///
/// F3b preserves the frozen F0--F2 admission and projection behavior while
/// placing its mutable state behind the future SCC-closure boundary.
struct InferenceSession {
    batch: ConstraintBatch,
    store: ConstraintStore,
    errors: Vec<SolverError>,
    reported_errors: HashSet<(ConstraintOccurrenceId, SolverErrorKind)>,
    cross_kind_components: HashSet<ComponentId>,
    /// One injective startup translation for immutable collected component
    /// recipes.  These dense entries are live-session identity, not source
    /// component/root/occurrence identity.
    live_components: Vec<LiveComponentEndpoint>,
    bounds: Vec<VariableBounds>,
    effect_bounds: Vec<EffectBounds>,
    value_levels: Vec<u32>,
    effect_levels: Vec<u32>,
    value_metadata: Vec<LiveVariableMetadata>,
    effect_metadata: Vec<LiveVariableMetadata>,
    extrusion_stack: Vec<ExtrusionEndpoint>,
    extrusion_value_marks: Vec<u32>,
    extrusion_effect_marks: Vec<u32>,
    extrusion_generation: u32,
    bound_payload_bytes: usize,
    /// Retained only as an F4 compatibility/resource field.  It is always
    /// empty; projections are derived from the live rows below.
    occurrence_exact_bounds: Vec<OccurrenceExactBounds>,
    typed_pairs: HashMap<TypedPairKey, TypedPairMemo>,
    /// Heap capacity owned by `TypedPairMemo::Value.children`. The map slot
    /// stores only each Vec header, so this tracks the nested diagnostic-edge
    /// lane without turning O(1) resource samples into memo scans.
    typed_pair_payload_bytes: usize,
    typed_worklist: VecDeque<TypedWorkItem>,
    /// The current synchronous call's newly admitted value pairs.  Completion
    /// reads old Complete children but never reopens or revisits them.
    diagnostic_delta: Vec<CanonicalValuePairKey>,
    diagnostic_delta_indices: HashMap<CanonicalValuePairKey, usize>,
    /// Reused only within one synchronous diagnostic completion.  Pair memo
    /// entries retain outgoing edges; reverse edges and SCC state do not leak
    /// beyond the fallible availability boundary of this session scratch.
    diagnostic_reverse_offsets: Vec<usize>,
    diagnostic_reverse_edges: Vec<DiagnosticReverseEdge>,
    diagnostic_reverse_cursors: Vec<usize>,
    diagnostic_dfs_stack: Vec<(usize, usize)>,
    diagnostic_finish_order: Vec<usize>,
    diagnostic_scc_indices: Vec<usize>,
    diagnostic_scc_nodes: Vec<usize>,
    diagnostic_scc_offsets: Vec<usize>,
    diagnostic_scc_pending_children: Vec<usize>,
    diagnostic_scc_worklist: VecDeque<usize>,
    /// Per-SCC canonical-witness propagation is a checked, intrusive FIFO
    /// bucket table.  The key is §40's `(distance - d0, kind, first field)`;
    /// no route, predecessor, heap, or improvement queue survives the call.
    diagnostic_bucket_heads: Vec<Option<usize>>,
    diagnostic_bucket_tails: Vec<Option<usize>>,
    diagnostic_bucket_candidates: Vec<DiagnosticBucketCandidate>,
    diagnostic_node_witnesses: Vec<Option<DiagnosticWitness>>,
    #[cfg(test)]
    diagnostic_settle_visits: usize,
    #[cfg(test)]
    diagnostic_internal_reverse_edge_visits: usize,
    #[cfg(test)]
    diagnostic_scc_member_seed_scans: usize,
    #[cfg(test)]
    typed_pair_worklist_pushes: usize,
    #[cfg(test)]
    typed_pair_worklist_pops: usize,
    #[cfg(test)]
    typed_pair_worklist_maximum_live: usize,
    #[cfg(test)]
    typed_pair_worklist_capacity_growths: usize,
    #[cfg(test)]
    typed_pair_worklist_peak_bytes: usize,
    #[cfg(test)]
    typed_direct_edges: usize,
    #[cfg(test)]
    typed_exact_lower_memberships: usize,
    #[cfg(test)]
    typed_exact_upper_memberships: usize,
    #[cfg(test)]
    typed_transmission_attempts: usize,
    #[cfg(test)]
    typed_same_row_atom_intersections: usize,
    routed_uses: Vec<RoutedUseProvenance>,
    routed_use_positions: HashSet<DefinitionUseId>,
    schemes: Vec<Option<ClosedValueScheme>>,
    finalization: Option<ClosedTypeFinalizationSession>,
    current_closed_retained_bytes: usize,
    drafts: Vec<DraftScheme>,
    execution_counters: ProductionCounters,
    #[cfg(test)]
    summary_reads: usize,
    #[cfg(test)]
    summary_false_to_true_transitions: usize,
    #[cfg(test)]
    initial_value_pair_probes: usize,
    #[cfg(test)]
    injected_finalization_failure_after: Option<usize>,
    #[cfg(test)]
    successful_finalizations: usize,
    #[cfg(test)]
    ordering_observer: Option<OrderingObserver>,
    #[cfg(test)]
    resource_boundary_samples: usize,
    #[cfg(test)]
    resource_ledger: IndependentResourceLedger,
    #[cfg(test)]
    independent_nested_capacities: IndependentNestedCapacityLedger,
}
impl InferenceSession {
    #[cfg(test)]
    fn new(batch: ConstraintBatch) -> Self {
        Self::try_new(batch)
            .expect("test/internal session construction has available closed identity")
    }

    fn try_new(batch: ConstraintBatch) -> Result<Self, SolveAvailabilityError> {
        let value_component_count = batch
            .components
            .iter()
            .filter(|component| component.kind() == ComponentKind::Value)
            .count();
        let effect_component_count = batch
            .components
            .iter()
            .filter(|component| component.kind() == ComponentKind::Effect)
            .count();
        let component_count = batch.components.len();
        let definition_count = batch.definitions.len();
        let fact_capacity = batch
            .occurrences
            .len()
            .checked_add(batch.definition_uses.len())
            .expect("F4 fact capacity");
        let draft_capacity = batch.counters.scc_maximum_component_size;
        let routed_capacity = batch.definition_uses.len();
        let mut session = Self {
            // The solve branch receives the collected lineage directly.  The
            // retained batch is only F2 plan/recipe state; it never owns a
            // second mutable term arena or rebuilds a handle from HIR.
            store: ConstraintStore::with_capacity(
                batch.hir.clone(),
                batch.term_lineage(),
                fact_capacity,
            ),
            batch,
            errors: Vec::new(),
            reported_errors: HashSet::new(),
            cross_kind_components: HashSet::new(),
            live_components: Vec::new(),
            bounds: Vec::new(),
            effect_bounds: Vec::new(),
            value_levels: Vec::new(),
            effect_levels: Vec::new(),
            value_metadata: Vec::new(),
            effect_metadata: Vec::new(),
            extrusion_stack: Vec::new(),
            extrusion_value_marks: Vec::new(),
            extrusion_effect_marks: Vec::new(),
            extrusion_generation: 0,
            bound_payload_bytes: 0,
            occurrence_exact_bounds: Vec::new(),
            typed_pairs: HashMap::new(),
            typed_pair_payload_bytes: 0,
            typed_worklist: VecDeque::new(),
            diagnostic_delta: Vec::new(),
            diagnostic_delta_indices: HashMap::new(),
            diagnostic_reverse_offsets: Vec::new(),
            diagnostic_reverse_edges: Vec::new(),
            diagnostic_reverse_cursors: Vec::new(),
            diagnostic_dfs_stack: Vec::new(),
            diagnostic_finish_order: Vec::new(),
            diagnostic_scc_indices: Vec::new(),
            diagnostic_scc_nodes: Vec::new(),
            diagnostic_scc_offsets: Vec::new(),
            diagnostic_scc_pending_children: Vec::new(),
            diagnostic_scc_worklist: VecDeque::new(),
            diagnostic_bucket_heads: Vec::new(),
            diagnostic_bucket_tails: Vec::new(),
            diagnostic_bucket_candidates: Vec::new(),
            diagnostic_node_witnesses: Vec::new(),
            #[cfg(test)]
            diagnostic_settle_visits: 0,
            #[cfg(test)]
            diagnostic_internal_reverse_edge_visits: 0,
            #[cfg(test)]
            diagnostic_scc_member_seed_scans: 0,
            #[cfg(test)]
            typed_pair_worklist_pushes: 0,
            #[cfg(test)]
            typed_pair_worklist_pops: 0,
            #[cfg(test)]
            typed_pair_worklist_maximum_live: 0,
            #[cfg(test)]
            typed_pair_worklist_capacity_growths: 0,
            #[cfg(test)]
            typed_pair_worklist_peak_bytes: 0,
            #[cfg(test)]
            typed_direct_edges: 0,
            #[cfg(test)]
            typed_exact_lower_memberships: 0,
            #[cfg(test)]
            typed_exact_upper_memberships: 0,
            #[cfg(test)]
            typed_transmission_attempts: 0,
            #[cfg(test)]
            typed_same_row_atom_intersections: 0,
            routed_uses: Vec::new(),
            routed_use_positions: HashSet::new(),
            schemes: Vec::new(),
            finalization: Some(
                ClosedTypeFinalizationSession::try_new().map_err(Self::map_finalization_error)?,
            ),
            current_closed_retained_bytes: 0,
            drafts: Vec::new(),
            execution_counters: ProductionCounters::default(),
            #[cfg(test)]
            summary_reads: 0,
            #[cfg(test)]
            summary_false_to_true_transitions: 0,
            #[cfg(test)]
            initial_value_pair_probes: 0,
            #[cfg(test)]
            injected_finalization_failure_after: None,
            #[cfg(test)]
            successful_finalizations: 0,
            #[cfg(test)]
            ordering_observer: None,
            #[cfg(test)]
            resource_boundary_samples: 0,
            #[cfg(test)]
            resource_ledger: IndependentResourceLedger::default(),
            #[cfg(test)]
            independent_nested_capacities: IndependentNestedCapacityLedger::default(),
        };
        // Every F5b live table and diagnostic workspace acquires capacity
        // before startup can publish a live identity or mutate a row.
        let extrusion_capacity = value_component_count
            .checked_add(effect_component_count)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        macro_rules! reserve_startup {
            ($field:ident, $additional:expr, $lane:ident) => {
                reserve_f5b(&mut session.$field, $additional, F5bCapacityLane::$lane)
                    .map_err(SolveAvailabilityError::from)?;
            };
        }
        reserve_startup!(live_components, component_count, LiveComponents);
        reserve_startup!(bounds, value_component_count, ValueBounds);
        reserve_startup!(effect_bounds, effect_component_count, EffectBounds);
        reserve_startup!(value_levels, value_component_count, ValueLevels);
        reserve_startup!(effect_levels, effect_component_count, EffectLevels);
        reserve_startup!(value_metadata, value_component_count, ValueMetadata);
        reserve_startup!(effect_metadata, effect_component_count, EffectMetadata);
        reserve_startup!(extrusion_stack, extrusion_capacity, ExtrusionStack);
        reserve_startup!(
            extrusion_value_marks,
            value_component_count,
            ExtrusionValueMarks
        );
        reserve_startup!(
            extrusion_effect_marks,
            effect_component_count,
            ExtrusionEffectMarks
        );
        reserve_startup!(typed_pairs, fact_capacity, TypedPairs);
        reserve_startup!(typed_worklist, fact_capacity, TypedWorklist);
        #[cfg(test)]
        {
            session.typed_pair_worklist_peak_bytes = checked_capacity_bytes::<TypedWorkItem>(
                session.typed_worklist.capacity(),
                "initial typed worklist capacity",
            );
        }
        reserve_startup!(diagnostic_delta, fact_capacity, DiagnosticDelta);
        reserve_startup!(
            diagnostic_delta_indices,
            fact_capacity,
            DiagnosticDeltaIndices
        );
        reserve_startup!(
            diagnostic_reverse_offsets,
            fact_capacity,
            DiagnosticReverseOffsets
        );
        reserve_startup!(
            diagnostic_reverse_edges,
            fact_capacity,
            DiagnosticReverseEdges
        );
        reserve_startup!(
            diagnostic_reverse_cursors,
            fact_capacity,
            DiagnosticReverseCursors
        );
        reserve_startup!(diagnostic_dfs_stack, fact_capacity, DiagnosticDfsStack);
        reserve_startup!(
            diagnostic_finish_order,
            fact_capacity,
            DiagnosticFinishOrder
        );
        reserve_startup!(diagnostic_scc_indices, fact_capacity, DiagnosticSccIndices);
        reserve_startup!(diagnostic_scc_nodes, fact_capacity, DiagnosticSccNodes);
        reserve_startup!(diagnostic_scc_offsets, fact_capacity, DiagnosticSccOffsets);
        reserve_startup!(
            diagnostic_scc_pending_children,
            fact_capacity,
            DiagnosticSccPendingChildren
        );
        reserve_startup!(
            diagnostic_scc_worklist,
            fact_capacity,
            DiagnosticSccWorklist
        );
        reserve_startup!(
            diagnostic_bucket_heads,
            fact_capacity,
            DiagnosticBucketHeads
        );
        reserve_startup!(
            diagnostic_bucket_tails,
            fact_capacity,
            DiagnosticBucketTails
        );
        reserve_startup!(
            diagnostic_bucket_candidates,
            fact_capacity,
            DiagnosticBucketCandidates
        );
        reserve_startup!(
            diagnostic_node_witnesses,
            fact_capacity,
            DiagnosticNodeWitnesses
        );
        reserve_startup!(errors, fact_capacity, Errors);
        reserve_startup!(reported_errors, fact_capacity, ReportedErrors);
        reserve_startup!(
            cross_kind_components,
            value_component_count,
            CrossKindComponents
        );
        reserve_startup!(routed_uses, routed_capacity, RoutedUses);
        reserve_startup!(routed_use_positions, routed_capacity, RoutedUsePositions);
        reserve_startup!(schemes, definition_count, Schemes);
        reserve_startup!(drafts, draft_capacity, Drafts);
        session
            .extrusion_value_marks
            .resize(value_component_count, 0);
        session
            .extrusion_effect_marks
            .resize(effect_component_count, 0);
        session.schemes.resize(definition_count, None);
        // Collection IDs are frozen recipe positions only.  Every component,
        // including effect components, receives exactly one checked dense live
        // ordinal at level one before any fact admission.
        let mut next_value = 0u32;
        let mut next_effect = 0u32;
        for component in &session.batch.components {
            let endpoint = match component.kind() {
                ComponentKind::Value => {
                    let ordinal = next_value;
                    next_value = next_value
                        .checked_add(1)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    session.bounds.push(VariableBounds::default());
                    session.value_levels.push(1);
                    session.value_metadata.push(LiveVariableMetadata {
                        origin: LiveVariableOrigin::Collected,
                        non_generic: false,
                    });
                    LiveComponentEndpoint {
                        kind: ComponentKind::Value,
                        ordinal,
                    }
                }
                ComponentKind::Effect => {
                    let ordinal = next_effect;
                    next_effect = next_effect
                        .checked_add(1)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    session.effect_bounds.push(EffectBounds::default());
                    session.effect_levels.push(1);
                    session.effect_metadata.push(LiveVariableMetadata {
                        origin: LiveVariableOrigin::Collected,
                        non_generic: false,
                    });
                    LiveComponentEndpoint {
                        kind: ComponentKind::Effect,
                        ordinal,
                    }
                }
            };
            session.live_components.push(endpoint);
        }
        // Initial reservations coexist before any fact admission and are a
        // real resource boundary, not a final retained-byte alias.
        session.sample_f4_resources(ResourceBoundary::InitialReservation);
        Ok(session)
    }

    fn map_finalization_error(error: ClosedTypeFinalizeError) -> SolveAvailabilityError {
        match error {
            ClosedTypeFinalizeError::IdentityExhausted => SolveAvailabilityError::IdentityExhausted,
            ClosedTypeFinalizeError::InvalidDraft => {
                panic!("F4 finalization draft is internally validated before publication")
            }
        }
    }

    #[allow(
        dead_code,
        reason = "F5b private Function witnesses allocate incoming live variables"
    )]
    fn fresh_value_at_level(&mut self, level: u32) -> Result<u32, SolveAvailabilityError> {
        let ordinal = u32::try_from(self.bounds.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        reserve_f5b(&mut self.bounds, 1, F5bCapacityLane::ValueBounds)?;
        reserve_f5b(&mut self.value_levels, 1, F5bCapacityLane::ValueLevels)?;
        reserve_f5b(&mut self.value_metadata, 1, F5bCapacityLane::ValueMetadata)?;
        reserve_f5b(
            &mut self.extrusion_value_marks,
            1,
            F5bCapacityLane::ExtrusionValueMarks,
        )?;
        self.bounds.push(VariableBounds::default());
        self.value_levels.push(level);
        self.value_metadata.push(LiveVariableMetadata {
            origin: LiveVariableOrigin::Fresh,
            non_generic: false,
        });
        self.extrusion_value_marks.push(0);
        Ok(ordinal)
    }

    #[allow(
        dead_code,
        reason = "F5b private Function witnesses allocate incoming live variables"
    )]
    fn fresh_effect_at_level(&mut self, level: u32) -> Result<u32, SolveAvailabilityError> {
        let ordinal = u32::try_from(self.effect_bounds.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        reserve_f5b(&mut self.effect_bounds, 1, F5bCapacityLane::EffectBounds)?;
        reserve_f5b(&mut self.effect_levels, 1, F5bCapacityLane::EffectLevels)?;
        reserve_f5b(
            &mut self.effect_metadata,
            1,
            F5bCapacityLane::EffectMetadata,
        )?;
        reserve_f5b(
            &mut self.extrusion_effect_marks,
            1,
            F5bCapacityLane::ExtrusionEffectMarks,
        )?;
        self.effect_bounds.push(EffectBounds::default());
        self.effect_levels.push(level);
        self.effect_metadata.push(LiveVariableMetadata {
            origin: LiveVariableOrigin::Fresh,
            non_generic: false,
        });
        self.extrusion_effect_marks.push(0);
        Ok(ordinal)
    }

    #[allow(dead_code, reason = "nested live allocation is deferred to F5c/F5d")]
    fn child_level(level: u32) -> Result<u32, SolveAvailabilityError> {
        level
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    #[allow(
        dead_code,
        reason = "F5b private Function witnesses construct opaque live terms"
    )]
    fn live_value_term(
        &mut self,
        polarity: Polarity,
        ordinal: u32,
    ) -> Result<Term, SolveAvailabilityError> {
        self.store
            .terms
            .live_variable(ComponentKind::Value, polarity, ordinal)
            .map_err(SolveAvailabilityError::from)
    }

    #[allow(
        dead_code,
        reason = "F5b private Function witnesses construct opaque live terms"
    )]
    fn live_effect_term(
        &mut self,
        polarity: Polarity,
        ordinal: u32,
    ) -> Result<Term, SolveAvailabilityError> {
        self.store
            .terms
            .live_variable(ComponentKind::Effect, polarity, ordinal)
            .map_err(SolveAvailabilityError::from)
    }

    fn positive_bottom_term(&mut self) -> Result<Term, SolveAvailabilityError> {
        self.store
            .terms
            .positive_bottom()
            .map_err(SolveAvailabilityError::from)
    }

    fn negative_top_term(&mut self) -> Result<Term, SolveAvailabilityError> {
        self.store
            .terms
            .negative_top()
            .map_err(SolveAvailabilityError::from)
    }

    fn negative_bottom_term(&mut self) -> Result<Term, SolveAvailabilityError> {
        self.store
            .terms
            .negative_bottom()
            .map_err(SolveAvailabilityError::from)
    }

    #[allow(
        dead_code,
        reason = "F5b private Function witnesses construct opaque live terms"
    )]
    fn positive_function_term(
        &mut self,
        argument: Term,
        argument_effect: Term,
        result_effect: Term,
        result: Term,
    ) -> Result<Term, SolveAvailabilityError> {
        self.store
            .terms
            .positive_function(argument, argument_effect, result_effect, result)
            .map_err(SolveAvailabilityError::from)
    }

    #[allow(
        dead_code,
        reason = "F5b private Function witnesses construct opaque live terms"
    )]
    fn negative_function_term(
        &mut self,
        argument: Term,
        argument_effect: Term,
        result_effect: Term,
        result: Term,
    ) -> Result<Term, SolveAvailabilityError> {
        self.store
            .terms
            .negative_function(argument, argument_effect, result_effect, result)
            .map_err(SolveAvailabilityError::from)
    }

    #[cfg(test)]
    fn inject_next_admission_failure(&mut self, error: ConstraintError) {
        self.store.injected_admission_failure = Some(error);
    }

    #[cfg(test)]
    fn inject_next_provenance_failure(&mut self, error: ConstraintError) {
        self.store.injected_provenance_failure = Some(error);
    }

    #[cfg(test)]
    fn inject_finalization_failure_after(&mut self, successful_finalizations: usize) {
        self.injected_finalization_failure_after = Some(successful_finalizations);
    }

    fn run(mut self) -> Result<SolvedModule, SolveAvailabilityError> {
        self.admit_all_collected_facts()?;
        self.execute_scc_plan()?;
        self.sample_f4_resources(ResourceBoundary::StoreAccounting);
        self.store.finish_accounting();
        self.sample_f4_resources(ResourceBoundary::StoreAccounting);
        self.finish()
    }

    #[cfg(test)]
    fn run_with_observer(
        mut self,
        capacity: usize,
    ) -> Result<(SolvedModule, OrderingObserver, SummaryObservation), SolveAvailabilityError> {
        self.ordering_observer = Some(OrderingObserver::new(capacity));
        self.admit_all_collected_facts()?;
        self.execute_scc_plan()?;
        self.sample_f4_resources(ResourceBoundary::StoreAccounting);
        self.store.finish_accounting();
        self.sample_f4_resources(ResourceBoundary::StoreAccounting);
        let observer = self
            .ordering_observer
            .take()
            .expect("test observer installed");
        let mut summary = SummaryObservation {
            ordinary_initial_value_pair_probes: self.initial_value_pair_probes
                - self.batch.synthetic_seed_value_pair_probes,
            synthetic_seed_value_pair_probes: self.batch.synthetic_seed_value_pair_probes,
            reads: self.summary_reads,
            false_to_true_transitions: self.summary_false_to_true_transitions,
            frontier_pushes: self.typed_pair_worklist_pushes,
            frontier_pops: self.typed_pair_worklist_pops,
            frontier_maximum_live: self.typed_pair_worklist_maximum_live,
            frontier_capacity: self.typed_worklist.capacity(),
            frontier_capacity_growths: self.typed_pair_worklist_capacity_growths,
            frontier_retained_bytes: checked_capacity_bytes::<TypedWorkItem>(
                self.typed_worklist.capacity(),
                "F5b observed typed frontier queue",
            ),
            frontier_peak_bytes: self.typed_pair_worklist_peak_bytes,
            direct_edges: self.typed_direct_edges,
            exact_lower_memberships: self.typed_exact_lower_memberships,
            exact_upper_memberships: self.typed_exact_upper_memberships,
            transmission_attempts: self.typed_transmission_attempts,
            same_row_atom_intersections: self.typed_same_row_atom_intersections,
            semantic_arena_retained_bytes: self.execution_counters.semantic_arena_retained_bytes,
            semantic_arena_peak_bytes: self.execution_counters.semantic_arena_peak_bytes,
            inference_session_retained_bytes: self
                .execution_counters
                .inference_session_retained_bytes,
            inference_session_peak_bytes: self.execution_counters.inference_session_peak_bytes,
            resource_boundary_samples: self.resource_boundary_samples,
            resource_boundary_coverage: self.resource_ledger.coverage.count_ones() as usize,
            independent_queue_retained_bytes: self.resource_ledger.queue_retained_bytes,
            independent_finish_output_retained_bytes: self
                .resource_ledger
                .finish_output_retained_bytes,
            independent_semantic_arena_retained_bytes: self
                .resource_ledger
                .semantic_arena_retained_bytes,
            independent_inference_session_retained_bytes: self
                .resource_ledger
                .inference_session_retained_bytes,
            independent_semantic_arena_peak_bytes: self.resource_ledger.semantic_arena_peak_bytes,
            independent_inference_session_peak_bytes: self
                .resource_ledger
                .inference_session_peak_bytes,
        };
        let solved = self.finish()?;
        summary.semantic_arena_retained_bytes = solved.counters.semantic_arena_retained_bytes;
        summary.semantic_arena_peak_bytes = solved.counters.semantic_arena_peak_bytes;
        summary.inference_session_retained_bytes = solved.counters.inference_session_retained_bytes;
        summary.inference_session_peak_bytes = solved.counters.inference_session_peak_bytes;
        summary.resource_boundary_samples = solved.resource_boundary_samples;
        summary.resource_boundary_coverage = solved.resource_ledger.coverage.count_ones() as usize;
        summary.independent_queue_retained_bytes = solved.resource_ledger.queue_retained_bytes;
        summary.independent_finish_output_retained_bytes =
            solved.resource_ledger.finish_output_retained_bytes;
        summary.independent_semantic_arena_retained_bytes =
            solved.resource_ledger.semantic_arena_retained_bytes;
        summary.independent_inference_session_retained_bytes =
            solved.resource_ledger.inference_session_retained_bytes;
        summary.independent_semantic_arena_peak_bytes =
            solved.resource_ledger.semantic_arena_peak_bytes;
        summary.independent_inference_session_peak_bytes =
            solved.resource_ledger.inference_session_peak_bytes;
        Ok((solved, observer, summary))
    }

    fn sample_f4_resources(&mut self, _boundary: ResourceBoundary) {
        self.sample_f4_resources_with_finish_output(_boundary, 0);
    }

    fn sample_f4_resources_with_finish_output(
        &mut self,
        _boundary: ResourceBoundary,
        finish_output_retained_bytes: usize,
    ) {
        Self::sample_f4_resource_parts(
            &self.store,
            &self.errors,
            &self.reported_errors,
            &self.cross_kind_components,
            &self.live_components,
            &self.bounds,
            &self.effect_bounds,
            &self.value_levels,
            &self.effect_levels,
            &self.value_metadata,
            &self.effect_metadata,
            &self.extrusion_stack,
            &self.extrusion_value_marks,
            &self.extrusion_effect_marks,
            self.bound_payload_bytes,
            &self.occurrence_exact_bounds,
            &self.typed_pairs,
            self.typed_pair_payload_bytes,
            &self.typed_worklist,
            &self.diagnostic_delta,
            &self.diagnostic_delta_indices,
            &self.diagnostic_reverse_offsets,
            &self.diagnostic_reverse_edges,
            &self.diagnostic_reverse_cursors,
            &self.diagnostic_dfs_stack,
            &self.diagnostic_finish_order,
            &self.diagnostic_scc_indices,
            &self.diagnostic_scc_nodes,
            &self.diagnostic_scc_offsets,
            &self.diagnostic_scc_pending_children,
            &self.diagnostic_scc_worklist,
            &self.diagnostic_bucket_heads,
            &self.diagnostic_bucket_tails,
            &self.diagnostic_bucket_candidates,
            &self.diagnostic_node_witnesses,
            &self.routed_uses,
            &self.routed_use_positions,
            &self.schemes,
            &self.drafts,
            self.current_closed_retained_bytes,
            self.batch.counters.f2_batch_retained_bytes,
            self.batch.component_term_positions.capacity(),
            finish_output_retained_bytes,
            &mut self.execution_counters,
            #[cfg(test)]
            &mut self.resource_boundary_samples,
            #[cfg(test)]
            _boundary,
            #[cfg(test)]
            &mut self.resource_ledger,
            #[cfg(test)]
            &self.independent_nested_capacities,
        );
    }

    /// This is a constant-size capacity snapshot.  It deliberately receives
    /// only already-owned containers, so a route can sample immediately after
    /// an allocation, reuse, or ownership-transfer boundary without scanning
    /// the batch, bound rows, or pair table.
    #[allow(clippy::too_many_arguments)]
    fn sample_f4_resource_parts(
        store: &ConstraintStore,
        errors: &Vec<SolverError>,
        reported_errors: &HashSet<(ConstraintOccurrenceId, SolverErrorKind)>,
        cross_kind_components: &HashSet<ComponentId>,
        live_components: &Vec<LiveComponentEndpoint>,
        bounds: &Vec<VariableBounds>,
        effect_bounds: &Vec<EffectBounds>,
        value_levels: &Vec<u32>,
        effect_levels: &Vec<u32>,
        value_metadata: &Vec<LiveVariableMetadata>,
        effect_metadata: &Vec<LiveVariableMetadata>,
        extrusion_stack: &Vec<ExtrusionEndpoint>,
        extrusion_value_marks: &Vec<u32>,
        extrusion_effect_marks: &Vec<u32>,
        bound_payload_bytes: usize,
        occurrence_exact_bounds: &Vec<OccurrenceExactBounds>,
        typed_pairs: &HashMap<TypedPairKey, TypedPairMemo>,
        typed_pair_payload_bytes: usize,
        typed_worklist: &VecDeque<TypedWorkItem>,
        diagnostic_delta: &Vec<CanonicalValuePairKey>,
        diagnostic_delta_indices: &HashMap<CanonicalValuePairKey, usize>,
        diagnostic_reverse_offsets: &Vec<usize>,
        diagnostic_reverse_edges: &Vec<DiagnosticReverseEdge>,
        diagnostic_reverse_cursors: &Vec<usize>,
        diagnostic_dfs_stack: &Vec<(usize, usize)>,
        diagnostic_finish_order: &Vec<usize>,
        diagnostic_scc_indices: &Vec<usize>,
        diagnostic_scc_nodes: &Vec<usize>,
        diagnostic_scc_offsets: &Vec<usize>,
        diagnostic_scc_pending_children: &Vec<usize>,
        diagnostic_scc_worklist: &VecDeque<usize>,
        diagnostic_bucket_heads: &Vec<Option<usize>>,
        diagnostic_bucket_tails: &Vec<Option<usize>>,
        diagnostic_bucket_candidates: &Vec<DiagnosticBucketCandidate>,
        diagnostic_node_witnesses: &Vec<Option<DiagnosticWitness>>,
        routed_uses: &Vec<RoutedUseProvenance>,
        routed_use_positions: &HashSet<DefinitionUseId>,
        schemes: &Vec<Option<ClosedValueScheme>>,
        drafts: &Vec<DraftScheme>,
        closed_type_retained_bytes: usize,
        f2_batch_retained_bytes: usize,
        component_term_positions_capacity: usize,
        finish_output_retained_bytes: usize,
        counters: &mut ProductionCounters,
        #[cfg(test)] resource_boundary_samples: &mut usize,
        #[cfg(test)] boundary: ResourceBoundary,
        #[cfg(test)] resource_ledger: &mut IndependentResourceLedger,
        #[cfg(test)] independent_nested_capacities: &IndependentNestedCapacityLedger,
    ) {
        #[cfg(not(test))]
        let _ = component_term_positions_capacity;
        #[cfg(test)]
        {
            *resource_boundary_samples += 1;
            resource_ledger.record(
                boundary,
                store,
                errors,
                reported_errors,
                cross_kind_components,
                live_components,
                bounds,
                effect_bounds,
                value_levels,
                effect_levels,
                value_metadata,
                effect_metadata,
                extrusion_stack,
                extrusion_value_marks,
                extrusion_effect_marks,
                occurrence_exact_bounds,
                typed_pairs,
                typed_worklist,
                diagnostic_delta,
                diagnostic_delta_indices,
                diagnostic_reverse_offsets,
                diagnostic_reverse_edges,
                diagnostic_reverse_cursors,
                diagnostic_dfs_stack,
                diagnostic_finish_order,
                diagnostic_scc_indices,
                diagnostic_scc_nodes,
                diagnostic_scc_offsets,
                diagnostic_scc_pending_children,
                diagnostic_scc_worklist,
                diagnostic_bucket_heads,
                diagnostic_bucket_tails,
                diagnostic_bucket_candidates,
                diagnostic_node_witnesses,
                routed_uses,
                routed_use_positions,
                schemes,
                drafts,
                closed_type_retained_bytes,
                f2_batch_retained_bytes,
                component_term_positions_capacity,
                finish_output_retained_bytes,
                independent_nested_capacities,
            );
        }
        let bounds_bytes = checked_usize_sum(
            [
                checked_capacity_bytes::<LiveComponentEndpoint>(
                    live_components.capacity(),
                    "F5b live translation",
                ),
                checked_capacity_bytes::<VariableBounds>(bounds.capacity(), "F5b value bound rows"),
                checked_capacity_bytes::<EffectBounds>(
                    effect_bounds.capacity(),
                    "F5b effect bound rows",
                ),
                checked_capacity_bytes::<u32>(value_levels.capacity(), "F5b value levels"),
                checked_capacity_bytes::<u32>(effect_levels.capacity(), "F5b effect levels"),
                checked_capacity_bytes::<LiveVariableMetadata>(
                    value_metadata.capacity(),
                    "F5b value metadata",
                ),
                checked_capacity_bytes::<LiveVariableMetadata>(
                    effect_metadata.capacity(),
                    "F5b effect metadata",
                ),
                checked_capacity_bytes::<ExtrusionEndpoint>(
                    extrusion_stack.capacity(),
                    "F5b extrusion stack",
                ),
                checked_capacity_bytes::<u32>(
                    extrusion_value_marks.capacity(),
                    "F5b extrusion value marks",
                ),
                checked_capacity_bytes::<u32>(
                    extrusion_effect_marks.capacity(),
                    "F5b extrusion effect marks",
                ),
                bound_payload_bytes,
            ],
            "F5b live bound tables",
        );
        let pair_bytes = checked_usize_sum(
            [
                checked_capacity_bytes::<(TypedPairKey, TypedPairMemo)>(
                    typed_pairs.capacity(),
                    "F5b typed pair memo",
                ),
                typed_pair_payload_bytes,
            ],
            "F5b typed pair memo including diagnostic edges",
        );
        let frontier_bytes = checked_capacity_bytes::<TypedWorkItem>(
            typed_worklist.capacity(),
            "F5b typed frontier queue",
        );
        let diagnostic_scratch_bytes = checked_usize_sum(
            [
                checked_capacity_bytes::<CanonicalValuePairKey>(
                    diagnostic_delta.capacity(),
                    "F5b diagnostic delta",
                ),
                checked_capacity_bytes::<(CanonicalValuePairKey, usize)>(
                    diagnostic_delta_indices.capacity(),
                    "F5b diagnostic delta index",
                ),
                checked_capacity_bytes::<usize>(
                    diagnostic_reverse_offsets.capacity(),
                    "F5b reverse offsets",
                ),
                checked_capacity_bytes::<DiagnosticReverseEdge>(
                    diagnostic_reverse_edges.capacity(),
                    "F5b reverse edges",
                ),
                checked_capacity_bytes::<usize>(
                    diagnostic_reverse_cursors.capacity(),
                    "F5b reverse cursors",
                ),
                checked_capacity_bytes::<(usize, usize)>(
                    diagnostic_dfs_stack.capacity(),
                    "F5b diagnostic DFS",
                ),
                checked_capacity_bytes::<usize>(
                    diagnostic_finish_order.capacity(),
                    "F5b finish order",
                ),
                checked_capacity_bytes::<usize>(
                    diagnostic_scc_indices.capacity(),
                    "F5b SCC indices",
                ),
                checked_capacity_bytes::<usize>(diagnostic_scc_nodes.capacity(), "F5b SCC nodes"),
                checked_capacity_bytes::<usize>(
                    diagnostic_scc_offsets.capacity(),
                    "F5b SCC offsets",
                ),
                checked_capacity_bytes::<usize>(
                    diagnostic_scc_pending_children.capacity(),
                    "F5b SCC pending",
                ),
                checked_capacity_bytes::<usize>(
                    diagnostic_scc_worklist.capacity(),
                    "F5b SCC worklist",
                ),
                checked_capacity_bytes::<Option<usize>>(
                    diagnostic_bucket_heads.capacity(),
                    "F5b bucket heads",
                ),
                checked_capacity_bytes::<Option<usize>>(
                    diagnostic_bucket_tails.capacity(),
                    "F5b bucket tails",
                ),
                checked_capacity_bytes::<DiagnosticBucketCandidate>(
                    diagnostic_bucket_candidates.capacity(),
                    "F5b bucket candidates",
                ),
                checked_capacity_bytes::<Option<DiagnosticWitness>>(
                    diagnostic_node_witnesses.capacity(),
                    "F5b node witnesses",
                ),
            ],
            "F5b diagnostic scratch",
        );
        let exact_bytes = checked_capacity_bytes::<OccurrenceExactBounds>(
            occurrence_exact_bounds.capacity(),
            "F4 production occurrence bounds",
        );
        let scheme_bytes = checked_capacity_bytes::<Option<ClosedValueScheme>>(
            schemes.capacity(),
            "F4 production scheme table",
        );
        let routes_bytes = checked_capacity_bytes::<RoutedUseProvenance>(
            routed_uses.capacity(),
            "F4 production routed-use provenance",
        );
        let drafts_bytes =
            checked_capacity_bytes::<DraftScheme>(drafts.capacity(), "F4 production draft scratch");
        let store_bytes = checked_usize_sum(
            [
                checked_capacity_bytes::<SemanticFact>(
                    store.facts.capacity(),
                    "F4 production facts",
                ),
                checked_capacity_bytes::<(FactKey, FactId)>(
                    store.canonical.capacity(),
                    "F4 production canonical map",
                ),
                checked_capacity_bytes::<ProvenanceEdge>(
                    store.provenance.capacity(),
                    "F4 production provenance",
                ),
                checked_capacity_bytes::<u64>(
                    store.consumed_receipts.capacity(),
                    "F4 production consumed receipts",
                ),
            ],
            "F4 production store",
        );
        counters.draft_scratch_capacity = drafts.capacity();
        counters.draft_scratch_retained_bytes = drafts_bytes;
        // Compatibility accessor: aggregate the dense live-table lanes rather
        // than reporting one value-row Vec while retained bytes cover the
        // complete value/effect table family. Nested row storage is
        // heterogeneous and remains represented exactly by retained bytes.
        counters.bound_table_capacity = checked_usize_sum(
            [
                live_components.capacity(),
                bounds.capacity(),
                effect_bounds.capacity(),
                value_levels.capacity(),
                effect_levels.capacity(),
                value_metadata.capacity(),
                effect_metadata.capacity(),
                extrusion_stack.capacity(),
                extrusion_value_marks.capacity(),
                extrusion_effect_marks.capacity(),
            ],
            "F5b aggregate live-table capacity",
        );
        counters.bound_table_retained_bytes = bounds_bytes;
        counters.bound_table_peak_bytes = counters.bound_table_peak_bytes.max(bounds_bytes);
        counters.constraint_pair_cache_capacity = typed_pairs.capacity();
        counters.constraint_pair_cache_retained_bytes = pair_bytes;
        counters.constraint_pair_cache_peak_bytes =
            counters.constraint_pair_cache_peak_bytes.max(pair_bytes);
        counters.scheme_table_len = schemes.len();
        counters.scheme_table_capacity = schemes.capacity();
        counters.scheme_table_retained_bytes = scheme_bytes;
        counters.routed_use_provenance_len = routed_uses.len();
        counters.routed_use_provenance_capacity = routed_uses.capacity();
        counters.routed_use_provenance_retained_bytes = routes_bytes;
        counters.occurrence_bound_state_len = occurrence_exact_bounds.len();
        counters.occurrence_bound_state_capacity = occurrence_exact_bounds.capacity();
        counters.occurrence_bound_state_retained_bytes = exact_bytes;
        // Solver errors remain live session storage after F4.  Unlike removed
        // finish-only workspaces, this is a retained diagnostic boundary.
        counters.solver_error_workspace_capacity = errors.capacity();
        counters.solver_error_workspace_retained_bytes =
            checked_capacity_bytes::<SolverError>(errors.capacity(), "F4 production solver errors");
        counters.semantic_arena_retained_bytes = checked_usize_sum(
            [
                bounds_bytes,
                pair_bytes,
                frontier_bytes,
                diagnostic_scratch_bytes,
                scheme_bytes,
                routes_bytes,
                drafts_bytes,
                closed_type_retained_bytes,
                exact_bytes,
                store.inference_term_retained_bytes(),
            ],
            "F4 production semantic arena",
        );
        counters.semantic_arena_peak_bytes = counters
            .semantic_arena_peak_bytes
            .max(counters.semantic_arena_retained_bytes);
        counters.inference_session_retained_bytes = checked_usize_sum(
            [
                counters.semantic_arena_retained_bytes,
                store_bytes,
                checked_capacity_bytes::<SolverError>(
                    errors.capacity(),
                    "F4 production solver errors",
                ),
                checked_capacity_bytes::<(ConstraintOccurrenceId, SolverErrorKind)>(
                    reported_errors.capacity(),
                    "F5b production reported-error index",
                ),
                checked_capacity_bytes::<ComponentId>(
                    cross_kind_components.capacity(),
                    "F4 production cross-kind components",
                ),
                checked_capacity_bytes::<DefinitionUseId>(
                    routed_use_positions.capacity(),
                    "F4 production routed-use index",
                ),
                f2_batch_retained_bytes,
            ],
            "F4 production session",
        );
        let full_session_bytes = counters
            .inference_session_retained_bytes
            .checked_add(finish_output_retained_bytes)
            .expect("F4 finish-output session accounting fits usize");
        counters.inference_session_peak_bytes = counters
            .inference_session_peak_bytes
            .max(full_session_bytes);
    }

    fn admit_all_collected_facts(&mut self) -> Result<(), SolveAvailabilityError> {
        for occurrence_index in 0..self.batch.occurrences().len() {
            let occurrence = self.batch.occurrences()[occurrence_index].clone();
            let result = {
                let mut transaction = self.store.transaction();
                transaction.admit(&occurrence)
            };
            match result {
                Ok(receipt) => {
                    self.store
                        .record_provenance(receipt)
                        .map_err(SolveAvailabilityError::from)?;
                    match self
                        .store
                        .term_kind(occurrence.lower)
                        .expect("admitted term remains valid")
                    {
                        ComponentKind::Value => {
                            #[cfg(test)]
                            {
                                self.initial_value_pair_probes += 1;
                            }
                            let key = CanonicalValuePairKey {
                                lower: self.value_endpoint(occurrence.lower, Polarity::Positive),
                                upper: self.value_endpoint(occurrence.upper, Polarity::Negative),
                            };
                            let transitions =
                                self.constrain_live_value(key, &occurrence.id, &occurrence.cause)?;
                            #[cfg(test)]
                            {
                                self.summary_false_to_true_transitions += transitions;
                            }
                            #[cfg(not(test))]
                            let _ = transitions;
                            self.sample_f4_resources(ResourceBoundary::InitialAdmission);
                        }
                        ComponentKind::Effect => {
                            let lower = self.effect_endpoint(occurrence.lower, Polarity::Positive);
                            let upper = self.effect_endpoint(occurrence.upper, Polarity::Negative);
                            self.constrain_live_effect(
                                lower,
                                upper,
                                &occurrence.id,
                                &occurrence.cause,
                            )?;
                            self.sample_f4_resources(ResourceBoundary::InitialAdmission);
                        }
                    }
                }
                Err(ConstraintError::CrossKind { lower, upper }) => {
                    reserve_f5b(&mut self.errors, 1, F5bCapacityLane::Errors)?;
                    reserve_f5b(
                        &mut self.cross_kind_components,
                        2,
                        F5bCapacityLane::CrossKindComponents,
                    )?;
                    self.errors.push(SolverError {
                        occurrence: occurrence.id.clone(),
                        cause: occurrence.cause.clone(),
                        kind: SolverErrorKind::CrossKind { lower, upper },
                    });
                    for term in [occurrence.lower, occurrence.upper] {
                        if let Ok(TermView::Component(component)) = self.store.term_view(term) {
                            self.cross_kind_components.insert(component.clone());
                        }
                    }
                    self.sample_f4_resources(ResourceBoundary::CrossKind);
                }
                Err(error) => return Err(error.into()),
            }
        }
        Ok(())
    }

    fn component_endpoint(&self, term: Term) -> LiveComponentEndpoint {
        let position = *self
            .batch
            .component_term_positions
            .get(&term)
            .expect("collected component term has one immutable recipe position");
        self.live_components[position]
    }

    fn value_endpoint(&self, term: Term, polarity: Polarity) -> ValueEndpointKey {
        match self
            .store
            .term_view(term)
            .expect("collected value term is visible in its solve branch")
        {
            TermView::Leaf(Leaf::IntPositive) => ValueEndpointKey::IntPositive,
            TermView::Leaf(Leaf::IntNegative) => ValueEndpointKey::IntNegative,
            TermView::Component(component) => {
                debug_assert_eq!(component.kind(), ComponentKind::Value);
                ValueEndpointKey::ValueRow(self.component_endpoint(term).ordinal)
            }
            TermView::LiveVariable(view) => {
                assert_eq!(view.kind(), ComponentKind::Value);
                assert_eq!(view.polarity(), polarity);
                ValueEndpointKey::ValueRow(view.ordinal())
            }
            TermView::PositiveBottom => ValueEndpointKey::BottomPositive,
            TermView::NegativeTop => ValueEndpointKey::TopNegative,
            TermView::NegativeBottom => ValueEndpointKey::BottomNegative,
            TermView::PositiveFunction { .. } => {
                assert_eq!(polarity, Polarity::Positive);
                ValueEndpointKey::PositiveFunction(term)
            }
            TermView::NegativeFunction { .. } => {
                assert_eq!(polarity, Polarity::Negative);
                ValueEndpointKey::NegativeFunction(term)
            }
            TermView::Leaf(_) => panic!("effect leaf cannot translate as a value endpoint"),
        }
    }

    fn effect_endpoint(&self, term: Term, polarity: Polarity) -> EffectEndpointKey {
        match self
            .store
            .term_view(term)
            .expect("collected effect term is visible in its solve branch")
        {
            TermView::Leaf(Leaf::EffectBottomPositive) => EffectEndpointKey::BottomPositive,
            TermView::Leaf(Leaf::EmptyEffectNegative) => EffectEndpointKey::EmptyNegative,
            TermView::Component(component) => {
                debug_assert_eq!(component.kind(), ComponentKind::Effect);
                EffectEndpointKey::EffectRow(self.component_endpoint(term).ordinal)
            }
            TermView::LiveVariable(view) => {
                assert_eq!(view.kind(), ComponentKind::Effect);
                assert_eq!(view.polarity(), polarity);
                EffectEndpointKey::EffectRow(view.ordinal())
            }
            TermView::PositiveBottom | TermView::NegativeTop | TermView::NegativeBottom => {
                panic!("value extreme cannot translate as an effect endpoint")
            }
            _ => panic!("value term cannot translate as an effect endpoint"),
        }
    }

    /// Lower reachable younger variables with reusable generation marks.  The
    /// traversal follows only installed exact structure and direct adjacency;
    /// it neither allocates per pair nor materializes transitive relations.
    fn extrude_value_endpoint(
        &mut self,
        endpoint: ValueEndpointKey,
        target_level: u32,
    ) -> Result<(), SolveAvailabilityError> {
        self.extrude(ExtrusionEndpoint::Value(endpoint), target_level)
    }

    /// Every growth of the iterative traversal is fallible.  In particular,
    /// Function children are not bounded by the startup component count: a
    /// private F5b witness or later fresh instantiation can be arbitrarily
    /// deep.
    fn extrude(
        &mut self,
        initial: ExtrusionEndpoint,
        target_level: u32,
    ) -> Result<(), SolveAvailabilityError> {
        self.extrusion_generation = self.extrusion_generation.wrapping_add(1);
        if self.extrusion_generation == 0 {
            self.extrusion_value_marks.fill(0);
            self.extrusion_effect_marks.fill(0);
            self.extrusion_generation = 1;
        }
        let generation = self.extrusion_generation;
        self.extrusion_stack.clear();
        self.push_extrusion(initial)?;
        while let Some(endpoint) = self.extrusion_stack.pop() {
            match endpoint {
                ExtrusionEndpoint::Value(endpoint) => match endpoint {
                    ValueEndpointKey::ValueRow(ordinal) => {
                        let index = ordinal as usize;
                        if self.extrusion_value_marks[index] == generation
                            || self.value_levels[index] <= target_level
                        {
                            continue;
                        }
                        self.extrusion_value_marks[index] = generation;
                        self.value_levels[index] = target_level;
                        for item_index in 0..self.bounds[index].exact_non_variable_lowers.len() {
                            self.push_extrusion(ExtrusionEndpoint::Value(
                                self.bounds[index].exact_non_variable_lowers[item_index],
                            ))?;
                        }
                        for item_index in 0..self.bounds[index].exact_non_variable_uppers.len() {
                            self.push_extrusion(ExtrusionEndpoint::Value(
                                self.bounds[index].exact_non_variable_uppers[item_index],
                            ))?;
                        }
                        for row_index in 0..self.bounds[index].direct_lower_rows.len() {
                            self.push_extrusion(ExtrusionEndpoint::Value(
                                ValueEndpointKey::ValueRow(
                                    self.bounds[index].direct_lower_rows[row_index],
                                ),
                            ))?;
                        }
                        for row_index in 0..self.bounds[index].direct_upper_rows.len() {
                            self.push_extrusion(ExtrusionEndpoint::Value(
                                ValueEndpointKey::ValueRow(
                                    self.bounds[index].direct_upper_rows[row_index],
                                ),
                            ))?;
                        }
                    }
                    ValueEndpointKey::PositiveFunction(term) => {
                        let TermView::PositiveFunction {
                            argument,
                            argument_effect,
                            result_effect,
                            result,
                        } = self
                            .store
                            .term_view(term)
                            .expect("live Function remains branch-owned")
                        else {
                            unreachable!("positive Function endpoint retains its constructor");
                        };
                        // Reverse push preserves the normative pop/decomposition order.
                        self.push_extrusion(ExtrusionEndpoint::Value(
                            self.value_endpoint(result, Polarity::Positive),
                        ))?;
                        self.push_extrusion(ExtrusionEndpoint::Effect(
                            self.effect_endpoint(result_effect, Polarity::Positive),
                        ))?;
                        self.push_extrusion(ExtrusionEndpoint::Effect(
                            self.effect_endpoint(argument_effect, Polarity::Negative),
                        ))?;
                        self.push_extrusion(ExtrusionEndpoint::Value(
                            self.value_endpoint(argument, Polarity::Negative),
                        ))?;
                    }
                    ValueEndpointKey::NegativeFunction(term) => {
                        let TermView::NegativeFunction {
                            argument,
                            argument_effect,
                            result_effect,
                            result,
                        } = self
                            .store
                            .term_view(term)
                            .expect("live Function remains branch-owned")
                        else {
                            unreachable!("negative Function endpoint retains its constructor");
                        };
                        self.push_extrusion(ExtrusionEndpoint::Value(
                            self.value_endpoint(result, Polarity::Negative),
                        ))?;
                        self.push_extrusion(ExtrusionEndpoint::Effect(
                            self.effect_endpoint(result_effect, Polarity::Negative),
                        ))?;
                        self.push_extrusion(ExtrusionEndpoint::Effect(
                            self.effect_endpoint(argument_effect, Polarity::Positive),
                        ))?;
                        self.push_extrusion(ExtrusionEndpoint::Value(
                            self.value_endpoint(argument, Polarity::Positive),
                        ))?;
                    }
                    _ => {}
                },
                ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(ordinal)) => {
                    let index = ordinal as usize;
                    if self.extrusion_effect_marks[index] == generation
                        || self.effect_levels[index] <= target_level
                    {
                        continue;
                    }
                    self.extrusion_effect_marks[index] = generation;
                    self.effect_levels[index] = target_level;
                    for item_index in 0..self.effect_bounds[index].exact_non_variable_lowers.len() {
                        self.push_extrusion(ExtrusionEndpoint::Effect(
                            self.effect_bounds[index].exact_non_variable_lowers[item_index],
                        ))?;
                    }
                    for item_index in 0..self.effect_bounds[index].exact_non_variable_uppers.len() {
                        self.push_extrusion(ExtrusionEndpoint::Effect(
                            self.effect_bounds[index].exact_non_variable_uppers[item_index],
                        ))?;
                    }
                    for row_index in 0..self.effect_bounds[index].direct_lower_rows.len() {
                        self.push_extrusion(ExtrusionEndpoint::Effect(
                            EffectEndpointKey::EffectRow(
                                self.effect_bounds[index].direct_lower_rows[row_index],
                            ),
                        ))?;
                    }
                    for row_index in 0..self.effect_bounds[index].direct_upper_rows.len() {
                        self.push_extrusion(ExtrusionEndpoint::Effect(
                            EffectEndpointKey::EffectRow(
                                self.effect_bounds[index].direct_upper_rows[row_index],
                            ),
                        ))?;
                    }
                }
                ExtrusionEndpoint::Effect(_) => {}
            }
        }
        Ok(())
    }

    fn push_extrusion(
        &mut self,
        endpoint: ExtrusionEndpoint,
    ) -> Result<(), SolveAvailabilityError> {
        reserve_f5b(
            &mut self.extrusion_stack,
            1,
            F5bCapacityLane::ExtrusionStack,
        )?;
        self.extrusion_stack.push(endpoint);
        Ok(())
    }

    /// Effect constraints share the one session worklist and typed memo with
    /// values.  Every replay keeps the inducing direct occurrence and cause.
    fn constrain_live_effect(
        &mut self,
        lower: EffectEndpointKey,
        upper: EffectEndpointKey,
        occurrence: &ConstraintOccurrenceId,
        cause: &CauseId,
    ) -> Result<usize, SolveAvailabilityError> {
        self.constrain_live(LiveConstraintTask::Effect(lower, upper), occurrence, cause)
    }

    fn apply_effect_task(
        &mut self,
        lower: EffectEndpointKey,
        upper: EffectEndpointKey,
    ) -> Result<(), SolveAvailabilityError> {
        match (lower, upper) {
            (EffectEndpointKey::EffectRow(a), EffectEndpointKey::EffectRow(b)) => {
                let minimum = self.effect_levels[a as usize].min(self.effect_levels[b as usize]);
                self.extrude(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(a)),
                    minimum,
                )?;
                self.extrude(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(b)),
                    minimum,
                )?;
                let old_lower_capacity =
                    self.effect_bounds[b as usize].direct_lower_rows.capacity();
                let old_upper_capacity =
                    self.effect_bounds[a as usize].direct_upper_rows.capacity();
                reserve_f5b(
                    &mut self.effect_bounds[b as usize].direct_lower_rows,
                    1,
                    F5bCapacityLane::EffectDirectLower,
                )?;
                reserve_f5b(
                    &mut self.effect_bounds[a as usize].direct_upper_rows,
                    1,
                    F5bCapacityLane::EffectDirectUpper,
                )?;
                self.effect_bounds[b as usize].direct_lower_rows.push(a);
                self.effect_bounds[a as usize].direct_upper_rows.push(b);
                Self::record_bound_capacity_growth(
                    &mut self.bound_payload_bytes,
                    #[cfg(test)]
                    &mut self.independent_nested_capacities.effect_direct_lower,
                    &mut self.execution_counters,
                    old_lower_capacity,
                    self.effect_bounds[b as usize].direct_lower_rows.capacity(),
                    std::mem::size_of::<u32>(),
                );
                Self::record_bound_capacity_growth(
                    &mut self.bound_payload_bytes,
                    #[cfg(test)]
                    &mut self.independent_nested_capacities.effect_direct_upper,
                    &mut self.execution_counters,
                    old_upper_capacity,
                    self.effect_bounds[a as usize].direct_upper_rows.capacity(),
                    std::mem::size_of::<u32>(),
                );
                let lower_len = self.effect_bounds[a as usize]
                    .exact_non_variable_lowers
                    .len();
                for index in 0..lower_len {
                    self.enqueue_task(LiveConstraintTask::Effect(
                        self.effect_bounds[a as usize].exact_non_variable_lowers[index],
                        EffectEndpointKey::EffectRow(b),
                    ))?;
                }
                let upper_len = self.effect_bounds[b as usize]
                    .exact_non_variable_uppers
                    .len();
                for index in 0..upper_len {
                    self.enqueue_task(LiveConstraintTask::Effect(
                        EffectEndpointKey::EffectRow(a),
                        self.effect_bounds[b as usize].exact_non_variable_uppers[index],
                    ))?;
                }
            }
            (item, EffectEndpointKey::EffectRow(row)) => {
                let index = row as usize;
                self.extrude(ExtrusionEndpoint::Effect(item), self.effect_levels[index])?;
                let old_capacity = self.effect_bounds[index]
                    .exact_non_variable_lowers
                    .capacity();
                reserve_f5b(
                    &mut self.effect_bounds[index].exact_non_variable_lowers,
                    1,
                    F5bCapacityLane::EffectExactLower,
                )?;
                self.effect_bounds[index]
                    .exact_non_variable_lowers
                    .push(item);
                Self::record_bound_capacity_growth(
                    &mut self.bound_payload_bytes,
                    #[cfg(test)]
                    &mut self.independent_nested_capacities.effect_exact_lower,
                    &mut self.execution_counters,
                    old_capacity,
                    self.effect_bounds[index]
                        .exact_non_variable_lowers
                        .capacity(),
                    std::mem::size_of::<EffectEndpointKey>(),
                );
                self.effect_bounds[index].has_bottom_lower |=
                    item == EffectEndpointKey::BottomPositive;
                let upper_len = self.effect_bounds[index].exact_non_variable_uppers.len();
                for upper_index in 0..upper_len {
                    self.enqueue_task(LiveConstraintTask::Effect(
                        item,
                        self.effect_bounds[index].exact_non_variable_uppers[upper_index],
                    ))?;
                }
                let row_len = self.effect_bounds[index].direct_upper_rows.len();
                for row_index in 0..row_len {
                    self.enqueue_task(LiveConstraintTask::Effect(
                        item,
                        EffectEndpointKey::EffectRow(
                            self.effect_bounds[index].direct_upper_rows[row_index],
                        ),
                    ))?;
                }
            }
            (EffectEndpointKey::EffectRow(row), item) => {
                let index = row as usize;
                self.extrude(ExtrusionEndpoint::Effect(item), self.effect_levels[index])?;
                let old_capacity = self.effect_bounds[index]
                    .exact_non_variable_uppers
                    .capacity();
                reserve_f5b(
                    &mut self.effect_bounds[index].exact_non_variable_uppers,
                    1,
                    F5bCapacityLane::EffectExactUpper,
                )?;
                self.effect_bounds[index]
                    .exact_non_variable_uppers
                    .push(item);
                Self::record_bound_capacity_growth(
                    &mut self.bound_payload_bytes,
                    #[cfg(test)]
                    &mut self.independent_nested_capacities.effect_exact_upper,
                    &mut self.execution_counters,
                    old_capacity,
                    self.effect_bounds[index]
                        .exact_non_variable_uppers
                        .capacity(),
                    std::mem::size_of::<EffectEndpointKey>(),
                );
                self.effect_bounds[index].has_empty_upper |=
                    item == EffectEndpointKey::EmptyNegative;
                let lower_len = self.effect_bounds[index].exact_non_variable_lowers.len();
                for lower_index in 0..lower_len {
                    self.enqueue_task(LiveConstraintTask::Effect(
                        self.effect_bounds[index].exact_non_variable_lowers[lower_index],
                        item,
                    ))?;
                }
                let row_len = self.effect_bounds[index].direct_lower_rows.len();
                for row_index in 0..row_len {
                    self.enqueue_task(LiveConstraintTask::Effect(
                        EffectEndpointKey::EffectRow(
                            self.effect_bounds[index].direct_lower_rows[row_index],
                        ),
                        item,
                    ))?;
                }
            }
            (EffectEndpointKey::BottomPositive, EffectEndpointKey::EmptyNegative) => {}
            _ => unreachable!("effect endpoints are polarized before constraining"),
        }
        Ok(())
    }

    /// The full F5b algebra owns one typed worklist and one typed memo for the
    /// lifetime of the session.  Direct-bound replay and Function children are
    /// ordinary work items; there is no value-only cache or frontier.
    fn constrain_live_value(
        &mut self,
        initial: CanonicalValuePairKey,
        occurrence: &ConstraintOccurrenceId,
        cause: &CauseId,
    ) -> Result<usize, SolveAvailabilityError> {
        self.constrain_live(LiveConstraintTask::Value(initial), occurrence, cause)
    }

    fn constrain_live(
        &mut self,
        initial: LiveConstraintTask,
        occurrence: &ConstraintOccurrenceId,
        cause: &CauseId,
    ) -> Result<usize, SolveAvailabilityError> {
        assert!(
            self.typed_worklist.is_empty(),
            "constrain begins with an empty worklist"
        );
        self.clear_diagnostic_scratch();
        let mut transitions = 0;
        self.enqueue_task(initial)?;
        while let Some(item) = self.typed_worklist.pop_front() {
            #[cfg(test)]
            if matches!(item.task, LiveConstraintTask::Value(_)) {
                self.typed_pair_worklist_pops += 1;
            }
            match item.task {
                LiveConstraintTask::Effect(lower, upper) => {
                    let key = TypedPairKey::Effect { lower, upper };
                    if self.typed_pairs.contains_key(&key) {
                        self.execution_counters.constraint_pair_duplicates += 1;
                    } else {
                        self.record_typed_pair_admission(key, TypedPairMemo::Effect)?;
                        self.apply_effect_task(lower, upper)?;
                    }
                }
                LiveConstraintTask::Value(key) => {
                    let memo_key = TypedPairKey::Value(key);
                    if self.typed_pairs.contains_key(&memo_key) {
                        self.execution_counters.constraint_pair_duplicates += 1;
                        continue;
                    }
                    if let Some((lower, upper)) = Self::incompatible_value_shapes(key) {
                        self.record_typed_pair_admission(
                            memo_key,
                            TypedPairMemo::Value {
                                children: Vec::new(),
                                direct_witness: Some(DiagnosticWitness {
                                    terminal: key,
                                    kind: SolverErrorKind::IncompatibleValue { lower, upper },
                                    distance: 0,
                                    first_field: None,
                                }),
                                completion: DiagnosticCompletion::Pending,
                            },
                        )?;
                        continue;
                    }
                    if matches!(key.lower, ValueEndpointKey::BottomPositive)
                        || matches!(key.upper, ValueEndpointKey::TopNegative)
                    {
                        self.record_typed_pair_admission(
                            memo_key,
                            TypedPairMemo::Value {
                                children: Vec::new(),
                                direct_witness: None,
                                completion: DiagnosticCompletion::Pending,
                            },
                        )?;
                        continue;
                    }
                    let (Some(lower), Some(upper)) = (
                        Self::positive_function_children(&self.store, key.lower),
                        Self::negative_function_children(&self.store, key.upper),
                    ) else {
                        // Atoms and structured constructors have no live
                        // level.  Only a structural bound is extruded into
                        // its receiving variable; Var/Var aging belongs to
                        // the direct-row transition below.
                        match (key.lower, key.upper) {
                            (lower, ValueEndpointKey::ValueRow(row))
                                if !matches!(lower, ValueEndpointKey::ValueRow(_)) =>
                            {
                                self.extrude_value_endpoint(
                                    lower,
                                    self.value_levels[row as usize],
                                )?;
                            }
                            (ValueEndpointKey::ValueRow(row), upper)
                                if !matches!(upper, ValueEndpointKey::ValueRow(_)) =>
                            {
                                self.extrude_value_endpoint(
                                    upper,
                                    self.value_levels[row as usize],
                                )?;
                            }
                            _ => {}
                        }
                        self.record_typed_pair_admission(
                            memo_key,
                            TypedPairMemo::Value {
                                children: Vec::new(),
                                direct_witness: None,
                                completion: DiagnosticCompletion::Pending,
                            },
                        )?;
                        transitions += self.apply_value_task(key)?;
                        continue;
                    };
                    let children = [
                        (
                            FunctionField::Argument,
                            TypedPairKey::Value(CanonicalValuePairKey {
                                lower: self.value_endpoint(upper.0, Polarity::Positive),
                                upper: self.value_endpoint(lower.0, Polarity::Negative),
                            }),
                        ),
                        (
                            FunctionField::ArgumentEffect,
                            TypedPairKey::Effect {
                                lower: self.effect_endpoint(upper.1, Polarity::Positive),
                                upper: self.effect_endpoint(lower.1, Polarity::Negative),
                            },
                        ),
                        (
                            FunctionField::ResultEffect,
                            TypedPairKey::Effect {
                                lower: self.effect_endpoint(lower.2, Polarity::Positive),
                                upper: self.effect_endpoint(upper.2, Polarity::Negative),
                            },
                        ),
                        (
                            FunctionField::Result,
                            TypedPairKey::Value(CanonicalValuePairKey {
                                lower: self.value_endpoint(lower.3, Polarity::Positive),
                                upper: self.value_endpoint(upper.3, Polarity::Negative),
                            }),
                        ),
                    ];
                    self.record_typed_pair_admission(
                        memo_key,
                        TypedPairMemo::Value {
                            children: Vec::new(),
                            direct_witness: None,
                            completion: DiagnosticCompletion::Pending,
                        },
                    )?;
                    for (field, child) in children {
                        if let TypedPairKey::Value(child) = child {
                            self.record_diagnostic_edge(key, child, Some(field))?;
                        }
                    }
                    for (_, child) in children.into_iter().rev() {
                        self.enqueue_front(match child {
                            TypedPairKey::Value(value) => LiveConstraintTask::Value(value),
                            TypedPairKey::Effect { lower, upper } => {
                                LiveConstraintTask::Effect(lower, upper)
                            }
                        })?;
                    }
                }
            }
        }
        self.complete_diagnostic_delta()?;
        if let LiveConstraintTask::Value(root) = initial {
            self.replay_witness(root, occurrence, cause)?;
        }
        self.clear_diagnostic_scratch();
        debug_assert!(
            self.typed_worklist.is_empty(),
            "constrain drains its worklist before return"
        );
        Ok(transitions)
    }

    fn enqueue_task(&mut self, task: LiveConstraintTask) -> Result<(), SolveAvailabilityError> {
        reserve_f5b(&mut self.typed_worklist, 1, F5bCapacityLane::TypedWorklist)?;
        let old_capacity = self.typed_worklist.capacity();
        self.typed_worklist.push_back(TypedWorkItem { task });
        #[cfg(test)]
        self.record_typed_worklist_push(task, old_capacity);
        #[cfg(not(test))]
        let _ = old_capacity;
        Ok(())
    }

    fn enqueue_front(&mut self, task: LiveConstraintTask) -> Result<(), SolveAvailabilityError> {
        reserve_f5b(&mut self.typed_worklist, 1, F5bCapacityLane::TypedWorklist)?;
        let old_capacity = self.typed_worklist.capacity();
        self.typed_worklist.push_front(TypedWorkItem { task });
        #[cfg(test)]
        self.record_typed_worklist_push(task, old_capacity);
        #[cfg(not(test))]
        let _ = old_capacity;
        Ok(())
    }

    #[cfg(test)]
    fn record_typed_worklist_push(&mut self, task: LiveConstraintTask, old_capacity: usize) {
        if matches!(task, LiveConstraintTask::Value(_)) {
            self.typed_pair_worklist_pushes += 1;
        }
        self.typed_pair_worklist_maximum_live = self
            .typed_pair_worklist_maximum_live
            .max(self.typed_worklist.len());
        if self.typed_worklist.capacity() != old_capacity {
            self.typed_pair_worklist_capacity_growths += 1;
        }
        self.typed_pair_worklist_peak_bytes =
            self.typed_pair_worklist_peak_bytes
                .max(checked_capacity_bytes::<TypedWorkItem>(
                    self.typed_worklist.capacity(),
                    "typed worklist capacity",
                ));
    }

    fn record_typed_pair_admission(
        &mut self,
        key: TypedPairKey,
        entry: TypedPairMemo,
    ) -> Result<(), SolveAvailabilityError> {
        // Reserve every persistent memo/delta lane before the first admission
        // makes the pair semantically visible.  The session is discardable on
        // availability failure, but no unreserved logical edge is published.
        reserve_f5b(&mut self.typed_pairs, 1, F5bCapacityLane::TypedPairs)?;
        if matches!(key, TypedPairKey::Value(_)) {
            reserve_f5b(
                &mut self.diagnostic_delta,
                1,
                F5bCapacityLane::DiagnosticDelta,
            )?;
            reserve_f5b(
                &mut self.diagnostic_delta_indices,
                1,
                F5bCapacityLane::DiagnosticDeltaIndices,
            )?;
        }
        let old_capacity = self.typed_pairs.capacity();
        assert!(
            self.typed_pairs.insert(key, entry).is_none(),
            "pair admitted once"
        );
        self.execution_counters.constraint_pair_admissions += 1;
        if let TypedPairKey::Value(value) = key {
            let index = self.diagnostic_delta.len();
            self.diagnostic_delta.push(value);
            assert!(
                self.diagnostic_delta_indices.insert(value, index).is_none(),
                "a newly admitted value pair enters one diagnostic delta"
            );
        }
        if self.typed_pairs.capacity() != old_capacity {
            self.execution_counters.constraint_pair_cache_growths += 1;
            self.execution_counters.constraint_pair_cache_rebuilds += 1;
        }
        Ok(())
    }

    fn record_diagnostic_edge(
        &mut self,
        parent: CanonicalValuePairKey,
        child: CanonicalValuePairKey,
        field: Option<FunctionField>,
    ) -> Result<(), SolveAvailabilityError> {
        let parent_edge = DiagnosticEdge { child, field };
        let Some(TypedPairMemo::Value { children, .. }) =
            self.typed_pairs.get_mut(&TypedPairKey::Value(parent))
        else {
            unreachable!("a semantic value pair owns its diagnostic children");
        };
        let old_capacity = children.capacity();
        reserve_f5b(children, 1, F5bCapacityLane::DiagnosticEdges)?;
        children.push(parent_edge);
        if children.capacity() != old_capacity {
            let added = children
                .capacity()
                .checked_sub(old_capacity)
                .and_then(|slots| slots.checked_mul(std::mem::size_of::<DiagnosticEdge>()))
                .expect("F5b diagnostic edge capacity fits usize");
            self.typed_pair_payload_bytes = self
                .typed_pair_payload_bytes
                .checked_add(added)
                .expect("F5b typed-pair payload accounting fits usize");
            #[cfg(test)]
            {
                self.independent_nested_capacities.diagnostic_edges = self
                    .independent_nested_capacities
                    .diagnostic_edges
                    .checked_add(added)
                    .expect("independent diagnostic-edge accounting fits usize");
            }
        }
        Ok(())
    }

    fn complete_diagnostic_delta(&mut self) -> Result<(), SolveAvailabilityError> {
        // §39 owns this phase.  Persistent entries retain only fixed outgoing
        // edges.  Reverse edges, SCC membership, and pending counts are
        // call-local scratch, so an old Complete child is only an O(1) seed.
        let pair_count = self.diagnostic_delta.len();
        if pair_count == 0 {
            return Ok(());
        }
        #[cfg(test)]
        {
            self.diagnostic_settle_visits = 0;
            self.diagnostic_internal_reverse_edge_visits = 0;
            self.diagnostic_scc_member_seed_scans = 0;
        }
        let mut edge_count = 0usize;
        for &key in &self.diagnostic_delta {
            let children = match self.typed_pairs.get(&TypedPairKey::Value(key)) {
                Some(TypedPairMemo::Value { children, .. }) => children,
                _ => unreachable!("diagnostic delta names value pairs"),
            };
            edge_count = edge_count
                .checked_add(
                    children
                        .iter()
                        .filter(|edge| self.diagnostic_delta_indices.contains_key(&edge.child))
                        .count(),
                )
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        }
        self.prepare_diagnostic_scratch(pair_count, edge_count)?;

        self.diagnostic_reverse_offsets.resize(pair_count + 1, 0);
        for &parent_key in &self.diagnostic_delta {
            let children = match self.typed_pairs.get(&TypedPairKey::Value(parent_key)) {
                Some(TypedPairMemo::Value { children, .. }) => children,
                _ => unreachable!("diagnostic parent remains a value pair"),
            };
            for edge in children {
                if let Some(&child) = self.diagnostic_delta_indices.get(&edge.child) {
                    self.diagnostic_reverse_offsets[child + 1] += 1;
                }
            }
        }
        for index in 1..=pair_count {
            self.diagnostic_reverse_offsets[index] += self.diagnostic_reverse_offsets[index - 1];
        }
        self.diagnostic_reverse_cursors
            .extend_from_slice(&self.diagnostic_reverse_offsets[..pair_count]);
        self.diagnostic_reverse_edges.resize(
            edge_count,
            DiagnosticReverseEdge {
                parent: 0,
                field: None,
            },
        );
        for (parent, &parent_key) in self.diagnostic_delta.iter().enumerate() {
            let children = match self.typed_pairs.get(&TypedPairKey::Value(parent_key)) {
                Some(TypedPairMemo::Value { children, .. }) => children,
                _ => unreachable!("diagnostic parent remains a value pair"),
            };
            for edge in children {
                if let Some(&child) = self.diagnostic_delta_indices.get(&edge.child) {
                    let cursor = self.diagnostic_reverse_cursors[child];
                    self.diagnostic_reverse_edges[cursor] = DiagnosticReverseEdge {
                        parent,
                        field: edge.field,
                    };
                    self.diagnostic_reverse_cursors[child] += 1;
                }
            }
        }

        // Iterative Kosaraju: first discover postorder over only delta edges,
        // then walk the scratch reverse graph.  No old entry participates.
        self.diagnostic_scc_indices.resize(pair_count, usize::MAX);
        self.diagnostic_reverse_cursors.clear();
        self.diagnostic_reverse_cursors.resize(pair_count, 0);
        for root in 0..pair_count {
            if self.diagnostic_reverse_cursors[root] != 0 {
                continue;
            }
            self.diagnostic_reverse_cursors[root] = 1;
            self.diagnostic_dfs_stack.push((root, 0));
            while let Some((node, child_position)) = self.diagnostic_dfs_stack.pop() {
                let key = self.diagnostic_delta[node];
                let children = match self.typed_pairs.get(&TypedPairKey::Value(key)) {
                    Some(TypedPairMemo::Value { children, .. }) => children,
                    _ => unreachable!("diagnostic DFS names value pairs"),
                };
                if child_position == children.len() {
                    self.diagnostic_finish_order.push(node);
                    continue;
                }
                self.diagnostic_dfs_stack.push((node, child_position + 1));
                if let Some(&child) = self
                    .diagnostic_delta_indices
                    .get(&children[child_position].child)
                {
                    if self.diagnostic_reverse_cursors[child] == 0 {
                        self.diagnostic_reverse_cursors[child] = 1;
                        self.diagnostic_dfs_stack.push((child, 0));
                    }
                }
            }
        }
        for &root in self.diagnostic_finish_order.iter().rev() {
            if self.diagnostic_scc_indices[root] != usize::MAX {
                continue;
            }
            let scc = self.diagnostic_scc_offsets.len();
            self.diagnostic_scc_offsets
                .push(self.diagnostic_scc_nodes.len());
            self.diagnostic_scc_indices[root] = scc;
            self.diagnostic_dfs_stack.push((root, 0));
            while let Some((node, reverse_position)) = self.diagnostic_dfs_stack.pop() {
                let start = self.diagnostic_reverse_offsets[node];
                let end = self.diagnostic_reverse_offsets[node + 1];
                if reverse_position == 0 {
                    self.diagnostic_scc_nodes.push(node);
                }
                if start + reverse_position == end {
                    continue;
                }
                self.diagnostic_dfs_stack.push((node, reverse_position + 1));
                let parent = self.diagnostic_reverse_edges[start + reverse_position].parent;
                if self.diagnostic_scc_indices[parent] == usize::MAX {
                    self.diagnostic_scc_indices[parent] = scc;
                    self.diagnostic_dfs_stack.push((parent, 0));
                }
            }
        }
        self.diagnostic_scc_offsets
            .push(self.diagnostic_scc_nodes.len());
        let scc_count = self.diagnostic_scc_offsets.len() - 1;

        // Kosaraju discovers members in graph-walk order. Rebuild its output
        // once into per-SCC slices ordered by dense delta index. The later
        // seed pass visits only the current SCC's members and never rescans
        // all delta pairs for every SCC.
        self.diagnostic_scc_offsets.clear();
        self.diagnostic_scc_offsets.resize(scc_count + 1, 0);
        for &scc in &self.diagnostic_scc_indices {
            self.diagnostic_scc_offsets[scc + 1] += 1;
        }
        for index in 1..=scc_count {
            self.diagnostic_scc_offsets[index] += self.diagnostic_scc_offsets[index - 1];
        }
        self.diagnostic_reverse_cursors.clear();
        self.diagnostic_reverse_cursors
            .extend_from_slice(&self.diagnostic_scc_offsets[..scc_count]);
        self.diagnostic_scc_nodes.clear();
        self.diagnostic_scc_nodes.resize(pair_count, 0);
        for node in 0..pair_count {
            let scc = self.diagnostic_scc_indices[node];
            let position = self.diagnostic_reverse_cursors[scc];
            self.diagnostic_scc_nodes[position] = node;
            self.diagnostic_reverse_cursors[scc] += 1;
        }
        self.diagnostic_scc_pending_children.resize(scc_count, 0);
        for parent in 0..pair_count {
            let parent_scc = self.diagnostic_scc_indices[parent];
            let key = self.diagnostic_delta[parent];
            let children = match self.typed_pairs.get(&TypedPairKey::Value(key)) {
                Some(TypedPairMemo::Value { children, .. }) => children,
                _ => unreachable!("diagnostic SCC names value pairs"),
            };
            for edge in children {
                if let Some(&child) = self.diagnostic_delta_indices.get(&edge.child) {
                    if self.diagnostic_scc_indices[child] != parent_scc {
                        self.diagnostic_scc_pending_children[parent_scc] += 1;
                    }
                }
            }
        }
        for scc in 0..scc_count {
            if self.diagnostic_scc_pending_children[scc] == 0 {
                self.diagnostic_scc_worklist.push_back(scc);
            }
        }

        // Condensed children are completed before their parents.  Within one
        // SCC §39 settles a member on its *first* bucket arrival.  Thus every
        // internal reverse edge expands at most once; there is no improving
        // witness/requeue path.  We retain every direct/external seed because
        // a single SCC-global seed is not sufficient for member-local minima.
        while let Some(scc) = self.diagnostic_scc_worklist.pop_front() {
            let start = self.diagnostic_scc_offsets[scc];
            let end = self.diagnostic_scc_offsets[scc + 1];
            let member_count = end - start;
            self.diagnostic_node_witnesses.resize(pair_count, None);

            // Scan this deterministic member slice exactly once. Direct and
            // external seeds are retained transiently until their shared d0
            // is known; the candidate lane grows at each insertion because
            // external/replay seed cardinality is not a startup invariant.
            self.diagnostic_bucket_candidates.clear();
            let mut minimum_seed_distance = None;
            for member_position in start..end {
                let node = self.diagnostic_scc_nodes[member_position];
                #[cfg(test)]
                {
                    self.diagnostic_scc_member_seed_scans += 1;
                }
                let key = self.diagnostic_delta[node];
                let direct_witness = match self.typed_pairs.get(&TypedPairKey::Value(key)) {
                    Some(TypedPairMemo::Value { direct_witness, .. }) => *direct_witness,
                    _ => unreachable!("diagnostic SCC names value pairs"),
                };
                if let Some(witness) = direct_witness {
                    self.push_diagnostic_seed(node, witness)?;
                    minimum_seed_distance = Some(
                        minimum_seed_distance.map_or(witness.distance, |current: u32| {
                            current.min(witness.distance)
                        }),
                    );
                }
                let child_count = match self.typed_pairs.get(&TypedPairKey::Value(key)) {
                    Some(TypedPairMemo::Value { children, .. }) => children.len(),
                    _ => unreachable!("diagnostic SCC names value pairs"),
                };
                for child_index in 0..child_count {
                    let edge = match self.typed_pairs.get(&TypedPairKey::Value(key)) {
                        Some(TypedPairMemo::Value { children, .. }) => children[child_index],
                        _ => unreachable!("diagnostic SCC names value pairs"),
                    };
                    if let Some(&child_node) = self.diagnostic_delta_indices.get(&edge.child) {
                        if self.diagnostic_scc_indices[child_node] == scc {
                            continue;
                        }
                    }
                    let child = match self.typed_pairs.get(&TypedPairKey::Value(edge.child)) {
                        Some(TypedPairMemo::Value {
                            completion: DiagnosticCompletion::Complete(witness),
                            ..
                        }) => *witness,
                        Some(TypedPairMemo::Value {
                            completion: DiagnosticCompletion::Pending,
                            ..
                        }) => unreachable!("old pending pair cannot cross constrain boundary"),
                        _ => unreachable!("diagnostic edge names an admitted value pair"),
                    };
                    if let Some(witness) = child
                        .map(|witness| Self::extend_witness(witness, edge))
                        .transpose()?
                    {
                        self.push_diagnostic_seed(node, witness)?;
                        minimum_seed_distance = Some(
                            minimum_seed_distance.map_or(witness.distance, |current: u32| {
                                current.min(witness.distance)
                            }),
                        );
                    }
                }
            }
            if let Some(d0) = minimum_seed_distance {
                // A simple path through an n-member SCC has at most n - 1
                // internal edges.  Anything farther cannot be the first
                // arrival of an unsettled member and is discarded before it
                // enters the bounded scratch FIFO.
                let maximum_distance = d0
                    .checked_add(
                        u32::try_from(member_count.saturating_sub(1))
                            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                    )
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                let bucket_count = member_count
                    .checked_mul(45)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                self.prepare_diagnostic_buckets(bucket_count)?;
                let seed_count = self.diagnostic_bucket_candidates.len();
                for seed in 0..seed_count {
                    self.link_diagnostic_bucket_candidate(seed, d0, maximum_distance)?;
                }

                for bucket in 0..bucket_count {
                    while let Some(candidate) = self.pop_diagnostic_bucket(bucket) {
                        if self.diagnostic_node_witnesses[candidate.node].is_some() {
                            continue;
                        }
                        self.diagnostic_node_witnesses[candidate.node] = Some(candidate.witness);
                        #[cfg(test)]
                        {
                            self.diagnostic_settle_visits += 1;
                        }
                        let reverse_start = self.diagnostic_reverse_offsets[candidate.node];
                        let reverse_end = self.diagnostic_reverse_offsets[candidate.node + 1];
                        for edge_index in reverse_start..reverse_end {
                            let reverse_edge = self.diagnostic_reverse_edges[edge_index];
                            if self.diagnostic_scc_indices[reverse_edge.parent] != scc {
                                continue;
                            }
                            #[cfg(test)]
                            {
                                self.diagnostic_internal_reverse_edge_visits += 1;
                            }
                            let witness = Self::extend_witness(
                                candidate.witness,
                                DiagnosticEdge {
                                    child: self.diagnostic_delta[candidate.node],
                                    field: reverse_edge.field,
                                },
                            )?;
                            self.push_diagnostic_bucket(
                                reverse_edge.parent,
                                witness,
                                d0,
                                maximum_distance,
                            )?;
                        }
                    }
                }
            }
            for member_position in start..end {
                let node = self.diagnostic_scc_nodes[member_position];
                let key = self.diagnostic_delta[node];
                let Some(TypedPairMemo::Value { completion, .. }) =
                    self.typed_pairs.get_mut(&TypedPairKey::Value(key))
                else {
                    unreachable!("diagnostic SCC writes value pairs");
                };
                *completion = DiagnosticCompletion::Complete(self.diagnostic_node_witnesses[node]);
            }
            for member_position in start..end {
                let child = self.diagnostic_scc_nodes[member_position];
                for edge in self.diagnostic_reverse_offsets[child]
                    ..self.diagnostic_reverse_offsets[child + 1]
                {
                    let parent_scc =
                        self.diagnostic_scc_indices[self.diagnostic_reverse_edges[edge].parent];
                    if parent_scc == scc {
                        continue;
                    }
                    let pending = &mut self.diagnostic_scc_pending_children[parent_scc];
                    *pending -= 1;
                    if *pending == 0 {
                        self.diagnostic_scc_worklist.push_back(parent_scc);
                    }
                }
            }
        }
        assert!(
            self.diagnostic_scc_pending_children
                .iter()
                .all(|pending| *pending == 0),
            "the delta condensation completes every new diagnostic entry"
        );
        self.clear_diagnostic_scratch();
        Ok(())
    }

    fn prepare_diagnostic_scratch(
        &mut self,
        pair_count: usize,
        edge_count: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let offset_count = pair_count
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        macro_rules! reserve_scratch {
            ($field:ident, $additional:expr, $lane:ident) => {
                reserve_f5b(&mut self.$field, $additional, F5bCapacityLane::$lane)?;
            };
        }
        reserve_scratch!(
            diagnostic_reverse_offsets,
            offset_count,
            DiagnosticReverseOffsets
        );
        reserve_scratch!(diagnostic_reverse_edges, edge_count, DiagnosticReverseEdges);
        reserve_scratch!(
            diagnostic_reverse_cursors,
            pair_count,
            DiagnosticReverseCursors
        );
        reserve_scratch!(diagnostic_dfs_stack, pair_count, DiagnosticDfsStack);
        reserve_scratch!(diagnostic_finish_order, pair_count, DiagnosticFinishOrder);
        reserve_scratch!(diagnostic_scc_indices, pair_count, DiagnosticSccIndices);
        reserve_scratch!(diagnostic_scc_nodes, pair_count, DiagnosticSccNodes);
        reserve_scratch!(diagnostic_scc_offsets, offset_count, DiagnosticSccOffsets);
        reserve_scratch!(
            diagnostic_scc_pending_children,
            pair_count,
            DiagnosticSccPendingChildren
        );
        reserve_scratch!(diagnostic_scc_worklist, pair_count, DiagnosticSccWorklist);
        reserve_scratch!(diagnostic_bucket_heads, pair_count, DiagnosticBucketHeads);
        reserve_scratch!(diagnostic_bucket_tails, pair_count, DiagnosticBucketTails);
        reserve_scratch!(
            diagnostic_node_witnesses,
            pair_count,
            DiagnosticNodeWitnesses
        );
        self.clear_diagnostic_completion_scratch();
        Ok(())
    }

    fn clear_diagnostic_scratch(&mut self) {
        self.diagnostic_delta.clear();
        self.diagnostic_delta_indices.clear();
        self.clear_diagnostic_completion_scratch();
    }

    fn clear_diagnostic_completion_scratch(&mut self) {
        self.diagnostic_reverse_offsets.clear();
        self.diagnostic_reverse_edges.clear();
        self.diagnostic_reverse_cursors.clear();
        self.diagnostic_dfs_stack.clear();
        self.diagnostic_finish_order.clear();
        self.diagnostic_scc_indices.clear();
        self.diagnostic_scc_nodes.clear();
        self.diagnostic_scc_offsets.clear();
        self.diagnostic_scc_pending_children.clear();
        self.diagnostic_scc_worklist.clear();
        self.diagnostic_bucket_heads.clear();
        self.diagnostic_bucket_tails.clear();
        self.diagnostic_bucket_candidates.clear();
        self.diagnostic_node_witnesses.clear();
    }

    fn prepare_diagnostic_buckets(
        &mut self,
        bucket_count: usize,
    ) -> Result<(), SolveAvailabilityError> {
        reserve_f5b(
            &mut self.diagnostic_bucket_heads,
            bucket_count,
            F5bCapacityLane::DiagnosticBucketHeads,
        )?;
        reserve_f5b(
            &mut self.diagnostic_bucket_tails,
            bucket_count,
            F5bCapacityLane::DiagnosticBucketTails,
        )?;
        self.diagnostic_bucket_heads.clear();
        self.diagnostic_bucket_tails.clear();
        self.diagnostic_bucket_heads.resize(bucket_count, None);
        self.diagnostic_bucket_tails.resize(bucket_count, None);
        Ok(())
    }

    fn push_diagnostic_seed(
        &mut self,
        node: usize,
        witness: DiagnosticWitness,
    ) -> Result<(), SolveAvailabilityError> {
        reserve_f5b(
            &mut self.diagnostic_bucket_candidates,
            1,
            F5bCapacityLane::DiagnosticBucketCandidates,
        )?;
        self.diagnostic_bucket_candidates
            .push(DiagnosticBucketCandidate {
                node,
                witness,
                next: None,
            });
        Ok(())
    }

    fn link_diagnostic_bucket_candidate(
        &mut self,
        candidate: usize,
        d0: u32,
        maximum_distance: u32,
    ) -> Result<(), SolveAvailabilityError> {
        let witness = self.diagnostic_bucket_candidates[candidate].witness;
        if witness.distance > maximum_distance {
            return Ok(());
        }
        let bucket = Self::diagnostic_bucket(witness, d0)?;
        self.diagnostic_bucket_candidates[candidate].next = None;
        if let Some(tail) = self.diagnostic_bucket_tails[bucket] {
            self.diagnostic_bucket_candidates[tail].next = Some(candidate);
        } else {
            self.diagnostic_bucket_heads[bucket] = Some(candidate);
        }
        self.diagnostic_bucket_tails[bucket] = Some(candidate);
        Ok(())
    }

    /// Add one event to its stable FIFO bucket.  Buckets are selected only by
    /// the observable §40 comparator; dense pair order is the insertion tie.
    fn push_diagnostic_bucket(
        &mut self,
        node: usize,
        witness: DiagnosticWitness,
        d0: u32,
        maximum_distance: u32,
    ) -> Result<(), SolveAvailabilityError> {
        if witness.distance > maximum_distance {
            return Ok(());
        }
        let candidate = self.diagnostic_bucket_candidates.len();
        self.push_diagnostic_seed(node, witness)?;
        self.link_diagnostic_bucket_candidate(candidate, d0, maximum_distance)
    }

    fn diagnostic_bucket(
        witness: DiagnosticWitness,
        d0: u32,
    ) -> Result<usize, SolveAvailabilityError> {
        let distance = usize::try_from(witness.distance - d0)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let kind = Self::error_rank(witness.kind);
        let kind = usize::from(kind.0)
            .checked_mul(3)
            .and_then(|rank| rank.checked_add(usize::from(kind.1)))
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        distance
            .checked_mul(45)
            .and_then(|offset| offset.checked_add(kind.checked_mul(5)?))
            .and_then(|offset| {
                offset.checked_add(usize::from(Self::field_rank(witness.first_field)))
            })
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    fn pop_diagnostic_bucket(&mut self, bucket: usize) -> Option<DiagnosticBucketCandidate> {
        let head = self.diagnostic_bucket_heads[bucket]?;
        let candidate = self.diagnostic_bucket_candidates[head];
        self.diagnostic_bucket_heads[bucket] = candidate.next;
        if candidate.next.is_none() {
            self.diagnostic_bucket_tails[bucket] = None;
        }
        Some(candidate)
    }

    fn extend_witness(
        witness: DiagnosticWitness,
        edge: DiagnosticEdge,
    ) -> Result<DiagnosticWitness, SolveAvailabilityError> {
        Ok(DiagnosticWitness {
            terminal: witness.terminal,
            kind: witness.kind,
            distance: witness
                .distance
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            first_field: edge.field.or(witness.first_field),
        })
    }

    fn error_rank(kind: SolverErrorKind) -> (u8, u8) {
        let SolverErrorKind::IncompatibleValue { lower, upper } = kind else {
            return (u8::MAX, u8::MAX);
        };
        (Self::shape_rank(lower), Self::shape_rank(upper))
    }

    const fn shape_rank(shape: ValueShape) -> u8 {
        match shape {
            ValueShape::Bottom => 0,
            ValueShape::Int => 1,
            ValueShape::Function => 2,
        }
    }

    const fn field_rank(field: Option<FunctionField>) -> u8 {
        match field {
            Some(FunctionField::Argument) => 0,
            Some(FunctionField::ArgumentEffect) => 1,
            Some(FunctionField::ResultEffect) => 2,
            Some(FunctionField::Result) => 3,
            None => 4,
        }
    }

    fn replay_witness(
        &mut self,
        key: CanonicalValuePairKey,
        occurrence: &ConstraintOccurrenceId,
        cause: &CauseId,
    ) -> Result<(), SolveAvailabilityError> {
        let Some(TypedPairMemo::Value {
            completion: DiagnosticCompletion::Complete(witness),
            ..
        }) = self.typed_pairs.get(&TypedPairKey::Value(key))
        else {
            unreachable!("constrain completes every root value pair");
        };
        if let Some(DiagnosticWitness {
            kind: SolverErrorKind::IncompatibleValue { lower, upper },
            ..
        }) = witness
        {
            self.report_incompatible(occurrence, cause, *lower, *upper)?;
        }
        Ok(())
    }

    fn apply_value_task(
        &mut self,
        key: CanonicalValuePairKey,
    ) -> Result<usize, SolveAvailabilityError> {
        let mut transitions = 0;
        match (key.lower, key.upper) {
            (ValueEndpointKey::ValueRow(lower), ValueEndpointKey::ValueRow(upper)) => {
                let lower_index = lower as usize;
                let upper_index = upper as usize;
                let minimum = self.value_levels[lower_index].min(self.value_levels[upper_index]);
                self.extrude_value_endpoint(ValueEndpointKey::ValueRow(lower), minimum)?;
                self.extrude_value_endpoint(ValueEndpointKey::ValueRow(upper), minimum)?;
                #[cfg(test)]
                {
                    self.typed_direct_edges += 1;
                }
                let old_lower_capacity = self.bounds[upper_index].direct_lower_rows.capacity();
                let old_upper_capacity = self.bounds[lower_index].direct_upper_rows.capacity();
                reserve_f5b(
                    &mut self.bounds[upper_index].direct_lower_rows,
                    1,
                    F5bCapacityLane::ValueDirectLower,
                )?;
                reserve_f5b(
                    &mut self.bounds[lower_index].direct_upper_rows,
                    1,
                    F5bCapacityLane::ValueDirectUpper,
                )?;
                self.bounds[upper_index].direct_lower_rows.push(lower);
                Self::record_bound_capacity_growth(
                    &mut self.bound_payload_bytes,
                    #[cfg(test)]
                    &mut self.independent_nested_capacities.value_direct_lower,
                    &mut self.execution_counters,
                    old_lower_capacity,
                    self.bounds[upper_index].direct_lower_rows.capacity(),
                    std::mem::size_of::<u32>(),
                );
                self.execution_counters.lower_bound_insertions += 1;
                self.bounds[lower_index].direct_upper_rows.push(upper);
                Self::record_bound_capacity_growth(
                    &mut self.bound_payload_bytes,
                    #[cfg(test)]
                    &mut self.independent_nested_capacities.value_direct_upper,
                    &mut self.execution_counters,
                    old_upper_capacity,
                    self.bounds[lower_index].direct_upper_rows.capacity(),
                    std::mem::size_of::<u32>(),
                );
                self.execution_counters.upper_bound_insertions += 1;
                let lower_len = self.bounds[lower_index].exact_non_variable_lowers.len();
                for item_index in 0..lower_len {
                    let item = self.bounds[lower_index].exact_non_variable_lowers[item_index];
                    self.execution_counters.lower_bound_replays += 1;
                    #[cfg(test)]
                    {
                        self.typed_transmission_attempts += 1;
                    }
                    let child = CanonicalValuePairKey {
                        lower: item,
                        upper: ValueEndpointKey::ValueRow(upper),
                    };
                    self.record_diagnostic_edge(key, child, None)?;
                    self.enqueue_task(LiveConstraintTask::Value(child))?;
                }
                let upper_len = self.bounds[upper_index].exact_non_variable_uppers.len();
                for item_index in 0..upper_len {
                    let item = self.bounds[upper_index].exact_non_variable_uppers[item_index];
                    self.execution_counters.upper_bound_replays += 1;
                    #[cfg(test)]
                    {
                        self.typed_transmission_attempts += 1;
                    }
                    let child = CanonicalValuePairKey {
                        lower: ValueEndpointKey::ValueRow(lower),
                        upper: item,
                    };
                    self.record_diagnostic_edge(key, child, None)?;
                    self.enqueue_task(LiveConstraintTask::Value(child))?;
                }
            }
            (atom, ValueEndpointKey::ValueRow(row)) => {
                let index = row as usize;
                let old_capacity = self.bounds[index].exact_non_variable_lowers.capacity();
                reserve_f5b(
                    &mut self.bounds[index].exact_non_variable_lowers,
                    1,
                    F5bCapacityLane::ValueExactLower,
                )?;
                self.bounds[index].exact_non_variable_lowers.push(atom);
                Self::record_bound_capacity_growth(
                    &mut self.bound_payload_bytes,
                    #[cfg(test)]
                    &mut self.independent_nested_capacities.value_exact_lower,
                    &mut self.execution_counters,
                    old_capacity,
                    self.bounds[index].exact_non_variable_lowers.capacity(),
                    std::mem::size_of::<ValueEndpointKey>(),
                );
                self.execution_counters.lower_bound_insertions += 1;
                #[cfg(test)]
                {
                    self.typed_exact_lower_memberships += 1;
                }
                if atom == ValueEndpointKey::IntPositive
                    && !std::mem::replace(&mut self.bounds[index].has_int_positive_lower, true)
                {
                    transitions += 1;
                }
                let upper_len = self.bounds[index].exact_non_variable_uppers.len();
                for item_index in 0..upper_len {
                    let item = self.bounds[index].exact_non_variable_uppers[item_index];
                    self.execution_counters.lower_bound_replays += 1;
                    #[cfg(test)]
                    {
                        self.typed_same_row_atom_intersections += 1;
                    }
                    let child = CanonicalValuePairKey {
                        lower: atom,
                        upper: item,
                    };
                    self.record_diagnostic_edge(key, child, None)?;
                    self.enqueue_task(LiveConstraintTask::Value(child))?;
                }
                let row_len = self.bounds[index].direct_upper_rows.len();
                for row_index in 0..row_len {
                    let upper = self.bounds[index].direct_upper_rows[row_index];
                    self.execution_counters.lower_bound_replays += 1;
                    #[cfg(test)]
                    {
                        self.typed_transmission_attempts += 1;
                    }
                    let child = CanonicalValuePairKey {
                        lower: atom,
                        upper: ValueEndpointKey::ValueRow(upper),
                    };
                    self.record_diagnostic_edge(key, child, None)?;
                    self.enqueue_task(LiveConstraintTask::Value(child))?;
                }
            }
            (ValueEndpointKey::ValueRow(row), atom) => {
                let index = row as usize;
                let old_capacity = self.bounds[index].exact_non_variable_uppers.capacity();
                reserve_f5b(
                    &mut self.bounds[index].exact_non_variable_uppers,
                    1,
                    F5bCapacityLane::ValueExactUpper,
                )?;
                self.bounds[index].exact_non_variable_uppers.push(atom);
                Self::record_bound_capacity_growth(
                    &mut self.bound_payload_bytes,
                    #[cfg(test)]
                    &mut self.independent_nested_capacities.value_exact_upper,
                    &mut self.execution_counters,
                    old_capacity,
                    self.bounds[index].exact_non_variable_uppers.capacity(),
                    std::mem::size_of::<ValueEndpointKey>(),
                );
                self.execution_counters.upper_bound_insertions += 1;
                #[cfg(test)]
                {
                    self.typed_exact_upper_memberships += 1;
                }
                let lower_len = self.bounds[index].exact_non_variable_lowers.len();
                for item_index in 0..lower_len {
                    let item = self.bounds[index].exact_non_variable_lowers[item_index];
                    self.execution_counters.lower_bound_replays += 1;
                    #[cfg(test)]
                    {
                        self.typed_same_row_atom_intersections += 1;
                    }
                    let child = CanonicalValuePairKey {
                        lower: item,
                        upper: atom,
                    };
                    self.record_diagnostic_edge(key, child, None)?;
                    self.enqueue_task(LiveConstraintTask::Value(child))?;
                }
                let row_len = self.bounds[index].direct_lower_rows.len();
                for row_index in 0..row_len {
                    let lower = self.bounds[index].direct_lower_rows[row_index];
                    self.execution_counters.upper_bound_replays += 1;
                    #[cfg(test)]
                    {
                        self.typed_transmission_attempts += 1;
                    }
                    let child = CanonicalValuePairKey {
                        lower: ValueEndpointKey::ValueRow(lower),
                        upper: atom,
                    };
                    self.record_diagnostic_edge(key, child, None)?;
                    self.enqueue_task(LiveConstraintTask::Value(child))?;
                }
            }
            _ => {}
        }
        Ok(transitions)
    }

    fn positive_function_children(
        store: &ConstraintStore,
        endpoint: ValueEndpointKey,
    ) -> Option<(Term, Term, Term, Term)> {
        let ValueEndpointKey::PositiveFunction(term) = endpoint else {
            return None;
        };
        match store
            .term_view(term)
            .expect("live Function remains branch-owned")
        {
            TermView::PositiveFunction {
                argument,
                argument_effect,
                result_effect,
                result,
            } => Some((argument, argument_effect, result_effect, result)),
            _ => unreachable!("positive endpoint preserves its Function tag"),
        }
    }

    fn negative_function_children(
        store: &ConstraintStore,
        endpoint: ValueEndpointKey,
    ) -> Option<(Term, Term, Term, Term)> {
        let ValueEndpointKey::NegativeFunction(term) = endpoint else {
            return None;
        };
        match store
            .term_view(term)
            .expect("live Function remains branch-owned")
        {
            TermView::NegativeFunction {
                argument,
                argument_effect,
                result_effect,
                result,
            } => Some((argument, argument_effect, result_effect, result)),
            _ => unreachable!("negative endpoint preserves its Function tag"),
        }
    }

    fn incompatible_value_shapes(key: CanonicalValuePairKey) -> Option<(ValueShape, ValueShape)> {
        let lower = match key.lower {
            ValueEndpointKey::IntPositive => ValueShape::Int,
            ValueEndpointKey::PositiveFunction(_) => ValueShape::Function,
            ValueEndpointKey::BottomPositive => ValueShape::Bottom,
            _ => return None,
        };
        let upper = match key.upper {
            ValueEndpointKey::TopNegative => return None,
            ValueEndpointKey::IntNegative => ValueShape::Int,
            ValueEndpointKey::NegativeFunction(_) => ValueShape::Function,
            ValueEndpointKey::BottomNegative => ValueShape::Bottom,
            _ => return None,
        };
        matches!(
            (lower, upper),
            (ValueShape::Int, ValueShape::Bottom)
                | (ValueShape::Int, ValueShape::Function)
                | (ValueShape::Function, ValueShape::Bottom)
                | (ValueShape::Function, ValueShape::Int)
        )
        .then_some((lower, upper))
    }

    fn report_incompatible(
        &mut self,
        occurrence: &ConstraintOccurrenceId,
        cause: &CauseId,
        lower: ValueShape,
        upper: ValueShape,
    ) -> Result<(), SolveAvailabilityError> {
        let kind = SolverErrorKind::IncompatibleValue { lower, upper };
        let key = (occurrence.clone(), kind);
        if !self.reported_errors.contains(&key) {
            reserve_f5b(
                &mut self.reported_errors,
                1,
                F5bCapacityLane::ReportedErrors,
            )?;
            reserve_f5b(&mut self.errors, 1, F5bCapacityLane::Errors)?;
            assert!(self.reported_errors.insert(key));
            self.errors.push(SolverError {
                occurrence: occurrence.clone(),
                cause: cause.clone(),
                kind,
            });
        }
        Ok(())
    }

    fn record_bound_capacity_growth(
        payload_bytes: &mut usize,
        #[cfg(test)] independent_lane_bytes: &mut usize,
        counters: &mut ProductionCounters,
        old_capacity: usize,
        new_capacity: usize,
        slot_size: usize,
    ) {
        if new_capacity != old_capacity {
            let delta = new_capacity
                .checked_sub(old_capacity)
                .and_then(|slots| slots.checked_mul(slot_size))
                .expect("F4 bound capacity growth fits usize");
            *payload_bytes = payload_bytes
                .checked_add(delta)
                .expect("F4 bound payload byte accounting fits usize");
            #[cfg(test)]
            {
                *independent_lane_bytes = independent_lane_bytes
                    .checked_add(delta)
                    .expect("independent bound lane accounting fits usize");
            }
            counters.bound_table_growths += 1;
            counters.bound_table_rebuilds += 1;
        }
    }

    fn execute_scc_plan(&mut self) -> Result<(), SolveAvailabilityError> {
        // The F2 plan is dependency-sink-first.  All three partition slices
        // stay borrowed for their complete phase; only durable route records
        // copy their identity after admission.
        macro_rules! sample_boundary {
            ($boundary:expr) => {
                Self::sample_f4_resource_parts(
                    &self.store,
                    &self.errors,
                    &self.reported_errors,
                    &self.cross_kind_components,
                    &self.live_components,
                    &self.bounds,
                    &self.effect_bounds,
                    &self.value_levels,
                    &self.effect_levels,
                    &self.value_metadata,
                    &self.effect_metadata,
                    &self.extrusion_stack,
                    &self.extrusion_value_marks,
                    &self.extrusion_effect_marks,
                    self.bound_payload_bytes,
                    &self.occurrence_exact_bounds,
                    &self.typed_pairs,
                    self.typed_pair_payload_bytes,
                    &self.typed_worklist,
                    &self.diagnostic_delta,
                    &self.diagnostic_delta_indices,
                    &self.diagnostic_reverse_offsets,
                    &self.diagnostic_reverse_edges,
                    &self.diagnostic_reverse_cursors,
                    &self.diagnostic_dfs_stack,
                    &self.diagnostic_finish_order,
                    &self.diagnostic_scc_indices,
                    &self.diagnostic_scc_nodes,
                    &self.diagnostic_scc_offsets,
                    &self.diagnostic_scc_pending_children,
                    &self.diagnostic_scc_worklist,
                    &self.diagnostic_bucket_heads,
                    &self.diagnostic_bucket_tails,
                    &self.diagnostic_bucket_candidates,
                    &self.diagnostic_node_witnesses,
                    &self.routed_uses,
                    &self.routed_use_positions,
                    &self.schemes,
                    &self.drafts,
                    self.current_closed_retained_bytes,
                    self.batch.counters.f2_batch_retained_bytes,
                    self.batch.component_term_positions.capacity(),
                    0,
                    &mut self.execution_counters,
                    #[cfg(test)]
                    &mut self.resource_boundary_samples,
                    #[cfg(test)]
                    $boundary,
                    #[cfg(test)]
                    &mut self.resource_ledger,
                    #[cfg(test)]
                    &self.independent_nested_capacities,
                )
            };
        }
        let components = self
            .batch
            .scc_components_in_dependency_first_order()
            .cloned()
            .collect::<Vec<_>>();
        for component in components {
            self.execution_counters.scc_execution_component_visits += 1;
            let internal_uses = self
                .batch
                .scc_component_internal_uses(&component)
                .expect("plan-owned component")
                .to_vec();
            for use_index in 0..internal_uses.len() {
                let id = internal_uses[use_index].clone();
                #[cfg(test)]
                if let Some(observer) = self.ordering_observer.as_mut() {
                    observer.record(|| ExecutionEvent::InternalUse(id.clone()));
                }
                let transitions = self.route_internal(&id)?;
                self.execution_counters
                    .scc_execution_internal_use_connections += 1;
                #[cfg(test)]
                {
                    self.summary_false_to_true_transitions += transitions;
                }
                #[cfg(not(test))]
                let _ = transitions;
                sample_boundary!(ResourceBoundary::InternalRoute);
            }
            let members = self
                .batch
                .scc_component_members(&component)
                .expect("plan-owned component");
            #[cfg(test)]
            {
                self.summary_reads += members.len();
            }
            self.drafts.clear();
            // `clear` is a reuse boundary: it changes live draft ownership
            // without changing capacity, so sample it independently.
            sample_boundary!(ResourceBoundary::DraftScratchClear);
            let mut generalization_drafts = Vec::with_capacity(members.len());
            for member_index in 0..members.len() {
                let member = &members[member_index];
                self.execution_counters.scc_execution_draft_members += 1;
                #[cfg(test)]
                if let Some(observer) = self.ordering_observer.as_mut() {
                    observer.record(|| ExecutionEvent::Drafted(member.clone()));
                }
                generalization_drafts.push(self.generalization_draft(member)?);
            }
            self.execution_counters
                .scc_execution_drafts_visible_barriers += 1;
            #[cfg(test)]
            if let Some(observer) = self.ordering_observer.as_mut() {
                observer.record(|| {
                    ExecutionEvent::DraftsVisible(component.clone(), generalization_drafts.len())
                });
            }
            for plan in &generalization_drafts {
                let old_capacity = self.drafts.capacity();
                #[cfg(test)]
                let inject_finalization_failure = if self.injected_finalization_failure_after
                    == Some(self.successful_finalizations)
                {
                    self.injected_finalization_failure_after = None;
                    true
                } else {
                    false
                };
                #[cfg(test)]
                let finalized = Self::finalize_generalization_draft(
                    self.finalization
                        .as_mut()
                        .expect("F4 finalization session remains live before finish"),
                    plan,
                    inject_finalization_failure,
                )?;
                #[cfg(not(test))]
                let finalized = Self::finalize_generalization_draft(
                    self.finalization
                        .as_mut()
                        .expect("F4 finalization session remains live before finish"),
                    plan,
                )?;
                let (draft, checkpoint) = finalized.into_parts();
                assert_eq!(
                    checkpoint.retained_bytes_before(),
                    self.current_closed_retained_bytes,
                    "successful solver finalizations form one uninterrupted accounting epoch"
                );
                let semantic_without_closed = self
                    .execution_counters
                    .semantic_arena_retained_bytes
                    .checked_sub(self.current_closed_retained_bytes)
                    .expect("latest F4 semantic sample includes closed storage once");
                let session_without_closed = self
                    .execution_counters
                    .inference_session_retained_bytes
                    .checked_sub(self.current_closed_retained_bytes)
                    .expect("latest F4 session sample includes closed storage once");
                self.execution_counters.semantic_arena_peak_bytes =
                    self.execution_counters.semantic_arena_peak_bytes.max(
                        semantic_without_closed
                            .checked_add(checkpoint.peak_bytes_during_call())
                            .expect("F4 closed finalization semantic peak fits usize"),
                    );
                self.execution_counters.inference_session_peak_bytes =
                    self.execution_counters.inference_session_peak_bytes.max(
                        session_without_closed
                            .checked_add(checkpoint.peak_bytes_during_call())
                            .expect("F4 closed finalization session peak fits usize"),
                    );
                self.current_closed_retained_bytes = checkpoint.retained_bytes_after();
                self.drafts.push(DraftScheme(draft));
                #[cfg(test)]
                {
                    self.successful_finalizations += 1;
                }
                if self.drafts.capacity() != old_capacity {
                    self.execution_counters.draft_scratch_growths += 1;
                }
                sample_boundary!(ResourceBoundary::DraftMember);
            }
            self.execution_counters.draft_scratch_max_len = self
                .execution_counters
                .draft_scratch_max_len
                .max(self.drafts.len());
            for (ordinal, member) in members.iter().enumerate() {
                self.execution_counters.scc_execution_draft_lookups += 1;
                self.execution_counters.scc_execution_finalized_members += 1;
                self.execution_counters.scc_execution_installed_members += 1;
                let draft = self
                    .drafts
                    .get(ordinal)
                    .cloned()
                    .expect("draft view is ordinal-indexed")
                    .0;
                let verified = Self::verified_scheme_definition(&self.batch, member);
                assert!(
                    self.schemes[verified.position].replace(draft).is_none(),
                    "scheme installed once"
                );
                #[cfg(test)]
                if let Some(observer) = self.ordering_observer.as_mut() {
                    observer.record(|| ExecutionEvent::Installed(verified.record.root.clone()));
                }
                // Finalized schemes and drafts coexist at each direct move.
                sample_boundary!(ResourceBoundary::SchemeInstall);
            }
            let incoming_uses = self
                .batch
                .scc_component_incoming_uses(&component)
                .expect("plan-owned component")
                .to_vec();
            for use_index in 0..incoming_uses.len() {
                let id = incoming_uses[use_index].clone();
                #[cfg(test)]
                if let Some(observer) = self.ordering_observer.as_mut() {
                    // The scale observer has capacity zero.  Do not perform a
                    // test-only batch lookup, scheme read, or event build for
                    // an omitted event: production route probes are I + X.
                    if observer.has_capacity() {
                        let use_record = self.batch.definition_use(&id).expect("plan-owned use");
                        let position = use_record.target.ordinal() as usize;
                        let kind = match Self::decode_closed_scheme(
                            self.finalization
                                .as_ref()
                                .expect("F4 finalization session remains live before finish"),
                            self.schemes[position]
                                .as_ref()
                                .expect("incoming observes finalized component scheme"),
                        ) {
                            Ok(GeneralizationDraft {
                                predicate: F5cPositive::Int,
                                ..
                            }) => ObservedIncomingKind::Int,
                            Ok(GeneralizationDraft {
                                predicate: F5cPositive::Bottom,
                                ..
                            }) => ObservedIncomingKind::BottomTrivial,
                            Ok(_) => ObservedIncomingKind::Structured,
                            Err(_) => panic!("session-owned scheme remains decodable"),
                        };
                        observer.record(|| ExecutionEvent::IncomingUse(id.clone(), kind));
                    } else {
                        observer.omit();
                    }
                }
                let transitions = self.route_incoming(&id)?;
                self.execution_counters
                    .scc_execution_incoming_instantiations += 1;
                #[cfg(test)]
                {
                    self.summary_false_to_true_transitions += transitions;
                }
                #[cfg(not(test))]
                let _ = transitions;
                sample_boundary!(ResourceBoundary::IncomingRoute);
            }
        }
        Ok(())
    }

    fn route_internal(&mut self, id: &DefinitionUseId) -> Result<usize, SolveAvailabilityError> {
        let use_record = Self::validated_route_use(&self.batch, id)?.clone();
        let root = self
            .batch
            .component_term_at(use_record.target_root_component);
        let value = self.batch.component_term_at(use_record.use_value_component);
        let key = CanonicalValuePairKey {
            lower: ValueEndpointKey::ValueRow(
                self.live_components[use_record.target_root_component].ordinal,
            ),
            upper: ValueEndpointKey::ValueRow(
                self.live_components[use_record.use_value_component].ordinal,
            ),
        };
        self.route(id, &use_record, root, value, key, RoutedUseKind::Internal)
    }

    fn decode_positive_scheme(
        view: yu_types::ClosedValueSchemeView<'_>,
        id: yu_types::PositiveValueId,
    ) -> Result<F5cPositive, SolveAvailabilityError> {
        match view
            .positive_value(id)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?
        {
            PositiveValueView::Bottom => Ok(F5cPositive::Bottom),
            PositiveValueView::Int => Ok(F5cPositive::Int),
            PositiveValueView::Quantified(q) => Ok(F5cPositive::Quantified(q.ordinal())),
            PositiveValueView::Recursive(r) => Ok(F5cPositive::Recursive(r.ordinal())),
            PositiveValueView::Function {
                argument,
                argument_effect,
                result_effect,
                result,
            } => Ok(F5cPositive::Function {
                argument: Box::new(Self::decode_negative_scheme(view, argument)?),
                argument_effect: match view.negative_effect(argument_effect) {
                    Ok(yu_types::NegativeEffectView::Empty) => F5cNegativeEffect::Empty,
                    Err(_) => return Err(SolveAvailabilityError::IdentityExhausted),
                },
                result_effect: match view.positive_effect(result_effect) {
                    Ok(yu_types::PositiveEffectView::Bottom) => F5cPositiveEffect::Bottom,
                    Err(_) => return Err(SolveAvailabilityError::IdentityExhausted),
                },
                result: Box::new(Self::decode_positive_scheme(view, result)?),
            }),
            PositiveValueView::Union(values) => values
                .iter()
                .map(|value| Self::decode_positive_scheme(view, *value))
                .collect::<Result<Vec<_>, _>>()
                .map(F5cPositive::Union),
        }
    }

    fn decode_negative_scheme(
        view: yu_types::ClosedValueSchemeView<'_>,
        id: yu_types::NegativeValueId,
    ) -> Result<F5cNegative, SolveAvailabilityError> {
        match view
            .negative_value(id)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?
        {
            NegativeValueView::Top => Ok(F5cNegative::Top),
            NegativeValueView::Bottom => Ok(F5cNegative::Bottom),
            NegativeValueView::Int => Ok(F5cNegative::Int),
            NegativeValueView::Quantified(q) => Ok(F5cNegative::Quantified(q.ordinal())),
            NegativeValueView::Recursive(r) => Ok(F5cNegative::Recursive(r.ordinal())),
            NegativeValueView::Function {
                argument,
                argument_effect,
                result_effect,
                result,
            } => Ok(F5cNegative::Function {
                argument: Box::new(Self::decode_positive_scheme(view, argument)?),
                argument_effect: match view.positive_effect(argument_effect) {
                    Ok(yu_types::PositiveEffectView::Bottom) => F5cPositiveEffect::Bottom,
                    Err(_) => return Err(SolveAvailabilityError::IdentityExhausted),
                },
                result_effect: match view.negative_effect(result_effect) {
                    Ok(yu_types::NegativeEffectView::Empty) => F5cNegativeEffect::Empty,
                    Err(_) => return Err(SolveAvailabilityError::IdentityExhausted),
                },
                result: Box::new(Self::decode_negative_scheme(view, result)?),
            }),
            NegativeValueView::Intersection(values) => values
                .iter()
                .map(|value| Self::decode_negative_scheme(view, *value))
                .collect::<Result<Vec<_>, _>>()
                .map(F5cNegative::Intersection),
        }
    }

    fn decode_closed_scheme(
        finalization: &ClosedTypeFinalizationSession,
        scheme: &ClosedValueScheme,
    ) -> Result<GeneralizationDraft, SolveAvailabilityError> {
        let view = finalization
            .scheme_view(scheme)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let quantifier_count = view.quantifier_count();
        let predicate = Self::decode_positive_scheme(view, view.predicate())?;
        let mut recursive_bounds = Vec::with_capacity(view.recursive_bounds().len());
        for bound in view.recursive_bounds() {
            let NeutralValueView::Bounds { lower, upper } = view
                .neutral_value(bound.bounds())
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            recursive_bounds.push(F5cRecursiveBound {
                ordinal: bound.binder().ordinal(),
                lower: Self::decode_positive_scheme(view, lower)?,
                upper: Self::decode_negative_scheme(view, upper)?,
            });
        }
        Ok(GeneralizationDraft {
            quantifier_count,
            recursive_bounds,
            predicate,
        })
    }

    fn instantiate_positive(
        &mut self,
        value: &F5cPositive,
        substitution: &HashMap<u32, u32>,
    ) -> Result<Term, SolveAvailabilityError> {
        match value {
            F5cPositive::Bottom => self.positive_bottom_term(),
            F5cPositive::Int => Ok(self.batch.collected_leaf_term(Leaf::IntPositive)),
            F5cPositive::Quantified(ordinal) | F5cPositive::Recursive(ordinal) => {
                let row = substitution
                    .get(ordinal)
                    .copied()
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                self.live_value_term(Polarity::Positive, row)
            }
            F5cPositive::Variable(_) => Err(SolveAvailabilityError::IdentityExhausted),
            F5cPositive::Union(_) => Err(SolveAvailabilityError::IdentityExhausted),
            F5cPositive::Function {
                argument, result, ..
            } => {
                let argument = self.instantiate_negative(argument, substitution)?;
                let result = self.instantiate_positive(result, substitution)?;
                let argument_effect = self.batch.collected_leaf_term(Leaf::EmptyEffectNegative);
                let result_effect = self.batch.collected_leaf_term(Leaf::EffectBottomPositive);
                self.positive_function_term(argument, argument_effect, result_effect, result)
            }
        }
    }

    fn instantiate_positive_parts(
        &mut self,
        value: &F5cPositive,
        substitution: &HashMap<u32, u32>,
    ) -> Result<Vec<Term>, SolveAvailabilityError> {
        match value {
            F5cPositive::Union(values) => {
                values
                    .iter()
                    .try_fold(Vec::with_capacity(values.len()), |mut terms, value| {
                        terms.extend(self.instantiate_positive_parts(value, substitution)?);
                        Ok(terms)
                    })
            }
            _ => Ok(vec![self.instantiate_positive(value, substitution)?]),
        }
    }

    fn instantiate_negative(
        &mut self,
        value: &F5cNegative,
        substitution: &HashMap<u32, u32>,
    ) -> Result<Term, SolveAvailabilityError> {
        match value {
            F5cNegative::Top => self.negative_top_term(),
            F5cNegative::Bottom => self.negative_bottom_term(),
            F5cNegative::Int => Ok(self.batch.collected_leaf_term(Leaf::IntNegative)),
            F5cNegative::Quantified(ordinal) | F5cNegative::Recursive(ordinal) => {
                let row = substitution
                    .get(ordinal)
                    .copied()
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                self.live_value_term(Polarity::Negative, row)
            }
            F5cNegative::Variable(_) => Err(SolveAvailabilityError::IdentityExhausted),
            F5cNegative::Intersection(_) => Err(SolveAvailabilityError::IdentityExhausted),
            F5cNegative::Function {
                argument, result, ..
            } => {
                let argument = self.instantiate_positive(argument, substitution)?;
                let result = self.instantiate_negative(result, substitution)?;
                let argument_effect = self.batch.collected_leaf_term(Leaf::EffectBottomPositive);
                let result_effect = self.batch.collected_leaf_term(Leaf::EmptyEffectNegative);
                self.negative_function_term(argument, argument_effect, result_effect, result)
            }
        }
    }

    fn instantiate_negative_parts(
        &mut self,
        value: &F5cNegative,
        substitution: &HashMap<u32, u32>,
    ) -> Result<Vec<Term>, SolveAvailabilityError> {
        match value {
            F5cNegative::Intersection(values) => {
                values
                    .iter()
                    .try_fold(Vec::with_capacity(values.len()), |mut terms, value| {
                        terms.extend(self.instantiate_negative_parts(value, substitution)?);
                        Ok(terms)
                    })
            }
            _ => Ok(vec![self.instantiate_negative(value, substitution)?]),
        }
    }

    /// A closed positive union has no single live Term representation in the
    /// F5c arena. Its canonical first member is therefore the intentional
    /// public representative fact; every remaining normalized member is a
    /// private lower-bound edge under the same source route and provenance.
    fn route_many(
        &mut self,
        id: &DefinitionUseId,
        use_record: &DefinitionUse,
        lowers: Vec<Term>,
        upper: Term,
        kind: RoutedUseKind,
    ) -> Result<usize, SolveAvailabilityError> {
        let mut lowers = lowers.into_iter();
        let first = lowers
            .next()
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let key = CanonicalValuePairKey {
            lower: self.value_endpoint(first, Polarity::Positive),
            upper: ValueEndpointKey::ValueRow(
                self.live_components[use_record.use_value_component].ordinal,
            ),
        };
        // The source use owns one public route/fact. Remaining normalized
        // members are private decomposition edges under that same cause.
        let mut transitions = self.route(id, use_record, first, upper, key, kind)?;
        let occurrence_id = ConstraintOccurrenceId::new(use_record.occurrence.clone(), 0);
        let cause = CauseId::for_occurrence(occurrence_id.clone());
        for lower in lowers {
            let key = CanonicalValuePairKey {
                lower: self.value_endpoint(lower, Polarity::Positive),
                upper: ValueEndpointKey::ValueRow(
                    self.live_components[use_record.use_value_component].ordinal,
                ),
            };
            transitions += self.constrain_live_value(key, &occurrence_id, &cause)?;
        }
        Ok(transitions)
    }

    fn instantiate_and_route(
        &mut self,
        id: &DefinitionUseId,
        use_record: &DefinitionUse,
        draft: &GeneralizationDraft,
        value: Term,
    ) -> Result<usize, SolveAvailabilityError> {
        let mut substitution = HashMap::new();
        for ordinal in 0..draft.quantifier_count {
            let fresh = self.fresh_value_at_level(use_record.use_level)?;
            substitution.insert(ordinal, fresh);
        }
        for bound in &draft.recursive_bounds {
            if !substitution.contains_key(&bound.ordinal) {
                let fresh = self.fresh_value_at_level(use_record.use_level)?;
                substitution.insert(bound.ordinal, fresh);
            }
        }
        let occurrence_id = ConstraintOccurrenceId::new(use_record.occurrence.clone(), 0);
        let cause = CauseId::for_occurrence(occurrence_id.clone());
        for bound in &draft.recursive_bounds {
            let row = substitution
                .get(&bound.ordinal)
                .copied()
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            for lower in self.instantiate_positive_parts(&bound.lower, &substitution)? {
                let lower_key = CanonicalValuePairKey {
                    lower: self.value_endpoint(lower, Polarity::Positive),
                    upper: ValueEndpointKey::ValueRow(row),
                };
                self.constrain_live_value(lower_key, &occurrence_id, &cause)?;
            }
            for upper in self.instantiate_negative_parts(&bound.upper, &substitution)? {
                let upper_key = CanonicalValuePairKey {
                    lower: ValueEndpointKey::ValueRow(row),
                    upper: self.value_endpoint(upper, Polarity::Negative),
                };
                self.constrain_live_value(upper_key, &occurrence_id, &cause)?;
            }
        }
        let predicates = self.instantiate_positive_parts(&draft.predicate, &substitution)?;
        if predicates.len() == 1 {
            let predicate = predicates.into_iter().next().expect("one predicate");
            let key = CanonicalValuePairKey {
                lower: self.value_endpoint(predicate, Polarity::Positive),
                upper: ValueEndpointKey::ValueRow(
                    self.live_components[use_record.use_value_component].ordinal,
                ),
            };
            self.route(
                id,
                use_record,
                predicate,
                value,
                key,
                RoutedUseKind::IncomingStructured,
            )
        } else {
            self.route_many(
                id,
                use_record,
                predicates,
                value,
                RoutedUseKind::IncomingStructured,
            )
        }
    }

    fn route_incoming(&mut self, id: &DefinitionUseId) -> Result<usize, SolveAvailabilityError> {
        let use_record = Self::validated_route_use(&self.batch, id)?.clone();
        let position = use_record.target.ordinal() as usize;
        let scheme = self.schemes[position]
            .as_ref()
            .expect("incoming observes finalized component scheme")
            .clone();
        let value = self.batch.component_term_at(use_record.use_value_component);
        let draft = Self::decode_closed_scheme(
            self.finalization
                .as_ref()
                .expect("finalization remains live"),
            &scheme,
        )?;
        match draft.predicate.clone() {
            F5cPositive::Bottom => {
                self.execution_counters
                    .scc_execution_bottom_trivial_instantiations += 1;
                reserve_f5b(
                    &mut self.routed_use_positions,
                    1,
                    F5bCapacityLane::RoutedUsePositions,
                )?;
                reserve_f5b(&mut self.routed_uses, 1, F5bCapacityLane::RoutedUses)?;
                assert!(
                    self.routed_use_positions.insert(id.clone()),
                    "each use routes once"
                );
                let old_capacity = self.routed_uses.capacity();
                self.routed_uses.push(RoutedUseProvenance {
                    use_id: id.clone(),
                    fact: None,
                    kind: RoutedUseKind::IncomingBottomTrivial,
                });
                if self.routed_uses.capacity() != old_capacity {
                    self.execution_counters.routed_use_provenance_growths += 1;
                }
                Ok(0)
            }
            F5cPositive::Int => {
                self.execution_counters
                    .scc_execution_int_instantiation_facts += 1;
                let lower = self.batch.collected_leaf_term(Leaf::IntPositive);
                let key = CanonicalValuePairKey {
                    lower: ValueEndpointKey::IntPositive,
                    upper: ValueEndpointKey::ValueRow(
                        self.live_components[use_record.use_value_component].ordinal,
                    ),
                };
                self.route(
                    id,
                    &use_record,
                    lower,
                    value,
                    key,
                    RoutedUseKind::IncomingInt,
                )
            }
            F5cPositive::Function { .. }
            | F5cPositive::Quantified(_)
            | F5cPositive::Recursive(_)
            | F5cPositive::Union(_)
            | F5cPositive::Variable(_) => {
                self.instantiate_and_route(id, &use_record, &draft, value)
            }
        }
    }

    fn route(
        &mut self,
        id: &DefinitionUseId,
        use_record: &DefinitionUse,
        lower: Term,
        upper: Term,
        key: CanonicalValuePairKey,
        kind: RoutedUseKind,
    ) -> Result<usize, SolveAvailabilityError> {
        // Route provenance is logically coupled to fact admission: reserve
        // both durable route lanes before the transaction can publish a fact.
        reserve_f5b(
            &mut self.routed_use_positions,
            1,
            F5bCapacityLane::RoutedUsePositions,
        )?;
        reserve_f5b(&mut self.routed_uses, 1, F5bCapacityLane::RoutedUses)?;
        assert!(
            !self.routed_use_positions.contains(id),
            "each use routes once"
        );
        let occurrence_id = ConstraintOccurrenceId::new(use_record.occurrence.clone(), 0);
        let occurrence = ConstraintOccurrence {
            cause: CauseId::for_occurrence(occurrence_id.clone()),
            id: occurrence_id,
            lower: lower.clone(),
            upper: upper.clone(),
        };
        let receipt = {
            let mut transaction = self.store.transaction();
            transaction.admit(&occurrence)
        }
        .map_err(SolveAvailabilityError::from)?;
        let fact = receipt.fact();
        self.store
            .record_provenance(receipt)
            .map_err(SolveAvailabilityError::from)?;
        let transitions = self.constrain_live_value(key, &occurrence.id, &occurrence.cause)?;
        assert!(
            self.routed_use_positions.insert(id.clone()),
            "each use routes once"
        );
        let old_capacity = self.routed_uses.capacity();
        self.routed_uses.push(RoutedUseProvenance {
            use_id: id.clone(),
            fact: Some(fact),
            kind,
        });
        if self.routed_uses.capacity() != old_capacity {
            self.execution_counters.routed_use_provenance_growths += 1;
        }
        Ok(transitions)
    }

    /// Route provenance is an atomic admission precondition.  It must be
    /// checked before route uniqueness, counters, facts, bounds, or durable
    /// provenance can observe the use.
    fn validated_route_use<'a>(
        batch: &'a ConstraintBatch,
        id: &DefinitionUseId,
    ) -> Result<&'a DefinitionUse, SolveAvailabilityError> {
        let use_record = batch.definition_use(id).expect("plan-owned use");
        (use_record.cause.id() == id)
            .then_some(use_record)
            .ok_or(SolveAvailabilityError::CauseMismatch)
    }

    fn generalization_draft(
        &self,
        definition: &DefinitionOrderId,
    ) -> Result<GeneralizationDraft, SolveAvailabilityError> {
        let verified = Self::verified_scheme_definition(&self.batch, definition);
        let component = self
            .batch
            .root_component_positions
            .get(&verified.record.root)
            .expect("definition root retains its immutable component recipe")
            .component;
        let row = self.live_components[component].ordinal as usize;
        F5cGeneralizer::new(self).build(row as u32)
    }

    fn finalize_generalization_draft(
        finalization: &mut ClosedTypeFinalizationSession,
        draft: &GeneralizationDraft,
        #[cfg(test)] inject_finalization_failure: bool,
    ) -> Result<ClosedSchemeFinalization, SolveAvailabilityError> {
        fn positive<'tx>(
            finalizer: &mut ClosedTypeFinalizer<'tx>,
            value: &F5cPositive,
            quantifiers: &[yu_types::DraftQuantifierId<'tx>],
            recursive_binders: &[yu_types::DraftRecursiveBinderId<'tx>],
        ) -> Result<DraftPositiveValueId<'tx>, ClosedTypeFinalizeError> {
            match value {
                F5cPositive::Bottom => finalizer.positive_bottom(),
                F5cPositive::Int => finalizer.positive_int(),
                F5cPositive::Variable(_) => Err(ClosedTypeFinalizeError::InvalidDraft),
                F5cPositive::Quantified(ordinal) => {
                    finalizer.positive_quantified(quantifiers[*ordinal as usize])
                }
                F5cPositive::Recursive(ordinal) => {
                    let index = (*ordinal - quantifiers.len() as u32) as usize;
                    finalizer.positive_recursive(recursive_binders[index])
                }
                F5cPositive::Union(values) => {
                    let values = values
                        .iter()
                        .map(|value| positive(finalizer, value, quantifiers, recursive_binders))
                        .collect::<Result<Vec<_>, _>>()?;
                    finalizer.positive_union(&values)
                }
                F5cPositive::Function {
                    argument, result, ..
                } => {
                    let argument = negative(finalizer, argument, quantifiers, recursive_binders)?;
                    let argument_effect = finalizer.negative_effect_empty()?;
                    let result_effect = finalizer.positive_effect_bottom()?;
                    let result = positive(finalizer, result, quantifiers, recursive_binders)?;
                    finalizer.positive_function(argument, argument_effect, result_effect, result)
                }
            }
        }
        fn negative<'tx>(
            finalizer: &mut ClosedTypeFinalizer<'tx>,
            value: &F5cNegative,
            quantifiers: &[yu_types::DraftQuantifierId<'tx>],
            recursive_binders: &[yu_types::DraftRecursiveBinderId<'tx>],
        ) -> Result<DraftNegativeValueId<'tx>, ClosedTypeFinalizeError> {
            match value {
                F5cNegative::Top => finalizer.negative_top(),
                F5cNegative::Bottom => finalizer.negative_bottom(),
                F5cNegative::Int => finalizer.negative_int(),
                F5cNegative::Variable(_) => Err(ClosedTypeFinalizeError::InvalidDraft),
                F5cNegative::Quantified(ordinal) => {
                    finalizer.negative_quantified(quantifiers[*ordinal as usize])
                }
                F5cNegative::Recursive(ordinal) => {
                    let index = (*ordinal - quantifiers.len() as u32) as usize;
                    finalizer.negative_recursive(recursive_binders[index])
                }
                F5cNegative::Intersection(values) => {
                    let values = values
                        .iter()
                        .map(|value| negative(finalizer, value, quantifiers, recursive_binders))
                        .collect::<Result<Vec<_>, _>>()?;
                    finalizer.negative_intersection(&values)
                }
                F5cNegative::Function {
                    argument, result, ..
                } => {
                    let argument = positive(finalizer, argument, quantifiers, recursive_binders)?;
                    let argument_effect = finalizer.positive_effect_bottom()?;
                    let result_effect = finalizer.negative_effect_empty()?;
                    let result = negative(finalizer, result, quantifiers, recursive_binders)?;
                    finalizer.negative_function(argument, argument_effect, result_effect, result)
                }
            }
        }

        finalization
            .finalize_scheme(|finalizer| {
                #[cfg(test)]
                if inject_finalization_failure {
                    return Err(ClosedTypeFinalizeError::IdentityExhausted);
                }
                // The finalizer validates dense Q ordinals and disjoint R
                // ordinals.  R occupies the numeric range immediately after Q.
                let quantifiers = (0..draft.quantifier_count)
                    .map(|ordinal| finalizer.quantifier(ordinal))
                    .collect::<Vec<_>>();
                let recursive_binders = draft
                    .recursive_bounds
                    .iter()
                    .map(|bound| finalizer.recursive_binder(bound.ordinal))
                    .collect::<Vec<_>>();
                let mut recursive_bounds = Vec::with_capacity(draft.recursive_bounds.len());
                for bound in &draft.recursive_bounds {
                    let binder = recursive_binders[recursive_bounds.len()];
                    let lower =
                        positive(finalizer, &bound.lower, &quantifiers, &recursive_binders)?;
                    let upper =
                        negative(finalizer, &bound.upper, &quantifiers, &recursive_binders)?;
                    let neutral = finalizer.neutral_bounds(lower, upper)?;
                    recursive_bounds.push(finalizer.recursive_bound(binder, neutral)?);
                }
                let predicate = positive(
                    finalizer,
                    &draft.predicate,
                    &quantifiers,
                    &recursive_binders,
                )?;
                finalizer.set_scheme(draft.quantifier_count, &recursive_bounds, predicate)
            })
            .map_err(Self::map_finalization_error)
    }

    #[cfg(test)]
    fn generalize(
        batch: &ConstraintBatch,
        bounds: &[VariableBounds],
        live_components: &[LiveComponentEndpoint],
        finalization: &mut ClosedTypeFinalizationSession,
        definition: &DefinitionOrderId,
        #[cfg(test)] summary_reads: &mut usize,
        #[cfg(test)] inject_finalization_failure: bool,
    ) -> Result<ClosedSchemeFinalization, SolveAvailabilityError> {
        let verified = Self::verified_scheme_definition(batch, definition);
        let component = batch
            .root_component_positions
            .get(&verified.record.root)
            .expect("definition root retains its immutable component recipe")
            .component;
        let row = live_components[component].ordinal as usize;
        #[cfg(test)]
        {
            *summary_reads += 1;
        }
        finalization
            .finalize_scheme(|finalizer| {
                #[cfg(test)]
                if inject_finalization_failure {
                    return Err(ClosedTypeFinalizeError::IdentityExhausted);
                }
                let predicate = if bounds[row].has_int_positive_lower {
                    finalizer.positive_int()?
                } else {
                    finalizer.positive_bottom()?
                };
                finalizer.set_scheme(0, &[], predicate)
            })
            .map_err(Self::map_finalization_error)
    }

    /// F2 member ordinals select dense storage, but they never become a
    /// semantic identity.  Validate the exact frozen member before reading a
    /// scheme slot or the definition-root row carried by that record.
    fn verified_scheme_definition<'a>(
        batch: &'a ConstraintBatch,
        member: &DefinitionOrderId,
    ) -> VerifiedSchemeDefinition<'a> {
        let position = member.ordinal() as usize;
        let record = batch
            .definitions
            .get(position)
            .expect("F4 scheme member ordinal is a valid dense definition slot");
        assert_eq!(
            &record.definition, member,
            "F4 scheme member exactly matches its frozen F2 definition slot"
        );
        let root = &record.root;
        assert_eq!(
            batch.root_order.get(position),
            Some(root),
            "F4 scheme member carries its exact collected definition root"
        );
        assert_eq!(
            batch.root_definition_positions.get(root),
            Some(&position),
            "F4 scheme root maps to its exact dense definition position"
        );
        VerifiedSchemeDefinition { record, position }
    }

    fn finish(mut self) -> Result<SolvedModule, SolveAvailabilityError> {
        let mut projections = HashMap::with_capacity(self.batch.projection_order.len());
        let mut work = ProductionCounters::default();
        for occurrence in &self.batch.projection_order {
            work.finish_projection_visits += 1;
            let (value, effect) = if let Some(positions) =
                self.batch.occurrence_component_positions.get(occurrence)
            {
                let value_live = self.live_components[positions.value].ordinal as usize;
                let effect_live = self.live_components[positions.effect].ordinal as usize;
                let value_row = &self.bounds[value_live];
                let effect_row = &self.effect_bounds[effect_live];
                (
                    if value_row.has_int_positive_lower
                        && value_row
                            .exact_non_variable_uppers
                            .contains(&ValueEndpointKey::IntNegative)
                    {
                        SolvedValue::Int
                    } else {
                        SolvedValue::Unknown
                    },
                    if effect_row.has_bottom_lower && effect_row.has_empty_upper {
                        SolvedEffect::Empty
                    } else {
                        SolvedEffect::Unknown
                    },
                )
            } else {
                // Expressions without a component retain F4's Unknown view.
                (SolvedValue::Unknown, SolvedEffect::Unknown)
            };
            projections.insert(occurrence.clone(), SolvedProjection { value, effect });
        }
        work.solved_projection_retained_bytes =
            checked_capacity_bytes::<(HirOccurrenceId, SolvedProjection)>(
                projections.capacity(),
                "F4 finish projection output",
            );
        work.scheme_root_index_capacity = self.batch.root_definition_positions.capacity();
        work.scheme_root_index_retained_bytes = checked_usize_sum(
            [
                checked_capacity_bytes::<(DefinitionRootId, usize)>(
                    self.batch.root_definition_positions.capacity(),
                    "F4 finish scheme-root index",
                ),
                checked_capacity_bytes::<usize>(
                    self.batch.root_scheme_identity_payload_bytes.capacity(),
                    "F4 finish scheme-root identity payload",
                ),
            ],
            "F4 finish scheme-root index",
        );
        // Projection allocation is a real coexistence boundary: the closed
        // session and its reusable staging are still live here.
        self.sample_f4_resources_with_finish_output(
            ResourceBoundary::FinishOutputWithStaging,
            work.solved_projection_retained_bytes,
        );
        // `finish` is fallible only for terminal closed-type accounting. Map it
        // after the real pre-finish coexistence sample but before combining
        // final counters or constructing the public result.
        let finalization = self
            .finalization
            .take()
            .expect("F4 finalization session is consumed exactly once by finish");
        let (closed_types, receipt) = finalization
            .finish()
            .map_err(Self::map_finalization_error)?
            .into_parts();
        assert_eq!(
            receipt.retained_bytes_before_finish(),
            self.current_closed_retained_bytes,
            "closed finalization receipt continues the solver-owned total"
        );
        self.current_closed_retained_bytes = receipt.retained_bytes_after_finish();
        self.sample_f4_resources_with_finish_output(
            ResourceBoundary::FinishOutput,
            work.solved_projection_retained_bytes,
        );
        let mut counters = self.batch.counters();
        counters.combine(self.store.counters());
        counters.combine(&work);
        counters.combine(&self.execution_counters);
        Ok(SolvedModule {
            hir: self.batch.hir,
            projection_order: self.batch.projection_order,
            projections,
            root_scheme_positions: self.batch.root_definition_positions,
            root_scheme_identity_payload_bytes: self.batch.root_scheme_identity_payload_bytes,
            schemes: self.schemes,
            closed_types,
            routed_uses: self.routed_uses,
            errors: self.errors,
            store: self.store,
            counters,
            solved_root_query_probes: AtomicUsize::new(0),
            scheme_root_query_probes: AtomicUsize::new(0),
            scheme_root_query_identity_hash_byte_incidences: AtomicUsize::new(0),
            scheme_root_query_logical_successful_equality_byte_incidences: AtomicUsize::new(0),
            #[cfg(test)]
            resource_boundary_samples: self.resource_boundary_samples,
            #[cfg(test)]
            resource_ledger: self.resource_ledger,
        })
    }
}
impl SolvedModule {
    pub fn solve(batch: ConstraintBatch) -> Result<Self, SolveAvailabilityError> {
        InferenceSession::try_new(batch)?.run()
    }
    pub fn hir(&self) -> &Arc<HirModule> {
        &self.hir
    }
    pub fn occurrences(&self) -> &[HirOccurrenceId] {
        &self.projection_order
    }
    pub fn errors(&self) -> &[SolverError] {
        &self.errors
    }
    pub fn store(&self) -> &ConstraintStore {
        &self.store
    }
    pub fn counters(&self) -> ProductionCounters {
        let mut counters = self.counters.clone();
        counters.solved_root_query_probes += self.solved_root_query_probes.load(Ordering::Relaxed);
        let scheme_queries = self.scheme_root_query_probes.load(Ordering::Relaxed);
        counters.scheme_root_query_probes += scheme_queries;
        counters.scheme_root_query_identity_hash_byte_incidences += self
            .scheme_root_query_identity_hash_byte_incidences
            .load(Ordering::Relaxed);
        counters.scheme_root_query_logical_successful_equality_byte_incidences += self
            .scheme_root_query_logical_successful_equality_byte_incidences
            .load(Ordering::Relaxed);
        counters
    }
    pub fn projection_for(
        &self,
        occurrence: &HirOccurrenceId,
    ) -> Result<SolvedProjection, ArtifactMismatch> {
        if !self.hir.owns_occurrence(occurrence) {
            return Err(ArtifactMismatch);
        }
        Ok(*self
            .projections
            .get(occurrence)
            .unwrap_or(&SolvedProjection {
                value: SolvedValue::Unknown,
                effect: SolvedEffect::Unknown,
            }))
    }
    pub fn root_value_for(&self, root: &DefinitionRootId) -> Result<SolvedValue, ArtifactMismatch> {
        if !self.hir.owns_definition_root(root) {
            return Err(ArtifactMismatch);
        }
        self.solved_root_query_probes
            .fetch_add(1, Ordering::Relaxed);
        self.scheme_root_query_probes
            .fetch_add(1, Ordering::Relaxed);
        let position = *self
            .root_scheme_positions
            .get(root)
            .expect("every admitted root has a scheme position");
        let identity_payload_bytes = self.root_scheme_identity_payload_bytes[position];
        // This successful public root-index lookup is the only F4 path that
        // charges source-bearing identity work.  The dense side table was
        // frozen with the same root position during collection, so it records
        // the actual retained spelling/path payload rather than handle size.
        self.scheme_root_query_identity_hash_byte_incidences
            .fetch_add(identity_payload_bytes, Ordering::Relaxed);
        self.scheme_root_query_logical_successful_equality_byte_incidences
            .fetch_add(identity_payload_bytes, Ordering::Relaxed);
        let view = self
            .closed_types
            .scheme_view(
                self.schemes[position]
                    .as_ref()
                    .expect("every admitted root has a finalized scheme"),
            )
            .expect("solved module retains its exact finalized closed arena");
        match view
            .positive_value(view.predicate())
            .expect("scheme predicate remains valid")
        {
            PositiveValueView::Int => Ok(SolvedValue::Int),
            PositiveValueView::Bottom => Ok(SolvedValue::Never),
            PositiveValueView::Quantified(_)
            | PositiveValueView::Recursive(_)
            | PositiveValueView::Function { .. }
            | PositiveValueView::Union(_) => Ok(SolvedValue::Unknown),
        }
    }
}

#[cfg(test)]
#[allow(deprecated)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports, lower_module};
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    fn module(source: &str, path: &str) -> Arc<HirModule> {
        module_with_identity(source, "test", path)
    }
    fn module_with_identity(source: &str, realm: &str, path: &str) -> Arc<HirModule> {
        let source: Arc<SourceText> = Arc::from(source);
        let header = Arc::new(scan_header(source.clone()));
        Arc::new(
            lower_module(
                ModuleIdentity::source_root(FileId::new(FileKey::new(realm, path))),
                &parse_file(source, header, Arc::new(SyntaxEnvironment::empty())),
                SemanticImports::empty(),
            )
            .unwrap(),
        )
    }
    fn collect(hir: Arc<HirModule>) -> ConstraintBatch {
        ConstraintBatch::collect(hir).unwrap()
    }
    fn retain_batch_occurrences(
        batch: &mut ConstraintBatch,
        keep: impl Fn(&ConstraintOccurrence) -> bool,
    ) {
        let occurrences = std::mem::take(&mut batch.occurrences);
        for occurrence in occurrences {
            if keep(&occurrence) {
                batch.occurrences.push(occurrence);
            }
        }
    }
    fn root(module: &HirModule, index: usize) -> &ResolvedExpr {
        match &module.items()[index] {
            HirItem::Expression(value) => value,
            _ => panic!("root expression"),
        }
    }
    fn shape(batch: &ConstraintBatch, item: &ConstraintOccurrence) -> (Option<Leaf>, Option<Leaf>) {
        let leaf = |term: Term| match batch.term_view(term) {
            Ok(TermView::Leaf(leaf)) => Some(leaf),
            _ => None,
        };
        (leaf(item.lower()), leaf(item.upper()))
    }

    /// Builds an artifact-valid F4 batch from real collection/F2 output, then
    /// injects only an `Int+` seed through the normal store transaction path.
    /// This is deliberately test-only: source syntax cannot express all SCC
    /// witness shapes needed by the F4 resource contract.
    fn synthetic_semantic_batch(
        source: &str,
        path: &str,
        seeded_roots: &[usize],
    ) -> ConstraintBatch {
        let hir = module(source, path);
        let mut batch = collect(hir.clone());
        for &index in seeded_roots {
            let HirItem::Binding(binding) = &hir.items()[index] else {
                panic!("synthetic seed names a binding");
            };
            let root = batch
                .root_value_component(binding.definition_root())
                .unwrap();
            let id = ConstraintOccurrenceId::new(binding.value().occurrence().clone(), 127);
            batch.occurrences.push(ConstraintOccurrence {
                cause: CauseId::for_occurrence(id.clone()),
                id,
                lower: batch.collected_leaf_term(Leaf::IntPositive),
                upper: batch.term_for_component(&root),
            });
            batch.counters.emitted_facts += 1;
            batch.counters.generated_work_items += 1;
            batch.synthetic_seed_value_pair_probes += 1;
        }
        batch
    }

    /// A source-independent F4 execution witness.  Its HIR and collection
    /// artifact are real, but its definition-use graph is assembled here so
    /// the scale matrix can cover semantic shapes that the current one-Name
    /// binding body surface cannot express (notably wide fan-out and several
    /// distinct use IDs on one graph arc).
    struct SyntheticScaleWitness {
        name: &'static str,
        /// C: frozen F2 components.
        components: usize,
        /// D: finalized definition roots.
        definitions: usize,
        /// I: component-internal definition uses.
        internal_uses: usize,
        /// X: dependency-closed incoming definition uses.
        incoming_uses: usize,
        /// M: ordinary initial slot-3 value-pair inputs.
        ordinary_initial_value_pair_probes: usize,
        /// S: test-only synthetic `Int+` seed inputs.
        synthetic_seed_value_pair_probes: usize,
        /// Exact direct-frontier physical work for this fixture.
        direct_edges: usize,
        exact_lower_memberships: usize,
        exact_upper_memberships: usize,
        transmission_attempts: usize,
        same_row_atom_intersections: usize,
        /// R = lower/upper replay attempts, exactly T + J for every scale
        /// witness under the direct-frontier contract.
        replay_attempts: usize,
        /// Exact pair-cache outcomes.  Their sum is the total P probe count:
        /// `A + T + J`, including duplicates.
        constraint_pair_admissions: usize,
        /// F5 §34 extends the retained pair counter to the effect half of the
        /// typed memo.  This is an independently derived exact addition to
        /// the original value-only frontier ledger.
        typed_effect_pair_admissions: usize,
        constraint_pair_duplicates: usize,
        typed_effect_pair_duplicates: usize,
        edges: Vec<(usize, usize)>,
        seeded_roots: Vec<usize>,
        pair_work_is_linear: bool,
    }

    /// A doubling baseline is always an actual preceding solve.  It never
    /// stores synthetic values in production counter fields.
    struct ScaleRatioBaseline {
        counters: ProductionCounters,
        summary: SummaryObservation,
        pair_work_is_linear: bool,
    }

    /// The isolated measurement must satisfy every exact unbounded-cycle field
    /// at its own named size.  Actual doubling evidence is separate.
    fn assert_unbounded_cycle_exact_scale_fields(
        witness: &SyntheticScaleWitness,
        counters: &ProductionCounters,
        summary: SummaryObservation,
    ) {
        if witness.name != "unbounded-cycle" {
            return;
        }
        let n = witness.definitions;
        let twice = n
            .checked_mul(2)
            .expect("F4 unbounded-cycle exact 2N fits usize");
        let fourfold = n
            .checked_mul(4)
            .expect("F4 unbounded-cycle exact 4N fits usize");
        assert_eq!(counters.definition_use_query_probes(), n);
        assert_eq!(counters.scc_component_members_query_probes(), 1);
        assert_eq!(counters.scc_component_internal_uses_query_probes(), 1);
        assert_eq!(counters.scc_component_incoming_uses_query_probes(), 1);
        assert_eq!(counters.scc_plan_component_index_probes(), 1);
        assert_eq!(counters.scc_plan_definition_index_probes(), n);
        assert_eq!(counters.scc_execution_component_visits(), 1);
        assert_eq!(counters.scc_execution_internal_use_connections(), n);
        assert_eq!(counters.scc_execution_draft_members(), n);
        assert_eq!(counters.scc_execution_drafts_visible_barriers(), 1);
        assert_eq!(counters.scc_execution_finalized_members(), n);
        assert_eq!(counters.scc_execution_installed_members(), n);
        assert_eq!(counters.scc_execution_incoming_instantiations(), 0);
        assert_eq!(counters.scc_execution_int_instantiation_facts(), 0);
        assert_eq!(counters.scc_execution_bottom_trivial_instantiations(), 0);
        assert_eq!(counters.scc_execution_draft_lookups(), n);
        assert_eq!(counters.scc_execution_cross_draft_visits(), 0);
        assert_eq!(counters.constraint_pair_admissions(), fourfold * 3 / 2 + 1);
        assert_eq!(counters.constraint_pair_duplicates(), n);
        assert_eq!(counters.lower_bound_insertions(), fourfold);
        assert_eq!(counters.upper_bound_insertions(), twice);
        assert_eq!(counters.lower_bound_replays(), twice);
        assert_eq!(counters.upper_bound_replays(), 0);
        assert_eq!(counters.scheme_table_len(), n);
        assert_eq!(counters.scheme_root_query_probes(), n);
        assert_eq!(counters.draft_scratch_max_len(), n);
        assert_eq!(counters.routed_use_provenance_len(), n);
        assert_eq!(
            counters.occurrence_bound_state_len(),
            0,
            "F5 §35 deprecates occurrence-bound summary storage"
        );
        assert_eq!(counters.finish_projection_visits(), twice);
        assert_eq!(summary.frontier_maximum_live, 1);
    }

    fn synthetic_scale_batch(witness: &SyntheticScaleWitness, path: &str) -> ConstraintBatch {
        assert!(witness.definitions > 0);
        assert!(
            witness
                .edges
                .iter()
                .all(|&(parent, target)| parent < witness.definitions
                    && target < witness.definitions)
        );
        assert!(
            witness
                .seeded_roots
                .iter()
                .all(|&root| root < witness.definitions)
        );

        let mut source = (0..witness.definitions)
            .map(|index| format!("my n{index} = missing"))
            .collect::<Vec<_>>();
        source.extend(
            witness
                .edges
                .iter()
                .map(|&(_, target)| format!("n{target}")),
        );
        let hir = module(&source.join("; "), path);
        let mut batch = collect(hir.clone());
        let use_occurrences = hir
            .items()
            .iter()
            .skip(witness.definitions)
            .map(|item| match item {
                HirItem::Expression(ResolvedExpr::Name {
                    occurrence,
                    resolution: NameResolution::Resolved(_),
                    ..
                }) => occurrence.clone(),
                _ => panic!("synthetic source contributes one resolved Name per use"),
            })
            .collect::<Vec<_>>();
        assert_eq!(use_occurrences.len(), witness.edges.len());

        // Replace the empty source-level use set with artifact-valid semantic
        // records.  Every record retains a unique real HIR occurrence, and
        // the normal F2 constructor seals the resulting total index.
        batch.definition_uses = Vec::with_capacity(witness.edges.len());
        batch.definition_use_positions = HashMap::with_capacity(witness.edges.len());
        for (position, (&(parent, target), occurrence)) in
            witness.edges.iter().zip(&use_occurrences).enumerate()
        {
            let parent_definition = batch.definitions[parent].definition.clone();
            let parent_root = batch.definitions[parent].root.clone();
            let target_definition = batch.definitions[target].definition.clone();
            batch
                .emit_resolved_binding_name(occurrence.clone(), parent_root)
                .expect("synthetic occurrence and root share the real artifact");
            let id = DefinitionUseId::new(batch.collection_artifact.clone(), occurrence.clone());
            assert!(
                batch
                    .definition_use_positions
                    .insert(id.clone(), position)
                    .is_none(),
                "each synthetic use has a distinct real occurrence ID"
            );
            batch.definition_uses.push(DefinitionUse {
                cause: DefinitionUseCause::for_use(id.clone()),
                id,
                parent: parent_definition,
                target: target_definition,
                occurrence: occurrence.clone(),
                use_level: 1,
                use_value_component: batch
                    .occurrence_component_positions
                    .get(occurrence)
                    .expect("synthetic occurrence has a value component")
                    .value,
                target_root_component: batch
                    .root_component_positions
                    .get(&batch.definitions[target].root)
                    .expect("synthetic target has a value component")
                    .component,
            });
        }
        batch
            .ensure_total_definition_use_map()
            .expect("synthetic use index is total");

        for &root_index in &witness.seeded_roots {
            let HirItem::Binding(binding) = &hir.items()[root_index] else {
                panic!("synthetic seed names a binding");
            };
            let root = batch.root_value_component_for_session(binding.definition_root());
            let occurrence = binding.value().occurrence().clone();
            let id = ConstraintOccurrenceId::new(occurrence, 127);
            batch.occurrences.push(ConstraintOccurrence {
                cause: CauseId::for_occurrence(id.clone()),
                id,
                lower: batch.collected_leaf_term(Leaf::IntPositive),
                upper: batch.term_for_component(&root),
            });
            batch.counters.emitted_facts += 1;
            batch.counters.generated_work_items += 1;
            batch.synthetic_seed_value_pair_probes += 1;
        }

        // The F4 resource counters below include the synthetic semantic state
        // rather than the source's intentionally empty Name-use graph.
        batch.counters.component_retained_bytes = checked_capacity_bytes::<ComponentId>(
            batch.components.capacity(),
            "F4 synthetic components",
        );
        batch.counters.occurrence_record_retained_bytes =
            checked_capacity_bytes::<ConstraintOccurrence>(
                batch.occurrences.capacity(),
                "F4 synthetic occurrences",
            );
        batch.counters.occurrence_component_index_capacity =
            batch.occurrence_component_positions.capacity();
        batch.counters.occurrence_component_index_retained_bytes =
            checked_capacity_bytes::<(HirOccurrenceId, ComponentPositions)>(
                batch.occurrence_component_positions.capacity(),
                "F4 synthetic occurrence component index",
            );
        batch.counters.definition_use_retained_bytes = checked_capacity_bytes::<DefinitionUse>(
            batch.definition_uses.capacity(),
            "F4 synthetic definition uses",
        );
        batch.counters.definition_use_index_capacity = batch.definition_use_positions.capacity();
        batch.counters.definition_use_index_retained_bytes =
            checked_capacity_bytes::<(DefinitionUseId, usize)>(
                batch.definition_use_positions.capacity(),
                "F4 synthetic definition-use index",
            );
        batch.counters.retained_definition_uses = batch.definition_uses.len();
        batch.counters.index_capacity = batch.occurrence_component_positions.capacity()
            + batch.root_component_positions.capacity();
        batch.finish_collection_accounting(0, 0);

        let mut plan_counters = ProductionCounters::default();
        let plan = SccPlan::build(
            &batch.collection_artifact,
            &batch.definitions,
            &batch.definition_uses,
            &mut plan_counters,
        )
        .expect("synthetic definitions and uses are artifact-valid and total");
        batch.scc_plan = Some(plan);
        // These are the F1 outputs consumed by F4 allocation/accounting.  The
        // source collection's empty plan is intentionally not the semantic
        // plan under test.
        batch.counters.scc_maximum_component_size = plan_counters.scc_maximum_component_size;
        batch.counters.scc_plan_component_index_probes =
            plan_counters.scc_plan_component_index_probes;
        batch.counters.scc_plan_definition_index_probes =
            plan_counters.scc_plan_definition_index_probes;
        batch.counters.scc_plan_retained_payload_bytes =
            plan_counters.scc_plan_retained_payload_bytes;
        batch.counters.scc_f1_graph_input_plan_peak_known_bytes =
            plan_counters.scc_f1_graph_input_plan_peak_known_bytes;
        batch.finish_scc_plan_accounting();
        batch
    }

    fn assert_f4_scale_witness(witnesses: impl IntoIterator<Item = SyntheticScaleWitness>) {
        let mut previous: Option<ScaleRatioBaseline> = None;
        for witness in witnesses {
            let path = format!("f4-scale-{}-{}.yu", witness.name, witness.definitions);
            let batch = synthetic_scale_batch(&witness, &path);
            let (solved, observer, summary) =
                InferenceSession::new(batch).run_with_observer(0).unwrap();
            assert!(observer.events.is_empty());
            assert_eq!(
                observer.omitted,
                witness.internal_uses
                    + witness.definitions
                    + witness.components
                    + witness.definitions
                    + witness.incoming_uses,
                "{} has the declared bounded execution event count",
                witness.name
            );
            assert_eq!(summary.reads, witness.definitions);
            assert_eq!(
                summary.false_to_true_transitions, witness.exact_lower_memberships,
                "{} records exactly one Int-positive summary transition for every exact lower membership",
                witness.name
            );
            assert_eq!(
                summary.ordinary_initial_value_pair_probes,
                witness.ordinary_initial_value_pair_probes,
                "{} preserves the causal M input class",
                witness.name
            );
            assert_eq!(
                summary.synthetic_seed_value_pair_probes, witness.synthetic_seed_value_pair_probes,
                "{} preserves the causal S input class",
                witness.name
            );
            let pair_probe_inputs = witness
                .ordinary_initial_value_pair_probes
                .checked_add(witness.internal_uses)
                .and_then(|value| value.checked_add(witness.incoming_uses))
                .and_then(|value| value.checked_add(witness.synthetic_seed_value_pair_probes))
                .expect("F4 scale A fits usize");
            assert_eq!(
                summary.frontier_pushes,
                pair_probe_inputs
                    + witness.transmission_attempts
                    + witness.same_row_atom_intersections,
                "{} preserves A = M + I_p + X_p + S and exact replay probes",
                witness.name
            );
            assert_eq!(summary.frontier_pushes, summary.frontier_pops);
            assert_eq!(summary.frontier_peak_bytes, summary.frontier_retained_bytes);
            assert!(summary.frontier_maximum_live <= summary.frontier_capacity);
            assert_eq!(summary.frontier_capacity_growths, 0);
            let direct_edge_transmission_limit = summary
                .direct_edges
                .checked_mul(2)
                .expect("F4 scale direct-edge transmission bound fits usize");
            assert!(summary.transmission_attempts <= direct_edge_transmission_limit);
            assert_eq!(summary.direct_edges, witness.direct_edges);
            assert_eq!(
                summary.exact_lower_memberships,
                witness.exact_lower_memberships
            );
            assert_eq!(
                summary.exact_upper_memberships,
                witness.exact_upper_memberships
            );
            assert_eq!(summary.transmission_attempts, witness.transmission_attempts);
            assert_eq!(
                summary.same_row_atom_intersections,
                witness.same_row_atom_intersections
            );

            // Query every root once.  The counter is logical handle work, so
            // it stays deterministic across randomized HashMap hash seeds and
            // does not claim bucket-collision comparisons.
            for item in solved.hir().items().iter().take(witness.definitions) {
                let HirItem::Binding(binding) = item else {
                    panic!("synthetic definitions remain bindings");
                };
                assert_eq!(
                    solved.root_value_for(binding.definition_root()),
                    Ok(SolvedValue::Int),
                    "{} has its fixture-defined Int scheme",
                    witness.name
                );
            }
            let counters = solved.counters();
            assert_eq!(counters.definition_query_probes(), 0);
            let expected_definition_use_queries = witness
                .internal_uses
                .checked_add(witness.incoming_uses)
                .expect("F4 scale DefinitionUse query count fits usize");
            assert_eq!(
                counters.definition_use_query_probes(),
                expected_definition_use_queries,
                "{} counts only production internal and incoming route probes when the scale observer has zero capacity",
                witness.name
            );
            assert_eq!(counters.scc_component_for_definition_query_probes(), 0);
            assert_eq!(
                counters.scc_component_members_query_probes(),
                witness.components,
                "{} borrows each F2 member slice exactly once",
                witness.name
            );
            assert_eq!(
                counters.scc_component_internal_uses_query_probes(),
                witness.components,
                "{} borrows each F2 internal-use slice exactly once",
                witness.name
            );
            assert_eq!(
                counters.scc_component_incoming_uses_query_probes(),
                witness.components,
                "{} borrows each F2 incoming-use slice exactly once",
                witness.name
            );
            assert_eq!(
                counters.scc_plan_component_index_probes(),
                witness.components,
                "{} retains one frozen F2 component-index insertion probe per component",
                witness.name
            );
            assert_eq!(
                counters.scc_plan_definition_index_probes(),
                witness.definitions,
                "{} retains one frozen F2 definition-index insertion probe per member",
                witness.name
            );
            let replay_attempts = counters
                .lower_bound_replays()
                .checked_add(counters.upper_bound_replays())
                .expect("F4 replay count fits usize");
            assert_eq!(replay_attempts, witness.replay_attempts);
            assert_eq!(
                replay_attempts,
                witness
                    .transmission_attempts
                    .checked_add(witness.same_row_atom_intersections)
                    .expect("F4 T + J fits usize"),
                "{} preserves R = T + J",
                witness.name
            );
            let initial_admission_samples = witness
                .edges
                .len()
                .checked_mul(3)
                .and_then(|count| count.checked_add(witness.synthetic_seed_value_pair_probes))
                .expect("F4 scale initial-admission sample count fits usize");
            let expected_resource_samples = checked_usize_sum(
                [
                    1, // initial reservation
                    initial_admission_samples,
                    witness.internal_uses,
                    witness.components, // one scratch clear per component
                    witness.definitions,
                    witness.definitions, // one scheme install per member
                    witness.incoming_uses,
                    2, // before and after finish store accounting
                    2, // output with live closed staging, then post-finish transfer
                ],
                "F4 scale resource boundary sample count",
            );
            assert_eq!(
                summary.resource_boundary_samples, expected_resource_samples,
                "{} samples every causal F4 resource boundary exactly",
                witness.name
            );
            assert_eq!(
                summary.resource_boundary_coverage,
                8 + usize::from(witness.internal_uses != 0)
                    + usize::from(witness.incoming_uses != 0),
                "{} records every applicable named resource boundary exactly",
                witness.name
            );
            assert_eq!(
                summary.independent_queue_retained_bytes, summary.frontier_retained_bytes,
                "{} independently records the frontier queue contribution",
                witness.name
            );
            assert_eq!(
                summary.independent_semantic_arena_retained_bytes,
                counters.semantic_arena_retained_bytes(),
                "{} independent boundary ledger agrees with the production semantic aggregate",
                witness.name
            );
            assert_eq!(
                summary.independent_semantic_arena_peak_bytes,
                counters.semantic_arena_peak_bytes(),
                "{} independent boundary ledger agrees with the production semantic peak",
                witness.name
            );
            assert_eq!(
                summary.independent_inference_session_retained_bytes,
                counters.inference_session_retained_bytes(),
                "{} independent boundary ledger agrees with the production session aggregate",
                witness.name
            );
            assert_eq!(
                summary.independent_finish_output_retained_bytes,
                counters.solved_projection_retained_bytes(),
                "{} independently retains the finish output through result construction",
                witness.name
            );
            assert_eq!(
                summary.independent_inference_session_peak_bytes,
                counters.inference_session_peak_bytes(),
                "{} independently checked full session peak, including finish output coexistence, agrees with production",
                witness.name
            );
            assert!(
                summary.semantic_arena_retained_bytes >= summary.frontier_retained_bytes,
                "{} semantic aggregate includes the source-free frontier queue contribution",
                witness.name
            );
            assert_eq!(
                counters.constraint_pair_admissions(),
                witness.constraint_pair_admissions + witness.typed_effect_pair_admissions,
                "{} retains F4's pair name while F5 §34 counts every typed value/effect memo admission",
                witness.name
            );
            assert_eq!(
                counters.constraint_pair_duplicates(),
                witness.constraint_pair_duplicates + witness.typed_effect_pair_duplicates,
                "{} retains F4's pair name while F5 §34 counts every typed value/effect memo duplicate",
                witness.name
            );
            assert_eq!(
                counters.constraint_pair_admissions() + counters.constraint_pair_duplicates(),
                pair_probe_inputs
                    + witness.transmission_attempts
                    + witness.same_row_atom_intersections
                    + witness.typed_effect_pair_admissions
                    + witness.typed_effect_pair_duplicates,
                "{} counts every value frontier probe plus the F5 §34 effect typed-memo admissions exactly once",
                witness.name
            );
            if witness.name == "unbounded-cycle" {
                eprintln!(
                    "f4-direct-frontier n={} E={} L={} U={} T={} J={} queue_peak={} queue_capacity={} queue_bytes={} queue_peak_bytes={} P={} replays={} semantic_peak={} session_peak={}",
                    witness.definitions,
                    summary.direct_edges,
                    summary.exact_lower_memberships,
                    summary.exact_upper_memberships,
                    summary.transmission_attempts,
                    summary.same_row_atom_intersections,
                    summary.frontier_maximum_live,
                    summary.frontier_capacity,
                    summary.frontier_retained_bytes,
                    summary.frontier_peak_bytes,
                    counters.constraint_pair_admissions() + counters.constraint_pair_duplicates(),
                    counters.lower_bound_replays() + counters.upper_bound_replays(),
                    counters.semantic_arena_peak_bytes(),
                    counters.inference_session_peak_bytes(),
                );
            }
            assert_eq!(
                counters.scc_execution_component_visits(),
                witness.components
            );
            assert_eq!(counters.scc_execution_draft_members(), witness.definitions);
            assert_eq!(
                counters.scc_execution_finalized_members(),
                witness.definitions
            );
            assert_eq!(
                counters.scc_execution_installed_members(),
                witness.definitions
            );
            assert_eq!(
                counters.scc_execution_internal_use_connections(),
                witness.internal_uses
            );
            assert_eq!(
                counters.scc_execution_incoming_instantiations(),
                witness.incoming_uses
            );
            assert_eq!(
                counters.scc_execution_int_instantiation_facts()
                    + counters.scc_execution_bottom_trivial_instantiations(),
                witness.incoming_uses,
                "{} gives every incoming use exactly one closed route",
                witness.name
            );
            assert_eq!(
                counters.routed_use_provenance_len(),
                witness.internal_uses + witness.incoming_uses,
                "{} retains one route record for every distinct DefinitionUseId",
                witness.name
            );
            assert_eq!(counters.constraint_store_growths(), 0);
            assert_eq!(counters.constraint_store_rebuilds(), 0);
            assert_eq!(counters.fact_store_growths(), 0);
            assert_eq!(counters.fact_store_rebuilds, 0);
            assert_eq!(counters.canonical_map_growths(), 0);
            assert_eq!(counters.canonical_map_rebuilds(), 0);
            assert_eq!(counters.provenance_growths(), 0);
            assert_eq!(counters.provenance_rebuilds(), 0);
            assert_eq!(counters.consumed_receipt_growths(), 0);
            assert_eq!(counters.consumed_receipt_rebuilds(), 0);
            assert_eq!(counters.routed_use_provenance_growths(), 0);
            let store_sum = |lanes: [usize; 4]| {
                lanes
                    .into_iter()
                    .try_fold(0usize, |total, lane| total.checked_add(lane))
                    .expect("scale store aggregate fits usize")
            };
            assert_eq!(
                counters.constraint_store_requested_capacity(),
                store_sum([
                    counters.fact_store_requested_capacity(),
                    counters.canonical_map_requested_capacity(),
                    counters.provenance_requested_capacity(),
                    counters.consumed_receipt_requested_capacity(),
                ]),
                "{} keeps the named requested-capacity ledger exact",
                witness.name
            );
            assert_eq!(
                counters.constraint_store_actual_capacity(),
                store_sum([
                    counters.fact_store_actual_capacity(),
                    counters.canonical_map_actual_capacity(),
                    counters.provenance_actual_capacity(),
                    counters.consumed_receipt_actual_capacity(),
                ]),
                "{} keeps the named actual-capacity ledger exact",
                witness.name
            );
            assert_eq!(
                counters.constraint_store_growths(),
                store_sum([
                    counters.fact_store_growths(),
                    counters.canonical_map_growths(),
                    counters.provenance_growths(),
                    counters.consumed_receipt_growths(),
                ])
            );
            assert_eq!(
                counters.constraint_store_rebuilds(),
                store_sum([
                    counters.fact_store_rebuilds,
                    counters.canonical_map_rebuilds(),
                    counters.provenance_rebuilds(),
                    counters.consumed_receipt_rebuilds(),
                ])
            );

            assert_unbounded_cycle_exact_scale_fields(&witness, &counters, summary);

            // Only an actual preceding solve can be a doubling baseline.
            // The separately named non-timed unbounded-cycle ratio witness
            // supplies all three measurements in one process; each capped
            // named-size witness remains intentionally self-contained.
            if let Some(previous) = previous.as_ref() {
                let previous_counters = &previous.counters;
                let previous_summary = previous.summary;
                let previous_pair_work_is_linear = previous.pair_work_is_linear;
                let mut linear_fields = vec![
                    (
                        "definition-use queries",
                        counters.definition_use_query_probes(),
                        previous_counters.definition_use_query_probes(),
                    ),
                    (
                        "F2 member-slice queries",
                        counters.scc_component_members_query_probes(),
                        previous_counters.scc_component_members_query_probes(),
                    ),
                    (
                        "F2 internal-use-slice queries",
                        counters.scc_component_internal_uses_query_probes(),
                        previous_counters.scc_component_internal_uses_query_probes(),
                    ),
                    (
                        "F2 incoming-use-slice queries",
                        counters.scc_component_incoming_uses_query_probes(),
                        previous_counters.scc_component_incoming_uses_query_probes(),
                    ),
                    (
                        "F2 component-index probes",
                        counters.scc_plan_component_index_probes(),
                        previous_counters.scc_plan_component_index_probes(),
                    ),
                    (
                        "F2 definition-index probes",
                        counters.scc_plan_definition_index_probes(),
                        previous_counters.scc_plan_definition_index_probes(),
                    ),
                    (
                        "component visits",
                        counters.scc_execution_component_visits(),
                        previous_counters.scc_execution_component_visits(),
                    ),
                    (
                        "internal use connections",
                        counters.scc_execution_internal_use_connections(),
                        previous_counters.scc_execution_internal_use_connections(),
                    ),
                    (
                        "draft members",
                        counters.scc_execution_draft_members(),
                        previous_counters.scc_execution_draft_members(),
                    ),
                    (
                        "draft barriers",
                        counters.scc_execution_drafts_visible_barriers(),
                        previous_counters.scc_execution_drafts_visible_barriers(),
                    ),
                    (
                        "finalized members",
                        counters.scc_execution_finalized_members(),
                        previous_counters.scc_execution_finalized_members(),
                    ),
                    (
                        "installed members",
                        counters.scc_execution_installed_members(),
                        previous_counters.scc_execution_installed_members(),
                    ),
                    (
                        "incoming instantiations",
                        counters.scc_execution_incoming_instantiations(),
                        previous_counters.scc_execution_incoming_instantiations(),
                    ),
                    (
                        "scheme table length",
                        counters.scheme_table_len(),
                        previous_counters.scheme_table_len(),
                    ),
                    (
                        "scheme table capacity",
                        counters.scheme_table_capacity(),
                        previous_counters.scheme_table_capacity(),
                    ),
                    (
                        "scheme table retained bytes",
                        counters.scheme_table_retained_bytes(),
                        previous_counters.scheme_table_retained_bytes(),
                    ),
                    (
                        "scheme root index capacity",
                        counters.scheme_root_index_capacity(),
                        previous_counters.scheme_root_index_capacity(),
                    ),
                    (
                        "scheme root index retained bytes",
                        counters.scheme_root_index_retained_bytes(),
                        previous_counters.scheme_root_index_retained_bytes(),
                    ),
                    (
                        "draft scratch capacity",
                        counters.draft_scratch_capacity(),
                        previous_counters.draft_scratch_capacity(),
                    ),
                    (
                        "draft scratch retained bytes",
                        counters.draft_scratch_retained_bytes(),
                        previous_counters.draft_scratch_retained_bytes(),
                    ),
                    (
                        "bound table capacity",
                        counters.bound_table_capacity(),
                        previous_counters.bound_table_capacity(),
                    ),
                    (
                        "routed-use provenance length",
                        counters.routed_use_provenance_len(),
                        previous_counters.routed_use_provenance_len(),
                    ),
                    (
                        "routed-use provenance capacity",
                        counters.routed_use_provenance_capacity(),
                        previous_counters.routed_use_provenance_capacity(),
                    ),
                    (
                        "routed-use provenance retained bytes",
                        counters.routed_use_provenance_retained_bytes(),
                        previous_counters.routed_use_provenance_retained_bytes(),
                    ),
                    (
                        "occurrence bound-state length",
                        counters.occurrence_bound_state_len(),
                        previous_counters.occurrence_bound_state_len(),
                    ),
                    (
                        "occurrence bound-state capacity",
                        counters.occurrence_bound_state_capacity(),
                        previous_counters.occurrence_bound_state_capacity(),
                    ),
                    (
                        "finish projection visits",
                        counters.finish_projection_visits(),
                        previous_counters.finish_projection_visits(),
                    ),
                    (
                        "scheme root query probes",
                        counters.scheme_root_query_probes(),
                        previous_counters.scheme_root_query_probes(),
                    ),
                    (
                        "scheme root identity hash-byte incidences",
                        counters.scheme_root_query_identity_hash_byte_incidences(),
                        previous_counters.scheme_root_query_identity_hash_byte_incidences(),
                    ),
                    (
                        "scheme root logical equality-byte incidences",
                        counters.scheme_root_query_logical_successful_equality_byte_incidences(),
                        previous_counters
                            .scheme_root_query_logical_successful_equality_byte_incidences(),
                    ),
                    (
                        "summary false-to-true transitions",
                        summary.false_to_true_transitions,
                        previous_summary.false_to_true_transitions,
                    ),
                    (
                        "frontier maximum live",
                        summary.frontier_maximum_live,
                        previous_summary.frontier_maximum_live,
                    ),
                    (
                        "frontier capacity",
                        summary.frontier_capacity,
                        previous_summary.frontier_capacity,
                    ),
                    (
                        "frontier retained bytes",
                        summary.frontier_retained_bytes,
                        previous_summary.frontier_retained_bytes,
                    ),
                    (
                        "frontier peak bytes",
                        summary.frontier_peak_bytes,
                        previous_summary.frontier_peak_bytes,
                    ),
                    (
                        "solved projection retained bytes",
                        counters.solved_projection_retained_bytes(),
                        previous_counters.solved_projection_retained_bytes(),
                    ),
                ];
                // Every fixed F4 count/capacity/retained/peak/probe field is
                // part of the declared doubling contract.  A field that is
                // structurally zero for a witness must remain zero; no hidden
                // scale-only allocation or observer work is exempted.
                linear_fields.extend([
                    (
                        "int instantiation facts",
                        counters.scc_execution_int_instantiation_facts(),
                        previous_counters.scc_execution_int_instantiation_facts(),
                    ),
                    (
                        "Bottom trivial instantiations",
                        counters.scc_execution_bottom_trivial_instantiations(),
                        previous_counters.scc_execution_bottom_trivial_instantiations(),
                    ),
                    (
                        "draft lookups",
                        counters.scc_execution_draft_lookups(),
                        previous_counters.scc_execution_draft_lookups(),
                    ),
                    (
                        "cross-draft visits",
                        counters.scc_execution_cross_draft_visits(),
                        previous_counters.scc_execution_cross_draft_visits(),
                    ),
                    (
                        "constraint pair duplicates",
                        counters.constraint_pair_duplicates(),
                        previous_counters.constraint_pair_duplicates(),
                    ),
                    (
                        "lower insertions",
                        counters.lower_bound_insertions(),
                        previous_counters.lower_bound_insertions(),
                    ),
                    (
                        "upper insertions",
                        counters.upper_bound_insertions(),
                        previous_counters.upper_bound_insertions(),
                    ),
                    (
                        "lower replays",
                        counters.lower_bound_replays(),
                        previous_counters.lower_bound_replays(),
                    ),
                    (
                        "upper replays",
                        counters.upper_bound_replays(),
                        previous_counters.upper_bound_replays(),
                    ),
                    (
                        "total replays",
                        replay_attempts,
                        previous_counters.lower_bound_replays()
                            + previous_counters.upper_bound_replays(),
                    ),
                    (
                        "scheme table rebuilds",
                        counters.scheme_table_rebuilds(),
                        previous_counters.scheme_table_rebuilds(),
                    ),
                    (
                        "scheme root index growths",
                        counters.scheme_root_index_growths(),
                        previous_counters.scheme_root_index_growths(),
                    ),
                    (
                        "scheme root index rebuilds",
                        counters.scheme_root_index_rebuilds(),
                        previous_counters.scheme_root_index_rebuilds(),
                    ),
                    (
                        "draft scratch maximum",
                        counters.draft_scratch_max_len(),
                        previous_counters.draft_scratch_max_len(),
                    ),
                    (
                        "draft scratch growths",
                        counters.draft_scratch_growths(),
                        previous_counters.draft_scratch_growths(),
                    ),
                    (
                        "bound table retained bytes",
                        counters.bound_table_retained_bytes(),
                        previous_counters.bound_table_retained_bytes(),
                    ),
                    (
                        "bound table growths",
                        counters.bound_table_growths(),
                        previous_counters.bound_table_growths(),
                    ),
                    (
                        "bound table rebuilds",
                        counters.bound_table_rebuilds(),
                        previous_counters.bound_table_rebuilds(),
                    ),
                    (
                        "bound table peak bytes",
                        counters.bound_table_peak_bytes(),
                        previous_counters.bound_table_peak_bytes(),
                    ),
                    (
                        "pair cache growths",
                        counters.constraint_pair_cache_growths(),
                        previous_counters.constraint_pair_cache_growths(),
                    ),
                    (
                        "pair cache rebuilds",
                        counters.constraint_pair_cache_rebuilds(),
                        previous_counters.constraint_pair_cache_rebuilds(),
                    ),
                    (
                        "pair cache peak bytes",
                        counters.constraint_pair_cache_peak_bytes(),
                        previous_counters.constraint_pair_cache_peak_bytes(),
                    ),
                    (
                        "routed-use provenance growths",
                        counters.routed_use_provenance_growths(),
                        previous_counters.routed_use_provenance_growths(),
                    ),
                    (
                        "occurrence bound-state retained bytes",
                        counters.occurrence_bound_state_retained_bytes(),
                        previous_counters.occurrence_bound_state_retained_bytes(),
                    ),
                    (
                        "occurrence bound-state growths",
                        counters.occurrence_bound_state_growths(),
                        previous_counters.occurrence_bound_state_growths(),
                    ),
                    (
                        "solver error capacity",
                        counters.solver_error_workspace_capacity(),
                        previous_counters.solver_error_workspace_capacity(),
                    ),
                    (
                        "solver error retained bytes",
                        counters.solver_error_workspace_retained_bytes(),
                        previous_counters.solver_error_workspace_retained_bytes(),
                    ),
                    (
                        "store requested capacity",
                        counters.constraint_store_requested_capacity(),
                        previous_counters.constraint_store_requested_capacity(),
                    ),
                    (
                        "store actual capacity",
                        counters.constraint_store_actual_capacity(),
                        previous_counters.constraint_store_actual_capacity(),
                    ),
                    (
                        "store growths",
                        counters.constraint_store_growths(),
                        previous_counters.constraint_store_growths(),
                    ),
                    (
                        "store rebuilds",
                        counters.constraint_store_rebuilds(),
                        previous_counters.constraint_store_rebuilds(),
                    ),
                    (
                        "fact requested capacity",
                        counters.fact_store_requested_capacity(),
                        previous_counters.fact_store_requested_capacity(),
                    ),
                    (
                        "fact actual capacity",
                        counters.fact_store_actual_capacity(),
                        previous_counters.fact_store_actual_capacity(),
                    ),
                    (
                        "fact growths",
                        counters.fact_store_growths(),
                        previous_counters.fact_store_growths(),
                    ),
                    (
                        "canonical requested capacity",
                        counters.canonical_map_requested_capacity(),
                        previous_counters.canonical_map_requested_capacity(),
                    ),
                    (
                        "canonical actual capacity",
                        counters.canonical_map_actual_capacity(),
                        previous_counters.canonical_map_actual_capacity(),
                    ),
                    (
                        "canonical growths",
                        counters.canonical_map_growths(),
                        previous_counters.canonical_map_growths(),
                    ),
                    (
                        "canonical rebuilds",
                        counters.canonical_map_rebuilds(),
                        previous_counters.canonical_map_rebuilds(),
                    ),
                    (
                        "provenance requested capacity",
                        counters.provenance_requested_capacity(),
                        previous_counters.provenance_requested_capacity(),
                    ),
                    (
                        "provenance actual capacity",
                        counters.provenance_actual_capacity(),
                        previous_counters.provenance_actual_capacity(),
                    ),
                    (
                        "provenance growths",
                        counters.provenance_growths(),
                        previous_counters.provenance_growths(),
                    ),
                    (
                        "provenance rebuilds",
                        counters.provenance_rebuilds(),
                        previous_counters.provenance_rebuilds(),
                    ),
                    (
                        "receipt requested capacity",
                        counters.consumed_receipt_requested_capacity(),
                        previous_counters.consumed_receipt_requested_capacity(),
                    ),
                    (
                        "receipt actual capacity",
                        counters.consumed_receipt_actual_capacity(),
                        previous_counters.consumed_receipt_actual_capacity(),
                    ),
                    (
                        "receipt growths",
                        counters.consumed_receipt_growths(),
                        previous_counters.consumed_receipt_growths(),
                    ),
                    (
                        "receipt rebuilds",
                        counters.consumed_receipt_rebuilds(),
                        previous_counters.consumed_receipt_rebuilds(),
                    ),
                ]);
                if witness.pair_work_is_linear && previous_pair_work_is_linear {
                    linear_fields.extend([
                        (
                            "constraint pair admissions",
                            counters.constraint_pair_admissions(),
                            previous_counters.constraint_pair_admissions(),
                        ),
                        (
                            "constraint pair probes",
                            counters.constraint_pair_admissions()
                                + counters.constraint_pair_duplicates(),
                            previous_counters.constraint_pair_admissions()
                                + previous_counters.constraint_pair_duplicates(),
                        ),
                        (
                            "constraint pair cache capacity",
                            counters.constraint_pair_cache_capacity(),
                            previous_counters.constraint_pair_cache_capacity(),
                        ),
                        (
                            "constraint pair cache retained bytes",
                            counters.constraint_pair_cache_retained_bytes(),
                            previous_counters.constraint_pair_cache_retained_bytes(),
                        ),
                        (
                            "semantic arena retained bytes",
                            counters.semantic_arena_retained_bytes(),
                            previous_counters.semantic_arena_retained_bytes(),
                        ),
                        (
                            "semantic arena peak bytes",
                            counters.semantic_arena_peak_bytes(),
                            previous_counters.semantic_arena_peak_bytes(),
                        ),
                        (
                            "inference-session retained bytes",
                            counters.inference_session_retained_bytes(),
                            previous_counters.inference_session_retained_bytes(),
                        ),
                        (
                            "inference-session peak bytes",
                            counters.inference_session_peak_bytes(),
                            previous_counters.inference_session_peak_bytes(),
                        ),
                    ]);
                }
                for (name, current, prior) in linear_fields {
                    if prior != 0 {
                        let doubled = current
                            .checked_mul(2)
                            .expect("F4 scale current doubling comparison fits usize");
                        let fivefold = prior
                            .checked_mul(5)
                            .expect("F4 scale prior ratio comparison fits usize");
                        assert!(
                            doubled < fivefold,
                            "{} {} exceeded the declared <2.5x doubling bound",
                            witness.name,
                            name
                        );
                    } else {
                        assert_eq!(current, 0, "{} {} grew from zero", witness.name, name);
                    }
                }
            }
            previous = Some(ScaleRatioBaseline {
                counters,
                summary,
                pair_work_is_linear: witness.pair_work_is_linear,
            });
        }
    }

    #[test]
    fn f4_orders_internal_drafts_installs_and_incoming_with_a_bounded_observer() {
        let batch = collect(module("my a = b; my b = a; my c = a", "f4-order.yu"));
        let (solved, observer, _) = InferenceSession::new(batch).run_with_observer(32).unwrap();
        assert_eq!(observer.omitted, 0);
        let barrier = observer
            .events
            .iter()
            .position(|event| matches!(event, ExecutionEvent::DraftsVisible(_, 2)))
            .expect("mutual component barrier");
        assert!(
            observer.events[..barrier]
                .iter()
                .any(|event| matches!(event, ExecutionEvent::InternalUse(_)))
        );
        assert_eq!(
            observer.events[..barrier]
                .iter()
                .filter(|event| matches!(event, ExecutionEvent::Drafted(_)))
                .count(),
            2
        );
        let first_incoming = observer
            .events
            .iter()
            .position(|event| matches!(event, ExecutionEvent::IncomingUse(_, _)))
            .expect("closed incoming use");
        assert!(
            observer.events[..first_incoming]
                .iter()
                .filter(|event| matches!(event, ExecutionEvent::Installed(_)))
                .count()
                >= 2
        );
        assert!(solved.errors().is_empty());
    }

    #[test]
    #[should_panic(expected = "F4 scheme root maps to its exact dense definition position")]
    fn f4_generalization_rejects_a_member_with_a_mismatched_frozen_root_position() {
        let mut batch = collect(module("my only = 42", "f4-root-position.yu"));
        let definition = batch.definitions[0].definition.clone();
        let root = batch.definitions[0].root.clone();
        *batch
            .root_definition_positions
            .get_mut(&root)
            .expect("collected definition owns a frozen scheme position") = 1;
        let mut summary_reads = 0;
        let mut finalization = ClosedTypeFinalizationSession::try_new().unwrap();
        let _ = InferenceSession::generalize(
            &batch,
            &[],
            &[],
            &mut finalization,
            &definition,
            &mut summary_reads,
            false,
        );
    }

    #[test]
    fn f4_synthetic_seeded_internal_cycle_coalesces_to_int_and_retains_use_provenance() {
        let batch = synthetic_semantic_batch(
            "my left = right; my right = left",
            "f4-seeded-cycle.yu",
            &[0],
        );
        let (solved, _, summary) = InferenceSession::new(batch).run_with_observer(0).unwrap();
        for item in solved.hir().items() {
            let HirItem::Binding(binding) = item else {
                continue;
            };
            assert_eq!(
                solved.root_value_for(binding.definition_root()),
                Ok(SolvedValue::Int)
            );
        }
        let counters = solved.counters();
        assert_eq!(counters.scc_execution_internal_use_connections(), 2);
        assert_eq!(counters.scc_execution_incoming_instantiations(), 0);
        assert_eq!(counters.routed_use_provenance_len(), 2);
        assert_eq!(counters.constraint_store_growths(), 0);
        assert_eq!(counters.constraint_store_rebuilds(), 0);
        assert_eq!(
            summary.false_to_true_transitions, 4,
            "the one Int seed reaches the two root and two Name-value rows only through canonical lower-bound insertion"
        );
    }

    #[test]
    fn f4_error_and_complete_unconstrained_roots_both_generalize_to_never() {
        let hir = module(
            "my broken = @; my empty = missing; my integer = 42",
            "f4-errors.yu",
        );
        let solved = SolvedModule::solve(collect(hir.clone())).unwrap();
        let roots = hir
            .items()
            .iter()
            .filter_map(|item| match item {
                HirItem::Binding(binding) => Some(binding),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            solved.root_value_for(roots[0].definition_root()),
            Ok(SolvedValue::Never)
        );
        assert_eq!(
            solved.root_value_for(roots[1].definition_root()),
            Ok(SolvedValue::Never)
        );
        assert_eq!(
            solved.root_value_for(roots[2].definition_root()),
            Ok(SolvedValue::Int)
        );
    }

    #[test]
    fn f4_incoming_int_routes_keep_the_exact_definition_use_cause() {
        let batch = collect(module(
            "my source = 42; my sink = source",
            "f4-provenance.yu",
        ));
        let use_record = batch.definition_uses()[0].clone();
        let (solved, _, summary) = InferenceSession::new(batch).run_with_observer(0).unwrap();
        let slot_zero = ConstraintOccurrenceId::new(use_record.occurrence().clone(), 0);
        assert!(
            solved
                .store()
                .provenance()
                .iter()
                .any(|edge| { edge.cause() == &CauseId::for_occurrence(slot_zero.clone()) })
        );
        assert_eq!(solved.counters().scc_execution_int_instantiation_facts(), 1);
        assert_eq!(
            summary.false_to_true_transitions, 4,
            "the incoming Int reaches the sink value/root through canonical lower-bound insertion after the source literal/root transitions"
        );
    }

    #[test]
    fn f4_bottom_incoming_route_is_trivial_and_retains_no_slot_zero_fact() {
        let hir = module(
            "my bottom = missing; my sink = bottom",
            "f4-bottom-route.yu",
        );
        let batch = collect(hir.clone());
        let initial_facts = batch.occurrences().len();
        let (solved, _, summary) = InferenceSession::new(batch).run_with_observer(0).unwrap();
        assert_eq!(solved.store().facts().len(), initial_facts);
        assert_eq!(
            solved
                .counters()
                .scc_execution_bottom_trivial_instantiations(),
            1
        );
        assert_eq!(solved.counters().scc_execution_int_instantiation_facts(), 0);
        let HirItem::Binding(sink) = &hir.items()[1] else {
            panic!("sink remains a binding")
        };
        assert_eq!(
            solved.root_value_for(sink.definition_root()),
            Ok(SolvedValue::Never),
            "a Bottom predecessor finalizes its dependent root as Bottom/Never"
        );
        assert_eq!(
            summary.false_to_true_transitions, 0,
            "Bottom routing has no value-bound predecessor or summary transition"
        );
    }

    #[test]
    fn f4_route_cause_mismatch_is_atomic_for_internal_and_closed_routes() {
        let mut internal = collect(module(
            "my left = right; my right = left",
            "f4-cause-internal.yu",
        ));
        let internal_id = internal.definition_uses()[0].id.clone();
        let other_id = internal.definition_uses()[1].id.clone();
        internal.definition_uses[0].cause = DefinitionUseCause::for_use(other_id);
        let mut session = InferenceSession::new(internal);
        let result = session.route_internal(&internal_id);
        assert_eq!(result, Err(SolveAvailabilityError::CauseMismatch));
        assert!(session.store.facts().is_empty());
        assert!(session.store.provenance().is_empty());
        assert!(session.typed_pairs.is_empty());
        assert!(session.typed_worklist.is_empty());
        assert!(session.routed_uses.is_empty());
        assert!(session.routed_use_positions.is_empty());

        for scheme in [F4SchemeBody::Int, F4SchemeBody::Bottom] {
            let mut batch = collect(module(
                "my source = 42; my sink = source",
                "f4-cause-closed.yu",
            ));
            let route_id = batch.definition_uses()[0].id.clone();
            let unrelated = DefinitionUseId::new(
                batch.collection_artifact.clone(),
                batch.projection_order[0].clone(),
            );
            batch.definition_uses[0].cause = DefinitionUseCause::for_use(unrelated);
            let mut session = InferenceSession::new(batch);
            session.schemes[0] = Some(
                session
                    .finalization
                    .as_mut()
                    .expect("test session has not finished")
                    .finalize_scheme(|finalizer| {
                        let predicate = match scheme {
                            F4SchemeBody::Int => finalizer.positive_int()?,
                            F4SchemeBody::Bottom => finalizer.positive_bottom()?,
                        };
                        finalizer.set_scheme(0, &[], predicate)
                    })
                    .unwrap()
                    .into_parts()
                    .0,
            );
            let result = session.route_incoming(&route_id);
            assert_eq!(result, Err(SolveAvailabilityError::CauseMismatch));
            assert!(session.store.facts().is_empty());
            assert!(session.store.provenance().is_empty());
            assert!(session.typed_pairs.is_empty());
            assert!(session.typed_worklist.is_empty());
            assert!(session.routed_uses.is_empty());
            assert!(session.routed_use_positions.is_empty());
            assert_eq!(
                session
                    .execution_counters
                    .scc_execution_int_instantiation_facts(),
                0
            );
            assert_eq!(
                session
                    .execution_counters
                    .scc_execution_bottom_trivial_instantiations(),
                0
            );
        }
    }

    #[test]
    fn f4_solve_rejects_foreign_artifacts_before_any_partial_result_exists() {
        let local_hir = module("my local = 42", "f4-foreign-local.yu");
        let foreign_hir = module("my foreign = 42", "f4-foreign-other.yu");
        let foreign_batch = collect(foreign_hir.clone());
        let foreign_term = foreign_batch.occurrences()[0].upper();
        let foreign_occurrence = |mut batch: ConstraintBatch| {
            let local = batch.occurrences[0].clone();
            batch.occurrences[0] = ConstraintOccurrence {
                id: local.id.clone(),
                cause: local.cause.clone(),
                lower: foreign_term,
                upper: local.upper,
            };
            batch
        };

        let mut session = InferenceSession::new(foreign_occurrence(collect(local_hir.clone())));
        assert_eq!(
            session.admit_all_collected_facts(),
            Err(SolveAvailabilityError::ArtifactMismatch)
        );
        assert!(session.store.facts().is_empty());
        assert!(session.store.provenance().is_empty());
        assert!(session.typed_pairs.is_empty());
        assert!(session.typed_worklist.is_empty());
        assert!(session.routed_uses.is_empty());

        assert!(matches!(
            SolvedModule::solve(foreign_occurrence(collect(local_hir))),
            Err(SolveAvailabilityError::ArtifactMismatch)
        ));
    }

    #[test]
    fn f4_cross_kind_is_local_and_mutates_no_value_or_route_state() {
        let cross_kind_batch = || {
            let hir = module("42", "f4-cross-kind-atomic.yu");
            let mut batch = collect(hir);
            retain_batch_occurrences(&mut batch, |occurrence| occurrence.id.local_slot == 0);
            batch.occurrences[0].lower = batch.collected_leaf_term(Leaf::EffectBottomPositive);
            batch
        };

        let mut session = InferenceSession::new(cross_kind_batch());
        session.admit_all_collected_facts().unwrap();
        assert!(session.store.facts().is_empty());
        assert!(session.store.provenance().is_empty());
        assert!(session.typed_pairs.is_empty());
        assert!(session.typed_worklist.is_empty());
        assert!(session.routed_uses.is_empty());
        assert!(session.routed_use_positions.is_empty());
        assert!(session.bounds.iter().all(|bounds| {
            bounds.direct_lower_rows.is_empty()
                && bounds.direct_upper_rows.is_empty()
                && bounds.exact_non_variable_lowers.is_empty()
                && bounds.exact_non_variable_uppers.is_empty()
                && !bounds.has_int_positive_lower
        }));
        assert!(session.occurrence_exact_bounds.iter().all(|exact| {
            !exact.value_lower_int
                && !exact.value_upper_int
                && !exact.effect_lower_bottom
                && !exact.effect_upper_empty
        }));
        assert!(matches!(
            session.errors.as_slice(),
            [SolverError {
                kind: SolverErrorKind::CrossKind { .. },
                ..
            }]
        ));

        // CrossKind is deliberately a successful, local diagnostic path.  A
        // completed solve retains that diagnostic rather than manufacturing a
        // partial availability result.
        let solved = SolvedModule::solve(cross_kind_batch()).unwrap();
        assert_eq!(solved.errors().len(), 1);
        assert!(solved.store().facts().is_empty());
        assert!(solved.counters().solver_error_workspace_capacity() >= solved.errors().len());
    }

    #[test]
    fn f4_real_session_receipt_and_identity_failures_are_atomic() {
        // These cfg(test)-only seams sit at the existing store owners.  The
        // real session executes normal collection/solve setup, then maps the
        // exact availability failure without exposing a partial result.
        let mut receipt_session =
            InferenceSession::new(collect(module("42", "f4-receipt-atomic.yu")));
        receipt_session.inject_next_provenance_failure(ConstraintError::ReceiptMismatch);
        assert!(matches!(
            receipt_session.run(),
            Err(SolveAvailabilityError::ReceiptMismatch)
        ));

        let mut exhaustion_session =
            InferenceSession::new(collect(module("42", "f4-exhaustion-atomic.yu")));
        exhaustion_session.inject_next_admission_failure(ConstraintError::IdentityExhausted);
        assert!(matches!(
            exhaustion_session.run(),
            Err(SolveAvailabilityError::IdentityExhausted)
        ));
    }

    #[test]
    fn f5b_finalization_availability_exhaustion_returns_no_module_or_final_counter_work() {
        let batch = || {
            let batch = collect(module(
                "my left = right; my right = left",
                "f5b-finalization-atomic.yu",
            ));
            assert_eq!(batch.counters.scc_maximum_component_size, 2);
            batch
        };

        // `run` owns the only route to a `SolvedModule`; the injected second
        // finalization fails after the first succeeds, so it returns no
        // partial module.
        let mut run_session = InferenceSession::new(batch());
        run_session.inject_finalization_failure_after(1);
        assert!(matches!(
            run_session.run(),
            Err(SolveAvailabilityError::IdentityExhausted)
        ));

        // Inspect the same path before ownership is consumed. The earlier
        // session scheme exists, but component publication begins only after
        // every member draft has finalized successfully.
        let mut session = InferenceSession::new(batch());
        session.inject_finalization_failure_after(1);
        session.admit_all_collected_facts().unwrap();
        assert_eq!(
            session.execute_scc_plan(),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert_eq!(session.successful_finalizations, 1);
        assert_eq!(session.drafts.len(), 1);
        assert!(session.schemes.iter().all(Option::is_none));
        assert_eq!(session.execution_counters.finish_projection_visits, 0);
        assert_eq!(
            session.execution_counters.solved_projection_retained_bytes, 0,
            "final counters are neither combined nor published after finalization availability failure"
        );
        assert!(
            session
                .finalization
                .as_ref()
                .expect("test session has not finished")
                .scheme_view(&session.drafts[0].0)
                .is_ok()
        );
    }

    #[test]
    fn f5b_finalization_failure_keeps_the_f4_availability_boundary_exhaustive() {
        // F5b may only reuse F4's exhaustion result. A malformed draft is an
        // internal finalizer invariant, so it cannot manufacture a fifth
        // solver availability result or a partially published module.
        assert_eq!(
            InferenceSession::map_finalization_error(ClosedTypeFinalizeError::IdentityExhausted),
            SolveAvailabilityError::IdentityExhausted
        );
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                InferenceSession::map_finalization_error(ClosedTypeFinalizeError::InvalidDraft)
            }))
            .is_err()
        );
    }

    #[test]
    fn f4_all_obsolete_finish_only_accessors_are_documented_zeroes() {
        let counters = SolvedModule::solve(collect(module("42", "f4-deprecated-zeroes.yu")))
            .unwrap()
            .counters();
        assert_eq!(counters.adjacency_appends(), 0);
        assert_eq!(counters.adjacency_visits(), 0);
        assert_eq!(counters.maximum_fan_out(), 0);
        assert_eq!(counters.solved_root_index_probes(), 0);
        assert_eq!(counters.solved_root_index_capacity(), 0);
        assert_eq!(counters.solved_root_index_retained_bytes(), 0);
        assert_eq!(counters.bounds_workspace_capacity(), 0);
        assert_eq!(counters.bounds_workspace_retained_bytes(), 0);
        assert_eq!(counters.fanout_index_capacity(), 0);
        assert_eq!(counters.fanout_index_retained_bytes(), 0);
        assert_eq!(counters.solver_workspace_retained_bytes(), 0);
        assert_eq!(counters.failed_component_workspace_capacity(), 0);
        assert_eq!(counters.failed_component_workspace_retained_bytes(), 0);
        assert!(counters.solver_error_workspace_capacity() > 0);
        assert_eq!(
            counters.solver_error_workspace_retained_bytes(),
            checked_capacity_bytes::<SolverError>(
                counters.solver_error_workspace_capacity(),
                "F4 solver error workspace witness",
            )
        );
    }

    #[test]
    fn f4_forward_and_backward_source_chains_generalize_each_root() {
        for (source, path) in [
            ("my head = tail; my tail = 42", "f4-forward-chain.yu"),
            ("my tail = 42; my head = tail", "f4-backward-chain.yu"),
        ] {
            let hir = module(source, path);
            let solved = SolvedModule::solve(collect(hir.clone())).unwrap();
            for item in hir.items() {
                let HirItem::Binding(binding) = item else {
                    continue;
                };
                assert_eq!(
                    solved.root_value_for(binding.definition_root()),
                    Ok(SolvedValue::Int),
                    "{path} generalizes every chain member"
                );
            }
        }
    }

    #[test]
    fn f4_execution_uses_frozen_ordinals_not_definition_spelling_or_path() {
        let short_hir = module("my a = 42; my b = a", "a.yu");
        let long_hir = module(
            "my extraordinarily_long_source_binding_name = 42; my extraordinarily_long_sink_binding_name = extraordinarily_long_source_binding_name",
            "nested/a/much/longer/module/path/for/f4-ordinal-routing.yu",
        );
        let short = SolvedModule::solve(collect(short_hir.clone())).unwrap();
        let long = SolvedModule::solve(collect(long_hir.clone())).unwrap();
        for solved in [&short, &long] {
            for item in solved.hir().items() {
                let HirItem::Binding(binding) = item else {
                    continue;
                };
                assert_eq!(
                    solved.root_value_for(binding.definition_root()),
                    Ok(SolvedValue::Int)
                );
            }
        }
        let comparable = |counters: &ProductionCounters| {
            (
                counters.scc_execution_component_visits(),
                counters.scc_execution_internal_use_connections(),
                counters.scc_execution_incoming_instantiations(),
                counters.constraint_pair_admissions(),
                counters.constraint_pair_duplicates(),
                counters.lower_bound_insertions(),
                counters.upper_bound_insertions(),
                counters.lower_bound_replays(),
                counters.upper_bound_replays(),
            )
        };
        assert_eq!(comparable(&short.counters()), comparable(&long.counters()));
        // Query accounting remains at the public root-query boundary; F4
        // execution itself cannot charge source identity hash/equality work.
        assert_eq!(short.counters().scheme_root_query_probes(), 2);
        assert_eq!(long.counters().scheme_root_query_probes(), 2);
        assert!(
            long.counters()
                .scheme_root_query_identity_hash_byte_incidences()
                > short
                    .counters()
                    .scheme_root_query_identity_hash_byte_incidences(),
            "successful public root queries charge their actual retained identity payload"
        );
        assert!(
            long.counters()
                .scheme_root_query_logical_successful_equality_byte_incidences()
                > short
                    .counters()
                    .scheme_root_query_logical_successful_equality_byte_incidences()
        );
    }

    #[test]
    fn f4_unseeded_self_and_mutual_cycles_generalize_to_never() {
        for (source, path) in [
            ("my self_ref = self_ref", "f4-unseeded-self.yu"),
            ("my left = right; my right = left", "f4-unseeded-mutual.yu"),
        ] {
            let hir = module(source, path);
            let solved = SolvedModule::solve(collect(hir.clone())).unwrap();
            for item in hir.items() {
                let HirItem::Binding(binding) = item else {
                    continue;
                };
                assert_eq!(
                    solved.root_value_for(binding.definition_root()),
                    Ok(SolvedValue::Never),
                    "{path} remains unseeded"
                );
            }
        }
    }

    #[test]
    fn f4_resolved_name_keeps_slots_one_to_three_and_routes_slot_zero_in_store_order() {
        let hir = module("my source = 42; my sink = source", "f4-name-slots.yu");
        let batch = collect(hir.clone());
        let use_record = batch.definition_uses()[0].clone();
        let use_occurrence = use_record.occurrence().clone();
        assert_eq!(
            batch
                .occurrences()
                .iter()
                .filter(|fact| fact.id().occurrence() == &use_occurrence)
                .map(|fact| fact.id().local_slot())
                .collect::<Vec<_>>(),
            vec![1, 2, 3],
        );
        let initial_facts = batch.occurrences().len();
        let solved = SolvedModule::solve(batch).unwrap();
        let route_id = ConstraintOccurrenceId::new(use_occurrence, 0);
        assert_eq!(solved.store().facts().len(), initial_facts + 1);
        assert_eq!(
            solved.store().facts().last().unwrap().id().index(),
            initial_facts as u32
        );
        assert_eq!(
            solved.store().provenance().last().unwrap().cause(),
            &CauseId::for_occurrence(route_id)
        );
        let projection = solved
            .projection_for(match &hir.items()[1] {
                HirItem::Binding(binding) => binding.value().occurrence(),
                _ => panic!("sink binding"),
            })
            .unwrap();
        assert_eq!(
            (projection.value(), projection.effect()),
            (SolvedValue::Unknown, SolvedEffect::Empty),
            "a resolved binding-body Name retains its exact occurrence projection"
        );
    }

    #[test]
    fn f4_chain_scale_matrix_is_linear() {
        assert_f4_scale_witness([1_000, 2_000, 4_000].map(|n| SyntheticScaleWitness {
            name: "chain",
            // M/I/X/S; E/L/U/T/J = n-1/0/n-1/1; n-1/2n-1/0/n-1/0.
            components: n,
            definitions: n,
            internal_uses: 0,
            incoming_uses: n - 1,
            ordinary_initial_value_pair_probes: n - 1,
            synthetic_seed_value_pair_probes: 1,
            direct_edges: n - 1,
            exact_lower_memberships: 2 * n - 1,
            exact_upper_memberships: 0,
            transmission_attempts: n - 1,
            same_row_atom_intersections: 0,
            replay_attempts: n - 1,
            constraint_pair_admissions: 3 * n - 2,
            typed_effect_pair_admissions: 2 * n - 1,
            constraint_pair_duplicates: 0,
            typed_effect_pair_duplicates: n - 2,
            edges: (1..n).map(|index| (index, index - 1)).collect(),
            seeded_roots: vec![0],
            pair_work_is_linear: true,
        }));
    }

    #[test]
    fn f4_diamond_scale_matrix_is_linear() {
        assert_f4_scale_witness([1_000, 2_000, 4_000].map(|n| {
            SyntheticScaleWitness {
                name: "diamond",
                // M/I/X/S; E/L/U/T/J = n/0/n/n/4; n/2n/0/n/0.
                components: n,
                definitions: n,
                internal_uses: 0,
                incoming_uses: n,
                ordinary_initial_value_pair_probes: n,
                synthetic_seed_value_pair_probes: n / 4,
                direct_edges: n,
                exact_lower_memberships: 2 * n,
                exact_upper_memberships: 0,
                transmission_attempts: n,
                same_row_atom_intersections: 0,
                replay_attempts: n,
                constraint_pair_admissions: 3 * n,
                typed_effect_pair_admissions: 2 * n + 1,
                constraint_pair_duplicates: n / 4,
                typed_effect_pair_duplicates: n - 1,
                edges: (0..n / 4)
                    .flat_map(|group| {
                        let base = group * 4;
                        [
                            (base, base + 1),
                            (base, base + 2),
                            (base + 1, base + 3),
                            (base + 2, base + 3),
                        ]
                    })
                    .collect(),
                seeded_roots: (0..n / 4).map(|group| group * 4 + 3).collect(),
                pair_work_is_linear: true,
            }
        }));
    }

    #[test]
    fn f4_bounded_cycle_scale_matrix_is_linear() {
        assert_f4_scale_witness([1_000, 2_000, 4_000].map(|n| {
            SyntheticScaleWitness {
                name: "bounded-cycle",
                // M/I/X/S; E/L/U/T/J = n/n/0/n/2; 2n/2n/0/2n/0.
                components: n / 2,
                definitions: n,
                internal_uses: n,
                incoming_uses: 0,
                ordinary_initial_value_pair_probes: n,
                synthetic_seed_value_pair_probes: n / 2,
                direct_edges: 2 * n,
                exact_lower_memberships: 2 * n,
                exact_upper_memberships: 0,
                transmission_attempts: 2 * n,
                same_row_atom_intersections: 0,
                replay_attempts: 2 * n,
                constraint_pair_admissions: 4 * n,
                typed_effect_pair_admissions: 2 * n + 1,
                constraint_pair_duplicates: n / 2,
                typed_effect_pair_duplicates: n - 1,
                edges: (0..n / 2)
                    .flat_map(|pair| [(pair * 2, pair * 2 + 1), (pair * 2 + 1, pair * 2)])
                    .collect(),
                seeded_roots: (0..n / 2).map(|pair| pair * 2).collect(),
                pair_work_is_linear: true,
            }
        }));
    }

    fn unbounded_cycle_witness(n: usize) -> SyntheticScaleWitness {
        SyntheticScaleWitness {
            name: "unbounded-cycle",
            // M/I/X/S; E/L/U/T/J = n/n/0/1; 2n/2n/0/2n/0.
            components: 1,
            definitions: n,
            internal_uses: n,
            incoming_uses: 0,
            ordinary_initial_value_pair_probes: n,
            synthetic_seed_value_pair_probes: 1,
            direct_edges: 2 * n,
            exact_lower_memberships: 2 * n,
            exact_upper_memberships: 0,
            transmission_attempts: 2 * n,
            same_row_atom_intersections: 0,
            replay_attempts: 2 * n,
            constraint_pair_admissions: 4 * n,
            typed_effect_pair_admissions: 2 * n + 1,
            constraint_pair_duplicates: 1,
            typed_effect_pair_duplicates: n - 1,
            edges: (0..n).map(|index| (index, (index + 1) % n)).collect(),
            seeded_roots: vec![0],
            pair_work_is_linear: true,
        }
    }

    #[test]
    fn f4_unbounded_cycle_scale_1k_keeps_direct_frontier_linear() {
        assert_f4_scale_witness(std::iter::once(unbounded_cycle_witness(1_000)));
    }

    #[test]
    fn f4_unbounded_cycle_scale_ratio_evidence_1k_2k_4k() {
        // This is the sole unbounded-cycle ratio witness.  Unlike the three
        // named-size timing witnesses below, it deliberately performs the
        // complete actual 1k/2k/4k sequence in one non-timed process so every
        // capacity, retained/peak, probe, growth, and resource field compares
        // against a real prior ProductionCounters observation.
        assert_f4_scale_witness([1_000, 2_000, 4_000].map(unbounded_cycle_witness));
    }

    #[test]
    fn f4_unbounded_cycle_scale_2k_keeps_direct_frontier_linear() {
        // This capped timing process solves only its named size.  Exact per-N
        // E/L/U/T/J and resource assertions remain in the shared witness.
        assert_f4_scale_witness(std::iter::once(unbounded_cycle_witness(2_000)));
    }

    #[test]
    fn f4_unbounded_cycle_scale_4k_keeps_direct_frontier_linear() {
        // This capped timing process solves only its named size; actual
        // doubling evidence belongs to the dedicated non-timed test above.
        assert_f4_scale_witness(std::iter::once(unbounded_cycle_witness(4_000)));
    }

    #[test]
    fn f4_wide_internal_fanout_scale_matrix_keeps_direct_frontier_linear() {
        assert_f4_scale_witness([1_000, 2_000, 4_000].map(|n| SyntheticScaleWitness {
            name: "wide-internal-fanout",
            // M/I/X/S; E/L/U/T/J = 2n-2/2n-2/0/1; 4n-4/3n-2/0/4n-4/0.
            components: 1,
            definitions: n,
            internal_uses: 2 * n - 2,
            incoming_uses: 0,
            ordinary_initial_value_pair_probes: 2 * n - 2,
            synthetic_seed_value_pair_probes: 1,
            direct_edges: 4 * n - 4,
            exact_lower_memberships: 3 * n - 2,
            exact_upper_memberships: 0,
            transmission_attempts: 4 * n - 4,
            same_row_atom_intersections: 0,
            replay_attempts: 4 * n - 4,
            constraint_pair_admissions: 7 * n - 6,
            typed_effect_pair_admissions: 4 * n - 3,
            constraint_pair_duplicates: n - 1,
            typed_effect_pair_duplicates: 2 * n - 3,
            edges: (1..n).flat_map(|index| [(0, index), (index, 0)]).collect(),
            seeded_roots: vec![0],
            pair_work_is_linear: true,
        }));
    }

    #[test]
    fn f4_distinct_use_routes_share_one_source_scheme_scale_matrix_is_linear() {
        assert_f4_scale_witness([1_000, 2_000, 4_000].map(|n| SyntheticScaleWitness {
            name: "distinct-use-routes-share-one-source-scheme",
            // M/I/X/S; E/L/U/T/J = n/0/n/1; n/n+2/0/n/0.
            components: 2,
            definitions: 2,
            internal_uses: 0,
            incoming_uses: n,
            ordinary_initial_value_pair_probes: n,
            synthetic_seed_value_pair_probes: 1,
            direct_edges: n,
            exact_lower_memberships: n + 2,
            exact_upper_memberships: 0,
            transmission_attempts: n,
            same_row_atom_intersections: 0,
            replay_attempts: n,
            constraint_pair_admissions: 2 * n + 2,
            typed_effect_pair_admissions: 2 * n + 1,
            constraint_pair_duplicates: n - 1,
            typed_effect_pair_duplicates: n - 1,
            edges: vec![(0, 1); n],
            seeded_roots: vec![1],
            pair_work_is_linear: true,
        }));
    }

    #[derive(Debug, Eq, PartialEq)]
    struct FrontierReferenceSnapshot {
        variable_reachability: HashSet<CanonicalValuePairKey>,
        exact_lowers: Vec<HashSet<ValueEndpointKey>>,
        exact_uppers: Vec<HashSet<ValueEndpointKey>>,
        terminal_pairs: HashSet<CanonicalValuePairKey>,
        int_lower_summary: Vec<bool>,
    }

    fn reference_frontier_closure(
        rows: usize,
        inputs: &[CanonicalValuePairKey],
    ) -> FrontierReferenceSnapshot {
        let mut lower = vec![HashSet::new(); rows];
        let mut upper = vec![HashSet::new(); rows];
        let mut pairs = HashSet::new();
        let mut pending = VecDeque::from(inputs.to_vec());
        while let Some(key) = pending.pop_front() {
            if !pairs.insert(key) {
                continue;
            }
            if let ValueEndpointKey::ValueRow(row) = key.lower {
                let row = row as usize;
                if upper[row].insert(key.upper) {
                    pending.extend(
                        lower[row]
                            .iter()
                            .copied()
                            .map(|lower| CanonicalValuePairKey {
                                lower,
                                upper: key.upper,
                            }),
                    );
                }
            }
            if let ValueEndpointKey::ValueRow(row) = key.upper {
                let row = row as usize;
                if lower[row].insert(key.lower) {
                    pending.extend(
                        upper[row]
                            .iter()
                            .copied()
                            .map(|upper| CanonicalValuePairKey {
                                lower: key.lower,
                                upper,
                            }),
                    );
                }
            }
        }
        let variable_reachability = pairs
            .iter()
            .copied()
            .filter(|key| {
                matches!(key.lower, ValueEndpointKey::ValueRow(_))
                    && matches!(key.upper, ValueEndpointKey::ValueRow(_))
            })
            .collect();
        let terminal_pairs = pairs
            .iter()
            .copied()
            .filter(|key| {
                !matches!(key.lower, ValueEndpointKey::ValueRow(_))
                    && !matches!(key.upper, ValueEndpointKey::ValueRow(_))
            })
            .collect();
        let int_lower_summary = lower
            .iter()
            .map(|bounds| bounds.contains(&ValueEndpointKey::IntPositive))
            .collect();
        FrontierReferenceSnapshot {
            variable_reachability,
            exact_lowers: lower
                .into_iter()
                .map(|bounds| {
                    bounds
                        .into_iter()
                        .filter(|key| !matches!(key, ValueEndpointKey::ValueRow(_)))
                        .collect()
                })
                .collect(),
            exact_uppers: upper
                .into_iter()
                .map(|bounds| {
                    bounds
                        .into_iter()
                        .filter(|key| !matches!(key, ValueEndpointKey::ValueRow(_)))
                        .collect()
                })
                .collect(),
            terminal_pairs,
            int_lower_summary,
        }
    }

    fn direct_frontier_snapshot(
        batch: &ConstraintBatch,
        rows: usize,
        inputs: &[CanonicalValuePairKey],
    ) -> (
        FrontierReferenceSnapshot,
        SummaryObservation,
        ProductionCounters,
    ) {
        // This is intentionally a production harness, not a second closure.
        // The exhaustive test below compares its extracted session state to
        // `reference_frontier_closure`; keeping the two routes independent is
        // the regression contract F5 §35 retains from F4.
        let mut session = InferenceSession::try_new(batch.clone())
            .expect("the tiny production harness has capacity");
        while session.bounds.len() < rows {
            session
                .fresh_value_at_level(1)
                .expect("tiny production harness has live identity");
        }
        let occurrence = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 0);
        let cause = CauseId::for_occurrence(occurrence.clone());
        for &input in inputs {
            session
                .constrain_live_value(input, &occurrence, &cause)
                .expect("tiny production frontier has capacity");
        }
        let mut variable_reachability = HashSet::new();
        // The production memo intentionally has no transitive Var/Var pairs
        // (F5 §5).  Extract the reachability observation from the production
        // direct rows instead of mistaking memo membership for the old F4
        // closure representation.
        for source in 0..rows {
            let mut seen = vec![false; rows];
            let mut pending = VecDeque::new();
            pending.push_back(source as u32);
            while let Some(lower) = pending.pop_front() {
                for &upper in &session.bounds[lower as usize].direct_upper_rows {
                    if seen[upper as usize] {
                        continue;
                    }
                    seen[upper as usize] = true;
                    variable_reachability.insert(CanonicalValuePairKey {
                        lower: ValueEndpointKey::ValueRow(source as u32),
                        upper: ValueEndpointKey::ValueRow(upper),
                    });
                    pending.push_back(upper);
                }
            }
        }
        let snapshot = FrontierReferenceSnapshot {
            variable_reachability,
            exact_lowers: session.bounds[..rows]
                .iter()
                .map(|row| row.exact_non_variable_lowers.iter().copied().collect())
                .collect(),
            exact_uppers: session.bounds[..rows]
                .iter()
                .map(|row| row.exact_non_variable_uppers.iter().copied().collect())
                .collect(),
            terminal_pairs: session
                .typed_pairs
                .keys()
                .filter_map(|key| match *key {
                    TypedPairKey::Value(pair)
                        if !matches!(pair.lower, ValueEndpointKey::ValueRow(_))
                            && !matches!(pair.upper, ValueEndpointKey::ValueRow(_)) =>
                    {
                        Some(pair)
                    }
                    _ => None,
                })
                .collect(),
            int_lower_summary: session.bounds[..rows]
                .iter()
                .map(|row| row.has_int_positive_lower)
                .collect(),
        };
        let observation = SummaryObservation {
            ordinary_initial_value_pair_probes: 0,
            synthetic_seed_value_pair_probes: 0,
            reads: 0,
            false_to_true_transitions: 0,
            frontier_pushes: session.typed_pair_worklist_pushes,
            frontier_pops: session.typed_pair_worklist_pops,
            frontier_maximum_live: session.typed_pair_worklist_maximum_live,
            frontier_capacity: session.typed_worklist.capacity(),
            frontier_capacity_growths: session.typed_pair_worklist_capacity_growths,
            frontier_retained_bytes: checked_capacity_bytes::<TypedWorkItem>(
                session.typed_worklist.capacity(),
                "F5b production typed frontier queue",
            ),
            frontier_peak_bytes: session.typed_pair_worklist_peak_bytes,
            direct_edges: session.typed_direct_edges,
            exact_lower_memberships: session.typed_exact_lower_memberships,
            exact_upper_memberships: session.typed_exact_upper_memberships,
            transmission_attempts: session.typed_transmission_attempts,
            same_row_atom_intersections: session.typed_same_row_atom_intersections,
            semantic_arena_retained_bytes: 0,
            semantic_arena_peak_bytes: 0,
            inference_session_retained_bytes: 0,
            inference_session_peak_bytes: 0,
            resource_boundary_samples: 0,
            resource_boundary_coverage: 0,
            independent_queue_retained_bytes: 0,
            independent_finish_output_retained_bytes: 0,
            independent_semantic_arena_retained_bytes: 0,
            independent_inference_session_retained_bytes: 0,
            independent_semantic_arena_peak_bytes: 0,
            independent_inference_session_peak_bytes: 0,
        };
        (snapshot, observation, session.execution_counters)
    }

    #[test]
    fn f4_direct_frontier_exhaustively_matches_reference_for_zero_to_three_rows() {
        let batch = ConstraintBatch::collect(module("1", "f4-direct-frontier-production"))
            .expect("the tiny production harness collects");
        for rows in 0..=3 {
            let edge_count = rows * rows;
            for graph_bits in 0..(1usize << edge_count) {
                let edges = (0..rows)
                    .flat_map(|lower| {
                        (0..rows).filter_map(move |upper| {
                            (graph_bits & (1usize << (lower * rows + upper)) != 0).then_some(
                                CanonicalValuePairKey {
                                    lower: ValueEndpointKey::ValueRow(lower as u32),
                                    upper: ValueEndpointKey::ValueRow(upper as u32),
                                },
                            )
                        })
                    })
                    .collect::<Vec<_>>();
                for lower_bits in 0..(1usize << rows) {
                    for upper_bits in 0..(1usize << rows) {
                        let lowers = (0..rows)
                            .filter_map(|row| {
                                (lower_bits & (1usize << row) != 0).then_some(
                                    CanonicalValuePairKey {
                                        lower: ValueEndpointKey::IntPositive,
                                        upper: ValueEndpointKey::ValueRow(row as u32),
                                    },
                                )
                            })
                            .collect::<Vec<_>>();
                        let uppers = (0..rows)
                            .filter_map(|row| {
                                (upper_bits & (1usize << row) != 0).then_some(
                                    CanonicalValuePairKey {
                                        lower: ValueEndpointKey::ValueRow(row as u32),
                                        upper: ValueEndpointKey::IntNegative,
                                    },
                                )
                            })
                            .collect::<Vec<_>>();
                        let orders = [
                            [&edges[..], &lowers[..], &uppers[..]],
                            [&lowers[..], &edges[..], &uppers[..]],
                            [&uppers[..], &edges[..], &lowers[..]],
                            [&uppers[..], &lowers[..], &edges[..]],
                        ];
                        let reference_inputs = [&edges[..], &lowers[..], &uppers[..]].concat();
                        let reference = reference_frontier_closure(rows, &reference_inputs);
                        for ordered_parts in orders {
                            let inputs = ordered_parts.concat();
                            let (actual, observation, counters) =
                                direct_frontier_snapshot(&batch, rows, &inputs);
                            assert_eq!(actual, reference);
                            let expected_edges = edges.len();
                            let expected_lowers = reference
                                .exact_lowers
                                .iter()
                                .map(HashSet::len)
                                .sum::<usize>();
                            let expected_uppers = reference
                                .exact_uppers
                                .iter()
                                .map(HashSet::len)
                                .sum::<usize>();
                            let expected_intersections = reference
                                .exact_lowers
                                .iter()
                                .zip(&reference.exact_uppers)
                                .filter(|(lower, upper)| !lower.is_empty() && !upper.is_empty())
                                .count();
                            let expected_transmissions = edges
                                .iter()
                                .filter(|edge| {
                                    reference.exact_lowers[match edge.lower {
                                        ValueEndpointKey::ValueRow(row) => row as usize,
                                        _ => unreachable!(),
                                    }]
                                    .len()
                                        > 0
                                })
                                .count()
                                + edges
                                    .iter()
                                    .filter(|edge| {
                                        reference.exact_uppers[match edge.upper {
                                            ValueEndpointKey::ValueRow(row) => row as usize,
                                            _ => unreachable!(),
                                        }]
                                        .len()
                                            > 0
                                    })
                                    .count();
                            assert_eq!(observation.direct_edges, expected_edges);
                            assert_eq!(observation.exact_lower_memberships, expected_lowers);
                            assert_eq!(observation.exact_upper_memberships, expected_uppers);
                            assert_eq!(observation.transmission_attempts, expected_transmissions);
                            assert_eq!(
                                observation.same_row_atom_intersections,
                                expected_intersections
                            );
                            let direct_edge_transmission_limit =
                                expected_edges.checked_mul(2).expect(
                                    "F4 exhaustive direct-frontier transmission bound fits usize",
                                );
                            assert!(
                                observation.transmission_attempts <= direct_edge_transmission_limit
                            );
                            assert_eq!(observation.frontier_pushes, observation.frontier_pops);
                            assert_eq!(
                                observation.frontier_peak_bytes,
                                observation.frontier_retained_bytes
                            );
                            assert_eq!(
                                observation.frontier_pushes,
                                inputs.len()
                                    + observation.transmission_attempts
                                    + observation.same_row_atom_intersections
                            );
                            assert_eq!(
                                counters.constraint_pair_admissions()
                                    + counters.constraint_pair_duplicates(),
                                inputs.len()
                                    + observation.transmission_attempts
                                    + observation.same_row_atom_intersections,
                                "every direct input, frontier transmission, and atom intersection probes the cache once"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn f4_direct_frontier_intersects_same_row_atoms_in_both_insertion_orders() {
        let batch = ConstraintBatch::collect(module("1", "f4-direct-frontier-production"))
            .expect("the tiny production harness collects");
        let lower = CanonicalValuePairKey {
            lower: ValueEndpointKey::IntPositive,
            upper: ValueEndpointKey::ValueRow(0),
        };
        let upper = CanonicalValuePairKey {
            lower: ValueEndpointKey::ValueRow(0),
            upper: ValueEndpointKey::IntNegative,
        };
        for inputs in [[lower, upper], [upper, lower]] {
            let (snapshot, observation, counters) = direct_frontier_snapshot(&batch, 1, &inputs);
            assert_eq!(snapshot.int_lower_summary, vec![true]);
            assert_eq!(
                snapshot.terminal_pairs,
                HashSet::from([CanonicalValuePairKey {
                    lower: ValueEndpointKey::IntPositive,
                    upper: ValueEndpointKey::IntNegative,
                }])
            );
            assert_eq!(observation.exact_lower_memberships, 1);
            assert_eq!(observation.exact_upper_memberships, 1);
            assert_eq!(observation.same_row_atom_intersections, 1);
            assert_eq!(counters.lower_bound_replays(), 1);
            assert_eq!(counters.upper_bound_replays(), 0);
        }
    }

    #[test]
    fn f4_direct_frontier_transmits_a_seeded_chain_to_its_terminal_upper() {
        let batch = ConstraintBatch::collect(module("1", "f4-direct-frontier-production"))
            .expect("the tiny production harness collects");
        let inputs = [
            CanonicalValuePairKey {
                lower: ValueEndpointKey::IntPositive,
                upper: ValueEndpointKey::ValueRow(0),
            },
            CanonicalValuePairKey {
                lower: ValueEndpointKey::ValueRow(0),
                upper: ValueEndpointKey::ValueRow(1),
            },
            CanonicalValuePairKey {
                lower: ValueEndpointKey::ValueRow(1),
                upper: ValueEndpointKey::ValueRow(2),
            },
            CanonicalValuePairKey {
                lower: ValueEndpointKey::ValueRow(2),
                upper: ValueEndpointKey::IntNegative,
            },
        ];
        let (snapshot, observation, counters) = direct_frontier_snapshot(&batch, 3, &inputs);
        assert_eq!(snapshot.int_lower_summary, vec![true, true, true]);
        assert_eq!(observation.direct_edges, 2);
        assert_eq!(observation.transmission_attempts, 4);
        assert_eq!(observation.same_row_atom_intersections, 3);
        assert_eq!(counters.lower_bound_replays(), 5);
        assert_eq!(counters.upper_bound_replays(), 2);
    }

    #[test]
    fn exact_four_ordered_relations_and_empty_effect() {
        let hir = module("42", "one.yu");
        let batch = collect(hir.clone());
        assert_eq!(
            batch
                .occurrences()
                .iter()
                .map(|item| (
                    item.id().source_ordinal(),
                    item.id().local_slot(),
                    shape(&batch, item)
                ))
                .collect::<Vec<_>>(),
            vec![
                (0, 0, (Some(Leaf::IntPositive), None)),
                (0, 1, (None, Some(Leaf::IntNegative))),
                (0, 2, (Some(Leaf::EffectBottomPositive), None)),
                (0, 3, (None, Some(Leaf::EmptyEffectNegative))),
            ]
        );
        let solved = SolvedModule::solve(batch).unwrap();
        assert!(Arc::ptr_eq(solved.hir(), &hir));
        assert_eq!(
            solved.projection_for(root(&hir, 0).occurrence()).unwrap(),
            SolvedProjection {
                value: SolvedValue::Int,
                effect: SolvedEffect::Empty
            }
        );
    }
    #[test]
    fn deterministic_multi_expression_alpha_and_path_independence() {
        let a = module("my alpha = 0; 42; f 1; 42", "a/one.yu");
        let b = module("my beta = 0; 42; f 1; 42", "b/two.yu");
        let ab = collect(a.clone());
        let bb = collect(b.clone());
        let order = |batch: &ConstraintBatch| {
            batch
                .occurrences()
                .iter()
                .map(|item| {
                    (
                        item.id().source_ordinal(),
                        item.id().local_slot(),
                        shape(batch, item),
                    )
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(order(&ab), order(&bb));
        assert_eq!(order(&ab).len(), 13);
        let asolved = SolvedModule::solve(ab).unwrap();
        let bsolved = SolvedModule::solve(bb).unwrap();
        assert_eq!(
            asolved
                .occurrences()
                .iter()
                .map(HirOccurrenceId::ordinal)
                .collect::<Vec<_>>(),
            vec![0, 1, 2, 3]
        );
        for index in [1, 3] {
            assert_eq!(
                asolved
                    .projection_for(root(&a, index).occurrence())
                    .unwrap(),
                bsolved
                    .projection_for(root(&b, index).occurrence())
                    .unwrap()
            );
        }
    }
    #[test]
    fn f4_binding_bodies_feed_finalized_definition_roots() {
        let hir = module("my x = 42", "binding.yu");
        let [HirItem::Binding(binding)] = hir.items() else {
            panic!("one binding")
        };
        let batch = collect(hir.clone());
        let body = batch
            .components_for(binding.value().occurrence())
            .unwrap()
            .unwrap();
        let root = batch
            .root_value_component(binding.definition_root())
            .unwrap();
        assert_eq!(batch.occurrences().len(), 5);
        assert!(matches!(body.value(), ComponentId::Occurrence { .. }));
        assert!(
            matches!(root, ComponentId::DefinitionValue { ref root } if root == binding.definition_root())
        );
        assert_eq!(
            batch
                .occurrences()
                .iter()
                .map(|item| (item.id().local_slot(), shape(&batch, item)))
                .collect::<Vec<_>>(),
            vec![
                (0, (Some(Leaf::IntPositive), None)),
                (1, (None, Some(Leaf::IntNegative))),
                (2, (Some(Leaf::EffectBottomPositive), None)),
                (3, (None, Some(Leaf::EmptyEffectNegative))),
                (4, (None, None)),
            ]
        );
        let fifth = &batch.occurrences()[4];
        assert_eq!(fifth.lower(), batch.term_for_component(body.value()));
        assert_eq!(fifth.upper(), batch.term_for_component(&root));
        let solved = SolvedModule::solve(batch).unwrap();
        assert_eq!(
            solved.projection_for(binding.value().occurrence()).unwrap(),
            SolvedProjection {
                value: SolvedValue::Int,
                effect: SolvedEffect::Empty,
            }
        );
        assert_eq!(
            solved.root_value_for(binding.definition_root()).unwrap(),
            SolvedValue::Int
        );
        let counters = solved.counters();
        assert_eq!(counters.occurrence_component_query_probes(), 1);
        assert_eq!(counters.root_component_query_probes(), 1);
        assert_eq!(counters.solved_root_query_probes(), 1);
    }
    #[test]
    fn f0_collects_definition_order_body_status_and_resolved_binding_uses() {
        let hir = module(
            "my forward = target; my target = 42; my backward = forward; target; my broken = @",
            "f0-collection.yu",
        );
        let batch = collect(hir);

        assert_eq!(batch.definitions().len(), 4);
        assert_eq!(batch.definition_uses().len(), 2);
        assert_eq!(
            batch
                .definitions()
                .iter()
                .map(|definition| definition.definition().ordinal())
                .collect::<Vec<_>>(),
            vec![0, 1, 2, 3]
        );
        assert_eq!(
            batch
                .definitions()
                .iter()
                .map(|definition| {
                    (
                        definition.body_fact_range().clone(),
                        definition.body_status(),
                    )
                })
                .collect::<Vec<_>>(),
            vec![
                (0..3, CollectedBodyStatus::Complete),
                (3..8, CollectedBodyStatus::Complete),
                (8..11, CollectedBodyStatus::Complete),
                (11..11, CollectedBodyStatus::Error),
            ]
        );
        assert_eq!(
            batch
                .definition_uses()
                .iter()
                .map(|use_record| {
                    (
                        use_record.parent().ordinal(),
                        use_record.target().ordinal(),
                        use_record.id().occurrence().ordinal(),
                        use_record.occurrence().ordinal(),
                    )
                })
                .collect::<Vec<_>>(),
            vec![(0, 1, 0, 0), (2, 0, 2, 2)]
        );
        for use_record in batch.definition_uses() {
            assert_eq!(use_record.cause().id(), use_record.id());
            assert_eq!(batch.definition_use(use_record.id()), Ok(use_record));
        }
        for definition in batch.definitions() {
            assert_eq!(batch.definition(definition.definition()), Ok(definition));
        }
        let counters = batch.counters();
        assert_eq!(counters.hir_traversals(), 1);
        assert_eq!(counters.body_pass_visits(), 5);
        assert_eq!(counters.definition_registration_visits(), 4);
        assert_eq!(counters.collected_definitions(), 4);
        assert_eq!(counters.collected_complete_bodies(), 3);
        assert_eq!(counters.collected_error_bodies(), 1);
        assert_eq!(counters.collected_ambiguous_name_bodies(), 0);
        assert_eq!(counters.collected_unresolved_name_bodies(), 0);
        assert_eq!(counters.definition_use_endpoint_pass_visits(), 2);
        assert!(counters.definition_use_endpoint_workspace_peak_capacity() >= 2);
        assert_eq!(counters.definition_endpoint_index_inserts(), 4);
        assert_eq!(counters.definition_endpoint_index_probes(), 2);
        assert_eq!(counters.definition_record_index_inserts(), 4);
        assert_eq!(counters.definition_use_index_inserts(), 2);
        assert_eq!(counters.retained_definition_uses(), 2);
        assert_eq!(counters.definition_query_probes(), 4);
        assert_eq!(counters.definition_use_query_probes(), 2);
    }
    #[test]
    fn f0_definition_queries_reject_foreign_and_missing_batch_identities() {
        let first = collect(module("my x = 42", "f0-first.yu"));
        let second = collect(module("my x = 42", "f0-second.yu"));
        let foreign_definition = second.definitions()[0].definition();
        let foreign_use = {
            let with_use = collect(module("my x = x", "f0-use.yu"));
            with_use.definition_uses()[0].id().clone()
        };
        assert_eq!(
            first.definition(foreign_definition),
            Err(CollectionLookupError::ArtifactMismatch)
        );
        assert_eq!(
            first.definition_use(&foreign_use),
            Err(CollectionLookupError::ArtifactMismatch)
        );
        let missing_definition = DefinitionOrderId::new(first.collection_artifact.clone(), 99);
        assert_eq!(
            first.definition(&missing_definition),
            Err(CollectionLookupError::MissingIdentity)
        );
    }
    #[test]
    fn f0_keeps_direct_ambiguous_and_unresolved_names_out_of_dependencies() {
        let batch = collect(module(
            "my x = 1; my x = 2; my ambiguous = x; my unresolved = missing; x; missing",
            "f0-no-false-use.yu",
        ));
        assert_eq!(batch.definitions().len(), 4);
        assert!(batch.definition_uses().is_empty());
        assert_eq!(
            batch
                .definitions()
                .iter()
                .map(CollectedDefinition::body_status)
                .collect::<Vec<_>>(),
            vec![
                CollectedBodyStatus::Complete,
                CollectedBodyStatus::Complete,
                CollectedBodyStatus::Error,
                CollectedBodyStatus::Error,
            ]
        );
        let counters = batch.counters();
        assert_eq!(counters.collected_complete_bodies(), 2);
        assert_eq!(counters.collected_error_bodies(), 2);
        assert_eq!(counters.collected_ambiguous_name_bodies(), 1);
        assert_eq!(counters.collected_unresolved_name_bodies(), 1);
    }
    #[test]
    fn f0_retains_self_and_mutual_dependency_occurrences() {
        let batch = collect(module(
            "my self = self; my left = right; my right = left",
            "f0-cycles.yu",
        ));
        assert_eq!(
            batch
                .definition_uses()
                .iter()
                .map(|use_record| (use_record.parent().ordinal(), use_record.target().ordinal()))
                .collect::<Vec<_>>(),
            vec![(0, 0), (1, 2), (2, 1)]
        );
    }
    fn synthetic_scc_plan(
        definitions: usize,
        edges: &[(usize, usize)],
        insertion_order: &[usize],
    ) -> (SccPlan, ProductionCounters) {
        synthetic_scc_plan_with_identity(
            definitions,
            edges,
            insertion_order,
            "definition",
            "f1-synthetic.yu",
        )
    }
    fn synthetic_scc_plan_with_identity(
        definitions: usize,
        edges: &[(usize, usize)],
        insertion_order: &[usize],
        definition_stem: &str,
        module_path: &str,
    ) -> (SccPlan, ProductionCounters) {
        let (artifact, synthetic_definitions, uses) = synthetic_scc_records(
            definitions,
            edges,
            insertion_order,
            definition_stem,
            module_path,
        );
        let mut counters = ProductionCounters::default();
        let plan = SccPlan::build(&artifact, &synthetic_definitions, &uses, &mut counters).unwrap();
        (plan, counters)
    }
    fn synthetic_scc_records(
        definitions: usize,
        edges: &[(usize, usize)],
        insertion_order: &[usize],
        definition_stem: &str,
        module_path: &str,
    ) -> (
        Arc<CollectionArtifactToken>,
        Vec<DefinitionOrderId>,
        Vec<DefinitionUse>,
    ) {
        assert_eq!(insertion_order.len(), edges.len());
        let mut source = (0..definitions)
            .map(|index| format!("my {definition_stem}_{index} = 0"))
            .collect::<Vec<_>>();
        for _ in definitions..edges.len() {
            source.push("0".to_owned());
        }
        let hir = module(&source.join("; "), module_path);
        let occurrences = hir
            .items()
            .iter()
            .map(|item| match item {
                HirItem::Binding(binding) => binding.value().occurrence().clone(),
                HirItem::Expression(expression) => expression.occurrence().clone(),
                HirItem::Error { .. } => panic!("synthetic source has no HIR error"),
            })
            .collect::<Vec<_>>();
        assert!(occurrences.len() >= edges.len());
        let artifact = Arc::new(CollectionArtifactToken);
        let synthetic_definitions = (0..definitions)
            .map(|ordinal| DefinitionOrderId::new(artifact.clone(), ordinal as u32))
            .collect::<Vec<_>>();
        let uses = insertion_order
            .iter()
            .map(|&edge_index| {
                let (parent, target) = edges[edge_index];
                let id = DefinitionUseId::new(artifact.clone(), occurrences[edge_index].clone());
                DefinitionUse {
                    cause: DefinitionUseCause::for_use(id.clone()),
                    id,
                    parent: synthetic_definitions[parent].clone(),
                    target: synthetic_definitions[target].clone(),
                    occurrence: occurrences[edge_index].clone(),
                    use_level: 1,
                    use_value_component: 0,
                    target_root_component: 0,
                }
            })
            .collect::<Vec<_>>();
        (artifact, synthetic_definitions, uses)
    }
    fn raw_scc_plan(plan: &SccPlan) -> Vec<(u32, Vec<u32>, Vec<u32>, Vec<u32>)> {
        plan.components_in_dependency_first_order()
            .map(|component| {
                (
                    component.canonical_definition().ordinal(),
                    plan.members_for_test(component)
                        .expect("plan component from its own iterator")
                        .iter()
                        .map(DefinitionOrderId::ordinal)
                        .collect(),
                    plan.internal_uses_for_test(component)
                        .expect("plan component from its own iterator")
                        .iter()
                        .map(|id| id.occurrence().ordinal())
                        .collect(),
                    plan.incoming_uses_for_test(component)
                        .expect("plan component from its own iterator")
                        .iter()
                        .map(|id| id.occurrence().ordinal())
                        .collect(),
                )
            })
            .collect()
    }
    fn raw_batch_scc_plan(batch: &ConstraintBatch) -> Vec<(u32, Vec<u32>, Vec<u32>, Vec<u32>)> {
        batch
            .scc_components_in_dependency_first_order()
            .map(|component| {
                (
                    component.canonical_definition().ordinal(),
                    batch
                        .scc_component_members(component)
                        .unwrap()
                        .iter()
                        .map(DefinitionOrderId::ordinal)
                        .collect(),
                    batch
                        .scc_component_internal_uses(component)
                        .unwrap()
                        .iter()
                        .map(|id| id.occurrence().ordinal())
                        .collect(),
                    batch
                        .scc_component_incoming_uses(component)
                        .unwrap()
                        .iter()
                        .map(|id| id.occurrence().ordinal())
                        .collect(),
                )
            })
            .collect()
    }
    #[test]
    fn f1_synthetic_records_freeze_isolated_and_dependency_sink_first_components() {
        let (isolated, _) = synthetic_scc_plan(1, &[], &[]);
        assert_eq!(raw_scc_plan(&isolated), vec![(0, vec![0], vec![], vec![])]);
        let (forward, _) = synthetic_scc_plan(3, &[(0, 1), (1, 2)], &[0, 1]);
        let (backward, _) = synthetic_scc_plan(3, &[(2, 1), (1, 0)], &[1, 0]);
        assert_eq!(
            raw_scc_plan(&forward),
            vec![
                (2, vec![2], vec![], vec![1]),
                (1, vec![1], vec![], vec![0]),
                (0, vec![0], vec![], vec![]),
            ]
        );
        assert_eq!(
            raw_scc_plan(&backward),
            vec![
                (0, vec![0], vec![], vec![1]),
                (1, vec![1], vec![], vec![0]),
                (2, vec![2], vec![], vec![]),
            ]
        );
    }
    #[test]
    fn f1_partitions_diamond_duplicate_self_mutual_and_independent_uses() {
        let (diamond, _) = synthetic_scc_plan(4, &[(0, 1), (0, 2), (1, 3), (2, 3)], &[0, 1, 2, 3]);
        assert_eq!(
            raw_scc_plan(&diamond),
            vec![
                (3, vec![3], vec![], vec![2, 3]),
                (1, vec![1], vec![], vec![0]),
                (2, vec![2], vec![], vec![1]),
                (0, vec![0], vec![], vec![]),
            ]
        );
        let (duplicate, _) = synthetic_scc_plan(2, &[(0, 1), (0, 1)], &[1, 0]);
        assert_eq!(
            raw_scc_plan(&duplicate),
            vec![
                (1, vec![1], vec![], vec![0, 1]),
                (0, vec![0], vec![], vec![])
            ]
        );
        let (self_cycle, _) = synthetic_scc_plan(1, &[(0, 0)], &[0]);
        assert_eq!(
            raw_scc_plan(&self_cycle),
            vec![(0, vec![0], vec![0], vec![])]
        );
        let (mutual, _) = synthetic_scc_plan(2, &[(0, 1), (1, 0)], &[0, 1]);
        assert_eq!(
            raw_scc_plan(&mutual),
            vec![(0, vec![0, 1], vec![0, 1], vec![])]
        );
        let (independent, _) = synthetic_scc_plan(4, &[], &[]);
        assert_eq!(
            raw_scc_plan(&independent),
            vec![
                (0, vec![0], vec![], vec![]),
                (1, vec![1], vec![], vec![]),
                (2, vec![2], vec![], vec![]),
                (3, vec![3], vec![], vec![]),
            ]
        );
    }
    #[test]
    fn f1_synthetic_plan_is_raw_insertion_and_identity_deterministic() {
        let edges = [(0, 1), (0, 2), (1, 3), (2, 3), (0, 1)];
        let (first, _) = synthetic_scc_plan(4, &edges, &[0, 1, 2, 3, 4]);
        let (second, _) = synthetic_scc_plan(4, &edges, &[4, 3, 1, 0, 2]);
        assert_eq!(raw_scc_plan(&first), raw_scc_plan(&second));
    }
    #[test]
    fn f1_raw_plan_is_alpha_and_module_path_independent_modulo_artifact_brand() {
        let edges = [(0, 1), (0, 2), (1, 3), (2, 3), (0, 1)];
        let (first, _) = synthetic_scc_plan_with_identity(
            4,
            &edges,
            &[0, 1, 2, 3, 4],
            "alpha",
            "alpha/module.yu",
        );
        let (second, _) = synthetic_scc_plan_with_identity(
            4,
            &edges,
            &[4, 3, 1, 0, 2],
            "renamed",
            "renamed/other-module.yu",
        );
        assert_eq!(raw_scc_plan(&first), raw_scc_plan(&second));
    }
    #[test]
    fn f1_standalone_build_rejects_foreign_missing_and_duplicate_identities() {
        let (artifact, definitions, uses) =
            synthetic_scc_records(2, &[(0, 1)], &[0], "negative", "f1-negative.yu");
        let (foreign_artifact, foreign_definitions, _) =
            synthetic_scc_records(2, &[], &[], "foreign", "f1-foreign.yu");
        let mut counters = ProductionCounters::default();
        assert!(matches!(
            SccPlan::build(&artifact, &foreign_definitions, &uses, &mut counters),
            Err(CollectionAvailabilityError::MissingDefinitionEndpoint)
        ));
        assert!(!Arc::ptr_eq(&artifact, &foreign_artifact));

        let mut foreign_endpoint = uses.clone();
        foreign_endpoint[0].target = foreign_definitions[1].clone();
        assert!(matches!(
            SccPlan::build(
                &artifact,
                &definitions,
                &foreign_endpoint,
                &mut ProductionCounters::default(),
            ),
            Err(CollectionAvailabilityError::MissingDefinitionEndpoint)
        ));

        let mut missing_endpoint = uses.clone();
        missing_endpoint[0].target = DefinitionOrderId::new(artifact.clone(), 99);
        assert!(matches!(
            SccPlan::build(
                &artifact,
                &definitions,
                &missing_endpoint,
                &mut ProductionCounters::default(),
            ),
            Err(CollectionAvailabilityError::MissingDefinitionEndpoint)
        ));

        assert!(matches!(
            SccPlan::build(
                &artifact,
                &[definitions[0].clone(), definitions[0].clone()],
                &[],
                &mut ProductionCounters::default(),
            ),
            Err(CollectionAvailabilityError::DuplicateDefinitionOrderId)
        ));
        assert!(matches!(
            SccPlan::build(
                &artifact,
                &definitions,
                &[uses[0].clone(), uses[0].clone()],
                &mut ProductionCounters::default(),
            ),
            Err(CollectionAvailabilityError::DuplicateDefinitionUseId)
        ));
    }
    #[test]
    fn f2_hir_batches_freeze_dependency_first_order_and_exact_partitions() {
        let isolated = collect(module("my lone = 42", "f2-isolated.yu"));
        assert_eq!(
            raw_batch_scc_plan(&isolated),
            vec![(0, vec![0], vec![], vec![])]
        );

        let chain = collect(module(
            "my head = middle; my middle = tail; my tail = 42",
            "f2-chain.yu",
        ));
        assert_eq!(
            raw_batch_scc_plan(&chain),
            vec![
                (2, vec![2], vec![], vec![1]),
                (1, vec![1], vec![], vec![0]),
                (0, vec![0], vec![], vec![]),
            ]
        );

        let backward_chain = collect(module(
            "my tail = 42; my middle = tail; my head = middle",
            "f2-backward-chain.yu",
        ));
        assert_eq!(
            raw_batch_scc_plan(&backward_chain),
            vec![
                (0, vec![0], vec![], vec![1]),
                (1, vec![1], vec![], vec![2]),
                (2, vec![2], vec![], vec![]),
            ]
        );

        let diamond = collect(module(
            "my top = left; my left = sink; my right = sink; my sink = 42",
            "f2-diamond.yu",
        ));
        assert_eq!(
            raw_batch_scc_plan(&diamond),
            vec![
                (3, vec![3], vec![], vec![1, 2]),
                (1, vec![1], vec![], vec![0]),
                (0, vec![0], vec![], vec![]),
                (2, vec![2], vec![], vec![]),
            ]
        );

        let duplicate = collect(module(
            "my sink = 42; my first = sink; my second = sink",
            "f2-duplicate.yu",
        ));
        assert_eq!(
            raw_batch_scc_plan(&duplicate),
            vec![
                (0, vec![0], vec![], vec![1, 2]),
                (1, vec![1], vec![], vec![]),
                (2, vec![2], vec![], vec![]),
            ]
        );

        let self_cycle = collect(module("my self_ref = self_ref", "f2-self.yu"));
        assert_eq!(
            raw_batch_scc_plan(&self_cycle),
            vec![(0, vec![0], vec![0], vec![])]
        );

        let mutual = collect(module("my left = right; my right = left", "f2-mutual.yu"));
        assert_eq!(
            raw_batch_scc_plan(&mutual),
            vec![(0, vec![0, 1], vec![0, 1], vec![])]
        );

        let independent = collect(module(
            "my first = 42; my second = 42; my third = 42",
            "f2-independent.yu",
        ));
        assert_eq!(
            raw_batch_scc_plan(&independent),
            vec![
                (0, vec![0], vec![], vec![]),
                (1, vec![1], vec![], vec![]),
                (2, vec![2], vec![], vec![]),
            ]
        );
    }
    #[test]
    fn f2_batch_queries_reject_foreign_and_missing_identities_with_decisive_probes() {
        let first = collect(module("my x = x; 42", "f2-first.yu"));
        let second = collect(module("my x = x", "f2-second.yu"));
        let definition = first.definitions()[0].definition();
        let component = first
            .scc_component_for_definition(definition)
            .unwrap()
            .clone();
        assert_eq!(
            first.scc_component_members(&component).unwrap(),
            std::slice::from_ref(definition)
        );
        assert_eq!(
            first.scc_component_internal_uses(&component).unwrap(),
            std::slice::from_ref(first.definition_uses()[0].id())
        );
        assert!(
            first
                .scc_component_incoming_uses(&component)
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            first
                .definition_use(first.definition_uses()[0].id())
                .unwrap()
                .id(),
            first.definition_uses()[0].id()
        );

        let missing_definition = DefinitionOrderId::new(first.collection_artifact.clone(), 99);
        let missing_component = SccComponentId::new(missing_definition.clone());
        let missing_use = DefinitionUseId::new(
            first.collection_artifact.clone(),
            root(first.hir(), 1).occurrence().clone(),
        );
        assert_eq!(
            first.scc_component_for_definition(&missing_definition),
            Err(CollectionLookupError::MissingIdentity)
        );
        assert_eq!(
            first.scc_component_members(&missing_component),
            Err(CollectionLookupError::MissingIdentity)
        );
        assert_eq!(
            first.scc_component_internal_uses(&missing_component),
            Err(CollectionLookupError::MissingIdentity)
        );
        assert_eq!(
            first.scc_component_incoming_uses(&missing_component),
            Err(CollectionLookupError::MissingIdentity)
        );
        assert_eq!(
            first.definition_use(&missing_use),
            Err(CollectionLookupError::MissingIdentity)
        );

        let foreign_definition = second.definitions()[0].definition();
        let foreign_component = second
            .scc_component_for_definition(foreign_definition)
            .unwrap()
            .clone();
        assert_eq!(
            first.scc_component_for_definition(foreign_definition),
            Err(CollectionLookupError::ArtifactMismatch)
        );
        assert_eq!(
            first.scc_component_members(&foreign_component),
            Err(CollectionLookupError::ArtifactMismatch)
        );
        assert_eq!(
            first.scc_component_internal_uses(&foreign_component),
            Err(CollectionLookupError::ArtifactMismatch)
        );
        assert_eq!(
            first.scc_component_incoming_uses(&foreign_component),
            Err(CollectionLookupError::ArtifactMismatch)
        );
        assert_eq!(
            first.definition_use(second.definition_uses()[0].id()),
            Err(CollectionLookupError::ArtifactMismatch)
        );

        let counters = first.counters();
        assert_eq!(counters.scc_component_for_definition_query_probes(), 2);
        assert_eq!(counters.scc_component_members_query_probes(), 2);
        assert_eq!(counters.scc_component_internal_uses_query_probes(), 2);
        assert_eq!(counters.scc_component_incoming_uses_query_probes(), 2);
        assert_eq!(counters.definition_use_query_probes(), 2);
    }
    #[test]
    fn f2_preserves_full_internal_and_incoming_use_slices_and_composes_batch_plan_accounting() {
        let internal_uses = 32;
        let mut internal_source = String::new();
        for index in 0..internal_uses {
            if index != 0 {
                internal_source.push_str("; ");
            }
            internal_source.push_str(&format!(
                "my member_{index} = member_{}",
                (index + 1) % internal_uses
            ));
        }
        let internal_batch = collect(module(&internal_source, "f2-full-internal.yu"));
        let internal_component = internal_batch
            .scc_component_for_definition(internal_batch.definitions()[0].definition())
            .unwrap();
        let internal = internal_batch
            .scc_component_internal_uses(internal_component)
            .unwrap();
        assert_eq!(internal.len(), internal_uses);
        assert_eq!(
            internal
                .iter()
                .map(|id| internal_batch
                    .definition_use(id)
                    .unwrap()
                    .occurrence()
                    .ordinal())
                .collect::<Vec<_>>(),
            (0..internal_uses as u32).collect::<Vec<_>>(),
        );
        assert_eq!(
            internal_batch.counters().scc_internal_use_count(),
            internal_uses
        );

        // One sink component retains every distinct incoming occurrence ID.
        let uses = 32;
        let mut source = String::from("my sink = 42");
        for index in 0..uses {
            source.push_str(&format!("; my user_{index} = sink"));
        }
        let batch = collect(module(&source, "f2-full-incoming.yu"));
        let sink = batch.definitions()[0].definition();
        let component = batch.scc_component_for_definition(sink).unwrap();
        let incoming = batch.scc_component_incoming_uses(component).unwrap();
        assert_eq!(incoming.len(), uses);
        assert_eq!(
            incoming
                .iter()
                .map(|id| batch.definition_use(id).unwrap().occurrence().ordinal())
                .collect::<Vec<_>>(),
            (1..=uses as u32).collect::<Vec<_>>(),
        );
        let counters = batch.counters();
        assert_eq!(counters.scc_incoming_use_count(), uses);
        assert!(counters.scc_plan_incoming_use_capacity() >= uses);
        assert_eq!(
            counters.f2_batch_retained_bytes(),
            counters.f0_collection_retained_bytes() + counters.scc_plan_retained_payload_bytes()
        );
        let f1_input_bytes = batch.definitions().len() * std::mem::size_of::<CollectedDefinition>()
            + batch.definition_uses().len() * std::mem::size_of::<DefinitionUse>();
        assert_eq!(
            counters.f2_batch_plan_peak_bytes(),
            counters.f0_collection_peak_bytes().max(
                // The endpoint index and pending-use vector were dropped before
                // SccPlan::build, so this is the only F2 co-resident peak.
                counters.f0_collection_retained_bytes()
                    + counters
                        .scc_f1_graph_input_plan_peak_known_bytes()
                        .saturating_sub(f1_input_bytes)
            )
        );
    }
    #[test]
    fn f2_batch_clone_preserves_immutable_plan_brand_and_existing_counter_contract() {
        let batch = collect(module("my left = right; my right = left", "f2-clone.yu"));
        let stable_id_clone_count = batch.counters().scc_stable_id_clone_count();
        let cloned = batch.clone();

        assert!(Arc::ptr_eq(
            &batch.collection_artifact,
            &cloned.collection_artifact
        ));
        assert_eq!(raw_batch_scc_plan(&cloned), raw_batch_scc_plan(&batch));
        assert_eq!(
            cloned.counters().scc_stable_id_clone_count(),
            stable_id_clone_count
        );

        let component = cloned
            .scc_component_for_definition(batch.definitions()[0].definition())
            .unwrap();
        assert_eq!(cloned.scc_component_members(component).unwrap().len(), 2);
        // The pre-existing derived `ConstraintBatch::Clone` contract shares
        // query probes through its `Arc<AtomicUsize>` fields. F1-only clone
        // accounting intentionally remains a construction counter.
        assert_eq!(
            batch.counters().scc_component_for_definition_query_probes(),
            1
        );
        assert_eq!(batch.counters(), cloned.counters());
        assert_eq!(batch.counters().scc_component_members_query_probes(), 3);
    }
    #[test]
    fn f2_excludes_error_ambiguous_unresolved_and_direct_root_names_without_semantic_changes() {
        let hir = module(
            "my target = 42; my user = target; my ambiguous = dup; my dup = 1; my dup = 2; my unresolved = missing; my broken = @; target",
            "f2-exclusions.yu",
        );
        let batch = collect(hir.clone());
        assert_eq!(batch.definition_uses().len(), 1);
        assert_eq!(
            raw_batch_scc_plan(&batch),
            vec![
                (0, vec![0], vec![], vec![1]),
                (1, vec![1], vec![], vec![]),
                (2, vec![2], vec![], vec![]),
                (3, vec![3], vec![], vec![]),
                (4, vec![4], vec![], vec![]),
                (5, vec![5], vec![], vec![]),
                (6, vec![6], vec![], vec![]),
            ]
        );
        // F2 owns only the frozen topology and exclusions.  F4 Name/root
        // result behavior is witnessed in its dedicated tests above.
        assert_eq!(batch.counters().scc_count(), 7);
    }
    #[test]
    fn f1_static_scaling_keeps_graph_work_linear_and_ordering_budget_separate() {
        let families: [fn(usize) -> Vec<(usize, usize)>; 7] = [
            // Chain.
            |n| (1..n).map(|index| (index, index - 1)).collect(),
            // Diamond.
            |n| {
                (0..n / 4)
                    .flat_map(|group| {
                        let base = group * 4;
                        [
                            (base, base + 1),
                            (base, base + 2),
                            (base + 1, base + 3),
                            (base + 2, base + 3),
                        ]
                    })
                    .collect()
            },
            // Duplicate payloads on one arc.
            |n| (1..n).flat_map(|index| [(index, 0), (index, 0)]).collect(),
            // Independent components.
            |_| Vec::new(),
            // One long final cycle: one source-sized SCC, not a two-node proxy.
            |n| (0..n).map(|index| (index, (index + 1) % n)).collect(),
            // Self cycles.
            |n| (0..n).map(|index| (index, index)).collect(),
            // Independent mutual cycles.
            |n| {
                (0..n / 2)
                    .flat_map(|pair| [(pair * 2, pair * 2 + 1), (pair * 2 + 1, pair * 2)])
                    .collect()
            },
        ];
        for family in families {
            let measurements = [1000, 2000, 4000].map(|n| {
                let edges = family(n);
                let insertion = (0..edges.len()).rev().collect::<Vec<_>>();
                let (_, counters) = synthetic_scc_plan(n, &edges, &insertion);
                let ordering_limit =
                    32 * (n + edges.len() + 1) * ((n + edges.len() + 1).ilog2() as usize + 1);
                assert!(
                    counters.scc_sort_comparisons() + counters.scc_ready_queue_comparisons()
                        <= ordering_limit
                );
                (n, counters)
            });
            for pair in measurements.windows(2) {
                let [(_, small), (large_n, large)] = pair else {
                    unreachable!("two adjacent scaling measurements");
                };
                for (large, small) in [
                    (large.scc_node_visits(), small.scc_node_visits()),
                    (large.scc_edge_visits(), small.scc_edge_visits()),
                    (large.scc_stack_pushes(), small.scc_stack_pushes()),
                    (large.scc_lowlink_writes(), small.scc_lowlink_writes()),
                    (large.scc_component_writes(), small.scc_component_writes()),
                    (large.scc_distinct_arcs(), small.scc_distinct_arcs()),
                    (
                        large.scc_retained_occurrence_payloads(),
                        small.scc_retained_occurrence_payloads(),
                    ),
                    (
                        large.scc_forward_adjacency_entries(),
                        small.scc_forward_adjacency_entries(),
                    ),
                    (
                        large.scc_forward_payload_lengths(),
                        small.scc_forward_payload_lengths(),
                    ),
                    (
                        large.scc_forward_adjacency_capacity(),
                        small.scc_forward_adjacency_capacity(),
                    ),
                    (
                        large.scc_forward_payload_capacity(),
                        small.scc_forward_payload_capacity(),
                    ),
                    (
                        large.scc_reverse_adjacency_entries(),
                        small.scc_reverse_adjacency_entries(),
                    ),
                    (
                        large.scc_reverse_adjacency_capacity(),
                        small.scc_reverse_adjacency_capacity(),
                    ),
                    (
                        large.scc_definition_index_probes(),
                        small.scc_definition_index_probes(),
                    ),
                    (
                        large.scc_definition_index_capacity(),
                        small.scc_definition_index_capacity(),
                    ),
                    (
                        large.scc_seen_use_set_probes(),
                        small.scc_seen_use_set_probes(),
                    ),
                    (
                        large.scc_seen_use_set_capacity(),
                        small.scc_seen_use_set_capacity(),
                    ),
                    (
                        large.scc_condensation_set_probes(),
                        small.scc_condensation_set_probes(),
                    ),
                    (
                        large.scc_condensation_set_capacity(),
                        small.scc_condensation_set_capacity(),
                    ),
                    (
                        large.scc_plan_component_index_probes(),
                        small.scc_plan_component_index_probes(),
                    ),
                    (
                        large.scc_plan_component_index_capacity(),
                        small.scc_plan_component_index_capacity(),
                    ),
                    (
                        large.scc_plan_definition_index_probes(),
                        small.scc_plan_definition_index_probes(),
                    ),
                    (
                        large.scc_plan_definition_index_capacity(),
                        small.scc_plan_definition_index_capacity(),
                    ),
                    (large.scc_map_set_rebuilds(), small.scc_map_set_rebuilds()),
                    (
                        large.scc_stable_id_clone_count(),
                        small.scc_stable_id_clone_count(),
                    ),
                    (
                        large.scc_stable_id_clone_payload_bytes(),
                        small.scc_stable_id_clone_payload_bytes(),
                    ),
                    (large.scc_peak_stack_bytes(), small.scc_peak_stack_bytes()),
                    (
                        large.scc_peak_temporary_set_bytes(),
                        small.scc_peak_temporary_set_bytes(),
                    ),
                    (
                        large.scc_kosaraju_workspace_peak_bytes(),
                        small.scc_kosaraju_workspace_peak_bytes(),
                    ),
                    (
                        large.scc_partition_workspace_peak_bytes(),
                        small.scc_partition_workspace_peak_bytes(),
                    ),
                    (
                        large.scc_scheduler_workspace_peak_bytes(),
                        small.scc_scheduler_workspace_peak_bytes(),
                    ),
                    (
                        large.scc_freeze_transition_peak_bytes(),
                        small.scc_freeze_transition_peak_bytes(),
                    ),
                    (
                        large.scc_internal_use_count(),
                        small.scc_internal_use_count(),
                    ),
                    (
                        large.scc_incoming_use_count(),
                        small.scc_incoming_use_count(),
                    ),
                    (
                        large.scc_maximum_component_size(),
                        small.scc_maximum_component_size(),
                    ),
                    (large.scc_count(), small.scc_count()),
                    (
                        large.scc_condensation_node_visits(),
                        small.scc_condensation_node_visits(),
                    ),
                    (
                        large.scc_condensation_edge_visits(),
                        small.scc_condensation_edge_visits(),
                    ),
                    (
                        large.scc_ready_queue_operations(),
                        small.scc_ready_queue_operations(),
                    ),
                    (
                        large.scc_ready_queue_maximum_size(),
                        small.scc_ready_queue_maximum_size(),
                    ),
                    (large.scc_sort_count(), small.scc_sort_count()),
                    (large.scc_sort_elements(), small.scc_sort_elements()),
                    (
                        large.scc_plan_component_capacity(),
                        small.scc_plan_component_capacity(),
                    ),
                    (
                        large.scc_plan_member_capacity(),
                        small.scc_plan_member_capacity(),
                    ),
                    (
                        large.scc_plan_internal_use_capacity(),
                        small.scc_plan_internal_use_capacity(),
                    ),
                    (
                        large.scc_plan_incoming_use_capacity(),
                        small.scc_plan_incoming_use_capacity(),
                    ),
                    (
                        large.scc_plan_retained_payload_bytes(),
                        small.scc_plan_retained_payload_bytes(),
                    ),
                    (
                        large.scc_graph_workspace_peak_known_bytes(),
                        small.scc_graph_workspace_peak_known_bytes(),
                    ),
                    (
                        large.scc_f1_graph_input_plan_peak_known_bytes(),
                        small.scc_f1_graph_input_plan_peak_known_bytes(),
                    ),
                ] {
                    if small != 0 {
                        assert!(
                            large * 2 < small * 5,
                            "{large} exceeded linear growth from {small}"
                        );
                    } else {
                        assert_eq!(large, 0, "zero linear counter grew at doubling");
                    }
                }
                assert!(large.scc_count() <= *large_n);
            }
        }
    }
    #[test]
    fn f1_peak_accounting_forces_co_resident_kosaraju_and_scheduler_workspaces() {
        let n = 1_000;
        let chain = (1..n).map(|index| (index, index - 1)).collect::<Vec<_>>();
        let insertion = (0..chain.len()).rev().collect::<Vec<_>>();
        let (_, chain_counters) = synthetic_scc_plan(n, &chain, &insertion);
        assert!(
            chain_counters.scc_kosaraju_workspace_peak_bytes()
                >= chain_counters.scc_graph_workspace_peak_known_bytes()
                    + 2 * n * std::mem::size_of::<bool>()
                    + n * std::mem::size_of::<usize>()
        );
        assert!(chain_counters.scc_partition_workspace_peak_bytes() > 0);
        assert!(
            chain_counters.scc_f1_graph_input_plan_peak_known_bytes()
                >= chain_counters.scc_kosaraju_workspace_peak_bytes()
                && chain_counters.scc_f1_graph_input_plan_peak_known_bytes()
                    >= chain_counters.scc_partition_workspace_peak_bytes()
                && chain_counters.scc_f1_graph_input_plan_peak_known_bytes()
                    >= chain_counters.scc_freeze_transition_peak_bytes()
        );

        let (_, independent_counters) = synthetic_scc_plan(n, &[], &[]);
        assert_eq!(independent_counters.scc_ready_queue_maximum_size(), n);
        assert!(
            independent_counters.scc_scheduler_workspace_peak_bytes()
                >= independent_counters.scc_graph_workspace_peak_known_bytes()
                    + n * std::mem::size_of::<usize>()
        );
        assert!(
            independent_counters.scc_f1_graph_input_plan_peak_known_bytes()
                >= independent_counters.scc_scheduler_workspace_peak_bytes()
        );
    }
    #[test]
    fn f1_stable_id_clone_witness_counts_handles_not_referent_payloads() {
        let (_, counters) = synthetic_scc_plan(3, &[(0, 1), (1, 2), (2, 0)], &[2, 1, 0]);
        // 4D + 2C + 2U = 4 * 3 + 2 * 1 + 2 * 3 stable-ID handle clones.
        assert_eq!(counters.scc_stable_id_clone_count(), 20);
        assert_eq!(
            counters.scc_stable_id_clone_payload_bytes(),
            14 * std::mem::size_of::<DefinitionOrderId>()
                + 6 * std::mem::size_of::<DefinitionUseId>()
        );
    }
    #[test]
    fn f0_resolved_name_endpoint_work_remains_linear_for_chain_and_repeated_target_families() {
        let chain = |n| {
            let mut source = String::from("my binding_0 = 42");
            for index in 1..n {
                source.push_str(&format!("; my binding_{index} = binding_{}", index - 1));
            }
            source
        };
        let repeated_target = |n| {
            let mut source = String::from("my target = 42");
            for index in 1..n {
                source.push_str(&format!("; my user_{index} = target"));
            }
            source
        };
        let assert_exact_counts = |n, batch: &ConstraintBatch| {
            let counters = batch.counters();
            let (definition_insert_bytes, successful_lookup_bytes) = batch
                .hir()
                .items()
                .iter()
                .filter_map(|item| {
                    let HirItem::Binding(binding) = item else {
                        return None;
                    };
                    let successful_lookup_bytes = match binding.value() {
                        ResolvedExpr::Name {
                            resolution: NameResolution::Resolved(target),
                            ..
                        } => target.hash_eq_payload_bytes(),
                        _ => 0,
                    };
                    Some((
                        binding.id().hash_eq_payload_bytes(),
                        successful_lookup_bytes,
                    ))
                })
                .fold((0, 0), |(inserts, lookups), (insert, lookup)| {
                    (inserts + insert, lookups + lookup)
                });
            assert_eq!(counters.hir_traversals(), 1);
            assert_eq!(counters.body_pass_visits(), n);
            assert_eq!(counters.definition_registration_visits(), n);
            assert_eq!(counters.collected_definitions(), n);
            assert_eq!(counters.collected_complete_bodies(), n);
            assert_eq!(counters.collected_error_bodies(), 0);
            assert_eq!(counters.collected_ambiguous_name_bodies(), 0);
            assert_eq!(counters.collected_unresolved_name_bodies(), 0);
            assert_eq!(counters.definition_endpoint_index_inserts(), n);
            assert_eq!(counters.definition_use_endpoint_pass_visits(), n - 1);
            assert_eq!(counters.definition_endpoint_index_probes(), n - 1);
            assert_eq!(
                counters.definition_endpoint_identity_hash_byte_incidences(),
                definition_insert_bytes + successful_lookup_bytes
            );
            assert_eq!(
                counters.definition_endpoint_logical_successful_equality_byte_incidences(),
                successful_lookup_bytes
            );
            assert_eq!(counters.retained_definition_uses(), n - 1);
            assert_eq!(counters.definition_record_index_inserts(), n);
            assert_eq!(counters.definition_use_index_inserts(), n - 1);
            assert_eq!(
                counters.definition_endpoint_index_peak_bytes(),
                counters.definition_endpoint_index_peak_capacity()
                    * std::mem::size_of::<(&DefId, DefinitionOrderId)>()
            );
            assert_eq!(
                counters.definition_use_endpoint_workspace_peak_bytes(),
                counters.definition_use_endpoint_workspace_peak_capacity()
                    * std::mem::size_of::<PendingDefinitionUse<'_>>()
            );
            assert_eq!(
                counters.f0_collection_peak_bytes(),
                counters.f0_collection_retained_bytes()
                    + counters.definition_endpoint_index_peak_bytes()
                    + counters.definition_use_endpoint_workspace_peak_bytes()
            );
            // Canonical-store comparison growth has its later O(N log N) budget;
            // this F0-only witness does not fold it into the linear endpoint budget.
            assert_eq!(counters.canonical_map_probes(), 0);
            assert_eq!(counters.canonical_map_rebuilds(), 0);
        };
        let chains = [1000, 2000, 4000].map(|n| collect(module(&chain(n), "f0-chain.yu")));
        let repeated = [1000, 2000, 4000]
            .map(|n| collect(module(&repeated_target(n), "f0-repeated-target.yu")));
        let isolated = [1000, 2000, 4000].map(|n| {
            collect(module(
                &(0..n)
                    .map(|index| format!("my isolated_{index} = 42"))
                    .collect::<Vec<_>>()
                    .join("; "),
                "f2-isolated-scale.yu",
            ))
        });
        let long_realm = "endpoint-realm-".repeat(64);
        let long_path = format!("f0/{}/endpoint.yu", "module-path-".repeat(128));
        let long_target = format!("target_{}", "identity_".repeat(128));
        let repeated_long_identity_target = |n| {
            let mut source = format!("my {long_target} = 42");
            for index in 1..n {
                source.push_str(&format!("; my user_{index} = {long_target}"));
            }
            source
        };
        let repeated_long_identity = [1000, 2000, 4000].map(|n| {
            collect(module_with_identity(
                &repeated_long_identity_target(n),
                &long_realm,
                &long_path,
            ))
        });
        for (((&n, chain), repeated), long_identity) in [1000, 2000, 4000]
            .iter()
            .zip(chains.iter())
            .zip(repeated.iter())
            .zip(repeated_long_identity.iter())
        {
            assert_exact_counts(n, &chain);
            assert_exact_counts(n, &repeated);
            assert_exact_counts(n, long_identity);
            assert!(
                long_identity
                    .counters()
                    .definition_endpoint_identity_hash_byte_incidences()
                    > repeated
                        .counters()
                        .definition_endpoint_identity_hash_byte_incidences()
            );
            assert!(
                long_identity
                    .counters()
                    .definition_endpoint_logical_successful_equality_byte_incidences()
                    > repeated
                        .counters()
                        .definition_endpoint_logical_successful_equality_byte_incidences()
            );
        }
        for family in [&chains, &repeated, &repeated_long_identity] {
            for pair in family.windows(2) {
                let small = pair[0].counters();
                let large = pair[1].counters();
                for (large, small) in [
                    (
                        large.definition_endpoint_index_peak_capacity(),
                        small.definition_endpoint_index_peak_capacity(),
                    ),
                    (
                        large.definition_use_endpoint_workspace_peak_capacity(),
                        small.definition_use_endpoint_workspace_peak_capacity(),
                    ),
                    (
                        large.definition_endpoint_index_capacity_growths(),
                        small.definition_endpoint_index_capacity_growths(),
                    ),
                    (
                        large.definition_use_endpoint_workspace_capacity_growths(),
                        small.definition_use_endpoint_workspace_capacity_growths(),
                    ),
                    (
                        large.definition_endpoint_index_peak_bytes(),
                        small.definition_endpoint_index_peak_bytes(),
                    ),
                    (
                        large.definition_use_endpoint_workspace_peak_bytes(),
                        small.definition_use_endpoint_workspace_peak_bytes(),
                    ),
                    (
                        large.definition_endpoint_identity_hash_byte_incidences(),
                        small.definition_endpoint_identity_hash_byte_incidences(),
                    ),
                    (
                        large.definition_endpoint_logical_successful_equality_byte_incidences(),
                        small.definition_endpoint_logical_successful_equality_byte_incidences(),
                    ),
                    (
                        large.definition_record_index_capacity(),
                        small.definition_record_index_capacity(),
                    ),
                    (
                        large.definition_use_index_capacity(),
                        small.definition_use_index_capacity(),
                    ),
                    (
                        large.f0_collection_retained_bytes(),
                        small.f0_collection_retained_bytes(),
                    ),
                    (
                        large.f0_collection_peak_bytes(),
                        small.f0_collection_peak_bytes(),
                    ),
                    (large.index_rebuilds(), small.index_rebuilds()),
                ] {
                    assert!(large < small * 5 / 2 + 1);
                }
            }
        }
        // F2 reuses the collected definitions directly: no DefinitionOrderId
        // input vector is built, and the retained batch/plan peak is measured
        // after F0 endpoint workspaces have dropped.
        for (&n, batch) in [1000, 2000, 4000].iter().zip(isolated.iter()) {
            let counters = batch.counters();
            assert_eq!(counters.hir_traversals(), 1);
            assert_eq!(counters.collected_definitions(), n);
            assert_eq!(counters.retained_definition_uses(), 0);
            assert_eq!(counters.scc_count(), n);
        }
        for family in [&chains, &repeated, &isolated] {
            for batch in family {
                let counters = batch.counters();
                let f1_input_bytes = batch.definitions().len()
                    * std::mem::size_of::<CollectedDefinition>()
                    + batch.definition_uses().len() * std::mem::size_of::<DefinitionUse>();
                assert_eq!(
                    counters.f2_batch_retained_bytes(),
                    counters.f0_collection_retained_bytes()
                        + counters.scc_plan_retained_payload_bytes()
                );
                assert_eq!(
                    counters.f2_batch_plan_peak_bytes(),
                    counters.f0_collection_peak_bytes().max(
                        counters.f0_collection_retained_bytes()
                            + counters
                                .scc_f1_graph_input_plan_peak_known_bytes()
                                .saturating_sub(f1_input_bytes)
                    )
                );
            }
            for pair in family.windows(2) {
                let small = pair[0].counters();
                let large = pair[1].counters();
                for (large, small) in [
                    (
                        large.definition_record_retained_bytes(),
                        small.definition_record_retained_bytes(),
                    ),
                    (
                        large.definition_record_index_retained_bytes(),
                        small.definition_record_index_retained_bytes(),
                    ),
                    (
                        large.f2_batch_retained_bytes(),
                        small.f2_batch_retained_bytes(),
                    ),
                    (
                        large.f2_batch_plan_peak_bytes(),
                        small.f2_batch_plan_peak_bytes(),
                    ),
                    (
                        large.scc_plan_retained_payload_bytes(),
                        small.scc_plan_retained_payload_bytes(),
                    ),
                    (
                        large.scc_f1_graph_input_plan_peak_known_bytes(),
                        small.scc_f1_graph_input_plan_peak_known_bytes(),
                    ),
                ] {
                    assert!(large < small * 5 / 2 + 1);
                }
            }
        }
    }
    #[test]
    fn names_errors_and_underconstrained_intervals_remain_unknown() {
        let hir = module(
            "my resolved = 42; resolved; my dup = 0; my dup = 1; dup; missing; f 1; 42",
            "states.yu",
        );
        let batch = collect(hir.clone());
        assert_eq!(batch.occurrences().len(), 19);
        assert!(
            batch
                .components_for(match &hir.items()[0] {
                    HirItem::Binding(binding) => binding.value().occurrence(),
                    _ => unreachable!(),
                })
                .unwrap()
                .is_some()
        );
        assert!(matches!(
            root(&hir, 1),
            ResolvedExpr::Name {
                resolution: yu_hir::NameResolution::Resolved(_),
                ..
            }
        ));
        assert!(matches!(
            root(&hir, 4),
            ResolvedExpr::Name {
                resolution: yu_hir::NameResolution::Ambiguous,
                ..
            }
        ));
        assert!(matches!(
            root(&hir, 5),
            ResolvedExpr::Name {
                resolution: yu_hir::NameResolution::Unresolved,
                ..
            }
        ));
        assert!(matches!(root(&hir, 6), ResolvedExpr::Error { .. }));
        let solved = SolvedModule::solve(batch).unwrap();
        for index in [1, 4, 5, 6] {
            let expression = match &hir.items()[index] {
                HirItem::Binding(binding) => binding.value(),
                HirItem::Expression(expression) => expression,
                _ => unreachable!(),
            };
            assert_eq!(
                solved.projection_for(expression.occurrence()).unwrap(),
                SolvedProjection {
                    value: SolvedValue::Unknown,
                    effect: SolvedEffect::Unknown
                }
            );
        }
        for index in [0, 2, 3] {
            let HirItem::Binding(binding) = &hir.items()[index] else {
                unreachable!()
            };
            assert_eq!(
                solved.projection_for(binding.value().occurrence()).unwrap(),
                SolvedProjection {
                    value: SolvedValue::Int,
                    effect: SolvedEffect::Empty,
                }
            );
        }
        assert_eq!(
            solved
                .projection_for(root(&hir, 7).occurrence())
                .unwrap()
                .value(),
            SolvedValue::Int
        );
        let hir = module("42", "under.yu");
        let mut batch = collect(hir.clone());
        retain_batch_occurrences(&mut batch, |item| item.id.local_slot != 1);
        assert_eq!(
            SolvedModule::solve(batch)
                .unwrap()
                .projection_for(root(&hir, 0).occurrence())
                .unwrap(),
            SolvedProjection {
                value: SolvedValue::Unknown,
                effect: SolvedEffect::Empty
            }
        );
        let mut batch = collect(hir.clone());
        retain_batch_occurrences(&mut batch, |item| item.id.local_slot != 3);
        assert_eq!(
            SolvedModule::solve(batch)
                .unwrap()
                .projection_for(root(&hir, 0).occurrence())
                .unwrap(),
            SolvedProjection {
                value: SolvedValue::Int,
                effect: SolvedEffect::Unknown
            }
        );
    }
    #[test]
    fn duplicate_malformed_and_name_bodies_keep_distinct_roots_without_relations() {
        let hir = module(
            "my x = 1; my x = 1; my broken = @; my named = x; my good = 42",
            "roots.yu",
        );
        let bindings = hir
            .items()
            .iter()
            .map(|item| match item {
                HirItem::Binding(binding) => binding,
                _ => panic!("admitted binding"),
            })
            .collect::<Vec<_>>();
        let batch = collect(hir.clone());
        assert_eq!(batch.occurrences().len(), 15);
        assert_ne!(bindings[0].definition_root(), bindings[1].definition_root());
        for binding in &bindings {
            assert!(
                batch
                    .root_value_component(binding.definition_root())
                    .is_ok()
            );
        }
        assert!(
            batch
                .components_for(bindings[2].value().occurrence())
                .unwrap()
                .is_none()
        );
        assert!(
            batch
                .components_for(bindings[3].value().occurrence())
                .unwrap()
                .is_none()
        );
        // This F2/direct-root fixture owns only the frozen root/component
        // topology.  Final scheme and Name behavior remains in F4 witnesses.
    }

    #[test]
    fn f4_finalizes_distinct_duplicate_malformed_and_name_body_root_schemes() {
        let hir = module(
            "my x = 1; my x = 1; my broken = @; my named = x; my good = 42",
            "f4-root-schemes.yu",
        );
        let bindings = hir
            .items()
            .iter()
            .map(|item| match item {
                HirItem::Binding(binding) => binding,
                _ => panic!("admitted binding"),
            })
            .collect::<Vec<_>>();
        let solved = SolvedModule::solve(collect(hir.clone())).unwrap();
        assert_eq!(solved.schemes.len(), bindings.len());
        assert_eq!(
            bindings
                .iter()
                .map(|binding| solved.root_value_for(binding.definition_root()))
                .collect::<Vec<_>>(),
            vec![
                Ok(SolvedValue::Int),
                Ok(SolvedValue::Int),
                Ok(SolvedValue::Never),
                Ok(SolvedValue::Never),
                Ok(SolvedValue::Int),
            ]
        );
    }

    #[test]
    fn f5a_lambda_is_retained_but_collector_emits_no_function_facts() {
        let hir = module("my f x = x", "f5a-no-function-facts.yu");
        let [HirItem::Binding(binding)] = hir.items() else {
            panic!("one binding")
        };
        assert!(matches!(binding.value(), ResolvedExpr::Lambda { .. }));
        assert!(hir.errors().is_empty());

        let batch = collect(hir.clone());
        assert_eq!(batch.definitions().len(), 1);
        assert_eq!(
            batch.definitions()[0].body_status(),
            CollectedBodyStatus::Complete
        );
        assert_eq!(batch.definitions()[0].body_fact_range(), &(0..0));
        assert!(batch.definition_uses().is_empty());
        assert!(batch.occurrences().is_empty());

        let solved = SolvedModule::solve(batch).expect("F5a Lambda remains solvable");
        assert!(solved.store().facts().is_empty());
        assert_eq!(
            solved.root_value_for(binding.definition_root()),
            Ok(SolvedValue::Never)
        );
    }
    #[test]
    fn roots_and_components_reject_foreign_artifacts_without_name_relations() {
        let first = module("my x = 42; x", "first-roots.yu");
        let second = module("my x = 42", "second-roots.yu");
        let HirItem::Binding(first_binding) = &first.items()[0] else {
            panic!("first binding")
        };
        let HirItem::Binding(second_binding) = &second.items()[0] else {
            panic!("second binding")
        };
        let first_batch = collect(first.clone());
        let second_batch = collect(second.clone());
        assert_eq!(first_batch.occurrences().len(), 5);
        assert!(matches!(
            first_batch.root_value_component(second_binding.definition_root()),
            Err(ArtifactMismatch)
        ));
        assert!(matches!(
            second_batch.components_for(first_binding.value().occurrence()),
            Err(ArtifactMismatch)
        ));
        let local = first_batch.occurrences()[0].clone();
        let bad_id = local.id.clone();
        let foreign_definition_endpoint = ConstraintOccurrence {
            id: bad_id.clone(),
            cause: CauseId::for_occurrence(bad_id),
            lower: second_batch.occurrences()[0].upper(),
            upper: local.upper(),
        };
        assert!(matches!(
            ConstraintStore::from_batch(first_batch.clone())
                .transaction()
                .admit(&foreign_definition_endpoint),
            Err(ConstraintError::ArtifactMismatch)
        ));
        let solved = SolvedModule::solve(first_batch).unwrap();
        assert!(matches!(
            solved.root_value_for(second_binding.definition_root()),
            Err(ArtifactMismatch)
        ));
    }
    #[test]
    fn f5b_batch_lookup_transfer_and_aliases_preserve_collected_terms() {
        let batch = collect(module("42", "f5b-term-transfer.yu"));
        let alias = batch.clone();
        let term = batch.occurrences()[0].lower();
        assert_eq!(batch.term_view(term), alias.term_view(term));
        let store = ConstraintStore::from_batch(batch);
        assert!(matches!(
            store.term_view(term),
            Ok(TermView::Leaf(Leaf::IntPositive))
        ));
        assert!(matches!(
            alias.term_view(term),
            Ok(TermView::Leaf(Leaf::IntPositive))
        ));

        let foreign = collect(module("42", "f5b-term-foreign.yu"));
        assert_eq!(
            store.term_view(foreign.occurrences()[0].lower()),
            Err(TermLookupError::ArenaMismatch)
        );
    }
    #[test]
    fn f5b_collection_prefix_alignment_exhaustion_returns_no_batch() {
        let maximum_aligned_length = u32::MAX - (TERM_PAGE_SLOTS - 1);
        let maximum = {
            let _override = term::override_seal_collected_length(maximum_aligned_length);
            ConstraintBatch::collect(module("42", "f5b-term-prefix-maximum.yu"))
        };
        let maximum = maximum.expect("maximum aligned collected length seals a batch");
        assert!(matches!(
            maximum.term_view(maximum.occurrences()[0].lower()),
            Ok(TermView::Leaf(Leaf::IntPositive))
        ));

        let overflowing = {
            let _override = term::override_seal_collected_length(u32::MAX);
            ConstraintBatch::collect(module("42", "f5b-term-prefix-overflow.yu"))
        };
        assert!(matches!(
            overflowing,
            Err(CollectionAvailabilityError::ComponentIdentityExhausted)
        ));
    }
    #[test]
    fn f5b_same_lineage_missing_term_panics_before_admission_state_changes() {
        let batch = collect(module("42", "f5b-term-invalid-handle.yu"));
        let mut allocating_branch = ConstraintStore::from_batch(batch.clone());
        let branch_only =
            allocating_branch.push_test_branch_term(TermNode::Leaf(Leaf::IntPositive));
        let foreign_batch = collect(module("42", "f5b-term-invalid-owner.yu"));
        let mut sibling_branch = ConstraintStore::from_batch(batch.clone());
        let mut occurrence = foreign_batch.occurrences()[0].clone();
        occurrence.lower = branch_only;

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            sibling_branch.transaction().admit(&occurrence)
        }));
        assert!(result.is_err());
        assert!(sibling_branch.facts().is_empty());
        assert!(sibling_branch.provenance().is_empty());
        assert_eq!(sibling_branch.counters().admitted_facts(), 0);
        assert_eq!(sibling_branch.counters().accepted_work_items(), 0);
    }
    #[test]
    fn f5b_consumed_batch_aliases_claim_disjoint_sparse_postprefix_pages() {
        let batch = collect(module("42", "f5b-term-clone-pages.yu"));
        let mut first = ConstraintStore::from_batch(batch.clone());
        let mut second = ConstraintStore::from_batch(batch.clone());

        let first_term = first.push_test_branch_term(TermNode::Leaf(Leaf::IntPositive));
        let second_term = second.push_test_branch_term(TermNode::Leaf(Leaf::IntNegative));
        assert_eq!(
            second_term.test_index(),
            first_term.test_index() + TERM_PAGE_SLOTS
        );
        assert_eq!(first.term_page_observations().claims, 1);
        assert_eq!(first.term_page_observations().committed_nodes, 1);
        assert_eq!(
            first.term_page_observations().reserved_slots,
            TERM_PAGE_SLOTS as usize
        );
        assert_eq!(second.term_page_observations().claims, 1);
        assert_eq!(second.term_page_observations().committed_nodes, 1);
        assert_eq!(second.term_page_observations().slack_slots, 255);
        assert_eq!(
            first.term_view(second_term),
            Err(TermLookupError::InvalidHandle)
        );
        assert_eq!(
            second.term_view(first_term),
            Err(TermLookupError::InvalidHandle)
        );
    }
    #[test]
    fn brands_receipts_and_local_failure_are_isolated() {
        let first = module("42; 42", "first.yu");
        let second = module("42", "second.yu");
        let batch = collect(first.clone());
        let other = collect(second.clone());
        assert_ne!(batch.occurrences()[0].id(), other.occurrences()[0].id());
        assert_ne!(
            batch.occurrences()[0].cause(),
            other.occurrences()[0].cause()
        );
        assert!(matches!(
            ConstraintStore::from_batch(batch.clone())
                .transaction()
                .admit(&other.occurrences()[0]),
            Err(ConstraintError::ArtifactMismatch)
        ));
        let first_item = batch.occurrences()[0].clone();
        let other_id = batch.occurrences()[4].id.clone();
        let duplicate_id =
            ConstraintOccurrenceId::new(other_id.occurrence.clone(), first_item.id.local_slot);
        let duplicate = ConstraintOccurrence {
            id: duplicate_id.clone(),
            cause: CauseId::for_occurrence(duplicate_id),
            lower: first_item.lower.clone(),
            upper: first_item.upper.clone(),
        };
        let mut store = ConstraintStore::from_batch(batch.clone());
        let r1 = store.transaction().admit(&first_item).unwrap();
        let r2 = store.transaction().admit(&duplicate).unwrap();
        assert_eq!(r1.fact(), r2.fact());
        assert_eq!(r1.delta(), AdmissionDelta::Accepted);
        assert_eq!(r2.delta(), AdmissionDelta::Duplicate);
        store.record_provenance(r1).unwrap();
        store.record_provenance(r2).unwrap();
        assert_ne!(store.provenance()[0].cause(), store.provenance()[1].cause());
        let receipt = store.transaction().admit(&first_item).unwrap();
        let mut alien_store = ConstraintStore::from_batch(batch.clone());
        assert!(matches!(
            alien_store.record_provenance(receipt.clone()),
            Err(ConstraintError::AlienReceipt)
        ));
        store.record_provenance(receipt.clone()).unwrap();
        assert!(matches!(
            store.record_provenance(receipt),
            Err(ConstraintError::ReceiptConsumed)
        ));
        let mut failure = collect(first.clone());
        failure.occurrences[0] = ConstraintOccurrence {
            id: failure.occurrences[0].id.clone(),
            cause: failure.occurrences[0].cause.clone(),
            lower: failure.collected_leaf_term(Leaf::EffectBottomPositive),
            upper: failure.occurrences[0].upper(),
        };
        let solved = SolvedModule::solve(failure).unwrap();
        assert!(matches!(
            solved.errors(),
            [SolverError {
                kind: SolverErrorKind::CrossKind { .. },
                ..
            }]
        ));
        assert_eq!(
            solved
                .projection_for(root(&first, 0).occurrence())
                .unwrap()
                .value(),
            SolvedValue::Unknown
        );
        assert_eq!(
            solved
                .projection_for(root(&first, 1).occurrence())
                .unwrap()
                .value(),
            SolvedValue::Int
        );
    }
    #[test]
    fn direct_root_n_and_2n_counters_remain_linear() {
        let source = |n| std::iter::repeat_n("42", n).collect::<Vec<_>>().join("; ");
        let a = SolvedModule::solve(collect(module(&source(1000), "direct-n.yu"))).unwrap();
        let b = SolvedModule::solve(collect(module(&source(2000), "direct-2n.yu"))).unwrap();
        for (n, solved) in [(1000, &a), (2000, &b)] {
            let c = solved.counters();
            assert_eq!(c.hir_traversals(), 1);
            assert_eq!(c.component_allocations(), 2 * n);
            assert_eq!(c.emitted_facts(), 4 * n);
            assert_eq!(c.admitted_facts(), 4 * n);
            assert_eq!(c.occurrence_allocations(), n);
            assert_eq!(c.fact_allocations(), 4 * n);
            assert_eq!(c.provenance_edges(), 4 * n);
            assert_eq!(c.generated_work_items(), 4 * n);
            assert_eq!(c.accepted_work_items(), 4 * n);
            assert_eq!(c.duplicate_work_items(), 0);
            assert_eq!(c.adjacency_appends(), 0);
            assert_eq!(c.adjacency_visits(), 0);
            assert_eq!(c.maximum_fan_out(), 0);
            assert_eq!(c.root_allocations(), 0);
            assert_eq!(c.duplicate_facts(), 0);
            assert_eq!(c.cst_traversals(), 0);
            assert_eq!(c.cst_rescans(), 0);
            assert_eq!(c.hir_clone_count(), 0);
            assert_eq!(c.typed_tree_copies(), 0);
            assert_eq!(c.copied_spelling_bytes(), 0);
            assert_eq!(c.eager_explanation_builds(), 0);
            assert_eq!(c.scc_count(), 0);
        }
        let x = a.counters();
        let y = b.counters();
        for (large, small) in [
            (y.generated_work_items(), x.generated_work_items()),
            (y.accepted_work_items(), x.accepted_work_items()),
            (y.adjacency_visits(), x.adjacency_visits()),
            (y.component_allocations(), x.component_allocations()),
            (y.fact_allocations(), x.fact_allocations()),
            (y.occurrence_retained_bytes(), x.occurrence_retained_bytes()),
            (y.emitted_facts(), x.emitted_facts()),
            (
                y.occurrence_record_retained_bytes(),
                x.occurrence_record_retained_bytes(),
            ),
            (y.component_retained_bytes(), x.component_retained_bytes()),
            (y.fact_retained_bytes(), x.fact_retained_bytes()),
            (y.provenance_retained_bytes(), x.provenance_retained_bytes()),
            (
                y.solved_projection_retained_bytes(),
                x.solved_projection_retained_bytes(),
            ),
            (
                y.solver_workspace_retained_bytes(),
                x.solver_workspace_retained_bytes(),
            ),
            (y.canonical_map_capacity(), x.canonical_map_capacity()),
            (y.index_capacity(), x.index_capacity()),
            (y.canonical_map_rebuilds(), x.canonical_map_rebuilds()),
            (y.index_rebuilds(), x.index_rebuilds()),
        ] {
            assert!(large < small * 5 / 2 + 1);
        }
        assert!(y.canonical_map_probes() < x.canonical_map_probes().saturating_mul(5) / 2 + 1);
    }
    #[test]
    fn binding_n_and_2n_counters_remain_linear() {
        let source = |n| {
            (0..n)
                .map(|index| format!("my binding_{index} = 42"))
                .collect::<Vec<_>>()
                .join("; ")
        };
        let a = SolvedModule::solve(collect(module(&source(1000), "n.yu"))).unwrap();
        let b = SolvedModule::solve(collect(module(&source(2000), "2n.yu"))).unwrap();
        for (n, solved) in [(1000, &a), (2000, &b)] {
            for item in solved.hir().items() {
                let HirItem::Binding(binding) = item else {
                    panic!("integer-only scale fixture contains bindings");
                };
                assert_eq!(
                    solved.root_value_for(binding.definition_root()),
                    Ok(SolvedValue::Int),
                    "every integer binding has its exact finalized Int root result"
                );
            }
            let c = solved.counters();
            assert_eq!(c.hir_traversals(), 1);
            assert_eq!(c.body_pass_visits(), n);
            assert_eq!(c.definition_registration_visits(), n);
            assert_eq!(c.collected_definitions(), n);
            assert_eq!(c.collected_complete_bodies(), n);
            assert_eq!(c.collected_error_bodies(), 0);
            assert_eq!(c.definition_use_endpoint_pass_visits(), 0);
            assert_eq!(c.definition_use_endpoint_workspace_peak_capacity(), 0);
            assert_eq!(c.retained_definition_uses(), 0);
            assert_eq!(c.emitted_facts(), 5 * n);
            assert_eq!(c.admitted_facts(), 5 * n);
            assert_eq!(c.occurrence_allocations(), n);
            assert_eq!(c.root_allocations(), n);
            assert_eq!(
                c.hir_definition_root_allocation_bytes(),
                n * std::mem::size_of::<DefinitionRootId>()
            );
            assert_eq!(c.component_allocations(), 3 * n);
            assert_eq!(c.fact_allocations(), 5 * n);
            assert_eq!(c.provenance_edges(), 5 * n);
            assert_eq!(c.generated_work_items(), 5 * n);
            assert_eq!(c.accepted_work_items(), 5 * n);
            assert_eq!(c.duplicate_work_items(), 0);
            assert_eq!(c.adjacency_appends(), 0);
            assert_eq!(c.adjacency_visits(), 0);
            assert_eq!(c.maximum_fan_out(), 0);
            assert_eq!(c.duplicate_facts(), 0);
            assert_eq!(c.cst_traversals(), 0);
            assert_eq!(c.cst_rescans(), 0);
            assert_eq!(c.hir_clone_count(), 0);
            assert_eq!(c.typed_tree_copies(), 0);
            assert_eq!(c.copied_spelling_bytes(), 0);
            assert_eq!(c.definition_root_def_id_clone_bytes(), 0);
            assert_eq!(c.eager_explanation_builds(), 0);
            assert_eq!(c.scc_count(), n);
            assert_eq!(c.definition_query_probes(), 0);
            assert_eq!(c.definition_use_query_probes(), 0);
            assert_eq!(c.scc_component_for_definition_query_probes(), 0);
            assert_eq!(c.scc_component_members_query_probes(), n);
            assert_eq!(c.scc_component_internal_uses_query_probes(), n);
            assert_eq!(c.scc_component_incoming_uses_query_probes(), n);
            assert_eq!(c.scc_plan_component_index_probes(), n);
            assert_eq!(c.scc_plan_definition_index_probes(), n);
            assert_eq!(c.scc_execution_component_visits(), n);
            assert_eq!(c.scc_execution_internal_use_connections(), 0);
            assert_eq!(c.scc_execution_draft_members(), n);
            assert_eq!(c.scc_execution_drafts_visible_barriers(), n);
            assert_eq!(c.scc_execution_finalized_members(), n);
            assert_eq!(c.scc_execution_installed_members(), n);
            assert_eq!(c.scc_execution_incoming_instantiations(), 0);
            assert_eq!(c.scc_execution_int_instantiation_facts(), 0);
            assert_eq!(c.scc_execution_bottom_trivial_instantiations(), 0);
            assert_eq!(c.scc_execution_draft_lookups(), n);
            assert_eq!(c.scc_execution_cross_draft_visits(), 0);
            assert_eq!(c.scheme_table_len(), n);
            assert_eq!(c.finish_projection_visits(), n);
            assert_eq!(c.solved_root_query_probes(), n);
            assert_eq!(c.scheme_root_query_probes(), n);
        }
        let x = a.counters();
        let y = b.counters();
        for (large, small) in [
            (y.generated_work_items(), x.generated_work_items()),
            (y.accepted_work_items(), x.accepted_work_items()),
            (y.adjacency_visits(), x.adjacency_visits()),
            (y.component_allocations(), x.component_allocations()),
            (y.fact_allocations(), x.fact_allocations()),
            (y.occurrence_retained_bytes(), x.occurrence_retained_bytes()),
            (y.root_retained_bytes(), x.root_retained_bytes()),
            (y.component_retained_bytes(), x.component_retained_bytes()),
            (y.f2_batch_retained_bytes(), x.f2_batch_retained_bytes()),
            (y.f2_batch_plan_peak_bytes(), x.f2_batch_plan_peak_bytes()),
            (
                y.scc_plan_retained_payload_bytes(),
                x.scc_plan_retained_payload_bytes(),
            ),
            (
                y.scc_f1_graph_input_plan_peak_known_bytes(),
                x.scc_f1_graph_input_plan_peak_known_bytes(),
            ),
            (y.fact_retained_bytes(), x.fact_retained_bytes()),
            (
                y.canonical_map_retained_bytes(),
                x.canonical_map_retained_bytes(),
            ),
            (
                y.occurrence_component_index_retained_bytes(),
                x.occurrence_component_index_retained_bytes(),
            ),
            (
                y.root_component_index_retained_bytes(),
                x.root_component_index_retained_bytes(),
            ),
            (
                y.consumed_receipt_index_retained_bytes(),
                x.consumed_receipt_index_retained_bytes(),
            ),
            (
                y.solved_root_index_retained_bytes(),
                x.solved_root_index_retained_bytes(),
            ),
            (
                y.occurrence_record_retained_bytes(),
                x.occurrence_record_retained_bytes(),
            ),
            (y.provenance_retained_bytes(), x.provenance_retained_bytes()),
            (
                y.solved_projection_retained_bytes(),
                x.solved_projection_retained_bytes(),
            ),
            (
                y.solver_workspace_retained_bytes(),
                x.solver_workspace_retained_bytes(),
            ),
            (
                y.bounds_workspace_retained_bytes(),
                x.bounds_workspace_retained_bytes(),
            ),
            (
                y.fanout_index_retained_bytes(),
                x.fanout_index_retained_bytes(),
            ),
            (
                y.failed_component_workspace_retained_bytes(),
                x.failed_component_workspace_retained_bytes(),
            ),
            (
                y.solver_error_workspace_retained_bytes(),
                x.solver_error_workspace_retained_bytes(),
            ),
            (y.canonical_map_capacity(), x.canonical_map_capacity()),
            (
                y.occurrence_component_index_capacity(),
                x.occurrence_component_index_capacity(),
            ),
            (
                y.root_component_index_capacity(),
                x.root_component_index_capacity(),
            ),
            (
                y.consumed_receipt_index_capacity(),
                x.consumed_receipt_index_capacity(),
            ),
            (
                y.solved_root_index_capacity(),
                x.solved_root_index_capacity(),
            ),
            (y.index_capacity(), x.index_capacity()),
            (y.canonical_map_rebuilds(), x.canonical_map_rebuilds()),
            (y.index_rebuilds(), x.index_rebuilds()),
            (
                y.definition_endpoint_index_peak_capacity(),
                x.definition_endpoint_index_peak_capacity(),
            ),
            (
                y.definition_record_index_capacity(),
                x.definition_record_index_capacity(),
            ),
            (
                y.scc_component_members_query_probes(),
                x.scc_component_members_query_probes(),
            ),
            (
                y.scc_component_internal_uses_query_probes(),
                x.scc_component_internal_uses_query_probes(),
            ),
            (
                y.scc_component_incoming_uses_query_probes(),
                x.scc_component_incoming_uses_query_probes(),
            ),
            (
                y.scc_plan_component_index_probes(),
                x.scc_plan_component_index_probes(),
            ),
            (
                y.scc_plan_definition_index_probes(),
                x.scc_plan_definition_index_probes(),
            ),
            (
                y.scc_execution_component_visits(),
                x.scc_execution_component_visits(),
            ),
            (
                y.scc_execution_draft_members(),
                x.scc_execution_draft_members(),
            ),
            (
                y.scc_execution_drafts_visible_barriers(),
                x.scc_execution_drafts_visible_barriers(),
            ),
            (
                y.scc_execution_finalized_members(),
                x.scc_execution_finalized_members(),
            ),
            (
                y.scc_execution_installed_members(),
                x.scc_execution_installed_members(),
            ),
            (
                y.scc_execution_draft_lookups(),
                x.scc_execution_draft_lookups(),
            ),
            (y.scheme_table_len(), x.scheme_table_len()),
            (y.finish_projection_visits(), x.finish_projection_visits()),
        ] {
            assert!(large < small * 5 / 2 + 1);
        }
        for (large, small) in [
            (y.canonical_map_probes(), x.canonical_map_probes()),
            (
                y.occurrence_component_index_probes(),
                x.occurrence_component_index_probes(),
            ),
            (
                y.root_component_index_probes(),
                x.root_component_index_probes(),
            ),
            (
                y.consumed_receipt_index_probes(),
                x.consumed_receipt_index_probes(),
            ),
            (y.solved_root_query_probes(), x.solved_root_query_probes()),
            (y.scheme_root_query_probes(), x.scheme_root_query_probes()),
        ] {
            assert!(large < small.saturating_mul(5) / 2 + 1);
        }
    }

    #[test]
    fn f5b_live_rows_translate_injectively_and_drive_f4_projection() {
        let batch = ConstraintBatch::collect(module("1", "f5b-live-rows")).unwrap();
        let component_count = batch.components.len();
        let value_count = batch
            .components
            .iter()
            .filter(|component| component.kind() == ComponentKind::Value)
            .count();
        let mut session = InferenceSession::try_new(batch).unwrap();
        assert_eq!(session.live_components.len(), component_count);
        assert_eq!(session.bounds.len(), value_count);
        assert!(session.value_levels.iter().all(|&level| level == 1));
        assert!(session.effect_levels.iter().all(|&level| level == 1));
        let values = session
            .live_components
            .iter()
            .filter(|endpoint| endpoint.kind == ComponentKind::Value)
            .map(|endpoint| endpoint.ordinal)
            .collect::<Vec<_>>();
        let effects = session
            .live_components
            .iter()
            .filter(|endpoint| endpoint.kind == ComponentKind::Effect)
            .map(|endpoint| endpoint.ordinal)
            .collect::<Vec<_>>();
        assert_eq!(values, (0..value_count as u32).collect::<Vec<_>>());
        assert_eq!(effects, (0..effects.len() as u32).collect::<Vec<_>>());
        session.admit_all_collected_facts().unwrap();
        assert!(session.occurrence_exact_bounds.is_empty());
        let occurrence = session.batch.projection_order[0].clone();
        let positions = session.batch.occurrence_component_positions[&occurrence];
        let value = session.live_components[positions.value].ordinal as usize;
        let effect = session.live_components[positions.effect].ordinal as usize;
        assert!(session.bounds[value].has_int_positive_lower);
        assert!(
            session.bounds[value]
                .exact_non_variable_uppers
                .contains(&ValueEndpointKey::IntNegative)
        );
        assert!(session.effect_bounds[effect].has_bottom_lower);
        assert!(session.effect_bounds[effect].has_empty_upper);
    }

    #[test]
    fn f5b_resolved_use_recipes_freeze_level_and_translate_with_metadata() {
        let batch = ConstraintBatch::collect(module(
            "my source = 42; my sink = source",
            "f5b-live-recipe-evidence.yu",
        ))
        .unwrap();
        assert_eq!(batch.definition_uses.len(), 1);
        let use_record = &batch.definition_uses[0];
        assert_eq!(use_record.use_level, 1);
        let use_positions = batch.occurrence_component_positions[&use_record.occurrence];
        let target_position = use_record.target_root_component;
        assert_eq!(use_record.use_value_component, use_positions.value);
        assert_ne!(use_positions.value, use_positions.effect);
        assert_ne!(use_positions.value, target_position);

        let mut session = InferenceSession::try_new(batch).unwrap();
        let use_value = session.live_components[use_positions.value];
        let use_effect = session.live_components[use_positions.effect];
        let target_root = session.live_components[target_position];
        assert_eq!(use_value.kind, ComponentKind::Value);
        assert_eq!(use_effect.kind, ComponentKind::Effect);
        assert_eq!(target_root.kind, ComponentKind::Value);
        assert_ne!(use_value.ordinal, target_root.ordinal);
        assert_eq!(session.value_levels[use_value.ordinal as usize], 1);
        assert_eq!(session.effect_levels[use_effect.ordinal as usize], 1);
        assert_eq!(session.value_levels[target_root.ordinal as usize], 1);
        assert_eq!(
            session.value_metadata[use_value.ordinal as usize],
            LiveVariableMetadata {
                origin: LiveVariableOrigin::Collected,
                non_generic: false
            }
        );
        assert_eq!(
            session.effect_metadata[use_effect.ordinal as usize],
            LiveVariableMetadata {
                origin: LiveVariableOrigin::Collected,
                non_generic: false
            }
        );

        let fresh_value = session.fresh_value_at_level(2).unwrap() as usize;
        let fresh_effect = session.fresh_effect_at_level(3).unwrap() as usize;
        assert_eq!(session.value_levels[fresh_value], 2);
        assert_eq!(session.effect_levels[fresh_effect], 3);
        assert_eq!(
            session.value_metadata[fresh_value].origin,
            LiveVariableOrigin::Fresh
        );
        assert_eq!(
            session.effect_metadata[fresh_effect].origin,
            LiveVariableOrigin::Fresh
        );
        assert!(!session.value_metadata[fresh_value].non_generic);
        assert!(!session.effect_metadata[fresh_effect].non_generic);
    }

    #[test]
    fn f5b_function_decomposition_ages_variables_and_preserves_incompatible_rows() {
        let batch = ConstraintBatch::collect(module("1", "f5b-function-table")).unwrap();
        let mut session = InferenceSession::try_new(batch).unwrap();
        let left = session.fresh_value_at_level(2).unwrap();
        let right = session.fresh_value_at_level(3).unwrap();
        let left_effect = session.fresh_effect_at_level(2).unwrap();
        let right_effect = session.fresh_effect_at_level(3).unwrap();
        let left_arg = session.live_value_term(Polarity::Negative, left).unwrap();
        let left_argument_effect = session
            .live_effect_term(Polarity::Negative, left_effect)
            .unwrap();
        let left_result_effect = session
            .live_effect_term(Polarity::Positive, left_effect)
            .unwrap();
        let left_result = session.live_value_term(Polarity::Positive, left).unwrap();
        let positive = session
            .positive_function_term(
                left_arg,
                left_argument_effect,
                left_result_effect,
                left_result,
            )
            .unwrap();
        let right_arg = session.live_value_term(Polarity::Positive, right).unwrap();
        let right_argument_effect = session
            .live_effect_term(Polarity::Positive, right_effect)
            .unwrap();
        let right_result_effect = session
            .live_effect_term(Polarity::Negative, right_effect)
            .unwrap();
        let right_result = session.live_value_term(Polarity::Negative, right).unwrap();
        let negative = session
            .negative_function_term(
                right_arg,
                right_argument_effect,
                right_result_effect,
                right_result,
            )
            .unwrap();
        let occurrence = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 91);
        let cause = CauseId::for_occurrence(occurrence.clone());
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(positive),
                    upper: ValueEndpointKey::NegativeFunction(negative),
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        assert!(
            session.bounds[left as usize]
                .direct_lower_rows
                .contains(&right)
        );
        assert!(
            session.bounds[left as usize]
                .direct_upper_rows
                .contains(&right)
        );
        assert_eq!(session.value_levels[left as usize], 2);
        assert_eq!(session.value_levels[right as usize], 2);
        let before = session.bounds.clone();
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::IntPositive,
                    upper: ValueEndpointKey::BottomNegative,
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        assert_eq!(session.bounds, before);
        assert!(matches!(
            session.errors.last().map(SolverError::kind),
            Some(SolverErrorKind::IncompatibleValue {
                lower: ValueShape::Int,
                upper: ValueShape::Bottom,
            })
        ));
    }

    #[test]
    fn f5b_structured_variable_extrusion_lowers_value_and_effect_children_in_both_directions() {
        let batch = ConstraintBatch::collect(module("1", "f5b-structured-extrusion")).unwrap();
        let mut session = InferenceSession::try_new(batch).unwrap();
        let positive_value = session.fresh_value_at_level(2).unwrap();
        let positive_effect = session.fresh_effect_at_level(2).unwrap();
        let negative_value = session.fresh_value_at_level(2).unwrap();
        let negative_effect = session.fresh_effect_at_level(2).unwrap();
        let receiver = session.fresh_value_at_level(1).unwrap();
        let sender = session.fresh_value_at_level(1).unwrap();
        let positive_children = (
            session
                .live_value_term(Polarity::Negative, positive_value)
                .unwrap(),
            session
                .live_effect_term(Polarity::Negative, positive_effect)
                .unwrap(),
            session
                .live_effect_term(Polarity::Positive, positive_effect)
                .unwrap(),
            session
                .live_value_term(Polarity::Positive, positive_value)
                .unwrap(),
        );
        let positive = session
            .positive_function_term(
                positive_children.0,
                positive_children.1,
                positive_children.2,
                positive_children.3,
            )
            .unwrap();
        let negative_children = (
            session
                .live_value_term(Polarity::Positive, negative_value)
                .unwrap(),
            session
                .live_effect_term(Polarity::Positive, negative_effect)
                .unwrap(),
            session
                .live_effect_term(Polarity::Negative, negative_effect)
                .unwrap(),
            session
                .live_value_term(Polarity::Negative, negative_value)
                .unwrap(),
        );
        let negative = session
            .negative_function_term(
                negative_children.0,
                negative_children.1,
                negative_children.2,
                negative_children.3,
            )
            .unwrap();
        let occurrence =
            ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 125);
        let cause = CauseId::for_occurrence(occurrence.clone());
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(positive),
                    upper: ValueEndpointKey::ValueRow(receiver),
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::ValueRow(sender),
                    upper: ValueEndpointKey::NegativeFunction(negative),
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        for value in [positive_value, negative_value] {
            assert_eq!(session.value_levels[value as usize], 1);
        }
        for effect in [positive_effect, negative_effect] {
            assert_eq!(session.effect_levels[effect as usize], 1);
        }
    }

    #[test]
    fn f5b_structured_duplicate_replays_one_canonical_witness_for_its_new_source() {
        let batch = ConstraintBatch::collect(module("1", "f5b-duplicate-summary")).unwrap();
        let mut session = InferenceSession::try_new(batch).unwrap();
        let negative_leaf_function = session
            .negative_function_term(
                session.batch.collected_leaf_term(Leaf::IntPositive),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                session.batch.collected_leaf_term(Leaf::IntNegative),
            )
            .unwrap();
        let positive_leaf_function = session
            .positive_function_term(
                session.batch.collected_leaf_term(Leaf::IntNegative),
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                session.batch.collected_leaf_term(Leaf::IntPositive),
            )
            .unwrap();
        let lower = session
            .positive_function_term(
                negative_leaf_function,
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                positive_leaf_function,
            )
            .unwrap();
        let upper = session
            .negative_function_term(
                session.batch.collected_leaf_term(Leaf::IntPositive),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                session.batch.collected_leaf_term(Leaf::IntNegative),
            )
            .unwrap();
        let key = CanonicalValuePairKey {
            lower: ValueEndpointKey::PositiveFunction(lower),
            upper: ValueEndpointKey::NegativeFunction(upper),
        };
        let first = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 92);
        let first_cause = CauseId::for_occurrence(first.clone());
        session
            .constrain_live_value(key, &first, &first_cause)
            .unwrap();
        assert_eq!(
            std::mem::size_of::<TypedWorkItem>(),
            std::mem::size_of::<LiveConstraintTask>(),
            "typed transmission storage carries no occurrence/cause identity"
        );
        assert!(session.typed_pair_worklist_pushes > 1);
        let after_first_pairs = session.typed_pairs.len();
        let after_first_bounds = session.bounds.clone();
        assert_eq!(
            session
                .errors
                .iter()
                .map(SolverError::kind)
                .collect::<Vec<_>>(),
            vec![SolverErrorKind::IncompatibleValue {
                lower: ValueShape::Int,
                upper: ValueShape::Function,
            },]
        );
        session
            .constrain_live_value(key, &first, &first_cause)
            .unwrap();
        assert_eq!(session.errors.len(), 1, "same source stays deduplicated");
        let replay = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 93);
        let replay_cause = CauseId::for_occurrence(replay.clone());
        session
            .constrain_live_value(key, &replay, &replay_cause)
            .unwrap();
        assert_eq!(session.typed_pairs.len(), after_first_pairs);
        assert_eq!(session.bounds, after_first_bounds);
        assert_eq!(
            &session.errors[1..],
            [SolverError {
                occurrence: replay.clone(),
                cause: replay_cause.clone(),
                kind: SolverErrorKind::IncompatibleValue {
                    lower: ValueShape::Int,
                    upper: ValueShape::Function,
                },
            },]
        );
        assert!(session.typed_worklist.is_empty());
    }

    #[test]
    fn f5b_variable_mediated_int_function_incompatibility_is_order_independent() {
        for function_first in [false, true] {
            let batch =
                ConstraintBatch::collect(module("1", "f5b-mediated-incompatibility")).unwrap();
            let mut session = InferenceSession::try_new(batch).unwrap();
            let variable = session.fresh_value_at_level(1).unwrap();
            let negative_function = session
                .negative_function_term(
                    session.batch.collected_leaf_term(Leaf::IntPositive),
                    session
                        .batch
                        .collected_leaf_term(Leaf::EffectBottomPositive),
                    session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                    session.batch.collected_leaf_term(Leaf::IntNegative),
                )
                .unwrap();
            let function = CanonicalValuePairKey {
                lower: ValueEndpointKey::ValueRow(variable),
                upper: ValueEndpointKey::NegativeFunction(negative_function),
            };
            let integer = CanonicalValuePairKey {
                lower: ValueEndpointKey::IntPositive,
                upper: ValueEndpointKey::ValueRow(variable),
            };
            let first = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 94);
            let second = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 95);
            let first_cause = CauseId::for_occurrence(first.clone());
            let second_cause = CauseId::for_occurrence(second.clone());
            let (first_key, second_key) = if function_first {
                (function, integer)
            } else {
                (integer, function)
            };
            session
                .constrain_live_value(first_key, &first, &first_cause)
                .unwrap();
            assert!(session.errors.is_empty());
            session
                .constrain_live_value(second_key, &second, &second_cause)
                .unwrap();
            assert_eq!(
                session.errors.as_slice(),
                [SolverError {
                    occurrence: second.clone(),
                    cause: second_cause,
                    kind: SolverErrorKind::IncompatibleValue {
                        lower: ValueShape::Int,
                        upper: ValueShape::Function,
                    },
                }],
                "the second direct fact induces the replay in either insertion order"
            );
            assert!(session.typed_worklist.is_empty());
            assert!(session.typed_pairs.contains_key(&TypedPairKey::Value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::IntPositive,
                    upper: ValueEndpointKey::NegativeFunction(negative_function),
                }
            )));
        }
    }

    #[test]
    fn f5b_cyclic_witness_completes_and_later_duplicate_replays_once() {
        let batch = ConstraintBatch::collect(module("1", "f5b-cyclic-witness")).unwrap();
        let mut session = InferenceSession::try_new(batch).unwrap();
        let lower_row = session.fresh_value_at_level(1).unwrap();
        let upper_row = session.fresh_value_at_level(1).unwrap();
        let argument_function = session
            .positive_function_term(
                session.batch.collected_leaf_term(Leaf::IntNegative),
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                session.batch.collected_leaf_term(Leaf::IntPositive),
            )
            .unwrap();
        let lower_result = session
            .live_value_term(Polarity::Positive, lower_row)
            .unwrap();
        let upper_result = session
            .live_value_term(Polarity::Negative, upper_row)
            .unwrap();
        let lower = session
            .positive_function_term(
                session.batch.collected_leaf_term(Leaf::IntNegative),
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                lower_result,
            )
            .unwrap();
        let upper = session
            .negative_function_term(
                argument_function,
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                upper_result,
            )
            .unwrap();
        let first = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 97);
        let first_cause = CauseId::for_occurrence(first.clone());
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(lower),
                    upper: ValueEndpointKey::ValueRow(lower_row),
                },
                &first,
                &first_cause,
            )
            .unwrap();
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::ValueRow(upper_row),
                    upper: ValueEndpointKey::NegativeFunction(upper),
                },
                &first,
                &first_cause,
            )
            .unwrap();
        let root = CanonicalValuePairKey {
            lower: ValueEndpointKey::ValueRow(lower_row),
            upper: ValueEndpointKey::ValueRow(upper_row),
        };
        session
            .constrain_live_value(root, &first, &first_cause)
            .unwrap();
        assert_eq!(
            session.errors.last().map(SolverError::kind),
            Some(SolverErrorKind::IncompatibleValue {
                lower: ValueShape::Function,
                upper: ValueShape::Int,
            })
        );
        assert!(session.typed_worklist.is_empty());
        assert!(session.diagnostic_delta.is_empty());
        assert!(session.diagnostic_scc_worklist.is_empty());
        let pair_count = session.typed_pairs.len();
        let replay = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 98);
        let replay_cause = CauseId::for_occurrence(replay.clone());
        session
            .constrain_live_value(root, &replay, &replay_cause)
            .unwrap();
        assert_eq!(session.typed_pairs.len(), pair_count);
        assert_eq!(
            session.errors.last(),
            Some(&SolverError {
                occurrence: replay,
                cause: replay_cause,
                kind: SolverErrorKind::IncompatibleValue {
                    lower: ValueShape::Function,
                    upper: ValueShape::Int,
                },
            })
        );
    }

    #[test]
    fn f5b_canonical_witness_orders_kind_before_argument_result_field() {
        for reverse_allocation in [false, true] {
            let batch = ConstraintBatch::collect(module("1", "f5b-witness-order")).unwrap();
            let mut session = InferenceSession::try_new(batch).unwrap();
            let make_argument = |session: &mut InferenceSession| {
                session
                    .positive_function_term(
                        session.batch.collected_leaf_term(Leaf::IntNegative),
                        session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                        session
                            .batch
                            .collected_leaf_term(Leaf::EffectBottomPositive),
                        session.batch.collected_leaf_term(Leaf::IntPositive),
                    )
                    .unwrap()
            };
            let make_result = |session: &mut InferenceSession| {
                session
                    .negative_function_term(
                        session.batch.collected_leaf_term(Leaf::IntPositive),
                        session
                            .batch
                            .collected_leaf_term(Leaf::EffectBottomPositive),
                        session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                        session.batch.collected_leaf_term(Leaf::IntNegative),
                    )
                    .unwrap()
            };
            let (argument_function, result_function) = if reverse_allocation {
                let result = make_result(&mut session);
                let argument = make_argument(&mut session);
                (argument, result)
            } else {
                let argument = make_argument(&mut session);
                let result = make_result(&mut session);
                (argument, result)
            };
            let lower = session
                .positive_function_term(
                    session.batch.collected_leaf_term(Leaf::IntNegative),
                    session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                    session
                        .batch
                        .collected_leaf_term(Leaf::EffectBottomPositive),
                    session.batch.collected_leaf_term(Leaf::IntPositive),
                )
                .unwrap();
            let upper = session
                .negative_function_term(
                    argument_function,
                    session
                        .batch
                        .collected_leaf_term(Leaf::EffectBottomPositive),
                    session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                    result_function,
                )
                .unwrap();
            let argument_child = CanonicalValuePairKey {
                lower: ValueEndpointKey::PositiveFunction(argument_function),
                upper: ValueEndpointKey::IntNegative,
            };
            let result_child = CanonicalValuePairKey {
                lower: ValueEndpointKey::IntPositive,
                upper: ValueEndpointKey::NegativeFunction(result_function),
            };
            let child_occurrence = ConstraintOccurrenceId::new(
                session.batch.projection_order[0].clone(),
                if reverse_allocation { 101 } else { 100 },
            );
            let child_cause = CauseId::for_occurrence(child_occurrence.clone());
            let children = if reverse_allocation {
                [result_child, argument_child]
            } else {
                [argument_child, result_child]
            };
            for child in children {
                session
                    .constrain_live_value(child, &child_occurrence, &child_cause)
                    .unwrap();
            }
            let occurrence = ConstraintOccurrenceId::new(
                session.batch.projection_order[0].clone(),
                if reverse_allocation { 103 } else { 102 },
            );
            let cause = CauseId::for_occurrence(occurrence.clone());
            session
                .constrain_live_value(
                    CanonicalValuePairKey {
                        lower: ValueEndpointKey::PositiveFunction(lower),
                        upper: ValueEndpointKey::NegativeFunction(upper),
                    },
                    &occurrence,
                    &cause,
                )
                .unwrap();
            assert_eq!(
                session.errors.last().map(SolverError::kind),
                Some(SolverErrorKind::IncompatibleValue {
                    lower: ValueShape::Int,
                    upper: ValueShape::Function,
                }),
                "the lower-ranked kind wins despite the Result field"
            );
        }
    }

    #[test]
    fn f5b_cyclic_multi_seed_witnesses_choose_each_members_nearest_terminal() {
        for reverse_admission_and_allocation in [false, true] {
            let batch = ConstraintBatch::collect(module("1", "f5b-cyclic-multi-seed")).unwrap();
            let mut session = InferenceSession::try_new(batch).unwrap();
            let (first_row, second_row) = if reverse_admission_and_allocation {
                let second = session.fresh_value_at_level(1).unwrap();
                let first = session.fresh_value_at_level(1).unwrap();
                (first, second)
            } else {
                let first = session.fresh_value_at_level(1).unwrap();
                let second = session.fresh_value_at_level(1).unwrap();
                (first, second)
            };
            let first = CanonicalValuePairKey {
                lower: ValueEndpointKey::ValueRow(first_row),
                upper: ValueEndpointKey::ValueRow(second_row),
            };
            let second = CanonicalValuePairKey {
                lower: ValueEndpointKey::ValueRow(second_row),
                upper: ValueEndpointKey::ValueRow(first_row),
            };
            let first_terminal = CanonicalValuePairKey {
                lower: ValueEndpointKey::IntPositive,
                upper: ValueEndpointKey::BottomNegative,
            };
            let positive_function = session
                .positive_function_term(
                    session.batch.collected_leaf_term(Leaf::IntNegative),
                    session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                    session
                        .batch
                        .collected_leaf_term(Leaf::EffectBottomPositive),
                    session.batch.collected_leaf_term(Leaf::IntPositive),
                )
                .unwrap();
            let second_terminal = CanonicalValuePairKey {
                lower: ValueEndpointKey::PositiveFunction(positive_function),
                upper: ValueEndpointKey::IntNegative,
            };
            let terminal_memo = |terminal, kind| TypedPairMemo::Value {
                children: Vec::new(),
                direct_witness: Some(DiagnosticWitness {
                    terminal,
                    kind,
                    distance: 0,
                    first_field: None,
                }),
                completion: DiagnosticCompletion::Complete(Some(DiagnosticWitness {
                    terminal,
                    kind,
                    distance: 0,
                    first_field: None,
                })),
            };
            session.typed_pairs.insert(
                TypedPairKey::Value(first_terminal),
                terminal_memo(
                    first_terminal,
                    SolverErrorKind::IncompatibleValue {
                        lower: ValueShape::Int,
                        upper: ValueShape::Bottom,
                    },
                ),
            );
            session.typed_pairs.insert(
                TypedPairKey::Value(second_terminal),
                terminal_memo(
                    second_terminal,
                    SolverErrorKind::IncompatibleValue {
                        lower: ValueShape::Function,
                        upper: ValueShape::Int,
                    },
                ),
            );
            let node_memo = |children| TypedPairMemo::Value {
                children,
                direct_witness: None,
                completion: DiagnosticCompletion::Pending,
            };
            // Each SCC entry has its own one-edge external seed.  The
            // internal edges make a two-node cycle, so a one-global-seed
            // traversal would incorrectly give one member a distance-two
            // witness from its neighbour.
            session.typed_pairs.insert(
                TypedPairKey::Value(first),
                node_memo(vec![
                    DiagnosticEdge {
                        child: second,
                        field: Some(FunctionField::Argument),
                    },
                    DiagnosticEdge {
                        child: first_terminal,
                        field: Some(FunctionField::Result),
                    },
                ]),
            );
            session.typed_pairs.insert(
                TypedPairKey::Value(second),
                node_memo(vec![
                    DiagnosticEdge {
                        child: first,
                        field: Some(FunctionField::Argument),
                    },
                    DiagnosticEdge {
                        child: second_terminal,
                        field: Some(FunctionField::Result),
                    },
                ]),
            );
            let delta = if reverse_admission_and_allocation {
                [second, first]
            } else {
                [first, second]
            };
            session.diagnostic_delta.extend(delta);
            for (index, key) in delta.into_iter().enumerate() {
                session.diagnostic_delta_indices.insert(key, index);
            }
            session.complete_diagnostic_delta().unwrap();
            let witness_for = |key| match session.typed_pairs[&TypedPairKey::Value(key)] {
                TypedPairMemo::Value {
                    completion: DiagnosticCompletion::Complete(Some(witness)),
                    ..
                } => witness,
                _ => unreachable!("each cyclic entry completes"),
            };
            let first_witness = witness_for(first);
            let second_witness = witness_for(second);
            assert_eq!(first_witness.terminal, first_terminal);
            assert_eq!(second_witness.terminal, second_terminal);
            assert_eq!(first_witness.distance, 1);
            assert_eq!(second_witness.distance, 1);
            assert_eq!(first_witness.first_field, Some(FunctionField::Result));
            assert_eq!(second_witness.first_field, Some(FunctionField::Result));
            assert_eq!(session.diagnostic_settle_visits, 2);
            assert_eq!(session.diagnostic_internal_reverse_edge_visits, 2);
            assert_eq!(
                session.diagnostic_scc_member_seed_scans, 2,
                "the two-member delta is scanned once through its SCC member slice"
            );
            assert!(session.diagnostic_delta.is_empty());
            assert!(session.diagnostic_reverse_edges.is_empty());
        }
    }

    #[test]
    fn f5b_seedless_diagnostic_cycle_completes_none_without_settle_or_edge_visit() {
        let batch = ConstraintBatch::collect(module("1", "f5b-seedless-cycle")).unwrap();
        let mut session = InferenceSession::try_new(batch).unwrap();
        let first_row = session.fresh_value_at_level(1).unwrap();
        let second_row = session.fresh_value_at_level(1).unwrap();
        let first = CanonicalValuePairKey {
            lower: ValueEndpointKey::ValueRow(first_row),
            upper: ValueEndpointKey::ValueRow(second_row),
        };
        let second = CanonicalValuePairKey {
            lower: ValueEndpointKey::ValueRow(second_row),
            upper: ValueEndpointKey::ValueRow(first_row),
        };
        let pending = |child, field| TypedPairMemo::Value {
            children: vec![DiagnosticEdge { child, field }],
            direct_witness: None,
            completion: DiagnosticCompletion::Pending,
        };
        session.typed_pairs.insert(
            TypedPairKey::Value(first),
            pending(second, Some(FunctionField::Argument)),
        );
        session.typed_pairs.insert(
            TypedPairKey::Value(second),
            pending(first, Some(FunctionField::Result)),
        );
        for (index, key) in [first, second].into_iter().enumerate() {
            session.diagnostic_delta.push(key);
            session.diagnostic_delta_indices.insert(key, index);
        }
        session.complete_diagnostic_delta().unwrap();
        for key in [first, second] {
            assert!(matches!(
                session.typed_pairs[&TypedPairKey::Value(key)],
                TypedPairMemo::Value {
                    completion: DiagnosticCompletion::Complete(None),
                    ..
                }
            ));
        }
        assert_eq!(session.diagnostic_settle_visits, 0);
        assert_eq!(session.diagnostic_internal_reverse_edge_visits, 0);
        assert!(session.diagnostic_delta.is_empty());
        assert!(session.diagnostic_reverse_edges.is_empty());
    }

    #[test]
    fn f5b_singleton_scc_seed_scan_is_one_dense_delta_member() {
        let batch = ConstraintBatch::collect(module("1", "f5b-singleton-scc-scan")).unwrap();
        let mut session = InferenceSession::try_new(batch).unwrap();
        let key = CanonicalValuePairKey {
            lower: ValueEndpointKey::IntPositive,
            upper: ValueEndpointKey::BottomNegative,
        };
        let witness = DiagnosticWitness {
            terminal: key,
            kind: SolverErrorKind::IncompatibleValue {
                lower: ValueShape::Int,
                upper: ValueShape::Bottom,
            },
            distance: 0,
            first_field: None,
        };
        session.typed_pairs.insert(
            TypedPairKey::Value(key),
            TypedPairMemo::Value {
                children: Vec::new(),
                direct_witness: Some(witness),
                completion: DiagnosticCompletion::Pending,
            },
        );
        session.diagnostic_delta.push(key);
        session.diagnostic_delta_indices.insert(key, 0);
        session.complete_diagnostic_delta().unwrap();
        assert_eq!(session.diagnostic_scc_member_seed_scans, 1);
    }

    #[test]
    fn f5b_disjoint_admissions_leave_old_complete_entries_out_of_delta_work() {
        let batch = ConstraintBatch::collect(module("1", "f5b-disjoint-delta")).unwrap();
        let mut session = InferenceSession::try_new(batch).unwrap();
        let positive = session
            .positive_function_term(
                session.batch.collected_leaf_term(Leaf::IntNegative),
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                session.batch.collected_leaf_term(Leaf::IntPositive),
            )
            .unwrap();
        let negative = session
            .negative_function_term(
                session.batch.collected_leaf_term(Leaf::IntPositive),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                session.batch.collected_leaf_term(Leaf::IntNegative),
            )
            .unwrap();
        let first_key = CanonicalValuePairKey {
            lower: ValueEndpointKey::PositiveFunction(positive),
            upper: ValueEndpointKey::IntNegative,
        };
        let second_key = CanonicalValuePairKey {
            lower: ValueEndpointKey::IntPositive,
            upper: ValueEndpointKey::NegativeFunction(negative),
        };
        let first = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 104);
        let first_cause = CauseId::for_occurrence(first.clone());
        session
            .constrain_live_value(first_key, &first, &first_cause)
            .unwrap();
        let first_witness = match session.typed_pairs[&TypedPairKey::Value(first_key)] {
            TypedPairMemo::Value {
                completion: DiagnosticCompletion::Complete(witness),
                ..
            } => witness,
            _ => unreachable!("the first synchronous delta completed"),
        };
        assert_eq!(session.typed_pairs.len(), 1);
        let second = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 105);
        let second_cause = CauseId::for_occurrence(second.clone());
        session
            .constrain_live_value(second_key, &second, &second_cause)
            .unwrap();
        assert_eq!(session.typed_pairs.len(), 2);
        assert_eq!(
            match session.typed_pairs[&TypedPairKey::Value(first_key)] {
                TypedPairMemo::Value {
                    completion: DiagnosticCompletion::Complete(witness),
                    ..
                } => witness,
                _ => unreachable!("old entries stay Complete"),
            },
            first_witness
        );
        assert!(session.diagnostic_delta.is_empty());
        assert!(session.diagnostic_reverse_edges.is_empty());
        assert!(session.diagnostic_scc_worklist.is_empty());
    }

    #[test]
    fn f5b_bottom_and_top_identity_rows_leave_live_rows_and_levels_unchanged() {
        let batch = ConstraintBatch::collect(module("1", "f5b-identity-rows")).unwrap();
        let mut session = InferenceSession::try_new(batch).unwrap();
        let value = session.fresh_value_at_level(3).unwrap();
        let occurrence = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 96);
        let cause = CauseId::for_occurrence(occurrence.clone());
        let before_bounds = session.bounds.clone();
        let before_levels = session.value_levels.clone();
        for key in [
            CanonicalValuePairKey {
                lower: ValueEndpointKey::BottomPositive,
                upper: ValueEndpointKey::ValueRow(value),
            },
            CanonicalValuePairKey {
                lower: ValueEndpointKey::ValueRow(value),
                upper: ValueEndpointKey::TopNegative,
            },
        ] {
            session
                .constrain_live_value(key, &occurrence, &cause)
                .unwrap();
        }
        assert_eq!(session.bounds, before_bounds);
        assert_eq!(session.value_levels, before_levels);
        assert!(session.errors.is_empty());
    }

    #[test]
    fn f5b_reserve_lanes_fail_before_publication_and_clean_retry_preserves_committed_handles() {
        // Startup owns all coupled live/diagnostic lanes.  Each deterministic
        // lane failure occurs before a session can publish a SolvedModule.
        for lane in [
            F5bCapacityLane::LiveComponents,
            F5bCapacityLane::ValueBounds,
            F5bCapacityLane::EffectBounds,
            F5bCapacityLane::ValueLevels,
            F5bCapacityLane::EffectLevels,
            F5bCapacityLane::ValueMetadata,
            F5bCapacityLane::EffectMetadata,
            F5bCapacityLane::ExtrusionStack,
            F5bCapacityLane::ExtrusionValueMarks,
            F5bCapacityLane::ExtrusionEffectMarks,
            F5bCapacityLane::TypedPairs,
            F5bCapacityLane::TypedWorklist,
            F5bCapacityLane::DiagnosticDelta,
            F5bCapacityLane::DiagnosticDeltaIndices,
            F5bCapacityLane::DiagnosticReverseOffsets,
            F5bCapacityLane::DiagnosticReverseEdges,
            F5bCapacityLane::DiagnosticReverseCursors,
            F5bCapacityLane::DiagnosticDfsStack,
            F5bCapacityLane::DiagnosticFinishOrder,
            F5bCapacityLane::DiagnosticSccIndices,
            F5bCapacityLane::DiagnosticSccNodes,
            F5bCapacityLane::DiagnosticSccOffsets,
            F5bCapacityLane::DiagnosticSccPendingChildren,
            F5bCapacityLane::DiagnosticSccWorklist,
            F5bCapacityLane::DiagnosticBucketHeads,
            F5bCapacityLane::DiagnosticBucketTails,
            F5bCapacityLane::DiagnosticNodeWitnesses,
            F5bCapacityLane::Errors,
            F5bCapacityLane::ReportedErrors,
            F5bCapacityLane::CrossKindComponents,
            F5bCapacityLane::RoutedUses,
            F5bCapacityLane::RoutedUsePositions,
            F5bCapacityLane::Schemes,
            F5bCapacityLane::Drafts,
        ] {
            inject_next_f5b_reserve_failure(lane);
            assert!(
                matches!(
                    InferenceSession::try_new(
                        ConstraintBatch::collect(module("1", "f5b-reserve")).unwrap()
                    ),
                    Err(SolveAvailabilityError::IdentityExhausted)
                ),
                "{lane:?} fails before session publication"
            );
        }

        let mut session = InferenceSession::try_new(
            ConstraintBatch::collect(module("1", "f5b-reserve-retry")).unwrap(),
        )
        .unwrap();
        let committed = session.fresh_value_at_level(1).unwrap();
        inject_next_f5b_reserve_failure(F5bCapacityLane::ValueBounds);
        assert_eq!(
            session.fresh_value_at_level(2),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert_eq!(session.value_levels[committed as usize], 1);
        let retry = session.fresh_value_at_level(2).unwrap();
        assert_eq!(session.value_levels[retry as usize], 2);
    }

    #[test]
    fn f5b_runtime_reserve_failures_remain_availability_and_do_not_publish_a_module() {
        let make_occurrence = |session: &InferenceSession, ordinal| {
            let occurrence =
                ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), ordinal);
            let cause = CauseId::for_occurrence(occurrence.clone());
            (occurrence, cause)
        };

        // Deep Function extrusion grows at operation time, not only at startup.
        let mut session = InferenceSession::try_new(
            ConstraintBatch::collect(module("1", "f5b-deep-extrusion")).unwrap(),
        )
        .unwrap();
        let younger = session.fresh_value_at_level(2).unwrap();
        let younger_term = session
            .live_value_term(Polarity::Positive, younger)
            .unwrap();
        let mut nested = younger_term;
        for _ in 0..32 {
            nested = session
                .positive_function_term(
                    session.batch.collected_leaf_term(Leaf::IntNegative),
                    session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                    session
                        .batch
                        .collected_leaf_term(Leaf::EffectBottomPositive),
                    nested,
                )
                .unwrap();
        }
        let target = session.fresh_value_at_level(1).unwrap();
        let (occurrence, cause) = make_occurrence(&session, 122);
        let before_levels = session.value_levels.clone();
        inject_next_f5b_reserve_failure(F5bCapacityLane::ExtrusionStack);
        assert_eq!(
            session.constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(nested),
                    upper: ValueEndpointKey::ValueRow(target),
                },
                &occurrence,
                &cause,
            ),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert_eq!(session.value_levels, before_levels);
        assert!(session.typed_pairs.is_empty());
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(nested),
                    upper: ValueEndpointKey::ValueRow(target),
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        assert_eq!(session.value_levels[younger as usize], 1);

        // Exact rows, direct rows, and Function diagnostic edges all expose
        // the retained availability error rather than silently allocating.
        for lane in [
            F5bCapacityLane::ValueExactLower,
            F5bCapacityLane::ValueDirectLower,
            F5bCapacityLane::ValueDirectUpper,
        ] {
            let mut attempt = InferenceSession::try_new(
                ConstraintBatch::collect(module("1", "f5b-runtime-reserve")).unwrap(),
            )
            .unwrap();
            let lower = attempt.fresh_value_at_level(1).unwrap();
            let upper = attempt.fresh_value_at_level(1).unwrap();
            let (occurrence, cause) = make_occurrence(&attempt, 123);
            inject_next_f5b_reserve_failure(lane);
            let key = match lane {
                F5bCapacityLane::ValueExactLower => CanonicalValuePairKey {
                    lower: ValueEndpointKey::IntPositive,
                    upper: ValueEndpointKey::ValueRow(upper),
                },
                F5bCapacityLane::ValueDirectLower | F5bCapacityLane::ValueDirectUpper => {
                    CanonicalValuePairKey {
                        lower: ValueEndpointKey::ValueRow(lower),
                        upper: ValueEndpointKey::ValueRow(upper),
                    }
                }
                _ => unreachable!("the witness names only value-row reserve lanes"),
            };
            assert_eq!(
                attempt.constrain_live_value(key, &occurrence, &cause),
                Err(SolveAvailabilityError::IdentityExhausted)
            );
            assert!(attempt.errors.is_empty());
        }
        let mut effect_attempt = InferenceSession::try_new(
            ConstraintBatch::collect(module("1", "f5b-effect-runtime-reserve")).unwrap(),
        )
        .unwrap();
        let effect_row = effect_attempt.fresh_effect_at_level(1).unwrap();
        let (occurrence, cause) = make_occurrence(&effect_attempt, 126);
        inject_next_f5b_reserve_failure(F5bCapacityLane::EffectExactLower);
        assert_eq!(
            effect_attempt.constrain_live_effect(
                EffectEndpointKey::BottomPositive,
                EffectEndpointKey::EffectRow(effect_row),
                &occurrence,
                &cause,
            ),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert!(effect_attempt.errors.is_empty());
        assert!(effect_attempt.typed_worklist.is_empty());
        let mut diagnostic_attempt = InferenceSession::try_new(
            ConstraintBatch::collect(module("1", "f5b-diagnostic-reserve")).unwrap(),
        )
        .unwrap();
        let (occurrence, cause) = make_occurrence(&diagnostic_attempt, 124);
        inject_next_f5b_reserve_failure(F5bCapacityLane::DiagnosticBucketCandidates);
        assert_eq!(
            diagnostic_attempt.constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::IntPositive,
                    upper: ValueEndpointKey::BottomNegative,
                },
                &occurrence,
                &cause,
            ),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert!(diagnostic_attempt.errors.is_empty());
        let mut edge_attempt = InferenceSession::try_new(
            ConstraintBatch::collect(module("1", "f5b-diagnostic-edge-reserve")).unwrap(),
        )
        .unwrap();
        let positive = edge_attempt
            .positive_function_term(
                edge_attempt.batch.collected_leaf_term(Leaf::IntNegative),
                edge_attempt
                    .batch
                    .collected_leaf_term(Leaf::EmptyEffectNegative),
                edge_attempt
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                edge_attempt.batch.collected_leaf_term(Leaf::IntPositive),
            )
            .unwrap();
        let negative = edge_attempt
            .negative_function_term(
                edge_attempt.batch.collected_leaf_term(Leaf::IntPositive),
                edge_attempt
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                edge_attempt
                    .batch
                    .collected_leaf_term(Leaf::EmptyEffectNegative),
                edge_attempt.batch.collected_leaf_term(Leaf::IntNegative),
            )
            .unwrap();
        let (occurrence, cause) = make_occurrence(&edge_attempt, 125);
        inject_next_f5b_reserve_failure(F5bCapacityLane::DiagnosticEdges);
        assert_eq!(
            edge_attempt.constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(positive),
                    upper: ValueEndpointKey::NegativeFunction(negative),
                },
                &occurrence,
                &cause,
            ),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert!(edge_attempt.errors.is_empty());
        assert!(
            SolvedModule::solve(
                ConstraintBatch::collect(module("1", "f5b-diagnostic-retry")).unwrap()
            )
            .is_ok(),
            "a discarded failed attempt leaves a clean batch retry path"
        );
        assert_eq!(
            InferenceSession::child_level(u32::MAX),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
    }

    #[test]
    fn f5b_live_effect_function_and_diagnostic_growth_reconcile_independent_aggregates() {
        let batch = ConstraintBatch::collect(module("1", "f5b-aggregate")).unwrap();
        let mut session = InferenceSession::try_new(batch).unwrap();
        let value = session.fresh_value_at_level(2).unwrap();
        let effect = session.fresh_effect_at_level(2).unwrap();
        let negative_value = session.live_value_term(Polarity::Negative, value).unwrap();
        let positive_value = session.live_value_term(Polarity::Positive, value).unwrap();
        let negative_effect = session
            .live_effect_term(Polarity::Negative, effect)
            .unwrap();
        let positive_effect = session
            .live_effect_term(Polarity::Positive, effect)
            .unwrap();
        let positive = session
            .positive_function_term(
                negative_value,
                negative_effect,
                positive_effect,
                positive_value,
            )
            .unwrap();
        let negative = session
            .negative_function_term(
                positive_value,
                positive_effect,
                negative_effect,
                negative_value,
            )
            .unwrap();
        let occurrence =
            ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 119);
        let cause = CauseId::for_occurrence(occurrence.clone());
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(positive),
                    upper: ValueEndpointKey::NegativeFunction(negative),
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        let second_value = session.fresh_value_at_level(2).unwrap();
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::ValueRow(value),
                    upper: ValueEndpointKey::ValueRow(second_value),
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::IntPositive,
                    upper: ValueEndpointKey::ValueRow(value),
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::ValueRow(second_value),
                    upper: ValueEndpointKey::IntNegative,
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        let second_effect = session.fresh_effect_at_level(2).unwrap();
        session
            .constrain_live_effect(
                EffectEndpointKey::EffectRow(effect),
                EffectEndpointKey::EffectRow(second_effect),
                &occurrence,
                &cause,
            )
            .unwrap();
        session
            .constrain_live_effect(
                EffectEndpointKey::BottomPositive,
                EffectEndpointKey::EffectRow(effect),
                &occurrence,
                &cause,
            )
            .unwrap();
        session
            .constrain_live_effect(
                EffectEndpointKey::EffectRow(second_effect),
                EffectEndpointKey::EmptyNegative,
                &occurrence,
                &cause,
            )
            .unwrap();
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(positive),
                    upper: ValueEndpointKey::BottomNegative,
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        session.sample_f4_resources(ResourceBoundary::InternalRoute);
        let lanes = &session.independent_nested_capacities;
        assert!(lanes.value_direct_lower > 0);
        assert!(lanes.value_direct_upper > 0);
        assert!(lanes.value_exact_lower > 0);
        assert!(lanes.value_exact_upper > 0);
        assert!(lanes.effect_direct_lower > 0);
        assert!(lanes.effect_direct_upper > 0);
        assert!(lanes.effect_exact_lower > 0);
        assert!(lanes.effect_exact_upper > 0);
        assert!(lanes.diagnostic_edges > 0);
        assert_eq!(lanes.total_bound_bytes(), session.bound_payload_bytes);
        assert!(session.execution_counters.bound_table_capacity() >= session.bounds.capacity());
        assert!(session.execution_counters.bound_table_retained_bytes() > 0);
        assert_eq!(
            session.resource_ledger.semantic_arena_retained_bytes,
            session.execution_counters.semantic_arena_retained_bytes()
        );
        assert_eq!(
            session.resource_ledger.inference_session_retained_bytes,
            session
                .execution_counters
                .inference_session_retained_bytes()
        );
        assert_eq!(session.errors.len(), 1);
    }

    #[test]
    fn f5b_all_incompatible_shapes_include_function_bottom_direct_and_derived_duplicates() {
        let batch = ConstraintBatch::collect(module("1", "f5b-incompatible-shapes")).unwrap();
        let mut session = InferenceSession::try_new(batch).unwrap();
        let value = session.fresh_value_at_level(1).unwrap();
        let effect = session.fresh_effect_at_level(1).unwrap();
        let negative_value = session.live_value_term(Polarity::Negative, value).unwrap();
        let positive_value = session.live_value_term(Polarity::Positive, value).unwrap();
        let negative_effect = session
            .live_effect_term(Polarity::Negative, effect)
            .unwrap();
        let positive_effect = session
            .live_effect_term(Polarity::Positive, effect)
            .unwrap();
        let positive = session
            .positive_function_term(
                negative_value,
                negative_effect,
                positive_effect,
                positive_value,
            )
            .unwrap();
        let negative = session
            .negative_function_term(
                positive_value,
                positive_effect,
                negative_effect,
                negative_value,
            )
            .unwrap();
        let occurrence =
            ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 120);
        let cause = CauseId::for_occurrence(occurrence.clone());
        for key in [
            CanonicalValuePairKey {
                lower: ValueEndpointKey::IntPositive,
                upper: ValueEndpointKey::BottomNegative,
            },
            CanonicalValuePairKey {
                lower: ValueEndpointKey::IntPositive,
                upper: ValueEndpointKey::NegativeFunction(negative),
            },
            CanonicalValuePairKey {
                lower: ValueEndpointKey::PositiveFunction(positive),
                upper: ValueEndpointKey::BottomNegative,
            },
            CanonicalValuePairKey {
                lower: ValueEndpointKey::PositiveFunction(positive),
                upper: ValueEndpointKey::IntNegative,
            },
        ] {
            let before = session.bounds.clone();
            session
                .constrain_live_value(key, &occurrence, &cause)
                .unwrap();
            assert_eq!(
                session.bounds, before,
                "incompatible pair does not mutate a bound row"
            );
        }
        let errors_after_direct = session.errors.len();
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(positive),
                    upper: ValueEndpointKey::BottomNegative,
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        assert_eq!(
            session.errors.len(),
            errors_after_direct,
            "same direct source deduplicates"
        );

        let derived_row = session.fresh_value_at_level(1).unwrap();
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(positive),
                    upper: ValueEndpointKey::ValueRow(derived_row),
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        let derived = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 121);
        let derived_cause = CauseId::for_occurrence(derived.clone());
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::ValueRow(derived_row),
                    upper: ValueEndpointKey::BottomNegative,
                },
                &derived,
                &derived_cause,
            )
            .unwrap();
        assert_eq!(
            session.bounds[derived_row as usize].exact_non_variable_lowers,
            vec![ValueEndpointKey::PositiveFunction(positive)],
            "the derived incompatible child leaves its already-installed lower unchanged"
        );
        let errors_after_derived = session.errors.len();
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::ValueRow(derived_row),
                    upper: ValueEndpointKey::BottomNegative,
                },
                &derived,
                &derived_cause,
            )
            .unwrap();
        assert_eq!(
            session.errors.len(),
            errors_after_derived,
            "same derived source deduplicates"
        );
    }

    #[test]
    fn f5c_generalization_census_assigns_one_quantifier_to_a_bipolar_function_variable() {
        let batch = collect(module("my f = 1", "f5c-identity"));
        let mut session = InferenceSession::new(batch);
        let root = session.batch.definitions[0].root.clone();
        let definition = session.batch.definitions[0].definition.clone();
        let root_row = session.live_components
            [session.batch.root_component_positions[&root].component]
            .ordinal;
        let variable = session.fresh_value_at_level(1).unwrap();
        let argument = session
            .live_value_term(Polarity::Negative, variable)
            .unwrap();
        let result = session
            .live_value_term(Polarity::Positive, variable)
            .unwrap();
        let argument_effect = session.batch.collected_leaf_term(Leaf::EmptyEffectNegative);
        let result_effect = session
            .batch
            .collected_leaf_term(Leaf::EffectBottomPositive);
        let function = session
            .positive_function_term(argument, argument_effect, result_effect, result)
            .unwrap();
        let occurrence =
            ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 200);
        let cause = CauseId::for_occurrence(occurrence.clone());
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(function),
                    upper: ValueEndpointKey::ValueRow(root_row),
                },
                &occurrence,
                &cause,
            )
            .unwrap();

        let draft = session.generalization_draft(&definition).unwrap();
        assert_eq!(draft.quantifier_count, 1);
        assert!(draft.recursive_bounds.is_empty());
        let F5cPositive::Function {
            argument, result, ..
        } = &draft.predicate
        else {
            panic!("identity predicate remains a Function");
        };
        assert_eq!(**argument, F5cNegative::Quantified(0));
        assert_eq!(**result, F5cPositive::Quantified(0));

        let finalized = InferenceSession::finalize_generalization_draft(
            session.finalization.as_mut().unwrap(),
            &draft,
            false,
        )
        .unwrap();
        let (scheme, _) = finalized.into_parts();
        let decoded =
            InferenceSession::decode_closed_scheme(session.finalization.as_ref().unwrap(), &scheme)
                .unwrap();
        assert_eq!(decoded, draft);
    }

    #[test]
    fn f5c_generalization_expands_direct_rows_and_multiple_exact_lowers() {
        let batch = collect(module("my f = 1", "f5c-bounds"));
        let mut session = InferenceSession::new(batch);
        let root = session.batch.definitions[0].root.clone();
        let definition = session.batch.definitions[0].definition.clone();
        let root_row = session.live_components
            [session.batch.root_component_positions[&root].component]
            .ordinal;
        let lower_row = session.fresh_value_at_level(1).unwrap();
        let occurrence =
            ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 201);
        let cause = CauseId::for_occurrence(occurrence.clone());
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::ValueRow(lower_row),
                    upper: ValueEndpointKey::ValueRow(root_row),
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::IntPositive,
                    upper: ValueEndpointKey::ValueRow(lower_row),
                },
                &occurrence,
                &cause,
            )
            .unwrap();

        let draft = session.generalization_draft(&definition).unwrap();
        assert_eq!(draft.predicate, F5cPositive::Int);

        let function_argument = session.negative_top_term().unwrap();
        let function_result = session
            .live_value_term(Polarity::Positive, lower_row)
            .unwrap();
        let function = session
            .positive_function_term(
                function_argument,
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                function_result,
            )
            .unwrap();
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(function),
                    upper: ValueEndpointKey::ValueRow(root_row),
                },
                &occurrence,
                &cause,
            )
            .unwrap();
        let draft = session.generalization_draft(&definition).unwrap();
        let F5cPositive::Union(values) = draft.predicate else {
            panic!("direct row and Function lower are normalized together");
        };
        assert_eq!(values.len(), 2);
    }

    #[test]
    fn f5c_generalization_retains_guarded_self_as_one_recursive_bound() {
        let batch = collect(module("my f = 1", "f5c-self"));
        let mut session = InferenceSession::new(batch);
        let root = session.batch.definitions[0].root.clone();
        let definition = session.batch.definitions[0].definition.clone();
        let root_row = session.live_components
            [session.batch.root_component_positions[&root].component]
            .ordinal;
        let function_argument = session.negative_top_term().unwrap();
        let argument_effect = session.batch.collected_leaf_term(Leaf::EmptyEffectNegative);
        let result_effect = session
            .batch
            .collected_leaf_term(Leaf::EffectBottomPositive);
        let function_result = session
            .live_value_term(Polarity::Positive, root_row)
            .unwrap();
        let function = session
            .positive_function_term(
                function_argument,
                argument_effect,
                result_effect,
                function_result,
            )
            .unwrap();
        let occurrence =
            ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 202);
        let cause = CauseId::for_occurrence(occurrence.clone());
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(function),
                    upper: ValueEndpointKey::ValueRow(root_row),
                },
                &occurrence,
                &cause,
            )
            .unwrap();

        let draft = session.generalization_draft(&definition).unwrap();
        assert_eq!(draft.quantifier_count, 0);
        assert_eq!(draft.recursive_bounds.len(), 1);
        let F5cPositive::Function {
            argument, result, ..
        } = &draft.predicate
        else {
            panic!("guarded self predicate remains a Function");
        };
        assert_eq!(**argument, F5cNegative::Top);
        assert_eq!(**result, F5cPositive::Recursive(0));
        let bound = &draft.recursive_bounds[0];
        assert_eq!(bound.ordinal, 0);
        assert!(matches!(bound.upper, F5cNegative::Top));
        let F5cPositive::Function { result, .. } = &bound.lower else {
            panic!("recursive lower side keeps the guarded Function");
        };
        assert_eq!(**result, F5cPositive::Recursive(0));
    }

    #[test]
    fn f5c_guarded_opposite_polarity_reentry_owns_one_recursive_binder() {
        let batch = collect(module("my f = 1", "f5c-opposite-polarity"));
        let mut session = InferenceSession::new(batch);
        let root = session.batch.definitions[0].root.clone();
        let definition = session.batch.definitions[0].definition.clone();
        let root_row = session.live_components
            [session.batch.root_component_positions[&root].component]
            .ordinal;
        let argument = session
            .live_value_term(Polarity::Negative, root_row)
            .unwrap();
        let result = session.batch.collected_leaf_term(Leaf::IntPositive);
        let function = session
            .positive_function_term(
                argument,
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                result,
            )
            .unwrap();
        let occurrence =
            ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 203);
        let cause = CauseId::for_occurrence(occurrence.clone());
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(function),
                    upper: ValueEndpointKey::ValueRow(root_row),
                },
                &occurrence,
                &cause,
            )
            .unwrap();

        let draft = session.generalization_draft(&definition).unwrap();
        assert_eq!(draft.quantifier_count, 0);
        assert_eq!(draft.recursive_bounds.len(), 1);
        let F5cPositive::Function {
            argument, result, ..
        } = &draft.predicate
        else {
            panic!("opposite-polarity guarded predicate remains a Function");
        };
        assert_eq!(**argument, F5cNegative::Recursive(0));
        assert_eq!(**result, F5cPositive::Int);
    }

    #[test]
    fn f5c_incoming_union_routes_each_normalized_member() {
        let batch = collect(module("my source = 1; my sink = source", "f5c-union-route"));
        let route_id = batch.definition_uses()[0].id.clone();
        let mut session = InferenceSession::new(batch);
        let draft = GeneralizationDraft {
            quantifier_count: 0,
            recursive_bounds: Vec::new(),
            predicate: F5cPositive::Union(vec![
                F5cPositive::Int,
                F5cPositive::Function {
                    argument: Box::new(F5cNegative::Top),
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result: Box::new(F5cPositive::Int),
                },
            ]),
        };
        let finalized = InferenceSession::finalize_generalization_draft(
            session.finalization.as_mut().unwrap(),
            &draft,
            false,
        )
        .unwrap();
        let target = session.batch.definition_uses()[0].target.ordinal() as usize;
        session.schemes[target] = Some(finalized.into_parts().0);

        session.route_incoming(&route_id).unwrap();
        assert_eq!(session.routed_uses.len(), 1);
        assert_eq!(session.store.facts().len(), 1);
        assert_eq!(session.routed_use_positions.len(), 1);
    }
}
