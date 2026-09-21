//! Ordered directed-subtyping collection and deterministic reference solving.

use std::{
    collections::{HashMap, HashSet, VecDeque, hash_map::Entry},
    hash::{Hash, Hasher},
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

use yu_hir::{
    DefId, DefinitionRootId, HirItem, HirModule, HirOccurrenceId, NameResolution, ResolvedExpr,
};
use yu_types::{ClosedPositiveValue, ClosedValueScheme, ComponentKind, Leaf};

mod scc;
use scc::{SccComponentId, SccPlan};

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

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Term {
    Leaf(Leaf),
    Component(ComponentId),
}
impl Term {
    pub const fn kind(&self) -> ComponentKind {
        match self {
            Self::Leaf(leaf) => leaf.component_kind(),
            Self::Component(component) => component.kind(),
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
    pub fn lower(&self) -> &Term {
        &self.lower
    }
    pub fn upper(&self) -> &Term {
        &self.upper
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
    /// Frozen during collection so F4 generalization never hashes a source
    /// root to recover its value row.
    root_value_row: u32,
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
    /// Frozen F4 value-row endpoints. These are collection-owned ordinals,
    /// not source identities, so routing never reconstructs them from HIR.
    use_value_row: u32,
    parent_root_row: u32,
    target_root_row: u32,
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
    occurrence_bound_row: u32,
    value_bound_row: u32,
}

#[derive(Clone, Copy, Debug)]
struct RootComponentPositions {
    component: usize,
    value_bound_row: u32,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ValueEndpointKey {
    IntPositive,
    IntNegative,
    ValueRow(u32),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct CanonicalValuePairKey {
    lower: ValueEndpointKey,
    upper: ValueEndpointKey,
}

#[derive(Clone, Copy, Debug)]
enum FrozenConstraintClass {
    Value(CanonicalValuePairKey),
    Effect {
        occurrence_bound_row: u32,
        lower_is_bottom: bool,
        upper_is_empty: bool,
    },
    CrossKind,
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
    /// One private, fixed-size admission class per public occurrence.
    frozen_constraint_classes: Vec<FrozenConstraintClass>,
    frozen_occurrence_bound_rows: Vec<u32>,
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
            occurrence_component_positions: HashMap::new(),
            root_component_positions: HashMap::new(),
            root_definition_positions: HashMap::new(),
            root_scheme_identity_payload_bytes: Vec::new(),
            occurrences: Vec::new(),
            frozen_constraint_classes: Vec::new(),
            frozen_occurrence_bound_rows: Vec::new(),
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
                    let root_value_row = batch
                        .root_component_positions
                        .get(binding.definition_root())
                        .expect("new definition root has a frozen position")
                        .value_bound_row;
                    batch.definitions.push(CollectedDefinition {
                        definition: definition.clone(),
                        root: binding.definition_root().clone(),
                        root_value_row,
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
            let occurrence_bound_row = u32::try_from(batch.projection_order.len())
                .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
            batch.projection_order.push(expression.occurrence().clone());
            batch.counters.occurrence_allocations += 1;
            if matches!(expression, ResolvedExpr::Integer { .. }) {
                batch.emit_integer(
                    expression.occurrence().clone(),
                    definition_root.cloned(),
                    occurrence_bound_row,
                )?;
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
                batch.emit_resolved_binding_name(
                    occurrence.clone(),
                    (*root).clone(),
                    occurrence_bound_row,
                )?;
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
            let target_root_row = batch
                .root_component_positions
                .get(&batch.definitions[target.ordinal() as usize].root)
                .expect("target root has frozen component position")
                .value_bound_row;
            let target_root_component = batch
                .root_component_positions
                .get(&batch.definitions[target.ordinal() as usize].root)
                .expect("target root has frozen component position")
                .component;
            let parent_root_row = batch
                .root_component_positions
                .get(&batch.definitions[pending.parent_ordinal as usize].root)
                .expect("parent root has frozen component position")
                .value_bound_row;
            let use_value_row = batch
                .occurrence_component_positions
                .get(&pending.occurrence)
                .expect("resolved use has frozen component positions")
                .value_bound_row;
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
                use_value_row,
                parent_root_row,
                target_root_row,
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
        debug_assert_eq!(
            batch.occurrences.len(),
            batch.frozen_constraint_classes.len()
        );
        debug_assert_eq!(
            batch.occurrences.len(),
            batch.frozen_occurrence_bound_rows.len()
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
        let value_bound_row = self.next_value_bound_row()?;
        let value = self.definition_value_component(root.clone());
        let old_capacity = self.root_component_positions.capacity();
        self.root_component_positions.insert(
            root,
            RootComponentPositions {
                component: self.components.len() - 1,
                value_bound_row,
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
        occurrence_bound_row: u32,
    ) -> Result<(), CollectionAvailabilityError> {
        let value_bound_row = self.next_value_bound_row()?;
        let value = self.occurrence_component(occurrence.clone(), ComponentKind::Value);
        let effect = self.occurrence_component(occurrence.clone(), ComponentKind::Effect);
        let positions = ComponentPositions {
            value: self.components.len() - 2,
            effect: self.components.len() - 1,
            occurrence_bound_row,
            value_bound_row,
        };
        let old_capacity = self.occurrence_component_positions.capacity();
        self.occurrence_component_positions
            .insert(occurrence.clone(), positions);
        if self.occurrence_component_positions.capacity() != old_capacity {
            self.counters.index_rebuilds += 1;
        }
        self.emit(
            occurrence.clone(),
            0,
            Term::Leaf(Leaf::IntPositive),
            Term::Component(value.clone()),
        );
        self.emit(
            occurrence.clone(),
            1,
            Term::Component(value.clone()),
            Term::Leaf(Leaf::IntNegative),
        );
        self.emit(
            occurrence.clone(),
            2,
            Term::Leaf(Leaf::EffectBottomPositive),
            Term::Component(effect.clone()),
        );
        self.emit(
            occurrence.clone(),
            3,
            Term::Component(effect),
            Term::Leaf(Leaf::EmptyEffectNegative),
        );
        if let Some(root) = definition_root {
            let definition_value = self.root_value_component_for_collect(&root)?;
            self.emit(
                occurrence,
                4,
                Term::Component(value),
                Term::Component(definition_value),
            );
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
        occurrence_bound_row: u32,
    ) -> Result<(), CollectionAvailabilityError> {
        let value_bound_row = self.next_value_bound_row()?;
        let value = self.occurrence_component(occurrence.clone(), ComponentKind::Value);
        let effect = self.occurrence_component(occurrence.clone(), ComponentKind::Effect);
        let positions = ComponentPositions {
            value: self.components.len() - 2,
            effect: self.components.len() - 1,
            occurrence_bound_row,
            value_bound_row,
        };
        if self
            .occurrence_component_positions
            .insert(occurrence.clone(), positions)
            .is_some()
        {
            return Err(CollectionAvailabilityError::DuplicateDefinitionUseId);
        }
        let root = self.root_value_component_for_collect(&definition_root)?;
        self.emit(
            occurrence.clone(),
            1,
            Term::Leaf(Leaf::EffectBottomPositive),
            Term::Component(effect.clone()),
        );
        self.emit(
            occurrence.clone(),
            2,
            Term::Component(effect),
            Term::Leaf(Leaf::EmptyEffectNegative),
        );
        self.emit(occurrence, 3, Term::Component(value), Term::Component(root));
        Ok(())
    }
    fn occurrence_component(
        &mut self,
        occurrence: HirOccurrenceId,
        kind: ComponentKind,
    ) -> ComponentId {
        let component = ComponentId::Occurrence { occurrence, kind };
        self.components.push(component.clone());
        self.counters.component_allocations += 1;
        component
    }
    fn definition_value_component(&mut self, root: DefinitionRootId) -> ComponentId {
        let component = ComponentId::DefinitionValue { root };
        self.components.push(component.clone());
        self.counters.component_allocations += 1;
        component
    }
    fn emit(&mut self, occurrence: HirOccurrenceId, local_slot: u8, lower: Term, upper: Term) {
        let class = self.freeze_constraint_class(&lower, &upper);
        let occurrence_bound_row = self
            .occurrence_component_positions
            .get(&occurrence)
            .expect("emitted occurrence has frozen component positions")
            .occurrence_bound_row;
        let id = ConstraintOccurrenceId::new(occurrence, local_slot);
        self.occurrences.push(ConstraintOccurrence {
            cause: CauseId::for_occurrence(id.clone()),
            id,
            lower,
            upper,
        });
        self.frozen_constraint_classes.push(class);
        self.frozen_occurrence_bound_rows.push(occurrence_bound_row);
        self.counters.emitted_facts += 1;
        self.counters.generated_work_items += 1;
    }
    fn next_value_bound_row(&self) -> Result<u32, CollectionAvailabilityError> {
        let rows = self
            .root_component_positions
            .len()
            .checked_add(self.occurrence_component_positions.len())
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        u32::try_from(rows).map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)
    }
    fn freeze_constraint_class(&self, lower: &Term, upper: &Term) -> FrozenConstraintClass {
        if lower.kind() != upper.kind() {
            return FrozenConstraintClass::CrossKind;
        }
        match lower.kind() {
            ComponentKind::Value => FrozenConstraintClass::Value(CanonicalValuePairKey {
                lower: self.value_endpoint_key(lower),
                upper: self.value_endpoint_key(upper),
            }),
            ComponentKind::Effect => {
                let occurrence_bound_row = [lower, upper]
                    .into_iter()
                    .find_map(|term| match term {
                        Term::Component(ComponentId::Occurrence { occurrence, .. }) => Some(
                            self.occurrence_component_positions
                                .get(occurrence)
                                .expect("effect occurrence has a frozen position")
                                .occurrence_bound_row,
                        ),
                        _ => None,
                    })
                    .expect("F4 effect facts have an occurrence endpoint");
                FrozenConstraintClass::Effect {
                    occurrence_bound_row,
                    lower_is_bottom: matches!(lower, Term::Leaf(Leaf::EffectBottomPositive)),
                    upper_is_empty: matches!(upper, Term::Leaf(Leaf::EmptyEffectNegative)),
                }
            }
        }
    }
    fn value_endpoint_key(&self, term: &Term) -> ValueEndpointKey {
        match term {
            Term::Leaf(Leaf::IntPositive) => ValueEndpointKey::IntPositive,
            Term::Leaf(Leaf::IntNegative) => ValueEndpointKey::IntNegative,
            Term::Component(ComponentId::Occurrence { occurrence, .. }) => {
                ValueEndpointKey::ValueRow(
                    self.occurrence_component_positions
                        .get(occurrence)
                        .expect("value occurrence has a frozen position")
                        .value_bound_row,
                )
            }
            Term::Component(ComponentId::DefinitionValue { root }) => ValueEndpointKey::ValueRow(
                self.root_component_positions
                    .get(root)
                    .expect("definition root has a frozen position")
                    .value_bound_row,
            ),
            Term::Leaf(_) => unreachable!("F4 value endpoint is an integer leaf"),
        }
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
    pub fn lower(&self) -> &Term {
        &self.lower
    }
    pub fn upper(&self) -> &Term {
        &self.upper
    }
}

/// The artifact-bound semantic authority. The transaction emits receipts;
/// only `record_provenance` consumes them into the separate provenance log.
#[derive(Debug)]
pub struct ConstraintStore {
    hir: Arc<HirModule>,
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
    pub fn new(hir: Arc<HirModule>) -> Self {
        Self::with_capacity(hir, 0)
    }
    /// F4 reserves every store lane before initial admission.  The public
    /// constructor intentionally remains unreserved for standalone store use.
    fn with_capacity(hir: Arc<HirModule>, requested_capacity: usize) -> Self {
        let facts = Vec::with_capacity(requested_capacity);
        let canonical = HashMap::with_capacity(requested_capacity);
        let provenance = Vec::with_capacity(requested_capacity);
        let consumed_receipts = HashSet::with_capacity(requested_capacity);
        Self {
            hir,
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
    fn require_owned_component(&self, component: &ComponentId) -> Result<(), ConstraintError> {
        match component {
            ComponentId::Occurrence { occurrence, .. } => self.require_owned(occurrence),
            ComponentId::DefinitionValue { root } => self
                .hir
                .owns_definition_root(root)
                .then_some(())
                .ok_or(ConstraintError::ArtifactMismatch),
        }
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
        self.store.require_owned(occurrence.id.occurrence())?;
        if occurrence.cause.occurrence != occurrence.id {
            return Err(ConstraintError::CauseMismatch);
        }
        for term in [&occurrence.lower, &occurrence.upper] {
            if let Term::Component(component) = term {
                self.store.require_owned_component(component)?;
            }
        }
        if occurrence.lower.kind() != occurrence.upper.kind() {
            return Err(ConstraintError::CrossKind {
                lower: occurrence.lower.kind(),
                upper: occurrence.upper.kind(),
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
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SolverErrorKind {
    CrossKind {
        lower: ComponentKind,
        upper: ComponentKind,
    },
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
#[derive(Clone, Default)]
struct VariableBounds {
    /// The two row lists are the paired physical representation of one direct
    /// variable edge.  They deliberately do not encode transitive reachability.
    direct_lower_rows: Vec<u32>,
    direct_upper_rows: Vec<u32>,
    exact_non_variable_lowers: Vec<ValueEndpointKey>,
    exact_non_variable_uppers: Vec<ValueEndpointKey>,
    has_int_positive_lower: bool,
}

/// The source-free, session-local execution frontier.  It carries only the
/// same fixed keys accepted by the canonical value-pair cache; it is neither a
/// second type authority nor a persistent reachability label.
struct DirectBoundFrontier {
    queue: VecDeque<CanonicalValuePairKey>,
    peak_bytes: usize,
    #[cfg(test)]
    pushes: usize,
    #[cfg(test)]
    pops: usize,
    #[cfg(test)]
    maximum_live: usize,
    #[cfg(test)]
    capacity_growths: usize,
    #[cfg(test)]
    direct_edges: usize,
    #[cfg(test)]
    exact_lower_memberships: usize,
    #[cfg(test)]
    exact_upper_memberships: usize,
    #[cfg(test)]
    transmission_attempts: usize,
    #[cfg(test)]
    same_row_atom_intersections: usize,
}

impl DirectBoundFrontier {
    fn with_capacity(capacity: usize) -> Self {
        let queue = VecDeque::with_capacity(capacity);
        let peak_bytes = checked_capacity_bytes::<CanonicalValuePairKey>(
            queue.capacity(),
            "F4 direct frontier initial queue",
        );
        Self {
            queue,
            peak_bytes,
            #[cfg(test)]
            pushes: 0,
            #[cfg(test)]
            pops: 0,
            #[cfg(test)]
            maximum_live: 0,
            #[cfg(test)]
            capacity_growths: 0,
            #[cfg(test)]
            direct_edges: 0,
            #[cfg(test)]
            exact_lower_memberships: 0,
            #[cfg(test)]
            exact_upper_memberships: 0,
            #[cfg(test)]
            transmission_attempts: 0,
            #[cfg(test)]
            same_row_atom_intersections: 0,
        }
    }

    fn push(&mut self, key: CanonicalValuePairKey) {
        let old_capacity = self.queue.capacity();
        self.queue.push_back(key);
        let bytes = checked_capacity_bytes::<CanonicalValuePairKey>(
            self.queue.capacity(),
            "F4 direct frontier queue",
        );
        self.peak_bytes = self.peak_bytes.max(bytes);
        #[cfg(test)]
        {
            self.pushes += 1;
            self.maximum_live = self.maximum_live.max(self.queue.len());
            if self.queue.capacity() != old_capacity {
                self.capacity_growths += 1;
            }
        }
        #[cfg(not(test))]
        let _ = old_capacity;
    }

    fn pop(&mut self) -> Option<CanonicalValuePairKey> {
        let value = self.queue.pop_front();
        #[cfg(test)]
        if value.is_some() {
            self.pops += 1;
        }
        value
    }

    #[cfg(test)]
    fn direct_edge_installed(&mut self) {
        self.direct_edges += 1;
    }
    #[cfg(not(test))]
    fn direct_edge_installed(&mut self) {}

    #[cfg(test)]
    fn exact_lower_membership_installed(&mut self) {
        self.exact_lower_memberships += 1;
    }
    #[cfg(not(test))]
    fn exact_lower_membership_installed(&mut self) {}

    #[cfg(test)]
    fn exact_upper_membership_installed(&mut self) {
        self.exact_upper_memberships += 1;
    }
    #[cfg(not(test))]
    fn exact_upper_membership_installed(&mut self) {}

    #[cfg(test)]
    fn transmission_attempted(&mut self) {
        self.transmission_attempts += 1;
    }
    #[cfg(not(test))]
    fn transmission_attempted(&mut self) {}

    #[cfg(test)]
    fn same_row_intersection(&mut self) {
        self.same_row_atom_intersections += 1;
    }
    #[cfg(not(test))]
    fn same_row_intersection(&mut self) {}
}

#[derive(Clone, Copy, Default)]
struct OccurrenceExactBounds {
    value_lower_int: bool,
    value_upper_int: bool,
    effect_lower_bottom: bool,
    effect_upper_empty: bool,
}

#[derive(Clone, Copy)]
struct DraftScheme(ClosedValueScheme);

struct VerifiedSchemeDefinition<'a> {
    record: &'a CollectedDefinition,
    position: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RoutedUseKind {
    Internal,
    IncomingInt,
    IncomingBottomTrivial,
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
impl IndependentResourceLedger {
    fn record(
        &mut self,
        boundary: ResourceBoundary,
        store: &ConstraintStore,
        errors: &Vec<SolverError>,
        cross_kind_components: &HashSet<ComponentId>,
        bounds: &Vec<VariableBounds>,
        bound_payload_bytes: usize,
        occurrence_exact_bounds: &Vec<OccurrenceExactBounds>,
        constraint_pairs: &HashSet<CanonicalValuePairKey>,
        frontier: &DirectBoundFrontier,
        routed_uses: &Vec<RoutedUseProvenance>,
        routed_use_positions: &HashSet<DefinitionUseId>,
        schemes: &Vec<Option<ClosedValueScheme>>,
        drafts: &Vec<DraftScheme>,
        frozen_constraint_class_capacity: usize,
        frozen_occurrence_row_capacity: usize,
        f2_batch_retained_bytes: usize,
        finish_output_retained_bytes: usize,
    ) {
        self.coverage |= 1 << (boundary as u8);
        self.samples += 1;
        let queue_bytes = checked_capacity_bytes::<CanonicalValuePairKey>(
            frontier.queue.capacity(),
            "F4 independent frontier queue",
        );
        let semantic = checked_usize_sum(
            [
                checked_capacity_bytes::<VariableBounds>(
                    bounds.capacity(),
                    "F4 independent bound rows",
                )
                .checked_add(bound_payload_bytes)
                .expect("F4 independent bound payload byte accounting fits usize"),
                checked_capacity_bytes::<CanonicalValuePairKey>(
                    constraint_pairs.capacity(),
                    "F4 independent pair cache",
                ),
                queue_bytes,
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
                checked_capacity_bytes::<OccurrenceExactBounds>(
                    occurrence_exact_bounds.capacity(),
                    "F4 independent occurrence bounds",
                ),
                checked_capacity_bytes::<FrozenConstraintClass>(
                    frozen_constraint_class_capacity,
                    "F4 independent frozen constraint classes",
                ),
                checked_capacity_bytes::<u32>(
                    frozen_occurrence_row_capacity,
                    "F4 independent frozen occurrence rows",
                ),
            ],
            "F4 independent semantic ledger",
        );
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
                checked_capacity_bytes::<ComponentId>(
                    cross_kind_components.capacity(),
                    "F4 independent cross-kind components",
                ),
                checked_capacity_bytes::<DefinitionUseId>(
                    routed_use_positions.capacity(),
                    "F4 independent routed-use index",
                ),
                f2_batch_retained_bytes,
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
    cross_kind_components: HashSet<ComponentId>,
    bounds: Vec<VariableBounds>,
    bound_payload_bytes: usize,
    occurrence_exact_bounds: Vec<OccurrenceExactBounds>,
    constraint_pairs: HashSet<CanonicalValuePairKey>,
    frontier: DirectBoundFrontier,
    routed_uses: Vec<RoutedUseProvenance>,
    routed_use_positions: HashSet<DefinitionUseId>,
    schemes: Vec<Option<ClosedValueScheme>>,
    drafts: Vec<DraftScheme>,
    execution_counters: ProductionCounters,
    #[cfg(test)]
    summary_reads: usize,
    #[cfg(test)]
    summary_false_to_true_transitions: usize,
    #[cfg(test)]
    initial_value_pair_probes: usize,
    #[cfg(test)]
    ordering_observer: Option<OrderingObserver>,
    #[cfg(test)]
    resource_boundary_samples: usize,
    #[cfg(test)]
    resource_ledger: IndependentResourceLedger,
}
impl InferenceSession {
    fn new(batch: ConstraintBatch) -> Self {
        let value_component_count = batch
            .root_component_positions
            .len()
            .checked_add(batch.occurrence_component_positions.len())
            .expect("F4 value-row capacity");
        let occurrence_count = batch.projection_order.len();
        let definition_count = batch.definitions.len();
        let fact_capacity = batch
            .occurrences
            .len()
            .checked_add(batch.definition_uses.len())
            .expect("F4 fact capacity");
        let draft_capacity = batch.counters.scc_maximum_component_size;
        let routed_capacity = batch.definition_uses.len();
        let mut session = Self {
            store: ConstraintStore::with_capacity(batch.hir.clone(), fact_capacity),
            batch,
            errors: Vec::with_capacity(fact_capacity),
            cross_kind_components: HashSet::with_capacity(value_component_count),
            bounds: vec![VariableBounds::default(); value_component_count],
            bound_payload_bytes: 0,
            occurrence_exact_bounds: vec![OccurrenceExactBounds::default(); occurrence_count],
            constraint_pairs: HashSet::with_capacity(fact_capacity),
            frontier: DirectBoundFrontier::with_capacity(fact_capacity),
            routed_uses: Vec::with_capacity(routed_capacity),
            routed_use_positions: HashSet::with_capacity(routed_capacity),
            schemes: (0..definition_count).map(|_| None).collect(),
            drafts: Vec::with_capacity(draft_capacity),
            execution_counters: ProductionCounters::default(),
            #[cfg(test)]
            summary_reads: 0,
            #[cfg(test)]
            summary_false_to_true_transitions: 0,
            #[cfg(test)]
            initial_value_pair_probes: 0,
            #[cfg(test)]
            ordering_observer: None,
            #[cfg(test)]
            resource_boundary_samples: 0,
            #[cfg(test)]
            resource_ledger: IndependentResourceLedger::default(),
        };
        // Initial reservations coexist before any fact admission and are a
        // real resource boundary, not a final retained-byte alias.
        session.sample_f4_resources(ResourceBoundary::InitialReservation);
        session
    }

    #[cfg(test)]
    fn inject_next_admission_failure(&mut self, error: ConstraintError) {
        self.store.injected_admission_failure = Some(error);
    }

    #[cfg(test)]
    fn inject_next_provenance_failure(&mut self, error: ConstraintError) {
        self.store.injected_provenance_failure = Some(error);
    }

    fn run(mut self) -> Result<SolvedModule, SolveAvailabilityError> {
        self.admit_all_collected_facts()?;
        self.execute_scc_plan()?;
        self.sample_f4_resources(ResourceBoundary::StoreAccounting);
        self.store.finish_accounting();
        self.sample_f4_resources(ResourceBoundary::StoreAccounting);
        Ok(self.finish())
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
            frontier_pushes: self.frontier.pushes,
            frontier_pops: self.frontier.pops,
            frontier_maximum_live: self.frontier.maximum_live,
            frontier_capacity: self.frontier.queue.capacity(),
            frontier_capacity_growths: self.frontier.capacity_growths,
            frontier_retained_bytes: checked_capacity_bytes::<CanonicalValuePairKey>(
                self.frontier.queue.capacity(),
                "F4 observed frontier queue",
            ),
            frontier_peak_bytes: self.frontier.peak_bytes,
            direct_edges: self.frontier.direct_edges,
            exact_lower_memberships: self.frontier.exact_lower_memberships,
            exact_upper_memberships: self.frontier.exact_upper_memberships,
            transmission_attempts: self.frontier.transmission_attempts,
            same_row_atom_intersections: self.frontier.same_row_atom_intersections,
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
        let solved = self.finish();
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
            &self.cross_kind_components,
            &self.bounds,
            self.bound_payload_bytes,
            &self.occurrence_exact_bounds,
            &self.constraint_pairs,
            &self.frontier,
            &self.routed_uses,
            &self.routed_use_positions,
            &self.schemes,
            &self.drafts,
            self.batch.frozen_constraint_classes.capacity(),
            self.batch.frozen_occurrence_bound_rows.capacity(),
            self.batch.counters.f2_batch_retained_bytes,
            finish_output_retained_bytes,
            &mut self.execution_counters,
            #[cfg(test)]
            &mut self.resource_boundary_samples,
            #[cfg(test)]
            _boundary,
            #[cfg(test)]
            &mut self.resource_ledger,
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
        cross_kind_components: &HashSet<ComponentId>,
        bounds: &Vec<VariableBounds>,
        bound_payload_bytes: usize,
        occurrence_exact_bounds: &Vec<OccurrenceExactBounds>,
        constraint_pairs: &HashSet<CanonicalValuePairKey>,
        frontier: &DirectBoundFrontier,
        routed_uses: &Vec<RoutedUseProvenance>,
        routed_use_positions: &HashSet<DefinitionUseId>,
        schemes: &Vec<Option<ClosedValueScheme>>,
        drafts: &Vec<DraftScheme>,
        frozen_constraint_class_capacity: usize,
        frozen_occurrence_row_capacity: usize,
        f2_batch_retained_bytes: usize,
        finish_output_retained_bytes: usize,
        counters: &mut ProductionCounters,
        #[cfg(test)] resource_boundary_samples: &mut usize,
        #[cfg(test)] boundary: ResourceBoundary,
        #[cfg(test)] resource_ledger: &mut IndependentResourceLedger,
    ) {
        #[cfg(test)]
        {
            *resource_boundary_samples += 1;
            resource_ledger.record(
                boundary,
                store,
                errors,
                cross_kind_components,
                bounds,
                bound_payload_bytes,
                occurrence_exact_bounds,
                constraint_pairs,
                frontier,
                routed_uses,
                routed_use_positions,
                schemes,
                drafts,
                frozen_constraint_class_capacity,
                frozen_occurrence_row_capacity,
                f2_batch_retained_bytes,
                finish_output_retained_bytes,
            );
        }
        let bounds_rows_bytes =
            checked_capacity_bytes::<VariableBounds>(bounds.capacity(), "F4 production bound rows");
        let bounds_bytes = bounds_rows_bytes
            .checked_add(bound_payload_bytes)
            .expect("F4 bounds byte accounting fits usize");
        let pair_bytes = checked_capacity_bytes::<CanonicalValuePairKey>(
            constraint_pairs.capacity(),
            "F4 production pair cache",
        );
        let frontier_bytes = checked_capacity_bytes::<CanonicalValuePairKey>(
            frontier.queue.capacity(),
            "F4 production frontier queue",
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
        counters.bound_table_capacity = bounds.capacity();
        counters.bound_table_retained_bytes = bounds_bytes;
        counters.bound_table_peak_bytes = counters.bound_table_peak_bytes.max(bounds_bytes);
        counters.constraint_pair_cache_capacity = constraint_pairs.capacity();
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
                scheme_bytes,
                routes_bytes,
                drafts_bytes,
                exact_bytes,
                checked_capacity_bytes::<FrozenConstraintClass>(
                    frozen_constraint_class_capacity,
                    "F4 production frozen constraint classes",
                ),
                checked_capacity_bytes::<u32>(
                    frozen_occurrence_row_capacity,
                    "F4 production frozen occurrence rows",
                ),
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
            let class = self.batch.frozen_constraint_classes[occurrence_index];
            let occurrence_bound_row = self.batch.frozen_occurrence_bound_rows[occurrence_index];
            let result = {
                let mut transaction = self.store.transaction();
                transaction.admit(&occurrence)
            };
            match result {
                Ok(receipt) => {
                    self.store
                        .record_provenance(receipt)
                        .map_err(SolveAvailabilityError::from)?;
                    match class {
                        FrozenConstraintClass::Value(key) => {
                            #[cfg(test)]
                            {
                                self.initial_value_pair_probes += 1;
                            }
                            let exact =
                                &mut self.occurrence_exact_bounds[occurrence_bound_row as usize];
                            exact.value_lower_int |= key.lower == ValueEndpointKey::IntPositive;
                            exact.value_upper_int |= key.upper == ValueEndpointKey::IntNegative;
                            let transitions = Self::constrain(
                                &mut self.bounds,
                                &mut self.bound_payload_bytes,
                                &mut self.constraint_pairs,
                                &mut self.frontier,
                                &mut self.execution_counters,
                                key,
                            );
                            #[cfg(test)]
                            {
                                self.summary_false_to_true_transitions += transitions;
                            }
                            #[cfg(not(test))]
                            let _ = transitions;
                            self.sample_f4_resources(ResourceBoundary::InitialAdmission);
                        }
                        FrozenConstraintClass::Effect {
                            occurrence_bound_row,
                            lower_is_bottom,
                            upper_is_empty,
                        } => {
                            let exact =
                                &mut self.occurrence_exact_bounds[occurrence_bound_row as usize];
                            exact.effect_lower_bottom |= lower_is_bottom;
                            exact.effect_upper_empty |= upper_is_empty;
                            self.sample_f4_resources(ResourceBoundary::InitialAdmission);
                        }
                        FrozenConstraintClass::CrossKind => {
                            unreachable!("store classifies cross-kind fact")
                        }
                    }
                }
                Err(ConstraintError::CrossKind { lower, upper }) => {
                    self.errors.push(SolverError {
                        occurrence: occurrence.id.clone(),
                        cause: occurrence.cause.clone(),
                        kind: SolverErrorKind::CrossKind { lower, upper },
                    });
                    for term in [&occurrence.lower, &occurrence.upper] {
                        if let Term::Component(component) = term {
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

    fn constrain(
        bounds: &mut [VariableBounds],
        bound_payload_bytes: &mut usize,
        constraint_pairs: &mut HashSet<CanonicalValuePairKey>,
        frontier: &mut DirectBoundFrontier,
        counters: &mut ProductionCounters,
        key: CanonicalValuePairKey,
    ) -> usize {
        assert!(
            frontier.queue.is_empty(),
            "each public constrain drains the direct-bound frontier synchronously"
        );
        let mut transitions = 0;
        frontier.push(key);
        while let Some(key) = frontier.pop() {
            let old_capacity = constraint_pairs.capacity();
            if !constraint_pairs.insert(key) {
                counters.constraint_pair_duplicates += 1;
                continue;
            }
            if constraint_pairs.capacity() != old_capacity {
                counters.constraint_pair_cache_growths += 1;
                counters.constraint_pair_cache_rebuilds += 1;
            }
            counters.constraint_pair_admissions += 1;
            match (key.lower, key.upper) {
                (ValueEndpointKey::ValueRow(lower), ValueEndpointKey::ValueRow(upper)) => {
                    frontier.direct_edge_installed();
                    let lower_index = lower as usize;
                    let upper_index = upper as usize;
                    let old_lower_capacity = bounds[upper_index].direct_lower_rows.capacity();
                    bounds[upper_index].direct_lower_rows.push(lower);
                    Self::record_bound_capacity_growth(
                        bound_payload_bytes,
                        counters,
                        old_lower_capacity,
                        bounds[upper_index].direct_lower_rows.capacity(),
                        std::mem::size_of::<u32>(),
                    );
                    counters.lower_bound_insertions += 1;
                    let old_upper_capacity = bounds[lower_index].direct_upper_rows.capacity();
                    bounds[lower_index].direct_upper_rows.push(upper);
                    Self::record_bound_capacity_growth(
                        bound_payload_bytes,
                        counters,
                        old_upper_capacity,
                        bounds[lower_index].direct_upper_rows.capacity(),
                        std::mem::size_of::<u32>(),
                    );
                    counters.upper_bound_insertions += 1;

                    let lower_len = bounds[lower_index].exact_non_variable_lowers.len();
                    for index in 0..lower_len {
                        counters.lower_bound_replays += 1;
                        frontier.transmission_attempted();
                        frontier.push(CanonicalValuePairKey {
                            lower: bounds[lower_index].exact_non_variable_lowers[index],
                            upper: ValueEndpointKey::ValueRow(upper),
                        });
                    }
                    let upper_len = bounds[upper_index].exact_non_variable_uppers.len();
                    for index in 0..upper_len {
                        counters.upper_bound_replays += 1;
                        frontier.transmission_attempted();
                        frontier.push(CanonicalValuePairKey {
                            lower: ValueEndpointKey::ValueRow(lower),
                            upper: bounds[upper_index].exact_non_variable_uppers[index],
                        });
                    }
                }
                (atom, ValueEndpointKey::ValueRow(row)) => {
                    let index = row as usize;
                    let old_capacity = bounds[index].exact_non_variable_lowers.capacity();
                    bounds[index].exact_non_variable_lowers.push(atom);
                    Self::record_bound_capacity_growth(
                        bound_payload_bytes,
                        counters,
                        old_capacity,
                        bounds[index].exact_non_variable_lowers.capacity(),
                        std::mem::size_of::<ValueEndpointKey>(),
                    );
                    counters.lower_bound_insertions += 1;
                    frontier.exact_lower_membership_installed();
                    if atom == ValueEndpointKey::IntPositive
                        && !std::mem::replace(&mut bounds[index].has_int_positive_lower, true)
                    {
                        transitions += 1;
                    }
                    let upper_atoms = bounds[index].exact_non_variable_uppers.len();
                    for upper_index in 0..upper_atoms {
                        // Same-row atom intersections are owned by the lower
                        // side regardless of which insertion arrived second.
                        counters.lower_bound_replays += 1;
                        frontier.same_row_intersection();
                        frontier.push(CanonicalValuePairKey {
                            lower: atom,
                            upper: bounds[index].exact_non_variable_uppers[upper_index],
                        });
                    }
                    let upper_rows = bounds[index].direct_upper_rows.len();
                    for upper_index in 0..upper_rows {
                        counters.lower_bound_replays += 1;
                        frontier.transmission_attempted();
                        frontier.push(CanonicalValuePairKey {
                            lower: atom,
                            upper: ValueEndpointKey::ValueRow(
                                bounds[index].direct_upper_rows[upper_index],
                            ),
                        });
                    }
                }
                (ValueEndpointKey::ValueRow(row), atom) => {
                    let index = row as usize;
                    let old_capacity = bounds[index].exact_non_variable_uppers.capacity();
                    bounds[index].exact_non_variable_uppers.push(atom);
                    Self::record_bound_capacity_growth(
                        bound_payload_bytes,
                        counters,
                        old_capacity,
                        bounds[index].exact_non_variable_uppers.capacity(),
                        std::mem::size_of::<ValueEndpointKey>(),
                    );
                    counters.upper_bound_insertions += 1;
                    frontier.exact_upper_membership_installed();
                    let lower_atoms = bounds[index].exact_non_variable_lowers.len();
                    for lower_index in 0..lower_atoms {
                        counters.lower_bound_replays += 1;
                        frontier.same_row_intersection();
                        frontier.push(CanonicalValuePairKey {
                            lower: bounds[index].exact_non_variable_lowers[lower_index],
                            upper: atom,
                        });
                    }
                    let lower_rows = bounds[index].direct_lower_rows.len();
                    for lower_index in 0..lower_rows {
                        counters.upper_bound_replays += 1;
                        frontier.transmission_attempted();
                        frontier.push(CanonicalValuePairKey {
                            lower: ValueEndpointKey::ValueRow(
                                bounds[index].direct_lower_rows[lower_index],
                            ),
                            upper: atom,
                        });
                    }
                }
                // The existing terminal rule is the successful canonical
                // admission itself.  This closed integer slice has no extra
                // terminal bound mutation.
                (_, _) => {}
            }
        }
        debug_assert!(frontier.queue.is_empty());
        transitions
    }

    fn record_bound_capacity_growth(
        payload_bytes: &mut usize,
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
                    &self.cross_kind_components,
                    &self.bounds,
                    self.bound_payload_bytes,
                    &self.occurrence_exact_bounds,
                    &self.constraint_pairs,
                    &self.frontier,
                    &self.routed_uses,
                    &self.routed_use_positions,
                    &self.schemes,
                    &self.drafts,
                    self.batch.frozen_constraint_classes.capacity(),
                    self.batch.frozen_occurrence_bound_rows.capacity(),
                    self.batch.counters.f2_batch_retained_bytes,
                    0,
                    &mut self.execution_counters,
                    #[cfg(test)]
                    &mut self.resource_boundary_samples,
                    #[cfg(test)]
                    $boundary,
                    #[cfg(test)]
                    &mut self.resource_ledger,
                )
            };
        }
        let components = self.batch.scc_components_in_dependency_first_order();
        for component in components {
            self.execution_counters.scc_execution_component_visits += 1;
            let internal_uses = self
                .batch
                .scc_component_internal_uses(component)
                .expect("plan-owned component");
            for use_index in 0..internal_uses.len() {
                let id = &internal_uses[use_index];
                #[cfg(test)]
                if let Some(observer) = self.ordering_observer.as_mut() {
                    observer.record(|| ExecutionEvent::InternalUse(id.clone()));
                }
                let transitions = Self::route_internal(
                    &self.batch,
                    &mut self.store,
                    &mut self.bounds,
                    &mut self.bound_payload_bytes,
                    &mut self.constraint_pairs,
                    &mut self.frontier,
                    &mut self.routed_uses,
                    &mut self.routed_use_positions,
                    &mut self.execution_counters,
                    id,
                )?;
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
                .scc_component_members(component)
                .expect("plan-owned component");
            self.drafts.clear();
            // `clear` is a reuse boundary: it changes live draft ownership
            // without changing capacity, so sample it independently.
            sample_boundary!(ResourceBoundary::DraftScratchClear);
            for member_index in 0..members.len() {
                let member = &members[member_index];
                self.execution_counters.scc_execution_draft_members += 1;
                #[cfg(test)]
                if let Some(observer) = self.ordering_observer.as_mut() {
                    observer.record(|| ExecutionEvent::Drafted(member.clone()));
                }
                let old_capacity = self.drafts.capacity();
                #[cfg(test)]
                let draft =
                    Self::generalize(&self.batch, &self.bounds, member, &mut self.summary_reads);
                #[cfg(not(test))]
                let draft = Self::generalize(&self.batch, &self.bounds, member);
                self.drafts.push(DraftScheme(draft));
                if self.drafts.capacity() != old_capacity {
                    self.execution_counters.draft_scratch_growths += 1;
                }
                sample_boundary!(ResourceBoundary::DraftMember);
            }
            self.execution_counters.draft_scratch_max_len = self
                .execution_counters
                .draft_scratch_max_len
                .max(self.drafts.len());
            self.execution_counters
                .scc_execution_drafts_visible_barriers += 1;
            #[cfg(test)]
            if let Some(observer) = self.ordering_observer.as_mut() {
                observer
                    .record(|| ExecutionEvent::DraftsVisible(component.clone(), self.drafts.len()));
            }
            for (ordinal, member) in members.iter().enumerate() {
                self.execution_counters.scc_execution_draft_lookups += 1;
                self.execution_counters.scc_execution_finalized_members += 1;
                self.execution_counters.scc_execution_installed_members += 1;
                let draft = self
                    .drafts
                    .get(ordinal)
                    .copied()
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
                .scc_component_incoming_uses(component)
                .expect("plan-owned component");
            for use_index in 0..incoming_uses.len() {
                let id = &incoming_uses[use_index];
                #[cfg(test)]
                if let Some(observer) = self.ordering_observer.as_mut() {
                    // The scale observer has capacity zero.  Do not perform a
                    // test-only batch lookup, scheme read, or event build for
                    // an omitted event: production route probes are I + X.
                    if observer.has_capacity() {
                        let use_record = self.batch.definition_use(id).expect("plan-owned use");
                        let position = use_record.target.ordinal() as usize;
                        let kind = match self.schemes[position]
                            .expect("incoming observes finalized component scheme")
                            .body()
                        {
                            ClosedPositiveValue::Int => ObservedIncomingKind::Int,
                            ClosedPositiveValue::Bottom => ObservedIncomingKind::BottomTrivial,
                        };
                        observer.record(|| ExecutionEvent::IncomingUse(id.clone(), kind));
                    } else {
                        observer.omit();
                    }
                }
                let transitions = Self::route_incoming(
                    &self.batch,
                    &mut self.store,
                    &mut self.bounds,
                    &mut self.bound_payload_bytes,
                    &mut self.constraint_pairs,
                    &mut self.frontier,
                    &mut self.routed_uses,
                    &mut self.routed_use_positions,
                    &self.schemes,
                    &mut self.execution_counters,
                    id,
                )?;
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

    fn route_internal(
        batch: &ConstraintBatch,
        store: &mut ConstraintStore,
        bounds: &mut [VariableBounds],
        bound_payload_bytes: &mut usize,
        constraint_pairs: &mut HashSet<CanonicalValuePairKey>,
        frontier: &mut DirectBoundFrontier,
        routed_uses: &mut Vec<RoutedUseProvenance>,
        routed_use_positions: &mut HashSet<DefinitionUseId>,
        counters: &mut ProductionCounters,
        id: &DefinitionUseId,
    ) -> Result<usize, SolveAvailabilityError> {
        let use_record = Self::validated_route_use(batch, id)?;
        let root = batch.components[use_record.target_root_component].clone();
        let value = batch.components[use_record.use_value_component].clone();
        Self::route(
            store,
            bounds,
            bound_payload_bytes,
            constraint_pairs,
            frontier,
            routed_uses,
            routed_use_positions,
            counters,
            id,
            use_record,
            Term::Component(root),
            Term::Component(value),
            CanonicalValuePairKey {
                lower: ValueEndpointKey::ValueRow(use_record.target_root_row),
                upper: ValueEndpointKey::ValueRow(use_record.use_value_row),
            },
            RoutedUseKind::Internal,
        )
    }

    fn route_incoming(
        batch: &ConstraintBatch,
        store: &mut ConstraintStore,
        bounds: &mut [VariableBounds],
        bound_payload_bytes: &mut usize,
        constraint_pairs: &mut HashSet<CanonicalValuePairKey>,
        frontier: &mut DirectBoundFrontier,
        routed_uses: &mut Vec<RoutedUseProvenance>,
        routed_use_positions: &mut HashSet<DefinitionUseId>,
        schemes: &[Option<ClosedValueScheme>],
        counters: &mut ProductionCounters,
        id: &DefinitionUseId,
    ) -> Result<usize, SolveAvailabilityError> {
        let use_record = Self::validated_route_use(batch, id)?;
        let position = use_record.target.ordinal() as usize;
        let scheme = schemes[position].expect("incoming observes finalized component scheme");
        let value = batch.components[use_record.use_value_component].clone();
        match scheme.body() {
            ClosedPositiveValue::Bottom => {
                counters.scc_execution_bottom_trivial_instantiations += 1;
                assert!(
                    routed_use_positions.insert(id.clone()),
                    "each use routes once"
                );
                let old_capacity = routed_uses.capacity();
                routed_uses.push(RoutedUseProvenance {
                    use_id: id.clone(),
                    fact: None,
                    kind: RoutedUseKind::IncomingBottomTrivial,
                });
                if routed_uses.capacity() != old_capacity {
                    counters.routed_use_provenance_growths += 1;
                }
                Ok(0)
            }
            ClosedPositiveValue::Int => {
                counters.scc_execution_int_instantiation_facts += 1;
                Self::route(
                    store,
                    bounds,
                    bound_payload_bytes,
                    constraint_pairs,
                    frontier,
                    routed_uses,
                    routed_use_positions,
                    counters,
                    id,
                    use_record,
                    Term::Leaf(Leaf::IntPositive),
                    Term::Component(value),
                    CanonicalValuePairKey {
                        lower: ValueEndpointKey::IntPositive,
                        upper: ValueEndpointKey::ValueRow(use_record.use_value_row),
                    },
                    RoutedUseKind::IncomingInt,
                )
            }
        }
    }

    fn route(
        store: &mut ConstraintStore,
        bounds: &mut [VariableBounds],
        bound_payload_bytes: &mut usize,
        constraint_pairs: &mut HashSet<CanonicalValuePairKey>,
        frontier: &mut DirectBoundFrontier,
        routed_uses: &mut Vec<RoutedUseProvenance>,
        routed_use_positions: &mut HashSet<DefinitionUseId>,
        counters: &mut ProductionCounters,
        id: &DefinitionUseId,
        use_record: &DefinitionUse,
        lower: Term,
        upper: Term,
        key: CanonicalValuePairKey,
        kind: RoutedUseKind,
    ) -> Result<usize, SolveAvailabilityError> {
        assert!(
            routed_use_positions.insert(id.clone()),
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
            let mut transaction = store.transaction();
            transaction.admit(&occurrence)
        }
        .map_err(SolveAvailabilityError::from)?;
        let fact = receipt.fact();
        store
            .record_provenance(receipt)
            .map_err(SolveAvailabilityError::from)?;
        let transitions = Self::constrain(
            bounds,
            bound_payload_bytes,
            constraint_pairs,
            frontier,
            counters,
            key,
        );
        let old_capacity = routed_uses.capacity();
        routed_uses.push(RoutedUseProvenance {
            use_id: id.clone(),
            fact: Some(fact),
            kind,
        });
        if routed_uses.capacity() != old_capacity {
            counters.routed_use_provenance_growths += 1;
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

    fn generalize(
        batch: &ConstraintBatch,
        bounds: &[VariableBounds],
        definition: &DefinitionOrderId,
        #[cfg(test)] summary_reads: &mut usize,
    ) -> ClosedValueScheme {
        let verified = Self::verified_scheme_definition(batch, definition);
        let row = verified.record.root_value_row as usize;
        #[cfg(test)]
        {
            *summary_reads += 1;
        }
        let body = if bounds[row].has_int_positive_lower {
            ClosedPositiveValue::Int
        } else {
            ClosedPositiveValue::Bottom
        };
        ClosedValueScheme::new(body)
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

    fn finish(mut self) -> SolvedModule {
        let mut projections = HashMap::with_capacity(self.batch.projection_order.len());
        let mut work = ProductionCounters::default();
        for (index, occurrence) in self.batch.projection_order.iter().enumerate() {
            work.finish_projection_visits += 1;
            let exact = self.occurrence_exact_bounds[index];
            let value = if exact.value_lower_int && exact.value_upper_int {
                SolvedValue::Int
            } else {
                SolvedValue::Unknown
            };
            let effect = if exact.effect_lower_bottom && exact.effect_upper_empty {
                SolvedEffect::Empty
            } else {
                SolvedEffect::Unknown
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
        // The allocated finish output remains live until it moves into the
        // result below. Sample that actual coexistence before ownership
        // transfer; final retained accounting must not alias this peak.
        self.sample_f4_resources_with_finish_output(
            ResourceBoundary::FinishOutput,
            work.solved_projection_retained_bytes,
        );
        let mut counters = self.batch.counters();
        counters.combine(self.store.counters());
        counters.combine(&work);
        counters.combine(&self.execution_counters);
        SolvedModule {
            hir: self.batch.hir,
            projection_order: self.batch.projection_order,
            projections,
            root_scheme_positions: self.batch.root_definition_positions,
            root_scheme_identity_payload_bytes: self.batch.root_scheme_identity_payload_bytes,
            schemes: self.schemes,
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
        }
    }
}
impl SolvedModule {
    pub fn solve(batch: ConstraintBatch) -> Result<Self, SolveAvailabilityError> {
        InferenceSession::new(batch).run()
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
        match self
            .schemes
            .get(position)
            .copied()
            .flatten()
            .expect("every admitted root has a finalized scheme")
            .body()
        {
            ClosedPositiveValue::Int => Ok(SolvedValue::Int),
            ClosedPositiveValue::Bottom => Ok(SolvedValue::Never),
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
        let classes = std::mem::take(&mut batch.frozen_constraint_classes);
        let rows = std::mem::take(&mut batch.frozen_occurrence_bound_rows);
        for ((occurrence, class), row) in occurrences.into_iter().zip(classes).zip(rows) {
            if keep(&occurrence) {
                batch.occurrences.push(occurrence);
                batch.frozen_constraint_classes.push(class);
                batch.frozen_occurrence_bound_rows.push(row);
            }
        }
    }
    fn root(module: &HirModule, index: usize) -> &ResolvedExpr {
        match &module.items()[index] {
            HirItem::Expression(value) => value,
            _ => panic!("root expression"),
        }
    }
    fn shape(item: &ConstraintOccurrence) -> (Option<Leaf>, Option<Leaf>) {
        let leaf = |term: &Term| {
            if let Term::Leaf(leaf) = term {
                Some(*leaf)
            } else {
                None
            }
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
            batch.emit(
                binding.value().occurrence().clone(),
                127,
                Term::Leaf(Leaf::IntPositive),
                Term::Component(root),
            );
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
        constraint_pair_duplicates: usize,
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
        assert_eq!(counters.constraint_pair_admissions(), fourfold);
        assert_eq!(counters.constraint_pair_duplicates(), 1);
        assert_eq!(counters.lower_bound_insertions(), fourfold);
        assert_eq!(counters.upper_bound_insertions(), twice);
        assert_eq!(counters.lower_bound_replays(), twice);
        assert_eq!(counters.upper_bound_replays(), 0);
        assert_eq!(counters.scheme_table_len(), n);
        assert_eq!(counters.scheme_root_query_probes(), n);
        assert_eq!(counters.draft_scratch_max_len(), n);
        assert_eq!(counters.routed_use_provenance_len(), n);
        assert_eq!(counters.occurrence_bound_state_len(), twice);
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
        // The synthetic fixture owns this one ordinal index.  Later edge and
        // seed construction reads it in O(1), never by a per-edge scan of the
        // source-sized projection order.
        let occurrence_bound_rows = batch
            .projection_order
            .iter()
            .enumerate()
            .map(|(row, occurrence)| {
                (
                    occurrence.clone(),
                    u32::try_from(row).expect("synthetic occurrence row fits u32"),
                )
            })
            .collect::<HashMap<_, _>>();
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
            let occurrence_bound_row = *occurrence_bound_rows
                .get(occurrence)
                .expect("synthetic occurrence is in the owned ordinal index");
            batch
                .emit_resolved_binding_name(occurrence.clone(), parent_root, occurrence_bound_row)
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
                use_value_row: batch
                    .occurrence_component_positions
                    .get(occurrence)
                    .expect("synthetic occurrence has a value row")
                    .value_bound_row,
                parent_root_row: batch
                    .root_component_positions
                    .get(&batch.definitions[parent].root)
                    .expect("synthetic parent has a value row")
                    .value_bound_row,
                target_root_row: batch
                    .root_component_positions
                    .get(&batch.definitions[target].root)
                    .expect("synthetic target has a value row")
                    .value_bound_row,
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
            let occurrence_bound_row = *occurrence_bound_rows
                .get(&occurrence)
                .expect("synthetic seed occurrence is in the owned ordinal index");
            let root_row = batch
                .root_component_positions
                .get(binding.definition_root())
                .expect("synthetic seed root has a value row")
                .value_bound_row;
            let id = ConstraintOccurrenceId::new(occurrence, 127);
            batch.occurrences.push(ConstraintOccurrence {
                cause: CauseId::for_occurrence(id.clone()),
                id,
                lower: Term::Leaf(Leaf::IntPositive),
                upper: Term::Component(root),
            });
            batch
                .frozen_constraint_classes
                .push(FrozenConstraintClass::Value(CanonicalValuePairKey {
                    lower: ValueEndpointKey::IntPositive,
                    upper: ValueEndpointKey::ValueRow(root_row),
                }));
            batch
                .frozen_occurrence_bound_rows
                .push(occurrence_bound_row);
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
                    1, // finish output ownership transfer
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
                7 + usize::from(witness.internal_uses != 0)
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
                witness.constraint_pair_admissions,
                "{} has the fixture-defined accepted direct/exact pair count",
                witness.name
            );
            assert_eq!(
                counters.constraint_pair_duplicates(),
                witness.constraint_pair_duplicates,
                "{} has the fixture-defined duplicate direct/frontier pair count",
                witness.name
            );
            assert_eq!(
                counters.constraint_pair_admissions() + counters.constraint_pair_duplicates(),
                pair_probe_inputs
                    + witness.transmission_attempts
                    + witness.same_row_atom_intersections,
                "{} counts every input, transmission, and intersection probe exactly once",
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
        let _ = InferenceSession::generalize(&batch, &[], &definition, &mut summary_reads);
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
        let result = InferenceSession::route_internal(
            &session.batch,
            &mut session.store,
            &mut session.bounds,
            &mut session.bound_payload_bytes,
            &mut session.constraint_pairs,
            &mut session.frontier,
            &mut session.routed_uses,
            &mut session.routed_use_positions,
            &mut session.execution_counters,
            &internal_id,
        );
        assert_eq!(result, Err(SolveAvailabilityError::CauseMismatch));
        assert!(session.store.facts().is_empty());
        assert!(session.store.provenance().is_empty());
        assert!(session.constraint_pairs.is_empty());
        assert!(session.frontier.queue.is_empty());
        assert!(session.routed_uses.is_empty());
        assert!(session.routed_use_positions.is_empty());

        for scheme in [ClosedPositiveValue::Int, ClosedPositiveValue::Bottom] {
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
            session.schemes[0] = Some(ClosedValueScheme::new(scheme));
            let result = InferenceSession::route_incoming(
                &session.batch,
                &mut session.store,
                &mut session.bounds,
                &mut session.bound_payload_bytes,
                &mut session.constraint_pairs,
                &mut session.frontier,
                &mut session.routed_uses,
                &mut session.routed_use_positions,
                &session.schemes,
                &mut session.execution_counters,
                &route_id,
            );
            assert_eq!(result, Err(SolveAvailabilityError::CauseMismatch));
            assert!(session.store.facts().is_empty());
            assert!(session.store.provenance().is_empty());
            assert!(session.constraint_pairs.is_empty());
            assert!(session.frontier.queue.is_empty());
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
        let HirItem::Binding(foreign_binding) = &foreign_hir.items()[0] else {
            panic!("one foreign binding")
        };
        let foreign_occurrence = |mut batch: ConstraintBatch| {
            let local = batch.occurrences[0].clone();
            batch.occurrences[0] = ConstraintOccurrence {
                id: local.id.clone(),
                cause: local.cause.clone(),
                lower: Term::Component(ComponentId::DefinitionValue {
                    root: foreign_binding.definition_root().clone(),
                }),
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
        assert!(session.constraint_pairs.is_empty());
        assert!(session.frontier.queue.is_empty());
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
            batch.occurrences[0].lower = Term::Leaf(Leaf::EffectBottomPositive);
            batch
        };

        let mut session = InferenceSession::new(cross_kind_batch());
        session.admit_all_collected_facts().unwrap();
        assert!(session.store.facts().is_empty());
        assert!(session.store.provenance().is_empty());
        assert!(session.constraint_pairs.is_empty());
        assert!(session.frontier.queue.is_empty());
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
            constraint_pair_duplicates: 0,
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
                constraint_pair_duplicates: n / 4,
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
                constraint_pair_duplicates: n / 2,
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
            constraint_pair_duplicates: 1,
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
            constraint_pair_duplicates: n - 1,
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
            constraint_pair_duplicates: n - 1,
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
        rows: usize,
        inputs: &[CanonicalValuePairKey],
    ) -> (
        FrontierReferenceSnapshot,
        SummaryObservation,
        ProductionCounters,
    ) {
        let mut bounds = vec![VariableBounds::default(); rows];
        let mut bound_payload_bytes = 0;
        let mut pairs = HashSet::new();
        let mut frontier = DirectBoundFrontier::with_capacity(inputs.len());
        let mut counters = ProductionCounters::default();
        for &key in inputs {
            InferenceSession::constrain(
                &mut bounds,
                &mut bound_payload_bytes,
                &mut pairs,
                &mut frontier,
                &mut counters,
                key,
            );
        }
        assert!(frontier.queue.is_empty());
        let mut variable_reachability = HashSet::new();
        for row in 0..rows {
            let mut pending = VecDeque::from([row as u32]);
            let mut visited = HashSet::new();
            while let Some(current) = pending.pop_front() {
                if !visited.insert(current) {
                    continue;
                }
                for &upper in &bounds[current as usize].direct_upper_rows {
                    variable_reachability.insert(CanonicalValuePairKey {
                        lower: ValueEndpointKey::ValueRow(row as u32),
                        upper: ValueEndpointKey::ValueRow(upper),
                    });
                    pending.push_back(upper);
                }
            }
        }
        let snapshot = FrontierReferenceSnapshot {
            variable_reachability,
            exact_lowers: bounds
                .iter()
                .map(|row| row.exact_non_variable_lowers.iter().copied().collect())
                .collect(),
            exact_uppers: bounds
                .iter()
                .map(|row| row.exact_non_variable_uppers.iter().copied().collect())
                .collect(),
            terminal_pairs: pairs
                .iter()
                .copied()
                .filter(|key| {
                    !matches!(key.lower, ValueEndpointKey::ValueRow(_))
                        && !matches!(key.upper, ValueEndpointKey::ValueRow(_))
                })
                .collect(),
            int_lower_summary: bounds
                .iter()
                .map(|row| row.has_int_positive_lower)
                .collect(),
        };
        let observation = SummaryObservation {
            ordinary_initial_value_pair_probes: 0,
            synthetic_seed_value_pair_probes: 0,
            reads: 0,
            false_to_true_transitions: 0,
            frontier_pushes: frontier.pushes,
            frontier_pops: frontier.pops,
            frontier_maximum_live: frontier.maximum_live,
            frontier_capacity: frontier.queue.capacity(),
            frontier_capacity_growths: frontier.capacity_growths,
            frontier_retained_bytes: checked_capacity_bytes::<CanonicalValuePairKey>(
                frontier.queue.capacity(),
                "F4 reference frontier queue",
            ),
            frontier_peak_bytes: frontier.peak_bytes,
            direct_edges: frontier.direct_edges,
            exact_lower_memberships: frontier.exact_lower_memberships,
            exact_upper_memberships: frontier.exact_upper_memberships,
            transmission_attempts: frontier.transmission_attempts,
            same_row_atom_intersections: frontier.same_row_atom_intersections,
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
        (snapshot, observation, counters)
    }

    #[test]
    fn f4_direct_frontier_exhaustively_matches_reference_for_zero_to_three_rows() {
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
                                direct_frontier_snapshot(rows, &inputs);
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
        let lower = CanonicalValuePairKey {
            lower: ValueEndpointKey::IntPositive,
            upper: ValueEndpointKey::ValueRow(0),
        };
        let upper = CanonicalValuePairKey {
            lower: ValueEndpointKey::ValueRow(0),
            upper: ValueEndpointKey::IntNegative,
        };
        for inputs in [[lower, upper], [upper, lower]] {
            let (snapshot, observation, counters) = direct_frontier_snapshot(1, &inputs);
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
        let (snapshot, observation, counters) = direct_frontier_snapshot(3, &inputs);
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
                    shape(item)
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
                        shape(item),
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
                .map(|item| (item.id().local_slot(), shape(item)))
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
        assert_eq!(fifth.lower(), &Term::Component(body.value().clone()));
        assert_eq!(fifth.upper(), &Term::Component(root));
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
                    use_value_row: 0,
                    parent_root_row: 0,
                    target_root_row: 0,
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
            lower: Term::Component(ComponentId::DefinitionValue {
                root: second_binding.definition_root().clone(),
            }),
            upper: local.upper.clone(),
        };
        assert!(matches!(
            ConstraintStore::new(first.clone())
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
            ConstraintStore::new(first.clone())
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
        let mut store = ConstraintStore::new(first.clone());
        let r1 = store.transaction().admit(&first_item).unwrap();
        let r2 = store.transaction().admit(&duplicate).unwrap();
        assert_eq!(r1.fact(), r2.fact());
        assert_eq!(r1.delta(), AdmissionDelta::Accepted);
        assert_eq!(r2.delta(), AdmissionDelta::Duplicate);
        store.record_provenance(r1).unwrap();
        store.record_provenance(r2).unwrap();
        assert_ne!(store.provenance()[0].cause(), store.provenance()[1].cause());
        let receipt = store.transaction().admit(&first_item).unwrap();
        let mut alien_store = ConstraintStore::new(first.clone());
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
            lower: Term::Leaf(Leaf::EffectBottomPositive),
            upper: failure.occurrences[0].upper.clone(),
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
}
