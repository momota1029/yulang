//! Ordered directed-subtyping collection and deterministic reference solving.

use std::{
    collections::{HashMap, HashSet, hash_map::Entry},
    hash::{Hash, Hasher},
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

use yu_hir::{
    DefId, DefinitionRootId, HirItem, HirModule, HirOccurrenceId, NameResolution, ResolvedExpr,
};
use yu_types::{ComponentKind, Leaf};

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
    components: Vec<ComponentId>,
    occurrence_component_positions: HashMap<HirOccurrenceId, ComponentPositions>,
    root_component_positions: HashMap<DefinitionRootId, usize>,
    occurrences: Vec<ConstraintOccurrence>,
    counters: ProductionCounters,
    definition_query_probes: Arc<AtomicUsize>,
    definition_use_query_probes: Arc<AtomicUsize>,
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
            components: Vec::new(),
            occurrence_component_positions: HashMap::new(),
            root_component_positions: HashMap::new(),
            occurrences: Vec::new(),
            definition_query_probes: Arc::new(AtomicUsize::new(0)),
            definition_use_query_probes: Arc::new(AtomicUsize::new(0)),
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
                ResolvedExpr::Name {
                    occurrence,
                    resolution: NameResolution::Resolved(target),
                    ..
                },
            ) = (definition.as_ref(), expression)
            {
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
            let position = batch.definition_uses.len();
            batch.definition_uses.push(DefinitionUse {
                cause: DefinitionUseCause::for_use(id.clone()),
                id: id.clone(),
                parent,
                target,
                occurrence: pending.occurrence.clone(),
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
        batch.counters.occurrence_retained_bytes =
            batch.projection_order.capacity() * std::mem::size_of::<HirOccurrenceId>();
        batch.counters.component_retained_bytes =
            batch.components.capacity() * std::mem::size_of::<ComponentId>();
        batch.counters.occurrence_record_retained_bytes =
            batch.occurrences.capacity() * std::mem::size_of::<ConstraintOccurrence>();
        batch.counters.root_retained_bytes =
            batch.root_order.capacity() * std::mem::size_of::<DefinitionRootId>();
        batch.counters.occurrence_component_index_capacity =
            batch.occurrence_component_positions.capacity();
        batch.counters.occurrence_component_index_retained_bytes =
            batch.occurrence_component_positions.capacity()
                * std::mem::size_of::<(HirOccurrenceId, ComponentPositions)>();
        batch.counters.root_component_index_capacity = batch.root_component_positions.capacity();
        batch.counters.root_component_index_retained_bytes =
            batch.root_component_positions.capacity()
                * std::mem::size_of::<(DefinitionRootId, usize)>();
        batch.counters.index_capacity = batch.occurrence_component_positions.capacity()
            + batch.root_component_positions.capacity();
        batch.counters.definition_record_index_capacity = batch.definition_positions.capacity();
        batch.counters.definition_record_index_retained_bytes =
            batch.definition_positions.capacity()
                * std::mem::size_of::<(DefinitionOrderId, usize)>();
        batch.counters.definition_record_retained_bytes =
            batch.definitions.capacity() * std::mem::size_of::<CollectedDefinition>();
        batch.counters.definition_use_retained_bytes =
            batch.definition_uses.capacity() * std::mem::size_of::<DefinitionUse>();
        batch.counters.definition_use_index_capacity = batch.definition_use_positions.capacity();
        batch.counters.definition_use_index_retained_bytes =
            batch.definition_use_positions.capacity()
                * std::mem::size_of::<(DefinitionUseId, usize)>();
        batch
            .finish_collection_accounting(definition_by_hir_id.capacity(), pending_uses.capacity());
        drop(pending_uses);
        drop(definition_by_hir_id);
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
    pub fn counters(&self) -> ProductionCounters {
        let mut counters = self.counters.clone();
        counters.definition_query_probes = self.definition_query_probes.load(Ordering::Relaxed);
        counters.definition_use_query_probes =
            self.definition_use_query_probes.load(Ordering::Relaxed);
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
        Ok(self.components[position].clone())
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
        let value = self.definition_value_component(root.clone());
        let old_capacity = self.root_component_positions.capacity();
        self.root_component_positions
            .insert(root, self.components.len() - 1);
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
        let value = self.occurrence_component(occurrence.clone(), ComponentKind::Value);
        let effect = self.occurrence_component(occurrence.clone(), ComponentKind::Effect);
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
        let id = ConstraintOccurrenceId::new(occurrence, local_slot);
        self.occurrences.push(ConstraintOccurrence {
            cause: CauseId::for_occurrence(id.clone()),
            id,
            lower,
            upper,
        });
        self.counters.emitted_facts += 1;
        self.counters.generated_work_items += 1;
    }
    fn component_position(
        &self,
        component: &ComponentId,
        work: &mut ProductionCounters,
    ) -> Option<usize> {
        match component {
            ComponentId::Occurrence { occurrence, kind } => {
                work.occurrence_component_index_probes += 1;
                let positions = self.occurrence_component_positions.get(occurrence)?;
                Some(match kind {
                    ComponentKind::Value => positions.value,
                    ComponentKind::Effect => positions.effect,
                })
            }
            ComponentId::DefinitionValue { root } => {
                work.root_component_index_probes += 1;
                self.root_component_positions.get(root).copied()
            }
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
    fn root_value_component_for_collect(
        &mut self,
        root: &DefinitionRootId,
    ) -> Result<ComponentId, CollectionAvailabilityError> {
        self.counters.root_component_index_probes += 1;
        let position = *self
            .root_component_positions
            .get(root)
            .ok_or(CollectionAvailabilityError::NonTotalDefinitionMap)?;
        self.components
            .get(position)
            .cloned()
            .ok_or(CollectionAvailabilityError::NonTotalDefinitionMap)
    }
    fn ensure_total_definition_maps(
        &self,
        definition_by_hir_id: &HashMap<&DefId, DefinitionOrderId>,
    ) -> Result<(), CollectionAvailabilityError> {
        (self.definitions.len() == self.definition_positions.len()
            && self.definitions.len() == definition_by_hir_id.len())
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
            definition_endpoint_index_capacity * std::mem::size_of::<(&DefId, DefinitionOrderId)>();
        self.counters.definition_use_endpoint_workspace_peak_bytes =
            pending_endpoint_capacity * std::mem::size_of::<PendingDefinitionUse<'_>>();
        self.counters.f0_collection_retained_bytes = self.counters.occurrence_retained_bytes
            + self.counters.root_retained_bytes
            + self.counters.definition_record_retained_bytes
            + self.counters.definition_record_index_retained_bytes
            + self.counters.definition_use_retained_bytes
            + self.counters.definition_use_index_retained_bytes
            + self.counters.component_retained_bytes
            + self.counters.occurrence_component_index_retained_bytes
            + self.counters.root_component_index_retained_bytes
            + self.counters.occurrence_record_retained_bytes;
        self.counters.f0_collection_peak_bytes = self.counters.f0_collection_retained_bytes
            + self.counters.definition_endpoint_index_peak_bytes
            + self.counters.definition_use_endpoint_workspace_peak_bytes;
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
    retained_definition_uses: usize,
    definition_record_index_capacity: usize,
    definition_record_index_retained_bytes: usize,
    definition_record_retained_bytes: usize,
    definition_use_retained_bytes: usize,
    definition_use_index_capacity: usize,
    definition_use_index_retained_bytes: usize,
    definition_query_probes: usize,
    definition_use_query_probes: usize,
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
    maximum_fan_out: usize,
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
        retained_definition_uses,
        definition_record_index_capacity,
        definition_record_index_retained_bytes,
        definition_record_retained_bytes,
        definition_use_retained_bytes,
        definition_use_index_capacity,
        definition_use_index_retained_bytes,
        definition_query_probes,
        definition_use_query_probes,
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
        maximum_fan_out,
        scc_count
    );
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
            retained_definition_uses,
            definition_record_index_capacity,
            definition_record_index_retained_bytes,
            definition_record_retained_bytes,
            definition_use_retained_bytes,
            definition_use_index_capacity,
            definition_use_index_retained_bytes,
            definition_query_probes,
            definition_use_query_probes,
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
            scc_count
        );
        self.maximum_fan_out = self.maximum_fan_out.max(other.maximum_fan_out);
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
}
impl ConstraintStore {
    pub fn new(hir: Arc<HirModule>) -> Self {
        Self {
            hir,
            receipt_token: Arc::new(StoreReceiptToken),
            next_receipt: 0,
            consumed_receipts: HashSet::new(),
            facts: Vec::new(),
            canonical: HashMap::new(),
            provenance: Vec::new(),
            comparisons: Arc::new(AtomicUsize::new(0)),
            counters: ProductionCounters::default(),
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
        self.counters.consumed_receipt_index_probes += 1;
        if !self.consumed_receipts.insert(receipt.serial) {
            return Err(ConstraintError::ReceiptConsumed);
        }
        self.provenance.push(ProvenanceEdge {
            cause: receipt.cause,
            fact: receipt.fact,
        });
        self.counters.provenance_edges += 1;
        self.counters.provenance_retained_bytes =
            self.provenance.capacity() * std::mem::size_of::<ProvenanceEdge>();
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
            self.facts.capacity() * std::mem::size_of::<SemanticFact>();
        self.counters.canonical_map_capacity = self.canonical.capacity();
        self.counters.canonical_map_retained_bytes =
            self.canonical.capacity() * std::mem::size_of::<(FactKey, FactId)>();
        self.counters.canonical_map_probes = self.comparisons.load(Ordering::Relaxed);
        self.counters.consumed_receipt_index_capacity = self.consumed_receipts.capacity();
        self.counters.consumed_receipt_index_retained_bytes =
            self.consumed_receipts.capacity() * std::mem::size_of::<u64>();
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
            self.store.facts.push(SemanticFact {
                id: fact,
                lower: occurrence.lower.clone(),
                upper: occurrence.upper.clone(),
            });
            let old_capacity = self.store.canonical.capacity();
            self.store.canonical.insert(key, fact);
            if self.store.canonical.capacity() != old_capacity {
                self.store.counters.canonical_map_rebuilds += 1;
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
#[derive(Clone, Copy, Default)]
struct Bounds {
    int_lower: bool,
    int_upper: bool,
    effect_lower: bool,
    effect_upper: bool,
}

/// A total artifact-bound frozen solve result. Local relation errors do not
/// prevent later independent components from solving.
#[derive(Debug)]
pub struct SolvedModule {
    hir: Arc<HirModule>,
    projection_order: Vec<HirOccurrenceId>,
    projections: HashMap<HirOccurrenceId, SolvedProjection>,
    root_values: HashMap<DefinitionRootId, SolvedValue>,
    errors: Vec<SolverError>,
    store: ConstraintStore,
    counters: ProductionCounters,
    solved_root_query_probes: AtomicUsize,
}
impl SolvedModule {
    pub fn solve(batch: ConstraintBatch) -> Result<Self, SolveAvailabilityError> {
        let mut store = ConstraintStore::new(batch.hir.clone());
        let mut errors = Vec::new();
        let mut failed_components = HashSet::new();
        for occurrence in batch.occurrences() {
            let result = {
                let mut transaction = store.transaction();
                transaction.admit(occurrence)
            };
            match result {
                Ok(receipt) => store
                    .record_provenance(receipt)
                    .map_err(SolveAvailabilityError::from)?,
                Err(ConstraintError::CrossKind { lower, upper }) => {
                    errors.push(SolverError {
                        occurrence: occurrence.id.clone(),
                        cause: occurrence.cause.clone(),
                        kind: SolverErrorKind::CrossKind { lower, upper },
                    });
                    for term in [&occurrence.lower, &occurrence.upper] {
                        if let Term::Component(component) = term {
                            failed_components.insert(component.clone());
                        }
                    }
                }
                Err(error) => return Err(error.into()),
            }
        }
        store.finish_accounting();
        let mut projections = HashMap::with_capacity(batch.projection_order.len());
        for occurrence in &batch.projection_order {
            projections.insert(
                occurrence.clone(),
                SolvedProjection {
                    value: SolvedValue::Unknown,
                    effect: SolvedEffect::Unknown,
                },
            );
        }
        let mut root_values = HashMap::with_capacity(batch.root_order.len());
        for root in &batch.root_order {
            root_values.insert(root.clone(), SolvedValue::Unknown);
        }
        let mut bounds = vec![Bounds::default(); batch.components.len()];
        let mut fanout = HashMap::<Term, usize>::new();
        let mut work = ProductionCounters::default();
        for fact in store.facts() {
            for endpoint in [fact.lower(), fact.upper()] {
                let old_capacity = fanout.capacity();
                *fanout.entry(endpoint.clone()).or_default() += 1;
                if fanout.capacity() != old_capacity {
                    work.index_rebuilds += 1;
                }
                work.adjacency_appends += 1;
                work.adjacency_visits += 1;
            }
            match (fact.lower(), fact.upper()) {
                (Term::Leaf(Leaf::IntPositive), Term::Component(component)) => {
                    if let Some(index) = batch.component_position(component, &mut work) {
                        bounds[index].int_lower = true;
                    }
                }
                (Term::Component(component), Term::Leaf(Leaf::IntNegative)) => {
                    if let Some(index) = batch.component_position(component, &mut work) {
                        bounds[index].int_upper = true;
                    }
                }
                (Term::Leaf(Leaf::EffectBottomPositive), Term::Component(component)) => {
                    if let Some(index) = batch.component_position(component, &mut work) {
                        bounds[index].effect_lower = true;
                    }
                }
                (Term::Component(component), Term::Leaf(Leaf::EmptyEffectNegative)) => {
                    if let Some(index) = batch.component_position(component, &mut work) {
                        bounds[index].effect_upper = true;
                    }
                }
                _ => {}
            }
        }
        work.index_capacity = fanout.capacity();
        work.solved_projection_retained_bytes =
            projections.capacity() * std::mem::size_of::<(HirOccurrenceId, SolvedProjection)>();
        work.solved_root_index_capacity = root_values.capacity();
        work.solved_root_index_retained_bytes =
            root_values.capacity() * std::mem::size_of::<(DefinitionRootId, SolvedValue)>();
        work.bounds_workspace_capacity = bounds.capacity();
        work.bounds_workspace_retained_bytes = bounds.capacity() * std::mem::size_of::<Bounds>();
        work.fanout_index_capacity = fanout.capacity();
        work.fanout_index_retained_bytes = fanout.capacity() * std::mem::size_of::<(Term, usize)>();
        work.failed_component_workspace_capacity = failed_components.capacity();
        work.failed_component_workspace_retained_bytes =
            failed_components.capacity() * std::mem::size_of::<ComponentId>();
        work.solver_error_workspace_capacity = errors.capacity();
        work.solver_error_workspace_retained_bytes =
            errors.capacity() * std::mem::size_of::<SolverError>();
        work.solver_workspace_retained_bytes = bounds.capacity() * std::mem::size_of::<Bounds>()
            + fanout.capacity() * std::mem::size_of::<(Term, usize)>()
            + failed_components.capacity() * std::mem::size_of::<ComponentId>()
            + errors.capacity() * std::mem::size_of::<SolverError>();
        for count in fanout.values() {
            work.maximum_fan_out = work.maximum_fan_out.max(*count);
        }
        for (index, component) in batch.components.iter().enumerate() {
            if failed_components.contains(component) {
                continue;
            }
            let Some(occurrence) = component.occurrence() else {
                continue;
            };
            let projection = projections
                .get_mut(occurrence)
                .expect("batch owns component");
            match component.kind() {
                ComponentKind::Value if bounds[index].int_lower && bounds[index].int_upper => {
                    projection.value = SolvedValue::Int
                }
                ComponentKind::Effect
                    if bounds[index].effect_lower && bounds[index].effect_upper =>
                {
                    projection.effect = SolvedEffect::Empty
                }
                _ => {}
            }
        }
        let mut counters = batch.counters();
        counters.combine(store.counters());
        counters.combine(&work);
        Ok(Self {
            hir: batch.hir,
            projection_order: batch.projection_order,
            projections,
            root_values,
            errors,
            store,
            counters,
            solved_root_query_probes: AtomicUsize::new(0),
        })
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
        Ok(*self
            .root_values
            .get(root)
            .expect("every admitted root has a solved projection"))
    }
}

#[cfg(test)]
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
    fn binding_bodies_attach_only_to_unknown_definition_roots() {
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
            SolvedValue::Unknown
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
                (0..0, CollectedBodyStatus::Complete),
                (0..5, CollectedBodyStatus::Complete),
                (5..5, CollectedBodyStatus::Complete),
                (5..5, CollectedBodyStatus::Error),
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
            assert_eq!(
                solved.root_value_for(binding.definition_root()).unwrap(),
                SolvedValue::Unknown
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
        batch.occurrences.retain(|item| item.id.local_slot != 1);
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
        batch.occurrences.retain(|item| item.id.local_slot != 3);
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
            "my x = 1; my x = 2; my broken = @; my named = x; my good = 42",
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
        let solved = SolvedModule::solve(batch).unwrap();
        assert_eq!(solved.root_values.len(), bindings.len());
        for binding in &bindings {
            assert_eq!(
                solved.root_value_for(binding.definition_root()).unwrap(),
                SolvedValue::Unknown
            );
        }
        assert_eq!(
            solved
                .projection_for(bindings[4].value().occurrence())
                .unwrap()
                .value(),
            SolvedValue::Int
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
            assert_eq!(c.adjacency_appends(), 8 * n);
            assert_eq!(c.adjacency_visits(), 8 * n);
            assert_eq!(c.maximum_fan_out(), n);
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
            assert_eq!(c.adjacency_appends(), 10 * n);
            assert_eq!(c.adjacency_visits(), 10 * n);
            assert_eq!(c.maximum_fan_out(), n);
            assert_eq!(c.duplicate_facts(), 0);
            assert_eq!(c.cst_traversals(), 0);
            assert_eq!(c.cst_rescans(), 0);
            assert_eq!(c.hir_clone_count(), 0);
            assert_eq!(c.typed_tree_copies(), 0);
            assert_eq!(c.copied_spelling_bytes(), 0);
            assert_eq!(c.definition_root_def_id_clone_bytes(), 0);
            assert_eq!(c.eager_explanation_builds(), 0);
            assert_eq!(c.scc_count(), 0);
        }
        for solved in [&a, &b] {
            for item in solved.hir().items() {
                if let HirItem::Binding(binding) = item {
                    assert_eq!(
                        solved.root_value_for(binding.definition_root()).unwrap(),
                        SolvedValue::Unknown
                    );
                }
            }
        }
        assert_eq!(a.counters().solved_root_query_probes(), 1000);
        assert_eq!(b.counters().solved_root_query_probes(), 2000);
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
        ] {
            assert!(large < small.saturating_mul(5) / 2 + 1);
        }
    }
}
