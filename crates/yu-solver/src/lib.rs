//! Ordered directed-subtyping collection and deterministic reference solving.

use std::{
    collections::{HashMap, HashSet},
    hash::{Hash, Hasher},
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

use yu_hir::{HirItem, HirModule, HirOccurrenceId, ResolvedExpr};
use yu_types::{ComponentKind, Leaf};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ComponentId {
    occurrence: HirOccurrenceId,
    kind: ComponentKind,
}
impl ComponentId {
    pub fn occurrence(&self) -> &HirOccurrenceId {
        &self.occurrence
    }
    pub const fn kind(&self) -> ComponentKind {
        self.kind
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
            Self::Component(component) => component.kind,
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
    projection_order: Vec<HirOccurrenceId>,
    components: Vec<ComponentId>,
    component_positions: HashMap<HirOccurrenceId, ComponentPositions>,
    occurrences: Vec<ConstraintOccurrence>,
    counters: ProductionCounters,
}
impl ConstraintBatch {
    pub fn collect(hir: Arc<HirModule>) -> Self {
        let mut batch = Self {
            hir,
            projection_order: Vec::new(),
            components: Vec::new(),
            component_positions: HashMap::new(),
            occurrences: Vec::new(),
            counters: ProductionCounters {
                hir_traversals: 1,
                ..ProductionCounters::default()
            },
        };
        let hir = batch.hir.clone();
        for item in hir.items() {
            let expression = match item {
                HirItem::Expression(expression) => expression,
                HirItem::Binding(binding) => binding.value(),
                HirItem::Error { .. } => continue,
            };
            batch.projection_order.push(expression.occurrence().clone());
            batch.counters.occurrence_allocations += 1;
            if matches!(item, HirItem::Expression(ResolvedExpr::Integer { .. })) {
                batch.emit_integer(expression.occurrence().clone());
            }
        }
        batch.counters.occurrence_retained_bytes =
            batch.projection_order.capacity() * std::mem::size_of::<HirOccurrenceId>();
        batch.counters.component_retained_bytes =
            batch.components.capacity() * std::mem::size_of::<ComponentId>();
        batch.counters.occurrence_record_retained_bytes =
            batch.occurrences.capacity() * std::mem::size_of::<ConstraintOccurrence>();
        batch.counters.index_capacity = batch.component_positions.capacity();
        batch
    }
    pub fn hir(&self) -> &Arc<HirModule> {
        &self.hir
    }
    pub fn occurrences(&self) -> &[ConstraintOccurrence] {
        &self.occurrences
    }
    pub fn counters(&self) -> &ProductionCounters {
        &self.counters
    }
    pub fn components_for(
        &self,
        occurrence: &HirOccurrenceId,
    ) -> Result<Option<Components>, ArtifactMismatch> {
        self.require_owned(occurrence)?;
        Ok(self
            .component_positions
            .get(occurrence)
            .map(|positions| Components {
                value: self.components[positions.value].clone(),
                effect: self.components[positions.effect].clone(),
            }))
    }
    fn emit_integer(&mut self, occurrence: HirOccurrenceId) {
        let value = self.component(occurrence.clone(), ComponentKind::Value);
        let effect = self.component(occurrence.clone(), ComponentKind::Effect);
        let positions = ComponentPositions {
            value: self.components.len() - 2,
            effect: self.components.len() - 1,
        };
        let old_capacity = self.component_positions.capacity();
        self.component_positions
            .insert(occurrence.clone(), positions);
        if self.component_positions.capacity() != old_capacity {
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
            Term::Component(value),
            Term::Leaf(Leaf::IntNegative),
        );
        self.emit(
            occurrence.clone(),
            2,
            Term::Leaf(Leaf::EffectBottomPositive),
            Term::Component(effect.clone()),
        );
        self.emit(
            occurrence,
            3,
            Term::Component(effect),
            Term::Leaf(Leaf::EmptyEffectNegative),
        );
    }
    fn component(&mut self, occurrence: HirOccurrenceId, kind: ComponentKind) -> ComponentId {
        let component = ComponentId { occurrence, kind };
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
    fn component_position(&self, component: &ComponentId) -> Option<usize> {
        let positions = self.component_positions.get(component.occurrence())?;
        Some(match component.kind() {
            ComponentKind::Value => positions.value,
            ComponentKind::Effect => positions.effect,
        })
    }
    fn require_owned(&self, occurrence: &HirOccurrenceId) -> Result<(), ArtifactMismatch> {
        self.hir
            .owns_occurrence(occurrence)
            .then_some(())
            .ok_or(ArtifactMismatch)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ArtifactMismatch;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ProductionCounters {
    hir_traversals: usize,
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
    index_rebuilds: usize,
    index_capacity: usize,
    provenance_edges: usize,
    provenance_retained_bytes: usize,
    solved_projection_retained_bytes: usize,
    solver_workspace_retained_bytes: usize,
    eager_explanation_builds: usize,
    maximum_fan_out: usize,
    scc_count: usize,
}
macro_rules! access { ($($field:ident),+ $(,)?) => {$(pub const fn $field(&self) -> usize { self.$field })+}; }
impl ProductionCounters {
    access!(
        hir_traversals,
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
        index_rebuilds,
        index_capacity,
        provenance_edges,
        provenance_retained_bytes,
        solved_projection_retained_bytes,
        solver_workspace_retained_bytes,
        eager_explanation_builds,
        maximum_fan_out,
        scc_count
    );
    fn combine(&mut self, other: &Self) {
        macro_rules! add { ($($field:ident),+) => {$(self.$field += other.$field;)+}; }
        add!(
            hir_traversals,
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
            index_rebuilds,
            index_capacity,
            provenance_edges,
            provenance_retained_bytes,
            solved_projection_retained_bytes,
            solver_workspace_retained_bytes,
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
    fn finish_accounting(&mut self) {
        self.counters.fact_retained_bytes =
            self.facts.capacity() * std::mem::size_of::<SemanticFact>();
        self.counters.canonical_map_capacity = self.canonical.capacity();
        self.counters.canonical_map_probes = self.comparisons.load(Ordering::Relaxed);
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
                self.store.require_owned(component.occurrence())?;
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
    errors: Vec<SolverError>,
    store: ConstraintStore,
    counters: ProductionCounters,
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
                    if let Some(index) = batch.component_position(component) {
                        bounds[index].int_lower = true;
                    }
                }
                (Term::Component(component), Term::Leaf(Leaf::IntNegative)) => {
                    if let Some(index) = batch.component_position(component) {
                        bounds[index].int_upper = true;
                    }
                }
                (Term::Leaf(Leaf::EffectBottomPositive), Term::Component(component)) => {
                    if let Some(index) = batch.component_position(component) {
                        bounds[index].effect_lower = true;
                    }
                }
                (Term::Component(component), Term::Leaf(Leaf::EmptyEffectNegative)) => {
                    if let Some(index) = batch.component_position(component) {
                        bounds[index].effect_upper = true;
                    }
                }
                _ => {}
            }
        }
        work.index_capacity = fanout.capacity();
        work.solved_projection_retained_bytes =
            projections.capacity() * std::mem::size_of::<(HirOccurrenceId, SolvedProjection)>();
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
            let projection = projections
                .get_mut(component.occurrence())
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
        let mut counters = batch.counters.clone();
        counters.combine(store.counters());
        counters.combine(&work);
        Ok(Self {
            hir: batch.hir,
            projection_order: batch.projection_order,
            projections,
            errors,
            store,
            counters,
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
    pub fn counters(&self) -> &ProductionCounters {
        &self.counters
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports, lower_module};
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    fn module(source: &str, path: &str) -> Arc<HirModule> {
        let source: Arc<SourceText> = Arc::from(source);
        let header = Arc::new(scan_header(source.clone()));
        Arc::new(
            lower_module(
                ModuleIdentity::source_root(FileId::new(FileKey::new("test", path))),
                &parse_file(source, header, Arc::new(SyntaxEnvironment::empty())),
                SemanticImports::empty(),
            )
            .unwrap(),
        )
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
        let batch = ConstraintBatch::collect(hir.clone());
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
        let ab = ConstraintBatch::collect(a.clone());
        let bb = ConstraintBatch::collect(b.clone());
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
        assert_eq!(order(&ab).len(), 8);
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
    fn bindings_names_errors_and_underconstrained_intervals_are_unknown() {
        let hir = module(
            "my resolved = 42; resolved; my dup = 0; my dup = 1; dup; missing; f 1; 42",
            "states.yu",
        );
        let batch = ConstraintBatch::collect(hir.clone());
        assert_eq!(batch.occurrences().len(), 4);
        assert!(
            batch
                .components_for(match &hir.items()[0] {
                    HirItem::Binding(binding) => binding.value().occurrence(),
                    _ => unreachable!(),
                })
                .unwrap()
                .is_none()
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
        for index in 0..7 {
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
        assert_eq!(
            solved
                .projection_for(root(&hir, 7).occurrence())
                .unwrap()
                .value(),
            SolvedValue::Int
        );
        let hir = module("42", "under.yu");
        let mut batch = ConstraintBatch::collect(hir.clone());
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
        let mut batch = ConstraintBatch::collect(hir.clone());
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
    fn brands_receipts_and_local_failure_are_isolated() {
        let first = module("42; 42", "first.yu");
        let second = module("42", "second.yu");
        let batch = ConstraintBatch::collect(first.clone());
        let other = ConstraintBatch::collect(second.clone());
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
        let mut failure = ConstraintBatch::collect(first.clone());
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
    fn n_and_2n_counters_remain_linear() {
        let source = |n| std::iter::repeat_n("42", n).collect::<Vec<_>>().join("; ");
        let a =
            SolvedModule::solve(ConstraintBatch::collect(module(&source(1000), "n.yu"))).unwrap();
        let b =
            SolvedModule::solve(ConstraintBatch::collect(module(&source(2000), "2n.yu"))).unwrap();
        for (n, solved) in [(1000, &a), (2000, &b)] {
            let c = solved.counters();
            assert_eq!(c.hir_traversals(), 1);
            assert_eq!(c.emitted_facts(), 4 * n);
            assert_eq!(c.admitted_facts(), 4 * n);
            assert_eq!(c.occurrence_allocations(), n);
            assert_eq!(c.component_allocations(), 2 * n);
            assert_eq!(c.fact_allocations(), 4 * n);
            assert_eq!(c.provenance_edges(), 4 * n);
            assert_eq!(c.generated_work_items(), 4 * n);
            assert_eq!(c.accepted_work_items(), 4 * n);
            assert_eq!(c.duplicate_work_items(), 0);
            assert_eq!(c.adjacency_appends(), 8 * n);
            assert_eq!(c.adjacency_visits(), 8 * n);
            assert_eq!(c.maximum_fan_out(), n);
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
            (y.component_retained_bytes(), x.component_retained_bytes()),
            (y.fact_retained_bytes(), x.fact_retained_bytes()),
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
            (y.canonical_map_capacity(), x.canonical_map_capacity()),
            (y.index_capacity(), x.index_capacity()),
            (y.canonical_map_rebuilds(), x.canonical_map_rebuilds()),
            (y.index_rebuilds(), x.index_rebuilds()),
        ] {
            assert!(large < small * 5 / 2 + 1);
        }
        assert!(y.canonical_map_probes() < x.canonical_map_probes().saturating_mul(5) / 2 + 1);
    }
}
