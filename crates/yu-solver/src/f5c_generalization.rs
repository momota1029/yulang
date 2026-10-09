use super::*;

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) struct ObservedWalkerSet<'meter, T> {
    // Rust drops fields in declaration order, so the allocation goes away
    // before its physical-owner release event is written.
    values: HashSet<T>,
    owner: Option<RawWalkerOwner<'meter>>,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<'meter, T: Eq + std::hash::Hash> ObservedWalkerSet<'meter, T> {
    fn new(meter: &'meter DraftHeapMeter, kind: F5cWalkerLaneKind) -> Self {
        Self { values: HashSet::new(),
            owner: Some(RawWalkerOwner::new(meter, kind as usize, kind.slot_size())) }
    }

    fn new_optional(meter: Option<&'meter DraftHeapMeter>, kind: F5cWalkerLaneKind) -> Self {
        Self { values: HashSet::new(),
            owner: meter.map(|meter| RawWalkerOwner::new(meter, kind as usize, kind.slot_size())) }
    }

    fn observe_capacity(&mut self, _requested: usize) {
        if let Some(owner) = self.owner.as_mut() {
            owner.observe(self.values.len(), self.values.capacity());
        }
    }

    fn insert(&mut self, value: T) -> bool {
        let inserted = self.values.insert(value);
        self.observe_capacity(0);
        inserted
    }

    fn clear(&mut self) {
        self.values.clear();
        self.observe_capacity(0);
    }

    fn retain(&mut self, f: impl FnMut(&T) -> bool) {
        self.values.retain(f);
        self.observe_capacity(0);
    }

}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<T> std::ops::Deref for ObservedWalkerSet<'_, T> {
    type Target = HashSet<T>;
    fn deref(&self) -> &Self::Target { &self.values }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<T> std::ops::DerefMut for ObservedWalkerSet<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.values }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<T: std::fmt::Debug> std::fmt::Debug for ObservedWalkerSet<'_, T> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.values.fmt(formatter)
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<T: Eq + std::hash::Hash> PartialEq<HashSet<T>> for ObservedWalkerSet<'_, T> {
    fn eq(&self, other: &HashSet<T>) -> bool { self.values == *other }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<T: Eq + std::hash::Hash> PartialEq<ObservedWalkerSet<'_, T>> for HashSet<T> {
    fn eq(&self, other: &ObservedWalkerSet<'_, T>) -> bool { *self == other.values }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<T: Eq + std::hash::Hash> PartialEq for ObservedWalkerSet<'_, T> {
    fn eq(&self, other: &Self) -> bool { self.values == other.values }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<T: Eq + std::hash::Hash> Eq for ObservedWalkerSet<'_, T> {}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<'a, T> IntoIterator for &'a ObservedWalkerSet<'_, T> {
    type Item = &'a T;
    type IntoIter = std::collections::hash_set::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter { self.values.iter() }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
type F5cObservedSet<'meter> = ObservedWalkerSet<'meter, u32>;
#[cfg(not(all(test, feature = "f5c_resource_probe")))]
type F5cObservedSet<'meter> = HashSet<u32>;

#[cfg(all(test, feature = "f5c_resource_probe"))]
type F5cRawIncidenceSet<'meter> = ObservedWalkerSet<'meter, u32>;
#[cfg(not(all(test, feature = "f5c_resource_probe")))]
type F5cRawIncidenceSet<'meter> = HashSet<u32>;

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) struct ObservedWalkerMap<'meter, K, V> {
    values: HashMap<K, V>,
    owner: Option<RawWalkerOwner<'meter>>,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<'meter, K: Eq + std::hash::Hash, V> ObservedWalkerMap<'meter, K, V> {
    fn new(meter: &'meter DraftHeapMeter, kind: F5cWalkerLaneKind) -> Self {
        Self::new_optional(Some(meter), kind)
    }

    fn new_optional(meter: Option<&'meter DraftHeapMeter>, kind: F5cWalkerLaneKind) -> Self {
        Self { values: HashMap::new(), owner: meter.map(|meter|
            RawWalkerOwner::new(meter, kind as usize, kind.slot_size())) }
    }

    fn from_values(meter: Option<&'meter DraftHeapMeter>, kind: F5cWalkerLaneKind,
        values: HashMap<K, V>) -> Self {
        let mut result = Self { values, owner: meter.map(|meter|
            RawWalkerOwner::new(meter, kind as usize, kind.slot_size())) };
        result.observe_capacity(result.values.len());
        result
    }

    fn observe_capacity(&mut self, _requested: usize) {
        if let Some(owner) = self.owner.as_mut() {
            owner.observe(self.values.len(), self.values.capacity());
        }
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        let old = self.values.insert(key, value);
        self.observe_capacity(0);
        old
    }

    fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where K: std::borrow::Borrow<Q>, Q: std::hash::Hash + Eq + ?Sized {
        let old = self.values.remove(key);
        self.observe_capacity(0);
        old
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<K, V> std::ops::Deref for ObservedWalkerMap<'_, K, V> {
    type Target = HashMap<K, V>;
    fn deref(&self) -> &Self::Target { &self.values }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<K, V> std::ops::DerefMut for ObservedWalkerMap<'_, K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.values }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<K: std::fmt::Debug, V: std::fmt::Debug> std::fmt::Debug
    for ObservedWalkerMap<'_, K, V> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.values.fmt(formatter)
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<K: Eq + std::hash::Hash, V: PartialEq> PartialEq<HashMap<K, V>>
    for ObservedWalkerMap<'_, K, V> {
    fn eq(&self, other: &HashMap<K, V>) -> bool { self.values == *other }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<K: Eq + std::hash::Hash, V: PartialEq> PartialEq
    for ObservedWalkerMap<'_, K, V> {
    fn eq(&self, other: &Self) -> bool { self.values == other.values }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl<K: Eq + std::hash::Hash, V: Eq> Eq for ObservedWalkerMap<'_, K, V> {}

#[cfg(all(test, feature = "f5c_resource_probe"))]
struct ObservedReentryMap<'meter> {
    values: HashMap<u32, Vec<usize>>,
    _map_owner: RawWalkerOwner<'meter>,
    _index_owners: HashMap<u32, RawWalkerOwner<'meter>>,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl std::ops::Deref for ObservedReentryMap<'_> {
    type Target = HashMap<u32, Vec<usize>>;
    fn deref(&self) -> &Self::Target { &self.values }
}

fn classify_staged_buffers(
    allocations: &mut [TrackedAllocation<'_>; 6],
    capacities: [usize; 6], requested: [usize; 6], sizes: [usize; 6],
) {
    for index in 0..6 {
        allocations[index].classify_shape(
            PhysicalOwnerKind::StagedBuffer(index), requested[index],
            capacities[index], sizes[index],
        );
    }
}

fn staged_requested(draft: &f5c_draft::FlatDraft) -> [usize; 6] {
    [draft.positive_nodes.len(), draft.negative_nodes.len(),
        draft.positive_children.len(), draft.negative_children.len(),
        draft.recursive_bounds.len(), draft.insertion_order.len()]
}

fn claim_flat_draft_batch<'meter>(
    meter: &'meter DraftHeapMeter,
    draft: &mut f5c_draft::FlatDraft,
    bytes: [usize; 6],
    future_external: usize,
    capacities: [usize; 6],
    sizes: [usize; 6],
) -> Result<[TrackedAllocation<'meter>; 6], ()> {
    let requested = staged_requested(draft);
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    if let Some(owners) = draft.owners.as_mut() {
        return meter.claim_existing_batch_with_owners(
            bytes, future_external, owners, requested, capacities, sizes);
    }
    let mut allocations = meter.claim_existing_batch(bytes, future_external)?;
    classify_staged_buffers(&mut allocations, capacities, requested, sizes);
    Ok(allocations)
}

#[cfg(test)]
pub(super) struct PhysicalJoint {
    pub(super) source_capacities: [u128; 4],
    pub(super) walker_capacities: [u128; 98],
    pub(super) memo_current: u128,
    pub(super) walker_current: u128,
    pub(super) source_current: u128,
    pub(super) source_nested_bytes: u128,
    pub(super) staged_source_current: u128,
    pub(super) peak: u128,
    pub(super) source_walker_peak: u128,
    pub(super) aggregate_overflow: bool,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct PartsPhysicalEvent {
    pub(super) growths: usize,
    pub(super) transfers: usize,
    pub(super) failed_reserves: usize,
    pub(super) live_capacity: usize,
    pub(super) peak_capacity: usize,
    pub(super) transfer_capacity: usize,
    pub(super) growth_joint_bytes: u128,
    pub(super) transfer_joint_bytes: u128,
    pub(super) peak_joint_bytes: u128,
    pub(super) expected_peak_bytes: u128,
    pub(super) failed_expected_bytes: u128,
    pub(super) growth_components: [u128; 4],
    pub(super) transfer_components: [u128; 4],
    pub(super) failed_components: [u128; 4],
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(super) struct PartsCensusSample {
    pub(super) components: Option<[u128; 3]>,
    pub(super) total: Option<u128>,
    pub(super) source_capacities: [usize; 2],
    pub(super) lane_capacities: [usize; 2],
    pub(super) logical_peak: Option<usize>,
    pub(super) physical_peak: Option<usize>,
}

#[cfg(test)]
impl Default for PhysicalJoint {
    fn default() -> Self {
        Self {
            source_capacities: [0; 4],
            walker_capacities: [0; 98],
            memo_current: 0,
            walker_current: 0,
            source_current: 0,
            source_nested_bytes: 0,
            staged_source_current: 0,
            peak: 0,
            source_walker_peak: 0,
            aggregate_overflow: false,
        }
    }
}

#[cfg(test)]
impl PhysicalJoint {
    fn sum_products(values: impl IntoIterator<Item = (u128, usize)>) -> Option<u128> {
        values.into_iter().try_fold(0u128, |sum, (capacity, size)| {
            sum.checked_add(capacity.checked_mul(size as u128)?)
        })
    }

    pub(super) fn source_event(&mut self) {
        let sizes = [
            std::mem::size_of::<GeneralizationDraft>(),
            std::mem::size_of::<TrackedAllocation<'static>>(),
            std::mem::size_of::<F5cRecursiveBound>(),
            std::mem::size_of::<F5cRecursiveBound>(),
        ];
        self.source_current = Self::sum_products(self.source_capacities.iter().copied().zip(sizes))
            .and_then(|bytes| bytes.checked_add(self.source_nested_bytes))
            .unwrap_or_else(|| {
                self.aggregate_overflow = true;
                u128::MAX
            });
        self.pair();
    }

    fn pair(&mut self) {
        let Some(source_walker) = self.source_current
            .checked_add(self.staged_source_current)
            .and_then(|sum| sum.checked_add(self.walker_current))
        else {
            self.aggregate_overflow = true;
            self.source_walker_peak = u128::MAX;
            self.peak = u128::MAX;
            return;
        };
        self.source_walker_peak = self.source_walker_peak.max(source_walker);
        let Some(total) = self
            .source_current
            .checked_add(self.staged_source_current)
            .and_then(|sum| sum.checked_add(self.memo_current))
            .and_then(|sum| sum.checked_add(self.walker_current))
        else {
            self.aggregate_overflow = true;
            self.peak = u128::MAX;
            return;
        };
        self.peak = self.peak.max(total);
        self.aggregate_overflow |= total > usize::MAX as u128;
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum F5cBulkDrainSite {
    SummaryPositive,
    SummaryNegative,
    RawMaterializePositive,
    RawMaterializeNegative,
    FlatMaterializePositive,
    FlatMaterializeNegative,
    RowPositive,
    RowNegative,
    ReplayPositive,
    ReplayNegative,
    SubstitutePositive,
    SubstituteNegative,
}

#[cfg(test)]
thread_local! {
    pub(super) static F5C_TAINT_BOUNDARY: std::cell::Cell<Option<(usize, usize)>> = const { std::cell::Cell::new(None) };
    pub(super) static F5C_FUNCTION_OUTPUT_CONSTRUCTION: std::cell::Cell<Option<(usize, usize)>> = const { std::cell::Cell::new(None) };
    pub(super) static F5C_ORDER_REGISTRATION: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
    pub(super) static F5C_BULK_DRAIN_BOUNDARY: std::cell::Cell<Option<(F5cBulkDrainSite, usize, usize)>> = const { std::cell::Cell::new(None) };
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
thread_local! {
    static F5C_GUARDED_PROGRESS: std::cell::Cell<Option<(usize, usize)>> =
        const { std::cell::Cell::new(None) };
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) struct F5cGuardedProgressGuard;

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) fn arm_f5c_guarded_progress() -> F5cGuardedProgressGuard {
    F5C_GUARDED_PROGRESS.with(|state| {
        assert!(state.get().is_none(), "F5c guarded progress observer already armed");
        state.set(Some((0, 1)));
    });
    F5cGuardedProgressGuard
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
impl Drop for F5cGuardedProgressGuard {
    fn drop(&mut self) {
        F5C_GUARDED_PROGRESS.with(|state| state.set(None));
    }
}

#[cfg(test)]
pub(super) fn record_bulk_drain_boundary(
    site: F5cBulkDrainSite,
    meter: &F5cDraftWorkMeter,
    count: usize,
) {
    F5C_BULK_DRAIN_BOUNDARY.with(|boundary| boundary.set(Some((site, meter.get(), count))));
}

#[derive(Clone, Default)]
pub(super) struct F5cDraftWorkMeter(
    std::rc::Rc<std::cell::Cell<usize>>,
    #[cfg(test)] std::rc::Rc<std::cell::Cell<Option<usize>>>,
    #[cfg(test)] std::rc::Rc<std::cell::Cell<Option<usize>>>,
);

impl F5cDraftWorkMeter {
    pub(super) fn charge(&self, count: usize) -> Result<(), SolveAvailabilityError> {
        let next = self
            .0
            .get()
            .checked_add(count)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.0.set(next);
        Ok(())
    }

    pub(super) fn get(&self) -> usize {
        self.0.get()
    }

    #[cfg(test)]
    pub(super) fn set(&self, value: usize) {
        self.0.set(value);
    }

    #[cfg(test)]
    pub(super) fn last_persistent_mutation_work(&self) -> Option<usize> {
        self.1.get()
    }

    #[cfg(test)]
    pub(super) fn arm_overflow_after_root_admission(&self, ordinal: usize) {
        self.2.set(Some(ordinal));
    }

    #[cfg(test)]
    fn record_persistent_mutation(&self) {
        self.1.set(Some(self.get()));
    }

    #[cfg(test)]
    fn record_root_admission(&self, ordinal: usize) {
        self.record_persistent_mutation();
        if self.2.get() == Some(ordinal) {
            self.2.set(None);
            self.set(usize::MAX);
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub(super) enum F5cPositive<'meter> {
    Bottom,
    Int,
    Unit,
    Variable(u32),
    Quantified(u32),
    Recursive(u32),
    Shared(F5cSummaryNodeId),
    Union(TrackedVec<'meter, F5cPositive<'meter>>),
    Function {
        argument: TrackedOne<'meter, F5cNegative<'meter>>,
        argument_effect: F5cNegativeEffect,
        result_effect: F5cPositiveEffect,
        result: TrackedOne<'meter, F5cPositive<'meter>>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum F5cPositiveEffect {
    Bottom,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum F5cNegativeEffect {
    Empty,
}

#[derive(Debug, Eq, PartialEq)]
pub(super) enum F5cNegative<'meter> {
    Top,
    Bottom,
    Int,
    Unit,
    Variable(u32),
    Quantified(u32),
    Recursive(u32),
    Shared(F5cSummaryNodeId),
    Intersection(TrackedVec<'meter, F5cNegative<'meter>>),
    Function {
        argument: TrackedOne<'meter, F5cPositive<'meter>>,
        argument_effect: F5cPositiveEffect,
        result_effect: F5cNegativeEffect,
        result: TrackedOne<'meter, F5cNegative<'meter>>,
    },
}

#[derive(Debug, Eq, PartialEq)]
pub(super) struct F5cRecursiveBound<'meter> {
    pub(super) ordinal: u32,
    pub(super) lower: F5cPositive<'meter>,
    pub(super) upper: F5cNegative<'meter>,
}

#[derive(Debug, Eq, PartialEq)]
pub(super) struct GeneralizationDraft<'meter> {
    pub(super) quantifier_count: u32,
    pub(super) recursive_bounds: Vec<F5cRecursiveBound<'meter>>,
    pub(super) predicate: F5cPositive<'meter>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum F5cBoundSide {
    Lower,
    Upper,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum F5cTraceHop {
    Exact {
        side: F5cBoundSide,
        slot: usize,
    },
    Direct {
        side: F5cBoundSide,
        slot: usize,
        source: u32,
        target: u32,
    },
    Function(FunctionField),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct F5cGuardedTrace {
    pub(super) owner: u32,
    pub(super) entry_polarity: Polarity,
    pub(super) reentry_polarity: Polarity,
    pub(super) path: Vec<F5cTraceHop>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct F5cExpansionKey {
    pub(super) row: u32,
    pub(super) polarity: Polarity,
    pub(super) frozen_bound_epoch: usize,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct F5cSummaryNodeId(pub(super) u32);

fn checked_summary_node_admission(len: usize) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
    let next = len
        .checked_add(1)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let next = u32::try_from(next).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
    Ok(F5cSummaryNodeId(next - 1))
}

fn checked_next_root_lane_len(len: usize) -> Result<usize, SolveAvailabilityError> {
    len.checked_add(1)
        .ok_or(SolveAvailabilityError::IdentityExhausted)
}

fn checked_reverse_parent_len(
    current: usize,
    child_count: usize,
) -> Result<usize, SolveAvailabilityError> {
    current
        .checked_add(child_count)
        .ok_or(SolveAvailabilityError::IdentityExhausted)
}

#[cfg(test)]
mod reverse_parent_len_tests {
    use super::*;

    #[test]
    fn checks_logical_incidence_append_at_usize_boundary() {
        assert_eq!(checked_reverse_parent_len(0, 0), Ok(0));
        assert_eq!(
            checked_reverse_parent_len(usize::MAX - 2, 2),
            Ok(usize::MAX)
        );
        assert_eq!(
            checked_reverse_parent_len(usize::MAX - 1, 2),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
    }
}

#[cfg(test)]
mod root_lane_len_tests {
    use super::*;

    #[test]
    fn checks_post_append_usize_boundary_without_a_u32_root_limit() {
        assert_eq!(checked_next_root_lane_len(0), Ok(1));
        assert_eq!(checked_next_root_lane_len(usize::MAX - 1), Ok(usize::MAX));
        assert_eq!(
            checked_next_root_lane_len(usize::MAX),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
    }
}

#[cfg(test)]
mod summary_node_admission_tests {
    use super::*;

    #[test]
    fn checks_post_append_count_before_admitting_node_id() {
        assert_eq!(
            checked_summary_node_admission(u32::MAX as usize - 1).unwrap(),
            F5cSummaryNodeId(u32::MAX - 1)
        );
        assert!(matches!(
            checked_summary_node_admission(u32::MAX as usize),
            Err(SolveAvailabilityError::IdentityExhausted)
        ));
        assert!(matches!(
            checked_summary_node_admission(usize::MAX),
            Err(SolveAvailabilityError::IdentityExhausted)
        ));
    }
}

#[allow(dead_code)] // The candidate source arena is wired to the walker in the next gate.
mod flat_source_arena;
#[allow(dead_code)] // The candidate is exercised only by module-local test entrypoints.
mod flat_walk_sink;
pub(super) use flat_walk_sink::{F5cFlatWalkSink, FlatWalkValue};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum F5cSummaryNodeKind {
    PositiveBottom,
    PositiveInt,
    PositiveUnit,
    PositiveRow(u32),
    PositiveAlias {
        start: u32,
    },
    PositiveUnion {
        start: u32,
        len: u32,
    },
    PositiveFunction {
        argument: F5cSummaryNodeId,
        result: F5cSummaryNodeId,
    },
    NegativeTop,
    NegativeBottom,
    NegativeInt,
    NegativeUnit,
    NegativeRow(u32),
    NegativeAlias {
        start: u32,
    },
    NegativeIntersection {
        start: u32,
        len: u32,
    },
    NegativeFunction {
        argument: F5cSummaryNodeId,
        result: F5cSummaryNodeId,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct F5cSummaryNode {
    pub(super) incidence: Option<(u32, Polarity)>,
    pub(super) transitive_incidence_count: usize,
    pub(super) kind: F5cSummaryNodeKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct F5cReverseParentEdge {
    pub(super) child: F5cSummaryNodeId,
    pub(super) parent: F5cSummaryNodeId,
    pub(super) next: Option<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct F5cIncidenceEdge {
    pub(super) node: F5cSummaryNodeId,
    pub(super) next: Option<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct F5cRootEdge {
    pub(super) root: F5cSummaryNodeId,
    pub(super) key: F5cExpansionKey,
    pub(super) next: Option<usize>,
    pub(super) live: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum F5cRootUndo {
    Admit(usize),
    Invalidate(usize),
}

#[cfg(test)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum F5cTestObservationFailure {
    Admit,
    Enter,
    Leave,
    ClosureRelease,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum F5cTestReserveFailure {
    ActiveMirrors,
    OrderAfterSeen,
    ReentryPathAfterReserve,
    RawOwnerOrder,
    BoxedReentryIndices,
    ChildrenAfterReserve,
    RootUndo,
    ConflictJournal,
    RecursiveBoundAfterReserve,
    FlatPreparationAfterPositiveOnly,
    PartsAfterReserve(usize),
}

#[derive(Clone, Copy, Default)]
pub(super) struct F5cMemoLane {
    pub(super) requested_slots: usize,
    pub(super) peak_bytes: usize,
    pub(super) capacity_growths: usize,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
#[derive(Clone, Copy, Default)]
pub(super) struct F5cMatrixMemoLane {
    pub(super) requested_slots: usize,
    pub(super) actual_capacity: usize,
    pub(super) slot_size: usize,
    pub(super) retained_bytes: usize,
    pub(super) peak_bytes: usize,
    pub(super) growths: usize,
    pub(super) cleared: bool,
}

#[derive(Clone, Copy)]
pub(super) enum F5cWalkerLaneKind {
    Tasks = 0,
    Values = 1,
    DirectEdges = 2,
    SummaryTasks = 3,
    SummaryIds = 4,
    DirectTargets = 5,
    Comparison = 6,
    PositiveParts = 7,
    NegativeParts = 8,
    MaterializeTasks = 9,
    MaterializeValues = 10,
    DraftMaterializeTasks = 11,
    DraftMaterializeValues = 12,
    AnalysisTasks = 13,
    ReplayTasks = 14,
    ReplayValues = 15,
    BinderTasks = 16,
    BinderValues = 17,
    SourcePositiveNodes = 18,
    SourceNegativeNodes = 19,
    SourcePositiveChildren = 20,
    SourceNegativeChildren = 21,
    FlatComparison = 22,
    FlatPositiveParts = 23,
    FlatNegativeParts = 24,
    FlatPromotionTasks = 25,
    FlatPromotionIds = 26,
    DraftPositiveNodes = 27,
    DraftNegativeNodes = 28,
    DraftPositiveChildren = 29,
    DraftNegativeChildren = 30,
    DraftRecursiveBounds = 31,
    DraftInsertionOrder = 32,
    FlatMaterializeTasks = 33,
    FlatMaterializeValues = 34,
    FlatSourceMaterializeTasks = 35,
    FlatSourceMaterializeValues = 36,
    FlatSourceMaterializeRoots = 37,
    RawOwnerOrder = 38,
    RawOwnerBounds = 39,
    RawOwnerSeen = 40,
    RawRoots = 41,
    RawCallbackTrace = 42,
    ReplayActivePositive = 43,
    ReplayActiveNegative = 44,
    ReplayOutputPositiveNodes = 45,
    ReplayOutputNegativeNodes = 46,
    ReplayOutputPositiveChildren = 47,
    ReplayOutputNegativeChildren = 48,
    ReplayOutputInsertionOrder = 49,
    RetainedOwnerBounds = 50,
    PostRSurvivingBounds = 51,
    PostRSurvivingTraces = 52,
    PostRRecursiveOwners = 53,
    PostRRecursiveSet = 54,
    PostROccurrenceOrder = 55,
    PostROccurrenceSeen = 56,
    PostRQuantifiers = 57,
    PostRRecursives = 58,
    SelectedRecursiveBounds = 59,
    SelectedPositiveEliminated = 60,
    SelectedNegativeEliminated = 61,
    SubstitutePositiveSeen = 62,
    SubstituteNegativeSeen = 63,
    SubstituteStack = 64,
    NormalizedPositiveNodes = 65,
    NormalizedNegativeNodes = 66,
    NormalizedPositiveChildren = 67,
    NormalizedNegativeChildren = 68,
    NormalizedRecursiveBounds = 69,
    NormalizedInsertionOrder = 70,
    ClosureAdjacency = 71,
    ClosureNeighbors = 72,
    ClosureConnected = 73,
    ClosureResult = 74,
    BoxedRetainedOwnerBounds = 97,
    ClosureFrontier = 75,
    RawPositiveIncidences = 76,
    RawNegativeIncidences = 77,
    UncacheableSeen = 78,
    ProvisionalRecursiveRows = 79,
    Path = 80,
    Order = 81,
    OrderSeen = 82,
    Reentries = 83,
    ReentryPaths = 84,
    BoxedRawBounds = 85,
    BoxedCompletedOwners = 86,
    BoxedReentriesByOwner = 87,
    BoxedReentryIndices = 88,
    BoxedPositiveOnly = 89,
    BoxedNegativeOnly = 90,
    RCandidates = 91,
    RPrevious = 92,
    RSurvivingBounds = 93,
    RReachable = 94,
    RFrontier = 95,
    RReferenced = 96,
}

impl F5cWalkerLaneKind {
    pub(super) const ALL: [Self; 98] = [
        Self::Tasks,
        Self::Values,
        Self::DirectEdges,
        Self::SummaryTasks,
        Self::SummaryIds,
        Self::DirectTargets,
        Self::Comparison,
        Self::PositiveParts,
        Self::NegativeParts,
        Self::MaterializeTasks,
        Self::MaterializeValues,
        Self::DraftMaterializeTasks,
        Self::DraftMaterializeValues,
        Self::AnalysisTasks,
        Self::ReplayTasks,
        Self::ReplayValues,
        Self::BinderTasks,
        Self::BinderValues,
        Self::SourcePositiveNodes,
        Self::SourceNegativeNodes,
        Self::SourcePositiveChildren,
        Self::SourceNegativeChildren,
        Self::FlatComparison,
        Self::FlatPositiveParts,
        Self::FlatNegativeParts,
        Self::FlatPromotionTasks,
        Self::FlatPromotionIds,
        Self::DraftPositiveNodes,
        Self::DraftNegativeNodes,
        Self::DraftPositiveChildren,
        Self::DraftNegativeChildren,
        Self::DraftRecursiveBounds,
        Self::DraftInsertionOrder,
        Self::FlatMaterializeTasks,
        Self::FlatMaterializeValues,
        Self::FlatSourceMaterializeTasks,
        Self::FlatSourceMaterializeValues,
        Self::FlatSourceMaterializeRoots,
        Self::RawOwnerOrder,
        Self::RawOwnerBounds,
        Self::RawOwnerSeen,
        Self::RawRoots,
        Self::RawCallbackTrace,
        Self::ReplayActivePositive,
        Self::ReplayActiveNegative,
        Self::ReplayOutputPositiveNodes,
        Self::ReplayOutputNegativeNodes,
        Self::ReplayOutputPositiveChildren,
        Self::ReplayOutputNegativeChildren,
        Self::ReplayOutputInsertionOrder,
        Self::RetainedOwnerBounds,
        Self::PostRSurvivingBounds,
        Self::PostRSurvivingTraces,
        Self::PostRRecursiveOwners,
        Self::PostRRecursiveSet,
        Self::PostROccurrenceOrder,
        Self::PostROccurrenceSeen,
        Self::PostRQuantifiers,
        Self::PostRRecursives,
        Self::SelectedRecursiveBounds,
        Self::SelectedPositiveEliminated,
        Self::SelectedNegativeEliminated,
        Self::SubstitutePositiveSeen,
        Self::SubstituteNegativeSeen,
        Self::SubstituteStack,
        Self::NormalizedPositiveNodes,
        Self::NormalizedNegativeNodes,
        Self::NormalizedPositiveChildren,
        Self::NormalizedNegativeChildren,
        Self::NormalizedRecursiveBounds,
        Self::NormalizedInsertionOrder,
        Self::ClosureAdjacency,
        Self::ClosureNeighbors,
        Self::ClosureConnected,
        Self::ClosureResult,
        Self::ClosureFrontier,
        Self::RawPositiveIncidences,
        Self::RawNegativeIncidences,
        Self::UncacheableSeen,
        Self::ProvisionalRecursiveRows,
        Self::Path,
        Self::Order,
        Self::OrderSeen,
        Self::Reentries,
        Self::ReentryPaths,
        Self::BoxedRawBounds,
        Self::BoxedCompletedOwners,
        Self::BoxedReentriesByOwner,
        Self::BoxedReentryIndices,
        Self::BoxedPositiveOnly,
        Self::BoxedNegativeOnly,
        Self::RCandidates,
        Self::RPrevious,
        Self::RSurvivingBounds,
        Self::RReachable,
        Self::RFrontier,
        Self::RReferenced,
        Self::BoxedRetainedOwnerBounds,
    ];

    pub(super) fn slot_size(self) -> usize {
        match self {
            Self::Tasks => std::mem::size_of::<F5cWalkTask>(),
            Self::Values => std::mem::size_of::<F5cWalkValue>(),
            Self::DirectEdges => std::mem::size_of::<(usize, u32)>(),
            Self::SummaryTasks => std::mem::size_of::<F5cSummaryTask<'static, 'static>>(),
            Self::SummaryIds => std::mem::size_of::<F5cSummaryNodeId>(),
            Self::DirectTargets => std::mem::size_of::<u32>(),
            Self::Comparison => std::mem::size_of::<F5cCompareTask<'static, 'static>>(),
            Self::PositiveParts => std::mem::size_of::<F5cPositive>(),
            Self::NegativeParts => std::mem::size_of::<F5cNegative>(),
            Self::MaterializeTasks => std::mem::size_of::<F5cMaterializeTask>(),
            Self::MaterializeValues => std::mem::size_of::<F5cWalkValue>(),
            Self::DraftMaterializeTasks => std::mem::size_of::<f5c_materialization::Task>(),
            Self::DraftMaterializeValues => std::mem::size_of::<F5cWalkValue>(),
            Self::FlatMaterializeTasks => std::mem::size_of::<f5c_materialization::FlatTask>(),
            Self::FlatMaterializeValues => std::mem::size_of::<f5c_draft::NodeRef>(),
            Self::FlatSourceMaterializeTasks => {
                std::mem::size_of::<flat_walk_sink::SourceMaterializeTask>()
            }
            Self::FlatSourceMaterializeValues => std::mem::size_of::<f5c_draft::NodeRef>(),
            Self::FlatSourceMaterializeRoots => std::mem::size_of::<f5c_draft::NodeRef>(),
            Self::RawOwnerOrder => std::mem::size_of::<u32>(),
            Self::RawOwnerBounds => {
                std::mem::size_of::<(u32, (f5c_draft::PositiveId, f5c_draft::NegativeId))>()
            }
            Self::RawOwnerSeen => std::mem::size_of::<u32>(),
            Self::RawRoots => std::mem::size_of::<flat_walk_sink::FlatWalkValue>(),
            Self::RawCallbackTrace => std::mem::size_of::<(u32, Polarity)>(),
            Self::AnalysisTasks => std::mem::size_of::<f5c_tree_analysis::Task<'static, 'static>>(),
            Self::ReplayTasks => std::mem::size_of::<f5c_replay::Task<'static, 'static>>(),
            Self::ReplayValues => std::mem::size_of::<F5cWalkValue>(),
            Self::BinderTasks => std::mem::size_of::<f5c_binder_substitution::Task>(),
            Self::BinderValues => std::mem::size_of::<F5cWalkValue>(),
            Self::SourcePositiveNodes => std::mem::size_of::<flat_source_arena::PositiveNode>(),
            Self::SourceNegativeNodes => std::mem::size_of::<flat_source_arena::NegativeNode>(),
            Self::SourcePositiveChildren => std::mem::size_of::<flat_source_arena::PositiveRef>(),
            Self::SourceNegativeChildren => std::mem::size_of::<flat_source_arena::NegativeRef>(),
            Self::FlatComparison => std::mem::size_of::<flat_walk_sink::CompareTask>(),
            Self::FlatPositiveParts => std::mem::size_of::<flat_source_arena::PositiveRef>(),
            Self::FlatNegativeParts => std::mem::size_of::<flat_source_arena::NegativeRef>(),
            Self::FlatPromotionTasks => std::mem::size_of::<flat_walk_sink::PromotionTask>(),
            Self::FlatPromotionIds => std::mem::size_of::<F5cSummaryNodeId>(),
            Self::DraftPositiveNodes => std::mem::size_of::<f5c_draft::PositiveNode>(),
            Self::DraftNegativeNodes => std::mem::size_of::<f5c_draft::NegativeNode>(),
            Self::DraftPositiveChildren => std::mem::size_of::<f5c_draft::PositiveId>(),
            Self::DraftNegativeChildren => std::mem::size_of::<f5c_draft::NegativeId>(),
            Self::DraftRecursiveBounds => std::mem::size_of::<f5c_draft::RecursiveBound>(),
            Self::SelectedRecursiveBounds => std::mem::size_of::<f5c_draft::RecursiveBound>(),
            Self::DraftInsertionOrder => std::mem::size_of::<f5c_draft::NodeRef>(),
            Self::ReplayActivePositive | Self::ReplayActiveNegative => std::mem::size_of::<bool>(),
            Self::ReplayOutputPositiveNodes => std::mem::size_of::<f5c_draft::PositiveNode>(),
            Self::ReplayOutputNegativeNodes => std::mem::size_of::<f5c_draft::NegativeNode>(),
            Self::ReplayOutputPositiveChildren => std::mem::size_of::<f5c_draft::PositiveId>(),
            Self::ReplayOutputNegativeChildren => std::mem::size_of::<f5c_draft::NegativeId>(),
            Self::ReplayOutputInsertionOrder => std::mem::size_of::<f5c_draft::NodeRef>(),
            Self::RetainedOwnerBounds => {
                std::mem::size_of::<(u32, (f5c_draft::PositiveId, f5c_draft::NegativeId))>()
            }
            Self::BoxedRetainedOwnerBounds => {
                std::mem::size_of::<(u32, (F5cPositive, F5cNegative))>()
            }
            Self::PostRSurvivingBounds | Self::PostRRecursiveSet | Self::PostROccurrenceSeen => {
                std::mem::size_of::<u32>()
            }
            Self::PostRSurvivingTraces => std::mem::size_of::<usize>(),
            Self::PostRRecursiveOwners | Self::PostROccurrenceOrder => std::mem::size_of::<u32>(),
            Self::PostRQuantifiers | Self::PostRRecursives => std::mem::size_of::<(u32, u32)>(),
            Self::SelectedPositiveEliminated | Self::SelectedNegativeEliminated => {
                std::mem::size_of::<u32>()
            }
            Self::SubstitutePositiveSeen | Self::SubstituteNegativeSeen => {
                std::mem::size_of::<bool>()
            }
            Self::SubstituteStack => std::mem::size_of::<f5c_draft::NodeRef>(),
            Self::NormalizedPositiveNodes => std::mem::size_of::<f5c_draft::PositiveNode>(),
            Self::NormalizedNegativeNodes => std::mem::size_of::<f5c_draft::NegativeNode>(),
            Self::NormalizedPositiveChildren => std::mem::size_of::<f5c_draft::PositiveId>(),
            Self::NormalizedNegativeChildren => std::mem::size_of::<f5c_draft::NegativeId>(),
            Self::NormalizedRecursiveBounds => std::mem::size_of::<f5c_draft::RecursiveBound>(),
            Self::NormalizedInsertionOrder => std::mem::size_of::<f5c_draft::NodeRef>(),
            Self::ClosureAdjacency => std::mem::size_of::<HashSet<u32>>(),
            Self::ClosureNeighbors
            | Self::ClosureConnected
            | Self::ClosureResult
            | Self::RawPositiveIncidences
            | Self::RawNegativeIncidences => std::mem::size_of::<u32>(),
            Self::ClosureFrontier => std::mem::size_of::<u32>(),
            Self::UncacheableSeen => std::mem::size_of::<F5cExpansionKey>(),
            Self::ProvisionalRecursiveRows | Self::Order | Self::OrderSeen => {
                std::mem::size_of::<u32>()
            }
            Self::Path | Self::ReentryPaths => std::mem::size_of::<F5cTraceHop>(),
            Self::Reentries => std::mem::size_of::<F5cGuardedTrace>(),
            Self::BoxedRawBounds => std::mem::size_of::<(u32, (F5cPositive, F5cNegative))>(),
            Self::BoxedCompletedOwners
            | Self::BoxedPositiveOnly
            | Self::BoxedNegativeOnly
            | Self::RCandidates
            | Self::RPrevious
            | Self::RSurvivingBounds
            | Self::RReachable
            | Self::RFrontier
            | Self::RReferenced => std::mem::size_of::<u32>(),
            Self::BoxedReentriesByOwner => std::mem::size_of::<(u32, Vec<usize>)>(),
            Self::BoxedReentryIndices => std::mem::size_of::<usize>(),
        }
    }
}

pub(super) fn release_flat_post_r_lanes(memo: &mut F5cComponentExpansionMemo) {
    for kind in [
        F5cWalkerLaneKind::RetainedOwnerBounds,
        F5cWalkerLaneKind::PostRSurvivingBounds,
        F5cWalkerLaneKind::PostRSurvivingTraces,
        F5cWalkerLaneKind::PostRRecursiveOwners,
        F5cWalkerLaneKind::PostRRecursiveSet,
        F5cWalkerLaneKind::PostROccurrenceOrder,
        F5cWalkerLaneKind::PostROccurrenceSeen,
        F5cWalkerLaneKind::PostRQuantifiers,
        F5cWalkerLaneKind::PostRRecursives,
    ] {
        memo.walker_resources.release(kind);
    }
}

#[derive(Clone, Copy, Default)]
pub(super) struct F5cWalkerLane {
    pub(super) requested_slots: usize,
    pub(super) actual_capacity: usize,
    #[cfg(test)]
    pub(super) peak_capacity: usize,
    pub(super) peak_bytes: usize,
    pub(super) capacity_growths: usize,
}

pub(super) struct F5cWalkerResources {
    pub(super) lanes: [F5cWalkerLane; 98],
    pub(super) peak_bytes: usize,
    pub(super) simultaneous_memo_peak_bytes: usize,
    pub(super) observed_memo_bytes: usize,
    pub(super) observed_source_bytes: Option<usize>,
    pub(super) simultaneous_source_memo_peak_bytes: usize,
    pub(super) value_slot_size: usize,
    #[cfg(test)]
    pub(super) physical_joint: PhysicalJoint,
    #[cfg(test)]
    pub(super) physical_walker_samples: usize,
    #[cfg(test)]
    pub(super) independent_lanes: [F5cWalkerLane; 98],
    #[cfg(test)]
    pub(super) independent_peak_bytes: usize,
    #[cfg(test)]
    pub(super) independent_simultaneous_memo_peak_bytes: usize,
    pub(super) flat_candidate_lanes:
        [f5c_normalization::FlatCandidateLane; f5c_normalization::FLAT_CANDIDATE_LANE_COUNT],
    pub(super) flat_batch_excluded_requests: usize,
}

impl Default for F5cWalkerResources {
    fn default() -> Self {
        Self {
            lanes: [F5cWalkerLane::default(); 98],
            peak_bytes: 0,
            simultaneous_memo_peak_bytes: 0,
            observed_memo_bytes: 0,
            observed_source_bytes: Some(0),
            simultaneous_source_memo_peak_bytes: 0,
            value_slot_size: 0,
            #[cfg(test)]
            physical_joint: PhysicalJoint::default(),
            #[cfg(test)]
            physical_walker_samples: 0,
            #[cfg(test)]
            independent_lanes: [F5cWalkerLane::default(); 98],
            #[cfg(test)]
            independent_peak_bytes: 0,
            #[cfg(test)]
            independent_simultaneous_memo_peak_bytes: 0,
            flat_candidate_lanes: [f5c_normalization::FlatCandidateLane::default();
                f5c_normalization::FLAT_CANDIDATE_LANE_COUNT],
            flat_batch_excluded_requests: 0,
        }
    }
}

impl F5cWalkerResources {
    #[cfg(test)]
    pub(super) fn physical_walker_bytes(&self) -> u128 {
        self.independent_lanes
            .iter()
            .enumerate()
            .map(|(index, lane)| {
                let kind = F5cWalkerLaneKind::ALL[index];
                let size = if matches!(kind, F5cWalkerLaneKind::Values) && self.value_slot_size != 0
                {
                    self.value_slot_size
                } else {
                    kind.slot_size()
                };
                lane.actual_capacity as u128 * size as u128
            })
            .sum()
    }

    pub(super) fn with_source<T>(
        &mut self,
        source_meter: &DraftHeapMeter,
        memo_bytes: usize,
        kind: F5cWalkerLaneKind,
        operation: impl FnOnce(&mut Self) -> Result<T, SolveAvailabilityError>,
    ) -> Result<T, SolveAvailabilityError> {
        let prior_capacity = self.lanes[kind as usize].actual_capacity;
        self.observed_source_bytes = source_meter.current_bytes();
        let result = operation(self);
        if self.lanes[kind as usize].actual_capacity != prior_capacity {
            self.observe_memo_with_source(memo_bytes, source_meter)?;
        }
        result
    }
    #[cfg(test)]
    fn observe_physical_walker(&mut self) {
        self.physical_walker_samples += 1;
        for lane in &mut self.independent_lanes {
            lane.peak_capacity = lane.peak_capacity.max(lane.actual_capacity);
        }
        let sizes = F5cWalkerLaneKind::ALL.map(|kind| {
            if matches!(kind, F5cWalkerLaneKind::Values) && self.value_slot_size != 0 {
                self.value_slot_size
            } else {
                kind.slot_size()
            }
        });
        self.physical_joint.walker_capacities = self
            .independent_lanes
            .map(|lane| lane.actual_capacity as u128);
        self.physical_joint.walker_current = PhysicalJoint::sum_products(
            self.physical_joint
                .walker_capacities
                .iter()
                .copied()
                .zip(sizes),
        )
        .unwrap_or_else(|| {
            self.physical_joint.aggregate_overflow = true;
            u128::MAX
        });
        self.physical_joint.pair();
    }

    #[cfg(test)]
    fn observe_physical_walker_target(&mut self, kind: F5cWalkerLaneKind, capacity: u128) {
        self.physical_walker_samples += 1;
        let index = kind as usize;
        if let Ok(capacity) = usize::try_from(capacity) {
            self.independent_lanes[index].peak_capacity =
                self.independent_lanes[index].peak_capacity.max(capacity);
        }
        self.physical_joint.walker_capacities[index] = capacity;
        self.physical_joint.walker_current = PhysicalJoint::sum_products(
            self.physical_joint
                .walker_capacities
                .iter()
                .copied()
                .zip(F5cWalkerLaneKind::ALL)
                .map(|(capacity, kind)| {
                    let size =
                        if matches!(kind, F5cWalkerLaneKind::Values) && self.value_slot_size != 0 {
                            self.value_slot_size
                        } else {
                            kind.slot_size()
                        };
                    (capacity, size)
                }),
        )
        .unwrap_or_else(|| {
            self.physical_joint.aggregate_overflow = true;
            u128::MAX
        });
        self.physical_joint.pair();
    }
    fn reserve_boxed_map<K: Eq + std::hash::Hash, V>(
        &mut self,
        map: &mut HashMap<K, V>,
        kind: F5cWalkerLaneKind,
        memo_bytes: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let index = kind as usize;
        let requested = self.lanes[index]
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        if map.len() < map.capacity() {
            #[cfg(test)]
            let independent_requested = self.independent_lanes[index]
                .requested_slots
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            self.lanes[index].requested_slots = requested;
            #[cfg(test)]
            {
                self.independent_lanes[index].requested_slots = independent_requested;
            }
            return Ok(());
        }
        let growth = self.lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_requested = self.independent_lanes[index]
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_growth = self.independent_lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let old = map.capacity();
        let reservation = map.try_reserve(1);
        let capacity = map.capacity();
        self.lanes[index].requested_slots = requested;
        self.lanes[index].actual_capacity = capacity;
        #[cfg(test)]
        {
            self.independent_lanes[index].requested_slots = independent_requested;
            self.independent_lanes[index].actual_capacity = capacity;
            if capacity != old {
                self.observe_physical_walker();
            }
        }
        if capacity != old {
            self.lanes[index].capacity_growths = growth;
            self.lanes[index].peak_bytes = self.lanes[index].peak_bytes.max(
                capacity
                    .checked_mul(kind.slot_size())
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            );
            #[cfg(test)]
            {
                self.independent_lanes[index].capacity_growths = independent_growth;
                self.independent_lanes[index].peak_bytes = self.lanes[index].peak_bytes;
            }
            self.observe_memo(memo_bytes)?;
            self.observed_memo_bytes = memo_bytes;
        }
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)
    }

    fn reserve_boxed_indices(
        &mut self,
        indices: &mut Vec<usize>,
        memo_bytes: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let kind = F5cWalkerLaneKind::BoxedReentryIndices;
        let index = kind as usize;
        let requested = self.lanes[index]
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let growth = self.lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_requested = self.independent_lanes[index]
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_growth = self.independent_lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let old = indices.capacity();
        let reservation = indices.try_reserve(1);
        #[cfg(test)]
        if indices.capacity() != old {
            self.observe_physical_walker_target(
                kind,
                self.independent_lanes[index].actual_capacity as u128
                    + (indices.capacity() - old) as u128,
            );
        }
        let delta = indices
            .capacity()
            .checked_sub(old)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let capacity = self.lanes[index]
            .actual_capacity
            .checked_add(delta)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.lanes[index].requested_slots = requested;
        self.lanes[index].actual_capacity = capacity;
        #[cfg(test)]
        {
            self.independent_lanes[index].requested_slots = independent_requested;
            self.independent_lanes[index].actual_capacity = capacity;
            if delta != 0 {
                self.observe_physical_walker();
            }
        }
        if delta != 0 {
            self.lanes[index].capacity_growths = growth;
            self.lanes[index].peak_bytes = self.lanes[index].peak_bytes.max(
                capacity
                    .checked_mul(kind.slot_size())
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            );
            #[cfg(test)]
            {
                self.independent_lanes[index].capacity_growths = independent_growth;
                self.independent_lanes[index].peak_bytes = self.lanes[index].peak_bytes;
            }
            self.observe_memo(memo_bytes)?;
            self.observed_memo_bytes = memo_bytes;
        }
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)
    }
    pub(super) fn reserve_generalizer_set<T: Eq + std::hash::Hash>(
        &mut self,
        set: &mut HashSet<T>,
        kind: F5cWalkerLaneKind,
        memo_bytes: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let index = kind as usize;
        let requested = self.lanes[index]
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        if set.len() < set.capacity() {
            #[cfg(test)]
            let independent_requested = self.independent_lanes[index]
                .requested_slots
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            self.lanes[index].requested_slots = requested;
            #[cfg(test)]
            {
                self.independent_lanes[index].requested_slots = independent_requested;
            }
            return Ok(());
        }
        #[cfg(test)]
        let independent_requested = self.independent_lanes[index]
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let growth = self.lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_growth = self.independent_lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let old = set.capacity();
        let result = set.try_reserve(1);
        let capacity = set.capacity();
        self.lanes[index].requested_slots = requested;
        self.lanes[index].actual_capacity = capacity;
        #[cfg(test)]
        {
            self.independent_lanes[index].requested_slots = independent_requested;
            self.independent_lanes[index].actual_capacity = capacity;
            if capacity != old {
                self.observe_physical_walker();
            }
        }
        if capacity != old {
            self.lanes[index].capacity_growths = growth;
            self.lanes[index].peak_bytes = self.lanes[index].peak_bytes.max(
                capacity
                    .checked_mul(kind.slot_size())
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            );
            #[cfg(test)]
            {
                self.independent_lanes[index].capacity_growths = independent_growth;
                self.independent_lanes[index].peak_bytes = self.lanes[index].peak_bytes;
            }
            self.observe_memo(memo_bytes)?;
            self.observed_memo_bytes = memo_bytes;
        }
        result.map_err(|_| SolveAvailabilityError::IdentityExhausted)
    }

    fn reserve_reentry_path(
        &mut self,
        path: &mut Vec<F5cTraceHop>,
        additional: usize,
        memo_bytes: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let kind = F5cWalkerLaneKind::ReentryPaths;
        let index = kind as usize;
        let requested = self.lanes[index]
            .requested_slots
            .checked_add(additional)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let growth = self.lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_requested = self.independent_lanes[index]
            .requested_slots
            .checked_add(additional)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_growth = self.independent_lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let old = path.capacity();
        let result = path.try_reserve(additional);
        #[cfg(test)]
        if path.capacity() != old {
            self.observe_physical_walker_target(
                kind,
                self.independent_lanes[index].actual_capacity as u128
                    + (path.capacity() - old) as u128,
            );
        }
        let delta = path
            .capacity()
            .checked_sub(old)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let capacity = self.lanes[index]
            .actual_capacity
            .checked_add(delta)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.lanes[index].requested_slots = requested;
        self.lanes[index].actual_capacity = capacity;
        #[cfg(test)]
        {
            self.independent_lanes[index].requested_slots = independent_requested;
            self.independent_lanes[index].actual_capacity = capacity;
            if delta != 0 {
                self.observe_physical_walker();
            }
        }
        if delta != 0 {
            self.lanes[index].capacity_growths = growth;
            self.lanes[index].peak_bytes = self.lanes[index].peak_bytes.max(
                capacity
                    .checked_mul(kind.slot_size())
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            );
            #[cfg(test)]
            {
                self.independent_lanes[index].capacity_growths = independent_growth;
                self.independent_lanes[index].peak_bytes = self.lanes[index].peak_bytes;
            }
            self.observe_memo(memo_bytes)?;
            self.observed_memo_bytes = memo_bytes;
        }
        result.map_err(|_| SolveAvailabilityError::IdentityExhausted)
    }

    fn release_reentry_path(&mut self, capacity: usize) {
        let kind = F5cWalkerLaneKind::ReentryPaths;
        let index = kind as usize;
        self.lanes[index].actual_capacity -= capacity;
        #[cfg(test)]
        {
            self.independent_lanes[index].actual_capacity -= capacity;
            if capacity != 0 {
                self.observe_physical_walker();
            }
        }
    }
    fn observe_existing_capacity(
        &mut self,
        kind: F5cWalkerLaneKind,
        capacity: usize,
        requested_slots: usize,
        memo_bytes: usize,
    ) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        if capacity != self.independent_lanes[kind as usize].actual_capacity {
            self.observe_physical_walker_target(kind, capacity as u128);
        }
        let lane = &self.lanes[kind as usize];
        #[cfg(test)]
        let independent = &self.independent_lanes[kind as usize];
        #[cfg(not(test))]
        let independent_requested = 0;
        #[cfg(not(test))]
        let independent_growth = 0;
        #[cfg(test)]
        let independent_requested = independent
            .requested_slots
            .checked_add(requested_slots)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_growth = independent
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let counters = (
            lane.requested_slots
                .checked_add(requested_slots)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            lane.capacity_growths
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            independent_requested,
            independent_growth,
        );
        let slot_size = kind.slot_size();
        let old_bytes = lane
            .actual_capacity
            .checked_mul(slot_size)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let new_bytes = capacity
            .checked_mul(slot_size)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let projected = self
            .retained_bytes()?
            .checked_sub(old_bytes)
            .and_then(|bytes| bytes.checked_add(new_bytes))
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        memo_bytes
            .checked_add(projected)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.observe_table_capacity(kind, 0, capacity, memo_bytes, counters)
    }

    fn preflight_table_counters(
        &self,
        kind: F5cWalkerLaneKind,
    ) -> Result<(usize, usize, usize, usize), SolveAvailabilityError> {
        let lane = &self.lanes[kind as usize];
        let requested = lane
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let growth = lane
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent = &self.independent_lanes[kind as usize];
        #[cfg(test)]
        let independent_requested = independent
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_growth = independent
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        return Ok((requested, growth, independent_requested, independent_growth));
        #[cfg(not(test))]
        Ok((requested, growth, 0, 0))
    }

    fn observe_table_capacity(
        &mut self,
        kind: F5cWalkerLaneKind,
        old: usize,
        capacity: usize,
        memo_bytes: usize,
        counters: (usize, usize, usize, usize),
    ) -> Result<(), SolveAvailabilityError> {
        self.lanes[kind as usize].requested_slots = counters.0;
        self.lanes[kind as usize].actual_capacity = capacity;
        #[cfg(test)]
        {
            self.independent_lanes[kind as usize].requested_slots = counters.2;
            self.independent_lanes[kind as usize].actual_capacity = capacity;
        }
        #[cfg(test)]
        if old != capacity {
            self.observe_physical_walker();
        }
        let lane = &mut self.lanes[kind as usize];
        if old != capacity {
            lane.capacity_growths = counters.1;
            lane.peak_bytes = lane.peak_bytes.max(
                capacity
                    .checked_mul(kind.slot_size())
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            );
            #[cfg(test)]
            {
                self.independent_lanes[kind as usize].capacity_growths = counters.3;
                self.independent_lanes[kind as usize].peak_bytes = lane.peak_bytes;
            }
        }
        self.observe_memo(memo_bytes)
    }

    fn reserve_raw_map(
        &mut self,
        map: &mut HashMap<u32, (f5c_draft::PositiveId, f5c_draft::NegativeId)>,
        memo_bytes: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let kind = F5cWalkerLaneKind::RawOwnerBounds;
        let counters = self.preflight_table_counters(kind)?;
        let old = map.capacity();
        let result = map.try_reserve(1);
        self.observe_table_capacity(kind, old, map.capacity(), memo_bytes, counters)?;
        result.map_err(|_| SolveAvailabilityError::IdentityExhausted)
    }

    fn reserve_retained_map(
        &mut self,
        map: &mut HashMap<u32, (f5c_draft::PositiveId, f5c_draft::NegativeId)>,
        memo_bytes: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let kind = F5cWalkerLaneKind::RetainedOwnerBounds;
        let counters = self.preflight_table_counters(kind)?;
        let old = map.capacity();
        let result = map.try_reserve(1);
        self.observe_table_capacity(kind, old, map.capacity(), memo_bytes, counters)?;
        result.map_err(|_| SolveAvailabilityError::IdentityExhausted)
    }

    fn reserve_post_r_set<T: Eq + std::hash::Hash>(
        &mut self,
        set: &mut HashSet<T>,
        kind: F5cWalkerLaneKind,
        memo_bytes: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let counters = self.preflight_table_counters(kind)?;
        let old = set.capacity();
        let result = set.try_reserve(1);
        self.observe_table_capacity(kind, old, set.capacity(), memo_bytes, counters)?;
        result.map_err(|_| SolveAvailabilityError::IdentityExhausted)
    }

    fn reserve_post_r_map(
        &mut self,
        map: &mut HashMap<u32, u32>,
        kind: F5cWalkerLaneKind,
        memo_bytes: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let counters = self.preflight_table_counters(kind)?;
        let old = map.capacity();
        let result = map.try_reserve(1);
        self.observe_table_capacity(kind, old, map.capacity(), memo_bytes, counters)?;
        result.map_err(|_| SolveAvailabilityError::IdentityExhausted)
    }

    fn reserve_raw_set(
        &mut self,
        set: &mut HashSet<u32>,
        memo_bytes: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let kind = F5cWalkerLaneKind::RawOwnerSeen;
        let counters = self.preflight_table_counters(kind)?;
        let old = set.capacity();
        let result = set.try_reserve(1);
        self.observe_table_capacity(kind, old, set.capacity(), memo_bytes, counters)?;
        result.map_err(|_| SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn reserve_set(
        &mut self,
        buffer: &mut HashSet<u32>,
        memo_bytes: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let kind = F5cWalkerLaneKind::DirectTargets;
        let index = kind as usize;
        let requested = self.lanes[index]
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let growth = self.lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_requested = self.independent_lanes[index]
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_growth = self.independent_lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let old_capacity = buffer.capacity();
        let reservation = buffer.try_reserve(1);
        let new_capacity = buffer.capacity();
        self.lanes[index].requested_slots = requested;
        self.lanes[index].actual_capacity = new_capacity;
        #[cfg(test)]
        {
            self.independent_lanes[index].requested_slots = independent_requested;
            self.independent_lanes[index].actual_capacity = new_capacity;
            if new_capacity != old_capacity {
                self.observe_physical_walker();
            }
        }
        if new_capacity != old_capacity {
            self.lanes[index].capacity_growths = growth;
            self.lanes[index].peak_bytes = self.lanes[index].peak_bytes.max(
                new_capacity
                    .checked_mul(kind.slot_size())
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            );
            #[cfg(test)]
            {
                self.independent_lanes[index].capacity_growths = independent_growth;
                self.independent_lanes[index].peak_bytes =
                    self.independent_lanes[index].peak_bytes.max(
                        new_capacity
                            .checked_mul(std::mem::size_of::<u32>())
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?,
                    );
            }
            self.observe_memo(memo_bytes)?;
            self.observed_memo_bytes = memo_bytes;
        }
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        Ok(())
    }

    pub(super) fn reserve_physical_set_insert(
        &mut self,
        buffer: &mut HashSet<u32>,
        kind: F5cWalkerLaneKind,
        memo_bytes: usize,
        needs_growth: bool,
    ) -> Result<(), SolveAvailabilityError> {
        if !needs_growth {
            return Ok(());
        }
        let index = kind as usize;
        let growth = self.lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_growth = self.independent_lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let old = buffer.capacity();
        let reservation = buffer.try_reserve(1);
        let capacity = buffer.capacity();
        let aggregate = matches!(kind, F5cWalkerLaneKind::ClosureNeighbors);
        #[cfg(test)]
        if capacity != old {
            self.observe_physical_walker_target(
                kind,
                if aggregate {
                    self.independent_lanes[index].actual_capacity as u128 + (capacity - old) as u128
                } else {
                    capacity as u128
                },
            );
        }
        let current = self.lanes[index].actual_capacity;
        let new_capacity = if aggregate {
            current
                .checked_add(capacity.saturating_sub(old))
                .ok_or(SolveAvailabilityError::IdentityExhausted)?
        } else {
            capacity
        };
        self.lanes[index].actual_capacity = new_capacity;
        #[cfg(test)]
        {
            self.independent_lanes[index].actual_capacity = new_capacity;
            if capacity != old {
                self.observe_physical_walker();
            }
        }
        if capacity != old {
            self.lanes[index].capacity_growths = growth;
            self.lanes[index].peak_bytes = self.lanes[index].peak_bytes.max(
                new_capacity
                    .checked_mul(kind.slot_size())
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            );
            #[cfg(test)]
            {
                self.independent_lanes[index].capacity_growths = independent_growth;
                self.independent_lanes[index].peak_bytes = self.lanes[index].peak_bytes;
            }
            self.observe_memo(memo_bytes)?;
            self.observed_memo_bytes = memo_bytes;
        }
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        Ok(())
    }

    fn record_physical_set_attempt(
        &mut self,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError> {
        let index = kind as usize;
        let requested = self.lanes[index]
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_requested = self.independent_lanes[index]
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.lanes[index].requested_slots = requested;
        #[cfg(test)]
        {
            self.independent_lanes[index].requested_slots = independent_requested;
        }
        Ok(())
    }

    pub(super) fn reserve<T>(
        &mut self,
        buffer: &mut Vec<T>,
        kind: F5cWalkerLaneKind,
        additional: usize,
        memo_bytes: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let index = kind as usize;
        let requested = self.lanes[index]
            .requested_slots
            .checked_add(additional)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let growth = self.lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_requested = self.independent_lanes[index]
            .requested_slots
            .checked_add(additional)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_growth = self.independent_lanes[index]
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        if matches!(kind, F5cWalkerLaneKind::Values) {
            self.value_slot_size = std::mem::size_of::<T>();
        }
        let slot_size = if matches!(kind, F5cWalkerLaneKind::Values) {
            self.value_slot_size
        } else {
            kind.slot_size()
        };
        let old_capacity = self.lanes[index].actual_capacity;
        let reservation = buffer.try_reserve(additional);
        let new_capacity = buffer.capacity();
        self.lanes[index].requested_slots = requested;
        self.lanes[index].actual_capacity = new_capacity;
        #[cfg(test)]
        {
            self.independent_lanes[index].requested_slots = independent_requested;
            self.independent_lanes[index].actual_capacity = new_capacity;
            if new_capacity != old_capacity {
                self.observe_physical_walker();
            }
        }
        if new_capacity != old_capacity {
            self.lanes[index].capacity_growths = growth;
            self.lanes[index].peak_bytes = self.lanes[index].peak_bytes.max(
                new_capacity
                    .checked_mul(slot_size)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            );
            #[cfg(test)]
            {
                self.independent_lanes[index].capacity_growths = independent_growth;
                self.independent_lanes[index].peak_bytes =
                    self.independent_lanes[index].peak_bytes.max(
                        buffer
                            .capacity()
                            .checked_mul(std::mem::size_of::<T>())
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?,
                    );
            }
            self.observe_memo(memo_bytes)?;
            self.observed_memo_bytes = memo_bytes;
        }
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        Ok(())
    }

    pub(super) fn release(&mut self, kind: F5cWalkerLaneKind) {
        #[cfg(test)]
        let prior_capacity = self.independent_lanes[kind as usize].actual_capacity;
        self.lanes[kind as usize].actual_capacity = 0;
        #[cfg(test)]
        {
            self.independent_lanes[kind as usize].actual_capacity = 0;
            if prior_capacity != 0 {
                self.observe_physical_walker();
            }
        }
    }

    pub(super) fn requested_slots(&self) -> Result<usize, SolveAvailabilityError> {
        let walker = self.lanes.iter().try_fold(0usize, |sum, lane| {
            sum.checked_add(lane.requested_slots)
                .ok_or(SolveAvailabilityError::IdentityExhausted)
        })?;
        let candidate = self
            .flat_candidate_lanes
            .iter()
            .try_fold(0usize, |sum, lane| {
                sum.checked_add(lane.requested_slots)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)
            })?;
        walker
            .checked_add(candidate)
            .and_then(|total| total.checked_sub(self.flat_batch_excluded_requests))
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn actual_capacity(&self) -> Result<usize, SolveAvailabilityError> {
        self.lanes.iter().try_fold(0usize, |sum, lane| {
            sum.checked_add(lane.actual_capacity)
                .ok_or(SolveAvailabilityError::IdentityExhausted)
        })
    }

    pub(super) fn capacity_growths(&self) -> Result<usize, SolveAvailabilityError> {
        self.lanes.iter().try_fold(0usize, |sum, lane| {
            sum.checked_add(lane.capacity_growths)
                .ok_or(SolveAvailabilityError::IdentityExhausted)
        })
    }

    pub(super) fn retained_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        self.lanes
            .iter()
            .enumerate()
            .try_fold(0usize, |sum, (index, lane)| {
                let kind = F5cWalkerLaneKind::ALL[index];
                let size = if matches!(kind, F5cWalkerLaneKind::Values) && self.value_slot_size != 0
                {
                    self.value_slot_size
                } else {
                    kind.slot_size()
                };
                sum.checked_add(
                    lane.actual_capacity
                        .checked_mul(size)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?,
                )
                .ok_or(SolveAvailabilityError::IdentityExhausted)
            })
    }

    pub(super) fn observe_memo_with_source(
        &mut self,
        memo_bytes: usize,
        source_meter: &DraftHeapMeter,
    ) -> Result<(), SolveAvailabilityError> {
        self.observed_source_bytes = source_meter.current_bytes();
        self.observe_memo(memo_bytes)?;
        let external = memo_bytes
            .checked_add(self.retained_bytes()?)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(not(test))]
        source_meter
            .observe_component_external(external)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        {
            #[cfg(feature = "f5c_resource_probe")]
            source_meter.observe_family6_walker(
                usize::try_from(self.physical_joint.walker_current)
                    .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                self.physical_joint.walker_capacities.iter().try_fold(0usize,
                    |sum, capacity| sum.checked_add(usize::try_from(*capacity).ok()?))
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            );
            let physical = usize::try_from(
                self.physical_joint
                    .memo_current
                    .checked_add(self.physical_joint.walker_current)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            )
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            source_meter
                .observe_component_external_pair(external, physical)
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        }
        Ok(())
    }

    pub(super) fn observe_memo(&mut self, memo_bytes: usize) -> Result<(), SolveAvailabilityError> {
        let scratch_bytes = self.retained_bytes()?;
        self.peak_bytes = self.peak_bytes.max(scratch_bytes);
        self.simultaneous_memo_peak_bytes = self.simultaneous_memo_peak_bytes.max(
            memo_bytes
                .checked_add(scratch_bytes)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        );
        let joint = self
            .observed_source_bytes
            .ok_or(SolveAvailabilityError::IdentityExhausted)?
            .checked_add(memo_bytes)
            .and_then(|bytes| bytes.checked_add(scratch_bytes))
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.simultaneous_source_memo_peak_bytes =
            self.simultaneous_source_memo_peak_bytes.max(joint);
        #[cfg(test)]
        {
            let sizes = F5cWalkerLaneKind::ALL.map(|kind| {
                if matches!(kind, F5cWalkerLaneKind::Values) && self.value_slot_size != 0 {
                    self.value_slot_size
                } else {
                    kind.slot_size()
                }
            });
            let bytes = self.independent_lanes.iter().zip(sizes).try_fold(
                0usize,
                |sum, (lane, size)| {
                    sum.checked_add(
                        lane.actual_capacity
                            .checked_mul(size)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?,
                    )
                    .ok_or(SolveAvailabilityError::IdentityExhausted)
                },
            )?;
            self.independent_peak_bytes = self.independent_peak_bytes.max(bytes);
            self.independent_simultaneous_memo_peak_bytes =
                self.independent_simultaneous_memo_peak_bytes.max(
                    memo_bytes
                        .checked_add(bytes)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?,
                );
        }
        Ok(())
    }
}

#[derive(Default)]
pub(super) struct F5cComponentExpansionMemo {
    pub(super) work_meter: F5cDraftWorkMeter,
    pub(super) roots: HashMap<F5cExpansionKey, F5cSummaryNodeId>,
    pub(super) nodes: Vec<F5cSummaryNode>,
    pub(super) children: Vec<F5cSummaryNodeId>,
    pub(super) parent_heads: Vec<Option<usize>>,
    pub(super) reverse_parents: Vec<F5cReverseParentEdge>,
    pub(super) incidence_heads: HashMap<u32, Option<usize>>,
    pub(super) incidences: Vec<F5cIncidenceEdge>,
    pub(super) root_heads: Vec<Option<usize>>,
    pub(super) root_edges: Vec<F5cRootEdge>,
    pub(super) root_edge_marks: Vec<u32>,
    pub(super) root_edge_mark_epoch: u32,
    pub(super) root_undo: Vec<F5cRootUndo>,
    pub(super) active_rows: HashMap<u32, usize>,
    pub(super) active_conflicts: HashMap<F5cExpansionKey, usize>,
    pub(super) work: Vec<F5cSummaryNodeId>,
    pub(super) conflict_journal: Vec<(F5cExpansionKey, usize)>,
    pub(super) visit_epochs: Vec<u32>,
    pub(super) visit_epoch: u32,
    pub(super) root_lane: F5cMemoLane,
    pub(super) node_lane: F5cMemoLane,
    pub(super) child_lane: F5cMemoLane,
    pub(super) index_lane: F5cMemoLane,
    pub(super) scratch_lane: F5cMemoLane,
    pub(super) walker_resources: F5cWalkerResources,
    pub(super) generalizer_scratch_capacities: [usize; 4],
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) matrix_active: bool,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) matrix_lanes: [F5cMatrixMemoLane; 20],
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) matrix_generalizer_lengths: [usize; 4],
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) matrix_peak_bytes: usize,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) matrix_group_peak_bytes: [usize; 5],
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) matrix_group_peak_capacity: [usize; 5],
    pub(super) simultaneous_peak_bytes: usize,
    pub(super) observed_source_bytes: Option<usize>,
    pub(super) simultaneous_source_memo_peak_bytes: usize,
    source_meter_overflow: bool,
    #[cfg(test)]
    pub(super) capacity_samples: Vec<[usize; 20]>,
    #[cfg(test)]
    pub(super) checked_materialization_scratch_sample: Option<[usize; 13]>,
    #[cfg(test)]
    pub(super) boxed_materialization_callback_trace: Vec<(u32, Polarity)>,
    #[cfg(test)]
    pub(super) boxed_raw_lanes_live_sample: Option<([usize; 6], [usize; 6])>,
    #[cfg(test)]
    pub(super) recursive_bound_physical_samples: Vec<([u128; 4], u128, u128, u128)>,
    #[cfg(test)]
    pub(super) parts_physical_events: [PartsPhysicalEvent; 2],
    #[cfg(test)]
    pub(super) parts_census_enabled: bool,
    #[cfg(test)]
    pub(super) parts_census_source_capacities: std::cell::Cell<[usize; 2]>,
    #[cfg(test)]
    pub(super) parts_census_samples: std::cell::RefCell<Vec<PartsCensusSample>>,
    #[cfg(test)]
    pub(super) independent_joint_peak_bytes: std::cell::Cell<u128>,
    #[cfg(test)]
    pub(super) source_owner_current: u128,
    #[cfg(test)]
    pub(super) transfer_raw_staged_samples: Vec<(u128, u128, u128)>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) matrix_transfer_raw_staged: Option<(u128, u128, u128)>,
    #[cfg(test)]
    pub(super) transfer_physical_samples: Vec<(u128, u128, u128, u128, u128)>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) matrix_transfer_physical: Option<(u128, u128, u128, u128, u128)>,
    #[cfg(test)]
    pub(super) transfer_live_capacity_samples: Vec<([u128; 4], [usize; 20], [usize; 98], usize)>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) matrix_transfer_live_capacity: Option<([u128; 4], [usize; 20], [usize; 98], usize)>,
    #[cfg(test)]
    pub(super) transfer_raw_capacity_samples: Vec<[usize; 9]>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) matrix_transfer_raw_capacity: Option<[usize; 9]>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) matrix_transfer_count: usize,
    #[cfg(test)]
    pub(super) flat_candidate_physical_peaks: Vec<f5c_normalization::FlatCandidatePhysicalPeak>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) matrix_flat_candidate_peaks:
        [Option<f5c_normalization::FlatCandidatePhysicalPeak>; 2],
    #[cfg(test)]
    pub(super) recursive_bound_reserves: Vec<(usize, usize, usize)>,
    #[cfg(test)]
    pub(super) post_r_temporary_live_samples: Vec<(F5cWalkerLaneKind, usize, usize)>,
    #[cfg(test)]
    pub(super) r_fixed_point_live_sample: Option<([usize; 6], [usize; 6])>,
    #[cfg(test)]
    pub(super) independent_generalizer_scratch_peak_bytes: usize,
    #[cfg(test)]
    pub(super) fail_observation_at: Option<F5cTestObservationFailure>,
    #[cfg(test)]
    pub(super) fail_reserve_at: Option<(F5cTestReserveFailure, usize)>,
    #[cfg(test)]
    pub(super) pending_observation_failure: bool,
    #[cfg(test)]
    pub(super) independent_root_growths: usize,
    #[cfg(test)]
    pub(super) independent_node_growths: usize,
    #[cfg(test)]
    pub(super) independent_child_growths: usize,
    #[cfg(test)]
    pub(super) independent_index_growths: usize,
    #[cfg(test)]
    pub(super) independent_scratch_growths: usize,
    #[cfg(test)]
    pub(super) independent_index_requests: usize,
    #[cfg(test)]
    pub(super) independent_scratch_requests: usize,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) matrix_owner_events: crate::f5c_draft_heap::ComponentMemoEvents,
}

impl F5cComponentExpansionMemo {
    #[cfg(test)]
    fn record_post_r_sample(&mut self, sample: (F5cWalkerLaneKind, usize, usize)) {
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if self.matrix_active { return; }
        self.post_r_temporary_live_samples.push(sample);
    }
    #[cfg(test)]
    pub(super) fn live_capacity_snapshot(&self) -> [usize; 20] {
        [
            self.roots.capacity(),
            self.nodes.capacity(),
            self.children.capacity(),
            self.parent_heads.capacity(),
            self.reverse_parents.capacity(),
            self.incidence_heads.capacity(),
            self.incidences.capacity(),
            self.root_heads.capacity(),
            self.root_edges.capacity(),
            self.root_edge_marks.capacity(),
            self.root_undo.capacity(),
            self.active_rows.capacity(),
            self.active_conflicts.capacity(),
            self.work.capacity(),
            self.conflict_journal.capacity(),
            self.visit_epochs.capacity(),
            self.generalizer_scratch_capacities[0],
            self.generalizer_scratch_capacities[1],
            self.generalizer_scratch_capacities[2],
            self.generalizer_scratch_capacities[3],
        ]
    }

    #[cfg(test)]
    fn parts_census_memo_bytes(&self) -> Option<u128> {
        let sizes = [
            std::mem::size_of::<(F5cExpansionKey, F5cSummaryNodeId)>(),
            std::mem::size_of::<F5cSummaryNode>(),
            std::mem::size_of::<F5cSummaryNodeId>(),
            std::mem::size_of::<Option<usize>>(),
            std::mem::size_of::<F5cReverseParentEdge>(),
            std::mem::size_of::<(u32, Option<usize>)>(),
            std::mem::size_of::<F5cIncidenceEdge>(),
            std::mem::size_of::<Option<usize>>(),
            std::mem::size_of::<F5cRootEdge>(),
            std::mem::size_of::<u32>(),
            std::mem::size_of::<F5cRootUndo>(),
            std::mem::size_of::<(u32, usize)>(),
            std::mem::size_of::<(F5cExpansionKey, usize)>(),
            std::mem::size_of::<F5cSummaryNodeId>(),
            std::mem::size_of::<(F5cExpansionKey, usize)>(),
            std::mem::size_of::<u32>(),
            std::mem::size_of::<F5cExpansionFrame>(),
            std::mem::size_of::<(u32, Polarity, usize)>(),
            std::mem::size_of::<(u32, Polarity)>(),
            std::mem::size_of::<u32>(),
        ];
        self.live_capacity_snapshot()
            .into_iter()
            .zip(sizes)
            .try_fold(0u128, |total, (capacity, size)| {
                total.checked_add((capacity as u128).checked_mul(size as u128)?)
            })
    }

    #[cfg(test)]
    pub(super) fn observe_physical_memo(&mut self) {
        let capacities = [
            self.roots.capacity(),
            self.nodes.capacity(),
            self.children.capacity(),
            self.parent_heads.capacity(),
            self.reverse_parents.capacity(),
            self.incidence_heads.capacity(),
            self.incidences.capacity(),
            self.root_heads.capacity(),
            self.root_edges.capacity(),
            self.root_edge_marks.capacity(),
            self.root_undo.capacity(),
            self.active_rows.capacity(),
            self.active_conflicts.capacity(),
            self.work.capacity(),
            self.conflict_journal.capacity(),
            self.visit_epochs.capacity(),
            self.generalizer_scratch_capacities[0],
            self.generalizer_scratch_capacities[1],
            self.generalizer_scratch_capacities[2],
            self.generalizer_scratch_capacities[3],
        ];
        let sizes = [
            std::mem::size_of::<(F5cExpansionKey, F5cSummaryNodeId)>(),
            std::mem::size_of::<F5cSummaryNode>(),
            std::mem::size_of::<F5cSummaryNodeId>(),
            std::mem::size_of::<Option<usize>>(),
            std::mem::size_of::<F5cReverseParentEdge>(),
            std::mem::size_of::<(u32, Option<usize>)>(),
            std::mem::size_of::<F5cIncidenceEdge>(),
            std::mem::size_of::<Option<usize>>(),
            std::mem::size_of::<F5cRootEdge>(),
            std::mem::size_of::<u32>(),
            std::mem::size_of::<F5cRootUndo>(),
            std::mem::size_of::<(u32, usize)>(),
            std::mem::size_of::<(F5cExpansionKey, usize)>(),
            std::mem::size_of::<F5cSummaryNodeId>(),
            std::mem::size_of::<(F5cExpansionKey, usize)>(),
            std::mem::size_of::<u32>(),
            std::mem::size_of::<F5cExpansionFrame>(),
            std::mem::size_of::<(u32, Polarity, usize)>(),
            std::mem::size_of::<(u32, Polarity)>(),
            std::mem::size_of::<u32>(),
        ];
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if self.matrix_active {
            let lengths = [
                self.roots.len(), self.nodes.len(), self.children.len(),
                self.parent_heads.len(), self.reverse_parents.len(),
                self.incidence_heads.len(), self.incidences.len(),
                self.root_heads.len(), self.root_edges.len(),
                self.root_edge_marks.len(), self.root_undo.len(),
                self.active_rows.len(), self.active_conflicts.len(), self.work.len(),
                self.conflict_journal.len(), self.visit_epochs.len(),
                self.matrix_generalizer_lengths[0], self.matrix_generalizer_lengths[1],
                self.matrix_generalizer_lengths[2], self.matrix_generalizer_lengths[3],
            ];
            let mut total = 0usize;
            for (index, lane) in self.matrix_lanes.iter_mut().enumerate() {
                let capacity = capacities[index];
                let bytes = capacity.checked_mul(sizes[index]).expect("matrix memo lane bytes");
                self.matrix_owner_events.observe(index, lengths[index].min(capacity), capacity, sizes[index]);
                if capacity > lane.actual_capacity { lane.growths += 1; }
                if lengths[index] == 0 && lane.requested_slots > 0 { lane.cleared = true; }
                lane.requested_slots = lengths[index];
                lane.actual_capacity = capacity;
                lane.slot_size = sizes[index];
                lane.retained_bytes = bytes;
                lane.peak_bytes = lane.peak_bytes.max(bytes);
                total = total.checked_add(bytes).expect("matrix memo bytes");
            }
            self.matrix_peak_bytes = self.matrix_peak_bytes.max(total);
            for (group, range) in [0..1, 1..2, 2..3, 3..11, 11..20].into_iter().enumerate() {
                let capacity = capacities[range.clone()].iter().try_fold(0usize,
                    |sum, value| sum.checked_add(*value)).expect("matrix group capacity");
                let bytes = capacities[range.clone()].iter().zip(&sizes[range])
                    .try_fold(0usize, |sum, (capacity, size)|
                        capacity.checked_mul(*size).and_then(|value| sum.checked_add(value)))
                    .expect("matrix group bytes");
                self.matrix_group_peak_capacity[group] =
                    self.matrix_group_peak_capacity[group].max(capacity);
                self.matrix_group_peak_bytes[group] = self.matrix_group_peak_bytes[group].max(bytes);
            }
        }
        self.walker_resources.physical_joint.memo_current = PhysicalJoint::sum_products(
            capacities
                .into_iter()
                .zip(sizes)
                .map(|(capacity, size)| (capacity as u128, size)),
        )
        .unwrap_or_else(|| {
            self.walker_resources.physical_joint.aggregate_overflow = true;
            u128::MAX
        });
        self.walker_resources.physical_joint.pair();
    }
    #[cfg(test)]
    pub(super) fn observe_physical_source(
        &mut self,
        outer_capacity: usize,
        sidecar_capacity: usize,
        active_bound_capacity: usize,
    ) {
        let joint = &mut self.walker_resources.physical_joint;
        joint.source_capacities[0] = outer_capacity as u128;
        joint.source_capacities[1] = sidecar_capacity as u128;
        joint.source_capacities[3] = active_bound_capacity as u128;
        joint.source_event();
    }

    #[cfg(test)]
    pub(super) fn release_physical_source(&mut self) {
        self.source_owner_current = 0;
        let joint = &mut self.walker_resources.physical_joint;
        joint.source_capacities = [0; 4];
        joint.source_nested_bytes = 0;
        joint.source_event();
    }

    #[cfg(test)]
    fn observe_physical_active_bound(&mut self, capacity: usize) {
        let joint = &mut self.walker_resources.physical_joint;
        joint.source_capacities[3] = capacity as u128;
        joint.source_event();
        self.capture_recursive_bound_physical_sample();
    }

    #[cfg(test)]
    fn transfer_physical_bound(&mut self, capacity: usize) {
        let joint = &mut self.walker_resources.physical_joint;
        joint.source_capacities[2] = joint.source_capacities[2]
            .checked_add(capacity as u128)
            .unwrap_or_else(|| {
                joint.aggregate_overflow = true;
                u128::MAX
            });
        joint.source_capacities[3] = 0;
        joint.source_event();
        self.capture_recursive_bound_physical_sample();
    }

    #[cfg(test)]
    fn capture_recursive_bound_physical_sample(&mut self) {
        let joint = &self.walker_resources.physical_joint;
        self.recursive_bound_physical_samples.push((
            joint.source_capacities,
            joint.memo_current,
            joint.walker_current,
            joint.source_current,
        ));
    }

    pub(super) fn observe_source_bytes(
        &mut self,
        source: Option<usize>,
    ) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        self.observe_physical_memo();
        self.observed_source_bytes = source;
        self.walker_resources.observed_source_bytes = source;
        self.source_meter_overflow = source.is_none();
        source.ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let memo_bytes = self.retained_bytes()?;
        self.observe_simultaneous_peak()?;
        self.walker_resources.observe_memo(memo_bytes)
    }

    pub(super) fn observe_source_meter(
        &mut self,
        source_meter: &DraftHeapMeter,
    ) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        {
            let joint = &mut self.walker_resources.physical_joint;
            let sizes = [
                std::mem::size_of::<GeneralizationDraft>(),
                std::mem::size_of::<TrackedAllocation<'static>>(),
                std::mem::size_of::<F5cRecursiveBound>(),
                std::mem::size_of::<F5cRecursiveBound>(),
            ];
            let fixed =
                PhysicalJoint::sum_products(joint.source_capacities.iter().copied().zip(sizes))
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let owned = source_meter
                .physical_current_bytes()
                .ok_or(SolveAvailabilityError::IdentityExhausted)? as u128;
            // Flat staging has its own source lane and uses a separate meter.
            // The boxed source lanes are explicitly active only while at least
            // one of their fixed owner capacities is present.
            self.source_owner_current = if joint.source_capacities == [0; 4] {
                0
            } else {
                owned
            };
            joint.source_nested_bytes = self
                .source_owner_current
                .checked_sub(fixed)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            joint.source_event();
        }
        self.observe_source_bytes(source_meter.current_bytes())?;
        self.observe_component_external(source_meter)
    }

    pub(super) fn observe_component_external(
        &self,
        source_meter: &DraftHeapMeter,
    ) -> Result<(), SolveAvailabilityError> {
        let external = self
            .retained_bytes()?
            .checked_add(self.walker_resources.retained_bytes()?)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(not(test))]
        source_meter
            .observe_component_external(external)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        {
            let joint = &self.walker_resources.physical_joint;
            #[cfg(feature = "f5c_resource_probe")]
            source_meter.observe_family6_walker(
                usize::try_from(joint.walker_current)
                    .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                joint.walker_capacities.iter().try_fold(0usize,
                    |sum, capacity| sum.checked_add(usize::try_from(*capacity).ok()?))
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            );
            let physical_external = usize::try_from(
                joint
                    .memo_current
                    .checked_add(joint.walker_current)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            )
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            source_meter
                .observe_component_external_pair(external, physical_external)
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        }
        #[cfg(test)]
        self.sample_independent_joint(source_meter);
        Ok(())
    }

    #[cfg(test)]
    fn sample_independent_joint(&self, source_meter: &DraftHeapMeter) {
        let joint = &self.walker_resources.physical_joint;
        let total = source_meter
            .physical_current_bytes()
            .map(|bytes| bytes as u128)
            .and_then(|source| source.checked_add(joint.memo_current))
            .and_then(|sum| sum.checked_add(joint.walker_current))
            .unwrap_or(u128::MAX);
        self.independent_joint_peak_bytes
            .set(self.independent_joint_peak_bytes.get().max(total));
        if self.parts_census_enabled {
            let source = self.parts_census_source_capacities.get();
            let source_bytes = (source[0] as u128)
                .checked_mul(std::mem::size_of::<F5cPositive>() as u128)
                .and_then(|positive| {
                    (source[1] as u128)
                        .checked_mul(std::mem::size_of::<F5cNegative>() as u128)
                        .and_then(|negative| positive.checked_add(negative))
                });
            let memo_bytes = self.parts_census_memo_bytes();
            let walker_bytes = self
                .walker_resources
                .independent_lanes
                .iter()
                .zip(F5cWalkerLaneKind::ALL)
                .try_fold(0u128, |total, (lane, kind)| {
                    let slot_size = if matches!(kind, F5cWalkerLaneKind::Values)
                        && self.walker_resources.value_slot_size != 0
                    {
                        self.walker_resources.value_slot_size
                    } else {
                        kind.slot_size()
                    };
                    total
                        .checked_add((lane.actual_capacity as u128).checked_mul(slot_size as u128)?)
                });
            let components = source_bytes
                .zip(memo_bytes)
                .zip(walker_bytes)
                .map(|((source, memo), walker)| [source, memo, walker]);
            let total =
                components.and_then(|parts| parts.into_iter().try_fold(0u128, u128::checked_add));
            let lane_capacities = [
                self.walker_resources.independent_lanes[F5cWalkerLaneKind::PositiveParts as usize]
                    .actual_capacity,
                self.walker_resources.independent_lanes[F5cWalkerLaneKind::NegativeParts as usize]
                    .actual_capacity,
            ];
            self.parts_census_samples
                .borrow_mut()
                .push(PartsCensusSample {
                    components,
                    total,
                    source_capacities: source,
                    lane_capacities,
                    logical_peak: source_meter.component_joint_peak(),
                    physical_peak: source_meter.physical_component_joint_peak(),
                });
        }
    }

    #[cfg(test)]
    fn mark_census_parts_adopted(&self, kind: F5cWalkerLaneKind, capacity: usize) {
        if self.parts_census_enabled {
            let mut capacities = self.parts_census_source_capacities.get();
            capacities[Self::parts_index(kind)] = capacity;
            self.parts_census_source_capacities.set(capacities);
        }
    }

    #[cfg(test)]
    pub(super) fn observe_census_parts_drop(
        &self,
        kind: F5cWalkerLaneKind,
        source_meter: &DraftHeapMeter,
    ) {
        assert!(self.parts_census_enabled);
        let mut capacities = self.parts_census_source_capacities.get();
        capacities[Self::parts_index(kind)] = 0;
        self.parts_census_source_capacities.set(capacities);
        self.sample_independent_joint(source_meter);
    }

    pub(super) fn capture_component_joint_peak(
        &mut self,
        source_meter: &DraftHeapMeter,
    ) -> Result<(), SolveAvailabilityError> {
        self.observe_component_external(source_meter)?;
        self.simultaneous_source_memo_peak_bytes = self.simultaneous_source_memo_peak_bytes.max(
            source_meter
                .component_joint_peak()
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        );
        #[cfg(test)]
        {
            let physical_peak = source_meter
                .physical_component_joint_peak()
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            self.walker_resources.physical_joint.peak = self
                .walker_resources
                .physical_joint
                .peak
                .max(physical_peak as u128);
        }
        Ok(())
    }
    pub(super) fn reserve_walker<T>(
        &mut self,
        buffer: &mut Vec<T>,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError> {
        let memo_bytes = self.retained_bytes()?;
        self.walker_resources.reserve(buffer, kind, 1, memo_bytes)
    }

    pub(super) fn reserve_walker_with_source<T>(
        &mut self,
        buffer: &mut Vec<T>,
        kind: F5cWalkerLaneKind,
        source_meter: &DraftHeapMeter,
    ) -> Result<(), SolveAvailabilityError> {
        let prior_capacity = self.walker_resources.lanes[kind as usize].actual_capacity;
        self.observed_source_bytes = source_meter.current_bytes();
        self.walker_resources.observed_source_bytes = source_meter.current_bytes();
        self.source_meter_overflow = source_meter.current_bytes().is_none();
        let reservation = self.reserve_walker(buffer, kind);
        if self.walker_resources.lanes[kind as usize].actual_capacity != prior_capacity {
            #[cfg(test)]
            if matches!(
                kind,
                F5cWalkerLaneKind::PositiveParts | F5cWalkerLaneKind::NegativeParts
            ) {
                self.observe_parts_physical(kind, buffer.capacity(), source_meter, false);
            }
            self.observe_walker_with_source(source_meter)?;
            #[cfg(test)]
            if matches!(
                kind,
                F5cWalkerLaneKind::PositiveParts | F5cWalkerLaneKind::NegativeParts
            ) {
                if self.fail_reserve_at
                    == Some((F5cTestReserveFailure::PartsAfterReserve(kind as usize), 0))
                {
                    self.fail_reserve_at = None;
                    let event = &mut self.parts_physical_events[Self::parts_index(kind)];
                    event.failed_reserves += 1;
                    event.failed_expected_bytes = event.expected_peak_bytes;
                    event.failed_components = event.growth_components;
                    return Err(SolveAvailabilityError::IdentityExhausted);
                }
            }
        }
        reservation
    }

    #[cfg(test)]
    fn parts_index(kind: F5cWalkerLaneKind) -> usize {
        match kind {
            F5cWalkerLaneKind::PositiveParts => 0,
            F5cWalkerLaneKind::NegativeParts => 1,
            _ => unreachable!("parts event kind"),
        }
    }

    #[cfg(test)]
    fn observe_parts_physical(
        &mut self,
        kind: F5cWalkerLaneKind,
        capacity: usize,
        source_meter: &DraftHeapMeter,
        transferred: bool,
    ) {
        let event = &mut self.parts_physical_events[Self::parts_index(kind)];
        if transferred {
            event.transfers += 1;
            event.transfer_capacity = capacity;
        } else if capacity != 0 {
            event.growths += 1;
        }
        event.live_capacity = if transferred { 0 } else { capacity };
        event.peak_capacity = event.peak_capacity.max(capacity);
        let joint = &self.walker_resources.physical_joint;
        let raw_parts_bytes = if transferred {
            0
        } else {
            (capacity as u128)
                .checked_mul(kind.slot_size() as u128)
                .unwrap_or(u128::MAX)
        };
        let other_walker_bytes = joint
            .walker_current
            .checked_sub(raw_parts_bytes)
            .unwrap_or(u128::MAX);
        let source_bytes = source_meter
            .physical_current_bytes()
            .map(|bytes| bytes as u128)
            .unwrap_or(u128::MAX);
        let total = source_bytes
            .checked_add(joint.memo_current)
            .and_then(|sum| sum.checked_add(other_walker_bytes))
            .and_then(|sum| sum.checked_add(raw_parts_bytes))
            .unwrap_or(u128::MAX);
        let components = [
            source_bytes,
            joint.memo_current,
            other_walker_bytes,
            raw_parts_bytes,
        ];
        if transferred {
            event.transfer_components = components;
        } else if capacity != 0 {
            event.growth_components = components;
        }
        event.expected_peak_bytes = event.expected_peak_bytes.max(total);
        if transferred {
            event.transfer_joint_bytes = total;
        } else if capacity != 0 {
            event.growth_joint_bytes = total;
        }
        event.peak_joint_bytes = event.peak_joint_bytes.max(total);
        self.sample_independent_joint(source_meter);
    }

    pub(super) fn release_walker_with_source(
        &mut self,
        kind: F5cWalkerLaneKind,
        source_meter: &DraftHeapMeter,
    ) -> Result<(), SolveAvailabilityError> {
        let prior_capacity = self.walker_resources.lanes[kind as usize].actual_capacity;
        self.walker_resources.release(kind);
        #[cfg(test)]
        if prior_capacity != 0
            && matches!(
                kind,
                F5cWalkerLaneKind::PositiveParts | F5cWalkerLaneKind::NegativeParts
            )
        {
            self.observe_parts_physical(kind, 0, source_meter, false);
        }
        if prior_capacity == 0 {
            return Ok(());
        }
        #[cfg(test)]
        if kind as usize == F5cWalkerLaneKind::ClosureAdjacency as usize
            && self.fail_observation_at == Some(F5cTestObservationFailure::ClosureRelease)
        {
            self.fail_observation_at = None;
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let memo_bytes = self.retained_bytes()?;
        let result = self
            .walker_resources
            .observe_memo_with_source(memo_bytes, source_meter);
        #[cfg(test)]
        self.sample_independent_joint(source_meter);
        result
    }

    fn release_reentry_path_with_source(
        &mut self,
        capacity: usize,
        source_meter: &DraftHeapMeter,
    ) -> Result<(), SolveAvailabilityError> {
        self.walker_resources.release_reentry_path(capacity);
        self.observe_walker_with_source(source_meter)
    }

    pub(super) fn reserve_walker_target(
        &mut self,
        targets: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        let memo_bytes = self.retained_bytes()?;
        self.walker_resources.reserve_set(targets, memo_bytes)
    }

    pub(super) fn insert_physical_set(
        &mut self,
        set: &mut HashSet<u32>,
        value: u32,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError> {
        self.reserve_physical_set_insert(set, value, kind)?;
        // HashSet::insert may grow a full table before it finds a duplicate.
        if set.len() < set.capacity() || !set.contains(&value) {
            set.insert(value);
        }
        Ok(())
    }

    pub(super) fn insert_physical_set_with_source(
        &mut self,
        set: &mut HashSet<u32>,
        value: u32,
        kind: F5cWalkerLaneKind,
        source_meter: &DraftHeapMeter,
    ) -> Result<(), SolveAvailabilityError> {
        let prior_capacity = self.walker_resources.lanes[kind as usize].actual_capacity;
        let insertion = self.insert_physical_set(set, value, kind);
        if self.walker_resources.lanes[kind as usize].actual_capacity != prior_capacity {
            self.observe_walker_with_source(source_meter)?;
        }
        insertion
    }

    pub(super) fn insert_physical_set_observed(
        &mut self,
        set: &mut HashSet<u32>,
        value: u32,
        kind: F5cWalkerLaneKind,
        source_meter: Option<&DraftHeapMeter>,
    ) -> Result<(), SolveAvailabilityError> {
        if let Some(meter) = source_meter {
            self.insert_physical_set_with_source(set, value, kind, meter)
        } else {
            self.insert_physical_set(set, value, kind)
        }
    }

    fn reserve_physical_set_insert(
        &mut self,
        set: &mut HashSet<u32>,
        value: u32,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError> {
        // Memo capacity may have changed since the last walker observation.
        // Reconcile it only when this insertion can grow the physical table.
        self.walker_resources.record_physical_set_attempt(kind)?;
        let full = set.len() == set.capacity();
        let duplicate = full && set.contains(&value);
        let memo_bytes = if full && !duplicate {
            self.retained_bytes()?
        } else {
            self.walker_resources.observed_memo_bytes
        };
        if duplicate {
            return Ok(());
        }
        self.walker_resources
            .reserve_physical_set_insert(set, kind, memo_bytes, full)
    }

    pub(super) fn reserve_physical_set_insert_with_source(
        &mut self,
        set: &mut HashSet<u32>,
        value: u32,
        kind: F5cWalkerLaneKind,
        source_meter: &DraftHeapMeter,
    ) -> Result<(), SolveAvailabilityError> {
        let prior_capacity = self.walker_resources.lanes[kind as usize].actual_capacity;
        let reservation = self.reserve_physical_set_insert(set, value, kind);
        if self.walker_resources.lanes[kind as usize].actual_capacity != prior_capacity {
            self.observe_walker_with_source(source_meter)?;
        }
        reservation
    }

    pub(super) fn observe_walker(&mut self) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        if std::mem::take(&mut self.pending_observation_failure) {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let memo_bytes = self.retained_bytes()?;
        if memo_bytes != self.walker_resources.observed_memo_bytes {
            self.walker_resources.observe_memo(memo_bytes)?;
            self.walker_resources.observed_memo_bytes = memo_bytes;
        }
        Ok(())
    }

    pub(super) fn observe_walker_with_source(
        &mut self,
        source_meter: &DraftHeapMeter,
    ) -> Result<(), SolveAvailabilityError> {
        self.observed_source_bytes = source_meter.current_bytes();
        self.walker_resources.observed_source_bytes = source_meter.current_bytes();
        self.source_meter_overflow = source_meter.current_bytes().is_none();
        let result = self.observe_walker();
        let memo_bytes = self.retained_bytes()?;
        self.walker_resources
            .observe_memo_with_source(memo_bytes, source_meter)?;
        #[cfg(test)]
        self.sample_independent_joint(source_meter);
        result
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn observe_walker_capacity_change_with_source(
        &mut self,
        source_meter: Option<&DraftHeapMeter>,
        old_capacity: usize,
        new_capacity: usize,
    ) -> Result<(), SolveAvailabilityError> {
        if old_capacity != new_capacity && let Some(source_meter) = source_meter {
            self.observe_walker_with_source(source_meter)?;
        }
        Ok(())
    }

    fn prepare_index_reserve(
        &self,
        requested: usize,
    ) -> Result<(usize, usize), SolveAvailabilityError> {
        Ok((
            self.index_lane
                .requested_slots
                .checked_add(requested)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            self.index_lane
                .capacity_growths
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        ))
    }

    fn reserve_root_undo(&mut self) -> Result<(), SolveAvailabilityError> {
        checked_next_root_lane_len(self.root_undo.len())?;
        self.reserve_root_undo_prechecked()
    }

    fn reserve_root_undo_prechecked(&mut self) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        if self.fail_reserve_at == Some((F5cTestReserveFailure::RootUndo, self.root_undo.len())) {
            self.fail_reserve_at = None;
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let (requested, growth) = self.prepare_index_reserve(1)?;
        let old = self.root_undo.capacity();
        let reservation = self.root_undo.try_reserve(1);
        #[cfg(test)]
        self.observe_physical_memo();
        let actual = self.root_undo.capacity();
        self.commit_index_reserve(requested, growth, old, actual)?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)
    }

    fn commit_index_reserve(
        &mut self,
        requested: usize,
        growth_if_changed: usize,
        old_capacity: usize,
        new_capacity: usize,
    ) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        let (independent_requests, independent_growths) = (
            self.independent_index_requests
                .checked_add(requested - self.index_lane.requested_slots)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            self.independent_index_growths
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        );
        self.index_lane.requested_slots = requested;
        if old_capacity != new_capacity {
            self.index_lane.capacity_growths = growth_if_changed;
            #[cfg(test)]
            {
                self.independent_index_growths = independent_growths;
            }
        }
        #[cfg(test)]
        {
            self.independent_index_requests = independent_requests;
        }
        if old_capacity != new_capacity {
            self.index_lane.peak_bytes =
                self.index_lane.peak_bytes.max(self.index_retained_bytes()?);
            self.observe_simultaneous_peak()?;
        }
        Ok(())
    }

    fn prepare_scratch_reserve(
        &self,
        requested: usize,
    ) -> Result<(usize, usize), SolveAvailabilityError> {
        Ok((
            self.scratch_lane
                .requested_slots
                .checked_add(requested)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            self.scratch_lane
                .capacity_growths
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        ))
    }

    fn commit_scratch_reserve(
        &mut self,
        requested: usize,
        growth_if_changed: usize,
        old_capacity: usize,
        new_capacity: usize,
    ) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        let (independent_requests, independent_growths) = (
            self.independent_scratch_requests
                .checked_add(requested - self.scratch_lane.requested_slots)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            self.independent_scratch_growths
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        );
        self.scratch_lane.requested_slots = requested;
        if old_capacity != new_capacity {
            self.scratch_lane.capacity_growths = growth_if_changed;
            #[cfg(test)]
            {
                self.independent_scratch_growths = independent_growths;
            }
        }
        #[cfg(test)]
        {
            self.independent_scratch_requests = independent_requests;
        }
        if old_capacity != new_capacity {
            self.scratch_lane.peak_bytes = self
                .scratch_lane
                .peak_bytes
                .max(self.scratch_retained_bytes()?);
            #[cfg(test)]
            {
                self.independent_generalizer_scratch_peak_bytes = self
                    .independent_generalizer_scratch_peak_bytes
                    .max(self.scratch_retained_bytes()?);
            }
            self.observe_simultaneous_peak()?;
        }
        Ok(())
    }

    fn observe_simultaneous_peak(&mut self) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        self.observe_physical_memo();
        let retained = self.retained_bytes()?;
        self.simultaneous_peak_bytes = self.simultaneous_peak_bytes.max(retained);
        let source = if self.source_meter_overflow {
            return Err(SolveAvailabilityError::IdentityExhausted);
        } else {
            self.observed_source_bytes.unwrap_or(0)
        };
        let joint = source
            .checked_add(retained)
            .and_then(|bytes| bytes.checked_add(self.walker_resources.retained_bytes().ok()?))
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.simultaneous_source_memo_peak_bytes =
            self.simultaneous_source_memo_peak_bytes.max(joint);
        #[cfg(test)]
        {
        #[cfg(feature = "f5c_resource_probe")]
        let record_capacity_history = !self.matrix_active;
        #[cfg(not(feature = "f5c_resource_probe"))]
        let record_capacity_history = true;
        if record_capacity_history { self.capacity_samples.push([
            self.roots.capacity(),
            self.nodes.capacity(),
            self.children.capacity(),
            self.parent_heads.capacity(),
            self.reverse_parents.capacity(),
            self.incidence_heads.capacity(),
            self.incidences.capacity(),
            self.root_heads.capacity(),
            self.root_edges.capacity(),
            self.root_edge_marks.capacity(),
            self.root_undo.capacity(),
            self.active_rows.capacity(),
            self.active_conflicts.capacity(),
            self.work.capacity(),
            self.conflict_journal.capacity(),
            self.visit_epochs.capacity(),
            self.generalizer_scratch_capacities[0],
            self.generalizer_scratch_capacities[1],
            self.generalizer_scratch_capacities[2],
            self.generalizer_scratch_capacities[3],
        ]); }
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn positive_node(
        &mut self,
        value: &F5cPositive,
        incidence: Option<(u32, Polarity)>,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        self.node_iterative(F5cSummaryTask::Positive(value, incidence), None)
    }

    fn positive_node_with_source(
        &mut self,
        value: &F5cPositive,
        incidence: Option<(u32, Polarity)>,
        source_meter: &DraftHeapMeter,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        self.node_iterative(
            F5cSummaryTask::Positive(value, incidence),
            Some(source_meter),
        )
    }

    #[cfg(test)]
    pub(super) fn negative_node(
        &mut self,
        value: &F5cNegative,
        incidence: Option<(u32, Polarity)>,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        self.node_iterative(F5cSummaryTask::Negative(value, incidence), None)
    }

    fn negative_node_with_source(
        &mut self,
        value: &F5cNegative,
        incidence: Option<(u32, Polarity)>,
        source_meter: &DraftHeapMeter,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        self.node_iterative(
            F5cSummaryTask::Negative(value, incidence),
            Some(source_meter),
        )
    }

    fn node_iterative(
        &mut self,
        first: F5cSummaryTask<'_, '_>,
        source_meter: Option<&DraftHeapMeter>,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut tasks_owner = source_meter.map(|meter| RawWalkerOwner::new(
            meter, F5cWalkerLaneKind::SummaryTasks as usize,
            F5cWalkerLaneKind::SummaryTasks.slot_size()));
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut ids_owner = source_meter.map(|meter| RawWalkerOwner::new(
            meter, F5cWalkerLaneKind::SummaryIds as usize,
            F5cWalkerLaneKind::SummaryIds.slot_size()));
        let mut tasks = Vec::new();
        let mut ids = Vec::<F5cSummaryNodeId>::new();
        macro_rules! push_task {
            ($value:expr) => {{
                let value = $value;
                self.work_meter.charge(1)?;
                let prior_capacity = tasks.capacity();
                let reservation = self.reserve_walker(&mut tasks, F5cWalkerLaneKind::SummaryTasks);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = tasks_owner.as_mut() { owner.observe(tasks.len(), tasks.capacity()); }
                if tasks.capacity() != prior_capacity {
                    if let Some(meter) = source_meter {
                        self.observe_component_external(meter)?;
                    }
                }
                reservation?;
                tasks.push(value);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = tasks_owner.as_mut() { owner.observe(tasks.len(), tasks.capacity()); }
            }};
        }
        macro_rules! push_id {
            ($value:expr) => {{
                self.work_meter.charge(1)?;
                let value =
                    (|| -> Result<F5cSummaryNodeId, SolveAvailabilityError> { Ok($value) })();
                if let Some(meter) = source_meter {
                    self.observe_component_external(meter)?;
                }
                let value: F5cSummaryNodeId = value?;
                self.observe_walker()?;
                let prior_capacity = ids.capacity();
                let reservation = self.reserve_walker(&mut ids, F5cWalkerLaneKind::SummaryIds);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = ids_owner.as_mut() { owner.observe(ids.len(), ids.capacity()); }
                if ids.capacity() != prior_capacity {
                    if let Some(meter) = source_meter {
                        self.observe_component_external(meter)?;
                    }
                }
                reservation?;
                ids.push(value);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = ids_owner.as_mut() { owner.observe(ids.len(), ids.capacity()); }
            }};
        }
        macro_rules! push_children {
            ($ids:expr) => {{
                let reservation = self.push_children($ids);
                if let Some(meter) = source_meter {
                    self.observe_component_external(meter)?;
                }
                reservation?
            }};
        }
        macro_rules! pop_id {
            () => {{
                let value = ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = ids_owner.as_mut() { owner.observe(ids.len(), ids.capacity()); }
                value
            }};
        }
        let result = (|| {
            push_task!(first);
            while !tasks.is_empty() {
                self.work_meter.charge(1)?;
                let task = tasks.pop().expect("nonempty summary tasks");
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = tasks_owner.as_mut() { owner.observe(tasks.len(), tasks.capacity()); }
                match task {
                    F5cSummaryTask::Positive(value, incidence) => match value {
                        F5cPositive::Bottom => {
                            push_id!(self.push_node(F5cSummaryNodeKind::PositiveBottom, incidence)?)
                        }
                        F5cPositive::Int => {
                            push_id!(self.push_node(F5cSummaryNodeKind::PositiveInt, incidence)?)
                        }
                        F5cPositive::Unit => {
                            push_id!(self.push_node(F5cSummaryNodeKind::PositiveUnit, incidence)?)
                        }
                        F5cPositive::Variable(row) => push_id!(
                            self.push_node(F5cSummaryNodeKind::PositiveRow(*row), incidence)?
                        ),
                        F5cPositive::Shared(id) => {
                            if incidence.is_some() {
                                let (start, _) = push_children!(&[*id]);
                                push_id!(self.push_node(
                                    F5cSummaryNodeKind::PositiveAlias { start },
                                    incidence
                                )?);
                            } else {
                                push_id!(*id);
                            }
                        }
                        F5cPositive::Union(children) => {
                            push_task!(F5cSummaryTask::PositiveUnion(ids.len(), incidence));
                            for child in children.iter().rev() {
                                self.work_meter.charge(1)?;
                                push_task!(F5cSummaryTask::Positive(child, None));
                            }
                        }
                        F5cPositive::Function {
                            argument, result, ..
                        } => {
                            push_task!(F5cSummaryTask::PositiveFunction(incidence));
                            self.work_meter.charge(1)?;
                            push_task!(F5cSummaryTask::Positive(result, None));
                            self.work_meter.charge(1)?;
                            push_task!(F5cSummaryTask::Negative(argument, None));
                        }
                        F5cPositive::Quantified(_) | F5cPositive::Recursive(_) => {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        }
                    },
                    F5cSummaryTask::Negative(value, incidence) => match value {
                        F5cNegative::Top => {
                            push_id!(self.push_node(F5cSummaryNodeKind::NegativeTop, incidence)?)
                        }
                        F5cNegative::Bottom => {
                            push_id!(self.push_node(F5cSummaryNodeKind::NegativeBottom, incidence)?)
                        }
                        F5cNegative::Int => {
                            push_id!(self.push_node(F5cSummaryNodeKind::NegativeInt, incidence)?)
                        }
                        F5cNegative::Unit => {
                            push_id!(self.push_node(F5cSummaryNodeKind::NegativeUnit, incidence)?)
                        }
                        F5cNegative::Variable(row) => push_id!(
                            self.push_node(F5cSummaryNodeKind::NegativeRow(*row), incidence)?
                        ),
                        F5cNegative::Shared(id) => {
                            if incidence.is_some() {
                                let (start, _) = push_children!(&[*id]);
                                push_id!(self.push_node(
                                    F5cSummaryNodeKind::NegativeAlias { start },
                                    incidence
                                )?);
                            } else {
                                push_id!(*id);
                            }
                        }
                        F5cNegative::Intersection(children) => {
                            push_task!(F5cSummaryTask::NegativeIntersection(ids.len(), incidence));
                            for child in children.iter().rev() {
                                self.work_meter.charge(1)?;
                                push_task!(F5cSummaryTask::Negative(child, None));
                            }
                        }
                        F5cNegative::Function {
                            argument, result, ..
                        } => {
                            push_task!(F5cSummaryTask::NegativeFunction(incidence));
                            self.work_meter.charge(1)?;
                            push_task!(F5cSummaryTask::Negative(result, None));
                            self.work_meter.charge(1)?;
                            push_task!(F5cSummaryTask::Positive(argument, None));
                        }
                        F5cNegative::Quantified(_) | F5cNegative::Recursive(_) => {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        }
                    },
                    F5cSummaryTask::PositiveUnion(start, incidence) => {
                        let (child_start, len) = push_children!(&ids[start..]);
                        ids.truncate(start);
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = ids_owner.as_mut() { owner.observe(ids.len(), ids.capacity()); }
                        push_id!(self.push_node(
                            F5cSummaryNodeKind::PositiveUnion {
                                start: child_start,
                                len
                            },
                            incidence
                        )?);
                    }
                    F5cSummaryTask::NegativeIntersection(start, incidence) => {
                        let (child_start, len) = push_children!(&ids[start..]);
                        ids.truncate(start);
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = ids_owner.as_mut() { owner.observe(ids.len(), ids.capacity()); }
                        push_id!(self.push_node(
                            F5cSummaryNodeKind::NegativeIntersection {
                                start: child_start,
                                len
                            },
                            incidence
                        )?);
                    }
                    F5cSummaryTask::PositiveFunction(incidence) => {
                        let result = pop_id!();
                        let argument =
                            pop_id!();
                        push_id!(self.push_node(
                            F5cSummaryNodeKind::PositiveFunction { argument, result },
                            incidence
                        )?);
                    }
                    F5cSummaryTask::NegativeFunction(incidence) => {
                        let result = pop_id!();
                        let argument =
                            pop_id!();
                        push_id!(self.push_node(
                            F5cSummaryNodeKind::NegativeFunction { argument, result },
                            incidence
                        )?);
                    }
                }
            }
            if ids.len() != 1 {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            let result = ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            if let Some(owner) = ids_owner.as_mut() { owner.observe(ids.len(), ids.capacity()); }
            result
        })();
        self.walker_resources
            .release(F5cWalkerLaneKind::SummaryTasks);
        self.walker_resources.release(F5cWalkerLaneKind::SummaryIds);
        if let Some(meter) = source_meter {
            self.observe_component_external(meter)?;
        }
        result
    }

    pub(super) fn child_slice(
        &self,
        start: u32,
        len: u32,
    ) -> Result<&[F5cSummaryNodeId], SolveAvailabilityError> {
        let start =
            usize::try_from(start).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let len = usize::try_from(len).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let end = start
            .checked_add(len)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.children
            .get(start..end)
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    #[cfg(test)]
    pub(super) fn positive_value<'meter>(
        &mut self,
        source_meter: &'meter DraftHeapMeter,
        id: F5cSummaryNodeId,
    ) -> Result<F5cPositive<'meter>, SolveAvailabilityError> {
        self.positive_value_with(source_meter, id, &mut |_, _| Ok(()))
    }

    pub(super) fn positive_value_with<'meter>(
        &mut self,
        source_meter: &'meter DraftHeapMeter,
        id: F5cSummaryNodeId,
        mark: &mut impl FnMut(u32, Polarity) -> Result<(), SolveAvailabilityError>,
    ) -> Result<F5cPositive<'meter>, SolveAvailabilityError> {
        self.observe_component_external(source_meter)?;
        match self.materialize_summary(source_meter, F5cMaterializeTask::Positive(id), mark)? {
            F5cWalkValue::Positive(value, _) => Ok(value),
            _ => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    #[cfg(test)]
    pub(super) fn negative_value<'meter>(
        &mut self,
        source_meter: &'meter DraftHeapMeter,
        id: F5cSummaryNodeId,
    ) -> Result<F5cNegative<'meter>, SolveAvailabilityError> {
        self.negative_value_with(source_meter, id, &mut |_, _| Ok(()))
    }

    pub(super) fn negative_value_with<'meter>(
        &mut self,
        source_meter: &'meter DraftHeapMeter,
        id: F5cSummaryNodeId,
        mark: &mut impl FnMut(u32, Polarity) -> Result<(), SolveAvailabilityError>,
    ) -> Result<F5cNegative<'meter>, SolveAvailabilityError> {
        self.observe_component_external(source_meter)?;
        match self.materialize_summary(source_meter, F5cMaterializeTask::Negative(id), mark)? {
            F5cWalkValue::Negative(value, _) => Ok(value),
            _ => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    fn materialize_summary<'meter>(
        &mut self,
        source_meter: &'meter DraftHeapMeter,
        first: F5cMaterializeTask,
        mark: &mut impl FnMut(u32, Polarity) -> Result<(), SolveAvailabilityError>,
    ) -> Result<F5cWalkValue<'meter>, SolveAvailabilityError> {
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut tasks_owner = RawWalkerOwner::new(source_meter,
            F5cWalkerLaneKind::MaterializeTasks as usize,
            F5cWalkerLaneKind::MaterializeTasks.slot_size());
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut values_owner = RawWalkerOwner::new(source_meter,
            F5cWalkerLaneKind::MaterializeValues as usize,
            F5cWalkerLaneKind::MaterializeValues.slot_size());
        let mut tasks = Vec::new();
        let mut values = Vec::new();
        macro_rules! push_task {
            ($task:expr) => {{
                let task = $task;
                self.work_meter.charge(1)?; // scheduled task
                let reservation = self.reserve_walker_with_source(
                    &mut tasks,
                    F5cWalkerLaneKind::MaterializeTasks,
                    source_meter,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                tasks_owner.observe(tasks.len(), tasks.capacity());
                reservation?;
                tasks.push(task);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                tasks_owner.observe(tasks.len(), tasks.capacity());
            }};
        }
        macro_rules! push_value {
            ($value:expr) => {{
                self.work_meter.charge(1)?; // emitted value
                let value = $value;
                let reservation = self.reserve_walker_with_source(
                    &mut values,
                    F5cWalkerLaneKind::MaterializeValues,
                    source_meter,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                values_owner.observe(values.len(), values.capacity());
                reservation?;
                values.push(value);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                values_owner.observe(values.len(), values.capacity());
            }};
        }
        macro_rules! pop_value {
            () => {{
                let value = values.pop().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                values_owner.observe(values.len(), values.capacity());
                value
            }};
        }
        let result = (|| {
            push_task!(first);
            while !tasks.is_empty() {
                self.work_meter.charge(1)?; // popped task
                let task = tasks.pop().expect("nonempty materialization tasks");
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                tasks_owner.observe(tasks.len(), tasks.capacity());
                match task {
                    F5cMaterializeTask::Positive(id) | F5cMaterializeTask::Negative(id) => {
                        let node = self.node(id)?;
                        if let Some((row, polarity)) = node.incidence {
                            #[cfg(test)]
                            self.boxed_materialization_callback_trace
                                .push((row, polarity));
                            mark(row, polarity)?;
                        }
                        match (task, node.kind) {
                            (
                                F5cMaterializeTask::Positive(_),
                                F5cSummaryNodeKind::PositiveBottom,
                            ) => push_value!(F5cWalkValue::Positive(F5cPositive::Bottom, true)),
                            (F5cMaterializeTask::Positive(_), F5cSummaryNodeKind::PositiveInt) => {
                                push_value!(F5cWalkValue::Positive(F5cPositive::Int, true))
                            }
                            (F5cMaterializeTask::Positive(_), F5cSummaryNodeKind::PositiveUnit) => {
                                push_value!(F5cWalkValue::Positive(F5cPositive::Unit, true))
                            }
                            (
                                F5cMaterializeTask::Positive(_),
                                F5cSummaryNodeKind::PositiveRow(row),
                            ) => push_value!(F5cWalkValue::Positive(
                                F5cPositive::Variable(row),
                                true
                            )),
                            (F5cMaterializeTask::Negative(_), F5cSummaryNodeKind::NegativeTop) => {
                                push_value!(F5cWalkValue::Negative(F5cNegative::Top, true))
                            }
                            (
                                F5cMaterializeTask::Negative(_),
                                F5cSummaryNodeKind::NegativeBottom,
                            ) => push_value!(F5cWalkValue::Negative(F5cNegative::Bottom, true)),
                            (F5cMaterializeTask::Negative(_), F5cSummaryNodeKind::NegativeInt) => {
                                push_value!(F5cWalkValue::Negative(F5cNegative::Int, true))
                            }
                            (F5cMaterializeTask::Negative(_), F5cSummaryNodeKind::NegativeUnit) => {
                                push_value!(F5cWalkValue::Negative(F5cNegative::Unit, true))
                            }
                            (
                                F5cMaterializeTask::Negative(_),
                                F5cSummaryNodeKind::NegativeRow(row),
                            ) => push_value!(F5cWalkValue::Negative(
                                F5cNegative::Variable(row),
                                true
                            )),
                            (
                                F5cMaterializeTask::Positive(_),
                                F5cSummaryNodeKind::PositiveAlias { start },
                            ) => {
                                let child = self.child_slice(start, 1)?[0];
                                self.work_meter.charge(1)?; // inspected alias edge
                                push_task!(F5cMaterializeTask::Positive(child));
                            }
                            (
                                F5cMaterializeTask::Negative(_),
                                F5cSummaryNodeKind::NegativeAlias { start },
                            ) => {
                                let child = self.child_slice(start, 1)?[0];
                                self.work_meter.charge(1)?; // inspected alias edge
                                push_task!(F5cMaterializeTask::Negative(child));
                            }
                            (
                                F5cMaterializeTask::Positive(_),
                                F5cSummaryNodeKind::PositiveUnion { start, len },
                            ) => {
                                push_task!(F5cMaterializeTask::PositiveUnion(values.len()));
                                let count = self.child_slice(start, len)?.len();
                                for index in (0..count).rev() {
                                    self.work_meter.charge(1)?; // inspected child edge
                                    let child = self.child_slice(start, len)?[index];
                                    push_task!(F5cMaterializeTask::Positive(child));
                                }
                            }
                            (
                                F5cMaterializeTask::Negative(_),
                                F5cSummaryNodeKind::NegativeIntersection { start, len },
                            ) => {
                                push_task!(F5cMaterializeTask::NegativeIntersection(values.len()));
                                let count = self.child_slice(start, len)?.len();
                                for index in (0..count).rev() {
                                    self.work_meter.charge(1)?; // inspected child edge
                                    let child = self.child_slice(start, len)?[index];
                                    push_task!(F5cMaterializeTask::Negative(child));
                                }
                            }
                            (
                                F5cMaterializeTask::Positive(_),
                                F5cSummaryNodeKind::PositiveFunction { argument, result },
                            ) => {
                                self.work_meter.charge(2)?; // argument and result edges
                                push_task!(F5cMaterializeTask::PositiveFunction);
                                push_task!(F5cMaterializeTask::Positive(result));
                                push_task!(F5cMaterializeTask::Negative(argument));
                            }
                            (
                                F5cMaterializeTask::Negative(_),
                                F5cSummaryNodeKind::NegativeFunction { argument, result },
                            ) => {
                                self.work_meter.charge(2)?; // argument and result edges
                                push_task!(F5cMaterializeTask::NegativeFunction);
                                push_task!(F5cMaterializeTask::Negative(result));
                                push_task!(F5cMaterializeTask::Positive(argument));
                            }
                            _ => return Err(SolveAvailabilityError::IdentityExhausted),
                        }
                    }
                    F5cMaterializeTask::PositiveUnion(start) => {
                        // The finish task follows only positive child tasks; each child
                        // leaves one value, so this suffix is exactly their results.
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        let mut raw_owner = RawWalkerOwner::new(source_meter,
                            F5cWalkerLaneKind::PositiveParts as usize,
                            std::mem::size_of::<F5cPositive>());
                        let mut parts = Vec::new();
                        let count = values
                            .len()
                            .checked_sub(start)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        #[cfg(test)]
                        record_bulk_drain_boundary(
                            F5cBulkDrainSite::SummaryPositive,
                            &self.work_meter,
                            count,
                        );
                        self.work_meter.charge(count)?;
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        let capacity = values.capacity();
                        let drained = values.drain(start..);
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        values_owner.observe(start, capacity);
                        for child in drained {
                            let F5cWalkValue::Positive(value, _) = child else {
                                return Err(SolveAvailabilityError::IdentityExhausted);
                            };
                            let reservation = self.reserve_walker_with_source(
                                &mut parts,
                                F5cWalkerLaneKind::PositiveParts,
                                source_meter,
                            );
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            raw_owner.observe(parts.len(), parts.capacity());
                            reservation?;
                            parts.push(value);
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            raw_owner.observe(parts.len(), parts.capacity());
                        }
                        self.observe_component_external(source_meter)?;
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        let adopted = TrackedVec::try_adopt_raw_from_walker_with_owner(
                            source_meter, parts, PhysicalOwnerKind::UnionChildren, raw_owner);
                        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                        let adopted = TrackedVec::try_adopt_raw_from_walker_with_kind(
                            source_meter, parts, PhysicalOwnerKind::UnionChildren);
                        let parts = match adopted {
                            Ok(parts) => parts,
                            Err((parts, raw_owner)) => {
                                drop(parts);
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                drop(raw_owner);
                                #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                                let _ = raw_owner;
                                self.release_walker_with_source(
                                    F5cWalkerLaneKind::PositiveParts,
                                    source_meter,
                                )?;
                                return Err(SolveAvailabilityError::IdentityExhausted);
                            }
                        };
                        #[cfg(test)]
                        self.mark_census_parts_adopted(
                            F5cWalkerLaneKind::PositiveParts,
                            parts.capacity(),
                        );
                        self.release_walker_with_source(
                            F5cWalkerLaneKind::PositiveParts,
                            source_meter,
                        )?;
                        #[cfg(test)]
                        self.observe_parts_physical(
                            F5cWalkerLaneKind::PositiveParts,
                            parts.capacity(),
                            source_meter,
                            true,
                        );
                        push_value!(F5cWalkValue::Positive(F5cPositive::Union(parts), true));
                    }
                    F5cMaterializeTask::NegativeIntersection(start) => {
                        // The finish task follows only negative child tasks; each child
                        // leaves one value, so this suffix is exactly their results.
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        let mut raw_owner = RawWalkerOwner::new(source_meter,
                            F5cWalkerLaneKind::NegativeParts as usize,
                            std::mem::size_of::<F5cNegative>());
                        let mut parts = Vec::new();
                        let count = values
                            .len()
                            .checked_sub(start)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        #[cfg(test)]
                        record_bulk_drain_boundary(
                            F5cBulkDrainSite::SummaryNegative,
                            &self.work_meter,
                            count,
                        );
                        self.work_meter.charge(count)?;
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        let capacity = values.capacity();
                        let drained = values.drain(start..);
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        values_owner.observe(start, capacity);
                        for child in drained {
                            let F5cWalkValue::Negative(value, _) = child else {
                                return Err(SolveAvailabilityError::IdentityExhausted);
                            };
                            let reservation = self.reserve_walker_with_source(
                                &mut parts,
                                F5cWalkerLaneKind::NegativeParts,
                                source_meter,
                            );
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            raw_owner.observe(parts.len(), parts.capacity());
                            reservation?;
                            parts.push(value);
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            raw_owner.observe(parts.len(), parts.capacity());
                        }
                        self.observe_component_external(source_meter)?;
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        let adopted = TrackedVec::try_adopt_raw_from_walker_with_owner(
                            source_meter, parts, PhysicalOwnerKind::IntersectionChildren, raw_owner);
                        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                        let adopted = TrackedVec::try_adopt_raw_from_walker_with_kind(
                            source_meter, parts, PhysicalOwnerKind::IntersectionChildren);
                        let parts = match adopted {
                            Ok(parts) => parts,
                            Err((parts, raw_owner)) => {
                                drop(parts);
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                drop(raw_owner);
                                #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                                let _ = raw_owner;
                                self.release_walker_with_source(
                                    F5cWalkerLaneKind::NegativeParts,
                                    source_meter,
                                )?;
                                return Err(SolveAvailabilityError::IdentityExhausted);
                            }
                        };
                        #[cfg(test)]
                        self.mark_census_parts_adopted(
                            F5cWalkerLaneKind::NegativeParts,
                            parts.capacity(),
                        );
                        self.release_walker_with_source(
                            F5cWalkerLaneKind::NegativeParts,
                            source_meter,
                        )?;
                        #[cfg(test)]
                        self.observe_parts_physical(
                            F5cWalkerLaneKind::NegativeParts,
                            parts.capacity(),
                            source_meter,
                            true,
                        );
                        push_value!(F5cWalkValue::Negative(
                            F5cNegative::Intersection(parts),
                            true
                        ));
                    }
                    F5cMaterializeTask::PositiveFunction => {
                        let F5cWalkValue::Positive(result, _) = pop_value!()
                        else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        let F5cWalkValue::Negative(argument, _) = pop_value!()
                        else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        push_value!(F5cWalkValue::Positive(
                            F5cPositive::Function {
                                argument: TrackedOne::try_new_with_kind(source_meter, argument,
                                    PhysicalOwnerKind::PositiveFunctionArgument)
                                    .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                                argument_effect: F5cNegativeEffect::Empty,
                                result_effect: F5cPositiveEffect::Bottom,
                                result: TrackedOne::try_new_with_kind(source_meter, result,
                                    PhysicalOwnerKind::PositiveFunctionResult)
                                    .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                            },
                            true
                        ));
                    }
                    F5cMaterializeTask::NegativeFunction => {
                        let F5cWalkValue::Negative(result, _) = pop_value!()
                        else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        let F5cWalkValue::Positive(argument, _) = pop_value!()
                        else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        push_value!(F5cWalkValue::Negative(
                            F5cNegative::Function {
                                argument: TrackedOne::try_new_with_kind(source_meter, argument,
                                    PhysicalOwnerKind::NegativeFunctionArgument)
                                    .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                                argument_effect: F5cPositiveEffect::Bottom,
                                result_effect: F5cNegativeEffect::Empty,
                                result: TrackedOne::try_new_with_kind(source_meter, result,
                                    PhysicalOwnerKind::NegativeFunctionResult)
                                    .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                            },
                            true
                        ));
                    }
                }
            }
            if values.len() != 1 {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            let result = values.pop().ok_or(SolveAvailabilityError::IdentityExhausted);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            values_owner.observe(values.len(), values.capacity());
            result
        })();
        self.release_walker_with_source(F5cWalkerLaneKind::MaterializeTasks, source_meter)?;
        self.release_walker_with_source(F5cWalkerLaneKind::MaterializeValues, source_meter)?;
        self.release_walker_with_source(F5cWalkerLaneKind::PositiveParts, source_meter)?;
        self.release_walker_with_source(F5cWalkerLaneKind::NegativeParts, source_meter)?;
        result
    }

    pub(super) fn node(
        &self,
        id: F5cSummaryNodeId,
    ) -> Result<F5cSummaryNode, SolveAvailabilityError> {
        self.nodes
            .get(id.0 as usize)
            .copied()
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn begin_visit(&mut self) -> Result<(), SolveAvailabilityError> {
        self.work.clear();
        #[cfg(test)]
        self.observe_physical_memo();
        if self.visit_epoch == u32::MAX {
            self.work_meter.charge(self.visit_epochs.len())?;
            self.visit_epochs.fill(0);
            self.visit_epoch = 1;
        } else {
            self.visit_epoch += 1;
        }
        Ok(())
    }

    pub(super) fn queue_once(
        &mut self,
        id: F5cSummaryNodeId,
    ) -> Result<(), SolveAvailabilityError> {
        let index = id.0 as usize;
        let mark = *self
            .visit_epochs
            .get(index)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        if mark != self.visit_epoch {
            self.work_meter.charge(1)?;
            let (requested, growth_if_changed) = self.prepare_scratch_reserve(1)?;
            let old = self.work.capacity();
            let reservation = self.work.try_reserve(1);
            #[cfg(test)]
            self.observe_physical_memo();
            self.commit_scratch_reserve(requested, growth_if_changed, old, self.work.capacity())?;
            reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            self.visit_epochs[index] = self.visit_epoch;
            self.work.push(id);
            #[cfg(test)]
            self.observe_physical_memo();
        }
        Ok(())
    }

    pub(super) fn seed_row(&mut self, row: u32) -> Result<(), SolveAvailabilityError> {
        let mut edge = self.incidence_heads.get(&row).copied().flatten();
        while let Some(index) = edge {
            self.work_meter.charge(1)?;
            let incidence = *self
                .incidences
                .get(index)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            self.queue_once(incidence.node)?;
            edge = incidence.next;
        }
        Ok(())
    }

    fn propagate_active_row(
        &mut self,
        row: u32,
        entering: bool,
    ) -> Result<(), SolveAvailabilityError> {
        self.conflict_journal.clear();
        #[cfg(test)]
        self.observe_physical_memo();
        let (journal_requested, journal_growth) = self.prepare_scratch_reserve(self.roots.len())?;
        #[cfg(test)]
        if self.fail_reserve_at == Some((F5cTestReserveFailure::ConflictJournal, self.roots.len()))
        {
            self.fail_reserve_at = None;
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let old_journal_capacity = self.conflict_journal.capacity();
        let reservation = self.conflict_journal.try_reserve(self.roots.len());
        #[cfg(test)]
        self.observe_physical_memo();
        self.commit_scratch_reserve(
            journal_requested,
            journal_growth,
            old_journal_capacity,
            self.conflict_journal.capacity(),
        )?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.begin_visit()?;
        if self.root_edge_mark_epoch == u32::MAX {
            self.work_meter.charge(self.root_edge_marks.len())?;
            self.root_edge_marks.fill(0);
            self.root_edge_mark_epoch = 1;
        } else {
            self.root_edge_mark_epoch += 1;
        }
        self.seed_row(row)?;
        while !self.work.is_empty() {
            self.work_meter.charge(1)?;
            let id = self.work.pop().expect("nonempty memo work");
            #[cfg(test)]
            self.observe_physical_memo();
            let mut root_edge = *self
                .root_heads
                .get(id.0 as usize)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            while let Some(index) = root_edge {
                self.work_meter.charge(1)?;
                let edge = *self
                    .root_edges
                    .get(index)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                if edge.live {
                    let prior = self.active_conflicts.get(&edge.key).copied().unwrap_or(0);
                    let mark = self
                        .root_edge_marks
                        .get_mut(index)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    if *mark != self.root_edge_mark_epoch {
                        if entering {
                            prior
                                .checked_add(1)
                                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        } else if prior == 0 {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        }
                        self.work_meter.charge(1)?; // copied conflict-journal entry
                        *mark = self.root_edge_mark_epoch;
                        self.conflict_journal.push((edge.key, prior));
                        #[cfg(test)]
                        self.observe_physical_memo();
                    }
                }
                root_edge = edge.next;
            }
            let mut parent_edge = *self
                .parent_heads
                .get(id.0 as usize)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            while let Some(index) = parent_edge {
                self.work_meter.charge(1)?;
                let edge = *self
                    .reverse_parents
                    .get(index)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                self.queue_once(edge.parent)?;
                parent_edge = edge.next;
            }
        }
        if entering {
            let (requested, growth) = self.prepare_scratch_reserve(self.conflict_journal.len())?;
            let old = self.active_conflicts.capacity();
            let reservation = self
                .active_conflicts
                .try_reserve(self.conflict_journal.len());
            #[cfg(test)]
            self.observe_physical_memo();
            self.commit_scratch_reserve(requested, growth, old, self.active_conflicts.capacity())?;
            reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        }
        self.work_meter.charge(self.conflict_journal.len())?; // conflict updates
        for &(key, prior) in &self.conflict_journal {
            if entering {
                self.active_conflicts.insert(key, prior + 1);
            } else if prior == 1 {
                self.active_conflicts.remove(&key);
            } else {
                self.active_conflicts.insert(key, prior - 1);
            }
        }
        #[cfg(test)]
        self.observe_physical_memo();
        self.conflict_journal.clear();
        #[cfg(test)]
        self.observe_physical_memo();
        Ok(())
    }

    pub(super) fn enter_active(&mut self, row: u32) -> Result<(), SolveAvailabilityError> {
        let (row_requested, row_growth) = self.prepare_scratch_reserve(1)?;
        let old_row_capacity = self.active_rows.capacity();
        let reservation = self.active_rows.try_reserve(1);
        #[cfg(test)]
        self.observe_physical_memo();
        self.commit_scratch_reserve(
            row_requested,
            row_growth,
            old_row_capacity,
            self.active_rows.capacity(),
        )?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let (conflict_requested, conflict_growth) =
            self.prepare_scratch_reserve(self.roots.len())?;
        let old_conflict_capacity = self.active_conflicts.capacity();
        let reservation = self.active_conflicts.try_reserve(self.roots.len());
        #[cfg(test)]
        self.observe_physical_memo();
        self.commit_scratch_reserve(
            conflict_requested,
            conflict_growth,
            old_conflict_capacity,
            self.active_conflicts.capacity(),
        )?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let prior = self.active_rows.get(&row).copied().unwrap_or(0);
        let next = prior
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.scratch_lane.peak_bytes = self
            .scratch_lane
            .peak_bytes
            .max(self.scratch_retained_bytes()?);
        if prior == 0 {
            self.propagate_active_row(row, true)?;
        }
        self.active_rows.insert(row, next);
        #[cfg(test)]
        self.observe_physical_memo();
        #[cfg(test)]
        if self.fail_observation_at == Some(F5cTestObservationFailure::Enter) {
            self.pending_observation_failure = true;
            self.fail_observation_at = None;
        }
        Ok(())
    }

    pub(super) fn leave_active(&mut self, row: u32) -> Result<(), SolveAvailabilityError> {
        let prior = self
            .active_rows
            .get(&row)
            .copied()
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let next = prior
            .checked_sub(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        if next == 0 {
            self.propagate_active_row(row, false)?;
            self.active_rows.remove(&row);
        } else {
            self.active_rows.insert(row, next);
        }
        #[cfg(test)]
        self.observe_physical_memo();
        #[cfg(test)]
        if self.fail_observation_at == Some(F5cTestObservationFailure::Leave) {
            self.pending_observation_failure = true;
            self.fail_observation_at = None;
        }
        Ok(())
    }

    pub(super) fn conflicts_active(&self, key: F5cExpansionKey) -> bool {
        self.active_conflicts.get(&key).copied().unwrap_or(0) != 0
    }

    pub(super) fn invalidate_row(&mut self, row: u32) -> Result<(), SolveAvailabilityError> {
        self.begin_visit()?;
        self.seed_row(row)?;
        while !self.work.is_empty() {
            self.work_meter.charge(1)?;
            let id = self.work.pop().expect("nonempty memo work");
            #[cfg(test)]
            self.observe_physical_memo();
            let mut root_edge = *self
                .root_heads
                .get(id.0 as usize)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            while let Some(index) = root_edge {
                self.work_meter.charge(1)?;
                let edge = *self
                    .root_edges
                    .get(index)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                if edge.live {
                    self.reserve_root_undo()?;
                    self.roots.remove(&edge.key);
                    self.active_conflicts.remove(&edge.key);
                    self.root_edges[index].live = false;
                    self.root_undo.push(F5cRootUndo::Invalidate(index));
                    #[cfg(test)]
                    self.observe_physical_memo();
                }
                root_edge = edge.next;
            }
            let mut parent_edge = *self
                .parent_heads
                .get(id.0 as usize)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            while let Some(index) = parent_edge {
                self.work_meter.charge(1)?;
                let edge = *self
                    .reverse_parents
                    .get(index)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                self.queue_once(edge.parent)?;
                parent_edge = edge.next;
            }
        }
        Ok(())
    }

    pub(super) fn push_node(
        &mut self,
        kind: F5cSummaryNodeKind,
        incidence: Option<(u32, Polarity)>,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        self.work_meter.charge(1)?;
        let id = checked_summary_node_admission(self.nodes.len())?;
        let mut count = usize::from(incidence.is_some());
        let mut include = |child: F5cSummaryNodeId| -> Result<(), SolveAvailabilityError> {
            let child = self.node(child)?;
            count = count
                .checked_add(child.transitive_incidence_count)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            Ok(())
        };
        match kind {
            F5cSummaryNodeKind::PositiveAlias { start }
            | F5cSummaryNodeKind::NegativeAlias { start } => {
                self.work_meter.charge(1)?;
                let child = *self
                    .child_slice(start, 1)?
                    .first()
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                include(child)?;
            }
            F5cSummaryNodeKind::PositiveUnion { start, len }
            | F5cSummaryNodeKind::NegativeIntersection { start, len } => {
                for child in self.child_slice(start, len)? {
                    self.work_meter.charge(1)?;
                    include(*child)?;
                }
            }
            F5cSummaryNodeKind::PositiveFunction { argument, result }
            | F5cSummaryNodeKind::NegativeFunction { argument, result } => {
                self.work_meter.charge(1)?;
                include(argument)?;
                self.work_meter.charge(1)?;
                include(result)?;
            }
            _ => {}
        }
        let child_count = match kind {
            F5cSummaryNodeKind::PositiveAlias { .. } | F5cSummaryNodeKind::NegativeAlias { .. } => {
                1
            }
            F5cSummaryNodeKind::PositiveUnion { len, .. }
            | F5cSummaryNodeKind::NegativeIntersection { len, .. } => len as usize,
            F5cSummaryNodeKind::PositiveFunction { .. }
            | F5cSummaryNodeKind::NegativeFunction { .. } => 2,
            _ => 0,
        };
        checked_reverse_parent_len(self.reverse_parents.len(), child_count)?;
        let requested = self
            .node_lane
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let old = self.nodes.capacity();
        let node_growth = self
            .node_lane
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_node_growth = self
            .independent_node_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let reservation = self.nodes.try_reserve(1);
        #[cfg(test)]
        self.observe_physical_memo();
        let node_grew = usize::from(self.nodes.capacity() != old);
        if node_grew != 0 {
            self.node_lane.capacity_growths = node_growth;
            #[cfg(test)]
            {
                self.independent_node_growths = independent_node_growth;
            }
        }
        self.node_lane.requested_slots = requested;
        self.node_lane.peak_bytes = self.node_lane.peak_bytes.max(self.node_retained_bytes()?);
        if node_grew != 0 {
            self.observe_simultaneous_peak()?;
        }
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;

        let (next, growth) = self.prepare_index_reserve(1)?;
        let old = self.parent_heads.capacity();
        let reservation = self.parent_heads.try_reserve(1);
        #[cfg(test)]
        self.observe_physical_memo();
        self.commit_index_reserve(next, growth, old, self.parent_heads.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let (next, growth) = self.prepare_index_reserve(1)?;
        let old = self.root_heads.capacity();
        let reservation = self.root_heads.try_reserve(1);
        #[cfg(test)]
        self.observe_physical_memo();
        self.commit_index_reserve(next, growth, old, self.root_heads.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let (next, growth) = self.prepare_scratch_reserve(1)?;
        let old = self.visit_epochs.capacity();
        let reservation = self.visit_epochs.try_reserve(1);
        #[cfg(test)]
        self.observe_physical_memo();
        self.commit_scratch_reserve(next, growth, old, self.visit_epochs.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let (next, growth) = self.prepare_index_reserve(child_count)?;
        let old = self.reverse_parents.capacity();
        let reservation = self.reverse_parents.try_reserve(child_count);
        #[cfg(test)]
        self.observe_physical_memo();
        self.commit_index_reserve(next, growth, old, self.reverse_parents.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        if incidence.is_some() {
            let (next, growth) = self.prepare_index_reserve(1)?;
            let old = self.incidences.capacity();
            let reservation = self.incidences.try_reserve(1);
            #[cfg(test)]
            self.observe_physical_memo();
            self.commit_index_reserve(next, growth, old, self.incidences.capacity())?;
            reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            let (next, growth) = self.prepare_index_reserve(1)?;
            let old = self.incidence_heads.capacity();
            let reservation = self.incidence_heads.try_reserve(1);
            #[cfg(test)]
            self.observe_physical_memo();
            self.commit_index_reserve(next, growth, old, self.incidence_heads.capacity())?;
            reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        }
        self.nodes.push(F5cSummaryNode {
            incidence,
            transitive_incidence_count: count,
            kind,
        });
        self.parent_heads.push(None);
        self.root_heads.push(None);
        self.visit_epochs.push(0);
        #[cfg(test)]
        self.observe_physical_memo();
        #[cfg(test)]
        self.work_meter.record_persistent_mutation();
        let add_parent =
            |this: &mut Self, child: F5cSummaryNodeId| -> Result<(), SolveAvailabilityError> {
                this.work_meter.charge(1)?;
                let head = this
                    .parent_heads
                    .get_mut(child.0 as usize)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                let next = *head;
                *head = Some(this.reverse_parents.len());
                this.reverse_parents.push(F5cReverseParentEdge {
                    child,
                    parent: id,
                    next,
                });
                #[cfg(test)]
                this.observe_physical_memo();
                Ok(())
            };
        match kind {
            F5cSummaryNodeKind::PositiveAlias { start }
            | F5cSummaryNodeKind::NegativeAlias { start } => {
                add_parent(self, self.child_slice(start, 1)?[0])?;
            }
            F5cSummaryNodeKind::PositiveUnion { start, len }
            | F5cSummaryNodeKind::NegativeIntersection { start, len } => {
                self.work_meter.charge(len as usize)?;
                for offset in 0..len as usize {
                    let child = *self
                        .children
                        .get(start as usize + offset)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    add_parent(self, child)?;
                }
            }
            F5cSummaryNodeKind::PositiveFunction { argument, result }
            | F5cSummaryNodeKind::NegativeFunction { argument, result } => {
                add_parent(self, argument)?;
                add_parent(self, result)?;
            }
            _ => {}
        }
        if let Some((row, _)) = incidence {
            self.work_meter.charge(1)?;
            let next = self.incidence_heads.get(&row).copied().flatten();
            self.incidence_heads
                .insert(row, Some(self.incidences.len()));
            self.incidences.push(F5cIncidenceEdge { node: id, next });
            #[cfg(test)]
            self.observe_physical_memo();
        }
        Ok(id)
    }

    pub(super) fn push_children(
        &mut self,
        ids: &[F5cSummaryNodeId],
    ) -> Result<(u32, u32), SolveAvailabilityError> {
        let start = u32::try_from(self.children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let len =
            u32::try_from(ids.len()).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        start
            .checked_add(len)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let requested = self
            .child_lane
            .requested_slots
            .checked_add(ids.len())
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let growth_if_changed = self
            .child_lane
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_growth_if_changed = self
            .independent_child_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let old = self.children.capacity();
        let reservation = self.children.try_reserve(ids.len());
        #[cfg(test)]
        self.observe_physical_memo();
        if self.children.capacity() != old {
            self.child_lane.capacity_growths = growth_if_changed;
            #[cfg(test)]
            {
                self.independent_child_growths = independent_growth_if_changed;
            }
        }
        self.child_lane.requested_slots = requested;
        let peak_bytes = self.child_lane.peak_bytes.max(self.child_retained_bytes()?);
        self.child_lane.peak_bytes = peak_bytes;
        if self.children.capacity() != old {
            self.observe_simultaneous_peak()?;
        }
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        if self.fail_reserve_at
            == Some((F5cTestReserveFailure::ChildrenAfterReserve, start as usize))
        {
            self.fail_reserve_at = None;
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        self.work_meter.charge(ids.len())?;
        self.children.extend_from_slice(ids);
        #[cfg(test)]
        self.observe_physical_memo();
        Ok((start, len))
    }

    pub(super) fn admit(
        &mut self,
        key: F5cExpansionKey,
        root: F5cSummaryNodeId,
    ) -> Result<(), SolveAvailabilityError> {
        if self.roots.contains_key(&key) {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        self.node(root)?;
        for len in [
            self.roots.len(),
            self.root_edges.len(),
            self.root_edge_marks.len(),
            self.active_conflicts.len(),
            self.root_undo.len(),
        ] {
            checked_next_root_lane_len(len)?;
        }
        let requested = self
            .root_lane
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let root_growth = self
            .root_lane
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(test)]
        let independent_root_growth = self
            .independent_root_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let old = self.roots.capacity();
        let reservation = self.roots.try_reserve(1);
        #[cfg(test)]
        self.observe_physical_memo();
        let root_grew = usize::from(self.roots.capacity() != old);
        if root_grew != 0 {
            self.root_lane.capacity_growths = root_growth;
            #[cfg(test)]
            {
                self.independent_root_growths = independent_root_growth;
            }
        }
        self.root_lane.requested_slots = requested;
        self.root_lane.peak_bytes = self.root_lane.peak_bytes.max(self.root_retained_bytes()?);
        if root_grew != 0 {
            self.observe_simultaneous_peak()?;
        }
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;

        let (next, growth) = self.prepare_index_reserve(1)?;
        let old = self.root_edges.capacity();
        let reservation = self.root_edges.try_reserve(1);
        #[cfg(test)]
        self.observe_physical_memo();
        self.commit_index_reserve(next, growth, old, self.root_edges.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let (next, growth) = self.prepare_index_reserve(1)?;
        let old = self.root_edge_marks.capacity();
        let reservation = self.root_edge_marks.try_reserve(1);
        #[cfg(test)]
        self.observe_physical_memo();
        self.commit_index_reserve(next, growth, old, self.root_edge_marks.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let (next, growth) = self.prepare_scratch_reserve(1)?;
        let old = self.active_conflicts.capacity();
        let reservation = self.active_conflicts.try_reserve(1);
        #[cfg(test)]
        self.observe_physical_memo();
        self.commit_scratch_reserve(next, growth, old, self.active_conflicts.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.reserve_root_undo_prechecked()?;
        // Re-entry, conflicted warm lookup, and Shared materialization taint
        // active frames. A completed root-neutral summary therefore has no
        // active incidence when it reaches admission.
        let next = *self
            .root_heads
            .get(root.0 as usize)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let edge_index = self.root_edges.len();
        self.work_meter.charge(1)?;
        self.root_edges.push(F5cRootEdge {
            root,
            key,
            next,
            live: true,
        });
        self.root_edge_marks.push(0);
        self.root_heads[root.0 as usize] = Some(edge_index);
        self.roots.insert(key, root);
        self.root_undo.push(F5cRootUndo::Admit(edge_index));
        #[cfg(test)]
        self.observe_physical_memo();
        #[cfg(test)]
        self.work_meter.record_root_admission(self.root_undo.len());
        #[cfg(test)]
        if self.fail_observation_at == Some(F5cTestObservationFailure::Admit) {
            self.pending_observation_failure = true;
            self.fail_observation_at = None;
        }
        Ok(())
    }

    pub(super) fn requested_slots(&self) -> Result<usize, SolveAvailabilityError> {
        self.root_lane
            .requested_slots
            .checked_add(self.node_lane.requested_slots)
            .and_then(|value| value.checked_add(self.child_lane.requested_slots))
            .and_then(|value| value.checked_add(self.index_lane.requested_slots))
            .and_then(|value| value.checked_add(self.scratch_lane.requested_slots))
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn capacity_growths(&self) -> Result<usize, SolveAvailabilityError> {
        self.root_lane
            .capacity_growths
            .checked_add(self.node_lane.capacity_growths)
            .and_then(|value| value.checked_add(self.child_lane.capacity_growths))
            .and_then(|value| value.checked_add(self.index_lane.capacity_growths))
            .and_then(|value| value.checked_add(self.scratch_lane.capacity_growths))
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn actual_capacity(&self) -> Result<usize, SolveAvailabilityError> {
        self.roots
            .capacity()
            .checked_add(self.nodes.capacity())
            .and_then(|v| v.checked_add(self.children.capacity()))
            .and_then(|v| v.checked_add(self.index_capacity().ok()?))
            .and_then(|v| v.checked_add(self.scratch_capacity().ok()?))
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn root_retained_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        self.roots
            .capacity()
            .checked_mul(std::mem::size_of::<(F5cExpansionKey, F5cSummaryNodeId)>())
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn node_retained_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        self.nodes
            .capacity()
            .checked_mul(std::mem::size_of::<F5cSummaryNode>())
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn child_retained_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        self.children
            .capacity()
            .checked_mul(std::mem::size_of::<F5cSummaryNodeId>())
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn index_capacity(&self) -> Result<usize, SolveAvailabilityError> {
        [
            self.parent_heads.capacity(),
            self.reverse_parents.capacity(),
            self.incidence_heads.capacity(),
            self.incidences.capacity(),
            self.root_heads.capacity(),
            self.root_edges.capacity(),
            self.root_edge_marks.capacity(),
            self.root_undo.capacity(),
        ]
        .into_iter()
        .try_fold(0usize, |sum, value| sum.checked_add(value))
        .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn scratch_capacity(&self) -> Result<usize, SolveAvailabilityError> {
        [
            self.active_rows.capacity(),
            self.active_conflicts.capacity(),
            self.work.capacity(),
            self.conflict_journal.capacity(),
            self.visit_epochs.capacity(),
            self.generalizer_scratch_capacities[0],
            self.generalizer_scratch_capacities[1],
            self.generalizer_scratch_capacities[2],
            self.generalizer_scratch_capacities[3],
        ]
        .into_iter()
        .try_fold(0usize, |sum, value| sum.checked_add(value))
        .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn index_retained_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        let lanes = [
            self.parent_heads
                .capacity()
                .checked_mul(std::mem::size_of::<Option<usize>>()),
            self.reverse_parents
                .capacity()
                .checked_mul(std::mem::size_of::<F5cReverseParentEdge>()),
            self.incidence_heads
                .capacity()
                .checked_mul(std::mem::size_of::<(u32, Option<usize>)>()),
            self.incidences
                .capacity()
                .checked_mul(std::mem::size_of::<F5cIncidenceEdge>()),
            self.root_heads
                .capacity()
                .checked_mul(std::mem::size_of::<Option<usize>>()),
            self.root_edges
                .capacity()
                .checked_mul(std::mem::size_of::<F5cRootEdge>()),
            self.root_edge_marks
                .capacity()
                .checked_mul(std::mem::size_of::<u32>()),
            self.root_undo
                .capacity()
                .checked_mul(std::mem::size_of::<F5cRootUndo>()),
        ];
        lanes
            .into_iter()
            .try_fold(0usize, |sum, value| sum.checked_add(value?))
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn scratch_retained_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        let lanes = [
            self.active_rows
                .capacity()
                .checked_mul(std::mem::size_of::<(u32, usize)>()),
            self.active_conflicts
                .capacity()
                .checked_mul(std::mem::size_of::<(F5cExpansionKey, usize)>()),
            self.work
                .capacity()
                .checked_mul(std::mem::size_of::<F5cSummaryNodeId>()),
            self.conflict_journal
                .capacity()
                .checked_mul(std::mem::size_of::<(F5cExpansionKey, usize)>()),
            self.visit_epochs
                .capacity()
                .checked_mul(std::mem::size_of::<u32>()),
            self.generalizer_scratch_capacities[0]
                .checked_mul(std::mem::size_of::<F5cExpansionFrame>()),
            self.generalizer_scratch_capacities[1].checked_mul(std::mem::size_of::<(
                u32,
                Polarity,
                usize,
            )>()),
            self.generalizer_scratch_capacities[2]
                .checked_mul(std::mem::size_of::<(u32, Polarity)>()),
            self.generalizer_scratch_capacities[3].checked_mul(std::mem::size_of::<u32>()),
        ];
        lanes
            .into_iter()
            .try_fold(0usize, |sum, value| sum.checked_add(value?))
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn retained_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        self.root_retained_bytes()?
            .checked_add(self.node_retained_bytes()?)
            .and_then(|value| value.checked_add(self.child_retained_bytes().ok()?))
            .and_then(|value| value.checked_add(self.index_retained_bytes().ok()?))
            .and_then(|value| value.checked_add(self.scratch_retained_bytes().ok()?))
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn peak_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        Ok(self.simultaneous_peak_bytes)
    }

    pub(super) fn clear(&mut self) {
        #[cfg(test)]
        let prior_joint = std::mem::take(&mut self.walker_resources.physical_joint);
        self.roots = HashMap::new();
        self.nodes = Vec::new();
        self.children = Vec::new();
        self.parent_heads = Vec::new();
        self.reverse_parents = Vec::new();
        self.incidence_heads = HashMap::new();
        self.incidences = Vec::new();
        self.root_heads = Vec::new();
        self.root_edges = Vec::new();
        self.root_edge_marks = Vec::new();
        self.root_edge_mark_epoch = 0;
        self.root_undo = Vec::new();
        self.active_rows = HashMap::new();
        self.active_conflicts = HashMap::new();
        self.work = Vec::new();
        self.conflict_journal = Vec::new();
        self.visit_epochs = Vec::new();
        self.walker_resources = F5cWalkerResources::default();
        #[cfg(test)]
        {
            let joint = &mut self.walker_resources.physical_joint;
            joint.source_capacities = prior_joint.source_capacities;
            joint.source_nested_bytes = prior_joint.source_nested_bytes;
            joint.staged_source_current = prior_joint.staged_source_current;
            joint.peak = prior_joint.peak;
            joint.source_walker_peak = prior_joint.source_walker_peak;
            joint.aggregate_overflow = prior_joint.aggregate_overflow;
            joint.source_event();
        }
        self.generalizer_scratch_capacities = [0; 4];
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if self.matrix_active {
            self.matrix_generalizer_lengths = [0; 4];
            self.matrix_owner_events.release_all();
            for lane in &mut self.matrix_lanes {
                if lane.requested_slots > 0 || lane.actual_capacity > 0 { lane.cleared = true; }
                lane.requested_slots = 0;
                lane.actual_capacity = 0;
                lane.retained_bytes = 0;
            }
        }
        self.simultaneous_peak_bytes = 0;
        #[cfg(test)]
        self.capacity_samples.clear();
        #[cfg(test)]
        {
            self.boxed_raw_lanes_live_sample = None;
            self.r_fixed_point_live_sample = None;
        }
        #[cfg(test)]
        {
            self.independent_generalizer_scratch_peak_bytes = 0;
        }
        #[cfg(test)]
        {
            self.fail_observation_at = None;
            self.fail_reserve_at = None;
            self.pending_observation_failure = false;
        }
    }

    pub(super) fn rollback_nodes(
        &mut self,
        node_checkpoint: usize,
        child_checkpoint: usize,
        reverse_checkpoint: usize,
        incidence_checkpoint: usize,
    ) -> Result<(), SolveAvailabilityError> {
        while self.reverse_parents.len() > reverse_checkpoint {
            let edge = self
                .reverse_parents
                .pop()
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let head = self
                .parent_heads
                .get_mut(edge.child.0 as usize)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            if *head != Some(self.reverse_parents.len()) {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            *head = edge.next;
        }
        while self.incidences.len() > incidence_checkpoint {
            let edge = self
                .incidences
                .pop()
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let row = self
                .nodes
                .get(edge.node.0 as usize)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?
                .incidence
                .ok_or(SolveAvailabilityError::IdentityExhausted)?
                .0;
            if let Some(next) = edge.next {
                // A predecessor means this row's head already existed before
                // the appended edge. Updating it never inserts or allocates.
                *self
                    .incidence_heads
                    .get_mut(&row)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)? = Some(next);
            } else {
                self.incidence_heads.remove(&row);
            }
        }
        self.nodes.truncate(node_checkpoint);
        self.children.truncate(child_checkpoint);
        self.parent_heads.truncate(node_checkpoint);
        self.root_heads.truncate(node_checkpoint);
        self.visit_epochs.truncate(node_checkpoint);
        #[cfg(test)]
        self.observe_physical_memo();
        Ok(())
    }

    pub(super) fn finish_root_transaction(
        &mut self,
        checkpoint: usize,
        commit: bool,
    ) -> Result<(), SolveAvailabilityError> {
        if !commit {
            let mut live = self.roots.len();
            let mut edge_len = self.root_edges.len();
            if self.root_edge_marks.len() != edge_len {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            for event in self
                .root_undo
                .get(checkpoint..)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?
                .iter()
                .rev()
                .copied()
            {
                match event {
                    F5cRootUndo::Admit(index) => {
                        if index.checked_add(1) != Some(edge_len) {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        }
                        let edge = self
                            .root_edges
                            .get(index)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        if edge.root.0 as usize >= self.root_heads.len() {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        }
                        edge_len -= 1;
                        live = live
                            .checked_sub(1)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    }
                    F5cRootUndo::Invalidate(index) => {
                        if index >= edge_len {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        }
                        live = live
                            .checked_add(1)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    }
                }
                if live > self.roots.capacity() {
                    return Err(SolveAvailabilityError::IdentityExhausted);
                }
            }
            for event in self.root_undo[checkpoint..].iter().rev().copied() {
                match event {
                    F5cRootUndo::Admit(index) => {
                        let edge = self
                            .root_edges
                            .pop()
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        self.root_edge_marks
                            .pop()
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        if index != self.root_edges.len() {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        }
                        self.roots.remove(&edge.key);
                        *self
                            .root_heads
                            .get_mut(edge.root.0 as usize)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)? = edge.next;
                    }
                    F5cRootUndo::Invalidate(index) => {
                        let edge = self
                            .root_edges
                            .get_mut(index)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        edge.live = true;
                        self.roots.insert(edge.key, edge.root);
                    }
                }
            }
        }
        self.root_undo.truncate(checkpoint);
        #[cfg(test)]
        self.observe_physical_memo();
        Ok(())
    }

    pub(super) fn reset_active_scratch(&mut self) {
        self.active_rows.clear();
        self.active_conflicts.clear();
        self.work.clear();
        self.conflict_journal.clear();
        self.visit_epochs.fill(0);
        self.visit_epoch = 0;
        self.root_edge_marks.fill(0);
        self.root_edge_mark_epoch = 0;
        #[cfg(test)]
        self.observe_physical_memo();
    }
}

#[derive(Default)]
pub(super) struct F5cExpansionFrame {
    pub(super) tainted: bool,
}

pub(super) enum F5cWalkTask {
    EnterRow {
        row: u32,
        polarity: Polarity,
        root: bool,
    },
    PositiveEndpoint(ValueEndpointKey),
    NegativeEndpoint(ValueEndpointKey),
    EnterTerm {
        term: Term,
        polarity: Polarity,
    },
    ExitRow {
        row: u32,
        polarity: Polarity,
        root: bool,
        values_start: usize,
    },
    ExitFunction {
        polarity: Polarity,
    },
    EnterPath(F5cTraceHop),
    LeavePath,
}

pub(super) enum F5cWalkValue<'meter> {
    Positive(F5cPositive<'meter>, bool),
    Negative(F5cNegative<'meter>, bool),
}

pub(super) enum F5cCompareTask<'tree, 'meter> {
    Positive(&'tree F5cPositive<'meter>, &'tree F5cPositive<'meter>),
    Negative(&'tree F5cNegative<'meter>, &'tree F5cNegative<'meter>),
}

pub(super) enum F5cSummaryTask<'tree, 'meter> {
    Positive(&'tree F5cPositive<'meter>, Option<(u32, Polarity)>),
    Negative(&'tree F5cNegative<'meter>, Option<(u32, Polarity)>),
    PositiveUnion(usize, Option<(u32, Polarity)>),
    NegativeIntersection(usize, Option<(u32, Polarity)>),
    PositiveFunction(Option<(u32, Polarity)>),
    NegativeFunction(Option<(u32, Polarity)>),
}

#[derive(Clone, Copy)]
pub(super) enum F5cMaterializeTask {
    Positive(F5cSummaryNodeId),
    Negative(F5cSummaryNodeId),
    PositiveUnion(usize),
    NegativeIntersection(usize),
    PositiveFunction,
    NegativeFunction,
}

/// Root-local F5c expansion state.  Collected rows remain immutable recipes;
/// this walker is the sole owner of polarity incidence, active-path re-entry,
/// and the Q/R decision for one draft.
pub(super) struct F5cGeneralizer<'a, 'meter> {
    #[cfg(feature = "shadow-f5")]
    pub(super) shadow_origins: Option<&'a mut Vec<(ShadowFreshBinderKind, u32, u32)>>,
    pub(super) session: &'a InferenceSession,
    pub(super) source_meter: &'meter DraftHeapMeter,
    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
    pub(super) memo: F5cComponentExpansionMemo,
    pub(super) flat_sink: F5cFlatWalkSink,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    source_arena_owners: [RawWalkerOwner<'meter>; 4],
    raw_forest_live: bool,
    normalized_candidate_live: bool,
    raw_forest_rollback_failed: bool,
    frozen_bound_epoch: usize,
    pub(super) frames: Vec<F5cExpansionFrame>,
    pub(super) shared_summary_hits: usize,
    pub(super) uncacheable_states: usize,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    uncacheable_seen: ObservedWalkerSet<'meter, F5cExpansionKey>,
    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
    uncacheable_seen: HashSet<F5cExpansionKey>,
    fatal_taint: bool,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) provisional_recursive_rows: ObservedWalkerSet<'meter, u32>,
    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
    pub(super) provisional_recursive_rows: HashSet<u32>,
    node_checkpoint: usize,
    child_checkpoint: usize,
    reverse_checkpoint: usize,
    incidence_checkpoint: usize,
    root_undo_checkpoint: usize,
    in_component: bool,
    pub(super) active: Vec<(u32, Polarity, usize)>,
    pub(super) active_set: HashSet<(u32, Polarity)>,
    #[cfg(test)]
    pub(super) assert_admission_invariant: bool,
    pub(super) path: Vec<F5cTraceHop>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    path_owner: RawWalkerOwner<'meter>,
    pub(super) order: Vec<u32>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    order_owner: RawWalkerOwner<'meter>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) order_seen: ObservedWalkerSet<'meter, u32>,
    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
    pub(super) order_seen: HashSet<u32>,
    pub(super) reentries: Vec<F5cGuardedTrace>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    reentries_owner: RawWalkerOwner<'meter>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    reentry_path_owners: Vec<RawWalkerOwner<'meter>>,
    pub(super) invalid_effects: bool,
    // The memo's event owners release after the generalizer scratch buffers.
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) memo: F5cComponentExpansionMemo,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
pub(super) struct F5cRawForest<'meter> {
    pub(super) draft: f5c_draft::FlatDraft,
    pub(super) raw_owner_order: Vec<u32>,
    #[allow(dead_code)] // The owner releases after raw_owner_order drops.
    raw_owner_order_owner: RawWalkerOwner<'meter>,
    pub(super) raw_bounds: HashMap<u32, (f5c_draft::PositiveId, f5c_draft::NegativeId)>,
    #[allow(dead_code)] // The owner releases after raw_bounds drops.
    raw_bounds_owner: RawWalkerOwner<'meter>,
    #[cfg(test)]
    pub(super) callback_trace: Vec<(u32, Polarity)>,
    #[allow(dead_code)] // The owner releases after callback_trace drops.
    callback_trace_owner: RawWalkerOwner<'meter>,
}

#[cfg(not(all(test, feature = "f5c_resource_probe")))]
pub(super) struct F5cRawForestInner {
    pub(super) draft: f5c_draft::FlatDraft,
    pub(super) raw_owner_order: Vec<u32>,
    pub(super) raw_bounds: HashMap<u32, (f5c_draft::PositiveId, f5c_draft::NegativeId)>,
    #[cfg(test)]
    pub(super) callback_trace: Vec<(u32, Polarity)>,
}

#[cfg(not(all(test, feature = "f5c_resource_probe")))]
pub(super) type F5cRawForest<'meter> = F5cRawForestInner;

#[allow(dead_code)] // The private candidate entrypoint is intentionally unselected.
pub(super) struct F5cNormalizedCandidate {
    pub(super) draft: f5c_draft::FlatDraft,
    pub(super) stats: f5c_normalization::FlatNormalizationStats,
}

/// An SCC-owned candidate. Field order drops every array before its charge.
#[allow(dead_code)]
pub(super) struct F5cStagedCandidate<'meter> {
    pub(super) candidate: F5cNormalizedCandidate,
    _allocations: [TrackedAllocation<'meter>; 6],
}

/// The persistent memo state at entry to one candidate SCC. Member-local
/// generalizers keep their own checkpoints until their raw forest is staged.
#[derive(Clone, Copy)]
#[allow(dead_code)] // The private batch path is selected only by test orchestration.
pub(super) struct F5cBatchCheckpoint {
    root_undo: usize,
    nodes: usize,
    children: usize,
    reverse_parents: usize,
    incidences: usize,
}

impl F5cComponentExpansionMemo {
    #[allow(dead_code)]
    pub(super) fn begin_flat_batch(&self) -> F5cBatchCheckpoint {
        F5cBatchCheckpoint {
            root_undo: self.root_undo.len(),
            nodes: self.nodes.len(),
            children: self.children.len(),
            reverse_parents: self.reverse_parents.len(),
            incidences: self.incidences.len(),
        }
    }

    #[allow(dead_code)]
    pub(super) fn finish_flat_batch(
        &mut self,
        checkpoint: F5cBatchCheckpoint,
        commit: bool,
    ) -> Result<(), SolveAvailabilityError> {
        if commit {
            return self.finish_root_transaction(checkpoint.root_undo, true);
        }
        let roots = self.finish_root_transaction(checkpoint.root_undo, false);
        if roots.is_err() {
            self.clear();
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        if self
            .rollback_nodes(
                checkpoint.nodes,
                checkpoint.children,
                checkpoint.reverse_parents,
                checkpoint.incidences,
            )
            .is_err()
        {
            self.clear();
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        self.reset_active_scratch();
        Ok(())
    }

    #[allow(dead_code)]
    pub(super) fn replace_flat_batch_member<'meter>(
        &mut self,
        source_meter: &'meter DraftHeapMeter,
        staged: &mut F5cStagedCandidate<'meter>,
        mut draft: f5c_draft::FlatDraft,
    ) -> Result<(), SolveAvailabilityError> {
        let capacities = [
            draft.positive_nodes.capacity(),
            draft.negative_nodes.capacity(),
            draft.positive_children.capacity(),
            draft.negative_children.capacity(),
            draft.recursive_bounds.capacity(),
            draft.insertion_order.capacity(),
        ];
        let sizes = [
            std::mem::size_of::<f5c_draft::PositiveNode>(),
            std::mem::size_of::<f5c_draft::NegativeNode>(),
            std::mem::size_of::<f5c_draft::PositiveId>(),
            std::mem::size_of::<f5c_draft::NegativeId>(),
            std::mem::size_of::<f5c_draft::RecursiveBound>(),
            std::mem::size_of::<f5c_draft::NodeRef>(),
        ];
        let mut bytes = [0; 6];
        for index in 0..6 {
            bytes[index] = capacities[index]
                .checked_mul(sizes[index])
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        }
        let future_external = self
            .retained_bytes()?
            .checked_add(self.walker_resources.retained_bytes()?)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let allocations = claim_flat_draft_batch(
            source_meter, &mut draft, bytes, future_external, capacities, sizes)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let old = std::mem::replace(
            staged,
            F5cStagedCandidate {
                candidate: F5cNormalizedCandidate {
                    draft,
                    stats: f5c_normalization::FlatNormalizationStats {
                        key_writes: 0,
                        child_comparisons: 0,
                        descriptor_words: 0,
                        word_comparisons: 0,
                        duplicates: 0,
                        resource: None,
                    },
                },
                _allocations: allocations,
            },
        );
        drop(old);
        self.observe_source_meter(source_meter)
    }
}

trait F5cRCandidateSource<'meter> {
    type ReplayedBound;
    type ReplayedPredicate;

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn f5c_probe_meter(&self) -> Option<&'meter DraftHeapMeter>;

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn f5c_retained_bound_lane(&self) -> F5cWalkerLaneKind;

    fn new_retained_bounds(&self, candidate_count: usize) -> HashMap<u32, Self::ReplayedBound>;

    fn replay_bound(
        &mut self,
        memo: &mut F5cComponentExpansionMemo,
        owner: u32,
        protected: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> Result<Option<Self::ReplayedBound>, SolveAvailabilityError>;

    fn guarded_bound_survives(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        owner: u32,
        bound: &Self::ReplayedBound,
    ) -> Result<bool, SolveAvailabilityError>;

    fn replay_predicate(
        &mut self,
        memo: &mut F5cComponentExpansionMemo,
        protected: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> Result<Self::ReplayedPredicate, SolveAvailabilityError>;

    fn references_predicate<'tree>(
        &'tree self,
        walker: &mut f5c_tree_analysis::Walker<'_, 'tree, 'meter>,
        predicate: &'tree Self::ReplayedPredicate,
        candidates: &HashSet<u32>,
        reachable: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError>
    where
        'meter: 'tree;

    fn references_bound<'tree>(
        &'tree self,
        walker: &mut f5c_tree_analysis::Walker<'_, 'tree, 'meter>,
        owner: u32,
        candidates: &HashSet<u32>,
        referenced: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError>
    where
        'meter: 'tree;

    fn release_replay_scratch(&mut self);

    fn reserve_retained_bound(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        bounds: &mut HashMap<u32, Self::ReplayedBound>,
    ) -> Result<(), SolveAvailabilityError>;

    fn reserve_post_r_set(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        set: &mut HashSet<u32>,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError>;

    fn reserve_post_r_trace_set(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        set: &mut HashSet<usize>,
    ) -> Result<(), SolveAvailabilityError>;

    fn reserve_post_r_map(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        map: &mut HashMap<u32, u32>,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError>;

    fn reserve_post_r_vec(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        values: &mut Vec<u32>,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError>;

    fn release_post_r_lane(&self, memo: &mut F5cComponentExpansionMemo, kind: F5cWalkerLaneKind);

    fn retained_occurrences(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        predicate: &Self::ReplayedPredicate,
        owners: &[u32],
        bounds: &HashMap<u32, Self::ReplayedBound>,
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        owner: Option<&mut RawWalkerOwner<'_>>,
    ) -> Result<Vec<u32>, SolveAvailabilityError>;
}

pub(super) struct F5cPostRSelection<'meter, B, P> {
    #[cfg_attr(not(test), allow(dead_code))]
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) retained_bounds: ObservedWalkerMap<'meter, u32, B>,
    #[cfg_attr(not(test), allow(dead_code))]
    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
    pub(super) retained_bounds: HashMap<u32, B>,
    #[cfg_attr(not(test), allow(dead_code))]
    pub(super) retained_predicate: P,
    pub(super) recursive_owners: Vec<u32>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    recursive_owners_owner: Option<RawWalkerOwner<'meter>>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) recursive_set: ObservedWalkerSet<'meter, u32>,
    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
    pub(super) recursive_set: HashSet<u32>,
    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
    lifetime: std::marker::PhantomData<&'meter ()>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) q: ObservedWalkerMap<'meter, u32, u32>,
    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
    pub(super) q: HashMap<u32, u32>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) r: ObservedWalkerMap<'meter, u32, u32>,
    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
    pub(super) r: HashMap<u32, u32>,
}

struct F5cBoxedRCandidateSource<'a, 'meter> {
    source_meter: &'meter DraftHeapMeter,
    predicate: &'a F5cPositive<'meter>,
    bounds: &'a HashMap<u32, (F5cPositive<'meter>, F5cNegative<'meter>)>,
}

impl<'meter> F5cRCandidateSource<'meter> for F5cBoxedRCandidateSource<'_, 'meter> {
    type ReplayedBound = (F5cPositive<'meter>, F5cNegative<'meter>);
    type ReplayedPredicate = F5cPositive<'meter>;

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn f5c_probe_meter(&self) -> Option<&'meter DraftHeapMeter> {
        Some(self.source_meter)
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn f5c_retained_bound_lane(&self) -> F5cWalkerLaneKind {
        F5cWalkerLaneKind::BoxedRetainedOwnerBounds
    }

    fn new_retained_bounds(&self, _candidate_count: usize) -> HashMap<u32, Self::ReplayedBound> {
        HashMap::new()
    }

    fn replay_bound(
        &mut self,
        memo: &mut F5cComponentExpansionMemo,
        owner: u32,
        protected: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> Result<Option<Self::ReplayedBound>, SolveAvailabilityError> {
        let Some((lower, upper)) = self.bounds.get(&owner) else {
            return Ok(None);
        };
        Ok(Some((
            f5c_replay::replay_positive(
                self.source_meter,
                memo,
                lower,
                protected,
                positive_only,
                negative_only,
            )?,
            f5c_replay::replay_negative(
                self.source_meter,
                memo,
                upper,
                protected,
                positive_only,
                negative_only,
            )?,
        )))
    }

    fn guarded_bound_survives(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        owner: u32,
        bound: &Self::ReplayedBound,
    ) -> Result<bool, SolveAvailabilityError> {
        f5c_tree_analysis::Walker::new_with_source(memo, self.source_meter)
            .guarded_bound_survives(owner, &bound.0, &bound.1)
    }

    fn replay_predicate(
        &mut self,
        memo: &mut F5cComponentExpansionMemo,
        protected: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> Result<Self::ReplayedPredicate, SolveAvailabilityError> {
        f5c_replay::replay_positive(
            self.source_meter,
            memo,
            self.predicate,
            protected,
            positive_only,
            negative_only,
        )
    }

    fn references_predicate<'tree>(
        &'tree self,
        walker: &mut f5c_tree_analysis::Walker<'_, 'tree, 'meter>,
        predicate: &'tree Self::ReplayedPredicate,
        candidates: &HashSet<u32>,
        reachable: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError>
    where
        'meter: 'tree,
    {
        walker.references_positive_with_lane(
            predicate,
            candidates,
            reachable,
            Some(F5cWalkerLaneKind::RReachable),
        )
    }

    fn references_bound<'tree>(
        &'tree self,
        walker: &mut f5c_tree_analysis::Walker<'_, 'tree, 'meter>,
        owner: u32,
        candidates: &HashSet<u32>,
        referenced: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError>
    where
        'meter: 'tree,
    {
        let Some((lower, upper)) = self.bounds.get(&owner) else {
            return Ok(());
        };
        walker.references_positive_with_lane(
            lower,
            candidates,
            referenced,
            Some(F5cWalkerLaneKind::RReferenced),
        )?;
        walker.references_negative_with_lane(
            upper,
            candidates,
            referenced,
            Some(F5cWalkerLaneKind::RReferenced),
        )
    }

    fn release_replay_scratch(&mut self) {}

    fn reserve_retained_bound(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        bounds: &mut HashMap<u32, Self::ReplayedBound>,
    ) -> Result<(), SolveAvailabilityError> {
        let bytes = if bounds.len() == bounds.capacity() {
            memo.retained_bytes()?
        } else {
            0
        };
        let memo_bytes = memo.retained_bytes()?;
        memo.walker_resources.with_source(
            self.source_meter,
            memo_bytes,
            F5cWalkerLaneKind::BoxedRetainedOwnerBounds,
            |walker| {
                walker.reserve_boxed_map(bounds, F5cWalkerLaneKind::BoxedRetainedOwnerBounds, bytes)
            },
        )
    }

    fn reserve_post_r_set(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        set: &mut HashSet<u32>,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError> {
        let bytes = if set.len() == set.capacity() {
            memo.retained_bytes()?
        } else {
            0
        };
        let memo_bytes = memo.retained_bytes()?;
        memo.walker_resources
            .with_source(self.source_meter, memo_bytes, kind, |walker| {
                walker.reserve_generalizer_set(set, kind, bytes)
            })
    }

    fn reserve_post_r_trace_set(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        set: &mut HashSet<usize>,
    ) -> Result<(), SolveAvailabilityError> {
        let bytes = if set.len() == set.capacity() {
            memo.retained_bytes()?
        } else {
            0
        };
        let memo_bytes = memo.retained_bytes()?;
        memo.walker_resources.with_source(
            self.source_meter,
            memo_bytes,
            F5cWalkerLaneKind::PostRSurvivingTraces,
            |walker| {
                walker.reserve_generalizer_set(set, F5cWalkerLaneKind::PostRSurvivingTraces, bytes)
            },
        )
    }

    fn reserve_post_r_map(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        map: &mut HashMap<u32, u32>,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError> {
        let bytes = if map.len() == map.capacity() {
            memo.retained_bytes()?
        } else {
            0
        };
        let memo_bytes = memo.retained_bytes()?;
        memo.walker_resources
            .with_source(self.source_meter, memo_bytes, kind, |walker| {
                walker.reserve_boxed_map(map, kind, bytes)
            })
    }

    fn reserve_post_r_vec(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        values: &mut Vec<u32>,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError> {
        memo.reserve_walker_with_source(values, kind, self.source_meter)
    }

    fn release_post_r_lane(&self, memo: &mut F5cComponentExpansionMemo, kind: F5cWalkerLaneKind) {
        memo.walker_resources.release(kind);
        let _ = memo.observe_component_external(self.source_meter);
    }

    fn retained_occurrences(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        predicate: &Self::ReplayedPredicate,
        owners: &[u32],
        bounds: &HashMap<u32, Self::ReplayedBound>,
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        mut ordered_owner: Option<&mut RawWalkerOwner<'_>>,
    ) -> Result<Vec<u32>, SolveAvailabilityError> {
        let mut ordered = Vec::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut seen_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::PostROccurrenceSeen as usize,
            F5cWalkerLaneKind::PostROccurrenceSeen.slot_size());
        let mut seen = HashSet::new();
        let mut walker = f5c_tree_analysis::Walker::new_with_source(memo, self.source_meter);
        let result = (|| {
            walker.occurrences_positive_checked(predicate, &mut ordered, &mut seen,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                ordered_owner.as_deref_mut(),
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                Some(&mut seen_owner))?;
            for owner in owners {
                walker.memo.work_meter.charge(1)?;
                let (lower, upper) = bounds
                    .get(owner)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                walker.occurrences_positive_checked(lower, &mut ordered, &mut seen,
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    ordered_owner.as_deref_mut(),
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    Some(&mut seen_owner))?;
                walker.occurrences_negative_checked(upper, &mut ordered, &mut seen,
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    ordered_owner.as_deref_mut(),
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    Some(&mut seen_owner))?;
            }
            Ok(())
        })();
        #[cfg(test)]
        walker.memo.record_post_r_sample((
            F5cWalkerLaneKind::PostROccurrenceSeen,
            seen.capacity(),
            walker.memo.walker_resources.lanes[F5cWalkerLaneKind::PostROccurrenceSeen as usize]
                .actual_capacity,
        ));
        drop(seen);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        drop(seen_owner);
        walker
            .memo
            .walker_resources
            .release(F5cWalkerLaneKind::PostROccurrenceSeen);
        match result {
            Ok(()) => Ok(ordered),
            Err(error) => {
                drop(ordered);
                walker
                    .memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::PostROccurrenceOrder);
                Err(error)
            }
        }
    }
}

struct F5cFlatRCandidateSource<'a, 'meter> {
    source: &'a f5c_draft::FlatDraft,
    output: f5c_draft::FlatDraft,
    bounds: &'a HashMap<u32, (f5c_draft::PositiveId, f5c_draft::NegativeId)>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    probe_meter: Option<&'meter DraftHeapMeter>,
    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
    _meter: std::marker::PhantomData<&'meter ()>,
}

impl<'a, 'meter> F5cRCandidateSource<'meter> for F5cFlatRCandidateSource<'a, 'meter> {
    type ReplayedBound = (f5c_draft::PositiveId, f5c_draft::NegativeId);
    type ReplayedPredicate = f5c_draft::PositiveId;

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn f5c_probe_meter(&self) -> Option<&'meter DraftHeapMeter> {
        self.probe_meter
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn f5c_retained_bound_lane(&self) -> F5cWalkerLaneKind {
        F5cWalkerLaneKind::RetainedOwnerBounds
    }

    fn new_retained_bounds(&self, _candidate_count: usize) -> HashMap<u32, Self::ReplayedBound> {
        HashMap::new()
    }

    fn replay_bound(
        &mut self,
        memo: &mut F5cComponentExpansionMemo,
        owner: u32,
        protected: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> Result<Option<Self::ReplayedBound>, SolveAvailabilityError> {
        use f5c_draft::NodeRef;
        let Some((lower, upper)) = self.bounds.get(&owner) else {
            return Ok(None);
        };
        let NodeRef::Positive(lower) = f5c_replay::replay_flat(
            memo,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.probe_meter,
            self.source,
            NodeRef::Positive(*lower),
            &mut self.output,
            protected,
            positive_only,
            negative_only,
        )?
        else {
            return Err(SolveAvailabilityError::IdentityExhausted);
        };
        let NodeRef::Negative(upper) = f5c_replay::replay_flat(
            memo,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.probe_meter,
            self.source,
            NodeRef::Negative(*upper),
            &mut self.output,
            protected,
            positive_only,
            negative_only,
        )?
        else {
            return Err(SolveAvailabilityError::IdentityExhausted);
        };
        Ok(Some((lower, upper)))
    }

    fn guarded_bound_survives(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        owner: u32,
        bound: &Self::ReplayedBound,
    ) -> Result<bool, SolveAvailabilityError> {
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut walker = if let Some(meter) = self.probe_meter {
            f5c_tree_analysis::Walker::new_with_probe_meter(memo, meter)
        } else {
            f5c_tree_analysis::Walker::new(memo)
        };
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut walker = f5c_tree_analysis::Walker::new(memo);
        walker.flat_guarded_bound_survives(
            &self.output,
            owner,
            bound.0,
            bound.1,
        )
    }

    fn replay_predicate(
        &mut self,
        memo: &mut F5cComponentExpansionMemo,
        protected: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> Result<Self::ReplayedPredicate, SolveAvailabilityError> {
        use f5c_draft::NodeRef;
        let predicate = self
            .source
            .predicate
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let NodeRef::Positive(predicate) = f5c_replay::replay_flat(
            memo,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.probe_meter,
            self.source,
            NodeRef::Positive(predicate),
            &mut self.output,
            protected,
            positive_only,
            negative_only,
        )?
        else {
            return Err(SolveAvailabilityError::IdentityExhausted);
        };
        Ok(predicate)
    }

    fn references_predicate<'tree>(
        &'tree self,
        walker: &mut f5c_tree_analysis::Walker<'_, 'tree, 'meter>,
        predicate: &'tree Self::ReplayedPredicate,
        candidates: &HashSet<u32>,
        reachable: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError>
    where
        'meter: 'tree,
    {
        walker.flat_references_with_lane(
            &self.output,
            f5c_draft::NodeRef::Positive(*predicate),
            candidates,
            reachable,
            Some(F5cWalkerLaneKind::RReachable),
        )
    }

    fn references_bound<'tree>(
        &'tree self,
        walker: &mut f5c_tree_analysis::Walker<'_, 'tree, 'meter>,
        owner: u32,
        candidates: &HashSet<u32>,
        referenced: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError>
    where
        'meter: 'tree,
    {
        use f5c_draft::NodeRef;
        let Some((lower, upper)) = self.bounds.get(&owner) else {
            return Ok(());
        };
        walker.flat_references_with_lane(
            self.source,
            NodeRef::Positive(*lower),
            candidates,
            referenced,
            Some(F5cWalkerLaneKind::RReferenced),
        )?;
        walker.flat_references_with_lane(
            self.source,
            NodeRef::Negative(*upper),
            candidates,
            referenced,
            Some(F5cWalkerLaneKind::RReferenced),
        )
    }

    fn release_replay_scratch(&mut self) {
        self.output.positive_nodes.clear();
        self.output.negative_nodes.clear();
        self.output.positive_children.clear();
        self.output.negative_children.clear();
        self.output.insertion_order.clear();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.output.sync_owners();
    }

    fn reserve_retained_bound(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        bounds: &mut HashMap<u32, Self::ReplayedBound>,
    ) -> Result<(), SolveAvailabilityError> {
        let bytes = memo.retained_bytes()?;
        memo.walker_resources.reserve_retained_map(bounds, bytes)
    }

    fn reserve_post_r_set(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        set: &mut HashSet<u32>,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError> {
        let bytes = memo.retained_bytes()?;
        memo.walker_resources.reserve_post_r_set(set, kind, bytes)
    }

    fn reserve_post_r_trace_set(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        set: &mut HashSet<usize>,
    ) -> Result<(), SolveAvailabilityError> {
        let bytes = memo.retained_bytes()?;
        memo.walker_resources.reserve_post_r_set(
            set,
            F5cWalkerLaneKind::PostRSurvivingTraces,
            bytes,
        )
    }

    fn reserve_post_r_map(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        map: &mut HashMap<u32, u32>,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError> {
        let bytes = memo.retained_bytes()?;
        memo.walker_resources.reserve_post_r_map(map, kind, bytes)
    }

    fn reserve_post_r_vec(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        values: &mut Vec<u32>,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError> {
        memo.reserve_walker(values, kind)
    }

    fn release_post_r_lane(&self, memo: &mut F5cComponentExpansionMemo, kind: F5cWalkerLaneKind) {
        memo.walker_resources.release(kind);
    }

    fn retained_occurrences(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        predicate: &Self::ReplayedPredicate,
        owners: &[u32],
        bounds: &HashMap<u32, Self::ReplayedBound>,
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        mut owner: Option<&mut RawWalkerOwner<'_>>,
    ) -> Result<Vec<u32>, SolveAvailabilityError> {
        use f5c_draft::NodeRef;
        let mut ordered = Vec::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut seen_owner = self.probe_meter.map(|meter| RawWalkerOwner::new(meter,
            F5cWalkerLaneKind::PostROccurrenceSeen as usize,
            F5cWalkerLaneKind::PostROccurrenceSeen.slot_size()));
        let mut seen = HashSet::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut walker = if let Some(meter) = self.probe_meter {
            f5c_tree_analysis::Walker::new_with_probe_meter(memo, meter)
        } else {
            f5c_tree_analysis::Walker::new(memo)
        };
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut walker = f5c_tree_analysis::Walker::new(memo);
        let mut visit = |walker: &mut f5c_tree_analysis::Walker<'_, '_, '_>, root| {
            walker.flat_occurrences_checked(
                &self.output,
                root,
                &mut ordered,
                &mut seen,
                |memo, ordered, seen, after_insert| {
                    if after_insert {
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        {
                            if let Some(owner) = seen_owner.as_mut() {
                                owner.observe(seen.len(), seen.capacity());
                            }
                            if let Some(owner) = owner.as_deref_mut() {
                                owner.observe(ordered.len(), ordered.capacity());
                            }
                        }
                        return Ok(());
                    }
                    let bytes = memo.retained_bytes()?;
                    let set_reservation = memo.walker_resources.reserve_post_r_set(
                        seen,
                        F5cWalkerLaneKind::PostROccurrenceSeen,
                        bytes,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    if let Some(owner) = seen_owner.as_mut() {
                        owner.observe(seen.len(), seen.capacity());
                    }
                    set_reservation?;
                    let reservation = memo.reserve_walker(
                        ordered, F5cWalkerLaneKind::PostROccurrenceOrder);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    if let Some(owner) = owner.as_deref_mut() {
                        owner.observe(ordered.len(), ordered.capacity());
                    }
                    reservation
                },
            )
        };
        let result = (|| {
            visit(&mut walker, NodeRef::Positive(*predicate))?;
            for owner in owners {
                walker.memo.work_meter.charge(1)?; // retained bound owner
                let (lower, upper) = bounds
                    .get(owner)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                visit(&mut walker, NodeRef::Positive(*lower))?;
                visit(&mut walker, NodeRef::Negative(*upper))?;
            }
            Ok(())
        })();
        #[cfg(test)]
        walker.memo.record_post_r_sample((
            F5cWalkerLaneKind::PostROccurrenceSeen,
            seen.capacity(),
            walker.memo.walker_resources.lanes[F5cWalkerLaneKind::PostROccurrenceSeen as usize]
                .actual_capacity,
        ));
        drop(seen);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        drop(seen_owner);
        walker
            .memo
            .walker_resources
            .release(F5cWalkerLaneKind::PostROccurrenceSeen);
        match result {
            Ok(()) => Ok(ordered),
            Err(error) => {
                drop(ordered);
                walker
                    .memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::PostROccurrenceOrder);
                Err(error)
            }
        }
    }
}

trait F5cWalkSink<'meter> {
    type Value;
    fn variable(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
        row: u32,
        cacheable: bool,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn shared(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
        id: F5cSummaryNodeId,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn int(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn unit(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn bottom(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn top(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn cacheable(&self, value: &Self::Value) -> bool;
    fn finish_row(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        values: &mut Vec<Self::Value>,
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        values_owner: &mut RawWalkerOwner<'meter>,
        start: usize,
        row: u32,
        polarity: Polarity,
        root: bool,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn function(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
        argument: Self::Value,
        result: Self::Value,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn promote(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        value: &Self::Value,
        row: u32,
        polarity: Polarity,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError>;
}

struct F5cBoxedWalkSink;

impl<'meter> F5cWalkSink<'meter> for F5cBoxedWalkSink {
    type Value = F5cWalkValue<'meter>;
    fn variable(
        &mut self,
        _generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
        row: u32,
        cacheable: bool,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        Ok(match polarity {
            Polarity::Positive => F5cWalkValue::Positive(F5cPositive::Variable(row), cacheable),
            Polarity::Negative => F5cWalkValue::Negative(F5cNegative::Variable(row), cacheable),
        })
    }
    fn shared(
        &mut self,
        _generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
        id: F5cSummaryNodeId,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        Ok(match polarity {
            Polarity::Positive => F5cWalkValue::Positive(F5cPositive::Shared(id), true),
            Polarity::Negative => F5cWalkValue::Negative(F5cNegative::Shared(id), true),
        })
    }
    fn int(
        &mut self,
        _generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        Ok(match polarity {
            Polarity::Positive => F5cWalkValue::Positive(F5cPositive::Int, true),
            Polarity::Negative => F5cWalkValue::Negative(F5cNegative::Int, true),
        })
    }
    fn unit(
        &mut self,
        _generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        Ok(match polarity {
            Polarity::Positive => F5cWalkValue::Positive(F5cPositive::Unit, true),
            Polarity::Negative => F5cWalkValue::Negative(F5cNegative::Unit, true),
        })
    }
    fn bottom(
        &mut self,
        _generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        Ok(match polarity {
            Polarity::Positive => F5cWalkValue::Positive(F5cPositive::Bottom, true),
            Polarity::Negative => F5cWalkValue::Negative(F5cNegative::Bottom, true),
        })
    }
    fn top(
        &mut self,
        _generalizer: &mut F5cGeneralizer<'_, 'meter>,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        Ok(F5cWalkValue::Negative(F5cNegative::Top, true))
    }
    fn cacheable(&self, value: &Self::Value) -> bool {
        match value {
            F5cWalkValue::Positive(_, cacheable) | F5cWalkValue::Negative(_, cacheable) => {
                *cacheable
            }
        }
    }
    fn finish_row(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        values: &mut Vec<Self::Value>,
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        values_owner: &mut RawWalkerOwner<'meter>,
        values_start: usize,
        row: u32,
        polarity: Polarity,
        root: bool,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        let value = match polarity {
            Polarity::Positive => {
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let mut raw_owner = RawWalkerOwner::new(generalizer.source_meter,
                    F5cWalkerLaneKind::PositiveParts as usize,
                    std::mem::size_of::<F5cPositive>());
                let mut parts = Vec::new();
                let mut cacheable = true;
                if generalizer.candidate_own_row_references()
                    && !root
                    && values.len() > values_start
                {
                    // Bounds refine this row; they do not erase its own diagonal.
                    generalizer.memo.work_meter.charge(1)?;
                    let reservation = generalizer.memo.reserve_walker_with_source(
                        &mut parts,
                        F5cWalkerLaneKind::PositiveParts,
                        generalizer.source_meter,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    raw_owner.observe(parts.len(), parts.capacity());
                    reservation?;
                    parts.push(F5cPositive::Variable(row));
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    raw_owner.observe(parts.len(), parts.capacity());
                    // Stable own-row references use existing incidence-aware promotion.
                    // Active-path reentry still taints its enclosing frame separately.
                }
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let capacity = values.capacity();
                let drained = values.drain(values_start..);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                values_owner.observe(values_start, capacity);
                for child in drained {
                    let F5cWalkValue::Positive(value, child_cacheable) = child else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    let duplicate = {
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        let mut comparisons_owner = RawWalkerOwner::new(generalizer.source_meter,
                            F5cWalkerLaneKind::Comparison as usize,
                            F5cWalkerLaneKind::Comparison.slot_size());
                        let mut comparisons = Vec::new();
                        let mut duplicate = false;
                        for previous in &parts {
                            generalizer.memo.work_meter.charge(1)?;
                            if generalizer.structural_equal_with_owner(
                                F5cCompareTask::Positive(previous, &value),
                                &mut comparisons,
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                Some(&mut comparisons_owner),
                            )? {
                                duplicate = true;
                                break;
                            }
                        }
                        generalizer.memo.release_walker_with_source(
                            F5cWalkerLaneKind::Comparison,
                            generalizer.source_meter,
                        )?;
                        duplicate
                    };
                    if !duplicate {
                        cacheable &= child_cacheable;
                        let reservation = generalizer.memo.reserve_walker_with_source(
                            &mut parts,
                            F5cWalkerLaneKind::PositiveParts,
                            generalizer.source_meter,
                        );
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        raw_owner.observe(parts.len(), parts.capacity());
                        reservation?;
                        parts.push(value);
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        raw_owner.observe(parts.len(), parts.capacity());
                    }
                }
                let nonempty = !parts.is_empty();
                let value = F5cWalkValue::Positive(
                    match parts.len() {
                        0 => {
                            drop(parts);
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            drop(raw_owner);
                            generalizer.memo.release_walker_with_source(
                                F5cWalkerLaneKind::PositiveParts,
                                generalizer.source_meter,
                            )?;
                            if root {
                                F5cPositive::Bottom
                            } else {
                                F5cPositive::Variable(row)
                            }
                        }
                        1 => {
                            let value = parts.pop().expect("one lower member");
                            drop(parts);
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            drop(raw_owner);
                            generalizer.memo.release_walker_with_source(
                                F5cWalkerLaneKind::PositiveParts,
                                generalizer.source_meter,
                            )?;
                            value
                        }
                        _ => {
                            generalizer
                                .memo
                                .observe_component_external(generalizer.source_meter)?;
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            let adopted = TrackedVec::try_adopt_raw_from_walker_with_owner(
                                generalizer.source_meter, parts,
                                PhysicalOwnerKind::UnionChildren, raw_owner);
                            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                            let adopted = TrackedVec::try_adopt_raw_from_walker_with_kind(
                                generalizer.source_meter, parts,
                                PhysicalOwnerKind::UnionChildren);
                            let parts = match adopted {
                                Ok(parts) => parts,
                                Err((parts, raw_owner)) => {
                                    drop(parts);
                                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                                    drop(raw_owner);
                                    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                                    let _ = raw_owner;
                                    generalizer.memo.release_walker_with_source(
                                        F5cWalkerLaneKind::PositiveParts,
                                        generalizer.source_meter,
                                    )?;
                                    return Err(SolveAvailabilityError::IdentityExhausted);
                                }
                            };
                            #[cfg(test)]
                            generalizer.memo.mark_census_parts_adopted(
                                F5cWalkerLaneKind::PositiveParts,
                                parts.capacity(),
                            );
                            generalizer.memo.release_walker_with_source(
                                F5cWalkerLaneKind::PositiveParts,
                                generalizer.source_meter,
                            )?;
                            #[cfg(test)]
                            generalizer.memo.observe_parts_physical(
                                F5cWalkerLaneKind::PositiveParts,
                                parts.capacity(),
                                generalizer.source_meter,
                                true,
                            );
                            F5cPositive::Union(parts)
                        }
                    },
                    cacheable && (nonempty || root || generalizer.candidate_own_row_references()),
                );
                value
            }
            Polarity::Negative => {
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let mut raw_owner = RawWalkerOwner::new(generalizer.source_meter,
                    F5cWalkerLaneKind::NegativeParts as usize,
                    std::mem::size_of::<F5cNegative>());
                let mut parts = Vec::new();
                let mut cacheable = true;
                if generalizer.candidate_own_row_references()
                    && !root
                    && values.len() > values_start
                {
                    // Bounds refine this row; they do not erase its own diagonal.
                    generalizer.memo.work_meter.charge(1)?;
                    let reservation = generalizer.memo.reserve_walker_with_source(
                        &mut parts,
                        F5cWalkerLaneKind::NegativeParts,
                        generalizer.source_meter,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    raw_owner.observe(parts.len(), parts.capacity());
                    reservation?;
                    parts.push(F5cNegative::Variable(row));
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    raw_owner.observe(parts.len(), parts.capacity());
                    // Stable own-row references use existing incidence-aware promotion.
                    // Active-path reentry still taints its enclosing frame separately.
                }
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let capacity = values.capacity();
                let drained = values.drain(values_start..);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                values_owner.observe(values_start, capacity);
                for child in drained {
                    let F5cWalkValue::Negative(value, child_cacheable) = child else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    let duplicate = {
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        let mut comparisons_owner = RawWalkerOwner::new(generalizer.source_meter,
                            F5cWalkerLaneKind::Comparison as usize,
                            F5cWalkerLaneKind::Comparison.slot_size());
                        let mut comparisons = Vec::new();
                        let mut duplicate = false;
                        for previous in &parts {
                            generalizer.memo.work_meter.charge(1)?;
                            if generalizer.structural_equal_with_owner(
                                F5cCompareTask::Negative(previous, &value),
                                &mut comparisons,
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                Some(&mut comparisons_owner),
                            )? {
                                duplicate = true;
                                break;
                            }
                        }
                        generalizer.memo.release_walker_with_source(
                            F5cWalkerLaneKind::Comparison,
                            generalizer.source_meter,
                        )?;
                        duplicate
                    };
                    if !duplicate {
                        cacheable &= child_cacheable;
                        let reservation = generalizer.memo.reserve_walker_with_source(
                            &mut parts,
                            F5cWalkerLaneKind::NegativeParts,
                            generalizer.source_meter,
                        );
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        raw_owner.observe(parts.len(), parts.capacity());
                        reservation?;
                        parts.push(value);
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        raw_owner.observe(parts.len(), parts.capacity());
                    }
                }
                let nonempty = !parts.is_empty();
                let value = F5cWalkValue::Negative(
                    match parts.len() {
                        0 => {
                            drop(parts);
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            drop(raw_owner);
                            generalizer.memo.release_walker_with_source(
                                F5cWalkerLaneKind::NegativeParts,
                                generalizer.source_meter,
                            )?;
                            F5cNegative::Variable(row)
                        }
                        1 => {
                            let value = parts.pop().expect("one upper member");
                            drop(parts);
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            drop(raw_owner);
                            generalizer.memo.release_walker_with_source(
                                F5cWalkerLaneKind::NegativeParts,
                                generalizer.source_meter,
                            )?;
                            value
                        }
                        _ => {
                            generalizer
                                .memo
                                .observe_component_external(generalizer.source_meter)?;
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            let adopted = TrackedVec::try_adopt_raw_from_walker_with_owner(
                                generalizer.source_meter, parts,
                                PhysicalOwnerKind::IntersectionChildren, raw_owner);
                            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                            let adopted = TrackedVec::try_adopt_raw_from_walker_with_kind(
                                generalizer.source_meter, parts,
                                PhysicalOwnerKind::IntersectionChildren);
                            let parts = match adopted {
                                Ok(parts) => parts,
                                Err((parts, raw_owner)) => {
                                    drop(parts);
                                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                                    drop(raw_owner);
                                    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                                    let _ = raw_owner;
                                    generalizer.memo.release_walker_with_source(
                                        F5cWalkerLaneKind::NegativeParts,
                                        generalizer.source_meter,
                                    )?;
                                    return Err(SolveAvailabilityError::IdentityExhausted);
                                }
                            };
                            #[cfg(test)]
                            generalizer.memo.mark_census_parts_adopted(
                                F5cWalkerLaneKind::NegativeParts,
                                parts.capacity(),
                            );
                            generalizer.memo.release_walker_with_source(
                                F5cWalkerLaneKind::NegativeParts,
                                generalizer.source_meter,
                            )?;
                            #[cfg(test)]
                            generalizer.memo.observe_parts_physical(
                                F5cWalkerLaneKind::NegativeParts,
                                parts.capacity(),
                                generalizer.source_meter,
                                true,
                            );
                            F5cNegative::Intersection(parts)
                        }
                    },
                    cacheable && (nonempty || generalizer.candidate_own_row_references()),
                );
                value
            }
        };
        Ok(value)
    }
    fn function(
        &mut self,
        _generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
        argument: Self::Value,
        result: Self::Value,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        #[cfg(test)]
        F5C_FUNCTION_OUTPUT_CONSTRUCTION.with(|marker| {
            let count = marker.get().map_or(0, |(_, count)| count);
            marker.set(Some((_generalizer.memo.work_meter.get(), count + 1)));
        });
        Ok(match (polarity, argument, result) {
            (
                Polarity::Positive,
                F5cWalkValue::Negative(argument, argument_cacheable),
                F5cWalkValue::Positive(result, result_cacheable),
            ) => F5cWalkValue::Positive(
                F5cPositive::Function {
                    argument: TrackedOne::try_new_with_kind(_generalizer.source_meter, argument,
                        PhysicalOwnerKind::PositiveFunctionArgument)
                        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result: TrackedOne::try_new_with_kind(_generalizer.source_meter, result,
                        PhysicalOwnerKind::PositiveFunctionResult)
                        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                },
                argument_cacheable && result_cacheable,
            ),
            (
                Polarity::Negative,
                F5cWalkValue::Positive(argument, argument_cacheable),
                F5cWalkValue::Negative(result, result_cacheable),
            ) => F5cWalkValue::Negative(
                F5cNegative::Function {
                    argument: TrackedOne::try_new_with_kind(_generalizer.source_meter, argument,
                        PhysicalOwnerKind::NegativeFunctionArgument)
                        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                    argument_effect: F5cPositiveEffect::Bottom,
                    result_effect: F5cNegativeEffect::Empty,
                    result: TrackedOne::try_new_with_kind(_generalizer.source_meter, result,
                        PhysicalOwnerKind::NegativeFunctionResult)
                        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                },
                argument_cacheable && result_cacheable,
            ),
            _ => return Err(SolveAvailabilityError::IdentityExhausted),
        })
    }
    fn promote(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        value: &Self::Value,
        row: u32,
        polarity: Polarity,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        match value {
            F5cWalkValue::Positive(value, _) => generalizer.memo.positive_node_with_source(
                value,
                Some((row, polarity)),
                generalizer.source_meter,
            ),
            F5cWalkValue::Negative(value, _) => generalizer.memo.negative_node_with_source(
                value,
                Some((row, polarity)),
                generalizer.source_meter,
            ),
        }
    }
}

impl<'a, 'meter> F5cGeneralizer<'a, 'meter> {
    fn candidate_own_row_references(&self) -> bool {
        #[cfg(feature = "shadow-apply-candidate")]
        {
            self.session.candidate_own_row_references
        }
        #[cfg(not(feature = "shadow-apply-candidate"))]
        {
            false
        }
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn observe_guarded_progress(&self, tasks_capacity: usize) {
        F5C_GUARDED_PROGRESS.with(|state| {
            let Some((emitted, milestone)) = state.get() else { return; };
            let work = self.memo.work_meter.get();
            if work < milestone { return; }
            let path_capacity = self.memo.walker_resources.lanes
                [F5cWalkerLaneKind::ReentryPaths as usize].actual_capacity;
            let path_bytes = path_capacity
                .checked_mul(F5cWalkerLaneKind::ReentryPaths.slot_size())
                .expect("F5c guarded progress path bytes");
            let separator = if emitted == 0 { "\n" } else { "" };
            eprintln!("{separator}F5C_GUARDED_PROGRESS\tseq={}\twork={}\treentries={}\treentry_path_capacity={}\treentry_path_bytes={}\tpath_depth={}\tactive_depth={}\tframe_depth={}\ttasks_capacity={}",
                emitted + 1, work, self.reentries.len(), path_capacity, path_bytes,
                self.path.len(), self.active.len(), self.frames.len(), tasks_capacity);
            let next = work.checked_next_power_of_two()
                .and_then(|power| if power <= work { power.checked_mul(2) } else { Some(power) });
            state.set(if emitted + 1 == 64 { None } else { next.map(|work| (emitted + 1, work)) });
        });
    }

    fn pure_function_effect(
        &mut self,
        term: Term,
        polarity: Polarity,
    ) -> Result<bool, SolveAvailabilityError> {
        match (polarity, self.session.store.term_view(term)) {
            (Polarity::Positive, Ok(TermView::Leaf(Leaf::EffectBottomPositive)))
            | (Polarity::Negative, Ok(TermView::Leaf(Leaf::EmptyEffectNegative))) => Ok(true),
            (expected, Ok(TermView::LiveVariable(view)))
                if view.kind() == ComponentKind::Effect && view.polarity() == expected =>
            {
                let row = self
                    .session
                    .effect_bounds
                    .get(
                        usize::try_from(view.ordinal())
                            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                    )
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                self.memo.work_meter.charge(2)?; // exact lower and upper effect bounds
                Ok(row.has_bottom_lower && row.has_empty_upper)
            }
            _ => Ok(false),
        }
    }
    #[cfg(test)]
    pub(super) fn component_idle_checkpoint_for_test(
        &self,
    ) -> (bool, bool, bool, usize, usize, usize, usize, usize) {
        (
            self.raw_forest_live,
            self.raw_forest_rollback_failed,
            self.in_component,
            self.node_checkpoint,
            self.child_checkpoint,
            self.reverse_checkpoint,
            self.incidence_checkpoint,
            self.root_undo_checkpoint,
        )
    }

    fn release_persistent_lanes(&mut self) {
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        { self.uncacheable_seen = ObservedWalkerSet::new(self.source_meter,
            F5cWalkerLaneKind::UncacheableSeen);
          self.provisional_recursive_rows = ObservedWalkerSet::new(self.source_meter,
            F5cWalkerLaneKind::ProvisionalRecursiveRows); }
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        { self.uncacheable_seen = HashSet::new();
          self.provisional_recursive_rows = HashSet::new(); }
        self.path = Vec::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        { self.path_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::Path as usize, F5cWalkerLaneKind::Path.slot_size()); }
        self.order = Vec::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        { self.order_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::Order as usize, F5cWalkerLaneKind::Order.slot_size()); }
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        { self.order_seen = ObservedWalkerSet::new(self.source_meter,
            F5cWalkerLaneKind::OrderSeen); }
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        { self.order_seen = HashSet::new(); }
        self.reentries = Vec::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        { self.reentries_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::Reentries as usize, F5cWalkerLaneKind::Reentries.slot_size()); }
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.reentry_path_owners.clear();
        for kind in [
            F5cWalkerLaneKind::UncacheableSeen,
            F5cWalkerLaneKind::ProvisionalRecursiveRows,
            F5cWalkerLaneKind::Path,
            F5cWalkerLaneKind::Order,
            F5cWalkerLaneKind::OrderSeen,
            F5cWalkerLaneKind::Reentries,
            F5cWalkerLaneKind::ReentryPaths,
        ] {
            self.memo.walker_resources.release(kind);
            let _ = self.memo.observe_component_external(self.source_meter);
        }
    }

    fn observe_walker_component(&mut self) -> Result<(), SolveAvailabilityError> {
        self.memo.observe_walker_with_source(self.source_meter)
    }

    fn reserve_active_mirrors(&mut self, frame: bool) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        if self.memo.fail_reserve_at
            == Some((
                F5cTestReserveFailure::ActiveMirrors,
                self.memo.root_undo.len(),
            ))
        {
            self.memo.fail_reserve_at = None;
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        if frame {
            let (requested, growth) = self.memo.prepare_scratch_reserve(1)?;
            let old = self.frames.capacity();
            let reservation = self.frames.try_reserve(1);
            self.memo.generalizer_scratch_capacities[0] = self.frames.capacity();
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            if self.memo.matrix_active { self.memo.matrix_generalizer_lengths[0] = self.frames.len(); }
            #[cfg(test)]
            self.memo.observe_physical_memo();
            let committed =
                self.memo
                    .commit_scratch_reserve(requested, growth, old, self.frames.capacity());
            self.memo.observe_component_external(self.source_meter)?;
            committed?;
            reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        }
        let (requested, growth) = self.memo.prepare_scratch_reserve(1)?;
        let old = self.active.capacity();
        let reservation = self.active.try_reserve(1);
        self.memo.generalizer_scratch_capacities[1] = self.active.capacity();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if self.memo.matrix_active { self.memo.matrix_generalizer_lengths[1] = self.active.len(); }
        #[cfg(test)]
        self.memo.observe_physical_memo();
        let committed =
            self.memo
                .commit_scratch_reserve(requested, growth, old, self.active.capacity());
        self.memo.observe_component_external(self.source_meter)?;
        committed?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;

        let (requested, growth) = self.memo.prepare_scratch_reserve(1)?;
        let old = self.active_set.capacity();
        let reservation = self.active_set.try_reserve(1);
        self.memo.generalizer_scratch_capacities[2] = self.active_set.capacity();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if self.memo.matrix_active { self.memo.matrix_generalizer_lengths[2] = self.active_set.len(); }
        #[cfg(test)]
        self.memo.observe_physical_memo();
        let committed =
            self.memo
                .commit_scratch_reserve(requested, growth, old, self.active_set.capacity());
        self.memo.observe_component_external(self.source_meter)?;
        committed?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn with_source_meter(
        session: &'a InferenceSession,
        source_meter: &'meter DraftHeapMeter,
    ) -> Self {
        Self::with_memo(
            session,
            source_meter,
            F5cComponentExpansionMemo::default(),
            0,
        )
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn new_source_arena_owners(meter: &'meter DraftHeapMeter) -> [RawWalkerOwner<'meter>; 4] {
        [
            F5cWalkerLaneKind::SourcePositiveNodes,
            F5cWalkerLaneKind::SourceNegativeNodes,
            F5cWalkerLaneKind::SourcePositiveChildren,
            F5cWalkerLaneKind::SourceNegativeChildren,
        ].map(|lane| RawWalkerOwner::new(meter, lane as usize, lane.slot_size()))
    }

    pub(super) fn with_memo(
        session: &'a InferenceSession,
        source_meter: &'meter DraftHeapMeter,
        mut memo: F5cComponentExpansionMemo,
        frozen_bound_epoch: usize,
    ) -> Self {
        memo.work_meter = session.f5c_draft_work.clone();
        let node_checkpoint = memo.nodes.len();
        let child_checkpoint = memo.children.len();
        let reverse_checkpoint = memo.reverse_parents.len();
        let incidence_checkpoint = memo.incidences.len();
        assert!(memo.active_rows.is_empty());
        assert!(memo.active_conflicts.is_empty());
        assert!(memo.work.is_empty());
        assert!(memo.conflict_journal.is_empty());
        let root_undo_checkpoint = memo.root_undo.len();
        Self {
            #[cfg(feature = "shadow-f5")]
            shadow_origins: None,
            session,
            source_meter,
            memo,
            flat_sink: F5cFlatWalkSink::default(),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            source_arena_owners: Self::new_source_arena_owners(source_meter),
            raw_forest_live: false,
            normalized_candidate_live: false,
            raw_forest_rollback_failed: false,
            frozen_bound_epoch,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            path_owner: RawWalkerOwner::new(source_meter, F5cWalkerLaneKind::Path as usize,
                F5cWalkerLaneKind::Path.slot_size()),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            order_owner: RawWalkerOwner::new(source_meter, F5cWalkerLaneKind::Order as usize,
                F5cWalkerLaneKind::Order.slot_size()),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            reentries_owner: RawWalkerOwner::new(source_meter, F5cWalkerLaneKind::Reentries as usize,
                F5cWalkerLaneKind::Reentries.slot_size()),
            frames: Vec::new(),
            shared_summary_hits: 0,
            uncacheable_states: 0,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            uncacheable_seen: ObservedWalkerSet::new(source_meter,
                F5cWalkerLaneKind::UncacheableSeen),
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            uncacheable_seen: HashSet::new(),
            fatal_taint: false,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            provisional_recursive_rows: ObservedWalkerSet::new(source_meter,
                F5cWalkerLaneKind::ProvisionalRecursiveRows),
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            provisional_recursive_rows: HashSet::new(),
            node_checkpoint,
            child_checkpoint,
            reverse_checkpoint,
            incidence_checkpoint,
            root_undo_checkpoint,
            in_component: false,
            active: Vec::new(),
            active_set: HashSet::new(),
            #[cfg(test)]
            assert_admission_invariant: false,
            path: Vec::new(),
            order: Vec::new(),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            order_seen: ObservedWalkerSet::new(source_meter,
                F5cWalkerLaneKind::OrderSeen),
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            order_seen: HashSet::new(),
            reentries: Vec::new(),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            reentry_path_owners: Vec::new(),
            invalid_effects: false,
        }
    }

    fn mark(&mut self, ordinal: u32, _polarity: Polarity) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        F5C_ORDER_REGISTRATION.with(|marker| marker.set(Some(self.memo.work_meter.get())));
        self.memo.work_meter.charge(1)?;
        if !self.order_seen.contains(&ordinal) {
            self.memo.work_meter.charge(2)?;
            let memo_bytes = self.memo.retained_bytes()?;
            let reservation = self.memo.walker_resources.with_source(
                self.source_meter,
                memo_bytes,
                F5cWalkerLaneKind::OrderSeen,
                |walker| {
                    walker.reserve_generalizer_set(
                        &mut self.order_seen,
                        F5cWalkerLaneKind::OrderSeen,
                        memo_bytes,
                    )
                },
            );
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.order_seen.observe_capacity(self.order_seen.len() + 1);
            reservation?;
            #[cfg(test)]
            if self.memo.fail_reserve_at
                == Some((F5cTestReserveFailure::OrderAfterSeen, self.order.len()))
            {
                self.memo.fail_reserve_at = None;
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            let reservation = self.memo.reserve_walker_with_source(
                &mut self.order,
                F5cWalkerLaneKind::Order,
                self.source_meter,
            );
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.order_owner.observe(self.order.len(), self.order.capacity());
            reservation?;
            self.order_seen.insert(ordinal);
            self.order.push(ordinal);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.order_owner.observe(self.order.len(), self.order.capacity());
        }
        if self.provisional_recursive_rows.contains(&ordinal)
            || self
                .session
                .value_metadata
                .get(ordinal as usize)
                .is_none_or(|metadata| metadata.non_generic)
            || self
                .session
                .value_levels
                .get(ordinal as usize)
                .is_none_or(|level| *level == 0)
        {
            if let Some(frame) = self.frames.last_mut() {
                frame.tainted = true;
            }
        }
        Ok(())
    }

    pub(super) fn register_order(
        meter: &F5cDraftWorkMeter,
        seen: &mut HashSet<u32>,
        order: &mut Vec<u32>,
        ordinal: u32,
    ) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        F5C_ORDER_REGISTRATION.with(|marker| marker.set(Some(meter.get())));
        meter.charge(1)?; // seen-set lookup
        if !seen.contains(&ordinal) {
            // Admit both operations before changing either lane.
            meter.charge(2)?; // set insertion and ordered append
            seen.try_reserve(1)
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            order
                .try_reserve(1)
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            seen.insert(ordinal);
            order.push(ordinal);
        }
        Ok(())
    }

    pub(super) fn taint_active_states(&mut self) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        F5C_TAINT_BOUNDARY.with(|boundary| {
            if boundary.get().is_none() && self.frames.len() >= 64 {
                boundary.set(Some((self.memo.work_meter.get(), self.frames.len())));
            }
        });
        self.memo.work_meter.charge(self.frames.len())?;
        for frame in &mut self.frames {
            frame.tainted = true;
        }
        Ok(())
    }

    fn taint_failed_draft(&mut self) -> Result<(), SolveAvailabilityError> {
        self.taint_active_states()?;
        self.fatal_taint = true;
        Ok(())
    }

    fn record_uncacheable(
        &mut self,
        row: u32,
        polarity: Polarity,
    ) -> Result<(), SolveAvailabilityError> {
        let key = F5cExpansionKey {
            row,
            polarity,
            frozen_bound_epoch: self.frozen_bound_epoch,
        };
        if !self.uncacheable_seen.contains(&key) {
            let count = self
                .uncacheable_states
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let memo_bytes = self.memo.retained_bytes()?;
            let reservation = self.memo.walker_resources.with_source(
                self.source_meter,
                memo_bytes,
                F5cWalkerLaneKind::UncacheableSeen,
                |walker| {
                    walker.reserve_generalizer_set(
                        &mut self.uncacheable_seen,
                        F5cWalkerLaneKind::UncacheableSeen,
                        memo_bytes,
                    )
                },
            );
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.uncacheable_seen.observe_capacity(self.uncacheable_seen.len() + 1);
            reservation?;
            self.uncacheable_seen.insert(key);
            self.uncacheable_states = count;
        }
        Ok(())
    }

    fn active(&self, ordinal: u32, polarity: Polarity) -> bool {
        self.active_set.contains(&(ordinal, polarity))
    }

    fn active_any(&self, ordinal: u32) -> bool {
        self.active_set.contains(&(ordinal, Polarity::Positive))
            || self.active_set.contains(&(ordinal, Polarity::Negative))
    }

    #[cfg(test)]
    fn assert_admitted_summary_has_no_active_incidence(&self, root: F5cSummaryNodeId) {
        let mut pending = vec![root];
        let mut seen = HashSet::new();
        while let Some(id) = pending.pop() {
            let Some(node) = self.memo.nodes.get(id.0 as usize) else {
                assert!(false, "admitted summary node ID is valid");
                return;
            };
            if !seen.insert(id) {
                continue;
            }
            if let Some((row, _)) = node.incidence {
                assert!(
                    !self.active_any(row),
                    "admitted summary contains an active row"
                );
            }
            match node.kind {
                F5cSummaryNodeKind::PositiveAlias { start }
                | F5cSummaryNodeKind::NegativeAlias { start } => {
                    let children = self.memo.child_slice(start, 1);
                    assert!(children.is_ok(), "admitted alias children are valid");
                    pending.extend_from_slice(children.unwrap());
                }
                F5cSummaryNodeKind::PositiveUnion { start, len }
                | F5cSummaryNodeKind::NegativeIntersection { start, len } => {
                    let children = self.memo.child_slice(start, len);
                    assert!(children.is_ok(), "admitted summary children are valid");
                    pending.extend_from_slice(children.unwrap());
                }
                F5cSummaryNodeKind::PositiveFunction { argument, result }
                | F5cSummaryNodeKind::NegativeFunction { argument, result } => {
                    pending.extend([argument, result]);
                }
                _ => {}
            }
        }
    }

    fn record_reentry(
        &mut self,
        ordinal: u32,
        reentry_polarity: Polarity,
    ) -> Result<(), SolveAvailabilityError> {
        if !self.provisional_recursive_rows.contains(&ordinal) {
            let memo_bytes = self.memo.retained_bytes()?;
            let reservation = self.memo.walker_resources.with_source(
                self.source_meter,
                memo_bytes,
                F5cWalkerLaneKind::ProvisionalRecursiveRows,
                |walker| {
                    walker.reserve_generalizer_set(
                        &mut self.provisional_recursive_rows,
                        F5cWalkerLaneKind::ProvisionalRecursiveRows,
                        memo_bytes,
                    )
                },
            );
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.provisional_recursive_rows.observe_capacity(
                self.provisional_recursive_rows.len() + 1);
            reservation?;
            self.provisional_recursive_rows.insert(ordinal);
            let invalidated = self.memo.invalidate_row(ordinal);
            self.memo.observe_component_external(self.source_meter)?;
            invalidated?;
        }
        let mut entry = None;
        for &(active, polarity, path_start) in &self.active {
            self.memo.work_meter.charge(1)?;
            if active == ordinal {
                entry = Some((polarity, path_start));
                break;
            }
        }
        let Some((entry_polarity, path_start)) = entry else {
            return Ok(());
        };
        self.memo.work_meter.charge(self.path.len() - path_start)?;
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut raw_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::ReentryPaths as usize,
            std::mem::size_of::<F5cTraceHop>());
        let mut path = Vec::new();
        let copied = self.path.len() - path_start;
        let memo_bytes = self.memo.retained_bytes()?;
        let before_capacity = self.memo.walker_resources.lanes
            [F5cWalkerLaneKind::ReentryPaths as usize]
            .actual_capacity;
        let reservation = self.memo.walker_resources.with_source(
            self.source_meter,
            memo_bytes,
            F5cWalkerLaneKind::ReentryPaths,
            |walker| walker.reserve_reentry_path(&mut path, copied, memo_bytes),
        );
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        raw_owner.observe(path.len(), path.capacity());
        if let Err(error) = reservation {
            let capacity = path.capacity();
            drop(path);
            if self.memo.walker_resources.lanes[F5cWalkerLaneKind::ReentryPaths as usize]
                .actual_capacity
                != before_capacity
            {
                self.memo
                    .release_reentry_path_with_source(capacity, self.source_meter)?;
            }
            return Err(error);
        }
        #[cfg(test)]
        if self.memo.fail_reserve_at
            == Some((
                F5cTestReserveFailure::ReentryPathAfterReserve,
                self.reentries.len(),
            ))
        {
            self.memo.fail_reserve_at = None;
            let capacity = path.capacity();
            drop(path);
            self.memo
                .release_reentry_path_with_source(capacity, self.source_meter)?;
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        path.extend_from_slice(&self.path[path_start..]);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        raw_owner.observe(path.len(), path.capacity());
        let mut guarded = false;
        for hop in &path {
            if let Err(error) = self.memo.work_meter.charge(1) {
                let capacity = path.capacity();
                drop(path);
                self.memo
                    .release_reentry_path_with_source(capacity, self.source_meter)?;
                return Err(error);
            }
            if matches!(hop, F5cTraceHop::Function(_)) {
                guarded = true;
                break;
            }
        }
        if guarded {
            let reservation = self.memo.reserve_walker_with_source(
                &mut self.reentries,
                F5cWalkerLaneKind::Reentries,
                self.source_meter,
            );
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.reentries_owner.observe(self.reentries.len(), self.reentries.capacity());
            if let Err(error) = reservation {
                let capacity = path.capacity();
                drop(path);
                self.memo
                    .release_reentry_path_with_source(capacity, self.source_meter)?;
                return Err(error);
            }
            self.reentries.push(F5cGuardedTrace {
                owner: ordinal,
                entry_polarity,
                reentry_polarity,
                path,
            });
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.reentries_owner.observe(self.reentries.len(), self.reentries.capacity());
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.reentry_path_owners.push(raw_owner);
        } else {
            let capacity = path.capacity();
            drop(path);
            self.memo
                .release_reentry_path_with_source(capacity, self.source_meter)?;
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn record_reentry_for_test(
        &mut self,
        ordinal: u32,
        polarity: Polarity,
    ) -> Result<(), SolveAvailabilityError> {
        self.record_reentry(ordinal, polarity)
    }

    #[cfg(test)]
    pub(super) fn structural_equal<'b>(
        &mut self,
        first: F5cCompareTask<'b, 'meter>,
        stack: &mut Vec<F5cCompareTask<'b, 'meter>>,
    ) -> Result<bool, SolveAvailabilityError> {
        self.structural_equal_with_owner(first, stack,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            None)
    }

    fn structural_equal_with_owner<'b>(
        &mut self,
        first: F5cCompareTask<'b, 'meter>,
        stack: &mut Vec<F5cCompareTask<'b, 'meter>>,
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        mut owner: Option<&mut RawWalkerOwner<'meter>>,
    ) -> Result<bool, SolveAvailabilityError> {
        macro_rules! reserve_comparison {
            () => {{
                let reservation = self.memo.reserve_walker_with_source(
                    stack, F5cWalkerLaneKind::Comparison, self.source_meter);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = owner.as_deref_mut() {
                    owner.observe(stack.len(), stack.capacity());
                }
                reservation?;
            }};
        }
        stack.clear();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if let Some(owner) = owner.as_deref_mut() { owner.observe(stack.len(), stack.capacity()); }
        self.memo.work_meter.charge(1)?;
        reserve_comparison!();
        stack.push(first);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if let Some(owner) = owner.as_deref_mut() { owner.observe(stack.len(), stack.capacity()); }
        while !stack.is_empty() {
            self.memo.work_meter.charge(1)?;
            let pair = stack.pop().expect("nonempty comparison stack");
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            if let Some(owner) = owner.as_deref_mut() { owner.observe(stack.len(), stack.capacity()); }
            match pair {
                F5cCompareTask::Positive(left, right) => match (left, right) {
                    (F5cPositive::Bottom, F5cPositive::Bottom)
                    | (F5cPositive::Int, F5cPositive::Int)
                    | (F5cPositive::Unit, F5cPositive::Unit) => {}
                    (F5cPositive::Variable(a), F5cPositive::Variable(b))
                    | (F5cPositive::Quantified(a), F5cPositive::Quantified(b))
                    | (F5cPositive::Recursive(a), F5cPositive::Recursive(b))
                        if a == b => {}
                    (F5cPositive::Shared(a), F5cPositive::Shared(b)) if a == b => {}
                    (F5cPositive::Union(a), F5cPositive::Union(b)) if a.len() == b.len() => {
                        for (left, right) in a.iter().zip(b.iter()).rev() {
                            self.memo.work_meter.charge(1)?;
                            self.memo.work_meter.charge(1)?;
                            reserve_comparison!();
                            stack.push(F5cCompareTask::Positive(left, right));
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = owner.as_deref_mut() { owner.observe(stack.len(), stack.capacity()); }
                        }
                    }
                    (
                        F5cPositive::Function {
                            argument: aa,
                            argument_effect: ae,
                            result_effect: re,
                            result: ar,
                        },
                        F5cPositive::Function {
                            argument: ba,
                            argument_effect: be,
                            result_effect: br,
                            result: b,
                        },
                    ) if ae == be && re == br => {
                        self.memo.work_meter.charge(2)?;
                        self.memo.work_meter.charge(1)?;
                        reserve_comparison!();
                        stack.push(F5cCompareTask::Positive(ar, b));
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = owner.as_deref_mut() { owner.observe(stack.len(), stack.capacity()); }
                        self.memo.work_meter.charge(1)?;
                        reserve_comparison!();
                        stack.push(F5cCompareTask::Negative(aa, ba));
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = owner.as_deref_mut() { owner.observe(stack.len(), stack.capacity()); }
                    }
                    _ => {
                        stack.clear();
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = owner.as_deref_mut() { owner.observe(stack.len(), stack.capacity()); }
                        return Ok(false);
                    }
                },
                F5cCompareTask::Negative(left, right) => match (left, right) {
                    (F5cNegative::Top, F5cNegative::Top)
                    | (F5cNegative::Bottom, F5cNegative::Bottom)
                    | (F5cNegative::Int, F5cNegative::Int)
                    | (F5cNegative::Unit, F5cNegative::Unit) => {}
                    (F5cNegative::Variable(a), F5cNegative::Variable(b))
                    | (F5cNegative::Quantified(a), F5cNegative::Quantified(b))
                    | (F5cNegative::Recursive(a), F5cNegative::Recursive(b))
                        if a == b => {}
                    (F5cNegative::Shared(a), F5cNegative::Shared(b)) if a == b => {}
                    (F5cNegative::Intersection(a), F5cNegative::Intersection(b))
                        if a.len() == b.len() =>
                    {
                        for (left, right) in a.iter().zip(b.iter()).rev() {
                            self.memo.work_meter.charge(1)?;
                            self.memo.work_meter.charge(1)?;
                            reserve_comparison!();
                            stack.push(F5cCompareTask::Negative(left, right));
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = owner.as_deref_mut() { owner.observe(stack.len(), stack.capacity()); }
                        }
                    }
                    (
                        F5cNegative::Function {
                            argument: aa,
                            argument_effect: ae,
                            result_effect: re,
                            result: ar,
                        },
                        F5cNegative::Function {
                            argument: ba,
                            argument_effect: be,
                            result_effect: br,
                            result: b,
                        },
                    ) if ae == be && re == br => {
                        self.memo.work_meter.charge(2)?;
                        self.memo.work_meter.charge(1)?;
                        reserve_comparison!();
                        stack.push(F5cCompareTask::Negative(ar, b));
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = owner.as_deref_mut() { owner.observe(stack.len(), stack.capacity()); }
                        self.memo.work_meter.charge(1)?;
                        reserve_comparison!();
                        stack.push(F5cCompareTask::Positive(aa, ba));
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = owner.as_deref_mut() { owner.observe(stack.len(), stack.capacity()); }
                    }
                    _ => {
                        stack.clear();
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = owner.as_deref_mut() { owner.observe(stack.len(), stack.capacity()); }
                        return Ok(false);
                    }
                },
            }
        }
        Ok(true)
    }

    fn walk_with<S: F5cWalkSink<'meter>>(
        &mut self,
        first: F5cWalkTask,
        sink: &mut S,
    ) -> Result<S::Value, SolveAvailabilityError> {
        let active_checkpoint = self.active.len();
        let frame_checkpoint = self.frames.len();
        let path_checkpoint = self.path.len();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut tasks_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::Tasks as usize, F5cWalkerLaneKind::Tasks.slot_size());
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut values_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::Values as usize, std::mem::size_of::<S::Value>());
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut direct_edges_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::DirectEdges as usize, F5cWalkerLaneKind::DirectEdges.slot_size());
        let mut tasks = Vec::new();
        let mut values = Vec::<S::Value>::new();
        let mut direct_edges = Vec::<(usize, u32)>::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut direct_targets = ObservedWalkerSet::new(self.source_meter, F5cWalkerLaneKind::DirectTargets);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut direct_targets = HashSet::<u32>::new();
        macro_rules! push_task {
            ($value:expr) => {{
                let value = $value;
                self.memo.work_meter.charge(1)?;
                let reservation = self.memo.reserve_walker_with_source(
                    &mut tasks,
                    F5cWalkerLaneKind::Tasks,
                    self.source_meter,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                tasks_owner.observe(tasks.len(), tasks.capacity());
                reservation?;
                tasks.push(value);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                tasks_owner.observe(tasks.len(), tasks.capacity());
            }};
        }
        macro_rules! push_value {
            ($value:expr) => {{
                self.memo.work_meter.charge(1)?; // emitted walk value
                let value = $value;
                let reservation = self.memo.reserve_walker_with_source(
                    &mut values,
                    F5cWalkerLaneKind::Values,
                    self.source_meter,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                values_owner.observe(values.len(), values.capacity());
                reservation?;
                values.push(value);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                values_owner.observe(values.len(), values.capacity());
            }};
        }
        macro_rules! push_direct {
            ($value:expr) => {{
                let value = $value;
                self.memo.work_meter.charge(1)?; // stored direct edge
                let reservation = self.memo.reserve_walker_with_source(
                    &mut direct_edges,
                    F5cWalkerLaneKind::DirectEdges,
                    self.source_meter,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                direct_edges_owner.observe(direct_edges.len(), direct_edges.capacity());
                reservation?;
                direct_edges.push(value);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                direct_edges_owner.observe(direct_edges.len(), direct_edges.capacity());
            }};
        }
        macro_rules! pop_value {
            () => {{
                let value = values.pop().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                values_owner.observe(values.len(), values.capacity());
                value
            }};
        }
        let result = (|| {
            push_task!(first);
            while !tasks.is_empty() {
                self.memo.work_meter.charge(1)?;
                let task = tasks.pop().expect("nonempty generalization tasks");
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                tasks_owner.observe(tasks.len(), tasks.capacity());
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                self.observe_guarded_progress(tasks.capacity());
                match task {
                    F5cWalkTask::EnterPath(hop) => {
                        let reservation = self.memo.reserve_walker_with_source(
                            &mut self.path,
                            F5cWalkerLaneKind::Path,
                            self.source_meter,
                        );
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        self.path_owner.observe(self.path.len(), self.path.capacity());
                        reservation?;
                        self.path.push(hop);
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        self.path_owner.observe(self.path.len(), self.path.capacity());
                    }
                    F5cWalkTask::LeavePath => {
                        self.path.pop();
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        self.path_owner.observe(self.path.len(), self.path.capacity());
                    }
                    F5cWalkTask::EnterRow {
                        row,
                        polarity,
                        root,
                    } => {
                        if self.active(row, polarity) {
                            self.taint_active_states()?;
                            self.record_reentry(row, polarity)?;
                            self.observe_walker_component()?;
                            self.mark(row, polarity)?;
                            push_value!(match polarity {
                                Polarity::Positive =>
                                    sink.variable(self, Polarity::Positive, row, false)?,
                                Polarity::Negative =>
                                    sink.variable(self, Polarity::Negative, row, false)?,
                            });
                            continue;
                        }
                        if self.active_any(row) {
                            self.taint_active_states()?;
                            self.record_reentry(row, polarity)?;
                            self.observe_walker_component()?;
                        }
                        let key = F5cExpansionKey {
                            row,
                            polarity,
                            frozen_bound_epoch: self.frozen_bound_epoch,
                        };
                        let mut warm_conflict = false;
                        if !root {
                            if let Some(id) = self.memo.roots.get(&key).copied() {
                                if self.memo.conflicts_active(key) {
                                    self.taint_active_states()?;
                                    warm_conflict = true;
                                } else {
                                    self.shared_summary_hits = self
                                        .shared_summary_hits
                                        .checked_add(self.memo.node(id)?.transitive_incidence_count)
                                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                                    push_value!(match polarity {
                                        Polarity::Positive =>
                                            sink.shared(self, Polarity::Positive, id)?,
                                        Polarity::Negative =>
                                            sink.shared(self, Polarity::Negative, id)?,
                                    });
                                    continue;
                                }
                            }
                        }
                        self.reserve_active_mirrors(!root)?;
                        if !root {
                            self.frames.push(F5cExpansionFrame {
                                tainted: self.fatal_taint || warm_conflict,
                            });
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            if self.memo.matrix_active { self.memo.matrix_generalizer_lengths[0] = self.frames.len(); }
                            #[cfg(test)]
                            self.memo.observe_physical_memo();
                        }
                        self.mark(row, polarity)?;
                        let entered = self.memo.enter_active(row);
                        self.memo.observe_component_external(self.source_meter)?;
                        entered?;
                        self.active.push((row, polarity, self.path.len()));
                        self.active_set.insert((row, polarity));
                        self.memo.generalizer_scratch_capacities[2] = self.active_set.capacity();
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if self.memo.matrix_active {
                            self.memo.matrix_generalizer_lengths[1] = self.active.len();
                            self.memo.matrix_generalizer_lengths[2] = self.active_set.len();
                        }
                        #[cfg(test)]
                        self.memo.observe_physical_memo();
                        self.observe_walker_component()?;
                        let bounds = self
                            .session
                            .bounds
                            .get(row as usize)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let start = values.len();
                        push_task!(F5cWalkTask::ExitRow {
                            row,
                            polarity,
                            root,
                            values_start: start,
                        });
                        direct_edges.clear();
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        direct_edges_owner.observe(direct_edges.len(), direct_edges.capacity());
                        if !root {
                            direct_targets.clear();
                            let direct = match polarity {
                                Polarity::Positive => &bounds.direct_lower_rows,
                                Polarity::Negative => &bounds.direct_upper_rows,
                            };
                            for (slot, target) in direct.iter().copied().enumerate() {
                                self.memo.work_meter.charge(1)?;
                                if !direct_targets.contains(&target) {
                                    let prior_capacity = self.memo.walker_resources.lanes
                                        [F5cWalkerLaneKind::DirectTargets as usize]
                                        .actual_capacity;
                                    let reservation =
                                        self.memo.reserve_walker_target(&mut direct_targets);
                                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                                    direct_targets.observe_capacity(direct_targets.len() + 1);
                                    if self.memo.walker_resources.lanes
                                        [F5cWalkerLaneKind::DirectTargets as usize]
                                        .actual_capacity
                                        != prior_capacity
                                    {
                                        self.memo.observe_walker_with_source(self.source_meter)?;
                                    }
                                    reservation?;
                                    direct_targets.insert(target);
                                    push_direct!((slot, target));
                                }
                            }
                            for (slot, target) in direct_edges.iter().rev().copied() {
                                self.memo.work_meter.charge(1)?;
                                let side = match polarity {
                                    Polarity::Positive => F5cBoundSide::Lower,
                                    Polarity::Negative => F5cBoundSide::Upper,
                                };
                                push_task!(F5cWalkTask::LeavePath);
                                push_task!(match polarity {
                                    Polarity::Positive | Polarity::Negative =>
                                        F5cWalkTask::EnterRow {
                                            row: target,
                                            polarity,
                                            root: false
                                        },
                                });
                                push_task!(F5cWalkTask::EnterPath(F5cTraceHop::Direct {
                                    side,
                                    slot,
                                    source: row,
                                    target,
                                }));
                            }
                        }
                        // The sole direct target already carries this entire lower
                        // sequence. Its traversal supplies the same positive values.
                        let mut replayed_lower = false;
                        if !root
                            && polarity == Polarity::Positive
                            && bounds.direct_lower_rows.len() == 1
                            && bounds.direct_lower_rows[0] != row
                            && !bounds.exact_non_variable_lowers.is_empty()
                            && bounds.direct_upper_rows.is_empty()
                            && bounds.exact_non_variable_uppers.is_empty()
                        {
                            self.memo.work_meter.charge(1)?;
                            if let Some(target) = self
                                .session
                                .bounds
                                .get(bounds.direct_lower_rows[0] as usize)
                            {
                                if target.direct_lower_rows.is_empty()
                                    && target.exact_non_variable_lowers.len()
                                        == bounds.exact_non_variable_lowers.len()
                                {
                                    replayed_lower = true;
                                    for (left, right) in bounds
                                        .exact_non_variable_lowers
                                        .iter()
                                        .zip(&target.exact_non_variable_lowers)
                                    {
                                        self.memo.work_meter.charge(1)?;
                                        if left != right {
                                            replayed_lower = false;
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                        let exact = match polarity {
                            Polarity::Positive => &bounds.exact_non_variable_lowers,
                            Polarity::Negative => &bounds.exact_non_variable_uppers,
                        };
                        for (slot, endpoint) in exact
                            .iter()
                            .copied()
                            .enumerate()
                            .rev()
                            .take(if replayed_lower { 0 } else { exact.len() })
                        {
                            self.memo.work_meter.charge(1)?;
                            let side = match polarity {
                                Polarity::Positive => F5cBoundSide::Lower,
                                Polarity::Negative => F5cBoundSide::Upper,
                            };
                            push_task!(F5cWalkTask::LeavePath);
                            push_task!(match polarity {
                                Polarity::Positive => F5cWalkTask::PositiveEndpoint(endpoint),
                                Polarity::Negative => F5cWalkTask::NegativeEndpoint(endpoint),
                            });
                            push_task!(F5cWalkTask::EnterPath(F5cTraceHop::Exact { side, slot }));
                        }
                    }
                    F5cWalkTask::ExitRow {
                        row,
                        polarity,
                        root,
                        values_start,
                    } => {
                        // Row entry schedules homogeneous bound children before this exit;
                        // each completed child leaves one value above values_start.
                        // Precharge the entire suffix before touching active state or values.
                        let count = values
                            .len()
                            .checked_sub(values_start)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        #[cfg(test)]
                        record_bulk_drain_boundary(
                            match polarity {
                                Polarity::Positive => F5cBulkDrainSite::RowPositive,
                                Polarity::Negative => F5cBulkDrainSite::RowNegative,
                            },
                            &self.memo.work_meter,
                            count,
                        );
                        self.memo.work_meter.charge(count)?; // drained child values
                        let left = self.memo.leave_active(row);
                        self.memo.observe_component_external(self.source_meter)?;
                        left?;
                        self.active.pop();
                        self.active_set.remove(&(row, polarity));
                        self.memo.generalizer_scratch_capacities[2] = self.active_set.capacity();
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if self.memo.matrix_active {
                            self.memo.matrix_generalizer_lengths[1] = self.active.len();
                            self.memo.matrix_generalizer_lengths[2] = self.active_set.len();
                        }
                        #[cfg(test)]
                        self.memo.observe_physical_memo();
                        self.observe_walker_component()?;
                        let value =
                            sink.finish_row(self, &mut values,
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                &mut values_owner,
                                values_start, row, polarity, root)?;
                        if root {
                            push_value!(value);
                            continue;
                        }
                        let mut frame = self
                            .frames
                            .pop()
                            .expect("non-root expansion owns one frame");
                        frame.tainted |= !sink.cacheable(&value);
                        if frame.tainted {
                            self.record_uncacheable(row, polarity)?;
                            self.taint_active_states()?;
                            push_value!(value);
                        } else {
                            let id = sink.promote(self, &value, row, polarity)?;
                            let key = F5cExpansionKey {
                                row,
                                polarity,
                                frozen_bound_epoch: self.frozen_bound_epoch,
                            };
                            let admission = self.memo.admit(key, id);
                            self.memo.observe_component_external(self.source_meter)?;
                            admission?;
                            // admit records its stable edge before any fallible observation.
                            self.observe_walker_component()?;
                            #[cfg(test)]
                            if self.assert_admission_invariant {
                                self.assert_admitted_summary_has_no_active_incidence(id);
                            }
                            push_value!(match polarity {
                                Polarity::Positive => sink.shared(self, Polarity::Positive, id)?,
                                Polarity::Negative => sink.shared(self, Polarity::Negative, id)?,
                            });
                        }
                    }
                    F5cWalkTask::PositiveEndpoint(endpoint) => push_task!(match endpoint {
                        ValueEndpointKey::IntPositive => {
                            push_value!(sink.int(self, Polarity::Positive)?);
                            continue;
                        }
                        ValueEndpointKey::UnitPositive => {
                            push_value!(sink.unit(self, Polarity::Positive)?);
                            continue;
                        }
                        ValueEndpointKey::BottomPositive => {
                            push_value!(sink.bottom(self, Polarity::Positive)?);
                            continue;
                        }
                        ValueEndpointKey::ValueRow(row) => F5cWalkTask::EnterRow {
                            row,
                            polarity: Polarity::Positive,
                            root: false
                        },
                        ValueEndpointKey::PositiveFunction(term) => F5cWalkTask::EnterTerm {
                            term,
                            polarity: Polarity::Positive
                        },
                        _ => return Err(SolveAvailabilityError::IdentityExhausted),
                    }),
                    F5cWalkTask::NegativeEndpoint(endpoint) => push_task!(match endpoint {
                        ValueEndpointKey::IntNegative => {
                            push_value!(sink.int(self, Polarity::Negative)?);
                            continue;
                        }
                        ValueEndpointKey::UnitNegative => {
                            push_value!(sink.unit(self, Polarity::Negative)?);
                            continue;
                        }
                        ValueEndpointKey::TopNegative => {
                            push_value!(sink.top(self)?);
                            continue;
                        }
                        ValueEndpointKey::BottomNegative => {
                            push_value!(sink.bottom(self, Polarity::Negative)?);
                            continue;
                        }
                        ValueEndpointKey::ValueRow(row) => F5cWalkTask::EnterRow {
                            row,
                            polarity: Polarity::Negative,
                            root: false
                        },
                        ValueEndpointKey::NegativeFunction(term) => F5cWalkTask::EnterTerm {
                            term,
                            polarity: Polarity::Negative
                        },
                        _ => return Err(SolveAvailabilityError::IdentityExhausted),
                    }),
                    F5cWalkTask::EnterTerm { term, polarity } => {
                        match (
                            polarity,
                            self.session
                                .store
                                .term_view(term)
                                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                        ) {
                            (Polarity::Positive, TermView::Leaf(Leaf::IntPositive)) => {
                                push_value!(sink.int(self, Polarity::Positive)?)
                            }
                            (Polarity::Positive, TermView::Leaf(Leaf::UnitPositive)) => {
                                push_value!(sink.unit(self, Polarity::Positive)?)
                            }
                            (Polarity::Negative, TermView::Leaf(Leaf::IntNegative)) => {
                                push_value!(sink.int(self, Polarity::Negative)?)
                            }
                            (Polarity::Negative, TermView::Leaf(Leaf::UnitNegative)) => {
                                push_value!(sink.unit(self, Polarity::Negative)?)
                            }
                            (Polarity::Positive, TermView::PositiveBottom) => {
                                push_value!(sink.bottom(self, Polarity::Positive)?)
                            }
                            (Polarity::Negative, TermView::NegativeTop) => {
                                push_value!(sink.top(self)?)
                            }
                            (Polarity::Negative, TermView::NegativeBottom) => {
                                push_value!(sink.bottom(self, Polarity::Negative)?)
                            }
                            (polarity, TermView::LiveVariable(view))
                                if view.polarity() == polarity =>
                            {
                                push_task!(match polarity {
                                    Polarity::Positive | Polarity::Negative =>
                                        F5cWalkTask::EnterRow {
                                            row: view.ordinal(),
                                            polarity,
                                            root: false
                                        },
                                })
                            }
                            (
                                Polarity::Positive,
                                TermView::PositiveFunction {
                                    argument,
                                    argument_effect,
                                    result_effect,
                                    result,
                                },
                            )
                            | (
                                Polarity::Negative,
                                TermView::NegativeFunction {
                                    argument,
                                    argument_effect,
                                    result_effect,
                                    result,
                                },
                            ) => {
                                let (argument_polarity, result_polarity) = match polarity {
                                    Polarity::Positive => (Polarity::Negative, Polarity::Positive),
                                    Polarity::Negative => (Polarity::Positive, Polarity::Negative),
                                };
                                let argument_valid =
                                    self.pure_function_effect(argument_effect, argument_polarity)?;
                                let result_valid =
                                    self.pure_function_effect(result_effect, result_polarity)?;
                                let valid = argument_valid && result_valid;
                                if !valid {
                                    self.invalid_effects = true;
                                    self.taint_failed_draft()?;
                                }
                                push_task!(F5cWalkTask::ExitFunction { polarity });
                                push_task!(F5cWalkTask::LeavePath);
                                self.memo.work_meter.charge(1)?; // result child edge
                                push_task!(match polarity {
                                    Polarity::Positive | Polarity::Negative =>
                                        F5cWalkTask::EnterTerm {
                                            term: result,
                                            polarity
                                        },
                                });
                                push_task!(F5cWalkTask::EnterPath(F5cTraceHop::Function(
                                    FunctionField::Result
                                )));
                                push_task!(F5cWalkTask::LeavePath);
                                self.memo.work_meter.charge(1)?; // argument child edge
                                push_task!(match polarity {
                                    Polarity::Positive => F5cWalkTask::EnterTerm {
                                        term: argument,
                                        polarity: Polarity::Negative
                                    },
                                    Polarity::Negative => F5cWalkTask::EnterTerm {
                                        term: argument,
                                        polarity: Polarity::Positive
                                    },
                                });
                                push_task!(F5cWalkTask::EnterPath(F5cTraceHop::Function(
                                    FunctionField::Argument
                                )));
                            }
                            _ => return Err(SolveAvailabilityError::IdentityExhausted),
                        }
                    }
                    F5cWalkTask::ExitFunction { polarity } => {
                        let result = pop_value!();
                        let argument = pop_value!();
                        push_value!(sink.function(self, polarity, argument, result)?);
                    }
                }
            }
            if values.len() != 1 {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            let result = values.pop().ok_or(SolveAvailabilityError::IdentityExhausted);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            values_owner.observe(values.len(), values.capacity());
            result
        })();
        let result = match result {
            Ok(value) => self.observe_walker_component().map(|()| value),
            Err(error) => {
                let _ = self.observe_walker_component();
                Err(error)
            }
        };
        if result.is_err() {
            while self.active.len() > active_checkpoint {
                if let Some((row, polarity, _)) = self.active.pop() {
                    self.active_set.remove(&(row, polarity));
                    self.memo.generalizer_scratch_capacities[2] = self.active_set.capacity();
                }
            }
            if !self.in_component {
                self.memo.reset_active_scratch();
            }
            self.frames.truncate(frame_checkpoint);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            if self.memo.matrix_active {
                self.memo.matrix_generalizer_lengths[0] = self.frames.len();
                self.memo.matrix_generalizer_lengths[1] = self.active.len();
                self.memo.matrix_generalizer_lengths[2] = self.active_set.len();
            }
            #[cfg(test)]
            self.memo.observe_physical_memo();
            self.path.truncate(path_checkpoint);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            self.path_owner.observe(self.path.len(), self.path.capacity());
            let _ = self.taint_active_states();
        }
        for kind in [
            F5cWalkerLaneKind::Tasks,
            F5cWalkerLaneKind::Values,
            F5cWalkerLaneKind::DirectEdges,
            F5cWalkerLaneKind::DirectTargets,
            F5cWalkerLaneKind::Comparison,
            F5cWalkerLaneKind::PositiveParts,
            F5cWalkerLaneKind::NegativeParts,
        ] {
            self.memo
                .release_walker_with_source(kind, self.source_meter)?;
        }
        result
    }

    pub(super) fn walk(
        &mut self,
        first: F5cWalkTask,
    ) -> Result<F5cWalkValue<'meter>, SolveAvailabilityError> {
        self.walk_with(first, &mut F5cBoxedWalkSink)
    }

    /// Private flat producer candidate. Production callers continue to use the boxed draft.
    #[allow(dead_code)]
    pub(super) fn build_flat_candidate(
        &mut self,
        root: u32,
        #[cfg(test)] fail_after_first_post_output: bool,
    ) -> Result<F5cNormalizedCandidate, SolveAvailabilityError> {
        let (candidate, forest) = self.build_flat_candidate_pending(
            root,
            #[cfg(test)]
            fail_after_first_post_output,
            #[cfg(test)]
            false,
        )?;
        self.release_raw_forest(forest);
        Ok(candidate)
    }

    #[allow(dead_code)]
    fn build_flat_raw_candidate_pending(
        &mut self,
        root: u32,
        #[cfg(test)] fail_after_first_post_output: bool,
    ) -> Result<(f5c_draft::FlatDraft, F5cRawForest<'meter>), SolveAvailabilityError> {
        if self.normalized_candidate_live {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let forest = self.build_raw_forest_inner(
            root,
            #[cfg(test)]
            false,
        )?;
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut positive_only = ObservedWalkerSet::new(self.source_meter,
            F5cWalkerLaneKind::BoxedPositiveOnly);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut positive_only = HashSet::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut negative_only = ObservedWalkerSet::new(self.source_meter,
            F5cWalkerLaneKind::BoxedNegativeOnly);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut negative_only = HashSet::new();
        let prepared = (|| {
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            let mut reentry_owners = HashMap::<u32, RawWalkerOwner<'_>>::new();
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            let mut boxed_map_owner = RawWalkerOwner::new(self.source_meter,
                F5cWalkerLaneKind::BoxedReentriesByOwner as usize,
                F5cWalkerLaneKind::BoxedReentriesByOwner.slot_size());
            let mut reentries_by_owner = HashMap::<u32, Vec<usize>>::new();
            for (index, trace) in self.reentries.iter().enumerate() {
                self.memo.work_meter.charge(2)?;
                let bytes = self.memo.retained_bytes()?;
                if let Some(indices) = reentries_by_owner.get_mut(&trace.owner) {
                    let reservation = self.memo
                        .walker_resources
                        .reserve_boxed_indices(indices, bytes);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    reentry_owners.get_mut(&trace.owner).expect("raw reentry owner")
                        .observe(indices.len(), indices.capacity());
                    reservation?;
                    indices.push(index);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    reentry_owners.get_mut(&trace.owner).expect("raw reentry owner")
                        .observe(indices.len(), indices.capacity());
                } else {
                    let reservation = self.memo.walker_resources.reserve_boxed_map(
                        &mut reentries_by_owner,
                        F5cWalkerLaneKind::BoxedReentriesByOwner,
                        bytes,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    boxed_map_owner.observe(reentries_by_owner.len(),
                        reentries_by_owner.capacity());
                    reservation?;
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    let mut raw_owner = RawWalkerOwner::new(self.source_meter,
                        F5cWalkerLaneKind::BoxedReentryIndices as usize,
                        std::mem::size_of::<usize>());
                    let mut indices = Vec::new();
                    let reservation = self.memo
                        .walker_resources
                        .reserve_boxed_indices(&mut indices, bytes);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    raw_owner.observe(indices.len(), indices.capacity());
                    reservation?;
                    indices.push(index);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    raw_owner.observe(indices.len(), indices.capacity());
                    reentries_by_owner.insert(trace.owner, indices);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    boxed_map_owner.observe(reentries_by_owner.len(), reentries_by_owner.capacity());
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    reentry_owners.insert(trace.owner, raw_owner);
                }
            }
            let non_generic = self.non_generic_closure()?;
            let (positive, negative) = self.flat_raw_forest_incidences(&forest)?;
            for &owner in &self.order {
                self.memo.work_meter.charge(2)?;
                let eligible = self
                    .session
                    .value_levels
                    .get(owner as usize)
                    .is_some_and(|level| *level > 0)
                    && !non_generic.contains(&owner);
                if eligible && positive.contains(&owner) && !negative.contains(&owner) {
                    self.memo.work_meter.charge(1)?;
                    let bytes = self.memo.retained_bytes()?;
                    let reservation = self.memo.walker_resources.reserve_generalizer_set(
                        &mut positive_only,
                        F5cWalkerLaneKind::BoxedPositiveOnly,
                        bytes,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    positive_only.observe_capacity(positive_only.len() + 1);
                    reservation?;
                    positive_only.insert(owner);
                    #[cfg(test)]
                    if self.memo.fail_reserve_at
                        == Some((F5cTestReserveFailure::FlatPreparationAfterPositiveOnly, 0))
                    {
                        self.memo.fail_reserve_at = None;
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    }
                }
                if eligible && negative.contains(&owner) && !positive.contains(&owner) {
                    self.memo.work_meter.charge(1)?;
                    let bytes = self.memo.retained_bytes()?;
                    let reservation = self.memo.walker_resources.reserve_generalizer_set(
                        &mut negative_only,
                        F5cWalkerLaneKind::BoxedNegativeOnly,
                        bytes,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    negative_only.observe_capacity(negative_only.len() + 1);
                    reservation?;
                    negative_only.insert(owner);
                }
            }
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            let reentries_by_owner = ObservedReentryMap {
                values: reentries_by_owner, _map_owner: boxed_map_owner,
                _index_owners: reentry_owners,
            };
            Ok::<_, SolveAvailabilityError>((reentries_by_owner, non_generic, positive, negative))
        })();
        let (reentries_by_owner, non_generic, positive, negative) = match prepared {
            Ok(values) => values,
            Err(error) => {
                drop(positive_only);
                drop(negative_only);
                self.release_flat_candidate_one_sided_lanes();
                let rollback = self.abort_raw_forest(forest);
                self.release_flat_candidate_preparation_lanes();
                rollback?;
                return Err(error);
            }
        };
        let session = self.session;
        let eligible = |ordinal: u32| {
            session
                .value_levels
                .get(ordinal as usize)
                .is_some_and(|level| *level > 0)
                && !non_generic.contains(&ordinal)
        };
        let reentries = std::mem::take(&mut self.reentries);
        let order = std::mem::take(&mut self.order);
        let selected = self.flat_r_q_with_raw_forest_candidate_inner(
            forest,
            &reentries,
            &reentries_by_owner,
            &order,
            eligible,
            &positive,
            &negative,
            &positive_only,
            &negative_only,
            #[cfg(test)]
            fail_after_first_post_output,
        );
        match selected {
            Ok(selected) => {
                self.reentries = reentries;
                self.order = order;
                let selected = Ok(selected);
                drop(reentries_by_owner);
                drop(non_generic);
                drop(positive);
                drop(negative);
                self.release_flat_candidate_preparation_lanes();
                let finished = selected.and_then(|(selection, output, forest)| {
                    self.flat_finish_selected_raw_pending(
                        selection,
                        output,
                        forest,
                        &positive_only,
                        &negative_only,
                    )
                });
                drop(positive_only);
                drop(negative_only);
                self.release_flat_candidate_one_sided_lanes();
                return finished;
            }
            Err((error, forest)) => {
                drop(reentries);
                drop(order);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                {
                    self.reentries_owner = RawWalkerOwner::new(self.source_meter,
                        F5cWalkerLaneKind::Reentries as usize,
                        F5cWalkerLaneKind::Reentries.slot_size());
                    self.order_owner = RawWalkerOwner::new(self.source_meter,
                        F5cWalkerLaneKind::Order as usize,
                        F5cWalkerLaneKind::Order.slot_size());
                }
                drop(reentries_by_owner);
                drop(non_generic);
                drop(positive);
                drop(negative);
                drop(positive_only);
                drop(negative_only);
                self.release_flat_candidate_preparation_lanes();
                self.release_flat_candidate_one_sided_lanes();
                self.abort_raw_forest(forest)?;
                return Err(error);
            }
        }
    }

    fn build_flat_candidate_pending(
        &mut self,
        root: u32,
        #[cfg(test)] fail_after_first_post_output: bool,
        #[cfg(test)] fail_during_normalization: bool,
    ) -> Result<(F5cNormalizedCandidate, F5cRawForest<'meter>), SolveAvailabilityError> {
        if self.normalized_candidate_live {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let forest = self.build_raw_forest_inner(
            root,
            #[cfg(test)]
            false,
        )?;
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut positive_only = ObservedWalkerSet::new(self.source_meter,
            F5cWalkerLaneKind::BoxedPositiveOnly);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut positive_only = HashSet::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut negative_only = ObservedWalkerSet::new(self.source_meter,
            F5cWalkerLaneKind::BoxedNegativeOnly);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut negative_only = HashSet::new();
        let prepared = (|| {
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            let mut reentry_owners = HashMap::<u32, RawWalkerOwner<'_>>::new();
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            let mut boxed_map_owner = RawWalkerOwner::new(self.source_meter,
                F5cWalkerLaneKind::BoxedReentriesByOwner as usize,
                F5cWalkerLaneKind::BoxedReentriesByOwner.slot_size());
            let mut reentries_by_owner = HashMap::<u32, Vec<usize>>::new();
            for (index, trace) in self.reentries.iter().enumerate() {
                self.memo.work_meter.charge(2)?;
                let bytes = self.memo.retained_bytes()?;
                if let Some(indices) = reentries_by_owner.get_mut(&trace.owner) {
                    let reservation = self.memo
                        .walker_resources
                        .reserve_boxed_indices(indices, bytes);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    reentry_owners.get_mut(&trace.owner).expect("raw reentry owner")
                        .observe(indices.len(), indices.capacity());
                    reservation?;
                    indices.push(index);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    reentry_owners.get_mut(&trace.owner).expect("raw reentry owner")
                        .observe(indices.len(), indices.capacity());
                } else {
                    let reservation = self.memo.walker_resources.reserve_boxed_map(
                        &mut reentries_by_owner,
                        F5cWalkerLaneKind::BoxedReentriesByOwner,
                        bytes,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    boxed_map_owner.observe(reentries_by_owner.len(),
                        reentries_by_owner.capacity());
                    reservation?;
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    let mut raw_owner = RawWalkerOwner::new(self.source_meter,
                        F5cWalkerLaneKind::BoxedReentryIndices as usize,
                        std::mem::size_of::<usize>());
                    let mut indices = Vec::new();
                    let reservation = self.memo
                        .walker_resources
                        .reserve_boxed_indices(&mut indices, bytes);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    raw_owner.observe(indices.len(), indices.capacity());
                    reservation?;
                    indices.push(index);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    raw_owner.observe(indices.len(), indices.capacity());
                    reentries_by_owner.insert(trace.owner, indices);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    boxed_map_owner.observe(reentries_by_owner.len(), reentries_by_owner.capacity());
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    reentry_owners.insert(trace.owner, raw_owner);
                }
            }
            let non_generic = self.non_generic_closure()?;
            let (positive, negative) = self.flat_raw_forest_incidences(&forest)?;
            for &owner in &self.order {
                self.memo.work_meter.charge(2)?;
                let eligible = self
                    .session
                    .value_levels
                    .get(owner as usize)
                    .is_some_and(|level| *level > 0)
                    && !non_generic.contains(&owner);
                if eligible && positive.contains(&owner) && !negative.contains(&owner) {
                    self.memo.work_meter.charge(1)?;
                    let bytes = self.memo.retained_bytes()?;
                    let reservation = self.memo.walker_resources.reserve_generalizer_set(
                        &mut positive_only,
                        F5cWalkerLaneKind::BoxedPositiveOnly,
                        bytes,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    positive_only.observe_capacity(positive_only.len() + 1);
                    reservation?;
                    positive_only.insert(owner);
                    #[cfg(test)]
                    if self.memo.fail_reserve_at
                        == Some((F5cTestReserveFailure::FlatPreparationAfterPositiveOnly, 0))
                    {
                        self.memo.fail_reserve_at = None;
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    }
                }
                if eligible && negative.contains(&owner) && !positive.contains(&owner) {
                    self.memo.work_meter.charge(1)?;
                    let bytes = self.memo.retained_bytes()?;
                    let reservation = self.memo.walker_resources.reserve_generalizer_set(
                        &mut negative_only,
                        F5cWalkerLaneKind::BoxedNegativeOnly,
                        bytes,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    negative_only.observe_capacity(negative_only.len() + 1);
                    reservation?;
                    negative_only.insert(owner);
                }
            }
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            let reentries_by_owner = ObservedReentryMap {
                values: reentries_by_owner, _map_owner: boxed_map_owner,
                _index_owners: reentry_owners,
            };
            Ok::<_, SolveAvailabilityError>((reentries_by_owner, non_generic, positive, negative))
        })();
        let (reentries_by_owner, non_generic, positive, negative) = match prepared {
            Ok(values) => values,
            Err(error) => {
                drop(positive_only);
                drop(negative_only);
                self.release_flat_candidate_one_sided_lanes();
                let rollback = self.abort_raw_forest(forest);
                self.release_flat_candidate_preparation_lanes();
                rollback?;
                return Err(error);
            }
        };
        let session = self.session;
        let eligible = |ordinal: u32| {
            session
                .value_levels
                .get(ordinal as usize)
                .is_some_and(|level| *level > 0)
                && !non_generic.contains(&ordinal)
        };
        let reentries = std::mem::take(&mut self.reentries);
        let order = std::mem::take(&mut self.order);
        let selected = self.flat_r_q_with_raw_forest_candidate_inner(
            forest,
            &reentries,
            &reentries_by_owner,
            &order,
            eligible,
            &positive,
            &negative,
            &positive_only,
            &negative_only,
            #[cfg(test)]
            fail_after_first_post_output,
        );
        match selected {
            Ok(selected) => {
                self.reentries = reentries;
                self.order = order;
                let selected = Ok(selected);
                drop(reentries_by_owner);
                drop(non_generic);
                drop(positive);
                drop(negative);
                self.release_flat_candidate_preparation_lanes();
                let finished = selected.and_then(|(selection, output, forest)| {
                    self.flat_finish_selected_candidate_pending(
                        selection,
                        output,
                        forest,
                        &positive_only,
                        &negative_only,
                        #[cfg(test)]
                        fail_during_normalization,
                    )
                });
                drop(positive_only);
                drop(negative_only);
                self.release_flat_candidate_one_sided_lanes();
                return finished;
            }
            Err((error, forest)) => {
                drop(reentries);
                drop(order);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                {
                    self.reentries_owner = RawWalkerOwner::new(self.source_meter,
                        F5cWalkerLaneKind::Reentries as usize,
                        F5cWalkerLaneKind::Reentries.slot_size());
                    self.order_owner = RawWalkerOwner::new(self.source_meter,
                        F5cWalkerLaneKind::Order as usize,
                        F5cWalkerLaneKind::Order.slot_size());
                }
                drop(reentries_by_owner);
                drop(non_generic);
                drop(positive);
                drop(negative);
                drop(positive_only);
                drop(negative_only);
                self.release_flat_candidate_preparation_lanes();
                self.release_flat_candidate_one_sided_lanes();
                self.abort_raw_forest(forest)?;
                return Err(error);
            }
        }
    }

    /// Keep this member's memo transaction open until its candidate owns a
    /// reserved SCC slot. Earlier staged members retain their own ownership.
    #[allow(dead_code)]
    pub(super) fn build_and_stage_flat_candidate(
        self,
        root: u32,
        staged: &mut TrackedVec<'meter, F5cStagedCandidate<'meter>>,
    ) -> (
        Result<f5c_normalization::FlatNormalizationStats, SolveAvailabilityError>,
        F5cComponentExpansionMemo,
        usize,
        usize,
    ) {
        self.build_and_stage_flat_candidate_inner(
            root,
            staged,
            false,
            #[cfg(test)]
            false,
        )
    }

    fn build_and_stage_flat_candidate_inner(
        mut self,
        root: u32,
        staged: &mut TrackedVec<'meter, F5cStagedCandidate<'meter>>,
        fail_observe: bool,
        #[cfg(test)] fail_during_normalization: bool,
    ) -> (
        Result<f5c_normalization::FlatNormalizationStats, SolveAvailabilityError>,
        F5cComponentExpansionMemo,
        usize,
        usize,
    ) {
        let result = self.build_flat_candidate_pending(
            root,
            #[cfg(test)]
            false,
            #[cfg(test)]
            fail_during_normalization,
        );
        let result = result.and_then(|(candidate, forest)| {
            let stats = f5c_normalization::FlatNormalizationStats {
                key_writes: candidate.stats.key_writes,
                child_comparisons: candidate.stats.child_comparisons,
                descriptor_words: candidate.stats.descriptor_words,
                word_comparisons: candidate.stats.word_comparisons,
                duplicates: candidate.stats.duplicates,
                resource: None,
            };
            let hits = self.shared_summary_hits;
            let uncacheable = self.uncacheable_states;
            match self.stage_normalized_candidate_inner(staged, candidate, false, fail_observe) {
                Ok(()) => {
                    #[cfg(test)]
                    self.record_transfer_raw_staged(&forest, staged);
                    self.release_raw_forest(forest);
                    Ok((stats, hits, uncacheable))
                }
                Err(error) => {
                    self.abort_raw_forest(forest)?;
                    Err(error)
                }
            }
        });
        let (result, hits, uncacheable) = match result {
            Ok((stats, hits, uncacheable)) => (Ok(stats), hits, uncacheable),
            Err(error) => (
                Err(error),
                self.shared_summary_hits,
                self.uncacheable_states,
            ),
        };
        (result, self.memo, hits, uncacheable)
    }

    #[cfg(test)]
    pub(super) fn build_and_stage_flat_candidate_with_failure(
        self,
        root: u32,
        staged: &mut TrackedVec<'meter, F5cStagedCandidate<'meter>>,
    ) -> (
        Result<f5c_normalization::FlatNormalizationStats, SolveAvailabilityError>,
        F5cComponentExpansionMemo,
        usize,
        usize,
    ) {
        self.build_and_stage_flat_candidate_inner(root, staged, true, false)
    }

    #[cfg(test)]
    fn record_transfer_raw_staged(
        &mut self,
        forest: &F5cRawForest<'meter>,
        staged: &TrackedVec<'meter, F5cStagedCandidate<'meter>>,
    ) {
        fn bytes<T>(capacity: usize) -> u128 {
            capacity as u128 * std::mem::size_of::<T>() as u128
        }
        let raw = &forest.draft;
        let raw_lanes = [
            (
                F5cWalkerLaneKind::DraftPositiveNodes,
                raw.positive_nodes.capacity(),
            ),
            (
                F5cWalkerLaneKind::DraftNegativeNodes,
                raw.negative_nodes.capacity(),
            ),
            (
                F5cWalkerLaneKind::DraftPositiveChildren,
                raw.positive_children.capacity(),
            ),
            (
                F5cWalkerLaneKind::DraftNegativeChildren,
                raw.negative_children.capacity(),
            ),
            (
                F5cWalkerLaneKind::DraftRecursiveBounds,
                raw.recursive_bounds.capacity(),
            ),
            (
                F5cWalkerLaneKind::DraftInsertionOrder,
                raw.insertion_order.capacity(),
            ),
            (
                F5cWalkerLaneKind::RawOwnerOrder,
                forest.raw_owner_order.capacity(),
            ),
            (
                F5cWalkerLaneKind::RawOwnerBounds,
                forest.raw_bounds.capacity(),
            ),
            (
                F5cWalkerLaneKind::RawCallbackTrace,
                forest.callback_trace.capacity(),
            ),
        ];
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if self.memo.matrix_active {
            self.memo.matrix_transfer_raw_capacity = Some(raw_lanes.map(|(_, capacity)| capacity));
        } else {
            self.memo.transfer_raw_capacity_samples.push(raw_lanes.map(|(_, capacity)| capacity));
        }
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        self.memo.transfer_raw_capacity_samples.push(raw_lanes.map(|(_, capacity)| capacity));
        let raw_bytes: u128 = raw_lanes
            .into_iter()
            .map(|(kind, capacity)| {
                assert_eq!(
                    self.memo.walker_resources.lanes[kind as usize].actual_capacity,
                    capacity
                );
                capacity as u128 * kind.slot_size() as u128
            })
            .sum();
        // The last successful transfer supplies the previous census. A fresh
        // batch starts with only the already reserved outer staging vector.
        let draft = &staged
            .last()
            .expect("successful stage appended a member")
            .candidate
            .draft;
        let previous_staged = if staged.len() == 1 {
            None
        } else {
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            let matrix = self.memo.matrix_active
                .then_some(self.memo.matrix_transfer_raw_staged)
                .flatten().map(|sample| sample.1);
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            let matrix = None;
            matrix.or_else(|| self.memo.transfer_raw_staged_samples.last().map(|sample| sample.1))
        };
        let previous_staged = if let Some(previous_staged) = previous_staged {
            previous_staged
        } else {
            bytes::<F5cStagedCandidate<'_>>(staged.capacity())
        };
        let staged_bytes = previous_staged
            + bytes::<f5c_draft::PositiveNode>(draft.positive_nodes.capacity())
            + bytes::<f5c_draft::NegativeNode>(draft.negative_nodes.capacity())
            + bytes::<f5c_draft::PositiveId>(draft.positive_children.capacity())
            + bytes::<f5c_draft::NegativeId>(draft.negative_children.capacity())
            + bytes::<f5c_draft::RecursiveBound>(draft.recursive_bounds.capacity())
            + bytes::<f5c_draft::NodeRef>(draft.insertion_order.capacity());
        assert_eq!(
            self.source_meter.current_bytes(),
            Some(staged_bytes as usize)
        );
        self.observe_staged_physical_source(staged_bytes);
        let joint = &self.memo.walker_resources.physical_joint;
        assert!(joint.walker_current >= raw_bytes);
        let total = staged_bytes + joint.source_current + joint.memo_current + joint.walker_current;
        assert!(joint.peak >= total);
        let physical_memo = self.memo.retained_bytes().expect("memo capacities fit") as u128;
        let physical_walker = self.memo.walker_resources.physical_walker_bytes();
        let physical_source: u128 = joint
            .source_capacities
            .into_iter()
            .zip([
                std::mem::size_of::<GeneralizationDraft>(),
                std::mem::size_of::<TrackedAllocation<'static>>(),
                std::mem::size_of::<F5cRecursiveBound>(),
                std::mem::size_of::<F5cRecursiveBound>(),
            ])
            .map(|(capacity, size)| capacity * size as u128)
            .sum();
        let physical = (
            raw_bytes,
            staged_bytes,
            physical_source,
            physical_memo,
            physical_walker,
        );
        let live = (
            joint.source_capacities,
            self.memo.live_capacity_snapshot(),
            self.memo
                .walker_resources
                .independent_lanes
                .map(|lane| lane.actual_capacity),
            self.memo.walker_resources.value_slot_size,
        );
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if self.memo.matrix_active {
            self.memo.matrix_transfer_physical = Some(physical);
            self.memo.matrix_transfer_live_capacity = Some(live);
            self.memo.matrix_transfer_raw_staged = Some((raw_bytes, staged_bytes, total));
            self.memo.matrix_transfer_count += 1;
        } else {
            self.memo.transfer_physical_samples.push(physical);
            self.memo.transfer_live_capacity_samples.push(live);
            self.memo.transfer_raw_staged_samples.push((raw_bytes, staged_bytes, total));
        }
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        {
            self.memo.transfer_physical_samples.push(physical);
            self.memo.transfer_live_capacity_samples.push(live);
            self.memo.transfer_raw_staged_samples.push((raw_bytes, staged_bytes, total));
        }
    }

    fn release_flat_candidate_one_sided_lanes(&mut self) {
        for kind in [
            F5cWalkerLaneKind::BoxedPositiveOnly,
            F5cWalkerLaneKind::BoxedNegativeOnly,
        ] {
            self.memo.walker_resources.release(kind);
        }
    }

    fn release_flat_candidate_preparation_lanes(&mut self) {
        for kind in [
            F5cWalkerLaneKind::BoxedReentriesByOwner,
            F5cWalkerLaneKind::BoxedReentryIndices,
            F5cWalkerLaneKind::ClosureResult,
            F5cWalkerLaneKind::RawPositiveIncidences,
            F5cWalkerLaneKind::RawNegativeIncidences,
        ] {
            self.memo.walker_resources.release(kind);
        }
    }

    pub(super) fn walk_flat(
        &mut self,
        first: F5cWalkTask,
    ) -> Result<FlatWalkValue, SolveAvailabilityError> {
        if self.raw_forest_live || self.raw_forest_rollback_failed {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        // The source and memo have the same owner. Keep the sink attached even
        // when a walk fails so retained capacities remain accounted for.
        let mut sink = std::mem::take(&mut self.flat_sink);
        let result = self.walk_flat_with_sink(first, &mut sink);
        self.flat_sink = sink;
        result
    }

    #[cfg(test)]
    pub(super) fn build_raw_forest(
        &mut self,
        root: u32,
    ) -> Result<F5cRawForest<'meter>, SolveAvailabilityError> {
        self.build_raw_forest_with_bound_reinsertion_for_test(root, false)
    }

    #[cfg(test)]
    pub(super) fn build_raw_forest_with_bound_reinsertion_for_test(
        &mut self,
        root: u32,
        reverse_bounds: bool,
    ) -> Result<F5cRawForest<'meter>, SolveAvailabilityError> {
        self.build_raw_forest_inner(root, reverse_bounds)
    }

    fn build_raw_forest_inner(
        &mut self,
        root: u32,
        #[cfg(test)] reverse_bounds: bool,
    ) -> Result<F5cRawForest<'meter>, SolveAvailabilityError> {
        if self.raw_forest_live || self.raw_forest_rollback_failed {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        use f5c_draft::{NegativeId, NodeRef, PositiveId};
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut raw_owner_order_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::RawOwnerOrder as usize,
            F5cWalkerLaneKind::RawOwnerOrder.slot_size());
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut roots_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::RawRoots as usize,
            F5cWalkerLaneKind::RawRoots.slot_size());
        let mut raw_owner_order = Vec::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut raw_bounds_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::RawOwnerBounds as usize,
            F5cWalkerLaneKind::RawOwnerBounds.slot_size());
        let mut raw_bounds = HashMap::<u32, (PositiveId, NegativeId)>::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut seen_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::RawOwnerSeen as usize,
            F5cWalkerLaneKind::RawOwnerSeen.slot_size());
        let mut seen = HashSet::<u32>::new();
        let mut roots = Vec::<FlatWalkValue>::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut outputs_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::FlatSourceMaterializeRoots as usize,
            F5cWalkerLaneKind::FlatSourceMaterializeRoots.slot_size());
        let mut outputs = Vec::<NodeRef>::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut callback_trace_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::RawCallbackTrace as usize,
            F5cWalkerLaneKind::RawCallbackTrace.slot_size());
        #[cfg(test)]
        let mut callback_trace = Vec::<(u32, Polarity)>::new();
        let mut draft = f5c_draft::FlatDraft::default();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        draft.attach_owners(self.source_meter, [
            F5cWalkerLaneKind::DraftPositiveNodes as usize,
            F5cWalkerLaneKind::DraftNegativeNodes as usize,
            F5cWalkerLaneKind::DraftPositiveChildren as usize,
            F5cWalkerLaneKind::DraftNegativeChildren as usize,
            F5cWalkerLaneKind::DraftRecursiveBounds as usize,
            F5cWalkerLaneKind::DraftInsertionOrder as usize,
        ]);
        let result = (|| {
            let predicate = self.walk_flat(F5cWalkTask::EnterRow {
                row: root,
                polarity: Polarity::Positive,
                root: true,
            })?;
            checked_raw_root_append(roots.len(), 1)?;
            let bytes = self.memo.retained_bytes()?;
            let reservation = self.memo.walker_resources.reserve(
                &mut roots,
                F5cWalkerLaneKind::RawRoots,
                1,
                bytes,
            );
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            roots_owner.observe(roots.len(), roots.capacity());
            reservation?;
            roots.push(predicate);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            roots_owner.observe(roots.len(), roots.capacity());
            let mut next_owner = 0;
            while next_owner < self.reentries.len() {
                self.memo.work_meter.charge(1)?;
                let owner = self.reentries[next_owner].owner;
                next_owner += 1;
                self.memo.work_meter.charge(1)?;
                if seen.contains(&owner) {
                    continue;
                }
                let bytes = self.memo.retained_bytes()?;
                let reservation = self.memo
                    .walker_resources
                    .reserve_raw_set(&mut seen, bytes);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                seen_owner.observe(seen.len(), seen.capacity());
                reservation?;
                seen.insert(owner);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                seen_owner.observe(seen.len(), seen.capacity());
                let bounds = self
                    .session
                    .bounds
                    .get(owner as usize)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                let has_lower = !bounds.exact_non_variable_lowers.is_empty()
                    || !bounds.direct_lower_rows.is_empty();
                let has_upper = !bounds.exact_non_variable_uppers.is_empty()
                    || !bounds.direct_upper_rows.is_empty();
                let lower = self.walk_flat(F5cWalkTask::EnterRow {
                    row: owner,
                    polarity: Polarity::Positive,
                    root: false,
                })?;
                let upper = self.walk_flat(F5cWalkTask::EnterRow {
                    row: owner,
                    polarity: Polarity::Negative,
                    root: false,
                })?;
                let lower = if has_lower {
                    lower
                } else {
                    let mut sink = std::mem::take(&mut self.flat_sink);
                    let value = sink.bottom(self, Polarity::Positive);
                    self.flat_sink = sink;
                    value?
                };
                let upper = if has_upper {
                    upper
                } else {
                    let mut sink = std::mem::take(&mut self.flat_sink);
                    let value = sink.top(self);
                    self.flat_sink = sink;
                    value?
                };
                self.memo.work_meter.charge(2)?;
                let lower_index = checked_raw_root_append(roots.len(), 2)?;
                let bytes = self.memo.retained_bytes()?;
                let order_reservation = self.memo.walker_resources.reserve(
                    &mut raw_owner_order,
                    F5cWalkerLaneKind::RawOwnerOrder,
                    1,
                    bytes,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                raw_owner_order_owner.observe(raw_owner_order.len(), raw_owner_order.capacity());
                order_reservation?;
                let roots_reservation = self.memo.walker_resources.reserve(
                    &mut roots,
                    F5cWalkerLaneKind::RawRoots,
                    2,
                    bytes,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                roots_owner.observe(roots.len(), roots.capacity());
                roots_reservation?;
                let reservation = self.memo
                    .walker_resources
                    .reserve_raw_map(&mut raw_bounds, bytes);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                raw_bounds_owner.observe(raw_bounds.len(), raw_bounds.capacity());
                reservation?;
                roots.push(lower);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                roots_owner.observe(roots.len(), roots.capacity());
                roots.push(upper);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                roots_owner.observe(roots.len(), roots.capacity());
                raw_owner_order.push(owner);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                raw_owner_order_owner.observe(raw_owner_order.len(), raw_owner_order.capacity());
                // The indices are replaced with draft IDs after one ordered batch.
                raw_bounds.insert(
                    owner,
                    (
                        PositiveId(
                            u32::try_from(lower_index)
                                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                        ),
                        NegativeId(
                            u32::try_from(lower_index + 1)
                                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                        ),
                    ),
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                raw_bounds_owner.observe(raw_bounds.len(), raw_bounds.capacity());
            }
            if self.invalid_effects {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            #[cfg(test)]
            if reverse_bounds {
                for owner in raw_owner_order.iter().rev() {
                    let bounds = raw_bounds
                        .remove(owner)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    raw_bounds_owner.observe(raw_bounds.len(), raw_bounds.capacity());
                    raw_bounds.insert(*owner, bounds);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    raw_bounds_owner.observe(raw_bounds.len(), raw_bounds.capacity());
                }
            }
            let memo = &mut self.memo;
            let sink = &self.flat_sink;
            #[cfg(test)]
            {
                let bytes = memo.retained_bytes()?;
                let reservation = memo.walker_resources.reserve(
                    &mut callback_trace,
                    F5cWalkerLaneKind::RawCallbackTrace,
                    0,
                    bytes,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                callback_trace_owner.observe(callback_trace.len(), callback_trace.capacity());
                reservation?;
                memo.walker_resources.observe_memo(bytes)?;
            }
            sink.materialize_roots(
                memo,
                &mut draft,
                &roots,
                &mut outputs,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                Some(&mut outputs_owner),
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                Some(self.source_meter),
                |#[allow(unused_variables)] resources,
                 #[allow(unused_variables)] memo_bytes,
                 #[allow(unused_variables)] row,
                 #[allow(unused_variables)] polarity| {
                    #[cfg(test)]
                    {
                        let reservation = resources.reserve(
                            &mut callback_trace,
                            F5cWalkerLaneKind::RawCallbackTrace,
                            1,
                            memo_bytes,
                        );
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        callback_trace_owner.observe(callback_trace.len(), callback_trace.capacity());
                        reservation?;
                        callback_trace.push((row, polarity));
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        callback_trace_owner.observe(callback_trace.len(), callback_trace.capacity());
                    }
                    Ok(())
                },
            )?;
            let NodeRef::Positive(predicate) = outputs[0] else {
                return Err(SolveAvailabilityError::IdentityExhausted);
            };
            draft.predicate = Some(predicate);
            for owner in &raw_owner_order {
                let (lower_index, upper_index) = raw_bounds
                    .get(owner)
                    .copied()
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                let NodeRef::Positive(lower) = outputs[lower_index.0 as usize] else {
                    return Err(SolveAvailabilityError::IdentityExhausted);
                };
                let NodeRef::Negative(upper) = outputs[upper_index.0 as usize] else {
                    return Err(SolveAvailabilityError::IdentityExhausted);
                };
                raw_bounds.insert(*owner, (lower, upper));
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                raw_bounds_owner.observe(raw_bounds.len(), raw_bounds.capacity());
            }
            Ok(())
        })();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let had_outputs_capacity = outputs.capacity() != 0;
        drop(outputs);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        drop(outputs_owner);
        self.flat_sink.release_materialized_roots(&mut self.memo);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let result = if had_outputs_capacity {
            self.memo.observe_walker_with_source(self.source_meter).and(result)
        } else {
            result
        };
        drop(roots);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        drop(roots_owner);
        self.memo
            .walker_resources
            .release(F5cWalkerLaneKind::RawRoots);
        drop(seen);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        drop(seen_owner);
        self.memo
            .walker_resources
            .release(F5cWalkerLaneKind::RawOwnerSeen);
        if let Err(error) = result {
            drop(draft);
            for kind in [
                F5cWalkerLaneKind::DraftPositiveNodes,
                F5cWalkerLaneKind::DraftNegativeNodes,
                F5cWalkerLaneKind::DraftPositiveChildren,
                F5cWalkerLaneKind::DraftNegativeChildren,
                F5cWalkerLaneKind::DraftRecursiveBounds,
                F5cWalkerLaneKind::DraftInsertionOrder,
            ] {
                self.memo.walker_resources.release(kind);
            }
            drop(raw_owner_order);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            drop(raw_owner_order_owner);
            drop(raw_bounds);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            drop(raw_bounds_owner);
            #[cfg(test)]
            drop(callback_trace);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            drop(callback_trace_owner);
            self.memo
                .walker_resources
                .release(F5cWalkerLaneKind::RawOwnerOrder);
            self.memo
                .walker_resources
                .release(F5cWalkerLaneKind::RawOwnerBounds);
            self.memo
                .walker_resources
                .release(F5cWalkerLaneKind::RawCallbackTrace);
            self.abort_flat_component()?;
            return Err(error);
        }
        drop(std::mem::take(&mut self.flat_sink.arena));
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        {
            let fresh = Self::new_source_arena_owners(self.source_meter);
            drop(std::mem::replace(&mut self.source_arena_owners, fresh));
        }
        self.flat_sink.component_checkpoint = None;
        self.flat_sink.counter_checkpoint = None;
        for kind in [
            F5cWalkerLaneKind::SourcePositiveNodes,
            F5cWalkerLaneKind::SourceNegativeNodes,
            F5cWalkerLaneKind::SourcePositiveChildren,
            F5cWalkerLaneKind::SourceNegativeChildren,
        ] {
            self.memo.walker_resources.release(kind);
        }
        self.raw_forest_live = true;
        Ok(F5cRawForest {
            draft,
            raw_owner_order,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            raw_owner_order_owner,
            raw_bounds,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            raw_bounds_owner,
            #[cfg(test)]
            callback_trace,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            callback_trace_owner,
        })
    }

    pub(super) fn release_raw_forest(&mut self, forest: F5cRawForest<'meter>) {
        assert!(
            self.raw_forest_live,
            "one live raw forest owns the candidate output lanes"
        );
        self.memo
            .finish_root_transaction(self.root_undo_checkpoint, true)
            .expect("raw forest commit must use its live root checkpoint");
        self.release_raw_forest_lanes(forest);
        self.node_checkpoint = self.memo.nodes.len();
        self.child_checkpoint = self.memo.children.len();
        self.reverse_checkpoint = self.memo.reverse_parents.len();
        self.incidence_checkpoint = self.memo.incidences.len();
        self.root_undo_checkpoint = self.memo.root_undo.len();
        self.reset_after_raw_forest();
    }

    #[allow(dead_code)]
    fn release_raw_forest_for_batch(&mut self, forest: F5cRawForest<'meter>) {
        assert!(self.raw_forest_live);
        self.release_raw_forest_lanes(forest);
        self.reset_after_raw_forest();
        #[cfg(test)]
        self.memo.observe_physical_memo();
    }

    pub(super) fn abort_raw_forest(
        &mut self,
        forest: F5cRawForest<'meter>,
    ) -> Result<(), SolveAvailabilityError> {
        assert!(self.raw_forest_live);
        self.release_raw_forest_lanes(forest);
        let rollback = self.abort_flat_component();
        self.reset_after_raw_forest();
        rollback
    }

    fn release_raw_forest_lanes(&mut self, forest: F5cRawForest<'meter>) {
        drop(forest);
        for kind in [
            F5cWalkerLaneKind::RawOwnerOrder,
            F5cWalkerLaneKind::RawOwnerBounds,
            F5cWalkerLaneKind::RawCallbackTrace,
            F5cWalkerLaneKind::DraftPositiveNodes,
            F5cWalkerLaneKind::DraftNegativeNodes,
            F5cWalkerLaneKind::DraftPositiveChildren,
            F5cWalkerLaneKind::DraftNegativeChildren,
            F5cWalkerLaneKind::DraftRecursiveBounds,
            F5cWalkerLaneKind::DraftInsertionOrder,
        ] {
            self.memo.walker_resources.release(kind);
        }
    }

    fn reset_after_raw_forest(&mut self) {
        self.memo.reset_active_scratch();
        self.frames = Vec::new();
        self.active = Vec::new();
        self.active_set = HashSet::new();
        self.release_persistent_lanes();
        self.memo.generalizer_scratch_capacities = [0; 4];
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if self.memo.matrix_active {
            self.memo.matrix_generalizer_lengths = [0; 4];
            for lane in 16..20 { self.memo.matrix_owner_events.release(lane); }
        }
        #[cfg(test)]
        self.memo.observe_physical_memo();
        self.shared_summary_hits = 0;
        self.uncacheable_states = 0;
        self.fatal_taint = false;
        self.invalid_effects = false;
        self.in_component = false;
        self.raw_forest_live = false;
    }

    fn walk_flat_with_sink(
        &mut self,
        first: F5cWalkTask,
        sink: &mut F5cFlatWalkSink,
    ) -> Result<FlatWalkValue, SolveAvailabilityError> {
        let checkpoint = *sink
            .component_checkpoint
            .get_or_insert_with(|| sink.arena.checkpoint());
        let counter_checkpoint = *sink
            .counter_checkpoint
            .get_or_insert((self.shared_summary_hits, self.uncacheable_states));
        self.in_component = true;
        let result = self.walk_with(first, sink);
        if result.is_err() {
            sink.arena.rollback(checkpoint);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            for (owner, (len, capacity)) in self.source_arena_owners.iter_mut().zip([
                (sink.arena.positive_nodes.len(), sink.arena.positive_nodes.capacity()),
                (sink.arena.negative_nodes.len(), sink.arena.negative_nodes.capacity()),
                (sink.arena.positive_children.len(), sink.arena.positive_children.capacity()),
                (sink.arena.negative_children.len(), sink.arena.negative_children.capacity()),
            ]) {
                owner.observe(len, capacity);
            }
            sink.component_checkpoint = None;
            sink.counter_checkpoint = None;
            (self.shared_summary_hits, self.uncacheable_states) = counter_checkpoint;
            self.abort_flat_component()?;
        }
        result
    }

    fn abort_flat_component(&mut self) -> Result<(), SolveAvailabilityError> {
        if let Some(checkpoint) = self.flat_sink.component_checkpoint.take() {
            self.flat_sink.arena.rollback(checkpoint);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            for (owner, (len, capacity)) in self.source_arena_owners.iter_mut().zip([
                (self.flat_sink.arena.positive_nodes.len(), self.flat_sink.arena.positive_nodes.capacity()),
                (self.flat_sink.arena.negative_nodes.len(), self.flat_sink.arena.negative_nodes.capacity()),
                (self.flat_sink.arena.positive_children.len(), self.flat_sink.arena.positive_children.capacity()),
                (self.flat_sink.arena.negative_children.len(), self.flat_sink.arena.negative_children.capacity()),
            ]) {
                owner.observe(len, capacity);
            }
        }
        if let Some(counters) = self.flat_sink.counter_checkpoint.take() {
            (self.shared_summary_hits, self.uncacheable_states) = counters;
        }
        let roots = self
            .memo
            .finish_root_transaction(self.root_undo_checkpoint, false);
        self.memo.reset_active_scratch();
        self.active.clear();
        self.active_set.clear();
        self.frames.clear();
        self.release_persistent_lanes();
        self.fatal_taint = false;
        self.invalid_effects = false;
        let nodes = self.memo.rollback_nodes(
            self.node_checkpoint,
            self.child_checkpoint,
            self.reverse_checkpoint,
            self.incidence_checkpoint,
        );
        let rollback = roots.and(nodes);
        if rollback.is_err() {
            self.raw_forest_rollback_failed = true;
        }
        rollback
    }

    pub(super) fn positive_row(
        &mut self,
        ordinal: u32,
        root: bool,
    ) -> Result<F5cPositive<'meter>, SolveAvailabilityError> {
        match self.walk(F5cWalkTask::EnterRow {
            row: ordinal,
            polarity: Polarity::Positive,
            root,
        })? {
            F5cWalkValue::Positive(value, _) => Ok(value),
            F5cWalkValue::Negative(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    pub(super) fn negative_row(
        &mut self,
        ordinal: u32,
    ) -> Result<F5cNegative<'meter>, SolveAvailabilityError> {
        match self.walk(F5cWalkTask::EnterRow {
            row: ordinal,
            polarity: Polarity::Negative,
            root: false,
        })? {
            F5cWalkValue::Negative(value, _) => Ok(value),
            F5cWalkValue::Positive(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    #[cfg(test)]
    pub(super) fn positive_endpoint(
        &mut self,
        endpoint: ValueEndpointKey,
    ) -> Result<F5cPositive<'meter>, SolveAvailabilityError> {
        match self.walk(F5cWalkTask::PositiveEndpoint(endpoint))? {
            F5cWalkValue::Positive(value, _) => Ok(value),
            F5cWalkValue::Negative(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    #[cfg(test)]
    pub(super) fn negative_endpoint(
        &mut self,
        endpoint: ValueEndpointKey,
    ) -> Result<F5cNegative<'meter>, SolveAvailabilityError> {
        match self.walk(F5cWalkTask::NegativeEndpoint(endpoint))? {
            F5cWalkValue::Negative(value, _) => Ok(value),
            F5cWalkValue::Positive(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    #[cfg(test)]
    pub(super) fn positive_term(
        &mut self,
        term: Term,
    ) -> Result<F5cPositive<'meter>, SolveAvailabilityError> {
        match self.walk(F5cWalkTask::EnterTerm {
            term,
            polarity: Polarity::Positive,
        })? {
            F5cWalkValue::Positive(value, _) => Ok(value),
            F5cWalkValue::Negative(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    #[cfg(test)]
    pub(super) fn negative_term(
        &mut self,
        term: Term,
    ) -> Result<F5cNegative<'meter>, SolveAvailabilityError> {
        match self.walk(F5cWalkTask::EnterTerm {
            term,
            polarity: Polarity::Negative,
        })? {
            F5cWalkValue::Negative(value, _) => Ok(value),
            F5cWalkValue::Positive(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    #[cfg(test)]
    fn guarded_trace_path_survives(
        trace: &F5cGuardedTrace,
        protected: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> bool {
        trace.path.iter().all(|hop| match hop {
            F5cTraceHop::Direct {
                side,
                source,
                target,
                ..
            } => {
                let eliminated = match side {
                    F5cBoundSide::Lower => positive_only,
                    F5cBoundSide::Upper => negative_only,
                };
                (protected.contains(source) || !eliminated.contains(source))
                    && (protected.contains(target) || !eliminated.contains(target))
            }
            _ => true,
        })
    }

    fn guarded_trace_path_survives_with_meter(
        memo: &F5cComponentExpansionMemo,
        trace: &F5cGuardedTrace,
        protected: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> Result<bool, SolveAvailabilityError> {
        for hop in &trace.path {
            memo.work_meter.charge(1)?; // examined trace hop
            if let F5cTraceHop::Direct {
                side,
                source,
                target,
                ..
            } = hop
            {
                let eliminated = match side {
                    F5cBoundSide::Lower => positive_only,
                    F5cBoundSide::Upper => negative_only,
                };
                if (!protected.contains(source) && eliminated.contains(source))
                    || (!protected.contains(target) && eliminated.contains(target))
                {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    #[cfg(test)]
    pub(super) fn guarded_trace_survives(
        trace: &F5cGuardedTrace,
        owner: u32,
        protected: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
        raw_recursive_bounds: &HashMap<u32, (F5cPositive, F5cNegative)>,
    ) -> bool {
        if !Self::guarded_trace_path_survives(trace, protected, positive_only, negative_only) {
            return false;
        }
        let Some((lower, upper)) = raw_recursive_bounds.get(&owner) else {
            return false;
        };
        let source_meter = DraftHeapMeter::default();
        let mut memo = F5cComponentExpansionMemo::default();
        let Ok(lower) = f5c_replay::replay_positive(
            &source_meter,
            &mut memo,
            lower,
            protected,
            positive_only,
            negative_only,
        ) else {
            return false;
        };
        let Ok(upper) = f5c_replay::replay_negative(
            &source_meter,
            &mut memo,
            upper,
            protected,
            positive_only,
            negative_only,
        ) else {
            return false;
        };
        f5c_tree_analysis::Walker::new(&mut memo)
            .guarded_bound_survives(owner, &lower, &upper)
            .unwrap_or(false)
    }

    #[cfg(test)]
    pub(super) fn normalize_positive(
        source_meter: &'meter DraftHeapMeter,
        value: F5cPositive<'meter>,
    ) -> Result<F5cPositive<'meter>, SolveAvailabilityError> {
        f5c_normalization::normalize_positive(source_meter, value)
    }

    #[cfg(test)]
    pub(super) fn normalize_negative(
        source_meter: &'meter DraftHeapMeter,
        value: F5cNegative<'meter>,
    ) -> Result<F5cNegative<'meter>, SolveAvailabilityError> {
        f5c_normalization::normalize_negative(source_meter, value)
    }

    pub(super) fn non_generic_closure(&mut self) -> Result<F5cObservedSet<'meter>, SolveAvailabilityError> {
        let result = self.non_generic_closure_work();
        let mut release_error = None;
        for kind in [
            F5cWalkerLaneKind::ClosureAdjacency,
            F5cWalkerLaneKind::ClosureNeighbors,
            F5cWalkerLaneKind::ClosureConnected,
            F5cWalkerLaneKind::ClosureFrontier,
        ] {
            if let Err(error) = self
                .memo
                .release_walker_with_source(kind, self.source_meter)
            {
                release_error.get_or_insert(error);
            }
        }
        if result.is_err() || release_error.is_some() {
            let work_error = result.err();
            if let Err(error) = self
                .memo
                .release_walker_with_source(F5cWalkerLaneKind::ClosureResult, self.source_meter)
            {
                release_error.get_or_insert(error);
            }
            return Err(work_error.or(release_error).unwrap());
        }
        result
    }

    fn non_generic_closure_work(&mut self) -> Result<F5cObservedSet<'meter>, SolveAvailabilityError> {
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut adjacency_owners = Vec::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut adjacency_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::ClosureAdjacency as usize,
            F5cWalkerLaneKind::ClosureAdjacency.slot_size());
        let mut adjacency = Vec::new();
        let mut walker =
            f5c_tree_analysis::Walker::new_with_source(&mut self.memo, self.source_meter);
        let memo_bytes = walker.memo.retained_bytes()?;
        let reservation = walker.memo.walker_resources.with_source(
            self.source_meter,
            memo_bytes,
            F5cWalkerLaneKind::ClosureAdjacency,
            |resources| {
                resources.reserve(
                    &mut adjacency,
                    F5cWalkerLaneKind::ClosureAdjacency,
                    self.session.bounds.len(),
                    memo_bytes,
                )
            },
        );
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        adjacency_owner.observe(adjacency.len(), adjacency.capacity());
        reservation?;
        adjacency.resize_with(self.session.bounds.len(), HashSet::new);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        adjacency_owner.observe(adjacency.len(), adjacency.capacity());
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        adjacency_owners.extend((0..adjacency.len()).map(|_| RawWalkerOwner::new(
            self.source_meter,
            F5cWalkerLaneKind::ClosureNeighbors as usize,
            F5cWalkerLaneKind::ClosureNeighbors.slot_size(),
        )));
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut connected = ObservedWalkerSet::new(self.source_meter, F5cWalkerLaneKind::ClosureConnected);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut connected = HashSet::new();
        for (owner, bounds) in self.session.bounds.iter().enumerate() {
            walker.memo.work_meter.charge(1)?; // scanned bounds owner
            let owner = owner as u32;
            let direct_count = bounds
                .direct_lower_rows
                .len()
                .checked_add(bounds.direct_upper_rows.len())
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            walker.memo.work_meter.charge(direct_count)?; // copied direct adjacency endpoints
            connected.clear();
            for row in bounds
                .direct_lower_rows
                .iter()
                .chain(&bounds.direct_upper_rows)
            {
                let reservation = walker.memo.insert_physical_set_with_source(
                    &mut connected, *row, F5cWalkerLaneKind::ClosureConnected, self.source_meter,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                connected.observe_capacity(connected.len() + 1);
                reservation?;
            }
            for endpoint in bounds
                .exact_non_variable_lowers
                .iter()
                .chain(&bounds.exact_non_variable_uppers)
            {
                walker.memo.work_meter.charge(1)?; // examined exact endpoint
                match endpoint {
                    ValueEndpointKey::ValueRow(row) => {
                        let reservation = walker.memo.insert_physical_set_with_source(
                            &mut connected, *row, F5cWalkerLaneKind::ClosureConnected, self.source_meter,
                        );
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        connected.observe_capacity(connected.len() + 1);
                        reservation?;
                    }
                    ValueEndpointKey::PositiveFunction(term)
                    | ValueEndpointKey::NegativeFunction(term) => {
                        let traversal = walker.term_rows_with_lane(
                            &self.session.store,
                            *term,
                            &mut connected,
                            Some(F5cWalkerLaneKind::ClosureConnected),
                        );
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        connected.observe_capacity(connected.len());
                        traversal?;
                    }
                    _ => {}
                }
            }
            for &target in &connected {
                walker.memo.work_meter.charge(1)?; // adjacency incidence
                if let Some(neighbors) = adjacency.get_mut(owner as usize) {
                    let reservation = walker.memo.insert_physical_set_with_source(
                        neighbors, target, F5cWalkerLaneKind::ClosureNeighbors, self.source_meter,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    adjacency_owners[owner as usize].observe(neighbors.len(), neighbors.capacity());
                    reservation?;
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    adjacency_owners[owner as usize].observe(neighbors.len(), neighbors.capacity());
                }
                if let Some(neighbors) = adjacency.get_mut(target as usize) {
                    let reservation = walker.memo.insert_physical_set_with_source(
                        neighbors, owner, F5cWalkerLaneKind::ClosureNeighbors, self.source_meter,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    adjacency_owners[target as usize].observe(neighbors.len(), neighbors.capacity());
                    reservation?;
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    adjacency_owners[target as usize].observe(neighbors.len(), neighbors.capacity());
                }
            }
        }
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut closure = ObservedWalkerSet::new(self.source_meter, F5cWalkerLaneKind::ClosureResult);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut closure = HashSet::new();
        for (ordinal, metadata) in self.session.value_metadata.iter().enumerate() {
            walker.memo.work_meter.charge(1)?; // metadata owner
            if metadata.non_generic {
                walker.memo.work_meter.charge(1)?; // closure entry
                let reservation = walker.memo.insert_physical_set_with_source(
                    &mut closure, ordinal as u32, F5cWalkerLaneKind::ClosureResult, self.source_meter,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                closure.observe_capacity(closure.len() + 1);
                reservation?;
            }
        }
        walker.memo.work_meter.charge(closure.len())?; // copied frontier owners
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut frontier_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::ClosureFrontier as usize,
            F5cWalkerLaneKind::ClosureFrontier.slot_size());
        let mut frontier = Vec::new();
        for owner in &closure {
            let reservation = walker.memo.reserve_walker_with_source(
                &mut frontier,
                F5cWalkerLaneKind::ClosureFrontier,
                self.source_meter,
            );
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            frontier_owner.observe(frontier.len(), frontier.capacity());
            reservation?;
            frontier.push(*owner);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            frontier_owner.observe(frontier.len(), frontier.capacity());
        }
        while !frontier.is_empty() {
            walker.memo.work_meter.charge(1)?; // closure frontier pop
            let owner = frontier.pop().expect("nonempty closure frontier");
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            frontier_owner.observe(frontier.len(), frontier.capacity());
            let Some(neighbors) = adjacency.get(owner as usize) else {
                continue;
            };
            for neighbor in neighbors {
                walker.memo.work_meter.charge(1)?; // examined adjacency neighbor
                walker.memo.work_meter.charge(1)?; // possible closure and frontier entries
                if !closure.contains(neighbor) {
                    let reservation = walker.memo.insert_physical_set_with_source(
                        &mut closure, *neighbor, F5cWalkerLaneKind::ClosureResult, self.source_meter,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    closure.observe_capacity(closure.len() + 1);
                    reservation?;
                    let reservation = walker.memo.reserve_walker_with_source(
                        &mut frontier,
                        F5cWalkerLaneKind::ClosureFrontier,
                        self.source_meter,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    frontier_owner.observe(frontier.len(), frontier.capacity());
                    reservation?;
                    frontier.push(*neighbor);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    frontier_owner.observe(frontier.len(), frontier.capacity());
                }
            }
        }
        Ok(closure)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(super) fn retained_occurrences<'tree>(
        retained_predicate: &'tree F5cPositive,
        recursive_owners: &[u32],
        recursive_bounds: &'tree HashMap<u32, (F5cPositive, F5cNegative)>,
        memo: &mut F5cComponentExpansionMemo,
    ) -> Result<Vec<u32>, SolveAvailabilityError> {
        let mut ordered = Vec::new();
        let mut seen = HashSet::new();
        let mut walker = f5c_tree_analysis::Walker::new(memo);
        walker.occurrences_positive(retained_predicate, &mut ordered, &mut seen)?;
        for owner in recursive_owners {
            walker.memo.work_meter.charge(1)?; // retained bound owner
            let (lower, upper) = recursive_bounds
                .get(owner)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            walker.occurrences_positive(lower, &mut ordered, &mut seen)?;
            walker.occurrences_negative(upper, &mut ordered, &mut seen)?;
        }
        Ok(ordered)
    }

    fn raw_forest_incidences<'tree>(
        source_meter: Option<&'meter DraftHeapMeter>,
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        probe_meter: Option<&'meter DraftHeapMeter>,
        memo: &mut F5cComponentExpansionMemo,
        raw_owner_order: &[u32],
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        mut visit: impl FnMut(
            &mut f5c_tree_analysis::Walker<'_, 'tree, 'meter>,
            Option<u32>, &mut HashSet<u32>, &mut HashSet<u32>,
            Option<&mut RawWalkerOwner<'meter>>, Option<&mut RawWalkerOwner<'meter>>,
        ) -> Result<(), SolveAvailabilityError>,
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        mut visit: impl FnMut(
            &mut f5c_tree_analysis::Walker<'_, 'tree, 'meter>,
            Option<u32>, &mut HashSet<u32>, &mut HashSet<u32>,
        ) -> Result<(), SolveAvailabilityError>,
    ) -> Result<(F5cRawIncidenceSet<'meter>, F5cRawIncidenceSet<'meter>), SolveAvailabilityError>
    where
        'meter: 'tree,
    {
        let result =
            Self::raw_forest_incidences_work(source_meter,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                probe_meter,
                memo, raw_owner_order, &mut visit);
        if result.is_err() {
            memo.walker_resources
                .release(F5cWalkerLaneKind::RawPositiveIncidences);
            memo.walker_resources
                .release(F5cWalkerLaneKind::RawNegativeIncidences);
            if let Some(meter) = source_meter {
                let _ = memo.observe_component_external(meter);
            }
        }
        result
    }

    fn raw_forest_incidences_work<'tree>(
        source_meter: Option<&'meter DraftHeapMeter>,
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        probe_meter: Option<&'meter DraftHeapMeter>,
        memo: &mut F5cComponentExpansionMemo,
        raw_owner_order: &[u32],
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        visit: &mut impl FnMut(
            &mut f5c_tree_analysis::Walker<'_, 'tree, 'meter>,
            Option<u32>, &mut HashSet<u32>, &mut HashSet<u32>,
            Option<&mut RawWalkerOwner<'meter>>, Option<&mut RawWalkerOwner<'meter>>,
        ) -> Result<(), SolveAvailabilityError>,
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        visit: &mut impl FnMut(
            &mut f5c_tree_analysis::Walker<'_, 'tree, 'meter>,
            Option<u32>, &mut HashSet<u32>, &mut HashSet<u32>,
        ) -> Result<(), SolveAvailabilityError>,
    ) -> Result<(F5cRawIncidenceSet<'meter>, F5cRawIncidenceSet<'meter>), SolveAvailabilityError>
    where
        'meter: 'tree,
    {
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut positive = ObservedWalkerSet::new_optional(
            source_meter.or(probe_meter), F5cWalkerLaneKind::RawPositiveIncidences);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut positive = HashSet::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut negative = ObservedWalkerSet::new_optional(
            source_meter.or(probe_meter), F5cWalkerLaneKind::RawNegativeIncidences);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut negative = HashSet::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut walker = if let Some(meter) = source_meter {
            f5c_tree_analysis::Walker::new_with_source(memo, meter)
        } else if let Some(meter) = probe_meter {
            f5c_tree_analysis::Walker::new_with_probe_meter(memo, meter)
        } else {
            f5c_tree_analysis::Walker::new(memo)
        };
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut walker = if let Some(meter) = source_meter {
            f5c_tree_analysis::Walker::new_with_source(memo, meter)
        } else {
            f5c_tree_analysis::Walker::new(memo)
        };
        visit(&mut walker, None,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            &mut positive.values,
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            &mut positive,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            &mut negative.values,
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            &mut negative,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            positive.owner.as_mut(),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            negative.owner.as_mut())?;
        for &owner in raw_owner_order {
            walker.memo.work_meter.charge(1)?; // raw bound owner
            visit(&mut walker, Some(owner),
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                &mut positive.values,
                #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                &mut positive,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                &mut negative.values,
                #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                &mut negative,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                positive.owner.as_mut(),
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                negative.owner.as_mut())?;
        }
        Ok((positive, negative))
    }

    #[cfg(test)]
    pub(super) fn boxed_raw_forest_incidences_for_test(
        memo: &mut F5cComponentExpansionMemo,
        predicate: &F5cPositive<'meter>,
        raw_owner_order: &[u32],
        raw_bounds: &HashMap<u32, (F5cPositive<'meter>, F5cNegative<'meter>)>,
    ) -> Result<(HashSet<u32>, HashSet<u32>), SolveAvailabilityError> {
        let result = Self::raw_forest_incidences(
            None,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            None,
            memo,
            raw_owner_order,
            |walker, owner, positive, negative,
             #[cfg(all(test, feature = "f5c_resource_probe"))] mut positive_owner,
             #[cfg(all(test, feature = "f5c_resource_probe"))] mut negative_owner| {
                if let Some(owner) = owner {
                    let (lower, upper) = raw_bounds
                        .get(&owner)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    walker.incidences_positive(lower, positive, negative,
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        positive_owner.as_deref_mut(),
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        negative_owner.as_deref_mut())?;
                    walker.incidences_negative(upper, positive, negative,
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        positive_owner.as_deref_mut(),
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        negative_owner.as_deref_mut())
                } else {
                    walker.incidences_positive(predicate, positive, negative,
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        positive_owner.as_deref_mut(),
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        negative_owner.as_deref_mut())
                }
            },
        );
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let result = result.map(|(mut positive, mut negative)|
            (std::mem::take(&mut positive.values), std::mem::take(&mut negative.values)));
        result
    }

    pub(super) fn flat_raw_forest_incidences(
        &mut self,
        forest: &F5cRawForest<'meter>,
    ) -> Result<(F5cRawIncidenceSet<'meter>, F5cRawIncidenceSet<'meter>), SolveAvailabilityError> {
        if !self.raw_forest_live {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        Self::flat_raw_forest_incidences_with_meter(
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            Some(self.source_meter),
            &mut self.memo,
            &forest.draft,
            &forest.raw_owner_order,
            &forest.raw_bounds,
        )
    }

    #[cfg(test)]
    pub(super) fn flat_raw_forest_incidences_for_test(
        memo: &mut F5cComponentExpansionMemo,
        draft: &f5c_draft::FlatDraft,
        raw_owner_order: &[u32],
        raw_bounds: &HashMap<u32, (f5c_draft::PositiveId, f5c_draft::NegativeId)>,
    ) -> Result<(HashSet<u32>, HashSet<u32>), SolveAvailabilityError> {
        let result = Self::flat_raw_forest_incidences_with_meter(
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            None,
            memo, draft, raw_owner_order, raw_bounds);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let result = result.map(|(mut positive, mut negative)|
            (std::mem::take(&mut positive.values), std::mem::take(&mut negative.values)));
        result
    }

    fn flat_raw_forest_incidences_with_meter(
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        source_meter: Option<&'meter DraftHeapMeter>,
        memo: &mut F5cComponentExpansionMemo,
        draft: &f5c_draft::FlatDraft,
        raw_owner_order: &[u32],
        raw_bounds: &HashMap<u32, (f5c_draft::PositiveId, f5c_draft::NegativeId)>,
    ) -> Result<(F5cRawIncidenceSet<'meter>, F5cRawIncidenceSet<'meter>), SolveAvailabilityError> {
        use f5c_draft::NodeRef;
        Self::raw_forest_incidences(
            None,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            source_meter,
            memo,
            raw_owner_order,
            |walker, owner, positive, negative,
             #[cfg(all(test, feature = "f5c_resource_probe"))] mut positive_owner,
             #[cfg(all(test, feature = "f5c_resource_probe"))] mut negative_owner| {
                if let Some(owner) = owner {
                    let (lower, upper) = raw_bounds
                        .get(&owner)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    walker.flat_incidences(draft, NodeRef::Positive(*lower), positive, negative,
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        positive_owner.as_deref_mut(),
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        negative_owner.as_deref_mut())?;
                    walker.flat_incidences(draft, NodeRef::Negative(*upper), positive, negative,
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        positive_owner.as_deref_mut(),
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        negative_owner.as_deref_mut())
                } else {
                    let predicate = draft
                        .predicate
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    walker.flat_incidences(draft, NodeRef::Positive(predicate), positive, negative,
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        positive_owner.as_deref_mut(),
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        negative_owner.as_deref_mut())
                }
            },
        )
    }

    #[cfg(test)]
    pub(super) fn flat_r_candidates_for_test(
        memo: &mut F5cComponentExpansionMemo,
        draft: &f5c_draft::FlatDraft,
        bounds: &HashMap<u32, (f5c_draft::PositiveId, f5c_draft::NegativeId)>,
        reentries: &[F5cGuardedTrace],
        reentries_by_owner: &HashMap<u32, Vec<usize>>,
        eligible: impl Fn(u32) -> bool,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> Result<HashSet<u32>, SolveAvailabilityError> {
        let source_meter = DraftHeapMeter::default();
        let mut source = F5cFlatRCandidateSource {
            source: draft,
            output: f5c_draft::FlatDraft::default(),
            bounds,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            probe_meter: None,
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            _meter: std::marker::PhantomData,
        };
        let result = Self::r_candidates(
            &source_meter,
            memo,
            &mut source,
            reentries,
            reentries_by_owner,
            eligible,
            positive_only,
            negative_only,
        );
        f5c_replay::release_flat_output(memo, source.output,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            Some(&source_meter));
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let result = result.map(|mut candidates| std::mem::take(&mut candidates.values));
        result
    }

    #[cfg(test)]
    pub(super) fn flat_r_with_raw_forest_for_test(
        &mut self,
        forest: F5cRawForest<'meter>,
        reentries: &[F5cGuardedTrace],
        reentries_by_owner: &HashMap<u32, Vec<usize>>,
        eligible: impl Fn(u32) -> bool,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> Result<(HashSet<u32>, F5cRawForest<'meter>), SolveAvailabilityError> {
        let result = Self::flat_r_candidates_for_test(
            &mut self.memo,
            &forest.draft,
            &forest.raw_bounds,
            reentries,
            reentries_by_owner,
            eligible,
            positive_only,
            negative_only,
        );
        match result {
            Ok(candidates) => Ok((candidates, forest)),
            Err(error) => {
                self.abort_raw_forest(forest)?;
                Err(error)
            }
        }
    }

    #[cfg(test)]
    pub(super) fn flat_r_q_with_raw_forest_candidate_for_test(
        &mut self,
        forest: F5cRawForest<'meter>,
        reentries: &[F5cGuardedTrace],
        reentries_by_owner: &HashMap<u32, Vec<usize>>,
        order: &[u32],
        eligible: impl Fn(u32) -> bool + Copy,
        positive_incidences: &HashSet<u32>,
        negative_incidences: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
        #[cfg(test)] fail_after_first_post_output: bool,
    ) -> Result<
        (
            F5cPostRSelection<'meter,
                (f5c_draft::PositiveId, f5c_draft::NegativeId),
                f5c_draft::PositiveId,
            >,
            f5c_draft::FlatDraft,
            F5cRawForest<'meter>,
        ),
        SolveAvailabilityError,
    > {
        match self.flat_r_q_with_raw_forest_candidate_inner(
            forest,
            reentries,
            reentries_by_owner,
            order,
            eligible,
            positive_incidences,
            negative_incidences,
            positive_only,
            negative_only,
            #[cfg(test)]
            fail_after_first_post_output,
        ) {
            Ok(value) => Ok(value),
            Err((error, forest)) => {
                self.abort_raw_forest(forest)?;
                Err(error)
            }
        }
    }

    fn flat_r_q_with_raw_forest_candidate_inner(
        &mut self,
        forest: F5cRawForest<'meter>,
        reentries: &[F5cGuardedTrace],
        reentries_by_owner: &HashMap<u32, Vec<usize>>,
        order: &[u32],
        eligible: impl Fn(u32) -> bool + Copy,
        positive_incidences: &HashSet<u32>,
        negative_incidences: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
        #[cfg(test)] fail_after_first_post_output: bool,
    ) -> Result<
        (
            F5cPostRSelection<'meter,
                (f5c_draft::PositiveId, f5c_draft::NegativeId),
                f5c_draft::PositiveId,
            >,
            f5c_draft::FlatDraft,
            F5cRawForest<'meter>,
        ),
        (SolveAvailabilityError, F5cRawForest<'meter>),
    > {
        if !self.raw_forest_live {
            return Err((SolveAvailabilityError::IdentityExhausted, forest));
        }
        let mut source = F5cFlatRCandidateSource {
            source: &forest.draft,
            output: {
                #[allow(unused_mut)]
                let mut draft = f5c_draft::FlatDraft::default();
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                draft.attach_owners(self.source_meter, [
                    F5cWalkerLaneKind::ReplayOutputPositiveNodes as usize,
                    F5cWalkerLaneKind::ReplayOutputNegativeNodes as usize,
                    F5cWalkerLaneKind::ReplayOutputPositiveChildren as usize,
                    F5cWalkerLaneKind::ReplayOutputNegativeChildren as usize,
                    F5cWalkerLaneKind::SelectedRecursiveBounds as usize,
                    F5cWalkerLaneKind::ReplayOutputInsertionOrder as usize,
                ]);
                draft
            },
            bounds: &forest.raw_bounds,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            probe_meter: Some(self.source_meter),
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            _meter: std::marker::PhantomData,
        };
        let result = (|| {
            let candidates = Self::r_candidates(
                self.source_meter,
                &mut self.memo,
                &mut source,
                reentries,
                reentries_by_owner,
                eligible,
                positive_only,
                negative_only,
            )?;
            #[cfg(test)]
            if fail_after_first_post_output {
                f5c_replay::inject_failure_after_flat_output();
            }
            let selection = Self::post_r_selection(
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                Some(self.source_meter),
                &mut self.memo,
                &mut source,
                &candidates,
                &forest.raw_owner_order,
                reentries,
                order,
                positive_incidences,
                negative_incidences,
                positive_only,
                negative_only,
                eligible,
            );
            drop(candidates);
            self.memo
                .walker_resources
                .release(F5cWalkerLaneKind::RCandidates);
            selection
        })();
        let output = source.output;
        match result {
            Ok(selection) => Ok((selection, output, forest)),
            Err(error) => {
                f5c_replay::release_flat_output(&mut self.memo, output,
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    Some(self.source_meter));
                release_flat_post_r_lanes(&mut self.memo);
                Err((error, forest))
            }
        }
    }

    #[cfg(test)]
    pub(super) fn release_flat_r_q_for_test(
        &mut self,
        selection: F5cPostRSelection<'meter,
            (f5c_draft::PositiveId, f5c_draft::NegativeId),
            f5c_draft::PositiveId,
        >,
        output: f5c_draft::FlatDraft,
        forest: F5cRawForest<'meter>,
    ) {
        drop(selection);
        f5c_replay::release_flat_output(&mut self.memo, output,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            Some(self.source_meter));
        release_flat_post_r_lanes(&mut self.memo);
        self.release_raw_forest(forest);
    }

    #[cfg(test)]
    pub(super) fn flat_finish_selected_candidate(
        &mut self,
        selection: F5cPostRSelection<'meter,
            (f5c_draft::PositiveId, f5c_draft::NegativeId),
            f5c_draft::PositiveId,
        >,
        output: f5c_draft::FlatDraft,
        forest: F5cRawForest<'meter>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
        #[cfg(test)] fail_during_normalization: bool,
    ) -> Result<F5cNormalizedCandidate, SolveAvailabilityError> {
        let (candidate, forest) = self.flat_finish_selected_candidate_pending(
            selection,
            output,
            forest,
            positive_only,
            negative_only,
            #[cfg(test)]
            fail_during_normalization,
        )?;
        self.release_raw_forest(forest);
        Ok(candidate)
    }

    #[allow(dead_code)]
    fn flat_finish_selected_raw_pending(
        &mut self,
        selection: F5cPostRSelection<'meter,
            (f5c_draft::PositiveId, f5c_draft::NegativeId),
            f5c_draft::PositiveId,
        >,
        mut output: f5c_draft::FlatDraft,
        forest: F5cRawForest<'meter>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> Result<(f5c_draft::FlatDraft, F5cRawForest<'meter>), SolveAvailabilityError> {
        if self.normalized_candidate_live {
            drop(selection);
            f5c_replay::release_flat_output(&mut self.memo, output,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                Some(self.source_meter));
            release_flat_post_r_lanes(&mut self.memo);
            self.abort_raw_forest(forest)?;
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let result = (|| {
            let q_count = u32::try_from(selection.q.len())
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            f5c_draft::checked_q_r_count(q_count, selection.recursive_owners.len())?;
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            let mut positive_eliminated = ObservedWalkerSet::new(self.source_meter,
                F5cWalkerLaneKind::SelectedPositiveEliminated);
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            let mut positive_eliminated = HashSet::new();
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            let mut negative_eliminated = ObservedWalkerSet::new(self.source_meter,
                F5cWalkerLaneKind::SelectedNegativeEliminated);
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            let mut negative_eliminated = HashSet::new();
            for &ordinal in &self.order {
                self.memo.work_meter.charge(1)?;
                if !selection.recursive_set.contains(&ordinal)
                    && !selection.q.contains_key(&ordinal)
                    && positive_only.contains(&ordinal)
                {
                    self.memo.work_meter.charge(1)?;
                    let bytes = self.memo.retained_bytes()?;
                    let reservation = self.memo.walker_resources.reserve_post_r_set(
                        &mut positive_eliminated,
                        F5cWalkerLaneKind::SelectedPositiveEliminated,
                        bytes,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    positive_eliminated.observe_capacity(0);
                    reservation?;
                    positive_eliminated.insert(ordinal);
                }
            }
            for &ordinal in &self.order {
                self.memo.work_meter.charge(1)?;
                if !selection.recursive_set.contains(&ordinal)
                    && !selection.q.contains_key(&ordinal)
                    && negative_only.contains(&ordinal)
                {
                    self.memo.work_meter.charge(1)?;
                    let bytes = self.memo.retained_bytes()?;
                    let reservation = self.memo.walker_resources.reserve_post_r_set(
                        &mut negative_eliminated,
                        F5cWalkerLaneKind::SelectedNegativeEliminated,
                        bytes,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    negative_eliminated.observe_capacity(0);
                    reservation?;
                    negative_eliminated.insert(ordinal);
                }
            }
            output.predicate = Some(selection.retained_predicate);
            output.quantifier_count = q_count;
            for owner in &selection.recursive_owners {
                self.memo.work_meter.charge(1)?;
                let binder = *selection
                    .r
                    .get(owner)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                self.memo.work_meter.charge(1)?;
                let &(lower, upper) = selection
                    .retained_bounds
                    .get(owner)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                self.memo.work_meter.charge(1)?;
                let bytes = self.memo.retained_bytes()?;
                let reservation = self.memo.walker_resources.reserve(
                    &mut output.recursive_bounds,
                    F5cWalkerLaneKind::SelectedRecursiveBounds,
                    1,
                    bytes,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                output.observe_owner(4, output.recursive_bounds.len() + 1);
                reservation?;
                output.recursive_bounds.push(f5c_draft::RecursiveBound {
                    ordinal: binder,
                    lower,
                    upper,
                });
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                output.observe_owner(4, 0);
            }
            f5c_binder_substitution::substitute_flat_metered(
                &mut self.memo,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                self.source_meter,
                &mut output,
                &selection.q,
                &selection.r,
                &positive_eliminated,
                &negative_eliminated,
            )?;
            Ok::<_, SolveAvailabilityError>(())
        })();
        drop(selection);
        release_flat_post_r_lanes(&mut self.memo);
        for lane in [
            F5cWalkerLaneKind::SelectedPositiveEliminated,
            F5cWalkerLaneKind::SelectedNegativeEliminated,
        ] {
            self.memo.walker_resources.release(lane);
        }
        match result {
            Ok(()) => Ok((output, forest)),
            Err(error) => {
                f5c_replay::release_flat_output(&mut self.memo, output,
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    Some(self.source_meter));
                self.memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::SelectedRecursiveBounds);
                self.abort_raw_forest(forest)?;
                Err(error)
            }
        }
    }

    fn flat_finish_selected_candidate_pending(
        &mut self,
        selection: F5cPostRSelection<'meter,
            (f5c_draft::PositiveId, f5c_draft::NegativeId),
            f5c_draft::PositiveId,
        >,
        mut output: f5c_draft::FlatDraft,
        forest: F5cRawForest<'meter>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
        #[cfg(test)] fail_during_normalization: bool,
    ) -> Result<(F5cNormalizedCandidate, F5cRawForest<'meter>), SolveAvailabilityError> {
        if self.normalized_candidate_live {
            drop(selection);
            f5c_replay::release_flat_output(&mut self.memo, output,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                Some(self.source_meter));
            release_flat_post_r_lanes(&mut self.memo);
            self.abort_raw_forest(forest)?;
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut selected_bounds_owner = output.owners.is_none().then(||
            RawWalkerOwner::new(self.source_meter,
                F5cWalkerLaneKind::SelectedRecursiveBounds as usize,
                F5cWalkerLaneKind::SelectedRecursiveBounds.slot_size()));
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if let Some(owner) = selected_bounds_owner.as_mut() {
            owner.observe(output.recursive_bounds.len(), output.recursive_bounds.capacity());
        }
        let result = (|| {
            let q_count = u32::try_from(selection.q.len())
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            f5c_draft::checked_q_r_count(q_count, selection.recursive_owners.len())?;
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            let mut positive_eliminated = ObservedWalkerSet::new(self.source_meter,
                F5cWalkerLaneKind::SelectedPositiveEliminated);
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            let mut positive_eliminated = HashSet::new();
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            let mut negative_eliminated = ObservedWalkerSet::new(self.source_meter,
                F5cWalkerLaneKind::SelectedNegativeEliminated);
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            let mut negative_eliminated = HashSet::new();
            for &ordinal in &self.order {
                self.memo.work_meter.charge(1)?;
                if !selection.recursive_set.contains(&ordinal)
                    && !selection.q.contains_key(&ordinal)
                    && positive_only.contains(&ordinal)
                {
                    self.memo.work_meter.charge(1)?;
                    let bytes = self.memo.retained_bytes()?;
                    let reservation = self.memo.walker_resources.reserve_post_r_set(
                        &mut positive_eliminated,
                        F5cWalkerLaneKind::SelectedPositiveEliminated,
                        bytes,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    positive_eliminated.observe_capacity(0);
                    reservation?;
                    positive_eliminated.insert(ordinal);
                }
            }
            for &ordinal in &self.order {
                self.memo.work_meter.charge(1)?;
                if !selection.recursive_set.contains(&ordinal)
                    && !selection.q.contains_key(&ordinal)
                    && negative_only.contains(&ordinal)
                {
                    self.memo.work_meter.charge(1)?;
                    let bytes = self.memo.retained_bytes()?;
                    let reservation = self.memo.walker_resources.reserve_post_r_set(
                        &mut negative_eliminated,
                        F5cWalkerLaneKind::SelectedNegativeEliminated,
                        bytes,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    negative_eliminated.observe_capacity(0);
                    reservation?;
                    negative_eliminated.insert(ordinal);
                }
            }
            output.predicate = Some(selection.retained_predicate);
            output.quantifier_count = q_count;
            for owner in &selection.recursive_owners {
                self.memo.work_meter.charge(1)?;
                let binder = *selection
                    .r
                    .get(owner)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                self.memo.work_meter.charge(1)?;
                let &(lower, upper) = selection
                    .retained_bounds
                    .get(owner)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                self.memo.work_meter.charge(1)?;
                let bytes = self.memo.retained_bytes()?;
                let reservation = self.memo.walker_resources.reserve(
                    &mut output.recursive_bounds,
                    F5cWalkerLaneKind::SelectedRecursiveBounds,
                    1,
                    bytes,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                {
                    output.observe_owner(4, output.recursive_bounds.len() + 1);
                    if let Some(owner) = selected_bounds_owner.as_mut() {
                        owner.observe(output.recursive_bounds.len(),
                            output.recursive_bounds.capacity());
                    }
                }
                reservation?;
                output.recursive_bounds.push(f5c_draft::RecursiveBound {
                    ordinal: binder,
                    lower,
                    upper,
                });
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                {
                    output.observe_owner(4, 0);
                    if let Some(owner) = selected_bounds_owner.as_mut() {
                        owner.observe(output.recursive_bounds.len(), output.recursive_bounds.capacity());
                    }
                }
            }
            f5c_binder_substitution::substitute_flat_metered(
                &mut self.memo,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                self.source_meter,
                &mut output,
                &selection.q,
                &selection.r,
                &positive_eliminated,
                &negative_eliminated,
            )?;
            f5c_normalization::normalize_flat_metered(
                &mut self.memo,
                self.source_meter,
                &output,
                #[cfg(test)]
                fail_during_normalization,
            )
        })();
        drop(selection);
        f5c_replay::release_flat_output(&mut self.memo, output,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            Some(self.source_meter));
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        drop(selected_bounds_owner);
        release_flat_post_r_lanes(&mut self.memo);
        for lane in [
            F5cWalkerLaneKind::SelectedRecursiveBounds,
            F5cWalkerLaneKind::SelectedPositiveEliminated,
            F5cWalkerLaneKind::SelectedNegativeEliminated,
        ] {
            self.memo.walker_resources.release(lane);
        }
        match result {
            Ok((draft, stats)) => {
                let published = (|| {
                    let bytes = self.memo.retained_bytes()?;
                    // Normalizer output lanes already count the emitted requests.
                    // Publication retains those same allocations in walker lanes.
                    for (kind, capacity) in [
                        (
                            F5cWalkerLaneKind::NormalizedPositiveNodes,
                            draft.positive_nodes.capacity(),
                        ),
                        (
                            F5cWalkerLaneKind::NormalizedNegativeNodes,
                            draft.negative_nodes.capacity(),
                        ),
                        (
                            F5cWalkerLaneKind::NormalizedPositiveChildren,
                            draft.positive_children.capacity(),
                        ),
                        (
                            F5cWalkerLaneKind::NormalizedNegativeChildren,
                            draft.negative_children.capacity(),
                        ),
                        (
                            F5cWalkerLaneKind::NormalizedRecursiveBounds,
                            draft.recursive_bounds.capacity(),
                        ),
                        (
                            F5cWalkerLaneKind::NormalizedInsertionOrder,
                            draft.insertion_order.capacity(),
                        ),
                    ] {
                        self.memo
                            .walker_resources
                            .observe_existing_capacity(kind, capacity, 0, bytes)?;
                    }
                    Ok::<_, SolveAvailabilityError>(())
                })();
                if let Err(error) = published {
                    drop(draft);
                    self.release_normalized_candidate_lanes();
                    self.abort_raw_forest(forest)?;
                    return Err(error);
                }
                self.normalized_candidate_live = true;
                Ok((F5cNormalizedCandidate { draft, stats }, forest))
            }
            Err(error) => {
                self.abort_raw_forest(forest)?;
                Err(error)
            }
        }
    }

    fn release_normalized_candidate_lanes(&mut self) {
        for kind in [
            F5cWalkerLaneKind::NormalizedPositiveNodes,
            F5cWalkerLaneKind::NormalizedNegativeNodes,
            F5cWalkerLaneKind::NormalizedPositiveChildren,
            F5cWalkerLaneKind::NormalizedNegativeChildren,
            F5cWalkerLaneKind::NormalizedRecursiveBounds,
            F5cWalkerLaneKind::NormalizedInsertionOrder,
        ] {
            self.memo.walker_resources.release(kind);
        }
    }

    #[allow(dead_code)] // The private candidate entrypoint is intentionally unselected.
    pub(super) fn release_normalized_candidate(&mut self, candidate: F5cNormalizedCandidate) {
        drop(candidate);
        self.release_normalized_candidate_lanes();
        self.normalized_candidate_live = false;
    }

    /// The SCC owner reserves its member slot before this transfer. No vector
    /// buffer is copied or grown here, and the emitted requests stay unchanged.
    #[allow(dead_code)]
    pub(super) fn stage_normalized_candidate(
        &mut self,
        staged: &mut TrackedVec<'meter, F5cStagedCandidate<'meter>>,
        candidate: F5cNormalizedCandidate,
    ) -> Result<(), SolveAvailabilityError> {
        self.stage_normalized_candidate_inner(staged, candidate, false, false)
    }

    #[cfg(test)]
    pub(super) fn stage_normalized_candidate_with_failure(
        &mut self,
        staged: &mut TrackedVec<'meter, F5cStagedCandidate<'meter>>,
        candidate: F5cNormalizedCandidate,
        fail_preflight: bool,
        fail_observe: bool,
    ) -> Result<(), SolveAvailabilityError> {
        self.stage_normalized_candidate_inner(staged, candidate, fail_preflight, fail_observe)
    }

    #[cfg(test)]
    pub(super) fn observe_staged_physical_source(&mut self, bytes: u128) {
        let joint = &mut self.memo.walker_resources.physical_joint;
        joint.staged_source_current = joint.staged_source_current.min(bytes);
        self.memo.observe_physical_memo();
        self.memo.walker_resources.observe_physical_walker();
        let joint = &mut self.memo.walker_resources.physical_joint;
        let prior_peak = joint.peak;
        joint.staged_source_current = bytes;
        joint.pair();
        assert_eq!(
            joint.peak,
            prior_peak
                .max(joint.source_current + bytes + joint.memo_current + joint.walker_current)
        );
    }

    fn stage_normalized_candidate_inner(
        &mut self,
        staged: &mut TrackedVec<'meter, F5cStagedCandidate<'meter>>,
        mut candidate: F5cNormalizedCandidate,
        fail_preflight: bool,
        fail_observe: bool,
    ) -> Result<(), SolveAvailabilityError> {
        if !self.normalized_candidate_live || staged.len() == staged.capacity() {
            self.release_normalized_candidate(candidate);
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let draft = &candidate.draft;
        let capacities = [
            draft.positive_nodes.capacity(),
            draft.negative_nodes.capacity(),
            draft.positive_children.capacity(),
            draft.negative_children.capacity(),
            draft.recursive_bounds.capacity(),
            draft.insertion_order.capacity(),
        ];
        let kinds = [
            F5cWalkerLaneKind::NormalizedPositiveNodes,
            F5cWalkerLaneKind::NormalizedNegativeNodes,
            F5cWalkerLaneKind::NormalizedPositiveChildren,
            F5cWalkerLaneKind::NormalizedNegativeChildren,
            F5cWalkerLaneKind::NormalizedRecursiveBounds,
            F5cWalkerLaneKind::NormalizedInsertionOrder,
        ];
        let mut bytes = [0; 6];
        for i in 0..6 {
            if self.memo.walker_resources.lanes[kinds[i] as usize].actual_capacity != capacities[i]
            {
                self.release_normalized_candidate(candidate);
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            let Some(size) = capacities[i].checked_mul(kinds[i].slot_size()) else {
                self.release_normalized_candidate(candidate);
                return Err(SolveAvailabilityError::IdentityExhausted);
            };
            bytes[i] = size;
        }
        let total = bytes
            .iter()
            .try_fold(0usize, |sum, byte| sum.checked_add(*byte));
        let future_external = self.memo.retained_bytes().and_then(|memo| {
            self.memo
                .walker_resources
                .retained_bytes()?
                .checked_sub(total.ok_or(SolveAvailabilityError::IdentityExhausted)?)
                .and_then(|walker| walker.checked_add(memo))
                .ok_or(SolveAvailabilityError::IdentityExhausted)
        });
        let Ok(future_external) = future_external else {
            self.release_normalized_candidate(candidate);
            return Err(SolveAvailabilityError::IdentityExhausted);
        };
        if fail_preflight {
            self.release_normalized_candidate(candidate);
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let allocations = match claim_flat_draft_batch(
            self.source_meter, &mut candidate.draft, bytes, future_external,
            capacities, kinds.map(F5cWalkerLaneKind::slot_size)) {
            Ok(allocations) => allocations,
            Err(()) => {
                self.release_normalized_candidate(candidate);
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
        };
        self.release_normalized_candidate_lanes();
        self.normalized_candidate_live = false;
        staged.push_reserved(F5cStagedCandidate {
            candidate,
            _allocations: allocations,
        });
        let observation = if fail_observe {
            Err(SolveAvailabilityError::IdentityExhausted)
        } else {
            self.memo.observe_source_meter(self.source_meter)
        };
        if let Err(error) = observation {
            drop(staged.pop());
            return Err(error);
        }
        Ok(())
    }

    #[allow(dead_code)]
    fn release_staged_raw_output_lanes(&mut self) {
        for kind in [
            F5cWalkerLaneKind::ReplayOutputPositiveNodes,
            F5cWalkerLaneKind::ReplayOutputNegativeNodes,
            F5cWalkerLaneKind::ReplayOutputPositiveChildren,
            F5cWalkerLaneKind::ReplayOutputNegativeChildren,
            F5cWalkerLaneKind::ReplayOutputInsertionOrder,
            F5cWalkerLaneKind::SelectedRecursiveBounds,
        ] {
            self.memo.walker_resources.release(kind);
        }
    }

    #[allow(dead_code)]
    fn stage_flat_raw_candidate(
        &mut self,
        staged: &mut TrackedVec<'meter, F5cStagedCandidate<'meter>>,
        mut draft: f5c_draft::FlatDraft,
    ) -> Result<(), SolveAvailabilityError> {
        let kinds = [
            F5cWalkerLaneKind::ReplayOutputPositiveNodes,
            F5cWalkerLaneKind::ReplayOutputNegativeNodes,
            F5cWalkerLaneKind::ReplayOutputPositiveChildren,
            F5cWalkerLaneKind::ReplayOutputNegativeChildren,
            F5cWalkerLaneKind::SelectedRecursiveBounds,
            F5cWalkerLaneKind::ReplayOutputInsertionOrder,
        ];
        let capacities = [
            draft.positive_nodes.capacity(),
            draft.negative_nodes.capacity(),
            draft.positive_children.capacity(),
            draft.negative_children.capacity(),
            draft.recursive_bounds.capacity(),
            draft.insertion_order.capacity(),
        ];
        let transfer = (|| {
            if staged.len() == staged.capacity() {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            let mut bytes = [0; 6];
            for index in 0..6 {
                if self.memo.walker_resources.lanes[kinds[index] as usize].actual_capacity
                    != capacities[index]
                {
                    return Err(SolveAvailabilityError::IdentityExhausted);
                }
                bytes[index] = capacities[index]
                    .checked_mul(kinds[index].slot_size())
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            }
            let transferred = bytes
                .iter()
                .try_fold(0usize, |total, bytes| total.checked_add(*bytes))
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let future_external = self
                .memo
                .retained_bytes()?
                .checked_add(
                    self.memo
                        .walker_resources
                        .retained_bytes()?
                        .checked_sub(transferred)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?,
                )
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            claim_flat_draft_batch(self.source_meter, &mut draft, bytes,
                future_external, capacities, kinds.map(F5cWalkerLaneKind::slot_size))
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)
        })();
        let allocations = match transfer {
            Ok(allocations) => allocations,
            Err(error) => {
                f5c_replay::release_flat_output(&mut self.memo, draft,
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    Some(self.source_meter));
                self.memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::SelectedRecursiveBounds);
                return Err(error);
            }
        };
        self.release_staged_raw_output_lanes();
        staged.push_reserved(F5cStagedCandidate {
            candidate: F5cNormalizedCandidate {
                draft,
                stats: f5c_normalization::FlatNormalizationStats {
                    key_writes: 0,
                    child_comparisons: 0,
                    descriptor_words: 0,
                    word_comparisons: 0,
                    duplicates: 0,
                    resource: None,
                },
            },
            _allocations: allocations,
        });
        if let Err(error) = self.memo.observe_source_meter(self.source_meter) {
            drop(staged.pop());
            return Err(error);
        }
        Ok(())
    }

    /// Stage a substituted raw member while leaving the SCC root log open.
    #[allow(dead_code)]
    pub(super) fn build_and_stage_flat_raw_candidate(
        mut self,
        root: u32,
        staged: &mut TrackedVec<'meter, F5cStagedCandidate<'meter>>,
    ) -> (
        Result<(), SolveAvailabilityError>,
        F5cComponentExpansionMemo,
        usize,
        usize,
    ) {
        let result = self.build_flat_raw_candidate_pending(
            root,
            #[cfg(test)]
            false,
        );
        let result = result.and_then(|(draft, forest)| {
            let hits = self.shared_summary_hits;
            let uncacheable = self.uncacheable_states;
            let staged_result = self.stage_flat_raw_candidate(staged, draft);
            match staged_result {
                Ok(()) => {
                    #[cfg(test)]
                    self.record_transfer_raw_staged(&forest, staged);
                    self.release_raw_forest_for_batch(forest);
                    Ok((hits, uncacheable))
                }
                Err(error) => {
                    self.abort_raw_forest(forest)?;
                    Err(error)
                }
            }
        });
        let (result, hits, uncacheable) = match result {
            Ok((hits, uncacheable)) => (Ok(()), hits, uncacheable),
            Err(error) => (
                Err(error),
                self.shared_summary_hits,
                self.uncacheable_states,
            ),
        };
        (result, self.memo, hits, uncacheable)
    }

    #[cfg(test)]
    pub(super) fn boxed_r_candidates_for_test(
        source_meter: &'meter DraftHeapMeter,
        memo: &mut F5cComponentExpansionMemo,
        predicate: &F5cPositive<'meter>,
        bounds: &HashMap<u32, (F5cPositive<'meter>, F5cNegative<'meter>)>,
        reentries: &[F5cGuardedTrace],
        reentries_by_owner: &HashMap<u32, Vec<usize>>,
        eligible: impl Fn(u32) -> bool,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> Result<F5cObservedSet<'meter>, SolveAvailabilityError> {
        let mut source = F5cBoxedRCandidateSource {
            source_meter,
            predicate,
            bounds,
        };
        Self::r_candidates(
            source_meter,
            memo,
            &mut source,
            reentries,
            reentries_by_owner,
            eligible,
            positive_only,
            negative_only,
        )
    }

    #[cfg(test)]
    pub(super) fn boxed_post_r_for_test(
        source_meter: &'meter DraftHeapMeter,
        memo: &mut F5cComponentExpansionMemo,
        predicate: &F5cPositive<'meter>,
        bounds: &HashMap<u32, (F5cPositive<'meter>, F5cNegative<'meter>)>,
        raw_owner_order: &[u32],
        reentries: &[F5cGuardedTrace],
        candidates: &HashSet<u32>,
        order: &[u32],
        positive_incidences: &HashSet<u32>,
        negative_incidences: &HashSet<u32>,
    ) -> Result<
        F5cPostRSelection<'meter, (F5cPositive<'meter>, F5cNegative<'meter>), F5cPositive<'meter>>,
        SolveAvailabilityError,
    > {
        let mut source = F5cBoxedRCandidateSource {
            source_meter,
            predicate,
            bounds,
        };
        Self::post_r_selection(
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            Some(source_meter),
            memo,
            &mut source,
            candidates,
            raw_owner_order,
            reentries,
            order,
            positive_incidences,
            negative_incidences,
            &HashSet::new(),
            &HashSet::new(),
            |_| true,
        )
    }

    #[cfg(test)]
    pub(super) fn flat_post_r_for_test(
        memo: &mut F5cComponentExpansionMemo,
        draft: &f5c_draft::FlatDraft,
        bounds: &HashMap<u32, (f5c_draft::PositiveId, f5c_draft::NegativeId)>,
        raw_owner_order: &[u32],
        reentries: &[F5cGuardedTrace],
        candidates: &HashSet<u32>,
        order: &[u32],
        positive_incidences: &HashSet<u32>,
        negative_incidences: &HashSet<u32>,
    ) -> Result<
        (
            F5cPostRSelection<'meter,
                (f5c_draft::PositiveId, f5c_draft::NegativeId),
                f5c_draft::PositiveId,
            >,
            f5c_draft::FlatDraft,
        ),
        SolveAvailabilityError,
    > {
        let mut source = F5cFlatRCandidateSource {
            source: draft,
            output: f5c_draft::FlatDraft::default(),
            bounds,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            probe_meter: None,
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            _meter: std::marker::PhantomData,
        };
        let result = Self::post_r_selection(
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            None,
            memo,
            &mut source,
            candidates,
            raw_owner_order,
            reentries,
            order,
            positive_incidences,
            negative_incidences,
            &HashSet::new(),
            &HashSet::new(),
            |_| true,
        );
        match result {
            Ok(selection) => Ok((selection, source.output)),
            Err(error) => {
                f5c_replay::release_flat_output(memo, source.output,
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    None);
                release_flat_post_r_lanes(memo);
                Err(error)
            }
        }
    }

    #[cfg(test)]
    pub(super) fn build(
        &mut self,
        root: u32,
    ) -> Result<GeneralizationDraft<'meter>, SolveAvailabilityError> {
        let mut draft = self.build_inner(root)?;
        f5c_normalization::normalize_component(
            self.source_meter,
            std::slice::from_mut(&mut draft),
        )?;
        Ok(draft)
    }

    #[cfg(test)]
    pub(super) fn build_component(
        self,
        root: u32,
    ) -> (
        Result<GeneralizationDraft<'meter>, SolveAvailabilityError>,
        F5cComponentExpansionMemo,
        usize,
        usize,
    ) {
        self.build_component_with_bound_sidecar(root, None)
    }

    pub(super) fn build_component_with_bound_sidecar(
        mut self,
        root: u32,
        bound_sidecar: Option<&mut TrackedVec<'meter, TrackedAllocation<'meter>>>,
    ) -> (
        Result<GeneralizationDraft<'meter>, SolveAvailabilityError>,
        F5cComponentExpansionMemo,
        usize,
        usize,
    ) {
        self.in_component = true;
        let mut result = self.build_inner_with_bound_sidecar(root, bound_sidecar);
        if result.is_err() {
            let roots_restored = self
                .memo
                .finish_root_transaction(self.root_undo_checkpoint, false);
            self.memo.reset_active_scratch();
            self.active.clear();
            self.active_set.clear();
            self.frames.clear();
            let nodes_restored = self.memo.rollback_nodes(
                self.node_checkpoint,
                self.child_checkpoint,
                self.reverse_checkpoint,
                self.incidence_checkpoint,
            );
            if roots_restored.is_err() || nodes_restored.is_err() {
                result = Err(SolveAvailabilityError::IdentityExhausted);
            }
        } else {
            assert!(self.active.is_empty() && self.active_set.is_empty() && self.frames.is_empty());
            assert!(self.memo.active_rows.is_empty() && self.memo.active_conflicts.is_empty());
            assert!(self.memo.work.is_empty() && self.memo.conflict_journal.is_empty());
            if let Err(error) = self
                .memo
                .finish_root_transaction(self.root_undo_checkpoint, true)
            {
                result = Err(error);
            }
        }
        self.frames = Vec::new();
        self.active = Vec::new();
        self.active_set = HashSet::new();
        self.memo.generalizer_scratch_capacities = [0; 4];
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if self.memo.matrix_active {
            self.memo.matrix_generalizer_lengths = [0; 4];
            for lane in 16..20 { self.memo.matrix_owner_events.release(lane); }
        }
        #[cfg(test)]
        self.memo.observe_physical_memo();
        self.release_persistent_lanes();
        (
            result,
            self.memo,
            self.shared_summary_hits,
            self.uncacheable_states,
        )
    }

    pub(super) fn reject_unclassified_rows(
        meter: &F5cDraftWorkMeter,
        order: &[u32],
        recursive_set: &HashSet<u32>,
        q: &HashMap<u32, u32>,
        eligible: impl Fn(u32) -> bool,
    ) -> Result<(), SolveAvailabilityError> {
        for ordinal in order {
            meter.charge(1)?;
            if !eligible(*ordinal) && !recursive_set.contains(ordinal) && !q.contains_key(ordinal) {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
        }
        Ok(())
    }

    fn post_r_selection<S: F5cRCandidateSource<'meter>>(
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        source_meter: Option<&'meter DraftHeapMeter>,
        memo: &mut F5cComponentExpansionMemo,
        source: &mut S,
        candidates: &HashSet<u32>,
        raw_owner_order: &[u32],
        reentries: &[F5cGuardedTrace],
        order: &[u32],
        positive_incidences: &HashSet<u32>,
        negative_incidences: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
        eligible: impl Fn(u32) -> bool,
    ) -> Result<F5cPostRSelection<'meter, S::ReplayedBound, S::ReplayedPredicate>, SolveAvailabilityError>
    {
        let result = Self::post_r_selection_work(
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            source_meter,
            memo,
            source,
            candidates,
            raw_owner_order,
            reentries,
            order,
            positive_incidences,
            negative_incidences,
            positive_only,
            negative_only,
            eligible,
        );
        if result.is_err() {
            for kind in [
                F5cWalkerLaneKind::RetainedOwnerBounds,
                F5cWalkerLaneKind::BoxedRetainedOwnerBounds,
                F5cWalkerLaneKind::PostRSurvivingBounds,
                F5cWalkerLaneKind::PostRSurvivingTraces,
                F5cWalkerLaneKind::PostRRecursiveOwners,
                F5cWalkerLaneKind::PostRRecursiveSet,
                F5cWalkerLaneKind::PostROccurrenceOrder,
                F5cWalkerLaneKind::PostROccurrenceSeen,
                F5cWalkerLaneKind::PostRQuantifiers,
                F5cWalkerLaneKind::PostRRecursives,
            ] {
                source.release_post_r_lane(memo, kind);
            }
        }
        result
    }

    fn post_r_selection_work<S: F5cRCandidateSource<'meter>>(
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        source_meter: Option<&'meter DraftHeapMeter>,
        memo: &mut F5cComponentExpansionMemo,
        source: &mut S,
        candidates: &HashSet<u32>,
        raw_owner_order: &[u32],
        reentries: &[F5cGuardedTrace],
        order: &[u32],
        positive_incidences: &HashSet<u32>,
        negative_incidences: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
        eligible: impl Fn(u32) -> bool,
    ) -> Result<F5cPostRSelection<'meter, S::ReplayedBound, S::ReplayedPredicate>, SolveAvailabilityError>
    {
        source.release_replay_scratch();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let owner_meter = source_meter.or_else(|| source.f5c_probe_meter());
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut retained_bounds = ObservedWalkerMap::from_values(
            owner_meter, source.f5c_retained_bound_lane(),
            source.new_retained_bounds(candidates.len()));
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut retained_bounds = source.new_retained_bounds(candidates.len());
        for owner in raw_owner_order {
            if !candidates.contains(owner) {
                continue;
            }
            memo.work_meter.charge(1)?; // post-convergence bound owner
            let bound = source
                .replay_bound(memo, *owner, candidates, positive_only, negative_only)?
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let reservation = source.reserve_retained_bound(memo, &mut retained_bounds);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            retained_bounds.observe_capacity(retained_bounds.len() + 1);
            reservation?;
            retained_bounds.insert(*owner, bound);
        }
        if retained_bounds.len() != candidates.len() {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut surviving_bound_owners = ObservedWalkerSet::new_optional(
            owner_meter, F5cWalkerLaneKind::PostRSurvivingBounds);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut surviving_bound_owners = HashSet::new();
        for owner in raw_owner_order {
            let Some(bound) = retained_bounds.get(owner) else {
                continue;
            };
            memo.work_meter.charge(1)?; // revisited retained bound
            if source.guarded_bound_survives(memo, *owner, bound)? {
                let reservation = source.reserve_post_r_set(
                    memo,
                    &mut surviving_bound_owners,
                    F5cWalkerLaneKind::PostRSurvivingBounds,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                surviving_bound_owners.observe_capacity(surviving_bound_owners.len() + 1);
                reservation?;
                surviving_bound_owners.insert(*owner);
            }
        }
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut surviving_traces = ObservedWalkerSet::new_optional(
            owner_meter, F5cWalkerLaneKind::PostRSurvivingTraces);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut surviving_traces = HashSet::new();
        for (index, trace) in reentries.iter().enumerate() {
            memo.work_meter.charge(1)?; // post-convergence trace record
            if candidates.contains(&trace.owner)
                && surviving_bound_owners.contains(&trace.owner)
                && Self::guarded_trace_path_survives_with_meter(
                    memo,
                    trace,
                    candidates,
                    positive_only,
                    negative_only,
                )?
            {
                let reservation = source.reserve_post_r_trace_set(memo, &mut surviving_traces);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                surviving_traces.observe_capacity(surviving_traces.len() + 1);
                reservation?;
                surviving_traces.insert(index);
            }
        }
        #[cfg(test)]
        memo.record_post_r_sample((
            F5cWalkerLaneKind::PostRSurvivingBounds,
            surviving_bound_owners.capacity(),
            memo.walker_resources.lanes[F5cWalkerLaneKind::PostRSurvivingBounds as usize]
                .actual_capacity,
        ));
        drop(surviving_bound_owners);
        source.release_post_r_lane(memo, F5cWalkerLaneKind::PostRSurvivingBounds);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut recursive_owners_owner = owner_meter.map(|meter| RawWalkerOwner::new(meter,
            F5cWalkerLaneKind::PostRRecursiveOwners as usize,
            F5cWalkerLaneKind::PostRRecursiveOwners.slot_size()));
        let mut recursive_owners = Vec::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut recursive_set = ObservedWalkerSet::new_optional(
            owner_meter, F5cWalkerLaneKind::PostRRecursiveSet);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut recursive_set = HashSet::new();
        for (index, trace) in reentries.iter().enumerate() {
            memo.work_meter.charge(1)?; // recursive-owner ordering trace
            if surviving_traces.contains(&index) && !recursive_set.contains(&trace.owner) {
                let reservation = source.reserve_post_r_set(
                    memo,
                    &mut recursive_set,
                    F5cWalkerLaneKind::PostRRecursiveSet,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                recursive_set.observe_capacity(recursive_set.len() + 1);
                reservation?;
                let reservation = source.reserve_post_r_vec(
                    memo,
                    &mut recursive_owners,
                    F5cWalkerLaneKind::PostRRecursiveOwners,
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = recursive_owners_owner.as_mut() {
                    owner.observe(recursive_owners.len(), recursive_owners.capacity());
                }
                reservation?;
                recursive_set.insert(trace.owner);
                recursive_owners.push(trace.owner);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = recursive_owners_owner.as_mut() {
                    owner.observe(recursive_owners.len(), recursive_owners.capacity());
                }
            }
        }
        #[cfg(test)]
        memo.record_post_r_sample((
            F5cWalkerLaneKind::PostRSurvivingTraces,
            surviving_traces.capacity(),
            memo.walker_resources.lanes[F5cWalkerLaneKind::PostRSurvivingTraces as usize]
                .actual_capacity,
        ));
        drop(surviving_traces);
        source.release_post_r_lane(memo, F5cWalkerLaneKind::PostRSurvivingTraces);
        let retained_predicate =
            source.replay_predicate(memo, &recursive_set, positive_only, negative_only)?;
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut occurrence_owner = owner_meter.map(|meter| RawWalkerOwner::new(
            meter, F5cWalkerLaneKind::PostROccurrenceOrder as usize,
            F5cWalkerLaneKind::PostROccurrenceOrder.slot_size()));
        let first_occurrences = source.retained_occurrences(
            memo,
            &retained_predicate,
            &recursive_owners,
            &retained_bounds,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            occurrence_owner.as_mut(),
        )?;
        #[cfg(test)]
        memo.record_post_r_sample((
            F5cWalkerLaneKind::PostROccurrenceOrder,
            first_occurrences.capacity(),
            memo.walker_resources.lanes[F5cWalkerLaneKind::PostROccurrenceOrder as usize]
                .actual_capacity,
        ));
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut q = ObservedWalkerMap::new_optional(
            owner_meter, F5cWalkerLaneKind::PostRQuantifiers);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut q = HashMap::new();
        for ordinal in first_occurrences {
            memo.work_meter.charge(1)?; // Q first occurrence
            if !recursive_set.contains(&ordinal)
                && positive_incidences.contains(&ordinal)
                && negative_incidences.contains(&ordinal)
                && eligible(ordinal)
            {
                let next = u32::try_from(q.len())
                    .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                memo.work_meter.charge(1)?; // Q entry
                let reservation = source.reserve_post_r_map(
                    memo, &mut q, F5cWalkerLaneKind::PostRQuantifiers);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                q.observe_capacity(q.len() + 1);
                reservation?;
                q.insert(ordinal, next);
            }
        }
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        drop(occurrence_owner);
        source.release_post_r_lane(memo, F5cWalkerLaneKind::PostROccurrenceOrder);
        let q_count =
            u32::try_from(q.len()).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        f5c_draft::checked_q_r_count(q_count, recursive_owners.len())?;
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut r = ObservedWalkerMap::new_optional(
            owner_meter, F5cWalkerLaneKind::PostRRecursives);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut r = HashMap::new();
        for (index, ordinal) in recursive_owners.iter().enumerate() {
            memo.work_meter.charge(1)?; // R owner
            let offset =
                u32::try_from(index).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            let binder = q_count
                .checked_add(offset)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            memo.work_meter.charge(1)?; // R entry
            let reservation = source.reserve_post_r_map(
                memo, &mut r, F5cWalkerLaneKind::PostRRecursives);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            r.observe_capacity(r.len() + 1);
            reservation?;
            r.insert(*ordinal, binder);
        }
        Self::reject_unclassified_rows(&memo.work_meter, order, &recursive_set, &q, eligible)?;
        Ok(F5cPostRSelection {
            retained_bounds,
            retained_predicate,
            recursive_owners,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            recursive_owners_owner,
            recursive_set,
            #[cfg(not(all(test, feature = "f5c_resource_probe")))]
            lifetime: std::marker::PhantomData,
            q,
            r,
        })
    }

    fn r_candidates<'probe, S: F5cRCandidateSource<'meter>>(
        source_meter: &'probe DraftHeapMeter,
        memo: &mut F5cComponentExpansionMemo,
        source: &mut S,
        reentries: &[F5cGuardedTrace],
        reentries_by_owner: &HashMap<u32, Vec<usize>>,
        eligible: impl Fn(u32) -> bool,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> Result<F5cObservedSet<'probe>, SolveAvailabilityError> {
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut candidates = ObservedWalkerSet::new(source_meter, F5cWalkerLaneKind::RCandidates);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut candidates = HashSet::new();
        let result = (|| {
            for &owner in reentries_by_owner.keys() {
                memo.work_meter.charge(1)?; // candidate eligibility owner
                if eligible(owner) {
                    memo.work_meter.charge(1)?; // candidate entry
                    let reservation = memo.insert_physical_set_with_source(
                        &mut candidates,
                        owner,
                        F5cWalkerLaneKind::RCandidates,
                        source_meter,
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    candidates.observe_capacity(candidates.len() + 1);
                    reservation?;
                }
            }
            loop {
                memo.work_meter.charge(1)?; // fixed-point round
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let mut previous = ObservedWalkerSet::new(source_meter, F5cWalkerLaneKind::RPrevious);
                #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                let mut previous = HashSet::new();
                let round = (|| {
                    for &owner in &candidates {
                        let reservation = memo.reserve_physical_set_insert_with_source(
                            &mut previous,
                            owner,
                            F5cWalkerLaneKind::RPrevious,
                            source_meter,
                        );
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        previous.observe_capacity(previous.len() + 1);
                        reservation?;
                        memo.work_meter.charge(1)?; // copied candidate owner
                        previous.insert(owner);
                    }
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    let mut surviving_bounds = ObservedWalkerSet::new(source_meter, F5cWalkerLaneKind::RSurvivingBounds);
                    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                    let mut surviving_bounds = HashSet::new();
                    for owner in &previous {
                        memo.work_meter.charge(1)?; // examined bound owner
                        let Some(bound) = source.replay_bound(
                            memo,
                            *owner,
                            &previous,
                            positive_only,
                            negative_only,
                        )?
                        else {
                            continue;
                        };
                        let survives = source.guarded_bound_survives(memo, *owner, &bound)?;
                        source.release_replay_scratch();
                        if survives {
                            let reservation = memo.insert_physical_set_with_source(
                                &mut surviving_bounds,
                                *owner,
                                F5cWalkerLaneKind::RSurvivingBounds,
                                source_meter,
                            );
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            surviving_bounds.observe_capacity(surviving_bounds.len() + 1);
                            reservation?;
                        }
                    }
                    source.release_replay_scratch();
                    memo.work_meter.charge(candidates.capacity())?; // complete retain bucket scan
                    let mut retain_error = None;
                    candidates.retain(|owner| {
                        if retain_error.is_some() {
                            return true;
                        }
                        if !surviving_bounds.contains(owner) {
                            return false;
                        }
                        let Some(indices) = reentries_by_owner.get(owner) else {
                            return false;
                        };
                        for index in indices {
                            if let Err(error) = memo.work_meter.charge(1) {
                                retain_error = Some(error);
                                return true;
                            }
                            match Self::guarded_trace_path_survives_with_meter(
                                memo,
                                &reentries[*index],
                                &previous,
                                positive_only,
                                negative_only,
                            ) {
                                Ok(true) => return true,
                                Ok(false) => {}
                                Err(error) => {
                                    retain_error = Some(error);
                                    return true;
                                }
                            }
                        }
                        false
                    });
                    if let Some(error) = retain_error {
                        return Err(error);
                    }
                    let replayed_predicate =
                        source.replay_predicate(memo, &candidates, positive_only, negative_only)?;
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    let mut reachable = ObservedWalkerSet::new(source_meter, F5cWalkerLaneKind::RReachable);
                    #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                    let mut reachable = HashSet::new();
                    {
                        let mut walker =
                            f5c_tree_analysis::Walker::new_with_source(memo, source_meter);
                        let references = source.references_predicate(
                            &mut walker,
                            &replayed_predicate,
                            &candidates,
                            &mut reachable,
                        );
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        reachable.observe_capacity(reachable.len());
                        references?;
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        let mut frontier_owner = RawWalkerOwner::new(source_meter,
                            F5cWalkerLaneKind::RFrontier as usize,
                            F5cWalkerLaneKind::RFrontier.slot_size());
                        let mut frontier = Vec::new();
                        let frontier_result: Result<(), SolveAvailabilityError> = (|| {
                            for &owner in &reachable {
                                let reservation = walker.memo.reserve_walker_with_source(
                                    &mut frontier,
                                    F5cWalkerLaneKind::RFrontier,
                                    source_meter,
                                );
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                frontier_owner.observe(frontier.len(), frontier.capacity());
                                reservation?;
                                walker.memo.work_meter.charge(1)?; // copied frontier owner
                                frontier.push(owner);
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                frontier_owner.observe(frontier.len(), frontier.capacity());
                            }
                            while !frontier.is_empty() {
                                walker.memo.work_meter.charge(1)?; // reachability frontier pop
                                let owner = frontier.pop().expect("nonempty reachability frontier");
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                frontier_owner.observe(frontier.len(), frontier.capacity());
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                let mut referenced = ObservedWalkerSet::new(source_meter, F5cWalkerLaneKind::RReferenced);
                                #[cfg(not(all(test, feature = "f5c_resource_probe")))]
                                let mut referenced = HashSet::new();
                                let reference_result: Result<(), SolveAvailabilityError> = (|| {
                                    let references = source.references_bound(
                                        &mut walker,
                                        owner,
                                        &candidates,
                                        &mut referenced,
                                    );
                                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                                    referenced.observe_capacity(referenced.len());
                                    references?;
                                    #[cfg(test)]
                                    {
                                        let kinds = [
                                            F5cWalkerLaneKind::RCandidates,
                                            F5cWalkerLaneKind::RPrevious,
                                            F5cWalkerLaneKind::RSurvivingBounds,
                                            F5cWalkerLaneKind::RReachable,
                                            F5cWalkerLaneKind::RFrontier,
                                            F5cWalkerLaneKind::RReferenced,
                                        ];
                                        let physical = [
                                            candidates.capacity(),
                                            previous.capacity(),
                                            surviving_bounds.capacity(),
                                            reachable.capacity(),
                                            frontier.capacity(),
                                            referenced.capacity(),
                                        ];
                                        let reported = kinds.map(|kind| {
                                            walker.memo.walker_resources.lanes[kind as usize]
                                                .actual_capacity
                                        });
                                        walker.memo.r_fixed_point_live_sample =
                                            Some((physical, reported));
                                    }
                                    for referenced_owner in referenced.iter().copied() {
                                        walker.memo.work_meter.charge(1)?; // examined reference
                                        walker.memo.work_meter.charge(1)?; // possible frontier entry
                                        let new_owner = !reachable.contains(&referenced_owner);
                                        if new_owner {
                                            let reservation = walker.memo.insert_physical_set_with_source(
                                                &mut reachable,
                                                referenced_owner,
                                                F5cWalkerLaneKind::RReachable,
                                                source_meter,
                                            );
                                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                                            reachable.observe_capacity(reachable.len() + 1);
                                            reservation?;
                                            let reservation = walker.memo.reserve_walker_with_source(
                                                &mut frontier,
                                                F5cWalkerLaneKind::RFrontier,
                                                source_meter,
                                            );
                                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                                            frontier_owner.observe(frontier.len(), frontier.capacity());
                                            reservation?;
                                            frontier.push(referenced_owner);
                                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                                            frontier_owner.observe(frontier.len(), frontier.capacity());
                                        }
                                    }
                                    Ok(())
                                })(
                                );
                                drop(referenced);
                                walker.memo.release_walker_with_source(
                                    F5cWalkerLaneKind::RReferenced,
                                    source_meter,
                                )?;
                                reference_result?;
                            }
                            Ok(())
                        })(
                        );
                        drop(frontier);
                        walker
                            .memo
                            .walker_resources
                            .release(F5cWalkerLaneKind::RFrontier);
                        frontier_result?;
                    }
                    memo.work_meter.charge(candidates.capacity())?; // complete retain bucket scan
                    candidates.retain(|owner| reachable.contains(owner));
                    Ok(candidates == previous)
                })();
                drop(previous);
                memo.release_walker_with_source(F5cWalkerLaneKind::RPrevious, source_meter)?;
                memo.release_walker_with_source(F5cWalkerLaneKind::RSurvivingBounds, source_meter)?;
                memo.release_walker_with_source(F5cWalkerLaneKind::RReachable, source_meter)?;
                if round? {
                    break;
                }
            }
            Ok(())
        })();
        if let Err(error) = result {
            drop(candidates);
            memo.release_walker_with_source(F5cWalkerLaneKind::RCandidates, source_meter)?;
            return Err(error);
        }
        Ok(candidates)
    }

    #[cfg(test)]
    fn build_inner(
        &mut self,
        root: u32,
    ) -> Result<GeneralizationDraft<'meter>, SolveAvailabilityError> {
        self.build_inner_with_bound_sidecar(root, None)
    }

    fn build_inner_with_bound_sidecar(
        &mut self,
        root: u32,
        mut bound_sidecar: Option<&mut TrackedVec<'meter, TrackedAllocation<'meter>>>,
    ) -> Result<GeneralizationDraft<'meter>, SolveAvailabilityError> {
        let result = self.build_inner_work(root, bound_sidecar.as_deref_mut());
        // A failed build has already dropped its active bounds buffer. Refresh
        // the retained source charge before walker scratch is released.
        #[cfg(test)]
        self.memo.observe_physical_active_bound(0);
        let source_refresh = bound_sidecar
            .as_ref()
            .map(|sidecar| self.memo.observe_source_meter(sidecar.meter()));
        for kind in [
            F5cWalkerLaneKind::ClosureResult,
            F5cWalkerLaneKind::RawPositiveIncidences,
            F5cWalkerLaneKind::RawNegativeIncidences,
            F5cWalkerLaneKind::BoxedRawBounds,
            F5cWalkerLaneKind::BoxedCompletedOwners,
            F5cWalkerLaneKind::BoxedReentriesByOwner,
            F5cWalkerLaneKind::BoxedReentryIndices,
            F5cWalkerLaneKind::BoxedPositiveOnly,
            F5cWalkerLaneKind::BoxedNegativeOnly,
            F5cWalkerLaneKind::BoxedRetainedOwnerBounds,
            F5cWalkerLaneKind::PostRRecursiveOwners,
            F5cWalkerLaneKind::PostRRecursiveSet,
            F5cWalkerLaneKind::PostRQuantifiers,
            F5cWalkerLaneKind::PostRRecursives,
            F5cWalkerLaneKind::SelectedPositiveEliminated,
            F5cWalkerLaneKind::SelectedNegativeEliminated,
        ] {
            self.memo
                .release_walker_with_source(kind, self.source_meter)?;
        }
        if let Some(refresh) = source_refresh {
            refresh?;
        }
        result
    }

    fn build_inner_work(
        &mut self,
        root: u32,
        bound_sidecar: Option<&mut TrackedVec<'meter, TrackedAllocation<'meter>>>,
    ) -> Result<GeneralizationDraft<'meter>, SolveAvailabilityError> {
        #[cfg(test)]
        {
            self.memo.boxed_raw_lanes_live_sample = None;
        }
        let predicate = self.positive_row(root, true)?;
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut raw_recursive_bounds = ObservedWalkerMap::new(self.source_meter,
            F5cWalkerLaneKind::BoxedRawBounds);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut raw_recursive_bounds = HashMap::new();
        let mut raw_owner_order = Vec::new();
        let mut next_owner = 0;
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut completed_owners = ObservedWalkerSet::new(self.source_meter,
            F5cWalkerLaneKind::BoxedCompletedOwners);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut completed_owners = HashSet::new();
        while next_owner < self.reentries.len() {
            self.memo.work_meter.charge(1)?; // reentry owner
            let ordinal = self.reentries[next_owner].owner;
            next_owner += 1;
            self.memo.work_meter.charge(1)?; // completed-owner entry
            if completed_owners.contains(&ordinal) {
                continue;
            }
            let memo_bytes = self.memo.retained_bytes()?;
            let reservation = self.memo.walker_resources.with_source(
                self.source_meter,
                memo_bytes,
                F5cWalkerLaneKind::BoxedCompletedOwners,
                |walker| {
                    walker.reserve_generalizer_set(
                        &mut completed_owners,
                        F5cWalkerLaneKind::BoxedCompletedOwners,
                        memo_bytes,
                    )
                },
            );
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            completed_owners.observe_capacity(completed_owners.len() + 1);
            reservation?;
            completed_owners.insert(ordinal);
            let bounds = self
                .session
                .bounds
                .get(ordinal as usize)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let lower_empty =
                bounds.exact_non_variable_lowers.is_empty() && bounds.direct_lower_rows.is_empty();
            let upper_empty =
                bounds.exact_non_variable_uppers.is_empty() && bounds.direct_upper_rows.is_empty();
            let expanded_lower = self.positive_row(ordinal, false)?;
            let expanded_upper = self.negative_row(ordinal)?;
            let lower = if lower_empty {
                F5cPositive::Bottom
            } else {
                expanded_lower
            };
            let upper = if upper_empty {
                F5cNegative::Top
            } else {
                expanded_upper
            };
            self.memo.work_meter.charge(1)?; // raw bound entry
            self.memo.work_meter.charge(1)?; // raw owner order entry
            let memo_bytes = self.memo.retained_bytes()?;
            let reservation = self.memo.walker_resources.with_source(
                self.source_meter,
                memo_bytes,
                F5cWalkerLaneKind::BoxedRawBounds,
                |walker| {
                    walker.reserve_boxed_map(
                        &mut raw_recursive_bounds,
                        F5cWalkerLaneKind::BoxedRawBounds,
                        memo_bytes,
                    )
                },
            );
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            raw_recursive_bounds.observe_capacity(raw_recursive_bounds.len() + 1);
            reservation?;
            let (requested, growth) = self.memo.prepare_scratch_reserve(1)?;
            let old = raw_owner_order.capacity();
            let reservation = raw_owner_order.try_reserve(1);
            self.memo.generalizer_scratch_capacities[3] = raw_owner_order.capacity();
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            if self.memo.matrix_active { self.memo.matrix_generalizer_lengths[3] = raw_owner_order.len(); }
            #[cfg(test)]
            self.memo.observe_physical_memo();
            let committed = self.memo.commit_scratch_reserve(
                requested,
                growth,
                old,
                raw_owner_order.capacity(),
            );
            self.memo.observe_component_external(self.source_meter)?;
            committed?;
            reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            #[cfg(test)]
            if self.memo.fail_reserve_at
                == Some((F5cTestReserveFailure::RawOwnerOrder, raw_owner_order.len()))
            {
                self.memo.fail_reserve_at = None;
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            raw_recursive_bounds.insert(ordinal, (lower, upper));
            raw_owner_order.push(ordinal);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            if self.memo.matrix_active {
                self.memo.matrix_generalizer_lengths[3] = raw_owner_order.len();
                self.memo.observe_physical_memo();
            }
        }
        if self.invalid_effects {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let predicate = self.materialize_positive(predicate)?;
        self.materialize_recursive_bounds(&raw_owner_order, &mut raw_recursive_bounds)?;
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut reentry_owners = HashMap::<u32, RawWalkerOwner<'_>>::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut boxed_map_owner = RawWalkerOwner::new(self.source_meter,
            F5cWalkerLaneKind::BoxedReentriesByOwner as usize,
            F5cWalkerLaneKind::BoxedReentriesByOwner.slot_size());
        let mut reentries_by_owner = HashMap::<u32, Vec<usize>>::new();
        for (index, trace) in self.reentries.iter().enumerate() {
            self.memo.work_meter.charge(1)?; // indexed trace record
            self.memo.work_meter.charge(1)?; // owner index entry
            if let Some(indices) = reentries_by_owner.get_mut(&trace.owner) {
                let memo_bytes = self.memo.retained_bytes()?;
                let reservation = self.memo.walker_resources.with_source(
                    self.source_meter,
                    memo_bytes,
                    F5cWalkerLaneKind::BoxedReentryIndices,
                    |walker| walker.reserve_boxed_indices(indices, memo_bytes),
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                reentry_owners.get_mut(&trace.owner).expect("raw reentry owner")
                    .observe(indices.len(), indices.capacity());
                reservation?;
                indices.push(index);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                reentry_owners.get_mut(&trace.owner).expect("raw reentry owner")
                    .observe(indices.len(), indices.capacity());
            } else {
                let memo_bytes = self.memo.retained_bytes()?;
                let reservation = self.memo.walker_resources.with_source(
                    self.source_meter,
                    memo_bytes,
                    F5cWalkerLaneKind::BoxedReentriesByOwner,
                    |walker| {
                        walker.reserve_boxed_map(
                            &mut reentries_by_owner,
                            F5cWalkerLaneKind::BoxedReentriesByOwner,
                            memo_bytes,
                        )
                    },
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                boxed_map_owner.observe(reentries_by_owner.len(),
                    reentries_by_owner.capacity());
                reservation?;
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let mut raw_owner = RawWalkerOwner::new(self.source_meter,
                    F5cWalkerLaneKind::BoxedReentryIndices as usize,
                    std::mem::size_of::<usize>());
                let mut indices = Vec::new();
                let reservation = self.memo.walker_resources.with_source(
                    self.source_meter,
                    memo_bytes,
                    F5cWalkerLaneKind::BoxedReentryIndices,
                    |walker| walker.reserve_boxed_indices(&mut indices, memo_bytes),
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                raw_owner.observe(indices.len(), indices.capacity());
                reservation?;
                #[cfg(test)]
                if self.memo.fail_reserve_at
                    == Some((F5cTestReserveFailure::BoxedReentryIndices, index))
                {
                    self.memo.fail_reserve_at = None;
                    return Err(SolveAvailabilityError::IdentityExhausted);
                }
                indices.push(index);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                raw_owner.observe(indices.len(), indices.capacity());
                reentries_by_owner.insert(trace.owner, indices);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                boxed_map_owner.observe(reentries_by_owner.len(), reentries_by_owner.capacity());
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                reentry_owners.insert(trace.owner, raw_owner);
            }
        }
        let non_generic = self.non_generic_closure()?;
        let eligible = |ordinal: u32| {
            self.session
                .value_levels
                .get(ordinal as usize)
                .is_some_and(|level| *level > 0)
                && !non_generic.contains(&ordinal)
        };
        let (positive_incidences, negative_incidences) = Self::raw_forest_incidences(
            Some(self.source_meter),
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            None,
            &mut self.memo,
            &raw_owner_order,
            |walker, owner, positive, negative,
             #[cfg(all(test, feature = "f5c_resource_probe"))] mut positive_owner,
             #[cfg(all(test, feature = "f5c_resource_probe"))] mut negative_owner| {
                if let Some(owner) = owner {
                    let (lower, upper) = raw_recursive_bounds
                        .get(&owner)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    walker.incidences_positive(lower, positive, negative,
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        positive_owner.as_deref_mut(),
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        negative_owner.as_deref_mut())?;
                    walker.incidences_negative(upper, positive, negative,
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        positive_owner.as_deref_mut(),
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        negative_owner.as_deref_mut())
                } else {
                    walker.incidences_positive(&predicate, positive, negative,
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        positive_owner.as_deref_mut(),
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        negative_owner.as_deref_mut())
                }
            },
        )?;
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut positive_only = ObservedWalkerSet::new(self.source_meter,
            F5cWalkerLaneKind::BoxedPositiveOnly);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut positive_only = HashSet::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut negative_only = ObservedWalkerSet::new(self.source_meter,
            F5cWalkerLaneKind::BoxedNegativeOnly);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut negative_only = HashSet::new();
        for &owner in &self.order {
            self.memo.work_meter.charge(1)?; // metadata and eligibility owner
            if eligible(owner) {
                if positive_incidences.contains(&owner) && !negative_incidences.contains(&owner) {
                    self.memo.work_meter.charge(1)?; // positive-only entry
                    let memo_bytes = self.memo.retained_bytes()?;
                    let reservation = self.memo.walker_resources.with_source(
                        self.source_meter,
                        memo_bytes,
                        F5cWalkerLaneKind::BoxedPositiveOnly,
                        |walker| {
                            walker.reserve_generalizer_set(
                                &mut positive_only,
                                F5cWalkerLaneKind::BoxedPositiveOnly,
                                memo_bytes,
                            )
                        },
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    positive_only.observe_capacity(positive_only.len() + 1);
                    reservation?;
                    positive_only.insert(owner);
                }
                self.memo.work_meter.charge(1)?; // second eligibility/order scan
                if negative_incidences.contains(&owner) && !positive_incidences.contains(&owner) {
                    self.memo.work_meter.charge(1)?; // negative-only entry
                    let memo_bytes = self.memo.retained_bytes()?;
                    let reservation = self.memo.walker_resources.with_source(
                        self.source_meter,
                        memo_bytes,
                        F5cWalkerLaneKind::BoxedNegativeOnly,
                        |walker| {
                            walker.reserve_generalizer_set(
                                &mut negative_only,
                                F5cWalkerLaneKind::BoxedNegativeOnly,
                                memo_bytes,
                            )
                        },
                    );
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    negative_only.observe_capacity(negative_only.len() + 1);
                    reservation?;
                    negative_only.insert(owner);
                }
            } else {
                self.memo.work_meter.charge(1)?; // second eligibility/order scan
            }
        }
        #[cfg(test)]
        {
            let kinds = [
                F5cWalkerLaneKind::BoxedRawBounds,
                F5cWalkerLaneKind::BoxedCompletedOwners,
                F5cWalkerLaneKind::BoxedReentriesByOwner,
                F5cWalkerLaneKind::BoxedReentryIndices,
                F5cWalkerLaneKind::BoxedPositiveOnly,
                F5cWalkerLaneKind::BoxedNegativeOnly,
            ];
            let physical = [
                raw_recursive_bounds.capacity(),
                completed_owners.capacity(),
                reentries_by_owner.capacity(),
                reentries_by_owner.values().map(Vec::capacity).sum(),
                positive_only.capacity(),
                negative_only.capacity(),
            ];
            let reported =
                kinds.map(|kind| self.memo.walker_resources.lanes[kind as usize].actual_capacity);
            self.memo.boxed_raw_lanes_live_sample = Some((physical, reported));
        }
        let mut r_source = F5cBoxedRCandidateSource {
            source_meter: self.source_meter,
            predicate: &predicate,
            bounds: &raw_recursive_bounds,
        };
        let candidates = Self::r_candidates(
            self.source_meter,
            &mut self.memo,
            &mut r_source,
            &self.reentries,
            &reentries_by_owner,
            eligible,
            &positive_only,
            &negative_only,
        )?;
        let selection = Self::post_r_selection(
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            Some(self.source_meter),
            &mut self.memo,
            &mut r_source,
            &candidates,
            &raw_owner_order,
            &self.reentries,
            &self.order,
            &positive_incidences,
            &negative_incidences,
            &positive_only,
            &negative_only,
            eligible,
        );
        drop(candidates);
        self.memo
            .release_walker_with_source(F5cWalkerLaneKind::RCandidates, self.source_meter)?;
        let F5cPostRSelection {
            retained_bounds,
            retained_predicate: _,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            recursive_owners_owner,
            recursive_owners,
            recursive_set,
            q,
            r,
            ..
        } = selection?;
        drop(retained_bounds);
        self.memo.release_walker_with_source(
            F5cWalkerLaneKind::BoxedRetainedOwnerBounds,
            self.source_meter,
        )?;
        let q_count =
            u32::try_from(q.len()).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        #[cfg(feature = "shadow-f5")]
        if let Some(origins) = self.shadow_origins.as_deref_mut() {
            // Keys are the exact live-row ordinals traversed by this generalizer.
            // Write by its selected binder ordinal, retaining no predicate/bounds.
            origins.resize(q.len() + r.len(), (ShadowFreshBinderKind::Quantified, 0, 0));
            for (&row, &binder) in q.iter() {
                origins[binder as usize] = (ShadowFreshBinderKind::Quantified, binder, row);
            }
            for (&row, &binder) in r.iter() {
                origins[binder as usize] = (ShadowFreshBinderKind::Recursive, binder, row);
            }
        }

        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut positive_eliminated = ObservedWalkerSet::new(self.source_meter,
            F5cWalkerLaneKind::SelectedPositiveEliminated);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut positive_eliminated = HashSet::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut negative_eliminated = ObservedWalkerSet::new(self.source_meter,
            F5cWalkerLaneKind::SelectedNegativeEliminated);
        #[cfg(not(all(test, feature = "f5c_resource_probe")))]
        let mut negative_eliminated = HashSet::new();
        for ordinal in self.order.iter().copied() {
            self.memo.work_meter.charge(1)?; // positive eliminated-set owner
            if !recursive_set.contains(&ordinal)
                && !q.contains_key(&ordinal)
                && positive_only.contains(&ordinal)
            {
                self.memo.work_meter.charge(1)?;
                let bytes = self.memo.retained_bytes()?;
                let reservation = self.memo.walker_resources.with_source(
                    self.source_meter,
                    bytes,
                    F5cWalkerLaneKind::SelectedPositiveEliminated,
                    |walker| {
                        walker.reserve_generalizer_set(
                            &mut positive_eliminated,
                            F5cWalkerLaneKind::SelectedPositiveEliminated,
                            bytes,
                        )
                    },
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                positive_eliminated.observe_capacity(positive_eliminated.len() + 1);
                reservation?;
                positive_eliminated.insert(ordinal);
            }
        }
        for ordinal in self.order.iter().copied() {
            self.memo.work_meter.charge(1)?; // negative eliminated-set owner
            if !recursive_set.contains(&ordinal)
                && !q.contains_key(&ordinal)
                && negative_only.contains(&ordinal)
            {
                self.memo.work_meter.charge(1)?;
                let bytes = self.memo.retained_bytes()?;
                let reservation = self.memo.walker_resources.with_source(
                    self.source_meter,
                    bytes,
                    F5cWalkerLaneKind::SelectedNegativeEliminated,
                    |walker| {
                        walker.reserve_generalizer_set(
                            &mut negative_eliminated,
                            F5cWalkerLaneKind::SelectedNegativeEliminated,
                            bytes,
                        )
                    },
                );
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                negative_eliminated.observe_capacity(negative_eliminated.len() + 1);
                reservation?;
                negative_eliminated.insert(ordinal);
            }
        }
        let predicate = f5c_binder_substitution::substitute_positive(
            self.source_meter,
            &mut self.memo,
            predicate,
            &q,
            &r,
            &positive_eliminated,
            &negative_eliminated,
        )?;
        let mut tracked_bounds = bound_sidecar
            .as_ref()
            .map(|sidecar| TrackedVec::<F5cRecursiveBound>::new_with_kind(
                sidecar.meter(), PhysicalOwnerKind::SourceActiveBounds));
        if let Some(bounds) = tracked_bounds.as_mut() {
            #[cfg(test)]
            let old_capacity = bounds.capacity();
            self.memo.observe_component_external(bounds.meter())?;
            let reservation = bounds.try_reserve_exact(recursive_owners.len());
            #[cfg(test)]
            self.memo.recursive_bound_reserves.push((
                recursive_owners.len(),
                bounds.capacity(),
                usize::from(bounds.capacity() > old_capacity),
            ));
            // A failed reserve can still leave a real allocation behind.
            #[cfg(test)]
            self.memo.observe_physical_active_bound(bounds.capacity());
            self.memo.observe_source_meter(bounds.meter())?;
            reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            #[cfg(test)]
            if self.memo.fail_reserve_at
                == Some((F5cTestReserveFailure::RecursiveBoundAfterReserve, 0))
            {
                self.memo.fail_reserve_at = None;
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
        }
        let mut recursive_bounds = if tracked_bounds.is_none() {
            Vec::with_capacity(recursive_owners.len())
        } else {
            Vec::new()
        };
        for ordinal in &recursive_owners {
            self.memo.work_meter.charge(1)?; // recursive bound owner
            let Some(binder) = r.get(ordinal).copied() else {
                continue;
            };
            self.memo.work_meter.charge(1)?; // removed raw bound
            let (raw_lower, raw_upper) = raw_recursive_bounds
                .remove(ordinal)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let lower = f5c_binder_substitution::substitute_positive(
                self.source_meter,
                &mut self.memo,
                raw_lower,
                &q,
                &r,
                &positive_eliminated,
                &negative_eliminated,
            )?;
            let upper = f5c_binder_substitution::substitute_negative(
                self.source_meter,
                &mut self.memo,
                raw_upper,
                &q,
                &r,
                &positive_eliminated,
                &negative_eliminated,
            )?;
            self.memo.work_meter.charge(1)?; // result bound
            let bound = F5cRecursiveBound {
                ordinal: binder,
                lower,
                upper,
            };
            if let Some(bounds) = tracked_bounds.as_mut() {
                bounds.push_reserved(bound);
            } else {
                recursive_bounds.push(bound);
            }
        }
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        drop(recursive_owners);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        drop(recursive_owners_owner);
        if let (Some(bounds), Some(sidecar)) = (tracked_bounds, bound_sidecar) {
            #[cfg(test)]
            let bound_capacity = bounds.capacity();
            let (raw, mut token) = bounds.into_raw_with_token();
            token.classify(PhysicalOwnerKind::SourceHeldBounds);
            sidecar.push_reserved(token);
            #[cfg(test)]
            self.memo.transfer_physical_bound(bound_capacity);
            recursive_bounds = raw;
        }
        Ok(GeneralizationDraft {
            quantifier_count: q_count,
            recursive_bounds,
            predicate,
        })
    }
}

fn checked_raw_root_append(
    current: usize,
    additional: usize,
) -> Result<usize, SolveAvailabilityError> {
    let appended = current
        .checked_add(additional)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    u32::try_from(appended).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
    Ok(current)
}

#[cfg(test)]
mod raw_root_count_tests {
    use super::{SolveAvailabilityError, checked_raw_root_append};

    #[test]
    fn checked_raw_root_append_rejects_unrepresentable_post_append_count() {
        let limit = u32::MAX as usize;
        assert_eq!(checked_raw_root_append(limit - 1, 1), Ok(limit - 1));
        assert_eq!(
            checked_raw_root_append(limit - 1, 2),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert_eq!(
            checked_raw_root_append(limit, 1),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert_eq!(
            checked_raw_root_append(usize::MAX, 1),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
    }
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
mod observed_walker_set_tests {
    use super::*;

    #[test]
    fn flat_occurrence_order_uses_probe_meter_without_explicit_source_meter() {
        let path = std::env::temp_dir().join(format!(
            "f5c-flat-occurrence-order-{}-{:?}.bin", std::process::id(),
            std::thread::current().id()));
        crate::f5c_draft_heap::open_f5c_resource_events(&path).unwrap();
        let meter = DraftHeapMeter::default();
        meter.set_event_component(23);
        let mut draft = f5c_draft::FlatDraft::default();
        draft.predicate = Some(draft.positive(f5c_draft::PositiveNode::Variable(7)).unwrap());
        let bounds = HashMap::new();
        let mut source = F5cFlatRCandidateSource {
            source: &draft,
            output: f5c_draft::FlatDraft::default(),
            bounds: &bounds,
            probe_meter: Some(&meter),
        };
        let mut memo = F5cComponentExpansionMemo::default();
        let selection = F5cGeneralizer::post_r_selection(
            None, &mut memo, &mut source, &HashSet::new(), &[], &[], &[],
            &HashSet::new(), &HashSet::new(), &HashSet::new(), &HashSet::new(), |_| true,
        ).unwrap();
        drop(selection);
        release_flat_post_r_lanes(&mut memo);
        let before_release = meter.family6_event_current().unwrap();
        f5c_replay::release_flat_output(&mut memo, source.output, Some(&meter));
        let after_release = meter.family6_event_current().unwrap();
        assert!(after_release.1 < before_release.1);
        crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(path).unwrap();
        let role = 32 + F5cWalkerLaneKind::PostROccurrenceOrder as u64;
        let events: Vec<[u64; 8]> = bytes[8..].chunks_exact(64).map(|event| {
            std::array::from_fn(|index| u64::from_le_bytes(
                event[index * 8..(index + 1) * 8].try_into().unwrap()))
        }).filter(|event| event[3] == role).collect();
        assert_eq!(events.iter().map(|event| event[2]).collect::<Vec<_>>(),
            [1, 3, 5]);
        assert!(events.iter().all(|event| event[0] == 23
            && event[1] == events[0][1]));
        let seen_role = 32 + F5cWalkerLaneKind::PostROccurrenceSeen as u64;
        let seen_events: Vec<[u64; 8]> = bytes[8..].chunks_exact(64).map(|event| {
            std::array::from_fn(|index| u64::from_le_bytes(
                event[index * 8..(index + 1) * 8].try_into().unwrap()))
        }).filter(|event| event[3] == seen_role).collect();
        assert_eq!(seen_events.iter().map(|event| event[2]).collect::<Vec<_>>(),
            [1, 3, 5]);
        assert!(seen_events.iter().all(|event| event[0] == 23
            && event[1] == seen_events[0][1]));
    }

    #[test]
    fn selected_eliminated_sets_release_after_success_and_error() {
        let path = std::env::temp_dir().join(format!(
            "f5c-selected-eliminated-{}-{:?}.bin", std::process::id(),
            std::thread::current().id()));
        crate::f5c_draft_heap::open_f5c_resource_events(&path).unwrap();
        let meter = DraftHeapMeter::default();
        for (kind, fail) in [
            (F5cWalkerLaneKind::SelectedPositiveEliminated, false),
            (F5cWalkerLaneKind::SelectedNegativeEliminated, false),
            (F5cWalkerLaneKind::SelectedPositiveEliminated, true),
            (F5cWalkerLaneKind::SelectedNegativeEliminated, true),
        ] {
            let result = (|| -> Result<(), ()> {
                let mut set = ObservedWalkerSet::<u32>::new(&meter, kind);
                let reservation = set.values.try_reserve(1).map_err(|_| ());
                set.observe_capacity(0);
                reservation?;
                if fail { return Err(()); }
                set.insert(7);
                Ok(())
            })();
            assert_eq!(result.is_err(), fail);
        }
        crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(path).unwrap();
        let events: Vec<[u64; 8]> = bytes[8..].chunks_exact(64).map(|event| {
            std::array::from_fn(|index| u64::from_le_bytes(
                event[index * 8..(index + 1) * 8].try_into().unwrap()))
        }).collect();
        for lane in [F5cWalkerLaneKind::SelectedPositiveEliminated,
            F5cWalkerLaneKind::SelectedNegativeEliminated]
        {
            let owners: Vec<u64> = events.iter()
                .filter(|event| event[3] == 32 + lane as u64 && event[2] == 1)
                .map(|event| event[1]).collect();
            assert_eq!(owners.len(), 2);
            assert_ne!(owners[0], owners[1]);
            for (index, owner) in owners.iter().enumerate() {
                let operations: Vec<u64> = events.iter()
                    .filter(|event| event[1] == *owner)
                    .map(|event| event[2]).collect();
                assert_eq!(operations, if index == 0 {
                    vec![1, 3, 5]
                } else {
                    vec![1, 3, 5]
                });
            }
        }
    }

    #[test]
    fn raw_forest_set_map_and_callback_owners_shape_and_release() {
        let path = std::env::temp_dir().join(format!(
            "f5c-raw-forest-owners-{}-{:?}.bin", std::process::id(),
            std::thread::current().id()));
        crate::f5c_draft_heap::open_f5c_resource_events(&path).unwrap();
        let meter = DraftHeapMeter::default();
        let mut seen_owner = RawWalkerOwner::new(&meter,
            F5cWalkerLaneKind::RawOwnerSeen as usize,
            F5cWalkerLaneKind::RawOwnerSeen.slot_size());
        let mut seen = HashSet::<u32>::new();
        let mut bounds_owner = RawWalkerOwner::new(&meter,
            F5cWalkerLaneKind::RawOwnerBounds as usize,
            F5cWalkerLaneKind::RawOwnerBounds.slot_size());
        let mut bounds = HashMap::<u32, (f5c_draft::PositiveId, f5c_draft::NegativeId)>::new();
        let mut trace_owner = RawWalkerOwner::new(&meter,
            F5cWalkerLaneKind::RawCallbackTrace as usize,
            F5cWalkerLaneKind::RawCallbackTrace.slot_size());
        let mut trace = Vec::<(u32, Polarity)>::new();
        seen.try_reserve(1).unwrap();
        seen_owner.observe(seen.len(), seen.capacity());
        assert!(seen.try_reserve(usize::MAX).is_err());
        seen_owner.observe(seen.len(), seen.capacity());
        seen.insert(7);
        seen_owner.observe(seen.len(), seen.capacity());
        bounds.try_reserve(1).unwrap();
        bounds_owner.observe(bounds.len(), bounds.capacity());
        bounds.insert(7, (f5c_draft::PositiveId(0), f5c_draft::NegativeId(0)));
        bounds_owner.observe(bounds.len(), bounds.capacity());
        let value = bounds.remove(&7).unwrap();
        bounds_owner.observe(bounds.len(), bounds.capacity());
        bounds.insert(7, value);
        bounds_owner.observe(bounds.len(), bounds.capacity());
        trace.try_reserve(1).unwrap();
        trace_owner.observe(trace.len(), trace.capacity());
        trace.push((7, Polarity::Positive));
        trace_owner.observe(trace.len(), trace.capacity());
        drop(trace);
        drop(trace_owner);
        drop(bounds);
        drop(bounds_owner);
        drop(seen);
        drop(seen_owner);
        let (_, _) = crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(path).unwrap();
        let events: Vec<[u64; 8]> = bytes[8..].chunks_exact(64).map(|event| {
            std::array::from_fn(|index| u64::from_le_bytes(
                event[index * 8..(index + 1) * 8].try_into().unwrap()))
        }).collect();
        for lane in [F5cWalkerLaneKind::RawOwnerSeen,
            F5cWalkerLaneKind::RawOwnerBounds, F5cWalkerLaneKind::RawCallbackTrace]
        {
            let operations: Vec<u64> = events.iter()
                .filter(|event| event[3] == 32 + lane as u64)
                .map(|event| event[2]).collect();
            assert_eq!(operations.first(), Some(&1));
            assert_eq!(operations.last(), Some(&5));
            assert!(operations.contains(&3));
            assert!(!operations.contains(&2));
        }
        assert!(!events.iter().any(|event| event[4] == usize::MAX as u64));
    }

    #[test]
    fn reserve_then_early_return_releases_set_owner() {
        let path = std::env::temp_dir().join(format!(
            "f5c-observed-set-{}-{:?}.bin", std::process::id(),
            std::thread::current().id()));
        crate::f5c_draft_heap::open_f5c_resource_events(&path).unwrap();
        let meter = DraftHeapMeter::default();
        let result = (|| -> Result<(), ()> {
            let mut set = ObservedWalkerSet::<u32>::new(&meter,
                F5cWalkerLaneKind::BoxedPositiveOnly);
            let reservation = set.values.try_reserve(1).map_err(|_| ());
            set.observe_capacity(1);
            reservation?;
            return Err(());
        })();
        assert_eq!(result, Err(()));
        let (count, _) = crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(path).unwrap();
        assert_eq!(count, 3);
        let operations: Vec<u64> = bytes[8..].chunks_exact(64).map(|event| {
            u64::from_le_bytes(event[16..24].try_into().unwrap())
        }).collect();
        assert_eq!(operations, [1, 3, 5]);
    }

    #[test]
    fn observed_walker_map_remove_accepts_borrowed_key() {
        let meter = DraftHeapMeter::default();
        let mut map = ObservedWalkerMap::<String, u32>::new(&meter,
            F5cWalkerLaneKind::BoxedRawBounds);
        map.insert("owner".to_owned(), 7);
        assert_eq!(map.len(), 1);
        assert_eq!(map.remove("owner"), Some(7));
        assert!(map.is_empty());
    }

    #[test]
    fn moved_post_r_selection_releases_recursive_set_owner() {
        let path = std::env::temp_dir().join(format!(
            "f5c-post-r-set-{}-{:?}.bin", std::process::id(),
            std::thread::current().id()));
        crate::f5c_draft_heap::open_f5c_resource_events(&path).unwrap();
        let meter = DraftHeapMeter::default();
        let mut recursive_set = ObservedWalkerSet::<u32>::new(&meter,
            F5cWalkerLaneKind::PostRRecursiveSet);
        recursive_set.values.try_reserve(1).unwrap();
        recursive_set.observe_capacity(1);
        recursive_set.insert(7);
        let selection = F5cPostRSelection {
            retained_bounds: ObservedWalkerMap::<u32, ()>::new(&meter,
                F5cWalkerLaneKind::BoxedRetainedOwnerBounds),
            retained_predicate: (), recursive_owners: Vec::new(),
            recursive_owners_owner: None,
            recursive_set,
            q: ObservedWalkerMap::new(&meter, F5cWalkerLaneKind::PostRQuantifiers),
            r: ObservedWalkerMap::new(&meter, F5cWalkerLaneKind::PostRRecursives),
        };
        assert!(selection.recursive_set.contains(&7));
        drop(selection);
        let (count, _) = crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(path).unwrap();
        assert_eq!(count, 9);
        let operations: Vec<u64> = bytes[8..].chunks_exact(64).map(|event| {
            u64::from_le_bytes(event[16..24].try_into().unwrap())
        }).collect();
        assert_eq!(operations, [1, 3, 1, 1, 1, 5, 5, 5, 5]);
    }

    #[test]
    fn moved_reentry_map_keeps_distinct_index_owner() {
        let path = std::env::temp_dir().join(format!(
            "f5c-reentry-map-{}-{:?}.bin", std::process::id(),
            std::thread::current().id()));
        crate::f5c_draft_heap::open_f5c_resource_events(&path).unwrap();
        let meter = DraftHeapMeter::default();
        let mut map_owner = RawWalkerOwner::new(&meter,
            F5cWalkerLaneKind::BoxedReentriesByOwner as usize,
            F5cWalkerLaneKind::BoxedReentriesByOwner.slot_size());
        let mut index_owner = RawWalkerOwner::new(&meter,
            F5cWalkerLaneKind::BoxedReentryIndices as usize,
            std::mem::size_of::<usize>());
        let mut indices = Vec::with_capacity(2);
        indices.push(3);
        index_owner.observe(indices.len(), indices.capacity());
        let mut values = HashMap::new();
        values.insert(7, indices);
        map_owner.observe(values.len(), values.capacity());
        let mut index_owners = HashMap::new();
        index_owners.insert(7, index_owner);
        let moved = ObservedReentryMap { values, _map_owner: map_owner,
            _index_owners: index_owners };
        assert_eq!(moved.get(&7).unwrap(), &[3]);
        drop(moved);
        let (count, _) = crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(path).unwrap();
        assert_eq!(count, 6);
        let events: Vec<[u64; 8]> = bytes[8..].chunks_exact(64).map(|event| {
            std::array::from_fn(|index| u64::from_le_bytes(
                event[index * 8..(index + 1) * 8].try_into().unwrap()))
        }).collect();
        assert_eq!(events.iter().map(|event| event[2]).collect::<Vec<_>>(),
            [1, 1, 3, 3, 5, 5]);
        assert_ne!(events[0][1], events[1][1]);
    }
}
