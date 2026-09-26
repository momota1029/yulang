use super::*;

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

    #[cfg(test)]
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum F5cPositive {
    Bottom,
    Int,
    Variable(u32),
    Quantified(u32),
    Recursive(u32),
    Shared(F5cSummaryNodeId),
    Union(Vec<F5cPositive>),
    Function {
        argument: Box<F5cNegative>,
        argument_effect: F5cNegativeEffect,
        result_effect: F5cPositiveEffect,
        result: Box<F5cPositive>,
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum F5cNegative {
    Top,
    Bottom,
    Int,
    Variable(u32),
    Quantified(u32),
    Recursive(u32),
    Shared(F5cSummaryNodeId),
    Intersection(Vec<F5cNegative>),
    Function {
        argument: Box<F5cPositive>,
        argument_effect: F5cPositiveEffect,
        result_effect: F5cNegativeEffect,
        result: Box<F5cNegative>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct F5cRecursiveBound {
    pub(super) ordinal: u32,
    pub(super) lower: F5cPositive,
    pub(super) upper: F5cNegative,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct GeneralizationDraft {
    pub(super) quantifier_count: u32,
    pub(super) recursive_bounds: Vec<F5cRecursiveBound>,
    pub(super) predicate: F5cPositive,
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

#[allow(dead_code)] // The candidate source arena is wired to the walker in the next gate.
mod flat_source_arena;
#[allow(dead_code)] // The candidate is exercised only by module-local test entrypoints.
mod flat_walk_sink;
#[cfg(test)]
pub(super) use flat_walk_sink::{F5cFlatWalkSink, FlatWalkValue};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum F5cSummaryNodeKind {
    PositiveBottom,
    PositiveInt,
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
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum F5cTestReserveFailure {
    ActiveMirrors,
    RawOwnerOrder,
    ChildrenAfterReserve,
    RootUndo,
}

#[derive(Clone, Copy, Default)]
pub(super) struct F5cMemoLane {
    pub(super) requested_slots: usize,
    pub(super) peak_bytes: usize,
    pub(super) capacity_growths: usize,
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
}

impl F5cWalkerLaneKind {
    pub(super) const ALL: [Self; 43] = [
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
    ];

    pub(super) fn slot_size(self) -> usize {
        match self {
            Self::Tasks => std::mem::size_of::<F5cWalkTask>(),
            Self::Values => std::mem::size_of::<F5cWalkValue>(),
            Self::DirectEdges => std::mem::size_of::<(usize, u32)>(),
            Self::SummaryTasks => std::mem::size_of::<F5cSummaryTask<'static>>(),
            Self::SummaryIds => std::mem::size_of::<F5cSummaryNodeId>(),
            Self::DirectTargets => std::mem::size_of::<u32>(),
            Self::Comparison => std::mem::size_of::<F5cCompareTask<'static>>(),
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
            Self::RawRoots => std::mem::size_of::<FlatWalkValue>(),
            Self::RawCallbackTrace => std::mem::size_of::<(u32, Polarity)>(),
            Self::AnalysisTasks => std::mem::size_of::<f5c_tree_analysis::Task<'static>>(),
            Self::ReplayTasks => std::mem::size_of::<f5c_replay::Task<'static>>(),
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
            Self::DraftInsertionOrder => std::mem::size_of::<f5c_draft::NodeRef>(),
        }
    }
}

#[derive(Clone, Copy, Default)]
pub(super) struct F5cWalkerLane {
    pub(super) requested_slots: usize,
    pub(super) actual_capacity: usize,
    pub(super) peak_bytes: usize,
    pub(super) capacity_growths: usize,
}

pub(super) struct F5cWalkerResources {
    pub(super) lanes: [F5cWalkerLane; 43],
    pub(super) peak_bytes: usize,
    pub(super) simultaneous_memo_peak_bytes: usize,
    pub(super) observed_memo_bytes: usize,
    value_slot_size: usize,
    #[cfg(test)]
    pub(super) independent_lanes: [F5cWalkerLane; 43],
    #[cfg(test)]
    pub(super) independent_peak_bytes: usize,
    #[cfg(test)]
    pub(super) independent_simultaneous_memo_peak_bytes: usize,
}

impl Default for F5cWalkerResources {
    fn default() -> Self {
        Self {
            lanes: [F5cWalkerLane::default(); 43],
            peak_bytes: 0,
            simultaneous_memo_peak_bytes: 0,
            observed_memo_bytes: 0,
            value_slot_size: 0,
            #[cfg(test)]
            independent_lanes: [F5cWalkerLane::default(); 43],
            #[cfg(test)]
            independent_peak_bytes: 0,
            #[cfg(test)]
            independent_simultaneous_memo_peak_bytes: 0,
        }
    }
}

impl F5cWalkerResources {
    #[cfg(test)]
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
        let independent = &self.independent_lanes[kind as usize];
        let independent_requested = independent
            .requested_slots
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let independent_growth = independent
            .capacity_growths
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        Ok((requested, growth, independent_requested, independent_growth))
    }

    #[cfg(test)]
    fn observe_table_capacity(
        &mut self,
        kind: F5cWalkerLaneKind,
        old: usize,
        capacity: usize,
        memo_bytes: usize,
        counters: (usize, usize, usize, usize),
    ) -> Result<(), SolveAvailabilityError> {
        let lane = &mut self.lanes[kind as usize];
        lane.requested_slots = counters.0;
        lane.actual_capacity = capacity;
        self.independent_lanes[kind as usize].requested_slots = counters.2;
        self.independent_lanes[kind as usize].actual_capacity = capacity;
        if old != capacity {
            lane.capacity_growths = counters.1;
            lane.peak_bytes = lane.peak_bytes.max(
                capacity
                    .checked_mul(kind.slot_size())
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            );
            self.independent_lanes[kind as usize].capacity_growths = counters.3;
            self.independent_lanes[kind as usize].peak_bytes = lane.peak_bytes;
        }
        self.observe_memo(memo_bytes)
    }

    #[cfg(test)]
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

    #[cfg(test)]
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
        let old_capacity = buffer.capacity();
        let reservation = buffer.try_reserve(additional);
        let new_capacity = buffer.capacity();
        self.lanes[index].requested_slots = requested;
        self.lanes[index].actual_capacity = new_capacity;
        #[cfg(test)]
        {
            self.independent_lanes[index].requested_slots = independent_requested;
            self.independent_lanes[index].actual_capacity = new_capacity;
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
        self.lanes[kind as usize].actual_capacity = 0;
        #[cfg(test)]
        {
            self.independent_lanes[kind as usize].actual_capacity = 0;
        }
    }

    pub(super) fn requested_slots(&self) -> Result<usize, SolveAvailabilityError> {
        self.lanes.iter().try_fold(0usize, |sum, lane| {
            sum.checked_add(lane.requested_slots)
                .ok_or(SolveAvailabilityError::IdentityExhausted)
        })
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

    pub(super) fn observe_memo(&mut self, memo_bytes: usize) -> Result<(), SolveAvailabilityError> {
        let scratch_bytes = self.retained_bytes()?;
        self.peak_bytes = self.peak_bytes.max(scratch_bytes);
        self.simultaneous_memo_peak_bytes = self.simultaneous_memo_peak_bytes.max(
            memo_bytes
                .checked_add(scratch_bytes)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        );
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
    pub(super) simultaneous_peak_bytes: usize,
    #[cfg(test)]
    pub(super) capacity_samples: Vec<[usize; 20]>,
    #[cfg(test)]
    pub(super) checked_materialization_scratch_sample: Option<[usize; 13]>,
    #[cfg(test)]
    pub(super) independent_generalizer_scratch_peak_bytes: usize,
    #[cfg(test)]
    pub(super) fail_observation_at: Option<F5cTestObservationFailure>,
    #[cfg(test)]
    pub(super) fail_reserve_at: Option<(F5cTestReserveFailure, usize)>,
    #[cfg(test)]
    pending_observation_failure: bool,
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
}

impl F5cComponentExpansionMemo {
    pub(super) fn reserve_walker<T>(
        &mut self,
        buffer: &mut Vec<T>,
        kind: F5cWalkerLaneKind,
    ) -> Result<(), SolveAvailabilityError> {
        let memo_bytes = self.retained_bytes()?;
        self.walker_resources.reserve(buffer, kind, 1, memo_bytes)
    }

    pub(super) fn reserve_walker_target(
        &mut self,
        targets: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        let memo_bytes = self.retained_bytes()?;
        self.walker_resources.reserve_set(targets, memo_bytes)
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
        #[cfg(test)]
        if self.fail_reserve_at == Some((F5cTestReserveFailure::RootUndo, self.root_undo.len())) {
            self.fail_reserve_at = None;
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let (requested, growth) = self.prepare_index_reserve(1)?;
        let old = self.root_undo.capacity();
        let reservation = self.root_undo.try_reserve(1);
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
        self.simultaneous_peak_bytes = self.simultaneous_peak_bytes.max(self.retained_bytes()?);
        #[cfg(test)]
        self.capacity_samples.push([
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
        ]);
        Ok(())
    }

    pub(super) fn positive_node(
        &mut self,
        value: &F5cPositive,
        incidence: Option<(u32, Polarity)>,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        self.node_iterative(F5cSummaryTask::Positive(value, incidence))
    }

    pub(super) fn negative_node(
        &mut self,
        value: &F5cNegative,
        incidence: Option<(u32, Polarity)>,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        self.node_iterative(F5cSummaryTask::Negative(value, incidence))
    }

    fn node_iterative(
        &mut self,
        first: F5cSummaryTask<'_>,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        let mut tasks = Vec::new();
        let mut ids = Vec::<F5cSummaryNodeId>::new();
        macro_rules! push_task {
            ($value:expr) => {{
                let value = $value;
                self.work_meter.charge(1)?;
                self.reserve_walker(&mut tasks, F5cWalkerLaneKind::SummaryTasks)?;
                tasks.push(value);
            }};
        }
        macro_rules! push_id {
            ($value:expr) => {{
                self.work_meter.charge(1)?;
                let value = $value;
                self.observe_walker()?;
                self.reserve_walker(&mut ids, F5cWalkerLaneKind::SummaryIds)?;
                ids.push(value);
            }};
        }
        let result = (|| {
            push_task!(first);
            while !tasks.is_empty() {
                self.work_meter.charge(1)?;
                let task = tasks.pop().expect("nonempty summary tasks");
                match task {
                    F5cSummaryTask::Positive(value, incidence) => match value {
                        F5cPositive::Bottom => {
                            push_id!(self.push_node(F5cSummaryNodeKind::PositiveBottom, incidence)?)
                        }
                        F5cPositive::Int => {
                            push_id!(self.push_node(F5cSummaryNodeKind::PositiveInt, incidence)?)
                        }
                        F5cPositive::Variable(row) => push_id!(
                            self.push_node(F5cSummaryNodeKind::PositiveRow(*row), incidence)?
                        ),
                        F5cPositive::Shared(id) => {
                            if incidence.is_some() {
                                let (start, _) = self.push_children(&[*id])?;
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
                        F5cNegative::Variable(row) => push_id!(
                            self.push_node(F5cSummaryNodeKind::NegativeRow(*row), incidence)?
                        ),
                        F5cNegative::Shared(id) => {
                            if incidence.is_some() {
                                let (start, _) = self.push_children(&[*id])?;
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
                        let (child_start, len) = self.push_children(&ids[start..])?;
                        ids.truncate(start);
                        push_id!(self.push_node(
                            F5cSummaryNodeKind::PositiveUnion {
                                start: child_start,
                                len
                            },
                            incidence
                        )?);
                    }
                    F5cSummaryTask::NegativeIntersection(start, incidence) => {
                        let (child_start, len) = self.push_children(&ids[start..])?;
                        ids.truncate(start);
                        push_id!(self.push_node(
                            F5cSummaryNodeKind::NegativeIntersection {
                                start: child_start,
                                len
                            },
                            incidence
                        )?);
                    }
                    F5cSummaryTask::PositiveFunction(incidence) => {
                        let result = ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let argument =
                            ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        push_id!(self.push_node(
                            F5cSummaryNodeKind::PositiveFunction { argument, result },
                            incidence
                        )?);
                    }
                    F5cSummaryTask::NegativeFunction(incidence) => {
                        let result = ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let argument =
                            ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted)?;
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
            ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted)
        })();
        self.walker_resources
            .release(F5cWalkerLaneKind::SummaryTasks);
        self.walker_resources.release(F5cWalkerLaneKind::SummaryIds);
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
    pub(super) fn positive_value(
        &mut self,
        id: F5cSummaryNodeId,
    ) -> Result<F5cPositive, SolveAvailabilityError> {
        self.positive_value_with(id, &mut |_, _| Ok(()))
    }

    pub(super) fn positive_value_with(
        &mut self,
        id: F5cSummaryNodeId,
        mark: &mut impl FnMut(u32, Polarity) -> Result<(), SolveAvailabilityError>,
    ) -> Result<F5cPositive, SolveAvailabilityError> {
        match self.materialize_summary(F5cMaterializeTask::Positive(id), mark)? {
            F5cWalkValue::Positive(value, _) => Ok(value),
            _ => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    #[cfg(test)]
    pub(super) fn negative_value(
        &mut self,
        id: F5cSummaryNodeId,
    ) -> Result<F5cNegative, SolveAvailabilityError> {
        self.negative_value_with(id, &mut |_, _| Ok(()))
    }

    pub(super) fn negative_value_with(
        &mut self,
        id: F5cSummaryNodeId,
        mark: &mut impl FnMut(u32, Polarity) -> Result<(), SolveAvailabilityError>,
    ) -> Result<F5cNegative, SolveAvailabilityError> {
        match self.materialize_summary(F5cMaterializeTask::Negative(id), mark)? {
            F5cWalkValue::Negative(value, _) => Ok(value),
            _ => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    fn materialize_summary(
        &mut self,
        first: F5cMaterializeTask,
        mark: &mut impl FnMut(u32, Polarity) -> Result<(), SolveAvailabilityError>,
    ) -> Result<F5cWalkValue, SolveAvailabilityError> {
        let mut tasks = Vec::new();
        let mut values = Vec::new();
        macro_rules! push_task {
            ($task:expr) => {{
                let task = $task;
                self.work_meter.charge(1)?; // scheduled task
                self.reserve_walker(&mut tasks, F5cWalkerLaneKind::MaterializeTasks)?;
                tasks.push(task);
            }};
        }
        macro_rules! push_value {
            ($value:expr) => {{
                self.work_meter.charge(1)?; // emitted value
                let value = $value;
                self.reserve_walker(&mut values, F5cWalkerLaneKind::MaterializeValues)?;
                values.push(value);
            }};
        }
        let result = (|| {
            push_task!(first);
            while !tasks.is_empty() {
                self.work_meter.charge(1)?; // popped task
                let task = tasks.pop().expect("nonempty materialization tasks");
                match task {
                    F5cMaterializeTask::Positive(id) | F5cMaterializeTask::Negative(id) => {
                        let node = self.node(id)?;
                        if let Some((row, polarity)) = node.incidence {
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
                        for child in values.drain(start..) {
                            let F5cWalkValue::Positive(value, _) = child else {
                                return Err(SolveAvailabilityError::IdentityExhausted);
                            };
                            self.reserve_walker(&mut parts, F5cWalkerLaneKind::PositiveParts)?;
                            parts.push(value);
                        }
                        push_value!(F5cWalkValue::Positive(F5cPositive::Union(parts), true));
                        self.walker_resources
                            .release(F5cWalkerLaneKind::PositiveParts);
                    }
                    F5cMaterializeTask::NegativeIntersection(start) => {
                        // The finish task follows only negative child tasks; each child
                        // leaves one value, so this suffix is exactly their results.
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
                        for child in values.drain(start..) {
                            let F5cWalkValue::Negative(value, _) = child else {
                                return Err(SolveAvailabilityError::IdentityExhausted);
                            };
                            self.reserve_walker(&mut parts, F5cWalkerLaneKind::NegativeParts)?;
                            parts.push(value);
                        }
                        push_value!(F5cWalkValue::Negative(
                            F5cNegative::Intersection(parts),
                            true
                        ));
                        self.walker_resources
                            .release(F5cWalkerLaneKind::NegativeParts);
                    }
                    F5cMaterializeTask::PositiveFunction => {
                        let F5cWalkValue::Positive(result, _) = values
                            .pop()
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?
                        else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        let F5cWalkValue::Negative(argument, _) = values
                            .pop()
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?
                        else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        push_value!(F5cWalkValue::Positive(
                            F5cPositive::Function {
                                argument: Box::new(argument),
                                argument_effect: F5cNegativeEffect::Empty,
                                result_effect: F5cPositiveEffect::Bottom,
                                result: Box::new(result),
                            },
                            true
                        ));
                    }
                    F5cMaterializeTask::NegativeFunction => {
                        let F5cWalkValue::Negative(result, _) = values
                            .pop()
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?
                        else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        let F5cWalkValue::Positive(argument, _) = values
                            .pop()
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?
                        else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        push_value!(F5cWalkValue::Negative(
                            F5cNegative::Function {
                                argument: Box::new(argument),
                                argument_effect: F5cPositiveEffect::Bottom,
                                result_effect: F5cNegativeEffect::Empty,
                                result: Box::new(result),
                            },
                            true
                        ));
                    }
                }
            }
            if values.len() != 1 {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            values
                .pop()
                .ok_or(SolveAvailabilityError::IdentityExhausted)
        })();
        self.walker_resources
            .release(F5cWalkerLaneKind::MaterializeTasks);
        self.walker_resources
            .release(F5cWalkerLaneKind::MaterializeValues);
        self.walker_resources
            .release(F5cWalkerLaneKind::PositiveParts);
        self.walker_resources
            .release(F5cWalkerLaneKind::NegativeParts);
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
            self.commit_scratch_reserve(requested, growth_if_changed, old, self.work.capacity())?;
            reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            self.visit_epochs[index] = self.visit_epoch;
            self.work.push(id);
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
        let (journal_requested, journal_growth) = self.prepare_scratch_reserve(self.roots.len())?;
        let old_journal_capacity = self.conflict_journal.capacity();
        let reservation = self.conflict_journal.try_reserve(self.roots.len());
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
        self.conflict_journal.clear();
        Ok(())
    }

    pub(super) fn enter_active(&mut self, row: u32) -> Result<(), SolveAvailabilityError> {
        let (row_requested, row_growth) = self.prepare_scratch_reserve(1)?;
        let old_row_capacity = self.active_rows.capacity();
        let reservation = self.active_rows.try_reserve(1);
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
        let id = F5cSummaryNodeId(
            u32::try_from(self.nodes.len())
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
        );
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
        self.commit_index_reserve(next, growth, old, self.parent_heads.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let (next, growth) = self.prepare_index_reserve(1)?;
        let old = self.root_heads.capacity();
        let reservation = self.root_heads.try_reserve(1);
        self.commit_index_reserve(next, growth, old, self.root_heads.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let (next, growth) = self.prepare_scratch_reserve(1)?;
        let old = self.visit_epochs.capacity();
        let reservation = self.visit_epochs.try_reserve(1);
        self.commit_scratch_reserve(next, growth, old, self.visit_epochs.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let (next, growth) = self.prepare_index_reserve(child_count)?;
        let old = self.reverse_parents.capacity();
        let reservation = self.reverse_parents.try_reserve(child_count);
        self.commit_index_reserve(next, growth, old, self.reverse_parents.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        if incidence.is_some() {
            let (next, growth) = self.prepare_index_reserve(1)?;
            let old = self.incidences.capacity();
            let reservation = self.incidences.try_reserve(1);
            self.commit_index_reserve(next, growth, old, self.incidences.capacity())?;
            reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            let (next, growth) = self.prepare_index_reserve(1)?;
            let old = self.incidence_heads.capacity();
            let reservation = self.incidence_heads.try_reserve(1);
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
        self.commit_index_reserve(next, growth, old, self.root_edges.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let (next, growth) = self.prepare_index_reserve(1)?;
        let old = self.root_edge_marks.capacity();
        let reservation = self.root_edge_marks.try_reserve(1);
        self.commit_index_reserve(next, growth, old, self.root_edge_marks.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let (next, growth) = self.prepare_scratch_reserve(1)?;
        let old = self.active_conflicts.capacity();
        let reservation = self.active_conflicts.try_reserve(1);
        self.commit_scratch_reserve(next, growth, old, self.active_conflicts.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.reserve_root_undo()?;
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
        self.generalizer_scratch_capacities = [0; 4];
        self.simultaneous_peak_bytes = 0;
        #[cfg(test)]
        self.capacity_samples.clear();
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

pub(super) enum F5cWalkValue {
    Positive(F5cPositive, bool),
    Negative(F5cNegative, bool),
}

pub(super) enum F5cCompareTask<'a> {
    Positive(&'a F5cPositive, &'a F5cPositive),
    Negative(&'a F5cNegative, &'a F5cNegative),
}

pub(super) enum F5cSummaryTask<'a> {
    Positive(&'a F5cPositive, Option<(u32, Polarity)>),
    Negative(&'a F5cNegative, Option<(u32, Polarity)>),
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
pub(super) struct F5cGeneralizer<'a> {
    pub(super) session: &'a InferenceSession,
    pub(super) memo: F5cComponentExpansionMemo,
    #[cfg(test)]
    pub(super) flat_sink: F5cFlatWalkSink,
    #[cfg(test)]
    raw_forest_live: bool,
    frozen_bound_epoch: usize,
    pub(super) frames: Vec<F5cExpansionFrame>,
    pub(super) shared_summary_hits: usize,
    pub(super) uncacheable_states: usize,
    uncacheable_seen: HashSet<F5cExpansionKey>,
    fatal_taint: bool,
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
    pub(super) order: Vec<u32>,
    pub(super) order_seen: HashSet<u32>,
    pub(super) reentries: Vec<F5cGuardedTrace>,
    pub(super) invalid_effects: bool,
}

#[cfg(test)]
pub(super) struct F5cRawForest {
    pub(super) draft: f5c_draft::FlatDraft,
    pub(super) raw_owner_order: Vec<u32>,
    pub(super) raw_bounds: HashMap<u32, (f5c_draft::PositiveId, f5c_draft::NegativeId)>,
    pub(super) callback_trace: Vec<(u32, Polarity)>,
}

trait F5cWalkSink {
    type Value;
    fn variable(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        polarity: Polarity,
        row: u32,
        cacheable: bool,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn shared(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        polarity: Polarity,
        id: F5cSummaryNodeId,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn int(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn bottom(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn top(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn cacheable(&self, value: &Self::Value) -> bool;
    fn finish_row(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        values: &mut Vec<Self::Value>,
        start: usize,
        row: u32,
        polarity: Polarity,
        root: bool,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn function(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        polarity: Polarity,
        argument: Self::Value,
        result: Self::Value,
    ) -> Result<Self::Value, SolveAvailabilityError>;
    fn promote(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        value: &Self::Value,
        row: u32,
        polarity: Polarity,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError>;
}

struct F5cBoxedWalkSink;

impl F5cWalkSink for F5cBoxedWalkSink {
    type Value = F5cWalkValue;
    fn variable(
        &mut self,
        _generalizer: &mut F5cGeneralizer<'_>,
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
        _generalizer: &mut F5cGeneralizer<'_>,
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
        _generalizer: &mut F5cGeneralizer<'_>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        Ok(match polarity {
            Polarity::Positive => F5cWalkValue::Positive(F5cPositive::Int, true),
            Polarity::Negative => F5cWalkValue::Negative(F5cNegative::Int, true),
        })
    }
    fn bottom(
        &mut self,
        _generalizer: &mut F5cGeneralizer<'_>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        Ok(match polarity {
            Polarity::Positive => F5cWalkValue::Positive(F5cPositive::Bottom, true),
            Polarity::Negative => F5cWalkValue::Negative(F5cNegative::Bottom, true),
        })
    }
    fn top(
        &mut self,
        _generalizer: &mut F5cGeneralizer<'_>,
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
        generalizer: &mut F5cGeneralizer<'_>,
        values: &mut Vec<Self::Value>,
        values_start: usize,
        row: u32,
        polarity: Polarity,
        root: bool,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        let value = match polarity {
            Polarity::Positive => {
                let mut parts = Vec::new();
                let mut cacheable = true;
                for child in values.drain(values_start..) {
                    let F5cWalkValue::Positive(value, child_cacheable) = child else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    let duplicate = {
                        let mut comparisons = Vec::new();
                        let mut duplicate = false;
                        for previous in &parts {
                            generalizer.memo.work_meter.charge(1)?;
                            if generalizer.structural_equal(
                                F5cCompareTask::Positive(previous, &value),
                                &mut comparisons,
                            )? {
                                duplicate = true;
                                break;
                            }
                        }
                        generalizer
                            .memo
                            .walker_resources
                            .release(F5cWalkerLaneKind::Comparison);
                        duplicate
                    };
                    if !duplicate {
                        cacheable &= child_cacheable;
                        generalizer
                            .memo
                            .reserve_walker(&mut parts, F5cWalkerLaneKind::PositiveParts)?;
                        parts.push(value);
                    }
                }
                let nonempty = !parts.is_empty();
                let value = F5cWalkValue::Positive(
                    match parts.len() {
                        0 if root => F5cPositive::Bottom,
                        0 => F5cPositive::Variable(row),
                        1 => parts.pop().expect("one lower member"),
                        _ => F5cPositive::Union(parts),
                    },
                    cacheable && (nonempty || root),
                );
                generalizer
                    .memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::PositiveParts);
                value
            }
            Polarity::Negative => {
                let mut parts = Vec::new();
                let mut cacheable = true;
                for child in values.drain(values_start..) {
                    let F5cWalkValue::Negative(value, child_cacheable) = child else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    let duplicate = {
                        let mut comparisons = Vec::new();
                        let mut duplicate = false;
                        for previous in &parts {
                            generalizer.memo.work_meter.charge(1)?;
                            if generalizer.structural_equal(
                                F5cCompareTask::Negative(previous, &value),
                                &mut comparisons,
                            )? {
                                duplicate = true;
                                break;
                            }
                        }
                        generalizer
                            .memo
                            .walker_resources
                            .release(F5cWalkerLaneKind::Comparison);
                        duplicate
                    };
                    if !duplicate {
                        cacheable &= child_cacheable;
                        generalizer
                            .memo
                            .reserve_walker(&mut parts, F5cWalkerLaneKind::NegativeParts)?;
                        parts.push(value);
                    }
                }
                let nonempty = !parts.is_empty();
                let value = F5cWalkValue::Negative(
                    match parts.len() {
                        0 => F5cNegative::Variable(row),
                        1 => parts.pop().expect("one upper member"),
                        _ => F5cNegative::Intersection(parts),
                    },
                    cacheable && nonempty,
                );
                generalizer
                    .memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::NegativeParts);
                value
            }
        };
        Ok(value)
    }
    fn function(
        &mut self,
        _generalizer: &mut F5cGeneralizer<'_>,
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
                    argument: Box::new(argument),
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result: Box::new(result),
                },
                argument_cacheable && result_cacheable,
            ),
            (
                Polarity::Negative,
                F5cWalkValue::Positive(argument, argument_cacheable),
                F5cWalkValue::Negative(result, result_cacheable),
            ) => F5cWalkValue::Negative(
                F5cNegative::Function {
                    argument: Box::new(argument),
                    argument_effect: F5cPositiveEffect::Bottom,
                    result_effect: F5cNegativeEffect::Empty,
                    result: Box::new(result),
                },
                argument_cacheable && result_cacheable,
            ),
            _ => return Err(SolveAvailabilityError::IdentityExhausted),
        })
    }
    fn promote(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        value: &Self::Value,
        row: u32,
        polarity: Polarity,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        match value {
            F5cWalkValue::Positive(value, _) => {
                generalizer.memo.positive_node(value, Some((row, polarity)))
            }
            F5cWalkValue::Negative(value, _) => {
                generalizer.memo.negative_node(value, Some((row, polarity)))
            }
        }
    }
}

impl<'a> F5cGeneralizer<'a> {
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
            self.memo
                .commit_scratch_reserve(requested, growth, old, self.frames.capacity())?;
            reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        }
        let (requested, growth) = self.memo.prepare_scratch_reserve(1)?;
        let old = self.active.capacity();
        let reservation = self.active.try_reserve(1);
        self.memo.generalizer_scratch_capacities[1] = self.active.capacity();
        self.memo
            .commit_scratch_reserve(requested, growth, old, self.active.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;

        let (requested, growth) = self.memo.prepare_scratch_reserve(1)?;
        let old = self.active_set.capacity();
        let reservation = self.active_set.try_reserve(1);
        self.memo.generalizer_scratch_capacities[2] = self.active_set.capacity();
        self.memo
            .commit_scratch_reserve(requested, growth, old, self.active_set.capacity())?;
        reservation.map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn new(session: &'a InferenceSession) -> Self {
        Self::with_memo(session, F5cComponentExpansionMemo::default(), 0)
    }

    pub(super) fn with_memo(
        session: &'a InferenceSession,
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
            session,
            memo,
            #[cfg(test)]
            flat_sink: F5cFlatWalkSink::default(),
            #[cfg(test)]
            raw_forest_live: false,
            frozen_bound_epoch,
            frames: Vec::new(),
            shared_summary_hits: 0,
            uncacheable_states: 0,
            uncacheable_seen: HashSet::new(),
            fatal_taint: false,
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
            order_seen: HashSet::new(),
            reentries: Vec::new(),
            invalid_effects: false,
        }
    }

    fn mark(&mut self, ordinal: u32, _polarity: Polarity) -> Result<(), SolveAvailabilityError> {
        Self::register_order(
            &self.memo.work_meter,
            &mut self.order_seen,
            &mut self.order,
            ordinal,
        )?;
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

    fn record_uncacheable(&mut self, row: u32, polarity: Polarity) {
        if self.uncacheable_seen.insert(F5cExpansionKey {
            row,
            polarity,
            frozen_bound_epoch: self.frozen_bound_epoch,
        }) {
            self.uncacheable_states += 1;
        }
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
        if self.provisional_recursive_rows.insert(ordinal) {
            self.memo.invalidate_row(ordinal)?;
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
        let path = self.path[path_start..].to_vec();
        let mut guarded = false;
        for hop in &path {
            self.memo.work_meter.charge(1)?;
            if matches!(hop, F5cTraceHop::Function(_)) {
                guarded = true;
                break;
            }
        }
        if guarded {
            self.reentries.push(F5cGuardedTrace {
                owner: ordinal,
                entry_polarity,
                reentry_polarity,
                path,
            });
        }
        Ok(())
    }

    pub(super) fn structural_equal<'b>(
        &mut self,
        first: F5cCompareTask<'b>,
        stack: &mut Vec<F5cCompareTask<'b>>,
    ) -> Result<bool, SolveAvailabilityError> {
        stack.clear();
        self.memo.work_meter.charge(1)?;
        self.memo
            .reserve_walker(stack, F5cWalkerLaneKind::Comparison)?;
        stack.push(first);
        while !stack.is_empty() {
            self.memo.work_meter.charge(1)?;
            let pair = stack.pop().expect("nonempty comparison stack");
            match pair {
                F5cCompareTask::Positive(left, right) => match (left, right) {
                    (F5cPositive::Bottom, F5cPositive::Bottom)
                    | (F5cPositive::Int, F5cPositive::Int) => {}
                    (F5cPositive::Variable(a), F5cPositive::Variable(b))
                    | (F5cPositive::Quantified(a), F5cPositive::Quantified(b))
                    | (F5cPositive::Recursive(a), F5cPositive::Recursive(b))
                        if a == b => {}
                    (F5cPositive::Shared(a), F5cPositive::Shared(b)) if a == b => {}
                    (F5cPositive::Union(a), F5cPositive::Union(b)) if a.len() == b.len() => {
                        for (left, right) in a.iter().zip(b).rev() {
                            self.memo.work_meter.charge(1)?;
                            self.memo.work_meter.charge(1)?;
                            self.memo
                                .reserve_walker(stack, F5cWalkerLaneKind::Comparison)?;
                            stack.push(F5cCompareTask::Positive(left, right));
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
                        self.memo
                            .reserve_walker(stack, F5cWalkerLaneKind::Comparison)?;
                        stack.push(F5cCompareTask::Positive(ar, b));
                        self.memo.work_meter.charge(1)?;
                        self.memo
                            .reserve_walker(stack, F5cWalkerLaneKind::Comparison)?;
                        stack.push(F5cCompareTask::Negative(aa, ba));
                    }
                    _ => {
                        stack.clear();
                        return Ok(false);
                    }
                },
                F5cCompareTask::Negative(left, right) => match (left, right) {
                    (F5cNegative::Top, F5cNegative::Top)
                    | (F5cNegative::Bottom, F5cNegative::Bottom)
                    | (F5cNegative::Int, F5cNegative::Int) => {}
                    (F5cNegative::Variable(a), F5cNegative::Variable(b))
                    | (F5cNegative::Quantified(a), F5cNegative::Quantified(b))
                    | (F5cNegative::Recursive(a), F5cNegative::Recursive(b))
                        if a == b => {}
                    (F5cNegative::Shared(a), F5cNegative::Shared(b)) if a == b => {}
                    (F5cNegative::Intersection(a), F5cNegative::Intersection(b))
                        if a.len() == b.len() =>
                    {
                        for (left, right) in a.iter().zip(b).rev() {
                            self.memo.work_meter.charge(1)?;
                            self.memo.work_meter.charge(1)?;
                            self.memo
                                .reserve_walker(stack, F5cWalkerLaneKind::Comparison)?;
                            stack.push(F5cCompareTask::Negative(left, right));
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
                        self.memo
                            .reserve_walker(stack, F5cWalkerLaneKind::Comparison)?;
                        stack.push(F5cCompareTask::Negative(ar, b));
                        self.memo.work_meter.charge(1)?;
                        self.memo
                            .reserve_walker(stack, F5cWalkerLaneKind::Comparison)?;
                        stack.push(F5cCompareTask::Positive(aa, ba));
                    }
                    _ => {
                        stack.clear();
                        return Ok(false);
                    }
                },
            }
        }
        Ok(true)
    }

    fn walk_with<S: F5cWalkSink>(
        &mut self,
        first: F5cWalkTask,
        sink: &mut S,
    ) -> Result<S::Value, SolveAvailabilityError> {
        let active_checkpoint = self.active.len();
        let frame_checkpoint = self.frames.len();
        let path_checkpoint = self.path.len();
        let mut tasks = Vec::new();
        let mut values = Vec::<S::Value>::new();
        let mut direct_edges = Vec::<(usize, u32)>::new();
        let mut direct_targets = HashSet::<u32>::new();
        macro_rules! push_task {
            ($value:expr) => {{
                let value = $value;
                self.memo.work_meter.charge(1)?;
                self.memo
                    .reserve_walker(&mut tasks, F5cWalkerLaneKind::Tasks)?;
                tasks.push(value);
            }};
        }
        macro_rules! push_value {
            ($value:expr) => {{
                self.memo.work_meter.charge(1)?; // emitted walk value
                let value = $value;
                self.memo
                    .reserve_walker(&mut values, F5cWalkerLaneKind::Values)?;
                values.push(value);
            }};
        }
        macro_rules! push_direct {
            ($value:expr) => {{
                let value = $value;
                self.memo.work_meter.charge(1)?; // stored direct edge
                self.memo
                    .reserve_walker(&mut direct_edges, F5cWalkerLaneKind::DirectEdges)?;
                direct_edges.push(value);
            }};
        }
        let result = (|| {
            push_task!(first);
            while !tasks.is_empty() {
                self.memo.work_meter.charge(1)?;
                let task = tasks.pop().expect("nonempty generalization tasks");
                match task {
                    F5cWalkTask::EnterPath(hop) => self.path.push(hop),
                    F5cWalkTask::LeavePath => {
                        self.path.pop();
                    }
                    F5cWalkTask::EnterRow {
                        row,
                        polarity,
                        root,
                    } => {
                        if self.active(row, polarity) {
                            self.taint_active_states()?;
                            self.record_reentry(row, polarity)?;
                            self.memo.observe_walker()?;
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
                            self.memo.observe_walker()?;
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
                        }
                        self.mark(row, polarity)?;
                        self.memo.enter_active(row)?;
                        self.active.push((row, polarity, self.path.len()));
                        self.active_set.insert((row, polarity));
                        self.memo.observe_walker()?;
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
                        if !root {
                            direct_targets.clear();
                            let direct = match polarity {
                                Polarity::Positive => &bounds.direct_lower_rows,
                                Polarity::Negative => &bounds.direct_upper_rows,
                            };
                            for (slot, target) in direct.iter().copied().enumerate() {
                                self.memo.work_meter.charge(1)?;
                                if !direct_targets.contains(&target) {
                                    self.memo.reserve_walker_target(&mut direct_targets)?;
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
                        let exact = match polarity {
                            Polarity::Positive => &bounds.exact_non_variable_lowers,
                            Polarity::Negative => &bounds.exact_non_variable_uppers,
                        };
                        for (slot, endpoint) in exact.iter().copied().enumerate().rev() {
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
                        self.memo.leave_active(row)?;
                        self.active.pop();
                        self.active_set.remove(&(row, polarity));
                        self.memo.observe_walker()?;
                        let value =
                            sink.finish_row(self, &mut values, values_start, row, polarity, root)?;
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
                            self.record_uncacheable(row, polarity);
                            self.taint_active_states()?;
                            push_value!(value);
                        } else {
                            let id = sink.promote(self, &value, row, polarity)?;
                            let key = F5cExpansionKey {
                                row,
                                polarity,
                                frozen_bound_epoch: self.frozen_bound_epoch,
                            };
                            self.memo.admit(key, id)?;
                            // admit records its stable edge before any fallible observation.
                            self.memo.observe_walker()?;
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
                            (Polarity::Negative, TermView::Leaf(Leaf::IntNegative)) => {
                                push_value!(sink.int(self, Polarity::Negative)?)
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
                                let valid = match polarity {
                                    Polarity::Positive => {
                                        matches!(
                                            self.session.store.term_view(argument_effect),
                                            Ok(TermView::Leaf(Leaf::EmptyEffectNegative))
                                        ) && matches!(
                                            self.session.store.term_view(result_effect),
                                            Ok(TermView::Leaf(Leaf::EffectBottomPositive))
                                        )
                                    }
                                    Polarity::Negative => {
                                        matches!(
                                            self.session.store.term_view(argument_effect),
                                            Ok(TermView::Leaf(Leaf::EffectBottomPositive))
                                        ) && matches!(
                                            self.session.store.term_view(result_effect),
                                            Ok(TermView::Leaf(Leaf::EmptyEffectNegative))
                                        )
                                    }
                                };
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
                        let result = values
                            .pop()
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let argument = values
                            .pop()
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        push_value!(sink.function(self, polarity, argument, result)?);
                    }
                }
            }
            if values.len() != 1 {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            values
                .pop()
                .ok_or(SolveAvailabilityError::IdentityExhausted)
        })();
        let result = match result {
            Ok(value) => self.memo.observe_walker().map(|()| value),
            Err(error) => {
                let _ = self.memo.observe_walker();
                Err(error)
            }
        };
        if result.is_err() {
            while self.active.len() > active_checkpoint {
                if let Some((row, polarity, _)) = self.active.pop() {
                    self.active_set.remove(&(row, polarity));
                }
            }
            if !self.in_component {
                self.memo.reset_active_scratch();
            }
            self.frames.truncate(frame_checkpoint);
            self.path.truncate(path_checkpoint);
            let _ = self.taint_active_states();
        }
        self.memo.walker_resources.release(F5cWalkerLaneKind::Tasks);
        self.memo
            .walker_resources
            .release(F5cWalkerLaneKind::Values);
        self.memo
            .walker_resources
            .release(F5cWalkerLaneKind::DirectEdges);
        self.memo
            .walker_resources
            .release(F5cWalkerLaneKind::DirectTargets);
        self.memo
            .walker_resources
            .release(F5cWalkerLaneKind::Comparison);
        self.memo
            .walker_resources
            .release(F5cWalkerLaneKind::PositiveParts);
        self.memo
            .walker_resources
            .release(F5cWalkerLaneKind::NegativeParts);
        result
    }

    pub(super) fn walk(
        &mut self,
        first: F5cWalkTask,
    ) -> Result<F5cWalkValue, SolveAvailabilityError> {
        self.walk_with(first, &mut F5cBoxedWalkSink)
    }

    #[cfg(test)]
    pub(super) fn walk_flat(
        &mut self,
        first: F5cWalkTask,
    ) -> Result<FlatWalkValue, SolveAvailabilityError> {
        if self.raw_forest_live {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        // The source and memo have the same owner. Keep the sink attached even
        // when a walk fails so retained capacities remain accounted for.
        let mut sink = std::mem::take(&mut self.flat_sink);
        let result = self.walk_flat_with_sink(first, &mut sink);
        self.flat_sink = sink;
        result
    }

    /// Test-only raw producer forest. Binder selection and Q/R rewriting are later gates.
    #[cfg(test)]
    pub(super) fn build_raw_forest(
        &mut self,
        root: u32,
    ) -> Result<F5cRawForest, SolveAvailabilityError> {
        if self.raw_forest_live {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        use f5c_draft::{NegativeId, NodeRef, PositiveId};
        let mut raw_owner_order = Vec::new();
        let mut raw_bounds = HashMap::<u32, (PositiveId, NegativeId)>::new();
        let mut seen = HashSet::<u32>::new();
        let mut roots = Vec::<FlatWalkValue>::new();
        let mut outputs = Vec::<NodeRef>::new();
        let mut callback_trace = Vec::<(u32, Polarity)>::new();
        let mut draft = f5c_draft::FlatDraft::default();
        let result = (|| {
            let predicate = self.walk_flat(F5cWalkTask::EnterRow {
                row: root,
                polarity: Polarity::Positive,
                root: true,
            })?;
            let bytes = self.memo.retained_bytes()?;
            self.memo.walker_resources.reserve(
                &mut roots,
                F5cWalkerLaneKind::RawRoots,
                1,
                bytes,
            )?;
            roots.push(predicate);
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
                self.memo
                    .walker_resources
                    .reserve_raw_set(&mut seen, bytes)?;
                seen.insert(owner);
                let bounds = self
                    .session
                    .bounds
                    .get(owner as usize)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                let copied = bounds
                    .direct_lower_rows
                    .len()
                    .checked_add(bounds.direct_upper_rows.len())
                    .and_then(|n| n.checked_add(bounds.exact_non_variable_lowers.len()))
                    .and_then(|n| n.checked_add(bounds.exact_non_variable_uppers.len()))
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                self.memo.work_meter.charge(copied)?;
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
                let bytes = self.memo.retained_bytes()?;
                self.memo.walker_resources.reserve(
                    &mut raw_owner_order,
                    F5cWalkerLaneKind::RawOwnerOrder,
                    1,
                    bytes,
                )?;
                self.memo.walker_resources.reserve(
                    &mut roots,
                    F5cWalkerLaneKind::RawRoots,
                    2,
                    bytes,
                )?;
                self.memo
                    .walker_resources
                    .reserve_raw_map(&mut raw_bounds, bytes)?;
                let lower_index = roots.len();
                roots.push(lower);
                roots.push(upper);
                raw_owner_order.push(owner);
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
            }
            if self.invalid_effects {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            let memo = &mut self.memo;
            let sink = &self.flat_sink;
            let bytes = memo.retained_bytes()?;
            memo.walker_resources.reserve(
                &mut callback_trace,
                F5cWalkerLaneKind::RawCallbackTrace,
                0,
                bytes,
            )?;
            memo.walker_resources.observe_memo(bytes)?;
            sink.materialize_roots(
                memo,
                &mut draft,
                &roots,
                &mut outputs,
                |resources, memo_bytes, row, polarity| {
                    resources.reserve(
                        &mut callback_trace,
                        F5cWalkerLaneKind::RawCallbackTrace,
                        1,
                        memo_bytes,
                    )?;
                    callback_trace.push((row, polarity));
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
            }
            Ok(())
        })();
        drop(outputs);
        self.flat_sink.release_materialized_roots(&mut self.memo);
        drop(roots);
        self.memo
            .walker_resources
            .release(F5cWalkerLaneKind::RawRoots);
        drop(seen);
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
            drop(raw_bounds);
            drop(callback_trace);
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
        self.memo
            .finish_root_transaction(self.root_undo_checkpoint, true)?;
        drop(std::mem::take(&mut self.flat_sink.arena));
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
            raw_bounds,
            callback_trace,
        })
    }

    #[cfg(test)]
    pub(super) fn release_raw_forest(&mut self, forest: F5cRawForest) {
        assert!(
            self.raw_forest_live,
            "one live raw forest owns the candidate output lanes"
        );
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
        self.node_checkpoint = self.memo.nodes.len();
        self.child_checkpoint = self.memo.children.len();
        self.reverse_checkpoint = self.memo.reverse_parents.len();
        self.incidence_checkpoint = self.memo.incidences.len();
        self.root_undo_checkpoint = self.memo.root_undo.len();
        self.memo.reset_active_scratch();
        self.frames = Vec::new();
        self.active = Vec::new();
        self.active_set = HashSet::new();
        self.path = Vec::new();
        self.order = Vec::new();
        self.order_seen = HashSet::new();
        self.reentries = Vec::new();
        self.provisional_recursive_rows = HashSet::new();
        self.uncacheable_seen = HashSet::new();
        self.memo.generalizer_scratch_capacities = [0; 4];
        self.shared_summary_hits = 0;
        self.uncacheable_states = 0;
        self.fatal_taint = false;
        self.invalid_effects = false;
        self.in_component = false;
        self.raw_forest_live = false;
    }

    #[cfg(test)]
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
            sink.component_checkpoint = None;
            sink.counter_checkpoint = None;
            (self.shared_summary_hits, self.uncacheable_states) = counter_checkpoint;
            self.abort_flat_component()?;
        }
        result
    }

    #[cfg(test)]
    fn abort_flat_component(&mut self) -> Result<(), SolveAvailabilityError> {
        if let Some(checkpoint) = self.flat_sink.component_checkpoint.take() {
            self.flat_sink.arena.rollback(checkpoint);
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
        self.path.clear();
        self.order.clear();
        self.order_seen.clear();
        self.reentries.clear();
        self.provisional_recursive_rows.clear();
        self.uncacheable_seen.clear();
        self.fatal_taint = false;
        self.invalid_effects = false;
        let nodes = self.memo.rollback_nodes(
            self.node_checkpoint,
            self.child_checkpoint,
            self.reverse_checkpoint,
            self.incidence_checkpoint,
        );
        roots?;
        nodes
    }

    pub(super) fn positive_row(
        &mut self,
        ordinal: u32,
        root: bool,
    ) -> Result<F5cPositive, SolveAvailabilityError> {
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
    ) -> Result<F5cNegative, SolveAvailabilityError> {
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
    ) -> Result<F5cPositive, SolveAvailabilityError> {
        match self.walk(F5cWalkTask::PositiveEndpoint(endpoint))? {
            F5cWalkValue::Positive(value, _) => Ok(value),
            F5cWalkValue::Negative(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    #[cfg(test)]
    pub(super) fn negative_endpoint(
        &mut self,
        endpoint: ValueEndpointKey,
    ) -> Result<F5cNegative, SolveAvailabilityError> {
        match self.walk(F5cWalkTask::NegativeEndpoint(endpoint))? {
            F5cWalkValue::Negative(value, _) => Ok(value),
            F5cWalkValue::Positive(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    #[cfg(test)]
    pub(super) fn positive_term(
        &mut self,
        term: Term,
    ) -> Result<F5cPositive, SolveAvailabilityError> {
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
    ) -> Result<F5cNegative, SolveAvailabilityError> {
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

    fn guarded_trace_path_survives_metered(
        &self,
        trace: &F5cGuardedTrace,
        protected: &HashSet<u32>,
        positive_only: &HashSet<u32>,
        negative_only: &HashSet<u32>,
    ) -> Result<bool, SolveAvailabilityError> {
        for hop in &trace.path {
            self.memo.work_meter.charge(1)?; // examined trace hop
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
        let mut memo = F5cComponentExpansionMemo::default();
        let Ok(lower) =
            f5c_replay::replay_positive(&mut memo, lower, protected, positive_only, negative_only)
        else {
            return false;
        };
        let Ok(upper) =
            f5c_replay::replay_negative(&mut memo, upper, protected, positive_only, negative_only)
        else {
            return false;
        };
        f5c_tree_analysis::Walker::new(&mut memo)
            .guarded_bound_survives(owner, &lower, &upper)
            .unwrap_or(false)
    }

    #[cfg(test)]
    pub(super) fn normalize_positive(
        value: F5cPositive,
    ) -> Result<F5cPositive, SolveAvailabilityError> {
        f5c_normalization::normalize_positive(value)
    }

    #[cfg(test)]
    pub(super) fn normalize_negative(
        value: F5cNegative,
    ) -> Result<F5cNegative, SolveAvailabilityError> {
        f5c_normalization::normalize_negative(value)
    }

    pub(super) fn non_generic_closure(&mut self) -> Result<HashSet<u32>, SolveAvailabilityError> {
        let mut adjacency = vec![HashSet::new(); self.session.bounds.len()];
        let mut walker = f5c_tree_analysis::Walker::new(&mut self.memo);
        for (owner, bounds) in self.session.bounds.iter().enumerate() {
            walker.memo.work_meter.charge(1)?; // scanned bounds owner
            let owner = owner as u32;
            let direct_count = bounds
                .direct_lower_rows
                .len()
                .checked_add(bounds.direct_upper_rows.len())
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            walker.memo.work_meter.charge(direct_count)?; // copied direct adjacency endpoints
            let mut connected = bounds
                .direct_lower_rows
                .iter()
                .chain(&bounds.direct_upper_rows)
                .copied()
                .collect::<HashSet<_>>();
            for endpoint in bounds
                .exact_non_variable_lowers
                .iter()
                .chain(&bounds.exact_non_variable_uppers)
            {
                walker.memo.work_meter.charge(1)?; // examined exact endpoint
                match endpoint {
                    ValueEndpointKey::ValueRow(row) => {
                        connected.insert(*row);
                    }
                    ValueEndpointKey::PositiveFunction(term)
                    | ValueEndpointKey::NegativeFunction(term) => {
                        walker.term_rows(&self.session.store, *term, &mut connected)?;
                    }
                    _ => {}
                }
            }
            for target in connected {
                walker.memo.work_meter.charge(1)?; // adjacency incidence
                if let Some(neighbors) = adjacency.get_mut(owner as usize) {
                    neighbors.insert(target);
                }
                if let Some(neighbors) = adjacency.get_mut(target as usize) {
                    neighbors.insert(owner);
                }
            }
        }
        let mut closure = HashSet::new();
        for (ordinal, metadata) in self.session.value_metadata.iter().enumerate() {
            walker.memo.work_meter.charge(1)?; // metadata owner
            if metadata.non_generic {
                walker.memo.work_meter.charge(1)?; // closure entry
                closure.insert(ordinal as u32);
            }
        }
        walker.memo.work_meter.charge(closure.len())?; // copied frontier owners
        let mut frontier = closure.iter().copied().collect::<Vec<_>>();
        while !frontier.is_empty() {
            walker.memo.work_meter.charge(1)?; // closure frontier pop
            let owner = frontier.pop().expect("nonempty closure frontier");
            let Some(neighbors) = adjacency.get(owner as usize) else {
                continue;
            };
            for neighbor in neighbors {
                walker.memo.work_meter.charge(1)?; // examined adjacency neighbor
                walker.memo.work_meter.charge(1)?; // possible closure and frontier entries
                if closure.insert(*neighbor) {
                    frontier.push(*neighbor);
                }
            }
        }
        Ok(closure)
    }

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

    #[cfg(test)]
    pub(super) fn build(
        &mut self,
        root: u32,
    ) -> Result<GeneralizationDraft, SolveAvailabilityError> {
        let mut draft = self.build_inner(root)?;
        f5c_normalization::normalize_component(std::slice::from_mut(&mut draft))?;
        Ok(draft)
    }

    pub(super) fn build_component(
        mut self,
        root: u32,
    ) -> (
        Result<GeneralizationDraft, SolveAvailabilityError>,
        F5cComponentExpansionMemo,
        usize,
        usize,
    ) {
        self.in_component = true;
        let mut result = self.build_inner(root);
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

    fn build_inner(&mut self, root: u32) -> Result<GeneralizationDraft, SolveAvailabilityError> {
        let predicate = self.positive_row(root, true)?;
        let mut raw_recursive_bounds = HashMap::new();
        let mut raw_owner_order = Vec::new();
        let mut next_owner = 0;
        let mut completed_owners = HashSet::new();
        while next_owner < self.reentries.len() {
            self.memo.work_meter.charge(1)?; // reentry owner
            let ordinal = self.reentries[next_owner].owner;
            next_owner += 1;
            self.memo.work_meter.charge(1)?; // completed-owner entry
            if !completed_owners.insert(ordinal) {
                continue;
            }
            let bounds = self
                .session
                .bounds
                .get(ordinal as usize)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let copied = bounds
                .direct_lower_rows
                .len()
                .checked_add(bounds.direct_upper_rows.len())
                .and_then(|count| count.checked_add(bounds.exact_non_variable_lowers.len()))
                .and_then(|count| count.checked_add(bounds.exact_non_variable_uppers.len()))
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            self.memo.work_meter.charge(copied)?;
            let bounds = bounds.clone();
            let expanded_lower = self.positive_row(ordinal, false)?;
            let expanded_upper = self.negative_row(ordinal)?;
            let lower = if bounds.exact_non_variable_lowers.is_empty()
                && bounds.direct_lower_rows.is_empty()
            {
                F5cPositive::Bottom
            } else {
                expanded_lower
            };
            let upper = if bounds.exact_non_variable_uppers.is_empty()
                && bounds.direct_upper_rows.is_empty()
            {
                F5cNegative::Top
            } else {
                expanded_upper
            };
            self.memo.work_meter.charge(1)?; // raw bound entry
            self.memo.work_meter.charge(1)?; // raw owner order entry
            let (requested, growth) = self.memo.prepare_scratch_reserve(1)?;
            let old = raw_owner_order.capacity();
            let reservation = raw_owner_order.try_reserve(1);
            self.memo.generalizer_scratch_capacities[3] = raw_owner_order.capacity();
            self.memo
                .commit_scratch_reserve(requested, growth, old, raw_owner_order.capacity())?;
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
        }
        if self.invalid_effects {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let predicate = self.materialize_positive(predicate)?;
        self.materialize_recursive_bounds(&raw_owner_order, &mut raw_recursive_bounds)?;
        let mut reentries_by_owner = HashMap::<u32, Vec<usize>>::new();
        for (index, trace) in self.reentries.iter().enumerate() {
            self.memo.work_meter.charge(1)?; // indexed trace record
            self.memo.work_meter.charge(1)?; // owner index entry
            reentries_by_owner
                .entry(trace.owner)
                .or_default()
                .push(index);
        }
        let non_generic = self.non_generic_closure()?;
        let eligible = |ordinal: u32| {
            self.session
                .value_levels
                .get(ordinal as usize)
                .is_some_and(|level| *level > 0)
                && !non_generic.contains(&ordinal)
        };
        let mut positive_incidences = HashSet::new();
        let mut negative_incidences = HashSet::new();
        {
            let mut walker = f5c_tree_analysis::Walker::new(&mut self.memo);
            walker.incidences_positive(
                &predicate,
                &mut positive_incidences,
                &mut negative_incidences,
            )?;
            for owner in &raw_owner_order {
                let (lower, upper) = raw_recursive_bounds
                    .get(owner)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                walker.memo.work_meter.charge(1)?; // raw bound owner
                walker.incidences_positive(
                    lower,
                    &mut positive_incidences,
                    &mut negative_incidences,
                )?;
                walker.incidences_negative(
                    upper,
                    &mut positive_incidences,
                    &mut negative_incidences,
                )?;
            }
        }
        let mut positive_only = HashSet::new();
        let mut negative_only = HashSet::new();
        for &owner in &self.order {
            self.memo.work_meter.charge(1)?; // metadata and eligibility owner
            if eligible(owner) {
                if positive_incidences.contains(&owner) && !negative_incidences.contains(&owner) {
                    self.memo.work_meter.charge(1)?; // positive-only entry
                    positive_only.insert(owner);
                }
                self.memo.work_meter.charge(1)?; // second eligibility/order scan
                if negative_incidences.contains(&owner) && !positive_incidences.contains(&owner) {
                    self.memo.work_meter.charge(1)?; // negative-only entry
                    negative_only.insert(owner);
                }
            } else {
                self.memo.work_meter.charge(1)?; // second eligibility/order scan
            }
        }
        let mut candidates = HashSet::new();
        for &owner in reentries_by_owner.keys() {
            self.memo.work_meter.charge(1)?; // candidate eligibility owner
            if eligible(owner) {
                self.memo.work_meter.charge(1)?; // candidate entry
                candidates.insert(owner);
            }
        }
        loop {
            self.memo.work_meter.charge(1)?; // fixed-point round
            self.memo.work_meter.charge(candidates.len())?; // copied candidate owners
            let previous = candidates.clone();
            let mut surviving_bounds = HashSet::new();
            for owner in &previous {
                self.memo.work_meter.charge(1)?; // examined bound owner
                let Some((lower, upper)) = raw_recursive_bounds.get(owner) else {
                    continue;
                };
                let lower = f5c_replay::replay_positive(
                    &mut self.memo,
                    lower,
                    &previous,
                    &positive_only,
                    &negative_only,
                )?;
                let upper = f5c_replay::replay_negative(
                    &mut self.memo,
                    upper,
                    &previous,
                    &positive_only,
                    &negative_only,
                )?;
                if f5c_tree_analysis::Walker::new(&mut self.memo)
                    .guarded_bound_survives(*owner, &lower, &upper)?
                {
                    surviving_bounds.insert(*owner);
                }
            }
            self.memo.work_meter.charge(candidates.capacity())?; // complete retain bucket scan
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
                    if let Err(error) = self.memo.work_meter.charge(1) {
                        retain_error = Some(error);
                        return true;
                    }
                    match self.guarded_trace_path_survives_metered(
                        &self.reentries[*index],
                        &previous,
                        &positive_only,
                        &negative_only,
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
            let replayed_predicate = f5c_replay::replay_positive(
                &mut self.memo,
                &predicate,
                &candidates,
                &positive_only,
                &negative_only,
            )?;
            let mut reachable = HashSet::new();
            {
                let mut walker = f5c_tree_analysis::Walker::new(&mut self.memo);
                walker.references_positive(&replayed_predicate, &candidates, &mut reachable)?;
                walker.memo.work_meter.charge(reachable.len())?; // copied frontier owners
                let mut frontier = reachable.iter().copied().collect::<Vec<_>>();
                while !frontier.is_empty() {
                    walker.memo.work_meter.charge(1)?; // reachability frontier pop
                    let owner = frontier.pop().expect("nonempty reachability frontier");
                    let Some((lower, upper)) = raw_recursive_bounds.get(&owner) else {
                        continue;
                    };
                    let mut referenced = HashSet::new();
                    walker.references_positive(lower, &candidates, &mut referenced)?;
                    walker.references_negative(upper, &candidates, &mut referenced)?;
                    for referenced_owner in referenced {
                        walker.memo.work_meter.charge(1)?; // examined reference
                        walker.memo.work_meter.charge(1)?; // possible frontier entry
                        if reachable.insert(referenced_owner) {
                            frontier.push(referenced_owner);
                        }
                    }
                }
            }
            self.memo.work_meter.charge(candidates.capacity())?; // complete retain bucket scan
            candidates.retain(|owner| reachable.contains(owner));
            if candidates == previous {
                break;
            }
        }
        let mut retained_bounds = HashMap::with_capacity(candidates.len());
        for owner in &candidates {
            self.memo.work_meter.charge(1)?; // post-convergence bound owner
            let (lower, upper) = raw_recursive_bounds
                .get(owner)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let lower = f5c_replay::replay_positive(
                &mut self.memo,
                lower,
                &candidates,
                &positive_only,
                &negative_only,
            )?;
            let upper = f5c_replay::replay_negative(
                &mut self.memo,
                upper,
                &candidates,
                &positive_only,
                &negative_only,
            )?;
            retained_bounds.insert(*owner, (lower, upper));
        }
        let mut surviving_bound_owners = HashSet::new();
        {
            let mut walker = f5c_tree_analysis::Walker::new(&mut self.memo);
            for (owner, (lower, upper)) in &retained_bounds {
                walker.memo.work_meter.charge(1)?; // revisited retained bound
                if walker.guarded_bound_survives(*owner, lower, upper)? {
                    surviving_bound_owners.insert(*owner);
                }
            }
        }
        let mut surviving_traces = HashSet::new();
        for (index, trace) in self.reentries.iter().enumerate() {
            self.memo.work_meter.charge(1)?; // post-convergence trace record
            if candidates.contains(&trace.owner)
                && surviving_bound_owners.contains(&trace.owner)
                && self.guarded_trace_path_survives_metered(
                    trace,
                    &candidates,
                    &positive_only,
                    &negative_only,
                )?
            {
                surviving_traces.insert(index);
            }
        }
        let mut recursive_owners = Vec::new();
        let mut recursive_set = HashSet::new();
        for (index, trace) in self.reentries.iter().enumerate() {
            self.memo.work_meter.charge(1)?; // recursive-owner ordering trace
            if surviving_traces.contains(&index) && recursive_set.insert(trace.owner) {
                recursive_owners.push(trace.owner);
            }
        }
        let retained_predicate = f5c_replay::replay_positive(
            &mut self.memo,
            &predicate,
            &recursive_set,
            &positive_only,
            &negative_only,
        )?;
        let first_occurrences = Self::retained_occurrences(
            &retained_predicate,
            &recursive_owners,
            &retained_bounds,
            &mut self.memo,
        )?;
        let mut q = HashMap::new();
        for ordinal in first_occurrences {
            self.memo.work_meter.charge(1)?; // Q first occurrence
            if !recursive_set.contains(&ordinal)
                && positive_incidences.contains(&ordinal)
                && negative_incidences.contains(&ordinal)
                && eligible(ordinal)
            {
                let next = u32::try_from(q.len())
                    .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                self.memo.work_meter.charge(1)?; // Q entry
                q.insert(ordinal, next);
            }
        }
        let q_count =
            u32::try_from(q.len()).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let mut r = HashMap::new();
        for (index, ordinal) in recursive_owners.iter().enumerate() {
            self.memo.work_meter.charge(1)?; // R owner
            let offset =
                u32::try_from(index).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            let binder = q_count
                .checked_add(offset)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            self.memo.work_meter.charge(1)?; // R entry
            r.insert(*ordinal, binder);
        }
        Self::reject_unclassified_rows(
            &self.memo.work_meter,
            &self.order,
            &recursive_set,
            &q,
            eligible,
        )?;
        let mut positive_eliminated = HashSet::new();
        let mut negative_eliminated = HashSet::new();
        for ordinal in self.order.iter().copied() {
            self.memo.work_meter.charge(1)?; // positive eliminated-set owner
            if !recursive_set.contains(&ordinal)
                && !q.contains_key(&ordinal)
                && positive_only.contains(&ordinal)
            {
                self.memo.work_meter.charge(1)?;
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
                negative_eliminated.insert(ordinal);
            }
        }
        let predicate = f5c_binder_substitution::substitute_positive(
            &mut self.memo,
            predicate,
            &q,
            &r,
            &positive_eliminated,
            &negative_eliminated,
        )?;
        let mut recursive_bounds = Vec::with_capacity(recursive_owners.len());
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
                &mut self.memo,
                raw_lower,
                &q,
                &r,
                &positive_eliminated,
                &negative_eliminated,
            )?;
            let upper = f5c_binder_substitution::substitute_negative(
                &mut self.memo,
                raw_upper,
                &q,
                &r,
                &positive_eliminated,
                &negative_eliminated,
            )?;
            self.memo.work_meter.charge(1)?; // result bound
            recursive_bounds.push(F5cRecursiveBound {
                ordinal: binder,
                lower,
                upper,
            });
        }
        Ok(GeneralizationDraft {
            quantifier_count: q_count,
            recursive_bounds,
            predicate,
        })
    }
}
