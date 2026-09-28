use super::SolveAvailabilityError;
use super::f5c_draft_heap::{DraftHeapMeter, PhysicalOwnerKind, TrackedVec};
#[cfg(all(test, feature = "f5c_resource_probe"))]
use super::f5c_draft_heap::FlatDraftOwner;
use yu_types::{
    IndexedChildSpan, IndexedNegativeNode, IndexedNegativeNodeId, IndexedPositiveNode,
    IndexedPositiveNodeId, IndexedRecursiveBound, IndexedSchemeRef,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PositiveId(pub(super) u32);
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct NegativeId(pub(super) u32);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ChildSpan {
    pub(super) start: u32,
    pub(super) len: u32,
}

#[cfg(all(test, feature = "f5c_resource_probe"))]
mod owner_transfer_tests {
    use super::*;
    use super::super::f5c_draft_heap::{close_f5c_resource_events, open_f5c_resource_events};

    fn events(path: &std::path::Path) -> Vec<[u64; 8]> {
        let bytes = std::fs::read(path).unwrap();
        bytes[8..].chunks_exact(64).map(|event| std::array::from_fn(|i| {
            u64::from_le_bytes(event[i * 8..(i + 1) * 8].try_into().unwrap())
        })).collect()
    }

    #[test]
    fn flat_draft_move_failed_preflight_and_drop_keep_one_identity() {
        let path = std::env::temp_dir().join(format!("f5c-draft-owner-{}-{:?}.bin",
            std::process::id(), std::thread::current().id()));
        open_f5c_resource_events(&path).unwrap();
        let meter = DraftHeapMeter::default();
        meter.set_event_component(17);
        let mut draft = FlatDraft::default();
        draft.attach_owners(&meter, [1, 2, 3, 4, 5, 6]);
        draft.positive(PositiveNode::Int).unwrap();
        let mut moved = draft;
        meter.begin_component().unwrap();
        let capacities = moved.capacities();
        let sizes = [std::mem::size_of::<PositiveNode>(),
            std::mem::size_of::<NegativeNode>(), std::mem::size_of::<PositiveId>(),
            std::mem::size_of::<NegativeId>(), std::mem::size_of::<RecursiveBound>(),
            std::mem::size_of::<NodeRef>()];
        let bytes = std::array::from_fn(|i| capacities[i] * sizes[i]);
        assert!(meter.claim_existing_batch_with_owners(bytes, usize::MAX,
            moved.owners.as_mut().unwrap(), [1, 0, 0, 0, 0, 1], capacities, sizes).is_err());
        let failed_reserve = moved.positive_nodes.try_reserve(usize::MAX);
        moved.observe_owner(0, usize::MAX);
        assert!(failed_reserve.is_err());
        moved.positive(PositiveNode::Bottom).unwrap();
        drop(moved);
        close_f5c_resource_events().unwrap();
        let rows = events(&path);
        std::fs::remove_file(path).unwrap();
        assert_eq!(rows.iter().filter(|row| row[2] == 1).count(), 6);
        assert_eq!(rows.iter().filter(|row| row[2] == 4).count(), 0);
        assert_eq!(rows.iter().filter(|row| row[2] == 5).count(), 6);
        let grown: Vec<_> = rows.iter().filter(|row| row[2] == 3).collect();
        assert!(!grown.is_empty());
        assert!(grown.iter().all(|row| row[0] == 17));
        assert!(rows.iter().any(|row| row[2] == 2 && row[4] == 2));
        assert!(!rows.iter().any(|row| row[4] == usize::MAX as u64));
    }

    #[test]
    fn flat_draft_transfer_reuses_ids_and_failure_drop_releases_once() {
        let path = std::env::temp_dir().join(format!("f5c-draft-transfer-{}-{:?}.bin",
            std::process::id(), std::thread::current().id()));
        open_f5c_resource_events(&path).unwrap();
        let meter = DraftHeapMeter::default();
        meter.set_event_component(23);
        let mut draft = FlatDraft::default();
        draft.attach_owners(&meter, [1, 2, 3, 4, 5, 6]);
        draft.positive(PositiveNode::Int).unwrap();
        meter.begin_component().unwrap();
        let capacities = draft.capacities();
        let sizes = [std::mem::size_of::<PositiveNode>(),
            std::mem::size_of::<NegativeNode>(), std::mem::size_of::<PositiveId>(),
            std::mem::size_of::<NegativeId>(), std::mem::size_of::<RecursiveBound>(),
            std::mem::size_of::<NodeRef>()];
        let bytes = std::array::from_fn(|i| capacities[i] * sizes[i]);
        let allocations = meter.claim_existing_batch_with_owners(bytes, 0,
            draft.owners.as_mut().unwrap(), [1, 0, 0, 0, 0, 1], capacities, sizes).unwrap();
        drop(draft);
        drop(allocations);
        close_f5c_resource_events().unwrap();
        let rows = events(&path);
        std::fs::remove_file(path).unwrap();
        let created: Vec<_> = rows.iter().filter(|row| row[2] == 1).map(|row| row[1]).collect();
        let transferred: Vec<_> = rows.iter().filter(|row| row[2] == 4).map(|row| row[1]).collect();
        let released: Vec<_> = rows.iter().filter(|row| row[2] == 5).map(|row| row[1]).collect();
        assert_eq!(created, transferred);
        assert_eq!(created, released);
        assert_eq!(rows.iter().filter(|row| row[2] == 4 && row[4] == 1).count(), 2);
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PositiveNode {
    Bottom,
    Int,
    Variable(u32),
    Quantified(u32),
    Recursive(u32),
    Union(ChildSpan),
    Function {
        argument: NegativeId,
        result: PositiveId,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NegativeNode {
    Top,
    Bottom,
    Int,
    Variable(u32),
    Quantified(u32),
    Recursive(u32),
    Intersection(ChildSpan),
    Function {
        argument: PositiveId,
        result: NegativeId,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct RecursiveBound {
    pub(super) ordinal: u32,
    pub(super) lower: PositiveId,
    pub(super) upper: NegativeId,
}

#[derive(Default)]
pub(super) struct FlatDraft {
    pub(super) structural_incidences: usize,
    pub(super) quantifier_count: u32,
    pub(super) predicate: Option<PositiveId>,
    pub(super) positive_nodes: Vec<PositiveNode>,
    pub(super) negative_nodes: Vec<NegativeNode>,
    pub(super) positive_children: Vec<PositiveId>,
    pub(super) negative_children: Vec<NegativeId>,
    pub(super) recursive_bounds: Vec<RecursiveBound>,
    pub(super) insertion_order: Vec<NodeRef>,
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) owners: Option<[FlatDraftOwner; 6]>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NodeRef {
    Positive(PositiveId),
    Negative(NegativeId),
}

// Own the mapped lanes while yu-types borrows the indexed view.
#[allow(dead_code)] // Private candidate; production selection is a later gate.
pub(super) struct IndexedFlatDraft<'meter> {
    quantifier_count: u32,
    predicate: IndexedPositiveNodeId,
    positive_nodes: TrackedVec<'meter, IndexedPositiveNode>,
    negative_nodes: TrackedVec<'meter, IndexedNegativeNode>,
    positive_children: TrackedVec<'meter, IndexedPositiveNodeId>,
    negative_children: TrackedVec<'meter, IndexedNegativeNodeId>,
    recursive_bounds: TrackedVec<'meter, IndexedRecursiveBound>,
}

impl IndexedFlatDraft<'_> {
    #[cfg(test)]
    pub(super) fn physical_capacities(&self) -> [usize; 5] {
        [
            self.positive_nodes.capacity(),
            self.negative_nodes.capacity(),
            self.positive_children.capacity(),
            self.negative_children.capacity(),
            self.recursive_bounds.capacity(),
        ]
    }

    #[allow(dead_code)]
    pub(super) fn as_ref(&self) -> IndexedSchemeRef<'_> {
        IndexedSchemeRef {
            quantifier_count: self.quantifier_count,
            predicate: self.predicate,
            positive_nodes: &self.positive_nodes,
            negative_nodes: &self.negative_nodes,
            positive_children: &self.positive_children,
            negative_children: &self.negative_children,
            recursive_bounds: &self.recursive_bounds,
        }
    }

    #[allow(dead_code)]
    pub(super) fn retained_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        [
            self.positive_nodes.accounted_bytes(),
            self.negative_nodes.accounted_bytes(),
            self.positive_children.accounted_bytes(),
            self.negative_children.accounted_bytes(),
            self.recursive_bounds.accounted_bytes(),
        ]
        .into_iter()
        .try_fold(0usize, |sum, bytes| sum.checked_add(bytes))
        .ok_or(SolveAvailabilityError::IdentityExhausted)
    }
}

#[allow(dead_code)]
fn mapped<'meter, T, U>(
    meter: &'meter DraftHeapMeter,
    kind: PhysicalOwnerKind,
    source: &[T],
    mut convert: impl FnMut(&T) -> Result<U, SolveAvailabilityError>,
) -> Result<TrackedVec<'meter, U>, SolveAvailabilityError> {
    let mut result = TrackedVec::new_with_kind(meter, kind);
    result
        .try_reserve(source.len())
        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
    for item in source {
        result.push_reserved(convert(item)?);
    }
    Ok(result)
}

#[allow(dead_code)]
fn indexed_span(span: ChildSpan) -> Result<IndexedChildSpan, SolveAvailabilityError> {
    span.start
        .checked_add(span.len)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    Ok(IndexedChildSpan {
        start: span.start,
        len: span.len,
    })
}

fn indexed_count(len: usize) -> Result<u32, SolveAvailabilityError> {
    u32::try_from(len).map_err(|_| SolveAvailabilityError::IdentityExhausted)
}

fn checked_next_node_count(len: usize) -> Result<u32, SolveAvailabilityError> {
    indexed_count(
        len.checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?,
    )
}

pub(super) fn checked_q_r_count(q: u32, r: usize) -> Result<u32, SolveAvailabilityError> {
    q.checked_add(indexed_count(r)?)
        .ok_or(SolveAvailabilityError::IdentityExhausted)
}

#[cfg(test)]
pub(super) fn indexed_count_for_test(len: usize) -> Result<u32, SolveAvailabilityError> {
    indexed_count(len)
}

impl FlatDraft {
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn attach_owners(&mut self, meter: &DraftHeapMeter, lanes: [usize; 6]) {
        self.attach_owners_component(meter.event_component(), lanes);
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn attach_owners_component(&mut self, component: usize, lanes: [usize; 6]) {
        self.attach_owners_with_kind(component, lanes, false);
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn attach_normalization_owners(&mut self, component: usize) {
        self.attach_owners_with_kind(component, [21, 22, 23, 24, 25, 26], true);
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn attach_owners_with_kind(&mut self, component: usize, lanes: [usize; 6],
        normalization: bool) {
        assert!(self.owners.is_none());
        let sizes = [
            std::mem::size_of::<PositiveNode>(),
            std::mem::size_of::<NegativeNode>(),
            std::mem::size_of::<PositiveId>(),
            std::mem::size_of::<NegativeId>(),
            std::mem::size_of::<RecursiveBound>(),
            std::mem::size_of::<NodeRef>(),
        ];
        let capacities = self.capacities();
        let lengths = self.lengths();
        self.owners = Some(std::array::from_fn(|i| {
            let mut owner = if normalization {
                FlatDraftOwner::new_normalization(component, lanes[i], sizes[i])
            } else {
                FlatDraftOwner::new_with_component(component, lanes[i], sizes[i])
            };
            owner.observe(lengths[i], capacities[i]);
            owner
        }));
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn capacities(&self) -> [usize; 6] {
        [self.positive_nodes.capacity(), self.negative_nodes.capacity(),
            self.positive_children.capacity(), self.negative_children.capacity(),
            self.recursive_bounds.capacity(), self.insertion_order.capacity()]
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    fn lengths(&self) -> [usize; 6] {
        [self.positive_nodes.len(), self.negative_nodes.len(),
            self.positive_children.len(), self.negative_children.len(),
            self.recursive_bounds.len(), self.insertion_order.len()]
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn observe_owner(&mut self, index: usize, _requested: usize) {
        let capacity = self.capacities()[index];
        let requested = self.lengths()[index];
        if let Some(owners) = self.owners.as_mut() {
            owners[index].observe(requested, capacity);
        }
    }

    #[cfg(all(test, feature = "f5c_resource_probe"))]
    pub(super) fn sync_owners(&mut self) {
        for index in 0..6 { self.observe_owner(index, 0); }
    }
    pub(super) fn structural_census(&self) -> Result<(usize, usize), SolveAvailabilityError> {
        Ok((
            self.positive_children
                .len()
                .checked_add(self.negative_children.len())
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
            self.structural_incidences,
        ))
    }

    pub(super) fn restore_structural_census(&mut self, incidences: usize) {
        self.structural_incidences = incidences;
    }

    pub(super) fn admit_child_entries(&self, count: usize) -> Result<(), SolveAvailabilityError> {
        self.structural_census()?
            .0
            .checked_add(count)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn positive_child(
        &mut self,
        child: PositiveId,
    ) -> Result<(), SolveAvailabilityError> {
        self.admit_child_entries(1)?;
        u32::try_from(self.positive_children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let reservation = self.positive_children.try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(2, self.positive_children.len() + 1);
        reservation?;
        self.positive_children.push(child);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(2, 0);
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn negative_child(
        &mut self,
        child: NegativeId,
    ) -> Result<(), SolveAvailabilityError> {
        self.admit_child_entries(1)?;
        u32::try_from(self.negative_children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let reservation = self.negative_children.try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(3, self.negative_children.len() + 1);
        reservation?;
        self.negative_children.push(child);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(3, 0);
        Ok(())
    }

    fn node_incidences(&self, count: usize) -> Result<usize, SolveAvailabilityError> {
        self.structural_incidences
            .checked_add(count)
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    pub(super) fn admit_logical_incidences(
        &self,
        count: usize,
    ) -> Result<(), SolveAvailabilityError> {
        self.node_incidences(count)?;
        Ok(())
    }

    // The caller admits the entire batch and reserves this lane before draining it.
    pub(super) fn push_reserved_positive_child(&mut self, child: PositiveId) {
        debug_assert!(self.positive_children.len() < self.positive_children.capacity());
        self.positive_children.push(child);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(2, 0);
    }

    pub(super) fn push_reserved_negative_child(&mut self, child: NegativeId) {
        debug_assert!(self.negative_children.len() < self.negative_children.capacity());
        self.negative_children.push(child);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(3, 0);
    }

    pub(super) fn admit_positive_node(
        &self,
        node: PositiveNode,
    ) -> Result<(), SolveAvailabilityError> {
        checked_next_node_count(self.positive_nodes.len())?;
        self.node_incidences(match node {
            PositiveNode::Union(span) => span.len as usize,
            PositiveNode::Function { .. } => 2,
            _ => 0,
        })?;
        Ok(())
    }

    pub(super) fn admit_negative_node(
        &self,
        node: NegativeNode,
    ) -> Result<(), SolveAvailabilityError> {
        checked_next_node_count(self.negative_nodes.len())?;
        self.node_incidences(match node {
            NegativeNode::Intersection(span) => span.len as usize,
            NegativeNode::Function { .. } => 2,
            _ => 0,
        })?;
        Ok(())
    }

    #[allow(dead_code)]
    pub(super) fn indexed<'meter>(
        &self,
        meter: &'meter DraftHeapMeter,
    ) -> Result<IndexedFlatDraft<'meter>, SolveAvailabilityError> {
        let exhausted = SolveAvailabilityError::IdentityExhausted;
        checked_q_r_count(self.quantifier_count, self.recursive_bounds.len())?;
        for len in [
            self.positive_nodes.len(),
            self.negative_nodes.len(),
            self.positive_children.len(),
            self.negative_children.len(),
        ] {
            indexed_count(len)?;
        }
        let predicate = IndexedPositiveNodeId(self.predicate.ok_or(exhausted)?.0);
        let positive_nodes = mapped(meter, PhysicalOwnerKind::IndexedBuffer(0), &self.positive_nodes, |node| {
            Ok(match *node {
                PositiveNode::Bottom => IndexedPositiveNode::Bottom,
                PositiveNode::Int => IndexedPositiveNode::Int,
                PositiveNode::Variable(_) => return Err(exhausted),
                PositiveNode::Quantified(n) => IndexedPositiveNode::Quantified(n),
                PositiveNode::Recursive(n) => IndexedPositiveNode::Recursive(n),
                PositiveNode::Union(span) => IndexedPositiveNode::Union(indexed_span(span)?),
                PositiveNode::Function { argument, result } => IndexedPositiveNode::Function {
                    argument: IndexedNegativeNodeId(argument.0),
                    result: IndexedPositiveNodeId(result.0),
                },
            })
        })?;
        let negative_nodes = mapped(meter, PhysicalOwnerKind::IndexedBuffer(1), &self.negative_nodes, |node| {
            Ok(match *node {
                NegativeNode::Top => IndexedNegativeNode::Top,
                NegativeNode::Bottom => IndexedNegativeNode::Bottom,
                NegativeNode::Int => IndexedNegativeNode::Int,
                NegativeNode::Variable(_) => return Err(exhausted),
                NegativeNode::Quantified(n) => IndexedNegativeNode::Quantified(n),
                NegativeNode::Recursive(n) => IndexedNegativeNode::Recursive(n),
                NegativeNode::Intersection(span) => {
                    IndexedNegativeNode::Intersection(indexed_span(span)?)
                }
                NegativeNode::Function { argument, result } => IndexedNegativeNode::Function {
                    argument: IndexedPositiveNodeId(argument.0),
                    result: IndexedNegativeNodeId(result.0),
                },
            })
        })?;
        Ok(IndexedFlatDraft {
            quantifier_count: self.quantifier_count,
            predicate,
            positive_nodes,
            negative_nodes,
            positive_children: mapped(meter, PhysicalOwnerKind::IndexedBuffer(2), &self.positive_children, |id| {
                Ok(IndexedPositiveNodeId(id.0))
            })?,
            negative_children: mapped(meter, PhysicalOwnerKind::IndexedBuffer(3), &self.negative_children, |id| {
                Ok(IndexedNegativeNodeId(id.0))
            })?,
            recursive_bounds: mapped(meter, PhysicalOwnerKind::IndexedBuffer(4), &self.recursive_bounds, |bound| {
                Ok(IndexedRecursiveBound {
                    ordinal: bound.ordinal,
                    lower: IndexedPositiveNodeId(bound.lower.0),
                    upper: IndexedNegativeNodeId(bound.upper.0),
                })
            })?,
        })
    }
}

impl FlatDraft {
    pub(super) fn positive(
        &mut self,
        node: PositiveNode,
    ) -> Result<PositiveId, SolveAvailabilityError> {
        self.admit_positive_node(node)?;
        let incidences = self.node_incidences(match node {
            PositiveNode::Union(span) => span.len as usize,
            PositiveNode::Function { .. } => 2,
            _ => 0,
        })?;
        let id = PositiveId(
            u32::try_from(self.positive_nodes.len())
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
        );
        let reservation = self.positive_nodes.try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(0, self.positive_nodes.len() + 1);
        reservation?;
        let reservation = self.insertion_order.try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(5, self.insertion_order.len() + 1);
        reservation?;
        self.positive_nodes.push(node);
        self.insertion_order.push(NodeRef::Positive(id));
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        {
            self.observe_owner(0, 0);
            self.observe_owner(5, 0);
        }
        self.structural_incidences = incidences;
        Ok(id)
    }

    pub(super) fn negative(
        &mut self,
        node: NegativeNode,
    ) -> Result<NegativeId, SolveAvailabilityError> {
        self.admit_negative_node(node)?;
        let incidences = self.node_incidences(match node {
            NegativeNode::Intersection(span) => span.len as usize,
            NegativeNode::Function { .. } => 2,
            _ => 0,
        })?;
        let id = NegativeId(
            u32::try_from(self.negative_nodes.len())
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
        );
        let reservation = self.negative_nodes.try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(1, self.negative_nodes.len() + 1);
        reservation?;
        let reservation = self.insertion_order.try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(5, self.insertion_order.len() + 1);
        reservation?;
        self.negative_nodes.push(node);
        self.insertion_order.push(NodeRef::Negative(id));
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        {
            self.observe_owner(1, 0);
            self.observe_owner(5, 0);
        }
        self.structural_incidences = incidences;
        Ok(id)
    }

    pub(super) fn positive_span(
        &mut self,
        children: &[PositiveId],
    ) -> Result<ChildSpan, SolveAvailabilityError> {
        self.admit_child_entries(children.len())?;
        self.admit_logical_incidences(children.len())?;
        let start = u32::try_from(self.positive_children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let len =
            u32::try_from(children.len()).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        start
            .checked_add(len)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let reservation = self.positive_children.try_reserve(children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(2, self.positive_children.len() + children.len());
        reservation?;
        self.positive_children.extend_from_slice(children);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(2, 0);
        Ok(ChildSpan { start, len })
    }

    pub(super) fn negative_span(
        &mut self,
        children: &[NegativeId],
    ) -> Result<ChildSpan, SolveAvailabilityError> {
        self.admit_child_entries(children.len())?;
        self.admit_logical_incidences(children.len())?;
        let start = u32::try_from(self.negative_children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let len =
            u32::try_from(children.len()).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        start
            .checked_add(len)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let reservation = self.negative_children.try_reserve(children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(3, self.negative_children.len() + children.len());
        reservation?;
        self.negative_children.extend_from_slice(children);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(3, 0);
        Ok(ChildSpan { start, len })
    }

    pub(super) fn bound(&mut self, bound: RecursiveBound) -> Result<(), SolveAvailabilityError> {
        let next = self
            .recursive_bounds
            .len()
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        checked_q_r_count(self.quantifier_count, next)?;
        let reservation = self.recursive_bounds.try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(4, self.recursive_bounds.len() + 1);
        reservation?;
        self.recursive_bounds.push(bound);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        self.observe_owner(4, 0);
        Ok(())
    }
}

#[cfg(test)]
mod node_count_tests {
    use super::*;

    #[test]
    fn next_node_count_fits_indexed_array_length() {
        assert_eq!(checked_next_node_count(u32::MAX as usize - 1), Ok(u32::MAX));
        assert_eq!(
            checked_next_node_count(u32::MAX as usize),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert_eq!(
            checked_next_node_count(usize::MAX),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
    }

    #[test]
    fn append_ids_and_counts_remain_polarity_specific() {
        let mut draft = FlatDraft::default();
        assert_eq!(draft.positive(PositiveNode::Int), Ok(PositiveId(0)));
        assert_eq!(draft.negative(NegativeNode::Top), Ok(NegativeId(0)));
        assert_eq!(draft.positive(PositiveNode::Bottom), Ok(PositiveId(1)));
        assert_eq!(draft.negative(NegativeNode::Int), Ok(NegativeId(1)));
        assert_eq!(draft.positive_nodes.len(), 2);
        assert_eq!(draft.negative_nodes.len(), 2);
        assert_eq!(draft.insertion_order.len(), 4);
    }
}

#[cfg(test)]
mod structural_census_tests {
    use super::*;

    #[test]
    fn counts_stored_entries_and_parent_incidences_separately() {
        let mut draft = FlatDraft::default();
        let leaf = draft.positive(PositiveNode::Int).unwrap();
        let negative = draft.negative(NegativeNode::Top).unwrap();
        draft.negative_child(negative).unwrap();
        let span = draft.positive_span(&[leaf, leaf]).unwrap();
        let negative_span = draft.negative_span(&[negative, negative]).unwrap();
        assert_eq!(draft.structural_census().unwrap(), (5, 0));
        draft.positive(PositiveNode::Union(span)).unwrap();
        draft.positive(PositiveNode::Union(span)).unwrap();
        draft
            .negative(NegativeNode::Intersection(negative_span))
            .unwrap();
        draft
            .positive(PositiveNode::Function {
                argument: negative,
                result: leaf,
            })
            .unwrap();
        draft
            .negative(NegativeNode::Function {
                argument: leaf,
                result: negative,
            })
            .unwrap();
        assert_eq!(draft.structural_census().unwrap(), (5, 10));
        let before = draft.structural_census().unwrap();
        draft.positive_child(leaf).unwrap();
        draft
            .positive(PositiveNode::Function {
                argument: negative,
                result: leaf,
            })
            .unwrap();
        draft.positive_children.pop();
        draft.positive_nodes.pop();
        draft.insertion_order.pop();
        draft.restore_structural_census(before.1);
        assert_eq!(draft.structural_census().unwrap(), before);
    }
}
