use super::SolveAvailabilityError;
use super::f5c_draft_heap::{DraftHeapMeter, TrackedVec};
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
    pub(super) quantifier_count: u32,
    pub(super) predicate: Option<PositiveId>,
    pub(super) positive_nodes: Vec<PositiveNode>,
    pub(super) negative_nodes: Vec<NegativeNode>,
    pub(super) positive_children: Vec<PositiveId>,
    pub(super) negative_children: Vec<NegativeId>,
    pub(super) recursive_bounds: Vec<RecursiveBound>,
    pub(super) insertion_order: Vec<NodeRef>,
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
    source: &[T],
    mut convert: impl FnMut(&T) -> Result<U, SolveAvailabilityError>,
) -> Result<TrackedVec<'meter, U>, SolveAvailabilityError> {
    let mut result = TrackedVec::new(meter);
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

#[cfg(test)]
pub(super) fn indexed_count_for_test(len: usize) -> Result<u32, SolveAvailabilityError> {
    indexed_count(len)
}

impl FlatDraft {
    #[allow(dead_code)]
    pub(super) fn indexed<'meter>(
        &self,
        meter: &'meter DraftHeapMeter,
    ) -> Result<IndexedFlatDraft<'meter>, SolveAvailabilityError> {
        let exhausted = SolveAvailabilityError::IdentityExhausted;
        let bounds = indexed_count(self.recursive_bounds.len())?;
        self.quantifier_count.checked_add(bounds).ok_or(exhausted)?;
        for len in [
            self.positive_nodes.len(),
            self.negative_nodes.len(),
            self.positive_children.len(),
            self.negative_children.len(),
        ] {
            indexed_count(len)?;
        }
        let predicate = IndexedPositiveNodeId(self.predicate.ok_or(exhausted)?.0);
        let positive_nodes = mapped(meter, &self.positive_nodes, |node| {
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
        let negative_nodes = mapped(meter, &self.negative_nodes, |node| {
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
            positive_children: mapped(meter, &self.positive_children, |id| {
                Ok(IndexedPositiveNodeId(id.0))
            })?,
            negative_children: mapped(meter, &self.negative_children, |id| {
                Ok(IndexedNegativeNodeId(id.0))
            })?,
            recursive_bounds: mapped(meter, &self.recursive_bounds, |bound| {
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
        let id = PositiveId(
            u32::try_from(self.positive_nodes.len())
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
        );
        self.positive_nodes
            .try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.insertion_order
            .try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.positive_nodes.push(node);
        self.insertion_order.push(NodeRef::Positive(id));
        Ok(id)
    }

    pub(super) fn negative(
        &mut self,
        node: NegativeNode,
    ) -> Result<NegativeId, SolveAvailabilityError> {
        let id = NegativeId(
            u32::try_from(self.negative_nodes.len())
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
        );
        self.negative_nodes
            .try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.insertion_order
            .try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.negative_nodes.push(node);
        self.insertion_order.push(NodeRef::Negative(id));
        Ok(id)
    }

    pub(super) fn positive_span(
        &mut self,
        children: &[PositiveId],
    ) -> Result<ChildSpan, SolveAvailabilityError> {
        let start = u32::try_from(self.positive_children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let len =
            u32::try_from(children.len()).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        start
            .checked_add(len)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.positive_children
            .try_reserve(children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.positive_children.extend_from_slice(children);
        Ok(ChildSpan { start, len })
    }

    pub(super) fn negative_span(
        &mut self,
        children: &[NegativeId],
    ) -> Result<ChildSpan, SolveAvailabilityError> {
        let start = u32::try_from(self.negative_children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let len =
            u32::try_from(children.len()).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        start
            .checked_add(len)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.negative_children
            .try_reserve(children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.negative_children.extend_from_slice(children);
        Ok(ChildSpan { start, len })
    }

    pub(super) fn bound(&mut self, bound: RecursiveBound) -> Result<(), SolveAvailabilityError> {
        self.recursive_bounds
            .try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.recursive_bounds.push(bound);
        Ok(())
    }
}
