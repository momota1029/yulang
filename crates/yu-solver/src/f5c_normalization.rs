use std::cmp::Ordering;

#[cfg(test)]
use super::F5cRecursiveBound;
use super::f5c_draft::{
    FlatDraft, NegativeId, NegativeNode, NodeRef, PositiveId, PositiveNode, RecursiveBound,
};
use super::{F5cNegative, F5cPositive, GeneralizationDraft, SolveAvailabilityError};

type NodeId = usize;

pub(super) const LANE_COUNT: usize = 13;
const RADIX_ALPHABET: usize = 257;
const RADIX_WORKSPACE_SLOTS: usize = RADIX_ALPHABET * 3;
const RADIX_INSERTION_LIMIT: usize = 8;

#[derive(Clone, Copy)]
#[repr(usize)]
enum Lane {
    Nodes,
    Children,
    Walk,
    Values,
    Roots,
    HeightCounts,
    HeightOffsets,
    HeightNodes,
    SortScratch,
    DescriptorWords,
    Output,
    RadixFrames,
    RadixWorkspace,
}

#[derive(Clone, Copy)]
struct RadixFrame {
    start: usize,
    end: usize,
    byte: usize,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct NormalizationLaneStats {
    pub(super) requested_slots: usize,
    pub(super) actual_capacity: usize,
    pub(super) peak_capacity: usize,
    pub(super) slot_size: usize,
    pub(super) retained_bytes: usize,
    pub(super) peak_bytes: usize,
    pub(super) capacity_growths: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NormalizedKeyId {
    height: u32,
    rank: u32,
}

#[derive(Clone, Copy)]
enum NodeKind {
    PositiveBottom,
    PositiveInt,
    PositiveQuantified(u32),
    PositiveRecursive(u32),
    PositiveUnion { start: usize, len: usize },
    PositiveFunction { start: usize },
    NegativeTop,
    NegativeBottom,
    NegativeInt,
    NegativeQuantified(u32),
    NegativeRecursive(u32),
    NegativeIntersection { start: usize, len: usize },
    NegativeFunction { start: usize },
}

#[derive(Clone, Copy)]
struct Node {
    kind: NodeKind,
    height: u32,
    rank: u32,
    descriptor: Option<(usize, usize)>,
}

enum Walk {
    Positive(F5cPositive),
    Negative(F5cNegative),
    FinishPositiveUnion(usize),
    FinishPositiveFunction,
    FinishNegativeIntersection(usize),
    FinishNegativeFunction,
}

#[derive(Clone, Copy)]
enum BuiltRef {
    Positive(NodeId),
    Negative(NodeId),
}

enum BuiltValue {
    Positive(F5cPositive),
    Negative(F5cNegative),
}

#[derive(Clone, Copy)]
enum RootLocation {
    Predicate(usize),
    Lower(usize, usize),
    Upper(usize, usize),
}

#[derive(Clone, Copy)]
struct Root {
    node: NodeId,
    location: RootLocation,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct NormalizationStats {
    pub(super) key_writes: usize,
    pub(super) child_comparisons: usize,
    pub(super) descriptor_words: usize,
    pub(super) word_comparisons: usize,
    pub(super) duplicates: usize,
    pub(super) index_requested_slots: usize,
    pub(super) index_actual_capacity: usize,
    pub(super) index_retained_bytes: usize,
    pub(super) index_peak_bytes: usize,
    pub(super) index_capacity_growths: usize,
    pub(super) index_lanes: [NormalizationLaneStats; LANE_COUNT],
    #[cfg(test)]
    pub(super) physical_lane_capacities: [usize; LANE_COUNT],
    #[cfg(test)]
    pub(super) physical_lane_slot_sizes: [usize; LANE_COUNT],
}

// Candidate-only logical counters; not the production normalization/resource ledger.
#[derive(Debug, Eq, PartialEq)]
pub(super) struct FlatNormalizationStats {
    key_writes: usize,
    child_comparisons: usize,
    descriptor_words: usize,
    word_comparisons: usize,
    duplicates: usize,
}

impl From<&NormalizationStats> for FlatNormalizationStats {
    fn from(stats: &NormalizationStats) -> Self {
        Self {
            key_writes: stats.key_writes,
            child_comparisons: stats.child_comparisons,
            descriptor_words: stats.descriptor_words,
            word_comparisons: stats.word_comparisons,
            duplicates: stats.duplicates,
        }
    }
}

struct Normalizer {
    nodes: Vec<Node>,
    children: Vec<NodeId>,
    walk: Vec<Walk>,
    values: Vec<BuiltRef>,
    roots: Vec<Root>,
    height_counts: Vec<usize>,
    height_offsets: Vec<usize>,
    height_nodes: Vec<NodeId>,
    sort_scratch: Vec<NodeId>,
    descriptor_words: Vec<u32>,
    output: Vec<Option<BuiltValue>>,
    radix_frames: Vec<RadixFrame>,
    radix_workspace: Vec<usize>,
    stats: NormalizationStats,
}

impl Normalizer {
    fn new() -> Self {
        Self {
            nodes: Vec::new(),
            children: Vec::new(),
            walk: Vec::new(),
            values: Vec::new(),
            roots: Vec::new(),
            height_counts: Vec::new(),
            height_offsets: Vec::new(),
            height_nodes: Vec::new(),
            sort_scratch: Vec::new(),
            descriptor_words: Vec::new(),
            output: Vec::new(),
            radix_frames: Vec::new(),
            radix_workspace: Vec::new(),
            stats: NormalizationStats::default(),
        }
    }

    #[cfg(test)]
    fn physical_lane_snapshot(&self) -> ([usize; LANE_COUNT], [usize; LANE_COUNT]) {
        (
            [
                self.nodes.capacity(),
                self.children.capacity(),
                self.walk.capacity(),
                self.values.capacity(),
                self.roots.capacity(),
                self.height_counts.capacity(),
                self.height_offsets.capacity(),
                self.height_nodes.capacity(),
                self.sort_scratch.capacity(),
                self.descriptor_words.capacity(),
                self.output.capacity(),
                self.radix_frames.capacity(),
                self.radix_workspace.capacity(),
            ],
            [
                std::mem::size_of::<Node>(),
                std::mem::size_of::<NodeId>(),
                std::mem::size_of::<Walk>(),
                std::mem::size_of::<BuiltRef>(),
                std::mem::size_of::<Root>(),
                std::mem::size_of::<usize>(),
                std::mem::size_of::<usize>(),
                std::mem::size_of::<NodeId>(),
                std::mem::size_of::<NodeId>(),
                std::mem::size_of::<u32>(),
                std::mem::size_of::<Option<BuiltValue>>(),
                if self.radix_frames.capacity() == 0 {
                    0
                } else {
                    std::mem::size_of::<RadixFrame>()
                },
                if self.radix_workspace.capacity() == 0 {
                    0
                } else {
                    std::mem::size_of::<usize>()
                },
            ],
        )
    }

    fn reserve<T>(
        items: &mut Vec<T>,
        additional: usize,
        lane: Lane,
        stats: &mut NormalizationStats,
    ) -> Result<(), SolveAvailabilityError> {
        let old_capacity = items.capacity();
        let requested_slots = stats.index_lanes[lane as usize]
            .requested_slots
            .checked_add(additional)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        items
            .try_reserve(additional)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let capacity = items.capacity();
        let slot_size = std::mem::size_of::<T>();
        let old_bytes = old_capacity
            .checked_mul(slot_size)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let retained_bytes = capacity
            .checked_mul(slot_size)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let lane_stats = &mut stats.index_lanes[lane as usize];
        lane_stats.requested_slots = requested_slots;
        lane_stats.actual_capacity = capacity;
        lane_stats.peak_capacity = lane_stats.peak_capacity.max(capacity);
        lane_stats.slot_size = slot_size;
        lane_stats.retained_bytes = retained_bytes;
        if capacity != old_capacity {
            lane_stats.capacity_growths = lane_stats
                .capacity_growths
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        }
        lane_stats.peak_bytes = lane_stats.peak_bytes.max(lane_stats.retained_bytes);
        stats.index_requested_slots = stats
            .index_requested_slots
            .checked_add(additional)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        stats.index_actual_capacity = stats
            .index_actual_capacity
            .checked_sub(old_capacity)
            .and_then(|total| total.checked_add(capacity))
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        stats.index_retained_bytes = stats
            .index_retained_bytes
            .checked_sub(old_bytes)
            .and_then(|total| total.checked_add(retained_bytes))
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        if capacity != old_capacity {
            stats.index_capacity_growths = stats
                .index_capacity_growths
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        }
        stats.index_peak_bytes = stats.index_peak_bytes.max(stats.index_retained_bytes);
        Ok(())
    }

    fn push<T>(
        items: &mut Vec<T>,
        item: T,
        lane: Lane,
        stats: &mut NormalizationStats,
    ) -> Result<(), SolveAvailabilityError> {
        Self::reserve(items, 1, lane, stats)?;
        items.push(item);
        Ok(())
    }

    fn push_word(&mut self, word: u32) -> Result<(), SolveAvailabilityError> {
        let next = self
            .stats
            .descriptor_words
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        Self::push(
            &mut self.descriptor_words,
            word,
            Lane::DescriptorWords,
            &mut self.stats,
        )?;
        self.stats.descriptor_words = next;
        Ok(())
    }

    fn push_node(
        &mut self,
        kind: NodeKind,
        children: &[NodeId],
    ) -> Result<NodeId, SolveAvailabilityError> {
        let start = self.children.len();
        Self::reserve(
            &mut self.children,
            children.len(),
            Lane::Children,
            &mut self.stats,
        )?;
        self.children.extend_from_slice(children);
        self.push_node_at(kind, start, children.len())
    }

    fn push_node_at(
        &mut self,
        kind: NodeKind,
        start: usize,
        child_count: usize,
    ) -> Result<NodeId, SolveAvailabilityError> {
        let end = start
            .checked_add(child_count)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let mut height = 0u32;
        for child in self
            .children
            .get(start..end)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?
        {
            let child_height = self
                .nodes
                .get(*child)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?
                .height;
            height = height.max(child_height);
        }
        if child_count != 0 {
            height = height
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        }
        let node = Node {
            kind,
            height,
            rank: 0,
            descriptor: None,
        };
        let id = self.nodes.len();
        Self::push(&mut self.nodes, node, Lane::Nodes, &mut self.stats)?;
        Ok(match kind {
            NodeKind::PositiveUnion { .. } => {
                self.nodes[id].kind = NodeKind::PositiveUnion {
                    start,
                    len: child_count,
                };
                id
            }
            NodeKind::PositiveFunction { .. } => {
                self.nodes[id].kind = NodeKind::PositiveFunction { start };
                id
            }
            NodeKind::NegativeIntersection { .. } => {
                self.nodes[id].kind = NodeKind::NegativeIntersection {
                    start,
                    len: child_count,
                };
                id
            }
            NodeKind::NegativeFunction { .. } => {
                self.nodes[id].kind = NodeKind::NegativeFunction { start };
                id
            }
            _ => id,
        })
    }

    fn flatten_positive(&mut self, value: F5cPositive) -> Result<NodeId, SolveAvailabilityError> {
        Self::push(
            &mut self.walk,
            Walk::Positive(value),
            Lane::Walk,
            &mut self.stats,
        )?;
        self.flatten()
    }

    fn flatten_negative(&mut self, value: F5cNegative) -> Result<NodeId, SolveAvailabilityError> {
        Self::push(
            &mut self.walk,
            Walk::Negative(value),
            Lane::Walk,
            &mut self.stats,
        )?;
        self.flatten()
    }

    fn flatten(&mut self) -> Result<NodeId, SolveAvailabilityError> {
        self.values.clear();
        while let Some(work) = self.walk.pop() {
            match work {
                Walk::Positive(value) => match value {
                    F5cPositive::Bottom => self.push_leaf(NodeKind::PositiveBottom)?,
                    F5cPositive::Int => self.push_leaf(NodeKind::PositiveInt)?,
                    F5cPositive::Variable(_) | F5cPositive::Shared(_) => {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    }
                    F5cPositive::Quantified(ordinal) => {
                        self.push_leaf(NodeKind::PositiveQuantified(ordinal))?;
                    }
                    F5cPositive::Recursive(ordinal) => {
                        self.push_leaf(NodeKind::PositiveRecursive(ordinal))?;
                    }
                    F5cPositive::Union(children) => {
                        let len = children.len();
                        Self::push(
                            &mut self.walk,
                            Walk::FinishPositiveUnion(len),
                            Lane::Walk,
                            &mut self.stats,
                        )?;
                        for child in children.into_iter().rev() {
                            Self::push(
                                &mut self.walk,
                                Walk::Positive(child),
                                Lane::Walk,
                                &mut self.stats,
                            )?;
                        }
                    }
                    F5cPositive::Function {
                        argument, result, ..
                    } => {
                        Self::push(
                            &mut self.walk,
                            Walk::FinishPositiveFunction,
                            Lane::Walk,
                            &mut self.stats,
                        )?;
                        Self::push(
                            &mut self.walk,
                            Walk::Positive(*result),
                            Lane::Walk,
                            &mut self.stats,
                        )?;
                        Self::push(
                            &mut self.walk,
                            Walk::Negative(*argument),
                            Lane::Walk,
                            &mut self.stats,
                        )?;
                    }
                },
                Walk::Negative(value) => match value {
                    F5cNegative::Top => self.push_leaf(NodeKind::NegativeTop)?,
                    F5cNegative::Bottom => self.push_leaf(NodeKind::NegativeBottom)?,
                    F5cNegative::Int => self.push_leaf(NodeKind::NegativeInt)?,
                    F5cNegative::Variable(_) | F5cNegative::Shared(_) => {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    }
                    F5cNegative::Quantified(ordinal) => {
                        self.push_leaf(NodeKind::NegativeQuantified(ordinal))?;
                    }
                    F5cNegative::Recursive(ordinal) => {
                        self.push_leaf(NodeKind::NegativeRecursive(ordinal))?;
                    }
                    F5cNegative::Intersection(children) => {
                        let len = children.len();
                        Self::push(
                            &mut self.walk,
                            Walk::FinishNegativeIntersection(len),
                            Lane::Walk,
                            &mut self.stats,
                        )?;
                        for child in children.into_iter().rev() {
                            Self::push(
                                &mut self.walk,
                                Walk::Negative(child),
                                Lane::Walk,
                                &mut self.stats,
                            )?;
                        }
                    }
                    F5cNegative::Function {
                        argument, result, ..
                    } => {
                        Self::push(
                            &mut self.walk,
                            Walk::FinishNegativeFunction,
                            Lane::Walk,
                            &mut self.stats,
                        )?;
                        Self::push(
                            &mut self.walk,
                            Walk::Negative(*result),
                            Lane::Walk,
                            &mut self.stats,
                        )?;
                        Self::push(
                            &mut self.walk,
                            Walk::Positive(*argument),
                            Lane::Walk,
                            &mut self.stats,
                        )?;
                    }
                },
                Walk::FinishPositiveUnion(len) => {
                    let (start, count) = self.take_values_into_children(len, true)?;
                    let id = self.push_node_at(
                        NodeKind::PositiveUnion { start: 0, len: 0 },
                        start,
                        count,
                    )?;
                    Self::push(
                        &mut self.values,
                        BuiltRef::Positive(id),
                        Lane::Values,
                        &mut self.stats,
                    )?;
                }
                Walk::FinishPositiveFunction => {
                    let result = self.take_value()?;
                    let argument = self.take_value()?;
                    let (BuiltRef::Negative(argument), BuiltRef::Positive(result)) =
                        (argument, result)
                    else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    let id = self
                        .push_node(NodeKind::PositiveFunction { start: 0 }, &[argument, result])?;
                    Self::push(
                        &mut self.values,
                        BuiltRef::Positive(id),
                        Lane::Values,
                        &mut self.stats,
                    )?;
                }
                Walk::FinishNegativeIntersection(len) => {
                    let (start, count) = self.take_values_into_children(len, false)?;
                    let id = self.push_node_at(
                        NodeKind::NegativeIntersection { start: 0, len: 0 },
                        start,
                        count,
                    )?;
                    Self::push(
                        &mut self.values,
                        BuiltRef::Negative(id),
                        Lane::Values,
                        &mut self.stats,
                    )?;
                }
                Walk::FinishNegativeFunction => {
                    let result = self.take_value()?;
                    let argument = self.take_value()?;
                    let (BuiltRef::Positive(argument), BuiltRef::Negative(result)) =
                        (argument, result)
                    else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    let id = self
                        .push_node(NodeKind::NegativeFunction { start: 0 }, &[argument, result])?;
                    Self::push(
                        &mut self.values,
                        BuiltRef::Negative(id),
                        Lane::Values,
                        &mut self.stats,
                    )?;
                }
            }
        }
        let [value] = self.values.as_slice() else {
            return Err(SolveAvailabilityError::IdentityExhausted);
        };
        match value {
            BuiltRef::Positive(id) | BuiltRef::Negative(id) => Ok(*id),
        }
    }

    fn push_leaf(&mut self, kind: NodeKind) -> Result<(), SolveAvailabilityError> {
        let id = self.push_node(kind, &[])?;
        let reference = match kind {
            NodeKind::NegativeTop
            | NodeKind::NegativeBottom
            | NodeKind::NegativeInt
            | NodeKind::NegativeQuantified(_)
            | NodeKind::NegativeRecursive(_) => BuiltRef::Negative(id),
            _ => BuiltRef::Positive(id),
        };
        Self::push(&mut self.values, reference, Lane::Values, &mut self.stats)
    }

    fn take_values_into_children(
        &mut self,
        len: usize,
        positive: bool,
    ) -> Result<(usize, usize), SolveAvailabilityError> {
        let start = self
            .values
            .len()
            .checked_sub(len)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let children_start = self.children.len();
        Self::reserve(&mut self.children, len, Lane::Children, &mut self.stats)?;
        for value in &self.values[start..] {
            let id = match (positive, value) {
                (true, BuiltRef::Positive(id)) | (false, BuiltRef::Negative(id)) => *id,
                _ => return Err(SolveAvailabilityError::IdentityExhausted),
            };
            self.children.push(id);
        }
        self.values.truncate(start);
        Ok((children_start, len))
    }

    fn take_value(&mut self) -> Result<BuiltRef, SolveAvailabilityError> {
        self.values
            .pop()
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    }

    fn add_root(
        &mut self,
        value: BuiltRef,
        location: RootLocation,
    ) -> Result<(), SolveAvailabilityError> {
        let node = match value {
            BuiltRef::Positive(node) | BuiltRef::Negative(node) => node,
        };
        Self::push(
            &mut self.roots,
            Root { node, location },
            Lane::Roots,
            &mut self.stats,
        )
    }

    fn collect_drafts(
        &mut self,
        drafts: &mut [GeneralizationDraft],
    ) -> Result<(), SolveAvailabilityError> {
        for (draft_index, draft) in drafts.iter_mut().enumerate() {
            let predicate = std::mem::replace(&mut draft.predicate, F5cPositive::Bottom);
            let predicate = self.flatten_positive(predicate)?;
            self.add_root(
                BuiltRef::Positive(predicate),
                RootLocation::Predicate(draft_index),
            )?;
            for (bound_index, bound) in draft.recursive_bounds.iter_mut().enumerate() {
                let lower = std::mem::replace(&mut bound.lower, F5cPositive::Bottom);
                let upper = std::mem::replace(&mut bound.upper, F5cNegative::Top);
                let lower = self.flatten_positive(lower)?;
                self.add_root(
                    BuiltRef::Positive(lower),
                    RootLocation::Lower(draft_index, bound_index),
                )?;
                let upper = self.flatten_negative(upper)?;
                self.add_root(
                    BuiltRef::Negative(upper),
                    RootLocation::Upper(draft_index, bound_index),
                )?;
            }
        }
        Ok(())
    }

    fn prepare_height_groups(&mut self) -> Result<(), SolveAvailabilityError> {
        let max_height = self.nodes.iter().map(|node| node.height).max().unwrap_or(0);
        let height_count = usize::try_from(max_height)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        Self::reserve(
            &mut self.height_counts,
            height_count,
            Lane::HeightCounts,
            &mut self.stats,
        )?;
        self.height_counts.resize(height_count, 0);
        for node in &self.nodes {
            let index = usize::try_from(node.height)
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            self.height_counts[index] = self.height_counts[index]
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        }
        let offsets_len = height_count
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        Self::reserve(
            &mut self.height_offsets,
            offsets_len,
            Lane::HeightOffsets,
            &mut self.stats,
        )?;
        self.height_offsets.resize(offsets_len, 0);
        for index in 0..height_count {
            self.height_offsets[index + 1] = self.height_offsets[index]
                .checked_add(self.height_counts[index])
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        }
        Self::reserve(
            &mut self.height_nodes,
            self.nodes.len(),
            Lane::HeightNodes,
            &mut self.stats,
        )?;
        self.height_nodes.resize(self.nodes.len(), 0);
        self.height_counts
            .copy_from_slice(&self.height_offsets[..height_count]);
        for (id, node) in self.nodes.iter().enumerate() {
            let height = usize::try_from(node.height)
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            let slot = self.height_counts[height];
            self.height_nodes[slot] = id;
            self.height_counts[height] = slot
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        }
        Self::reserve(
            &mut self.sort_scratch,
            self.nodes.len(),
            Lane::SortScratch,
            &mut self.stats,
        )?;
        self.sort_scratch.resize(self.nodes.len(), 0);
        Ok(())
    }

    fn rank_all(&mut self) -> Result<(), SolveAvailabilityError> {
        self.prepare_height_groups()?;
        for height in 0..self.height_offsets.len() - 1 {
            let start = self.height_offsets[height];
            let end = self.height_offsets[height + 1];
            for index in start..end {
                let node_id = self.height_nodes[index];
                self.sort_node_children(node_id)?;
                self.write_descriptor(node_id)?;
            }
            self.radix_sort_descriptor_words(start, end)?;
            {
                let nodes = &self.nodes;
                let words = &self.descriptor_words;
                let stats = &mut self.stats;
                let (height_nodes, scratch) = (
                    &mut self.height_nodes[start..end],
                    &mut self.sort_scratch[start..end],
                );
                stable_merge_sort(height_nodes, scratch, &mut |left, right| {
                    compare_descriptors(nodes, words, stats, left, right)
                })?;
            }
            let mut rank = 0u32;
            let mut previous = None;
            for index in start..end {
                let node_id = self.height_nodes[index];
                if let Some(previous_id) = previous {
                    if !self.descriptors_equal(previous_id, node_id)? {
                        rank = rank
                            .checked_add(1)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    }
                }
                self.nodes[node_id].rank = rank;
                previous = Some(node_id);
                self.stats.key_writes = self
                    .stats
                    .key_writes
                    .checked_add(1)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            }
        }
        Ok(())
    }

    fn prepare_radix_workspaces(&mut self) -> Result<(), SolveAvailabilityError> {
        let workspace_additional = RADIX_WORKSPACE_SLOTS
            .checked_sub(self.radix_workspace.len())
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        Self::reserve(
            &mut self.radix_workspace,
            workspace_additional,
            Lane::RadixWorkspace,
            &mut self.stats,
        )?;
        self.radix_workspace.resize(RADIX_WORKSPACE_SLOTS, 0);
        Ok(())
    }

    fn radix_sort_descriptor_words(
        &mut self,
        start: usize,
        end: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let len = end
            .checked_sub(start)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        if len < 3 {
            return Ok(());
        }
        let workspace = if len > RADIX_INSERTION_LIMIT {
            self.prepare_radix_workspaces()?;
            Some(self.radix_workspace.as_mut_slice())
        } else {
            None
        };
        let nodes = &self.nodes;
        let words = &self.descriptor_words;
        let values = &mut self.height_nodes[start..end];
        radix_sort_node_ids(
            values,
            None,
            workspace,
            &mut self.radix_frames,
            &mut self.stats,
            |node_id, byte| descriptor_radix_symbol(nodes, words, node_id, byte),
        )
    }

    fn radix_sort_key_ids(
        &mut self,
        start: usize,
        len: usize,
    ) -> Result<(), SolveAvailabilityError> {
        if len < 3 {
            return Ok(());
        }
        let workspace = if len > RADIX_INSERTION_LIMIT {
            self.prepare_radix_workspaces()?;
            Some(self.radix_workspace.as_mut_slice())
        } else {
            None
        };
        let end = start
            .checked_add(len)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let nodes = &self.nodes;
        let values = &mut self.children[start..end];
        radix_sort_node_ids(
            values,
            Some(2 * std::mem::size_of::<u32>()),
            workspace,
            &mut self.radix_frames,
            &mut self.stats,
            |node_id, byte| key_id_radix_symbol(nodes, node_id, byte),
        )
    }

    fn sort_node_children(&mut self, node_id: NodeId) -> Result<(), SolveAvailabilityError> {
        let (start, len) = match self.nodes[node_id].kind {
            NodeKind::PositiveUnion { start, len }
            | NodeKind::NegativeIntersection { start, len } => (Some(start), len),
            _ => (None, 0),
        };
        let Some(start) = start else {
            return Ok(());
        };
        if len < 2 {
            return Ok(());
        }
        let end = start
            .checked_add(len)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.radix_sort_key_ids(start, len)?;
        {
            let nodes = &self.nodes;
            let stats = &mut self.stats;
            let (children, scratch) = (
                &mut self.children[start..end],
                &mut self.sort_scratch[..len],
            );
            stable_merge_sort(children, scratch, &mut |left, right| {
                stats.child_comparisons = stats
                    .child_comparisons
                    .checked_add(1)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                compare_key_ids(nodes, stats, left, right)
            })?;
        }
        let nodes = &self.nodes;
        let stats = &mut self.stats;
        let children = &mut self.children[start..end];
        let mut write = 0usize;
        for read in 0..len {
            let child = children[read];
            let duplicate = if write > 0 {
                stats.child_comparisons = stats
                    .child_comparisons
                    .checked_add(1)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                compare_key_ids(nodes, stats, children[write - 1], child)? == Ordering::Equal
            } else {
                false
            };
            if duplicate {
                stats.duplicates = stats
                    .duplicates
                    .checked_add(1)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                continue;
            }
            children[write] = child;
            write += 1;
        }
        match &mut self.nodes[node_id].kind {
            NodeKind::PositiveUnion { len, .. } | NodeKind::NegativeIntersection { len, .. } => {
                *len = write
            }
            _ => return Err(SolveAvailabilityError::IdentityExhausted),
        }
        Ok(())
    }

    fn write_descriptor(&mut self, node_id: NodeId) -> Result<(), SolveAvailabilityError> {
        let start = self.descriptor_words.len();
        let kind = self.nodes[node_id].kind;
        self.push_word(discriminator(kind))?;
        match kind {
            NodeKind::PositiveQuantified(ordinal)
            | NodeKind::PositiveRecursive(ordinal)
            | NodeKind::NegativeQuantified(ordinal)
            | NodeKind::NegativeRecursive(ordinal) => self.push_word(ordinal)?,
            NodeKind::PositiveUnion { start, len }
            | NodeKind::NegativeIntersection { start, len } => {
                self.push_word(
                    u32::try_from(len).map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                )?;
                self.push_child_keys(start, len)?;
            }
            NodeKind::PositiveFunction { start } | NodeKind::NegativeFunction { start } => {
                self.push_child_keys(start, 2)?;
            }
            _ => {}
        }
        let len = self
            .descriptor_words
            .len()
            .checked_sub(start)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.nodes[node_id].descriptor = Some((start, len));
        Ok(())
    }

    fn push_child_keys(&mut self, start: usize, len: usize) -> Result<(), SolveAvailabilityError> {
        let end = start
            .checked_add(len)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        for index in start..end {
            let child = self.children[index];
            let node = self
                .nodes
                .get(child)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let key = NormalizedKeyId {
                height: node.height,
                rank: node.rank,
            };
            self.push_word(key.height)?;
            self.push_word(key.rank)?;
        }
        Ok(())
    }

    fn descriptors_equal(
        &mut self,
        left: NodeId,
        right: NodeId,
    ) -> Result<bool, SolveAvailabilityError> {
        let nodes = &self.nodes;
        let words = &self.descriptor_words;
        let stats = &mut self.stats;
        Ok(compare_descriptors(nodes, words, stats, left, right)? == Ordering::Equal)
    }

    fn rebuild(
        &mut self,
        drafts: &mut [GeneralizationDraft],
    ) -> Result<(), SolveAvailabilityError> {
        Self::reserve(
            &mut self.output,
            self.nodes.len(),
            Lane::Output,
            &mut self.stats,
        )?;
        self.output.resize_with(self.nodes.len(), || None);
        for id in 0..self.nodes.len() {
            let kind = self.nodes[id].kind;
            let built = match kind {
                NodeKind::PositiveBottom => BuiltValue::Positive(F5cPositive::Bottom),
                NodeKind::PositiveInt => BuiltValue::Positive(F5cPositive::Int),
                NodeKind::PositiveQuantified(ordinal) => {
                    BuiltValue::Positive(F5cPositive::Quantified(ordinal))
                }
                NodeKind::PositiveRecursive(ordinal) => {
                    BuiltValue::Positive(F5cPositive::Recursive(ordinal))
                }
                NodeKind::PositiveUnion { start, len } => {
                    let end = start
                        .checked_add(len)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    let mut values = Vec::new();
                    values
                        .try_reserve(len)
                        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                    for child in self.children[start..end].iter().copied() {
                        let Some(BuiltValue::Positive(value)) = self.output[child].take() else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        values.push(value);
                    }
                    BuiltValue::Positive(F5cPositive::Union(values))
                }
                NodeKind::PositiveFunction { start } => {
                    let argument_id = self.children[start];
                    let result_id = self.children[start + 1];
                    let Some(BuiltValue::Negative(argument)) = self.output[argument_id].take()
                    else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    let Some(BuiltValue::Positive(result)) = self.output[result_id].take() else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    BuiltValue::Positive(F5cPositive::Function {
                        argument: Box::new(argument),
                        argument_effect: super::F5cNegativeEffect::Empty,
                        result_effect: super::F5cPositiveEffect::Bottom,
                        result: Box::new(result),
                    })
                }
                NodeKind::NegativeTop => BuiltValue::Negative(F5cNegative::Top),
                NodeKind::NegativeBottom => BuiltValue::Negative(F5cNegative::Bottom),
                NodeKind::NegativeInt => BuiltValue::Negative(F5cNegative::Int),
                NodeKind::NegativeQuantified(ordinal) => {
                    BuiltValue::Negative(F5cNegative::Quantified(ordinal))
                }
                NodeKind::NegativeRecursive(ordinal) => {
                    BuiltValue::Negative(F5cNegative::Recursive(ordinal))
                }
                NodeKind::NegativeIntersection { start, len } => {
                    let end = start
                        .checked_add(len)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    let mut values = Vec::new();
                    values
                        .try_reserve(len)
                        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                    for child in self.children[start..end].iter().copied() {
                        let Some(BuiltValue::Negative(value)) = self.output[child].take() else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        values.push(value);
                    }
                    BuiltValue::Negative(F5cNegative::Intersection(values))
                }
                NodeKind::NegativeFunction { start } => {
                    let argument_id = self.children[start];
                    let result_id = self.children[start + 1];
                    let Some(BuiltValue::Positive(argument)) = self.output[argument_id].take()
                    else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    let Some(BuiltValue::Negative(result)) = self.output[result_id].take() else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    BuiltValue::Negative(F5cNegative::Function {
                        argument: Box::new(argument),
                        argument_effect: super::F5cPositiveEffect::Bottom,
                        result_effect: super::F5cNegativeEffect::Empty,
                        result: Box::new(result),
                    })
                }
            };
            self.output[id] = Some(built);
        }
        for root in &self.roots {
            let Some(value) = self.output[root.node].take() else {
                return Err(SolveAvailabilityError::IdentityExhausted);
            };
            match (root.location, value) {
                (RootLocation::Predicate(draft), BuiltValue::Positive(value)) => {
                    drafts[draft].predicate = value;
                }
                (RootLocation::Lower(draft, bound), BuiltValue::Positive(value)) => {
                    drafts[draft].recursive_bounds[bound].lower = value;
                }
                (RootLocation::Upper(draft, bound), BuiltValue::Negative(value)) => {
                    drafts[draft].recursive_bounds[bound].upper = value;
                }
                _ => return Err(SolveAvailabilityError::IdentityExhausted),
            }
        }
        Ok(())
    }
}

fn discriminator(kind: NodeKind) -> u32 {
    match kind {
        NodeKind::PositiveBottom => 0,
        NodeKind::PositiveInt => 1,
        NodeKind::PositiveQuantified(_) => 2,
        NodeKind::PositiveRecursive(_) => 3,
        NodeKind::PositiveUnion { .. } => 4,
        NodeKind::PositiveFunction { .. } => 5,
        NodeKind::NegativeTop => 6,
        NodeKind::NegativeBottom => 7,
        NodeKind::NegativeInt => 8,
        NodeKind::NegativeQuantified(_) => 9,
        NodeKind::NegativeRecursive(_) => 10,
        NodeKind::NegativeIntersection { .. } => 11,
        NodeKind::NegativeFunction { .. } => 12,
    }
}

fn compare_words(
    left: &[u32],
    right: &[u32],
    comparisons: &mut usize,
) -> Result<Ordering, SolveAvailabilityError> {
    for (left, right) in left.iter().zip(right) {
        *comparisons = comparisons
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        match left.cmp(right) {
            Ordering::Equal => {}
            order => return Ok(order),
        }
    }
    Ok(left.len().cmp(&right.len()))
}

fn compare_key_ids(
    nodes: &[Node],
    stats: &mut NormalizationStats,
    left: NodeId,
    right: NodeId,
) -> Result<Ordering, SolveAvailabilityError> {
    let left = nodes
        .get(left)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let right = nodes
        .get(right)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    stats.word_comparisons = stats
        .word_comparisons
        .checked_add(1)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    match left.height.cmp(&right.height) {
        Ordering::Equal => {
            stats.word_comparisons = stats
                .word_comparisons
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            Ok(left.rank.cmp(&right.rank))
        }
        ordering => Ok(ordering),
    }
}

fn compare_descriptors(
    nodes: &[Node],
    words: &[u32],
    stats: &mut NormalizationStats,
    left: NodeId,
    right: NodeId,
) -> Result<Ordering, SolveAvailabilityError> {
    let left = nodes
        .get(left)
        .and_then(|node| node.descriptor)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let right = nodes
        .get(right)
        .and_then(|node| node.descriptor)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let left_end = left
        .0
        .checked_add(left.1)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let right_end = right
        .0
        .checked_add(right.1)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    compare_words(
        words
            .get(left.0..left_end)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        words
            .get(right.0..right_end)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        &mut stats.word_comparisons,
    )
}

fn descriptor_radix_symbol(
    nodes: &[Node],
    words: &[u32],
    node_id: NodeId,
    byte: usize,
) -> Result<usize, SolveAvailabilityError> {
    let (start, len) = nodes
        .get(node_id)
        .and_then(|node| node.descriptor)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let byte_len = len
        .checked_mul(std::mem::size_of::<u32>())
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    if byte >= byte_len {
        return Ok(0);
    }
    let word_offset = byte / std::mem::size_of::<u32>();
    let byte_in_word = byte % std::mem::size_of::<u32>();
    let word_index = start
        .checked_add(word_offset)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let word = *words
        .get(word_index)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let shift = (std::mem::size_of::<u32>() - byte_in_word - 1)
        .checked_mul(u8::BITS as usize)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let byte_value = usize::try_from((word >> shift) & u32::from(u8::MAX))
        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
    byte_value
        .checked_add(1)
        .ok_or(SolveAvailabilityError::IdentityExhausted)
}

fn key_id_radix_symbol(
    nodes: &[Node],
    node_id: NodeId,
    byte: usize,
) -> Result<usize, SolveAvailabilityError> {
    let node = nodes
        .get(node_id)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let word = match byte / std::mem::size_of::<u32>() {
        0 => node.height,
        1 => node.rank,
        _ => return Err(SolveAvailabilityError::IdentityExhausted),
    };
    let byte_in_word = byte % std::mem::size_of::<u32>();
    let shift = (std::mem::size_of::<u32>() - byte_in_word - 1)
        .checked_mul(u8::BITS as usize)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let byte_value = usize::try_from((word >> shift) & u32::from(u8::MAX))
        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
    byte_value
        .checked_add(1)
        .ok_or(SolveAvailabilityError::IdentityExhausted)
}

fn compare_radix_keys(
    left: NodeId,
    right: NodeId,
    fixed_byte_len: Option<usize>,
    symbol_for: &mut impl FnMut(NodeId, usize) -> Result<usize, SolveAvailabilityError>,
) -> Result<Ordering, SolveAvailabilityError> {
    let mut byte = 0usize;
    loop {
        let left_symbol = symbol_for(left, byte)?;
        let right_symbol = symbol_for(right, byte)?;
        match left_symbol.cmp(&right_symbol) {
            Ordering::Equal => {}
            ordering => return Ok(ordering),
        }
        if left_symbol == 0
            || fixed_byte_len
                .is_some_and(|limit| byte.checked_add(1).is_some_and(|next| next >= limit))
        {
            return Ok(Ordering::Equal);
        }
        byte = byte
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    }
}

fn radix_sort_node_ids(
    values: &mut [NodeId],
    fixed_byte_len: Option<usize>,
    workspace: Option<&mut [usize]>,
    frames: &mut Vec<RadixFrame>,
    stats: &mut NormalizationStats,
    mut symbol_for: impl FnMut(NodeId, usize) -> Result<usize, SolveAvailabilityError>,
) -> Result<(), SolveAvailabilityError> {
    if values.len() < 2 {
        return Err(SolveAvailabilityError::IdentityExhausted);
    }
    if values.len() <= RADIX_INSERTION_LIMIT {
        for index in 1..values.len() {
            let value = values[index];
            let mut destination = index;
            while destination > 0
                && compare_radix_keys(
                    value,
                    values[destination - 1],
                    fixed_byte_len,
                    &mut symbol_for,
                )? == Ordering::Less
            {
                values[destination] = values[destination - 1];
                destination -= 1;
            }
            values[destination] = value;
        }
        return Ok(());
    }
    let workspace = workspace.ok_or(SolveAvailabilityError::IdentityExhausted)?;
    if workspace.len() != RADIX_WORKSPACE_SLOTS {
        return Err(SolveAvailabilityError::IdentityExhausted);
    }
    let (counts, rest) = workspace.split_at_mut(RADIX_ALPHABET);
    let (starts, cursors) = rest.split_at_mut(RADIX_ALPHABET);
    frames.clear();
    Normalizer::push(
        frames,
        RadixFrame {
            start: 0,
            end: values.len(),
            byte: 0,
        },
        Lane::RadixFrames,
        stats,
    )?;

    while let Some(frame) = frames.pop() {
        let frame_len = frame
            .end
            .checked_sub(frame.start)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        if frame.end > values.len() {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        if frame_len < 2 {
            continue;
        }
        counts.fill(0);
        for node_id in &values[frame.start..frame.end] {
            let symbol = symbol_for(*node_id, frame.byte)?;
            let count = counts
                .get_mut(symbol)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            *count = count
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        }
        let mut next_start = frame.start;
        for symbol in 0..RADIX_ALPHABET {
            starts[symbol] = next_start;
            cursors[symbol] = next_start;
            next_start = next_start
                .checked_add(counts[symbol])
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        }
        if next_start != frame.end {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        for symbol in 0..RADIX_ALPHABET {
            let bucket_end = starts[symbol]
                .checked_add(counts[symbol])
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            while cursors[symbol] < bucket_end {
                let position = cursors[symbol];
                let node_id = *values
                    .get(position)
                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                let destination = symbol_for(node_id, frame.byte)?;
                if destination >= RADIX_ALPHABET {
                    return Err(SolveAvailabilityError::IdentityExhausted);
                }
                if destination == symbol {
                    cursors[symbol] = position
                        .checked_add(1)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                } else {
                    let destination_end = starts[destination]
                        .checked_add(counts[destination])
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    let destination_cursor = cursors[destination];
                    if destination_cursor >= destination_end {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    }
                    values.swap(position, destination_cursor);
                    cursors[destination] = destination_cursor
                        .checked_add(1)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                }
            }
        }

        let next_byte = frame
            .byte
            .checked_add(1)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        if fixed_byte_len.is_some_and(|limit| next_byte >= limit) {
            continue;
        }
        for symbol in (1..RADIX_ALPHABET).rev() {
            let bucket_len = counts[symbol];
            if bucket_len < 2 {
                continue;
            }
            Normalizer::push(
                frames,
                RadixFrame {
                    start: starts[symbol],
                    end: starts[symbol]
                        .checked_add(bucket_len)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?,
                    byte: next_byte,
                },
                Lane::RadixFrames,
                stats,
            )?;
        }
    }
    Ok(())
}

fn stable_merge_sort<T: Copy>(
    values: &mut [T],
    scratch: &mut [T],
    compare: &mut impl FnMut(T, T) -> Result<Ordering, SolveAvailabilityError>,
) -> Result<(), SolveAvailabilityError> {
    if values.len() != scratch.len() {
        return Err(SolveAvailabilityError::IdentityExhausted);
    }
    if values.len() < 2 {
        return Ok(());
    }
    let middle = values.len() / 2;
    let (left, right) = values.split_at_mut(middle);
    let (left_scratch, right_scratch) = scratch.split_at_mut(middle);
    stable_merge_sort(left, left_scratch, compare)?;
    stable_merge_sort(right, right_scratch, compare)?;
    let (left, right) = values.split_at(middle);
    let mut left_index = 0;
    let mut right_index = 0;
    let mut output_index = 0;
    while left_index < left.len() && right_index < right.len() {
        if compare(left[left_index], right[right_index])? != Ordering::Greater {
            scratch[output_index] = left[left_index];
            left_index += 1;
        } else {
            scratch[output_index] = right[right_index];
            right_index += 1;
        }
        output_index += 1;
    }
    while left_index < left.len() {
        scratch[output_index] = left[left_index];
        left_index += 1;
        output_index += 1;
    }
    while right_index < right.len() {
        scratch[output_index] = right[right_index];
        right_index += 1;
        output_index += 1;
    }
    values.copy_from_slice(scratch);
    Ok(())
}

pub(super) fn normalize_component(
    drafts: &mut [GeneralizationDraft],
) -> Result<NormalizationStats, SolveAvailabilityError> {
    let mut normalizer = Normalizer::new();
    normalizer.collect_drafts(drafts)?;
    normalizer.rank_all()?;
    normalizer.rebuild(drafts)?;
    #[cfg(test)]
    let (physical_lane_capacities, physical_lane_slot_sizes) = normalizer.physical_lane_snapshot();
    let mut stats = normalizer.stats.clone();
    #[cfg(test)]
    {
        stats.physical_lane_capacities = physical_lane_capacities;
        stats.physical_lane_slot_sizes = physical_lane_slot_sizes;
    }
    stats.index_actual_capacity = 0;
    stats.index_retained_bytes = 0;
    for lane in &mut stats.index_lanes {
        lane.actual_capacity = 0;
        lane.retained_bytes = 0;
    }
    Ok(stats)
}

/// Normalize a producer-owned topological flat graph without creating boxed values.
/// Each input node may refer only to nodes already inserted in its polarity array.
#[allow(dead_code)]
pub(super) fn normalize_flat(
    input: &FlatDraft,
) -> Result<(FlatDraft, FlatNormalizationStats), SolveAvailabilityError> {
    let bad = SolveAvailabilityError::IdentityExhausted;
    let mut normalizer = Normalizer::new();
    let mut positives = Vec::new();
    let mut negatives = Vec::new();
    positives
        .try_reserve(input.positive_nodes.len())
        .map_err(|_| bad)?;
    negatives
        .try_reserve(input.negative_nodes.len())
        .map_err(|_| bad)?;
    let mut children = Vec::new();
    for reference in &input.insertion_order {
        children.clear();
        match *reference {
            NodeRef::Positive(source_id) => {
                let source_index = usize::try_from(source_id.0).map_err(|_| bad)?;
                if source_index != positives.len() {
                    return Err(bad);
                }
                let node = input.positive_nodes.get(source_index).ok_or(bad)?;
                let kind = match *node {
                    PositiveNode::Bottom => NodeKind::PositiveBottom,
                    PositiveNode::Int => NodeKind::PositiveInt,
                    PositiveNode::Variable(_) => return Err(bad),
                    PositiveNode::Quantified(n) => NodeKind::PositiveQuantified(n),
                    PositiveNode::Recursive(n) => NodeKind::PositiveRecursive(n),
                    PositiveNode::Union(span) => {
                        let start = usize::try_from(span.start).map_err(|_| bad)?;
                        let end = start
                            .checked_add(usize::try_from(span.len).map_err(|_| bad)?)
                            .ok_or(bad)?;
                        let slice = input.positive_children.get(start..end).ok_or(bad)?;
                        children.try_reserve(slice.len()).map_err(|_| bad)?;
                        for id in slice {
                            children.push(
                                *positives
                                    .get(usize::try_from(id.0).map_err(|_| bad)?)
                                    .ok_or(bad)?,
                            );
                        }
                        NodeKind::PositiveUnion { start: 0, len: 0 }
                    }
                    PositiveNode::Function { argument, result } => {
                        let a = *negatives
                            .get(usize::try_from(argument.0).map_err(|_| bad)?)
                            .ok_or(bad)?;
                        let r = *positives
                            .get(usize::try_from(result.0).map_err(|_| bad)?)
                            .ok_or(bad)?;
                        children.try_reserve(2).map_err(|_| bad)?;
                        children.extend_from_slice(&[a, r]);
                        NodeKind::PositiveFunction { start: 0 }
                    }
                };
                positives.push(normalizer.push_node(kind, &children)?);
            }
            NodeRef::Negative(source_id) => {
                let source_index = usize::try_from(source_id.0).map_err(|_| bad)?;
                if source_index != negatives.len() {
                    return Err(bad);
                }
                let node = input.negative_nodes.get(source_index).ok_or(bad)?;
                let kind = match *node {
                    NegativeNode::Top => NodeKind::NegativeTop,
                    NegativeNode::Bottom => NodeKind::NegativeBottom,
                    NegativeNode::Int => NodeKind::NegativeInt,
                    NegativeNode::Variable(_) => return Err(bad),
                    NegativeNode::Quantified(n) => NodeKind::NegativeQuantified(n),
                    NegativeNode::Recursive(n) => NodeKind::NegativeRecursive(n),
                    NegativeNode::Intersection(span) => {
                        let start = usize::try_from(span.start).map_err(|_| bad)?;
                        let end = start
                            .checked_add(usize::try_from(span.len).map_err(|_| bad)?)
                            .ok_or(bad)?;
                        let slice = input.negative_children.get(start..end).ok_or(bad)?;
                        children.try_reserve(slice.len()).map_err(|_| bad)?;
                        for id in slice {
                            children.push(
                                *negatives
                                    .get(usize::try_from(id.0).map_err(|_| bad)?)
                                    .ok_or(bad)?,
                            );
                        }
                        NodeKind::NegativeIntersection { start: 0, len: 0 }
                    }
                    NegativeNode::Function { argument, result } => {
                        let a = *positives
                            .get(usize::try_from(argument.0).map_err(|_| bad)?)
                            .ok_or(bad)?;
                        let r = *negatives
                            .get(usize::try_from(result.0).map_err(|_| bad)?)
                            .ok_or(bad)?;
                        children.try_reserve(2).map_err(|_| bad)?;
                        children.extend_from_slice(&[a, r]);
                        NodeKind::NegativeFunction { start: 0 }
                    }
                };
                negatives.push(normalizer.push_node(kind, &children)?);
            }
        }
    }
    if positives.len() != input.positive_nodes.len()
        || negatives.len() != input.negative_nodes.len()
    {
        return Err(bad);
    }
    let predicate = *positives
        .get(usize::try_from(input.predicate.ok_or(bad)?.0).map_err(|_| bad)?)
        .ok_or(bad)?;
    let mut roots = Vec::new();
    roots
        .try_reserve(
            input
                .recursive_bounds
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(bad)?,
        )
        .map_err(|_| bad)?;
    roots.push(predicate);
    for bound in &input.recursive_bounds {
        roots.push(
            *positives
                .get(usize::try_from(bound.lower.0).map_err(|_| bad)?)
                .ok_or(bad)?,
        );
        roots.push(
            *negatives
                .get(usize::try_from(bound.upper.0).map_err(|_| bad)?)
                .ok_or(bad)?,
        );
    }
    normalizer.rank_all()?;

    let mut output = FlatDraft {
        quantifier_count: input.quantifier_count,
        ..FlatDraft::default()
    };
    let mut mapped = Vec::new();
    mapped
        .try_reserve(normalizer.nodes.len())
        .map_err(|_| bad)?;
    mapped.resize(normalizer.nodes.len(), None::<BuiltRef>);
    let mut work = Vec::new();
    let mut positive_scratch = Vec::new();
    let mut negative_scratch = Vec::new();
    for &root in &roots {
        work.try_reserve(1).map_err(|_| bad)?;
        work.push((root, false));
        while let Some((id, ready)) = work.pop() {
            if mapped[id].is_some() {
                continue;
            }
            let kind = normalizer.nodes[id].kind;
            if !ready {
                work.try_reserve(1).map_err(|_| bad)?;
                work.push((id, true));
                let (start, len) = match kind {
                    NodeKind::PositiveUnion { start, len }
                    | NodeKind::NegativeIntersection { start, len } => (start, len),
                    NodeKind::PositiveFunction { start } | NodeKind::NegativeFunction { start } => {
                        (start, 2)
                    }
                    _ => (0, 0),
                };
                let end = start.checked_add(len).ok_or(bad)?;
                for &child in normalizer.children.get(start..end).ok_or(bad)?.iter().rev() {
                    if mapped[child].is_none() {
                        work.try_reserve(1).map_err(|_| bad)?;
                        work.push((child, false));
                    }
                }
                continue;
            }
            let positive = |id: usize| match mapped.get(id).copied().flatten() {
                Some(BuiltRef::Positive(n)) => u32::try_from(n).ok().map(PositiveId),
                _ => None,
            };
            let negative = |id: usize| match mapped.get(id).copied().flatten() {
                Some(BuiltRef::Negative(n)) => u32::try_from(n).ok().map(NegativeId),
                _ => None,
            };
            mapped[id] = Some(match kind {
                NodeKind::PositiveBottom => BuiltRef::Positive(
                    usize::try_from(output.positive(PositiveNode::Bottom)?.0).map_err(|_| bad)?,
                ),
                NodeKind::PositiveInt => BuiltRef::Positive(
                    usize::try_from(output.positive(PositiveNode::Int)?.0).map_err(|_| bad)?,
                ),
                NodeKind::PositiveQuantified(n) => BuiltRef::Positive(
                    usize::try_from(output.positive(PositiveNode::Quantified(n))?.0)
                        .map_err(|_| bad)?,
                ),
                NodeKind::PositiveRecursive(n) => BuiltRef::Positive(
                    usize::try_from(output.positive(PositiveNode::Recursive(n))?.0)
                        .map_err(|_| bad)?,
                ),
                NodeKind::NegativeTop => BuiltRef::Negative(
                    usize::try_from(output.negative(NegativeNode::Top)?.0).map_err(|_| bad)?,
                ),
                NodeKind::NegativeBottom => BuiltRef::Negative(
                    usize::try_from(output.negative(NegativeNode::Bottom)?.0).map_err(|_| bad)?,
                ),
                NodeKind::NegativeInt => BuiltRef::Negative(
                    usize::try_from(output.negative(NegativeNode::Int)?.0).map_err(|_| bad)?,
                ),
                NodeKind::NegativeQuantified(n) => BuiltRef::Negative(
                    usize::try_from(output.negative(NegativeNode::Quantified(n))?.0)
                        .map_err(|_| bad)?,
                ),
                NodeKind::NegativeRecursive(n) => BuiltRef::Negative(
                    usize::try_from(output.negative(NegativeNode::Recursive(n))?.0)
                        .map_err(|_| bad)?,
                ),
                NodeKind::PositiveUnion { start, len } => {
                    let end = start.checked_add(len).ok_or(bad)?;
                    positive_scratch.clear();
                    positive_scratch.try_reserve(len).map_err(|_| bad)?;
                    for &child in normalizer.children.get(start..end).ok_or(bad)? {
                        positive_scratch.push(positive(child).ok_or(bad)?);
                    }
                    let span = output.positive_span(&positive_scratch)?;
                    BuiltRef::Positive(
                        usize::try_from(output.positive(PositiveNode::Union(span))?.0)
                            .map_err(|_| bad)?,
                    )
                }
                NodeKind::NegativeIntersection { start, len } => {
                    let end = start.checked_add(len).ok_or(bad)?;
                    negative_scratch.clear();
                    negative_scratch.try_reserve(len).map_err(|_| bad)?;
                    for &child in normalizer.children.get(start..end).ok_or(bad)? {
                        negative_scratch.push(negative(child).ok_or(bad)?);
                    }
                    let span = output.negative_span(&negative_scratch)?;
                    BuiltRef::Negative(
                        usize::try_from(output.negative(NegativeNode::Intersection(span))?.0)
                            .map_err(|_| bad)?,
                    )
                }
                NodeKind::PositiveFunction { start } => {
                    let argument =
                        negative(*normalizer.children.get(start).ok_or(bad)?).ok_or(bad)?;
                    let result = positive(
                        *normalizer
                            .children
                            .get(start.checked_add(1).ok_or(bad)?)
                            .ok_or(bad)?,
                    )
                    .ok_or(bad)?;
                    BuiltRef::Positive(
                        usize::try_from(
                            output
                                .positive(PositiveNode::Function { argument, result })?
                                .0,
                        )
                        .map_err(|_| bad)?,
                    )
                }
                NodeKind::NegativeFunction { start } => {
                    let argument =
                        positive(*normalizer.children.get(start).ok_or(bad)?).ok_or(bad)?;
                    let result = negative(
                        *normalizer
                            .children
                            .get(start.checked_add(1).ok_or(bad)?)
                            .ok_or(bad)?,
                    )
                    .ok_or(bad)?;
                    BuiltRef::Negative(
                        usize::try_from(
                            output
                                .negative(NegativeNode::Function { argument, result })?
                                .0,
                        )
                        .map_err(|_| bad)?,
                    )
                }
            });
        }
    }
    let map_positive = |id: usize| match mapped[id] {
        Some(BuiltRef::Positive(n)) => u32::try_from(n).ok().map(PositiveId),
        _ => None,
    };
    let map_negative = |id: usize| match mapped[id] {
        Some(BuiltRef::Negative(n)) => u32::try_from(n).ok().map(NegativeId),
        _ => None,
    };
    output.predicate = Some(map_positive(roots[0]).ok_or(bad)?);
    for (bound, endpoints) in input
        .recursive_bounds
        .iter()
        .zip(roots[1..].chunks_exact(2))
    {
        output.bound(RecursiveBound {
            ordinal: bound.ordinal,
            lower: map_positive(endpoints[0]).ok_or(bad)?,
            upper: map_negative(endpoints[1]).ok_or(bad)?,
        })?;
    }
    Ok((output, FlatNormalizationStats::from(&normalizer.stats)))
}

#[cfg(test)]
mod flat_variable_tests {
    use super::*;

    #[test]
    fn closed_normalizer_rejects_both_variable_polarities() {
        let mut positive = FlatDraft::default();
        positive.predicate = Some(positive.positive(PositiveNode::Variable(4)).unwrap());
        assert!(matches!(
            normalize_flat(&positive),
            Err(SolveAvailabilityError::IdentityExhausted)
        ));

        let mut negative = FlatDraft::default();
        negative.predicate = Some(negative.positive(PositiveNode::Bottom).unwrap());
        negative.negative(NegativeNode::Variable(4)).unwrap();
        assert!(matches!(
            normalize_flat(&negative),
            Err(SolveAvailabilityError::IdentityExhausted)
        ));
    }
}

#[cfg(test)]
mod flat_tests {
    use super::*;

    #[test]
    fn repeated_summary_occurrences_match_boxed_normalization() {
        use super::super::f5c_materialization::materialize_summary_flat;
        use super::super::{
            F5cComponentExpansionMemo, F5cNegativeEffect, F5cPositiveEffect, F5cSummaryNode,
            F5cSummaryNodeId, F5cSummaryNodeKind, Polarity,
        };

        let ids = (0..5).map(F5cSummaryNodeId).collect::<Vec<_>>();
        let kinds = [
            F5cSummaryNodeKind::PositiveInt,
            F5cSummaryNodeKind::NegativeInt,
            F5cSummaryNodeKind::NegativeIntersection { start: 0, len: 2 },
            F5cSummaryNodeKind::PositiveFunction {
                argument: ids[2],
                result: ids[0],
            },
            F5cSummaryNodeKind::PositiveUnion { start: 2, len: 2 },
        ];
        let mut memo = F5cComponentExpansionMemo::default();
        memo.nodes = kinds
            .into_iter()
            .map(|kind| F5cSummaryNode {
                incidence: None,
                transitive_incidence_count: 0,
                kind,
            })
            .collect();
        memo.children = vec![ids[1], ids[1], ids[3], ids[3]];

        let mut flat = FlatDraft::default();
        let NodeRef::Positive(root) =
            materialize_summary_flat(&memo, &mut flat, ids[4], Polarity::Positive, |_, _| {})
                .unwrap()
        else {
            panic!("wrong root polarity");
        };
        flat.predicate = Some(root);
        let mut boxed = [GeneralizationDraft {
            quantifier_count: 0,
            predicate: memo.positive_value(ids[4]).unwrap(),
            recursive_bounds: vec![],
        }];
        let (normalized, flat_stats) = normalize_flat(&flat).unwrap();
        let boxed_stats = normalize_component(&mut boxed).unwrap();
        let expected = F5cPositive::Union(vec![F5cPositive::Function {
            argument: Box::new(F5cNegative::Intersection(vec![F5cNegative::Int])),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(F5cPositive::Int),
        }]);
        assert_eq!(boxed[0].predicate, expected);
        assert_eq!(
            normalized.positive_nodes,
            [
                PositiveNode::Int,
                PositiveNode::Function {
                    argument: NegativeId(1),
                    result: PositiveId(0)
                },
                PositiveNode::Union(super::super::f5c_draft::ChildSpan { start: 0, len: 1 }),
            ]
        );
        assert_eq!(
            normalized.negative_nodes,
            [
                NegativeNode::Int,
                NegativeNode::Intersection(super::super::f5c_draft::ChildSpan { start: 0, len: 1 }),
            ]
        );
        assert_eq!(normalized.positive_children, [PositiveId(1)]);
        assert_eq!(normalized.negative_children, [NegativeId(0)]);
        assert_eq!(normalized.predicate, Some(PositiveId(2)));
        assert_eq!(flat_stats.key_writes, boxed_stats.key_writes);
        assert_eq!(flat_stats.child_comparisons, boxed_stats.child_comparisons);
        assert_eq!(flat_stats.descriptor_words, boxed_stats.descriptor_words);
        assert_eq!(flat_stats.word_comparisons, boxed_stats.word_comparisons);
        assert_eq!(flat_stats.duplicates, boxed_stats.duplicates);
    }

    #[test]
    fn flat_compound_tree_matches_boxed_normalization_counters() {
        let mut flat = FlatDraft::default();
        let negative_function_argument = flat.positive(PositiveNode::Int).unwrap();
        let negative_function_result = flat.negative(NegativeNode::Int).unwrap();
        let negative_function = flat
            .negative(NegativeNode::Function {
                argument: negative_function_argument,
                result: negative_function_result,
            })
            .unwrap();
        let top = flat.negative(NegativeNode::Top).unwrap();
        let duplicate_int_a = flat.negative(NegativeNode::Int).unwrap();
        let duplicate_int_b = flat.negative(NegativeNode::Int).unwrap();
        let argument_children = flat
            .negative_span(&[negative_function, top, duplicate_int_a, duplicate_int_b])
            .unwrap();
        let argument = flat
            .negative(NegativeNode::Intersection(argument_children))
            .unwrap();
        let result = flat.positive(PositiveNode::Bottom).unwrap();
        let function = flat
            .positive(PositiveNode::Function { argument, result })
            .unwrap();
        let union_int = flat.positive(PositiveNode::Int).unwrap();
        let union_bottom = flat.positive(PositiveNode::Bottom).unwrap();
        let union_children = flat
            .positive_span(&[function, union_int, union_bottom])
            .unwrap();
        let predicate = flat.positive(PositiveNode::Union(union_children)).unwrap();
        flat.predicate = Some(predicate);
        let (_, flat_stats) = normalize_flat(&flat).unwrap();
        let mut old = [GeneralizationDraft {
            quantifier_count: 0,
            predicate: F5cPositive::Union(vec![
                F5cPositive::Function {
                    argument: Box::new(F5cNegative::Intersection(vec![
                        F5cNegative::Function {
                            argument: Box::new(F5cPositive::Int),
                            argument_effect: super::super::F5cPositiveEffect::Bottom,
                            result_effect: super::super::F5cNegativeEffect::Empty,
                            result: Box::new(F5cNegative::Int),
                        },
                        F5cNegative::Top,
                        F5cNegative::Int,
                        F5cNegative::Int,
                    ])),
                    argument_effect: super::super::F5cNegativeEffect::Empty,
                    result_effect: super::super::F5cPositiveEffect::Bottom,
                    result: Box::new(F5cPositive::Bottom),
                },
                F5cPositive::Int,
                F5cPositive::Bottom,
            ]),
            recursive_bounds: vec![],
        }];
        let boxed_stats = normalize_component(&mut old).unwrap();
        assert_eq!(flat_stats.key_writes, boxed_stats.key_writes);
        assert_eq!(flat_stats.child_comparisons, boxed_stats.child_comparisons);
        assert_eq!(flat_stats.descriptor_words, boxed_stats.descriptor_words);
        assert_eq!(flat_stats.word_comparisons, boxed_stats.word_comparisons);
        assert_eq!(flat_stats.duplicates, boxed_stats.duplicates);
    }

    #[test]
    fn flat_normalization_preserves_order_counters_sharing_and_bound_roots() {
        let mut flat = FlatDraft::default();
        let int = flat.positive(PositiveNode::Int).unwrap();
        let bottom = flat.positive(PositiveNode::Bottom).unwrap();
        let top = flat.negative(NegativeNode::Top).unwrap();
        let nint = flat.negative(NegativeNode::Int).unwrap();
        let nfunction = flat
            .negative(NegativeNode::Function {
                argument: int,
                result: nint,
            })
            .unwrap();
        let nspan = flat.negative_span(&[nfunction, nint, top, nint]).unwrap();
        let intersection = flat.negative(NegativeNode::Intersection(nspan)).unwrap();
        let function = flat
            .positive(PositiveNode::Function {
                argument: intersection,
                result: int,
            })
            .unwrap();
        let duplicate_function = flat
            .positive(PositiveNode::Function {
                argument: intersection,
                result: int,
            })
            .unwrap();
        let input_union_span = flat
            .positive_span(&[function, bottom, int, duplicate_function])
            .unwrap();
        let predicate = flat
            .positive(PositiveNode::Union(input_union_span))
            .unwrap();
        flat.predicate = Some(predicate);
        flat.bound(RecursiveBound {
            ordinal: 0,
            lower: function,
            upper: intersection,
        })
        .unwrap();
        flat.bound(RecursiveBound {
            ordinal: 1,
            lower: int,
            upper: nfunction,
        })
        .unwrap();
        let (normalized, stats) = normalize_flat(&flat).unwrap();
        assert_eq!(normalized.predicate, Some(PositiveId(3)));
        assert_eq!(
            normalized.positive_nodes,
            [
                PositiveNode::Bottom,
                PositiveNode::Int,
                PositiveNode::Function {
                    argument: NegativeId(3),
                    result: PositiveId(1)
                },
                PositiveNode::Union(super::super::f5c_draft::ChildSpan { start: 0, len: 3 }),
            ]
        );
        assert_eq!(
            normalized.negative_nodes,
            [
                NegativeNode::Top,
                NegativeNode::Int,
                NegativeNode::Function {
                    argument: PositiveId(1),
                    result: NegativeId(1)
                },
                NegativeNode::Intersection(super::super::f5c_draft::ChildSpan { start: 0, len: 3 }),
            ]
        );
        assert_eq!(
            normalized.positive_children,
            [PositiveId(0), PositiveId(1), PositiveId(2)]
        );
        assert_eq!(
            normalized.negative_children,
            [NegativeId(0), NegativeId(1), NegativeId(2)]
        );
        assert_eq!(
            normalized.recursive_bounds,
            [
                RecursiveBound {
                    ordinal: 0,
                    lower: PositiveId(2),
                    upper: NegativeId(3)
                },
                RecursiveBound {
                    ordinal: 1,
                    lower: PositiveId(1),
                    upper: NegativeId(2)
                },
            ]
        );
        assert_eq!(stats.duplicates, 2);
        assert_eq!(normalized.positive_nodes.len(), 4);
        assert_eq!(normalized.negative_nodes.len(), 4);
        assert!(flat.positive_nodes.len() > normalized.positive_nodes.len());
        let PositiveNode::Union(span) =
            normalized.positive_nodes[normalized.predicate.unwrap().0 as usize]
        else {
            panic!("union root")
        };
        assert_eq!(span.len, 3);
        let first = normalized.positive_children[span.start as usize];
        let second = normalized.positive_children[span.start as usize + 2];
        assert_eq!(
            normalized.positive_nodes[first.0 as usize],
            PositiveNode::Bottom
        );
        assert_eq!(second, normalized.recursive_bounds[0].lower);
        let PositiveNode::Function { argument, .. } = normalized.positive_nodes[second.0 as usize]
        else {
            panic!("shared function")
        };
        assert_eq!(argument, normalized.recursive_bounds[0].upper);
        assert_eq!(normalized.recursive_bounds[0].ordinal, 0);

        let start = usize::try_from(input_union_span.start).unwrap();
        let end = start + usize::try_from(input_union_span.len).unwrap();
        flat.positive_children[start..end].reverse();
        flat.recursive_bounds.reverse();
        let (_, permuted_stats) = normalize_flat(&flat).unwrap();
        assert_eq!(stats, permuted_stats);
    }

    #[test]
    fn flat_rejects_swapped_and_duplicate_source_ids() {
        let mut flat = FlatDraft::default();
        let int = flat.positive(PositiveNode::Int).unwrap();
        let bottom = flat.positive(PositiveNode::Bottom).unwrap();
        let span = flat.positive_span(&[int, bottom]).unwrap();
        let predicate = flat.positive(PositiveNode::Union(span)).unwrap();
        flat.predicate = Some(predicate);
        let (valid, _) = normalize_flat(&flat).unwrap();
        assert_eq!(
            valid.positive_nodes[valid.predicate.unwrap().0 as usize],
            PositiveNode::Union(super::super::f5c_draft::ChildSpan { start: 0, len: 2 })
        );

        flat.insertion_order.swap(0, 1);
        assert!(matches!(
            normalize_flat(&flat),
            Err(SolveAvailabilityError::IdentityExhausted)
        ));
        flat.insertion_order[0] = NodeRef::Positive(int);
        flat.insertion_order[1] = NodeRef::Positive(int);
        assert!(matches!(
            normalize_flat(&flat),
            Err(SolveAvailabilityError::IdentityExhausted)
        ));
        assert_eq!(bottom, PositiveId(1));
    }
}

pub(super) fn record_production_counters(
    stats: &NormalizationStats,
    counters: &mut super::ProductionCounters,
) -> Result<(), SolveAvailabilityError> {
    let mut next = counters.clone();
    next.closed_normalized_key_writes = next
        .closed_normalized_key_writes
        .checked_add(stats.key_writes)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    next.closed_normalization_child_comparisons = next
        .closed_normalization_child_comparisons
        .checked_add(stats.child_comparisons)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    next.closed_normalization_descriptor_words = next
        .closed_normalization_descriptor_words
        .checked_add(stats.descriptor_words)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    next.closed_normalization_word_comparisons = next
        .closed_normalization_word_comparisons
        .checked_add(stats.word_comparisons)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    next.closed_normalization_index_requested_slots = next
        .closed_normalization_index_requested_slots
        .checked_add(stats.index_requested_slots)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    next.closed_normalization_index_actual_capacity = stats.index_actual_capacity;
    next.closed_normalization_index_retained_bytes = stats.index_retained_bytes;
    next.closed_normalization_index_peak_bytes = next
        .closed_normalization_index_peak_bytes
        .max(stats.index_peak_bytes);
    next.closed_normalization_index_capacity_growths = next
        .closed_normalization_index_capacity_growths
        .checked_add(stats.index_capacity_growths)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let semantic_peak = next
        .semantic_arena_retained_bytes
        .checked_add(stats.index_peak_bytes)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let session_peak = next
        .inference_session_retained_bytes
        .checked_add(stats.index_peak_bytes)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    next.semantic_arena_peak_bytes = next.semantic_arena_peak_bytes.max(semantic_peak);
    next.inference_session_peak_bytes = next.inference_session_peak_bytes.max(session_peak);
    *counters = next;
    Ok(())
}

#[cfg(test)]
impl super::IndependentResourceLedger {
    pub(super) fn record_closed_normalization_index(
        &mut self,
        stats: &NormalizationStats,
    ) -> Result<(), SolveAvailabilityError> {
        let mut requested_slots = 0usize;
        let mut actual_capacity = 0usize;
        let mut retained_bytes = 0usize;
        let mut capacity_growths = 0usize;
        let mut physical_peak_bytes = 0usize;
        let mut next = self.clone();
        for index in 0..stats.index_lanes.len() {
            let independent = &mut next.closed_normalization_index_lanes[index];
            let measured = stats.index_lanes[index];
            let capacity = stats.physical_lane_capacities[index];
            let slot_size = stats.physical_lane_slot_sizes[index];
            let physical_lane_bytes = capacity
                .checked_mul(slot_size)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            if capacity != measured.peak_capacity
                || slot_size != measured.slot_size
                || physical_lane_bytes != measured.peak_bytes
                || measured.actual_capacity != 0
                || measured.retained_bytes != 0
            {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            independent.requested_slots = independent
                .requested_slots
                .checked_add(measured.requested_slots)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            independent.capacity_growths = independent
                .capacity_growths
                .checked_add(measured.capacity_growths)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            independent.actual_capacity = measured.actual_capacity;
            independent.peak_capacity = independent.peak_capacity.max(capacity);
            independent.slot_size = slot_size;
            independent.retained_bytes = measured.retained_bytes;
            independent.peak_bytes = independent.peak_bytes.max(physical_lane_bytes);
            requested_slots = requested_slots
                .checked_add(measured.requested_slots)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            actual_capacity = actual_capacity
                .checked_add(measured.actual_capacity)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            retained_bytes = retained_bytes
                .checked_add(measured.retained_bytes)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            capacity_growths = capacity_growths
                .checked_add(measured.capacity_growths)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            physical_peak_bytes = physical_peak_bytes
                .checked_add(physical_lane_bytes)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        }
        if requested_slots != stats.index_requested_slots
            || actual_capacity != stats.index_actual_capacity
            || retained_bytes != stats.index_retained_bytes
            || capacity_growths != stats.index_capacity_growths
            || physical_peak_bytes != stats.index_peak_bytes
        {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        next.closed_normalization_index_requested_slots = next
            .closed_normalization_index_requested_slots
            .checked_add(requested_slots)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        next.closed_normalization_index_actual_capacity = actual_capacity;
        next.closed_normalization_index_retained_bytes = retained_bytes;
        next.closed_normalization_index_peak_bytes = next
            .closed_normalization_index_peak_bytes
            .max(stats.index_peak_bytes);
        next.closed_normalization_index_capacity_growths = next
            .closed_normalization_index_capacity_growths
            .checked_add(capacity_growths)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let semantic_peak = next
            .semantic_arena_retained_bytes
            .checked_add(stats.index_peak_bytes)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let session_peak = next
            .inference_session_retained_bytes
            .checked_add(stats.index_peak_bytes)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        next.semantic_arena_peak_bytes = next.semantic_arena_peak_bytes.max(semantic_peak);
        next.inference_session_peak_bytes = next.inference_session_peak_bytes.max(session_peak);
        *self = next;
        Ok(())
    }
}

#[cfg(test)]
pub(super) fn normalize_positive(
    value: F5cPositive,
) -> Result<F5cPositive, SolveAvailabilityError> {
    let mut drafts = [GeneralizationDraft {
        quantifier_count: 0,
        recursive_bounds: Vec::<F5cRecursiveBound>::new(),
        predicate: value,
    }];
    normalize_component(&mut drafts)?;
    Ok(std::mem::replace(
        &mut drafts[0].predicate,
        F5cPositive::Bottom,
    ))
}

#[cfg(test)]
pub(super) fn normalize_negative(
    value: F5cNegative,
) -> Result<F5cNegative, SolveAvailabilityError> {
    let mut drafts = [GeneralizationDraft {
        quantifier_count: 0,
        recursive_bounds: vec![F5cRecursiveBound {
            ordinal: 0,
            lower: F5cPositive::Bottom,
            upper: F5cNegative::Top,
        }],
        predicate: F5cPositive::Bottom,
    }];
    let mut normalizer = Normalizer::new();
    let root = normalizer.flatten_negative(value)?;
    normalizer.add_root(BuiltRef::Negative(root), RootLocation::Upper(0, 0))?;
    normalizer.rank_all()?;
    normalizer.rebuild(&mut drafts)?;
    Ok(std::mem::replace(
        &mut drafts[0].recursive_bounds[0].upper,
        F5cNegative::Top,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{F5cNegativeEffect, F5cPositiveEffect};

    fn positive_function(argument: F5cNegative, result: F5cPositive) -> F5cPositive {
        F5cPositive::Function {
            argument: Box::new(argument),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(result),
        }
    }

    fn negative_function(argument: F5cPositive, result: F5cNegative) -> F5cNegative {
        F5cNegative::Function {
            argument: Box::new(argument),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(result),
        }
    }

    fn draft(predicate: F5cPositive) -> GeneralizationDraft {
        GeneralizationDraft {
            quantifier_count: 0,
            recursive_bounds: Vec::new(),
            predicate,
        }
    }

    fn oracle_compare_words(left: &[u32], right: &[u32], comparisons: &mut usize) -> Ordering {
        for (left_word, right_word) in left.iter().zip(right) {
            *comparisons += 1;
            match left_word.cmp(right_word) {
                Ordering::Equal => {}
                ordering => return ordering,
            }
        }
        left.len().cmp(&right.len())
    }

    fn oracle_merge_sort_words(values: &mut [Vec<u32>], comparisons: &mut usize) {
        if values.len() < 2 {
            return;
        }
        let middle = values.len() / 2;
        oracle_merge_sort_words(&mut values[..middle], comparisons);
        oracle_merge_sort_words(&mut values[middle..], comparisons);

        let mut left = 0;
        let mut right = middle;
        let mut sorted = Vec::with_capacity(values.len());
        while left < middle && right < values.len() {
            if oracle_compare_words(&values[left], &values[right], comparisons) != Ordering::Greater
            {
                sorted.push(values[left].clone());
                left += 1;
            } else {
                sorted.push(values[right].clone());
                right += 1;
            }
        }
        sorted.extend_from_slice(&values[left..middle]);
        sorted.extend_from_slice(&values[right..]);
        values.clone_from_slice(&sorted);
    }

    fn oracle_component_word_comparisons(mut words: Vec<Vec<u32>>) -> usize {
        words.sort();
        let mut comparisons = 0;
        oracle_merge_sort_words(&mut words, &mut comparisons);
        for pair in words.windows(2) {
            oracle_compare_words(&pair[0], &pair[1], &mut comparisons);
        }
        comparisons
    }

    #[test]
    fn positive_mixed_height_members_use_height_before_discriminator() {
        let shallow = positive_function(F5cNegative::Top, F5cPositive::Int);
        let deep = F5cPositive::Union(vec![positive_function(
            F5cNegative::Bottom,
            F5cPositive::Int,
        )]);
        let mut drafts = [draft(F5cPositive::Union(vec![
            deep.clone(),
            shallow.clone(),
        ]))];

        normalize_component(&mut drafts).unwrap();

        let F5cPositive::Union(members) = &drafts[0].predicate else {
            panic!("the normalized root remains a Union");
        };
        assert_eq!(members, &[shallow, deep]);
    }

    #[test]
    fn negative_mixed_height_members_use_height_before_discriminator() {
        let shallow = negative_function(F5cPositive::Bottom, F5cNegative::Top);
        let deep = F5cNegative::Intersection(vec![negative_function(
            F5cPositive::Int,
            F5cNegative::Bottom,
        )]);
        let mut normalizer = Normalizer::new();
        let root = normalizer
            .flatten_negative(F5cNegative::Intersection(vec![
                deep.clone(),
                shallow.clone(),
            ]))
            .unwrap();
        let mut draft = GeneralizationDraft {
            quantifier_count: 0,
            recursive_bounds: vec![F5cRecursiveBound {
                ordinal: 0,
                lower: F5cPositive::Bottom,
                upper: F5cNegative::Top,
            }],
            predicate: F5cPositive::Bottom,
        };
        normalizer
            .add_root(BuiltRef::Negative(root), RootLocation::Upper(0, 0))
            .unwrap();

        normalizer.rank_all().unwrap();
        normalizer
            .rebuild(std::slice::from_mut(&mut draft))
            .unwrap();

        let F5cNegative::Intersection(members) = &draft.recursive_bounds[0].upper else {
            panic!("the normalized root remains an Intersection");
        };
        assert_eq!(members, &[shallow, deep]);
    }

    #[test]
    fn exact_duplicate_members_share_rank_and_are_removed() {
        let shallow = positive_function(F5cNegative::Top, F5cPositive::Int);
        let deep = F5cPositive::Union(vec![positive_function(
            F5cNegative::Bottom,
            F5cPositive::Int,
        )]);
        let mut drafts = [draft(F5cPositive::Union(vec![
            deep.clone(),
            shallow.clone(),
            shallow.clone(),
        ]))];

        let stats = normalize_component(&mut drafts).unwrap();

        let F5cPositive::Union(members) = &drafts[0].predicate else {
            panic!("the normalized root remains a Union");
        };
        assert_eq!(members, &[shallow, deep]);
        assert_eq!(stats.duplicates, 1);
        assert_eq!(stats.key_writes, 11);
        assert_eq!(stats.descriptor_words, 31);
        assert!(stats.word_comparisons > 0);
        assert!(stats.child_comparisons > 0);
    }

    #[test]
    fn height_major_ranks_follow_height_then_descriptor_and_share_equal_keys() {
        let shallow = positive_function(F5cNegative::Top, F5cPositive::Int);
        let deep = F5cPositive::Union(vec![positive_function(
            F5cNegative::Bottom,
            F5cPositive::Int,
        )]);
        let mut normalizer = Normalizer::new();
        let root = normalizer
            .flatten_positive(F5cPositive::Union(vec![deep, shallow.clone(), shallow]))
            .unwrap();

        normalizer.rank_all().unwrap();

        let NodeKind::PositiveUnion { start, len } = normalizer.nodes[root].kind else {
            panic!("test root remains a positive Union node");
        };
        assert_eq!(len, 2);
        let ordered = &normalizer.children[start..start + len];
        let first = normalizer.nodes[ordered[0]];
        let second = normalizer.nodes[ordered[1]];
        assert!(first.height < second.height);

        let first_descriptor = first.descriptor.unwrap();
        let first_words = &normalizer.descriptor_words
            [first_descriptor.0..first_descriptor.0 + first_descriptor.1];
        let equal_function_ranks = normalizer
            .nodes
            .iter()
            .filter(|node| matches!(node.kind, NodeKind::PositiveFunction { .. }))
            .filter(|node| {
                let (start, len) = node.descriptor.unwrap();
                &normalizer.descriptor_words[start..start + len] == first_words
            })
            .map(|node| (node.height, node.rank))
            .collect::<Vec<_>>();
        assert_eq!(equal_function_ranks.len(), 2);
        assert_eq!(equal_function_ranks[0], equal_function_ranks[1]);
    }

    #[test]
    fn normalization_index_lanes_reconcile_after_transient_release() {
        let mut drafts = [draft(F5cPositive::Union(
            (0..12).map(F5cPositive::Quantified).collect(),
        ))];
        let stats = normalize_component(&mut drafts).unwrap();
        let mut independent = crate::IndependentResourceLedger::default();

        independent
            .record_closed_normalization_index(&stats)
            .unwrap();

        assert!(stats.index_requested_slots > 0);
        assert!(stats.index_capacity_growths > 0);
        assert!(stats.index_peak_bytes > 0);
        assert!(stats.index_lanes[Lane::RadixWorkspace as usize].peak_capacity > 0);
        assert!(stats.index_lanes[Lane::RadixFrames as usize].peak_capacity > 0);
        assert_eq!(stats.index_actual_capacity, 0);
        assert_eq!(stats.index_retained_bytes, 0);
        assert_eq!(
            independent.closed_normalization_index_requested_slots,
            stats.index_requested_slots
        );
        assert_eq!(
            independent.closed_normalization_index_capacity_growths,
            stats.index_capacity_growths
        );
        assert_eq!(
            independent.closed_normalization_index_peak_bytes,
            stats.index_peak_bytes
        );
        assert_eq!(independent.closed_normalization_index_actual_capacity, 0);
        assert_eq!(independent.closed_normalization_index_retained_bytes, 0);
        for lane in &independent.closed_normalization_index_lanes {
            assert_eq!(lane.actual_capacity, 0);
            assert_eq!(lane.retained_bytes, 0);
            assert_eq!(lane.peak_capacity * lane.slot_size, lane.peak_bytes);
        }
    }

    #[test]
    fn checked_counter_overflow_does_not_publish_a_partial_normalization_sample() {
        let mut stats = NormalizationStats::default();
        stats.key_writes = 1;
        stats.child_comparisons = 1;
        let mut counters = crate::ProductionCounters::default();
        counters.closed_normalized_key_writes = 7;
        counters.closed_normalization_child_comparisons = usize::MAX;
        let before = counters.clone();

        assert_eq!(
            record_production_counters(&stats, &mut counters),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert_eq!(counters, before);
    }

    #[test]
    fn child_key_word_counter_counts_only_lexicographic_fields_examined() {
        let nodes = [
            Node {
                kind: NodeKind::PositiveInt,
                height: 0,
                rank: 1,
                descriptor: None,
            },
            Node {
                kind: NodeKind::PositiveInt,
                height: 1,
                rank: 0,
                descriptor: None,
            },
            Node {
                kind: NodeKind::PositiveInt,
                height: 0,
                rank: 2,
                descriptor: None,
            },
        ];
        let mut stats = NormalizationStats::default();

        assert_eq!(
            compare_key_ids(&nodes, &mut stats, 0, 1).unwrap(),
            Ordering::Less
        );
        assert_eq!(stats.word_comparisons, 1);
        assert_eq!(
            compare_key_ids(&nodes, &mut stats, 0, 2).unwrap(),
            Ordering::Less
        );
        assert_eq!(stats.word_comparisons, 3);
    }

    #[test]
    fn radix_scratch_counter_overflow_fails_before_allocation_or_partition() {
        let mut normalizer = Normalizer::new();
        normalizer.stats.index_lanes[Lane::RadixWorkspace as usize].requested_slots = usize::MAX;
        let workspace_stats_before = normalizer.stats.clone();

        assert_eq!(
            normalizer.prepare_radix_workspaces(),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert_eq!(normalizer.stats, workspace_stats_before);
        assert_eq!(normalizer.radix_workspace.capacity(), 0);

        let mut values = (0..9).rev().collect::<Vec<_>>();
        let values_before = values.clone();
        let mut frames = Vec::new();
        let mut workspace = vec![0; RADIX_WORKSPACE_SLOTS];
        let mut stats = NormalizationStats::default();
        stats.index_lanes[Lane::RadixFrames as usize].requested_slots = usize::MAX;
        let stats_before = stats.clone();

        assert_eq!(
            radix_sort_node_ids(
                &mut values,
                None,
                Some(&mut workspace),
                &mut frames,
                &mut stats,
                |_, _| Ok(1),
            ),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert_eq!(values, values_before);
        assert!(frames.is_empty());
        assert_eq!(stats, stats_before);
    }

    #[test]
    fn descriptor_order_is_independent_of_union_input_order() {
        let shallow = positive_function(F5cNegative::Top, F5cPositive::Int);
        let deep = F5cPositive::Union(vec![positive_function(
            F5cNegative::Bottom,
            F5cPositive::Int,
        )]);
        let mut forward = [draft(F5cPositive::Union(vec![
            shallow.clone(),
            deep.clone(),
        ]))];
        let mut reverse = [draft(F5cPositive::Union(vec![deep, shallow]))];

        let forward_stats = normalize_component(&mut forward).unwrap();
        let reverse_stats = normalize_component(&mut reverse).unwrap();

        assert_eq!(forward[0].predicate, reverse[0].predicate);
        assert_eq!(
            forward_stats, reverse_stats,
            "logical and physical counters are source-order independent"
        );
    }

    #[test]
    fn exact_word_comparison_counts_match_an_independent_mergesort_oracle() {
        let run = |ordinals: &[u32]| {
            let mut drafts = ordinals
                .iter()
                .copied()
                .map(|ordinal| draft(F5cPositive::Quantified(ordinal)))
                .collect::<Vec<_>>();
            let stats = normalize_component(&mut drafts).unwrap();
            let mut schemes = drafts
                .into_iter()
                .map(|draft| match draft.predicate {
                    F5cPositive::Quantified(ordinal) => ordinal,
                    _ => panic!("quantified leaf remains quantified"),
                })
                .collect::<Vec<_>>();
            schemes.sort_unstable();
            let oracle = oracle_component_word_comparisons(
                ordinals.iter().map(|ordinal| vec![2, *ordinal]).collect(),
            );
            (schemes, stats, oracle)
        };
        let forward = run(&[0, 1, 2, 3, 4]);
        let rotated = run(&[2, 3, 4, 0, 1]);

        assert_eq!(forward.0, rotated.0);
        assert_eq!(forward.1, rotated.1);
        assert_eq!(forward.1.word_comparisons, forward.2);
        assert_eq!(rotated.1.word_comparisons, rotated.2);
        assert_eq!(forward.1.word_comparisons, rotated.1.word_comparisons);
        assert_eq!(
            (forward.1.word_comparisons, rotated.1.word_comparisons),
            (18, 18)
        );
    }

    #[test]
    fn union_member_permutations_preserve_all_normalization_counters() {
        let members = (0..5).map(F5cPositive::Quantified).collect::<Vec<_>>();
        let mut forward = [draft(F5cPositive::Union(members.clone()))];
        let mut reverse = [draft(F5cPositive::Union(
            members.iter().rev().cloned().collect(),
        ))];

        let forward_stats = normalize_component(&mut forward).unwrap();
        let reverse_stats = normalize_component(&mut reverse).unwrap();

        assert_eq!(forward[0].predicate, reverse[0].predicate);
        assert_eq!(forward_stats, reverse_stats);
        assert_eq!(forward_stats.child_comparisons, 9);
    }

    #[test]
    fn descriptor_radix_order_matches_unsigned_word_lexicographic_order() {
        let ordinals = [
            u32::MAX,
            0x0001_0000,
            0x0000_0100,
            0xFF,
            0,
            0x0100_0001,
            0x0000_0101,
            0x0000_FF00,
            0xFFFF_FF00,
            0x0001_00FF,
            0x8000_0000,
            u32::MAX,
        ];
        let build = |items: &[u32]| {
            [draft(F5cPositive::Union(
                items.iter().copied().map(F5cPositive::Quantified).collect(),
            ))]
        };
        let mut forward = build(&ordinals);
        let mut reverse = build(&ordinals.iter().rev().copied().collect::<Vec<_>>());
        let forward_stats = normalize_component(&mut forward).unwrap();
        let reverse_stats = normalize_component(&mut reverse).unwrap();

        let F5cPositive::Union(members) = &forward[0].predicate else {
            panic!("the normalized root remains a Union");
        };
        assert_eq!(
            members,
            &[
                F5cPositive::Quantified(0),
                F5cPositive::Quantified(0xFF),
                F5cPositive::Quantified(0x0000_0100),
                F5cPositive::Quantified(0x0000_0101),
                F5cPositive::Quantified(0x0000_FF00),
                F5cPositive::Quantified(0x0001_0000),
                F5cPositive::Quantified(0x0001_00FF),
                F5cPositive::Quantified(0x0100_0001),
                F5cPositive::Quantified(0x8000_0000),
                F5cPositive::Quantified(0xFFFF_FF00),
                F5cPositive::Quantified(u32::MAX),
            ]
        );
        assert_eq!(forward[0].predicate, reverse[0].predicate);
        assert_eq!(forward_stats, reverse_stats);
        assert!(forward_stats.index_lanes[Lane::RadixWorkspace as usize].peak_capacity > 0);
        assert!(forward_stats.index_lanes[Lane::RadixFrames as usize].peak_capacity > 0);
    }

    #[test]
    fn radix_sort_orders_variable_length_descriptor_word_sequences() {
        let keys = vec![
            vec![],
            vec![0],
            vec![0, 0],
            vec![0, 1],
            vec![0, 0, 0],
            vec![1],
            vec![u32::MAX],
            vec![0x100],
            vec![0, u32::MAX],
            vec![0, 1],
        ];
        let mut words = Vec::new();
        let mut nodes = Vec::new();
        for key in &keys {
            let start = words.len();
            words.extend_from_slice(key);
            nodes.push(Node {
                kind: NodeKind::PositiveInt,
                height: 0,
                rank: 0,
                descriptor: Some((start, key.len())),
            });
        }
        let mut values = (0..nodes.len()).rev().collect::<Vec<_>>();
        let mut expected = keys.clone();
        expected.sort();
        let mut frames = Vec::new();
        let mut workspace = vec![0; RADIX_WORKSPACE_SLOTS];
        let mut stats = NormalizationStats::default();

        radix_sort_node_ids(
            &mut values,
            None,
            Some(&mut workspace),
            &mut frames,
            &mut stats,
            |node_id, byte| descriptor_radix_symbol(&nodes, &words, node_id, byte),
        )
        .unwrap();

        let actual = values
            .iter()
            .map(|node_id| &keys[*node_id])
            .collect::<Vec<_>>();
        let expected = expected.iter().collect::<Vec<_>>();
        assert_eq!(actual, expected);
    }

    #[test]
    fn normalization_walk_handles_deep_boxed_function_chains_iteratively() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut value = F5cPositive::Int;
                for _ in 0..4096 {
                    value = positive_function(F5cNegative::Top, value);
                }
                let mut value = normalize_positive(value).unwrap();
                for _ in 0..4096 {
                    let F5cPositive::Function { result, .. } = value else {
                        panic!("the chain retains each Function node");
                    };
                    value = *result;
                }
                assert_eq!(value, F5cPositive::Int);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn normalization_rejects_unclassified_live_nodes() {
        for value in [
            F5cPositive::Variable(0),
            F5cPositive::Shared(super::super::F5cSummaryNodeId(0)),
        ] {
            assert_eq!(
                normalize_positive(value),
                Err(SolveAvailabilityError::IdentityExhausted)
            );
        }
        for value in [
            F5cNegative::Variable(0),
            F5cNegative::Shared(super::super::F5cSummaryNodeId(0)),
        ] {
            assert_eq!(
                normalize_negative(value),
                Err(SolveAvailabilityError::IdentityExhausted)
            );
        }
    }
}
