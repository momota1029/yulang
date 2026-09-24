use std::cmp::Ordering;

use super::{
    F5cNegative, F5cPositive, F5cRecursiveBound, GeneralizationDraft, SolveAvailabilityError,
};

type NodeId = usize;

const LANE_COUNT: usize = 11;

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

#[derive(Clone, Default)]
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
            stats: NormalizationStats::default(),
        }
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
            .try_reserve_exact(additional)
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
                        .try_reserve_exact(len)
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
                        .try_reserve_exact(len)
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
        .checked_add(2)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    Ok((left.height, left.rank).cmp(&(right.height, right.rank)))
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
    let mut stats = normalizer.stats.clone();
    stats.index_actual_capacity = 0;
    stats.index_retained_bytes = 0;
    for lane in &mut stats.index_lanes {
        lane.actual_capacity = 0;
        lane.retained_bytes = 0;
    }
    Ok(stats)
}

pub(super) fn record_production_counters(
    stats: &NormalizationStats,
    counters: &mut super::ProductionCounters,
) -> Result<(), SolveAvailabilityError> {
    counters.closed_normalized_key_writes = counters
        .closed_normalized_key_writes
        .checked_add(stats.key_writes)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    counters.closed_normalization_child_comparisons = counters
        .closed_normalization_child_comparisons
        .checked_add(stats.child_comparisons)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    counters.closed_normalization_descriptor_words = counters
        .closed_normalization_descriptor_words
        .checked_add(stats.descriptor_words)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    counters.closed_normalization_word_comparisons = counters
        .closed_normalization_word_comparisons
        .checked_add(stats.word_comparisons)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    counters.closed_normalization_index_requested_slots = counters
        .closed_normalization_index_requested_slots
        .checked_add(stats.index_requested_slots)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    counters.closed_normalization_index_actual_capacity = stats.index_actual_capacity;
    counters.closed_normalization_index_retained_bytes = stats.index_retained_bytes;
    counters.closed_normalization_index_peak_bytes = counters
        .closed_normalization_index_peak_bytes
        .max(stats.index_peak_bytes);
    counters.closed_normalization_index_capacity_growths = counters
        .closed_normalization_index_capacity_growths
        .checked_add(stats.index_capacity_growths)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let semantic_peak = counters
        .semantic_arena_retained_bytes
        .checked_add(stats.index_peak_bytes)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let session_peak = counters
        .inference_session_retained_bytes
        .checked_add(stats.index_peak_bytes)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    counters.semantic_arena_peak_bytes = counters.semantic_arena_peak_bytes.max(semantic_peak);
    counters.inference_session_peak_bytes = counters.inference_session_peak_bytes.max(session_peak);
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
        let mut next = self.clone();
        for (independent, measured) in next
            .closed_normalization_index_lanes
            .iter_mut()
            .zip(stats.index_lanes)
        {
            let peak_from_capacity = measured
                .peak_capacity
                .checked_mul(measured.slot_size)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            if peak_from_capacity != measured.peak_bytes
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
            independent.peak_capacity = independent.peak_capacity.max(measured.peak_capacity);
            independent.slot_size = measured.slot_size;
            independent.retained_bytes = measured.retained_bytes;
            independent.peak_bytes = independent.peak_bytes.max(measured.peak_bytes);
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
        }
        if requested_slots != stats.index_requested_slots
            || actual_capacity != stats.index_actual_capacity
            || retained_bytes != stats.index_retained_bytes
            || capacity_growths != stats.index_capacity_growths
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
    fn normalization_index_lanes_reconcile_after_transient_release() {
        let mut drafts = [draft(F5cPositive::Union(vec![
            F5cPositive::Int,
            positive_function(F5cNegative::Top, F5cPositive::Int),
        ]))];
        let stats = normalize_component(&mut drafts).unwrap();
        let mut independent = crate::IndependentResourceLedger::default();

        independent
            .record_closed_normalization_index(&stats)
            .unwrap();

        assert!(stats.index_requested_slots > 0);
        assert!(stats.index_capacity_growths > 0);
        assert!(stats.index_peak_bytes > 0);
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
            forward_stats.key_writes, reverse_stats.key_writes,
            "key writes are source-order independent"
        );
        assert_eq!(
            forward_stats.descriptor_words, reverse_stats.descriptor_words,
            "descriptor volume is source-order independent"
        );
        assert_eq!(
            forward_stats.word_comparisons, reverse_stats.word_comparisons,
            "the §36 operation counters are required to be source-order independent"
        );
        assert_eq!(
            forward_stats.child_comparisons, reverse_stats.child_comparisons,
            "member comparison count is source-order independent"
        );
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
                std::mem::forget(value);
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
