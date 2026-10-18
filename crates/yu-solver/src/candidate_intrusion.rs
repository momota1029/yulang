//! Candidate-only extrusion occurrences, source qualification and canonical row equality.
use crate::candidate_scheme::RowKey;
use crate::*;

#[cfg(test)]
#[path = "candidate_intrusion_tests.rs"]
mod tests;

#[derive(Debug, Default)]
pub(super) struct State {
    pub effect_algebra: candidate_effect::State,
    values: Vec<u32>,
    effects: Vec<u32>,
    pub(super) parents: Vec<Parent>,
    groups: Vec<PairGroup>,
    pending: Vec<usize>,
    pending_cursor: usize,
    activations: Vec<usize>,
    by_output: HashMap<(TypedPairKey, ExtrusionEndpoint), Vec<usize>>,
    output_index_bytes: usize,
    reuses: Vec<Reuse>,
    reuse_keys: HashSet<(usize, usize)>,
    pub diagnostic_edges: HashSet<(CanonicalValuePairKey, DiagnosticEdge)>,
    pub completed: HashMap<candidate_context::RelationId, u64>,
    pub generation: u64,
    next_occurrence: usize,
    pub dirty: bool,
    pub active_roots: HashMap<DefinitionOrderId, u32>,
    pub active_uses: HashSet<DefinitionUseId>,
    #[cfg(test)]
    forest_events: Vec<ForestEvent>,
    #[cfg(test)]
    forest_event_log_complete: Option<bool>,
}
#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ForestEvent {
    Birth(RowKey),
    ParentWrite { key: RowKey, before: u32, after: u32, kind: ForestWriteKind },
    Truncate { values_len: usize, effects_len: usize },
}
#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ForestWriteKind { Merge, Compress, Rollback }
#[cfg(test)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ForestSnapshot {
    pub values: Vec<u32>,
    pub effects: Vec<u32>,
    pub event_cursor: usize,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct Parent {
    pub copy: RowKey,
    pub parent: RowKey,
    pub polarity: Polarity,
    pub target: u32,
    pub sources: Option<usize>,
    pub comparison: Option<TypedPairKey>,
    pub occurrence: usize,
}
#[derive(Clone, Copy, Debug)]
struct PairGroup { occurrence: usize, start: usize, end: usize, activated: bool }
#[derive(Clone, Copy, Debug)]
struct Reuse { group: usize, sources: usize, occurrence: usize }
pub(super) struct Undo {
    pub(super) effect_algebra: candidate_effect::Checkpoint,
    values_len: usize,
    effects_len: usize,
    parents_len: usize,
    groups_len: usize,
    pending_len: usize,
    pending_cursor: usize,
    activations_len: usize,
    reuses_len: usize,
    generation: u64,
    next_occurrence: usize,
    dirty: bool,
    forests: Vec<(RowKey, u32)>,
    completions: Vec<(candidate_context::RelationId, Option<u64>)>,
    memos: Vec<(TypedPairKey, TypedPairMemo)>,
    memo_children_bytes: usize,
    completion_saved: HashSet<candidate_context::RelationId>,
    memo_saved: HashSet<TypedPairKey>,
    new_pairs: HashSet<TypedPairKey>,
    diagnostic_edges: Vec<(CanonicalValuePairKey, DiagnosticEdge)>,
}
fn exhausted() -> SolveAvailabilityError {
    SolveAvailabilityError::IdentityExhausted
}
fn push<T>(v: &mut Vec<T>, item: T) -> Result<(), SolveAvailabilityError> {
    v.try_reserve(1).map_err(|_| exhausted())?;
    v.push(item);
    Ok(())
}
fn bytes<T>(capacity: usize) -> Result<usize, SolveAvailabilityError> {
    capacity
        .checked_mul(std::mem::size_of::<T>())
        .ok_or_else(exhausted)
}
fn sum(parts: &[usize]) -> Result<usize, SolveAvailabilityError> {
    parts
        .iter()
        .try_fold(0usize, |n, part| n.checked_add(*part).ok_or_else(exhausted))
}
#[cfg(test)]
fn record_forest_event_parts(
    events: &mut Vec<ForestEvent>, complete: &mut Option<bool>, event: ForestEvent,
) -> Result<(), SolveAvailabilityError> {
    if *complete == Some(false) { return Err(exhausted()); }
    if events.try_reserve(1).is_err() {
        *complete = Some(false);
        return Err(exhausted());
    }
    events.push(event);
    *complete = Some(true);
    Ok(())
}
fn representative(forest: &[u32], mut row: u32) -> u32 {
    while let Some(&parent) = forest.get(row as usize) {
        if parent == row {
            break;
        }
        row = parent;
    }
    row
}
impl State {
    #[cfg(test)]
    fn record_forest_event(&mut self, event: ForestEvent) -> Result<(), SolveAvailabilityError> {
        record_forest_event_parts(&mut self.forest_events, &mut self.forest_event_log_complete, event)
    }
    #[cfg(test)]
    pub(super) fn forest_event_cursor(&self) -> usize { self.forest_events.len() }
    #[cfg(test)]
    pub(super) fn forest_events(&self) -> &[ForestEvent] { &self.forest_events }
    #[cfg(test)]
    pub(super) fn forest_event_log_complete(&self) -> bool {
        self.forest_event_log_complete != Some(false)
    }
    #[cfg(test)]
    pub(super) fn forest_snapshot(&self) -> Result<ForestSnapshot, SolveAvailabilityError> {
        let mut values = Vec::new();
        values.try_reserve_exact(self.values.len()).map_err(|_| exhausted())?;
        values.extend_from_slice(&self.values);
        let mut effects = Vec::new();
        effects.try_reserve_exact(self.effects.len()).map_err(|_| exhausted())?;
        effects.extend_from_slice(&self.effects);
        Ok(ForestSnapshot { values, effects, event_cursor: self.forest_events.len() })
    }
    #[cfg(test)]
    pub(super) fn observed_output_groups(&self, pair: TypedPairKey, output: ExtrusionEndpoint) -> Vec<(usize, usize, usize, usize, bool)> {
        self.by_output.get(&(pair, output)).into_iter().flatten().map(|&id| {
            let group = self.groups[id];
            (id, group.occurrence, group.start, group.end, group.activated)
        }).collect()
    }
    pub fn observed_groups(&self) -> impl Iterator<Item = (usize, usize, usize, usize, bool)> + '_ {
        self.groups.iter().enumerate().map(|(id, group)| (id, group.occurrence, group.start, group.end, group.activated))
    }
    pub fn observed_reuses(&self) -> impl Iterator<Item = (usize, usize, usize, usize)> + '_ {
        self.reuses.iter().enumerate().map(|(id, reuse)| (id, reuse.group, reuse.occurrence, reuse.sources))
    }
    pub fn observed_pending(&self) -> (usize, usize) { (self.pending.len(), self.pending_cursor) }
    pub fn value_rep(&self, row: u32) -> u32 {
        representative(&self.values, row)
    }
    pub fn effect_rep(&self, row: u32) -> u32 {
        representative(&self.effects, row)
    }
    pub fn rep(&self, key: RowKey) -> RowKey {
        match key {
            RowKey::Value(row) => RowKey::Value(self.value_rep(row)),
            RowKey::Effect(row) => RowKey::Effect(self.effect_rep(row)),
        }
    }
    pub fn begin(&self) -> Undo {
        Undo {
            effect_algebra: self.effect_algebra.checkpoint(),
            values_len: self.values.len(),
            effects_len: self.effects.len(),
            parents_len: self.parents.len(),
            groups_len: self.groups.len(),
            pending_len: self.pending.len(),
            pending_cursor: self.pending_cursor,
            activations_len: self.activations.len(),
            reuses_len: self.reuses.len(),
            generation: self.generation,
            next_occurrence: self.next_occurrence,
            dirty: self.dirty,
            forests: Vec::new(),
            completions: Vec::new(),
            memos: Vec::new(),
            memo_children_bytes: 0,
            completion_saved: HashSet::new(),
            memo_saved: HashSet::new(),
            new_pairs: HashSet::new(),
            diagnostic_edges: Vec::new(),
        }
    }
    pub fn rollback(&mut self, undo: Undo, memos: &mut HashMap<TypedPairKey, TypedPairMemo>) {
        self.effect_algebra.rollback(undo.effect_algebra);
        for (key, parent) in undo.forests.into_iter().rev() {
            #[cfg(test)]
            let before = match key {
                RowKey::Value(row) => self.values[row as usize],
                RowKey::Effect(row) => self.effects[row as usize],
            };
            #[cfg(test)]
            let _ = self.record_forest_event(ForestEvent::ParentWrite {
                key, before, after: parent, kind: ForestWriteKind::Rollback,
            });
            match key {
                RowKey::Value(row) => self.values[row as usize] = parent,
                RowKey::Effect(row) => self.effects[row as usize] = parent,
            }
        }
        #[cfg(test)]
        let _ = self.record_forest_event(ForestEvent::Truncate {
            values_len: undo.values_len, effects_len: undo.effects_len,
        });
        self.values.truncate(undo.values_len);
        self.effects.truncate(undo.effects_len);
        self.parents.truncate(undo.parents_len);
        for group in self.activations.drain(undo.activations_len..).rev() {
            self.groups[group].activated = false;
        }
        self.pending.truncate(undo.pending_len);
        self.pending_cursor = undo.pending_cursor;
        self.groups.truncate(undo.groups_len);
        for reuse in self.reuses.drain(undo.reuses_len..) { self.reuse_keys.remove(&(reuse.group, reuse.sources)); }
        self.by_output.retain(|_, groups| { groups.retain(|&group| group < undo.groups_len); !groups.is_empty() });
        self.output_index_bytes = self.by_output.values().map(|groups| groups.capacity() * std::mem::size_of::<usize>()).sum();
        self.generation = undo.generation;
        self.next_occurrence = undo.next_occurrence;
        self.dirty = undo.dirty;
        for (key, previous) in undo.completions.into_iter().rev() {
            if let Some(previous) = previous {
                self.completed.insert(key, previous);
            } else {
                self.completed.remove(&key);
            }
        }
        for key in undo.diagnostic_edges {
            self.diagnostic_edges.remove(&key);
        }
        for (key, previous) in undo.memos.into_iter().rev() {
            memos.insert(key, previous);
        }
    }
    pub fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        sum(&[
            self.effect_algebra.bytes()?,
            bytes::<u32>(self.values.capacity())?,
            bytes::<u32>(self.effects.capacity())?,
            bytes::<Parent>(self.parents.capacity())?,
            bytes::<PairGroup>(self.groups.capacity())?,
            bytes::<usize>(self.pending.capacity())?,
            bytes::<usize>(self.activations.capacity())?,
            bytes::<((TypedPairKey, ExtrusionEndpoint), Vec<usize>)>(self.by_output.capacity())?,
            self.output_index_bytes,
            bytes::<Reuse>(self.reuses.capacity())?,
            bytes::<(usize, usize)>(self.reuse_keys.capacity())?,
            bytes::<(CanonicalValuePairKey, DiagnosticEdge)>(self.diagnostic_edges.capacity())?,
            bytes::<(candidate_context::RelationId, u64)>(self.completed.capacity())?,
            bytes::<(DefinitionOrderId, u32)>(self.active_roots.capacity())?,
            bytes::<DefinitionUseId>(self.active_uses.capacity())?,
        ])
    }
}
impl Undo {
    pub(super) fn reserve_diagnostic_edge(&mut self) -> Result<(), SolveAvailabilityError> {
        self.diagnostic_edges.try_reserve(1).map_err(|_| exhausted())
    }
    pub(super) fn insert_diagnostic_edge(&mut self, key: (CanonicalValuePairKey, DiagnosticEdge)) {
        self.diagnostic_edges.push(key);
    }
    pub fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        sum(&[
            self.effect_algebra.bytes()?,
            bytes::<(RowKey, u32)>(self.forests.capacity())?,
            bytes::<(candidate_context::RelationId, Option<u64>)>(self.completions.capacity())?,
            bytes::<(TypedPairKey, TypedPairMemo)>(self.memos.capacity())?,
            bytes::<candidate_context::RelationId>(self.completion_saved.capacity())?,
            bytes::<TypedPairKey>(self.memo_saved.capacity())?,
            bytes::<TypedPairKey>(self.new_pairs.capacity())?,
            bytes::<(CanonicalValuePairKey, DiagnosticEdge)>(self.diagnostic_edges.capacity())?,
            self.memo_children_bytes,
        ])
    }
}
impl InferenceSession {
    pub(super) fn canonical_extrusion(&self, endpoint: ExtrusionEndpoint) -> ExtrusionEndpoint {
        match endpoint {
            ExtrusionEndpoint::Value(v) => ExtrusionEndpoint::Value(self.canonical_value(v)),
            ExtrusionEndpoint::Effect(e) => ExtrusionEndpoint::Effect(self.canonical_effect(e)),
        }
    }
    pub(super) fn begin_candidate_extrusion(&mut self) -> Result<usize, SolveAvailabilityError> {
        let state = &mut self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion;
        let id = state.next_occurrence;
        state.next_occurrence = id.checked_add(1).ok_or_else(exhausted)?;
        Ok(id)
    }
    pub(super) fn retain_extrusion_parent(
        &mut self,
        copy: ExtrusionEndpoint,
        parent: ExtrusionEndpoint,
        polarity: Polarity,
        target: u32,
        occurrence: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let (copy, parent) = match (copy, parent) {
            (
                ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(c)),
                ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(p)),
            ) => (RowKey::Value(c), RowKey::Value(p)),
            (
                ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(c)),
                ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(p)),
            ) => (RowKey::Effect(c), RowKey::Effect(p)),
            _ => return Err(exhausted()),
        };
        let sources = self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.effect_algebra.context.extrusion_sources();
        let qualified = sources.is_some_and(|sources| self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.source_events(sources).iter()
            .any(|&event| self.batch.candidate_source.references.qualifies(event)));
        let state = &mut self
            .candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .intrusion;
        if qualified { state.pending.try_reserve(1).map_err(|_| exhausted())?; }
        state
            .values
            .try_reserve(self.bounds.len().saturating_sub(state.values.len()))
            .map_err(|_| exhausted())?;
        state
            .effects
            .try_reserve(self.effect_bounds.len().saturating_sub(state.effects.len()))
            .map_err(|_| exhausted())?;
        state.parents.try_reserve(1).map_err(|_| exhausted())?;
        for row in state.values.len()..self.bounds.len() {
            let row = u32::try_from(row).map_err(|_| exhausted())?;
            #[cfg(test)]
            state.record_forest_event(ForestEvent::Birth(RowKey::Value(row)))?;
            state.values.push(row);
        }
        for row in state.effects.len()..self.effect_bounds.len() {
            let row = u32::try_from(row).map_err(|_| exhausted())?;
            #[cfg(test)]
            state.record_forest_event(ForestEvent::Birth(RowKey::Effect(row)))?;
            state.effects.push(row);
        }
        // This provenance is deliberately absent from the dependency adjacency.
        if qualified { state.pending.push(state.parents.len()); }
        state.parents.push(Parent {
            copy,
            parent,
            polarity,
            target,
            sources,
            comparison: state.effect_algebra.processing,
            occurrence,
        });
        state.dirty = true;
        Ok(())
    }
    pub(super) fn finish_candidate_extrusion(
        &mut self, occurrence: usize, start: usize, output: ExtrusionEndpoint,
    ) -> Result<(), SolveAvailabilityError> {
        let state = &mut self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion;
        if start == state.parents.len() { return Ok(()); }
        let Some(comparison) = state.effect_algebra.processing else { return Ok(()); };
        state.groups.try_reserve(1).map_err(|_| exhausted())?;
        state.by_output.try_reserve(1).map_err(|_| exhausted())?;
        let indices = state.by_output.entry((comparison, output)).or_default();
        let previous = indices.capacity();
        indices.try_reserve(1).map_err(|_| exhausted())?;
        state.output_index_bytes = state.output_index_bytes.checked_add(bytes::<usize>(indices.capacity() - previous)?).ok_or_else(exhausted)?;
        indices.push(state.groups.len());
        debug_assert!(state.parents[start..].iter().all(|parent|
            parent.occurrence == occurrence && parent.comparison == Some(comparison)));
        let activated = state.parents[start].sources.is_some_and(|sources| state.effect_algebra.context.source_events(sources).iter()
            .any(|&event| self.batch.candidate_source.references.qualifies(event)));
        state.groups.push(PairGroup { occurrence, start, end: state.parents.len(), activated });
        Ok(())
    }
    pub(super) fn recapture_candidate_extrusion(
        &mut self, key: TypedPairKey, output: CanonicalValuePairKey,
    ) -> Result<(), SolveAvailabilityError> {
        let state = &mut self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion;
        let Some(sources) = state.effect_algebra.context.extrusion_sources() else { return Ok(()); };
        let qualified = state.effect_algebra.context.source_events(sources).iter()
            .any(|&event| self.batch.candidate_source.references.qualifies(event));
        // Only groups producing the child actually reused by dispatch participate.
        // The original pair records and their source association remain immutable.
        for endpoint in [output.lower, output.upper] {
            let Some(groups) = state.by_output.get(&(key, ExtrusionEndpoint::Value(endpoint))) else { continue; };
            for &group in groups {
                let original = state.parents[state.groups[group].start];
                debug_assert_eq!(original.occurrence, state.groups[group].occurrence);
                if original.sources == Some(sources) || state.reuse_keys.contains(&(group, sources)) { continue; }
                state.reuses.try_reserve(1).map_err(|_| exhausted())?;
                state.reuse_keys.try_reserve(1).map_err(|_| exhausted())?;
                let occurrence = state.next_occurrence;
                state.next_occurrence = occurrence.checked_add(1).ok_or_else(exhausted)?;
                state.reuse_keys.insert((group, sources));
                state.reuses.push(Reuse { group, sources, occurrence });
                debug_assert_ne!(state.reuses.last().unwrap().occurrence, state.groups[group].occurrence);
                if qualified && !state.groups[group].activated {
                    let pairs = state.groups[group];
                    state.pending.try_reserve(pairs.end - pairs.start).map_err(|_| exhausted())?;
                    state.activations.try_reserve(1).map_err(|_| exhausted())?;
                    state.activations.push(group);
                    state.groups[group].activated = true;
                    state.pending.extend(pairs.start..pairs.end);
                }
                state.dirty = true;
            }
        }
        Ok(())
    }
    pub(super) fn mark_candidate_pair(
        &mut self,
        key: TypedPairKey,
    ) -> Result<(), SolveAvailabilityError> {
        // A raw alias owns diagnostic provenance, but its canonical work item
        // still owns semantic processing and relation completion.
        let canonical = self.candidate_context_pair(key);
        let state = &mut self
            .candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .intrusion;
        let relation = state.effect_algebra.context.processing.filter(|_| key == canonical);
        if relation.is_some() { state.completed.try_reserve(1).map_err(|_| exhausted())?; }
        if let Some(undo) = self
            .route_journal
            .as_mut()
            .and_then(|journal| journal.intrusion.as_mut())
        {
            if let Some(relation) = relation {
                if !undo.completion_saved.contains(&relation) {
                    undo.completion_saved.try_reserve(1).map_err(|_| exhausted())?;
                    push(&mut undo.completions, (relation, state.completed.get(&relation).copied()))?;
                    undo.completion_saved.insert(relation);
                }
            }
            if !self.typed_pairs.contains_key(&key) {
                undo.new_pairs.try_reserve(1).map_err(|_| exhausted())?;
                undo.new_pairs.insert(key);
            }
        }
        if let Some(relation) = relation { state.completed.insert(relation, state.generation); }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
    pub(super) fn journal_candidate_memo(
        &mut self,
        key: TypedPairKey,
    ) -> Result<(), SolveAvailabilityError> {
        let Some(undo) = self
            .route_journal
            .as_mut()
            .and_then(|journal| journal.intrusion.as_mut())
        else {
            return Ok(());
        };
        if undo.new_pairs.contains(&key) || undo.memo_saved.contains(&key) {
            return Ok(());
        }
        undo.memo_saved.try_reserve(1).map_err(|_| exhausted())?;
        undo.memos.try_reserve(1).map_err(|_| exhausted())?;
        // Save the entry memo once, before any diagnostic mutation.
        let saved = match &self.typed_pairs[&key] {
            TypedPairMemo::Effect => TypedPairMemo::Effect,
            TypedPairMemo::Value {
                children,
                direct_witness,
                completion,
                retained_extrusion_rewrite,
            } => {
                let mut entries = Vec::new();
                entries
                    .try_reserve_exact(children.capacity())
                    .map_err(|_| exhausted())?;
                entries.extend(children.iter().copied());
                TypedPairMemo::Value {
                    children: DiagnosticChildren::from_vec(entries),
                    direct_witness: *direct_witness,
                    completion: *completion,
                    retained_extrusion_rewrite: *retained_extrusion_rewrite,
                }
            }
        };
        let child_bytes = match &saved {
            TypedPairMemo::Effect => 0,
            TypedPairMemo::Value { children, .. } => bytes::<DiagnosticEdge>(children.capacity())?,
        };
        let memo_children_bytes = undo.memo_children_bytes
            .checked_add(child_bytes).ok_or_else(exhausted)?;
        undo.memos.push((key, saved));
        undo.memo_saved.insert(key);
        undo.memo_children_bytes = memo_children_bytes;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }

    fn compress_candidate_forests(&mut self) -> Result<(), SolveAvailabilityError> {
        let state = &mut self
            .candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .intrusion;
        if let Some(undo) = self
            .route_journal
            .as_mut()
            .and_then(|journal| journal.intrusion.as_mut())
        {
            undo.forests
                .try_reserve(
                    state
                        .values
                        .len()
                        .checked_add(state.effects.len())
                        .ok_or_else(exhausted)?,
                )
                .map_err(|_| exhausted())?;
        }
        for effect in [false, true] {
            #[cfg(test)]
            let (forest, events, event_log_complete) = if effect {
                (&mut state.effects, &mut state.forest_events, &mut state.forest_event_log_complete)
            } else {
                (&mut state.values, &mut state.forest_events, &mut state.forest_event_log_complete)
            };
            #[cfg(not(test))]
            let forest = if effect { &mut state.effects } else { &mut state.values };
            for index in 0..forest.len() {
                let root = representative(forest, index as u32);
                let mut row = index as u32;
                while forest[row as usize] != root {
                    let old = forest[row as usize];
                    #[cfg(test)]
                    record_forest_event_parts(events, event_log_complete, ForestEvent::ParentWrite {
                        key: if effect { RowKey::Effect(row) } else { RowKey::Value(row) },
                        before: old, after: root, kind: ForestWriteKind::Compress,
                    })?;
                    if let Some(undo) = self
                        .route_journal
                        .as_mut()
                        .and_then(|journal| journal.intrusion.as_mut())
                    {
                        undo.forests.push((
                            if effect {
                                RowKey::Effect(row)
                            } else {
                                RowKey::Value(row)
                            },
                            old,
                        ));
                    }
                    forest[row as usize] = root;
                    row = old;
                }
            }
        }
        Ok(())
    }
    pub(super) fn settle_candidate_intrusion(
        &mut self,
        root: Option<CanonicalValuePairKey>,
    ) -> Result<(), SolveAvailabilityError> {
        let state = &self
            .candidate_graph
            .as_ref()
            .ok_or_else(exhausted)?
            .intrusion;
        if state.pending_cursor == state.pending.len() {
            self.candidate_graph.as_mut().unwrap().intrusion.dirty = false;
            return Ok(());
        }
        self.compress_candidate_forests()?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        loop {
            let state = &self.candidate_graph.as_ref().unwrap().intrusion;
            let Some(&parent_index) = state.pending.get(state.pending_cursor) else { break; };
            let parent = state.parents[parent_index];
            debug_assert!(matches!(parent.polarity, Polarity::Positive | Polarity::Negative));
            debug_assert!(match parent.copy {
                RowKey::Value(row) => self.value_levels[row as usize] <= parent.target,
                RowKey::Effect(row) => self.effect_levels[row as usize] <= parent.target,
            });
            self.merge_candidate_rows(parent.copy, parent.parent, root, parent_index)?;
            self.candidate_graph.as_mut().unwrap().intrusion.pending_cursor += 1;
        }
        self.candidate_graph.as_mut().unwrap().intrusion.dirty = false;
        Ok(())
    }

    fn merge_candidate_rows(
        &mut self,
        copy: RowKey,
        parent: RowKey,
        root: Option<CanonicalValuePairKey>,
        parent_index: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let state = &self
            .candidate_graph
            .as_ref()
            .ok_or_else(exhausted)?
            .intrusion;
        let copy = state.rep(copy);
        let parent = state.rep(parent);
        if copy == parent {
            return Ok(());
        }
        let generation = state.generation.checked_add(1).ok_or_else(exhausted)?;
        let (effect, from, to) = match (copy, parent) {
            (RowKey::Value(from), RowKey::Value(to)) => (false, from as usize, to as usize),
            (RowKey::Effect(from), RowKey::Effect(to)) => (true, from as usize, to as usize),
            _ => return Err(exhausted()),
        };
        if let Some(undo) = self
            .route_journal
            .as_mut()
            .and_then(|journal| journal.intrusion.as_mut())
        {
            push(&mut undo.forests, (copy, from as u32))?;
        }
        if effect {
            self.journal_effect_row(to)?;
        } else {
            self.journal_value_row(to)?;
        }
        // Append both bound sides. Physical source storage remains intact, so
        // the existing length journal can restore every owner without aliases.
        for side in [Polarity::Positive, Polarity::Negative] {
            let count = self.candidate_opposite_count(
                row_endpoint(copy),
                if side == Polarity::Positive {
                    Polarity::Negative
                } else {
                    Polarity::Positive
                },
            )?;
            for n in 0..count {
                let item = self.candidate_opposite_bound(
                    row_endpoint(copy),
                    if side == Polarity::Positive {
                        Polarity::Negative
                    } else {
                        Polarity::Positive
                    },
                    n,
                );
                self.candidate_insert_copied_bound(row_endpoint(parent), side, item, false,
                    candidate_effect::BoundKey(row_endpoint(copy), side, item),
                    candidate_context::TransportReason::ParentCopy { parent_index })?;
                self.candidate_transfer_bound_origins(
                    candidate_effect::BoundKey(row_endpoint(copy), side, item),
                    candidate_effect::BoundKey(row_endpoint(parent), side, self.canonical_extrusion(item)),
                    candidate_context::TransportReason::ParentCopy { parent_index })?;
            }
        }
        if effect {
            // Equality moves capture metadata without creating a solver/SCC edge.
            self.candidate_splice_capture_incidence(from as u32, to as u32)?;
            let level = self.effect_levels[to].min(self.effect_levels[from]);
            let non_generic =
                self.effect_metadata[to].non_generic | self.effect_metadata[from].non_generic;
            self.effect_levels[to] = level;
            self.effect_metadata[to].non_generic = non_generic;
            #[cfg(test)]
            self.candidate_graph.as_mut().unwrap().intrusion.record_forest_event(ForestEvent::ParentWrite {
                key: RowKey::Effect(from as u32), before: from as u32,
                after: to as u32, kind: ForestWriteKind::Merge,
            })?;
            self.candidate_graph.as_mut().unwrap().intrusion.effects[from] = to as u32;
        } else {
            let level = self.value_levels[to].min(self.value_levels[from]);
            let non_generic =
                self.value_metadata[to].non_generic | self.value_metadata[from].non_generic;
            self.value_levels[to] = level;
            self.value_metadata[to].non_generic = non_generic;
            #[cfg(test)]
            self.candidate_graph.as_mut().unwrap().intrusion.record_forest_event(ForestEvent::ParentWrite {
                key: RowKey::Value(from as u32), before: from as u32,
                after: to as u32, kind: ForestWriteKind::Merge,
            })?;
            self.candidate_graph.as_mut().unwrap().intrusion.values[from] = to as u32;
        }
        self.candidate_context_canonicalize_bounds()?;
        self.candidate_graph.as_mut().unwrap().intrusion.generation = generation;
        self.candidate_graph.as_mut().unwrap().intrusion.dirty = true;
        if let Some(root) = root {
            self.candidate_reopen_root(root)?;
        }
        let owner = row_endpoint(parent);
        let lowers = self.candidate_opposite_count(owner, Polarity::Negative)?;
        for n in 0..lowers {
            let lower = self.candidate_opposite_bound(owner, Polarity::Negative, n);
            self.candidate_replay_bound(owner, Polarity::Positive, lower, root)?;
        }
        Ok(())
    }
}
fn row_endpoint(row: RowKey) -> ExtrusionEndpoint {
    match row {
        RowKey::Value(row) => ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(row)),
        RowKey::Effect(row) => ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row)),
    }
}
