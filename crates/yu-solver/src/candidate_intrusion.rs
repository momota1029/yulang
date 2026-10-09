//! Candidate-only parent retention, canonical row identity and dependency SCCs.
use crate::candidate_scheme::RowKey;
use crate::*;

#[derive(Debug, Default)]
pub(super) struct State {
    values: Vec<u32>,
    effects: Vec<u32>,
    parents: Vec<Parent>,
    pub diagnostic_edges: HashSet<(CanonicalValuePairKey, DiagnosticEdge)>,
    pub completed: HashMap<TypedPairKey, u64>,
    pub generation: u64,
    pub dirty: bool,
    pub active_roots: HashMap<DefinitionOrderId, u32>,
    pub active_uses: HashSet<DefinitionUseId>,
}
#[derive(Clone, Copy, Debug)]
struct Parent {
    copy: RowKey,
    parent: RowKey,
    polarity: Polarity,
    target: u32,
}
pub(super) struct Undo {
    values_len: usize,
    effects_len: usize,
    parents_len: usize,
    generation: u64,
    dirty: bool,
    forests: Vec<(RowKey, u32)>,
    completions: Vec<(TypedPairKey, Option<u64>)>,
    memos: Vec<(TypedPairKey, TypedPairMemo)>,
    memo_children_bytes: usize,
    completion_saved: HashSet<TypedPairKey>,
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
            values_len: self.values.len(),
            effects_len: self.effects.len(),
            parents_len: self.parents.len(),
            generation: self.generation,
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
        for (key, parent) in undo.forests.into_iter().rev() {
            match key {
                RowKey::Value(row) => self.values[row as usize] = parent,
                RowKey::Effect(row) => self.effects[row as usize] = parent,
            }
        }
        self.values.truncate(undo.values_len);
        self.effects.truncate(undo.effects_len);
        self.parents.truncate(undo.parents_len);
        self.generation = undo.generation;
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
            bytes::<u32>(self.values.capacity())?,
            bytes::<u32>(self.effects.capacity())?,
            bytes::<Parent>(self.parents.capacity())?,
            bytes::<(CanonicalValuePairKey, DiagnosticEdge)>(self.diagnostic_edges.capacity())?,
            bytes::<(TypedPairKey, u64)>(self.completed.capacity())?,
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
            bytes::<(RowKey, u32)>(self.forests.capacity())?,
            bytes::<(TypedPairKey, Option<u64>)>(self.completions.capacity())?,
            bytes::<(TypedPairKey, TypedPairMemo)>(self.memos.capacity())?,
            bytes::<TypedPairKey>(self.completion_saved.capacity())?,
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
    pub(super) fn retain_extrusion_parent(
        &mut self,
        copy: ExtrusionEndpoint,
        parent: ExtrusionEndpoint,
        polarity: Polarity,
        target: u32,
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
        let state = &mut self
            .candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .intrusion;
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
            state
                .values
                .push(u32::try_from(row).map_err(|_| exhausted())?);
        }
        for row in state.effects.len()..self.effect_bounds.len() {
            state
                .effects
                .push(u32::try_from(row).map_err(|_| exhausted())?);
        }
        // This provenance is deliberately absent from the dependency adjacency.
        state.parents.push(Parent {
            copy,
            parent,
            polarity,
            target,
        });
        state.dirty = true;
        Ok(())
    }
    pub(super) fn mark_candidate_pair(
        &mut self,
        key: TypedPairKey,
    ) -> Result<(), SolveAvailabilityError> {
        let state = &mut self
            .candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .intrusion;
        state.completed.try_reserve(1).map_err(|_| exhausted())?;
        if let Some(undo) = self
            .route_journal
            .as_mut()
            .and_then(|journal| journal.intrusion.as_mut())
        {
            if !undo.completion_saved.contains(&key) {
                undo.completion_saved.try_reserve(1).map_err(|_| exhausted())?;
                push(&mut undo.completions, (key, state.completed.get(&key).copied()))?;
                undo.completion_saved.insert(key);
            }
            if !self.typed_pairs.contains_key(&key) {
                undo.new_pairs.try_reserve(1).map_err(|_| exhausted())?;
                undo.new_pairs.insert(key);
            }
        }
        state.completed.insert(key, state.generation);
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
            let forest = if effect {
                &mut state.effects
            } else {
                &mut state.values
            };
            for index in 0..forest.len() {
                let root = representative(forest, index as u32);
                let mut row = index as u32;
                while forest[row as usize] != root {
                    let old = forest[row as usize];
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
        if !state.dirty {
            return Ok(());
        }
        if state.parents.is_empty() {
            self.candidate_graph.as_mut().unwrap().intrusion.dirty = false;
            return Ok(());
        }
        self.compress_candidate_forests()?;
        let mut graph = Dependencies::default();
        for row in 0..self.bounds.len() {
            graph.intern(self.canonical_extrusion(ExtrusionEndpoint::Value(
                ValueEndpointKey::ValueRow(row as u32),
            )))?;
        }
        for row in 0..self.effect_bounds.len() {
            graph.intern(self.canonical_extrusion(ExtrusionEndpoint::Effect(
                EffectEndpointKey::EffectRow(row as u32),
            )))?;
        }
        let mut cursor = 0;
        while cursor < graph.nodes.len() {
            let endpoint = graph.nodes[cursor];
            match endpoint {
                ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(row)) => {
                    let bounds = &self.bounds[row as usize];
                    for &child in bounds
                        .direct_lower_rows
                        .iter()
                        .chain(&bounds.direct_upper_rows)
                    {
                        graph.edge(
                            cursor,
                            self.canonical_extrusion(ExtrusionEndpoint::Value(
                                ValueEndpointKey::ValueRow(child),
                            )),
                        )?;
                    }
                    for &child in bounds
                        .exact_non_variable_lowers
                        .iter()
                        .chain(&bounds.exact_non_variable_uppers)
                    {
                        graph.edge(
                            cursor,
                            self.canonical_extrusion(ExtrusionEndpoint::Value(child)),
                        )?;
                    }
                }
                ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row)) => {
                    let bounds = &self.effect_bounds[row as usize];
                    for &child in bounds
                        .direct_lower_rows
                        .iter()
                        .chain(&bounds.direct_upper_rows)
                    {
                        graph.edge(
                            cursor,
                            self.canonical_extrusion(ExtrusionEndpoint::Effect(
                                EffectEndpointKey::EffectRow(child),
                            )),
                        )?;
                    }
                    for &child in bounds
                        .exact_non_variable_lowers
                        .iter()
                        .chain(&bounds.exact_non_variable_uppers)
                    {
                        graph.edge(
                            cursor,
                            self.canonical_extrusion(ExtrusionEndpoint::Effect(child)),
                        )?;
                    }
                }
                ExtrusionEndpoint::Value(value) => {
                    let (polarity, ports) = if let Some(ports) =
                        Self::positive_function_children(&self.store, value)
                    {
                        (Polarity::Positive, ports)
                    } else if let Some(ports) = Self::negative_function_children(&self.store, value)
                    {
                        (Polarity::Negative, ports)
                    } else {
                        return Err(exhausted());
                    };
                    let opposite = if polarity == Polarity::Positive {
                        Polarity::Negative
                    } else {
                        Polarity::Positive
                    };
                    for child in [
                        ExtrusionEndpoint::Value(self.value_endpoint(ports.0, opposite)),
                        ExtrusionEndpoint::Effect(self.effect_endpoint(ports.1, opposite)),
                        ExtrusionEndpoint::Effect(self.effect_endpoint(ports.2, polarity)),
                        ExtrusionEndpoint::Value(self.value_endpoint(ports.3, polarity)),
                    ] {
                        graph.edge(cursor, child)?;
                    }
                }
                _ => return Err(exhausted()),
            }
            cursor += 1;
        }
        let (components, scratch) = graph.components()?;
        let mut merges = Vec::new();
        let state = &self.candidate_graph.as_ref().unwrap().intrusion;
        for parent in &state.parents {
            let copy = state.rep(parent.copy);
            let original = state.rep(parent.parent);
            // Polarity/target remain creation provenance, not SCC graph edges.
            let _creation = (parent.polarity, parent.target);
            if copy != original
                && components[graph.positions[&row_endpoint(copy)]]
                    == components[graph.positions[&row_endpoint(original)]]
            {
                push(&mut merges, (copy, original))?;
            }
        }
        let scratch = sum(&[
            scratch,
            graph.bytes()?,
            bytes::<(RowKey, RowKey)>(merges.capacity())?,
        ])?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self
            .candidate_graph
            .as_ref()
            .unwrap()
            .scratch_bytes
            .checked_add(scratch)
            .ok_or_else(exhausted)?;
        let result = (|| {
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            self.candidate_graph.as_mut().unwrap().intrusion.dirty = false;
            for (copy, parent) in merges.iter().copied() {
                self.merge_candidate_rows(copy, parent, root)?;
            }
            Ok(())
        })();
        drop((graph, components, merges));
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= scratch;
        result
    }
    fn merge_candidate_rows(
        &mut self,
        copy: RowKey,
        parent: RowKey,
        root: Option<CanonicalValuePairKey>,
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
                self.candidate_insert_bound(row_endpoint(parent), side, item)?;
            }
        }
        if effect {
            let level = self.effect_levels[to].min(self.effect_levels[from]);
            let non_generic =
                self.effect_metadata[to].non_generic | self.effect_metadata[from].non_generic;
            self.effect_levels[to] = level;
            self.effect_metadata[to].non_generic = non_generic;
            self.candidate_graph.as_mut().unwrap().intrusion.effects[from] = to as u32;
        } else {
            let level = self.value_levels[to].min(self.value_levels[from]);
            let non_generic =
                self.value_metadata[to].non_generic | self.value_metadata[from].non_generic;
            self.value_levels[to] = level;
            self.value_metadata[to].non_generic = non_generic;
            self.candidate_graph.as_mut().unwrap().intrusion.values[from] = to as u32;
        }
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
#[derive(Default)]
struct Dependencies {
    nodes: Vec<ExtrusionEndpoint>,
    positions: HashMap<ExtrusionEndpoint, usize>,
    edges: Vec<Vec<usize>>,
    reverse: Vec<Vec<usize>>,
}
impl Dependencies {
    fn intern(
        &mut self,
        endpoint: ExtrusionEndpoint,
    ) -> Result<Option<usize>, SolveAvailabilityError> {
        if !matches!(
            endpoint,
            ExtrusionEndpoint::Value(
                ValueEndpointKey::ValueRow(_)
                    | ValueEndpointKey::PositiveFunction(_)
                    | ValueEndpointKey::NegativeFunction(_)
            ) | ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(_))
        ) {
            return Ok(None);
        }
        if let Some(&index) = self.positions.get(&endpoint) {
            return Ok(Some(index));
        }
        self.positions.try_reserve(1).map_err(|_| exhausted())?;
        self.nodes.try_reserve(1).map_err(|_| exhausted())?;
        self.edges.try_reserve(1).map_err(|_| exhausted())?;
        self.reverse.try_reserve(1).map_err(|_| exhausted())?;
        let index = self.nodes.len();
        self.nodes.push(endpoint);
        self.edges.push(Vec::new());
        self.reverse.push(Vec::new());
        self.positions.insert(endpoint, index);
        Ok(Some(index))
    }
    fn edge(
        &mut self,
        from: usize,
        endpoint: ExtrusionEndpoint,
    ) -> Result<(), SolveAvailabilityError> {
        if let Some(to) = self.intern(endpoint)? {
            push(&mut self.edges[from], to)?;
            push(&mut self.reverse[to], from)?;
        }
        Ok(())
    }
    fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        let mut total = sum(&[
            bytes::<ExtrusionEndpoint>(self.nodes.capacity())?,
            bytes::<(ExtrusionEndpoint, usize)>(self.positions.capacity())?,
            bytes::<Vec<usize>>(self.edges.capacity())?,
            bytes::<Vec<usize>>(self.reverse.capacity())?,
        ])?;
        for edges in self.edges.iter().chain(&self.reverse) {
            total = total
                .checked_add(bytes::<usize>(edges.capacity())?)
                .ok_or_else(exhausted)?;
        }
        Ok(total)
    }
    fn components(&self) -> Result<(Vec<usize>, usize), SolveAvailabilityError> {
        let mut seen = Vec::new();
        seen.try_reserve_exact(self.nodes.len())
            .map_err(|_| exhausted())?;
        seen.resize(self.nodes.len(), false);
        let mut finish = Vec::new();
        let mut stack = Vec::new();
        for start in 0..self.nodes.len() {
            if seen[start] {
                continue;
            }
            seen[start] = true;
            push(&mut stack, (start, 0usize))?;
            while let Some((node, edge)) = stack.last_mut() {
                if *edge == self.edges[*node].len() {
                    let node = *node;
                    stack.pop();
                    push(&mut finish, node)?;
                } else {
                    let child = self.edges[*node][*edge];
                    *edge += 1;
                    if !seen[child] {
                        seen[child] = true;
                        push(&mut stack, (child, 0))?;
                    }
                }
            }
        }
        let mut components = Vec::new();
        components
            .try_reserve_exact(self.nodes.len())
            .map_err(|_| exhausted())?;
        components.resize(self.nodes.len(), usize::MAX);
        let mut component = 0;
        for &start in finish.iter().rev() {
            if components[start] != usize::MAX {
                continue;
            }
            components[start] = component;
            push(&mut stack, (start, 0))?;
            while let Some((node, _)) = stack.pop() {
                for &child in &self.reverse[node] {
                    if components[child] == usize::MAX {
                        components[child] = component;
                        push(&mut stack, (child, 0))?;
                    }
                }
            }
            component += 1;
        }
        let scratch = sum(&[
            bytes::<bool>(seen.capacity())?,
            bytes::<usize>(finish.capacity())?,
            bytes::<usize>(components.capacity())?,
            bytes::<(usize, usize)>(stack.capacity())?,
        ])?;
        Ok((components, scratch))
    }
}
