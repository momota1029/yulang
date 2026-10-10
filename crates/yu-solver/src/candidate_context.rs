//! Exact structural context relation authority for the private candidate.
//! Derivations are a separate fiber: retaining another origin does not create
//! another semantic task or unfold a recursive identity derivation.
use crate::candidate_effect::BoundKey;
use crate::*;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct RelationId(pub u32);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ContextId(u32);
const IDENTITY: ContextId = ContextId(0);
// This handle names a complete immutable operation payload. Its source-owned
// constructor is a later seam; nominal effect or attachment IDs are not weights.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(
    not(test),
    allow(dead_code, reason = "operation payload construction is a later gate")
)]
struct LocalWeightId(u32);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct EntryCertificateId(u32);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(
    not(test),
    allow(dead_code, reason = "context propagation is a later gate")
)]
enum ContextExpr {
    PrefixLeft {
        weight: LocalWeightId,
        input: ContextId,
    },
    SuffixRightPops {
        input: ContextId,
        weight: LocalWeightId,
    },
    Swap {
        input: ContextId,
    },
    BothFromRight {
        input: ContextId,
        certificate: EntryCertificateId,
    },
    Replay {
        lower: ContextId,
        upper: ContextId,
    },
    WithoutLeftFilter {
        input: ContextId,
    },
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct RelationKey {
    pair: TypedPairKey,
    context: ContextId,
}
#[derive(Clone, Copy, Debug)]
struct Relation {
    key: RelationKey,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Dependency {
    Derived {
        child: RelationId,
        parent: RelationId,
    },
    // Parent order is lower then upper, independently of insertion direction.
    Replay {
        child: RelationId,
        lower: RelationId,
        upper: RelationId,
        lower_input: BoundKey,
        upper_input: BoundKey,
    },
    Transport {
        child: RelationId,
        parent: RelationId,
        use_origin: usize,
    },
}
#[derive(Debug)]
#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "source origin certificates are retained independently of semantic conflict traversal"
    )
)]
struct Origin {
    relation: RelationId,
    occurrence: ConstraintOccurrenceId,
}
#[derive(Debug, Default)]
pub(super) struct State {
    contexts: Vec<ContextExpr>,
    context_keys: HashMap<ContextExpr, ContextId>,
    relations: Vec<Relation>,
    keys: HashMap<RelationKey, RelationId>,
    dependencies: Vec<Dependency>,
    dependency_keys: HashSet<Dependency>,
    origins: Vec<Origin>,
    bounds: HashMap<BoundKey, RelationId>,
    bound_keys: Vec<BoundKey>,
    uses: usize,
    edges: HashMap<RelationId, Vec<RelationId>>,
    edge_keys: HashSet<(RelationId, RelationId)>,
    edge_log: Vec<(RelationId, RelationId)>,
    edge_bytes: usize,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Checkpoint {
    contexts: usize,
    relations: usize,
    dependencies: usize,
    origins: usize,
    bounds: usize,
    uses: usize,
    edges: usize,
}
fn exhausted() -> SolveAvailabilityError {
    SolveAvailabilityError::IdentityExhausted
}
impl State {
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            contexts: self.contexts.len(),
            relations: self.relations.len(),
            dependencies: self.dependencies.len(),
            origins: self.origins.len(),
            bounds: self.bound_keys.len(),
            uses: self.uses,
            edges: self.edge_log.len(),
        }
    }
    pub fn rollback(&mut self, checkpoint: Checkpoint) {
        for context in self.contexts.drain(checkpoint.contexts..) {
            self.context_keys.remove(&context);
        }
        for relation in self.relations.drain(checkpoint.relations..) {
            self.keys.remove(&relation.key);
        }
        for dependency in self.dependencies.drain(checkpoint.dependencies..) {
            self.dependency_keys.remove(&dependency);
        }
        for bound in self.bound_keys.drain(checkpoint.bounds..) {
            self.bounds.remove(&bound);
        }
        self.origins.truncate(checkpoint.origins);
        self.uses = checkpoint.uses;
        for (parent, child) in self.edge_log.drain(checkpoint.edges..).rev() {
            self.edge_keys.remove(&(parent, child));
            let entries = self.edges.get_mut(&parent).unwrap();
            assert_eq!(entries.pop(), Some(child));
            if entries.is_empty() {
                self.edge_bytes -= self.edges.remove(&parent).unwrap().capacity()
                    * std::mem::size_of::<RelationId>();
            }
        }
    }
    pub fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        let parts = [
            self.contexts
                .capacity()
                .checked_mul(std::mem::size_of::<ContextExpr>()),
            self.context_keys
                .capacity()
                .checked_mul(std::mem::size_of::<(ContextExpr, ContextId)>()),
            self.relations
                .capacity()
                .checked_mul(std::mem::size_of::<Relation>()),
            self.keys
                .capacity()
                .checked_mul(std::mem::size_of::<(RelationKey, RelationId)>()),
            self.dependencies
                .capacity()
                .checked_mul(std::mem::size_of::<Dependency>()),
            self.dependency_keys
                .capacity()
                .checked_mul(std::mem::size_of::<Dependency>()),
            self.origins
                .capacity()
                .checked_mul(std::mem::size_of::<Origin>()),
            self.bounds
                .capacity()
                .checked_mul(std::mem::size_of::<(BoundKey, RelationId)>()),
            self.bound_keys
                .capacity()
                .checked_mul(std::mem::size_of::<BoundKey>()),
        ];
        let owned = parts.into_iter().try_fold(0usize, |n, part| {
            n.checked_add(part.ok_or_else(exhausted)?)
                .ok_or_else(exhausted)
        })?;
        owned
            .checked_add(
                self.edges
                    .capacity()
                    .checked_mul(std::mem::size_of::<(RelationId, Vec<RelationId>)>())
                    .ok_or_else(exhausted)?,
            )
            .and_then(|n| {
                n.checked_add(
                    self.edge_keys
                        .capacity()
                        .checked_mul(std::mem::size_of::<(RelationId, RelationId)>())?,
                )
            })
            .and_then(|n| {
                n.checked_add(
                    self.edge_log
                        .capacity()
                        .checked_mul(std::mem::size_of::<(RelationId, RelationId)>())?,
                )
            })
            .and_then(|n| n.checked_add(self.edge_bytes))
            .ok_or_else(exhausted)
    }
    #[cfg(test)]
    pub fn enumerated_bytes(&self) -> usize {
        let adjacency_bytes = self
            .edges
            .values()
            .map(|entries| entries.capacity() * std::mem::size_of::<RelationId>())
            .sum::<usize>();
        assert_eq!(self.edge_bytes, adjacency_bytes);
        self.contexts.capacity() * std::mem::size_of::<ContextExpr>()
            + self.context_keys.capacity() * std::mem::size_of::<(ContextExpr, ContextId)>()
            + self.relations.capacity() * std::mem::size_of::<Relation>()
            + self.keys.capacity() * std::mem::size_of::<(RelationKey, RelationId)>()
            + self.dependencies.capacity() * std::mem::size_of::<Dependency>()
            + self.dependency_keys.capacity() * std::mem::size_of::<Dependency>()
            + self.origins.capacity() * std::mem::size_of::<Origin>()
            + self.bounds.capacity() * std::mem::size_of::<(BoundKey, RelationId)>()
            + self.bound_keys.capacity() * std::mem::size_of::<BoundKey>()
            + self.edges.capacity() * std::mem::size_of::<(RelationId, Vec<RelationId>)>()
            + self.edge_keys.capacity() * std::mem::size_of::<(RelationId, RelationId)>()
            + self.edge_log.capacity() * std::mem::size_of::<(RelationId, RelationId)>()
            + adjacency_bytes
    }
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "context propagation is a later gate")
    )]
    fn context(&mut self, expression: ContextExpr) -> Result<ContextId, SolveAvailabilityError> {
        match expression {
            ContextExpr::PrefixLeft { input, .. }
            | ContextExpr::SuffixRightPops { input, .. }
            | ContextExpr::Swap { input }
            | ContextExpr::BothFromRight { input, .. }
            | ContextExpr::WithoutLeftFilter { input } => self.assert_context(input),
            ContextExpr::Replay { lower, upper } => {
                self.assert_context(lower);
                self.assert_context(upper);
            }
        }
        if let Some(&id) = self.context_keys.get(&expression) {
            return Ok(id);
        }
        let id = ContextId(
            u32::try_from(self.contexts.len())
                .map_err(|_| exhausted())?
                .checked_add(1)
                .ok_or_else(exhausted)?,
        );
        self.contexts.try_reserve(1).map_err(|_| exhausted())?;
        self.context_keys.try_reserve(1).map_err(|_| exhausted())?;
        self.contexts.push(expression);
        self.context_keys.insert(expression, id);
        Ok(id)
    }
    fn assert_context(&self, context: ContextId) {
        assert!(
            context == IDENTITY || context.0 as usize <= self.contexts.len(),
            "context must be identity or an already interned node"
        );
    }
    fn relation(
        &mut self,
        pair: TypedPairKey,
        context: ContextId,
    ) -> Result<RelationId, SolveAvailabilityError> {
        self.assert_context(context);
        let key = RelationKey { pair, context };
        if let Some(&id) = self.keys.get(&key) {
            return Ok(id);
        }
        let id = RelationId(u32::try_from(self.relations.len()).map_err(|_| exhausted())?);
        self.relations.try_reserve(1).map_err(|_| exhausted())?;
        self.keys.try_reserve(1).map_err(|_| exhausted())?;
        self.relations.push(Relation { key });
        self.keys.insert(key, id);
        Ok(id)
    }
    pub fn begin_use(&mut self) -> Result<usize, SolveAvailabilityError> {
        self.uses = self.uses.checked_add(1).ok_or_else(exhausted)?;
        Ok(self.uses)
    }
    pub fn contains(&self, pair: TypedPairKey) -> bool {
        self.keys.contains_key(&RelationKey {
            pair,
            context: IDENTITY,
        })
    }
    fn dependency(&mut self, dependency: Dependency) -> Result<(), SolveAvailabilityError> {
        if self.dependency_keys.contains(&dependency) {
            return Ok(());
        }
        self.dependencies.try_reserve(1).map_err(|_| exhausted())?;
        self.dependency_keys
            .try_reserve(1)
            .map_err(|_| exhausted())?;
        match dependency {
            Dependency::Derived { child, parent } => self.edge(parent, child)?,
            // Transport retains provenance across instantiation and row
            // lifecycle changes; it is not a constraint from the template to
            // a fresh use and must not replay that use's conflicts upstream.
            Dependency::Transport { .. } => {}
            Dependency::Replay {
                child,
                lower,
                upper,
                ..
            } => {
                self.edge(lower, child)?;
                self.edge(upper, child)?;
            }
        }
        self.dependencies.push(dependency);
        self.dependency_keys.insert(dependency);
        Ok(())
    }
    fn edge(
        &mut self,
        parent: RelationId,
        child: RelationId,
    ) -> Result<(), SolveAvailabilityError> {
        if self.edge_keys.contains(&(parent, child)) {
            return Ok(());
        }
        self.edges.try_reserve(1).map_err(|_| exhausted())?;
        self.edge_keys.try_reserve(1).map_err(|_| exhausted())?;
        self.edge_log.try_reserve(1).map_err(|_| exhausted())?;
        let new = !self.edges.contains_key(&parent);
        let mut fresh = Vec::new();
        let entries = if new {
            &mut fresh
        } else {
            self.edges.get_mut(&parent).unwrap()
        };
        let old = entries.capacity();
        entries.try_reserve(1).map_err(|_| exhausted())?;
        self.edge_bytes = self
            .edge_bytes
            .checked_add(
                (entries.capacity() - old)
                    .checked_mul(std::mem::size_of::<RelationId>())
                    .ok_or_else(exhausted)?,
            )
            .ok_or_else(exhausted)?;
        entries.push(child);
        if new {
            self.edges.insert(parent, fresh);
        }
        self.edge_keys.insert((parent, child));
        self.edge_log.push((parent, child));
        Ok(())
    }
    pub fn children(&self, pair: TypedPairKey) -> impl Iterator<Item = TypedPairKey> + '_ {
        self.keys
            .get(&RelationKey {
                pair,
                context: IDENTITY,
            })
            .and_then(|id| self.edges.get(id))
            .into_iter()
            .flatten()
            .map(|id| self.relations[id.0 as usize].key.pair)
    }
    pub fn bound(&self, key: BoundKey) -> Option<RelationId> {
        self.bounds.get(&key).copied()
    }
    fn attach(
        &mut self,
        key: BoundKey,
        relation: RelationId,
    ) -> Result<(), SolveAvailabilityError> {
        if self.bounds.contains_key(&key) {
            return Ok(());
        }
        self.bounds.try_reserve(1).map_err(|_| exhausted())?;
        self.bound_keys.try_reserve(1).map_err(|_| exhausted())?;
        self.bounds.insert(key, relation);
        self.bound_keys.push(key);
        Ok(())
    }
}
pub(super) fn task_pair(task: LiveConstraintTask) -> TypedPairKey {
    match task {
        LiveConstraintTask::Value(pair) => TypedPairKey::Value(pair),
        LiveConstraintTask::Effect(lower, upper) => TypedPairKey::Effect { lower, upper },
    }
}
pub(super) fn bound_pair(BoundKey(owner, side, item): BoundKey) -> TypedPairKey {
    let (lower, upper) = if side == Polarity::Positive {
        (item, owner)
    } else {
        (owner, item)
    };
    match (lower, upper) {
        (ExtrusionEndpoint::Value(lower), ExtrusionEndpoint::Value(upper)) => {
            TypedPairKey::Value(CanonicalValuePairKey { lower, upper })
        }
        (ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(upper)) => {
            TypedPairKey::Effect { lower, upper }
        }
        _ => unreachable!("bound component kind"),
    }
}
impl InferenceSession {
    pub(super) fn candidate_context_pair(&self, pair: TypedPairKey) -> TypedPairKey {
        match pair {
            TypedPairKey::Value(pair) => TypedPairKey::Value(CanonicalValuePairKey {
                lower: self.canonical_value(pair.lower),
                upper: self.canonical_value(pair.upper),
            }),
            TypedPairKey::Effect { lower, upper } => TypedPairKey::Effect {
                lower: self.canonical_effect(lower),
                upper: self.canonical_effect(upper),
            },
        }
    }
    pub(super) fn candidate_context_seed(
        &mut self,
        task: LiveConstraintTask,
        occurrence: &ConstraintOccurrenceId,
    ) -> Result<(), SolveAvailabilityError> {
        if self.candidate_graph.is_none() {
            return Ok(());
        }
        let pair = self.candidate_context_pair(task_pair(task));
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let relation = state.relation(pair, IDENTITY)?;
        state.origins.try_reserve(1).map_err(|_| exhausted())?;
        state.origins.push(Origin {
            relation,
            occurrence: occurrence.clone(),
        });
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
    pub(super) fn candidate_context_admit(
        &mut self,
        task: LiveConstraintTask,
    ) -> Result<(), SolveAvailabilityError> {
        let Some(graph) = &self.candidate_graph else {
            return Ok(());
        };
        let parent = graph
            .intrusion
            .effect_algebra
            .processing
            .map(|p| self.candidate_context_pair(p));
        let pair = self.candidate_context_pair(task_pair(task));
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let child = state.relation(pair, IDENTITY)?;
        if let Some(parent) = parent {
            let parent = state.relation(parent, IDENTITY)?;
            state.dependency(Dependency::Derived { child, parent })?;
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
    pub(super) fn candidate_context_bound(
        &mut self,
        bound: BoundKey,
        origin: TypedPairKey,
    ) -> Result<(), SolveAvailabilityError> {
        let pair = self.candidate_context_pair(bound_pair(bound));
        let origin = self.candidate_context_pair(origin);
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let child = state.relation(pair, IDENTITY)?;
        let parent = state.relation(origin, IDENTITY)?;
        state.dependency(Dependency::Derived { child, parent })?;
        state.attach(bound, child)
    }
    pub(super) fn candidate_context_replay(
        &mut self,
        lower_input: BoundKey,
        upper_input: BoundKey,
        task: LiveConstraintTask,
    ) -> Result<(), SolveAvailabilityError> {
        let pair = self.candidate_context_pair(task_pair(task));
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let child = state.relation(pair, IDENTITY)?;
        if let (Some(lower), Some(upper)) = (state.bound(lower_input), state.bound(upper_input)) {
            state.dependency(Dependency::Replay {
                child,
                lower,
                upper,
                lower_input,
                upper_input,
            })?;
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
    pub(super) fn candidate_context_transport(
        &mut self,
        parent: RelationId,
        to: BoundKey,
        use_origin: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let pair = self.candidate_context_pair(bound_pair(to));
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let child = state.relation(pair, IDENTITY)?;
        state.dependency(Dependency::Transport {
            child,
            parent,
            use_origin,
        })?;
        state.attach(to, child)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
}
#[cfg(test)]
#[path = "candidate_context_tests.rs"]
mod tests;
