//! Exact structural context relation authority for the private candidate.
//! Derivations are a separate fiber: retaining another origin does not create
//! another semantic task or unfold a recursive identity derivation.
use crate::candidate_effect::BoundKey;
use crate::*;
use yu_hir::shadow::{SourceEffectId, SourceNodeKey};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct RelationId(pub u32);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ContextId(u32);
const IDENTITY: ContextId = ContextId(0);
// A payload handle is independent of nominal members and boundary identities.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct LocalWeightId(u32);
#[derive(Debug)]
struct LocalWeight {
    left_word: [(); 0],
    allowed: Vec<SourceEffectId>,
    right_pops: [(); 0],
    boundary: u32,
    owner: DefinitionRootId,
    position: SourceNodeKey,
    attachment: Option<AttachmentSet>,
}
// The payload ID is the set identity; ordinals index its resolved allowed operands.
#[derive(Debug)]
struct AttachmentSet {
    composed_polarity: Polarity,
    lexical_scope: candidate_effect::AnnotationScope,
    member_ordinals: Vec<usize>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct AttachmentSource {
    pub composed_polarity: Polarity,
    pub lexical_scope: candidate_effect::AnnotationScope,
}
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
    previous_on_pair: Option<RelationId>,
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
    weights: Vec<LocalWeight>,
    weight_bytes: usize,
    contexts: Vec<ContextExpr>,
    context_keys: HashMap<ContextExpr, ContextId>,
    relations: Vec<Relation>,
    keys: HashMap<RelationKey, RelationId>,
    pair_heads: HashMap<TypedPairKey, RelationId>,
    dependencies: Vec<Dependency>,
    dependency_keys: HashSet<Dependency>,
    origins: Vec<Origin>,
    bounds: HashMap<BoundKey, usize>,
    bound_keys: Vec<(BoundKey, RelationId, Option<usize>)>,
    replay_heads: HashMap<(BoundKey, BoundKey), (Option<usize>, Option<usize>)>,
    replay_log: Vec<((BoundKey, BoundKey), Option<(Option<usize>, Option<usize>)>)>,
    uses: usize,
    edges: HashMap<RelationId, Vec<RelationId>>,
    edge_keys: HashSet<(RelationId, RelationId)>,
    edge_log: Vec<(RelationId, RelationId)>,
    edge_bytes: usize,
    pub processing: Option<RelationId>,
    discharged: HashSet<RelationId>,
    discharge_log: Vec<RelationId>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Checkpoint {
    weights: usize,
    contexts: usize,
    relations: usize,
    dependencies: usize,
    origins: usize,
    bounds: usize,
    uses: usize,
    replay_log: usize,
    edges: usize,
    processing: Option<RelationId>,
    discharges: usize,
}
fn exhausted() -> SolveAvailabilityError {
    SolveAvailabilityError::IdentityExhausted
}
impl State {
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            weights: self.weights.len(),
            contexts: self.contexts.len(),
            relations: self.relations.len(),
            dependencies: self.dependencies.len(),
            origins: self.origins.len(),
            bounds: self.bound_keys.len(),
            uses: self.uses,
            replay_log: self.replay_log.len(),
            edges: self.edge_log.len(),
            processing: self.processing,
            discharges: self.discharge_log.len(),
        }
    }
    pub fn rollback(&mut self, checkpoint: Checkpoint) {
        for weight in self.weights.drain(checkpoint.weights..) {
            self.weight_bytes -= weight.allowed.capacity() * std::mem::size_of::<SourceEffectId>()
                + weight.attachment.as_ref().map_or(0, |set| set.member_ordinals.capacity() * std::mem::size_of::<usize>());
        }
        for (key, previous) in self.replay_log.drain(checkpoint.replay_log..).rev() {
            if let Some(previous) = previous { self.replay_heads.insert(key, previous); }
            else { self.replay_heads.remove(&key); }
        }
        for relation in self.discharge_log.drain(checkpoint.discharges..) {
            self.discharged.remove(&relation);
        }
        for context in self.contexts.drain(checkpoint.contexts..) {
            self.context_keys.remove(&context);
        }
        for relation in self.relations.drain(checkpoint.relations..).rev() {
            self.keys.remove(&relation.key);
            if let Some(previous) = relation.previous_on_pair {
                self.pair_heads.insert(relation.key.pair, previous);
            } else {
                self.pair_heads.remove(&relation.key.pair);
            }
        }
        for dependency in self.dependencies.drain(checkpoint.dependencies..) {
            self.dependency_keys.remove(&dependency);
        }
        for (bound, _, previous) in self.bound_keys.drain(checkpoint.bounds..).rev() {
            if let Some(previous) = previous { self.bounds.insert(bound, previous); }
            else { self.bounds.remove(&bound); }
        }
        self.origins.truncate(checkpoint.origins);
        self.uses = checkpoint.uses;
        self.processing = checkpoint.processing;
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
            Some(self.weight_bytes),
            self.weights.capacity().checked_mul(std::mem::size_of::<LocalWeight>()),
            self.replay_heads.capacity().checked_mul(std::mem::size_of::<((BoundKey, BoundKey), (Option<usize>, Option<usize>))>()),
            self.replay_log.capacity().checked_mul(std::mem::size_of::<((BoundKey, BoundKey), Option<(Option<usize>, Option<usize>)>)>()),
            self.discharged.capacity().checked_mul(std::mem::size_of::<RelationId>()),
            self.discharge_log.capacity().checked_mul(std::mem::size_of::<RelationId>()),
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
            self.pair_heads
                .capacity()
                .checked_mul(std::mem::size_of::<(TypedPairKey, RelationId)>()),
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
                .checked_mul(std::mem::size_of::<(BoundKey, usize)>()),
            self.bound_keys
                .capacity()
                .checked_mul(std::mem::size_of::<(BoundKey, RelationId, Option<usize>)>()),
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
        self.weights.capacity() * std::mem::size_of::<LocalWeight>()
            + self.weights.iter().map(|w| w.allowed.capacity() * std::mem::size_of::<SourceEffectId>()
                + w.attachment.as_ref().map_or(0, |set| set.member_ordinals.capacity() * std::mem::size_of::<usize>())).sum::<usize>()
            + self.replay_heads.capacity() * std::mem::size_of::<((BoundKey, BoundKey), (Option<usize>, Option<usize>))>()
            + self.replay_log.capacity() * std::mem::size_of::<((BoundKey, BoundKey), Option<(Option<usize>, Option<usize>)>)>()
            + self.discharged.capacity() * std::mem::size_of::<RelationId>()
            + self.discharge_log.capacity() * std::mem::size_of::<RelationId>()
            + self.contexts.capacity() * std::mem::size_of::<ContextExpr>()
            + self.context_keys.capacity() * std::mem::size_of::<(ContextExpr, ContextId)>()
            + self.relations.capacity() * std::mem::size_of::<Relation>()
            + self.keys.capacity() * std::mem::size_of::<(RelationKey, RelationId)>()
            + self.pair_heads.capacity() * std::mem::size_of::<(TypedPairKey, RelationId)>()
            + self.dependencies.capacity() * std::mem::size_of::<Dependency>()
            + self.dependency_keys.capacity() * std::mem::size_of::<Dependency>()
            + self.origins.capacity() * std::mem::size_of::<Origin>()
            + self.bounds.capacity() * std::mem::size_of::<(BoundKey, usize)>()
            + self.bound_keys.capacity() * std::mem::size_of::<(BoundKey, RelationId, Option<usize>)>()
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
    pub fn source_weight(&mut self, boundary: u32, owner: &DefinitionRootId, position: &SourceNodeKey, allowed: &[SourceEffectId], source: Option<AttachmentSource>) -> Result<LocalWeightId, SolveAvailabilityError> {
        let id = LocalWeightId(u32::try_from(self.weights.len()).map_err(|_| exhausted())?);
        let mut members = Vec::new();
        members.try_reserve_exact(allowed.len()).map_err(|_| exhausted())?;
        members.extend_from_slice(allowed);
        let attachment = source.map(|source| {
            let mut member_ordinals = Vec::new();
            member_ordinals.try_reserve_exact(allowed.len()).map_err(|_| exhausted())?;
            member_ordinals.extend(0..allowed.len());
            Ok::<_, SolveAvailabilityError>(AttachmentSet {
                composed_polarity: source.composed_polarity,
                lexical_scope: source.lexical_scope,
                member_ordinals,
            })
        }).transpose()?;
        let ordinal_bytes = attachment.as_ref().map_or(Some(0), |set| set.member_ordinals.capacity().checked_mul(std::mem::size_of::<usize>())).ok_or_else(exhausted)?;
        let weight_bytes = self.weight_bytes.checked_add(ordinal_bytes).and_then(|n| n.checked_add(members.capacity().checked_mul(std::mem::size_of::<SourceEffectId>())?)).ok_or_else(exhausted)?;
        self.weights.try_reserve(1).map_err(|_| exhausted())?;
        self.weights.push(LocalWeight { left_word: [], allowed: members, right_pops: [], boundary, owner: owner.clone(), position: position.clone(), attachment });
        self.weight_bytes = weight_bytes;
        Ok(id)
    }
    pub fn attachment_source(&self, weight: LocalWeightId) -> Option<AttachmentSource> {
        self.weights[weight.0 as usize].attachment.as_ref().map(|set| AttachmentSource {
            composed_polarity: set.composed_polarity,
            lexical_scope: set.lexical_scope.clone(),
        })
    }
    pub fn allowed(&self, weight: LocalWeightId) -> &[SourceEffectId] {
        &self.weights[weight.0 as usize].allowed
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
        self.pair_heads.try_reserve(1).map_err(|_| exhausted())?;
        let previous_on_pair = self.pair_heads.insert(pair, id);
        self.relations.push(Relation { key, previous_on_pair });
        self.keys.insert(key, id);
        Ok(id)
    }
    pub fn begin_use(&mut self) -> Result<usize, SolveAvailabilityError> {
        self.uses = self.uses.checked_add(1).ok_or_else(exhausted)?;
        Ok(self.uses)
    }
    pub fn contains(&self, pair: TypedPairKey) -> bool {
        self.pair_heads.contains_key(&pair)
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
        std::iter::successors(self.pair_heads.get(&pair).copied(), |id| {
            self.relations[id.0 as usize].previous_on_pair
        })
        .filter_map(|id| self.edges.get(&id))
        .flatten()
        .map(|id| self.relations[id.0 as usize].key.pair)
    }
    #[cfg(test)]
    pub fn bound(&self, key: BoundKey) -> Option<RelationId> {
        self.bound_relations(key).next()
    }
    pub fn bound_relations(&self, key: BoundKey) -> impl Iterator<Item = RelationId> + '_ {
        std::iter::successors(self.bounds.get(&key).copied(), |&index| {
            self.bound_keys[index].2
        }).map(|index| self.bound_keys[index].1)
    }
    pub fn bound_cursor(&self, key: BoundKey) -> Option<usize> {
        self.bounds.get(&key).copied()
    }
    pub fn bound_entry(&self, index: usize) -> (RelationId, Option<usize>) {
        let (_, relation, next) = self.bound_keys[index];
        (relation, next)
    }
    fn replay_progress(&mut self, key: (BoundKey, BoundKey), heads: (Option<usize>, Option<usize>)) -> Result<(), SolveAvailabilityError> {
        self.replay_heads.try_reserve(1).map_err(|_| exhausted())?;
        self.replay_log.try_reserve(1).map_err(|_| exhausted())?;
        let previous = self.replay_heads.insert(key, heads);
        self.replay_log.push((key, previous));
        Ok(())
    }
    fn attach(
        &mut self,
        key: BoundKey,
        relation: RelationId,
    ) -> Result<(), SolveAvailabilityError> {
        if self.bound_relations(key).any(|existing| existing == relation) {
            return Ok(());
        }
        self.bounds.try_reserve(1).map_err(|_| exhausted())?;
        self.bound_keys.try_reserve(1).map_err(|_| exhausted())?;
        let previous = self.bounds.insert(key, self.bound_keys.len());
        self.bound_keys.push((key, relation, previous));
        Ok(())
    }
    fn post_check_context(&self, relation: RelationId) -> ContextId {
        let context = self.relations[relation.0 as usize].key.context;
        if context != IDENTITY && matches!(self.contexts[context.0 as usize - 1],
            ContextExpr::PrefixLeft { input: IDENTITY, .. }) {
            // This executable filter is consumed at insertion; its bound and
            // derivation retain the current/future obligations.
            IDENTITY
        } else { context }
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
    fn candidate_closed_allowance(&self, pair: TypedPairKey) -> Option<LocalWeightId> {
        let TypedPairKey::Effect { upper: EffectEndpointKey::Allowance(view), .. } = pair else { return None; };
        let view_data = &self.candidate_graph.as_ref()?.intrusion.effect_algebra.views[view as usize];
        view_data.closed_weight
    }
    fn candidate_context_source(&mut self, pair: TypedPairKey) -> Result<ContextId, SolveAvailabilityError> {
        let weight = self.candidate_closed_allowance(pair);
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        match weight {
            Some(weight) => state.context(ContextExpr::PrefixLeft { weight, input: IDENTITY }),
            None => Ok(IDENTITY),
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
        let context = self.candidate_context_source(pair)?;
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let relation = state.relation(pair, context)?;
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
    ) -> Result<Option<RelationId>, SolveAvailabilityError> {
        let Some(graph) = &self.candidate_graph else { return Ok(None); };
        let retained_parent = graph.intrusion.effect_algebra.context.processing;
        let parent = graph.intrusion.effect_algebra.processing
            .map(|p| self.candidate_context_pair(p));
        let pair = self.candidate_context_pair(task_pair(task));
        let context = self.candidate_context_source(pair)?;
        let parent_context = parent.map(|pair| self.candidate_context_source(pair)).transpose()?;
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let child = state.relation(pair, context)?;
        if let Some(parent) = parent {
            let parent = match retained_parent {
                Some(id) if state.relations[id.0 as usize].key.pair == parent => id,
                _ => state.relation(parent, parent_context.unwrap())?,
            };
            state.dependency(Dependency::Derived { child, parent })?;
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(Some(child))
    }
    // Admission checks run before endpoint memoization and equality handling.
    // Once consumed, the normal Allowance bound retains current/future-lower
    // obligations. Children use the discharged context, not a repeated filter.
    pub(super) fn candidate_context_execute(
        &mut self,
        task: LiveConstraintTask,
        relation: Option<RelationId>,
    ) -> Result<bool, SolveAvailabilityError> {
        let Some(relation) = relation else { return Ok(false); };
        let state = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        let key = state.relations[relation.0 as usize].key;
        assert_eq!(key.pair, self.candidate_context_pair(task_pair(task)), "task retains its relation endpoints");
        if key.context == IDENTITY { return Ok(false); }
        if state.discharged.contains(&relation) { return Ok(true); }
        let ContextExpr::PrefixLeft { weight, input: IDENTITY } = state.contexts[key.context.0 as usize - 1] else {
            // Only closed source filters have an executable consumer in this
            // slice. Other ContextExpr constructors are not admitted here.
            return Err(exhausted());
        };
        let payload = state.weights.get(weight.0 as usize).ok_or_else(exhausted)?;
        let view = payload.boundary;
        let boundary = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[view as usize];
        assert_eq!((&payload.owner, &payload.position), (&boundary.owner, &boundary.position));
        assert!(payload.left_word.is_empty() && payload.right_pops.is_empty());
        let lower = match task {
            LiveConstraintTask::Effect(lower, _) => lower,
            LiveConstraintTask::Value(_) => return Err(exhausted()),
        };
        let upper = EffectEndpointKey::Allowance(view);
        let registered = match self.canonical_effect(lower) {
            EffectEndpointKey::EffectRow(row) => self.effect_bounds[row as usize].exact_non_variable_uppers.contains(&upper),
            _ => false,
        };
        if registered {
            // The allowance already owns its executable bound, but this
            // source occurrence still needs an edge to that bound. Otherwise
            // a conflict recorded before this relation was admitted cannot
            // be replayed at this occurrence.
            let EffectEndpointKey::EffectRow(row) = self.canonical_effect(lower) else { unreachable!() };
            self.candidate_bound_origin(
                BoundKey(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row)),
                    Polarity::Negative,
                    ExtrusionEndpoint::Effect(upper),
                ),
                Some(task_pair(task)),
            )?;
            self.candidate_replay_bound(
                ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row)),
                Polarity::Negative,
                ExtrusionEndpoint::Effect(upper),
                None,
            )?;
        } else {
            self.candidate_apply_effect(lower, upper)?;
        }
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        state.discharged.try_reserve(1).map_err(|_| exhausted())?;
        state.discharge_log.try_reserve(1).map_err(|_| exhausted())?;
        state.discharged.insert(relation);
        state.discharge_log.push(relation);
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(true)
    }
    pub(super) fn candidate_context_bound(
        &mut self,
        bound: BoundKey,
        origin: TypedPairKey,
    ) -> Result<(), SolveAvailabilityError> {
        let pair = self.candidate_context_pair(bound_pair(bound));
        let origin = self.candidate_context_pair(origin);
        let origin_context = self.candidate_context_source(origin)?;
        let retained_parent = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.processing;
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let parent = match retained_parent {
            Some(id) if state.relations[id.0 as usize].key.pair == origin => id,
            _ => state.relation(origin, origin_context)?,
        };
        let child = state.relation(pair, state.post_check_context(parent))?;
        state.dependency(Dependency::Derived { child, parent })?;
        state.attach(bound, child)
    }
    pub(super) fn candidate_context_replay<T>(
        &mut self,
        lower_input: BoundKey,
        upper_input: BoundKey,
        task: LiveConstraintTask,
        publish: impl FnOnce(&mut Self, &[RelationId]) -> Result<T, SolveAvailabilityError>,
    ) -> Result<T, SolveAvailabilityError> {
        self.candidate_context_replay_impl(lower_input, upper_input, task, false, publish)
    }
    pub(super) fn candidate_context_restore_replay<T>(
        &mut self,
        lower_input: BoundKey,
        upper_input: BoundKey,
        task: LiveConstraintTask,
        publish: impl FnOnce(&mut Self, &[RelationId]) -> Result<T, SolveAvailabilityError>,
    ) -> Result<T, SolveAvailabilityError> {
        self.candidate_context_replay_impl(lower_input, upper_input, task, true, publish)
    }
    fn candidate_context_replay_impl<T>(
        &mut self,
        lower_input: BoundKey,
        upper_input: BoundKey,
        task: LiveConstraintTask,
        incoming_use: bool,
        publish: impl FnOnce(&mut Self, &[RelationId]) -> Result<T, SolveAvailabilityError>,
    ) -> Result<T, SolveAvailabilityError> {
        let pair = self.candidate_context_pair(task_pair(task));
        let mut replay = Vec::new();
        let mut charge = 0;
        let result = (|| {
            let state = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
            let heads = (state.bound_cursor(lower_input), state.bound_cursor(upper_input));
            let recorded = state.replay_heads.get(&(lower_input, upper_input)).copied().unwrap_or((None, None));
            // Every incoming scheme use owns diagnostic replay, even when
            // ordinary propagation already admitted these exact dependencies.
            let old = if incoming_use { (None, None) } else { recorded };
            if !incoming_use && heads == old { return publish(self, &replay); }
            // Each newly retained fiber meets the opposite fibers once. Older
            // lower fibers meet only new uppers; the new/new quadrant is owned
            // by the first loop.
            for (start, stop, upper_start, upper_stop) in [
                (heads.0, old.0, heads.1, None),
                (old.0, None, heads.1, old.1),
            ] {
                if upper_start == upper_stop { continue; }
                let mut lower_cursor = start;
                while lower_cursor != stop {
                    let Some(index) = lower_cursor else { break; };
                    let (lower, next) = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_entry(index);
                    lower_cursor = next;
                    let mut upper_cursor = upper_start;
                    while upper_cursor != upper_stop {
                        let Some(index) = upper_cursor else { break; };
                        let (upper, next) = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_entry(index);
                        upper_cursor = next;
                        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                        let lower_context = state.relations[lower.0 as usize].key.context;
                        let upper_context = state.relations[upper.0 as usize].key.context;
                        // Empty-weight directed mix is identity; its ordered
                        // derivation remains in the dependency certificate.
                        let context = if lower_context == IDENTITY && upper_context == IDENTITY { IDENTITY }
                            else { state.context(ContextExpr::Replay { lower: lower_context, upper: upper_context })? };
                        let child = state.relation(pair, context)?;
                        let dependency = Dependency::Replay { child, lower, upper, lower_input, upper_input };
                        if !incoming_use && state.dependency_keys.contains(&dependency) { continue; }
                        state.dependency(dependency)?;
                        let old_capacity = replay.capacity();
                        replay.try_reserve(1).map_err(|_| exhausted())?;
                        self.candidate_scratch_growth(&mut charge,
                            (replay.capacity() - old_capacity).checked_mul(std::mem::size_of::<RelationId>()).ok_or_else(exhausted)?)?;
                        replay.push(child);
                    }
                }
            }
            if heads != recorded {
                self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.replay_progress((lower_input, upper_input), heads)?;
            }
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            publish(self, &replay)
        })();
        drop(replay);
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= charge;
        result
    }
    pub(super) fn candidate_context_canonicalize_bounds(&mut self) -> Result<(), SolveAvailabilityError> {
        // Representative changes affect third-owner incidence as well as the
        // merged row's outgoing bounds. Preserve the original fiber/provenance
        // and transport it to the canonical bound key before any replay.
        let count = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_keys.len();
        for index in 0..count {
            let (from, parent, _) = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_keys[index];
            let to = BoundKey(self.canonical_extrusion(from.0), from.1, self.canonical_extrusion(from.2));
            if to != from {
                self.candidate_context_transport(parent, to, 0)?;
                let pair = self.candidate_context_pair(bound_pair(to));
                let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                let child = state.relation(pair, state.post_check_context(parent))?;
                // Equality transport remains within this owner, unlike fresh
                // scheme uses: conflicts must retain the original derivation.
                state.dependency(Dependency::Derived { child, parent })?;
            }
        }
        Ok(())
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
        let child = state.relation(pair, state.post_check_context(parent))?;
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
