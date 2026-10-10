//! Private executable covariant annotation views at ordinary effect-row ports.
use crate::*;
use yu_hir::shadow::SourceNodeKey;
use yu_hir::HirLocalId;
use yu_hir::shadow::{
    SourceAnnotation, SourceAnnotationType, SourceAnnotationValue, SourceEffectId, SourceEffectRow,
};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct EffectOperandHandle {
    brand: u64,
    operand: OperandIdentity,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum OperandIdentity {
    Contribution(u32),
    AnnotationMember(u32, u32),
}
pub(super) enum ObservedOperand<'a> {
    Contribution(&'a Contribution),
    AnnotationMember {
        view: &'a View,
        member: u32,
        effect: &'a SourceEffectId,
    },
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct EffectAnnotationHandle {
    brand: u64,
    index: u32,
}
static NEXT_BRAND: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct BoundKey(pub ExtrusionEndpoint, pub Polarity, pub ExtrusionEndpoint);
#[derive(Clone, Copy, Debug)]
struct Conflict {
    operand: EffectOperandHandle,
    annotation: Option<EffectAnnotationHandle>,
}
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) enum AnnotationScope { Definition(DefinitionRootId), Local(HirLocalId) }
#[derive(Debug, Default)]
pub(super) struct State {
    pub formal_domains: HashMap<usize, Term>,
    pub(super) annotation_values: HashMap<(AnnotationScope, Box<str>), u32>,
    // Effect names share binding scope while remaining separate from value names.
    annotation_effects: HashMap<(AnnotationScope, Box<str>), u32>,
    pub contributions: Vec<Contribution>,
    pub views: Vec<View>,
    brand: u64,
    pub processing: Option<TypedPairKey>,
    edges: HashMap<TypedPairKey, Vec<TypedPairKey>>,
    edge_keys: HashSet<(TypedPairKey, TypedPairKey)>,
    origins: HashMap<BoundKey, Vec<TypedPairKey>>,
    origin_keys: HashSet<(BoundKey, TypedPairKey)>,
    conflicts: HashMap<TypedPairKey, Conflict>,
    nested_bytes: usize,
    evidence_bytes: usize,
    #[cfg(test)]
    fail_after_view: bool,
    #[cfg(test)]
    failed_view_sample: Option<(usize, usize)>,
    #[cfg(test)]
    failed_formal_sample: Option<(usize, usize, usize, usize, usize, usize)>,
}
#[derive(Debug)]
pub(super) struct Contribution {
    pub effect: SourceEffectId,
    pub origin: SourceNodeKey,
    pub instance: u32,
}
#[derive(Clone, Debug)]
pub(super) struct OperationOrigin {
    pub declaration: Arc<yu_hir::shadow::SourceOperationDeclaration>,
    pub occurrence: HirOccurrenceId,
    retained_bytes: usize,
}
#[derive(Clone, Debug)]
pub(super) enum ViewOrigin {
    Annotation,
    Operation(OperationOrigin),
}
enum SignatureContext<'a> {
    Annotation(&'a SourceAnnotation),
    Operation { declaration: &'a Arc<yu_hir::shadow::SourceOperationDeclaration>, owner: &'a DefinitionRootId, occurrence: &'a HirOccurrenceId, retained_bytes: usize },
}
impl SignatureContext<'_> {
    fn owner(&self) -> &DefinitionRootId { match self { Self::Annotation(a) => &a.owner, Self::Operation { owner, .. } => owner } }
    fn position(&self) -> &SourceNodeKey { match self { Self::Annotation(a) => &a.position, Self::Operation { declaration, .. } => &declaration.signature_position } }
    fn operation(&self) -> Option<OperationOrigin> { match self { Self::Annotation(_) => None, Self::Operation { declaration, occurrence, retained_bytes, .. } => Some(OperationOrigin { declaration: Arc::clone(declaration), occurrence: (*occurrence).clone(), retained_bytes: *retained_bytes }) } }
}
#[derive(Debug)]
pub(super) struct View {
    pub provenance: ViewOrigin,
    pub owner: DefinitionRootId,
    pub position: SourceNodeKey,
    pub allowed: Vec<SourceEffectId>,
    pub tail: Option<u32>,
}
pub(super) struct Checkpoint {
    contributions: usize,
    views: usize,
    nested_bytes: usize,
    processing: Option<TypedPairKey>,
    edges: Vec<(TypedPairKey, TypedPairKey, bool)>,
    origins: Vec<(BoundKey, TypedPairKey, bool)>,
    conflicts: Vec<TypedPairKey>,
    formal_domains: Vec<usize>,
    annotation_values: Vec<(AnnotationScope, Box<str>)>,
    annotation_effects: Vec<(AnnotationScope, Box<str>)>,
    annotation_value_bytes: usize,
}
fn exhausted() -> SolveAvailabilityError {
    SolveAvailabilityError::IdentityExhausted
}
fn bytes<T>(capacity: usize) -> Result<usize, SolveAvailabilityError> {
    capacity
        .checked_mul(std::mem::size_of::<T>())
        .ok_or_else(exhausted)
}
impl Checkpoint {
    pub fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        bytes::<(TypedPairKey, TypedPairKey, bool)>(self.edges.capacity())?
            .checked_add(bytes::<(BoundKey, TypedPairKey, bool)>(
                self.origins.capacity(),
            )?)
            .and_then(|n| n.checked_add(bytes::<TypedPairKey>(self.conflicts.capacity()).ok()?))
            .and_then(|n| n.checked_add(bytes::<usize>(self.formal_domains.capacity()).ok()?))
            .and_then(|n| n.checked_add(bytes::<(AnnotationScope, Box<str>)>(self.annotation_values.capacity()).ok()?))
            .and_then(|n| n.checked_add(bytes::<(AnnotationScope, Box<str>)>(self.annotation_effects.capacity()).ok()?))
            .and_then(|n| n.checked_add(self.annotation_value_bytes))
            .ok_or_else(exhausted)
    }
}
impl State {
    pub fn initialize(&mut self) -> Result<(), SolveAvailabilityError> {
        self.brand = NEXT_BRAND
            .fetch_update(
                std::sync::atomic::Ordering::Relaxed,
                std::sync::atomic::Ordering::Relaxed,
                |brand| brand.checked_add(1),
            )
            .map_err(|_| exhausted())?;
        Ok(())
    }
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            contributions: self.contributions.len(),
            views: self.views.len(),
            nested_bytes: self.nested_bytes,
            processing: self.processing,
            edges: Vec::new(),
            origins: Vec::new(),
            conflicts: Vec::new(),
            formal_domains: Vec::new(),
            annotation_values: Vec::new(),
            annotation_effects: Vec::new(),
            annotation_value_bytes: 0,
        }
    }
    pub fn rollback(&mut self, checkpoint: Checkpoint) {
        for key in checkpoint.formal_domains { self.formal_domains.remove(&key); }
        for key in checkpoint.annotation_values { self.annotation_values.remove(&key); }
        for key in checkpoint.annotation_effects { self.annotation_effects.remove(&key); }
        for key in checkpoint.conflicts {
            self.conflicts.remove(&key);
        }
        for (parent, child, new) in checkpoint.edges.into_iter().rev() {
            self.edge_keys.remove(&(parent, child));
            assert_eq!(self.edges.get_mut(&parent).unwrap().pop(), Some(child));
            if new {
                let entries = self.edges.remove(&parent).unwrap();
                self.evidence_bytes -= entries.capacity() * std::mem::size_of::<TypedPairKey>();
            }
        }
        for (bound, origin, new) in checkpoint.origins.into_iter().rev() {
            self.origin_keys.remove(&(bound, origin));
            assert_eq!(self.origins.get_mut(&bound).unwrap().pop(), Some(origin));
            if new {
                let entries = self.origins.remove(&bound).unwrap();
                self.evidence_bytes -= entries.capacity() * std::mem::size_of::<TypedPairKey>();
            }
        }
        self.contributions.truncate(checkpoint.contributions);
        self.views.truncate(checkpoint.views);
        self.nested_bytes = checkpoint.nested_bytes;
        self.processing = checkpoint.processing;
    }
    pub fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        let parts = [
            bytes::<Contribution>(self.contributions.capacity())?,
            bytes::<View>(self.views.capacity())?,
            bytes::<(TypedPairKey, Vec<TypedPairKey>)>(self.edges.capacity())?,
            bytes::<(TypedPairKey, TypedPairKey)>(self.edge_keys.capacity())?,
            bytes::<(BoundKey, Vec<TypedPairKey>)>(self.origins.capacity())?,
            bytes::<(BoundKey, TypedPairKey)>(self.origin_keys.capacity())?,
            bytes::<(TypedPairKey, Conflict)>(self.conflicts.capacity())?,
            bytes::<(usize, Term)>(self.formal_domains.capacity())?,
            bytes::<((AnnotationScope, Box<str>), u32)>(self.annotation_values.capacity())?,
            bytes::<((AnnotationScope, Box<str>), u32)>(self.annotation_effects.capacity())?,
            self.nested_bytes,
            self.evidence_bytes,
        ];
        parts
            .into_iter()
            .try_fold(0usize, |n, part| n.checked_add(part).ok_or_else(exhausted))
    }
    #[cfg(test)]
    fn formal_owned_bytes(&self) -> usize {
        let state = self;
        // These formal-only witnesses have no operation or annotation views.
        assert!(state.contributions.is_empty());
        assert!(state.views.is_empty());
        let evidence_bytes = state.edges.values().chain(state.origins.values())
            .map(|entries| entries.capacity() * std::mem::size_of::<TypedPairKey>())
            .sum::<usize>();
        assert_eq!(state.evidence_bytes, evidence_bytes);
        let retained_names = state.annotation_values.keys().chain(state.annotation_effects.keys()).map(|(_, name)| name.len()).sum::<usize>();
        assert_eq!(state.nested_bytes, retained_names);
        state.contributions.capacity() * std::mem::size_of::<Contribution>()
            + state.views.capacity() * std::mem::size_of::<View>()
            + state.edges.capacity() * std::mem::size_of::<(TypedPairKey, Vec<TypedPairKey>)>()
            + state.edge_keys.capacity() * std::mem::size_of::<(TypedPairKey, TypedPairKey)>()
            + state.origins.capacity() * std::mem::size_of::<(BoundKey, Vec<TypedPairKey>)>()
            + state.origin_keys.capacity() * std::mem::size_of::<(BoundKey, TypedPairKey)>()
            + state.conflicts.capacity() * std::mem::size_of::<(TypedPairKey, Conflict)>()
            + state.formal_domains.capacity() * std::mem::size_of::<(usize, Term)>()
            + state.annotation_values.capacity() * std::mem::size_of::<((AnnotationScope, Box<str>), u32)>()
            + state.annotation_effects.capacity() * std::mem::size_of::<((AnnotationScope, Box<str>), u32)>()
            + retained_names + evidence_bytes
    }
    pub fn observe(
        &self,
        operand: EffectOperandHandle,
        annotation: Option<EffectAnnotationHandle>,
    ) -> Option<(ObservedOperand<'_>, Option<&View>)> {
        if operand.brand != self.brand
            || annotation.is_some_and(|handle| handle.brand != self.brand)
        {
            return None;
        }
        let operand = match operand.operand {
            OperandIdentity::Contribution(index) => {
                ObservedOperand::Contribution(self.contributions.get(index as usize)?)
            }
            OperandIdentity::AnnotationMember(index, member) => {
                let view = self.views.get(index as usize)?;
                ObservedOperand::AnnotationMember {
                    view,
                    member,
                    effect: view.allowed.get(member as usize)?,
                }
            }
        };
        let annotation = match annotation {
            Some(handle) => Some(self.views.get(handle.index as usize)?),
            None => None,
        };
        Some((operand, annotation))
    }
}
fn task_key(task: LiveConstraintTask) -> TypedPairKey {
    match task {
        LiveConstraintTask::Value(key) => TypedPairKey::Value(key),
        LiveConstraintTask::Effect(lower, upper) => TypedPairKey::Effect { lower, upper },
    }
}
fn bound_pair(bound: BoundKey) -> TypedPairKey {
    let BoundKey(owner, side, item) = bound;
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
        _ => unreachable!("a bound keeps its kind"),
    }
}
impl InferenceSession {
    pub(super) fn candidate_processing(
        &mut self,
        pair: Option<TypedPairKey>,
    ) -> Option<TypedPairKey> {
        self.candidate_graph.as_mut().and_then(|graph| {
            std::mem::replace(&mut graph.intrusion.effect_algebra.processing, pair)
        })
    }
    pub(super) fn candidate_task_scope(&mut self, task: LiveConstraintTask) {
        self.candidate_processing(Some(task_key(task)));
    }
    pub(super) fn candidate_enqueue_evidence(
        &mut self,
        task: LiveConstraintTask,
    ) -> Result<(), SolveAvailabilityError> {
        let parent = self
            .candidate_graph
            .as_ref()
            .and_then(|graph| graph.intrusion.effect_algebra.processing);
        if let Some(parent) = parent {
            self.candidate_effect_edge(parent, task_key(task))?;
        }
        Ok(())
    }
    fn candidate_effect_edge(
        &mut self,
        parent: TypedPairKey,
        child: TypedPairKey,
    ) -> Result<(), SolveAvailabilityError> {
        if parent == child {
            return Ok(());
        }
        let Some(graph) = &mut self.candidate_graph else {
            return Ok(());
        };
        let state = &mut graph.intrusion.effect_algebra;
        if state.edge_keys.contains(&(parent, child)) {
            return Ok(());
        }
        let mut undo = self
            .route_journal
            .as_mut()
            .and_then(|journal| journal.intrusion.as_mut())
            .map(|undo| &mut undo.effect_algebra);
        if let Some(undo) = &mut undo {
            undo.edges.try_reserve(1).map_err(|_| exhausted())?;
        }
        state.edge_keys.try_reserve(1).map_err(|_| exhausted())?;
        state.edges.try_reserve(1).map_err(|_| exhausted())?;
        let new = !state.edges.contains_key(&parent);
        let mut fresh = Vec::new();
        let entries = if new {
            &mut fresh
        } else {
            state.edges.get_mut(&parent).unwrap()
        };
        let old = entries.capacity();
        entries.try_reserve(1).map_err(|_| exhausted())?;
        state.evidence_bytes = state
            .evidence_bytes
            .checked_add(bytes::<TypedPairKey>(entries.capacity() - old)?)
            .ok_or_else(exhausted)?;
        entries.push(child);
        if new {
            state.edges.insert(parent, fresh);
        }
        state.edge_keys.insert((parent, child));
        if let Some(undo) = undo {
            undo.edges.push((parent, child, new));
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
    pub(super) fn candidate_bound_origin(
        &mut self,
        bound: BoundKey,
        explicit: Option<TypedPairKey>,
    ) -> Result<(), SolveAvailabilityError> {
        let Some(graph) = &mut self.candidate_graph else {
            return Ok(());
        };
        let state = &mut graph.intrusion.effect_algebra;
        let origin = explicit
            .or(state.processing)
            .unwrap_or_else(|| bound_pair(bound));
        if state.origin_keys.contains(&(bound, origin)) {
            return Ok(());
        }
        let mut undo = self
            .route_journal
            .as_mut()
            .and_then(|journal| journal.intrusion.as_mut())
            .map(|undo| &mut undo.effect_algebra);
        if let Some(undo) = &mut undo {
            undo.origins.try_reserve(1).map_err(|_| exhausted())?;
        }
        state.origin_keys.try_reserve(1).map_err(|_| exhausted())?;
        state.origins.try_reserve(1).map_err(|_| exhausted())?;
        let new = !state.origins.contains_key(&bound);
        let mut fresh = Vec::new();
        let entries = if new {
            &mut fresh
        } else {
            state.origins.get_mut(&bound).unwrap()
        };
        let old = entries.capacity();
        entries.try_reserve(1).map_err(|_| exhausted())?;
        state.evidence_bytes = state
            .evidence_bytes
            .checked_add(bytes::<TypedPairKey>(entries.capacity() - old)?)
            .ok_or_else(exhausted)?;
        entries.push(origin);
        if new {
            state.origins.insert(bound, fresh);
        }
        state.origin_keys.insert((bound, origin));
        if let Some(undo) = undo {
            undo.origins.push((bound, origin, new));
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
    pub(super) fn candidate_bound_dependencies(
        &mut self,
        bound: BoundKey,
        child: LiveConstraintTask,
    ) -> Result<(), SolveAvailabilityError> {
        let count = self
            .candidate_graph
            .as_ref()
            .and_then(|graph| graph.intrusion.effect_algebra.origins.get(&bound))
            .map_or(0, Vec::len);
        for index in 0..count {
            let origin = self
                .candidate_graph
                .as_ref()
                .unwrap()
                .intrusion
                .effect_algebra
                .origins[&bound][index];
            self.candidate_effect_edge(origin, task_key(child))?;
        }
        Ok(())
    }
    pub(super) fn candidate_transfer_bound_origins(
        &mut self,
        from: BoundKey,
        to: BoundKey,
    ) -> Result<(), SolveAvailabilityError> {
        let count = self
            .candidate_graph
            .as_ref()
            .unwrap()
            .intrusion
            .effect_algebra
            .origins
            .get(&from)
            .map_or(0, Vec::len);
        for index in 0..count {
            let origin = self
                .candidate_graph
                .as_ref()
                .unwrap()
                .intrusion
                .effect_algebra
                .origins[&from][index];
            self.candidate_bound_origin(to, Some(origin))?;
        }
        Ok(())
    }
    fn candidate_effect_mismatch(
        &mut self,
        lower: EffectEndpointKey,
        upper: EffectEndpointKey,
    ) -> Result<(), SolveAvailabilityError> {
        let operand = match lower {
            EffectEndpointKey::Contribution(index) => OperandIdentity::Contribution(index),
            EffectEndpointKey::AnnotationMember(view, member) => {
                OperandIdentity::AnnotationMember(view, member)
            }
            _ => return Err(exhausted()),
        };
        let state = &mut self
            .candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .intrusion
            .effect_algebra;
        let key = TypedPairKey::Effect { lower, upper };
        if state.conflicts.contains_key(&key) {
            return Ok(());
        }
        let annotation = match upper {
            EffectEndpointKey::Allowance(index) if matches!(state.views[index as usize].provenance, ViewOrigin::Annotation) => Some(EffectAnnotationHandle {
                brand: state.brand,
                index,
            }),
            EffectEndpointKey::Allowance(_) | EffectEndpointKey::EmptyNegative => None,
            _ => return Err(exhausted()),
        };
        let undo = self
            .route_journal
            .as_mut()
            .and_then(|journal| journal.intrusion.as_mut())
            .map(|undo| &mut undo.effect_algebra);
        let mut undo = undo;
        if let Some(undo) = &mut undo {
            undo.conflicts.try_reserve(1).map_err(|_| exhausted())?;
        }
        state.conflicts.try_reserve(1).map_err(|_| exhausted())?;
        state.conflicts.insert(
            key,
            Conflict {
                operand: EffectOperandHandle {
                    brand: state.brand,
                    operand,
                },
                annotation,
            },
        );
        if let Some(undo) = undo {
            undo.conflicts.push(key);
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
    pub(super) fn candidate_replay_effect_conflicts(
        &mut self,
        initial: LiveConstraintTask,
        occurrence: &ConstraintOccurrenceId,
        cause: &CauseId,
    ) -> Result<(), SolveAvailabilityError> {
        if self
            .candidate_graph
            .as_ref()
            .is_none_or(|graph| graph.intrusion.effect_algebra.conflicts.is_empty())
        {
            return Ok(());
        }
        let mut pending = Vec::new();
        let mut visited = HashSet::new();
        let mut charge = 0usize;
        let result = (|| {
            pending.try_reserve(1).map_err(|_| exhausted())?;
            pending.push(task_key(initial));
            while let Some(key) = pending.pop() {
                if visited.contains(&key) {
                    continue;
                }
                visited.try_reserve(1).map_err(|_| exhausted())?;
                let state = &self
                    .candidate_graph
                    .as_ref()
                    .unwrap()
                    .intrusion
                    .effect_algebra;
                let count = state.edges.get(&key).map_or(0, Vec::len);
                let conflict = state.conflicts.get(&key).copied();
                pending.try_reserve(count).map_err(|_| exhausted())?;
                let next = bytes::<TypedPairKey>(pending.capacity())?
                    .checked_add(bytes::<TypedPairKey>(visited.capacity())?)
                    .ok_or_else(exhausted)?;
                let scratch = &mut self.candidate_graph.as_mut().unwrap().scratch_bytes;
                *scratch = scratch
                    .checked_sub(charge)
                    .and_then(|n| n.checked_add(next))
                    .ok_or_else(exhausted)?;
                charge = next;
                self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
                visited.insert(key);
                if let Some(conflict) = conflict {
                    self.report_solver_kind(
                        occurrence,
                        cause,
                        SolverErrorKind::IncompatibleEffect {
                            operand: conflict.operand,
                            annotation: conflict.annotation,
                        },
                    )?;
                }
                if let Some(children) = self
                    .candidate_graph
                    .as_ref()
                    .unwrap()
                    .intrusion
                    .effect_algebra
                    .edges
                    .get(&key)
                {
                    pending.extend(children.iter().copied());
                }
            }
            Ok(())
        })();
        drop((pending, visited));
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= charge;
        result
    }
    #[cfg(test)]
    pub(super) fn candidate_effect_view(
        &mut self,
        owner: DefinitionRootId,
        position: SourceNodeKey,
        allowed: Vec<SourceEffectId>,
        tail: Option<u32>,
    ) -> Result<u32, SolveAvailabilityError> {
        self.candidate_signature_view(owner, position, allowed, tail, None)
    }
    fn candidate_signature_view(
        &mut self,
        owner: DefinitionRootId,
        position: SourceNodeKey,
        allowed: Vec<SourceEffectId>,
        tail: Option<u32>,
        operation: Option<OperationOrigin>,
    ) -> Result<u32, SolveAvailabilityError> {
        let payload = operation.as_ref().map_or(0, |origin| origin.retained_bytes);
        let state = &mut self
            .candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .intrusion
            .effect_algebra;
        let id = u32::try_from(state.views.len()).map_err(|_| exhausted())?;
        let nested_bytes = allowed
            .capacity()
            .checked_mul(std::mem::size_of::<SourceEffectId>())
            .and_then(|n| n.checked_add(payload))
            .and_then(|n| n.checked_add(state.nested_bytes))
            .ok_or_else(exhausted)?;
        state.views.try_reserve(1).map_err(|_| exhausted())?;
        state.views.push(View {
            provenance: operation.map_or(ViewOrigin::Annotation, ViewOrigin::Operation),
            owner,
            position,
            allowed,
            tail,
        });
        state.nested_bytes = nested_bytes;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        #[cfg(test)]
        {
            let graph = self.candidate_graph.as_mut().unwrap();
            if graph.intrusion.effect_algebra.fail_after_view {
                graph.intrusion.effect_algebra.fail_after_view = false;
                graph.intrusion.effect_algebra.failed_view_sample =
                    Some((graph.scratch_bytes, graph.intrusion.effect_algebra.bytes()?));
                return Err(exhausted());
            }
        }
        Ok(id)
    }
    pub(super) fn candidate_operation(&mut self, declaration: &Arc<yu_hir::shadow::SourceOperationDeclaration>, owner: &DefinitionRootId, occurrence: &HirOccurrenceId, target: usize, level: u32) -> Result<(), SolveAvailabilityError> {
        let mut values = HashMap::new();
        let mut effects = HashMap::new();
        let mut views = HashMap::new();
        let count = declaration.signature.node_count();
        let retained_bytes = std::mem::size_of::<yu_hir::shadow::SourceOperationDeclaration>().checked_add(declaration.retained_arena_bytes()).ok_or_else(exhausted)?;
        values.try_reserve(count).map_err(|_| exhausted())?;
        effects.try_reserve(count).map_err(|_| exhausted())?;
        views.try_reserve(count).map_err(|_| exhausted())?;
        let scratch = bytes::<(&str, u32)>(values.capacity())?.checked_add(bytes::<(&str, u32)>(effects.capacity())?).and_then(|n| n.checked_add(bytes::<(SourceNodeKey, u32)>(views.capacity()).ok()?)).ok_or_else(exhausted)?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(scratch).ok_or_else(exhausted)?;
        let result = (|| {
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            let value = self.candidate_signature_value(&SignatureContext::Operation { declaration, owner, occurrence, retained_bytes }, &declaration.signature, Polarity::Positive, Polarity::Positive, level.checked_add(1).ok_or_else(exhausted)?, &mut values, &mut effects, &mut views)?;
            self.admit_candidate_value_link(occurrence, 42, value, self.batch.component_term_at(target))
        })();
        drop((values, effects, views));
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= scratch;
        result
    }
    pub(super) fn candidate_copy_effect_view(
        &mut self,
        id: u32,
        tail: Option<u32>,
    ) -> Result<u32, SolveAvailabilityError> {
        let view = &self
            .candidate_graph
            .as_ref()
            .ok_or_else(exhausted)?
            .intrusion
            .effect_algebra
            .views[id as usize];
        let (owner, position) = (view.owner.clone(), view.position.clone());
        let operation = match &view.provenance { ViewOrigin::Annotation => None, ViewOrigin::Operation(origin) => Some(origin.clone()) };
        let mut allowed = Vec::new();
        allowed
            .try_reserve_exact(view.allowed.len())
            .map_err(|_| exhausted())?;
        allowed.extend(view.allowed.iter().cloned());
        self.candidate_signature_view(owner, position, allowed, tail, operation)
    }
    // The caller reserves and charges this operation-local map before copying.
    pub(super) fn candidate_remapped_effect_view(
        &mut self,
        id: u32,
        tail: Option<u32>,
        remap: &mut HashMap<(u32, Option<u32>), u32>,
    ) -> Result<u32, SolveAvailabilityError> {
        if let Some(&copy) = remap.get(&(id, tail)) {
            return Ok(copy);
        }
        assert!(
            remap.len() < remap.capacity(),
            "view remap reserved before publication"
        );
        let copy = self.candidate_copy_effect_view(id, tail)?;
        remap.insert((id, tail), copy);
        Ok(copy)
    }
    pub(super) fn candidate_scratch_growth(
        &mut self,
        charge: &mut usize,
        growth: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
        let next_charge = charge.checked_add(growth).ok_or_else(exhausted)?;
        let next_scratch = state
            .scratch_bytes
            .checked_add(growth)
            .ok_or_else(exhausted)?;
        *charge = next_charge;
        state.scratch_bytes = next_scratch;
        Ok(())
    }
    pub(super) fn candidate_effect_contribution(
        &mut self,
        effect: SourceEffectId,
        origin: SourceNodeKey,
    ) -> Result<EffectEndpointKey, SolveAvailabilityError> {
        let state = &mut self
            .candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .intrusion
            .effect_algebra;
        let id = u32::try_from(state.contributions.len()).map_err(|_| exhausted())?;
        state
            .contributions
            .try_reserve(1)
            .map_err(|_| exhausted())?;
        state.contributions.push(Contribution {
            effect,
            origin,
            instance: id,
        });
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(EffectEndpointKey::Contribution(id))
    }
    pub(super) fn candidate_check_effect_operand(
        &mut self,
        lower: EffectEndpointKey,
        upper: EffectEndpointKey,
    ) -> Result<(), SolveAvailabilityError> {
        match (lower, upper) {
            (EffectEndpointKey::BottomPositive, _) => Ok(()),
            (EffectEndpointKey::Support(id), _) => {
                let view = &self
                    .candidate_graph
                    .as_ref()
                    .ok_or_else(exhausted)?
                    .intrusion
                    .effect_algebra
                    .views[id as usize];
                let (count, tail) = (view.allowed.len(), view.tail);
                for member in 0..count {
                    let member = u32::try_from(member).map_err(|_| exhausted())?;
                    self.enqueue_task(LiveConstraintTask::Effect(
                        EffectEndpointKey::AnnotationMember(id, member),
                        upper,
                    ))?;
                }
                if let Some(tail) = tail {
                    self.enqueue_task(LiveConstraintTask::Effect(
                        self.canonical_effect(EffectEndpointKey::EffectRow(tail)),
                        upper,
                    ))?;
                }
                Ok(())
            }
            (
                EffectEndpointKey::Contribution(_) | EffectEndpointKey::AnnotationMember(_, _),
                EffectEndpointKey::Allowance(id),
            ) => {
                let state = &self
                    .candidate_graph
                    .as_ref()
                    .ok_or_else(exhausted)?
                    .intrusion
                    .effect_algebra;
                let effect = match lower {
                    EffectEndpointKey::Contribution(index) => {
                        &state.contributions[index as usize].effect
                    }
                    EffectEndpointKey::AnnotationMember(view, member) => {
                        &state.views[view as usize].allowed[member as usize]
                    }
                    _ => unreachable!(),
                };
                let view = &state.views[id as usize];
                if view.allowed.contains(effect) {
                    return Ok(());
                }
                if let Some(tail) = view.tail {
                    return self.enqueue_task(LiveConstraintTask::Effect(
                        lower,
                        self.canonical_effect(EffectEndpointKey::EffectRow(tail)),
                    ));
                }
                self.candidate_effect_mismatch(lower, upper)
            }
            (
                EffectEndpointKey::Contribution(_) | EffectEndpointKey::AnnotationMember(_, _),
                EffectEndpointKey::EmptyNegative,
            ) => self.candidate_effect_mismatch(lower, upper),
            _ => Err(exhausted()),
        }
    }
    fn candidate_annotation_variable(&mut self, scope: &AnnotationScope, name: &str, level: u32) -> Result<u32, SolveAvailabilityError> {
        let key = (scope.clone(), Box::<str>::from(name));
        if let Some(&row) = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_values.get(&key) { return Ok(row); }
        let graph = self.candidate_graph.as_mut().unwrap();
        graph.intrusion.effect_algebra.annotation_values.try_reserve(1).map_err(|_| exhausted())?;
        if let Some(undo) = self.route_journal.as_mut().and_then(|journal| journal.intrusion.as_mut()) {
            undo.effect_algebra.annotation_values.try_reserve(1).map_err(|_| exhausted())?;
        }
        let row = self.fresh_value_at_level(level)?;
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra;
        state.nested_bytes = state.nested_bytes.checked_add(name.len()).ok_or_else(exhausted)?;
        if let Some(undo) = self.route_journal.as_mut().and_then(|journal| journal.intrusion.as_mut()) { undo.effect_algebra.annotation_value_bytes = undo.effect_algebra.annotation_value_bytes.checked_add(name.len()).ok_or_else(exhausted)?; undo.effect_algebra.annotation_values.push(key.clone()); }
        state.annotation_values.insert(key, row);
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        #[cfg(test)]
        self.record_failed_formal_sample(3)?;
        #[cfg(test)]
        if FORMAL_ANNOTATION_FAIL_STAGE.with(|stage| if stage.get() == 3 { stage.set(0); true } else { false }) { return Err(exhausted()); }
        Ok(row)
    }

    fn candidate_formal_effect_variable(&mut self, scope: &AnnotationScope, name: &str, level: u32) -> Result<u32, SolveAvailabilityError> {
        let key = (scope.clone(), Box::<str>::from(name));
        if let Some(&row) = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_effects.get(&key) { return Ok(row); }
        let graph = self.candidate_graph.as_mut().unwrap();
        graph.intrusion.effect_algebra.annotation_effects.try_reserve(1).map_err(|_| exhausted())?;
        if let Some(undo) = self.route_journal.as_mut().and_then(|journal| journal.intrusion.as_mut()) {
            undo.effect_algebra.annotation_effects.try_reserve(1).map_err(|_| exhausted())?;
        }
        let row = self.fresh_effect_at_level(level)?;
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra;
        state.nested_bytes = state.nested_bytes.checked_add(name.len()).ok_or_else(exhausted)?;
        if let Some(undo) = self.route_journal.as_mut().and_then(|journal| journal.intrusion.as_mut()) { undo.effect_algebra.annotation_value_bytes = undo.effect_algebra.annotation_value_bytes.checked_add(name.len()).ok_or_else(exhausted)?; undo.effect_algebra.annotation_effects.push(key.clone()); }
        state.annotation_effects.insert(key, row);
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        #[cfg(test)]
        self.record_failed_formal_sample(3)?;
        #[cfg(test)]
        if FORMAL_ANNOTATION_FAIL_STAGE.with(|stage| if stage.get() == 3 { stage.set(0); true } else { false }) { return Err(exhausted()); }
        Ok(row)
    }

    #[cfg(test)]
    fn record_failed_formal_sample(&mut self, stage: u8) -> Result<(), SolveAvailabilityError> {
        if FORMAL_ANNOTATION_FAIL_STAGE.with(|hook| hook.get() == stage) {
            let state = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            let Some(undo) = self.route_journal.as_ref()
                .and_then(|journal| journal.intrusion.as_ref())
                .map(|undo| &undo.effect_algebra) else { return Ok(()); };
            assert_eq!(undo.annotation_values.iter().chain(undo.annotation_effects.iter()).map(|(_, name)| name.len()).sum::<usize>(), undo.annotation_value_bytes);
            assert!(undo.annotation_values.iter().all(|key| state.annotation_values.contains_key(key)));
            assert!(undo.annotation_effects.iter().all(|key| state.annotation_effects.contains_key(key)));
            if stage == 2 {
                assert!(!undo.formal_domains.is_empty());
                assert!(undo.formal_domains.iter().all(|key| state.formal_domains.contains_key(key)));
            }
            let owned = state.formal_owned_bytes();
            let undo_owned = undo.edges.capacity() * std::mem::size_of::<(TypedPairKey, TypedPairKey, bool)>()
                + undo.origins.capacity() * std::mem::size_of::<(BoundKey, TypedPairKey, bool)>()
                + undo.conflicts.capacity() * std::mem::size_of::<TypedPairKey>()
                + undo.formal_domains.capacity() * std::mem::size_of::<usize>()
                + undo.annotation_values.capacity() * std::mem::size_of::<(AnnotationScope, Box<str>)>()
                + undo.annotation_effects.capacity() * std::mem::size_of::<(AnnotationScope, Box<str>)>()
                + undo.annotation_values.iter().chain(undo.annotation_effects.iter()).map(|(_, name)| name.len()).sum::<usize>();
            assert_eq!(state.bytes()?, owned);
            assert_eq!(undo.bytes()?, undo_owned);
            assert_eq!(self.execution_counters.inference_session_retained_bytes, self.resource_ledger.inference_session_retained_bytes);
            assert!(self.execution_counters.inference_session_peak_bytes >= self.resource_ledger.inference_session_retained_bytes);
            let sample = (state.nested_bytes, undo.annotation_value_bytes, owned, undo_owned, self.resource_ledger.inference_session_retained_bytes, self.resource_boundary_samples);
            self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.failed_formal_sample = Some(sample);
        }
        Ok(())
    }

    fn candidate_formal_pair(&mut self, ty: &SourceAnnotationType, scope: &AnnotationScope, level: u32) -> Result<(Term, Term), SolveAvailabilityError> {
        if ty.effects.as_ref().is_some_and(|row| !row.concrete.is_empty() || row.variables.len() != 1) { return Err(exhausted()); }
        match &ty.value {
            SourceAnnotationValue::Int => Ok((self.batch.collected_leaf_term(Leaf::IntPositive), self.batch.collected_leaf_term(Leaf::IntNegative))),
            SourceAnnotationValue::Unit => Ok((self.batch.collected_leaf_term(Leaf::UnitPositive), self.batch.collected_leaf_term(Leaf::UnitNegative))),
            SourceAnnotationValue::Variable(name) => {
                let row = self.candidate_annotation_variable(scope, name, level)?;
                Ok((self.live_value_term(Polarity::Positive, row)?, self.live_value_term(Polarity::Negative, row)?))
            }
            SourceAnnotationValue::Function { argument, result } => {
                let (ap, an) = self.candidate_formal_pair(argument, scope, level)?;
                let (rp, rn) = self.candidate_formal_pair(result, scope, level)?;
                let qa = self.candidate_formal_effect_port(argument.effects.as_ref(), scope, level)?;
                let qr = self.candidate_formal_effect_port(result.effects.as_ref(), scope, level)?;
                let qan = self.live_effect_term(Polarity::Negative, qa)?;
                let qap = self.live_effect_term(Polarity::Positive, qa)?;
                let qrn = self.live_effect_term(Polarity::Negative, qr)?;
                let qrp = self.live_effect_term(Polarity::Positive, qr)?;
                Ok((self.positive_function_term(an, qan, qrp, rp)?, self.negative_function_term(ap, qap, qrn, rn)?))
            }
        }
    }

    fn candidate_formal_effect_port(&mut self, effects: Option<&SourceEffectRow>, scope: &AnnotationScope, level: u32) -> Result<u32, SolveAvailabilityError> {
        match effects {
            None => self.fresh_effect_at_level(level),
            Some(row) if row.concrete.is_empty() && row.variables.len() == 1 =>
                self.candidate_formal_effect_variable(scope, &row.variables[0], level),
            Some(_) => Err(exhausted()),
        }
    }

    pub(super) fn candidate_formal_annotation(
        &mut self, annotation: &SourceAnnotation, parameter: usize, occurrence: &HirOccurrenceId, scope: &AnnotationScope,
    ) -> Result<(), SolveAvailabilityError> {
        if annotation.ty.effects.is_some() { return Err(exhausted()); }
        let row = self.parameter_live_base.checked_add(u32::try_from(parameter).map_err(|_| exhausted())?).ok_or_else(exhausted)?;
        let level = self.value_levels[row as usize];
        if self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.formal_domains.contains_key(&parameter) { return Err(exhausted()); }
        // Reserve a linear upper bound for the paired recursive constructor's
        // temporary child ports; source admission already bounds its depth.
        let scratch = bytes::<(Term, Term, Term, Term, u32, u32)>(annotation.ty.node_count())?;
        let graph = self.candidate_graph.as_mut().unwrap();
        graph.scratch_bytes = graph.scratch_bytes.checked_add(scratch).ok_or_else(exhausted)?;
        let pair = (|| {
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            self.candidate_formal_pair(&annotation.ty, scope, level)
        })();
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= scratch;
        let (positive, negative) = pair?;
        #[cfg(test)]
        if FORMAL_ANNOTATION_FAIL_STAGE.with(|stage| if stage.get() == 1 { stage.set(0); true } else { false }) { return Err(exhausted()); }
        let graph = self.candidate_graph.as_mut().unwrap();
        graph.intrusion.effect_algebra.formal_domains.try_reserve(1).map_err(|_| exhausted())?;
        if let Some(undo) = self.route_journal.as_mut().and_then(|journal| journal.intrusion.as_mut()) { undo.effect_algebra.formal_domains.try_reserve(1).map_err(|_| exhausted())?; }
        let upper = self.candidate_endpoint(shadow_apply::CandidateEndpoint::Parameter(parameter), Polarity::Negative)?;
        self.admit_candidate_value_link(occurrence, 43, positive, upper)?;
        #[cfg(test)]
        if FORMAL_ANNOTATION_FAIL_AFTER_FIRST_EDGE.with(|flag| flag.replace(false)) { return Err(exhausted()); }
        let lower = self.candidate_endpoint(shadow_apply::CandidateEndpoint::Parameter(parameter), Polarity::Positive)?;
        self.admit_candidate_value_link(occurrence, 44, lower, negative)?;
        if self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.formal_domains.insert(parameter, negative).is_none() {
            if let Some(undo) = self.route_journal.as_mut().and_then(|journal| journal.intrusion.as_mut()) { undo.effect_algebra.formal_domains.push(parameter); }
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        #[cfg(test)]
        self.record_failed_formal_sample(2)?;
        #[cfg(test)]
        if FORMAL_ANNOTATION_FAIL_STAGE.with(|stage| if stage.get() == 2 { stage.set(0); true } else { false }) { return Err(exhausted()); }
        Ok(())
    }

    pub(super) fn candidate_local_annotation(
        &mut self, annotation: &SourceAnnotation, slot: usize,
        endpoint: shadow_apply::CandidateEndpoint, occurrence: &HirOccurrenceId,
        level: u32, boundary: u32,
    ) -> Result<(), SolveAvailabilityError> {
        if !candidate_source::preflight_local_annotation(&annotation.ty) { return Err(exhausted()); }
        let mut value_variables = HashMap::new();
        let mut effect_variables = HashMap::new();
        let mut views = HashMap::new();
        let count = annotation.ty.node_count();
        value_variables.try_reserve(count).map_err(|_| exhausted())?;
        effect_variables.try_reserve(count).map_err(|_| exhausted())?;
        views.try_reserve(count).map_err(|_| exhausted())?;
        let scratch = value_variables.capacity().checked_add(effect_variables.capacity())
            .and_then(|n| n.checked_mul(std::mem::size_of::<(&str, u32)>()))
            .and_then(|n| n.checked_add(views.capacity().checked_mul(std::mem::size_of::<(SourceNodeKey, u32)>())?))
            .ok_or_else(exhausted)?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap()
            .scratch_bytes.checked_add(scratch).ok_or_else(exhausted)?;
        let result = (|| {
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            let negative = self.candidate_signature_value(
                &SignatureContext::Annotation(annotation), &annotation.ty,
                Polarity::Negative, Polarity::Positive, level,
                &mut value_variables, &mut effect_variables, &mut views,
            )?;
            let positive = self.candidate_signature_value(
                &SignatureContext::Annotation(annotation), &annotation.ty,
                Polarity::Positive, Polarity::Positive, level,
                &mut value_variables, &mut effect_variables, &mut views,
            )?;
            // Check the whole initializer; its evaluation effects remain on the
            // block edge. Only the paired annotation enters the local scheme.
            let root = self.fresh_value_at_level(level)?;
            let lower = self.candidate_endpoint(endpoint, Polarity::Positive)?;
            self.admit_candidate_value_link(occurrence, 40, lower, negative)?;
            #[cfg(test)]
            if FORMAL_ANNOTATION_FAIL_STAGE.with(|stage| if stage.get() == 4 { stage.set(0); true } else { false }) { return Err(exhausted()); }
            let upper = self.live_value_term(Polarity::Negative, root)?;
            self.admit_candidate_value_link(occurrence, 41, positive, upper)?;
            let exposed = self.live_value_term(Polarity::Positive, root)?;
            self.install_candidate_local_term(slot, exposed, boundary)
        })();
        drop((value_variables, effect_variables, views));
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= scratch;
        result
    }

    pub(super) fn candidate_annotation(
        &mut self,
        annotation: &SourceAnnotation,
        endpoint: shadow_apply::CandidateEndpoint,
        target: usize,
        occurrence: &HirOccurrenceId,
        level: u32,
    ) -> Result<(), SolveAvailabilityError> {
        if annotation.ty.effects.is_some() {
            return Err(exhausted());
        }
        let mut value_variables = HashMap::new();
        let mut effect_variables = HashMap::new();
        let mut views = HashMap::new();
        let count = annotation.ty.node_count();
        value_variables
            .try_reserve(count)
            .map_err(|_| exhausted())?;
        effect_variables
            .try_reserve(count)
            .map_err(|_| exhausted())?;
        views.try_reserve(count).map_err(|_| exhausted())?;
        let scratch = value_variables
            .capacity()
            .checked_add(effect_variables.capacity())
            .and_then(|n| n.checked_mul(std::mem::size_of::<(&str, u32)>()))
            .and_then(|n| {
                n.checked_add(
                    views
                        .capacity()
                        .checked_mul(std::mem::size_of::<(SourceNodeKey, u32)>())?,
                )
            })
            .ok_or_else(exhausted)?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self
            .candidate_graph
            .as_ref()
            .unwrap()
            .scratch_bytes
            .checked_add(scratch)
            .ok_or_else(exhausted)?;
        let result = (|| {
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            let upper = self.candidate_signature_value(
                &SignatureContext::Annotation(annotation),
                &annotation.ty,
                Polarity::Negative,
                Polarity::Positive,
                level,
                &mut value_variables,
                &mut effect_variables,
                &mut views,
            )?;
            let exposed = self.candidate_signature_value(
                &SignatureContext::Annotation(annotation),
                &annotation.ty,
                Polarity::Positive,
                Polarity::Positive,
                level,
                &mut value_variables,
                &mut effect_variables,
                &mut views,
            )?;
            let lower = self.candidate_endpoint(endpoint, Polarity::Positive)?;
            self.admit_candidate_value_link(occurrence, 40, lower, upper)?;
            self.admit_candidate_value_link(
                occurrence,
                41,
                exposed,
                self.batch.component_term_at(target),
            )
        })();
        drop((value_variables, effect_variables, views));
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= scratch;
        result
    }

    fn candidate_signature_value<'a>(
        &mut self,
        context: &SignatureContext<'_>,
        ty: &'a SourceAnnotationType,
        polarity: Polarity,
        variance: Polarity,
        level: u32,
        values: &mut HashMap<&'a str, u32>,
        effects: &mut HashMap<&'a str, u32>,
        views: &mut HashMap<SourceNodeKey, u32>,
    ) -> Result<Term, SolveAvailabilityError> {
        match &ty.value {
            SourceAnnotationValue::Unit => {
                Ok(self
                    .batch
                    .collected_leaf_term(if polarity == Polarity::Positive {
                        Leaf::UnitPositive
                    } else {
                        Leaf::UnitNegative
                    }))
            }
            SourceAnnotationValue::Int => {
                Ok(self
                    .batch
                    .collected_leaf_term(if polarity == Polarity::Positive {
                        Leaf::IntPositive
                    } else {
                        Leaf::IntNegative
                    }))
            }
            SourceAnnotationValue::Variable(name) => {
                let row = if let SignatureContext::Annotation(annotation) = context {
                    self.candidate_annotation_variable(&AnnotationScope::Definition(annotation.owner.clone()), name, level)?
                } else if let Some(&row) = values.get(name.as_ref()) {
                    row
                } else {
                    values.try_reserve(1).map_err(|_| exhausted())?;
                    let row = self.fresh_value_at_level(level)?;
                    values.insert(name.as_ref(), row);
                    row
                };
                self.live_value_term(polarity, row)
            }
            SourceAnnotationValue::Function { argument, result } => {
                let opposite = if polarity == Polarity::Positive {
                    Polarity::Negative
                } else {
                    Polarity::Positive
                };
                let reversed = if variance == Polarity::Positive {
                    Polarity::Negative
                } else {
                    Polarity::Positive
                };
                let a = self.candidate_signature_value(
                    context, argument, opposite, reversed, level, values, effects, views,
                )?;
                let r = self.candidate_signature_value(
                    context, result, polarity, variance, level, values, effects, views,
                )?;
                let ae = self.candidate_signature_effect(
                    context,
                    argument.effects.as_ref(),
                    None,
                    opposite,
                    reversed,
                    level,
                    effects,
                    views,
                )?;
                let family = match context {
                    SignatureContext::Operation { declaration, .. } if std::ptr::eq(ty, &declaration.signature) => Some(&declaration.id.family),
                    _ => None,
                };
                let re = self.candidate_signature_effect(
                    context,
                    result.effects.as_ref(),
                    family,
                    polarity,
                    variance,
                    level,
                    effects,
                    views,
                )?;
                if polarity == Polarity::Positive {
                    self.positive_function_term(a, ae, re, r)
                } else {
                    self.negative_function_term(a, ae, re, r)
                }
            }
        }
    }
    fn candidate_signature_effect<'a>(
        &mut self,
        context: &SignatureContext<'_>,
        row: Option<&'a SourceEffectRow>,
        family: Option<&SourceEffectId>,
        polarity: Polarity,
        variance: Polarity,
        level: u32,
        variables: &mut HashMap<&'a str, u32>,
        views: &mut HashMap<SourceNodeKey, u32>,
    ) -> Result<Term, SolveAvailabilityError> {
        let Some(row) = row else {
            if let Some(family) = family {
                let mut allowed = Vec::new();
                allowed.try_reserve_exact(1).map_err(|_| exhausted())?;
                allowed.push(family.clone());
                let view = self.candidate_signature_view(context.owner().clone(), context.position().clone(), allowed, None, context.operation())?;
                let port = self.fresh_effect_at_level(level)?;
                self.candidate_insert_bound(ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(port)), polarity, ExtrusionEndpoint::Effect(EffectEndpointKey::Support(view)))?;
                return self.live_effect_term(polarity, port);
            }
            if matches!(context, SignatureContext::Operation { .. }) {
                return Ok(self.batch.collected_leaf_term(if polarity == Polarity::Positive { Leaf::EffectBottomPositive } else { Leaf::EmptyEffectNegative }));
            }
            if variance == Polarity::Negative {
                return Ok(self
                    .batch
                    .collected_leaf_term(if polarity == Polarity::Positive {
                        Leaf::EffectBottomPositive
                    } else {
                        Leaf::EmptyEffectNegative
                    }));
            }
            let view = if let Some(&view) = views.get(context.position()) {
                view
            } else {
                views.try_reserve(1).map_err(|_| exhausted())?;
                let view = self.candidate_signature_view(
                    context.owner().clone(),
                    context.position().clone(),
                    Vec::new(),
                    None,
                    context.operation(),
                )?;
                views.insert(context.position().clone(), view);
                view
            };
            let port = self.fresh_effect_at_level(level)?;
            self.candidate_insert_bound(
                ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(port)),
                polarity,
                ExtrusionEndpoint::Effect(if polarity == Polarity::Positive {
                    EffectEndpointKey::Support(view)
                } else {
                    EffectEndpointKey::Allowance(view)
                }),
            )?;
            return self.live_effect_term(polarity, port);
        };
        if variance == Polarity::Negative && !row.concrete.is_empty() {
            return Err(exhausted());
        }
        if row.variables.len() > 1 {
            return Err(exhausted());
        }
        let tail = if let Some(name) = row.variables.first() {
            Some(if let SignatureContext::Annotation(annotation) = context {
                self.candidate_formal_effect_variable(&AnnotationScope::Definition(annotation.owner.clone()), name, level)?
            } else if let Some(&row) = variables.get(name.as_ref()) {
                row
            } else {
                variables.try_reserve(1).map_err(|_| exhausted())?;
                let row = self.fresh_effect_at_level(level)?;
                variables.insert(name.as_ref(), row);
                row
            })
        } else {
            None
        };
        if variance == Polarity::Negative {
            return match tail {
                Some(row) => self.live_effect_term(polarity, row),
                None => Ok(self
                    .batch
                    .collected_leaf_term(if polarity == Polarity::Positive {
                        Leaf::EffectBottomPositive
                    } else {
                        Leaf::EmptyEffectNegative
                    })),
            };
        }
        let view = if let Some(&view) = views.get(&row.position) {
            view
        } else {
            views.try_reserve(1).map_err(|_| exhausted())?;
            let mut allowed = Vec::new();
            allowed
                .try_reserve_exact(row.concrete.len() + usize::from(family.is_some()))
                .map_err(|_| exhausted())?;
            if let Some(family) = family { allowed.push(family.clone()); }
            allowed.extend(row.concrete.iter().cloned());
            let view = self.candidate_signature_view(
                context.owner().clone(),
                row.position.clone(),
                allowed,
                tail,
                context.operation(),
            )?;
            views.insert(row.position.clone(), view);
            view
        };
        let port = self.fresh_effect_at_level(level)?;
        self.candidate_insert_bound(
            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(port)),
            polarity,
            ExtrusionEndpoint::Effect(if polarity == Polarity::Positive {
                EffectEndpointKey::Support(view)
            } else {
                EffectEndpointKey::Allowance(view)
            }),
        )?;
        self.live_effect_term(polarity, port)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::candidate_scheme::{Node, RowKey};
    fn make_session(text: &str) -> InferenceSession {
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        assert!(parsed.structural_recoveries().is_empty());
        let hir = Arc::new(
            yu_hir::shadow::lower_module_with_local_source(
                yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                    "effect-kernel",
                    "source.yu",
                ))),
                &parsed,
                yu_hir::SemanticImports::empty(),
            )
            .unwrap(),
        );
        let mut session = InferenceSession::try_new(
            ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap(),
        )
        .unwrap();
        session.start_candidate_graph().unwrap();
        session
    }
    #[test]
    fn annotated_local_initializer_effect_has_one_block_edge_and_pure_lookups() {
        let session = make_session("act tick:\n    our next: () -> (int -> int)\n\nmy outer = { my local:int -> int = tick::next(); my first = local; local }");
        let owner = root(&session, "outer");
        let source = session.batch.hir.local_source(&owner).unwrap().unwrap();
        let local = &source.bindings()[0];
        let initializer = source.expression(&local.initializer).unwrap();
        let edges: Vec<_> = session.batch.occurrences.iter().filter(|fact| fact.id().occurrence() == &initializer.occurrence && fact.id().local_slot() == 20).collect();
        assert_eq!(edges.len(), 1, "one initializer evaluation edge to the enclosing block");
        let uses: Vec<_> = source.expressions().iter().filter(|expr| matches!(&expr.form, yu_hir::shadow::LocalSourceForm::Name { resolution: yu_hir::shadow::LocalSourceResolution::Local(id), .. } if id == &local.id)).collect();
        assert_eq!(uses.len(), 2);
        for lookup in uses {
            let facts: Vec<_> = session.batch.occurrences.iter().filter(|fact| fact.id().occurrence() == &lookup.occurrence && matches!(fact.id().local_slot(), 1 | 2)).collect();
            assert_eq!(facts.len(), 2);
            assert!(facts.iter().any(|fact| matches!(session.batch.term_view(fact.lower()), Ok(TermView::Leaf(Leaf::EffectBottomPositive)))));
            assert!(facts.iter().any(|fact| matches!(session.batch.term_view(fact.upper()), Ok(TermView::Leaf(Leaf::EmptyEffectNegative)))));
        }
    }

    #[test]
    fn local_annotation_first_edge_failure_rolls_back_and_retries() {
        for ty in ["int", "int -> int", "(int -> int) -> int", "int -> () -> int"] {
            let mut session = make_session(&format!("my outer x = {{ my local:{ty} = x; local }}"));
            let owner = root(&session, "outer");
            let actions = session.batch.candidate_source.schedules[&owner].clone();
            let candidate_source::Action::LocalAnnotation { annotation, slot, endpoint, occurrence, level, boundary } = actions.iter().find(|action| matches!(action, candidate_source::Action::LocalAnnotation { .. })).unwrap() else { unreachable!() };
            let mut checkpoint = None;
            FORMAL_ANNOTATION_FAIL_STAGE.with(|stage| stage.set(4));
            assert_eq!(session.with_route_transaction(|session| {
                checkpoint = Some(RouteCheckpoint::capture(session));
                session.candidate_local_annotation(annotation, *slot, *endpoint, occurrence, *level, *boundary)
            }), Err(exhausted()));
            checkpoint.unwrap().assert_restored(&session);
            assert!(session.candidate_graph.as_ref().unwrap().locals[*slot].is_none());
            let mut checkpoint = None;
            assert_eq!(session.with_route_transaction(|session| {
                checkpoint = Some(RouteCheckpoint::capture(session));
                session.candidate_local_annotation(annotation, *slot, *endpoint, occurrence, *level, *boundary)?;
                Err::<(), _>(exhausted())
            }), Err(exhausted()));
            checkpoint.unwrap().assert_restored(&session);
            assert!(session.candidate_graph.as_ref().unwrap().locals[*slot].is_none());
            session.with_route_transaction(|session| session.candidate_local_annotation(annotation, *slot, *endpoint, occurrence, *level, *boundary)).unwrap();
            assert!(session.candidate_graph.as_ref().unwrap().locals[*slot].is_some());
        }
    }

    #[test]
    fn local_scheme_publication_rollback_preserves_prior_slots_and_retries() {
        let mut session = make_session("my outer x = { my first:int = x; my second:int = x; second }");
        let owner = root(&session, "outer");
        let actions = session.batch.candidate_source.schedules[&owner].clone();
        let annotations: Vec<_> = actions.iter().filter_map(|action| match action {
            candidate_source::Action::LocalAnnotation { annotation, slot, endpoint, occurrence, level, boundary } =>
                Some((annotation, *slot, *endpoint, occurrence, *level, *boundary)),
            _ => None,
        }).collect();
        let (first, second) = (&annotations[0], &annotations[1]);
        session.candidate_local_annotation(first.0, first.1, first.2, first.3, first.4, first.5).unwrap();
        let mut checkpoint = None;
        assert_eq!(session.with_route_transaction(|session| {
            checkpoint = Some(RouteCheckpoint::capture(session));
            session.install_candidate_local(second.1, second.2, second.5)?;
            Err::<(), _>(exhausted())
        }), Err(exhausted()));
        checkpoint.unwrap().assert_restored(&session);
        let locals = &session.candidate_graph.as_ref().unwrap().locals;
        assert!(locals[first.1].is_some());
        assert!(locals[second.1].is_none());
        session.with_route_transaction(|session| session.install_candidate_local(second.1, second.2, second.5)).unwrap();
        assert!(session.candidate_graph.as_ref().unwrap().locals[second.1].is_some());
    }

    #[test]
    fn operation_lookup_evaluation_has_only_ordinary_exact_pure_facts() {
        let session = make_session("act tick:\n    our next: () -> int\n\nmy lookup = tick::next");
        let root = root(&session, "lookup");
        let source = session.batch.hir.local_source(&root).unwrap().unwrap();
        let operation = source.expressions().iter().find(|expr| matches!(expr.form, yu_hir::shadow::LocalSourceForm::Operation { .. })).unwrap();
        let facts: Vec<_> = session.batch.occurrences.iter().filter(|fact| fact.id().occurrence() == &operation.occurrence).collect();
        assert_eq!(facts.len(), 2);
        assert!(facts.iter().any(|fact| matches!(session.batch.term_view(fact.lower()), Ok(TermView::Leaf(Leaf::EffectBottomPositive)))));
        assert!(facts.iter().any(|fact| matches!(session.batch.term_view(fact.upper()), Ok(TermView::Leaf(Leaf::EmptyEffectNegative)))));
        assert!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.contributions.is_empty());
    }
    #[test]
    fn paired_formal_failure_samples_live_named_and_domain_storage() {
        let name = "a".repeat(4096);
        for (stage, symbolic) in [(2, false), (3, false), (2, true), (3, true)] {
            let text = if symbolic { format!("my f (x:int -> ['{name}] int) = x") } else { format!("my f (x:'{name} -> '{name}) = x") };
            let mut session = make_session(&text);
            let action = session.batch.candidate_source.schedules.values().next().unwrap().iter()
                .find(|action| matches!(action, candidate_source::Action::FormalAnnotation { .. })).unwrap().clone();
            let candidate_source::Action::FormalAnnotation { annotation, parameter, occurrence, scope } = action else { unreachable!() };
            let SourceAnnotationValue::Function { argument, result } = &annotation.ty.value else { unreachable!() };
            let expected_name_bytes = if symbolic { result.effects.as_ref().unwrap().variables[0].len() } else {
                let SourceAnnotationValue::Variable(annotation_name) = &argument.value else { unreachable!() };
                annotation_name.len()
            };
            let before_nested = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.nested_bytes;
            let mut before = None;
            FORMAL_ANNOTATION_FAIL_STAGE.with(|hook| hook.set(stage));
            assert_eq!(session.with_route_transaction(|session| {
                before = Some(RouteCheckpoint::capture(session));
                session.candidate_formal_annotation(&annotation, parameter, &occurrence, &scope)
            }), Err(exhausted()));
            before.unwrap().assert_restored(&session);
            let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            let (nested, undo_names, owned_bytes, undo_bytes, sampled_total, live_samples) = state.failed_formal_sample.unwrap();
            assert_eq!(nested, before_nested + expected_name_bytes);
            assert_eq!(undo_names, expected_name_bytes);
            assert!(owned_bytes >= nested);
            assert!(undo_bytes >= undo_names);
            assert!(sampled_total >= owned_bytes + undo_bytes);
            assert!(session.resource_ledger.inference_session_peak_bytes >= sampled_total);
            assert_eq!(session.resource_boundary_samples, live_samples);
            assert_eq!(session.resource_ledger.inference_session_retained_bytes, sampled_total);
            let live_peak = session.resource_ledger.inference_session_peak_bytes;
            assert_eq!(state.nested_bytes, before_nested);
            assert!(state.annotation_values.is_empty());
            assert!(state.annotation_effects.is_empty());
            assert!(state.formal_domains.is_empty());
            let surviving_state_bytes = state.bytes().unwrap();
            assert_eq!(surviving_state_bytes, state.formal_owned_bytes());
            session.sample_f4_resources(ResourceBoundary::IncomingRoute).unwrap();
            assert_eq!(session.resource_boundary_samples, live_samples + 1);
            assert_eq!(session.execution_counters.inference_session_retained_bytes, session.resource_ledger.inference_session_retained_bytes);
            assert!(session.resource_ledger.inference_session_retained_bytes >= surviving_state_bytes);
            assert_eq!(session.resource_ledger.inference_session_peak_bytes, live_peak);
        }
    }
    #[test]
    fn formal_and_whole_annotation_share_tail_in_the_returned_effect_fiber() {
        let mut session = make_session("act E\nmy left (f:int -> ['e] int): (int -> ['e] int) -> (int -> ['e] int) = { my pure x = 1; pure }");
        let owner = root(&session, "left");
        session.execute_candidate_source_root(&owner).unwrap();
        let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        assert_eq!(state.annotation_effects.len(), 1, "formal and whole annotation own one shared tail");
        let tail = state.annotation_effects[&(AnnotationScope::Definition(owner.clone()), Box::<str>::from("'e"))];
        let component = session.batch.root_component_positions[&owner].component;
        let value = session.live_components[component].ordinal;
        let contribution = atom(&mut session, "E");
        let (occurrence, cause) = cause(&session, "left", 61);
        session.constrain_live_effect(contribution, EffectEndpointKey::EffectRow(tail), &occurrence, &cause).unwrap();
        assert!(session.errors.is_empty());
        let graph = session.capture_candidate_graph(value, 0).unwrap();
        fn fiber(graph: &crate::candidate_scheme::Graph, start: usize, kind: ComponentKind) -> Vec<usize> {
            let mut pending = vec![start];
            let mut seen = Vec::new();
            while let Some(node) = pending.pop() {
                if seen.contains(&node) { continue; }
                seen.push(node);
                if let Node::EffectOperand { tail: Some(tail), .. } = graph.nodes[node] { pending.push(tail); }
                for bound in graph.bounds.iter().filter(|bound| bound.kind == kind) {
                    let same_row = match (graph.nodes[node], graph.nodes[bound.upper]) {
                        (Node::Row { row: a, .. }, Node::Row { row: b, .. }) => graph.rows[a].key == graph.rows[b].key,
                        _ => false,
                    };
                    if bound.upper == node || same_row { pending.push(bound.lower); }
                }
            }
            seen
        }
        let outer: Vec<_> = fiber(&graph, graph.root, ComponentKind::Value).into_iter().filter_map(|index| match graph.nodes[index] {
            Node::Function { polarity: Polarity::Positive, children } => Some(children), _ => None,
        }).collect();
        assert!(!outer.is_empty());
        let mut checked = 0;
        for function in outer {
            for index in fiber(&graph, function[3], ComponentKind::Value) {
                let Node::Function { polarity: Polarity::Positive, children } = graph.nodes[index] else { continue; };
                let effects = fiber(&graph, children[2], ComponentKind::Effect);
                // The unannotated pure implementation is also a lower; inspect
                // the exposed annotation's returned Function at this fiber.
                if effects.iter().any(|&index| matches!(graph.nodes[index], Node::EffectOperand { endpoint: EffectEndpointKey::Support(_), .. })) {
                    assert!(effects.iter().any(|&index| matches!(graph.nodes[index], Node::Row { row, .. } if graph.rows[row].key == RowKey::Effect(tail))));
                    assert!(effects.iter().any(|&index| matches!(graph.nodes[index], Node::EffectOperand { endpoint, .. } if endpoint == contribution)), "late concrete lower reaches the returned annotation effect fiber");
                    checked += 1;
                }
            }
        }
        assert!(checked > 0, "returned annotation effect fiber was checked");
    }

    #[test]
    fn whole_annotation_failure_preserves_the_preexisting_formal_tail() {
        let mut session = make_session("my left (f:int -> ['e] int): (int -> ['e] int) -> (int -> ['e] int) = { my pure x = 1; pure }");
        let owner = root(&session, "left");
        let actions = session.batch.candidate_source.schedules[&owner].clone();
        let candidate_source::Action::FormalAnnotation { annotation, parameter, occurrence, scope } = actions.iter().find(|action| matches!(action, candidate_source::Action::FormalAnnotation { .. })).unwrap() else { unreachable!() };
        session.with_route_transaction(|session| session.candidate_formal_annotation(annotation, *parameter, occurrence, scope)).unwrap();
        let names = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_effects.clone();
        assert_eq!(names.len(), 1);
        let candidate_source::Action::Annotation { annotation, endpoint, target, occurrence, level } = actions.iter().find(|action| matches!(action, candidate_source::Action::Annotation { .. })).unwrap() else { unreachable!() };
        let mut checkpoint = None;
        assert_eq!(session.with_route_transaction(|session| {
            checkpoint = Some(RouteCheckpoint::capture(session));
            session.candidate_annotation(annotation, *endpoint, *target, occurrence, *level)?;
            assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_effects, names);
            Err::<(), _>(exhausted())
        }), Err(exhausted()));
        checkpoint.unwrap().assert_restored(&session);
        assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_effects, names);
    }

    #[test]
    fn symbolic_formal_tail_rows_are_scoped_to_local_bindings() {
        let mut session = make_session("my answer = { my first (f:int -> ['e] int) = f; my second (f:int -> ['e] int) = f; second }");
        let owner = root(&session, "answer");
        session.execute_candidate_source_root(&owner).unwrap();
        let rows = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_effects;
        assert_eq!(rows.len(), 2);
        let entries: Vec<_> = rows.iter().collect();
        assert!(entries.iter().all(|((scope, name), _)| matches!(scope, AnnotationScope::Local(_)) && name.as_ref() == "'e"));
        assert_ne!(entries[0].0.0, entries[1].0.0);
        assert_ne!(entries[0].1, entries[1].1);
    }

    #[test]
    fn operation_nested_omitted_effect_rows_keep_their_actual_polarity_defaults() {
        let mut session = make_session("act tick:\n    our next: (() -> int) -> (int -> int)\n\nmy lookup = tick::next");
        let owner = root(&session, "lookup");
        session.execute_candidate_source_root(&owner).unwrap();
        let outer = session.store.facts().iter().find_map(|fact| match session.store.term_view(fact.lower()) {
            Ok(TermView::PositiveFunction { argument, argument_effect, result_effect, result }) => Some((argument, argument_effect, result_effect, result)),
            _ => None,
        }).unwrap();
        assert!(matches!(session.store.term_view(outer.1), Ok(TermView::Leaf(Leaf::EmptyEffectNegative))));
        let TermView::NegativeFunction { argument_effect, result_effect, .. } = session.store.term_view(outer.0).unwrap() else { panic!("nested negative Function"); };
        assert!(matches!(session.store.term_view(argument_effect), Ok(TermView::Leaf(Leaf::EffectBottomPositive))));
        assert!(matches!(session.store.term_view(result_effect), Ok(TermView::Leaf(Leaf::EmptyEffectNegative))));
        let TermView::PositiveFunction { argument_effect, result_effect, .. } = session.store.term_view(outer.3).unwrap() else { panic!("nested positive Function"); };
        assert!(matches!(session.store.term_view(argument_effect), Ok(TermView::Leaf(Leaf::EmptyEffectNegative))));
        assert!(matches!(session.store.term_view(result_effect), Ok(TermView::Leaf(Leaf::EffectBottomPositive))));
        let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        assert!(state.views.iter().all(|view| view.allowed == vec![session.batch.hir.source_effect_declarations()[0].id.clone()]));
    }
    #[test]
    fn operation_views_preserve_symbolic_tail_provenance_and_rollback_owned_payload() {
        let mut session = make_session("act E\nact tick:\n    our next: 'a -> [E, 'e] 'a\n\nmy lookup = tick::next");
        let owner = root(&session, "lookup");
        session.execute_candidate_source_root(&owner).unwrap();
        let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        let original = state.views.iter().position(|view| matches!(view.provenance, ViewOrigin::Operation(_))).unwrap() as u32;
        let view = &state.views[original as usize];
        assert_eq!(view.allowed, vec![session.batch.hir.source_effect_declarations()[1].id.clone(), session.batch.hir.source_effect_declarations()[0].id.clone()]);
        let tail = view.tail.expect("original symbolic tail retained");
        let ViewOrigin::Operation(origin) = &view.provenance else { unreachable!() };
        let operation = origin.clone();
        let retained_bytes = operation.retained_bytes;
        let copy = session.candidate_copy_effect_view(original, Some(tail)).unwrap();
        assert_ne!(copy, original);
        let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        let ViewOrigin::Operation(copied) = &state.views[copy as usize].provenance else { panic!("typed provenance copied"); };
        assert_eq!(copied.declaration.id, operation.declaration.id);
        assert_eq!(copied.occurrence, operation.occurrence);
        assert_eq!(state.views[copy as usize].tail, Some(tail));
        let before_views = state.views.len();
        let before_nested = state.nested_bytes;
        let before_rows = session.effect_bounds.len();
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.fail_after_view = true;
        let result: Result<(), SolveAvailabilityError> = session.with_route_transaction(|session| {
            session.candidate_copy_effect_view(original, Some(tail))?;
            panic!("injected view publication failure must abort the route")
        });
        assert_eq!(result, Err(exhausted()));
        let graph = session.candidate_graph.as_ref().unwrap();
        let state = &graph.intrusion.effect_algebra;
        assert_eq!(state.views.len(), before_views);
        assert_eq!(state.nested_bytes, before_nested);
        assert_eq!(session.effect_bounds.len(), before_rows);
        assert_eq!(graph.scratch_bytes, 0);
        let (_, sampled_view_bytes) = state.failed_view_sample.unwrap();
        assert!(sampled_view_bytes >= before_nested + retained_bytes, "failed publication sample charges the owned signature payload before rollback");
        assert!(session.resource_ledger.inference_session_peak_bytes >= sampled_view_bytes);
    }
    fn root(session: &InferenceSession, name: &str) -> DefinitionRootId {
        session
            .batch
            .hir
            .items()
            .iter()
            .find_map(|item| match item {
                HirItem::Binding(binding) if binding.name().spelling() == name => {
                    Some(binding.definition_root().clone())
                }
                _ => None,
            })
            .unwrap()
    }
    fn cause(
        session: &InferenceSession,
        name: &str,
        slot: u8,
    ) -> (ConstraintOccurrenceId, CauseId) {
        let root = root(session, name);
        let source = session.batch.hir.local_source(&root).unwrap().unwrap();
        let occurrence = ConstraintOccurrenceId::new(
            source.expressions()[source.body().ordinal() as usize]
                .occurrence
                .clone(),
            slot,
        );
        let cause = CauseId::for_occurrence(occurrence.clone());
        (occurrence, cause)
    }
    fn atom(session: &mut InferenceSession, name: &str) -> EffectEndpointKey {
        let declaration = session
            .batch
            .hir
            .source_effect_declarations()
            .iter()
            .find(|declaration| declaration.spelling.as_ref() == name)
            .unwrap();
        let (effect, origin) = (declaration.id.clone(), declaration.id.declaration.clone());
        session
            .candidate_effect_contribution(effect, origin)
            .unwrap()
    }
    fn view(session: &InferenceSession, name: &str) -> u32 {
        let owner = root(session, name);
        session
            .candidate_graph
            .as_ref()
            .unwrap()
            .intrusion
            .effect_algebra
            .views
            .iter()
            .position(|view| view.owner == owner)
            .unwrap() as u32
    }
    fn solve_effect(
        session: &mut InferenceSession,
        lower: EffectEndpointKey,
        upper: EffectEndpointKey,
        slot: u8,
    ) {
        let (occurrence, cause) = cause(session, "left", slot);
        session
            .constrain_live_effect(lower, upper, &occurrence, &cause)
            .unwrap();
    }
    #[test]
    fn covariant_allowance_is_not_production_and_conflicts_keep_actual_boundary_and_cause() {
        let mut session =
            make_session("act E\nact F\nmy left x: int -> [E] int = x; my pure x: int -> int = x");
        for name in ["left", "pure"] {
            let root = root(&session, name);
            session.execute_candidate_source_root(&root).unwrap();
        }
        assert!(
            session
                .candidate_graph
                .as_ref()
                .unwrap()
                .intrusion
                .effect_algebra
                .contributions
                .is_empty()
        );
        let allowed = EffectEndpointKey::Allowance(view(&session, "left"));
        let e = atom(&mut session, "E");
        let f = atom(&mut session, "F");
        solve_effect(&mut session, e, allowed, 1);
        assert!(session.errors.is_empty());
        solve_effect(&mut session, f, allowed, 2);
        solve_effect(&mut session, f, allowed, 3);
        assert_eq!(session.errors.len(), 2);
        for slot in [2, 3] {
            let (occurrence, cause) = cause(&session, "left", slot);
            assert!(
                session
                    .errors
                    .iter()
                    .any(|error| error.occurrence == occurrence && error.cause == cause)
            );
        }
        let SolverErrorKind::IncompatibleEffect {
            operand,
            annotation,
        } = session.errors[0].kind
        else {
            panic!("effect conflict")
        };
        let state = &session
            .candidate_graph
            .as_ref()
            .unwrap()
            .intrusion
            .effect_algebra;
        let (contribution_ref, annotation_ref) = state.observe(operand, annotation).unwrap();
        let ObservedOperand::Contribution(contribution_ref) = contribution_ref else {
            panic!("actual contribution")
        };
        assert_eq!(
            contribution_ref.effect,
            session.batch.hir.source_effect_declarations()[1].id
        );
        assert_eq!(annotation_ref.unwrap().owner, root(&session, "left"));
        let other = make_session("act E\nmy left x = x");
        assert!(
            other
                .candidate_graph
                .as_ref()
                .unwrap()
                .intrusion
                .effect_algebra
                .observe(operand, annotation)
                .is_none()
        );
        solve_effect(&mut session, f, EffectEndpointKey::EmptyNegative, 4);
        assert!(matches!(
            session.errors.last().unwrap().kind,
            SolverErrorKind::IncompatibleEffect {
                annotation: None,
                ..
            }
        ));
        let omitted = EffectEndpointKey::Allowance(view(&session, "pure"));
        solve_effect(&mut session, f, omitted, 5);
        let SolverErrorKind::IncompatibleEffect {
            operand,
            annotation,
        } = session.errors.last().unwrap().kind
        else {
            unreachable!()
        };
        assert!(annotation.is_some());
        assert_eq!(
            session
                .candidate_graph
                .as_ref()
                .unwrap()
                .intrusion
                .effect_algebra
                .observe(operand, annotation)
                .unwrap()
                .1
                .unwrap()
                .position,
            session
                .batch
                .hir
                .local_source(&root(&session, "pure"))
                .unwrap()
                .unwrap()
                .annotation()
                .unwrap()
                .position
        );
    }
    #[test]
    fn union_tail_preserves_flow_and_cached_effect_and_function_roots_replay_future_conflicts() {
        let mut session = make_session(
            "act E\nact F\nact G\nmy left x: 'a -> [E, 'e] 'a = x; my right x: 'a -> [F] 'a = x",
        );
        for name in ["left", "right"] {
            let root = root(&session, name);
            session.execute_candidate_source_root(&root).unwrap();
        }
        let left = view(&session, "left");
        let right = view(&session, "right");
        let tail = session
            .candidate_graph
            .as_ref()
            .unwrap()
            .intrusion
            .effect_algebra
            .views[left as usize]
            .tail
            .unwrap();
        let e = atom(&mut session, "E");
        let f = atom(&mut session, "F");
        let g = atom(&mut session, "G");
        solve_effect(&mut session, e, EffectEndpointKey::Allowance(left), 1);
        assert!(
            !session.effect_bounds[tail as usize]
                .exact_non_variable_lowers
                .contains(&e),
            "allowed E creates no tail backflow"
        );
        solve_effect(&mut session, f, EffectEndpointKey::Allowance(left), 2);
        assert!(
            session.effect_bounds[tail as usize]
                .exact_non_variable_lowers
                .contains(&f)
        );
        solve_effect(
            &mut session,
            EffectEndpointKey::EffectRow(tail),
            EffectEndpointKey::Allowance(right),
            3,
        );
        assert!(session.errors.is_empty());
        let input = session.fresh_effect_at_level(1).unwrap();
        let port = session.fresh_effect_at_level(1).unwrap();
        session
            .candidate_insert_bound(
                ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(port)),
                Polarity::Negative,
                ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(left)),
            )
            .unwrap();
        solve_effect(
            &mut session,
            EffectEndpointKey::EffectRow(input),
            EffectEndpointKey::EffectRow(port),
            4,
        );
        let positive_effect = session.live_effect_term(Polarity::Positive, input).unwrap();
        let negative_effect = session.live_effect_term(Polarity::Negative, port).unwrap();
        let positive = session
            .positive_function_term(
                session.batch.collected_leaf_term(Leaf::IntNegative),
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                positive_effect,
                session.batch.collected_leaf_term(Leaf::IntPositive),
            )
            .unwrap();
        let negative = session
            .negative_function_term(
                session.batch.collected_leaf_term(Leaf::IntPositive),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                negative_effect,
                session.batch.collected_leaf_term(Leaf::IntNegative),
            )
            .unwrap();
        let pair = CanonicalValuePairKey {
            lower: ValueEndpointKey::PositiveFunction(positive),
            upper: ValueEndpointKey::NegativeFunction(negative),
        };
        let (occurrence, origin) = cause(&session, "left", 5);
        session
            .constrain_live_value(pair, &occurrence, &origin)
            .unwrap();
        solve_effect(&mut session, g, EffectEndpointKey::EffectRow(input), 6);
        assert_eq!(session.errors.len(), 1);
        solve_effect(
            &mut session,
            EffectEndpointKey::EffectRow(input),
            EffectEndpointKey::EffectRow(port),
            7,
        );
        let (occurrence, origin) = cause(&session, "left", 8);
        session
            .constrain_live_value(pair, &occurrence, &origin)
            .unwrap();
        assert_eq!(
            session.errors.len(),
            3,
            "both cached roots reach the later conflict with new inducing causes"
        );
        assert!(session.errors.iter().all(|error| {
            match error.kind {
                SolverErrorKind::IncompatibleEffect {
                    operand,
                    annotation,
                } => {
                    session
                        .candidate_graph
                        .as_ref()
                        .unwrap()
                        .intrusion
                        .effect_algebra
                        .observe(operand, annotation)
                        .unwrap()
                        .1
                        .unwrap()
                        .owner
                        == root(&session, "right")
                }
                _ => false,
            }
        }));
    }
    #[test]
    fn views_keep_fresh_use_ownership_and_intrusion_rollback_restores_relations() {
        let mut session = make_session(
            "act E\nact F\nmy left x: 'a -> [E, 'e] 'a = x; my first = left; my second = left",
        );
        session.execute_candidate_graph_plan().unwrap();
        let graph = session.candidate_graph.as_ref().unwrap();
        let original = view(&session, "left");
        let checking = session
            .effect_bounds
            .iter()
            .enumerate()
            .find(|(_, bounds)| {
                bounds
                    .exact_non_variable_uppers
                    .contains(&EffectEndpointKey::Allowance(original))
            })
            .unwrap()
            .0;
        assert_eq!(
            session.effect_levels[checking], 1,
            "checking port remains at the actual body level"
        );
        assert!(
            session.effect_bounds.iter().any(|bounds| bounds
                .exact_non_variable_lowers
                .contains(&EffectEndpointKey::Support(original))),
            "paired exposed target retains the same annotation view and symbolic tail"
        );
        assert_eq!(graph.routes.len(), 2);
        assert!(
            graph
                .routes
                .iter()
                .all(|route| route.graph.nodes.iter().any(|node| matches!(
                    node,
                    Node::EffectOperand {
                        endpoint: EffectEndpointKey::Support(_),
                        polarity: Polarity::Positive,
                        ..
                    }
                )))
        );
        let ids = |route: &crate::candidate_scheme::FreshRoute| -> HashSet<u32> {
            route
                .rows
                .iter()
                .filter_map(|row| match graph.intrusion.rep(*row) {
                    RowKey::Effect(row) => Some(row),
                    _ => None,
                })
                .flat_map(|row| {
                    session.effect_bounds[row as usize]
                        .exact_non_variable_lowers
                        .iter()
                        .filter_map(|endpoint| match endpoint {
                            EffectEndpointKey::Support(id) => Some(*id),
                            _ => None,
                        })
                })
                .collect()
        };
        let first = ids(&graph.routes[0]);
        let second = ids(&graph.routes[1]);
        assert!(!first.is_empty() && !second.is_empty());
        assert!(first.is_disjoint(&second));
        for id in first.iter().chain(&second) {
            assert_eq!(
                graph.intrusion.effect_algebra.views[*id as usize].owner,
                root(&session, "left")
            );
        }
        let allowed = view(&session, "left");
        let closed = session.candidate_copy_effect_view(allowed, None).unwrap();
        let parent = session.fresh_effect_at_level(2).unwrap();
        session
            .candidate_insert_bound(
                ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(parent)),
                Polarity::Negative,
                ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(closed)),
            )
            .unwrap();
        let before = session
            .candidate_graph
            .as_ref()
            .unwrap()
            .intrusion
            .effect_algebra
            .checkpoint();
        let old_edges = session
            .candidate_graph
            .as_ref()
            .unwrap()
            .intrusion
            .effect_algebra
            .edge_keys
            .len();
        let old_origins = session
            .candidate_graph
            .as_ref()
            .unwrap()
            .intrusion
            .effect_algebra
            .origin_keys
            .len();
        let old_errors = session.errors.len();
        let old_rows = session.effect_bounds.len();
        let (occurrence, cause) = cause(&session, "left", 20);
        let result: Result<(), SolveAvailabilityError> =
            session.with_route_transaction(|session| {
                let ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(copy)) = session
                    .candidate_extrude(
                        ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(parent)),
                        Polarity::Positive,
                        0,
                    )?
                else {
                    unreachable!()
                };
                session.candidate_restore_bound(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(copy)),
                    Polarity::Negative,
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(parent)),
                    &occurrence,
                    &cause,
                )?;
                session.constrain_live_effect(
                    EffectEndpointKey::EffectRow(copy),
                    EffectEndpointKey::EffectRow(copy),
                    &occurrence,
                    &cause,
                )?;
                assert_eq!(
                    session.canonical_effect(EffectEndpointKey::EffectRow(copy)),
                    EffectEndpointKey::EffectRow(parent)
                );
                let f = atom(session, "F");
                solve_effect(session, f, EffectEndpointKey::EffectRow(copy), 21);
                assert!(session.errors.len() > old_errors);
                Err(exhausted())
            });
        assert_eq!(result, Err(exhausted()));
        let state = &session
            .candidate_graph
            .as_ref()
            .unwrap()
            .intrusion
            .effect_algebra;
        assert_eq!(state.views.len(), before.views);
        assert_eq!(state.contributions.len(), before.contributions);
        assert_eq!(state.edge_keys.len(), old_edges);
        assert_eq!(state.origin_keys.len(), old_origins);
        assert_eq!(session.errors.len(), old_errors);
        assert_eq!(session.effect_bounds.len(), old_rows);
        assert_eq!(session.effect_levels[parent as usize], 2);
        assert!(state.processing.is_none());
        assert!(
            session.effect_bounds[parent as usize]
                .exact_non_variable_uppers
                .contains(&EffectEndpointKey::Allowance(closed))
        );
    }
    #[test]
    fn forbidden_siblings_do_not_contaminate_a_later_allowed_cause() {
        let mut session = make_session("act E\nact F\nmy left x: int -> [E] int = x");
        let root = root(&session, "left");
        session.execute_candidate_source_root(&root).unwrap();
        let port = session.fresh_effect_at_level(1).unwrap();
        let allowed = EffectEndpointKey::Allowance(view(&session, "left"));
        solve_effect(
            &mut session,
            EffectEndpointKey::EffectRow(port),
            allowed,
            30,
        );
        let first = atom(&mut session, "F");
        let second = atom(&mut session, "F");
        let allowed_atom = atom(&mut session, "E");
        solve_effect(&mut session, first, EffectEndpointKey::EffectRow(port), 31);
        solve_effect(&mut session, second, EffectEndpointKey::EffectRow(port), 32);
        assert_eq!(session.errors.len(), 2);
        let operands: Vec<_> = session
            .errors
            .iter()
            .map(|error| match error.kind {
                SolverErrorKind::IncompatibleEffect { operand, .. } => operand,
                _ => panic!("effect conflict"),
            })
            .collect();
        assert_ne!(
            operands[0], operands[1],
            "independent F contributions keep their own diagnostic identity"
        );
        solve_effect(
            &mut session,
            allowed_atom,
            EffectEndpointKey::EffectRow(port),
            33,
        );
        assert_eq!(
            session.errors.len(),
            2,
            "allowed E must not replay sibling F conflicts under E's cause"
        );
        for slot in [31, 32] {
            let (occurrence, cause) = cause(&session, "left", slot);
            assert_eq!(
                session
                    .errors
                    .iter()
                    .filter(|error| error.occurrence == occurrence && error.cause == cause)
                    .count(),
                1
            );
        }
        solve_effect(
            &mut session,
            EffectEndpointKey::EffectRow(port),
            allowed,
            34,
        );
        assert_eq!(
            session.errors.len(),
            4,
            "the cached creator replays both later forbidden children"
        );
        let (occurrence, cause) = cause(&session, "left", 34);
        assert_eq!(
            session
                .errors
                .iter()
                .filter(|error| error.occurrence == occurrence && error.cause == cause)
                .count(),
            2
        );
    }
    #[test]
    fn multiatom_view_copy_is_shared_and_member_tails_freshen_with_the_view() {
        let mut session = make_session("act E\nact F\nact G\nact H\nmy left x = x");
        let owner = root(&session, "left");
        let allowed: Vec<_> = session
            .batch
            .hir
            .source_effect_declarations()
            .iter()
            .map(|declaration| declaration.id.clone())
            .collect();
        let tail = session.fresh_effect_at_level(2).unwrap();
        let original = session
            .candidate_effect_view(owner, allowed[0].declaration.clone(), allowed, Some(tail))
            .unwrap();
        let port = session.fresh_effect_at_level(2).unwrap();
        let value = session.fresh_value_at_level(2).unwrap();
        for (side, endpoint) in [
            (Polarity::Positive, EffectEndpointKey::Support(original)),
            (Polarity::Negative, EffectEndpointKey::Allowance(original)),
        ] {
            session
                .candidate_insert_bound(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(port)),
                    side,
                    ExtrusionEndpoint::Effect(endpoint),
                )
                .unwrap();
        }
        for member in 0..4 {
            session
                .candidate_insert_bound(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(port)),
                    Polarity::Positive,
                    ExtrusionEndpoint::Effect(EffectEndpointKey::AnnotationMember(
                        original, member,
                    )),
                )
                .unwrap();
        }
        let effect = session.live_effect_term(Polarity::Positive, port).unwrap();
        let function = session
            .positive_function_term(
                session.batch.collected_leaf_term(Leaf::IntNegative),
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                effect,
                session.batch.collected_leaf_term(Leaf::IntPositive),
            )
            .unwrap();
        session
            .candidate_insert_bound(
                ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(value)),
                Polarity::Positive,
                ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(function)),
            )
            .unwrap();
        let graph = session.capture_candidate_graph(value, 1).unwrap();
        assert_eq!(
            graph
                .nodes
                .iter()
                .filter(|node| matches!(
                    node,
                    Node::EffectOperand {
                        endpoint: EffectEndpointKey::AnnotationMember(_, _),
                        tail: Some(_),
                        ..
                    }
                ))
                .count(),
            4
        );
        let tail_index = graph
            .rows
            .iter()
            .position(|row| row.key == RowKey::Effect(tail))
            .unwrap();
        let (occurrence, cause) = cause(&session, "left", 40);
        let entry_scratch = session.candidate_graph.as_ref().unwrap().scratch_bytes;
        let mut copies = Vec::new();
        for _ in 0..2 {
            let before = session
                .candidate_graph
                .as_ref()
                .unwrap()
                .intrusion
                .effect_algebra
                .views
                .len();
            let (_, rows) = session
                .freshen_candidate_graph(&graph, 1, &occurrence, &cause)
                .unwrap();
            session.candidate_graph.as_mut().unwrap().scratch_bytes = entry_scratch;
            let state = &session
                .candidate_graph
                .as_ref()
                .unwrap()
                .intrusion
                .effect_algebra;
            assert_eq!(
                state.views.len() - before,
                1,
                "Support, Allowance and all members reuse one mapped view"
            );
            assert_eq!(
                state.views[before].allowed.len(),
                4,
                "copied atom slots are linear in the original view"
            );
            let RowKey::Effect(mapped_tail) = rows[tail_index] else {
                unreachable!()
            };
            assert_ne!(mapped_tail, tail);
            assert_eq!(state.views[before].tail, Some(mapped_tail));
            copies.push(mapped_tail);
            let RowKey::Effect(mapped_port) = rows[graph
                .rows
                .iter()
                .position(|row| row.key == RowKey::Effect(port))
                .unwrap()]
            else {
                unreachable!()
            };
            let bounds = &session.effect_bounds[mapped_port as usize];
            let copy = before as u32;
            assert!(
                bounds
                    .exact_non_variable_lowers
                    .contains(&EffectEndpointKey::Support(copy))
            );
            assert!(
                bounds
                    .exact_non_variable_uppers
                    .contains(&EffectEndpointKey::Allowance(copy))
            );
            for member in 0..4 {
                assert!(
                    bounds
                        .exact_non_variable_lowers
                        .contains(&EffectEndpointKey::AnnotationMember(copy, member))
                );
            }
        }
        assert_ne!(
            copies[0], copies[1],
            "independent uses do not share eligible young tails"
        );
    }
    #[test]
    fn extrusion_maps_opposite_tails_separately_and_drops_scratch_on_failure() {
        let mut session = make_session("act E\nact F\nmy left x = x");
        let owner = root(&session, "left");
        let allowed: Vec<_> = session
            .batch
            .hir
            .source_effect_declarations()
            .iter()
            .map(|declaration| declaration.id.clone())
            .collect();
        let tail = session.fresh_effect_at_level(2).unwrap();
        let original = session
            .candidate_effect_view(owner, allowed[0].declaration.clone(), allowed, Some(tail))
            .unwrap();
        let port = session.fresh_effect_at_level(2).unwrap();
        for (side, endpoint) in [
            (Polarity::Positive, EffectEndpointKey::Support(original)),
            (Polarity::Negative, EffectEndpointKey::Allowance(original)),
        ] {
            session
                .candidate_insert_bound(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(port)),
                    side,
                    ExtrusionEndpoint::Effect(endpoint),
                )
                .unwrap();
        }
        for member in 0..2 {
            session
                .candidate_insert_bound(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(port)),
                    Polarity::Positive,
                    ExtrusionEndpoint::Effect(EffectEndpointKey::AnnotationMember(
                        original, member,
                    )),
                )
                .unwrap();
        }
        let before = session
            .candidate_graph
            .as_ref()
            .unwrap()
            .intrusion
            .effect_algebra
            .views
            .len();
        let ae = session.live_effect_term(Polarity::Negative, port).unwrap();
        let re = session.live_effect_term(Polarity::Positive, port).unwrap();
        let function = session
            .positive_function_term(
                session.batch.collected_leaf_term(Leaf::IntNegative),
                ae,
                re,
                session.batch.collected_leaf_term(Leaf::IntPositive),
            )
            .unwrap();
        session
            .candidate_extrude(
                ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(function)),
                Polarity::Positive,
                0,
            )
            .unwrap();
        let state = &session
            .candidate_graph
            .as_ref()
            .unwrap()
            .intrusion
            .effect_algebra;
        assert_eq!(
            state.views.len() - before,
            2,
            "one view per mapped polarity tail, not per atom member"
        );
        assert_ne!(state.views[before].tail, state.views[before + 1].tail);
        assert!(
            state.views[before..]
                .iter()
                .all(|view| view.allowed.len() == 2 && view.tail != Some(tail))
        );
        assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
        let old_views = state.views.len();
        let old_rows = session.effect_bounds.len();
        let old_nested = state.nested_bytes;
        let old_origins = state.origin_keys.len();
        let old_peak = session.resource_ledger.inference_session_peak_bytes;
        session
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .fail_after_view = true;
        let result: Result<(), SolveAvailabilityError> =
            session.with_route_transaction(|session| {
                session.candidate_extrude(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::Support(original)),
                    Polarity::Positive,
                    0,
                )?;
                panic!("injected failure after view publication must abort extrusion");
            });
        assert_eq!(result, Err(exhausted()));
        let graph = session.candidate_graph.as_ref().unwrap();
        let state = &graph.intrusion.effect_algebra;
        let (scratch, view_bytes) = state.failed_view_sample.unwrap();
        assert!(
            scratch > 0 && view_bytes > 0,
            "view publication samples coexistence with all extrusion scratch"
        );
        assert!(session.resource_ledger.inference_session_peak_bytes >= old_peak);
        assert!(
            session.resource_ledger.inference_session_peak_bytes >= scratch + view_bytes,
            "peak retains simultaneous scratch and annotation storage"
        );
        assert_eq!(
            graph.scratch_bytes, 0,
            "failure scope drops scratch before removing its charge"
        );
        assert_eq!(state.views.len(), old_views);
        assert_eq!(state.nested_bytes, old_nested);
        assert_eq!(state.origin_keys.len(), old_origins);
        assert_eq!(session.effect_bounds.len(), old_rows);
    }
}
