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
pub(super) enum AnnotationScope { Definition(DefinitionRootId), Source(SourceRootId), Local(HirLocalId), Expression(yu_hir::shadow::LocalSourceIndex) }
impl AnnotationScope {
    pub(super) fn for_source(owner: SourceRootId) -> Self {
        match owner { SourceRootId::Definition(root) => Self::Definition(root), expression => Self::Source(expression) }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CaptureBucket { pub head: usize, pub tail: usize }
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CaptureIncidence { pub source: u32, pub view: u32, pub next: Option<usize> }
// Research observer: allocator requests are counted only during one inverse
// restoration. The production map and hasher are unchanged.
#[cfg(test)]
mod capture_probe_allocator {
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::cell::Cell;
    thread_local! {
        static ACTIVE: Cell<bool> = const { Cell::new(false) };
        static REQUESTS: Cell<usize> = const { Cell::new(0) };
    }
    struct Observer;
    #[global_allocator]
    static ALLOCATOR: Observer = Observer;
    fn request() {
        let _ = ACTIVE.try_with(|active| {
            if active.get() { let _ = REQUESTS.try_with(|count| count.set(count.get() + 1)); }
        });
    }
    unsafe impl GlobalAlloc for Observer {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            request();
            unsafe { System.alloc(layout) }
        }
        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            request();
            unsafe { System.alloc_zeroed(layout) }
        }
        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
            request();
            unsafe { System.realloc(ptr, layout, size) }
        }
        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            unsafe { System.dealloc(ptr, layout) }
        }
    }
    pub(super) fn begin() {
        REQUESTS.with(|count| count.set(0));
        ACTIVE.with(|active| assert!(!active.replace(true)));
    }
    pub(super) fn end() -> usize {
        ACTIVE.with(|active| active.set(false));
        REQUESTS.with(Cell::get)
    }
}
#[cfg(test)]
#[derive(Debug)]
struct CaptureProbeEvent {
    inverse: bool,
    // Vector residence only: LocalUse moves its frame out during an atomic
    // owner step, so false does not exclude execution inside that owner.
    local_frame: bool,
    row: u32,
    old_present: bool,
    before: (usize, usize),
    after: (usize, usize),
    allocation_requests: usize,
}
#[cfg(test)]
#[derive(Debug)]
struct CaptureProbe {
    events: Vec<CaptureProbeEvent>,
    fail_at_full_new: bool,
    failed: bool,
}
#[derive(Debug, Default)]
pub(super) struct State {
    pub context: candidate_context::State,
    pub formal_domains: HashMap<usize, Term>,
    pub(super) formal_permissions: Vec<FormalPermission>,
    formal_permission_bytes: usize,
    pub(super) annotation_values: HashMap<(AnnotationScope, Box<str>), u32>,
    // Effect names share binding scope while remaining separate from value names.
    annotation_effects: HashMap<(AnnotationScope, Box<str>), u32>,
    pub contributions: Vec<Contribution>,
    pub views: Vec<View>,
    pub(super) field_bounds_v1: Vec<FieldBoundV1>,
    field_bounds_v1_payload_bytes: usize,
    prepared_fields_v1: Vec<PreparedFieldV1>,
    brand: u64,
    pub processing: Option<TypedPairKey>,
    origins: HashMap<BoundKey, Vec<TypedPairKey>>,
    origin_keys: HashSet<(BoundKey, TypedPairKey)>,
    // Capture incidence only: these are ordinary bounds, never row edges.
    pub(super) capture_incidence: HashMap<u32, CaptureBucket>,
    pub(super) capture_records: Vec<CaptureIncidence>,
    capture_incidence_keys: HashSet<(u32, u32)>,
    conflicts: HashMap<TypedPairKey, Conflict>,
    nested_bytes: usize,
    evidence_bytes: usize,
    #[cfg(test)]
    fail_after_view: bool,
    #[cfg(test)]
    failed_view_sample: Option<(usize, usize)>,
    #[cfg(test)]
    failed_formal_sample: Option<(usize, usize, usize, usize, usize, usize)>,
    #[cfg(test)]
    capture_probe: Option<CaptureProbe>,
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
    Annotation(&'a SourceAnnotation, AnnotationScope),
    Operation { declaration: &'a Arc<yu_hir::shadow::SourceOperationDeclaration>, owner: &'a SourceRootId, occurrence: &'a HirOccurrenceId, retained_bytes: usize },
    Primitive { owner: &'a SourceRootId, position: &'a SourceNodeKey },
}
impl SignatureContext<'_> {
    fn owner(&self) -> &SourceRootId { match self { Self::Annotation(a, _) => &a.owner, Self::Operation { owner, .. } | Self::Primitive { owner, .. } => owner } }
    fn position(&self) -> &SourceNodeKey { match self { Self::Annotation(a, _) => &a.position, Self::Operation { declaration, .. } => &declaration.signature_position, Self::Primitive { position, .. } => position } }
    fn operation(&self) -> Option<OperationOrigin> { match self { Self::Annotation(_, _) | Self::Primitive { .. } => None, Self::Operation { declaration, occurrence, retained_bytes, .. } => Some(OperationOrigin { declaration: Arc::clone(declaration), occurrence: (*occurrence).clone(), retained_bytes: *retained_bytes }) } }
}
#[derive(Debug)]
pub(super) struct View {
    pub closed_weight: Option<candidate_context::LocalWeightId>,
    pub source_weight: Option<candidate_context::LocalWeightId>,
    pub provenance: ViewOrigin,
    pub owner: SourceRootId,
    pub position: SourceNodeKey,
    pub allowed: Vec<SourceEffectId>,
    pub tail: Option<u32>,
}
#[derive(Clone, Debug)]
pub(super) struct FieldBoundV1 {
    pub id: u32,
    pub source_occurrence: HirOccurrenceId,
    pub source_slot: u8,
    pub q: candidate_source::LicensedOperationFieldV1,
    pub m0: candidate_source::CallbackFieldRealizationV1,
    pub lower: EffectEndpointKey,
    pub upper: EffectEndpointKey,
    pub consumed: bool,
}
#[derive(Clone, Debug)]
struct PreparedFieldV1 {
    request: HirOccurrenceId,
    catch: HirOccurrenceId,
    arm_source: SourceNodeKey,
    declaration: yu_hir::shadow::SourceOperationId,
    h_arg: candidate_source::HandlerContinuationArgumentV1,
    q_view: u32,
    negative_row: u32,
}
fn same_handler_argument_v1(
    left: &candidate_source::HandlerContinuationArgumentV1,
    right: &candidate_source::HandlerContinuationArgumentV1,
) -> bool {
    left.owner == right.owner
        && left.request == right.request
        && left.catch_occurrence == right.catch_occurrence
        && left.arm_source == right.arm_source
        && left.declaration == right.declaration
        && left.continuation == right.continuation
        && left.apply_occurrence == right.apply_occurrence
        && left.argument_occurrence == right.argument_occurrence
        && left.response_definition == right.response_definition
        && Arc::ptr_eq(&left.response_annotation, &right.response_annotation)
        && left.declaration_field_position == right.declaration_field_position
        && left.response_field_position == right.response_field_position
        && left.field_family == right.field_family
        && left.callback_apply_occurrence == right.callback_apply_occurrence
        && left.callback_argument_occurrence == right.callback_argument_occurrence
        && left.callback_operation_occurrence == right.callback_operation_occurrence
        && Arc::ptr_eq(&left.callback_operation, &right.callback_operation)
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FormalPortStep { Argument, Result }
// This retained record describes local source permission only. It is not an
// arrival, provider, contribution or consumer witness.
#[allow(dead_code, reason = "the approved producer retains source permission; authentic arrival consumption remains open")]
#[derive(Debug)]
pub(super) struct FormalPermission {
    pub(super) parameter: usize,
    pub(super) occurrence: HirOccurrenceId,
    pub(super) source_owner: SourceRootId,
    scope: AnnotationScope,
    pub(super) path: Vec<FormalPortStep>,
    pub(super) source_row: SourceNodeKey,
    pub(super) concrete: Vec<SourceEffectId>,
}
pub(super) struct Checkpoint {
    context: candidate_context::Checkpoint,
    contributions: usize,
    views: usize,
    field_bounds_v1: usize,
    field_bounds_v1_payload_bytes: usize,
    prepared_fields_v1: usize,
    nested_bytes: usize,
    processing: Option<TypedPairKey>,
    origins: Vec<(BoundKey, TypedPairKey, bool)>,
    capture_incidence: Vec<(u32, Option<CaptureBucket>)>,
    capture_links: Vec<(usize, Option<usize>)>,
    capture_keys: Vec<(u32, u32)>,
    capture_records: usize,
    conflicts: Vec<TypedPairKey>,
    formal_domains: Vec<usize>,
    formal_permissions: usize,
    formal_permission_bytes: usize,
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
    pub(super) fn context_checkpoint(&self) -> candidate_context::Checkpoint {
        self.context
    }
    pub fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        bytes::<(BoundKey, TypedPairKey, bool)>(self.origins.capacity())?
            .checked_add(bytes::<(u32, Option<CaptureBucket>)>(self.capture_incidence.capacity())?)
            .and_then(|n| n.checked_add(bytes::<(usize, Option<usize>)>(self.capture_links.capacity()).ok()?))
            .and_then(|n| n.checked_add(bytes::<(u32, u32)>(self.capture_keys.capacity()).ok()?))
            .and_then(|n| n.checked_add(bytes::<TypedPairKey>(self.conflicts.capacity()).ok()?))
            .and_then(|n| n.checked_add(bytes::<usize>(self.formal_domains.capacity()).ok()?))
            .and_then(|n| n.checked_add(bytes::<(AnnotationScope, Box<str>)>(self.annotation_values.capacity()).ok()?))
            .and_then(|n| n.checked_add(bytes::<(AnnotationScope, Box<str>)>(self.annotation_effects.capacity()).ok()?))
            .and_then(|n| n.checked_add(self.annotation_value_bytes))
            .ok_or_else(exhausted)
    }
}
fn formal_permission_backing_bytes(permissions: &[FormalPermission]) -> Result<usize, SolveAvailabilityError> {
    permissions.iter().try_fold(0usize, |total, permission| {
        let path = bytes::<FormalPortStep>(permission.path.capacity())?;
        let concrete = bytes::<SourceEffectId>(permission.concrete.capacity())?;
        total.checked_add(path).and_then(|n| n.checked_add(concrete)).ok_or_else(exhausted)
    })
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
            context: self.context.checkpoint(),
            contributions: self.contributions.len(),
            views: self.views.len(),
            field_bounds_v1: self.field_bounds_v1.len(),
            field_bounds_v1_payload_bytes: self.field_bounds_v1_payload_bytes,
            prepared_fields_v1: self.prepared_fields_v1.len(),
            nested_bytes: self.nested_bytes,
            processing: self.processing,
            origins: Vec::new(),
            capture_incidence: Vec::new(),
            capture_links: Vec::new(),
            capture_keys: Vec::new(),
            capture_records: self.capture_records.len(),
            conflicts: Vec::new(),
            formal_domains: Vec::new(),
            formal_permissions: self.formal_permissions.len(),
            formal_permission_bytes: self.formal_permission_bytes,
            annotation_values: Vec::new(),
            annotation_effects: Vec::new(),
            annotation_value_bytes: 0,
        }
    }
    pub fn rollback(&mut self, checkpoint: Checkpoint) {
        self.context.rollback(checkpoint.context);
        for key in checkpoint.formal_domains { self.formal_domains.remove(&key); }
        self.formal_permissions.truncate(checkpoint.formal_permissions);
        self.formal_permission_bytes = checkpoint.formal_permission_bytes;
        for key in checkpoint.annotation_values { self.annotation_values.remove(&key); }
        for key in checkpoint.annotation_effects { self.annotation_effects.remove(&key); }
        for key in checkpoint.conflicts {
            self.conflicts.remove(&key);
        }
        for (bound, origin, new) in checkpoint.origins.into_iter().rev() {
            self.origin_keys.remove(&(bound, origin));
            assert_eq!(self.origins.get_mut(&bound).unwrap().pop(), Some(origin));
            if new {
                let entries = self.origins.remove(&bound).unwrap();
                self.evidence_bytes -= entries.capacity() * std::mem::size_of::<TypedPairKey>();
            }
        }
        for (index, next) in checkpoint.capture_links.into_iter().rev() {
            self.capture_records[index].next = next;
        }
        for (row, bucket) in checkpoint.capture_incidence.into_iter().rev() {
            #[cfg(test)]
            let probe_before = (self.capture_incidence.len(), self.capture_incidence.capacity());
            #[cfg(test)]
            if bucket.is_some() && self.capture_probe.is_some() { capture_probe_allocator::begin(); }
            if let Some(bucket) = bucket {
                if let Some(current) = self.capture_incidence.get_mut(&row) { *current = bucket; }
                else { self.capture_incidence.insert(row, bucket); }
            }
            else { self.capture_incidence.remove(&row); }
            #[cfg(test)]
            if let Some(probe) = &mut self.capture_probe {
                let allocation_requests = if bucket.is_some() { capture_probe_allocator::end() } else { 0 };
                probe.events.push(CaptureProbeEvent { inverse: true, local_frame: false, row, old_present: bucket.is_some(),
                    before: probe_before, after: (self.capture_incidence.len(), self.capture_incidence.capacity()), allocation_requests });
            }
        }
        for key in checkpoint.capture_keys { self.capture_incidence_keys.remove(&key); }
        self.capture_records.truncate(checkpoint.capture_records);
        self.contributions.truncate(checkpoint.contributions);
        self.views.truncate(checkpoint.views);
        self.field_bounds_v1.truncate(checkpoint.field_bounds_v1);
        self.field_bounds_v1_payload_bytes = checkpoint.field_bounds_v1_payload_bytes;
        self.prepared_fields_v1.truncate(checkpoint.prepared_fields_v1);
        self.nested_bytes = checkpoint.nested_bytes;
        self.processing = checkpoint.processing;
    }
    pub fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        let parts = [
            self.context.bytes()?,
            bytes::<Contribution>(self.contributions.capacity())?,
            bytes::<View>(self.views.capacity())?,
            bytes::<FieldBoundV1>(self.field_bounds_v1.capacity())?,
            self.field_bounds_v1_payload_bytes,
            bytes::<PreparedFieldV1>(self.prepared_fields_v1.capacity())?,
            bytes::<(BoundKey, Vec<TypedPairKey>)>(self.origins.capacity())?,
            bytes::<(BoundKey, TypedPairKey)>(self.origin_keys.capacity())?,
            bytes::<(u32, CaptureBucket)>(self.capture_incidence.capacity())?,
            bytes::<(u32, u32)>(self.capture_incidence_keys.capacity())?,
            bytes::<CaptureIncidence>(self.capture_records.capacity())?,
            bytes::<(TypedPairKey, Conflict)>(self.conflicts.capacity())?,
            bytes::<(usize, Term)>(self.formal_domains.capacity())?,
            bytes::<FormalPermission>(self.formal_permissions.capacity())?,
            bytes::<((AnnotationScope, Box<str>), u32)>(self.annotation_values.capacity())?,
            bytes::<((AnnotationScope, Box<str>), u32)>(self.annotation_effects.capacity())?,
            self.nested_bytes,
            self.formal_permission_bytes,
            self.evidence_bytes,
        ];
        parts
            .into_iter()
            .try_fold(0usize, |n, part| n.checked_add(part).ok_or_else(exhausted))
    }
    #[cfg(test)]
    fn formal_owned_bytes(&self) -> usize {
        let state = self;
        // Formal witnesses may own annotation views, but never operation payloads.
        assert!(state.contributions.is_empty());
        assert!(state.views.iter().all(|view| matches!(view.provenance, ViewOrigin::Annotation)));
        let evidence_bytes = state.origins.values()
            .map(|entries| entries.capacity() * std::mem::size_of::<TypedPairKey>())
            .sum::<usize>();
        assert_eq!(state.evidence_bytes, evidence_bytes);
        let retained_names = state.annotation_values.keys().chain(state.annotation_effects.keys()).map(|(_, name)| name.len()).sum::<usize>();
        let retained_views = state.views.iter().map(|view| view.allowed.capacity() * std::mem::size_of::<SourceEffectId>()).sum::<usize>();
        let retained_permissions = state.formal_permissions.iter().map(|permission| {
            permission.path.capacity() * std::mem::size_of::<FormalPortStep>()
                + permission.concrete.capacity() * std::mem::size_of::<SourceEffectId>()
        }).sum::<usize>();
        assert_eq!(state.nested_bytes, retained_names + retained_views);
        assert_eq!(state.formal_permission_bytes, retained_permissions);
        state.context.enumerated_bytes()
            + state.contributions.capacity() * std::mem::size_of::<Contribution>()
            + state.views.capacity() * std::mem::size_of::<View>()
            + state.origins.capacity() * std::mem::size_of::<(BoundKey, Vec<TypedPairKey>)>()
            + state.origin_keys.capacity() * std::mem::size_of::<(BoundKey, TypedPairKey)>()
            + state.capture_incidence.capacity() * std::mem::size_of::<(u32, CaptureBucket)>()
            + state.capture_incidence_keys.capacity() * std::mem::size_of::<(u32, u32)>()
            + state.capture_records.capacity() * std::mem::size_of::<CaptureIncidence>()
            + state.conflicts.capacity() * std::mem::size_of::<(TypedPairKey, Conflict)>()
            + state.formal_domains.capacity() * std::mem::size_of::<(usize, Term)>()
            + state.formal_permissions.capacity() * std::mem::size_of::<FormalPermission>()
            + state.annotation_values.capacity() * std::mem::size_of::<((AnnotationScope, Box<str>), u32)>()
            + state.annotation_effects.capacity() * std::mem::size_of::<((AnnotationScope, Box<str>), u32)>()
            + retained_names + retained_views + evidence_bytes + retained_permissions
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
    ) -> Result<Option<candidate_context::RelationId>, SolveAvailabilityError> {
        self.candidate_context_admit(task)
    }
    #[cfg(test)]
    pub(super) fn candidate_bound_origin_count(&self, bound: BoundKey) -> usize {
        self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.origins.get(&bound).map_or(0, Vec::len)
    }
    pub(super) fn candidate_bound_origin(
        &mut self, bound: BoundKey, explicit: Option<TypedPairKey>,
    ) -> Result<(), SolveAvailabilityError> {
        let Some(graph) = &self.candidate_graph else { return Ok(()); };
        let cause = candidate_context::BoundAdmissionCause::OwnerEmission { processing: graph.intrusion.effect_algebra.context.processing };
        self.candidate_bound_origin_with_evidence(bound, explicit, cause).map(|_| ())
    }
    pub(super) fn candidate_bound_origin_with_evidence(
        &mut self,
        bound: BoundKey,
        explicit: Option<TypedPairKey>,
        cause: candidate_context::BoundAdmissionCause,
    ) -> Result<candidate_context::BoundAdmissionId, SolveAvailabilityError> {
        let graph = self.candidate_graph.as_ref().ok_or_else(exhausted)?;
        let origin = explicit.or(graph.intrusion.effect_algebra.processing).unwrap_or_else(|| bound_pair(bound));
        self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.evidence_attempt();
        let scoped = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.scoped_enabled;
        let relation = if scoped {
            match cause {
                candidate_context::BoundAdmissionCause::FreshUse { antecedent, use_origin, source_bound, mapped_relation: Some(relation) } =>
                    Some(self.candidate_context_reuse_fresh_relation(bound, antecedent, source_bound, use_origin, relation)?),
                candidate_context::BoundAdmissionCause::FreshUse { mapped_relation: None, .. } => return Err(SolveAvailabilityError::ReceiptMismatch),
                // Diagnostic origins have no retained origin-to-fiber association.
                // The first transport loop owns every executable copied fiber.
                candidate_context::BoundAdmissionCause::BoundTransport { .. } => None,
                candidate_context::BoundAdmissionCause::OwnerEmission { .. } => Some(self.candidate_context_bound(bound, origin)?),
                candidate_context::BoundAdmissionCause::ExtrusionLink { .. } => Some(self.candidate_context_extrusion_link(bound, origin)?),
            }
        } else { Some(self.candidate_context_bound(bound, origin)?) };
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra;
        if state.origin_keys.contains(&(bound, origin)) {
            let id = state.context.evidence_admit(bound, origin, relation, cause, true)?;
            state.context.evidence_admission_sample();
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            #[cfg(test)]
            self.candidate_evidence_failure(candidate_context::EvidenceFailurePoint::Admission)?;
            return Ok(id);
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
        let id = state.context.evidence_admit(bound, origin, relation, cause, false)?;
        state.context.evidence_admission_sample();
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        #[cfg(test)]
        self.candidate_evidence_failure(candidate_context::EvidenceFailurePoint::Admission)?;
        Ok(id)
    }
    pub(super) fn candidate_capture_incidence(
        &mut self, tail: u32, source: u32, view: u32,
    ) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        let probe_local_frame = self.candidate_graph.as_ref().is_some_and(|state| !state.local_use.is_empty());
        let state = &mut self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion.effect_algebra;
        if state.capture_incidence_keys.contains(&(source, view)) { return Ok(()); }
        let bucket = state.capture_incidence.get(&tail).copied();
        #[cfg(test)]
        let probe_before = (state.capture_incidence.len(), state.capture_incidence.capacity());
        let mut undo = self.route_journal.as_mut().and_then(|journal| journal.intrusion.as_mut())
            .map(|undo| &mut undo.effect_algebra);
        if let Some(undo) = &mut undo {
            undo.capture_incidence.try_reserve(1).map_err(|_| exhausted())?;
            undo.capture_keys.try_reserve(1).map_err(|_| exhausted())?;
            undo.capture_links.try_reserve(usize::from(bucket.is_some())).map_err(|_| exhausted())?;
        }
        state.capture_incidence_keys.try_reserve(1).map_err(|_| exhausted())?;
        state.capture_incidence.try_reserve(1).map_err(|_| exhausted())?;
        state.capture_records.try_reserve(1).map_err(|_| exhausted())?;
        let index = state.capture_records.len();
        if let Some(undo) = &mut undo {
            undo.capture_incidence.push((tail, bucket));
            undo.capture_keys.push((source, view));
        }
        if let Some(bucket) = bucket {
            if let Some(undo) = &mut undo { undo.capture_links.push((bucket.tail, state.capture_records[bucket.tail].next)); }
            state.capture_records[bucket.tail].next = Some(index);
        }
        state.capture_records.push(CaptureIncidence { source, view, next: None });
        state.capture_incidence.insert(tail, CaptureBucket { head: bucket.map_or(index, |bucket| bucket.head), tail: index });
        state.capture_incidence_keys.insert((source, view));
        #[cfg(test)]
        if let Some(probe) = &mut state.capture_probe {
            probe.events.push(CaptureProbeEvent { inverse: false, local_frame: probe_local_frame, row: tail, old_present: bucket.is_some(),
                before: probe_before, after: (state.capture_incidence.len(), state.capture_incidence.capacity()), allocation_requests: 0 });
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        #[cfg(test)]
        {
            let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra;
            if let Some(probe) = &mut state.capture_probe {
                if probe.fail_at_full_new && bucket.is_none() && state.capture_incidence.len() >= 16
                    && state.capture_incidence.len() == state.capture_incidence.capacity()
                    && probe.events.iter().rev().nth(1).is_some_and(|event| !event.inverse && event.old_present) {
                    probe.failed = true;
                    return Err(exhausted());
                }
            }
        }
        Ok(())
    }
    pub(super) fn candidate_splice_capture_incidence(&mut self, from: u32, to: u32) -> Result<(), SolveAvailabilityError> {
        if from == to { return Ok(()); }
        let state = &mut self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion.effect_algebra;
        let Some(source) = state.capture_incidence.get(&from).copied() else { return Ok(()); };
        let destination = state.capture_incidence.get(&to).copied();
        let mut undo = self.route_journal.as_mut().and_then(|journal| journal.intrusion.as_mut())
            .map(|undo| &mut undo.effect_algebra);
        if let Some(undo) = &mut undo {
            undo.capture_incidence.try_reserve(2).map_err(|_| exhausted())?;
            undo.capture_links.try_reserve(usize::from(destination.is_some())).map_err(|_| exhausted())?;
        }
        state.capture_incidence.try_reserve(1).map_err(|_| exhausted())?;
        if let Some(undo) = &mut undo {
            undo.capture_incidence.push((from, Some(source)));
            undo.capture_incidence.push((to, destination));
        }
        if let Some(destination) = destination {
            if let Some(undo) = &mut undo { undo.capture_links.push((destination.tail, state.capture_records[destination.tail].next)); }
            state.capture_records[destination.tail].next = Some(source.head);
        }
        state.capture_incidence.remove(&from);
        state.capture_incidence.insert(to, CaptureBucket { head: destination.map_or(source.head, |bucket| bucket.head), tail: source.tail });
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
    pub(super) fn candidate_register_capture_bound(&mut self, bound: BoundKey) -> Result<(), SolveAvailabilityError> {
        if let BoundKey(ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(source)), Polarity::Negative,
            ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(view))) = bound {
            if let Some(tail) = self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.effect_algebra.views[view as usize].tail {
                let EffectEndpointKey::EffectRow(tail) = self.canonical_effect(EffectEndpointKey::EffectRow(tail)) else { unreachable!() };
                self.candidate_capture_incidence(tail, source, view)?;
            }
        }
        Ok(())
    }
    pub(super) fn candidate_transfer_bound_origins(
        &mut self,
        from: BoundKey,
        to: BoundKey,
        reason: candidate_context::TransportReason,
    ) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        candidate_context::r148_trace(format!("bound-transport from={from:?} to={to:?} reason={reason:?}"));
        let mut cursor = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_cursor(from);
        while let Some(index) = cursor {
            let (parent, next) = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_entry(index);
            cursor = next;
            self.candidate_context_transport_witness_with_evidence(parent, to, 0, candidate_context::TransportWitness { from, to, reason })?;
        }
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
            // The origin table does not retain an origin-to-fiber association.
            // In scoped mode BoundTransport admits metadata with relation None;
            // only the first loop transports executable fibers. Preserve the
            // association gap instead of seeding an identity alternative.
            let relation = None;
            let snapshot = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.evidence_snapshot(from, relation)
                .with_gap(candidate_context::CoverageGap::MissingOriginAssociation);
            let antecedent = self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.import_evidence(snapshot)?;
            self.candidate_bound_origin_with_evidence(to, Some(origin), candidate_context::BoundAdmissionCause::BoundTransport { antecedent, through: reason })?;
            #[cfg(test)]
            self.candidate_evidence_failure(candidate_context::EvidenceFailurePoint::Transport)?;
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
            let initial_pair = self.candidate_context_pair(task_key(initial));
            pending.push(task_key(initial));
            if initial_pair != task_key(initial) { pending.try_reserve(1).map_err(|_| exhausted())?; pending.push(initial_pair); }
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
                let count = state.context.children(key).count();
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
                pending.extend(self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.children(key));
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
        self.candidate_signature_view(owner.into(), position, allowed, tail, None, None)
    }
    fn candidate_signature_view(
        &mut self,
        owner: SourceRootId,
        position: SourceNodeKey,
        allowed: Vec<SourceEffectId>,
        tail: Option<u32>,
        operation: Option<OperationOrigin>,
        attachment_source: Option<candidate_context::AttachmentSource>,
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
        // Source attachment identity survives symbolic tails; only closed
        // annotation views expose an executable zero-word filter.
        let source_weight = if operation.is_none() && (tail.is_none() || attachment_source.is_some()) {
            Some(state.context.source_weight(id, &owner, &position, &allowed, attachment_source)?)
        } else { None };
        let closed_weight = if tail.is_none() { source_weight } else { None };
        state.views.push(View {
            closed_weight,
            source_weight,
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
    pub(super) fn candidate_operation(&mut self, declaration: &Arc<yu_hir::shadow::SourceOperationDeclaration>, owner: &SourceRootId, occurrence: &HirOccurrenceId, target: usize, level: u32) -> Result<(), SolveAvailabilityError> {
        let mut values = HashMap::new();
        let mut effects = HashMap::new();
        let mut views = HashMap::new();
        let count = declaration.signature.node_count();
        let retained_bytes = std::mem::size_of::<yu_hir::shadow::SourceOperationDeclaration>().checked_add(declaration.retained_arena_bytes()).ok_or_else(exhausted)?;
        values.try_reserve(count).map_err(|_| exhausted())?;
        effects.try_reserve(count).map_err(|_| exhausted())?;
        views.try_reserve(count).map_err(|_| exhausted())?;
        let scratch = bytes::<(Box<str>, u32)>(values.capacity())?.checked_add(bytes::<(Box<str>, u32)>(effects.capacity())?)
            .and_then(|n| n.checked_add(bytes::<(SourceNodeKey, u32)>(views.capacity()).ok()?))
            .and_then(|n| n.checked_add(retained_bytes))
            .ok_or_else(exhausted)?;
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

    pub(super) fn candidate_pinned_primitive(
        &mut self,
        operation: yu_hir::shadow::PinnedPrimitiveOp,
        owner: &SourceRootId,
        position: &SourceNodeKey,
        occurrence: &HirOccurrenceId,
        target: usize,
        level: u32,
    ) -> Result<(), SolveAvailabilityError> {
        use yu_hir::shadow::{SourceAnnotationType as Ty, SourceAnnotationValue as Value};
        let atom = |value| Ty { effects: None, value };
        let (argument, result) = match operation {
            yu_hir::shadow::PinnedPrimitiveOp::IntAdd => (Value::Int, Value::Int),
            yu_hir::shadow::PinnedPrimitiveOp::IntToString => (Value::Int, Value::Str),
            yu_hir::shadow::PinnedPrimitiveOp::StringConcat => (Value::Str, Value::Str),
            yu_hir::shadow::PinnedPrimitiveOp::Unsupported(_) => return Err(exhausted()),
        };
        let value_type = if matches!(&operation, yu_hir::shadow::PinnedPrimitiveOp::IntToString) {
            Ty { effects: None, value: Value::Function { argument: Box::new(atom(argument)), result: Box::new(atom(result)) } }
        } else {
            let inner = Ty { effects: None, value: Value::Function { argument: Box::new(atom(argument.clone())), result: Box::new(atom(result)) } };
            Ty { effects: None, value: Value::Function { argument: Box::new(atom(argument)), result: Box::new(inner) } }
        };
        let mut values = HashMap::new();
        let mut effects = HashMap::new();
        let mut views = HashMap::new();
        let context = SignatureContext::Primitive { owner, position };
        let value = self.candidate_signature_value(
            &context, &value_type, Polarity::Positive, Polarity::Positive,
            level.checked_add(1).ok_or_else(exhausted)?, &mut values, &mut effects, &mut views,
        )?;
        self.admit_candidate_value_link(occurrence, 42, value, self.batch.component_term_at(target))
    }
    pub(super) fn candidate_catch_operation(&mut self, declaration: &Arc<yu_hir::shadow::SourceOperationDeclaration>, owner: &SourceRootId, occurrence: &HirOccurrenceId, payload: Option<usize>, continuation: Option<usize>, original: shadow_apply::CandidateEndpoint, effect: usize, level: u32, h_arg: Option<&candidate_source::HandlerContinuationArgumentV1>) -> Result<(), SolveAvailabilityError> {
        if let Some(link) = h_arg {
            self.with_route_transaction(|session| session.candidate_catch_operation_inner(declaration, owner, occurrence, payload, continuation, original, effect, level, Some(link)))
        } else {
            self.candidate_catch_operation_inner(declaration, owner, occurrence, payload, continuation, original, effect, level, None)
        }
    }
    fn candidate_catch_operation_inner(&mut self, declaration: &Arc<yu_hir::shadow::SourceOperationDeclaration>, owner: &SourceRootId, occurrence: &HirOccurrenceId, payload: Option<usize>, continuation: Option<usize>, original: shadow_apply::CandidateEndpoint, effect: usize, level: u32, h_arg: Option<&candidate_source::HandlerContinuationArgumentV1>) -> Result<(), SolveAvailabilityError> {
        let SourceAnnotationValue::Function { argument, result } = &declaration.signature.value else { return Err(exhausted()); };
        let mut values = HashMap::new();
        let mut effects = HashMap::new();
        let mut views = HashMap::new();
        let count = declaration.signature.node_count();
        let retained_bytes = std::mem::size_of::<yu_hir::shadow::SourceOperationDeclaration>().checked_add(declaration.retained_arena_bytes()).ok_or_else(exhausted)?;
        values.try_reserve(count).map_err(|_| exhausted())?;
        effects.try_reserve(count).map_err(|_| exhausted())?;
        views.try_reserve(count).map_err(|_| exhausted())?;
        let key_payload_bound = retained_bytes.checked_add(if h_arg.is_some() { "__operation_v1_q".len() } else { 0 }).ok_or_else(exhausted)?;
        let scratch = bytes::<(Box<str>, u32)>(values.capacity())?.checked_add(bytes::<(Box<str>, u32)>(effects.capacity())?)
            .and_then(|n| n.checked_add(bytes::<(SourceNodeKey, u32)>(views.capacity()).ok()?))
            .and_then(|n| n.checked_add(key_payload_bound))
            .ok_or_else(exhausted)?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(scratch).ok_or_else(exhausted)?;
        let mut negative_response_type_keepalive = None;
        let admitted = (|| {
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            let context = SignatureContext::Operation { declaration, owner, occurrence, retained_bytes };
            // One environment pairs declaration A/B. No outer operation family
            // is injected into either packet field's own latent interface.
            if let Some(payload) = payload {
                let positive = self.candidate_signature_value(&context, argument, Polarity::Positive, Polarity::Positive, level, &mut values, &mut effects, &mut views)?;
                let negative = self.candidate_signature_value(&context, argument, Polarity::Negative, Polarity::Negative, level, &mut values, &mut effects, &mut views)?;
                let target = self.batch.component_term_at(payload);
                self.admit_candidate_value_link(occurrence, 60, positive, target)?;
                self.admit_candidate_value_link(occurrence, 61, target, negative)?;
            }
            if let Some(continuation) = continuation {
                let mut negative_response_type = (**result).clone();
                let mut q_view = None;
                if let Some(link) = h_arg {
                    let SourceAnnotationValue::Function { result: callback_result, .. } = &mut negative_response_type.value else { return Err(exhausted()); };
                    let row = callback_result.effects.as_ref().ok_or_else(exhausted)?;
                    if row.position != link.declaration_field_position || row.concrete.len() != 1 || row.concrete[0] != link.field_family || !row.variables.is_empty() { return Err(exhausted()); }
                    let mut allowed = Vec::new();
                    allowed.try_reserve_exact(1).map_err(|_| exhausted())?;
                    allowed.push(link.field_family.clone());
                    q_view = Some(self.candidate_signature_view(owner.clone(), link.declaration_field_position.clone(), allowed, None, None, None)?);
                    let mut variables = Vec::new();
                    variables.try_reserve_exact(1).map_err(|_| exhausted())?;
                    variables.push(Box::<str>::from("__operation_v1_q"));
                    callback_result.effects = Some(SourceEffectRow {
                        position: link.declaration_field_position.clone(), concrete: Vec::new(), variables,
                    });
                }
                negative_response_type_keepalive = Some(negative_response_type);
                let negative_response = self.candidate_signature_value(&context, negative_response_type_keepalive.as_ref().ok_or_else(exhausted)?, Polarity::Negative, Polarity::Negative, level, &mut values, &mut effects, &mut views)?;
                if let (Some(link), Some(q_view)) = (h_arg, q_view) {
                    let negative_row = *effects.get("__operation_v1_q").ok_or_else(exhausted)?;
                    let source_slot = 249u8;
                    let id = ConstraintOccurrenceId::new(link.apply_occurrence.clone(), source_slot);
                    if self.store.provenance().iter().any(|edge| edge.cause().occurrence() == &id) { return Err(exhausted()); }
                    let cause = CauseId::for_occurrence(id.clone());
                    self.constrain_live_effect(EffectEndpointKey::EffectRow(negative_row), EffectEndpointKey::Allowance(q_view), &id, &cause)?;
                    let state = &mut self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion.effect_algebra;
                    if state.prepared_fields_v1.iter().any(|prepared| prepared.request == link.request && prepared.catch == link.catch_occurrence && prepared.arm_source == link.arm_source) { return Err(exhausted()); }
                    state.prepared_fields_v1.try_reserve(1).map_err(|_| exhausted())?;
                    state.prepared_fields_v1.push(PreparedFieldV1 {
                        request: link.request.clone(), catch: link.catch_occurrence.clone(), arm_source: link.arm_source.clone(),
                        declaration: declaration.id.clone(), h_arg: link.clone(), q_view, negative_row,
                    });
                }
                let positive_response = self.candidate_signature_value(&context, result, Polarity::Positive, Polarity::Positive, level, &mut values, &mut effects, &mut views)?;
                let original_positive = self.candidate_endpoint(original, Polarity::Positive)?;
                let original_negative = self.candidate_endpoint(original, Polarity::Negative)?;
                let entry = self.fresh_effect_at_level(level)?;
                let returned = self.fresh_effect_at_level(level)?;
                let entry_positive = self.live_effect_term(Polarity::Positive, entry)?;
                let return_negative = self.live_effect_term(Polarity::Negative, returned)?;
                let original_effect = self.live_effect_term(Polarity::Positive, self.live_components[effect].ordinal)?;
                // Raw resumption receives a Value response, so its argument
                // computation is forced at entry by the existing entry rule.
                for (slot, lower) in [(64, entry_positive), (65, original_effect)] {
                    let id = ConstraintOccurrenceId::new(occurrence.clone(), slot);
                    let cause = CauseId::for_occurrence(id.clone());
                    self.store.admit_and_record_provenance(&ConstraintOccurrence { id: id.clone(), cause: cause.clone(), lower, upper: return_negative }).map_err(SolveAvailabilityError::from)?;
                    let inferred_entry = if slot == 64 {
                        Some(self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.retain_inferred_entry(occurrence, entry, returned, &id, &cause)?)
                    } else { None };
                    self.constrain_live_item_with_inferred_entry(TypedWorkItem {
                        task: LiveConstraintTask::Effect(self.effect_endpoint(lower, Polarity::Positive), self.effect_endpoint(return_negative, Polarity::Negative)),
                        relation: None, replay_ack: None,
                    }, &id, &cause, inferred_entry, None)?;
                }
                let entry_negative = self.live_effect_term(Polarity::Negative, entry)?;
                let return_positive = self.live_effect_term(Polarity::Positive, returned)?;
                // PROVISIONAL conservative full-S bound, matching Oracle's
                // constructor. Exact raw suffix effects can be empty; precision
                // and full handler hygiene remain OPEN. No handler is reinstalled.
                let positive = self.positive_function_term(negative_response, entry_negative, return_positive, original_positive)?;
                let negative = self.negative_function_term(positive_response, entry_positive, return_negative, original_negative)?;
                let target = self.batch.component_term_at(continuation);
                self.admit_candidate_value_link(occurrence, 62, positive, target)?;
                self.admit_candidate_value_link(occurrence, 63, target, negative)?;
            }
            Ok(())
        })();
        drop((values, effects, views));
        drop(negative_response_type_keepalive);
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= scratch;
        admitted
    }
    pub(super) fn candidate_field_bound_v1(&mut self, declaration: &Arc<yu_hir::shadow::SourceOperationDeclaration>, link: &candidate_source::HandlerContinuationArgumentV1) -> Result<(), SolveAvailabilityError> {
        self.with_route_transaction(|session| session.candidate_field_bound_v1_inner(declaration, link))
    }
    fn candidate_field_bound_v1_inner(&mut self, declaration: &Arc<yu_hir::shadow::SourceOperationDeclaration>, link: &candidate_source::HandlerContinuationArgumentV1) -> Result<(), SolveAvailabilityError> {
        if !self.batch.candidate_source.operation_v1 || declaration.id != link.declaration || link.owner != self.batch.candidate_source.source_owners.get(&link.request).cloned().ok_or_else(exhausted)? { return Err(exhausted()); }
        let lower_view = self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.effect_algebra.views.iter().enumerate().find_map(|(index, view)| {
            let ViewOrigin::Operation(origin) = &view.provenance else { return None; };
            (origin.occurrence == link.callback_operation_occurrence
                && origin.declaration.id == link.callback_operation.id
                && view.position == link.callback_operation.signature_position
                && view.allowed.as_slice() == [link.field_family.clone()]
                && view.tail.is_none()).then_some((index as u32, 0u32))
        }).ok_or_else(exhausted)?;
        let lower = EffectEndpointKey::AnnotationMember(lower_view.0, lower_view.1);
        let upper_view = self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.effect_algebra.prepared_fields_v1.iter().find_map(|prepared| {
            (prepared.request == link.request && prepared.catch == link.catch_occurrence && prepared.arm_source == link.arm_source
                && prepared.declaration == declaration.id && same_handler_argument_v1(&prepared.h_arg, link))
                .then_some((prepared.q_view, prepared.negative_row))
        }).ok_or_else(exhausted)?;
        let (upper_view, negative_port) = upper_view;
        let upper = EffectEndpointKey::Allowance(upper_view);
        // All ordinary source/recipe slots at this application are admitted
        // before the final v1 action. The dedicated slot is also checked in
        // the store's complete source provenance before it is allocated.
        let source_slot = 250u8;
        let id = ConstraintOccurrenceId::new(link.callback_apply_occurrence.clone(), source_slot);
        let cause = CauseId::for_occurrence(id.clone());
        if self.store.provenance().iter().any(|edge| edge.cause().occurrence() == &id) { return Err(exhausted()); }
        let state = &mut self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion.effect_algebra;
        if state.field_bounds_v1.iter().any(|record| record.m0.apply_occurrence == link.callback_apply_occurrence && record.source_slot == source_slot) { return Err(exhausted()); }
        let record_id = u32::try_from(state.field_bounds_v1.len()).map_err(|_| exhausted())?;
        let payload_bytes = std::mem::size_of::<yu_hir::shadow::SourceAnnotation>()
            .checked_add(link.response_annotation.retained_arena_bytes())
            .and_then(|n| n.checked_add(std::mem::size_of::<yu_hir::shadow::SourceOperationDeclaration>()))
            .and_then(|n| n.checked_add(declaration.retained_arena_bytes()))
            .and_then(|n| n.checked_add(link.callback_operation.retained_arena_bytes()))
            .ok_or_else(exhausted)?;
        let next_payload_bytes = state.field_bounds_v1_payload_bytes.checked_add(payload_bytes).ok_or_else(exhausted)?;
        state.field_bounds_v1.try_reserve(1).map_err(|_| exhausted())?;
        state.field_bounds_v1.push(FieldBoundV1 {
            id: record_id, source_occurrence: link.callback_apply_occurrence.clone(), source_slot,
            q: candidate_source::LicensedOperationFieldV1 {
                owner_request: link.request.clone(), declaration: Arc::clone(declaration),
                field_position: link.declaration_field_position.clone(), family: link.field_family.clone(),
                negative_port,
                handler_argument: link.clone(),
            },
            m0: candidate_source::CallbackFieldRealizationV1 {
                response_definition: link.response_definition.clone(), response_annotation: Arc::clone(&link.response_annotation),
                apply_occurrence: link.callback_apply_occurrence.clone(), operation_occurrence: link.callback_operation_occurrence.clone(),
                operation: Arc::clone(&link.callback_operation), handler_argument: link.clone(),
            },
            lower, upper, consumed: false,
        });
        state.field_bounds_v1_payload_bytes = next_payload_bytes;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        self.constrain_live_effect(lower, upper, &id, &cause)?;
        if self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.effect_algebra.conflicts.contains_key(&TypedPairKey::Effect { lower, upper }) {
            return Err(exhausted());
        }
        self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion.effect_algebra.field_bounds_v1[record_id as usize].consumed = true;
        Ok(())
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
            .views.get(id as usize).ok_or_else(exhausted)?;
        let context = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        if let Some(weight) = view.source_weight { context.validate_payload_view(weight, id, view)?; }
        else if view.closed_weight.is_some() { return Err(exhausted()); }
        let attachment_source = view.source_weight.and_then(|weight| context.attachment_source(weight));
        let (owner, position) = (view.owner.clone(), view.position.clone());
        let operation = match &view.provenance { ViewOrigin::Annotation => None, ViewOrigin::Operation(origin) => Some(origin.clone()) };
        let mut allowed = Vec::new();
        allowed
            .try_reserve_exact(view.allowed.len())
            .map_err(|_| exhausted())?;
        allowed.extend(view.allowed.iter().cloned());
        self.candidate_signature_view(owner, position, allowed, tail, operation, attachment_source)
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
                let allowed = view.closed_weight.map_or(view.allowed.as_slice(), |weight| state.context.allowed(weight));
                if allowed.contains(effect) {
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
            let undo_owned = undo.capture_incidence.capacity() * std::mem::size_of::<(u32, Option<CaptureBucket>)>()
                + undo.capture_links.capacity() * std::mem::size_of::<(usize, Option<usize>)>()
                + undo.capture_keys.capacity() * std::mem::size_of::<(u32, u32)>()
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

    fn candidate_formal_pair(
        &mut self, annotation: &SourceAnnotation, ty: &SourceAnnotationType, scope: &AnnotationScope,
        parameter: usize, occurrence: &HirOccurrenceId, variance: Polarity, level: u32,
        views: &mut HashMap<SourceNodeKey, u32>, path: &mut Vec<FormalPortStep>,
        permissions: &mut Vec<FormalPermission>, permission_nested_bytes: &mut usize, scratch_bytes: &mut usize,
    ) -> Result<(Term, Term), SolveAvailabilityError> {
        if ty.effects.as_ref().is_some_and(|row| row.variables.len() > 1 || (variance == Polarity::Negative
            && !((row.concrete.is_empty() && row.variables.len() == 1) || (!row.concrete.is_empty() && row.variables.is_empty())))) {
            return Err(exhausted());
        }
        self.candidate_formal_value_pair(annotation, ty, scope, parameter, occurrence, variance, level, views, path, permissions, permission_nested_bytes, scratch_bytes)
    }

    fn candidate_formal_value_pair(
        &mut self, annotation: &SourceAnnotation, ty: &SourceAnnotationType, scope: &AnnotationScope,
        parameter: usize, occurrence: &HirOccurrenceId, variance: Polarity, level: u32,
        views: &mut HashMap<SourceNodeKey, u32>, path: &mut Vec<FormalPortStep>,
        permissions: &mut Vec<FormalPermission>, permission_nested_bytes: &mut usize, scratch_bytes: &mut usize,
    ) -> Result<(Term, Term), SolveAvailabilityError> {
        match &ty.value {
            SourceAnnotationValue::Bool => Ok((self.batch.collected_leaf_term(Leaf::BoolPositive), self.batch.collected_leaf_term(Leaf::BoolNegative))),
            SourceAnnotationValue::Str => Ok((self.batch.collected_leaf_term(Leaf::StrPositive), self.batch.collected_leaf_term(Leaf::StrNegative))),
            SourceAnnotationValue::Int => Ok((self.batch.collected_leaf_term(Leaf::IntPositive), self.batch.collected_leaf_term(Leaf::IntNegative))),
            SourceAnnotationValue::Unit => Ok((self.batch.collected_leaf_term(Leaf::UnitPositive), self.batch.collected_leaf_term(Leaf::UnitNegative))),
            SourceAnnotationValue::Variable(name) => {
                let row = self.candidate_annotation_variable(scope, name, level)?;
                Ok((self.live_value_term(Polarity::Positive, row)?, self.live_value_term(Polarity::Negative, row)?))
            }
            SourceAnnotationValue::Function { argument, result } => {
                let reversed = if variance == Polarity::Positive { Polarity::Negative } else { Polarity::Positive };
                let base = path.len();
                path.push(FormalPortStep::Argument);
                let argument_pair = self.candidate_formal_pair(annotation, argument, scope, parameter, occurrence, reversed, level, views, path, permissions, permission_nested_bytes, scratch_bytes);
                path.truncate(base);
                let (ap, an) = argument_pair?;

                let base = path.len();
                path.push(FormalPortStep::Result);
                let result_pair = self.candidate_formal_pair(annotation, result, scope, parameter, occurrence, variance, level, views, path, permissions, permission_nested_bytes, scratch_bytes);
                path.truncate(base);
                let (rp, rn) = result_pair?;

                let base = path.len();
                path.push(FormalPortStep::Argument);
                let argument_effects = self.candidate_formal_effect_port(annotation, argument.effects.as_ref(), scope, parameter, occurrence, reversed, level, views, path, permissions, permission_nested_bytes, scratch_bytes);
                path.truncate(base);
                let (qap, qan) = argument_effects?;

                let base = path.len();
                path.push(FormalPortStep::Result);
                let result_effects = self.candidate_formal_effect_port(annotation, result.effects.as_ref(), scope, parameter, occurrence, variance, level, views, path, permissions, permission_nested_bytes, scratch_bytes);
                path.truncate(base);
                let (qrp, qrn) = result_effects?;
                Ok((self.positive_function_term(an, qan, qrp, rp)?, self.negative_function_term(ap, qap, qrn, rn)?))
            }
        }
    }

    fn candidate_formal_effect_port(
        &mut self, annotation: &SourceAnnotation, effects: Option<&SourceEffectRow>, scope: &AnnotationScope,
        parameter: usize, occurrence: &HirOccurrenceId, variance: Polarity, level: u32,
        views: &mut HashMap<SourceNodeKey, u32>, path: &[FormalPortStep],
        permissions: &mut Vec<FormalPermission>, permission_nested_bytes: &mut usize, scratch_bytes: &mut usize,
    ) -> Result<(Term, Term), SolveAvailabilityError> {
        let port = match effects {
            None => self.fresh_effect_at_level(level)?,
            Some(row) if row.concrete.is_empty() && row.variables.len() == 1 =>
                self.candidate_formal_effect_variable(scope, &row.variables[0], level)?,
            Some(row) if variance == Polarity::Negative && !row.concrete.is_empty() && row.variables.is_empty() => {
                let port = self.fresh_effect_at_level(level)?;
                // In a negative port, a concrete row such as [io] is an open
                // effect-row annotation ([io, 'e]); its concrete members grant
                // the formal's local handling permission but do not form a
                // closed upper bound on a supplied callback.
                if permissions.len() == permissions.capacity() { return Err(exhausted()); }
                let mut retained_path = Vec::new();
                retained_path.try_reserve_exact(path.len()).map_err(|_| exhausted())?;
                retained_path.extend_from_slice(path);
                let mut concrete = Vec::new();
                concrete.try_reserve_exact(row.concrete.len()).map_err(|_| exhausted())?;
                concrete.extend(row.concrete.iter().cloned());
                let backing = bytes::<FormalPortStep>(retained_path.capacity())?
                    .checked_add(bytes::<SourceEffectId>(concrete.capacity())?).ok_or_else(exhausted)?;
                let new_nested = permission_nested_bytes.checked_add(backing).ok_or_else(exhausted)?;
                let new_scratch = scratch_bytes.checked_add(backing).ok_or_else(exhausted)?;
                let graph = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
                graph.scratch_bytes = graph.scratch_bytes.checked_add(backing).ok_or_else(exhausted)?;
                *permission_nested_bytes = new_nested;
                *scratch_bytes = new_scratch;
                permissions.push(FormalPermission {
                    parameter,
                    occurrence: occurrence.clone(),
                    source_owner: annotation.owner.clone(),
                    scope: scope.clone(),
                    path: retained_path,
                    source_row: row.position.clone(),
                    concrete,
                });
                port
            }
            Some(row) if variance == Polarity::Positive && row.variables.len() <= 1 => {
                // Explicit covariant rows use the same source-owned view on both
                // sides; omitted and singleton symbolic ports stay shared rows.
                let context = SignatureContext::Annotation(annotation, scope.clone());
                let mut variables = HashMap::new();
                let positive = self.candidate_signature_effect(&context, Some(row), None, Polarity::Positive, variance, level, &mut variables, views)?;
                let negative = self.candidate_signature_effect(&context, Some(row), None, Polarity::Negative, variance, level, &mut variables, views)?;
                return Ok((positive, negative));
            }
            Some(_) => return Err(exhausted()),
        };
        Ok((self.live_effect_term(Polarity::Positive, port)?, self.live_effect_term(Polarity::Negative, port)?))
    }

    pub(super) fn candidate_formal_effect_equal(&mut self, occurrence: &HirOccurrenceId, slot: u8, first: u32, second: u32) -> Result<(), SolveAvailabilityError> {
        for (offset, lower, upper) in [(0, first, second), (1, second, first)] {
            let lower = self.live_effect_term(Polarity::Positive, lower)?;
            let upper = self.live_effect_term(Polarity::Negative, upper)?;
            let id = ConstraintOccurrenceId::new(occurrence.clone(), slot + offset);
            let cause = CauseId::for_occurrence(id.clone());
            self.store.admit_and_record_provenance(&ConstraintOccurrence { id: id.clone(), cause: cause.clone(), lower, upper }).map_err(SolveAvailabilityError::from)?;
            self.constrain_live_effect(self.effect_endpoint(lower, Polarity::Positive), self.effect_endpoint(upper, Polarity::Negative), &id, &cause)?;
        }
        Ok(())
    }

    pub(super) fn candidate_formal_entry_annotation(&mut self, registration: usize, annotation: &SourceAnnotation, occurrence: &HirOccurrenceId, scope: &AnnotationScope) -> Result<(), SolveAvailabilityError> {
        let row = annotation.ty.effects.as_ref().ok_or_else(exhausted)?;
        if row.variables.len() > 1 { return Err(exhausted()); }
        let entry = self.batch.candidate_calls.formals[registration].entry_effect.ok_or_else(exhausted)?;
        if let Some(name) = row.variables.first() {
            let level = self.effect_levels[entry as usize];
            let tail = self.candidate_formal_effect_variable(scope, name, level)?;
            self.candidate_formal_effect_equal(occurrence, 45, entry, tail)?;
        }
        // Concrete atoms grant local handling permission; they are not a
        // closed upper bound on the supplied computation. The source-owned
        // annotation remains on this action for the handling integration.
        Ok(())
    }

    pub(super) fn candidate_formal_annotation(
        &mut self, annotation: &SourceAnnotation, parameter: usize, occurrence: &HirOccurrenceId, scope: &AnnotationScope,
    ) -> Result<(), SolveAvailabilityError> {
        let row = self.parameter_live_base.checked_add(u32::try_from(parameter).map_err(|_| exhausted())?).ok_or_else(exhausted)?;
        let level = self.value_levels[row as usize];
        if self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.formal_domains.contains_key(&parameter) { return Err(exhausted()); }
        // Reserve source-bounded scratch for recursive child ports and their
        // retained Permission paths; source admission already bounds depth.
        let node_count = annotation.ty.node_count();
        let mut views = HashMap::new();
        views.try_reserve(node_count).map_err(|_| exhausted())?;
        let mut path = Vec::new();
        path.try_reserve_exact(node_count).map_err(|_| exhausted())?;
        let mut permissions = Vec::new();
        permissions.try_reserve_exact(node_count).map_err(|_| exhausted())?;
        let mut scratch = bytes::<(Term, Term, Term, Term, u32, u32)>(node_count)?
            .checked_add(bytes::<(SourceNodeKey, u32)>(views.capacity())?)
            .and_then(|n| n.checked_add(bytes::<FormalPortStep>(path.capacity()).ok()?))
            .and_then(|n| n.checked_add(bytes::<FormalPermission>(permissions.capacity()).ok()?))
            .ok_or_else(exhausted)?;
        let graph = self.candidate_graph.as_mut().unwrap();
        graph.scratch_bytes = graph.scratch_bytes.checked_add(scratch).ok_or_else(exhausted)?;
        let mut permission_nested_bytes = 0usize;
        let pair = (|| -> Result<(Term, Term), SolveAvailabilityError> {
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            self.candidate_formal_value_pair(annotation, &annotation.ty, scope, parameter, occurrence,
                Polarity::Negative, level, &mut views, &mut path, &mut permissions,
                &mut permission_nested_bytes, &mut scratch)
        })();
        let result = (|| -> Result<(), SolveAvailabilityError> {
            let (positive, negative) = pair?;
            #[cfg(test)]
            if FORMAL_ANNOTATION_FAIL_STAGE.with(|stage| if stage.get() == 1 { stage.set(0); true } else { false }) { return Err(exhausted()); }
            {
                let graph = self.candidate_graph.as_mut().unwrap();
                graph.intrusion.effect_algebra.formal_domains.try_reserve(1).map_err(|_| exhausted())?;
                graph.intrusion.effect_algebra.formal_permissions.try_reserve(permissions.len()).map_err(|_| exhausted())?;
            }
            if let Some(undo) = self.route_journal.as_mut().and_then(|journal| journal.intrusion.as_mut()) { undo.effect_algebra.formal_domains.try_reserve(1).map_err(|_| exhausted())?; }
            let upper = self.candidate_endpoint(shadow_apply::CandidateEndpoint::Parameter(parameter), Polarity::Negative)?;
            self.admit_candidate_value_link(occurrence, 43, positive, upper)?;
            #[cfg(test)]
            if FORMAL_ANNOTATION_FAIL_AFTER_FIRST_EDGE.with(|flag| flag.replace(false)) { return Err(exhausted()); }
            let lower = self.candidate_endpoint(shadow_apply::CandidateEndpoint::Parameter(parameter), Polarity::Positive)?;
            self.admit_candidate_value_link(occurrence, 44, lower, negative)?;
            let retained_permission_bytes = formal_permission_backing_bytes(&permissions)?;
            if retained_permission_bytes != permission_nested_bytes { return Err(exhausted()); }
            // Validate the ownership transfer before publishing anything.
            // State::bytes will own these nested vectors after the drain;
            // scratch keeps only the still-live outer temporary allocation.
            let scratch_after_transfer = scratch.checked_sub(retained_permission_bytes).ok_or_else(exhausted)?;
            let graph_scratch_after_transfer = self.candidate_graph.as_ref().unwrap().scratch_bytes
                .checked_sub(retained_permission_bytes).ok_or_else(exhausted)?;
            {
                let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra;
                state.formal_permission_bytes = state.formal_permission_bytes.checked_add(retained_permission_bytes).ok_or_else(exhausted)?;
                state.formal_permissions.extend(permissions.drain(..));
                if state.formal_domains.insert(parameter, negative).is_none() {
                    if let Some(undo) = self.route_journal.as_mut().and_then(|journal| journal.intrusion.as_mut()) { undo.effect_algebra.formal_domains.push(parameter); }
                }
            }
            self.candidate_graph.as_mut().unwrap().scratch_bytes = graph_scratch_after_transfer;
            scratch = scratch_after_transfer;
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            #[cfg(test)]
            self.record_failed_formal_sample(2)?;
            #[cfg(test)]
            if FORMAL_ANNOTATION_FAIL_STAGE.with(|stage| if stage.get() == 2 { stage.set(0); true } else { false }) { return Err(exhausted()); }
            Ok(())
        })();
        drop(views);
        drop(path);
        drop(permissions);
        let graph = self.candidate_graph.as_mut().unwrap();
        graph.scratch_bytes = graph.scratch_bytes.checked_sub(scratch).ok_or_else(exhausted)?;
        result
    }

    pub(super) fn candidate_local_annotation(
        &mut self, annotation: &SourceAnnotation, slot: usize,
        endpoint: shadow_apply::CandidateEndpoint, occurrence: &HirOccurrenceId,
        level: u32, boundary: u32, computation_effect: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let exposed = self.construct_candidate_local_annotation(annotation, slot, endpoint, occurrence, level, computation_effect)?;
        self.install_candidate_local_term(slot, exposed, boundary)
    }

    pub(super) fn construct_candidate_local_annotation(
        &mut self, annotation: &SourceAnnotation, slot: usize,
        endpoint: shadow_apply::CandidateEndpoint, occurrence: &HirOccurrenceId,
        level: u32, computation_effect: usize,
    ) -> Result<Term, SolveAvailabilityError> {
        if !candidate_source::preflight_local_annotation(&annotation.ty) { return Err(exhausted()); }
        let scope = AnnotationScope::Local(self.batch.candidate_source.locals.get(slot).ok_or_else(exhausted)?.clone());
        let context = SignatureContext::Annotation(annotation, scope);
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
            self.candidate_negative_empty_bundle(annotation, occurrence, &context, 41)?;
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            let negative = self.candidate_signature_value(
                &context, &annotation.ty,
                Polarity::Negative, Polarity::Positive, level,
                &mut value_variables, &mut effect_variables, &mut views,
            )?;
            let positive = self.candidate_signature_value(
                &context, &annotation.ty,
                Polarity::Positive, Polarity::Positive, level,
                &mut value_variables, &mut effect_variables, &mut views,
            )?;
            // Check the whole initializer; its evaluation effects remain on the
            // block edge. Only the paired annotation enters the local scheme.
            let root = self.fresh_value_at_level(level)?;
            let lower = self.candidate_endpoint(endpoint, Polarity::Positive)?;
            self.admit_candidate_value_link(occurrence, 40, lower, negative)?;
            self.candidate_annotation_computation_effect(
                &context, annotation, computation_effect, occurrence, level, 42,
                &mut effect_variables, &mut views,
            )?;
            #[cfg(test)]
            if FORMAL_ANNOTATION_FAIL_STAGE.with(|stage| if stage.get() == 4 { stage.set(0); true } else { false }) { return Err(exhausted()); }
            let upper = self.live_value_term(Polarity::Negative, root)?;
            self.admit_candidate_value_link(occurrence, 41, positive, upper)?;
            self.live_value_term(Polarity::Positive, root)
        })();
        drop((value_variables, effect_variables, views));
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= scratch;
        result
    }

    pub(super) fn candidate_register_source_role_obligation(
        &mut self,
        clause: &yu_hir::shadow::LocalSourceWhereClause,
        scope: &AnnotationScope,
    ) -> Result<(), SolveAvailabilityError> {
        let AnnotationScope::Definition(provider) = scope else { return Err(exhausted()); };
        let subject = clause.subject.text.trim();
        let Some(name) = subject.strip_prefix('\'') else { return Err(exhausted()); };
        if name.is_empty() || name.chars().any(char::is_whitespace) { return Err(exhausted()); }
        let role_spelling = clause.role.text.trim();
        if role_spelling.is_empty() { return Err(exhausted()); }
        let state = &self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.effect_algebra;
        let value = state.annotation_values.get(&(scope.clone(), Box::<str>::from(subject))).copied().ok_or_else(exhausted)?;
        let subject_row = self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.rep(crate::candidate_scheme::RowKey::Value(value));
        let role_identity = self.batch.hir_for_source_root(&SourceRootId::Definition(provider.clone()))
            .and_then(|hir| hir.source_imports()).and_then(|imports| {
            imports.role_id(role_spelling).cloned()
        });
        let candidate = crate::candidate_scheme::SourceRoleObligation {
            provider: provider.clone(),
            where_source: clause.source.clone(),
            subject_source: clause.subject.source.clone(),
            role_source: clause.role.source.clone(),
            role_spelling: role_spelling.into(),
            role_identity,
            subject_row,
        };
        self.candidate_graph.as_mut().ok_or_else(exhausted)?
            .retain_source_role_obligation(candidate)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(())
    }

    pub(super) fn candidate_annotation(
        &mut self,
        annotation: &SourceAnnotation,
        endpoint: shadow_apply::CandidateEndpoint,
        target: usize,
        occurrence: &HirOccurrenceId,
        level: u32,
        computation_effect: usize,
    ) -> Result<(), SolveAvailabilityError> {
        self.candidate_annotation_pair(annotation, endpoint,
            shadow_apply::CandidateEndpoint::Component(target), occurrence, level, computation_effect,
            &AnnotationScope::for_source(annotation.owner.clone()), [40, 41, 42])
    }

    pub(super) fn candidate_expression_ascription(
        &mut self, annotation: &SourceAnnotation, endpoint: shadow_apply::CandidateEndpoint,
        occurrence: &HirOccurrenceId, level: u32, computation_effect: usize, scope: &AnnotationScope,
    ) -> Result<(), SolveAvailabilityError> {
        // Ascriptions can share their HIR occurrence with a binding annotation.
        self.candidate_annotation_pair(annotation, endpoint, endpoint, occurrence, level, computation_effect, scope, [45, 46, 47])
    }

    fn candidate_annotation_pair(
        &mut self, annotation: &SourceAnnotation, endpoint: shadow_apply::CandidateEndpoint,
        target: shadow_apply::CandidateEndpoint, occurrence: &HirOccurrenceId,
        level: u32, computation_effect: usize, scope: &AnnotationScope, slots: [u8; 3],
    ) -> Result<(), SolveAvailabilityError> {
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
            self.candidate_negative_empty_bundle(annotation, occurrence,
                &SignatureContext::Annotation(annotation, scope.clone()), slots[1])?;
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            let upper = self.candidate_signature_value(
                &SignatureContext::Annotation(annotation, scope.clone()),
                &annotation.ty,
                Polarity::Negative,
                Polarity::Positive,
                level,
                &mut value_variables,
                &mut effect_variables,
                &mut views,
            )?;
            let exposed = self.candidate_signature_value(
                &SignatureContext::Annotation(annotation, scope.clone()),
                &annotation.ty,
                Polarity::Positive,
                Polarity::Positive,
                level,
                &mut value_variables,
                &mut effect_variables,
                &mut views,
            )?;
            let lower = self.candidate_endpoint(endpoint, Polarity::Positive)?;
            self.admit_candidate_value_link(occurrence, slots[0], lower, upper)?;
            self.candidate_annotation_computation_effect(
                &SignatureContext::Annotation(annotation, scope.clone()),
                annotation, computation_effect, occurrence, level, slots[2], &mut effect_variables, &mut views,
            )?;
            let target = self.candidate_endpoint(target, Polarity::Negative)?;
            self.admit_candidate_value_link(
                occurrence,
                slots[1],
                exposed,
                target,
            )
        })();
        drop((value_variables, effect_variables, views));
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= scratch;
        result
    }

    fn candidate_negative_empty_bundle(
        &mut self, annotation: &SourceAnnotation, occurrence: &HirOccurrenceId,
        context: &SignatureContext<'_>, slot: u8,
    ) -> Result<(), SolveAvailabilityError> {
        fn collect(ty: &SourceAnnotationType, variance: Polarity, annotation: &SourceAnnotation,
            scope: &AnnotationScope, sets: &mut Vec<candidate_context::EmptyAttachmentSet>) -> Result<(), SolveAvailabilityError> {
            if variance == Polarity::Negative {
                if let Some(row) = &ty.effects {
                    if row.concrete.is_empty() && row.variables.is_empty() {
                        sets.try_reserve(1).map_err(|_| exhausted())?;
                        sets.push(candidate_context::EmptyAttachmentSet {
                            owner: annotation.owner.clone(), position: row.position.clone(),
                            source: candidate_context::AttachmentSource { composed_polarity: variance, lexical_scope: scope.clone() },
                        });
                    }
                }
            }
            if let SourceAnnotationValue::Function { argument, result } = &ty.value {
                let opposite = if variance == Polarity::Positive { Polarity::Negative } else { Polarity::Positive };
                collect(argument, opposite, annotation, scope, sets)?;
                collect(result, variance, annotation, scope, sets)?;
            }
            Ok(())
        }
        let SignatureContext::Annotation(_, scope) = context else { return Ok(()); };
        let mut sets = Vec::new();
        collect(&annotation.ty, Polarity::Positive, annotation, scope, &mut sets)?;
        if !sets.is_empty() {
            self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.retain_bundle(
                candidate_context::AttachmentBundle { occurrence: ConstraintOccurrenceId::new(occurrence.clone(), slot), sets }, true)?;
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        }
        Ok(())
    }

    fn candidate_annotation_computation_effect<'a>(
        &mut self,
        context: &SignatureContext<'_>,
        annotation: &'a SourceAnnotation,
        computation_effect: usize,
        source: &HirOccurrenceId,
        level: u32,
        slot: u8,
        effects: &mut HashMap<Box<str>, u32>,
        views: &mut HashMap<SourceNodeKey, u32>,
    ) -> Result<(), SolveAvailabilityError> {
        // An explicit root row checks evaluation once; it never supplies a
        // positive support operand to the initializer or the local value scheme.
        let Some(row) = annotation.ty.effects.as_ref() else { return Ok(()); };
        let upper = if row.concrete.is_empty() && row.variables.len() == 1 {
            // A variable-only allowance is the scoped tail itself. Retain this
            // ordinary bound so a later lower remains reachable from exposed
            // Function support; an empty allowance wrapper would hide the edge.
            let SignatureContext::Annotation(_, scope) = context else { return Err(exhausted()); };
            let tail = self.candidate_formal_effect_variable(scope, &row.variables[0], level)?;
            self.live_effect_term(Polarity::Negative, tail)?
        } else {
            self.candidate_signature_effect(
                context, Some(row), None, Polarity::Negative, Polarity::Positive,
                level, effects, views,
            )?
        };
        let lower = self.batch.component_term_at(computation_effect);
        let id = ConstraintOccurrenceId::new(source.clone(), slot);
        let cause = CauseId::for_occurrence(id.clone());
        self.store.admit_and_record_provenance(&ConstraintOccurrence {
            id: id.clone(), cause: cause.clone(), lower, upper,
        }).map_err(SolveAvailabilityError::from)?;
        self.constrain_live_effect(
            self.effect_endpoint(lower, Polarity::Positive),
            self.effect_endpoint(upper, Polarity::Negative), &id, &cause,
        )?;
        Ok(())
    }

    fn candidate_signature_value<'a>(
        &mut self,
        context: &SignatureContext<'_>,
        ty: &'a SourceAnnotationType,
        polarity: Polarity,
        variance: Polarity,
        level: u32,
        values: &mut HashMap<Box<str>, u32>,
        effects: &mut HashMap<Box<str>, u32>,
        views: &mut HashMap<SourceNodeKey, u32>,
    ) -> Result<Term, SolveAvailabilityError> {
        match &ty.value {
            SourceAnnotationValue::Bool => Ok(self.batch.collected_leaf_term(if polarity == Polarity::Positive { Leaf::BoolPositive } else { Leaf::BoolNegative })),
            SourceAnnotationValue::Str => Ok(self.batch.collected_leaf_term(if polarity == Polarity::Positive { Leaf::StrPositive } else { Leaf::StrNegative })),
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
                let row = if let SignatureContext::Annotation(_, scope) = context {
                    self.candidate_annotation_variable(scope, name, level)?
                } else if let Some(&row) = values.get(name.as_ref()) {
                    row
                } else {
                    values.try_reserve(1).map_err(|_| exhausted())?;
                    let row = self.fresh_value_at_level(level)?;
                    values.insert(Box::<str>::from(name.as_ref()), row);
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
        variables: &mut HashMap<Box<str>, u32>,
        views: &mut HashMap<SourceNodeKey, u32>,
    ) -> Result<Term, SolveAvailabilityError> {
        let Some(row) = row else {
            if let Some(family) = family {
                let mut allowed = Vec::new();
                allowed.try_reserve_exact(1).map_err(|_| exhausted())?;
                allowed.push(family.clone());
                let view = self.candidate_signature_view(context.owner().clone(), context.position().clone(), allowed, None, context.operation(), None)?;
                let port = self.fresh_effect_at_level(level)?;
                self.candidate_insert_bound(ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(port)), polarity, ExtrusionEndpoint::Effect(EffectEndpointKey::Support(view)))?;
                return self.live_effect_term(polarity, port);
            }
            if matches!(context, SignatureContext::Operation { .. } | SignatureContext::Primitive { .. }) {
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
                    None,
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
            Some(if let SignatureContext::Annotation(_, scope) = context {
                self.candidate_formal_effect_variable(scope, name, level)?
            } else if let Some(&row) = variables.get(name.as_ref()) {
                row
            } else {
                variables.try_reserve(1).map_err(|_| exhausted())?;
                let row = self.fresh_effect_at_level(level)?;
                variables.insert(Box::<str>::from(name.as_ref()), row);
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
                match context {
                    SignatureContext::Annotation(_, scope) => Some(candidate_context::AttachmentSource {
                        composed_polarity: variance,
                        lexical_scope: scope.clone(),
                    }),
                    SignatureContext::Operation { .. } | SignatureContext::Primitive { .. } => None,
                },
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
    #[test]
    fn negative_concrete_formal_row_accepts_a_state_effect_callback() {
        let text = "act io:\n    our tick: int -> ()\nact state:\n    our tick: int -> ()\nmy bridge (callback: int -> [io] ()) = callback; my state_callback value = state::tick value; my answer = bridge state_callback";
        let source: std::sync::Arc<yu_syntax::SourceText> = std::sync::Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            std::sync::Arc::new(yu_syntax::scan_header(source)),
            std::sync::Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        assert!(parsed.structural_recoveries().is_empty(), "source must parse structurally");
        let hir = yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "negative-formal-effect-tail", "source.yu",
            ))),
            &parsed,
            yu_hir::SemanticImports::empty(),
        ).unwrap();
        let root = hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "bridge" => {
                Some(binding.definition_root().clone())
            }
            _ => None,
        }).unwrap();
        let answer_root = hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "answer" => {
                Some(binding.definition_root().clone())
            }
            _ => None,
        }).unwrap();
        let candidate = crate::shadow_apply::CandidateInference::solve(std::sync::Arc::new(hir)).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "negative [io] denotes [io, 'e], so [state] remains in the open tail: {:?}", candidate.candidate_conflicts());

        let graph = candidate.export(&root).unwrap();
        let permissions = graph.formal_effect_permissions().unwrap();
        assert!(permissions.iter().any(|permission|
            permission.permitted().len() == 1
                && permission.open_tail().row().is_some_and(|row|
                    row.kind() == ComponentKind::Effect)
        ), "the exported candidate scheme must keep the negative [io] permission joined to its open effect tail");

        let io = permissions.iter().find_map(|permission| permission.permitted().first())
            .expect("the source annotation retains the explicit io permission");
        let answer = candidate.export(&answer_root).unwrap();
        let contribution = answer.nodes().find_map(|node| match node.effect_operand()? {
            crate::shadow_apply::CandidateGraphEffectOperand::Contribution { effect, .. }
            | crate::shadow_apply::CandidateGraphEffectOperand::OperationInterfaceMember { effect, .. } => Some((node, effect)),
            crate::shadow_apply::CandidateGraphEffectOperand::SupportView { permitted, .. } =>
                permitted.iter().find(|effect| *effect != io).map(|effect| (node, effect)),
            _ => None,
        }).expect("the answer scheme retains the state effect label");
        assert_ne!(contribution.1, io, "the state label remains distinct from the io permission");
        assert!(answer.bounds().any(|bound|
            bound.kind() == ComponentKind::Effect
                && bound.lower().same_identity(contribution.0)
                && bound.upper().row().is_some_and(|row| row.kind() == ComponentKind::Effect)
        ), "the state contribution remains connected to an open effect residual row");
    }

    #[test]
    fn unsupported_pinned_primitive_is_not_admitted_as_an_effect_operation() {
        let text = "pub subtract = builtin_op::int_sub";
        let source: std::sync::Arc<yu_syntax::SourceText> = std::sync::Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            std::sync::Arc::new(yu_syntax::scan_header(source)),
            std::sync::Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        assert!(parsed.structural_recoveries().is_empty());
        let hir = yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "unsupported-pinned-primitive", "source.yu",
            ))),
            &parsed,
            yu_hir::SemanticImports::empty(),
        ).unwrap();
        let result = crate::shadow_apply::CandidateInference::solve(std::sync::Arc::new(hir));
        assert!(matches!(result, Err(crate::shadow_apply::CandidateError::Unsupported)));
    }

    #[test]
    fn capture_inverse_restores_occupied_without_allocation_and_inserts_absent() {
        let mut state = State::default();
        let saved = CaptureBucket { head: 0, tail: 1 };
        let changed = CaptureBucket { head: 2, tail: 3 };
        state.capture_incidence.reserve(28);
        let capacity = state.capture_incidence.capacity();
        for row in 0..capacity as u32 { state.capture_incidence.insert(row, changed); }
        let mut checkpoint = state.checkpoint();
        // Reverse a newly admitted row before replacing an occupied bucket,
        // matching the failure suffix in the actual Local observation.
        checkpoint.capture_incidence.push((0, Some(saved)));
        checkpoint.capture_incidence.push((1, None));
        state.capture_probe = Some(CaptureProbe { events: Vec::with_capacity(3), fail_at_full_new: false, failed: false });
        state.rollback(checkpoint);
        assert_eq!(state.capture_incidence.get(&0), Some(&saved));
        assert!(!state.capture_incidence.contains_key(&1));
        let occupied = &state.capture_probe.as_ref().unwrap().events[1];
        assert!(occupied.inverse && occupied.old_present);
        assert_eq!(occupied.before.0, occupied.after.0, "replacement keeps the occupied key");
        assert_eq!(occupied.allocation_requests, 0);

        let mut checkpoint = state.checkpoint();
        checkpoint.capture_incidence.push((1, Some(saved)));
        state.rollback(checkpoint);
        assert_eq!(state.capture_incidence.get(&1), Some(&saved));
        let absent = &state.capture_probe.as_ref().unwrap().events[2];
        assert!(absent.inverse && absent.old_present);
        assert_eq!(absent.after.0, absent.before.0 + 1, "an absent saved key still needs insertion");
    }
    #[test]
    #[ignore = "bounded actual Local capture rollback research observation"]
    fn retained_local_capture_inverse_observation() {
        use crate::candidate_source::{Action, CandidateRun, Schedule, Support};
        let tails = 28;
        let ports = (0..tails).flat_map(|index| [index, index])
            .map(|index| format!("(int -> [tick, 'e{index}] ())"))
            .collect::<Vec<_>>().join(" -> ");
        let text = format!("act tick:\n    our ping: () -> ()\nmy outer = {{ my bridge (consume:({ports} -> ())) = consume; bridge }}");
        let mut targets = 0;
        let mut allocating_sessions = 0;
        for fresh_session in 0..8 {
            let mut session = make_session(&text);
            let (root, position) = session.batch.candidate_source.schedules.iter()
                .find_map(|(root, actions)| actions.iter().rposition(|action| matches!(action, Action::Local { .. }))
                    .map(|position| (root.clone(), position))).unwrap();
            let schedule = Schedule::Root(session.batch.root_definition_positions[&root]);
            session.begin_candidate_source(schedule).unwrap();
            while session.candidate_graph.as_ref().unwrap().source.unwrap().next < position {
                assert_eq!(session.step_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(false));
            }
            let Action::Local { slot, .. } = session.batch.candidate_source.schedules[&root][position] else { unreachable!() };
            let graph = session.candidate_graph.as_ref().unwrap();
            assert!(graph.locals[slot].is_some(), "real schedule must install bridge before use");
            assert!(graph.local_use.is_empty(), "target starts a new actual Local route");
            let before_source = graph.source;
            let before_routes = graph.local_routes.len();
            let state = &graph.intrusion.effect_algebra;
            let before_map = state.capture_incidence.clone();
            let before_records = state.capture_records.clone();
            let before_keys = state.capture_incidence_keys.clone();
            let before_context = state.context.checkpoint();
            let before_size = (state.capture_incidence.len(), state.capture_incidence.capacity());
            session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.capture_probe =
                Some(CaptureProbe { events: Vec::with_capacity(tails * 16), fail_at_full_new: true, failed: false });
            let before_route = RouteCheckpoint::capture(&session);
            // The source owner dispatches Action::Local. Its production route
            // opens the transaction, captures/freshens once, and steps LocalUse.
            let result = session.step_candidate_source(Support::READY);
            let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            let probe = state.capture_probe.as_ref().unwrap();
            if probe.failed {
                assert_eq!(result, Err(exhausted()));
                before_route.assert_restored(&session);
                assert_eq!(state.capture_incidence, before_map);
                assert_eq!(state.capture_records, before_records);
                assert_eq!(state.capture_incidence_keys, before_keys);
                assert_eq!(state.context.checkpoint(), before_context);
                let graph = session.candidate_graph.as_ref().unwrap();
                assert_eq!(graph.source, before_source);
                assert_eq!(graph.local_routes.len(), before_routes);
                assert!(graph.local_use.is_empty());
            } else {
                assert_eq!(result, Ok(CandidateRun::Complete(false)), "unrelated failure invalidates the witness");
            }
            targets += usize::from(probe.failed);
            let admissions = probe.events.iter().filter(|event| !event.inverse).count();
            let retained_admissions = probe.events.iter().filter(|event| !event.inverse && event.local_frame).count();
            let requests: usize = probe.events.iter().filter(|event| event.inverse).map(|event| event.allocation_requests).sum();
            let occupied_inverses = probe.events.iter().filter(|event| event.inverse && event.old_present && event.before.0 == event.after.0).count();
            let occupied_requests: usize = probe.events.iter().filter(|event| event.inverse && event.old_present && event.before.0 == event.after.0).map(|event| event.allocation_requests).sum();
            assert_eq!(occupied_requests, 0, "occupied capture inverses restore in place");
            allocating_sessions += usize::from(requests > 0);
            eprintln!("retained_local_capture fresh={fresh_session} tails={tails} source_action={position} slot={slot} before={before_size:?} admissions={admissions} retained_admissions={retained_admissions} target={} inverse_allocation_requests={requests} occupied_inverses={occupied_inverses} occupied_allocation_requests={occupied_requests}", probe.failed);
            // Print only the suffix around the injected failure and allocating
            // inverses. The full event inventory is counted above.
            if let Some(last) = probe.events.iter().rposition(|event| !event.inverse) {
                for event in probe.events[last.saturating_sub(1)..].iter().take(4) {
                    eprintln!("retained_local_capture {} row={} old={} local_frame={} before={:?} after={:?} allocation_requests={}",
                        if event.inverse { "inverse" } else { "admit" }, event.row, event.old_present,
                        event.local_frame, event.before, event.after, event.allocation_requests);
                }
            }
            for event in probe.events.iter().filter(|event| event.allocation_requests > 0) {
                eprintln!("retained_local_capture allocating_inverse row={} before={:?} after={:?} requests={}", event.row, event.before, event.after, event.allocation_requests);
            }
        }
        eprintln!("retained_local_capture coverage sessions=8 tails=28 targets={targets} allocating_sessions={allocating_sessions} seeds=uncontrolled_RandomState");
    }
    #[test]
    #[ignore = "bounded native capture rollback research observation"]
    fn capture_map_native_admission_inverse_observation() {
        // Eight fresh RandomState sessions; no seed, key substitution or raw
        // table-layout assumption. This is a FormalAnnotation constructor
        // prefix, not a retained Local scheduling witness.
        let mut targets = 0;
        let mut allocating_sessions = 0;
        for tails in [28, 56] {
            let ports = (0..tails).flat_map(|index| [index, index])
                .map(|index| format!("(int -> [tick, 'e{index}] ())"))
                .collect::<Vec<_>>().join(" -> ");
            let text = format!("act tick:\n    our ping: () -> ()\nmy bridge (consume:({ports} -> ())) = consume");
            for fresh_session in 0..4 {
                let mut session = make_session(&text);
                let action = session.batch.candidate_source.schedules.values().next().unwrap().iter()
                    .find(|action| matches!(action, candidate_source::Action::FormalAnnotation { .. })).unwrap().clone();
                let candidate_source::Action::FormalAnnotation { annotation, parameter, occurrence, scope } = action else { unreachable!() };
                let state = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra;
                let before_map = state.capture_incidence.clone();
                let before_records = state.capture_records.clone();
                let before_keys = state.capture_incidence_keys.clone();
                state.capture_probe = Some(CaptureProbe { events: Vec::with_capacity(tails * 16), fail_at_full_new: true, failed: false });
                let mut constructed = false;
                let result = session.with_route_transaction(|session| {
                    session.candidate_formal_annotation(&annotation, parameter, &occurrence, &scope)?;
                    constructed = true;
                    // If the named target was not reached, rollback a complete
                    // native constructor and report that miss explicitly.
                    Err::<(), _>(exhausted())
                });
                assert_eq!(result, Err(exhausted()));
                let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
                assert_eq!(state.capture_incidence, before_map);
                assert_eq!(state.capture_records, before_records);
                assert_eq!(state.capture_incidence_keys, before_keys);
                let probe = state.capture_probe.as_ref().unwrap();
                assert!(constructed || probe.failed, "another failure invalidates this prefix");
                targets += usize::from(probe.failed);
                let requests: usize = probe.events.iter().filter(|event| event.inverse).map(|event| event.allocation_requests).sum();
                allocating_sessions += usize::from(requests > 0);
                eprintln!("capture_probe tails={tails} fresh={fresh_session} target={} constructed={constructed} inverse_allocation_requests={requests}", probe.failed);
                // Complete actual order, bounded to the target-sized prefix.
                for event in &probe.events {
                    eprintln!("capture_probe {} row={} old={} before={:?} after={:?} allocation_requests={}",
                        if event.inverse { "inverse" } else { "admit" }, event.row, event.old_present,
                        event.before, event.after, event.allocation_requests);
                }
            }
        }
        eprintln!("capture_probe coverage sessions=8 tail_counts=[28,56] targets={targets} allocating_sessions={allocating_sessions} seeds=uncontrolled_RandomState");
    }
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
    fn root_computation_annotation_allowance_never_creates_contributions() {
        for text in [
            "act E\nmy answer:[E] int = 1",
            "act E\nmy answer:[] int = { my local:[E] int = 1; my first = local; local }",
        ] {
            let mut session = make_session(text);
            let owner = root(&session, "answer");
            session.execute_candidate_source_root(&owner).unwrap();
            let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            assert!(state.contributions.is_empty(), "allowance is not an evaluation effect");
            assert!(state.conflicts.is_empty());
            assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
        }
    }

    #[test]
    fn root_computation_annotation_rolls_back_storage_and_retries() {
        for (text, direct_tail) in [
            ("act E\nmy answer:[E] int = 1", false),
            ("act E\nmy answer = { my local:[E] int = 1; local }", false),
            ("act E\nmy answer:[E, 'e] int = 1", false),
            ("act E\nmy answer = { my local:[E, 'e] int = 1; local }", false),
            ("my answer:['e] int = 1", true),
            ("my answer = { my local:['e] int = 1; local }", true),
        ] {
            let mut session = make_session(text);
            let owner = root(&session, "answer");
            let actions = session.batch.candidate_source.schedules[&owner].clone();
            let action = actions.iter().find(|action| matches!(action,
                candidate_source::Action::LocalAnnotation { .. } | candidate_source::Action::Annotation { .. })).unwrap();
            let apply = |session: &mut InferenceSession| match action {
                candidate_source::Action::LocalAnnotation { annotation, slot, endpoint, computation_effect, occurrence, level, boundary } =>
                    session.candidate_local_annotation(annotation, *slot, *endpoint, occurrence, *level, *boundary, *computation_effect),
                candidate_source::Action::Annotation { annotation, endpoint, computation_effect, target, occurrence, level } =>
                    session.candidate_annotation(annotation, *endpoint, *target, occurrence, *level, *computation_effect),
                _ => unreachable!(),
            };
            let before_views = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views.len();
            let before_tails = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_effects.clone();
            let before_incidence = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.capture_incidence.clone();
            let before_records = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.capture_records.clone();
            let before_keys = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.capture_incidence_keys.clone();
            let mut checkpoint = None;
            assert_eq!(session.with_route_transaction(|session| {
                checkpoint = Some(RouteCheckpoint::capture(session));
                apply(session)?;
                let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
                if direct_tail {
                    assert_eq!(state.views.len(), before_views, "variable-only root checks have no allowance wrapper");
                    assert_eq!(state.annotation_effects.len(), before_tails.len() + 1);
                } else {
                    assert!(state.views.len() > before_views);
                }
                assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
                Err::<(), _>(exhausted())
            }), Err(exhausted()));
            checkpoint.unwrap().assert_restored(&session);
            assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views.len(), before_views);
            assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_effects, before_tails);
            assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
            assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.capture_incidence, before_incidence);
            assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.capture_records, before_records);
            assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.capture_incidence_keys, before_keys);
            session.with_route_transaction(apply).unwrap();
            let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            if text.contains("E, 'e") {
                assert!(!state.capture_incidence.is_empty(), "mixed allowance retains its tail capture incidence after retry");
            }
            if direct_tail {
                assert_eq!(state.views.len(), before_views);
                assert_eq!(state.annotation_effects.len(), before_tails.len() + 1);
            } else {
                assert!(state.views.len() > before_views);
            }
        }
    }

    #[test]
    fn annotated_local_initializer_effect_has_one_block_edge_and_pure_lookups() {
        for annotation in ["int -> int", "'a"] {
            let session = make_session(&format!("act tick:\n    our next: () -> (int -> int)\n\nmy outer ignored = {{ my local:{annotation} = tick::next(); my first = local; local }}"));
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
    }

    #[test]
    fn local_annotation_first_edge_failure_rolls_back_and_retries() {
        for ty in ["int", "int -> int", "(int -> int) -> int", "int -> () -> int", "'a", "'a -> 'a", "('a -> int) -> 'a", "int -> ['a] int"] {
            let mut session = make_session(&format!("my outer x = {{ my local:{ty} = x; local }}"));
            let owner = root(&session, "outer");
            let actions = session.batch.candidate_source.schedules[&owner].clone();
            let candidate_source::Action::LocalAnnotation { annotation, slot, endpoint, computation_effect, occurrence, level, boundary } = actions.iter().find(|action| matches!(action, candidate_source::Action::LocalAnnotation { .. })).unwrap() else { unreachable!() };
            let names = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_values.clone();
            let effect_names = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_effects.clone();
            let mut checkpoint = None;
            FORMAL_ANNOTATION_FAIL_STAGE.with(|stage| stage.set(4));
            assert_eq!(session.with_route_transaction(|session| {
                checkpoint = Some(RouteCheckpoint::capture(session));
                session.candidate_local_annotation(annotation, *slot, *endpoint, occurrence, *level, *boundary, *computation_effect)
            }), Err(exhausted()));
            checkpoint.unwrap().assert_restored(&session);
            assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_values, names);
            assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_effects, effect_names);
            assert!(session.candidate_graph.as_ref().unwrap().locals[*slot].is_none());
            let mut checkpoint = None;
            assert_eq!(session.with_route_transaction(|session| {
                checkpoint = Some(RouteCheckpoint::capture(session));
                session.candidate_local_annotation(annotation, *slot, *endpoint, occurrence, *level, *boundary, *computation_effect)?;
                if matches!(ty, "'a" | "'a -> 'a" | "('a -> int) -> 'a") {
                    assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_values.len(), names.len() + 1);
                }
                if ty.contains("['a") {
                    assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_effects.len(), effect_names.len() + 1);
                }
                Err::<(), _>(exhausted())
            }), Err(exhausted()));
            checkpoint.unwrap().assert_restored(&session);
            assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_values, names);
            assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_effects, effect_names);
            assert!(session.candidate_graph.as_ref().unwrap().locals[*slot].is_none());
            session.with_route_transaction(|session| session.candidate_local_annotation(annotation, *slot, *endpoint, occurrence, *level, *boundary, *computation_effect)).unwrap();
            assert!(session.candidate_graph.as_ref().unwrap().locals[*slot].is_some());
        }
    }

    #[test]
    fn whole_local_named_scope_shares_formals_and_isolates_other_bindings() {
        let mut session = make_session("my outer = { my first (x:'a):'a -> 'a = x; my second (x:'a):'a -> 'a = x; second }");
        let owner = root(&session, "outer");
        let actions = session.batch.candidate_source.schedules[&owner].clone();
        let mut rows = Vec::new();
        for action in &actions {
            match action {
                candidate_source::Action::FormalAnnotation { annotation, parameter, occurrence, scope } => {
                    session.with_route_transaction(|session| session.candidate_formal_annotation(annotation, *parameter, occurrence, scope)).unwrap();
                }
                candidate_source::Action::LocalAnnotation { annotation, slot, endpoint, computation_effect, occurrence, level, boundary } => {
                    let scope = AnnotationScope::Local(session.batch.candidate_source.locals[*slot].clone());
                    let key = (scope, Box::<str>::from("'a"));
                    let before = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_values[&key];
                    session.with_route_transaction(|session| session.candidate_local_annotation(annotation, *slot, *endpoint, occurrence, *level, *boundary, *computation_effect)).unwrap();
                    let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
                    assert_eq!(state.annotation_values[&key], before, "whole-local pair reuses its formal's named row");
                    rows.push(before);
                }
                _ => {}
            }
        }
        assert_eq!(rows.len(), 2);
        assert_ne!(rows[0], rows[1], "actual local identities isolate equal names");
        assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.annotation_values.len(), 2);
    }

    #[test]
    fn local_scheme_publication_rollback_preserves_prior_slots_and_retries() {
        let mut session = make_session("my outer x = { my first:int = x; my second:int = x; second }");
        let owner = root(&session, "outer");
        let actions = session.batch.candidate_source.schedules[&owner].clone();
        let annotations: Vec<_> = actions.iter().filter_map(|action| match action {
            candidate_source::Action::LocalAnnotation { annotation, slot, endpoint, computation_effect, occurrence, level, boundary } =>
                Some((annotation, *slot, *endpoint, occurrence, *level, *boundary, *computation_effect)),
            _ => None,
        }).collect();
        let (first, second) = (&annotations[0], &annotations[1]);
        session.candidate_local_annotation(first.0, first.1, first.2, first.3, first.4, first.5, first.6).unwrap();
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
    fn original_choose_operation_rendering_reaches_native_frontier() {
        // New research rendering only: these bytes are not recovered historical
        // source/CST/HIR. Keep the negative [ctrl] row on the inner argument.
        let rendering = "act ctrl:\n    our choose: () -> (([ctrl] ()) -> [ctrl] int)\n\nmy f0 = ctrl::choose ()";
        let source: Arc<yu_syntax::SourceText> = Arc::from(rendering);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        assert!(parsed.structural_recoveries().is_empty(), "research rendering parser recoveries: {:?}", parsed.structural_recoveries());
        let hir = Arc::new(
            yu_hir::shadow::lower_module_with_local_source(
                yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                    "effect-kernel",
                    "original-choose-research-rendering.yu",
                ))),
                &parsed,
                yu_hir::SemanticImports::empty(),
            )
            .expect("research rendering should lower before the candidate owner path is observed"),
        );
        let declaration = hir.source_effect_declarations().iter()
            .find(|family| family.spelling.as_ref() == "ctrl")
            .and_then(|family| family.operations.iter().find(|operation| operation.spelling.as_ref() == "choose"))
            .expect("parsed source should contain the actual ctrl::choose declaration");
        let f0 = hir.items().iter().find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "f0" => Some(binding.definition_root().clone()),
            _ => None,
        }).expect("research source root f0");
        let local_source = hir.local_source(&f0).unwrap().unwrap();
        let operation_expression = local_source.expressions().iter().find(|expression| matches!(
            &expression.form,
            yu_hir::shadow::LocalSourceForm::Operation {
                resolution: yu_hir::shadow::SourceOperationResolution::Resolved(resolved)
            } if std::ptr::eq(resolved.as_ref(), declaration.as_ref())
        )).expect("actual parsed use should resolve to this SourceOperationDeclaration");
        let operation_occurrence = operation_expression.occurrence.clone();
        eprintln!(
            "research_rendering={rendering:?} declaration={:?} source_occurrence={:?} name_position={:?} signature_position={:?}",
            declaration.id, operation_occurrence, declaration.name_position, declaration.signature_position,
        );

        let batch = ConstraintBatch::collect_candidate_mode(Arc::clone(&hir), true, true).unwrap();
        let mut trace_session = InferenceSession::try_new(batch.clone()).unwrap();
        trace_session.start_candidate_graph().unwrap();
        let actions = trace_session.batch.candidate_source.schedules[&f0].clone();
        let operation_indices = actions.iter().enumerate().filter_map(|(index, action)| match action {
            candidate_source::Action::Operation { declaration: scheduled, occurrence, .. }
                if std::ptr::eq(scheduled.as_ref(), declaration.as_ref()) && occurrence == &operation_occurrence => Some(index),
            _ => None,
        }).collect::<Vec<_>>();
        assert_eq!(operation_indices.len(), 1, "schedule must contain exactly this parsed Operation action");
        let operation_index = operation_indices[0];
        let root_position = trace_session.batch.root_definition_positions[&f0];
        trace_session.begin_candidate_source(candidate_source::Schedule::Root(root_position)).unwrap();
        let mut source_steps = 0usize;
        loop {
            let frame = trace_session.candidate_graph.as_ref().unwrap().source.unwrap();
            if frame.next == operation_index { break; }
            assert!(frame.next < operation_index, "the source schedule cannot skip the target operation");
            source_steps += 1;
            assert!(source_steps <= actions.len() * 2 + 1, "prior source actions must make bounded progress");
            assert_eq!(
                trace_session.step_candidate_source(candidate_source::Support::READY).unwrap(),
                candidate_source::CandidateRun::Complete(false),
                "every action before the operation must complete before the refusal frontier",
            );
        }
        let frame = trace_session.candidate_graph.as_ref().unwrap().source.unwrap();
        assert_eq!(frame.next, operation_index);
        assert_eq!(frame.schedule, candidate_source::Schedule::Root(root_position));
        let candidate_source::Action::Operation { declaration: scheduled, occurrence, .. } = &actions[operation_index] else {
            panic!("recorded frontier index must name the parsed Operation action");
        };
        assert!(std::ptr::eq(scheduled.as_ref(), declaration.as_ref()));
        assert_eq!(occurrence, &operation_occurrence);
        let expected_slot = ConstraintOccurrenceId::new(operation_occurrence.clone(), 42);
        let trace_graph = trace_session.candidate_graph.as_ref().unwrap();
        let trace_views = trace_graph.intrusion.effect_algebra.views.len();
        let trace_contributions = trace_graph.intrusion.effect_algebra.contributions.len();
        let trace_conflicts = trace_graph.intrusion.effect_algebra.conflicts.len();
        let trace_effect_bounds = trace_session.effect_bounds.len();
        let trace_scratch = trace_graph.scratch_bytes;
        let trace_facts = trace_session.store.facts().len();
        let trace_terms = trace_session.store.terms.capacity_snapshot();
        let action_result = trace_session.step_candidate_source(candidate_source::Support::READY);
        eprintln!("observed_frontier=Action::Operation declaration={:?} occurrence={:?} result={action_result:?} slot42={expected_slot:?}", declaration.id, operation_occurrence);
        assert_eq!(action_result, Err(SolveAvailabilityError::IdentityExhausted));
        let trace_graph = trace_session.candidate_graph.as_ref().unwrap();
        assert_eq!(trace_graph.source.unwrap().next, operation_index, "failed action does not advance the schedule");
        assert_eq!(trace_graph.intrusion.effect_algebra.views.len(), trace_views);
        assert_eq!(trace_graph.intrusion.effect_algebra.contributions.len(), trace_contributions);
        assert_eq!(trace_graph.intrusion.effect_algebra.conflicts.len(), trace_conflicts);
        assert_eq!(trace_session.effect_bounds.len(), trace_effect_bounds);
        assert_eq!(trace_graph.scratch_bytes, trace_scratch);
        assert_eq!(trace_session.store.facts().len(), trace_facts);
        assert_eq!(trace_session.store.terms.capacity_snapshot(), trace_terms);

        // Separately observe the real synchronous root owner's rollback in a
        // fresh session, so the action trace above does not fake cleanup.
        let mut rollback_session = InferenceSession::try_new(batch).unwrap();
        rollback_session.start_candidate_graph().unwrap();
        let rollback_graph = rollback_session.candidate_graph.as_ref().unwrap();
        let before_views = rollback_graph.intrusion.effect_algebra.views.len();
        let before_contributions = rollback_graph.intrusion.effect_algebra.contributions.len();
        let before_conflicts = rollback_graph.intrusion.effect_algebra.conflicts.len();
        let before_bounds = rollback_session.effect_bounds.len();
        let before_scratch = rollback_graph.scratch_bytes;
        let before_facts = rollback_session.store.facts().len();
        let before_terms = rollback_session.store.terms.capacity_snapshot();
        let root_result = rollback_session.execute_candidate_source_root(&f0);
        eprintln!("candidate_source_root_result={root_result:?} slot42={expected_slot:?}");
        assert_eq!(root_result, Err(SolveAvailabilityError::IdentityExhausted));
        let graph = rollback_session.candidate_graph.as_ref().unwrap();
        let state = &graph.intrusion.effect_algebra;
        let slot42_published = rollback_session.store.provenance().iter().any(|edge| edge.cause().occurrence() == &expected_slot);
        eprintln!(
            "root_rollback source_frame={:?} views={} (initial {}, expected prefix {}) contributions={} (initial {}, expected prefix {}) conflicts={} (initial {}, expected prefix {}) effect_bounds={} (initial {}, expected prefix {}) scratch={} (initial {}, expected prefix {}) facts={} (initial {}, expected prefix {}) term_capacity_matches_initial={} term_capacity_matches_prefix={} slot42_published={slot42_published}",
            graph.source, state.views.len(), before_views, trace_views,
            state.contributions.len(), before_contributions, trace_contributions,
            state.conflicts.len(), before_conflicts, trace_conflicts,
            rollback_session.effect_bounds.len(), before_bounds, trace_effect_bounds,
            graph.scratch_bytes, before_scratch, trace_scratch,
            rollback_session.store.facts().len(), before_facts, trace_facts,
            rollback_session.store.terms.capacity_snapshot() == before_terms,
            rollback_session.store.terms.capacity_snapshot() == trace_terms,
        );
        assert!(graph.source.is_none(), "failed candidate source root must clear its partial frame");
        assert_eq!(state.views.len(), trace_views, "root failure must retain only the successfully executed prefix state");
        assert_eq!(state.contributions.len(), trace_contributions);
        assert_eq!(state.conflicts.len(), trace_conflicts);
        assert_eq!(rollback_session.effect_bounds.len(), trace_effect_bounds);
        assert_eq!(graph.scratch_bytes, trace_scratch);
        assert_eq!(rollback_session.store.facts().len(), trace_facts, "successful prefix facts are retained; the failed Operation contributes none");
        assert_eq!(rollback_session.store.terms.capacity_snapshot(), trace_terms);
        assert!(!slot42_published, "slot 42 is admitted only after full signature construction");
    }
    fn assert_formal_capture_incidence(
        session: &InferenceSession, views: std::ops::Range<u32>, tail: u32,
    ) -> HashSet<(u32, u32)> {
        let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        // Exact upper endpoints retain negative EffectRow(source) <: Allowance(view) bounds.
        let affected_views = &views;
        let expected: HashSet<_> = session.effect_bounds.iter().enumerate().flat_map(|(source, bounds)| {
            bounds.exact_non_variable_uppers.iter().filter_map(move |endpoint| match *endpoint {
                EffectEndpointKey::Allowance(view) if affected_views.contains(&view) => Some((source as u32, view)),
                _ => None,
            })
        }).collect();
        let records: Vec<_> = state.capture_records.iter().filter(|record| views.contains(&record.view))
            .map(|record| (record.source, record.view)).collect();
        let retained: HashSet<_> = records.iter().copied().collect();
        assert_eq!(records.len(), retained.len(), "incidence deduplicates source/view pairs");
        assert_eq!(retained, expected, "incidence has exactly the negative Allowance-bound provenance");
        let mut next = Some(state.capture_incidence[&tail].head);
        let mut visited = HashSet::new();
        let mut bucket_pairs = HashSet::new();
        while let Some(index) = next {
            assert!(visited.insert(index), "capture bucket remains acyclic");
            let record = state.capture_records[index];
            if views.contains(&record.view) {
                assert!(bucket_pairs.insert((record.source, record.view)), "each expected pair occurs once in its tail bucket");
            }
            next = record.next;
        }
        assert_eq!(bucket_pairs, expected, "tail bucket reaches every expected incidence");
        expected
    }

    #[test]
    fn covariant_formal_view_is_paired_and_rolls_back_at_publication_hooks() {
        let text = "act io\nmy bridge (consume:(int -> [io, 'e] ()) -> ()) = consume";
        for failure in 0..5 {
            let mut session = make_session(text);
            let action = session.batch.candidate_source.schedules.values().next().unwrap().iter()
                .find(|action| matches!(action, candidate_source::Action::FormalAnnotation { .. })).unwrap().clone();
            let candidate_source::Action::FormalAnnotation { annotation, parameter, occurrence, scope } = action else { unreachable!() };
            let before_incidence = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.capture_incidence.clone();
            let before_records = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.capture_records.clone();
            let before_keys = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.capture_incidence_keys.clone();
            let old_views = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views.len();
            let old_values = session.bounds.len();
            let old_effects = session.effect_bounds.len();
            let mut checkpoint = None;
            if failure == 1 || failure == 2 { FORMAL_ANNOTATION_FAIL_STAGE.with(|hook| hook.set(failure)); }
            if failure == 3 { FORMAL_ANNOTATION_FAIL_AFTER_FIRST_EDGE.with(|hook| hook.set(true)); }
            if failure == 4 { session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.fail_after_view = true; }
            let result = session.with_route_transaction(|session| {
                checkpoint = Some(RouteCheckpoint::capture(session));
                session.candidate_formal_annotation(&annotation, parameter, &occurrence, &scope)
            });
            let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            if failure == 0 {
                result.unwrap();
                assert_eq!(state.views.len(), old_views + 1, "one paired view per explicit row occurrence");
                let view = old_views as u32;
                assert!(state.views[old_views].tail.is_some());
                assert_eq!(state.annotation_effects.len(), 1);
                assert!(session.effect_bounds.iter().any(|bounds| bounds.exact_non_variable_lowers.contains(&EffectEndpointKey::Support(view))));
                assert!(session.effect_bounds.iter().any(|bounds| bounds.exact_non_variable_uppers.contains(&EffectEndpointKey::Allowance(view))));
            } else {
                assert_eq!(result, Err(exhausted()));
                checkpoint.unwrap().assert_restored(&session);
                assert_eq!(state.views.len(), old_views);
                assert!(state.annotation_effects.is_empty());
                assert!(state.formal_domains.is_empty());
                assert_eq!(session.bounds.len(), old_values);
                assert_eq!(session.effect_bounds.len(), old_effects);
                assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
                assert_eq!(state.capture_incidence, before_incidence);
                assert_eq!(state.capture_records, before_records);
                assert_eq!(state.capture_incidence_keys, before_keys);
                session.with_route_transaction(|session| session.candidate_formal_annotation(&annotation, parameter, &occurrence, &scope)).unwrap();
                let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
                assert_eq!(state.views.len(), old_views + 1);
                assert_eq!(state.annotation_effects.len(), 1);
                assert_eq!(state.capture_records.len(), before_records.len() + 2);
                let view = old_views as u32;
                assert!(session.effect_bounds.iter().any(|bounds| bounds.exact_non_variable_lowers.contains(&EffectEndpointKey::Support(view))));
                assert!(session.effect_bounds.iter().any(|bounds| bounds.exact_non_variable_uppers.contains(&EffectEndpointKey::Allowance(view))));
            }
            let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            let view = old_views as u32;
            let incidence = assert_formal_capture_incidence(&session, view..view + 1, state.views[old_views].tail.unwrap());
            assert_eq!(incidence.len(), 2, "checking and exposed ports each retain the paired Allowance");
            assert!(incidence.iter().any(|&(source, owner)| owner == view
                && session.effect_bounds[source as usize].exact_non_variable_lowers.contains(&EffectEndpointKey::Support(view))));
            assert!(state.contributions.is_empty());
        }
    }

    #[test]
    fn negative_concrete_formal_permission_recovers_its_shared_port_and_rolls_back() {
        // Internal-producer regression only: the direct method call below bypasses
        // source preflight and does not establish source acceptance.
        // The same declared family occurs at distinct negative source paths:
        // AA reverses twice, while RR preserves variance throughout.
        let text = "act io\nmy bridge (consume: ((int -> [io] ()) -> ()) -> (() -> (int -> [io] ()))) = consume";
        let mut session = make_session(text);
        let action = session.batch.candidate_source.schedules.values().next().unwrap().iter()
            .find(|action| matches!(action, candidate_source::Action::FormalAnnotation { .. })).unwrap().clone();
        let candidate_source::Action::FormalAnnotation { annotation, parameter, occurrence, scope } = action else { unreachable!() };

        let SourceAnnotationValue::Function { argument: outer_argument, result: outer_result } = &annotation.ty.value else { panic!("outer Function"); };
        let SourceAnnotationValue::Function { argument: aa_function, .. } = &outer_argument.value else { panic!("AA Function"); };
        let SourceAnnotationValue::Function { result: aa_effect_node, .. } = &aa_function.value else { panic!("AAR Function"); };
        let aa_row = aa_effect_node.effects.as_ref().expect("AAR effect row");
        let SourceAnnotationValue::Function { result: rr_function, .. } = &outer_result.value else { panic!("RR Function"); };
        let SourceAnnotationValue::Function { result: rr_effect_node, .. } = &rr_function.value else { panic!("RRR Function"); };
        let rr_row = rr_effect_node.effects.as_ref().expect("RRR effect row");

        session.with_route_transaction(|session| {
            session.candidate_formal_annotation(&annotation, parameter, &occurrence, &scope)
        }).unwrap();

        let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        assert_eq!(state.formal_permissions.len(), 2);
        let paths: Vec<_> = state.formal_permissions.iter().map(|permission| permission.path.clone()).collect();
        assert_eq!(paths, vec![
            vec![FormalPortStep::Argument, FormalPortStep::Argument, FormalPortStep::Result],
            vec![FormalPortStep::Result, FormalPortStep::Result, FormalPortStep::Result],
        ], "parsed Function effects are attached to each result child: {paths:?}");
        for permission in &state.formal_permissions {
            assert_eq!(permission.parameter, parameter);
            assert_eq!(permission.occurrence, occurrence);
            assert_eq!(permission.source_owner, annotation.owner);
            assert_eq!(permission.scope, scope);
        }
        assert_ne!(state.formal_permissions[0].source_row, state.formal_permissions[1].source_row);
        assert_eq!(state.formal_permissions[0].concrete, state.formal_permissions[1].concrete,
            "equal families must not merge distinct paths");
        for (permission, row) in state.formal_permissions.iter().zip([aa_row, rr_row]) {
            assert_eq!(permission.source_row, row.position);
            assert_eq!(permission.concrete, row.concrete);
        }

        let negative_root = state.formal_domains[&parameter];
        let facts = session.store.facts();
        let positive_root = facts[facts.len() - 2].lower(); // ordinary link 43
        assert_eq!(facts[facts.len() - 1].upper(), negative_root); // ordinary link 44

        fn effect_at_path(session: &InferenceSession, mut value: Term, path: &[FormalPortStep]) -> crate::LiveVariableView {
            let mut effect = None;
            for (index, step) in path.iter().enumerate() {
                let (argument, argument_effect, result_effect, result) = match session.store.term_view(value).unwrap() {
                    TermView::PositiveFunction { argument, argument_effect, result_effect, result }
                    | TermView::NegativeFunction { argument, argument_effect, result_effect, result } =>
                        (argument, argument_effect, result_effect, result),
                    other => panic!("path crosses non-Function term: {other:?}"),
                };
                for child in [argument, argument_effect, result_effect, result] {
                    session.store.term_view(child).expect("all four Function children remain retained");
                }
                let (child, child_effect) = match step {
                    FormalPortStep::Argument => (argument, argument_effect),
                    FormalPortStep::Result => (result, result_effect),
                };
                effect = Some(child_effect);
                if index + 1 != path.len() { value = child; }
            }
            let TermView::LiveVariable(view) = session.store.term_view(effect.expect("nonempty permission path")).unwrap()
                else { panic!("permission effect is a live projection"); };
            assert_eq!(view.kind(), ComponentKind::Effect);
            view
        }

        let mut recovered_ordinals = Vec::with_capacity(state.formal_permissions.len());
        for permission in &state.formal_permissions {
            let negative = effect_at_path(&session, negative_root, &permission.path);
            let positive = effect_at_path(&session, positive_root, &permission.path);
            assert_eq!(negative.polarity(), Polarity::Negative);
            assert_eq!(positive.polarity(), Polarity::Positive);
            assert_eq!(negative.ordinal(), positive.ordinal(), "both terms project the one constructor row");
            recovered_ordinals.push(negative.ordinal());
        }
        assert_ne!(recovered_ordinals[0], recovered_ordinals[1],
            "equal source families at distinct paths keep distinct fresh rows");

        let before_duplicate = {
            let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            (
                state.formal_permissions.iter().map(|permission| (
                    permission.parameter, permission.occurrence.clone(), permission.source_owner.clone(),
                    permission.scope.clone(), permission.path.clone(), permission.source_row.clone(), permission.concrete.clone(),
                )).collect::<Vec<_>>(),
                state.formal_domains.clone(),
                state.formal_permission_bytes,
                session.store.facts().len(),
                session.store.provenance().len(),
            )
        };
        assert_eq!(session.with_route_transaction(|session| {
            session.candidate_formal_annotation(&annotation, parameter, &occurrence, &scope)
        }), Err(exhausted()));
        let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        let after_duplicate = (
            state.formal_permissions.iter().map(|permission| (
                permission.parameter, permission.occurrence.clone(), permission.source_owner.clone(),
                permission.scope.clone(), permission.path.clone(), permission.source_row.clone(), permission.concrete.clone(),
            )).collect::<Vec<_>>(),
            state.formal_domains.clone(),
            state.formal_permission_bytes,
            session.store.facts().len(),
            session.store.provenance().len(),
        );
        assert_eq!(after_duplicate, before_duplicate,
            "duplicate parameter refusal preserves descriptors, roots, links and accounted bytes");

        // A failure after slot 43 occurs before descriptor publication; a
        // post-publication failure exercises descriptor/root byte rollback.
        for after_publication in [false, true] {
            let mut failing = make_session(text);
            let action = failing.batch.candidate_source.schedules.values().next().unwrap().iter()
                .find(|action| matches!(action, candidate_source::Action::FormalAnnotation { .. })).unwrap().clone();
            let candidate_source::Action::FormalAnnotation { annotation, parameter, occurrence, scope } = action else { unreachable!() };
            let mut checkpoint = None;
            if after_publication {
                FORMAL_ANNOTATION_FAIL_STAGE.with(|hook| hook.set(2));
            } else {
                FORMAL_ANNOTATION_FAIL_AFTER_FIRST_EDGE.with(|hook| hook.set(true));
            }
            assert_eq!(failing.with_route_transaction(|session| {
                checkpoint = Some(RouteCheckpoint::capture(session));
                session.candidate_formal_annotation(&annotation, parameter, &occurrence, &scope)
            }), Err(exhausted()));
            checkpoint.unwrap().assert_restored(&failing);
            let state = &failing.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            assert!(state.formal_permissions.is_empty());
            assert_eq!(state.formal_permission_bytes, 0);
            assert!(state.formal_domains.is_empty());
            assert_eq!(failing.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
        }
    }

    #[test]
    fn distinct_covariant_formal_positions_share_only_the_scoped_tail_and_freshen_independently() {
        let mut session = make_session("act io\nact other\nmy bridge (consume:(int -> [io, 'e] ()) -> (int -> [other, 'e] ()) -> ()) = consume");
        let action = session.batch.candidate_source.schedules.values().next().unwrap().iter()
            .find(|action| matches!(action, candidate_source::Action::FormalAnnotation { .. })).unwrap().clone();
        let candidate_source::Action::FormalAnnotation { annotation, parameter, occurrence, scope } = action else { unreachable!() };
        let parameter_row = session.parameter_live_base + parameter as u32;
        session.value_levels[parameter_row as usize] = 2;
        session.with_route_transaction(|session| session.candidate_formal_annotation(&annotation, parameter, &occurrence, &scope)).unwrap();
        let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        assert_eq!(state.views.len(), 2, "one paired view for each explicit row position");
        assert_ne!(state.views[0].position, state.views[1].position);
        assert_eq!(state.annotation_effects.len(), 1);
        let tail = state.views[0].tail.unwrap();
        assert_eq!(state.views[1].tail, Some(tail));
        assert_ne!(state.views[0].allowed, state.views[1].allowed);
        assert_eq!(state.capture_records.len(), 4);
        let original_incidence = assert_formal_capture_incidence(&session, 0..2, tail);
        for view in 0..2 {
            assert_eq!(original_incidence.iter().filter(|&&(_, owner)| owner == view).count(), 2);
            assert!(original_incidence.iter().any(|&(source, owner)| owner == view
                && session.effect_bounds[source as usize].exact_non_variable_lowers.contains(&EffectEndpointKey::Support(view))));
            assert!(session.effect_bounds.iter().any(|bounds| bounds.exact_non_variable_lowers.contains(&EffectEndpointKey::Support(view))));
            assert!(session.effect_bounds.iter().any(|bounds| bounds.exact_non_variable_uppers.contains(&EffectEndpointKey::Allowance(view))));
        }
        assert!(state.contributions.is_empty());
        let graph = session.capture_candidate_graph(parameter_row, 1).unwrap();
        let tail_index = graph.rows.iter().position(|row| row.key == RowKey::Effect(tail)).unwrap();
        let (fresh_occurrence, fresh_cause) = cause(&session, "bridge", 40);
        let entry_scratch = session.candidate_graph.as_ref().unwrap().scratch_bytes;
        let mut fresh_tails = Vec::new();
        for _ in 0..2 {
            let before = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views.len();
            let (_, rows) = session.freshen_candidate_graph(&graph, 1, &fresh_occurrence, &fresh_cause).unwrap();
            session.candidate_graph.as_mut().unwrap().scratch_bytes = entry_scratch;
            let RowKey::Effect(mapped_tail) = rows[tail_index] else { unreachable!() };
            assert_ne!(mapped_tail, tail);
            let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            assert_eq!(state.views.len(), before + 2);
            assert!(state.views[before..].iter().all(|view| view.tail == Some(mapped_tail)));
            assert_ne!(state.views[before].position, state.views[before + 1].position);
            let fresh_incidence = assert_formal_capture_incidence(&session, before as u32..(before + 2) as u32, mapped_tail);
            for &(source, original_view) in &original_incidence {
                let source_index = graph.rows.iter().position(|row| row.key == RowKey::Effect(source)).unwrap();
                let RowKey::Effect(mapped_source) = rows[source_index] else { unreachable!() };
                let original = &state.views[original_view as usize];
                let fresh_view = (before..before + 2).find(|&index| {
                    let fresh = &state.views[index];
                    fresh.owner == original.owner && fresh.position == original.position && fresh.allowed == original.allowed
                }).unwrap() as u32;
                assert!(fresh_incidence.contains(&(mapped_source, fresh_view)), "mapped source retains its mapped Allowance owner");
            }
            for view in before as u32..(before + 2) as u32 {
                assert!(fresh_incidence.iter().any(|&(_, owner)| owner == view));
                assert!(session.effect_bounds.iter().any(|bounds| bounds.exact_non_variable_lowers.contains(&EffectEndpointKey::Support(view))));
                assert!(session.effect_bounds.iter().any(|bounds| bounds.exact_non_variable_uppers.contains(&EffectEndpointKey::Allowance(view))));
            }
            fresh_tails.push(mapped_tail);
        }
        assert_ne!(fresh_tails[0], fresh_tails[1], "independent formal uses must not share mapped tails");
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
        let candidate_source::Action::Annotation { annotation, endpoint, computation_effect, target, occurrence, level } = actions.iter().find(|action| matches!(action, candidate_source::Action::Annotation { .. })).unwrap() else { unreachable!() };
        let mut checkpoint = None;
        assert_eq!(session.with_route_transaction(|session| {
            checkpoint = Some(RouteCheckpoint::capture(session));
            session.candidate_annotation(annotation, *endpoint, *target, occurrence, *level, *computation_effect)?;
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
            .position(|view| view.owner.definition_root() == Some(&owner))
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
    fn positive_extrusion_retains_mixed_allowance_before_capture_and_late_lower() {
        for listed in [true, false] {
            let mut session = make_session("act E\nact F\nmy left x = x");
            let owner = root(&session, "left");
            let declaration = session.batch.hir.source_effect_declarations().iter()
                .find(|declaration| declaration.spelling.as_ref() == "E").unwrap().id.clone();
            let tail = session.fresh_effect_at_level(2).unwrap();
            let checking = session.fresh_effect_at_level(2).unwrap();
            let annotation = session.candidate_effect_view(owner, declaration.declaration.clone(), vec![declaration], Some(tail)).unwrap();
            session.candidate_insert_bound(ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(checking)),
                Polarity::Negative, ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(annotation))).unwrap();
            let effect = session.live_effect_term(Polarity::Positive, tail).unwrap();
            let function = session.positive_function_term(
                session.batch.collected_leaf_term(Leaf::IntNegative),
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative), effect,
                session.batch.collected_leaf_term(Leaf::IntPositive)).unwrap();
            let ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(copied_function)) = session.candidate_extrude(
                ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(function)), Polarity::Positive, 1).unwrap() else { panic!("positive Function copy"); };
            let (_, _, effect, _) = InferenceSession::positive_function_children(&session.store,
                ValueEndpointKey::PositiveFunction(copied_function)).unwrap();
            let EffectEndpointKey::EffectRow(copied_tail) = session.effect_endpoint(effect, Polarity::Positive) else { panic!("copied tail"); };
            assert_ne!(copied_tail, tail);
            let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            let incidence = state.capture_records[state.capture_incidence[&copied_tail].head];
            assert_ne!(incidence.source, checking);
            assert_eq!(state.views[incidence.view as usize].tail, Some(copied_tail));
            let value = session.fresh_value_at_level(1).unwrap();
            session.candidate_insert_bound(ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(value)),
                Polarity::Positive, ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(copied_function))).unwrap();
            let graph = session.capture_candidate_graph(value, 0).unwrap();
            let source_index = graph.rows.iter().position(|row| row.key == RowKey::Effect(incidence.source)).unwrap();
            let tail_index = graph.rows.iter().position(|row| row.key == RowKey::Effect(copied_tail)).unwrap();
            let (occurrence, origin) = cause(&session, "left", 60);
            let (_, rows) = session.freshen_candidate_graph(&graph, 1, &occurrence, &origin).unwrap();
            let (RowKey::Effect(fresh_source), RowKey::Effect(fresh_tail)) = (rows[source_index], rows[tail_index]) else { panic!("fresh effect rows"); };
            solve_effect(&mut session, EffectEndpointKey::EffectRow(fresh_tail), EffectEndpointKey::EmptyNegative, 61);
            let lower = atom(&mut session, if listed { "E" } else { "F" });
            solve_effect(&mut session, lower, EffectEndpointKey::EffectRow(fresh_source), 62);
            assert_eq!(session.errors.is_empty(), listed, "listed E stays local; late F reaches the fresh empty tail boundary");
        }
    }

    #[test]
    fn capture_incidence_merge_chain_keeps_one_record_per_relation_and_rolls_back_splices() {
        let mut session = make_session("act E\nmy left x = x");
        let owner = root(&session, "left");
        let declaration = session.batch.hir.source_effect_declarations()[0].id.clone();
        let mut tails = Vec::new();
        for _ in 0..64 {
            let tail = session.fresh_effect_at_level(2).unwrap();
            let source = session.fresh_effect_at_level(2).unwrap();
            let view = session.candidate_effect_view(owner.clone(), declaration.declaration.clone(),
                vec![declaration.clone()], Some(tail)).unwrap();
            session.candidate_insert_bound(ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(source)),
                Polarity::Negative, ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(view))).unwrap();
            tails.push(tail);
        }
        let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        let before_buckets = state.capture_incidence.clone();
        let before_records = state.capture_records.clone();
        let before_keys = state.capture_incidence_keys.clone();
        let result = session.with_route_transaction(|session| {
            for pair in tails.windows(2) { session.candidate_splice_capture_incidence(pair[0], pair[1])?; }
            let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            assert_eq!(state.capture_records.len(), before_records.len(), "equality does not duplicate retained incidence");
            assert_eq!(state.capture_incidence.len(), 1);
            let mut next = Some(state.capture_incidence[tails.last().unwrap()].head);
            let mut visited = HashSet::new();
            while let Some(index) = next {
                assert!(visited.insert(index), "bucket remains acyclic");
                next = state.capture_records[index].next;
            }
            assert_eq!(visited.len(), before_records.len());
            Err::<(), _>(exhausted())
        });
        assert_eq!(result, Err(exhausted()));
        let state = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        assert_eq!(state.capture_incidence, before_buckets);
        assert_eq!(state.capture_records, before_records);
        assert_eq!(state.capture_incidence_keys, before_keys);
    }
    fn attach_effect_bound_origins(
        session: &mut InferenceSession,
        owner: EffectEndpointKey,
        upper: EffectEndpointKey,
        origins: &[TypedPairKey],
    ) {
        for &origin in origins {
            let previous = session.candidate_processing(Some(origin));
            session.candidate_insert_bound(ExtrusionEndpoint::Effect(owner), Polarity::Negative,
                ExtrusionEndpoint::Effect(upper)).unwrap();
            session.candidate_processing(previous);
        }
    }
    fn assert_effect_replay_has_one_owning_conflict(
        session: &mut InferenceSession,
        lower: EffectEndpointKey,
        upper: EffectEndpointKey,
        slot: u8,
    ) {
        let before = session.errors.len();
        solve_effect(session, lower, upper, slot);
        assert_eq!(session.errors.len(), before + 1);
        let (occurrence, cause) = cause(session, "left", slot);
        let error = session.errors.last().unwrap();
        assert_eq!(error.occurrence, occurrence);
        assert_eq!(error.cause, cause);
        assert!(matches!(error.kind, SolverErrorKind::IncompatibleEffect { .. }));
    }

    #[test]
    fn multiply_originated_bound_replays_future_conflict_once_for_each_owning_cause() {
        let mut session = make_session("act E\nact F\nmy left x: 'a -> [E] 'a = x");
        let owner = root(&session, "left");
        session.execute_candidate_source_root(&owner).unwrap();
        let allowed = EffectEndpointKey::Allowance(view(&session, "left"));
        let bound_owner = EffectEndpointKey::EffectRow(session.fresh_effect_at_level(1).unwrap());
        let first = EffectEndpointKey::EffectRow(session.fresh_effect_at_level(0).unwrap());
        let second = EffectEndpointKey::EffectRow(session.fresh_effect_at_level(0).unwrap());
        solve_effect(&mut session, first, first, 41);
        solve_effect(&mut session, second, second, 42);
        attach_effect_bound_origins(&mut session, bound_owner, allowed, &[
            TypedPairKey::Effect { lower: first, upper: first },
            TypedPairKey::Effect { lower: second, upper: second },
        ]);
        assert!(session.errors.is_empty());
        let forbidden = atom(&mut session, "F");
        assert_effect_replay_has_one_owning_conflict(&mut session, forbidden, bound_owner, 43);
        assert_effect_replay_has_one_owning_conflict(&mut session, first, first, 44);
        assert_effect_replay_has_one_owning_conflict(&mut session, second, second, 45);
    }

    // Qualification comes from the resolved recursive source call, independently
    // of the effect bounds whose transport these fixtures exercise.
    fn source_qualified_effect_extrude(
        session: &mut InferenceSession,
        parent: EffectEndpointKey,
        polarity: Polarity,
    ) -> Result<ExtrusionEndpoint, SolveAvailabilityError> {
        let seed = root(session, "intrusion_seed");
        let source = session.batch.hir.local_source(&seed).unwrap().unwrap();
        let references = &session.batch.candidate_source.references;
        let (checking, event) = references.checking.iter().find(|(checking, _)| {
            source.expressions().iter().any(|expression| &expression.occurrence == checking.occurrence())
        }).unwrap();
        assert!(references.qualifies(*event));
        let checking = checking.clone();
        let task = LiveConstraintTask::Effect(parent, parent);
        let relation = session.candidate_context_seed(task, &checking, None)?.unwrap();
        let previous = session.candidate_graph.as_mut().unwrap()
            .intrusion.effect_algebra.context.processing.replace(relation);
        let result = session.candidate_extrude(ExtrusionEndpoint::Effect(parent), polarity, 0);
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = previous;
        result
    }

    #[test]
    fn raw_and_canonical_effect_roots_replay_late_conflict_after_parent_copy_intrusion() {
        let mut session = make_session("act E\nact F\nmy left x: 'a -> [E] 'a = x; my intrusion_seed x = intrusion_seed x");
        let owner = root(&session, "left");
        session.execute_candidate_source_root(&owner).unwrap();
        let allowed = EffectEndpointKey::Allowance(view(&session, "left"));
        let parent = EffectEndpointKey::EffectRow(session.fresh_effect_at_level(2).unwrap());
        session.candidate_insert_bound(ExtrusionEndpoint::Effect(parent), Polarity::Negative,
            ExtrusionEndpoint::Effect(allowed)).unwrap();
        let ExtrusionEndpoint::Effect(copy) = source_qualified_effect_extrude(
            &mut session, parent, Polarity::Positive).unwrap() else { panic!("effect copy"); };
        assert_ne!(copy, parent);
        solve_effect(&mut session, copy, allowed, 51);
        let (occurrence, cause) = cause(&session, "left", 52);
        session.candidate_restore_bound(ExtrusionEndpoint::Effect(copy), Polarity::Negative,
            ExtrusionEndpoint::Effect(parent), &occurrence, &cause).unwrap();
        solve_effect(&mut session, copy, copy, 53);
        assert_eq!(session.canonical_effect(copy), parent);
        assert!(session.errors.is_empty());
        let forbidden = atom(&mut session, "F");
        assert_effect_replay_has_one_owning_conflict(&mut session, forbidden, parent, 54);
        assert_effect_replay_has_one_owning_conflict(&mut session, copy, allowed, 55);
        assert_effect_replay_has_one_owning_conflict(&mut session, parent, allowed, 56);
    }

    #[test]
    fn multiply_originated_bound_keeps_future_conflict_paths_through_extrusion_and_intrusion() {
        let mut session = make_session("act E\nact F\nmy left x: 'a -> [E] 'a = x; my intrusion_seed x = intrusion_seed x");
        let owner = root(&session, "left");
        session.execute_candidate_source_root(&owner).unwrap();
        let allowed = EffectEndpointKey::Allowance(view(&session, "left"));
        let parent = EffectEndpointKey::EffectRow(session.fresh_effect_at_level(2).unwrap());
        let first = EffectEndpointKey::EffectRow(session.fresh_effect_at_level(0).unwrap());
        let second = EffectEndpointKey::EffectRow(session.fresh_effect_at_level(0).unwrap());
        solve_effect(&mut session, first, first, 61);
        solve_effect(&mut session, second, second, 62);
        attach_effect_bound_origins(&mut session, parent, allowed, &[
            TypedPairKey::Effect { lower: first, upper: first },
            TypedPairKey::Effect { lower: second, upper: second },
        ]);
        let ExtrusionEndpoint::Effect(copy) = source_qualified_effect_extrude(
            &mut session, parent, Polarity::Negative).unwrap() else { panic!("effect copy"); };
        assert_ne!(copy, parent);
        let forbidden = atom(&mut session, "F");
        assert_effect_replay_has_one_owning_conflict(&mut session, forbidden, copy, 63);
        assert_effect_replay_has_one_owning_conflict(&mut session, first, first, 64);
        assert_effect_replay_has_one_owning_conflict(&mut session, second, second, 65);
        let (occurrence, intrusion_cause) = cause(&session, "left", 66);
        session.candidate_restore_bound(ExtrusionEndpoint::Effect(copy), Polarity::Positive,
            ExtrusionEndpoint::Effect(parent), &occurrence, &intrusion_cause).unwrap();
        solve_effect(&mut session, copy, copy, 67);
        assert_eq!(session.canonical_effect(copy), parent);
        // Source-qualified extrusion queues intrusion, so the earlier drain
        // may establish equality before the explicit reverse bound above.
        // Add another contribution after equality as well as retaining the first.
        let later_forbidden = atom(&mut session, "F");
        assert_effect_replay_has_one_owning_conflict(&mut session, later_forbidden, parent, 68);
        // Both actual forbidden contributions remain reachable, once each.
        for (origin, slot) in [(first, 69), (second, 70)] {
            let before = session.errors.len();
            solve_effect(&mut session, origin, origin, slot);
            assert_eq!(session.errors.len(), before + 2);
            let (occurrence, cause) = cause(&session, "left", slot);
            assert!(session.errors[before..].iter().all(|error| error.occurrence == occurrence && error.cause == cause));
            let operands: HashSet<_> = session.errors[before..].iter().map(|error| match error.kind {
                SolverErrorKind::IncompatibleEffect { operand, .. } => operand,
                _ => panic!("effect conflict"),
            }).collect();
            assert_eq!(operands.len(), 2);
        }
    }

    #[test]
    fn transported_fresh_effect_conflicts_do_not_replay_on_template_or_valid_use() {
        let mut session = make_session("act E\nact F\nmy left x: 'a -> [E] 'a = x");
        let owner = root(&session, "left");
        session.execute_candidate_source_root(&owner).unwrap();
        let allowed = EffectEndpointKey::Allowance(view(&session, "left"));
        let template = EffectEndpointKey::EffectRow(session.fresh_effect_at_level(2).unwrap());
        session.candidate_insert_bound(ExtrusionEndpoint::Effect(template), Polarity::Negative,
            ExtrusionEndpoint::Effect(allowed)).unwrap();
        let template_bound = BoundKey(ExtrusionEndpoint::Effect(template), Polarity::Negative,
            ExtrusionEndpoint::Effect(allowed));
        let source = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound(template_bound).unwrap();
        let invalid = EffectEndpointKey::EffectRow(session.fresh_effect_at_level(3).unwrap());
        let valid = EffectEndpointKey::EffectRow(session.fresh_effect_at_level(3).unwrap());
        // Exercise the same bound-carrier transport seam used by freshening,
        // with two independent use origins and the shared annotation boundary.
        for (endpoint, use_origin) in [(invalid, 1), (valid, 2)] {
            session.candidate_context_transport(source,
                BoundKey(ExtrusionEndpoint::Effect(endpoint), Polarity::Negative, ExtrusionEndpoint::Effect(allowed)),
                use_origin).unwrap();
            session.candidate_insert_bound(ExtrusionEndpoint::Effect(endpoint), Polarity::Negative,
                ExtrusionEndpoint::Effect(allowed)).unwrap();
        }
        let f = atom(&mut session, "F");
        solve_effect(&mut session, f, invalid, 31);
        assert_eq!(session.errors.len(), 1);
        let (invalid_occurrence, invalid_cause) = cause(&session, "left", 31);
        assert_eq!(session.errors[0].occurrence, invalid_occurrence);
        assert_eq!(session.errors[0].cause, invalid_cause);
        solve_effect(&mut session, template, allowed, 32);
        assert_eq!(session.errors.len(), 1, "template recheck must not replay a fresh-use conflict");
        let e = atom(&mut session, "E");
        solve_effect(&mut session, e, valid, 33);
        solve_effect(&mut session, valid, allowed, 34);
        assert_eq!(session.errors.len(), 1, "independent valid use must retain its own diagnostics");
        let context = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        assert!(context.bound(template_bound).is_some());
        assert!(context.children(TypedPairKey::Effect { lower: template, upper: allowed })
            .all(|pair| pair != TypedPairKey::Effect { lower: invalid, upper: allowed }));
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
        assert_eq!(annotation_ref.unwrap().owner, SourceRootId::Definition(root(&session, "left")));
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
                        .owner.definition_root()
                        == Some(&root(&session, "right"))
                }
                _ => false,
            }
        }));
    }
    #[test]
    fn views_keep_fresh_use_ownership_and_intrusion_rollback_restores_relations() {
        let mut session = make_session(
            "act E\nact F\nmy left x: 'a -> [E, 'e] 'a = x; my first = left; my second = left; my intrusion_seed x = intrusion_seed x",
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
                SourceRootId::Definition(root(&session, "left"))
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
                let ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(copy)) = source_qualified_effect_extrude(
                    session, EffectEndpointKey::EffectRow(parent), Polarity::Positive,
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
        assert_eq!(state.context.checkpoint(), before.context);
        assert_eq!(state.context.bytes().unwrap(), state.context.enumerated_bytes());
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
        solve_effect(&mut session, EffectEndpointKey::EffectRow(parent), EffectEndpointKey::Allowance(closed), 22);
        assert_eq!(session.errors.len(), old_errors, "rolled-back conflicts must not remain reachable");
        let retried_forbidden = atom(&mut session, "F");
        assert_effect_replay_has_one_owning_conflict(&mut session, retried_forbidden, EffectEndpointKey::EffectRow(parent), 23);
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
        let receiver = session.fresh_value_at_level(0).unwrap();
        let (occurrence, cause) = cause(&session, "left", 0);
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::PositiveFunction(function),
                    upper: ValueEndpointKey::ValueRow(receiver),
                },
                &occurrence,
                &cause,
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
