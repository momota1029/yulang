use super::program::{BlockStatement, RecordParameterField};
use super::{
    dispatch,
    continuation::{ResumeTemplate, TemplateHandle, TemplateNode},
    literal,
    program::{
        Binder, CasePattern, Code, ExecutionRoot, Instruction, Label, NameConsumption, ParameterRole,
        RuntimeProgram, RuntimeUnavailable, SourceSite,
    },
    receiving::{
        CallbackResultSchema, CallbackUseHandle, ExecutionView,
        Observation, Receiving, RootCompSchema, ViewHandle,
    },
};
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};
use yu_hir::shadow::{
    LocalSourceCatchPattern, LocalSourceCatchPayloadPattern, LocalSourceCatchValuePattern,
    LocalSourceResolution, SourceAnnotationValue, SourceOperationDeclaration, SourceOperationId,
    SourceOperationResolution,
};
use yu_hir::{DefId, ExpressionRootId, HirParameterId};


/// Explicit source small-step state. Source recursion grows arenas/frames, never
/// the Rust call stack. Environments and cells contain integer arena references,
/// so recursive closures do not construct reference-counted ownership cycles.
pub struct Machine {
    program: Arc<RuntimeProgram>,
    state: State,
    frames: Vec<Frame>,
    values: Vec<RuntimeValue>,
    executables: HashMap<usize, ExecutableValue>,
    environments: Vec<Environment>,
    cells: Vec<Option<ReceivedValue>>,
    execution_roots: Vec<ScheduledRoot>,
    initializing_globals: HashSet<usize>,
    selected: Option<usize>,
    steps: usize,
    next_receiver: usize,
    current_owner: ExecutionOwner,
    invocations: Vec<InvocationDescriptor>,
    resume_templates: Vec<ResumeTemplate>,
    next_handler: usize,
    next_request: usize,
    active_receivers: Vec<usize>,
    continuations: Vec<SavedContinuation>,
    receiving: Receiving,
    executing_views: Vec<ExecutionView>,
    operation_v1_trace: Option<OperationV1Trace>,
    tuple_prefixes: Vec<TuplePrefix>,
    dispatch: dispatch::Machine,
    name_entry_trace: Option<NameEntryCorrespondenceTrace>,
    name_entry_value_entry_attempts: Vec<NameEntryValueEntryAttempt>,
    pending_name_entry: Option<PendingNameEntry>,
    name_entry_return_token: Option<PendingNameEntry>,
    name_entry_return_observations: Vec<NameEntryReturnObservation>,
    pending_name_observation: Option<PendingNameObservation>,
    pending_name_return_observation: Option<CompletedNameObservation>,
    name_entry_name_return_observations: Vec<NameEntryNameReturnObservation>,
    name_receipt_calls: Vec<NameReceiptCallObservation>,
    #[cfg(test)]
    r312_name_lookups: Vec<R312NameLookup>,
    #[cfg(test)]
    r312_name_receipts: Vec<R312NameReceipt>,
    #[cfg(test)]
    r312_name_forces: Vec<R312NameForce>,
    #[cfg(test)]
    r312_name_force_completions: Vec<R312NameForceCompletion>,
    #[cfg(test)]
    r312_active_forces: HashMap<usize, R312PendingForce>,
    #[cfg(test)]
    r312_frame_events: Vec<R312FrameEvent>,
    #[cfg(test)]
    r312_pending_name_lookup: Option<usize>,
    #[cfg(test)]
    r312_pending_force: Option<R312PendingForce>,
    #[cfg(test)]
    r312_observations_truncated: bool,
    #[cfg(test)]
    r312_order: usize,
    #[cfg(test)]
    r313_next_frame_id: usize,
    #[cfg(test)]
    r313_value_entry_binds: Vec<R313ValueEntryBind>,
    #[cfg(test)]
    r313_watch_apply: Option<SourceSite>,
    #[cfg(test)]
    r313_return_snapshot: Option<R313CalleeReturnSnapshot>,
    #[cfg(test)]
    r315_module_uses: Vec<R315ModuleUse>,
    #[cfg(test)]
    r323_resume_observations: Vec<R323ResumeObservation>,
    #[cfg(test)]
    r323_request_observations: Vec<R323RequestObservation>,
    #[cfg(test)]
    r323_template_observations: Vec<R323TemplateObservation>,
    #[cfg(test)]
    r323_owner_replay_observations: Vec<R323OwnerReplayObservation>,
    name_receipt_seed_trace: Option<String>,
    name_receipt_calls_truncated: bool,
    name_receipt_observation_unavailable: bool,
    name_receipt_seed_status: NameReceiptSeedObservationStatus,
}

/// Availability of the bounded provisional Name/receipt observation.
/// `NoCorrespondenceObserved` describes this observer only; it is not semantic
/// evidence that no qualifying source event occurred.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NameReceiptSeedObservationStatus {
    NotCompleted,
    NoCorrespondenceObserved,
    Observed,
    Truncated,
    Unavailable,
}

/// Provisional research observation joining an actual lexical Name receipt to
/// the subsequent fresh ValueEntry parameter cell. This record grants no
/// runtime permission and is never read by execution decisions.
#[derive(Clone, Debug)]
pub struct NameEntryCorrespondenceTrace {
    pub invocation: usize,
    pub name_site: SourceSite,
    pub returned_value_origin_site: SourceSite,
    pub source_parameter: HirParameterId,
    pub entry_parameter: HirParameterId,
    pub source_cell: usize,
    pub value: usize,
    pub view: usize,
    pub receipt_index: usize,
    pub cells_before_bind: usize,
    pub bound_cell: usize,
    pub cells_after_bind: usize,
}

/// Per-attempt target evidence, independent of the sticky correspondence trace.
#[derive(Clone, Debug)]
pub struct NameEntryValueEntryAttempt {
    pub invocation: usize,
    pub entry_parameter_ordinal: u32,
    pub value: usize,
    pub view: usize,
    pub cells_before_bind: usize,
    pub bound_cell: usize,
    pub cells_after_bind: usize,
    pub token_receipt_index: Option<usize>,
    pub token_source_parameter_ordinal: Option<u32>,
    pub token_name_site_ordinal: Option<u32>,
    pub token_accepted: bool,
}

#[derive(Clone, Debug)]
pub struct NameEntryReturnObservation {
    pub frame: &'static str,
    pub invocation: Option<usize>,
    pub token_receipt_index: Option<usize>,
    pub token_source_parameter_ordinal: Option<u32>,
    pub token_name_site_ordinal: Option<u32>,
    pub token_value: Option<usize>,
    pub token_view: Option<usize>,
    pub token_cells_before_bind: Option<usize>,
    pub returned_value: usize,
    pub returned_view: usize,
    pub cells_at_return: usize,
}

#[derive(Clone, Debug)]
pub struct NameEntryNameReturnObservation {
    pub resolution: &'static str,
    pub name_site_ordinal: u32,
    pub source_cell: usize,
    pub value: usize,
    pub view: usize,
    pub receipt_index: usize,
    pub cells_before_observe: usize,
    pub return_frame: &'static str,
}

struct PendingNameObservation {
    resolution: &'static str,
    site: SourceSite,
    cell: usize,
}

struct CompletedNameObservation {
    resolution: &'static str,
    site: SourceSite,
    cell: usize,
    value: ValueHandle,
    view: ViewHandle,
    receipt_index: usize,
    cells_before_observe: usize,
}

struct NameReceiptCallObservation {
    call_site: SourceSite,
    #[cfg(test)]
    callee_code: Option<usize>,
    invocation: usize,
    previous_owner: ExecutionOwner,
    callee_value: ValueHandle,
    callee_view: ViewHandle,
    #[cfg(test)]
    callee_interface: ParameterRole,
    #[cfg(test)]
    callee_dispatch: Option<usize>,
    callee_site: SourceSite,
    formal: HirParameterId,
    closure_environment: usize,
    argument_environment: usize,
    delay_value: ValueHandle,
    argument_code: usize,
    delay_view: ViewHandle,
    #[cfg(test)]
    selected_step: usize,
    #[cfg(test)]
    selected_order: usize,
}
#[cfg(test)]
struct R312NameLookup {
    step: usize,
    order: usize,
    code: usize,
    site: SourceSite,
    owner: ExecutionOwner,
    environment: usize,
    parameter: HirParameterId,
    cell: usize,
    value: ValueHandle,
    view: ViewHandle,
    consumption: NameConsumption,
}
#[cfg(test)]
struct R312NameReceipt {
    lookup: usize,
    step: usize,
    order: usize,
    receipt: usize,
    owner: ExecutionOwner,
    site: SourceSite,
    value: ValueHandle,
    view: ViewHandle,
    consumption: NameConsumption,
}
#[cfg(test)]
struct R312NameForce {
    lookup: usize,
    receipt: usize,
    step: usize,
    order: usize,
    owner: ExecutionOwner,
    site: SourceSite,
    view: ViewHandle,
    value: ValueHandle,
    code: Label,
    environment: usize,
}
#[cfg(test)]
struct R312NameForceCompletion {
    lookup: usize,
    receipt: usize,
    step: usize,
    order: usize,
    owner: ExecutionOwner,
    return_owner: ExecutionOwner,
    entry_receiver: usize,
    parameter: HirParameterId,
    site: SourceSite,
    input_view: ViewHandle,
    input_value: ValueHandle,
    output_view: ViewHandle,
    output_value: ValueHandle,
}
#[cfg(test)]
struct R313ValueEntryBind {
    step: usize,
    order: usize,
    entry_receiver: usize,
    parameter: HirParameterId,
    binder_parent_environment: usize,
    binder_parent: Option<usize>,
    binder_at_parent: Option<(Binder, usize)>,
    parent_dispatch: String,
    cells_before_bind: usize,
    environments_before_bind: usize,
    received: ReceivedValue,
    bound_cell: usize,
    bound_environment: usize,
    cells_after_bind: usize,
    environments_after_bind: usize,
}
#[cfg(test)]
#[derive(Clone)]
struct R313CalleeReturnSnapshot {
    frame_id: usize,
    apply_site: SourceSite,
    argument_code: Label,
    caller_environment: usize,
    source_name_initialization: Option<R313SourceNameInitialization>,
    cells: Vec<Option<ReceivedValue>>,
    environments: Vec<Environment>,
    values: Vec<RuntimeValue>,
    receiving_views: Vec<String>,
    receiving_image_chains: Vec<String>,
    receiving_scan_truncated: bool,
}
#[cfg(test)]
#[derive(Clone)]
struct R313SourceNameInitialization {
    parameter: HirParameterId,
    cell: usize,
    received: ReceivedValue,
}
#[cfg(test)]
#[derive(Clone)]
struct R315ModuleUse {
    step: usize,
    code: usize,
    site: SourceSite,
    owner: ExecutionOwner,
    environment: usize,
    definition: DefId,
    cell: usize,
    consumption: NameConsumption,
}
#[cfg(test)]
enum R312FrameEvent {
    RequestObserved {
        step: usize,
        order: usize,
        request: usize,
        site: SourceSite,
        owner: ExecutionOwner,
    },
    PendingCalleeAtRequest {
        step: usize,
        order: usize,
        request: usize,
        frame_id: usize,
        request_site: SourceSite,
        owner: ExecutionOwner,
        apply_site: SourceSite,
        callee: Option<Label>,
        argument: Label,
        environment: usize,
    },
    CalleeReturned {
        step: usize,
        order: usize,
        frame_id: usize,
        owner: ExecutionOwner,
        apply_site: SourceSite,
        callee: Option<Label>,
        argument: Label,
        environment: usize,
        value: ValueHandle,
        view: ViewHandle,
        interface: ParameterRole,
        dispatch: Option<usize>,
        provider: SourceSite,
    },
}
#[cfg(test)]
#[derive(Clone)]
struct R312PendingForce {
    lookup: usize,
    receipt: usize,
    owner: ExecutionOwner,
    site: SourceSite,
    view: ViewHandle,
    value: ValueHandle,
}

#[cfg(test)]
#[derive(Clone)]
struct R323ResumeObservation {
    run_id: usize,
    request: usize,
    template: usize,
    response: ReceivedValue,
    source: SourceSite,
    owner: ExecutionOwner,
    owner_live: bool,
    step: usize,
}

#[cfg(test)]
#[derive(Clone)]
struct R323RequestObservation {
    run_id: usize,
    request: usize,
    declaration: Arc<SourceOperationDeclaration>,
    payload: ReceivedValue,
    source: SourceSite,
    owner: ExecutionOwner,
    owner_live: bool,
}
#[cfg(test)]
#[derive(Clone)]
struct R323TemplateObservation {
    run_id: usize,
    request: usize,
    template: usize,
    capture_owner: ExecutionOwner,
    saved_frame_order: Vec<R323FrameWitness>,
}

#[cfg(test)]
#[derive(Clone)]
enum R323FrameWitness {
    Callee {
        frame_id: usize,
        callee: Option<Label>,
        argument: Label,
        environment: usize,
        site: SourceSite,
    },
    BlockExpression {
        block: Arc<Code>,
        next: usize,
        environment: usize,
    },
    RootCompReturn {
        execution: ExecutionView,
    },
    Owner(ExecutionOwner),
    Unsupported,
}
#[cfg(test)]
#[derive(Clone)]
struct R323OwnerReplayObservation {
    run_id: usize,
    request: usize,
    template: usize,
    node: usize,
    original: ExecutionOwner,
    resolved: ExecutionOwner,
    resolved_active: bool,
    control: Vec<(usize, usize)>,
    owner: ExecutionOwner,
    owned: bool,
    previous: ExecutionOwner,
    owner_live: bool,
    current_owner_after: ExecutionOwner,
    call_site: Option<SourceSite>,
    provider_site: Option<SourceSite>,
}

struct PendingNameEntry {
    invocation: usize,
    site: SourceSite,
    source_parameter: HirParameterId,
    source_cell: usize,
    value: ValueHandle,
    view: ViewHandle,
    cells_before_bind: usize,
    receipt_index: Option<usize>,
}
#[derive(Default)]
struct OperationV1Trace {
    initializer_catch_owner: Option<ExecutionOwner>,
    installed_local_cell: Option<(usize, ValueHandle, usize, ExecutionOwner)>,
    read_local_cell: Option<(usize, ValueHandle, ExecutionOwner)>,
    local_invocation_owner: Option<ExecutionOwner>,
    response_definition_read: Option<(ValueHandle, usize, SourceSite)>,
    selected_closure: Option<(ValueHandle, usize)>,
    applied_response_invocation: Option<(SourceSite, ExecutionOwner)>,
    request_operation_seen: bool,
    callback_operation_seen: bool,
    callback_operation_owner: Option<ExecutionOwner>,
    callback_request_event: Option<usize>,
    callback_request: Option<(usize, SourceSite)>,
    live_handler: Option<(SourceSite, yu_hir::shadow::SourceNodeKey, usize, SourceSite)>,
}
/// Resolved machine plan: only definitions index cache cells.
#[derive(Clone)]
enum ScheduledRoot {
    Definition(usize),
    Expression { root: ExpressionRootId, code: Label },
}
// Execution ownership is distinct from receiving-boundary authority. The
// ambient module span never aliases invocation ordinal zero or grants a profile.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(super) enum ExecutionOwner {
    ModuleRun,
    Invocation(usize),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct HandlerInstallation {
    occurrence: usize,
    owner: ExecutionOwner,
}
#[derive(Clone)]
pub(super) struct InvocationDescriptor {
    call: SourceSite,
    provider: SourceSite,
    active: bool,
}
impl InvocationDescriptor {
    pub(super) fn is_active(&self) -> bool {
        self.active
    }
    #[cfg(test)]
    pub(super) fn active_for_test(site: SourceSite) -> Self {
        Self {
            call: site.clone(),
            provider: site,
            active: true,
        }
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ValueHandle(usize);
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ContinuationHandle(usize);
#[derive(Clone, Debug)]
pub struct RuntimeValue {
    pub source: SourceSite,
    pub kind: RuntimeValueKind,
}
#[derive(Clone, Debug)]
pub enum RuntimeValueKind {
    Unit,
    Integer(Box<str>),
    Boolean(bool),
    String(Box<str>),
    Primitive(yu_hir::shadow::PinnedPrimitiveOp),
    Tuple(Vec<TupleElement>),
    Variant { tag: Box<str>, payloads: Vec<TupleElement> },
    Record(Vec<(Box<str>, TupleElement)>),
    Closure,
    Computation,
    Operation(SourceOperationResolution),
}
/// One evaluated structural element, including the exact source receiving view.
/// The view remains private so callers cannot forge runtime evidence.
#[derive(Clone, Copy, Debug)]
pub struct TupleElement {
    received: ReceivedValue,
}
impl TupleElement {
    pub fn value(&self) -> ValueHandle {
        self.received.value
    }
}
#[derive(Clone, Debug)]
pub enum RuntimeOutcome {
    /// A whole-module schedule with no executable source completes without
    /// manufacturing a value or a source occurrence for an import statement.
    EmptyModuleCompleted,
    Running,
    Completed(ValueHandle),
    UnhandledRequest {
        source: SourceSite,
        operation: SourceOperationId,
        event: usize,
        payload: ValueHandle,
        continuation: ContinuationHandle,
    },
    Unavailable(RuntimeUnavailable),
    ResourceExhausted {
        steps: usize,
    },
}
// The actual value remains distinct from the source interface under which a
// receiver holds it. Later complete-view evidence belongs on ReceivedValue,
// rather than mutating a shared closure or inferring protection from its tag.
#[derive(Clone, Copy, Debug)]
pub(super) struct ReceivedValue {
    value: ValueHandle,
    interface: ParameterRole,
    view: ViewHandle,
    dispatch: Option<usize>,
}
struct TuplePrefix {
    previous: Option<usize>,
    received: ReceivedValue,
}
#[derive(Clone)]
struct Environment {
    parent: Option<usize>,
    binder: Option<(Binder, usize)>,
    dispatch: dispatch::State,
}
#[derive(Clone)]
enum ExecutableValue {
    Continuation(TemplateHandle),
    Closure {
        parameter: HirParameterId,
        unit_pattern: bool,
        record_pattern: Option<Arc<[RecordParameterField]>>,
        role: ParameterRole,
        root_schema: Option<Arc<RootCompSchema>>,
        callback_schema: Option<Arc<CallbackResultSchema>>,
        body: Label,
        environment: usize,
    },
    Delay {
        code: Label,
        environment: usize,
    },
    Request {
        declaration: Arc<SourceOperationDeclaration>,
        payload: ReceivedValue,
        source: SourceSite,
    },
    Primitive {
        operation: yu_hir::shadow::PinnedPrimitiveOp,
        arguments: Vec<ValueHandle>,
    },
}
enum State {
    Evaluate {
        code: Label,
        environment: usize,
    },
    Return(ReceivedValue),
    EnterTemplate {
        template: TemplateHandle,
        node: usize,
        control: HashMap<usize, usize>,
        response: ReceivedValue,
    },
    Request(PendingRequest),
    IntegerProduct {
        product: super::decimal::Product,
        site: SourceSite,
    },
    Stopped(RuntimeOutcome),
}
#[derive(Clone)]
pub(super) enum Frame {
    ResumeArgument {
        template: TemplateHandle,
        source: SourceSite,
    },
    ResumeReturn,
    OwnerReturn {
        owner: ExecutionOwner,
        owned: bool,
        previous: ExecutionOwner,
    },
    RootCompReturn {
        execution: ExecutionView,
    },
    CatchReturn {
        handler: Arc<Code>,
        environment: usize,
        installation: HandlerInstallation,
    },
    OperationPayload {
        declaration: Arc<SourceOperationDeclaration>,
        source: SourceSite,
    },
    OperationResultConsumer {
        source: SourceSite,
        callback_use: Option<CallbackUseHandle>,
    },
    DiscardToUnit {
        site: SourceSite,
    },
    Callee {
        #[cfg(test)]
        frame_id: usize,
        callee: Option<Label>,
        argument: Label,
        environment: usize,
        site: SourceSite,
    },
    PrimitiveArgument {
        operation: yu_hir::shadow::PinnedPrimitiveOp,
        arguments: Vec<ValueHandle>,
        site: SourceSite,
    },
    ReceiverReturn {
        activation: usize,
        previous: ExecutionOwner,
    },
    ValueEntry {
        parameter: HirParameterId,
        callback_schema: Option<Arc<CallbackResultSchema>>,
        entry_receiver: usize,
        unit_pattern: bool,
        record_pattern: Option<Arc<[RecordParameterField]>>,
        body: Label,
        environment: usize,
    },
    RecordDefault {
        fields: Arc<[RecordParameterField]>,
        index: usize,
        argument: ReceivedValue,
        body: Label,
        environment: usize,
    },
    Local {
        block: Arc<Code>,
        next: usize,
        environment: usize,
        cell: usize,
        recursive: bool,
    },
    Condition {
        conditional: Arc<Code>,
        arm: usize,
        environment: usize,
    },
    BlockExpression {
        block: Arc<Code>,
        next: usize,
        environment: usize,
    },
    Sequence {
        sequence: Arc<Code>,
        next: usize,
        environment: usize,
    },
    Record {
        record: Arc<Code>,
        next: usize,
        environment: usize,
        prefix: Option<usize>,
    },
    Tuple {
        tuple: Arc<Code>,
        next: usize,
        environment: usize,
        prefix: Option<usize>,
    },
    Case {
        case: Arc<Code>,
        environment: usize,
    },
    Root {
        next: usize,
        cell: usize,
    },
    ExpressionReturn {
        root: ExpressionRootId,
        next: usize,
    },
    GlobalRead {
        cell: usize,
        consumption: NameConsumption,
        site: SourceSite,
        environment: usize,
    },
}

struct PendingRequest {
    declaration: Arc<SourceOperationDeclaration>,
    payload: ReceivedValue,
    source: SourceSite,
    event: usize,
    observations: Vec<Observation>,
    suffix: Vec<SavedFrame>,
}
struct SavedContinuation {
    frames: Vec<SavedFrame>,
    template: Option<TemplateHandle>,
    resumed: bool,
    #[allow(
        dead_code,
        reason = "unhandled request observations retained for a future external response consumer"
    )]
    observations: Vec<Observation>,
}
// Capture retains original lineage; template entry resolves a live occurrence
// afresh and never reactivates a historical ID.
enum SavedFrame {
    AmbientBoundary,
    ReceiverBoundary {
        original_activation: usize,
    },
    HandlerBoundary {
        handler: Arc<Code>,
        environment: usize,
        installation: HandlerInstallation,
    },
    Ordinary(Frame),
}

#[cfg(test)]
fn r323_same_site(left: &SourceSite, right: &SourceSite) -> bool {
    left.source_root == right.source_root
        && left.occurrence == right.occurrence
        && left.range == right.range
}

#[cfg(test)]
fn r323_frame_witness(frame: &Frame) -> R323FrameWitness {
    match frame {
        Frame::Callee { frame_id, callee, argument, environment, site } =>
            R323FrameWitness::Callee {
                frame_id: *frame_id, callee: *callee, argument: *argument,
                environment: *environment, site: site.clone(),
            },
        Frame::BlockExpression { block, next, environment } =>
            R323FrameWitness::BlockExpression {
                block: block.clone(), next: *next, environment: *environment,
            },
        Frame::RootCompReturn { execution } =>
            R323FrameWitness::RootCompReturn { execution: *execution },
        _ => R323FrameWitness::Unsupported,
    }
}

#[cfg(test)]
fn r323_saved_frame_witness(frame: &SavedFrame) -> R323FrameWitness {
    match frame {
        SavedFrame::AmbientBoundary => R323FrameWitness::Owner(ExecutionOwner::ModuleRun),
        SavedFrame::ReceiverBoundary { original_activation } =>
            R323FrameWitness::Owner(ExecutionOwner::Invocation(*original_activation)),
        SavedFrame::Ordinary(frame) => r323_frame_witness(frame),
        SavedFrame::HandlerBoundary { .. } => R323FrameWitness::Unsupported,
    }
}

#[cfg(test)]
fn r323_template_node_witness(node: &TemplateNode) -> R323FrameWitness {
    match node {
        TemplateNode::Hole | TemplateNode::ForwardHandler { .. } => R323FrameWitness::Unsupported,
        TemplateNode::Bind { frame, .. } => r323_frame_witness(frame),
        TemplateNode::Owner { original, .. } => R323FrameWitness::Owner(*original),
        TemplateNode::View { original, .. } => R323FrameWitness::RootCompReturn { execution: *original },
    }
}

#[cfg(test)]
fn r323_frame_witness_matches(left: &R323FrameWitness, right: &R323FrameWitness) -> bool {
    match (left, right) {
        (R323FrameWitness::Callee { frame_id: lf, callee: lc, argument: la, environment: le, site: ls },
         R323FrameWitness::Callee { frame_id: rf, callee: rc, argument: ra, environment: re, site: rs }) =>
            lf == rf && lc == rc && la.0 == ra.0 && le == re && r323_same_site(ls, rs),
        (R323FrameWitness::BlockExpression { block: lb, next: ln, environment: le },
         R323FrameWitness::BlockExpression { block: rb, next: rn, environment: re }) =>
            Arc::ptr_eq(lb, rb) && ln == rn && le == re && r323_same_site(&lb.site, &rb.site),
        (R323FrameWitness::RootCompReturn { execution: left },
         R323FrameWitness::RootCompReturn { execution: right }) =>
            left.view.index() == right.view.index()
                && left.receipt.index() == right.receipt.index()
                && left.occurrence == right.occurrence,
        (R323FrameWitness::Owner(left), R323FrameWitness::Owner(right)) => left == right,
        _ => false,
    }
}

#[cfg(test)]
fn r323_template_inner(node: &TemplateNode) -> Option<usize> {
    match node {
        TemplateNode::Hole => None,
        TemplateNode::Bind { inner, .. }
        | TemplateNode::Owner { inner, .. }
        | TemplateNode::ForwardHandler { inner, .. }
        | TemplateNode::View { inner, .. } => Some(*inner),
    }
}

#[cfg(test)]
fn r323_live_template_matches(template: &ResumeTemplate, observation: &R323TemplateObservation) -> bool {
    let suffix_len = observation.saved_frame_order.len();
    if template.nodes.len() != suffix_len + 2
        || template.root != suffix_len + 1
        || !matches!(template.nodes.first(), Some(TemplateNode::Hole))
    {
        return false;
    }
    let Some(TemplateNode::Owner { inner, original }) = template.nodes.last() else {
        return false;
    };
    if *inner != suffix_len || *original != observation.capture_owner {
        return false;
    }
    let live_order = template.nodes.iter().skip(1).take(suffix_len)
        .enumerate().map(|(offset, node)| {
            r323_template_inner(node) == Some(offset)
                && observation.saved_frame_order.get(offset)
                    .is_some_and(|saved| r323_frame_witness_matches(saved, &r323_template_node_witness(node)))
        }).collect::<Vec<_>>();
    live_order.iter().all(|matches| *matches)
}

impl RuntimeProgram {
    /// Starts from the original source-order schedule retained by this program.
    pub(crate) fn start_source_schedule(
        self: &Arc<Self>,
        definition: &DefId,
    ) -> Result<Machine, RuntimeUnavailable> {
        self.start(definition, &self.source_schedule)
    }

    pub(crate) fn start_module_schedule(self: &Arc<Self>) -> Result<Machine, RuntimeUnavailable> {
        self.start_with_schedule(None, &self.source_schedule)
    }

    /// The source interface owner supplies computation roots in source order.
    /// Value definitions materialize at first access. Successful definition
    /// materialization is cached; executing a delayed argument is never cached.
    pub fn start(
        self: &Arc<Self>,
        definition: &DefId,
        execution_roots: &[ExecutionRoot],
    ) -> Result<Machine, RuntimeUnavailable> {
        let selected = *self
            .definition_indices
            .get(definition)
            .ok_or(RuntimeUnavailable::MissingDefinition)?;
        self.start_with_schedule(Some(selected), execution_roots)
    }

    fn start_with_schedule(
        self: &Arc<Self>,
        selected: Option<usize>,
        execution_roots: &[ExecutionRoot],
    ) -> Result<Machine, RuntimeUnavailable> {
        let mut seen_definitions = HashSet::new();
        let mut seen_expressions = HashSet::new();
        let mut roots = Vec::new();
        for root in execution_roots {
            match root {
                ExecutionRoot::Definition(id) => {
                    let index = *self
                        .definition_indices
                        .get(id)
                        .ok_or(RuntimeUnavailable::MissingDefinition)?;
                    if !seen_definitions.insert(index) {
                        return Err(RuntimeUnavailable::ModuleInitializationOrder);
                    }
                    roots.push(ScheduledRoot::Definition(index));
                }
                ExecutionRoot::Expression(expression) => {
                    let root = &expression.root;
                    let Some(code) = self.expression_roots.get(root) else {
                        return Err(RuntimeUnavailable::InvalidSourceReference);
                    };
                    if code.0 != expression.code || !self._hir.owns_expression_root(root) {
                        return Err(RuntimeUnavailable::InvalidSourceReference);
                    }
                    if !seen_expressions.insert(root.clone()) {
                        return Err(RuntimeUnavailable::ModuleInitializationOrder);
                    }
                    roots.push(ScheduledRoot::Expression {
                        root: root.clone(),
                        code: *code,
                    });
                }
            }
        }
        let mut machine = Machine {
            program: self.clone(),
            state: State::Stopped(RuntimeOutcome::Running),
            frames: Vec::new(),
            values: Vec::new(),
            executables: HashMap::new(),
            environments: vec![Environment {
                parent: None,
                binder: None,
                dispatch: dispatch::State::default(),
            }],
            cells: vec![None; self.definitions.len()],
            execution_roots: roots,
            initializing_globals: HashSet::new(),
            selected,
            steps: 0,
            next_receiver: 0,
            current_owner: ExecutionOwner::ModuleRun,
            invocations: Vec::new(),
            resume_templates: Vec::new(),
            next_handler: 0,
            next_request: 0,
            active_receivers: Vec::new(),
            continuations: Vec::new(),
            receiving: Receiving::default(),
            executing_views: Vec::new(),
            operation_v1_trace: self.operation_v1.as_ref().map(|_| OperationV1Trace::default()),
            tuple_prefixes: Vec::new(),
            dispatch: dispatch::Machine::default(),
            name_entry_trace: None,
            name_entry_value_entry_attempts: Vec::new(),
            pending_name_entry: None,
            name_entry_return_token: None,
            name_entry_return_observations: Vec::new(),
            pending_name_observation: None,
            pending_name_return_observation: None,
            name_entry_name_return_observations: Vec::new(),
            name_receipt_calls: Vec::new(),
            #[cfg(test)]
            r312_name_lookups: Vec::new(),
            #[cfg(test)]
            r312_name_receipts: Vec::new(),
            #[cfg(test)]
            r312_name_forces: Vec::new(),
            #[cfg(test)]
            r312_name_force_completions: Vec::new(),
            #[cfg(test)]
            r312_active_forces: HashMap::new(),
            #[cfg(test)]
            r312_frame_events: Vec::new(),
            #[cfg(test)]
            r312_pending_name_lookup: None,
            #[cfg(test)]
            r312_pending_force: None,
            #[cfg(test)]
            r312_observations_truncated: false,
            #[cfg(test)]
            r312_order: 0,
            #[cfg(test)]
            r313_next_frame_id: 0,
            #[cfg(test)]
            r313_value_entry_binds: Vec::new(),
            #[cfg(test)]
            r313_watch_apply: None,
            #[cfg(test)]
            r313_return_snapshot: None,
            #[cfg(test)]
            r315_module_uses: Vec::new(),
            #[cfg(test)]
            r323_resume_observations: Vec::new(),
            #[cfg(test)]
            r323_request_observations: Vec::new(),
            #[cfg(test)]
            r323_template_observations: Vec::new(),
            #[cfg(test)]
            r323_owner_replay_observations: Vec::new(),
            name_receipt_seed_trace: None,
            name_receipt_calls_truncated: false,
            name_receipt_observation_unavailable: false,
            name_receipt_seed_status: NameReceiptSeedObservationStatus::NotCompleted,
        };
        machine.begin_root(0);
        Ok(machine)
    }
}

impl Machine {
    /// Return the provisional source trace, if this run actually joined one
    /// lexical Name/Observe receipt to a fresh ValueEntry parameter bind.
    pub fn name_entry_correspondence(&self) -> Option<&NameEntryCorrespondenceTrace> {
        self.name_entry_trace.as_ref()
    }

    pub fn name_entry_value_entry_attempts(&self) -> Vec<String> {
        self.name_entry_value_entry_attempts.iter().map(|event| format!(
            "invocation={} entry_parameter={} value={} view={} cells_before_bind={} bound_cell={} cells_after_bind={} token_receipt={:?} token_source_parameter={:?} token_name_site={:?} token_accepted={}",
            event.invocation, event.entry_parameter_ordinal, event.value, event.view,
            event.cells_before_bind, event.bound_cell, event.cells_after_bind,
            event.token_receipt_index, event.token_source_parameter_ordinal,
            event.token_name_site_ordinal, event.token_accepted
        )).collect()
    }

    pub fn name_entry_return_observations(&self) -> Vec<String> {
        self.name_entry_return_observations.iter().map(|event| format!(
            "frame={} invocation={:?} token_receipt={:?} token_source_parameter={:?} token_name_site={:?} token_value={:?} token_view={:?} token_cells_before_bind={:?} returned_value={} returned_view={} cells_at_return={}",
            event.frame, event.invocation, event.token_receipt_index,
            event.token_source_parameter_ordinal, event.token_name_site_ordinal,
            event.token_value, event.token_view, event.token_cells_before_bind,
            event.returned_value, event.returned_view, event.cells_at_return
        )).collect()
    }

    pub fn name_entry_name_return_observations(&self) -> Vec<String> {
        self.name_entry_name_return_observations.iter().map(|event| format!(
            "resolution={} name_site={} source_cell={} value={} view={} receipt={} cells_before_observe={} return_frame={}",
            event.resolution, event.name_site_ordinal, event.source_cell, event.value,
            event.view, event.receipt_index, event.cells_before_observe, event.return_frame
        )).collect()
    }

    pub fn name_receipt_seed_trace(&self) -> Option<&str> {
        self.name_receipt_seed_trace.as_deref()
    }

    pub fn name_receipt_seed_observation_status(&self) -> NameReceiptSeedObservationStatus {
        self.name_receipt_seed_status
    }

    fn finish_name_receipt_observation(&mut self) {
        use NameReceiptSeedObservationStatus as Status;
        if !matches!(self.state, State::Stopped(RuntimeOutcome::Completed(_))) {
            return;
        }
        self.name_receipt_seed_trace = None;
        self.name_receipt_seed_status = if self.name_receipt_observation_unavailable {
            Status::Unavailable
        } else if self.name_receipt_calls_truncated {
            Status::Truncated
        } else {
            Status::NoCorrespondenceObserved
        };
        if self.name_receipt_observation_unavailable || self.name_receipt_calls_truncated {
            return;
        }
        let Some(entry) = &self.name_entry_trace else { return; };
        let Some(call) = self.name_receipt_calls.iter().find(|call| call.invocation == entry.invocation) else {
            self.name_receipt_seed_status = Status::Unavailable;
            return;
        };
        let Some(receipt) = self.receiving.raw_receipt_fields(entry.receipt_index) else {
            self.name_receipt_seed_status = Status::Unavailable;
            return;
        };
        let Some(view) = self.receiving.raw_view_fields(entry.view) else {
            self.name_receipt_seed_status = Status::Unavailable;
            return;
        };
        let image = match self.receiving.bounded_raw_image_chain(entry.view) {
            Ok(image) => image,
            Err(super::receiving::RawObservationError::Truncated) => {
                self.name_receipt_seed_status = Status::Truncated;
                return;
            }
            Err(super::receiving::RawObservationError::Unavailable) => {
                self.name_receipt_seed_status = Status::Unavailable;
                return;
            }
        };
        self.name_receipt_seed_trace = Some(format!(
            "invocation={} call_site={:?} previous_owner={:?} callee_value={} callee_view={} callee_site={:?} formal={:?} closure_environment={} argument_environment={} delay_value={} argument_code={} delay_view={} name_site={:?} source_parameter={:?} entry_parameter={:?} source_cell={} value={} view={} bound_cell={} cells_before_bind={} cells_after_bind={} receipt=[{}] view_fields=[{}] image_chain=[{}]",
            call.invocation, call.call_site, call.previous_owner, call.callee_value.0,
            call.callee_view.index(), call.callee_site, call.formal, call.closure_environment,
            call.argument_environment, call.delay_value.0, call.argument_code,
            call.delay_view.index(), entry.name_site, entry.source_parameter,
            entry.entry_parameter, entry.source_cell, entry.value, entry.view,
            entry.bound_cell, entry.cells_before_bind, entry.cells_after_bind, receipt, view, image,
        ));
        self.name_receipt_seed_status = Status::Observed;
    }

    /// Mint the dynamic receipt after an actual completed run, never from a
    /// partial, exhausted, unhandled, unavailable, or mismatched execution.
    pub fn operation_v1_runtime_receipt(
        &self,
        completed: ValueHandle,
    ) -> Option<crate::OperationV1RuntimeReceipt> {
        let RuntimeOutcome::Completed(handle) = self.state_outcome()? else { return None; };
        if *handle != completed { return None; }
        let value = self.value(completed)?;
        if !matches!(&value.kind, RuntimeValueKind::Integer(text) if text.as_ref() == "42") {
            return None;
        }
        let plan = self.program.operation_v1.as_ref()?;
        let trace = self.operation_v1_trace.as_ref()?;
        if let Some(lineage) = &plan.local_lineage {
            let (local_cell, local_value, local_environment, install_owner) =
                trace.installed_local_cell?;
            let (read_cell, read_value, read_owner) = trace.read_local_cell?;
            let local_invocation_owner = trace.local_invocation_owner?;
            if trace.initializer_catch_owner != Some(install_owner)
                || local_cell != read_cell
                || local_value != read_value
                || install_owner != read_owner
                || !matches!(local_invocation_owner,
                    ExecutionOwner::Invocation(id)
                        if self.invocations.get(id).is_some_and(|invocation|
                            invocation.call.occurrence == lineage.apply.occurrence
                                && !invocation.active))
                || trace.callback_operation_owner != Some(local_invocation_owner)
                || self.executables.get(&local_value.0).is_none_or(|executable| {
                    !matches!(executable,
                        ExecutableValue::Closure { environment, .. }
                            if *environment == local_environment)
                })
            {
                return None;
            }
        }
        let (response_argument_value, response_argument_environment, response_argument_read_source) =
            trace.response_definition_read.clone()?;
        let (response_handle, captured_environment) = trace.selected_closure?;
        if response_argument_value != response_handle
            || response_argument_read_source.occurrence != plan.response_argument.occurrence
            || trace.applied_response_invocation.as_ref().is_none_or(|(site, owner)| {
                site.occurrence != plan.response_invocation_apply.occurrence
                    || site.source_root != plan.response_invocation_apply.source_root
                    || Some(*owner) != trace.callback_operation_owner
            })
            || !trace.callback_operation_seen
        {
            return None;
        }
        let (live_handler_source, selected_arm, callback_request_event, callback_request_source) =
            trace.live_handler.clone()?;
        if trace.callback_request_event != Some(callback_request_event)
            || callback_request_source.occurrence != plan.link.callback_apply
        {
            return None;
        }
        let expected_handler = plan.expected_outer_handler.as_ref()?;
        let expected_arm = plan.expected_outer_arm.as_ref()?;
        if live_handler_source.occurrence != expected_handler.occurrence
            || &selected_arm != expected_arm
            || self.value(response_handle)?.source.occurrence != plan.response_lambda.occurrence
        {
            return None;
        }
        Some(crate::OperationV1RuntimeReceipt {
            field_bound_id: plan.link.field_bound_id,
            request: plan.link.request.clone(),
            callback_apply: plan.link.callback_apply.clone(),
            callback_operation: plan.link.callback_operation.clone(),
            callback_operation_use: plan.link.callback_operation_use.clone(),
            response_definition: plan.link.response_definition.clone(),
            continuation_apply_source: plan.continuation_apply.clone(),
            response_argument_source: plan.response_argument.clone(),
            response_argument_read_source,
            response_argument_environment,
            response_closure_source: self.value(response_handle)?.source.clone(),
            response_closure_handle: response_handle.0,
            captured_environment,
            callback_request_event,
            callback_request_source,
            live_handler_source,
            selected_arm,
            result: "42".into(),
        })
    }

    fn state_outcome(&self) -> Option<&RuntimeOutcome> {
        match &self.state {
            State::Stopped(outcome) => Some(outcome),
            _ => None,
        }
    }
    pub fn value(&self, handle: ValueHandle) -> Option<&RuntimeValue> {
        self.values.get(handle.0)
    }
    pub fn continuation_depth(&self, handle: ContinuationHandle) -> Option<usize> {
        self.continuations
            .get(handle.0)
            .map(|saved| saved.frames.len())
    }
    pub fn steps(&self) -> usize {
        self.steps
    }

    /// A depleted caller budget pauses the live private machine. It never
    /// publishes a partial value as a completed evaluation and can be resumed.
    pub fn run(&mut self, step_budget: usize) -> RuntimeOutcome {
        for _ in 0..step_budget {
            let outcome = self.step();
            if !matches!(outcome, RuntimeOutcome::Running) {
                return outcome;
            }
        }
        match &self.state {
            State::Stopped(outcome) => outcome.clone(),
            _ => RuntimeOutcome::ResourceExhausted { steps: self.steps },
        }
    }

    pub(crate) fn resume_host_write(
        &mut self,
        continuation: ContinuationHandle,
        operation: &SourceOperationId,
    ) -> Result<Box<str>, RuntimeUnavailable> {
        let (current_continuation, current_operation, payload, source) = match &self.state {
            State::Stopped(RuntimeOutcome::UnhandledRequest {
                source,
                operation,
                payload,
                continuation,
                ..
            }) => (*continuation, operation, *payload, source.clone()),
            _ => return Err(RuntimeUnavailable::InvalidSourceReference),
        };
        if current_continuation != continuation
            || current_operation != operation
            || self.program.host_write_operation() != Some(operation)
        {
            return Err(RuntimeUnavailable::HostWriteResponse(source));
        }
        let saved = self.continuations.get(continuation.0)
            .ok_or(RuntimeUnavailable::HostWriteResponse(source.clone()))?;
        if saved.resumed {
            return Err(RuntimeUnavailable::HostWriteResponse(source));
        }
        let template = saved.template
            .ok_or(RuntimeUnavailable::HostWriteResponse(source.clone()))?;
        let resume = self.resume_templates.get(template.0)
            .ok_or(RuntimeUnavailable::HostWriteResponse(source.clone()))?;
        if !self.program.host_write_declaration_matches(&resume.declaration)
            || !matches!(self.values.get(payload.0).map(|value| &value.kind),
                Some(RuntimeValueKind::String(_)))
        {
            return Err(RuntimeUnavailable::HostWriteResponse(source));
        }
        let captured = match &self.values[payload.0].kind {
            RuntimeValueKind::String(text) => text.clone(),
            _ => unreachable!("the payload kind was checked above"),
        };
        let template_root = resume.root;
        self.continuations[continuation.0].resumed = true;
        let response_value = self.allocate(&source, RuntimeValueKind::Unit, None);
        let response = ReceivedValue {
            dispatch: None,
            value: response_value,
            interface: ParameterRole::Value,
            view: self.receiving.ground(response_value),
        };
        self.frames.push(Frame::ResumeReturn);
        self.state = State::EnterTemplate {
            template,
            node: template_root,
            control: HashMap::new(),
            response,
        };
        Ok(captured)
    }

    pub fn step(&mut self) -> RuntimeOutcome {
        if let State::Stopped(outcome) = &self.state {
            return outcome.clone();
        }
        self.steps = self.steps.saturating_add(1);
        let state = std::mem::replace(&mut self.state, State::Stopped(RuntimeOutcome::Running));
        let result = match state {
            State::Evaluate { code, environment } => self.evaluate(code, environment),
            State::Return(value) => self.return_value(value),
            State::EnterTemplate {
                template,
                node,
                control,
                response,
            } => self.enter_template(template, node, control, response),
            State::Request(request) => {
                #[cfg(test)]
                self.r312_record_request(&request);
                #[cfg(test)]
                self.r312_record_pending_callee_frames(&request);
                self.propagate_request(request)
            }
            State::IntegerProduct { product, site } => self.advance_integer_product(product, site),
            State::Stopped(_) => unreachable!(),
        };
        if let Err(error) = result {
            self.pending_name_entry = None;
            self.name_entry_return_token = None;
            self.pending_name_observation = None;
            self.pending_name_return_observation = None;
            self.state = State::Stopped(RuntimeOutcome::Unavailable(error));
        }
        self.finish_name_receipt_observation();
        match &self.state {
            State::Stopped(outcome) => outcome.clone(),
            _ => RuntimeOutcome::Running,
        }
    }

    #[cfg(test)]
    fn r312_record_request(&mut self, request: &PendingRequest) {
        if !request.suffix.is_empty() { return; }
        if self.r312_frame_events.len() >= 1024
            || self.r312_frame_events.try_reserve(1).is_err()
        {
            self.r312_observations_truncated = true;
            return;
        }
        let order = self.r312_next_order();
        self.r312_frame_events.push(R312FrameEvent::RequestObserved {
            step: self.steps,
            order,
            request: request.event,
            site: request.source.clone(),
            owner: self.current_execution_owner(),
        });
        if self.r323_request_observations.len() < 1024
            && self.r323_request_observations.try_reserve(1).is_ok()
        {
            self.r323_request_observations.push(R323RequestObservation {
                run_id: self as *const Machine as usize,
                request: request.event,
                declaration: request.declaration.clone(),
                payload: request.payload,
                source: request.source.clone(),
                owner: self.current_execution_owner(),
                owner_live: self.owner_active(self.current_execution_owner()),
            });
        } else {
            self.r312_observations_truncated = true;
        }
    }

    #[cfg(test)]
    fn r312_record_pending_callee_frames(&mut self, request: &PendingRequest) {
        if !request.suffix.is_empty() { return; }
        for index in 0..self.frames.len() {
            let (frame_id, callee, argument, environment, site) = match &self.frames[index] {
                Frame::Callee { frame_id, callee, argument, environment, site } =>
                    (*frame_id, *callee, *argument, *environment, site.clone()),
                _ => continue,
            };
            if self.r312_frame_events.len() >= 1024
                || self.r312_frame_events.try_reserve(1).is_err()
            {
                self.r312_observations_truncated = true;
                return;
            }
            let order = self.r312_next_order();
            self.r312_frame_events.push(R312FrameEvent::PendingCalleeAtRequest {
                step: self.steps,
                order,
                request: request.event,
                frame_id,
                request_site: request.source.clone(),
                owner: self.current_execution_owner(),
                apply_site: site,
                callee,
                argument,
                environment,
            });
        }
    }

    #[cfg(test)]
    fn r312_next_order(&mut self) -> usize {
        let order = self.r312_order;
        self.r312_order = self.r312_order.saturating_add(1);
        order
    }

    #[cfg(test)]
    fn r313_new_frame_id(&mut self) -> usize {
        let frame_id = self.r313_next_frame_id;
        self.r313_next_frame_id = self.r313_next_frame_id.saturating_add(1);
        frame_id
    }

    fn evaluate(&mut self, label: Label, environment: usize) -> Result<(), RuntimeUnavailable> {
        let code = self
            .program
            .code
            .get(label.0)
            .cloned()
            .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
        let site = &code.site;
        match &code.instruction {
            Instruction::Unit => self.ground_data(site, RuntimeValueKind::Unit, None),
            Instruction::Integer(text) => self.ground_data(
                site,
                RuntimeValueKind::Integer(
                    literal::integer(text)
                        .ok_or_else(|| RuntimeUnavailable::LiteralDecoding(site.clone()))?,
                ),
                None,
            ),
            Instruction::Boolean(value) => {
                self.ground_data(site, RuntimeValueKind::Boolean(*value), None)
            }
            Instruction::String(text) => self.ground_data(
                site,
                RuntimeValueKind::String(
                    literal::string(text)
                        .ok_or_else(|| RuntimeUnavailable::LiteralDecoding(site.clone()))?,
                ),
                None,
            ),
            Instruction::DecodedString(text) => self.ground_data(site, RuntimeValueKind::String(text.clone()), None),
            Instruction::Primitive(operation) => self.data(
                site,
                RuntimeValueKind::Primitive(operation.clone()),
                Some(ExecutableValue::Primitive { operation: operation.clone(), arguments: Vec::new() }),
            ),
            Instruction::Record { fields } => {
                if let Some((_, first)) = fields.first() {
                    let first = *first;
                    self.frames.push(Frame::Record { record: code, next: 1, environment, prefix: None });
                    self.state = State::Evaluate { code: first, environment };
                } else {
                    self.data(site, RuntimeValueKind::Record(Vec::new()), None);
                }
            }
            Instruction::Tuple { elements } | Instruction::Variant { payloads: elements, .. } => {
                if let Some(first) = elements.first().copied() {
                    self.frames.push(Frame::Tuple {
                        tuple: code,
                        next: 1,
                        environment,
                        prefix: None,
                    });
                    self.state = State::Evaluate { code: first, environment };
                } else {
                    let value = match &code.instruction {
                        Instruction::Variant { tag, .. } => RuntimeValueKind::Variant { tag: tag.clone(), payloads: Vec::new() },
                        _ => RuntimeValueKind::Tuple(Vec::new()),
                    };
                    self.data(site, value, None);
                }
            }
            Instruction::FieldTail { receiver, .. } if self.program.dictionaries.is_some() => {
                let word = self.dispatch.word(self.environments[environment].dispatch)?;
                let key = dispatch::Site { owner: site.source_root.clone(), occurrence: site.occurrence.clone() };
                let callee = *self.program.dictionaries.as_ref().unwrap().get(&(word, key.clone()))
                    .ok_or_else(|| RuntimeUnavailable::UnsupportedFieldTail(site.clone()))?;
                let entered = self.dispatch_environment(environment, dispatch::Step { kind: dispatch::Kind::Member, site: key })?;
                #[cfg(test)]
                let frame_id = self.r313_new_frame_id();
                self.frames.push(Frame::Callee {
                    #[cfg(test)] frame_id,
                    callee: None, argument: *receiver, environment, site: site.clone(),
                });
                self.state = State::Evaluate { code: callee, environment: entered };
            }
            Instruction::FieldTail { .. } => {
                // Only exact candidate-retained abstract constraints survive
                // construction. Execution requires a concrete selection; no
                // runtime value tag supplies a missing dictionary.
                return Err(RuntimeUnavailable::UnsupportedFieldTail(site.clone()));
            }
            Instruction::OperatorApplication { left, right, key } if self.program.dictionaries.is_some() => {
                let callee = *self.program.operator_bodies.get(key).ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                let entered = self.dispatch_environment(environment, dispatch::Step {
                    kind: dispatch::Kind::Operator,
                    site: dispatch::Site { owner: site.source_root.clone(), occurrence: site.occurrence.clone() },
                })?;
                if let Some(right) = right {
                    #[cfg(test)]
                    let frame_id = self.r313_new_frame_id();
                    self.frames.push(Frame::Callee {
                        #[cfg(test)] frame_id,
                        callee: None, argument: *right, environment, site: site.clone(),
                    });
                }
                #[cfg(test)]
                let frame_id = self.r313_new_frame_id();
                self.frames.push(Frame::Callee {
                    #[cfg(test)] frame_id,
                    callee: None, argument: *left, environment, site: site.clone(),
                });
                self.state = State::Evaluate { code: callee, environment: entered };
            }
            Instruction::OperatorApplication { .. } => {
                return Err(RuntimeUnavailable::InvalidSourceReference);
            }
            Instruction::Forward(inner) => {
                self.state = State::Evaluate {
                    code: *inner,
                    environment,
                }
            }
            Instruction::Name {
                resolution,
                consumption,
            } => {
                let cell = match resolution {
                    LocalSourceResolution::ModuleDef(id) => {
                        let cell = self.program.definition_indices.get(id).copied();
                        #[cfg(test)]
                        if id.spelling() == "make" {
                            if self.r315_module_uses.len() < 1024
                                && self.r315_module_uses.try_reserve(1).is_ok()
                            {
                                self.r315_module_uses.push(R315ModuleUse {
                                    step: self.steps,
                                    code: label.0,
                                    site: site.clone(),
                                    owner: self.current_execution_owner(),
                                    environment,
                                    definition: id.clone(),
                                    cell: cell.ok_or(RuntimeUnavailable::InvalidSourceReference)?,
                                    consumption: *consumption,
                                });
                            }
                        }
                        cell
                    }
                    LocalSourceResolution::Parameter(id) => {
                        self.lookup(environment, |binder| {
                            matches!(binder, Binder::Parameter(candidate) if candidate == id)
                        })
                    }
                    LocalSourceResolution::Local(id) => {
                        self.lookup(environment, |binder| {
                            matches!(binder, Binder::Local(candidate) if candidate == id)
                        })
                    }
                    LocalSourceResolution::CatchBinder(id) => {
                        self.lookup(environment, |binder| {
                            matches!(binder, Binder::Catch(candidate) if candidate == id)
                        })
                    }
                    LocalSourceResolution::CaseBinder(id) => {
                        self.lookup(environment, |binder| {
                            matches!(binder, Binder::Catch(candidate) if candidate == id)
                        })
                    }
                    LocalSourceResolution::Imported(_)
                    | LocalSourceResolution::Unresolved
                    | LocalSourceResolution::Ambiguous => None,
                }
                .ok_or_else(|| RuntimeUnavailable::MissingBinding(site.clone()))?;
                if let Some(received) = self.cells[cell] {
                    let execution_owner = self.current_execution_owner();
                    #[cfg(test)]
                    if let LocalSourceResolution::Parameter(parameter) = resolution
                    {
                        if self.r312_name_lookups.len() >= 1024
                            || self.r312_name_lookups.try_reserve(1).is_err()
                        {
                            self.r312_observations_truncated = true;
                            self.r312_pending_name_lookup = None;
                        } else {
                            let index = self.r312_name_lookups.len();
                            let order = self.r312_next_order();
                            self.r312_name_lookups.push(R312NameLookup {
                                step: self.steps,
                                order,
                                code: label.0,
                                site: site.clone(),
                                owner: execution_owner,
                                environment,
                                parameter: parameter.clone(),
                                cell,
                                value: received.value,
                                view: received.view,
                                consumption: *consumption,
                            });
                            self.r312_pending_name_lookup = Some(index);
                        }
                    }
                    if *consumption == NameConsumption::Observe {
                        let resolution_kind = match resolution {
                            LocalSourceResolution::Parameter(_) => "Parameter",
                            LocalSourceResolution::Local(_) => "Local",
                            _ => "Other",
                        };
                        self.pending_name_observation = Some(PendingNameObservation {
                            resolution: resolution_kind,
                            site: site.clone(),
                            cell,
                        });
                        if let (LocalSourceResolution::Parameter(parameter),
                            ExecutionOwner::Invocation(invocation)) = (resolution, execution_owner)
                        {
                            self.pending_name_entry = Some(PendingNameEntry {
                                invocation,
                                site: site.clone(),
                                source_parameter: parameter.clone(),
                                source_cell: cell,
                                value: received.value,
                                view: received.view,
                                cells_before_bind: self.cells.len(),
                                receipt_index: None,
                            });
                        }
                    }
                    if let (Some(plan), Some(trace)) =
                        (&self.program.operation_v1, &mut self.operation_v1_trace)
                    {
                        if plan.local_lineage.as_ref().is_some_and(|lineage|
                            site.occurrence == lineage.name_use.occurrence)
                            && matches!(resolution,
                                LocalSourceResolution::Local(id)
                                    if plan.local_lineage.as_ref().is_some_and(|lineage|
                                        id == &lineage.binding))
                        {
                            trace.read_local_cell = Some((
                                cell,
                                received.value,
                                execution_owner,
                            ));
                        }
                        if site.occurrence == plan.response_argument.occurrence
                            && matches!(resolution,
                                LocalSourceResolution::Local(id)
                                    if id == &plan.link.response_definition)
                        {
                            trace.response_definition_read =
                                Some((received.value, environment, site.clone()));
                        }
                    }
                    let received = self.dispatch_name(received, cell, environment, site)?;
                    self.consume(received, *consumption, site)?;
                } else if matches!(resolution, LocalSourceResolution::ModuleDef(_)) {
                    if !self.initializing_globals.insert(cell) {
                        return Err(RuntimeUnavailable::RecursiveDefinitionInitialization(
                            site.clone(),
                        ));
                    }
                    self.frames.push(Frame::GlobalRead {
                        cell,
                        consumption: *consumption,
                        site: site.clone(),
                        environment,
                    });
                    let environment = self.initializer_environment(cell, 0)?;
                    self.state = State::Evaluate {
                        code: self.program.definitions[cell].body,
                        environment,
                    };
                } else {
                    return Err(RuntimeUnavailable::UninitializedBinding(site.clone()));
                }
            }
            Instruction::Lambda {
                source_permission_row: _,
                parameter,
                unit_pattern,
                record_pattern,
                role,
                root_schema,
                callback_schema,
                body,
            } => {
                self.data(
                    site,
                    RuntimeValueKind::Closure,
                    Some(ExecutableValue::Closure {
                        parameter: parameter.clone(),
                        unit_pattern: *unit_pattern,
                        record_pattern: record_pattern.clone(),
                        role: *role,
                        root_schema: root_schema.clone(),
                        callback_schema: callback_schema.clone(),
                        body: *body,
                        environment,
                    }),
                );
            }
            Instruction::Apply { callee, argument } => {
                #[cfg(test)]
                let frame_id = self.r313_new_frame_id();
                self.frames.push(Frame::Callee {
                    #[cfg(test)] frame_id,
                    callee: Some(*callee),
                    argument: *argument,
                    environment,
                    site: site.clone(),
                });
                self.state = State::Evaluate {
                    code: *callee,
                    environment,
                };
            }
            Instruction::Block { .. } | Instruction::StatementBlock { .. } => self.begin_local(code, 0, environment)?,
            Instruction::Sequence { items } => {
                let Some(first) = items.first().copied() else {
                    return Err(RuntimeUnavailable::InvalidSourceReference);
                };
                self.frames.push(Frame::Sequence { sequence: code, next: 1, environment });
                self.state = State::Evaluate { code: first, environment };
            }
            Instruction::If { arms, else_branch } => {
                if let Some((test, _)) = arms.first() {
                    let test = *test;
                    self.frames.push(Frame::Condition {
                        conditional: code,
                        arm: 0,
                        environment,
                    });
                    self.state = State::Evaluate {
                        code: test,
                        environment,
                    };
                } else if let Some(branch) = else_branch {
                    self.state = State::Evaluate {
                        code: *branch,
                        environment,
                    };
                } else {
                    self.ground_data(site, RuntimeValueKind::Unit, None);
                }
            }
            Instruction::Case { scrutinee, .. } => {
                self.frames.push(Frame::Case {
                    case: code.clone(),
                    environment,
                });
                self.state = State::Evaluate {
                    code: *scrutinee,
                    environment,
                };
            }
            Instruction::Operation(resolution) => {
                let execution_owner = self.current_execution_owner();
                if let (Some(plan), Some(trace)) =
                    (&self.program.operation_v1, &mut self.operation_v1_trace)
                {
                    if site.occurrence == plan.request.occurrence
                        && matches!(resolution, SourceOperationResolution::Resolved(declaration)
                            if declaration.id == plan.request_operation)
                    {
                        trace.request_operation_seen = true;
                    }
                    if site.occurrence == plan.callback_operation.occurrence
                        && trace.applied_response_invocation.as_ref().is_some_and(|(apply, owner)| {
                            apply.occurrence == plan.response_invocation_apply.occurrence
                                && apply.source_root == plan.response_invocation_apply.source_root
                                && *owner == execution_owner
                        })
                        && matches!(resolution, SourceOperationResolution::Resolved(declaration)
                            if declaration.id == plan.link.callback_operation)
                    {
                        trace.callback_operation_seen = true;
                        trace.callback_operation_owner = Some(execution_owner);
                    }
                }
                self.data(site, RuntimeValueKind::Operation(resolution.clone()), None)
            }
            Instruction::Catch { scrutinee, .. } => {
                let scrutinee = *scrutinee;
                let execution_owner = self.current_execution_owner();
                if let (Some(plan), Some(trace)) =
                    (&self.program.operation_v1, &mut self.operation_v1_trace)
                {
                    if plan.local_lineage.as_ref().is_some_and(|lineage|
                        site.occurrence == lineage.initializer_catch.occurrence
                            && site.source_root == lineage.initializer_catch.source_root)
                    {
                        trace.initializer_catch_owner = Some(execution_owner);
                    }
                }
                let occurrence = self.next_handler;
                self.next_handler = occurrence
                    .checked_add(1)
                    .ok_or(RuntimeUnavailable::IdentityExhausted)?;
                let installation = HandlerInstallation {
                    occurrence,
                    owner: self.current_execution_owner(),
                };
                self.frames.push(Frame::CatchReturn {
                    handler: code,
                    environment,
                    installation,
                });
                self.state = State::Evaluate {
                    code: scrutinee,
                    environment,
                };
            }
        }
        Ok(())
    }

    fn return_value(&mut self, received: ReceivedValue) -> Result<(), RuntimeUnavailable> {
        // The token belongs only to this one return consumer. Taking it before
        // inspecting the frame prevents it crossing Sequence/Condition/etc.
        let return_token = self.name_entry_return_token.take();
        let returned_name = self.pending_name_return_observation.take();
        let Some(frame) = self.frames.pop() else {
            self.state = State::Stopped(RuntimeOutcome::Completed(received.value));
            return Ok(());
        };
        let (frame_kind, frame_invocation) = match &frame {
            Frame::ValueEntry { entry_receiver, .. } => ("ValueEntry", Some(*entry_receiver)),
            Frame::Sequence { .. } => ("Sequence", None),
            Frame::Condition { .. } => ("Condition", None),
            Frame::BlockExpression { .. } => ("BlockExpression", None),
            _ => ("Other", None),
        };
        self.name_entry_return_observations.push(NameEntryReturnObservation {
            frame: frame_kind,
            invocation: frame_invocation,
            token_receipt_index: return_token.as_ref().and_then(|p| p.receipt_index),
            token_source_parameter_ordinal: return_token.as_ref().map(|p| p.source_parameter.ordinal()),
            token_name_site_ordinal: return_token.as_ref().map(|p| p.site.occurrence.ordinal()),
            token_value: return_token.as_ref().map(|p| p.value.0),
            token_view: return_token.as_ref().map(|p| p.view.index()),
            token_cells_before_bind: return_token.as_ref().map(|p| p.cells_before_bind),
            returned_value: received.value.0,
            returned_view: received.view.index(),
            cells_at_return: self.cells.len(),
        });
        if let Some(observed) = returned_name {
            self.name_entry_name_return_observations.push(NameEntryNameReturnObservation {
                resolution: observed.resolution,
                name_site_ordinal: observed.site.occurrence.ordinal(),
                source_cell: observed.cell,
                value: observed.value.0,
                view: observed.view.index(),
                receipt_index: observed.receipt_index,
                cells_before_observe: observed.cells_before_observe,
                return_frame: frame_kind,
            });
        }
        match frame {
            Frame::ResumeArgument { template, source } => {
                if let (Some(plan), Some(trace)) =
                    (&self.program.operation_v1, &mut self.operation_v1_trace)
                {
                    let exact_definition_read = trace.response_definition_read.as_ref()
                        .is_some_and(|(value, _, read_site)| {
                            *value == received.value
                                && read_site.occurrence == plan.response_argument.occurrence
                        });
                    if received.value.0 < self.values.len()
                        && self.values[received.value.0].source.occurrence
                            == plan.response_lambda.occurrence
                        && source.occurrence == plan.continuation_apply.occurrence
                        && exact_definition_read
                    {
                        if let Some(ExecutableValue::Closure { environment, .. }) =
                            self.executables.get(&received.value.0)
                        {
                            trace.selected_closure = Some((received.value, *environment));
                        }
                    }
                }
                let SourceAnnotationValue::Function { result, .. } = &self
                    .resume_templates
                    .get(template.0)
                    .ok_or(RuntimeUnavailable::InvalidSourceReference)?
                    .declaration
                    .signature
                    .value
                else {
                    return Err(RuntimeUnavailable::ContinuationResponse(source));
                };
                let exact_v1_function_response = matches!(
                    &result.value,
                    SourceAnnotationValue::Function { .. }
                ) && self.program.operation_v1.as_ref().is_some_and(|plan| {
                    received.interface == ParameterRole::Value
                        && self.receiving.matches_value(received.view, received.value)
                        && source.occurrence == plan.continuation_apply.occurrence
                        && self.operation_v1_trace.as_ref().is_some_and(|trace| {
                            trace.response_definition_read.as_ref().is_some_and(
                                |(value, _, read_site)| {
                                    *value == received.value
                                        && read_site.occurrence == plan.response_argument.occurrence
                                },
                            )
                        })
                        && self.values.get(received.value.0).is_some_and(|value| {
                            value.source.occurrence == plan.response_lambda.occurrence
                                && value.source.source_root == plan.response_lambda.source_root
                        })
                        && matches!(self.executables.get(&received.value.0),
                            Some(ExecutableValue::Closure { .. }))
                });
                if !self.primitive_matches(&result.value, received)
                    && !exact_v1_function_response
                {
                    return Err(RuntimeUnavailable::ContinuationResponse(source));
                }
                #[cfg(test)]
                {
                    let owner = self.current_execution_owner();
                    let request = self.resume_templates[template.0].original_event;
                    if self.r323_resume_observations.len() < 1024
                        && self.r323_resume_observations.try_reserve(1).is_ok()
                    {
                        self.r323_resume_observations.push(R323ResumeObservation {
                            run_id: self as *const Machine as usize,
                            request,
                            template: template.0,
                            response: received,
                            source: source.clone(),
                            owner,
                            owner_live: self.owner_active(owner),
                            step: self.steps,
                        });
                    } else {
                        self.r312_observations_truncated = true;
                    }
                }
                self.frames.push(Frame::ResumeReturn);
                let node = self
                    .resume_templates
                    .get(template.0)
                    .ok_or(RuntimeUnavailable::InvalidSourceReference)?
                    .root;
                self.state = State::EnterTemplate {
                    template,
                    node,
                    control: HashMap::new(),
                    response: received,
                };
            }
            Frame::ResumeReturn => self.state = State::Return(received),
            Frame::OwnerReturn {
                owner,
                owned,
                previous,
            } => {
                self.leave_owner(owner, owned, previous)?;
                self.state = State::Return(received);
            }
            Frame::RootCompReturn { execution } => {
                if !self.receiving.matches_value(received.view, received.value) {
                    return Err(RuntimeUnavailable::InvalidSourceReference);
                }
                self.end_execution_view(execution)?;
                // The consumed computation root has no result-path image.
                // Its actual result retains its own view, unknown coverage,
                // private captures and dictionary; no groundness is assumed.
                self.state = State::Return(received);
            }
            Frame::CatchReturn {
                handler,
                environment,
                installation,
            } => {
                self.validate_handler_installation(installation)?;
                // Popping this delimiter leaves the shallow handler before any
                // value pattern binding or arm code executes.
                let Instruction::Catch { arms, .. } = &handler.instruction else {
                    unreachable!()
                };
                if let Some(arm) = arms
                    .iter()
                    .find(|arm| matches!(arm.pattern, LocalSourceCatchPattern::Value(_)))
                {
                    let LocalSourceCatchPattern::Value(pattern) = &arm.pattern else {
                        unreachable!()
                    };
                    let environment = match pattern {
                        LocalSourceCatchValuePattern::Binder(binder) => self.bind(
                            environment,
                            Binder::Catch(binder.id.clone()),
                            ReceivedValue {
                                dispatch: received.dispatch,
                                value: received.value,
                                interface: ParameterRole::Value,
                                view: received.view,
                            },
                        ),
                        LocalSourceCatchValuePattern::Wildcard => environment,
                    };
                    let _ = (&arm.source, &arm.range);
                    self.state = State::Evaluate {
                        code: arm.body,
                        environment,
                    };
                } else {
                    self.state = State::Return(received);
                }
            }
            Frame::OperationPayload {
                declaration,
                source,
            } => self.make_request_carrier(declaration, received, &source),
            Frame::OperationResultConsumer { source, callback_use } => {
                if let Some(callback_use) = callback_use {
                    let execution = self.receiving.callback_execution(callback_use)
                        .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                    self.executing_views.push(execution);
                    self.frames.push(Frame::RootCompReturn { execution });
                }
                self.execute_with_substitution(received.value, &source, received.dispatch)?;
            }
            Frame::DiscardToUnit { site } => self.ground_data(&site, RuntimeValueKind::Unit, None),
            Frame::PrimitiveArgument { operation, mut arguments, site } => {
                arguments.try_reserve(1).map_err(|_| RuntimeUnavailable::InvalidSourceReference)?;
                arguments.push(received.value);
                let arity = pinned_primitive_arity(&operation).ok_or_else(|| RuntimeUnavailable::InvalidSourceReference)?;
                if arguments.len() < arity {
                    self.data(
                        &site,
                        RuntimeValueKind::Primitive(operation.clone()),
                        Some(ExecutableValue::Primitive { operation, arguments }),
                    );
                } else if arguments.len() == arity {
                    if matches!(operation, yu_hir::shadow::PinnedPrimitiveOp::IntMul) {
                        let Some(RuntimeValueKind::Integer(left)) = self.values.get(arguments[0].0).map(|value| &value.kind) else {
                            return Err(RuntimeUnavailable::InvalidSourceReference);
                        };
                        let Some(RuntimeValueKind::Integer(right)) = self.values.get(arguments[1].0).map(|value| &value.kind) else {
                            return Err(RuntimeUnavailable::InvalidSourceReference);
                        };
                        let product = super::decimal::Product::new(left, right)
                            .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                        self.state = State::IntegerProduct { product, site };
                    } else {
                        let result = pinned_primitive_apply(&operation, &arguments, &self.values)
                            .ok_or_else(|| RuntimeUnavailable::InvalidSourceReference)?;
                        self.ground_data(&site, result, None);
                    }
                } else {
                    return Err(RuntimeUnavailable::InvalidSourceReference);
                }
            }
            Frame::Callee {
                #[cfg(test)]
                frame_id,
                callee,
                argument,
                environment: caller_environment,
                site,
            } => {
                // Test-only R313 evidence is captured at the actual Return
                // elimination, before this frame allocates the argument Delay
                // or selects the received closure's entry mode.
                #[cfg(test)]
                if self.r313_return_snapshot.is_none()
                    && self.r313_watch_apply.as_ref().is_some_and(|watched|
                        watched.source_root == site.source_root
                            && watched.occurrence == site.occurrence
                            && watched.range == site.range)
                {
                    let source_name_initialization = self.program.code.get(argument.0)
                        .and_then(|argument_code| match &argument_code.instruction {
                            Instruction::Name {
                                resolution: LocalSourceResolution::Parameter(parameter),
                                consumption: NameConsumption::Observe,
                            } => self.lookup(caller_environment, |binder| matches!(binder,
                                Binder::Parameter(candidate) if candidate == parameter))
                                .and_then(|cell| self.cells.get(cell).copied().flatten()
                                    .map(|received| R313SourceNameInitialization {
                                        parameter: parameter.clone(), cell, received,
                                    })),
                            _ => None,
                        });
                    let mut receiving_views = Vec::new();
                    let mut receiving_image_chains = Vec::new();
                    let mut receiving_scan_truncated = true;
                    for index in 0..4096 {
                        let Some(fields) = self.receiving.raw_view_fields(index) else {
                            receiving_scan_truncated = false;
                            break;
                        };
                        receiving_views.push(fields);
                        receiving_image_chains.push(self.receiving
                            .bounded_raw_image_chain(index)
                            .map_or_else(|error| format!("error:{error:?}"), |chain| chain));
                    }
                    self.r313_return_snapshot = Some(R313CalleeReturnSnapshot {
                        frame_id,
                        apply_site: site.clone(),
                        argument_code: argument,
                        caller_environment,
                        source_name_initialization,
                        cells: self.cells.clone(),
                        environments: self.environments.clone(),
                        values: self.values.clone(),
                        receiving_views,
                        receiving_image_chains,
                        receiving_scan_truncated,
                    });
                }
                #[cfg(test)]
                if self.r312_frame_events.len() < 1024
                    && self.r312_frame_events.try_reserve(1).is_ok()
                {
                    let order = self.r312_next_order();
                    self.r312_frame_events.push(R312FrameEvent::CalleeReturned {
                        step: self.steps,
                        order,
                        frame_id,
                        owner: self.current_execution_owner(),
                        apply_site: site.clone(),
                        callee,
                        argument,
                        environment: caller_environment,
                        value: received.value,
                        view: received.view,
                        interface: received.interface,
                        dispatch: received.dispatch,
                        provider: self.values[received.value.0].source.clone(),
                    });
                } else {
                    #[cfg(test)]
                    { self.r312_observations_truncated = true; }
                }
                // This allocates only inert code plus lexical references. No
                // argument prefix runs before the receiver entry is selected.
                let delay = self.allocate(
                    &site,
                    RuntimeValueKind::Computation,
                    Some(ExecutableValue::Delay {
                        code: argument,
                        environment: caller_environment,
                    }),
                );
                let inherited = self.direct_formal_root(argument, caller_environment);
                let delay_view = self.receiving.delay(delay, inherited);
                let executable = self.executables.get(&received.value.0).cloned();
                match executable {
                    Some(ExecutableValue::Primitive { operation, arguments }) => {
                        // This actual primitive receives a Value argument. Its
                        // invocation owns the force, including a suspended raw
                        // suffix, just like an ordinary Value-entry closure.
                        let provider = self.values[received.value.0].source.clone();
                        let (activation, previous) = self.new_invocation(site.clone(), provider)?;
                        self.frames.push(Frame::ReceiverReturn { activation, previous });
                        self.frames.push(Frame::PrimitiveArgument { operation, arguments, site: site.clone() });
                        self.execute(delay, &site)?;
                    }
                    Some(ExecutableValue::Continuation(template)) => {
                        let provider = self.values[received.value.0].source.clone();
                        let (activation, previous) = self.new_invocation(site.clone(), provider)?;
                        self.frames.push(Frame::ReceiverReturn {
                            activation,
                            previous,
                        });
                        self.frames.push(Frame::ResumeArgument {
                            template,
                            source: site.clone(),
                        });
                        self.execute(delay, &site)?;
                    }
                    Some(ExecutableValue::Closure {
                        parameter,
                        unit_pattern,
                        record_pattern,
                        role,
                        root_schema,
                        callback_schema,
                        body,
                        environment,
                    }) => {
                        let exact_response_invocation = self
                            .program
                            .operation_v1
                            .as_ref()
                            .is_some_and(|plan| {
                                site.occurrence == plan.response_invocation_apply.occurrence
                                    && site.source_root == plan.response_invocation_apply.source_root
                            })
                            && self.operation_v1_trace.as_ref().is_some_and(|trace| {
                                trace.selected_closure.is_some_and(|(value, saved_environment)| {
                                    value == received.value && saved_environment == environment
                                })
                            });
                        let provider = self.values[received.value.0].source.clone();
                        let (activation, previous) = self.new_invocation(site.clone(), provider)?;
                        if self.name_receipt_calls.len() == 64 {
                            self.name_receipt_calls_truncated = true;
                        } else if self.name_receipt_calls.try_reserve(1).is_err() {
                            self.name_receipt_observation_unavailable = true;
                        } else {
                            #[cfg(test)]
                            let selected_order = self.r312_next_order();
                            self.name_receipt_calls.push(NameReceiptCallObservation {
                                call_site: site.clone(),
                                #[cfg(test)]
                                callee_code: callee.map(|label| label.0),
                                invocation: activation,
                                previous_owner: previous,
                                callee_value: received.value,
                                callee_view: received.view,
                                #[cfg(test)]
                                callee_interface: received.interface,
                                #[cfg(test)]
                                callee_dispatch: received.dispatch,
                                callee_site: self.values[received.value.0].source.clone(),
                                formal: parameter.clone(),
                                closure_environment: environment,
                                argument_environment: caller_environment,
                                delay_value: delay,
                                argument_code: argument.0,
                                delay_view,
                                #[cfg(test)]
                                selected_step: self.steps,
                                #[cfg(test)]
                                selected_order,
                            });
                        }
                        if let (Some(plan), Some(trace)) =
                            (&self.program.operation_v1, &mut self.operation_v1_trace)
                        {
                            if plan.local_lineage.as_ref().is_some_and(|lineage|
                                site.occurrence == lineage.apply.occurrence)
                                && trace.installed_local_cell.is_some_and(
                                    |(cell, value, saved_environment, install_owner)| {
                                        value == received.value
                                            && saved_environment == environment
                                            && trace.read_local_cell.is_some_and(
                                                |(read_cell, read_value, read_owner)| {
                                                    read_cell == cell
                                                        && read_value == value
                                                        && read_owner == install_owner
                                                },
                                            )
                                    },
                                )
                            {
                                trace.local_invocation_owner =
                                    Some(ExecutionOwner::Invocation(activation));
                            }
                        }
                        if exact_response_invocation {
                            if let Some(trace) = &mut self.operation_v1_trace {
                                trace.applied_response_invocation = Some((
                                    site.clone(),
                                    ExecutionOwner::Invocation(activation),
                                ));
                            }
                        }
                        let environment = self.substitute_environment(environment, received.dispatch)?;
                        self.frames.push(Frame::ReceiverReturn {
                            activation,
                            previous,
                        });
                        match role {
                            ParameterRole::Value => {
                                self.frames.push(Frame::ValueEntry {
                                    parameter,
                                    callback_schema,
                                    entry_receiver: activation,
                                    unit_pattern,
                                    record_pattern,
                                    body,
                                    environment,
                                });
                                self.execute(delay, &site)?;
                            }
                            ParameterRole::Computation => {
                                let view = if let Some(schema) = root_schema {
                                    let view = self.receiving.enter(
                                        delay,
                                        delay_view,
                                        activation,
                                        schema.clone(),
                                    );
                                    self.receiving.receipt(
                                        ExecutionOwner::Invocation(activation),
                                        view,
                                        &schema.lambda,
                                        Some(parameter.clone()),
                                    );
                                    view
                                } else {
                                    delay_view
                                };
                                let environment = self.bind(
                                    environment,
                                    Binder::Parameter(parameter),
                                    ReceivedValue {
                                        dispatch: None,
                                        value: delay,
                                        interface: ParameterRole::Computation,
                                        view,
                                    },
                                );
                                self.state = State::Evaluate {
                                    code: body,
                                    environment,
                                };
                            }
                        }
                    }
                    _ if matches!(
                        &self.values[received.value.0].kind,
                        RuntimeValueKind::Operation(_)
                    ) =>
                    {
                        let RuntimeValueKind::Operation(SourceOperationResolution::Resolved(
                            declaration,
                        )) = &self.values[received.value.0].kind
                        else {
                            return Err(RuntimeUnavailable::UnresolvedOperation(site));
                        };
                        let declaration = declaration.clone();
                        if declaration.signature.effects.is_some() {
                            return Err(RuntimeUnavailable::OperationConsumer(site));
                        }
                        let SourceAnnotationValue::Function { argument, result } =
                            &declaration.signature.value
                        else {
                            return Err(RuntimeUnavailable::OperationConsumer(site));
                        };
                        let role = if argument.effects.is_some() {
                            ParameterRole::Computation
                        } else {
                            ParameterRole::Value
                        };
                        let callback_use = if role == ParameterRole::Value
                            && argument.effects.is_none()
                            && matches!(argument.value, SourceAnnotationValue::Unit)
                            && result.effects.is_none()
                            && matches!(result.value, SourceAnnotationValue::Int)
                        {
                            let source_formal = callee.and_then(|callee| {
                                let code = self.program.code.get(callee.0)?;
                                let Instruction::Name {
                                    resolution: LocalSourceResolution::Parameter(formal),
                                    consumption: NameConsumption::Observe,
                                } = &code.instruction else { return None; };
                                self.receiving.callback_entry_for_apply(
                                    received.value,
                                    received.view,
                                    formal,
                                    self.current_execution_owner(),
                                    &code.site,
                                )
                            });
                            source_formal.and_then(|entry| {
                                self.receiving.callback_use(
                                    entry,
                                    received.value,
                                    received.view,
                                    &site,
                                    self.current_execution_owner(),
                                )
                            })
                        } else {
                            None
                        };
                        let provider = self.values[received.value.0].source.clone();
                        let (activation, previous) = self.new_invocation(site.clone(), provider)?;
                        // The declared source consumer runs after native return.
                        // Its authority comes from the operation declaration,
                        // including when the written result effect row is absent.
                        self.frames.push(Frame::OperationResultConsumer {
                            source: site.clone(),
                            callback_use,
                        });
                        self.frames.push(Frame::ReceiverReturn {
                            activation,
                            previous,
                        });
                        match role {
                            ParameterRole::Value => {
                                self.frames.push(Frame::OperationPayload {
                                    declaration,
                                    source: site.clone(),
                                });
                                self.execute(delay, &site)?;
                            }
                            ParameterRole::Computation => self.make_request_carrier(
                                declaration,
                                ReceivedValue {
                                    dispatch: None,
                                    value: delay,
                                    interface: ParameterRole::Computation,
                                    view: delay_view,
                                },
                                &site,
                            ),
                        }
                    }
                    _ => return Err(RuntimeUnavailable::ExpectedCallable(site)),
                }
            }
            Frame::ReceiverReturn {
                activation,
                previous,
            } => {
                self.leave_owner(ExecutionOwner::Invocation(activation), true, previous)?;
                self.state = State::Return(ReceivedValue {
                    dispatch: received.dispatch,
                    value: received.value,
                    interface: ParameterRole::Value,
                    view: received.view,
                });
            }
            Frame::ValueEntry {
                parameter,
                callback_schema,
                entry_receiver,
                unit_pattern,
                record_pattern,
                body,
                environment,
            } => {
                let ordinary_entry = callback_schema.is_none()
                    && !unit_pattern
                    && record_pattern.is_none();
                let received = if let Some(schema) = callback_schema {
                    let owner = ExecutionOwner::Invocation(entry_receiver);
                    if unit_pattern
                        || record_pattern.is_some()
                        || self.current_execution_owner() != owner
                        || schema.formal.id != parameter
                        || schema.formal.id.source_root() != &schema.lambda.source_root
                        || received.interface != ParameterRole::Value
                    {
                        return Err(RuntimeUnavailable::InvalidSourceReference);
                    }
                    let (view, _) = self.receiving.callback_entry(
                        schema,
                        owner,
                        received.value,
                        received.view,
                    ).ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                    ReceivedValue { interface: ParameterRole::Value, view, ..received }
                } else {
                    received
                };
                if let Some(fields) = record_pattern {
                    return self.bind_record_parameter(fields, 0, received, body, environment);
                }
                #[cfg(test)]
                if ordinary_entry {
                    let completed = self.r312_active_forces.iter().filter_map(|(lookup, pending)| {
                        let ExecutionOwner::Invocation(owner) = pending.owner else { return None; };
                        (owner == entry_receiver
                            && self.name_receipt_calls.iter().any(|call|
                                call.invocation == owner && call.formal == parameter))
                            .then_some(*lookup)
                    }).collect::<Vec<_>>();
                    for lookup in completed {
                        let Some(pending) = self.r312_active_forces.remove(&lookup) else { continue; };
                        if self.r312_name_force_completions.len() >= 1024
                            || self.r312_name_force_completions.try_reserve(1).is_err()
                        {
                            self.r312_observations_truncated = true;
                        } else {
                            let order = self.r312_next_order();
                            self.r312_name_force_completions.push(R312NameForceCompletion {
                                lookup: pending.lookup,
                                receipt: pending.receipt,
                                step: self.steps,
                                order,
                                owner: pending.owner,
                                return_owner: self.current_execution_owner(),
                                entry_receiver,
                                parameter: parameter.clone(),
                                site: pending.site,
                                input_view: pending.view,
                                input_value: pending.value,
                                output_view: received.view,
                                output_value: received.value,
                            });
                        }
                    }
                }
                let bound_cell = self.cells.len();
                let returned_value_origin_site = self.values[received.value.0].source.clone();
                #[cfg(test)]
                let r313_bind_before = ordinary_entry.then(|| {
                    let parent = &self.environments[environment];
                    (
                        environment,
                        parent.parent,
                        parent.binder.clone(),
                        format!("{:?}", parent.dispatch),
                        self.cells.len(),
                        self.environments.len(),
                        received,
                    )
                });
                let environment = if unit_pattern {
                    if !self.value(received.value).is_some_and(|value| matches!(value.kind, RuntimeValueKind::Unit)) {
                        return Err(RuntimeUnavailable::InvalidSourceReference);
                    }
                    environment
                } else { self.bind(
                    environment,
                    Binder::Parameter(parameter.clone()),
                    ReceivedValue {
                        dispatch: received.dispatch,
                        value: received.value,
                        interface: ParameterRole::Value,
                        view: received.view,
                    },
                ) };
                #[cfg(test)]
                if let Some((binder_parent_environment, binder_parent, binder_at_parent,
                    parent_dispatch, cells_before_bind, environments_before_bind, received_before_bind)) = r313_bind_before
                {
                    if self.r313_value_entry_binds.len() >= 1024
                        || self.r313_value_entry_binds.try_reserve(1).is_err()
                    {
                        self.r312_observations_truncated = true;
                    } else {
                        let order = self.r312_next_order();
                        self.r313_value_entry_binds.push(R313ValueEntryBind {
                            step: self.steps,
                            order,
                            entry_receiver,
                            parameter: parameter.clone(),
                            binder_parent_environment,
                            binder_parent,
                            binder_at_parent,
                            parent_dispatch,
                            cells_before_bind,
                            environments_before_bind,
                            received: received_before_bind,
                            bound_cell,
                            bound_environment: environment,
                            cells_after_bind: self.cells.len(),
                            environments_after_bind: self.environments.len(),
                        });
                    }
                }
                if ordinary_entry {
                    let owner_matches = self.current_execution_owner()
                        == ExecutionOwner::Invocation(entry_receiver);
                    let bound_matches = self.cells.get(bound_cell).is_some_and(|cell|
                        cell.is_some_and(|bound| bound.value == received.value
                            && bound.view == received.view
                            && bound.interface == ParameterRole::Value));
                    let token_accepted = owner_matches && bound_matches
                        && return_token.as_ref().is_some_and(|pending|
                            pending.invocation == entry_receiver
                                && pending.cells_before_bind == bound_cell
                                && pending.value == received.value
                                && pending.view == received.view
                                && pending.receipt_index.is_some());
                    self.name_entry_value_entry_attempts.push(NameEntryValueEntryAttempt {
                        invocation: entry_receiver,
                        entry_parameter_ordinal: parameter.ordinal(),
                        value: received.value.0,
                        view: received.view.index(),
                        cells_before_bind: bound_cell,
                        bound_cell,
                        cells_after_bind: self.cells.len(),
                        token_receipt_index: return_token.as_ref().and_then(|p| p.receipt_index),
                        token_source_parameter_ordinal: return_token.as_ref().map(|p| p.source_parameter.ordinal()),
                        token_name_site_ordinal: return_token.as_ref().map(|p| p.site.occurrence.ordinal()),
                        token_accepted,
                    });
                    if token_accepted {
                        if let Some(pending) = return_token {
                            self.name_entry_trace = Some(NameEntryCorrespondenceTrace {
                                invocation: entry_receiver,
                                name_site: pending.site,
                                returned_value_origin_site,
                                source_parameter: pending.source_parameter,
                                entry_parameter: parameter,
                                source_cell: pending.source_cell,
                                value: received.value.0,
                                view: received.view.index(),
                                receipt_index: pending.receipt_index.unwrap(),
                                cells_before_bind: pending.cells_before_bind,
                                bound_cell,
                                cells_after_bind: self.cells.len(),
                            });
                        }
                    }
                }
                self.state = State::Evaluate {
                    code: body,
                    environment,
                };
            }
            Frame::RecordDefault { fields, index, argument, body, environment } => {
                let view = self.receiving.project_record(argument.view, received.view, received.value)
                    .ok_or_else(|| RuntimeUnavailable::UnsupportedRecordPattern(self.values[argument.value.0].source.clone()))?;
                let environment = self.bind(environment, Binder::Parameter(fields[index].binder.clone()),
                    ReceivedValue { view, interface: ParameterRole::Value, ..received });
                self.bind_record_parameter(fields, index + 1, argument, body, environment)?;
            }
            Frame::Local {
                block,
                next,
                environment,
                cell,
                recursive,
            } => {
                let execution_owner = self.current_execution_owner();
                let binding = match &block.instruction {
                    Instruction::Block { bindings, .. } => bindings
                        .get(next - 1)
                        .ok_or(RuntimeUnavailable::InvalidSourceReference)?,
                    Instruction::StatementBlock { statements, .. } => match statements.get(next - 1) {
                        Some(BlockStatement::Binding(binding)) => binding,
                        _ => return Err(RuntimeUnavailable::InvalidSourceReference),
                    },
                    _ => return Err(RuntimeUnavailable::InvalidSourceReference),
                };
                if let (Some(plan), Some(trace)) =
                    (&self.program.operation_v1, &mut self.operation_v1_trace)
                {
                    if plan.local_lineage.as_ref().is_some_and(|lineage|
                        binding.id == lineage.binding)
                    {
                        let lineage = plan.local_lineage.as_ref()
                            .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                        let initializer_site = self.program.code.get(binding.initializer.0)
                            .ok_or(RuntimeUnavailable::InvalidSourceReference)?
                            .site.clone();
                        let closure_environment = match self.executables.get(&received.value.0) {
                            Some(ExecutableValue::Closure { environment, .. }) => *environment,
                            _ => return Err(RuntimeUnavailable::InvalidSourceReference),
                        };
                        if initializer_site.occurrence == lineage.initializer_catch.occurrence
                            && trace.initializer_catch_owner == Some(execution_owner)
                        {
                            trace.installed_local_cell = Some((
                                cell,
                                received.value,
                                closure_environment,
                                execution_owner,
                            ));
                        }
                    }
                }
                self.cells[cell] = Some(ReceivedValue {
                    dispatch: received.dispatch,
                    value: received.value,
                    interface: ParameterRole::Value,
                    view: received.view,
                });
                let local = binding.id.clone();
                let environment = if recursive {
                    environment
                } else {
                    self.extend(
                        environment,
                        Binder::Local(local),
                        cell,
                    )
                };
                self.begin_local(block, next, environment)?;
            }
            Frame::Condition {
                conditional,
                arm,
                environment,
            } => {
                let RuntimeValueKind::Boolean(condition) = &self.values[received.value.0].kind
                else {
                    return Err(RuntimeUnavailable::ExpectedBoolean(
                        conditional.site.clone(),
                    ));
                };
                let Instruction::If { arms, else_branch } = &conditional.instruction else {
                    unreachable!()
                };
                if *condition {
                    if else_branch.is_none() {
                        self.frames.push(Frame::DiscardToUnit {
                            site: conditional.site.clone(),
                        });
                    }
                    self.state = State::Evaluate {
                        code: arms[arm].1,
                        environment,
                    };
                } else if let Some((test, _)) = arms.get(arm + 1) {
                    let test = *test;
                    self.state = State::Evaluate {
                        code: test,
                        environment,
                    };
                    self.frames.push(Frame::Condition {
                        conditional,
                        arm: arm + 1,
                        environment,
                    });
                } else if let Some(branch) = else_branch {
                    self.state = State::Evaluate {
                        code: *branch,
                        environment,
                    };
                } else {
                    self.ground_data(&conditional.site, RuntimeValueKind::Unit, None);
                }
            }
            Frame::BlockExpression { block, next, environment } => {
                self.begin_local(block, next, environment)?;
            }
            Frame::Sequence { sequence, next, environment } => {
                let Instruction::Sequence { items } = &sequence.instruction else {
                    unreachable!()
                };
                if let Some(item) = items.get(next).copied() {
                    self.frames.push(Frame::Sequence { sequence, next: next + 1, environment });
                    self.state = State::Evaluate { code: item, environment };
                } else {
                    self.state = State::Return(received);
                }
            }
            Frame::Record { record, next, environment, prefix: previous } => {
                let prefix = self.tuple_prefixes.len();
                self.tuple_prefixes.push(TuplePrefix { previous, received });
                let Instruction::Record { fields } = &record.instruction else { unreachable!() };
                if let Some((_, element)) = fields.get(next) {
                    let element = *element;
                    self.frames.push(Frame::Record { record, next: next + 1, environment, prefix: Some(prefix) });
                    self.state = State::Evaluate { code: element, environment };
                } else {
                    let mut reversed = Vec::with_capacity(fields.len());
                    let mut cursor = Some(prefix);
                    while let Some(index) = cursor {
                        let node = self.tuple_prefixes.get(index).ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                        reversed.push(TupleElement { received: node.received });
                        cursor = node.previous;
                    }
                    if reversed.len() != fields.len() { return Err(RuntimeUnavailable::InvalidSourceReference); }
                    reversed.reverse();
                    let value = fields.iter().map(|(label, _)| label.clone()).zip(reversed).collect();
                    self.data(&record.site, RuntimeValueKind::Record(value), None);
                }
            }
            Frame::Tuple { tuple, next, environment, prefix: previous } => {
                let prefix = self.tuple_prefixes.len();
                self.tuple_prefixes.push(TuplePrefix {
                    previous,
                    received,
                });
                let elements = match &tuple.instruction {
                    Instruction::Tuple { elements } | Instruction::Variant { payloads: elements, .. } => elements,
                    _ => unreachable!(),
                };
                if let Some(element) = elements.get(next).copied() {
                    self.frames.push(Frame::Tuple {
                        tuple,
                        next: next + 1,
                        environment,
                        prefix: Some(prefix),
                    });
                    self.state = State::Evaluate { code: element, environment };
                } else {
                    let mut reversed = Vec::with_capacity(elements.len());
                    let mut cursor = Some(prefix);
                    while let Some(index) = cursor {
                        let node = self.tuple_prefixes.get(index)
                            .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                        reversed.push(TupleElement { received: node.received });
                        cursor = node.previous;
                    }
                    if reversed.len() != elements.len() { return Err(RuntimeUnavailable::InvalidSourceReference); }
                    reversed.reverse();
                    let value = match &tuple.instruction {
                        Instruction::Variant { tag, .. } => RuntimeValueKind::Variant { tag: tag.clone(), payloads: reversed },
                        _ => RuntimeValueKind::Tuple(reversed),
                    };
                    self.data(&tuple.site, value, None);
                }
            }
            Frame::Case { case, environment } => {
                let Instruction::Case { arms, .. } = &case.instruction else {
                    unreachable!()
                };
                let selected = {
                    let value = &self.values[received.value.0].kind;
                    arms.iter().position(|arm| match (&arm.pattern, value) {
                        (CasePattern::Integer(expected), RuntimeValueKind::Integer(actual)) => expected == actual,
                        (CasePattern::Binder(_), _) => true,
                        (CasePattern::Tuple(patterns), RuntimeValueKind::Tuple(elements)) => {
                            patterns.len() == elements.len()
                        }
                        (CasePattern::Variant { tag, payloads }, RuntimeValueKind::Variant { tag: actual, payloads: elements }) => {
                            tag == actual && payloads.len() == elements.len()
                        }
                        (CasePattern::Wildcard, _) => true,
                        _ => false,
                    })
                };
                if let Some(selected) = selected {
                    let arm = &arms[selected];
                    let environment = match &arm.pattern {
                        CasePattern::Binder(id) => self.bind(
                            environment,
                            Binder::Catch(id.clone()),
                            ReceivedValue { dispatch: received.dispatch, value: received.value, interface: ParameterRole::Value, view: received.view },
                        ),
                        CasePattern::Tuple(patterns) | CasePattern::Variant { payloads: patterns, .. } => {
                            let bindings = {
                                let elements = match &self.values[received.value.0].kind {
                                    RuntimeValueKind::Tuple(elements) | RuntimeValueKind::Variant { payloads: elements, .. } => elements,
                                    _ => unreachable!("the selected structural pattern matched its value"),
                                };
                                patterns.iter().zip(elements).filter_map(|(pattern, element)| {
                                    pattern.as_ref().map(|id| (id.clone(), element.received))
                                }).collect::<Vec<_>>()
                            };
                            let mut environment = environment;
                            for (id, mut value) in bindings {
                                value.dispatch = self.dispatch.then(value.dispatch, received.dispatch)?;
                                environment = self.bind(environment, Binder::Catch(id), value);
                            }
                            environment
                        }
                        CasePattern::Integer(_) => environment,
                        CasePattern::Wildcard => environment,
                    };
                    self.state = State::Evaluate {
                        code: arm.body,
                        environment,
                    };
                } else {
                    return Err(RuntimeUnavailable::NonExhaustiveCase(case.site.clone()));
                }
            }
            Frame::ExpressionReturn { root, next } => {
                if !self.program.expression_roots.contains_key(&root) {
                    return Err(RuntimeUnavailable::InvalidSourceReference);
                }
                self.begin_root(next);
            }
            Frame::Root { next, cell } => {
                self.cells[cell] = Some(ReceivedValue {
                    dispatch: received.dispatch,
                    value: received.value,
                    interface: ParameterRole::Value,
                    view: received.view,
                });
                self.initializing_globals.remove(&cell);
                self.begin_root(next);
            }
            Frame::GlobalRead {
                cell,
                consumption,
                site,
                environment,
            } => {
                let received = ReceivedValue {
                    dispatch: received.dispatch,
                    value: received.value,
                    interface: ParameterRole::Value,
                    view: received.view,
                };
                self.cells[cell] = Some(received);
                self.initializing_globals.remove(&cell);
                let received = self.dispatch_name(received, cell, environment, &site)?;
                self.consume(received, consumption, &site)?;
            }
        }
        Ok(())
    }

    fn primitive_matches(&self, ty: &SourceAnnotationValue, received: ReceivedValue) -> bool {
        received.interface == ParameterRole::Value
            && self.receiving.matches_value(received.view, received.value)
            && matches!(
                (ty, &self.values[received.value.0].kind),
                (SourceAnnotationValue::Unit, RuntimeValueKind::Unit)
                    | (SourceAnnotationValue::Int, RuntimeValueKind::Integer(_))
                    | (SourceAnnotationValue::Bool, RuntimeValueKind::Boolean(_))
                    | (SourceAnnotationValue::Str, RuntimeValueKind::String(_))
            )
    }
    fn new_invocation(
        &mut self,
        call: SourceSite,
        provider: SourceSite,
    ) -> Result<(usize, ExecutionOwner), RuntimeUnavailable> {
        let activation = self.next_receiver;
        self.next_receiver = activation
            .checked_add(1)
            .ok_or(RuntimeUnavailable::IdentityExhausted)?;
        debug_assert_eq!(self.invocations.len(), activation);
        self.invocations.push(InvocationDescriptor {
            call,
            provider,
            active: true,
        });
        self.active_receivers.push(activation);
        let previous = self.current_owner;
        self.current_owner = ExecutionOwner::Invocation(activation);
        Ok((activation, previous))
    }
    fn leave_owner(
        &mut self,
        owner: ExecutionOwner,
        owned: bool,
        previous: ExecutionOwner,
    ) -> Result<(), RuntimeUnavailable> {
        if self.current_owner != owner {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        }
        if owned {
            let ExecutionOwner::Invocation(id) = owner else {
                return Err(RuntimeUnavailable::InvalidSourceReference);
            };
            if self.active_receivers.pop() != Some(id) {
                return Err(RuntimeUnavailable::InvalidSourceReference);
            }
            let invocation = self
                .invocations
                .get_mut(id)
                .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
            if !invocation.active {
                return Err(RuntimeUnavailable::InvalidSourceReference);
            }
            invocation.active = false;
        } else if !self.owner_active(owner) {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        }
        self.current_owner = previous;
        Ok(())
    }
    fn resolve_control(
        original: ExecutionOwner,
        control: &HashMap<usize, usize>,
    ) -> ExecutionOwner {
        match original {
            ExecutionOwner::ModuleRun => ExecutionOwner::ModuleRun,
            ExecutionOwner::Invocation(id) => {
                ExecutionOwner::Invocation(control.get(&id).copied().unwrap_or(id))
            }
        }
    }
    fn capture_template(
        &mut self,
        request: &PendingRequest,
        containing: ExecutionOwner,
    ) -> Result<TemplateHandle, RuntimeUnavailable> {
        let mut nodes = vec![TemplateNode::Hole];
        let mut root = 0;
        for frame in &request.suffix {
            let node = match frame {
                SavedFrame::Ordinary(Frame::GlobalRead { .. } | Frame::Root { .. }) => {
                    return Err(RuntimeUnavailable::ContinuationMaterialization(
                        request.source.clone(),
                    ));
                }
                SavedFrame::Ordinary(Frame::RootCompReturn { execution }) => TemplateNode::View {
                    inner: root,
                    original: *execution,
                },
                SavedFrame::Ordinary(frame) => {
                    if let Frame::ResumeArgument { template, .. } = frame {
                        self.resume_templates
                            .get(template.0)
                            .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                    }
                    TemplateNode::Bind {
                        inner: root,
                        frame: frame.clone(),
                    }
                }
                SavedFrame::ReceiverBoundary {
                    original_activation,
                } => TemplateNode::Owner {
                    inner: root,
                    original: ExecutionOwner::Invocation(*original_activation),
                },
                SavedFrame::AmbientBoundary => TemplateNode::Owner {
                    inner: root,
                    original: ExecutionOwner::ModuleRun,
                },
                SavedFrame::HandlerBoundary {
                    handler,
                    environment,
                    installation,
                } => TemplateNode::ForwardHandler {
                    inner: root,
                    handler: handler.clone(),
                    environment: *environment,
                    owner: installation.owner,
                },
            };
            nodes.push(node);
            root = nodes.len() - 1;
        }
        // The installing source span still contains the capture bound, even
        // when its ordinary ReceiverReturn lies below it and was not captured.
        nodes.push(TemplateNode::Owner {
            inner: root,
            original: containing,
        });
        root = nodes.len() - 1;
        // Publish only after the whole cache-free template has validated. Nodes
        // and saved Bind frames retain handles, never owning template pointers.
        let handle = TemplateHandle(self.resume_templates.len());
        #[cfg(test)]
        if self.r323_template_observations.len() < 1024
            && self.r323_template_observations.try_reserve(1).is_ok()
        {
            let saved_frame_order = request.suffix.iter().map(r323_saved_frame_witness).collect();
            self.r323_template_observations.push(R323TemplateObservation {
                run_id: self as *const Machine as usize,
                request: request.event,
                template: handle.0,
                capture_owner: containing,
                saved_frame_order,
            });
        } else {
            #[cfg(test)]
            { self.r312_observations_truncated = true; }
        }
        self.resume_templates.push(ResumeTemplate {
            nodes,
            root,
            declaration: request.declaration.clone(),
            original_event: request.event,
        });
        Ok(handle)
    }
    fn enter_template(
        &mut self,
        template: TemplateHandle,
        node: usize,
        mut control: HashMap<usize, usize>,
        response: ReceivedValue,
    ) -> Result<(), RuntimeUnavailable> {
        let inner = match self
            .resume_templates
            .get(template.0)
            .ok_or(RuntimeUnavailable::InvalidSourceReference)?
            .nodes
            .get(node)
            .cloned()
            .ok_or(RuntimeUnavailable::InvalidSourceReference)?
        {
            TemplateNode::Hole => {
                self.state = State::Return(response);
                return Ok(());
            }
            TemplateNode::Bind { inner, mut frame } => {
                // Pending callback entries are executable frames, so their
                // owner follows this replay's control map. Existing callback
                // entries/uses/receipts remain immutable historical evidence.
                if let Frame::ValueEntry {
                    callback_schema: Some(_),
                    entry_receiver,
                    ..
                } = &mut frame
                {
                    let resolved = Self::resolve_control(
                        ExecutionOwner::Invocation(*entry_receiver),
                        &control,
                    );
                    let ExecutionOwner::Invocation(receiver) = resolved else {
                        return Err(RuntimeUnavailable::InvalidSourceReference);
                    };
                    *entry_receiver = receiver;
                }
                self.frames.push(frame);
                inner
            }
            TemplateNode::Owner { inner, original } => {
                let previous = self.current_owner;
                #[cfg(test)]
                let mut resolution_control = control.iter().map(|(from, to)| (*from, *to)).collect::<Vec<_>>();
                #[cfg(test)]
                resolution_control.sort_unstable();
                let resolved = Self::resolve_control(original, &control);
                let resolved_active = self.owner_active(resolved);
                let (owner, owned) = if resolved_active {
                    self.current_owner = resolved;
                    (resolved, false)
                } else {
                    let ExecutionOwner::Invocation(original_id) = original else {
                        return Err(RuntimeUnavailable::InvalidSourceReference);
                    };
                    let descriptor = self
                        .invocations
                        .get(original_id)
                        .cloned()
                        .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                    let (fresh, _) = self.new_invocation(descriptor.call, descriptor.provider)?;
                    (ExecutionOwner::Invocation(fresh), true)
                };
                if let (
                    ExecutionOwner::Invocation(original),
                    ExecutionOwner::Invocation(resolved),
                ) = (original, owner)
                {
                    // Entry follows one inward path before Hole. Moving this
                    // fresh per-use map and shadowing here equals the nearest
                    // parent binding; no later completion consults this map.
                    control.insert(original, resolved);
                }
                #[cfg(test)]
                if self.r323_owner_replay_observations.len() < 1024
                    && self.r323_owner_replay_observations.try_reserve(1).is_ok()
                {
                    let (call_site, provider_site) = match owner {
                        ExecutionOwner::Invocation(id) => self.invocations.get(id).map_or(
                            (None, None), |invocation| (Some(invocation.call.clone()), Some(invocation.provider.clone()))),
                        ExecutionOwner::ModuleRun => (None, None),
                    };
                    self.r323_owner_replay_observations.push(R323OwnerReplayObservation {
                        run_id: self as *const Machine as usize,
                        request: self.resume_templates[template.0].original_event,
                        template: template.0,
                        node,
                        original,
                        resolved,
                        resolved_active,
                        control: resolution_control,
                        owner,
                        owned,
                        previous,
                        owner_live: self.owner_active(owner),
                        current_owner_after: self.current_owner,
                        call_site,
                        provider_site,
                    });
                } else {
                    #[cfg(test)]
                    { self.r312_observations_truncated = true; }
                }
                self.frames.push(Frame::OwnerReturn {
                    owner,
                    owned,
                    previous,
                });
                inner
            }
            TemplateNode::ForwardHandler {
                inner,
                handler,
                environment,
                owner,
            } => {
                let owner = Self::resolve_control(owner, &control);
                if !self.owner_active(owner) || self.current_owner != owner {
                    return Err(RuntimeUnavailable::InvalidSourceReference);
                }
                let occurrence = self.next_handler;
                self.next_handler = occurrence
                    .checked_add(1)
                    .ok_or(RuntimeUnavailable::IdentityExhausted)?;
                self.frames.push(Frame::CatchReturn {
                    handler,
                    environment,
                    installation: HandlerInstallation { occurrence, owner },
                });
                inner
            }
            TemplateNode::View { inner, original } => {
                let execution = self
                    .receiving
                    .execution(original.view, original.receipt)
                    .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                self.executing_views.push(execution);
                self.frames.push(Frame::RootCompReturn { execution });
                inner
            }
        };
        self.state = State::EnterTemplate {
            template,
            node: inner,
            control,
            response,
        };
        Ok(())
    }
    fn direct_formal_root(&self, label: Label, environment: usize) -> Option<ViewHandle> {
        let Instruction::Name {
            resolution: LocalSourceResolution::Parameter(parameter),
            consumption: NameConsumption::Execute,
        } = &self.program.code.get(label.0)?.instruction
        else {
            return None;
        };
        let cell = self.lookup(environment, |binder| {
            matches!(binder, Binder::Parameter(candidate) if candidate == parameter)
        })?;
        let received = self.cells.get(cell).copied().flatten()?;
        (received.interface == ParameterRole::Computation).then_some(received.view)
    }
    fn end_execution_view(&mut self, execution: ExecutionView) -> Result<(), RuntimeUnavailable> {
        let Some(current) = self.executing_views.pop() else {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        };
        if current.view != execution.view
            || current.receipt != execution.receipt
            || current.occurrence != execution.occurrence
        {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        }
        Ok(())
    }
    fn current_execution_owner(&self) -> ExecutionOwner {
        self.current_owner
    }
    fn owner_active(&self, owner: ExecutionOwner) -> bool {
        match owner {
            ExecutionOwner::ModuleRun => true,
            ExecutionOwner::Invocation(id) => self
                .invocations
                .get(id)
                .is_some_and(InvocationDescriptor::is_active),
        }
    }
    fn validate_handler_installation(
        &self,
        installation: HandlerInstallation,
    ) -> Result<(), RuntimeUnavailable> {
        // The retained installer must be both executable here and actually live.
        // A borrowed resumed owner can be below the resumer in active order;
        // ModuleRun is the distinct ambient case, never an invocation ordinal.
        if installation.occurrence >= self.next_handler
            || installation.owner != self.current_execution_owner()
            || !self.owner_active(installation.owner)
        {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        }
        Ok(())
    }
    fn propagate_request(&mut self, mut request: PendingRequest) -> Result<(), RuntimeUnavailable> {
        let request_owner = self.current_execution_owner();
        if let (Some(plan), Some(trace)) =
            (&self.program.operation_v1, &mut self.operation_v1_trace)
        {
            if trace.callback_operation_seen
                && trace.callback_operation_owner == Some(request_owner)
                && trace.applied_response_invocation.as_ref().is_some_and(|(_, owner)| {
                    *owner == request_owner
                })
                && request.declaration.id == plan.link.callback_operation
                && request.source.occurrence == plan.link.callback_apply
            {
                trace.callback_request_event = Some(request.event);
                trace.callback_request = Some((request.event, request.source.clone()));
            }
        }
        // Inspect the actual installed candidate while its delimiter is still
        // active. Only a committed forwarding transition removes that occurrence.
        if let Some(Frame::CatchReturn {
            handler,
            installation,
            environment,
        }) = self.frames.last().cloned()
        {
            self.validate_handler_installation(installation)?;
            let Instruction::Catch { arms, .. } = &handler.instruction else {
                unreachable!()
            };
            for arm in arms {
                let LocalSourceCatchPattern::Operation {
                    resolution,
                    payloads,
                    continuation,
                    ..
                } = &arm.pattern
                else {
                    continue;
                };
                let declaration = match resolution {
                    SourceOperationResolution::Resolved(declaration)
                        if declaration.id != request.declaration.id =>
                    {
                        continue;
                    }
                    SourceOperationResolution::Resolved(declaration) => declaration,
                    _ => return Err(RuntimeUnavailable::HandlerEvidence(handler.site.clone())),
                };
                // The closed primitive ModuleRun certificate proves unprotected
                // events for this whole universe. Otherwise require a positive
                // local Grant; missing Grant alone supplies no negative fact.
                if !self.program.closed_primitive
                    && !self.receiving.local_grant(
                        &request.observations,
                        request.event,
                        installation.owner,
                        &self.invocations,
                        &request.declaration.id.family,
                    )
                {
                    return Err(RuntimeUnavailable::HandlerEvidence(handler.site.clone()));
                }
                let SourceAnnotationValue::Function { argument, result } =
                    &declaration.signature.value
                else {
                    return Err(RuntimeUnavailable::HandlerEvidence(handler.site.clone()));
                };
                if declaration.signature.effects.is_some() || argument.effects.is_some() {
                    return Err(RuntimeUnavailable::HandlerEvidence(handler.site.clone()));
                }
                let [payload_pattern] = payloads.as_slice() else {
                    return Err(RuntimeUnavailable::HandlerEvidence(handler.site.clone()));
                };
                if !self.primitive_matches(&argument.value, request.payload) {
                    return Err(RuntimeUnavailable::HandlerEvidence(handler.site.clone()));
                }
                let captured = if matches!(continuation, LocalSourceCatchValuePattern::Binder(_)) {
                    let primitive_response = matches!(
                        result.value,
                        SourceAnnotationValue::Unit
                            | SourceAnnotationValue::Int
                            | SourceAnnotationValue::Bool
                            | SourceAnnotationValue::Str
                    );
                    let exact_v1_function_response = matches!(
                        &result.value,
                        SourceAnnotationValue::Function { .. }
                    ) && self.program.operation_v1.as_ref().is_some_and(|plan| {
                        request.source.occurrence == plan.request_apply.occurrence
                            && request.declaration.id == plan.request_operation
                            && handler.site.occurrence == plan.request_handler.occurrence
                            && arm.source == plan.request_arm
                            && self.operation_v1_trace.as_ref().is_some_and(|trace| {
                                trace.request_operation_seen
                            })
                    });
                    if !primitive_response && !exact_v1_function_response {
                        return Err(RuntimeUnavailable::HandlerEvidence(handler.site.clone()));
                    }
                    Some(self.capture_template(&request, self.current_owner)?)
                } else {
                    None
                };
                // Commit shallow selection only after every ordered candidate
                // premise succeeds. Discarding its raw suffix is source control;
                // the arm executes outside this exact handler occurrence.
                self.frames.pop();
                if captured.is_none() {
                    self.abandon_suffix(&request.suffix);
                }
                let environment = match payload_pattern {
                    LocalSourceCatchPayloadPattern::Value(
                        LocalSourceCatchValuePattern::Binder(binder),
                    ) => self.bind(
                        environment,
                        Binder::Catch(binder.id.clone()),
                        request.payload,
                    ),
                    LocalSourceCatchPayloadPattern::Value(
                        LocalSourceCatchValuePattern::Wildcard,
                    )
                    // Empty-call pattern syntax lowers to a wildcard; payload
                    // compatibility is established above by the declaration.
                    | LocalSourceCatchPayloadPattern::Unit { .. } => environment,
                };
                let environment =
                    if let (LocalSourceCatchValuePattern::Binder(binder), Some(template)) =
                        (continuation, captured)
                    {
                        let value = self.allocate(
                            &handler.site,
                            RuntimeValueKind::Closure,
                            Some(ExecutableValue::Continuation(template)),
                        );
                        let view = self.receiving.opaque(value);
                        self.bind(
                            environment,
                            Binder::Catch(binder.id.clone()),
                            ReceivedValue {
                                dispatch: None,
                                value,
                                interface: ParameterRole::Value,
                                view,
                            },
                        )
                    } else {
                        environment
                    };
                self.state = State::Evaluate {
                    code: arm.body,
                    environment,
                };
                if let Some(trace) = &mut self.operation_v1_trace {
                    if let Some(plan) = &self.program.operation_v1 {
                        if trace.callback_request_event == Some(request.event)
                            && request.declaration.id == plan.link.callback_operation
                            && request.source.occurrence == plan.link.callback_apply
                            && plan.expected_outer_handler.as_ref().is_some_and(|expected|
                                handler.site.occurrence == expected.occurrence)
                            && plan.expected_outer_arm.as_ref().is_some_and(|expected|
                                &arm.source == expected)
                            && trace.callback_request.as_ref().is_some_and(|(event, source)| {
                                *event == request.event
                                    && source.occurrence == request.source.occurrence
                            })
                        {
                            trace.live_handler = Some((
                                handler.site.clone(),
                                arm.source.clone(),
                                request.event,
                                request.source.clone(),
                            ));
                        }
                    }
                }
                return Ok(());
            }
        }
        // An initializer's escaping request cannot search handlers installed
        // around the Name that demanded its value. Scheduled initializers have
        // the same cut for the authenticated resumable host consumer. Keep its
        // cache write and module cursor live; resume must drain owner frames
        // before another root starts. Other escaping operations remain terminal
        // and retain their existing opaque suffix observation.
        let resumable_host = self.program.host_write_operation()
            .is_some_and(|operation| operation == &request.declaration.id);
        if matches!(self.frames.last(), Some(Frame::GlobalRead { .. }))
            || (resumable_host && matches!(self.frames.last(),
                Some(Frame::Root { .. } | Frame::ExpressionReturn { .. }))) {
            self.stop_unhandled_request(request, request_owner)?;
            return Ok(());
        }
        let Some(frame) = self.frames.pop() else {
            self.stop_unhandled_request(request, request_owner)?;
            return Ok(());
        };
        let template = match frame {
            Frame::RootCompReturn { execution } => {
                self.end_execution_view(execution)?;
                SavedFrame::Ordinary(Frame::RootCompReturn { execution })
            }
            Frame::ReceiverReturn {
                activation,
                previous,
            } => {
                self.leave_owner(ExecutionOwner::Invocation(activation), true, previous)?;
                SavedFrame::ReceiverBoundary {
                    original_activation: activation,
                }
            }
            Frame::OwnerReturn {
                owner,
                owned,
                previous,
            } => {
                self.leave_owner(owner, owned, previous)?;
                match owner {
                    ExecutionOwner::Invocation(original_activation) => {
                        SavedFrame::ReceiverBoundary {
                            original_activation,
                        }
                    }
                    ExecutionOwner::ModuleRun => SavedFrame::AmbientBoundary,
                }
            }
            Frame::CatchReturn {
                handler,
                environment,
                installation,
            } => SavedFrame::HandlerBoundary {
                handler,
                environment,
                installation,
            },
            ordinary => SavedFrame::Ordinary(ordinary),
        };
        request.suffix.push(template);
        self.state = State::Request(request);
        Ok(())
    }
    fn stop_unhandled_request(
        &mut self,
        request: PendingRequest,
        containing: ExecutionOwner,
    ) -> Result<(), RuntimeUnavailable> {
        let template = if self.program.host_write_operation()
            .is_some_and(|operation| operation == &request.declaration.id)
        {
            Some(self.capture_template(&request, containing)?)
        } else {
            None
        };
        let continuation = ContinuationHandle(self.continuations.len());
        self.continuations.push(SavedContinuation {
            frames: request.suffix,
            template,
            resumed: false,
            observations: request.observations,
        });
        self.state = State::Stopped(RuntimeOutcome::UnhandledRequest {
            source: request.source,
            operation: request.declaration.id.clone(),
            payload: request.payload.value,
            event: request.event,
            continuation,
        });
        Ok(())
    }
    fn abandon_suffix(&mut self, suffix: &[SavedFrame]) {
        // These writes will never run: release only their pending materialization
        // markers. Live outer cache owners and retained/forwarded suffixes remain
        // untouched, and the selected arm is not their initializer result.
        for frame in suffix {
            if let SavedFrame::Ordinary(Frame::GlobalRead { cell, .. } | Frame::Root { cell, .. }) =
                frame
            {
                self.initializing_globals.remove(cell);
            }
        }
    }
    fn make_request_carrier(
        &mut self,
        declaration: Arc<SourceOperationDeclaration>,
        payload: ReceivedValue,
        source: &SourceSite,
    ) {
        self.data(
            source,
            RuntimeValueKind::Computation,
            Some(ExecutableValue::Request {
                declaration,
                payload,
                source: source.clone(),
            }),
        );
    }
    fn begin_root(&mut self, mut ordinal: usize) {
        // Completion is reached only after the root's handlers and real
        // invocation owners have returned. Never overwrite a mismatched owner.
        if self.current_owner != ExecutionOwner::ModuleRun {
            self.state = State::Stopped(RuntimeOutcome::Unavailable(
                RuntimeUnavailable::InvalidSourceReference,
            ));
            return;
        }
        // A slot is visited once; dependency-materialized definitions skip their
        // cache, while expression values have no publication cell or marker.
        while let Some(root) = self.execution_roots.get(ordinal).cloned() {
            ordinal += 1;
            let mut environment = 0;
            let code = match root {
                ScheduledRoot::Definition(index) => {
                    if self.cells[index].is_some() {
                        continue;
                    }
                    self.initializing_globals.insert(index);
                    self.frames.push(Frame::Root {
                        next: ordinal,
                        cell: index,
                    });
                    environment = match self.initializer_environment(index, 0) {
                        Ok(environment) => environment,
                        Err(error) => { self.state = State::Stopped(RuntimeOutcome::Unavailable(error)); return; }
                    };
                    self.program.definitions[index].body
                }
                ScheduledRoot::Expression { root, code } => {
                    self.frames.push(Frame::ExpressionReturn {
                        root,
                        next: ordinal,
                    });
                    code
                }
            };
            self.state = State::Evaluate {
                code,
                environment,
            };
            return;
        }
        if let Some(selected) = self.selected {
            self.complete_selected_definition(ordinal, selected);
        } else {
            self.complete_module();
        }
    }
    fn complete_selected_definition(&mut self, next_ordinal: usize, selected: usize) {
        // Schedule exhaustion retains the selected-definition entry contract:
        // use its cached cell, or evaluate its initializer as the final root.
        if let Some(value) = self.cells[selected] {
            self.state = State::Stopped(RuntimeOutcome::Completed(value.value));
        } else {
            self.initializing_globals.insert(selected);
            self.frames.push(Frame::Root {
                next: next_ordinal,
                cell: selected,
            });
            let environment = match self.initializer_environment(selected, 0) {
                Ok(environment) => environment,
                Err(error) => { self.state = State::Stopped(RuntimeOutcome::Unavailable(error)); return; }
            };
            self.state = State::Evaluate {
                code: self.program.definitions[selected].body,
                environment,
            };
        }
    }
    fn complete_module(&mut self) {
        if self.current_owner != ExecutionOwner::ModuleRun {
            self.state = State::Stopped(RuntimeOutcome::Unavailable(
                RuntimeUnavailable::InvalidSourceReference,
            ));
            return;
        }
        let site = match self.program.module_completion_site() {
            Ok(Some(site)) => site,
            Ok(None) => {
                self.state = State::Stopped(RuntimeOutcome::EmptyModuleCompleted);
                return;
            }
            Err(error) => {
                self.state = State::Stopped(RuntimeOutcome::Unavailable(error));
                return;
            }
        };
        let value = self.allocate(&site, RuntimeValueKind::Unit, None);
        self.state = State::Stopped(RuntimeOutcome::Completed(value));
    }
    fn consume(
        &mut self,
        received: ReceivedValue,
        consumption: NameConsumption,
        site: &SourceSite,
    ) -> Result<(), RuntimeUnavailable> {
        // A candidate is single-use and belongs to this Name consume only.
        // Any prior return token is likewise expired before a new consume.
        let candidate = self.pending_name_entry.take();
        let observed_name = self.pending_name_observation.take();
        self.name_entry_return_token = None;
        self.pending_name_return_observation = None;
        if !self.receiving.matches_value(received.view, received.value) {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        }
        let owner = self.current_execution_owner();
        let receipt_index = self.receiving.next_receipt_index();
        let receipt =
            self.receiving
                .receipt(owner, received.view, site, None);
        #[cfg(test)]
        let r312_lookup = self.r312_pending_name_lookup.take();
        #[cfg(test)]
        if let Some(lookup) = r312_lookup {
            if self.r312_name_receipts.len() >= 1024
                || self.r312_name_receipts.try_reserve(1).is_err()
            {
                self.r312_observations_truncated = true;
            } else {
                let order = self.r312_next_order();
                self.r312_name_receipts.push(R312NameReceipt {
                    lookup,
                    step: self.steps,
                    order,
                    receipt: receipt_index,
                    owner,
                    site: site.clone(),
                    value: received.value,
                    view: received.view,
                    consumption,
                });
            }
        }
        if consumption == NameConsumption::Observe {
            if let Some(observed) = observed_name.filter(|observed|
                observed.site.source_root == site.source_root
                    && observed.site.occurrence == site.occurrence)
            {
                self.pending_name_return_observation = Some(CompletedNameObservation {
                    resolution: observed.resolution,
                    site: observed.site,
                    cell: observed.cell,
                    value: received.value,
                    view: received.view,
                    receipt_index,
                    cells_before_observe: self.cells.len(),
                });
            }
        }
        if consumption == NameConsumption::Observe {
            if let Some(mut pending) = candidate {
            if pending.site.source_root == site.source_root
                && pending.site.occurrence == site.occurrence
                && pending.value == received.value
                && pending.view == received.view
                && owner == ExecutionOwner::Invocation(pending.invocation)
            {
                pending.receipt_index = Some(receipt_index);
                self.name_entry_return_token = Some(pending);
            }
            }
        }
        match consumption {
            NameConsumption::Observe => self.state = State::Return(received),
            NameConsumption::Execute => {
                #[cfg(test)]
                if let Some(lookup) = r312_lookup {
                    if let Some(source_receipt) = self.r312_name_receipts.iter().rev()
                        .find(|observation| observation.lookup == lookup)
                    {
                        self.r312_pending_force = Some(R312PendingForce {
                            lookup,
                            receipt: source_receipt.receipt,
                            owner: source_receipt.owner,
                            site: source_receipt.site.clone(),
                            view: source_receipt.view,
                            value: source_receipt.value,
                        });
                    }
                }
                if received.interface != ParameterRole::Computation {
                    return Err(RuntimeUnavailable::MissingConsumptionEvidence(site.clone()));
                }
                if self.receiving.has_root(received.view) {
                    let execution = self
                        .receiving
                        .execution(received.view, receipt)
                        .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                    self.executing_views.push(execution);
                    self.frames.push(Frame::RootCompReturn { execution });
                }
                self.execute_with_substitution(received.value, site, received.dispatch)?;
            }
        }
        Ok(())
    }
    fn begin_local(
        &mut self,
        block: Arc<Code>,
        ordinal: usize,
        mut environment: usize,
    ) -> Result<(), RuntimeUnavailable> {
        let (binding, final_expression) = match &block.instruction {
            Instruction::Block { bindings, final_expression } => (bindings.get(ordinal).cloned(), *final_expression),
            Instruction::StatementBlock { statements, final_expression } => match statements.get(ordinal) {
                Some(BlockStatement::Expression(expression)) => {
                    let code = *expression;
                    self.frames.push(Frame::BlockExpression { block, next: ordinal + 1, environment });
                    self.state = State::Evaluate { code, environment };
                    return Ok(());
                }
                Some(BlockStatement::Binding(binding)) => (Some(binding.clone()), *final_expression),
                None => (None, *final_expression),
            },
            _ => return Err(RuntimeUnavailable::InvalidSourceReference),
        };
        if let Some(binding) = binding {
            let initializer = binding.initializer;
            let recursive = binding.recursive;
            let cell = self.cells.len();
            self.cells.push(None);
            if recursive {
                environment = self.extend(environment, Binder::Local(binding.id.clone()), cell);
            }
            self.frames.push(Frame::Local {
                block,
                next: ordinal + 1,
                environment,
                cell,
                recursive,
            });
            let environment = self.initializer_environment(cell, environment)?;
            self.state = State::Evaluate {
                code: initializer,
                environment,
            };
        } else {
            self.state = State::Evaluate {
                code: final_expression,
                environment,
            };
        }
        Ok(())
    }
    fn execute(&mut self, value: ValueHandle, site: &SourceSite) -> Result<(), RuntimeUnavailable> {
        self.execute_with_substitution(value, site, None)
    }
    fn execute_with_substitution(&mut self, value: ValueHandle, site: &SourceSite,
        substitution: Option<usize>) -> Result<(), RuntimeUnavailable> {
        match self.executables.get(&value.0).cloned() {
            Some(ExecutableValue::Delay { code, environment }) => {
                let environment = self.substitute_environment(environment, substitution)?;
                #[cfg(test)]
                if let Some(pending) = self.r312_pending_force.take() {
                    if self.r312_name_forces.len() >= 1024
                        || self.r312_name_forces.try_reserve(1).is_err()
                    {
                        self.r312_observations_truncated = true;
                    } else {
                        let order = self.r312_next_order();
                        let active = pending.clone();
                        self.r312_name_forces.push(R312NameForce {
                            lookup: pending.lookup,
                            receipt: pending.receipt,
                            step: self.steps,
                            order,
                            owner: self.current_execution_owner(),
                            site: pending.site,
                            view: pending.view,
                            value,
                            code,
                            environment,
                        });
                        if self.r312_active_forces.len() >= 1024
                            || self.r312_active_forces.try_reserve(1).is_err()
                        {
                            self.r312_observations_truncated = true;
                        } else {
                            self.r312_active_forces.insert(active.lookup, active);
                        }
                    }
                }
                self.state = State::Evaluate { code, environment };
                Ok(())
            }
            Some(ExecutableValue::Request {
                declaration,
                mut payload,
                source,
            }) => {
                payload.dispatch = self.dispatch.then(payload.dispatch, substitution)?;
                let event = self.next_request;
                self.next_request = event
                    .checked_add(1)
                    .ok_or(RuntimeUnavailable::IdentityExhausted)?;
                self.state = State::Request(PendingRequest {
                    declaration,
                    payload,
                    source,
                    event,
                    observations: self
                        .receiving
                        .observe(event, &self.executing_views)
                        .ok_or(RuntimeUnavailable::IdentityExhausted)?,
                    suffix: Vec::new(),
                });
                Ok(())
            }
            _ => Err(RuntimeUnavailable::ExpectedComputation(site.clone())),
        }
    }
    fn lookup(&self, mut environment: usize, matches: impl Fn(&Binder) -> bool) -> Option<usize> {
        loop {
            let frame = self.environments.get(environment)?;
            if let Some((candidate, cell)) = &frame.binder {
                if matches(candidate) {
                    return Some(*cell);
                }
            }
            environment = frame.parent?;
        }
    }
    fn with_dispatch(&mut self, parent: usize, dispatch: dispatch::State) -> usize {
        let environment = self.environments.len();
        self.environments.push(Environment { parent: Some(parent), binder: None, dispatch });
        environment
    }
    fn initializer_environment(&mut self, cell: usize, parent: usize) -> Result<usize, RuntimeUnavailable> {
        if self.program.dictionaries.is_none() { return Ok(parent); }
        let dispatch = self.dispatch.initializer(cell, self.environments[parent].dispatch)?;
        Ok(self.with_dispatch(parent, dispatch))
    }
    fn substitute_environment(&mut self, environment: usize, substitution: Option<usize>) -> Result<usize, RuntimeUnavailable> {
        if self.program.dictionaries.is_none() || substitution.is_none() { return Ok(environment); }
        let mut dispatch = self.environments[environment].dispatch;
        dispatch.substitution = self.dispatch.then(dispatch.substitution, substitution)?;
        Ok(self.with_dispatch(environment, dispatch))
    }
    fn dispatch_environment(&mut self, environment: usize, step: dispatch::Step) -> Result<usize, RuntimeUnavailable> {
        let mut dispatch = self.environments[environment].dispatch;
        dispatch.context = self.dispatch.append(dispatch.context, step)?;
        Ok(self.with_dispatch(environment, dispatch))
    }
    fn dispatch_name(&mut self, mut value: ReceivedValue, cell: usize, environment: usize,
        site: &SourceSite) -> Result<ReceivedValue, RuntimeUnavailable> {
        if self.program.dictionaries.is_none() { return Ok(value); }
        let key = dispatch::Site { owner: site.source_root.clone(), occurrence: site.occurrence.clone() };
        let instantiate = self.program.dictionary_names.contains(&key)
            .then_some(dispatch::Step { kind: dispatch::Kind::Name, site: key });
        value.dispatch = self.dispatch.name(value.dispatch, self.environments[environment].dispatch, cell, instantiate)?;
        Ok(value)
    }
    fn extend(&mut self, parent: usize, binder: Binder, cell: usize) -> usize {
        let index = self.environments.len();
        self.environments.push(Environment {
            parent: Some(parent),
            binder: Some((binder, cell)),
            dispatch: self.environments[parent].dispatch,
        });
        index
    }
    fn bind(&mut self, environment: usize, binder: Binder, value: ReceivedValue) -> usize {
        let cell = self.cells.len();
        self.cells.push(Some(value));
        self.extend(environment, binder, cell)
    }
    fn ground_data(
        &mut self,
        site: &SourceSite,
        kind: RuntimeValueKind,
        executable: Option<ExecutableValue>,
    ) {
        let value = self.allocate(site, kind, executable);
        let view = self.receiving.ground(value);
        self.state = State::Return(ReceivedValue {
            dispatch: None,
            value,
            interface: ParameterRole::Value,
            view,
        });
    }
    fn bind_record_parameter(&mut self, fields: Arc<[RecordParameterField]>, mut index: usize,
        argument: ReceivedValue, body: Label, mut environment: usize) -> Result<(), RuntimeUnavailable> {
        if !self.receiving.matches_value(argument.view, argument.value) {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        }
        while index < fields.len() {
            let RuntimeValueKind::Record(actual) = &self.values[argument.value.0].kind else {
                return Err(RuntimeUnavailable::InvalidSourceReference);
            };
            let field = &fields[index];
            if let Some((_, actual)) = actual.iter().find(|(name, _)| name == &field.label) {
                let mut received = actual.received;
                received.view = self.receiving.project_record(argument.view, received.view, received.value)
                    .ok_or_else(|| RuntimeUnavailable::UnsupportedRecordPattern(self.values[argument.value.0].source.clone()))?;
                received.dispatch = self.dispatch.then(received.dispatch, argument.dispatch)?;
                received.interface = ParameterRole::Value;
                environment = self.bind(environment, Binder::Parameter(field.binder.clone()), received);
                index += 1;
            } else if let Some(default) = field.default {
                self.frames.push(Frame::RecordDefault { fields, index, argument, body, environment });
                self.state = State::Evaluate { code: default, environment };
                return Ok(());
            } else { return Err(RuntimeUnavailable::InvalidSourceReference); }
        }
        // Even an empty pattern requires an actual record.
        if !matches!(self.values[argument.value.0].kind, RuntimeValueKind::Record(_)) {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        }
        self.state = State::Evaluate { code: body, environment };
        Ok(())
    }
    fn data(
        &mut self,
        site: &SourceSite,
        kind: RuntimeValueKind,
        executable: Option<ExecutableValue>,
    ) {
        let value = self.allocate(site, kind, executable);
        let view = self.receiving.opaque(value);
        self.state = State::Return(ReceivedValue {
            dispatch: None,
            value,
            interface: ParameterRole::Value,
            view,
        });
    }
    fn allocate(
        &mut self,
        site: &SourceSite,
        kind: RuntimeValueKind,
        executable: Option<ExecutableValue>,
    ) -> ValueHandle {
        let handle = ValueHandle(self.values.len());
        self.values.push(RuntimeValue {
            source: site.clone(),
            kind,
        });
        if let Some(executable) = executable {
            self.executables.insert(handle.0, executable);
        }
        handle
    }
}

impl Machine {
    fn advance_integer_product(&mut self, mut product: super::decimal::Product, site: SourceSite) -> Result<(), RuntimeUnavailable> {
        if product.advance() {
            let value = product.finish().ok_or(RuntimeUnavailable::InvalidSourceReference)?;
            self.ground_data(&site, RuntimeValueKind::Integer(value.into_boxed_str()), None);
        } else {
            self.state = State::IntegerProduct { product, site };
        }
        Ok(())
    }
}

fn pinned_primitive_arity(operation: &yu_hir::shadow::PinnedPrimitiveOp) -> Option<usize> {
    match operation {
        yu_hir::shadow::PinnedPrimitiveOp::IntToString
        | yu_hir::shadow::PinnedPrimitiveOp::BoolNot
        | yu_hir::shadow::PinnedPrimitiveOp::BoolToString => Some(1),
        yu_hir::shadow::PinnedPrimitiveOp::IntAdd
        | yu_hir::shadow::PinnedPrimitiveOp::IntSub
        | yu_hir::shadow::PinnedPrimitiveOp::IntMul
        | yu_hir::shadow::PinnedPrimitiveOp::IntEq
        | yu_hir::shadow::PinnedPrimitiveOp::IntLt
        | yu_hir::shadow::PinnedPrimitiveOp::IntLe
        | yu_hir::shadow::PinnedPrimitiveOp::IntGt
        | yu_hir::shadow::PinnedPrimitiveOp::IntGe
        | yu_hir::shadow::PinnedPrimitiveOp::BoolEq
        | yu_hir::shadow::PinnedPrimitiveOp::StringConcat => Some(2),
        yu_hir::shadow::PinnedPrimitiveOp::Unsupported(_) => None,
    }
}

fn pinned_primitive_apply(
    operation: &yu_hir::shadow::PinnedPrimitiveOp,
    arguments: &[ValueHandle],
    values: &[RuntimeValue],
) -> Option<RuntimeValueKind> {
    let argument = |index: usize| values.get(arguments.get(index)?.0).map(|value| &value.kind);
    match operation {
        yu_hir::shadow::PinnedPrimitiveOp::BoolNot => {
            let RuntimeValueKind::Boolean(value) = argument(0)? else { return None; };
            Some(RuntimeValueKind::Boolean(!*value))
        }
        yu_hir::shadow::PinnedPrimitiveOp::BoolEq => {
            let RuntimeValueKind::Boolean(left) = argument(0)? else { return None; };
            let RuntimeValueKind::Boolean(right) = argument(1)? else { return None; };
            Some(RuntimeValueKind::Boolean(*left == *right))
        }
        yu_hir::shadow::PinnedPrimitiveOp::BoolToString => {
            let RuntimeValueKind::Boolean(value) = argument(0)? else { return None; };
            let text = if *value { "true" } else { "false" };
            let mut result = String::new();
            result.try_reserve(text.len()).ok()?;
            result.push_str(text);
            Some(RuntimeValueKind::String(result.into_boxed_str()))
        }
        yu_hir::shadow::PinnedPrimitiveOp::IntAdd => {
            let RuntimeValueKind::Integer(left) = argument(0)? else { return None; };
            let RuntimeValueKind::Integer(right) = argument(1)? else { return None; };
            Some(RuntimeValueKind::Integer(decimal_add(left, right)?.into_boxed_str()))
        }
        yu_hir::shadow::PinnedPrimitiveOp::IntSub => {
            let RuntimeValueKind::Integer(left) = argument(0)? else { return None; };
            let RuntimeValueKind::Integer(right) = argument(1)? else { return None; };
            let negative = super::decimal::negate(right)?;
            Some(RuntimeValueKind::Integer(decimal_add(left, &negative)?.into_boxed_str()))
        }
        yu_hir::shadow::PinnedPrimitiveOp::IntEq
        | yu_hir::shadow::PinnedPrimitiveOp::IntLt
        | yu_hir::shadow::PinnedPrimitiveOp::IntLe
        | yu_hir::shadow::PinnedPrimitiveOp::IntGt
        | yu_hir::shadow::PinnedPrimitiveOp::IntGe => {
            let RuntimeValueKind::Integer(left) = argument(0)? else { return None; };
            let RuntimeValueKind::Integer(right) = argument(1)? else { return None; };
            let ordering = super::decimal::compare(left, right)?;
            let result = match operation {
                yu_hir::shadow::PinnedPrimitiveOp::IntEq => ordering.is_eq(),
                yu_hir::shadow::PinnedPrimitiveOp::IntLt => ordering.is_lt(),
                yu_hir::shadow::PinnedPrimitiveOp::IntLe => !ordering.is_gt(),
                yu_hir::shadow::PinnedPrimitiveOp::IntGt => ordering.is_gt(),
                yu_hir::shadow::PinnedPrimitiveOp::IntGe => !ordering.is_lt(),
                _ => return None,
            };
            Some(RuntimeValueKind::Boolean(result))
        }
        // Multiplication uses the resumable Machine state above.
        yu_hir::shadow::PinnedPrimitiveOp::IntMul => None,
        yu_hir::shadow::PinnedPrimitiveOp::IntToString => {
            let RuntimeValueKind::Integer(value) = argument(0)? else { return None; };
            Some(RuntimeValueKind::String(value.clone()))
        }
        yu_hir::shadow::PinnedPrimitiveOp::StringConcat => {
            let RuntimeValueKind::String(left) = argument(0)? else { return None; };
            let RuntimeValueKind::String(right) = argument(1)? else { return None; };
            let mut result = String::new();
            result.try_reserve(left.len().checked_add(right.len())?).ok()?;
            result.push_str(left);
            result.push_str(right);
            Some(RuntimeValueKind::String(result.into_boxed_str()))
        }
        yu_hir::shadow::PinnedPrimitiveOp::Unsupported(_) => None,
    }
}

fn decimal_add(left: &str, right: &str) -> Option<String> {
    fn signed(negative: bool, digits: String) -> Option<String> {
        if !negative || digits == "0" { return Some(digits); }
        let mut output = String::new();
        output.try_reserve(digits.len().checked_add(1)?).ok()?;
        output.push('-');
        output.push_str(&digits);
        Some(output)
    }
    fn split(value: &str) -> Option<(bool, &str)> {
        let (negative, digits) = value.strip_prefix('-').map_or((false, value), |digits| (true, digits));
        if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) { return None; }
        let digits = digits.trim_start_matches('0');
        Some((negative, if digits.is_empty() { "0" } else { digits }))
    }
    fn add_magnitude(left: &str, right: &str) -> Option<String> {
        let width = left.len().max(right.len());
        let mut output = Vec::new();
        output.try_reserve(width.checked_add(1)?).ok()?;
        let (mut carry, mut index) = (0u8, 0usize);
        while index < width || carry != 0 {
            let a = left.len().checked_sub(index + 1).and_then(|at| left.as_bytes().get(at)).copied().map_or(0, |b| b - b'0');
            let b = right.len().checked_sub(index + 1).and_then(|at| right.as_bytes().get(at)).copied().map_or(0, |b| b - b'0');
            let sum = a + b + carry;
            output.push(b'0' + sum % 10);
            carry = sum / 10;
            index += 1;
        }
        output.reverse();
        String::from_utf8(output).ok()
    }
    fn compare_magnitude(left: &str, right: &str) -> std::cmp::Ordering {
        left.len().cmp(&right.len()).then_with(|| left.cmp(right))
    }
    fn subtract_magnitude(larger: &str, smaller: &str) -> Option<String> {
        let mut output = Vec::new();
        output.try_reserve(larger.len()).ok()?;
        let (mut borrow, mut index) = (0i16, 0usize);
        while index < larger.len() {
            let a = i16::from(*larger.as_bytes().get(larger.len() - index - 1)? - b'0');
            let b = i16::from(smaller.len().checked_sub(index + 1).and_then(|at| smaller.as_bytes().get(at)).copied().map_or(0, |digit| digit - b'0'));
            let mut digit = a - borrow - b;
            borrow = i16::from(digit < 0);
            if borrow != 0 { digit += 10; }
            output.push(b'0' + digit as u8);
            index += 1;
        }
        while output.len() > 1 && output.last() == Some(&b'0') { output.pop(); }
        output.reverse();
        String::from_utf8(output).ok()
    }
    let (left_negative, left) = split(left)?;
    let (right_negative, right) = split(right)?;
    if left_negative == right_negative {
        let sum = add_magnitude(left, right)?;
        signed(left_negative, sum)
    } else {
        match compare_magnitude(left, right) {
            std::cmp::Ordering::Equal => Some("0".to_owned()),
            std::cmp::Ordering::Greater => {
                let difference = subtract_magnitude(left, right)?;
                signed(left_negative, difference)
            }
            std::cmp::Ordering::Less => {
                let difference = subtract_magnitude(right, left)?;
                signed(right_negative, difference)
            }
        }
    }
}

#[cfg(test)]
mod module_expression_tests {
    use super::*;
    use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports, lower_module};
    use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, parse_file, scan_header};

    fn runtime_program(source: &str, opt_in_source: bool) -> Arc<RuntimeProgram> {
        let source: Arc<SourceText> = Arc::from(source);
        let parsed = parse_file(
            source.clone(),
            Arc::new(scan_header(source.clone())),
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let lower = if opt_in_source {
            yu_hir::shadow::lower_module_with_local_source
        } else {
            lower_module
        };
        let hir = Arc::new(
            lower(
                ModuleIdentity::source_root(FileId::new(FileKey::new("runtime-roots", "test.yu"))),
                &parsed,
                SemanticImports::empty(),
            )
            .unwrap(),
        );
        RuntimeProgram::from_hir(hir, super::super::RuntimeEvidence::default()).unwrap()
    }

    fn start(program: &Arc<RuntimeProgram>) -> Machine {
        let definition = program.definition_named("main").unwrap().clone();
        let roots = program.execution_roots().unwrap();
        program.start(&definition, &roots).unwrap()
    }

    fn machine(source: &str, opt_in_source: bool) -> Machine {
        start(&runtime_program(source, opt_in_source))
    }

    fn accepted_machine_with_parse(source: &str) -> (Machine, Arc<ParsedFile>) {
        let source: Arc<SourceText> = Arc::from(source);
        let parsed = Arc::new(parse_file(
            source.clone(),
            Arc::new(scan_header(source.clone())),
            Arc::new(SyntaxEnvironment::empty()),
        ));
        assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{source}");
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("r312-accepted", "callee-history.yu"))),
            &parsed,
            SemanticImports::empty(),
        ).unwrap());
        let candidate = yu_solver::shadow_apply::CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "accepted source has no candidate conflicts");
        let program = Arc::new(RuntimeProgram::from_hir(
            hir, super::super::RuntimeEvidence::default(),
        ).unwrap());
        (start(&program), parsed)
    }

    fn accepted_machine(source: &str) -> Machine {
        accepted_machine_with_parse(source).0
    }

    fn cache_snapshot(
        machine: &Machine,
    ) -> Vec<Option<(ValueHandle, ParameterRole, ViewHandle)>> {
        machine
            .cells
            .iter()
            .map(|cell| {
                cell.as_ref().map(|received| {
                    (received.value, received.interface, received.view)
                })
            })
            .collect()
    }

    fn integer_count(machine: &Machine, expected: &str) -> usize {
        machine
            .values
            .iter()
            .filter(|value| {
                matches!(
                    &value.kind,
                    RuntimeValueKind::Integer(text) if text.as_ref() == expected
                )
            })
            .count()
    }

    fn assert_same_source_site(left: &SourceSite, right: &SourceSite) {
        assert_eq!(left.source_root, right.source_root);
        assert_eq!(left.occurrence, right.occurrence);
        assert_eq!(left.range, right.range);
    }

    fn program_hir_owns_apply_argument(
        hir: &yu_hir::HirModule,
        program: &RuntimeProgram,
        site: &SourceSite,
        argument_label: usize,
    ) -> bool {
        let Ok(Some(local)) = hir.local_source_for(&site.source_root) else { return false; };
        let apply = local.expressions().iter()
            .find(|expression| expression.occurrence == site.occurrence);
        let Some(apply) = apply else { return false; };
        let yu_hir::shadow::LocalSourceForm::Apply { argument, .. } = &apply.form else {
            return false;
        };
        let Some(argument_code) = program.code.get(argument_label) else { return false; };
        let Some(source_argument) = local.expression(argument) else { return false; };
        source_argument.occurrence == argument_code.site.occurrence
            && argument_code.site.source_root == site.source_root
    }

    fn assert_name_argument_receipt(
        machine: &Machine,
        call: &NameReceiptCallObservation,
        consumption: NameConsumption,
    ) {
        assert!(!machine.r312_observations_truncated);
        assert!(program_hir_owns_apply_argument(
            &machine.program._hir, &machine.program, &call.call_site, call.argument_code
        ));
        let code = machine.program.code.get(call.argument_code).unwrap();
        let lookups = machine.r312_name_lookups.iter().enumerate()
            .filter(|(_, lookup)| lookup.site.source_root == code.site.source_root
                && lookup.site.occurrence == code.site.occurrence
                && lookup.site.range == code.site.range)
            .collect::<Vec<_>>();
        assert_eq!(lookups.len(), 1, "no early or duplicate execution of this source Name");
        let (lookup_index, lookup) = lookups[0];
        assert_eq!(lookup.code, call.argument_code, "the exact source occurrence uses its Apply-owned code label");
        assert!(lookup.step >= call.selected_step);
        assert!(lookup.order > call.selected_order, "the Name executes only after Callee selection");
        assert_eq!(lookup.owner, ExecutionOwner::Invocation(call.invocation));
        assert_eq!(lookup.environment, call.argument_environment);
        assert_same_source_site(&lookup.site, &code.site);
        assert!(matches!(
            &code.instruction,
            Instruction::Name {
                resolution: LocalSourceResolution::Parameter(parameter),
                consumption: actual,
            } if parameter == &lookup.parameter && *actual == consumption
        ));
        assert_eq!(lookup.consumption, consumption);
        assert_eq!(
            machine.lookup(lookup.environment, |binder| {
                matches!(binder, Binder::Parameter(parameter) if parameter == &lookup.parameter)
            }),
            Some(lookup.cell)
        );
        let received = machine.cells[lookup.cell].unwrap();
        assert_eq!(received.value, lookup.value);
        assert_eq!(received.view, lookup.view);
        assert!(machine.receiving.matches_value(lookup.view, lookup.value));

        let receipts = machine.r312_name_receipts.iter()
            .filter(|receipt| receipt.lookup == lookup_index)
            .collect::<Vec<_>>();
        assert_eq!(receipts.len(), 1, "the lookup has its actual consume receipt");
        let receipt = receipts[0];
        assert!(receipt.step >= lookup.step);
        assert!(receipt.order > lookup.order);
        assert_eq!(receipt.owner, lookup.owner);
        assert_eq!(receipt.consumption, consumption);
        assert_same_source_site(&receipt.site, &lookup.site);
        assert_eq!(receipt.value, lookup.value);
        assert_eq!(receipt.view, lookup.view);
        assert!(machine.receiving.matches_value(receipt.view, receipt.value));
        let raw = machine.receiving.raw_receipt_fields(receipt.receipt).unwrap();
        assert!(raw.contains(&format!("owner={:?}", receipt.owner)));
        assert!(raw.contains(&format!("view={}", receipt.view.index())));
        assert!(raw.contains(&format!("slot_root={:?}", receipt.site.source_root)));
        assert!(raw.contains(&format!("slot_occurrence={}", receipt.site.occurrence.ordinal())));

        let forces = machine.r312_name_forces.iter()
            .filter(|force| force.lookup == lookup_index)
            .collect::<Vec<_>>();
        if consumption == NameConsumption::Execute {
            assert_eq!(forces.len(), 1, "Execute has one actual Delay force under its receipt");
            let force = forces[0];
            assert!(force.step >= receipt.step);
            assert!(force.order > receipt.order);
            assert_eq!(force.receipt, receipt.receipt);
            assert_eq!(force.owner, receipt.owner);
            assert_eq!(force.owner, ExecutionOwner::Invocation(call.invocation));
            assert_eq!(force.view, receipt.view);
            assert_eq!(force.value, receipt.value);
            assert_same_source_site(&force.site, &receipt.site);
            assert!(matches!(
                machine.executables.get(&force.value.0),
                Some(ExecutableValue::Delay { code, environment })
                    if *code == force.code && *environment == force.environment
            ));
            let completions = machine.r312_name_force_completions.iter()
                .filter(|completion| completion.lookup == lookup_index)
                .collect::<Vec<_>>();
            assert_eq!(completions.len(), 1, "the same receipt's Force returns once");
            let completion = completions[0];
            assert!(completion.order > force.order);
            assert!(completion.step >= force.step);
            assert_eq!(completion.receipt, force.receipt);
            assert_eq!(completion.owner, force.owner);
            assert_eq!(completion.entry_receiver, call.invocation,
                "the actual saved ValueEntry receiver retains the Force invocation id");
            assert!(matches!(completion.return_owner, ExecutionOwner::Invocation(_)),
                "the resumed Force result is consumed by an actual invocation");
            // Request/resume may consume the saved ordinary ValueEntry under
            // its replay owner. Keep the original entry receiver and return
            // owner separate; the receipt/view/site/formal join authenticates
            // this Force without claiming those invocation ids are equal.
            assert_eq!(completion.parameter, call.formal,
                "the returned ValueEntry is the saved entry for this call's formal");
            assert_same_source_site(&completion.site, &force.site);
            assert_eq!(completion.input_view, force.view);
            assert_eq!(completion.input_value, force.value);
            assert!(machine.receiving.matches_value(completion.output_view, completion.output_value));
        } else {
            assert!(forces.is_empty(), "Observe does not manufacture a Force");
            assert!(machine.r312_name_force_completions.iter()
                .all(|completion| completion.lookup != lookup_index));
        }
    }

    fn assert_callee_frame_survived_request(machine: &Machine, call: &NameReceiptCallObservation) {
        let pending = machine.r312_frame_events.iter().filter_map(|event| match event {
            R312FrameEvent::PendingCalleeAtRequest {
                step, order, request, frame_id, request_site, owner, apply_site,
                callee, argument, environment,
            } if apply_site.source_root == call.call_site.source_root
                && apply_site.occurrence == call.call_site.occurrence
                && *callee == call.callee_code.map(Label)
                && *argument == Label(call.argument_code)
                && *environment == call.argument_environment =>
                Some((*step, *order, *request, *frame_id, request_site, *owner)),
            _ => None,
        }).collect::<Vec<_>>();
        assert_eq!(pending.len(), 1, "the exact Apply's Callee frame is present at one Request");

        let returned = machine.r312_frame_events.iter().filter_map(|event| match event {
            R312FrameEvent::CalleeReturned {
                step, order, frame_id, owner, apply_site, callee, argument, environment,
                value, view, interface, dispatch, provider,
            } if apply_site.source_root == call.call_site.source_root
                && apply_site.occurrence == call.call_site.occurrence
                && *callee == call.callee_code.map(Label)
                && *argument == Label(call.argument_code)
                && *environment == call.argument_environment =>
                Some((*step, *order, *frame_id, *value, *view, *interface, *dispatch, provider, *owner)),
            _ => None,
        }).collect::<Vec<_>>();
        assert_eq!(returned.len(), 1, "the same saved Callee frame is consumed once after resume");
        let (pending_step, pending_order, request_id, frame_id, request_site, request_owner) = pending[0];
        let (return_step, return_order, returned_frame_id, returned_callee, returned_view,
            returned_interface, returned_dispatch, provider, return_owner) = returned[0];
        assert!(pending_order < return_order);
        assert!(pending_step < return_step);
        assert!(return_order < call.selected_order);
        assert_eq!(returned_frame_id, frame_id,
            "dynamic frame identity survives suspension even when current owner changes");
        assert_eq!(returned_callee, call.callee_value);
        assert_eq!(returned_view, call.callee_view);
        assert_eq!(returned_interface, call.callee_interface);
        assert_eq!(returned_dispatch, call.callee_dispatch);
        assert!(matches!(request_owner, ExecutionOwner::Invocation(_)));
        assert!(matches!(return_owner, ExecutionOwner::Invocation(_)));
        // A resumed machine may execute the retained Callee frame under a
        // different current owner. Keep the two dynamic owners as distinct
        // observations; the saved frame is joined by its exact Apply labels,
        // caller environment and request/return order.
        assert_same_source_site(provider, &call.callee_site);
        assert_ne!(request_site.occurrence, call.call_site.occurrence);
        let actual_requests = machine.r312_frame_events.iter().filter_map(|event| match event {
            R312FrameEvent::RequestObserved { request, site, owner, .. }
                if *request == request_id && *owner == request_owner => Some(site),
            _ => None,
        }).collect::<Vec<_>>();
        assert_eq!(actual_requests.len(), 1, "saved frame lineage joins the one actual Request");
        assert_same_source_site(actual_requests[0], request_site);
    }

    fn source_apply_labels_match_call(
        program: &RuntimeProgram,
        call: &NameReceiptCallObservation,
        callee_label: usize,
        argument_label: usize,
    ) -> bool {
        let Ok(Some(source)) = program._hir.local_source_for(&call.call_site.source_root) else {
            return false;
        };
        let Some(apply) = source.expressions().iter()
            .find(|expression| expression.occurrence == call.call_site.occurrence) else {
            return false;
        };
        let yu_hir::shadow::LocalSourceForm::Apply { callee, argument, .. } = &apply.form else {
            return false;
        };
        let (Some(source_callee), Some(source_argument)) =
            (source.expression(callee), source.expression(argument)) else {
                return false;
            };
        let (Some(native_callee), Some(native_argument)) =
            (program.code.get(callee_label), program.code.get(argument_label)) else {
                return false;
            };
        source_callee.occurrence == native_callee.site.occurrence
            && source_argument.occurrence == native_argument.site.occurrence
            && native_callee.site.source_root == call.call_site.source_root
            && native_argument.site.source_root == call.call_site.source_root
    }

    fn assert_source_callee_return_observe_witness(
        machine: &Machine,
        call: &NameReceiptCallObservation,
    ) {
        let callee_label = call.callee_code.expect("source Apply retains its actual callee label");
        let apply_label = machine.program.code.iter().position(|code| {
            code.site.source_root == call.call_site.source_root
                && code.site.occurrence == call.call_site.occurrence
        }).expect("source Apply instruction is present in the retained RuntimeProgram");
        let apply_code = &machine.program.code[apply_label];
        let Instruction::Apply { callee, argument } = apply_code.instruction else {
            panic!("the retained owner occurrence must compile to Apply");
        };
        assert_eq!(callee.0, callee_label);
        assert_eq!(argument.0, call.argument_code);
        assert!(source_apply_labels_match_call(
            &machine.program, call, callee_label, call.argument_code,
        ));
        assert!(!source_apply_labels_match_call(
            &machine.program, call, call.argument_code, callee_label,
        ), "swapping the source Apply labels must be rejected");
        let other_apply = machine.program.code.iter().enumerate().find_map(|(index, code)| {
            (index != apply_label && matches!(code.instruction, Instruction::Apply { .. }))
                .then_some(index)
        });
        if let Some(other_apply) = other_apply {
            assert!(!source_apply_labels_match_call(
                &machine.program, call, other_apply, call.argument_code,
            ), "a label owned by another source node must be rejected");
        }

        let Some(ExecutableValue::Delay { code, environment }) =
            machine.executables.get(&call.delay_value.0) else {
                panic!("the actual receiver allocated a Delay for the source argument");
            };
        assert_eq!(*code, Label(call.argument_code));
        assert_eq!(*environment, call.argument_environment);
        assert!(machine.receiving.matches_value(call.delay_view, call.delay_value));
        assert_ne!(call.delay_value, call.callee_value);
        assert_ne!(call.delay_view, call.callee_view,
            "the argument Delay retains its own received view");
        assert_ne!(call.closure_environment, call.argument_environment,
            "the saved closure environment cannot stand in for the caller environment");

        let lookups = machine.r312_name_lookups.iter().filter(|lookup| {
            lookup.code == call.argument_code
                && lookup.site.source_root == call.call_site.source_root
                && lookup.site.occurrence == machine.program.code[call.argument_code].site.occurrence
        }).collect::<Vec<_>>();
        assert_eq!(lookups.len(), 1, "the exact argument Name is read once after dispatch");
        let lookup = lookups[0];
        assert!(lookup.order > call.selected_order);
        assert_eq!(lookup.consumption, NameConsumption::Observe);
        assert_eq!(lookup.environment, call.argument_environment);
        assert_ne!(call.delay_view, lookup.view,
            "the Delay view cannot replace the later Name value view");
        assert!(!machine.receiving.matches_value(call.callee_view, call.delay_value),
            "a different received value/view pair must be rejected");
        assert!(matches!(&machine.value(lookup.value).unwrap().kind,
            RuntimeValueKind::Integer(value) if value.as_ref() == "7"));
        assert!(machine.r312_name_forces.iter().all(|force| force.lookup
            != machine.r312_name_lookups.iter().position(|candidate| std::ptr::eq(candidate, lookup)).unwrap()));
    }

    fn r313_instruction_summary(instruction: &Instruction) -> String {
        match instruction {
            Instruction::Apply { callee, argument } =>
                format!("Apply(callee={}, argument={})", callee.0, argument.0),
            Instruction::Name { resolution, consumption } =>
                format!("Name(resolution={resolution:?}, consumption={consumption:?})"),
            other => format!("{}", std::any::type_name_of_val(other)),
        }
    }

    fn r313_watch_source_apply(machine: &mut Machine) {
        let candidates = machine.program.code.iter().filter_map(|apply_code| {
            let Instruction::Apply { callee, argument } = apply_code.instruction else { return None; };
            let (Some(callee_code), Some(argument_code)) = (
                machine.program.code.get(callee.0), machine.program.code.get(argument.0),
            ) else { return None; };
            (matches!(callee_code.instruction, Instruction::Apply { .. })
                && matches!(argument_code.instruction,
                    Instruction::Name { consumption: NameConsumption::Observe, .. })
                && apply_code.site.source_root == argument_code.site.source_root)
                .then(|| apply_code.site.clone())
        }).collect::<Vec<_>>();
        assert_eq!(candidates.len(), 1,
            "fixture has one source Apply with an Apply callee and Observe Name argument");
        machine.r313_watch_apply = Some(candidates[0].clone());
    }

    fn r313_witness_text(
        machine: &Machine,
        call: &NameReceiptCallObservation,
        completed: ValueHandle,
        source_text: &str,
    ) -> String {
        let callee_label = call.callee_code.unwrap();
        let apply_label = machine.program.code.iter().position(|code| {
            code.site.source_root == call.call_site.source_root
                && code.site.occurrence == call.call_site.occurrence
        }).unwrap();
        let source = machine.program._hir.local_source_for(&call.call_site.source_root)
            .unwrap().unwrap();
        let source_root_key = machine.program._hir
            .source_root_source_key(&call.call_site.source_root).unwrap().unwrap();
        let apply = source.expressions().iter()
            .find(|expression| expression.occurrence == call.call_site.occurrence).unwrap();
        let yu_hir::shadow::LocalSourceForm::Apply { callee, argument, .. } = &apply.form else {
            unreachable!();
        };
        let source_callee = source.expression(callee).unwrap();
        let source_argument = source.expression(argument).unwrap();
        let lookup_index = machine.r312_name_lookups.iter().position(|lookup| {
            lookup.code == call.argument_code && lookup.site.occurrence == source_argument.occurrence
        }).unwrap();
        let lookup = &machine.r312_name_lookups[lookup_index];
        let receipt = machine.r312_name_receipts.iter()
            .find(|receipt| receipt.lookup == lookup_index).unwrap();
        let bind = machine.r313_value_entry_binds.iter().find(|bind|
            bind.entry_receiver == call.invocation && bind.parameter == call.formal
        ).unwrap();
        let original_bind = machine.r313_value_entry_binds.iter().find(|bind|
            bind.bound_environment == lookup.environment && bind.bound_cell == lookup.cell
        ).unwrap();
        let mut out = String::new();
        use std::fmt::Write as _;
        let _ = writeln!(out, "claim_class=source-native-evidence; provisional=true; test_only=true");
        let _ = writeln!(out, "source_text={source_text:?}");
        let _ = writeln!(out, "source_file_key=r312-accepted/callee-history.yu");
        let _ = writeln!(out, "pipeline=parse+lower_local_source+CandidateInference::solve(no_conflicts)+RuntimeProgram::from_hir+Machine::run");
        let _ = writeln!(out, "single_hir_runtime_program=true; artifact_local_interns=H0,S0,A0,C0,G0,N0; H0_ptr={:p}; program_ptr={:p}",
            Arc::as_ptr(&machine.program._hir), Arc::as_ptr(&machine.program));
        let _ = writeln!(out, "S0_owner={:?}; source_root_key={source_root_key:?}; A0_cst_key={:?}; apply_scope={:?}; A0_occurrence={:?}; apply_range={:?}; apply_label={}",
            call.call_site.source_root, apply.source, apply.scope,
            call.call_site.occurrence, call.call_site.range, apply_label);
        let _ = writeln!(out, "A0_source_apply={:?}; C0_source_callee={:?}@{:?} scope={:?} cst_key={:?}; G0_source_argument={:?}@{:?} scope={:?} cst_key={:?}",
            apply.form, source_callee.occurrence, source_callee.range, source_callee.scope,
            source_callee.source, source_argument.occurrence, source_argument.range,
            source_argument.scope, source_argument.source);
        let _ = writeln!(out, "runtime_apply={}", r313_instruction_summary(&machine.program.code[apply_label].instruction));
        let _ = writeln!(out, "runtime_callee_label={callee_label}; callee_site={:?}; callee_instruction={}",
            machine.program.code[callee_label].site,
            r313_instruction_summary(&machine.program.code[callee_label].instruction));
        let _ = writeln!(out, "runtime_argument_label={}; argument_site={:?}; argument_instruction={}",
            call.argument_code, machine.program.code[call.argument_code].site,
            r313_instruction_summary(&machine.program.code[call.argument_code].instruction));
        let _ = writeln!(out, "G0_runtime_argument_occurrence={:?}; N0=G0_argument_Name_instruction",
            machine.program.code[call.argument_code].site.occurrence);
        let _ = writeln!(out, "selection_step={}; selection_order={}; callee_value={}; callee_view={}; callee_interface={:?}; callee_dispatch={:?}; callee_provider={:?}",
            call.selected_step, call.selected_order, call.callee_value.0, call.callee_view.index(),
            call.callee_interface, call.callee_dispatch, call.callee_site);
        for event in &machine.r312_frame_events {
            match event {
                R312FrameEvent::RequestObserved { step, order, request, site, owner } => {
                    let _ = writeln!(out, "request step={step} order={order} id={request} site={site:?} owner={owner:?}");
                }
                R312FrameEvent::PendingCalleeAtRequest { step, order, request, frame_id,
                    request_site, owner, apply_site, callee, argument, environment } => {
                    if apply_site.occurrence == call.call_site.occurrence {
                        let _ = writeln!(out, "pending_callee step={step} order={order} request={request} frame=F{frame_id} request_site={request_site:?} request_owner={owner:?} apply_site={apply_site:?} callee_label={callee:?} argument_label={} caller_environment={environment}", argument.0);
                    }
                }
                R312FrameEvent::CalleeReturned { step, order, frame_id, owner, apply_site,
                    callee, argument, environment, value, view, interface, dispatch, provider } => {
                    if apply_site.occurrence == call.call_site.occurrence {
                        let _ = writeln!(out, "callee_return step={step} order={order} frame=F{frame_id} return_owner={owner:?} apply_site={apply_site:?} callee_label={callee:?} argument_label={} caller_environment={environment} value={} view={} interface={interface:?} dispatch={dispatch:?} provider={provider:?}", argument.0, value.0, view.index());
                    }
                }
            }
        }
        let Some(ExecutableValue::Delay { code, environment }) = machine.executables.get(&call.delay_value.0) else { unreachable!() };
        let _ = writeln!(out, "delay value={} code={} environment={} view={}", call.delay_value.0, code.0, environment, call.delay_view.index());
        let _ = writeln!(out, "name_lookup step={} order={} site={:?} owner={:?} environment={} parameter={:?} cell={} value={} view={} consumption={:?}",
            lookup.step, lookup.order, lookup.site, lookup.owner, lookup.environment, lookup.parameter,
            lookup.cell, lookup.value.0, lookup.view.index(), lookup.consumption);
        let _ = writeln!(out, "name_receipt step={} order={} index={} site={:?} owner={:?} value={} view={} consumption={:?}",
            receipt.step, receipt.order, receipt.receipt, receipt.site, receipt.owner,
            receipt.value.0, receipt.view.index(), receipt.consumption);
        let _ = writeln!(out, "value_entry_bind step={} order={} receiver={} parameter={:?} lexical_parent_environment={} lexical_parent_node={:?} binder_at_parent={:?} parent_dispatch={} cells_before_bind={} environments_before_bind={} received=(value={},view={},interface={:?},dispatch={:?}) bound_cell={} bound_environment={} cells_after_bind={} environments_after_bind={}",
            bind.step, bind.order, bind.entry_receiver, bind.parameter,
            bind.binder_parent_environment, bind.binder_parent, bind.binder_at_parent,
            bind.parent_dispatch, bind.cells_before_bind, bind.environments_before_bind,
            bind.received.value.0, bind.received.view.index(), bind.received.interface,
            bind.received.dispatch, bind.bound_cell, bind.bound_environment,
            bind.cells_after_bind, bind.environments_after_bind);
        let _ = writeln!(out, "original_name_caller_bind step={} order={} receiver={} parameter={:?} lexical_parent_environment={} lexical_parent_node={:?} binder_at_parent={:?} parent_dispatch={} cells_before_bind={} environments_before_bind={} received=(value={},view={},interface={:?},dispatch={:?}) bound_cell={} bound_environment={} cells_after_bind={} environments_after_bind={}",
            original_bind.step, original_bind.order, original_bind.entry_receiver, original_bind.parameter,
            original_bind.binder_parent_environment, original_bind.binder_parent, original_bind.binder_at_parent,
            original_bind.parent_dispatch, original_bind.cells_before_bind, original_bind.environments_before_bind,
            original_bind.received.value.0, original_bind.received.view.index(), original_bind.received.interface,
            original_bind.received.dispatch, original_bind.bound_cell, original_bind.bound_environment,
            original_bind.cells_after_bind, original_bind.environments_after_bind);
        let return_snapshot = machine.r313_return_snapshot.as_ref().unwrap();
        let _ = writeln!(out, "callee_return_arena_snapshot frame=F{} apply_site={:?} sizes=(cells:{},environments:{},values:{},receiving_views:{}) receiving_scan_truncated={}",
            return_snapshot.frame_id, return_snapshot.apply_site,
            return_snapshot.cells.len(), return_snapshot.environments.len(),
            return_snapshot.values.len(), return_snapshot.receiving_views.len(),
            return_snapshot.receiving_scan_truncated);
        if let Some(initialization) = &return_snapshot.source_name_initialization {
            let _ = writeln!(out, "return_source_name_initialization code={} environment={} parameter={:?} cell={} value={} view={} interface={:?} dispatch={:?}",
                return_snapshot.argument_code.0, return_snapshot.caller_environment,
                initialization.parameter, initialization.cell, initialization.received.value.0,
                initialization.received.view.index(), initialization.received.interface,
                initialization.received.dispatch);
        } else {
            let _ = writeln!(out, "return_source_name_initialization=unavailable");
        }
        for (index, cell) in return_snapshot.cells.iter().enumerate() {
            match cell {
                Some(received) => {
                    let _ = writeln!(out, "return_cell[{index}]=Some(value={},view={},interface={:?},dispatch={:?})",
                        received.value.0, received.view.index(), received.interface, received.dispatch);
                }
                None => { let _ = writeln!(out, "return_cell[{index}]=None"); }
            }
        }
        for (index, environment) in return_snapshot.environments.iter().enumerate() {
            let _ = writeln!(out, "return_environment[{index}]=(parent={:?},binder={:?},dispatch={:?})",
                environment.parent, environment.binder, environment.dispatch);
        }
        for (index, value) in return_snapshot.values.iter().enumerate() {
            let _ = writeln!(out, "return_value[{index}]=(source={:?},kind={:?})", value.source, value.kind);
        }
        for (index, fields) in return_snapshot.receiving_views.iter().enumerate() {
            let chain = return_snapshot.receiving_image_chains.get(index).map(String::as_str).unwrap_or("missing");
            let _ = writeln!(out, "return_receiving_view[{index}]={fields}; image_chain={chain}");
        }
        let _ = writeln!(out, "post_run_arena_sizes=(cells:{},environments:{},values:{})", machine.cells.len(), machine.environments.len(), machine.values.len());
        let _ = writeln!(out, "completed_value={} kind={:?}; requests_total={}",
            completed.0, machine.values[completed.0].kind, machine.next_request);
        out
    }

    fn r314_lean_runtime_site(
        machine: &Machine,
        parsed: &ParsedFile,
        site: &SourceSite,
    ) -> Result<String, super::super::RuntimeUnavailable> {
        let hir = &machine.program._hir;
        if !hir.owns_source_root(&site.source_root) || !hir.owns_occurrence(&site.occurrence) {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let source_key = hir.occurrence_source_key(&site.occurrence)
            .map_err(|_| super::super::RuntimeUnavailable::InvalidSourceReference)?
            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        if !parsed.owns_source_key(source_key) {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let source = hir.local_source_for(&site.source_root)
            .map_err(|_| super::super::RuntimeUnavailable::InvalidSourceReference)?
            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        if !source.expressions().iter().any(|expression|
            expression.occurrence == site.occurrence && expression.range == site.range
                && expression.source == *source_key
        ) {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let Some(definition_root) = site.source_root.definition_root() else {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        };
        let binding = hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.definition_root() == definition_root => Some(binding),
            _ => None,
        }).ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        let (realm, path) = match binding.id().module() {
            yu_hir::ModuleId::SourceRoot(file) => (file.key().realm(), file.key().normalized_workspace_relative_path()),
        };
        Ok(format!("{{ bindingName := {}, realm := {}, path := {}, sameNameOrdinal := {}, occurrence := {}, startByte := {}, endByte := {} }}",
            super::super::program::r314_lean_string(binding.id().spelling()),
            super::super::program::r314_lean_string(realm), super::super::program::r314_lean_string(path),
            binding.id().same_name_ordinal(),
            site.occurrence.ordinal(), site.range.start, site.range.end))
    }

    fn r314_lean_source_root_identity(
        machine: &Machine,
        parsed: &ParsedFile,
        root: &yu_hir::SourceRootId,
    ) -> Result<String, super::super::RuntimeUnavailable> {
        use yu_hir::SourceRootId as R;
        let hir = &machine.program._hir;
        if !hir.owns_source_root(root) {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        Ok(match root {
            R::Definition(definition_root) => {
                let binding = hir.items().iter().find_map(|item| match item {
                    yu_hir::HirItem::Binding(binding)
                        if binding.definition_root() == definition_root => Some(binding),
                    _ => None,
                }).ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
                let (realm, path) = super::super::program::r314_module_fields(binding.id().module())?;
                format!("SourceRootIdentity.definition {} {} {} {}",
                    super::super::program::r314_lean_string(binding.id().spelling()),
                    super::super::program::r314_lean_string(realm),
                    super::super::program::r314_lean_string(path), binding.id().same_name_ordinal())
            }
            R::Expression(expression_root) => {
                let occurrence = expression_root.occurrence();
                let key = hir.occurrence_source_key(occurrence)
                    .map_err(|_| super::super::RuntimeUnavailable::InvalidSourceReference)?
                    .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
                if !parsed.owns_source_key(key) || !hir.owns_occurrence(occurrence) {
                    return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
                }
                format!("SourceRootIdentity.expression {}", occurrence.ordinal())
            }
            R::Member(member_root) => {
                let (realm, path) = super::super::program::r314_module_fields(member_root.module())?;
                if !parsed.owns_source_key(member_root.declaration_source_key())
                    || !parsed.owns_source_key(member_root.member_source_key())
                {
                    return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
                }
                let kind = match member_root.kind() {
                    yu_hir::SourceMemberKind::Role => "role",
                    yu_hir::SourceMemberKind::Implementation => "implementation",
                };
                format!("SourceRootIdentity.member {} {} {} {} {}",
                    super::super::program::r314_lean_string(realm),
                    super::super::program::r314_lean_string(path),
                    super::super::program::r314_lean_string(kind),
                    super::super::program::r314_key_position(parsed, member_root.declaration_source_key())?,
                    super::super::program::r314_key_position(parsed, member_root.member_source_key())?)
            }
        })
    }

    fn r314_lean_received(received: ReceivedValue) -> String {
        let interface = match received.interface {
            ParameterRole::Value => "Interface.value",
            ParameterRole::Computation => "Interface.computation",
        };
        format!("{{ value := {}, view := {}, interface := {interface}, dispatch := {} }}",
            received.value.0, received.view.index(), received.dispatch.map_or_else(|| "none".to_owned(), |id| format!("some {id}")))
    }

    fn r314_lean_owner(owner: ExecutionOwner) -> String {
        match owner {
            ExecutionOwner::ModuleRun => "ExecutionOwner.moduleRun".to_owned(),
            ExecutionOwner::Invocation(id) => format!("ExecutionOwner.invocation {id}"),
        }
    }

    fn r323_lean_owner(owner: ExecutionOwner) -> String {
        r314_lean_owner(owner).replace("ExecutionOwner.", "R314Artifact.ExecutionOwner.")
    }

    fn r314_lean_primitive(operation: &yu_hir::shadow::PinnedPrimitiveOp) -> String {
        use yu_hir::shadow::PinnedPrimitiveOp as P;
        let name = match operation {
            P::BoolNot => "BoolNot", P::BoolEq => "BoolEq", P::BoolToString => "BoolToString",
            P::IntAdd => "IntAdd", P::IntSub => "IntSub", P::IntMul => "IntMul", P::IntEq => "IntEq",
            P::IntLt => "IntLt", P::IntLe => "IntLe", P::IntGt => "IntGt", P::IntGe => "IntGe",
            P::IntToString => "IntToString", P::StringConcat => "StringConcat", P::Unsupported(_) => "Unsupported",
        };
        super::super::program::r314_lean_string(name)
    }

    fn r314_lean_operation_identity(
        operation: &yu_hir::shadow::SourceOperationResolution,
        parsed: &ParsedFile,
    ) -> Result<String, super::super::RuntimeUnavailable> {
        let SourceOperationResolution::Resolved(operation) = operation else {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        };
        let (realm, path) = super::super::program::r314_module_fields(&operation.id.family.module)?;
        let visibility = match operation.visibility {
            yu_hir::HirVisibility::Private => "Private",
            yu_hir::HirVisibility::Our => "Our",
            yu_hir::HirVisibility::Public => "Public",
        };
        let family_declaration = super::super::program::r314_key_position(parsed, &operation.id.family.declaration)?;
        let declaration = super::super::program::r314_key_position(parsed, &operation.id.declaration)?;
        let name_position = super::super::program::r314_key_position(parsed, &operation.name_position)?;
        let signature_position = super::super::program::r314_key_position(parsed, &operation.signature_position)?;
        let signature = super::super::program::r314_lean_annotation_type(&operation.signature, parsed)?;
        Ok(format!("{{ name := {}, familyRealm := {}, familyPath := {}, familyDeclaration := {}, declaration := {}, namePosition := {}, signaturePosition := {}, startByte := {}, endByte := {}, visibility := {}, signature := {} }}",
            super::super::program::r314_lean_string(&operation.spelling),
            super::super::program::r314_lean_string(realm), super::super::program::r314_lean_string(path),
            family_declaration, declaration, name_position, signature_position, operation.range.start, operation.range.end,
            super::super::program::r314_lean_string(visibility), signature))
    }

    fn r314_lean_runtime_value(
        machine: &Machine,
        parsed: &ParsedFile,
        index: usize,
        value: &RuntimeValue,
    ) -> Result<String, super::super::RuntimeUnavailable> {
        let source = r314_lean_runtime_site(machine, parsed, &value.source)?;
        let kind = match &value.kind {
            RuntimeValueKind::Unit => "ValueKind.unit".to_owned(),
            RuntimeValueKind::Integer(value) => format!("ValueKind.integer {}", super::super::program::r314_lean_string(value)),
            RuntimeValueKind::Boolean(value) => format!("ValueKind.boolean {value}"),
            RuntimeValueKind::String(value) => format!("ValueKind.string {}", super::super::program::r314_lean_string(value)),
            RuntimeValueKind::Primitive(operation) => format!("ValueKind.primitive {}", r314_lean_primitive(operation)),
            RuntimeValueKind::Tuple(items) => format!("ValueKind.tuple [{}]", items.iter().map(|item| r314_lean_received(item.received)).collect::<Vec<_>>().join(", ")),
            RuntimeValueKind::Variant { tag, payloads } => format!("ValueKind.variant {} [{}]", super::super::program::r314_lean_string(tag), payloads.iter().map(|item| r314_lean_received(item.received)).collect::<Vec<_>>().join(", ")),
            RuntimeValueKind::Record(fields) => format!("ValueKind.record [{}]", fields.iter().map(|(name, item)| format!("({}, {})", super::super::program::r314_lean_string(name), r314_lean_received(item.received))).collect::<Vec<_>>().join(", ")),
            RuntimeValueKind::Closure => "ValueKind.closure".to_owned(),
            RuntimeValueKind::Computation => "ValueKind.computation".to_owned(),
            RuntimeValueKind::Operation(resolution) => {
                format!("ValueKind.operation ({})", r314_lean_operation_identity(resolution, parsed)?)
            }
        };
        let _ = index;
        Ok(format!("{{ source := {source}, kind := {kind} }}"))
    }

    fn r314_lean_receiving_snapshot(
        snapshot: &R313CalleeReturnSnapshot,
    ) -> Result<(String, String), super::super::RuntimeUnavailable> {
        let mut views = Vec::new();
        for (index, raw) in snapshot.receiving_views.iter().enumerate() {
            let fields = raw.split_whitespace().collect::<Vec<_>>();
            if fields.len() != 5 { return Err(super::super::RuntimeUnavailable::InvalidSourceReference); }
            let parse_value = |field: &str, prefix: &str| -> Result<usize, super::super::RuntimeUnavailable> {
                field.strip_prefix(prefix).and_then(|value| value.parse().ok())
                    .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)
            };
            let view_index = parse_value(fields[0], "view_index=")?;
            let value_handle = fields[1].strip_prefix("value_handle=ValueHandle(")
                .and_then(|value| value.strip_suffix(')')).and_then(|value| value.parse::<usize>().ok())
                .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
            let image_raw = fields[2].strip_prefix("image=")
                .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
            let image = if image_raw == "None" { "none".to_owned() }
                else if let Some(value) = image_raw.strip_prefix("Some(").and_then(|value| value.strip_suffix(')')) {
                    format!("some {}", value.parse::<usize>().map_err(|_| super::super::RuntimeUnavailable::InvalidSourceReference)?)
                } else { return Err(super::super::RuntimeUnavailable::InvalidSourceReference); };
            let unknown = fields[3].strip_prefix("unknown=")
                .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
            if unknown != "true" && unknown != "false" { return Err(super::super::RuntimeUnavailable::InvalidSourceReference); }
            let kind = fields[4].strip_prefix("kind=")
                .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
            let kind = match kind {
                "Ordinary" => "ReceivingViewKind.ordinary".to_owned(),
                "RootComp" => "ReceivingViewKind.rootComp".to_owned(),
                other if other.starts_with("CallbackEntry(") => format!("ReceivingViewKind.callbackEntry {}",
                    other.strip_prefix("CallbackEntry(").and_then(|s| s.strip_suffix(')')).and_then(|s| s.parse::<usize>().ok())
                        .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?),
                other if other.starts_with("CallbackResult(") => format!("ReceivingViewKind.callbackResult {}",
                    other.strip_prefix("CallbackResult(").and_then(|s| s.strip_suffix(')')).and_then(|s| s.parse::<usize>().ok())
                        .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?),
                _ => return Err(super::super::RuntimeUnavailable::InvalidSourceReference),
            };
            if view_index != index { return Err(super::super::RuntimeUnavailable::InvalidSourceReference); }
            views.push(format!("{{ index := {view_index}, value := {value_handle}, image := {image}, unknown := {unknown}, kind := {kind} }}"));
        }
        let mut chains = Vec::new();
        for (view, raw) in snapshot.receiving_image_chains.iter().enumerate() {
            if raw.starts_with("error:") { return Err(super::super::RuntimeUnavailable::InvalidSourceReference); }
            let mut links = Vec::new();
            if !raw.is_empty() {
                for item in raw.split(';') {
                    let mut parts = item.split(',');
                    let image = parts.next().and_then(|part| part.strip_prefix("image=")).and_then(|n| n.parse::<usize>().ok())
                        .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
                    let boundary = parts.next().and_then(|part| part.strip_prefix("boundary=")).and_then(|n| n.parse::<usize>().ok())
                        .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
                    let receiver = parts.next().and_then(|part| part.strip_prefix("receiver=")).and_then(|n| n.parse::<usize>().ok())
                        .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
                    if parts.next().is_some() { return Err(super::super::RuntimeUnavailable::InvalidSourceReference); }
                    links.push(format!("{{ image := {image}, boundary := {boundary}, receiver := {receiver} }}"));
                }
            }
            chains.push(format!("{{ view := {view}, links := [{}] }}", links.join(", ")));
        }
        if chains.len() != views.len() { return Err(super::super::RuntimeUnavailable::InvalidSourceReference); }
        Ok((format!("[{}]", views.join(", ")), format!("[{}]", chains.join(", "))))
    }

    fn r314_lean_machine_artifact(
        machine: &Machine,
        call: &NameReceiptCallObservation,
        parsed: &ParsedFile,
        source_text: &str,
    ) -> Result<String, super::super::RuntimeUnavailable> {
        if !machine.name_receipt_calls.iter().any(|entry| std::ptr::eq(entry, call)) {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let snapshot = machine.r313_return_snapshot.as_ref()
            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        if snapshot.apply_site.source_root != call.call_site.source_root
            || snapshot.apply_site.occurrence != call.call_site.occurrence
            || snapshot.apply_site.range != call.call_site.range
            || snapshot.argument_code.0 != call.argument_code
            || snapshot.caller_environment != call.argument_environment
            || snapshot.receiving_scan_truncated
        {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let returns = machine.r312_frame_events.iter().filter_map(|event| match event {
            R312FrameEvent::CalleeReturned { step, order, frame_id, owner, apply_site, callee,
                argument, environment, value, view, interface, provider, .. }
                if apply_site.occurrence == call.call_site.occurrence =>
                    Some((*step, *order, *frame_id, *owner, apply_site, *callee, *argument,
                        *environment, *value, *view, *interface, provider)),
            _ => None,
        }).collect::<Vec<_>>();
        if returns.len() != 1 || returns[0].2 != snapshot.frame_id {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let mut out = machine.program.r314_lean_source_export(parsed, &call.call_site, source_text)?;
        use std::fmt::Write as _;
        let _ = writeln!(out, "def runId : Nat := {}", machine as *const Machine as usize);
        let mut events = Vec::new();
        for event in &machine.r312_frame_events {
            match event {
                R312FrameEvent::RequestObserved { step, order, request, site, owner } => {
                    let site = r314_lean_runtime_site(machine, parsed, site)?;
                    events.push(format!("RuntimeEvent.request {step} {order} {request} ({site}) ({})", r314_lean_owner(*owner)));
                }
                R312FrameEvent::PendingCalleeAtRequest { step, order, request, frame_id,
                    request_site, owner, apply_site, callee, argument, environment }
                    if apply_site.occurrence == call.call_site.occurrence => {
                    let request_site = r314_lean_runtime_site(machine, parsed, request_site)?;
                    let apply_site = r314_lean_runtime_site(machine, parsed, apply_site)?;
                    let callee = callee.map_or_else(|| "none".to_owned(), |label| format!("some {}", label.0));
                    events.push(format!("RuntimeEvent.pendingCallee {step} {order} {request} {frame_id} {} {environment} ({callee}) ({request_site}) ({apply_site}) ({})",
                        argument.0, r314_lean_owner(*owner)));
                }
                R312FrameEvent::CalleeReturned { step, order, frame_id, owner, apply_site, callee,
                    argument, environment, value, view, interface, dispatch, provider }
                    if apply_site.occurrence == call.call_site.occurrence => {
                    let site = r314_lean_runtime_site(machine, parsed, apply_site)?;
                    let provider = r314_lean_runtime_site(machine, parsed, provider)?;
                    let callee = callee.map_or_else(|| "none".to_owned(), |label| format!("some {}", label.0));
                    let interface = match interface { ParameterRole::Value => "Interface.value", ParameterRole::Computation => "Interface.computation" };
                    events.push(format!("RuntimeEvent.calleeReturn {step} {order} {frame_id} {} {environment} {} {} ({callee}) ({site}) ({}) {interface} ({provider})",
                        argument.0, value.0, view.index(), r314_lean_owner(*owner)));
                    let _ = dispatch;
                }
                _ => {}
            }
        }
        let Some(ExecutableValue::Delay { code, environment }) = machine.executables.get(&call.delay_value.0) else {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        };
        events.push(format!("RuntimeEvent.delay {} {} {} {}", call.delay_value.0, code.0, environment, call.delay_view.index()));
        for lookup in machine.r312_name_lookups.iter().filter(|lookup| lookup.code == call.argument_code
            && lookup.site.occurrence == machine.program.code[call.argument_code].site.occurrence) {
            let site = r314_lean_runtime_site(machine, parsed, &lookup.site)?;
            let consumption = super::super::program::r314_lean_string(match lookup.consumption { NameConsumption::Observe => "Observe", NameConsumption::Execute => "Execute" });
            events.push(format!("RuntimeEvent.nameLookup {} {} {} {} {} {} {} ({}) ({}) ({})",
                lookup.step, lookup.order, lookup.environment, lookup.parameter.ordinal(), lookup.cell,
                lookup.value.0, lookup.view.index(), format!("({site})"),
                r314_lean_owner(lookup.owner), consumption));
        }
        for receipt in &machine.r312_name_receipts {
            if receipt.site.occurrence != machine.program.code[call.argument_code].site.occurrence { continue; }
            let site = r314_lean_runtime_site(machine, parsed, &receipt.site)?;
            let consumption = super::super::program::r314_lean_string(match receipt.consumption { NameConsumption::Observe => "Observe", NameConsumption::Execute => "Execute" });
            events.push(format!("RuntimeEvent.nameReceipt {} {} {} {} {} ({}) ({}) ({})",
                receipt.step, receipt.order, receipt.receipt, receipt.value.0, receipt.view.index(),
                format!("({site})"), r314_lean_owner(receipt.owner), consumption));
        }
        for bind in &machine.r313_value_entry_binds {
            events.push(format!("RuntimeEvent.valueBind {} {} {} {} {} {} {} {} {}",
                bind.step, bind.order, bind.entry_receiver, bind.parameter.ordinal(), bind.bound_cell,
                bind.bound_environment, bind.received.value.0, bind.received.view.index(),
                match bind.received.interface { ParameterRole::Value => "Interface.value", ParameterRole::Computation => "Interface.computation" }));
        }
        let _ = writeln!(out, "def events : List RuntimeEvent := [{}]", events.join(",\n"));
        let cells = snapshot.cells.iter().map(|cell| cell.map_or_else(|| "{ value := none }".to_owned(), |received|
            format!("{{ value := some {} }}", r314_lean_received(received)))).collect::<Vec<_>>().join(", ");
        let environments = snapshot.environments.iter().map(|environment|
            -> Result<String, super::super::RuntimeUnavailable> {
            let (kind, id, binder_cell, binder_owner) = match environment.binder.as_ref() {
                None => ("none".to_owned(), "none".to_owned(), "none".to_owned(), "none".to_owned()),
                Some((binder, cell)) => {
                    let (kind, id, root) = match binder {
                        Binder::Parameter(id) => (super::super::program::r314_lean_string("parameter"), id.ordinal(), id.source_root()),
                        Binder::Local(id) => (super::super::program::r314_lean_string("local"), id.ordinal(), id.source_root()),
                        Binder::Catch(id) => (super::super::program::r314_lean_string("catch"), id.ordinal(), id.source_root()),
                    };
                    let owner = r314_lean_source_root_identity(machine, parsed, root)?;
                    (format!("some {kind}"), format!("some {id}"), format!("some {cell}"), format!("some ({owner})"))
                }
            };
            let (dispatch_base, dispatch_word) = environment.dispatch.context.r314_parts();
            let dispatch_base = dispatch_base.map_or_else(|| "none".to_owned(), |value| format!("some {value}"));
            let dispatch_word = dispatch_word.map_or_else(|| "none".to_owned(), |value| format!("some {value}"));
            let substitution = environment.dispatch.substitution.map_or_else(|| "none".to_owned(), |value| format!("some {value}"));
            Ok(format!("{{ parent := {}, binderKind := {kind}, binderId := {id}, binderCell := {binder_cell}, binderOwner := {binder_owner}, dispatchBase := {dispatch_base}, dispatchWord := {dispatch_word}, substitution := {substitution} }}",
                environment.parent.map_or_else(|| "none".to_owned(), |parent| format!("some {parent}"))))
        }).collect::<Result<Vec<_>, _>>()?.join(", ");
        let values = snapshot.values.iter().enumerate().map(|(index, value)|
            r314_lean_runtime_value(machine, parsed, index, value)).collect::<Result<Vec<_>, _>>()?.join(", ");
        let (receiving_views, receiving_chains) = r314_lean_receiving_snapshot(snapshot)?;
        let snapshot_source_name = snapshot.source_name_initialization.as_ref().map_or_else(|| "none".to_owned(), |initialization|
            format!("some {}", r314_lean_received(initialization.received)));
        let snapshot_parameter = snapshot.source_name_initialization.as_ref().map_or_else(|| "none".to_owned(), |initialization|
            format!("some {}", initialization.parameter.ordinal()));
        let apply_site = r314_lean_runtime_site(machine, parsed, &snapshot.apply_site)?;
        let _ = writeln!(out, "def returnSnapshot : ReturnSnapshot := {{ runId := {}, frame := {}, applySite := {}, argumentLabel := {}, callerEnvironment := {}, cells := [{}], environments := [{}], values := [{}], receivingViews := {}, receivingImageChains := {}, sourceNameInitialization := {}, sourceNameParameter := {}, receivingScanTruncated := {} }}",
            machine as *const Machine as usize, snapshot.frame_id, apply_site, snapshot.argument_code.0, snapshot.caller_environment, cells,
            environments, values, receiving_views, receiving_chains, snapshot_source_name, snapshot_parameter,
            snapshot.receiving_scan_truncated);
        let _ = writeln!(out, "end R314Artifact");
        Ok(out)
    }

    fn r315_lean_binding_artifact(
        machine: &Machine,
        parsed: &ParsedFile,
        source_text: &str,
        snapshot: &R313CalleeReturnSnapshot,
    ) -> Result<String, super::super::RuntimeUnavailable> {
        use std::fmt::Write as _;
        use yu_hir::{HirItem, SourceRootId};
        let owned_snapshot = machine.r313_return_snapshot.as_ref()
            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        if !std::ptr::eq(snapshot, owned_snapshot) {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let bindings = machine.program._hir.items().iter().filter_map(|item| match item {
            HirItem::Binding(binding) if binding.id().spelling() == "make" => Some(binding),
            _ => None,
        }).collect::<Vec<_>>();
        let [binding] = bindings.as_slice() else {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        };
        let root = SourceRootId::Definition(binding.definition_root().clone());
        if !machine.program._hir.owns_source_root(&root) {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let source = machine.program._hir.local_source_for(&root)
            .map_err(|_| super::super::RuntimeUnavailable::InvalidSourceReference)?
            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        let make_applies = machine.program.code.iter().filter(|code|
            code.site.source_root == root && matches!(code.instruction, Instruction::Apply { .. })
        ).collect::<Vec<_>>();
        let apply = *make_applies.first()
            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        let mut make_tree = machine.program.r314_lean_source_export(parsed, &apply.site, source_text)?;
        if make_applies.iter().any(|code| !source.expressions().iter().any(|expr|
            expr.occurrence == code.site.occurrence && expr.range == code.site.range
        )) {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        make_tree = make_tree
            .replacen("import Lean\nnamespace R314Artifact", "\nnamespace R315MakeArtifact", 1)
            .replace("end R314Artifact", "end R315MakeArtifact");

        let use_observations = machine.r315_module_uses.iter().filter(|observation|
            observation.definition == *binding.id()
        ).collect::<Vec<_>>();
        let [use_observation] = use_observations.as_slice() else {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        };
        let expected_cell = *machine.program.definition_indices.get(binding.id())
            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        if expected_cell != use_observation.cell
            || use_observation.site.source_root == root
            || use_observation.code >= machine.program.code.len()
            || use_observation.code != machine.program.code.iter().position(|code|
                code.site.source_root == use_observation.site.source_root
                    && code.site.occurrence == use_observation.site.occurrence
                    && code.site.range == use_observation.site.range
                    && matches!(&code.instruction,
                        Instruction::Name { resolution: LocalSourceResolution::ModuleDef(id), .. }
                            if id == binding.id())
            ).ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?
        {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let cell_value = snapshot.cells.get(expected_cell).copied().flatten()
            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        if cell_value.interface != ParameterRole::Value {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let value = snapshot.values.get(cell_value.value.0)
            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        let ExecutableValue::Closure { parameter, role, body, environment, .. } = machine.executables
            .get(&cell_value.value.0).ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?
        else {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        };
        let provider_environment = *environment;
        if value.source.source_root != root || parameter.source_root() != &root
            || *role != ParameterRole::Value
            || provider_environment >= snapshot.environments.len()
            || use_observation.environment >= snapshot.environments.len()
        {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }

        let indexes = yu_hir::shadow::index_source_exports(
            ModuleIdentity::source_root(binding.id().module().file().clone()),
            parsed,
        ).map_err(|_| super::super::RuntimeUnavailable::InvalidSourceReference)?;
        let declarations = indexes.declarations.iter().filter(|declaration|
            declaration.name.as_deref() == Some("make")
                && declaration.range == *binding.range()
                && !declaration.recovered
        ).collect::<Vec<_>>();
        let [declaration] = declarations.as_slice() else {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        };
        let module_binding_rows = machine.program._hir.items().iter().filter_map(|item| match item {
            HirItem::Binding(binding) => Some(binding),
            _ => None,
        }).map(|binding| -> Result<String, super::super::RuntimeUnavailable> {
            let rows = indexes.declarations.iter().filter(|declaration|
                declaration.name.as_deref() == Some(binding.id().spelling())
                    && declaration.range == *binding.range()
                    && !declaration.recovered
            ).collect::<Vec<_>>();
            let [declaration] = rows.as_slice() else {
                return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
            };
            let cell = *machine.program.definition_indices.get(binding.id())
                .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
            let (realm, path) = super::super::program::r314_module_fields(binding.id().module())?;
            let binding_root = SourceRootId::Definition(binding.definition_root().clone());
            let binding_source = machine.program._hir.local_source_for(&binding_root)
                .map_err(|_| super::super::RuntimeUnavailable::InvalidSourceReference)?
                .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
            let annotation = super::super::program::r314_lean_annotation(binding_source.annotation(), parsed, &binding_root)?;
            Ok(format!("{{ name := {}, realm := {}, path := {}, sameNameOrdinal := {}, definitionRoot := {}, declaration := {}, bindingAnnotation := {}, hirVisibility := {}, sourceIndexPublic := {}, runtimeCell := {} }}",
                super::super::program::r314_lean_string(binding.id().spelling()),
                super::super::program::r314_lean_string(realm), super::super::program::r314_lean_string(path),
                binding.id().same_name_ordinal(),
                format!("R314Artifact.{}", r314_lean_source_root_identity(machine, parsed, &SourceRootId::Definition(binding.definition_root().clone()))?),
                super::super::program::r314_key_position(parsed, &declaration.source)?,
                annotation,
                super::super::program::r314_lean_string(&format!("{:?}", binding.visibility())),
                declaration.public, cell))
        }).collect::<Result<Vec<_>, _>>()?.join(", ");
        let declaration_position = super::super::program::r314_key_position(parsed, &declaration.source)?;
        let binding_annotation = super::super::program::r314_lean_annotation(source.annotation(), parsed, &root)?;
        let definition_identity = format!("R314Artifact.{}", r314_lean_source_root_identity(machine, parsed, &root)?);
        let use_site = r314_lean_runtime_site(machine, parsed, &use_observation.site)?;
        let use_code = machine.program.code.get(use_observation.code)
            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        let (spelling, resolution, scope) = {
            let local_source = machine.program._hir.local_source_for(&use_observation.site.source_root)
                .map_err(|_| super::super::RuntimeUnavailable::InvalidSourceReference)?
                .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
            let expression = local_source.expressions().iter().find(|expression|
                expression.occurrence == use_observation.site.occurrence
            ).ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
            if expression.range != use_observation.site.range { return Err(super::super::RuntimeUnavailable::InvalidSourceReference); }
            let yu_hir::shadow::LocalSourceForm::Name { spelling, resolution } = &expression.form else {
                return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
            };
            (spelling.clone(), resolution.clone(), expression.scope.clone())
        };
        if spelling.as_ref() != "make"
            || !matches!(&resolution, LocalSourceResolution::ModuleDef(id) if id == binding.id())
            || !matches!(&use_code.instruction,
                Instruction::Name { resolution: LocalSourceResolution::ModuleDef(id), consumption }
                    if id == binding.id() && *consumption == use_observation.consumption)
        {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let scope = format!("R314Artifact.{}", super::super::program::r314_lean_scope(&scope, parsed)?);
        let consumption = super::super::program::r314_lean_string(match use_observation.consumption {
            NameConsumption::Observe => "Observe", NameConsumption::Execute => "Execute",
        });
        let visibility = super::super::program::r314_lean_string(&format!("{:?}", binding.visibility()));
        let initializer = source.body().ordinal();
        let provider_site = r314_lean_runtime_site(machine, parsed, &value.source)?;
        let use_environment_frame = snapshot.environments.get(use_observation.environment)
            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        let (env_kind, env_id, env_cell, env_owner) = match use_environment_frame.binder.as_ref() {
            None => ("none".to_owned(), "none".to_owned(), "none".to_owned(), "none".to_owned()),
            Some((binder, cell)) => {
                let (kind, id, owner) = match binder {
                    Binder::Parameter(id) => ("parameter", id.ordinal(), id.source_root()),
                    Binder::Local(id) => ("local", id.ordinal(), id.source_root()),
                    Binder::Catch(id) => ("catch", id.ordinal(), id.source_root()),
                };
                (format!("some {}", super::super::program::r314_lean_string(kind)),
                    format!("some {id}"), format!("some {cell}"),
                    format!("some (R314Artifact.{})", r314_lean_source_root_identity(machine, parsed, owner)?))
            }
        };
        let (dispatch_base, dispatch_word) = use_environment_frame.dispatch.context.r314_parts();
        let optional_nat = |value: Option<usize>| value.map_or_else(|| "none".to_owned(), |n| format!("some {n}"));
        let dispatch_substitution = optional_nat(use_environment_frame.dispatch.substitution);
        let hir_visibility_public = declaration.public;
        let resolution = format!("R314Artifact.{}", super::super::program::r314_lean_resolution(&resolution, &use_observation.site.source_root)?);
        let mut out = String::new();
        out.push_str(&make_tree);
        out.push_str("\nend R315MakeArtifact\n\nnamespace R315Artifact\n");
        out.push_str("structure BindingUsePublication where\n  makeRoot : R315MakeArtifact.RootBinding\n  makeDefinitionRoot : R314Artifact.SourceRootIdentity\n  declaration : R314Artifact.Position\n  bindingAnnotation : Option R314Artifact.Annotation\n  hirVisibility : String\n  sourceIndexPublic : Bool\n  initializer : Nat\n  useSite : R314Artifact.RuntimeSite\n  useOwner : R314Artifact.ExecutionOwner\n  useStep : Nat\n  useEnvironment : Nat\n  useScope : R314Artifact.ScopeTag\n  resolution : R314Artifact.Resolution\n  consumes : String\n  globalCell : Nat\n  cellValue : Nat\n  cellView : Nat\n  cellInterface : R314Artifact.Interface\n  providerSite : R314Artifact.RuntimeSite\n  providerFormal : Nat\n  providerBody : Nat\n  providerEnvironment : Nat\n  providerEnvironmentParent : Option Nat\n  providerInterfaceIsValue : Bool\n  useEnvironmentParent : Option Nat\n  useEnvironmentBinderKind : Option String\n  useEnvironmentBinderId : Option Nat\n  useEnvironmentBinderCell : Option Nat\n  useEnvironmentBinderOwner : Option R314Artifact.SourceRootIdentity\n  dispatchBase : Option Nat\n  dispatchWord : Option Nat\n  substitution : Option Nat\n  runId : Nat\n  deriving Repr\n");
        out.push_str("structure ModuleBindingRow where\n  name : String\n  realm : String\n  path : String\n  sameNameOrdinal : Nat\n  definitionRoot : R314Artifact.SourceRootIdentity\n  declaration : R314Artifact.Position\n  bindingAnnotation : Option R314Artifact.Annotation\n  hirVisibility : String\n  sourceIndexPublic : Bool\n  runtimeCell : Nat\n  deriving Repr\n");
        let _ = writeln!(out, "def moduleBindingsInSourceOrder : List ModuleBindingRow := [{}]", module_binding_rows);
        let provider_parent = snapshot.environments.get(provider_environment).and_then(|environment| environment.parent);
        let use_parent = use_environment_frame.parent;
        let _ = writeln!(out, "def makeBindingUse : BindingUsePublication := {{ makeRoot := R315MakeArtifact.rootBinding, makeDefinitionRoot := {definition_identity}, declaration := {declaration_position}, bindingAnnotation := {binding_annotation}, hirVisibility := {visibility}, sourceIndexPublic := {hir_visibility_public}, initializer := {initializer}, useSite := {use_site}, useOwner := {}, useStep := {}, useEnvironment := {}, useScope := {scope}, resolution := {resolution}, consumes := {consumption}, globalCell := {expected_cell}, cellValue := {}, cellView := {}, cellInterface := R314Artifact.Interface.value, providerSite := {provider_site}, providerFormal := {}, providerBody := {}, providerEnvironment := {}, providerEnvironmentParent := {}, providerInterfaceIsValue := {}, useEnvironmentParent := {}, useEnvironmentBinderKind := {env_kind}, useEnvironmentBinderId := {env_id}, useEnvironmentBinderCell := {env_cell}, useEnvironmentBinderOwner := {env_owner}, dispatchBase := {}, dispatchWord := {}, substitution := {}, runId := {} }}",
            format!("R314Artifact.{}", r314_lean_owner(use_observation.owner)), use_observation.step, use_observation.environment, cell_value.value.0,
            cell_value.view.index(), parameter.ordinal(), body.0, provider_environment,
            optional_nat(provider_parent), *role == ParameterRole::Value, optional_nat(use_parent),
            optional_nat(dispatch_base), optional_nat(dispatch_word), dispatch_substitution,
            machine as *const Machine as usize);
        out.push_str("end R315Artifact\n");
        Ok(out)
    }

    fn r323_lean_operation_artifact(
        machine: &Machine,
        call: &NameReceiptCallObservation,
        parsed: &ParsedFile,
        source_text: &str,
    ) -> Result<String, super::super::RuntimeUnavailable> {
        use std::fmt::Write as _;
        fn witness_row(
            machine: &Machine,
            parsed: &ParsedFile,
            witness: &R323FrameWitness,
        ) -> Result<String, super::super::RuntimeUnavailable> {
            Ok(match witness {
                R323FrameWitness::Callee { frame_id, callee, argument, environment, site } => {
                    let code_ref = |label: Label| -> Result<String, super::super::RuntimeUnavailable> {
                        let code = machine.program.code.get(label.0)
                            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
                        let site = r314_lean_runtime_site(machine, parsed, &code.site)?;
                        Ok(format!("{{ label := {}, site := {site} }}", label.0))
                    };
                    let callee = callee.map(|label| code_ref(label).map(|row| format!("some ({row})")))
                        .transpose()?.unwrap_or_else(|| "none".to_owned());
                    let argument = code_ref(*argument)?;
                    let site = r314_lean_runtime_site(machine, parsed, site)?;
                    format!("R323Frame.callee {{ frameId := {frame_id}, callee := {callee}, argument := {argument}, environment := {environment}, site := {site} }}")
                }
                R323FrameWitness::BlockExpression { block, next, environment } => {
                    let label = machine.program.code.iter().position(|candidate| Arc::ptr_eq(candidate, block))
                        .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
                    let site = r314_lean_runtime_site(machine, parsed, &block.site)?;
                    format!("R323Frame.blockExpression {{ codeLabel := {label}, codeSite := {site}, next := {next}, environment := {environment} }}")
                }
                R323FrameWitness::RootCompReturn { execution } =>
                    format!("R323Frame.rootCompReturn {{ view := {}, receipt := {}, occurrence := {} }}",
                        execution.view.index(), execution.receipt.index(), execution.occurrence),
                R323FrameWitness::Owner(owner) =>
                    format!("R323Frame.owner ({})", r323_lean_owner(*owner)),
                R323FrameWitness::Unsupported =>
                    return Err(super::super::RuntimeUnavailable::InvalidSourceReference),
            })
        }
        if !machine.name_receipt_calls.iter().any(|entry| std::ptr::eq(entry, call))
            || machine.r312_observations_truncated
        {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let _source_owner = machine.program.r314_lean_source_export(parsed, &call.call_site, source_text)?;
        let make_root = machine.program._hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.id().spelling() == "make" =>
                Some(yu_hir::SourceRootId::Definition(binding.definition_root().clone())),
            _ => None,
        }).ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        let requests = machine.r323_request_observations.iter().filter(|request|
            request.declaration.spelling.as_ref() == "tick"
                && request.source.source_root == make_root
        ).collect::<Vec<_>>();
        let [request] = requests.as_slice() else {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        };
        let run_id = machine as *const Machine as usize;
        if request.run_id != run_id || !request.owner_live
            || !matches!(request.owner, ExecutionOwner::Invocation(_))
            || !machine.receiving.matches_value(request.payload.view, request.payload.value)
            || !machine.program._hir.owns_source_root(&request.source.source_root)
        {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let templates = machine.r323_template_observations.iter().filter(|template|
            template.request == request.request
        ).collect::<Vec<_>>();
        let [template_observation] = templates.as_slice() else {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        };
        if template_observation.run_id != run_id
        {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let template = machine.resume_templates.get(template_observation.template)
            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        if template.original_event != request.request
            || !Arc::ptr_eq(&template.declaration, &request.declaration)
            || !r323_live_template_matches(template, template_observation)
        {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let owner_nodes = template.nodes.iter().enumerate().filter_map(|(index, node)|
            matches!(node, TemplateNode::Owner { .. }).then_some(index)
        ).collect::<Vec<_>>();
        let owner_replays = machine.r323_owner_replay_observations.iter().filter(|replay|
            replay.request == request.request && replay.template == template_observation.template
        ).collect::<Vec<_>>();
        let mut replay_node_ids = owner_replays.iter().map(|replay| replay.node).collect::<Vec<_>>();
        replay_node_ids.sort_unstable();
        if owner_replays.len() != owner_nodes.len() || replay_node_ids != owner_nodes
            || owner_replays.iter().any(|replay| {
                let invocation_sites_match = match replay.owner {
                    ExecutionOwner::Invocation(id) => machine.invocations.get(id).is_some_and(|invocation|
                        replay.call_site.as_ref().is_some_and(|site| r323_same_site(site, &invocation.call))
                        && replay.provider_site.as_ref().is_some_and(|site| r323_same_site(site, &invocation.provider))),
                    ExecutionOwner::ModuleRun => replay.call_site.is_none() && replay.provider_site.is_none(),
                };
                if replay.run_id != run_id || !replay.owner_live
                    || replay.owned == replay.resolved_active
                    || (replay.resolved_active && replay.owner != replay.resolved)
                    || (!replay.resolved_active && !matches!(replay.owner, ExecutionOwner::Invocation(_)))
                    || !invocation_sites_match
                    || Machine::resolve_control(replay.original,
                        &replay.control.iter().copied().collect::<HashMap<_, _>>()) != replay.resolved
                {
                    return true;
                }
                !matches!(template.nodes.get(replay.node), Some(TemplateNode::Owner { inner, original })
                    if *original == replay.original && *inner + 1 == replay.node)
            })
        {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let outer_callees = machine.r312_frame_events.iter().filter_map(|event| match event {
            R312FrameEvent::PendingCalleeAtRequest { request: id, frame_id, owner, apply_site, .. }
                if *id == request.request && *owner == request.owner =>
                    Some((*frame_id, apply_site)),
            _ => None,
        }).collect::<Vec<_>>();
        let outer = outer_callees.iter().find(|(frame_id, _)|
            template_observation.saved_frame_order.iter().any(|frame|
                matches!(frame, R323FrameWitness::Callee { frame_id: saved, .. } if saved == frame_id)))
            .ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?;
        let responses = machine.r323_resume_observations.iter().filter(|response|
            response.request == request.request && response.template == template_observation.template
        ).collect::<Vec<_>>();
        let [response] = responses.as_slice() else {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        };
        if response.run_id != run_id || !response.owner_live
            || !matches!(response.owner, ExecutionOwner::Invocation(_))
            || response.response.interface != ParameterRole::Value
            || !machine.receiving.matches_value(response.response.view, response.response.value)
            || !matches!(machine.values.get(response.response.value.0).map(|value| &value.kind),
                Some(RuntimeValueKind::Integer(number)) if number.as_ref() == "10")
        {
            return Err(super::super::RuntimeUnavailable::InvalidSourceReference);
        }
        let request_site = r314_lean_runtime_site(machine, parsed, &request.source)?;
        let outer_site = r314_lean_runtime_site(machine, parsed, outer.1)?;
        let response_site = r314_lean_runtime_site(machine, parsed, &response.source)?;
        let operation = super::super::program::r314_lean_string(&request.declaration.spelling);
        let operation_identity = r314_lean_operation_identity(
            &SourceOperationResolution::Resolved(request.declaration.clone()), parsed)?
            .replace("AnnotationType.", "R314Artifact.AnnotationType.")
            .replace("SourceType.", "R314Artifact.SourceType.");
        let payload = r314_lean_received(request.payload).replace("Interface.", "R314Artifact.Interface.");
        let response_value = format!("{{ value := {}, view := {}, interface := R314Artifact.Interface.value, dispatch := {} }}",
            response.response.value.0, response.response.view.index(),
            response.response.dispatch.map_or_else(|| "none".to_owned(), |dispatch| format!("some {dispatch}")));
        let payload_runtime = r314_lean_runtime_value(machine, parsed, request.payload.value.0,
            machine.values.get(request.payload.value.0).ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?)?
            .replace("ValueKind.", "R314Artifact.ValueKind.")
            .replace("interface := Interface.", "interface := R314Artifact.Interface.");
        let response_runtime = r314_lean_runtime_value(machine, parsed, response.response.value.0,
            machine.values.get(response.response.value.0).ok_or(super::super::RuntimeUnavailable::InvalidSourceReference)?)?
            .replace("ValueKind.", "R314Artifact.ValueKind.")
            .replace("interface := Interface.", "interface := R314Artifact.Interface.");
        let saved_frames = template_observation.saved_frame_order.iter()
            .map(|frame| witness_row(machine, parsed, frame))
            .collect::<Result<Vec<_>, _>>()?.join(", ");
        let template_frames = template.nodes.iter().skip(1).take(template_observation.saved_frame_order.len())
            .map(|node| witness_row(machine, parsed, &r323_template_node_witness(node)))
            .collect::<Result<Vec<_>, _>>()?.join(", ");
        let template_inner_links = template.nodes.iter().map(|node|
            r323_template_inner(node).map_or_else(|| "none".to_owned(), |inner| format!("some {inner}")))
            .collect::<Vec<_>>().join(", ");
        let owner_replay_rows = owner_replays.iter().map(|replay| {
            let call_site = replay.call_site.as_ref().map(|site|
                r314_lean_runtime_site(machine, parsed, site).map(|site| format!("some ({site})")))
                .transpose()?.unwrap_or_else(|| "none".to_owned());
            let provider_site = replay.provider_site.as_ref().map(|site|
                r314_lean_runtime_site(machine, parsed, site).map(|site| format!("some ({site})")))
                .transpose()?.unwrap_or_else(|| "none".to_owned());
            let control = replay.control.iter().map(|(from, to)| format!("({from}, {to})"))
                .collect::<Vec<_>>().join(", ");
            Ok::<_, super::super::RuntimeUnavailable>(format!(
                "{{ node := {}, original := {}, resolved := {}, resolvedWasActive := {}, owner := {}, owned := {}, previous := {}, ownerLive := {}, currentOwnerAfter := {}, control := [{control}], callSite := {call_site}, providerSite := {provider_site} }}",
                replay.node,
                r323_lean_owner(replay.original),
                r323_lean_owner(replay.resolved),
                replay.resolved_active,
                r323_lean_owner(replay.owner),
                replay.owned,
                r323_lean_owner(replay.previous),
                replay.owner_live,
                r323_lean_owner(replay.current_owner_after),
            ))
        }).collect::<Result<Vec<_>, _>>()?.join(", ");
        let mut out = String::from("\nnamespace R323Artifact\nopen R314Artifact\n");
        let _ = writeln!(out, "def requestEvent : Nat := {}", request.request);
        let _ = writeln!(out, "def operation : String := {operation}");
        let _ = writeln!(out, "def operationIdentity : R314Artifact.OperationIdentity := {operation_identity}");
        let _ = writeln!(out, "def requestSite : R314Artifact.RuntimeSite := {request_site}");
        let _ = writeln!(out, "def requestOwner : R314Artifact.ExecutionOwner := {}", r323_lean_owner(request.owner));
        let _ = writeln!(out, "def requestOwnerWasLive : Bool := {}", request.owner_live);
        let _ = writeln!(out, "def payload : R314Artifact.Received := {payload}");
        let _ = writeln!(out, "def payloadRuntimeValue : R314Artifact.RuntimeValue := {payload_runtime}");
        let _ = writeln!(out, "def templateHandle : Nat := {}", template_observation.template);
        let _ = writeln!(out, "def templateRoot : Nat := {}", template.root);
        let _ = writeln!(out, "def templateNodeCount : Nat := {}", template.nodes.len());
        let _ = writeln!(out, "def captureOwner : R314Artifact.ExecutionOwner := {}", r323_lean_owner(template_observation.capture_owner));
        out.push_str("structure R323CodeRef where\n  label : Nat\n  site : R314Artifact.RuntimeSite\n  deriving Repr\nstructure R323CalleeFrame where\n  frameId : Nat\n  callee : Option R323CodeRef\n  argument : R323CodeRef\n  environment : Nat\n  site : R314Artifact.RuntimeSite\n  deriving Repr\nstructure R323BlockExpressionFrame where\n  codeLabel : Nat\n  codeSite : R314Artifact.RuntimeSite\n  next : Nat\n  environment : Nat\n  deriving Repr\nstructure R323RootCompReturn where\n  view : Nat\n  receipt : Nat\n  occurrence : Nat\n  deriving Repr\ninductive R323Frame where\n  | callee (frame : R323CalleeFrame)\n  | blockExpression (frame : R323BlockExpressionFrame)\n  | rootCompReturn (execution : R323RootCompReturn)\n  | owner (owner : R314Artifact.ExecutionOwner)\n  deriving Repr\n");
        let _ = writeln!(out, "def savedFrameOrder : List R323Frame := [{saved_frames}]");
        let _ = writeln!(out, "def templateFrameOrder : List R323Frame := [{template_frames}]");
        let _ = writeln!(out, "def templateInnerByNode : List (Option Nat) := [{template_inner_links}]");
        let _ = writeln!(out, "def outerCalleeFrame : Nat := {}", outer.0);
        let _ = writeln!(out, "def outerCalleeSite : R314Artifact.RuntimeSite := {outer_site}");
        let _ = writeln!(out, "def resumeRequestEvent : Nat := {}", response.request);
        let _ = writeln!(out, "def resumeTemplateHandle : Nat := {}", response.template);
        let _ = writeln!(out, "def responseValue : Nat := {}", response.response.value.0);
        let _ = writeln!(out, "def responseView : Nat := {}", response.response.view.index());
        let _ = writeln!(out, "def response : R314Artifact.Received := {response_value}");
        let _ = writeln!(out, "def responseRuntimeValue : R314Artifact.RuntimeValue := {response_runtime}");
        let _ = writeln!(out, "def responseStep : Nat := {}", response.step);
        let _ = writeln!(out, "def responseSite : R314Artifact.RuntimeSite := {response_site}");
        let _ = writeln!(out, "def responseOwner : R314Artifact.ExecutionOwner := {}", r323_lean_owner(response.owner));
        let _ = writeln!(out, "def responseOwnerWasLive : Bool := {}", response.owner_live);
        out.push_str("structure OwnerReplay where\n  node : Nat\n  original : R314Artifact.ExecutionOwner\n  resolved : R314Artifact.ExecutionOwner\n  resolvedWasActive : Bool\n  owner : R314Artifact.ExecutionOwner\n  owned : Bool\n  previous : R314Artifact.ExecutionOwner\n  ownerLive : Bool\n  currentOwnerAfter : R314Artifact.ExecutionOwner\n  control : List (Nat × Nat)\n  callSite : Option R314Artifact.RuntimeSite\n  providerSite : Option R314Artifact.RuntimeSite\n  deriving Repr\n");
        let _ = writeln!(out, "def ownerReplay : List OwnerReplay := [{}]", owner_replay_rows);
        out.push_str("end R323Artifact\n");
        Ok(out)
    }

    #[test]
    fn r313_accepted_source_callee_returns_after_request_and_observes_value_name() {
        let source = "act io:\n    our tick: int -> int\nmy make seed = { io::tick seed; \\argument -> argument }\nmy relay value = make 1 value\nmy handle (thunk:[io] int) = catch thunk { io::tick(p), k -> handle { k 10 } }\nmy main = handle { relay 7 }";
        let (mut machine, parsed) = accepted_machine_with_parse(source);
        r313_watch_source_apply(&mut machine);
        let RuntimeOutcome::Completed(value) = machine.run(30_000) else {
            panic!("accepted source callee/Observe path did not complete: {:?}", machine.state_outcome());
        };
        assert!(matches!(&machine.value(value).unwrap().kind,
            RuntimeValueKind::Integer(actual) if actual.as_ref() == "7"));
        assert_eq!(machine.next_request, 1, "the source callee's Request prefix runs once");
        let call = machine.name_receipt_calls.iter().find(|call| {
            matches!(machine.program.code.get(call.argument_code).map(|code| &code.instruction),
                Some(Instruction::Name { consumption: NameConsumption::Observe, .. }))
                && call.call_site.source_root == machine.program.code[call.argument_code].site.source_root
        }).expect("the real source Apply carries an Observe Name argument");
        assert_source_callee_return_observe_witness(&machine, call);
        assert_name_argument_receipt(&machine, call, NameConsumption::Observe);
        assert_callee_frame_survived_request(&machine, call);
        let binds = machine.r313_value_entry_binds.iter().filter(|bind|
            bind.entry_receiver == call.invocation && bind.parameter == call.formal
        ).collect::<Vec<_>>();
        assert_eq!(binds.len(), 1, "the actual callee ValueEntry records one pre-bind arena snapshot");
        let bind = binds[0];
        assert_eq!(bind.binder_parent_environment, call.closure_environment);
        assert_eq!(bind.cells_before_bind, bind.bound_cell);
        assert_eq!(bind.bound_cell, bind.cells_after_bind - 1);
        assert_eq!(bind.environments_before_bind, bind.bound_environment);
        assert_eq!(bind.bound_environment, bind.environments_after_bind - 1);
        let observed = machine.r312_name_lookups.iter().find(|lookup|
            lookup.code == call.argument_code
                && lookup.site.occurrence == machine.program.code[call.argument_code].site.occurrence
        ).unwrap();
        assert_eq!(bind.received.value, observed.value);
        assert_eq!(bind.received.view, observed.view);
        assert_eq!(machine.environments[bind.bound_environment].parent,
            Some(bind.binder_parent_environment));
        let original_binds = machine.r313_value_entry_binds.iter().filter(|bind|
            bind.bound_environment == observed.environment && bind.bound_cell == observed.cell
        ).collect::<Vec<_>>();
        assert_eq!(original_binds.len(), 1,
            "the Observe Name is initialized by the exact caller parameter bind");
        let original_bind = original_binds[0];
        assert_eq!(original_bind.parameter, observed.parameter);
        assert_eq!(original_bind.received.value, observed.value);
        assert_eq!(original_bind.received.view, observed.view);
        assert_eq!(original_bind.received.interface, ParameterRole::Value);
        assert_eq!(original_bind.bound_cell, original_bind.cells_before_bind);
        assert_eq!(original_bind.bound_environment, original_bind.environments_before_bind);
        assert_eq!(original_bind.cells_after_bind, original_bind.cells_before_bind + 1);
        assert_eq!(original_bind.environments_after_bind, original_bind.environments_before_bind + 1);
        assert_eq!(machine.environments[original_bind.bound_environment].parent,
            Some(original_bind.binder_parent_environment));
        let return_snapshot = machine.r313_return_snapshot.as_ref().unwrap();
        assert!(!return_snapshot.receiving_scan_truncated,
            "CalRet Receiving view vector snapshot is complete");
        let lean = r314_lean_machine_artifact(&machine, call, &parsed, source)
            .expect("the exact snapshot and binder owners serialize into Lean data");
        let r315 = r315_lean_binding_artifact(&machine, &parsed, source, return_snapshot)
            .expect("the same accepted run exports make's full source root and global-cell use");
        let r323 = r323_lean_operation_artifact(&machine, call, &parsed, source)
            .expect("same-run tick request, captured ordered suffix, and exact response resume join");
        assert!(r323.contains("R314Artifact.OperationIdentity"));
        assert!(r323.contains("R314Artifact.AnnotationType.mk"));
        assert!(r323.contains("R323Frame.callee"));
        assert!(r323.contains("codeLabel := "));
        assert!(r323.contains("R314Artifact.ExecutionOwner.invocation"));
        let request_source = machine.r323_request_observations[0].source.clone();
        machine.r323_request_observations[0].source.range.start += 1;
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "a request moved away from its actual HIR source site is rejected");
        machine.r323_request_observations[0].source = request_source;
        let request_declaration = machine.r323_request_observations[0].declaration.clone();
        let mut altered_declaration = (*request_declaration).clone();
        altered_declaration.signature.value = SourceAnnotationValue::Int;
        machine.r323_request_observations[0].declaration = Arc::new(altered_declaration);
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "a changed operation signature cannot borrow the captured continuation");
        machine.r323_request_observations[0].declaration = request_declaration;
        let payload = machine.r323_request_observations[0].payload;
        assert!(!machine.receiving.matches_value(call.callee_view, payload.value),
            "the source callee view is not the Request payload's receiving view");
        machine.r323_request_observations[0].payload.view = call.callee_view;
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "a payload with no matching current receiving view is rejected");
        machine.r323_request_observations[0].payload = payload;
        let response = machine.r323_resume_observations[0].response;
        machine.r323_resume_observations[0].response = machine.r323_request_observations[0].payload;
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "a different same-shaped response value is rejected");
        machine.r323_resume_observations[0].response = response;
        let response_template = machine.r323_resume_observations[0].template;
        machine.r323_resume_observations[0].template = usize::MAX;
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "a response attached to another continuation handle is rejected");
        machine.r323_resume_observations[0].template = response_template;
        let owner_resolution = machine.r323_owner_replay_observations[0].resolved;
        machine.r323_owner_replay_observations[0].resolved = ExecutionOwner::Invocation(usize::MAX);
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "a fabricated replay owner resolution is rejected");
        machine.r323_owner_replay_observations[0].resolved = owner_resolution;
        let template_nodes = machine.resume_templates[0].nodes.clone();
        let template_root = machine.resume_templates[0].root;
        machine.resume_templates[0].root = 0;
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "an altered live template root is rejected");
        machine.resume_templates[0].root = template_root;
        machine.resume_templates[0].nodes.swap(1, 2);
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "reordered live template nodes are rejected");
        machine.resume_templates[0].nodes = template_nodes.clone();
        machine.resume_templates[0].nodes.remove(2);
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "a dropped live template node is rejected");
        machine.resume_templates[0].nodes = template_nodes.clone();
        let mut changed_callee = false;
        for node in &mut machine.resume_templates[0].nodes {
            if let TemplateNode::Bind { frame: Frame::Callee { environment, .. }, .. } = node {
                *environment = usize::MAX;
                changed_callee = true;
                break;
            }
        }
        assert!(changed_callee, "the R315 saved suffix contains its outer Callee frame");
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "changed live Callee operands are rejected");
        machine.resume_templates[0].nodes = template_nodes.clone();
        let mut changed_view_receipt = false;
        for node in &mut machine.resume_templates[0].nodes {
            if let TemplateNode::View { original, .. } = node {
                original.occurrence = original.occurrence.saturating_add(1);
                changed_view_receipt = true;
                break;
            }
        }
        assert!(changed_view_receipt, "the captured continuation includes a typed receiving View receipt");
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "a changed saved View receipt/occurrence is rejected");
        machine.resume_templates[0].nodes = template_nodes.clone();
        if let TemplateNode::Owner { inner, .. } = &mut machine.resume_templates[0].nodes[template_root] {
            *inner = usize::MAX;
        } else {
            panic!("the live template root is its capture-owner boundary");
        }
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "an altered live template inner link is rejected");
        machine.resume_templates[0].nodes = template_nodes;
        let r315 = format!("{lean}\n{r315}\n{r323}");
        assert!(r315.contains("namespace R314Artifact"));
        assert!(r315.contains("namespace R315MakeArtifact"));
        assert!(r315.contains("namespace R315Artifact"));
        assert!(r315.contains("def makeBindingUse : BindingUsePublication"));
        assert!(r315.contains("sourceIndexPublic := false"));
        assert!(r315.contains("Resolution.moduleDef"));
        assert!(r315.contains("cellInterface := R314Artifact.Interface.value"));
        assert!(r315.contains("namespace R323Artifact"));
        assert!(r315.contains("def operation : String := (String.ofList"));
        assert!(r315.contains("def operationIdentity : R314Artifact.OperationIdentity"));
        assert!(r315.contains("def savedFrameOrder : List R323Frame"));
        assert!(r315.contains("def requestOwner : R314Artifact.ExecutionOwner := R314Artifact.ExecutionOwner.invocation"));
        assert!(r315.contains("def responseOwnerWasLive : Bool := true"));
        assert!(r315.contains("structure OwnerReplay where"));
        assert!(r315.contains("def ownerReplay : List OwnerReplay := ["));
        let cloned_snapshot = return_snapshot.clone();
        assert!(r315_lean_binding_artifact(&machine, &parsed, source, &cloned_snapshot).is_err(),
            "a cloned snapshot has no authenticated ownership in this Machine");
        let make_cell = machine.program._hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.id().spelling() == "make" =>
                machine.program.definition_indices.get(binding.id()).copied(),
            _ => None,
        }).unwrap();
        let mut parameter_zero_owners = HashSet::new();
        for (environment_index, environment) in return_snapshot.environments.iter().enumerate() {
            let Some((binder, cell)) = environment.binder.as_ref() else { continue; };
            assert!(*cell < return_snapshot.cells.len(), "environment {environment_index} binder cell is retained");
            let (kind, id, owner) = match binder {
                Binder::Parameter(id) => {
                    if id.ordinal() == 0 { parameter_zero_owners.insert(id.source_root().clone()); }
                    ("parameter", id.ordinal(), id.source_root())
                }
                Binder::Local(id) => ("local", id.ordinal(), id.source_root()),
                Binder::Catch(id) => ("catch", id.ordinal(), id.source_root()),
            };
            let owner = r314_lean_source_root_identity(&machine, &parsed, owner).unwrap();
            let exact_link = format!("binderKind := some {}, binderId := some {id}, binderCell := some {cell}, binderOwner := some ({owner})",
                super::super::program::r314_lean_string(kind));
            assert!(lean.contains(&exact_link),
                "serialized Environment {environment_index} preserves its exact binder owner/id/cell relation");
        }
        assert!(parameter_zero_owners.len() >= 2,
            "the retained snapshot contains ordinal-zero parameters from multiple source roots");
        assert!(lean.contains("SourceRootIdentity.definition"));
        assert_same_source_site(&return_snapshot.apply_site, &call.call_site);
        assert_eq!(return_snapshot.argument_code, Label(call.argument_code));
        assert_eq!(return_snapshot.caller_environment, call.argument_environment);
        let initialized_name = return_snapshot.source_name_initialization.as_ref().unwrap();
        assert_eq!(initialized_name.parameter, observed.parameter);
        assert_eq!(initialized_name.cell, observed.cell);
        assert_eq!(initialized_name.received.value, observed.value);
        assert_eq!(initialized_name.received.view, observed.view);
        assert!(return_snapshot.cells[initialized_name.cell]
            .is_some_and(|received| received.value == observed.value
                && received.view == observed.view
                && received.interface == ParameterRole::Value
                && received.dispatch == original_bind.received.dispatch));
        assert_eq!(return_snapshot.frame_id, machine.r312_frame_events.iter().find_map(|event| match event {
            R312FrameEvent::CalleeReturned { apply_site, frame_id, .. }
                if apply_site.occurrence == call.call_site.occurrence => Some(*frame_id),
            _ => None,
        }).unwrap());

        let request_count = machine.r312_frame_events.iter().filter(|event| matches!(event,
            R312FrameEvent::RequestObserved { .. }
        )).count();
        assert_eq!(request_count, 1, "no resumed suffix replay creates another source Request");
        let make_cell_value = {
            let snapshot = machine.r313_return_snapshot.as_mut().unwrap();
            let received = snapshot.cells[make_cell].unwrap();
            snapshot.cells[make_cell] = Some(ReceivedValue {
                interface: ParameterRole::Computation,
                ..received
            });
            received
        };
        assert!(r315_lean_binding_artifact(&machine, &parsed, source,
            machine.r313_return_snapshot.as_ref().unwrap()).is_err(),
            "a definition cell with only its interface changed is rejected");
        machine.r313_return_snapshot.as_mut().unwrap().cells[make_cell] = Some(make_cell_value);

        let foreign = runtime_program(source, true);
        assert!(!Arc::ptr_eq(&foreign._hir, &machine.program._hir));
        assert!(!source_apply_labels_match_call(
            &foreign, call, call.callee_code.unwrap(), call.argument_code,
        ), "same-shaped foreign HIR cannot witness the accepted run's source owner");
        let lean = r314_lean_machine_artifact(&machine, call, &parsed, source)
            .expect("same-parse source and actual run must export as Lean data");
        assert!(lean.contains("def rootBinding : RootBinding"));
        assert!(lean.contains("SourceForm.apply"));
        assert!(lean.contains("Instruction.name (Resolution.parameter 0)"));
        assert!(lean.contains("sameNameOrdinal := 0"));
        assert!(lean.contains("binderCell := some "));
        let altered_same_length = source.replacen("relay", "riley", 1);
        assert_eq!(altered_same_length.len(), source.len());
        assert!(machine.program.r314_lean_source_export(&parsed, &call.call_site, &altered_same_length).is_err(),
            "same-length text from another source revision must be rejected");
        let foreign_parse_source: Arc<SourceText> = Arc::from(source);
        let foreign_parse = parse_file(
            foreign_parse_source.clone(),
            Arc::new(scan_header(foreign_parse_source)),
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert!(machine.program.r314_lean_source_export(&foreign_parse, &call.call_site, source).is_err(),
            "a second parse of identical text has a different parse owner");
        let mut second_run = start(&machine.program);
        assert!(r314_lean_machine_artifact(&second_run, call, &parsed, source).is_err(),
            "a second Machine over the same HIR cannot reuse the first run's Return snapshot");
        r313_watch_source_apply(&mut second_run);
        let RuntimeOutcome::Completed(_) = second_run.run(30_000) else {
            panic!("second same-program run did not complete for the foreign-snapshot mutation check");
        };
        assert!(r323_lean_operation_artifact(&second_run, call, &parsed, source).is_err(),
            "same-shaped source execution in a second Machine cannot reuse this run's operation evidence");
        let original_template_run = machine.r323_template_observations[0].run_id;
        let original_request = machine.r323_request_observations[0].clone();
        machine.r323_request_observations[0] = second_run.r323_request_observations[0].clone();
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "a request receipt from a separately executed same-HIR run is rejected");
        machine.r323_request_observations[0] = original_request;
        let foreign_template_run = second_run.r323_template_observations[0].run_id;
        machine.r323_template_observations[0].run_id = foreign_template_run;
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "a template receipt from a separately executed same-HIR run is rejected");
        machine.r323_template_observations[0].run_id = original_template_run;
        let foreign_response = machine.r323_resume_observations[0].clone();
        machine.r323_resume_observations[0] = second_run.r323_resume_observations[0].clone();
        assert!(r323_lean_operation_artifact(&machine, call, &parsed, source).is_err(),
            "a response receipt from a separately executed same-HIR run is rejected");
        machine.r323_resume_observations[0] = foreign_response;
        let foreign_snapshot = second_run.r313_return_snapshot.as_ref().unwrap();
        assert!(r315_lean_binding_artifact(&machine, &parsed, source, foreign_snapshot).is_err(),
            "a second Machine's structurally matching Return snapshot is rejected");
        drop(second_run);
        if let Some(path) = std::env::var_os("YULANG_R313_NATIVE_WITNESS") {
            let witness = r313_witness_text(&machine, call, value, source);
            std::fs::write(path, witness)
                .expect("explicit R314 witness export path must be writable");
        }
        if let Some(path) = std::env::var_os("YULANG_R314_LEAN_WITNESS") {
            std::fs::write(path, lean).expect("explicit R314 Lean witness path must be writable");
        }
        if let Some(path) = std::env::var_os("YULANG_R315_LEAN_WITNESS") {
            std::fs::write(path, &r315).expect("explicit R315 Lean witness path must be writable");
        }
        if let Some(path) = std::env::var_os("YULANG_R323_LEAN_WITNESS") {
            std::fs::write(path, &r315).expect("explicit R323 Lean witness path must be writable");
        }
    }

    #[test]
    fn r314_lean_source_export_emits_typed_ascription_and_rejects_corrupt_code_owner() {
        let source: Arc<SourceText> = Arc::from(
            "my id x = x\nmy relay value = id value as int\nmy main = relay 1",
        );
        let parsed = Arc::new(parse_file(
            source.clone(),
            Arc::new(scan_header(source.clone())),
            Arc::new(SyntaxEnvironment::empty()),
        ));
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("r314-ascription", "source.yu"))),
            &parsed,
            SemanticImports::empty(),
        ).unwrap());
        let program = RuntimeProgram::from_hir(hir.clone(), super::super::RuntimeEvidence::default()).unwrap();
        let relay = hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.id().spelling() == "relay" => Some(binding),
            _ => None,
        }).unwrap();
        let apply_site = program.code.iter().find(|code|
            code.site.source_root.definition_root() == Some(relay.definition_root())
                && matches!(code.instruction, Instruction::Apply { .. })
        ).unwrap().site.clone();
        let lean = program.r314_lean_source_export(&parsed, &apply_site, &source).unwrap();
        assert!(lean.contains("SourceForm.ascription ({ owner :="), "ascription is a required Annotation, not an Option");
        assert!(!lean.contains("SourceForm.ascription (some "));
        let other_site = program.code.iter().find(|code|
            code.site.source_root != apply_site.source_root && matches!(code.instruction, Instruction::Apply { .. })
        ).unwrap().site.clone();
        let mut wrong_root = apply_site.clone();
        wrong_root.source_root = other_site.source_root;
        assert!(program.r314_lean_source_export(&parsed, &wrong_root, &source).is_err(),
            "exporter must reject applying a source occurrence to another binding root");
        if let Some(path) = std::env::var_os("YULANG_R314_ASCRIPTION_WITNESS") {
            std::fs::write(path, lean).expect("explicit R314 ascription witness path must be writable");
        }

        let mut corrupt = RuntimeProgram::from_hir(hir, super::super::RuntimeEvidence::default()).unwrap();
        let corrupt_program = Arc::get_mut(&mut corrupt).unwrap();
        let row = corrupt_program.code.iter_mut().find(|code|
            code.site.source_root == apply_site.source_root && code.site.occurrence == apply_site.occurrence
        ).unwrap();
        let instruction = match &row.instruction {
            Instruction::Apply { callee, argument } => Instruction::Apply { callee: *argument, argument: *callee },
            _ => panic!("selected code is Apply"),
        };
        *row = Arc::new(Code { site: row.site.clone(), instruction });
        assert!(corrupt.r314_lean_source_export(&parsed, &apply_site, &source).is_err(),
            "exporter must reject source/instruction operand corruption");
    }

    #[test]
    fn callee_argument_history_r312_name_receipt_seed_joins_actual_invocation() {
        let mut machine = machine("my id x = x\nmy relay x = id x\nmy main = relay 7", true);
        use NameReceiptSeedObservationStatus as Status;
        assert_eq!(machine.name_receipt_seed_observation_status(), Status::NotCompleted);
        let completed = loop {
            match machine.run(1) {
                RuntimeOutcome::Completed(value) => break value,
                RuntimeOutcome::Running | RuntimeOutcome::ResourceExhausted { .. } => {
                    assert_eq!(machine.name_receipt_seed_trace(), None);
                    assert_eq!(machine.name_receipt_seed_observation_status(), Status::NotCompleted);
                }
                other => panic!("unexpected outcome: {other:?}"),
            }
        };
        assert!(matches!(&machine.value(completed).unwrap().kind,
            RuntimeValueKind::Integer(value) if value.as_ref() == "7"));
        assert_eq!(machine.name_receipt_seed_observation_status(), Status::Observed);
        let entry = machine.name_entry_correspondence().unwrap();
        let call = machine.name_receipt_calls.iter().find(|call| {
            matches!(
                machine.program.code.get(call.argument_code).map(|code| &code.instruction),
                Some(Instruction::Name { consumption: NameConsumption::Observe, .. })
            )
        }).unwrap();
        assert_name_argument_receipt(&machine, call, NameConsumption::Observe);
        let trace = machine.name_receipt_seed_trace().unwrap().to_owned();
        assert!(trace.contains(&format!("invocation={}", entry.invocation)));
        assert!(trace.contains(&format!("receipt_index={}", entry.receipt_index)));
        assert!(matches!(machine.step(), RuntimeOutcome::Completed(value) if value == completed));
        assert_eq!(machine.name_receipt_seed_trace(), Some(trace.as_str()));
        machine.name_receipt_observation_unavailable = true; // Simulate unavailable optional storage.
        machine.finish_name_receipt_observation();
        assert_eq!(machine.name_receipt_seed_trace(), None);
        assert_eq!(machine.name_receipt_seed_observation_status(), Status::Unavailable);
    }

    #[test]
    fn callee_argument_history_r312_preserves_pending_outer_call_and_forces_named_computation() {
        let source = "act io:\n    our tick: int -> int\nmy make seed = { io::tick seed; \\argument -> builtin_op::int_add seed argument }\nmy relay (thunk:[io] int) = make 1 thunk\nmy handle (thunk:[io] int) = catch thunk { io::tick(p), k -> handle { k 10 } }\nmy main = handle { relay { io::tick 2 } }";
        let mut machine = accepted_machine(source);
        let RuntimeOutcome::Completed(value) = machine.run(30_000) else {
            panic!("request/resume call path did not complete: {:?}", machine.state_outcome());
        };
        assert!(matches!(
            &machine.value(value).unwrap().kind,
            RuntimeValueKind::Integer(actual) if actual.as_ref() == "11"
        ), "the callee Request, resumed closure, forced argument and result suffix complete");
        assert_eq!(machine.next_request, 2, "each completed prefix executes once");

        let call = machine.name_receipt_calls.iter().find(|call| {
            matches!(
                machine.program.code.get(call.argument_code).map(|code| &code.instruction),
                Some(Instruction::Name { consumption: NameConsumption::Execute, .. })
            )
        }).expect("the returned make closure is applied to the original computation Name");
        assert_name_argument_receipt(&machine, call, NameConsumption::Execute);
        assert_callee_frame_survived_request(&machine, call);
        let lookup_index = machine.r312_name_lookups.iter()
            .position(|lookup| lookup.code == call.argument_code).unwrap();
        let force_completion = machine.r312_name_force_completions.iter()
            .find(|completion| completion.lookup == lookup_index)
            .unwrap();
        let force = machine.r312_name_forces.iter()
            .find(|force| force.lookup == lookup_index).unwrap();
        let force_requests = machine.r312_frame_events.iter().filter_map(|event| match event {
            R312FrameEvent::RequestObserved { step, order, request, site, owner }
                if *owner == ExecutionOwner::Invocation(call.invocation) =>
                Some((*step, *order, *request, site)),
            _ => None,
        }).collect::<Vec<_>>();
        assert_eq!(force_requests.len(), 1, "the actual forced Delay emits one Request under the same owner");
        let (request_step, request_order, request_id, request_site) = force_requests[0];
        let force_code = &machine.program.code[force.code.0];
        assert_eq!(request_id, 1);
        assert!(force.order < request_order && request_order < force_completion.order);
        assert!(force.step <= request_step && request_step <= force_completion.step);
        assert_eq!(request_site.source_root, force_code.site.source_root);
        assert!(request_site.range.start >= force_code.site.range.start
            && request_site.range.end <= force_code.site.range.end);
        assert!(matches!(
            &machine.value(force_completion.output_value).unwrap().kind,
            RuntimeValueKind::Integer(actual) if actual.as_ref() == "10"
        ), "the second handled Request returns through the same Force receipt");

        // Rejection controls use real retained source owners/labels. A
        // structurally equivalent HIR built separately cannot authorize this
        // occurrence, nor can another Apply or Name label stand in for it.
        let foreign = runtime_program(source, true);
        assert!(!Arc::ptr_eq(&foreign._hir, &machine.program._hir));
        assert!(!program_hir_owns_apply_argument(
            &foreign._hir, &machine.program, &call.call_site, call.argument_code
        ));
        let argument = machine.program.code.get(call.argument_code).unwrap();
        let mut wrong_apply = call.call_site.clone();
        wrong_apply.occurrence = argument.site.occurrence.clone();
        wrong_apply.range = argument.site.range.clone();
        assert!(!program_hir_owns_apply_argument(
            &machine.program._hir, &machine.program, &wrong_apply, call.argument_code
        ));
        let wrong_name = machine.program.code.iter().enumerate()
            .find(|(index, candidate)| *index != call.argument_code
                && candidate.site.occurrence != argument.site.occurrence
                && matches!(candidate.instruction, Instruction::Name { .. }))
            .map(|(index, _)| index)
            .expect("fixture contains another Name label for the rejection control");
        assert!(!program_hir_owns_apply_argument(
            &machine.program._hir, &machine.program, &call.call_site, wrong_name
        ));

        let code = argument;
        let Instruction::Name { resolution: LocalSourceResolution::Parameter(parameter), .. } = &code.instruction else {
            panic!("the selected argument is the source parameter Name");
        };
        let actual_lookup = machine.r312_name_lookups.iter().find(|lookup| lookup.code == call.argument_code).unwrap();
        let wrong_environment_cell = machine.lookup(call.closure_environment, |binder| {
                matches!(binder, Binder::Parameter(candidate) if candidate == parameter)
            });
        assert_ne!(wrong_environment_cell, Some(actual_lookup.cell),
            "the closure's saved environment cannot replace the Apply caller environment");
        let force = machine.r312_name_forces.iter().find(|force| force.lookup == machine.r312_name_lookups.iter().position(|lookup| lookup.code == call.argument_code).unwrap()).unwrap();
        assert_ne!(force.view, call.delay_view, "the wrapper Delay view cannot replace the received computation view");
    }

    #[test]
    fn name_receipt_seed_call_cap_is_explicit_and_does_not_change_execution() {
        use NameReceiptSeedObservationStatus as Status;
        for calls in [64, 65] {
            let source = format!("my id x = x\nmy main = {{ {} }}", vec!["id 7"; calls].join("; "));
            let mut machine = machine(&source, true);
            let RuntimeOutcome::Completed(value) = machine.run(10_000) else { panic!("completion"); };
            assert!(matches!(&machine.value(value).unwrap().kind,
                RuntimeValueKind::Integer(value) if value.as_ref() == "7"));
            assert_eq!(machine.name_receipt_calls.len(), 64);
            assert_eq!(machine.name_receipt_seed_trace(), None);
            assert_eq!(machine.name_receipt_seed_observation_status(),
                if calls == 64 { Status::NoCorrespondenceObserved } else { Status::Truncated });
        }
        let mut primitive = machine("my main = builtin_op::int_add 1 2", true);
        assert!(matches!(primitive.run(1000), RuntimeOutcome::Completed(_)));
        assert!(primitive.name_receipt_calls.is_empty());
        assert_eq!(primitive.name_receipt_seed_observation_status(), Status::NoCorrespondenceObserved);
        let mut failure = machine("my main = case :some 1: :none -> 0", true);
        assert!(matches!(failure.run(1000), RuntimeOutcome::Unavailable(_)));
        assert_eq!(failure.name_receipt_seed_trace(), None);
        assert_eq!(failure.name_receipt_seed_observation_status(), Status::NotCompleted);
    }

    #[test]
    fn variant_native_matching_checks_tag_arity_order_and_original_binders() {
        for (source, expected) in [
            ("my main = case :disabled: :disabled -> 7, _ -> 0", "7"),
            ("my main = case :pair(1,2): :other(x,y) -> 99, :pair(x) -> 98, :pair(left,right) -> right", "2"),
            ("my main = case :pair(1,2): :pair(_,right) -> right, :pair(left,_) -> left", "2"),
            ("my main = case :wrap (\\x -> x): :wrap f -> f 7", "7"),
            ("my main = case :disabled(): :disabled -> 99, :disabled _ -> 7", "7"),
            ("my main = case :other 3: :pair x -> x, _ -> 7", "7"),
        ] {
            let mut machine = machine(source, true);
            assert!(!machine.program.closed_primitive, "new shapes confer no old negative-visibility certificate");
            let RuntimeOutcome::Completed(value) = machine.run(10_000) else { panic!("variant native source: {source}"); };
            assert!(matches!(&machine.value(value).unwrap().kind,
                RuntimeValueKind::Integer(value) if value.as_ref() == expected), "{source}");
        }
        for source in [
            "my main = case :some 1: :none -> 0",
            "my main = case :pair(1,2): :pair x -> x",
        ] {
            assert!(matches!(machine(source, true).run(10_000),
                RuntimeOutcome::Unavailable(RuntimeUnavailable::NonExhaustiveCase(_))), "{source}");
        }
    }

    #[test]
    fn variant_result_rendering_keeps_tag_and_payload_arity() {
        for (expression, expected) in [
            (":disabled", ":disabled"),
            (":disabled()", ":disabled(())"),
            (":pair(41,23)", ":pair(41, 23)"),
        ] {
            let mut machine = machine(&format!("my main = {expression}"), true);
            let RuntimeOutcome::Completed(value) = machine.run(10_000) else { panic!("variant result"); };
            let mut output = crate::Output::new();
            crate::render_runtime_value(&machine, value, &mut output).unwrap();
            assert_eq!(output.finish().unwrap(), expected);
        }
    }

    #[test]
    fn variant_payload_projection_preserves_the_received_values_and_views() {
        let mut machine = machine("my main = case :pair(1,2): :pair(left,right) -> (right,left)", true);
        let RuntimeOutcome::Completed(value) = machine.run(10_000) else { panic!("variant projection"); };
        let RuntimeValueKind::Tuple(result) = &machine.value(value).unwrap().kind else { panic!("projected tuple"); };
        let payloads = machine.values.iter().find_map(|value| match &value.kind {
            RuntimeValueKind::Variant { tag, payloads } if tag.as_ref() == "pair" => Some(payloads), _ => None,
        }).unwrap();
        for (output, input) in result.iter().zip(payloads.iter().rev()) {
            assert_eq!(output.received.value, input.received.value);
            assert_eq!(output.received.view, input.received.view);
            assert_eq!(output.received.interface, input.received.interface);
            assert!(machine.receiving.matches_value(output.received.view, output.received.value));
        }
    }

    #[test]
    fn variant_prefix_survives_repeated_raw_resumption_without_replaying_children() {
        let source = "act io:\n    our tick: int -> int\nmy relay (thunk:[io] 'a) = catch thunk { io::tick(p), k -> { k 11; k 23 } }\nmy main = relay (:pair(41, io::tick 0))";
        let mut machine = machine(source, true);
        let mut completed = None;
        for _ in 0..10_000 {
            match machine.run(1) {
                RuntimeOutcome::Running | RuntimeOutcome::ResourceExhausted { .. } => {},
                RuntimeOutcome::Completed(value) => { completed = Some(value); break; },
                other => panic!("variant resume: {other:?}"),
            }
        }
        let RuntimeValueKind::Variant { tag, payloads } = &machine.value(completed.expect("variant completion")).unwrap().kind else { panic!("tagged result"); };
        assert_eq!(tag.as_ref(), "pair");
        assert_eq!(payloads.len(), 2);
        for (payload, expected) in payloads.iter().zip(["41", "23"]) {
            assert!(matches!(&machine.value(payload.value()).unwrap().kind,
                RuntimeValueKind::Integer(value) if value.as_ref() == expected));
            assert!(machine.receiving.matches_value(payload.received.view, payload.received.value));
        }
        assert_eq!(integer_count(&machine, "41"), 1, "the captured prefix is reused by both resumes");
    }

    #[test]
    fn primitive_value_entry_creates_each_invocation_before_forcing_the_argument() {
        let mut machine = machine("my main = builtin_op::int_add 1 2", true);
        let mut entries = Vec::new();
        let mut completed = None;
        for _ in 0..200 {
            if let Some(Frame::PrimitiveArgument { site, .. }) = machine.frames.last() {
                let Frame::ReceiverReturn { activation, previous } = &machine.frames[machine.frames.len() - 2] else { panic!("primitive invocation return"); };
                assert_eq!(machine.current_owner, ExecutionOwner::Invocation(*activation));
                assert_eq!(*previous, ExecutionOwner::ModuleRun);
                let invocation = &machine.invocations[*activation];
                assert!(invocation.active);
                assert_eq!(invocation.call.source_root, site.source_root);
                assert_eq!(invocation.call.occurrence, site.occurrence);
                if !entries.contains(activation) {
                    assert!(matches!(machine.state, State::Evaluate { .. }), "whole argument enters only after the receiver is live");
                    entries.push(*activation);
                }
            }
            match machine.run(1) {
                RuntimeOutcome::Running | RuntimeOutcome::ResourceExhausted { .. } => {},
                RuntimeOutcome::Completed(value) => { completed = Some(value); break; },
                other => panic!("primitive entry: {other:?}"),
            }
        }
        assert_eq!(entries, [0, 1], "curried calls have separate actual owners");
        assert!(machine.invocations.iter().all(|invocation| !invocation.active));
        assert!(machine.active_receivers.is_empty());
        assert_eq!(machine.current_owner, ExecutionOwner::ModuleRun);
        assert!(matches!(&machine.value(completed.expect("completion")).unwrap().kind,
            RuntimeValueKind::Integer(value) if value.as_ref() == "3"));
    }

    #[test]
    fn integer_product_budget_pause_preserves_the_live_machine() {
        let mut machine = machine("my main = builtin_op::int_mul 12345678901234567890 12345678901234567890", true);
        for _ in 0..100 {
            if matches!(machine.state, State::IntegerProduct { .. }) { break; }
            assert!(matches!(machine.run(1), RuntimeOutcome::ResourceExhausted { .. }));
        }
        assert!(matches!(machine.state, State::IntegerProduct { .. }));
        let before_steps = machine.steps();
        let before_values = machine.values.len();
        let before_frames = machine.frames.len();
        let before_cells = cache_snapshot(&machine);
        assert!(matches!(machine.run(7), RuntimeOutcome::ResourceExhausted { .. }));
        assert_eq!(machine.steps(), before_steps + 7);
        assert_eq!(machine.values.len(), before_values, "no partial product becomes a value");
        assert_eq!(machine.frames.len(), before_frames);
        assert_eq!(cache_snapshot(&machine), before_cells);
        assert!(matches!(machine.state, State::IntegerProduct { .. }));
        let RuntimeOutcome::Completed(value) = machine.run(1000) else { panic!("resumed product"); };
        assert!(matches!(&machine.value(value).unwrap().kind,
            RuntimeValueKind::Integer(value) if value.as_ref() == "152415787532388367501905199875019052100"));
    }

    #[test]
    fn tuple_elements_retain_their_received_views() {
        let mut machine = machine("my main = (1, 2)", true);
        let RuntimeOutcome::Completed(tuple) = machine.run(100) else {
            panic!("expected tuple completion")
        };
        let RuntimeValueKind::Tuple(elements) = &machine.value(tuple).unwrap().kind else {
            panic!("expected tuple value")
        };
        assert_eq!(elements.len(), 2);
        for element in elements {
            assert_eq!(element.received.interface, ParameterRole::Value);
            assert!(machine.receiving.matches_value(
                element.received.view,
                element.received.value
            ));
        }
    }

    #[test]
    fn computation_completion_preserves_the_actual_result_record() {
        for (source, minimum_returns) in [
            ("my relay (thunk:[] 'a) = thunk\nmy main = relay (7, \\x -> x)\n", 1),
            ("my relay (thunk:[] (int -> int)) = thunk\nmy main = relay (\\x -> x)\n", 1),
            ("my relay (thunk:[] 'a) = thunk\nmy forward (input:[] 'b) = relay input\nmy main = forward (\\x -> x)\n", 2),
            ("act io:\n    our tick: int -> int\nmy relay (thunk:[io] 'a) = catch thunk { io::tick(p), k -> { my first = k 11; k 23 } }\nmy main = relay { my x = io::tick 0; (x, \\u -> u) }\n", 2),
        ] {
            let mut machine = machine(source, true);
            let mut returns = 0;
            let mut executions = HashSet::new();
            let mut completed = false;
            for _ in 0..2000 {
                let before = match (&machine.state, machine.frames.last()) {
                    (State::Return(value), Some(Frame::RootCompReturn { execution })) =>
                        Some((*value, *execution, machine.executing_views.len())),
                    _ => None,
                };
                let outcome = machine.step();
                if let Some((before, execution, depth)) = before {
                    assert!(matches!(outcome, RuntimeOutcome::Running), "{source}: {outcome:?}");
                    let State::Return(after) = machine.state else { panic!("completion returns the actual record"); };
                    assert_eq!((after.value, after.interface, after.view, after.dispatch),
                        (before.value, before.interface, before.view, before.dispatch),
                        "completion cannot replace unknown/result evidence with a ground view");
                    assert!(machine.receiving.matches_value(after.view, after.value));
                    assert_eq!(machine.executing_views.len() + 1, depth);
                    assert!(executions.insert(execution.occurrence), "each execution closes once");
                    returns += 1;
                }
                match outcome {
                    RuntimeOutcome::Running => {},
                    RuntimeOutcome::Completed(_) => { completed = true; break; },
                    other => panic!("{source}: {other:?}"),
                }
            }
            assert!(completed, "{source}");
            assert!(returns >= minimum_returns, "{source}: {returns}");
            assert!(machine.executing_views.is_empty());
            assert!(machine.initializing_globals.is_empty());
        }
    }

    #[test]
    fn pinned_primitive_values_execute_with_currying_and_arbitrary_precision() {
        let mut add = machine("my main = builtin_op::int_add 999999999999999999999999999999 1", true);
        let outcome = add.run(100);
        assert_completed_integer(&add, outcome, "1000000000000000000000000000000");

        let mut format = machine(
            "my main = builtin_op::string_concat (builtin_op::int_to_string 42) \"!\"",
            true,
        );
        let RuntimeOutcome::Completed(value) = format.run(100) else { panic!("expected primitive string result") };
        assert!(matches!(format.value(value).map(|value| &value.kind), Some(RuntimeValueKind::String(text)) if text.as_ref() == "42!"));
        assert_eq!(decimal_add("-1000", "1").as_deref(), Some("-999"));
        assert_eq!(decimal_add("001", "-1").as_deref(), Some("0"));
    }

    fn assert_completed_integer(machine: &Machine, outcome: RuntimeOutcome, expected: &str) {
        let RuntimeOutcome::Completed(handle) = outcome else {
            panic!("expected completion with integer {expected}, got {outcome:?}");
        };
        assert!(matches!(
            machine.value(handle).map(|value| &value.kind),
            Some(RuntimeValueKind::Integer(text)) if text.as_ref() == expected
        ));
    }

    #[test]
    fn expression_roots_allocate_no_global_cells_or_initialization_markers() {
        let mut machine = machine(
            "later; 99; my later = { my value = 11; value }; later; my main = 7",
            false,
        );
        assert_eq!(machine.cells.len(), 2);
        assert_eq!(machine.program.definition_indices.len(), 2);
        assert!(machine.initializing_globals.is_empty());
        assert!(matches!(
            machine.frames.last(),
            Some(Frame::ExpressionReturn { .. })
        ));
        assert!(matches!(machine.run(10_000), RuntimeOutcome::Completed(_)));
        // One local initializer value, despite a forward Name demand and the
        // definition's later scheduled slot. Expressions publish no cells.
        assert_eq!(
            machine
                .values
                .iter()
                .filter(|value| matches!(
                    &value.kind, RuntimeValueKind::Integer(text) if text.as_ref() == "11"
                ))
                .count(),
            1
        );
        assert_eq!(machine.cells.len(), 3); // Two globals and the actual local.
        assert!(machine.initializing_globals.is_empty());
    }

    #[test]
    fn shared_program_machines_keep_module_root_caches_and_progress_private() {
        let program = runtime_program(
            "later; 99; my later = { my value = 11; value }; later; my main = 7",
            false,
        );
        let mut first = start(&program);
        let mut second = start(&program);
        assert!(Arc::ptr_eq(&first.program, &second.program));

        assert!(matches!(first.step(), RuntimeOutcome::Running));
        let first_steps = first.steps();
        let first_cells = cache_snapshot(&first);
        let first_frame_depth = first.frames.len();

        let second_outcome = second.run(10_000);
        assert_completed_integer(&second, second_outcome, "7");
        assert_eq!(first.steps(), first_steps);
        assert_eq!(cache_snapshot(&first), first_cells);
        assert_eq!(first.frames.len(), first_frame_depth);

        let first_outcome = first.run(10_000);
        assert_completed_integer(&first, first_outcome, "7");
        assert_eq!(first.steps(), second.steps());
        assert_eq!(integer_count(&first, "11"), 1);
        assert_eq!(integer_count(&second, "11"), 1);

        let third = start(&program);
        assert!(Arc::ptr_eq(&first.program, &third.program));
        assert!(third.cells.iter().all(Option::is_none));
        assert_eq!(third.steps(), 0);
    }

    #[test]
    fn initializer_stop_retains_the_cache_write_and_live_caller_prefix() {
        // A low-level boundary reproduction, without a claim about source
        // initialization order or resumed cache publication.
        let mut machine = machine(
            "act io:\n    our tick: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(p), k -> k p }\nmy main = relay later\nmy later = io::tick 7",
            true,
        );
        for _ in 0..10_000 {
            if matches!(machine.state, State::Request(_))
                && matches!(machine.frames.last(), Some(Frame::GlobalRead { .. }))
            {
                break;
            }
            assert!(matches!(machine.step(), RuntimeOutcome::Running));
        }
        let State::Request(request) = &machine.state else {
            panic!("pending request");
        };
        let expected_source = request.source.clone();
        let expected_operation = request.declaration.id.clone();
        let expected_event = request.event;
        let expected_payload = request.payload.value;
        let suffix_len = request.suffix.len();
        let observations_len = request.observations.len();
        let Frame::GlobalRead { cell, .. } = machine.frames.last().unwrap() else {
            panic!("cache write");
        };
        let cell = *cell;
        assert!(machine.cells[cell].is_none());
        assert!(machine.initializing_globals.contains(&cell));
        assert!(
            machine
                .frames
                .iter()
                .any(|frame| matches!(frame, Frame::CatchReturn { .. }))
        );
        let frames_len = machine.frames.len();
        let caller_handlers: Vec<_> = machine
            .frames
            .iter()
            .enumerate()
            .filter_map(|(index, frame)| {
                if let Frame::CatchReturn { installation, .. } = frame {
                    Some((index, *installation))
                } else {
                    None
                }
            })
            .collect();
        let markers = machine.initializing_globals.clone();
        let owner = machine.current_owner;
        let active = machine.active_receivers.clone();
        let invocation_activity: Vec<_> = machine
            .invocations
            .iter()
            .map(|invocation| invocation.active)
            .collect();
        let views: Vec<_> = machine
            .executing_views
            .iter()
            .map(|view| (view.view, view.receipt, view.occurrence))
            .collect();
        let templates_len = machine.resume_templates.len();
        let values_len = machine.values.len();
        let RuntimeOutcome::UnhandledRequest {
            source,
            operation,
            event,
            payload,
            continuation,
        } = machine.step()
        else {
            panic!("initializer boundary must stop before caller selection");
        };
        assert_eq!(source.source_root, expected_source.source_root);
        assert_eq!(source.occurrence, expected_source.occurrence);
        assert_eq!(source.range, expected_source.range);
        assert_eq!(operation, expected_operation);
        assert_eq!(event, expected_event);
        assert_eq!(payload, expected_payload);
        assert_eq!(machine.frames.len(), frames_len);
        assert!(
            matches!(machine.frames.last(), Some(Frame::GlobalRead { cell: retained, .. }) if *retained == cell)
        );
        assert!(
            machine
                .frames
                .iter()
                .any(|frame| matches!(frame, Frame::CatchReturn { .. }))
        );
        assert_eq!(
            machine
                .frames
                .iter()
                .enumerate()
                .filter_map(|(index, frame)| {
                    if let Frame::CatchReturn { installation, .. } = frame {
                        Some((index, *installation))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>(),
            caller_handlers
        );
        assert_eq!(machine.initializing_globals, markers);
        assert!(machine.cells[cell].is_none());
        assert_eq!(machine.current_owner, owner);
        assert_eq!(machine.active_receivers, active);
        assert_eq!(
            machine
                .invocations
                .iter()
                .map(|invocation| invocation.active)
                .collect::<Vec<_>>(),
            invocation_activity
        );
        assert_eq!(
            machine
                .executing_views
                .iter()
                .map(|view| (view.view, view.receipt, view.occurrence))
                .collect::<Vec<_>>(),
            views
        );
        assert_eq!(
            machine.resume_templates.len(),
            templates_len,
            "caller raw binder is never captured"
        );
        assert_eq!(
            machine.values.len(),
            values_len,
            "no continuation value is published"
        );
        let saved = &machine.continuations[continuation.0];
        assert_eq!(saved.frames.len(), suffix_len);
        assert_eq!(saved.observations.len(), observations_len);
        assert!(
            !saved
                .frames
                .iter()
                .any(|frame| matches!(frame, SavedFrame::Ordinary(Frame::GlobalRead { .. })))
        );
    }

    #[test]
    fn scheduled_initializer_host_writes_keep_one_live_publication_frame() {
        let source = "my main = { my emit x = say x; my first = emit (3, \"text\"); my second = println \"second\"; 7 }\nprintln \"after\"\n";
        let (hir, candidate, world, indexes) = crate::prepare_with_world(
            source, "scheduled-host-write.yu", false,
        ).unwrap();
        let program = RuntimeProgram::from_candidate_world(hir, world, &indexes, &candidate).unwrap();
        let definition = program.definition_named("main").unwrap();
        let cell = program.definition_indices[definition];
        let mut machine = program.start_source_schedule(definition).unwrap();
        for (ordinal, expected) in ["(3, text)\n", "second\n", "after\n"].into_iter().enumerate() {
            let outcome = machine.run(100_000);
            let RuntimeOutcome::UnhandledRequest { operation, continuation, .. } = outcome else {
                panic!("expected authenticated host write {ordinal}, got {outcome:?}");
            };
            assert_eq!(program.host_write_operation(), Some(&operation));
            if ordinal < 2 {
                assert!(machine.cells[cell].is_none());
                assert!(machine.initializing_globals.contains(&cell));
                assert_eq!(machine.frames.iter().filter(|frame|
                    matches!(frame, Frame::Root { cell: actual, .. } if *actual == cell)).count(), 1);
            } else {
                assert!(machine.cells[cell].is_some());
                assert!(!machine.initializing_globals.contains(&cell));
            }
            let saved = &machine.continuations[continuation.0];
            assert!(!saved.frames.iter().any(|frame|
                matches!(frame, SavedFrame::Ordinary(Frame::Root { .. } | Frame::GlobalRead { .. }
                    | Frame::ExpressionReturn { .. }))));
            let template = &machine.resume_templates[saved.template.unwrap().0];
            assert!(!template.nodes.iter().any(|node| matches!(node,
                TemplateNode::Bind { frame: Frame::Root { .. } | Frame::GlobalRead { .. }
                    | Frame::ExpressionReturn { .. }, .. })));
            assert_eq!(machine.resume_host_write(continuation, &operation).unwrap().as_ref(), expected);
            assert!(machine.resume_host_write(continuation, &operation).is_err(),
                "the external handle cannot publish a second response");
        }
        let outcome = machine.run(100_000);
        assert_completed_integer(&machine, outcome, "7");
        let cached = machine.cells[cell].unwrap().value;
        assert!(matches!(machine.state_outcome(), Some(RuntimeOutcome::Completed(value)) if *value == cached));
        assert_eq!(integer_count(&machine, "7"), 1);
        assert!(machine.initializing_globals.is_empty());
        assert!(machine.frames.is_empty());
    }

    #[test]
    fn mixed_statement_host_writes_preserve_one_initializer_publication() {
        let source = "my main = { println \"first\"; my ignored = println \"second\"; 7 }\nprintln \"after\"\n";
        let (hir, candidate, world, indexes) = crate::prepare_with_world(source, "mixed-host.yu", false).unwrap();
        let program = RuntimeProgram::from_candidate_world(hir, world, &indexes, &candidate).unwrap();
        let definition = program.definition_named("main").unwrap();
        let cell = program.definition_indices[definition];
        let mut machine = program.start_source_schedule(definition).unwrap();
        for (ordinal, expected) in ["first\n", "second\n", "after\n"].into_iter().enumerate() {
            let outcome = machine.run(100_000);
            let RuntimeOutcome::UnhandledRequest { operation, continuation, .. } = outcome else { panic!("{outcome:?}"); };
            assert_eq!(machine.cells[cell].is_some(), ordinal == 2);
            assert_eq!(machine.initializing_globals.contains(&cell), ordinal != 2);
            if ordinal < 2 {
                assert_eq!(machine.frames.iter().filter(|frame|
                    matches!(frame, Frame::Root { cell: actual, .. } if *actual == cell)).count(), 1);
            }
            assert_eq!(machine.resume_host_write(continuation, &operation).unwrap().as_ref(), expected);
        }
        let outcome = machine.run(100_000);
        assert_completed_integer(&machine, outcome, "7");
        assert_eq!(integer_count(&machine, "7"), 1);
        assert!(machine.frames.is_empty());
        assert!(machine.initializing_globals.is_empty());
    }

    #[test]
    fn mixed_statement_resumption_keeps_completed_prefix_outside_template() {
        let source = "act io:\n    our tick: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(p), k -> { k 11; k 23 } }\nmy main = relay { 99; io::tick 0; my x = 7; x }\n";
        let mut machine = machine(source, true);
        let outcome = machine.run(100_000);
        assert_completed_integer(&machine, outcome, "7");
        assert_eq!(integer_count(&machine, "99"), 1, "completed prefix is not in either resumed suffix");
        assert_eq!(integer_count(&machine, "7"), 2, "the suffix initializer runs separately for each continuation invocation");
        assert_eq!(machine.cells.iter().flatten().filter(|value|
            matches!(&machine.values[value.value.0].kind, RuntimeValueKind::Integer(n) if n.as_ref() == "7")).count(), 3,
            "two distinct local publications and the final module result");
        assert!(machine.frames.is_empty());
        assert!(machine.initializing_globals.is_empty());
    }

    #[test]
    fn polymorphic_dictionary_reads_preserve_identity_and_initialize_once() {
        for source in [
            "my add = { my once = println \"init\"; \\x -> x + x }\nmy main = (add 3, add \"a\")\n",
            "my main = { my add = { my once = println \"init\"; \\x -> x + x }; (add 3, add \"a\") }\n",
        ] {
            let (hir, candidate, world, indexes) = crate::prepare_with_world(
                source, "dictionary-initializer.yu", false,
            ).unwrap();
            let program = RuntimeProgram::from_candidate_world(hir, world, &indexes, &candidate).unwrap();
            assert!(program.dictionaries.is_some());
            let definition = program.definition_named("main").unwrap();
            let mut machine = program.start_source_schedule(definition).unwrap();
            let mut writes = 0;
            let mut identity_checks = 0;
            let mut steps = 0;
            let result = loop {
                steps += 1;
                assert!(steps <= 100_000, "source run must stay within its step budget");
                // Observe actual source Name transitions at already published
                // polymorphic cells, including their receiving view identity.
                if let State::Evaluate { code, environment } = &machine.state {
                    let code = &program.code[code.0];
                    let site = &code.site;
                    let key = dispatch::Site { owner: site.source_root.clone(), occurrence: site.occurrence.clone() };
                    if program.dictionary_names.contains(&key) {
                        if let Instruction::Name { resolution, consumption: NameConsumption::Observe } = &code.instruction {
                            let cell = match resolution {
                                LocalSourceResolution::ModuleDef(id) => program.definition_indices.get(id).copied(),
                                LocalSourceResolution::Local(id) => machine.lookup(*environment, |binder|
                                    matches!(binder, Binder::Local(candidate) if candidate == id)),
                                _ => panic!("dictionary Name must refer to an initialized binding"),
                            }.unwrap();
                            if let Some(before) = machine.cells[cell] {
                                assert!(matches!(machine.step(), RuntimeOutcome::Running));
                                let State::Return(after) = machine.state else { panic!("Name must return its cached value"); };
                                assert_eq!(before.value, after.value);
                                assert_eq!(before.view, after.view);
                                assert_eq!(before.interface, after.interface);
                                assert_eq!(machine.cells[cell].unwrap().dispatch, before.dispatch);
                                assert!(after.dispatch.is_some());
                                identity_checks += 1;
                                continue;
                            }
                        }
                    }
                }
                match machine.step() {
                    RuntimeOutcome::Running => {}
                    RuntimeOutcome::UnhandledRequest { operation, continuation, .. } => {
                        writes += 1;
                        assert_eq!(program.host_write_operation(), Some(&operation));
                        assert_eq!(machine.resume_host_write(continuation, &operation).unwrap().as_ref(), "init\n");
                    }
                    RuntimeOutcome::Completed(result) => break result,
                    other => panic!("source={source:?}: {other:?}"),
                }
            };
            assert_eq!(writes, 1, "initializer is never repeated by dictionary instantiation");
            assert!(identity_checks >= 2);
            let RuntimeValueKind::Tuple(elements) = &machine.value(result).unwrap().kind else { panic!("tuple result"); };
            assert!(matches!(&machine.value(elements[0].received.value).unwrap().kind, RuntimeValueKind::Integer(n) if n.as_ref() == "6"));
            assert!(matches!(&machine.value(elements[1].received.value).unwrap().kind, RuntimeValueKind::String(s) if s.as_ref() == "aa"));
            assert!(machine.frames.is_empty());
            assert!(machine.initializing_globals.is_empty());
        }
    }

    #[test]
    fn missing_contextual_dictionary_never_uses_runtime_value_shapes() {
        let source = "my add x = x + x\nmy main = (add 3, add \"a\")\n";
        let (hir, candidate, world, indexes) = crate::prepare_with_world(
            source, "missing-dictionary.yu", false,
        ).unwrap();
        let mut program = RuntimeProgram::from_candidate_world(hir, world, &indexes, &candidate).unwrap();
        Arc::get_mut(&mut program).unwrap().dictionaries.as_mut().unwrap().clear();
        let definition = program.definition_named("main").unwrap();
        let mut machine = program.start_source_schedule(definition).unwrap();
        assert!(matches!(machine.run(100_000), RuntimeOutcome::Unavailable(RuntimeUnavailable::UnsupportedFieldTail(_))));
    }

    #[test]
    fn retained_abstract_member_instruction_cannot_dispatch_without_evidence() {
        let source = "my main = { my unused x = x.show; 7 }\n";
        let (hir, candidate, world, indexes) = crate::prepare_with_world(
            source, "abstract-member.yu", false,
        ).unwrap();
        assert!(matches!(RuntimeProgram::from_hir(hir.clone(), super::super::RuntimeEvidence::default()),
            Err(RuntimeUnavailable::UnsupportedFieldTail(_))),
            "missing arbitrary evidence still rejects program construction");
        let templates: Vec<_> = candidate.retained_field_tail_templates().unwrap().collect();
        let program = RuntimeProgram::from_candidate_world(hir, world, &indexes, &candidate).unwrap();
        let (label, instruction) = program.code.iter().enumerate().find(|(_, code)|
            matches!(code.instruction, Instruction::FieldTail { .. })).unwrap();
        let site = instruction.site.clone();
        assert!(templates.iter().any(|template|
            template.source_owner == &site.source_root && template.occurrence == &site.occurrence));
        let definition = program.definition_named("main").unwrap();
        let mut machine = program.start_source_schedule(definition).unwrap();
        // Adversarial private-state probe, not a claimed source execution:
        // force entry into the retained abstract body without a dictionary.
        machine.state = State::Evaluate { code: Label(label), environment: 0 };
        assert!(matches!(machine.step(), RuntimeOutcome::Unavailable(RuntimeUnavailable::UnsupportedFieldTail(actual))
            if actual.source_root == site.source_root && actual.occurrence == site.occurrence));
        assert!(machine.continuations.is_empty());
        assert!(machine.values.is_empty());
    }

    #[test]
    fn expression_handle_must_match_its_original_code_join() {
        let machine = machine("99; my main = 7", false);
        let program = &machine.program;
        let mut roots = program.execution_roots().unwrap();
        let ExecutionRoot::Expression(expression) = &mut roots[0] else {
            panic!("expression")
        };
        expression.code = program.definitions[0].body.0;
        assert!(matches!(
            program.start(program.definition_named("main").unwrap(), &roots),
            Err(RuntimeUnavailable::InvalidSourceReference)
        ));
    }

    #[test]
    fn internal_raw_templates_exclude_the_module_scheduler() {
        let mut machine = machine(
            "act io:\n    our tick: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(p), k -> { my first = k 11; k 23 } }; relay (io::tick 7); relay (io::tick 9); my main = 5",
            true,
        );
        assert!(matches!(machine.run(30_000), RuntimeOutcome::Completed(_)));
        assert_eq!(machine.resume_templates.len(), 2);
        for template in &machine.resume_templates {
            assert!(!template.nodes.iter().any(|node| matches!(
                node,
                TemplateNode::Bind {
                    frame: Frame::ExpressionReturn { .. } | Frame::Root { .. },
                    ..
                }
            )));
        }
        assert_eq!(
            machine
                .values
                .iter()
                .filter(|value| matches!(
                    &value.kind, RuntimeValueKind::Integer(text) if text.as_ref() == "9"
                ))
                .count(),
            1
        );
        assert!(machine.frames.is_empty());
        assert_eq!(machine.current_owner, ExecutionOwner::ModuleRun);
    }
}
