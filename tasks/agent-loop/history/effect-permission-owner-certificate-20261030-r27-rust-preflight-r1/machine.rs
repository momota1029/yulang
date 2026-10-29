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
    #[cfg(test)]
    owner_replay_evidence: Vec<OwnerReplayEvidence>,
    #[cfg(test)]
    captured_template_evidence: Vec<CapturedTemplateEvidence>,
    #[cfg(test)]
    request_consumer_evidence: Vec<RequestConsumerEvidence>,
}

/// Test-only observations of the exact immutable owner replay path. These
/// records are never read by execution decisions and disappear from non-test
/// builds.
#[cfg(test)]
#[derive(Clone, Debug)]
struct OwnerReplayEvidence {
    template_handle: usize,
    capture_root_index: usize,
    node_index: usize,
    control_before: Vec<(usize, usize)>,
    resolved_control: ExecutionOwner,
    chosen_owner: ExecutionOwner,
    disposition: &'static str,
    previous_owner: ExecutionOwner,
    owner_return_owner: ExecutionOwner,
    owner_return_owned: bool,
    owner_return_previous: ExecutionOwner,
}

#[cfg(test)]
#[derive(Clone, Debug)]
struct CapturedTemplateEvidence {
    template_handle: usize,
    root: usize,
    original_event: usize,
    operation: String,
    source: SourceSite,
    containing_owner: ExecutionOwner,
}

#[cfg(test)]
#[derive(Clone, Debug)]
struct RequestConsumerEvidence {
    request_event: usize,
    operation: String,
    operation_family: String,
    operation_spelling: String,
    source: SourceSite,
    request_owner: ExecutionOwner,
    consumer_handler: SourceSite,
    consumer_arm: yu_hir::shadow::SourceNodeKey,
    consumer_owner: ExecutionOwner,
    lineage_templates: Vec<usize>,
    frames: Vec<RetainedFrameEvidence>,
    receiving_observations: Vec<super::receiving::ObservationCertificateEvidence>,
}

#[cfg(test)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct RetainedFrameEvidence {
    absolute_index: usize,
    kind: &'static str,
    owner_or_event_identity: String,
    predecessor: Option<usize>,
    successor: Option<usize>,
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
            #[cfg(test)]
            owner_replay_evidence: Vec::new(),
            #[cfg(test)]
            captured_template_evidence: Vec::new(),
            #[cfg(test)]
            request_consumer_evidence: Vec::new(),
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
            State::Request(request) => self.propagate_request(request),
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
        match &self.state {
            State::Stopped(outcome) => outcome.clone(),
            _ => RuntimeOutcome::Running,
        }
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
                self.frames.push(Frame::Callee { callee: None, argument: *receiver, environment, site: site.clone() });
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
                if let Some(right) = right { self.frames.push(Frame::Callee { callee: None, argument: *right, environment, site: site.clone() }); }
                self.frames.push(Frame::Callee { callee: None, argument: *left, environment, site: site.clone() });
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
                        self.program.definition_indices.get(id).copied()
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
                self.frames.push(Frame::Callee {
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
                callee,
                argument,
                environment,
                site,
            } => {
                // This allocates only inert code plus lexical references. No
                // argument prefix runs before the receiver entry is selected.
                let delay = self.allocate(
                    &site,
                    RuntimeValueKind::Computation,
                    Some(ExecutableValue::Delay {
                        code: argument,
                        environment,
                    }),
                );
                let inherited = self.direct_formal_root(argument, environment);
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
                let bound_cell = self.cells.len();
                let returned_value_origin_site = self.values[received.value.0].source.clone();
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
        self.resume_templates.push(ResumeTemplate {
            nodes,
            root,
            declaration: request.declaration.clone(),
            original_event: request.event,
        });
        #[cfg(test)]
        self.captured_template_evidence.push(CapturedTemplateEvidence {
            template_handle: handle.0,
            root,
            original_event: request.event,
            operation: format!("{:?}", request.declaration.id),
            source: request.source.clone(),
            containing_owner: containing,
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
        let capture_root_index = self
            .resume_templates
            .get(template.0)
            .ok_or(RuntimeUnavailable::InvalidSourceReference)?
            .root;
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
                #[cfg(test)]
                let control_before = {
                    let mut entries = control.iter().map(|(from, to)| (*from, *to)).collect::<Vec<_>>();
                    entries.sort_unstable();
                    entries
                };
                let previous = self.current_owner;
                let resolved = Self::resolve_control(original, &control);
                let (owner, owned) = if self.owner_active(resolved) {
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
                self.frames.push(Frame::OwnerReturn {
                    owner,
                    owned,
                    previous,
                });
                #[cfg(test)]
                self.owner_replay_evidence.push(OwnerReplayEvidence {
                    template_handle: template.0,
                    capture_root_index,
                    node_index: node,
                    control_before,
                    resolved_control: resolved,
                    chosen_owner: owner,
                    disposition: if owned { "fresh_invocation" } else { "borrowed_active_owner" },
                    previous_owner: previous,
                    owner_return_owner: owner,
                    owner_return_owned: owned,
                    owner_return_previous: previous,
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

    #[cfg(test)]
    fn certificate_frame_stack(&self) -> Vec<RetainedFrameEvidence> {
        let length = self.frames.len();
        self.frames
            .iter()
            .enumerate()
            .map(|(absolute_index, frame)| {
                let (kind, owner_or_event_identity) = match frame {
                    Frame::OwnerReturn { owner, owned, previous } => (
                        "owner_return",
                        format!("owner={owner:?};owned={owned};previous={previous:?}"),
                    ),
                    Frame::ReceiverReturn { activation, previous } => (
                        "receiver_return",
                        format!("activation={activation};previous={previous:?}"),
                    ),
                    Frame::CatchReturn { handler, installation, .. } => (
                        "catch_return",
                        format!("handler={:?};owner={:?};source={:?}",
                            handler.site.occurrence, installation.owner, handler.site),
                    ),
                    Frame::OperationResultConsumer { source, callback_use } => (
                        "operation_result_consumer",
                        format!("source={:?};callback_use={callback_use:?}", source.occurrence),
                    ),
                    Frame::OperationPayload { source, .. } => (
                        "operation_payload",
                        format!("source={:?}", source.occurrence),
                    ),
                    Frame::RootCompReturn { execution } => (
                        "root_comp_return",
                        format!("view={};receipt={};occurrence={}",
                            execution.view.0, execution.receipt.0, execution.occurrence),
                    ),
                    Frame::ResumeReturn => ("resume_return", "resume-return".to_owned()),
                    Frame::ResumeArgument { template, source } => (
                        "resume_argument",
                        format!("template={};source={:?}", template.0, source.occurrence),
                    ),
                    Frame::DiscardToUnit { site } => (
                        "discard_to_unit",
                        format!("source={:?}", site.occurrence),
                    ),
                    Frame::Callee { site, .. } => (
                        "callee",
                        format!("source={:?}", site.occurrence),
                    ),
                    Frame::PrimitiveArgument { site, .. } => (
                        "primitive_argument",
                        format!("source={:?}", site.occurrence),
                    ),
                    Frame::ValueEntry { parameter, entry_receiver, .. } => (
                        "value_entry",
                        format!("parameter={parameter:?};receiver={entry_receiver}"),
                    ),
                    Frame::RecordDefault { index, .. } => (
                        "record_default",
                        format!("field_index={index}"),
                    ),
                    Frame::Local { next, cell, .. } => (
                        "local",
                        format!("next={next};cell={cell}"),
                    ),
                    Frame::Condition { arm, .. } => ("condition", format!("arm={arm}")),
                    Frame::BlockExpression { next, .. } => (
                        "block_expression",
                        format!("next={next}"),
                    ),
                    Frame::Sequence { next, .. } => ("sequence", format!("next={next}")),
                    Frame::Record { next, .. } => ("record", format!("next={next}")),
                    Frame::Tuple { next, .. } => ("tuple", format!("next={next}")),
                    Frame::Case { .. } => ("case", "case-frame".to_owned()),
                    Frame::Root { next, cell } => ("root", format!("next={next};cell={cell}")),
                    Frame::ExpressionReturn { root, next } => (
                        "expression_return",
                        format!("root={root:?};next={next}"),
                    ),
                    Frame::GlobalRead { site, cell, .. } => (
                        "global_read",
                        format!("cell={cell};source={:?}", site.occurrence),
                    ),
                };
                RetainedFrameEvidence {
                    absolute_index,
                    kind,
                    owner_or_event_identity,
                    predecessor: absolute_index.checked_sub(1),
                    successor: (absolute_index + 1 < length).then_some(absolute_index + 1),
                }
            })
            .collect()
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
                #[cfg(test)]
                {
                    let receiving_observations = self.receiving.certificate_observations(
                        &request.observations,
                        request.event,
                        installation.owner,
                        &self.invocations,
                        &request.declaration.id.family,
                    );
                    self.request_consumer_evidence.push(RequestConsumerEvidence {
                        request_event: request.event,
                        operation: format!("{:?}", request.declaration.id),
                        operation_family: self.program._hir.source_effect_declarations()
                            .iter()
                            .find(|family| family.id == request.declaration.id.family)
                            .expect("resolved request family belongs to the actual HIR")
                            .spelling
                            .to_string(),
                        operation_spelling: request.declaration.spelling.to_string(),
                        source: request.source.clone(),
                        request_owner,
                        consumer_handler: handler.site.clone(),
                        consumer_arm: arm.source.clone(),
                        consumer_owner: installation.owner,
                        lineage_templates: self.owner_replay_evidence.iter()
                            .map(|replay| replay.template_handle)
                            .collect(),
                        frames: self.certificate_frame_stack(),
                        receiving_observations,
                    });
                }
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
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    fn runtime_program(source: &str, opt_in_source: bool) -> Arc<RuntimeProgram> {
        let source: Arc<SourceText> = Arc::from(source);
        let parsed = parse_file(
            source.clone(),
            Arc::new(scan_header(source)),
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

    fn validate_owner_replay(
        machine: &Machine,
        replay: &OwnerReplayEvidence,
        capture: &CapturedTemplateEvidence,
    ) -> Result<(), &'static str> {
        let Some(template) = machine.resume_templates.get(replay.template_handle) else {
            return Err("template handle is absent");
        };
        if capture.template_handle != replay.template_handle
            || capture.root != replay.capture_root_index
            || template.root != replay.capture_root_index
        {
            return Err("capture-time root coordinate mismatch");
        }
        if replay.node_index != replay.capture_root_index
            || replay.node_index != template.nodes.len().checked_sub(1).ok_or("empty template")?
        {
            return Err("replay coordinate is not the immutable capture root");
        }
        let Some(TemplateNode::Owner { inner, original }) = template.nodes.get(replay.node_index)
        else {
            return Err("capture root is not an Owner node");
        };
        if *inner != replay.capture_root_index.checked_sub(1).ok_or("root has no preceding node")? {
            return Err("capture root Owner does not point to the preceding saved root");
        }
        if *original != capture.containing_owner {
            return Err("capture root Owner differs from the source containing owner");
        }
        let control = replay.control_before.iter().copied().collect::<HashMap<_, _>>();
        let resolved = Machine::resolve_control(*original, &control);
        if resolved != replay.resolved_control {
            return Err("control map resolution differs from replay");
        }
        if replay.owner_return_owner != replay.chosen_owner
            || replay.owner_return_previous != replay.previous_owner
        {
            return Err("pushed OwnerReturn does not match the selected owner");
        }
        match replay.disposition {
            "borrowed_active_owner"
                if !replay.owner_return_owned && replay.chosen_owner == replay.resolved_control => {}
            "fresh_invocation"
                if replay.owner_return_owned
                    && matches!(replay.chosen_owner, ExecutionOwner::Invocation(_)) => {}
            _ => return Err("Owner branch disposition does not match the pushed frame"),
        }
        Ok(())
    }

    fn template_projection(template: &ResumeTemplate) -> Vec<RetainedFrameEvidence> {
        template
            .nodes
            .iter()
            .enumerate()
            .map(|(absolute_index, node)| {
                let (kind, owner_or_event_identity, predecessor) = match node {
                    TemplateNode::Hole => ("hole", "template-hole".to_owned(), None),
                    TemplateNode::Bind { inner, frame } => (
                        "bind",
                        format!("frame_kind={};inner={inner}", test_frame_kind(frame)),
                        Some(*inner),
                    ),
                    TemplateNode::Owner { inner, original } => (
                        "owner_boundary",
                        format!("owner={original:?};inner={inner}"),
                        Some(*inner),
                    ),
                    TemplateNode::ForwardHandler { inner, owner, .. } => (
                        "forward_handler",
                        format!("owner={owner:?};inner={inner}"),
                        Some(*inner),
                    ),
                    TemplateNode::View { inner, original } => (
                        "view",
                        format!("view={};receipt={};inner={inner}",
                            original.view.0, original.receipt.0),
                        Some(*inner),
                    ),
                };
                let successor = template.nodes.iter().enumerate().find_map(|(index, candidate)| {
                    if index <= absolute_index {
                        return None;
                    }
                    match candidate {
                        TemplateNode::Bind { inner, .. }
                        | TemplateNode::Owner { inner, .. }
                        | TemplateNode::ForwardHandler { inner, .. }
                        | TemplateNode::View { inner, .. } if *inner == absolute_index => Some(index),
                        _ => None,
                    }
                });
                RetainedFrameEvidence {
                    absolute_index,
                    kind,
                    owner_or_event_identity,
                    predecessor,
                    successor,
                }
            })
            .collect()
    }

    fn validate_template_projection(
        template: &ResumeTemplate,
        projection: &[RetainedFrameEvidence],
    ) -> Result<(), &'static str> {
        let expected = template_projection(template);
        if projection != expected {
            return Err("saved suffix projection differs from the immutable template chain");
        }
        let Some(first) = projection.first() else {
            return Err("saved suffix projection is empty");
        };
        let Some(last) = projection.last() else {
            return Err("saved suffix projection has no endpoint");
        };
        if first.predecessor.is_some()
            || last.successor.is_some()
            || last.absolute_index != template.root
            || last.kind != "owner_boundary"
        {
            return Err("saved suffix endpoints do not reach the capture-time Owner");
        }
        for pair in projection.windows(2) {
            if pair[0].successor != Some(pair[1].absolute_index)
                || pair[1].predecessor != Some(pair[0].absolute_index)
            {
                return Err("saved suffix projection has a disconnected inner edge");
            }
        }
        Ok(())
    }

    fn validate_outer_projection(
        consumer: &RequestConsumerEvidence,
        projection: &[RetainedFrameEvidence],
    ) -> Result<(), &'static str> {
        if projection.is_empty() || projection != consumer.frames {
            return Err("retained outer stack differs from the actual request-consumer stack");
        }
        for (index, frame) in projection.iter().enumerate() {
            if frame.absolute_index != index
                || frame.predecessor != index.checked_sub(1)
                || frame.successor != (index + 1 < projection.len()).then_some(index + 1)
            {
                return Err("retained outer stack endpoints are not connected");
            }
        }
        if !projection.iter().any(|frame| frame.kind == "catch_return")
            || !projection.iter().any(|frame| frame.kind == "receiver_return")
            || !projection.iter().any(|frame| frame.kind == "owner_return")
        {
            return Err("required handler, receiver, and owner boundaries are absent");
        }
        if consumer.request_owner != consumer.consumer_owner {
            return Err("write request does not reach the actual receiving owner");
        }
        Ok(())
    }

    fn test_frame_kind(frame: &Frame) -> &'static str {
        match frame {
            Frame::ResumeArgument { .. } => "resume_argument",
            Frame::ResumeReturn => "resume_return",
            Frame::OwnerReturn { .. } => "owner_return",
            Frame::RootCompReturn { .. } => "root_comp_return",
            Frame::CatchReturn { .. } => "catch_return",
            Frame::OperationPayload { .. } => "operation_payload",
            Frame::OperationResultConsumer { .. } => "operation_result_consumer",
            Frame::DiscardToUnit { .. } => "discard_to_unit",
            Frame::Callee { .. } => "callee",
            Frame::PrimitiveArgument { .. } => "primitive_argument",
            Frame::ReceiverReturn { .. } => "receiver_return",
            Frame::ValueEntry { .. } => "value_entry",
            Frame::RecordDefault { .. } => "record_default",
            Frame::Local { .. } => "local",
            Frame::Condition { .. } => "condition",
            Frame::BlockExpression { .. } => "block_expression",
            Frame::Sequence { .. } => "sequence",
            Frame::Record { .. } => "record",
            Frame::Tuple { .. } => "tuple",
            Frame::Case { .. } => "case",
            Frame::Root { .. } => "root",
            Frame::ExpressionReturn { .. } => "expression_return",
            Frame::GlobalRead { .. } => "global_read",
        }
    }

    #[derive(Clone, Debug)]
    struct MutationEvidence {
        case: &'static str,
        target_present: bool,
        before_value: String,
        after_value: String,
        applicable_record_changed: bool,
        validator_rejected: bool,
    }

    fn rejected_mutation(
        case: &'static str,
        target_present: bool,
        before_value: impl Into<String>,
        after_value: impl Into<String>,
        validator_rejected: bool,
    ) -> MutationEvidence {
        let before_value = before_value.into();
        let after_value = after_value.into();
        let applicable_record_changed = before_value != after_value;
        assert!(target_present, "{case}: intended mutation target must exist");
        assert!(applicable_record_changed, "{case}: applicable certificate record must change");
        assert!(validator_rejected, "{case}: altered certificate must be rejected");
        MutationEvidence {
            case,
            target_present,
            before_value,
            after_value,
            applicable_record_changed,
            validator_rejected,
        }
    }

    fn json_quote(value: &str) -> String {
        let mut out = String::with_capacity(value.len() + 2);
        out.push('"');
        for ch in value.chars() {
            match ch {
                '"' => out.push_str("\\\""),
                '\\' => out.push_str("\\\\"),
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                '\t' => out.push_str("\\t"),
                ch if ch < ' ' => {
                    use std::fmt::Write as _;
                    let _ = write!(out, "\\u{:04x}", ch as u32);
                }
                ch => out.push(ch),
            }
        }
        out.push('"');
        out
    }

    fn owner_json(owner: ExecutionOwner) -> String {
        json_quote(&format!("{owner:?}"))
    }

    fn projection_json(origin: &str, frames: &[RetainedFrameEvidence], complete: bool) -> String {
        let frames_json = frames.iter().map(|frame| format!(
            "{{\"absolute_index\":{},\"kind\":{},\"owner_or_event_identity\":{},\"predecessor\":{},\"successor\":{}}}",
            frame.absolute_index,
            json_quote(frame.kind),
            json_quote(&frame.owner_or_event_identity),
            frame.predecessor.map_or_else(|| "null".to_owned(), |value| value.to_string()),
            frame.successor.map_or_else(|| "null".to_owned(), |value| value.to_string()),
        )).collect::<Vec<_>>().join(",");
        let start = frames.first().map(|frame| frame.absolute_index);
        let end = frames.last().map(|frame| frame.absolute_index);
        format!(
            "{{\"origin\":{},\"frames\":[{}],\"start_endpoint\":{},\"end_endpoint\":{},\"complete\":{}}}",
            json_quote(origin),
            frames_json,
            start.map_or_else(|| "null".to_owned(), |value| value.to_string()),
            end.map_or_else(|| "null".to_owned(), |value| value.to_string()),
            complete,
        )
    }

    fn mutation_json(mutation: &MutationEvidence) -> String {
        format!(
            "{{\"case\":{},\"target_present\":{},\"before_value\":{},\"after_value\":{},\"applicable_record_changed\":{},\"validator_rejected\":{}}}",
            json_quote(mutation.case),
            mutation.target_present,
            json_quote(&mutation.before_value),
            json_quote(&mutation.after_value),
            mutation.applicable_record_changed,
            mutation.validator_rejected,
        )
    }

    fn template_nodes_json(template: &ResumeTemplate) -> String {
        template.nodes.iter().enumerate().map(|(index, node)| match node {
            TemplateNode::Hole => format!("{{\"index\":{index},\"variant\":\"Hole\"}}"),
            TemplateNode::Bind { inner, frame } => format!(
                "{{\"index\":{index},\"variant\":\"Bind\",\"inner\":{inner},\"frame_kind\":{}}}",
                json_quote(test_frame_kind(frame)),
            ),
            TemplateNode::Owner { inner, original } => format!(
                "{{\"index\":{index},\"variant\":\"Owner\",\"inner\":{inner},\"original\":{}}}",
                owner_json(*original),
            ),
            TemplateNode::ForwardHandler { inner, environment, owner, handler } => format!(
                "{{\"index\":{index},\"variant\":\"ForwardHandler\",\"inner\":{inner},\"handler\":{},\"environment\":{environment},\"owner\":{}}}",
                json_quote(&format!("{:?}", handler.site)),
                owner_json(*owner),
            ),
            TemplateNode::View { inner, original } => format!(
                "{{\"index\":{index},\"variant\":\"View\",\"inner\":{inner},\"view\":{},\"receipt\":{},\"execution_occurrence\":{}}}",
                original.view.0,
                original.receipt.0,
                original.occurrence,
            ),
        }).collect::<Vec<_>>().join(",")
    }

    fn receiving_observations_json(
        observations: &[super::super::receiving::ObservationCertificateEvidence],
    ) -> String {
        observations.iter().map(|evidence| format!(
            "{{\"event\":{},\"observer\":{},\"execution_occurrence\":{},\"view\":{},\"receipt\":{},\"value\":{},\"owner\":{},\"source_slot\":{},\"formal\":{},\"view_kind\":{},\"inherited_coverage_unknown\":{},\"local_grant_for_request\":{}}}",
            evidence.event,
            evidence.observer,
            evidence.execution_occurrence,
            evidence.view,
            evidence.receipt,
            evidence.value,
            json_quote(&evidence.owner),
            json_quote(&evidence.source_slot),
            evidence.formal.as_ref().map_or_else(|| "null".to_owned(), |value| json_quote(value)),
            json_quote(evidence.view_kind),
            evidence.inherited_coverage_unknown,
            evidence.local_grant_for_request,
        )).collect::<Vec<_>>().join(",")
    }

    fn owner_certificate_json(
        machine: &Machine,
        capture: &CapturedTemplateEvidence,
        replay: &OwnerReplayEvidence,
        saved_suffix: &[RetainedFrameEvidence],
        consumer: &RequestConsumerEvidence,
        mutations: &[MutationEvidence],
    ) -> String {
        let template = &machine.resume_templates[capture.template_handle];
        let control = replay.control_before.iter().map(|(from, to)|
            format!("[{},{}]", from, to)).collect::<Vec<_>>().join(",");
        let outer_complete = validate_outer_projection(consumer, &consumer.frames).is_ok();
        let saved_complete = validate_template_projection(template, saved_suffix).is_ok();
        let replay_json = format!(
            "{{\"template_handle\":{},\"capture_root_index\":{},\"node_index\":{},\"resolved_control\":{},\"control_before\":[{}],\"chosen_owner\":{},\"disposition\":{},\"previous_owner\":{},\"owner_return_frame\":{{\"owner\":{},\"owned\":{},\"previous\":{}}}}}",
            replay.template_handle,
            replay.capture_root_index,
            replay.node_index,
            owner_json(replay.resolved_control),
            control,
            owner_json(replay.chosen_owner),
            json_quote(replay.disposition),
            owner_json(replay.previous_owner),
            owner_json(replay.owner_return_owner),
            replay.owner_return_owned,
            owner_json(replay.owner_return_previous),
        );
        let mut projections = projection_json("saved_template_suffix", saved_suffix, saved_complete);
        projections.pop();
        projections.push_str(",\"retained_outer_projection\":");
        projections.push_str(&projection_json("retained_outer_stack", &consumer.frames, outer_complete));
        projections.push('}');
        let mutations = mutations.iter().map(mutation_json).collect::<Vec<_>>().join(",");
        let request_consumer = format!(
            "{{\"request_id\":{},\"operation\":{},\"operation_family\":{},\"operation_spelling\":{},\"source_owner\":{},\"request_owner\":{},\"catch_or_receiver_consumer\":{{\"handler\":{},\"arm\":{},\"owner\":{}}},\"lineage_from_capture\":{{\"template_handle\":{},\"capture_event\":{},\"root_index\":{},\"replay_node_index\":{}}},\"lineage_to_consumer\":{{\"request_event\":{},\"request_source\":{},\"projection_end\":{}}},\"receiving_observations\":[{}]}}",
            consumer.request_event,
            json_quote(&consumer.operation),
            json_quote(&consumer.operation_family),
            json_quote(&consumer.operation_spelling),
            owner_json(capture.containing_owner),
            owner_json(consumer.request_owner),
            json_quote(&format!("{:?}", consumer.consumer_handler)),
            json_quote(&format!("{:?}", consumer.consumer_arm)),
            owner_json(consumer.consumer_owner),
            capture.template_handle,
            capture.original_event,
            capture.root,
            replay.node_index,
            consumer.request_event,
            json_quote(&format!("{:?}", consumer.source)),
            consumer.frames.last().map_or_else(|| "null".to_owned(), |frame| frame.absolute_index.to_string()),
            receiving_observations_json(&consumer.receiving_observations),
        );
        format!(
            "{{\"schema\":\"effect-permission-owner-certificate-r27-v1\",\"route\":\"original-suffix-outer-receiver.yu\",\"run_id\":\"r27-rust-owner-certificate\",\"captured_template\":{{\"handle\":{},\"root\":{},\"declaration\":{},\"original_event\":{},\"nodes\":[{}]}},\"owner_replay\":{},\"frame_projection\":{},\"request_consumer\":{},\"mutations\":[{}]}}\n",
            capture.template_handle,
            capture.root,
            json_quote(&capture.operation),
            capture.original_event,
            template_nodes_json(template),
            replay_json,
            projections,
            request_consumer,
            mutations,
        )
    }

    #[test]
    fn r27_owner_certificate_authenticates_replay_chain_consumer_and_mutations() {
        let callback_source = "act signal:\n    our ping: () -> int\n\nmy relay(cb: () -> [signal] int) = catch cb() {\n    signal::ping(), _ -> 1,\n    v -> v\n}\nmy answer = relay signal::ping\n";
        let mut callback = machine(callback_source, true);
        let callback_outcome = callback.run(100_000);
        assert_completed_integer(&callback, callback_outcome, "1");

        let companion_source = include_str!("../../examples/original-suffix-outer-receiver.yu");
        let mut companion = machine(companion_source, true);
        let companion_outcome = companion.run(100_000);
        assert_completed_integer(&companion, companion_outcome, "23");
        assert!(!companion.captured_template_evidence.is_empty(), "the selected Catch continuation captures a template");
        assert!(!companion.owner_replay_evidence.is_empty(), "the captured continuation re-enters its root owner");
        assert!(!companion.request_consumer_evidence.is_empty(), "the distinct outer write request reaches its Catch consumer");

        let capture = companion.captured_template_evidence.first().unwrap();
        let template = &companion.resume_templates[capture.template_handle];
        assert_eq!(capture.root, template.root);
        assert_eq!(capture.root, template.nodes.len() - 1);
        assert!(matches!(template.nodes.get(capture.root),
            Some(TemplateNode::Owner { inner, original })
                if *inner == capture.root - 1 && *original == capture.containing_owner));
        let replay = companion.owner_replay_evidence.iter()
            .find(|replay| replay.template_handle == capture.template_handle)
            .expect("the captured template root is actually replayed");
        validate_owner_replay(&companion, replay, capture).unwrap();

        let saved_suffix = template_projection(template);
        assert!(saved_suffix.iter().any(|frame| frame.kind == "owner_boundary"),
            "capture-time outer Owner is a required saved-suffix boundary");
        assert_eq!(saved_suffix.first().map(|frame| frame.predecessor), Some(None));
        assert_eq!(saved_suffix.last().map(|frame| frame.successor), Some(None));
        validate_template_projection(template, &saved_suffix).unwrap();

        let consumer = companion.request_consumer_evidence.last().unwrap();
        assert_ne!(consumer.operation, capture.operation, "the consuming write request is distinct from the captured request");
        assert_eq!(consumer.operation_family, "write",
            "the selected consumer is the fixture's distinct write effect family");
        assert_eq!(consumer.operation_spelling, "ping",
            "the selected consumer is the fixture's write::ping operation");
        assert_ne!(consumer.source.occurrence, capture.source.occurrence);
        assert!(consumer.lineage_templates.contains(&capture.template_handle),
            "the captured template was actually replayed before this consumer");
        assert_eq!(consumer.request_owner, consumer.consumer_owner);
        assert!(consumer.frames.iter().any(|frame|
            frame.kind == "catch_return" && frame.owner_or_event_identity.contains("source=")));
        assert!(consumer.frames.iter().any(|frame|
            frame.kind == "receiver_return"),
            "outer projection retains the actual receiver-return boundary");
        assert!(consumer.frames.iter().any(|frame| frame.kind == "owner_return"),
            "outer projection retains the actual owner-return boundary");
        validate_outer_projection(consumer, &consumer.frames).unwrap();
        assert!(!consumer.receiving_observations.is_empty(),
            "the actual receiving consumer retains its permission observations");
        assert!(consumer.receiving_observations.iter().all(|evidence|
            evidence.event == consumer.request_event));

        // Every mutation resolves and changes its exact target before the
        // certificate validator is asked to reject the altered record.
        let mut wrong_index = replay.clone();
        let before_index = wrong_index.node_index;
        let alternate_owner = template.nodes.iter().enumerate().find_map(|(index, node)| {
            (index != capture.root && matches!(node, TemplateNode::Owner { .. })).then_some(index)
        });
        let wrong_index_value = alternate_owner.unwrap_or_else(|| capture.root - 1);
        let target_present = template.nodes.get(wrong_index_value).is_some();
        wrong_index.node_index = wrong_index_value;
        let changed = before_index != wrong_index.node_index;
        assert!(target_present && changed, "wrong-positive-index mutation target must exist and change");
        let rejected = validate_owner_replay(&companion, &wrong_index, capture).is_err();
        let mut mutation_records = vec![rejected_mutation(
            "wrong_positive_node_index",
            target_present,
            before_index.to_string(),
            wrong_index.node_index.to_string(),
            rejected,
        )];

        let mut without_boundary = saved_suffix.clone();
        let boundary_index = without_boundary.iter().position(|frame|
            frame.absolute_index == capture.root && frame.kind == "owner_boundary")
            .expect("required capture-time Owner boundary exists");
        let before_boundary_count = without_boundary.len();
        without_boundary.remove(boundary_index);
        assert_ne!(before_boundary_count, without_boundary.len(), "boundary deletion changed its record");
        let rejected = validate_template_projection(template, &without_boundary).is_err();
        mutation_records.push(rejected_mutation(
            "delete_required_boundary",
            true,
            format!("frames={before_boundary_count};root_owner_present=true"),
            format!("frames={};root_owner_present=false", without_boundary.len()),
            rejected,
        ));

        let mut altered_disposition = replay.clone();
        let before_disposition = altered_disposition.disposition;
        altered_disposition.disposition = match before_disposition {
            "borrowed_active_owner" => "fresh_invocation",
            "fresh_invocation" => "borrowed_active_owner",
            _ => panic!("unknown recorded disposition"),
        };
        assert_ne!(before_disposition, altered_disposition.disposition);
        let rejected = validate_owner_replay(&companion, &altered_disposition, capture).is_err();
        mutation_records.push(rejected_mutation(
            "alter_borrowed_fresh_disposition",
            true,
            before_disposition,
            altered_disposition.disposition,
            rejected,
        ));

        let mut disconnected_consumer = consumer.clone();
        let before_owner = disconnected_consumer.consumer_owner;
        disconnected_consumer.consumer_owner = ExecutionOwner::ModuleRun;
        assert_ne!(before_owner, disconnected_consumer.consumer_owner,
            "fixture receiver is a real invocation owner, so disconnect changes it");
        assert_ne!(disconnected_consumer.consumer_owner, disconnected_consumer.request_owner,
            "disconnected write lineage no longer reaches its selected receiver");
        let rejected = validate_outer_projection(&disconnected_consumer, &disconnected_consumer.frames).is_err();
        mutation_records.push(rejected_mutation(
            "disconnect_write_lineage",
            true,
            format!("request_owner={before_owner:?};consumer_owner={before_owner:?}"),
            format!("request_owner={:?};consumer_owner={:?}", disconnected_consumer.request_owner,
                disconnected_consumer.consumer_owner),
            rejected,
        ));

        // The no-op guard targets an existing endpoint and records a distinct
        // invalid endpoint. A missing/unchanged target cannot be reported as a
        // rejected certificate mutation.
        let mut no_op_guard = saved_suffix.clone();
        let target = no_op_guard.last_mut().expect("captured suffix has an endpoint");
        let before_endpoint = target.successor;
        let after_endpoint = Some(capture.root + 1);
        let target_present = target.absolute_index == capture.root;
        target.successor = after_endpoint;
        assert!(target_present && before_endpoint != target.successor,
            "no-op guard proves exact target presence and an actual applicable-record change");
        let rejected = validate_template_projection(template, &no_op_guard).is_err();
        mutation_records.push(rejected_mutation(
            "no_op_target_guard",
            target_present,
            format!("node={};successor={before_endpoint:?}", capture.root),
            format!("node={};successor={after_endpoint:?}", capture.root),
            rejected,
        ));
        assert_eq!(mutation_records.len(), 5);
        let receipt = owner_certificate_json(
            &companion,
            capture,
            replay,
            &saved_suffix,
            consumer,
            &mutation_records,
        );
        let receipt_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../receipts/owner-certificate.json");
        std::fs::write(receipt_path, receipt)
            .expect("write the test-only owner certificate after authorized execution");
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
