use super::{
    continuation::{ResumeTemplate, TemplateHandle, TemplateNode},
    literal,
    program::{
        Binder, CasePattern, Code, ExecutionRoot, Instruction, Label, NameConsumption, ParameterRole,
        RuntimeProgram, RuntimeUnavailable, SourceSite,
    },
    receiving::{ExecutionView, Observation, Receiving, RootCompSchema, ViewHandle},
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
    Closure,
    Computation,
    Operation(SourceOperationResolution),
}
/// One evaluated tuple element, including the exact source receiving view.
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
struct ReceivedValue {
    value: ValueHandle,
    interface: ParameterRole,
    view: ViewHandle,
}
struct TuplePrefix {
    previous: Option<usize>,
    received: ReceivedValue,
}
struct Environment {
    parent: Option<usize>,
    binder: Option<(Binder, usize)>,
}
#[derive(Clone)]
enum ExecutableValue {
    Continuation(TemplateHandle),
    Closure {
        parameter: HirParameterId,
        role: ParameterRole,
        root_schema: Option<Arc<RootCompSchema>>,
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
    },
    DiscardToUnit {
        site: SourceSite,
    },
    Callee {
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
    Sequence {
        sequence: Arc<Code>,
        next: usize,
        environment: usize,
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
        };
        machine.begin_root(0);
        Ok(machine)
    }
}

impl Machine {
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
            State::Stopped(_) => unreachable!(),
        };
        if let Err(error) = result {
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
            Instruction::Primitive(operation) => self.data(
                site,
                RuntimeValueKind::Primitive(operation.clone()),
                Some(ExecutableValue::Primitive { operation: operation.clone(), arguments: Vec::new() }),
            ),
            Instruction::Tuple { elements } => {
                if let Some(first) = elements.first().copied() {
                    self.frames.push(Frame::Tuple {
                        tuple: code,
                        next: 1,
                        environment,
                        prefix: None,
                    });
                    self.state = State::Evaluate { code: first, environment };
                } else {
                    self.data(site, RuntimeValueKind::Tuple(Vec::new()), None);
                }
            }
            Instruction::FieldTail { .. } | Instruction::InfixOperator { .. } => {
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
                    });
                    self.state = State::Evaluate {
                        code: self.program.definitions[cell].body,
                        environment: 0,
                    };
                } else {
                    return Err(RuntimeUnavailable::UninitializedBinding(site.clone()));
                }
            }
            Instruction::Lambda {
                parameter,
                role,
                root_schema,
                body,
            } => {
                self.data(
                    site,
                    RuntimeValueKind::Closure,
                    Some(ExecutableValue::Closure {
                        parameter: parameter.clone(),
                        role: *role,
                        root_schema: root_schema.clone(),
                        body: *body,
                        environment,
                    }),
                );
            }
            Instruction::Apply { callee, argument } => {
                self.frames.push(Frame::Callee {
                    argument: *argument,
                    environment,
                    site: site.clone(),
                });
                self.state = State::Evaluate {
                    code: *callee,
                    environment,
                };
            }
            Instruction::Block { .. } => self.begin_local(code, 0, environment)?,
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
        let Some(frame) = self.frames.pop() else {
            self.state = State::Stopped(RuntimeOutcome::Completed(received.value));
            return Ok(());
        };
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
                self.end_execution_view(execution)?;
                let view = self.receiving.ground(received.value);
                self.state = State::Return(ReceivedValue { view, ..received });
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
            Frame::OperationResultConsumer { source } => self.execute(received.value, &source)?,
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
                    let result = pinned_primitive_apply(&operation, &arguments, &self.values)
                        .ok_or_else(|| RuntimeUnavailable::InvalidSourceReference)?;
                    self.ground_data(&site, result, None);
                } else {
                    return Err(RuntimeUnavailable::InvalidSourceReference);
                }
            }
            Frame::Callee {
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
                        role,
                        root_schema,
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
                        self.frames.push(Frame::ReceiverReturn {
                            activation,
                            previous,
                        });
                        match role {
                            ParameterRole::Value => {
                                self.frames.push(Frame::ValueEntry {
                                    parameter,
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
                        let SourceAnnotationValue::Function { argument, .. } =
                            &declaration.signature.value
                        else {
                            return Err(RuntimeUnavailable::OperationConsumer(site));
                        };
                        let role = if argument.effects.is_some() {
                            ParameterRole::Computation
                        } else {
                            ParameterRole::Value
                        };
                        let provider = self.values[received.value.0].source.clone();
                        let (activation, previous) = self.new_invocation(site.clone(), provider)?;
                        // The declared source consumer runs after native return.
                        // Its authority comes from the operation declaration,
                        // including when the written result effect row is absent.
                        self.frames.push(Frame::OperationResultConsumer {
                            source: site.clone(),
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
                    value: received.value,
                    interface: ParameterRole::Value,
                    view: received.view,
                });
            }
            Frame::ValueEntry {
                parameter,
                body,
                environment,
            } => {
                let environment = self.bind(
                    environment,
                    Binder::Parameter(parameter),
                    ReceivedValue {
                        value: received.value,
                        interface: ParameterRole::Value,
                        view: received.view,
                    },
                );
                self.state = State::Evaluate {
                    code: body,
                    environment,
                };
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
                    value: received.value,
                    interface: ParameterRole::Value,
                    view: received.view,
                });
                let Instruction::Block { bindings, .. } = &block.instruction else {
                    unreachable!()
                };
                let environment = if recursive {
                    environment
                } else {
                    self.extend(
                        environment,
                        Binder::Local(bindings[next - 1].id.clone()),
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
            Frame::Tuple { tuple, next, environment, prefix: previous } => {
                let prefix = self.tuple_prefixes.len();
                self.tuple_prefixes.push(TuplePrefix {
                    previous,
                    received,
                });
                let Instruction::Tuple { elements } = &tuple.instruction else {
                    unreachable!()
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
                    reversed.reverse();
                    self.data(&tuple.site, RuntimeValueKind::Tuple(reversed), None);
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
                            ReceivedValue { value: received.value, interface: ParameterRole::Value, view: received.view },
                        ),
                        CasePattern::Tuple(patterns) => {
                            let bindings = {
                                let RuntimeValueKind::Tuple(elements) = &self.values[received.value.0].kind else {
                                    unreachable!("the selected tuple pattern matched a tuple value")
                                };
                                patterns.iter().zip(elements).filter_map(|(pattern, element)| {
                                    pattern.as_ref().map(|id| (id.clone(), element.received))
                                }).collect::<Vec<_>>()
                            };
                            bindings.into_iter().fold(environment, |environment, (id, value)| {
                                self.bind(environment, Binder::Catch(id), value)
                            })
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
            } => {
                let received = ReceivedValue {
                    value: received.value,
                    interface: ParameterRole::Value,
                    view: received.view,
                };
                self.cells[cell] = Some(received);
                self.initializing_globals.remove(&cell);
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
            TemplateNode::Bind { inner, frame } => {
                self.frames.push(frame);
                inner
            }
            TemplateNode::Owner { inner, original } => {
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
        // around the Name that demanded its value. Keep the cache-write frame
        // and caller prefix live; only the already unwound suffix is saved.
        if matches!(self.frames.last(), Some(Frame::GlobalRead { .. })) {
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
                environment: 0,
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
            self.state = State::Evaluate {
                code: self.program.definitions[selected].body,
                environment: 0,
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
            Ok(site) => site,
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
        if !self.receiving.matches_value(received.view, received.value) {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        }
        let receipt =
            self.receiving
                .receipt(self.current_execution_owner(), received.view, site, None);
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
                self.execute(received.value, site)?;
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
        let Instruction::Block {
            bindings,
            final_expression,
        } = &block.instruction
        else {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        };
        if let Some(binding) = bindings.get(ordinal) {
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
            self.state = State::Evaluate {
                code: initializer,
                environment,
            };
        } else {
            self.state = State::Evaluate {
                code: *final_expression,
                environment,
            };
        }
        Ok(())
    }
    fn execute(&mut self, value: ValueHandle, site: &SourceSite) -> Result<(), RuntimeUnavailable> {
        match self.executables.get(&value.0).cloned() {
            Some(ExecutableValue::Delay { code, environment }) => {
                self.state = State::Evaluate { code, environment };
                Ok(())
            }
            Some(ExecutableValue::Request {
                declaration,
                payload,
                source,
            }) => {
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
    fn extend(&mut self, parent: usize, binder: Binder, cell: usize) -> usize {
        let index = self.environments.len();
        self.environments.push(Environment {
            parent: Some(parent),
            binder: Some((binder, cell)),
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
            value,
            interface: ParameterRole::Value,
            view,
        });
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

fn pinned_primitive_arity(operation: &yu_hir::shadow::PinnedPrimitiveOp) -> Option<usize> {
    match operation {
        yu_hir::shadow::PinnedPrimitiveOp::IntToString => Some(1),
        yu_hir::shadow::PinnedPrimitiveOp::IntAdd
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
        yu_hir::shadow::PinnedPrimitiveOp::IntAdd => {
            let RuntimeValueKind::Integer(left) = argument(0)? else { return None; };
            let RuntimeValueKind::Integer(right) = argument(1)? else { return None; };
            Some(RuntimeValueKind::Integer(decimal_add(left, right)?.into_boxed_str()))
        }
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
