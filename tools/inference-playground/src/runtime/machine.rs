use super::{
    continuation::{ResumeTemplate, TemplateHandle, TemplateNode},
    literal,
    program::{
        Binder, Code, ExecutionRoot, Instruction, Label, NameConsumption, ParameterRole,
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
    globals: HashMap<DefId, usize>,
    execution_roots: Vec<ScheduledRoot>,
    initializing_globals: HashSet<usize>,
    selected: usize,
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
    Closure,
    Computation,
    Operation(SourceOperationResolution),
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
#[derive(Clone, Copy)]
struct ReceivedValue {
    value: ValueHandle,
    interface: ParameterRole,
    view: ViewHandle,
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
        let globals = self
            .definitions
            .iter()
            .enumerate()
            .map(|(index, definition)| (definition.id.clone(), index))
            .collect();
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
            globals,
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
        };
        machine.begin_root(0);
        Ok(machine)
    }
}

impl Machine {
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
                    LocalSourceResolution::ModuleDef(id) => self.globals.get(id).copied(),
                    LocalSourceResolution::Parameter(id) => {
                        self.lookup(environment, &Binder::Parameter(id.clone()))
                    }
                    LocalSourceResolution::Local(id) => {
                        self.lookup(environment, &Binder::Local(id.clone()))
                    }
                    LocalSourceResolution::CatchBinder(id) => {
                        self.lookup(environment, &Binder::Catch(id.clone()))
                    }
                    LocalSourceResolution::Unresolved | LocalSourceResolution::Ambiguous => None,
                }
                .ok_or_else(|| RuntimeUnavailable::MissingBinding(site.clone()))?;
                if let Some(received) = self.cells[cell] {
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
            Instruction::Block { .. } => self.begin_local(code.clone(), 0, environment)?,
            Instruction::If { arms, else_branch } => {
                if let Some((test, _)) = arms.first() {
                    self.frames.push(Frame::Condition {
                        conditional: code.clone(),
                        arm: 0,
                        environment,
                    });
                    self.state = State::Evaluate {
                        code: *test,
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
            Instruction::Operation(resolution) => {
                self.data(site, RuntimeValueKind::Operation(resolution.clone()), None)
            }
            Instruction::Catch { scrutinee, .. } => {
                let occurrence = self.next_handler;
                self.next_handler = occurrence
                    .checked_add(1)
                    .ok_or(RuntimeUnavailable::IdentityExhausted)?;
                let installation = HandlerInstallation {
                    occurrence,
                    owner: self.current_execution_owner(),
                };
                self.frames.push(Frame::CatchReturn {
                    handler: code.clone(),
                    environment,
                    installation,
                });
                self.state = State::Evaluate {
                    code: *scrutinee,
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
                if !self.primitive_matches(&result.value, received) {
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
                        let provider = self.values[received.value.0].source.clone();
                        let (activation, previous) = self.new_invocation(site.clone(), provider)?;
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
                    self.state = State::Evaluate {
                        code: *test,
                        environment,
                    };
                    self.frames.push(Frame::Condition {
                        conditional: conditional.clone(),
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
        let cell = self.lookup(environment, &Binder::Parameter(parameter.clone()))?;
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
                    if !matches!(
                        result.value,
                        SourceAnnotationValue::Unit
                            | SourceAnnotationValue::Int
                            | SourceAnnotationValue::Bool
                            | SourceAnnotationValue::Str
                    ) {
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
                return Ok(());
            }
        }
        let Some(frame) = self.frames.pop() else {
            let continuation = ContinuationHandle(self.continuations.len());
            self.continuations.push(SavedContinuation {
                frames: request.suffix,
                observations: request.observations,
            });
            self.state = State::Stopped(RuntimeOutcome::UnhandledRequest {
                source: request.source,
                operation: request.declaration.id.clone(),
                payload: request.payload.value,
                event: request.event,
                continuation,
            });
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
        if let Some(value) = self.cells[self.selected] {
            self.state = State::Stopped(RuntimeOutcome::Completed(value.value));
        } else {
            self.initializing_globals.insert(self.selected);
            self.frames.push(Frame::Root {
                next: ordinal,
                cell: self.selected,
            });
            self.state = State::Evaluate {
                code: self.program.definitions[self.selected].body,
                environment: 0,
            };
        }
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
            let cell = self.cells.len();
            self.cells.push(None);
            if binding.recursive {
                environment = self.extend(environment, Binder::Local(binding.id.clone()), cell);
            }
            self.frames.push(Frame::Local {
                block: block.clone(),
                next: ordinal + 1,
                environment,
                cell,
                recursive: binding.recursive,
            });
            self.state = State::Evaluate {
                code: binding.initializer,
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
    fn lookup(&self, mut environment: usize, binder: &Binder) -> Option<usize> {
        loop {
            let frame = self.environments.get(environment)?;
            if let Some((candidate, cell)) = &frame.binder {
                if candidate == binder {
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

#[cfg(test)]
mod module_expression_tests {
    use super::*;
    use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports, lower_module};
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    fn machine(source: &str, opt_in_source: bool) -> Machine {
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
        let program =
            RuntimeProgram::from_hir(hir, super::super::RuntimeEvidence::default()).unwrap();
        program
            .start(
                program.definition_named("main").unwrap(),
                &program.execution_roots().unwrap(),
            )
            .unwrap()
    }

    #[test]
    fn expression_roots_allocate_no_global_cells_or_initialization_markers() {
        let mut machine = machine(
            "later; 99; my later = { my value = 11; value }; later; my main = 7",
            false,
        );
        assert_eq!(machine.cells.len(), 2);
        assert_eq!(machine.globals.len(), 2);
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
