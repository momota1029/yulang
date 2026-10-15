use super::{
    literal,
    program::{
        Binder, Code, Instruction, Label, NameConsumption, ParameterRole, RuntimeProgram,
        RuntimeUnavailable, SourceSite,
    },
};
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};
use yu_hir::shadow::{LocalSourceResolution, SourceOperationResolution};
use yu_hir::{DefId, HirParameterId};

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
    execution_roots: Vec<usize>,
    initializing_globals: HashSet<usize>,
    selected: usize,
    steps: usize,
    next_receiver: usize,
    active_receivers: Vec<usize>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ValueHandle(usize);
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
    /// Reserved for the operation consumer gate; no request is manufactured
    /// without its complete typed request/continuation evidence.
    UnhandledRequest {
        source: SourceSite,
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
}
struct Environment {
    parent: Option<usize>,
    binder: Option<(Binder, usize)>,
}
#[derive(Clone)]
enum ExecutableValue {
    Closure {
        parameter: HirParameterId,
        role: ParameterRole,
        body: Label,
        environment: usize,
    },
    Delay {
        code: Label,
        environment: usize,
    },
}
enum State {
    Evaluate { code: Label, environment: usize },
    Return(ReceivedValue),
    Stopped(RuntimeOutcome),
}
enum Frame {
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
    GlobalRead {
        cell: usize,
        consumption: NameConsumption,
        site: SourceSite,
    },
}

impl RuntimeProgram {
    /// The source interface owner supplies computation roots in source order.
    /// Value definitions materialize at first access. Successful definition
    /// materialization is cached; executing a delayed argument is never cached.
    pub fn start(
        self: &Arc<Self>,
        definition: &DefId,
        execution_roots: &[DefId],
    ) -> Result<Machine, RuntimeUnavailable> {
        let selected = *self
            .definition_indices
            .get(definition)
            .ok_or(RuntimeUnavailable::MissingDefinition)?;
        let mut seen = HashSet::new();
        let mut roots = Vec::new();
        for id in execution_roots {
            let index = *self
                .definition_indices
                .get(id)
                .ok_or(RuntimeUnavailable::MissingDefinition)?;
            if !seen.insert(index) {
                return Err(RuntimeUnavailable::ModuleInitializationOrder);
            }
            roots.push(index);
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
            active_receivers: Vec::new(),
        };
        machine.begin_root(0);
        Ok(machine)
    }
}

impl Machine {
    pub fn value(&self, handle: ValueHandle) -> Option<&RuntimeValue> {
        self.values.get(handle.0)
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
            Instruction::Unit => self.data(site, RuntimeValueKind::Unit, None),
            Instruction::Integer(text) => self.data(
                site,
                RuntimeValueKind::Integer(
                    literal::integer(text)
                        .ok_or_else(|| RuntimeUnavailable::LiteralDecoding(site.clone()))?,
                ),
                None,
            ),
            Instruction::Boolean(value) => self.data(site, RuntimeValueKind::Boolean(*value), None),
            Instruction::String(text) => self.data(
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
                body,
            } => {
                self.data(
                    site,
                    RuntimeValueKind::Closure,
                    Some(ExecutableValue::Closure {
                        parameter: parameter.clone(),
                        role: *role,
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
                    self.data(site, RuntimeValueKind::Unit, None);
                }
            }
            Instruction::Operation(resolution) => {
                self.data(site, RuntimeValueKind::Operation(resolution.clone()), None)
            }
            Instruction::Catch { scrutinee, arms } => {
                // Neither executing under a fake handler nor dropping its missing
                // protection is a valid fallback. Keep all source metadata live.
                let _ = (scrutinee, arms);
                return Err(RuntimeUnavailable::HandlerEvidence(site.clone()));
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
            Frame::DiscardToUnit { site } => self.data(&site, RuntimeValueKind::Unit, None),
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
                let executable = self.executables.get(&received.value.0).cloned();
                match executable {
                    Some(ExecutableValue::Closure {
                        parameter,
                        role,
                        body,
                        environment,
                    }) => {
                        let activation = self.next_receiver;
                        self.next_receiver = activation
                            .checked_add(1)
                            .ok_or(RuntimeUnavailable::IdentityExhausted)?;
                        self.active_receivers.push(activation);
                        self.frames.push(Frame::ReceiverReturn { activation });
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
                                let environment = self.bind(
                                    environment,
                                    Binder::Parameter(parameter),
                                    ReceivedValue {
                                        value: delay,
                                        interface: ParameterRole::Computation,
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
                        return Err(RuntimeUnavailable::OperationConsumer(site));
                    }
                    _ => return Err(RuntimeUnavailable::ExpectedCallable(site)),
                }
            }
            Frame::ReceiverReturn { activation } => {
                if self.active_receivers.pop() != Some(activation) {
                    return Err(RuntimeUnavailable::InvalidSourceReference);
                }
                self.state = State::Return(ReceivedValue {
                    value: received.value,
                    interface: ParameterRole::Value,
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
                    self.data(&conditional.site, RuntimeValueKind::Unit, None);
                }
            }
            Frame::Root { next, cell } => {
                self.cells[cell] = Some(ReceivedValue {
                    value: received.value,
                    interface: ParameterRole::Value,
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
                };
                self.cells[cell] = Some(received);
                self.initializing_globals.remove(&cell);
                self.consume(received, consumption, &site)?;
            }
        }
        Ok(())
    }

    fn begin_root(&mut self, mut ordinal: usize) {
        // Skip roots already materialized through an earlier dependency. Each
        // root is visited once across the run, including these cached entries.
        while let Some(index) = self.execution_roots.get(ordinal).copied() {
            ordinal += 1;
            if self.cells[index].is_some() {
                continue;
            }
            self.initializing_globals.insert(index);
            self.frames.push(Frame::Root {
                next: ordinal,
                cell: index,
            });
            self.state = State::Evaluate {
                code: self.program.definitions[index].body,
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
        match consumption {
            NameConsumption::Observe => self.state = State::Return(received),
            NameConsumption::Execute => {
                if received.interface != ParameterRole::Computation {
                    return Err(RuntimeUnavailable::MissingConsumptionEvidence(site.clone()));
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
        match self.executables.get(&value.0) {
            Some(ExecutableValue::Delay { code, environment }) => {
                self.state = State::Evaluate {
                    code: *code,
                    environment: *environment,
                };
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
    fn data(
        &mut self,
        site: &SourceSite,
        kind: RuntimeValueKind,
        executable: Option<ExecutableValue>,
    ) {
        let value = self.allocate(site, kind, executable);
        self.state = State::Return(ReceivedValue {
            value,
            interface: ParameterRole::Value,
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
