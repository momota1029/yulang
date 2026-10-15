use std::{
    collections::{HashMap, HashSet},
    ops::Range,
    sync::Arc,
};
use yu_hir::shadow::{
    LocalSourceCatchPattern, LocalSourceForm, LocalSourceIndex, LocalSourceResolution,
    SourceOperationResolution,
};
use yu_hir::{
    DefId, DefinitionRootId, HirErrorKind, HirItem, HirLocalId, HirModule, HirOccurrenceId,
    HirParameterId,
};

/// One immutable source-qualified code arena. Lowering visits each retained
/// expression and reference once; recursive references remain binder references.
pub struct RuntimeProgram {
    pub(super) _hir: Arc<HirModule>,
    pub(super) code: Vec<Arc<Code>>,
    pub(super) definitions: Vec<Definition>,
    pub(super) definition_indices: HashMap<DefId, usize>,
}

/// Supplied by the source interface owner, never inferred from runtime shape.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NameConsumption {
    Observe,
    Execute,
}
#[derive(Clone, Debug, Default)]
pub struct RuntimeEvidence {
    pub name_consumption: HashMap<HirOccurrenceId, NameConsumption>,
}
#[derive(Clone, Debug)]
pub struct SourceSite {
    pub definition: DefinitionRootId,
    pub occurrence: HirOccurrenceId,
    pub range: Range<usize>,
}
#[derive(Clone, Debug)]
pub enum RuntimeUnavailable {
    MissingSource,
    IdentityExhausted,
    InvalidSourceReference,
    MissingDefinition,
    MissingBinding(SourceSite),
    UninitializedBinding(SourceSite),
    RecursiveDefinitionInitialization(SourceSite),
    AmbiguousDefinitionName,
    MissingConsumptionEvidence(SourceSite),
    LiteralDecoding(SourceSite),
    OperationConsumer(SourceSite),
    UnresolvedOperation(SourceSite),
    HandlerEvidence(SourceSite),
    ExpectedCallable(SourceSite),
    ExpectedBoolean(SourceSite),
    ExpectedComputation(SourceSite),
    ModuleInitializationOrder,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ParameterRole {
    Value,
    Computation,
}
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(super) enum Binder {
    Parameter(HirParameterId),
    Local(HirLocalId),
    Catch(yu_hir::shadow::LocalSourceCatchBinderId),
}
#[derive(Clone, Copy, Debug)]
pub(super) struct Label(pub usize);
pub(super) struct Definition {
    pub id: DefId,
    pub body: Label,
}
pub(super) struct Code {
    pub site: SourceSite,
    pub instruction: Instruction,
}
pub(super) struct LocalBinding {
    pub id: HirLocalId,
    pub initializer: Label,
    pub recursive: bool,
}
pub(super) struct CatchArm {
    pub pattern: LocalSourceCatchPattern,
    pub body: Label,
    pub source: yu_syntax::SourceNodeKey,
    pub range: Range<usize>,
}
pub(super) enum Instruction {
    Unit,
    Integer(Box<str>),
    Boolean(bool),
    String(Box<str>),
    Name {
        resolution: LocalSourceResolution,
        consumption: NameConsumption,
    },
    Forward(Label),
    Lambda {
        parameter: HirParameterId,
        role: ParameterRole,
        body: Label,
    },
    Apply {
        callee: Label,
        argument: Label,
    },
    Block {
        bindings: Vec<Arc<LocalBinding>>,
        final_expression: Label,
    },
    If {
        arms: Vec<(Label, Label)>,
        else_branch: Option<Label>,
    },
    Operation(SourceOperationResolution),
    // Retained intact until the owning handler/interface gate supplies evidence.
    Catch {
        scrutinee: Label,
        arms: Vec<CatchArm>,
    },
}

impl RuntimeProgram {
    /// Resolve CLI selection without running source code. Runtime Name execution
    /// continues to use only the already-resolved HIR identities.
    pub fn definition_named(&self, name: &str) -> Result<&DefId, RuntimeUnavailable> {
        let mut matches = self._hir.items().iter().filter_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding.id()),
            _ => None,
        });
        let selected = matches
            .next()
            .ok_or(RuntimeUnavailable::MissingDefinition)?;
        if matches.next().is_some() {
            return Err(RuntimeUnavailable::AmbiguousDefinitionName);
        }
        Ok(selected)
    }

    /// Derive top-level demand from source construction, never from solved effect
    /// support, SCC order, or a referenced definition's fetch classification.
    pub fn execution_roots(&self) -> Result<Vec<DefId>, RuntimeUnavailable> {
        let mut roots = Vec::new();
        for definition in &self.definitions {
            let mut current = definition.body;
            let computation = loop {
                let code = self
                    .code
                    .get(current.0)
                    .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                match &code.instruction {
                    Instruction::Forward(inner) => current = *inner,
                    Instruction::Block {
                        bindings,
                        final_expression,
                    } if bindings.is_empty() => current = *final_expression,
                    Instruction::Apply { .. }
                    | Instruction::If { .. }
                    | Instruction::Catch { .. }
                    | Instruction::Block { .. } => break true,
                    _ => break false,
                }
            };
            if computation {
                roots.push(definition.id.clone());
            }
        }
        Ok(roots)
    }
    pub fn from_hir(
        hir: Arc<HirModule>,
        evidence: RuntimeEvidence,
    ) -> Result<Arc<Self>, RuntimeUnavailable> {
        let mut code = Vec::new();
        let mut definitions = Vec::new();
        let mut definition_indices = HashMap::new();
        let declaration_errors = hir
            .source_effect_declarations()
            .iter()
            .flat_map(|declaration| declaration.placeholder_errors.iter().copied())
            .collect::<HashSet<_>>();
        let error_kinds = hir
            .errors()
            .iter()
            .map(|error| (error.id(), error.kind()))
            .collect::<HashMap<_, _>>();
        for item in hir.items() {
            let binding = match item {
                HirItem::Binding(binding) => binding,
                HirItem::Error { errors, .. }
                    if !errors.is_empty()
                        && errors.iter().all(|error| {
                            declaration_errors.contains(error)
                                && error_kinds.get(error) == Some(&HirErrorKind::UnsupportedItem)
                        }) =>
                {
                    continue;
                }
                _ => return Err(RuntimeUnavailable::MissingSource),
            };
            let source = hir
                .local_source(binding.definition_root())
                .map_err(|_| RuntimeUnavailable::MissingSource)?
                .ok_or(RuntimeUnavailable::MissingSource)?;
            let offset = code.len();
            let label = |index: &LocalSourceIndex| -> Result<Label, RuntimeUnavailable> {
                source
                    .expression(index)
                    .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                Ok(Label(offset + index.ordinal() as usize))
            };
            // Walk source ownership edges once. An actual self reference is
            // resolved to an initializer currently on the lexical walk stack;
            // later references to the published local never allocate a knot.
            enum Walk {
                Expression(LocalSourceIndex),
                Initializer(usize),
                Leave(HirLocalId),
            }
            let mut work = vec![Walk::Expression(source.body().clone())];
            let mut active = HashSet::new();
            let mut recursive = HashSet::new();
            let mut visited = HashSet::new();
            while let Some(next) = work.pop() {
                match next {
                    Walk::Leave(id) => {
                        active.remove(&id);
                    }
                    Walk::Initializer(ordinal) => {
                        let local = source
                            .bindings()
                            .get(ordinal)
                            .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                        if !local.parameters.is_empty() {
                            active.insert(local.id.clone());
                            work.push(Walk::Leave(local.id.clone()));
                        }
                        work.push(Walk::Expression(local.initializer.clone()));
                    }
                    Walk::Expression(index) => {
                        if !visited.insert(index.clone()) {
                            continue;
                        }
                        let expression = source
                            .expression(&index)
                            .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                        match &expression.form {
                            LocalSourceForm::Name {
                                resolution: LocalSourceResolution::Local(id),
                                ..
                            } if active.contains(id) => {
                                recursive.insert(id.clone());
                            }
                            LocalSourceForm::Group { inner }
                            | LocalSourceForm::Ascription { inner, .. } => {
                                work.push(Walk::Expression(inner.clone()))
                            }
                            LocalSourceForm::Lambda { body, .. } => {
                                work.push(Walk::Expression(body.clone()))
                            }
                            LocalSourceForm::Apply {
                                callee, argument, ..
                            } => {
                                work.push(Walk::Expression(argument.clone()));
                                work.push(Walk::Expression(callee.clone()));
                            }
                            LocalSourceForm::Block {
                                bindings,
                                final_expression,
                            } => {
                                work.push(Walk::Expression(final_expression.clone()));
                                for ordinal in bindings.iter().rev() {
                                    work.push(Walk::Initializer(*ordinal as usize));
                                }
                            }
                            LocalSourceForm::If { arms, else_branch } => {
                                if let Some(branch) = else_branch {
                                    work.push(Walk::Expression(branch.clone()));
                                }
                                for (test, body) in arms {
                                    work.push(Walk::Expression(test.clone()));
                                    work.push(Walk::Expression(body.clone()));
                                }
                            }
                            LocalSourceForm::Catch { scrutinee, arms } => {
                                work.push(Walk::Expression(scrutinee.clone()));
                                for arm in arms {
                                    work.push(Walk::Expression(arm.body.clone()));
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            let roles = source
                .expressions()
                .iter()
                .filter_map(|expression| {
                    let LocalSourceForm::Lambda { parameter, .. } = &expression.form else {
                        return None;
                    };
                    Some((
                        parameter.id.clone(),
                        if parameter
                            .annotation
                            .as_ref()
                            .is_some_and(|annotation| annotation.ty.effects.is_some())
                        {
                            NameConsumption::Execute
                        } else {
                            NameConsumption::Observe
                        },
                    ))
                })
                .collect::<HashMap<_, _>>();
            let bindings = source
                .bindings()
                .iter()
                .map(|local| {
                    Ok(Arc::new(LocalBinding {
                        id: local.id.clone(),
                        initializer: label(&local.initializer)?,
                        recursive: recursive.contains(&local.id),
                    }))
                })
                .collect::<Result<Vec<_>, RuntimeUnavailable>>()?;
            for expression in source.expressions() {
                let instruction = match &expression.form {
                    LocalSourceForm::Unit => Instruction::Unit,
                    LocalSourceForm::Integer(text) => Instruction::Integer(text.clone()),
                    LocalSourceForm::Boolean(value) => Instruction::Boolean(*value),
                    LocalSourceForm::String(text) => Instruction::String(text.clone()),
                    LocalSourceForm::Name { resolution, .. } => {
                        let consumption = match resolution {
                            LocalSourceResolution::Parameter(id) => *roles
                                .get(id)
                                .ok_or(RuntimeUnavailable::InvalidSourceReference)?,
                            _ => NameConsumption::Observe,
                        };
                        if evidence
                            .name_consumption
                            .get(&expression.occurrence)
                            .is_some_and(|supplied| *supplied != consumption)
                        {
                            return Err(RuntimeUnavailable::InvalidSourceReference);
                        }
                        Instruction::Name {
                            resolution: resolution.clone(),
                            consumption,
                        }
                    }
                    // This constructor validates the bounded LocalSource envelope:
                    // only bindings and registered Act placeholders are admitted.
                    // Error declarations/helpers/import items cannot enter it;
                    // SemanticImports currently carries no cast rules, and Act
                    // formation registers only family/operation namespaces. Thus
                    // there are no applicable effect-upcast adapters to execute.
                    // A future registration path must retain its actual adapters
                    // here before this erasure premise can remain valid.
                    LocalSourceForm::Group { inner }
                    | LocalSourceForm::Ascription { inner, .. } => {
                        Instruction::Forward(label(inner)?)
                    }
                    LocalSourceForm::Lambda { parameter, body } => Instruction::Lambda {
                        parameter: parameter.id.clone(),
                        role: if parameter
                            .annotation
                            .as_ref()
                            .is_some_and(|annotation| annotation.ty.effects.is_some())
                        {
                            ParameterRole::Computation
                        } else {
                            ParameterRole::Value
                        },
                        body: label(body)?,
                    },
                    LocalSourceForm::Apply {
                        callee, argument, ..
                    } => Instruction::Apply {
                        callee: label(callee)?,
                        argument: label(argument)?,
                    },
                    LocalSourceForm::Block {
                        bindings: ordinals,
                        final_expression,
                    } => Instruction::Block {
                        bindings: ordinals
                            .iter()
                            .map(|ordinal| {
                                bindings
                                    .get(*ordinal as usize)
                                    .cloned()
                                    .ok_or(RuntimeUnavailable::InvalidSourceReference)
                            })
                            .collect::<Result<_, _>>()?,
                        final_expression: label(final_expression)?,
                    },
                    LocalSourceForm::If { arms, else_branch } => Instruction::If {
                        arms: arms
                            .iter()
                            .map(|(test, body)| Ok((label(test)?, label(body)?)))
                            .collect::<Result<_, RuntimeUnavailable>>()?,
                        else_branch: else_branch.as_ref().map(label).transpose()?,
                    },
                    LocalSourceForm::Operation { resolution } => {
                        Instruction::Operation(resolution.clone())
                    }
                    LocalSourceForm::Catch { scrutinee, arms } => Instruction::Catch {
                        scrutinee: label(scrutinee)?,
                        arms: arms
                            .iter()
                            .map(|arm| {
                                Ok(CatchArm {
                                    pattern: arm.pattern.clone(),
                                    body: label(&arm.body)?,
                                    source: arm.source.clone(),
                                    range: arm.range.clone(),
                                })
                            })
                            .collect::<Result<_, RuntimeUnavailable>>()?,
                    },
                };
                code.push(Arc::new(Code {
                    site: SourceSite {
                        definition: binding.definition_root().clone(),
                        occurrence: expression.occurrence.clone(),
                        range: expression.range.clone(),
                    },
                    instruction,
                }));
            }
            definition_indices.insert(binding.id().clone(), definitions.len());
            definitions.push(Definition {
                id: binding.id().clone(),
                body: label(source.body())?,
            });
        }
        Ok(Arc::new(Self {
            _hir: hir,
            code,
            definitions,
            definition_indices,
        }))
    }
}
