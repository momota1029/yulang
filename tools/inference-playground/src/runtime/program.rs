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
    DefId, ExpressionRootId, HirErrorKind, HirItem, HirLocalId, HirModule, HirOccurrenceId,
    HirParameterId, SourceRootId,
};
use yu_solver::shadow_apply::CandidateInference;

/// One immutable source-qualified code arena. Lowering visits each retained
/// expression and reference once; recursive references remain binder references.
pub struct RuntimeProgram {
    pub(super) _hir: Arc<HirModule>,
    pub(super) code: Vec<Arc<Code>>,
    pub(super) definitions: Vec<Definition>,
    pub(super) definition_indices: HashMap<DefId, usize>,
    pub(super) expression_roots: HashMap<ExpressionRootId, Label>,
    pub(super) source_schedule: Vec<ExecutionRoot>,
    // Valid only for fresh ModuleRun entry into this complete constructed universe.
    pub(super) closed_primitive: bool,
    pub(super) operation_v1: Option<OperationV1Plan>,
}

/// Source-ordered module demand. Expression labels are accepted only when
/// they match the program's authenticated original root/code join.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExecutionRoot {
    Definition(DefId),
    Expression(ExpressionExecutionRoot),
}

/// An authenticated expression demand; only source compilation constructs it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpressionExecutionRoot {
    pub(super) root: ExpressionRootId,
    pub(super) code: usize,
}
impl ExpressionExecutionRoot {
    pub fn source_root(&self) -> &ExpressionRootId {
        &self.root
    }
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
    operation_v1: Option<OperationV1Link>,
}
#[derive(Clone, Debug)]
pub(super) struct OperationV1Link {
    pub(super) hir_identity: usize,
    pub(super) field_bound_id: u32,
    pub(super) request: HirOccurrenceId,
    pub(super) callback_apply: HirOccurrenceId,
    pub(super) callback_operation: yu_hir::shadow::SourceOperationId,
    pub(super) callback_operation_use: HirOccurrenceId,
    pub(super) response_definition: HirLocalId,
}
#[derive(Clone)]
pub(super) struct OperationV1Plan {
    pub(super) link: OperationV1Link,
    pub(super) response_lambda: SourceSite,
    pub(super) callback_operation: SourceSite,
    pub(super) request: SourceSite,
    pub(super) request_apply: SourceSite,
    pub(super) request_operation: yu_hir::shadow::SourceOperationId,
    pub(super) request_handler: SourceSite,
    pub(super) request_arm: yu_hir::shadow::SourceNodeKey,
    pub(super) response_argument: SourceSite,
    pub(super) expected_outer_handler: Option<SourceSite>,
    pub(super) expected_outer_arm: Option<yu_hir::shadow::SourceNodeKey>,
    pub(super) continuation_apply: SourceSite,
    pub(super) response_invocation_apply: SourceSite,
    pub(super) local_lineage: Option<OperationV1LocalLineage>,
}
#[derive(Clone)]
pub(super) struct OperationV1LocalLineage {
    pub(super) binding: HirLocalId,
    pub(super) initializer_catch: SourceSite,
    pub(super) name_use: SourceSite,
    pub(super) apply: SourceSite,
}
struct HandlerArgumentJoin {
    continuation_apply: SourceSite,
    response_argument: SourceSite,
    request_handler: SourceSite,
    request_arm: yu_hir::shadow::SourceNodeKey,
}
#[derive(Clone, Debug)]
pub struct SourceSite {
    pub source_root: SourceRootId,
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
    ContinuationMaterialization(SourceSite),
    ContinuationResponse(SourceSite),
    ExpectedCallable(SourceSite),
    ExpectedBoolean(SourceSite),
    NonExhaustiveCase(SourceSite),
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
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
pub(super) struct CaseArm {
    pub pattern: CasePattern,
    pub body: Label,
}
pub(super) enum CasePattern {
    Integer(Box<str>),
    Binder(yu_hir::shadow::LocalSourceCatchBinderId),
    Wildcard,
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
        root_schema: Option<Arc<super::receiving::RootCompSchema>>,
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
    Sequence { items: Vec<Label> },
    Case {
        scrutinee: Label,
        arms: Vec<CaseArm>,
    },
    Operation(SourceOperationResolution),
    // Retained intact until the owning handler/interface gate supplies evidence.
    Catch {
        scrutinee: Label,
        arms: Vec<CatchArm>,
    },
}

impl RuntimeProgram {
    /// Carries one successful v1 candidate from this exact HIR into the
    /// research-only runtime. The ordinary inference and execution entries do
    /// not construct this evidence.
    pub fn evidence_for_operation_v1(
        hir: &HirModule,
        candidate: &CandidateInference,
    ) -> Result<RuntimeEvidence, RuntimeUnavailable> {
        if !candidate.observes_hir(hir) || !candidate.candidate_conflicts().is_empty() {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        }
        let mut receipts = candidate.operation_v1_field_bounds();
        let receipt = receipts.next().ok_or(RuntimeUnavailable::InvalidSourceReference)?;
        if !receipt.consumed || receipts.next().is_some() {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        }
        Ok(RuntimeEvidence {
            name_consumption: HashMap::new(),
            operation_v1: Some(OperationV1Link {
                hir_identity: hir as *const HirModule as usize,
                field_bound_id: receipt.id,
                request: receipt.request.clone(),
                callback_apply: receipt.callback_apply.clone(),
                callback_operation: receipt.callback_operation.clone(),
                callback_operation_use: receipt.callback_operation_use.clone(),
                response_definition: receipt.response_definition.clone(),
            }),
        })
    }

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
    pub fn execution_roots(&self) -> Result<Vec<ExecutionRoot>, RuntimeUnavailable> {
        Ok(self.source_schedule.clone())
    }
    pub fn from_hir(
        hir: Arc<HirModule>,
        evidence: RuntimeEvidence,
    ) -> Result<Arc<Self>, RuntimeUnavailable> {
        if evidence.operation_v1.as_ref().is_some_and(|link| {
            link.hir_identity != Arc::as_ptr(&hir) as usize
        }) {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        }
        let mut code = Vec::new();
        let mut definitions = Vec::new();
        let mut definition_indices = HashMap::new();
        let mut expression_roots = HashMap::new();
        let mut source_schedule = Vec::new();
        let mut source_labels = evidence.operation_v1.as_ref().map(|_| HashMap::new());
        let mut local_initializers = evidence.operation_v1.as_ref().map(|_| HashMap::new());
        let mut local_names_and_applies = evidence.operation_v1.as_ref().map(|_| Vec::new());
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
            let source_root = match item {
                HirItem::Binding(binding) => {
                    SourceRootId::Definition(binding.definition_root().clone())
                }
                HirItem::Expression(expression) => SourceRootId::Expression(
                    hir.expression_root(expression.occurrence())
                        .map_err(|_| RuntimeUnavailable::InvalidSourceReference)?
                        .ok_or(RuntimeUnavailable::MissingSource)?
                        .clone(),
                ),
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
                .local_source_for(&source_root)
                .map_err(|_| RuntimeUnavailable::MissingSource)?
                .ok_or(RuntimeUnavailable::MissingSource)?;
            if let Some(local_names_and_applies) = &mut local_names_and_applies {
                for expression in source.expressions() {
                    if let LocalSourceForm::Apply { callee, .. } = &expression.form {
                        let Some(callee_expression) = source.expression(callee) else {
                            return Err(RuntimeUnavailable::InvalidSourceReference);
                        };
                        if let LocalSourceForm::Name {
                            resolution: LocalSourceResolution::Local(binding),
                            ..
                        } = &callee_expression.form
                        {
                            local_names_and_applies.push((
                                binding.clone(),
                                source_root.clone(),
                                callee_expression.occurrence.clone(),
                                expression.occurrence.clone(),
                            ));
                        }
                    }
                }
            }
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
                            LocalSourceForm::Sequence { items } => {
                                for item in items.iter().rev() { work.push(Walk::Expression(item.clone())); }
                            }
                            LocalSourceForm::Catch { scrutinee, arms } => {
                                work.push(Walk::Expression(scrutinee.clone()));
                                for arm in arms {
                                    work.push(Walk::Expression(arm.body.clone()));
                                }
                            }
                            LocalSourceForm::Case { scrutinee, arms } => {
                                work.push(Walk::Expression(scrutinee.clone()));
                                for arm in arms {
                                    if let yu_hir::shadow::LocalSourceCasePattern::Integer(pattern) = &arm.pattern {
                                        work.push(Walk::Expression(pattern.clone()));
                                    }
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
                    let initializer = label(&local.initializer)?;
                    if let Some(local_initializers) = &mut local_initializers {
                        local_initializers.insert(local.id.clone(), initializer);
                    }
                    Ok(Arc::new(LocalBinding {
                        id: local.id.clone(),
                        initializer,
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
                    // supported authentic roots and registered Act placeholders
                    // are admitted.
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
                        root_schema: super::receiving::RootCompSchema::from_parameter(
                            &SourceSite {
                                source_root: source_root.clone(),
                                occurrence: expression.occurrence.clone(),
                                range: expression.range.clone(),
                            },
                            parameter,
                        ),
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
                    LocalSourceForm::Sequence { items } => Instruction::Sequence {
                        items: items.iter().map(label).collect::<Result<_, _>>()?,
                    },
                    LocalSourceForm::Case { scrutinee, arms } => Instruction::Case {
                        scrutinee: label(scrutinee)?,
                        arms: arms.iter().map(|arm| {
                            let pattern = match &arm.pattern {
                                yu_hir::shadow::LocalSourceCasePattern::Integer(index) => {
                                    let expression = source.expression(index).ok_or(RuntimeUnavailable::InvalidSourceReference)?;
                                    let LocalSourceForm::Integer(text) = &expression.form else {
                                        return Err(RuntimeUnavailable::InvalidSourceReference);
                                    };
                                    let text = super::literal::integer(text).ok_or_else(|| RuntimeUnavailable::LiteralDecoding(SourceSite {
                                        source_root: source_root.clone(), occurrence: expression.occurrence.clone(), range: expression.range.clone(),
                                    }))?;
                                    CasePattern::Integer(text)
                                }
                                yu_hir::shadow::LocalSourceCasePattern::Binder(binder) => {
                                    CasePattern::Binder(binder.id.clone())
                                }
                                yu_hir::shadow::LocalSourceCasePattern::Wildcard => CasePattern::Wildcard,
                            };
                            Ok(CaseArm { pattern, body: label(&arm.body)? })
                        }).collect::<Result<_, RuntimeUnavailable>>()?,
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
                let site = SourceSite {
                        source_root: source_root.clone(),
                        occurrence: expression.occurrence.clone(),
                        range: expression.range.clone(),
                    };
                if let Some(source_labels) = &mut source_labels {
                    source_labels.insert(expression.occurrence.clone(), Label(code.len()));
                }
                code.push(Arc::new(Code {
                    site,
                    instruction,
                }));
            }
            let body = label(source.body())?;
            match item {
                HirItem::Binding(binding) => {
                    let index = definitions.len();
                    definition_indices.insert(binding.id().clone(), index);
                    definitions.push(Definition {
                        id: binding.id().clone(),
                        body,
                    });
                    // Preserve the existing source fetch classifier. Expression
                    // demands below are unconditional, including bare values.
                    let mut current = body;
                    let computation = loop {
                        match &code
                            .get(current.0)
                            .ok_or(RuntimeUnavailable::InvalidSourceReference)?
                            .instruction
                        {
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
                        source_schedule.push(ExecutionRoot::Definition(binding.id().clone()));
                    }
                }
                HirItem::Expression(_) => {
                    let SourceRootId::Expression(root) = source_root else {
                        unreachable!()
                    };
                    expression_roots.insert(root.clone(), body);
                    source_schedule.push(ExecutionRoot::Expression(ExpressionExecutionRoot {
                        root,
                        code: body.0,
                    }));
                }
                HirItem::Error { .. } => unreachable!(),
            }
        }
        let operation_v1 = evidence.operation_v1.map(|link| {
            let label_for = |occurrence: &HirOccurrenceId| {
                source_labels.as_ref().and_then(|labels| labels.get(occurrence)).copied()
                    .ok_or(RuntimeUnavailable::InvalidSourceReference)
            };
            let site_for = |occurrence: &HirOccurrenceId| {
                let label = label_for(occurrence)?;
                code.get(label.0).map(|code| code.site.clone())
                    .ok_or(RuntimeUnavailable::InvalidSourceReference)
            };
            let request = site_for(&link.request)?;
            let request_label = label_for(&link.request)?;
            let request_operation = match &code[request_label.0].instruction {
                Instruction::Operation(SourceOperationResolution::Resolved(declaration)) => declaration.id.clone(),
                _ => return Err(RuntimeUnavailable::InvalidSourceReference),
            };
            let request_apply = source_apply_for_child(&code, request_label)?;
            let callback_apply = site_for(&link.callback_apply)?;
            let callback_operation = site_for(&link.callback_operation_use)?;
            if !matches!(code.get(label_for(&link.request)?.0).map(|code| &code.instruction), Some(Instruction::Operation(_)))
                || !matches!(code.get(label_for(&link.callback_operation_use)?.0).map(|code| &code.instruction), Some(Instruction::Operation(_)))
            {
                return Err(RuntimeUnavailable::InvalidSourceReference);
            }
            let apply_label = label_for(&link.callback_apply)?;
            let Instruction::Apply { callee, argument } = &code[apply_label.0].instruction else {
                return Err(RuntimeUnavailable::InvalidSourceReference);
            };
            if callee.0 != label_for(&link.callback_operation_use)?.0
                && argument.0 != label_for(&link.callback_operation_use)?.0
            {
                return Err(RuntimeUnavailable::InvalidSourceReference);
            }
            let initializer = local_initializers.as_ref()
                .and_then(|initializers| initializers.get(&link.response_definition))
                .copied().ok_or(RuntimeUnavailable::InvalidSourceReference)?;
            let mut response_label = initializer;
            loop {
                match &code.get(response_label.0)
                    .ok_or(RuntimeUnavailable::InvalidSourceReference)?.instruction
                {
                    Instruction::Forward(inner) => response_label = *inner,
                    Instruction::Lambda { .. } => break,
                    _ => return Err(RuntimeUnavailable::InvalidSourceReference),
                }
            }
            let response_lambda = code[response_label.0].site.clone();
            let handler_argument = operation_v1_handler_argument_join(
                &code,
                &request,
                &link.callback_operation,
                &link.response_definition,
            ).ok_or(RuntimeUnavailable::InvalidSourceReference)?;
            let continuation_apply = handler_argument.continuation_apply;
            let response_argument = handler_argument.response_argument;
            let local_lineage = operation_v1_local_lineage(
                &code,
                &hir,
                local_initializers.as_ref(),
                local_names_and_applies.as_ref(),
                &link.request,
                &continuation_apply,
                &callback_apply,
                &response_argument,
            )?;
            let response_invocation_apply = if let Some(lineage) = &local_lineage {
                lineage.apply.clone()
            } else {
                source_apply_for_catch_result(
                    &code,
                    &handler_argument.request_handler,
                ).ok_or(RuntimeUnavailable::InvalidSourceReference)?
            };
            if response_invocation_apply.occurrence == continuation_apply.occurrence
                || response_invocation_apply.occurrence == callback_apply.occurrence
            {
                return Err(RuntimeUnavailable::InvalidSourceReference);
            }
            let Instruction::Lambda { body, .. } = &code[response_label.0].instruction else {
                return Err(RuntimeUnavailable::InvalidSourceReference);
            };
            if callback_apply.source_root != response_lambda.source_root
                || !code_subtree_contains(&code, *body, apply_label)
            {
                return Err(RuntimeUnavailable::InvalidSourceReference);
            }
            let mut expected_outer = code.iter().filter_map(|candidate| {
                let Instruction::Catch { arms, .. } = &candidate.instruction else { return None; };
                arms.iter().find_map(|arm| {
                    let LocalSourceCatchPattern::Operation {
                        resolution: SourceOperationResolution::Resolved(declaration), ..
                    } = &arm.pattern else { return None; };
                    let matches_callback = declaration.id == link.callback_operation;
                    let returns_42 = matches!(code.get(arm.body.0).map(|body| &body.instruction),
                        Some(Instruction::Integer(text)) if text.as_ref() == "42");
                    (matches_callback && returns_42).then(|| (candidate.site.clone(), arm.source.clone()))
                })
            });
            let first_expected_outer = expected_outer.next();
            if expected_outer.next().is_some() {
                return Err(RuntimeUnavailable::InvalidSourceReference);
            }
            let (expected_outer_handler, expected_outer_arm) = first_expected_outer
                .map(|(handler, arm)| (Some(handler), Some(arm)))
                .unwrap_or((None, None));
            Ok(OperationV1Plan {
                link,
                response_lambda,
                callback_operation,
                request,
                request_apply,
                request_operation,
                request_handler: handler_argument.request_handler,
                request_arm: handler_argument.request_arm,
                response_argument,
                expected_outer_handler,
                expected_outer_arm,
                continuation_apply,
                response_invocation_apply,
                local_lineage,
            })
        }).transpose()?;
        let mut program = Self {
            _hir: hir,
            code,
            definitions,
            definition_indices,
            expression_roots,
            source_schedule,
            closed_primitive: false,
            operation_v1,
        };
        program.closed_primitive = super::primitive::closed_primitive(&program);
        Ok(Arc::new(program))
    }
}

fn operation_v1_local_lineage(
    code: &[Arc<Code>],
    hir: &HirModule,
    local_initializers: Option<&HashMap<HirLocalId, Label>>,
    local_names_and_applies: Option<&Vec<(
        HirLocalId,
        SourceRootId,
        HirOccurrenceId,
        HirOccurrenceId,
    )>>,
    request: &HirOccurrenceId,
    continuation_apply: &SourceSite,
    callback_apply: &SourceSite,
    response_argument: &SourceSite,
) -> Result<Option<OperationV1LocalLineage>, RuntimeUnavailable> {
    let source_root = code.iter().find_map(|candidate| {
        (candidate.site.occurrence == *request).then(|| candidate.site.source_root.clone())
    }).ok_or(RuntimeUnavailable::InvalidSourceReference)?;
    let label_for = |occurrence: &HirOccurrenceId| {
        let mut matches = code.iter().enumerate().filter(|(_, candidate)| {
            candidate.site.source_root == source_root
                && candidate.site.occurrence == *occurrence
        });
        let (index, _) = matches.next().ok_or(RuntimeUnavailable::InvalidSourceReference)?;
        if matches.next().is_some() {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        }
        Ok(Label(index))
    };

    let mut found = Vec::new();
    let mut has_local_catch_g = false;
    for item in hir.items() {
        let HirItem::Binding(binding) = item else { continue; };
        let binding_root = SourceRootId::Definition(binding.definition_root().clone());
        let Some(source) = hir.local_source_for(&binding_root)
            .map_err(|_| RuntimeUnavailable::MissingSource)? else { continue; };
        for local in source.bindings().iter().filter(|local| local.spelling.as_ref() == "g") {
            let initializer = local_initializers
                .and_then(|initializers| initializers.get(&local.id))
                .copied()
                .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
            let initializer_code = code.get(initializer.0)
                .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
            if binding_root != source_root
                || !matches!(&initializer_code.instruction, Instruction::Catch { .. })
                || initializer_code.site.source_root != binding_root
                || !code_subtree_contains(code, initializer, label_for(request)?)
            {
                continue;
            }
            has_local_catch_g = true;
            for (used_binding, use_root, name_occurrence, apply_occurrence) in
                local_names_and_applies.into_iter().flatten()
            {
                if used_binding != &local.id || use_root != &binding_root {
                    continue;
                }
                let name_label = label_for(name_occurrence)?;
                let apply_label = label_for(apply_occurrence)?;
                let Instruction::Name {
                    resolution: LocalSourceResolution::Local(resolved_binding),
                    ..
                } = &code[name_label.0].instruction else {
                    return Err(RuntimeUnavailable::InvalidSourceReference);
                };
                let Instruction::Apply { callee, .. } = &code[apply_label.0].instruction else {
                    return Err(RuntimeUnavailable::InvalidSourceReference);
                };
                if resolved_binding != &local.id || *callee != name_label {
                    return Err(RuntimeUnavailable::InvalidSourceReference);
                }
                found.push(OperationV1LocalLineage {
                    binding: local.id.clone(),
                    initializer_catch: initializer_code.site.clone(),
                    name_use: code[name_label.0].site.clone(),
                    apply: code[apply_label.0].site.clone(),
                });
            }
        }
    }
    if !has_local_catch_g {
        return Ok(None);
    }
    if found.len() != 1 {
        return Err(RuntimeUnavailable::InvalidSourceReference);
    }
    let lineage = found.pop().ok_or(RuntimeUnavailable::InvalidSourceReference)?;
    if lineage.apply.occurrence == continuation_apply.occurrence
        || lineage.apply.occurrence == callback_apply.occurrence
        || lineage.name_use.occurrence == response_argument.occurrence
    {
        return Err(RuntimeUnavailable::InvalidSourceReference);
    }
    Ok(Some(lineage))
}

fn operation_v1_handler_argument_join(
    code: &[Arc<Code>],
    request: &SourceSite,
    callback_operation: &yu_hir::shadow::SourceOperationId,
    response_definition: &HirLocalId,
) -> Option<HandlerArgumentJoin> {
    let Some((request_index, request_code)) = code.iter().enumerate().find(|(_, candidate)| {
        candidate.site.occurrence == request.occurrence
            && candidate.site.source_root == request.source_root
    }) else { return None; };
    let Instruction::Operation(SourceOperationResolution::Resolved(request_decl)) =
        &request_code.instruction else { return None; };
    let mut joins = Vec::new();
    for candidate in code {
        if candidate.site.source_root != request.source_root { continue; }
        let Instruction::Catch { scrutinee, arms } = &candidate.instruction else { continue; };
        if !code_subtree_contains(code, *scrutinee, Label(request_index)) { continue; }
        for arm in arms {
            let LocalSourceCatchPattern::Operation {
                resolution: SourceOperationResolution::Resolved(declaration),
                continuation: yu_hir::shadow::LocalSourceCatchValuePattern::Binder(continuation),
                ..
            } = &arm.pattern else { continue; };
            if declaration.id != request_decl.id { continue; }
            let Some(body) = code.get(arm.body.0) else { return None; };
            if body.site.source_root != request.source_root { continue; }
            for (apply_index, expression) in code.iter().enumerate() {
                if expression.site.source_root != request.source_root
                    || !code_subtree_contains(code, arm.body, Label(apply_index))
                { continue; }
                let Instruction::Apply { callee, argument } = &expression.instruction else { continue; };
                let Some(callee_code) = code.get(callee.0) else { return None; };
                let Some(argument_code) = code.get(argument.0) else { return None; };
                let callee_is_binder = matches!(&callee_code.instruction,
                    Instruction::Name { resolution: LocalSourceResolution::CatchBinder(found), .. }
                        if found == &continuation.id);
                let argument_is_definition = matches!(&argument_code.instruction,
                    Instruction::Name { resolution: LocalSourceResolution::Local(found), .. }
                        if found == response_definition);
                if callee_is_binder && argument_is_definition {
                    joins.push(HandlerArgumentJoin {
                        continuation_apply: expression.site.clone(),
                        response_argument: argument_code.site.clone(),
                        request_handler: candidate.site.clone(),
                        request_arm: arm.source.clone(),
                    });
                }
            }
        }
    }
    let callback_is_outer = code.iter().any(|candidate| {
        candidate.site.occurrence == request.occurrence
            && matches!(&candidate.instruction,
                Instruction::Operation(SourceOperationResolution::Resolved(declaration))
                    if &declaration.id == callback_operation)
    });
    if joins.len() == 1 && !callback_is_outer { joins.pop() } else { None }
}

fn source_apply_for_child(code: &[Arc<Code>], child: Label) -> Result<SourceSite, RuntimeUnavailable> {
    let mut matches = code.iter().filter_map(|candidate| {
        let Instruction::Apply { callee, argument } = &candidate.instruction else { return None; };
        (callee.0 == child.0 || argument.0 == child.0).then(|| candidate.site.clone())
    });
    let found = matches.next().ok_or(RuntimeUnavailable::InvalidSourceReference)?;
    if matches.next().is_some() {
        return Err(RuntimeUnavailable::InvalidSourceReference);
    }
    Ok(found)
}

fn source_apply_for_catch_result(
    code: &[Arc<Code>],
    handler: &SourceSite,
) -> Option<SourceSite> {
    let mut handlers = code.iter().enumerate().filter(|(_, candidate)| {
        candidate.site.source_root == handler.source_root
            && candidate.site.occurrence == handler.occurrence
            && matches!(&candidate.instruction, Instruction::Catch { .. })
    });
    let (handler_index, _) = handlers.next()?;
    if handlers.next().is_some() {
        return None;
    }
    let mut applications = code.iter().filter_map(|candidate| {
        if candidate.site.source_root != handler.source_root {
            return None;
        }
        let Instruction::Apply { callee, .. } = &candidate.instruction else {
            return None;
        };
        code_subtree_contains(code, *callee, Label(handler_index))
            .then(|| candidate.site.clone())
    });
    let found = applications.next()?;
    applications.next().is_none().then_some(found)
}

fn code_subtree_contains(code: &[Arc<Code>], root: Label, target: Label) -> bool {
    let mut stack = vec![root];
    let mut visited = HashSet::new();
    while let Some(label) = stack.pop() {
        if label == target { return true; }
        if !visited.insert(label.0) { continue; }
        let Some(expression) = code.get(label.0) else { continue; };
        match &expression.instruction {
            Instruction::Forward(inner) => stack.push(*inner),
            Instruction::Lambda { body, .. } => stack.push(*body),
            Instruction::Apply { callee, argument } => { stack.push(*argument); stack.push(*callee); }
            Instruction::Block { bindings, final_expression } => {
                stack.push(*final_expression);
                stack.extend(bindings.iter().map(|binding| binding.initializer));
            }
            Instruction::If { arms, else_branch } => {
                if let Some(branch) = else_branch { stack.push(*branch); }
                for (test, body) in arms { stack.push(*body); stack.push(*test); }
            }
            Instruction::Sequence { items } => stack.extend(items.iter().rev().copied()),
            Instruction::Catch { scrutinee, arms } => {
                stack.push(*scrutinee);
                stack.extend(arms.iter().map(|arm| arm.body));
            }
            Instruction::Case { scrutinee, arms } => {
                stack.push(*scrutinee);
                stack.extend(arms.iter().map(|arm| arm.body));
            }
            Instruction::Unit | Instruction::Integer(_) | Instruction::Boolean(_)
            | Instruction::String(_) | Instruction::Name { .. } | Instruction::Operation(_) => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::{Instruction, ParameterRole, RuntimeEvidence, RuntimeProgram};
    use std::sync::Arc;
    use yu_hir::shadow::{LocalSourceForm, lower_module_with_local_source};
    use yu_hir::{
        FileId, FileKey, HirItem, ModuleIdentity, SemanticImports, SourceAnnotation,
        SourceAnnotationValue, SourceRootId,
    };
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    const SOURCE: &str = "act signal:\n    our ping: () -> int\nmy loop x = loop x\nmy ignore (x:[] int) = 9\nmy main = ignore (loop ())";

    fn formal_for<'a>(hir: &'a yu_hir::HirModule, name: &str) -> (SourceRootId, &'a yu_hir::shadow::LocalSourceExpr, &'a yu_hir::shadow::LocalSourceParameter) {
        let binding = hir
            .items()
            .iter()
            .find_map(|item| match item {
                HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding),
                _ => None,
            })
            .unwrap_or_else(|| panic!("missing {name} binding"));
        let root = SourceRootId::Definition(binding.definition_root().clone());
        let source = hir.local_source_for(&root).unwrap().unwrap();
        let (lambda, parameter) = source
            .expressions()
            .iter()
            .find_map(|expression| match &expression.form {
                LocalSourceForm::Lambda { parameter, .. } if parameter.spelling.as_ref() == "x" => {
                    Some((expression, parameter))
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("missing {name} formal lambda"));
        (root, lambda, parameter)
    }

    fn assert_annotation_projection(original: &SourceAnnotation, projected: &SourceAnnotation) {
        assert_eq!(projected.owner, original.owner);
        assert_eq!(projected.position, original.position);
        assert!(matches!(&original.ty.value, SourceAnnotationValue::Int));
        assert!(matches!(&projected.ty.value, SourceAnnotationValue::Int));
        let original_effects = original.ty.effects.as_ref().expect("source [] row retained");
        let projected_effects = projected.ty.effects.as_ref().expect("projected [] row retained");
        assert_eq!(projected_effects.position, original_effects.position);
        assert_eq!(projected_effects.concrete, original_effects.concrete);
        assert_eq!(projected_effects.variables, original_effects.variables);
        assert!(original_effects.concrete.is_empty());
        assert!(original_effects.variables.is_empty());
    }

    #[test]
    fn runtime_program_emits_computation_role_with_original_formal_and_schema() {
        let source: Arc<SourceText> = Arc::from(SOURCE);
        let parsed = parse_file(
            source.clone(),
            Arc::new(scan_header(source)),
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let hir = Arc::new(
            lower_module_with_local_source(
                ModuleIdentity::source_root(FileId::new(FileKey::new(
                    "runtime-program-projection",
                    "test.yu",
                ))),
                &parsed,
                SemanticImports::empty(),
            )
            .unwrap(),
        );

        let (ignore_root, ignore_lambda, original_formal) = formal_for(&hir, "ignore");
        let original_annotation = original_formal
            .annotation
            .as_ref()
            .expect("ignore formal has the source [] int annotation");
        assert_eq!(original_annotation.owner, ignore_root);

        let program = RuntimeProgram::from_hir(hir.clone(), RuntimeEvidence::default()).unwrap();
        let mut ignore_emissions = program.code.iter().filter_map(|code| match &code.instruction {
            Instruction::Lambda {
                parameter,
                role,
                root_schema,
                ..
            } if parameter == &original_formal.id => Some((code, *role, root_schema)),
            _ => None,
        });
        let (ignore_code, ignore_role, ignore_schema) =
            ignore_emissions.next().expect("ignore Lambda emitted");
        assert!(ignore_emissions.next().is_none(), "formal emitted exactly once");
        assert_eq!(ignore_role, ParameterRole::Computation);
        assert_eq!(ignore_code.site.source_root, ignore_root);
        assert_eq!(ignore_code.site.occurrence, ignore_lambda.occurrence);
        assert_eq!(ignore_code.site.range, ignore_lambda.range);
        let ignore_schema = ignore_schema.as_ref().expect("positive RootCompSchema emitted");
        assert_eq!(ignore_schema.formal.id, original_formal.id);
        assert_eq!(ignore_schema.formal.source, original_formal.source);
        assert_eq!(ignore_schema.formal.range, original_formal.range);
        assert_eq!(ignore_schema.formal.spelling, original_formal.spelling);
        assert_eq!(ignore_schema.lambda.source_root, ignore_root);
        assert_eq!(ignore_schema.lambda.occurrence, ignore_lambda.occurrence);
        assert_eq!(ignore_schema.lambda.range, ignore_lambda.range);
        assert_annotation_projection(
            original_annotation,
            ignore_schema.formal.annotation.as_ref().unwrap(),
        );

        let (loop_root, loop_lambda, original_loop_formal) = formal_for(&program._hir, "loop");
        assert!(original_loop_formal.annotation.is_none());
        let mut loop_emissions = program.code.iter().filter_map(|code| match &code.instruction {
            Instruction::Lambda {
                parameter,
                role,
                root_schema,
                ..
            } if parameter == &original_loop_formal.id => Some((code, *role, root_schema)),
            _ => None,
        });
        let (loop_code, loop_role, loop_schema) =
            loop_emissions.next().expect("loop Lambda emitted");
        assert!(loop_emissions.next().is_none(), "formal emitted exactly once");
        assert_eq!(loop_role, ParameterRole::Value);
        assert!(loop_schema.is_none());
        assert_eq!(loop_code.site.source_root, loop_root);
        assert_eq!(loop_code.site.occurrence, loop_lambda.occurrence);
        assert_eq!(loop_code.site.range, loop_lambda.range);
    }
}
