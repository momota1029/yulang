//! Nonshipping source formation owned by the HIR lowering event.
use super::*;
use yu_syntax::SourceNodeKey;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct LocalSourceIndex {
    owner: DefinitionRootId,
    ordinal: u32,
}

impl LocalSourceIndex {
    pub fn ordinal(&self) -> u32 {
        self.ordinal
    }
}
#[derive(Clone, Debug)]
pub struct LocalSource {
    owner: DefinitionRootId,
    body: LocalSourceIndex,
    expressions: Vec<LocalSourceExpr>,
    bindings: Vec<LocalSourceBinding>,
    annotation: Option<source_annotation::SourceAnnotation>,
}
impl LocalSource {
    pub fn definition_root(&self) -> &DefinitionRootId {
        &self.owner
    }
    pub fn body(&self) -> &LocalSourceIndex {
        &self.body
    }
    pub fn expression(&self, index: &LocalSourceIndex) -> Option<&LocalSourceExpr> {
        (index.owner == self.owner)
            .then(|| self.expressions.get(index.ordinal as usize))
            .flatten()
    }
    pub fn expressions(&self) -> &[LocalSourceExpr] {
        &self.expressions
    }
    pub fn annotation(&self) -> Option<&source_annotation::SourceAnnotation> {
        self.annotation.as_ref()
    }
    pub fn bindings(&self) -> &[LocalSourceBinding] {
        &self.bindings
    }
    /// Reserved arena/vector storage and retained spelling bytes; shared source
    /// and artifact payloads and allocator overhead are excluded.
    pub fn retained_arena_bytes(&self) -> usize {
        self.annotation
            .as_ref()
            .map_or(0, |annotation| annotation.retained_arena_bytes())
            + self.expressions.capacity() * std::mem::size_of::<LocalSourceExpr>()
            + self.bindings.capacity() * std::mem::size_of::<LocalSourceBinding>()
            + self
                .expressions
                .iter()
                .map(|expr| match &expr.form {
                    LocalSourceForm::Integer(text) | LocalSourceForm::String(text) => text.len(),
                    LocalSourceForm::If { arms, .. } => {
                        arms.capacity() * std::mem::size_of::<(LocalSourceIndex, LocalSourceIndex)>()
                    }
                    LocalSourceForm::Name { spelling, .. } => spelling.len(),
                    LocalSourceForm::Lambda { parameter, .. } => {
                        parameter.spelling.len()
                            + parameter
                                .annotation
                                .as_ref()
                                .map_or(0, |annotation| annotation.retained_arena_bytes())
                    }
                    LocalSourceForm::Ascription { annotation, .. } => {
                        annotation.retained_arena_bytes()
                    }
                    LocalSourceForm::Block { bindings, .. } => {
                        bindings.capacity() * std::mem::size_of::<u32>()
                    }
                    _ => 0,
                })
                .sum::<usize>()
            + self
                .bindings
                .iter()
                .map(|binding| {
                    binding.spelling.len()
                        + binding.annotation.as_ref().map_or(0, |annotation| annotation.retained_arena_bytes())
                        + binding.parameters.capacity()
                            * std::mem::size_of::<LocalSourceParameter>()
                        + binding
                            .parameters
                            .iter()
                            .map(|parameter| {
                                parameter.spelling.len()
                                    + parameter
                                        .annotation
                                        .as_ref()
                                        .map_or(0, |annotation| annotation.retained_arena_bytes())
                            })
                            .sum::<usize>()
                })
                .sum::<usize>()
    }
}
#[derive(Clone, Debug)]
pub struct LocalSourceExpr {
    pub occurrence: HirOccurrenceId,
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub scope: LocalSourceScope,
    pub form: LocalSourceForm,
}
#[derive(Clone, Debug)]
pub enum LocalSourceForm {
    Unit,
    Operation {
        resolution: source_annotation::SourceOperationResolution,
    },
    Integer(Box<str>),
    Boolean(bool),
    String(Box<str>),
    If {
        arms: Vec<(LocalSourceIndex, LocalSourceIndex)>,
        else_branch: LocalSourceIndex,
    },
    Name {
        spelling: Box<str>,
        resolution: LocalSourceResolution,
    },
    Apply {
        callee: LocalSourceIndex,
        argument: LocalSourceIndex,
        source_form: SyntaxKind,
    },
    Group {
        inner: LocalSourceIndex,
    },
    Ascription {
        inner: LocalSourceIndex,
        annotation: source_annotation::SourceAnnotation,
    },
    Lambda {
        parameter: LocalSourceParameter,
        body: LocalSourceIndex,
    },
    Block {
        bindings: Vec<u32>,
        final_expression: LocalSourceIndex,
    },
}
#[derive(Clone, Debug)]
pub enum LocalSourceResolution {
    ModuleDef(DefId),
    Parameter(HirParameterId),
    Local(HirLocalId),
    Unresolved,
    Ambiguous,
}
#[derive(Clone, Debug)]
pub enum LocalSourceScope {
    Definition(DefinitionRootId),
    Expression(LocalSourceIndex),
    Parameter(HirParameterId),
    LocalInitializer(HirLocalId),
}
#[derive(Clone, Debug)]
pub struct LocalSourceParameter {
    pub id: HirParameterId,
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub spelling: Box<str>,
    pub scope: LocalSourceScope,
    pub annotation: Option<source_annotation::SourceAnnotation>,
}
#[derive(Clone, Debug)]
pub struct LocalSourceBinding {
    pub annotation: Option<source_annotation::SourceAnnotation>,
    pub id: HirLocalId,
    pub binder_source: SourceNodeKey,
    pub range: Range<usize>,
    pub spelling: Box<str>,
    pub parameters: Vec<LocalSourceParameter>,
    pub initializer: LocalSourceIndex,
    pub scope: LocalSourceScope,
}

pub(super) enum SimpleBodyProjection {
    Atom(crate::OwnedAtom),
    Unsupported,
}

enum Work {
    Expression(SyntaxNode, LocalSourceIndex, LocalSourceScope),
    Initializer(u32, SyntaxNode),
    Publish(u32, usize),
    Restore(usize),
}
struct LexicalEntry {
    spelling: Box<str>,
    resolution: LocalSourceResolution,
    previous: Option<usize>,
}
struct Builder<'a> {
    owner: &'a DefinitionRootId,
    namespace: &'a HashMap<String, Vec<DefId>>,
    counters: &'a mut LoweringCounters,
    artifact: &'a Arc<HirArtifactToken>,
    next_occurrence: &'a mut u32,
    next_parameter: u32,
    expressions: Vec<Option<LocalSourceExpr>>,
    bindings: Vec<LocalSourceBinding>,
    lexical: Vec<LexicalEntry>,
    latest: HashMap<Box<str>, usize>,
    work: Vec<Work>,
}
fn invalid() -> HirAvailabilityError {
    HirAvailabilityError::StructuralProjection
}
fn push<T>(values: &mut Vec<T>, value: T) -> Result<(), HirAvailabilityError> {
    values
        .try_reserve(1)
        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    values.push(value);
    Ok(())
}
fn only_child(node: &SyntaxNode) -> Result<SyntaxNode, HirAvailabilityError> {
    let mut children = node.children();
    let child = children.next().ok_or_else(invalid)?;
    if children.next().is_some() {
        return Err(invalid());
    }
    Ok(child)
}
pub(crate) fn inline_colon_argument(node: &SyntaxNode) -> Result<SyntaxNode, HirAvailabilityError> {
    let child = only_child(node)?;
    if child.kind() != SyntaxKind::OperatorChain {
        return Err(invalid());
    }
    Ok(child)
}
fn body(statement: &SyntaxNode) -> Result<SyntaxNode, HirAvailabilityError> {
    let mut nodes = Vec::new();
    for node in statement.children() {
        push(&mut nodes, node)?;
    }
    if !matches!(nodes.as_slice(), [header, body] if header.kind() == SyntaxKind::BindingHeader && body.kind() == SyntaxKind::BindingBody)
    {
        return Err(invalid());
    }
    let mut header_kinds = nodes[0]
        .children_with_tokens()
        .filter(|element| {
            !matches!(
                element.kind(),
                SyntaxKind::Whitespace
                    | SyntaxKind::Newline
                    | SyntaxKind::LineComment
                    | SyntaxKind::BlockComment
            )
        })
        .map(|element| element.kind());
    if header_kinds.next() != Some(SyntaxKind::MyKw)
        || header_kinds.next() != Some(SyntaxKind::Pattern)
        || header_kinds.next() != Some(SyntaxKind::Equals)
        || header_kinds.next().is_some()
    {
        return Err(invalid());
    }
    let child = only_child(&nodes[1])?;
    if child.kind() != SyntaxKind::OperatorChain {
        return Err(invalid());
    }
    Ok(child)
}
pub(super) fn form(
    plan: &RootPlan,
    owner: &DefinitionRootId,
    parameters: &[HirParameter],
    namespace: &HashMap<String, Vec<DefId>>,
    counters: &mut LoweringCounters,
    artifact: &Arc<HirArtifactToken>,
    next_occurrence: &mut u32,
) -> Result<(LocalSource, SimpleBodyProjection), HirAvailabilityError> {
    if has_recovery(&plan.node) || parameters.len() >= 128 {
        return Err(invalid());
    }
    let RootPlanKind::Binding(admitted) = &plan.kind else {
        return Err(invalid());
    };
    let mut builder = Builder {
        owner,
        namespace,
        counters,
        artifact,
        next_occurrence,
        next_parameter: u32::try_from(parameters.len())
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?,
        expressions: Vec::new(),
        bindings: Vec::new(),
        lexical: Vec::new(),
        latest: HashMap::new(),
        work: Vec::new(),
    };
    let root = builder.slot()?;
    let mut current = root.clone();
    let mut scope = LocalSourceScope::Definition(owner.clone());
    for (parameter, admitted) in parameters.iter().zip(&admitted.parameters) {
        let parameter = LocalSourceParameter {
            id: parameter.id.clone(),
            source: admitted.source.clone().ok_or_else(invalid)?,
            range: parameter.range.clone(),
            spelling: parameter.name.spelling.clone().into_boxed_str(),
            scope: scope.clone(),
            annotation: admitted
                .annotation
                .as_ref()
                .map(|node| source_annotation::parse_annotation(node, owner, builder.counters))
                .transpose()?,
        };
        builder.push_binding(
            parameter.spelling.clone(),
            LocalSourceResolution::Parameter(parameter.id.clone()),
        )?;
        let next = builder.slot()?;
        builder.set(
            current,
            &plan.node,
            scope,
            LocalSourceForm::Lambda {
                parameter: parameter.clone(),
                body: next.clone(),
            },
        )?;
        current = next;
        scope = LocalSourceScope::Parameter(parameter.id);
    }
    let body_chain = body(&plan.node)?;
    push(
        &mut builder.work,
        Work::Expression(body_chain.clone(), current, scope),
    )?;
    while let Some(work) = builder.work.pop() {
        match work {
            Work::Expression(node, index, scope) => {
                builder.expression(node, index, scope)?
            }
            Work::Restore(depth) => builder.restore(depth),
            Work::Initializer(binding, node) => {
                let guard = builder.lexical.len();
                let data = &builder.bindings[binding as usize];
                let mut scope = LocalSourceScope::LocalInitializer(data.id.clone());
                let mut index = data.initializer.clone();
                let count = data.parameters.len();
                let self_binding = (count != 0).then(|| (data.spelling.clone(), data.id.clone()));
                // The temporary self identity belongs to the initializer scope;
                // parameters may shadow it, and Publish restores then installs it.
                if let Some((spelling, id)) = self_binding {
                    builder.push_binding(spelling, LocalSourceResolution::Local(id))?;
                }
                push(&mut builder.work, Work::Publish(binding, guard))?;
                for ordinal in 0..count {
                    let parameter = builder.bindings[binding as usize].parameters[ordinal].clone();
                    builder.push_binding(
                        parameter.spelling.clone(),
                        LocalSourceResolution::Parameter(parameter.id.clone()),
                    )?;
                    let next = builder.slot()?;
                    builder.set(
                        index,
                        &node,
                        scope,
                        LocalSourceForm::Lambda {
                            parameter: parameter.clone(),
                            body: next.clone(),
                        },
                    )?;
                    index = next;
                    scope = LocalSourceScope::Parameter(parameter.id);
                }
                push(
                    &mut builder.work,
                    Work::Expression(body(&node)?, index, scope),
                )?;
            }
            Work::Publish(binding, guard) => {
                builder.restore(guard);
                let data = &builder.bindings[binding as usize];
                builder.push_binding(
                    data.spelling.clone(),
                    LocalSourceResolution::Local(data.id.clone()),
                )?;
            }
        }
    }
    let mut expressions = Vec::new();
    expressions
        .try_reserve_exact(builder.expressions.len())
        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    for expression in builder.expressions {
        expressions.push(expression.ok_or_else(invalid)?);
    }
    let source = LocalSource {
        owner: owner.clone(),
        body: root,
        expressions,
        bindings: builder.bindings,
        annotation: source_annotation::form(&plan.node, owner, counters)?,
    };
    // Successful formation establishes that this actual root chain has the
    // same simple result without constructing a discarded associated tree.
    let projection = if source.expressions().iter().any(|expr| {
        matches!(expr.form, LocalSourceForm::Boolean(_) | LocalSourceForm::String(_) | LocalSourceForm::If { .. })
    }) {
        SimpleBodyProjection::Unsupported
    } else {
        crate::direct_atom(&body_chain)
            .map_or(SimpleBodyProjection::Unsupported, SimpleBodyProjection::Atom)
    };
    Ok((source, projection))
}
impl Builder<'_> {
    fn push_binding(
        &mut self,
        spelling: Box<str>,
        resolution: LocalSourceResolution,
    ) -> Result<(), HirAvailabilityError> {
        let previous = self.latest.get(spelling.as_ref()).copied();
        self.lexical
            .try_reserve(1)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        let new_key = if previous.is_none() {
            self.latest
                .try_reserve(1)
                .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            Some(spelling.clone())
        } else {
            None
        };
        let index = self.lexical.len();
        self.lexical.push(LexicalEntry {
            spelling,
            resolution,
            previous,
        });
        if let Some(key) = new_key {
            self.latest.insert(key, index);
        } else {
            *self
                .latest
                .get_mut(self.lexical[index].spelling.as_ref())
                .expect("active spelling has a latest binding") = index;
        }
        Ok(())
    }
    fn restore(&mut self, depth: usize) {
        while self.lexical.len() > depth {
            let entry = self.lexical.pop().expect("binding above restore depth");
            if let Some(previous) = entry.previous {
                *self
                    .latest
                    .get_mut(entry.spelling.as_ref())
                    .expect("active spelling has a latest binding") = previous;
            } else {
                self.latest.remove(entry.spelling.as_ref());
            }
        }
    }
    fn slot(&mut self) -> Result<LocalSourceIndex, HirAvailabilityError> {
        let index = u32::try_from(self.expressions.len())
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        push(&mut self.expressions, None)?;
        Ok(LocalSourceIndex {
            owner: self.owner.clone(),
            ordinal: index,
        })
    }
    fn key(&self, node: &SyntaxNode) -> Result<SourceNodeKey, HirAvailabilityError> {
        self.counters
            .source_nodes
            .get(node)
            .cloned()
            .ok_or_else(invalid)
    }
    fn set(
        &mut self,
        index: LocalSourceIndex,
        node: &SyntaxNode,
        scope: LocalSourceScope,
        form: LocalSourceForm,
    ) -> Result<(), HirAvailabilityError> {
        let source = self.key(node)?;
        let occurrence = next_occurrence(self.artifact, self.next_occurrence)?;
        self.counters
            .source_identity
            .as_mut()
            .ok_or_else(invalid)?
            .record_occurrence(occurrence.clone(), source.clone());
        self.expressions[index.ordinal as usize] = Some(LocalSourceExpr {
            occurrence,
            source,
            range: range_of(node),
            scope,
            form,
        });
        Ok(())
    }
    fn expression(
        &mut self,
        node: SyntaxNode,
        index: LocalSourceIndex,
        scope: LocalSourceScope,
    ) -> Result<(), HirAvailabilityError> {
        match node.kind() {
            SyntaxKind::OperatorChain => {
                let mut children = Vec::new();
                for child in node.children() {
                    push(&mut children, child)?;
                }
                let (head, all_tails) = children.split_first().ok_or_else(invalid)?;
                let operation_tail = all_tails
                    .first()
                    .filter(|tail| tail.kind() == SyntaxKind::PathTail);
                let tails = if operation_tail.is_some() {
                    &all_tails[1..]
                } else {
                    all_tails
                };
                let mut current = index;
                for tail in tails.iter().rev() {
                    if tail.kind() == SyntaxKind::TypeAnnotationTail {
                        let annotation = source_annotation::parse_expression_ascription(
                            tail,
                            self.owner,
                            self.counters,
                        )?;
                        let inner = self.slot()?;
                        self.set(
                            current,
                            tail,
                            scope.clone(),
                            LocalSourceForm::Ascription {
                                inner: inner.clone(),
                                annotation,
                            },
                        )?;
                        current = inner;
                        continue;
                    }
                    if !matches!(
                        tail.kind(),
                        SyntaxKind::MlArgument
                            | SyntaxKind::CallTail
                            | SyntaxKind::ColonApplicationTail
                    ) {
                        return Err(invalid());
                    }
                    if tail.children_with_tokens().any(|element| {
                        matches!(
                            element.kind(),
                            SyntaxKind::Comma | SyntaxKind::ExpressionDelimitedSeparator
                        )
                    }) {
                        return Err(invalid());
                    }
                    let argument_node = if tail.kind() == SyntaxKind::CallTail
                        && tail.children().next().is_none()
                    {
                        None
                    } else {
                        Some(if tail.kind() == SyntaxKind::ColonApplicationTail {
                            inline_colon_argument(tail)?
                        } else {
                            only_child(tail)?
                        })
                    };
                    let callee = self.slot()?;
                    let argument = self.slot()?;
                    self.set(
                        current,
                        tail,
                        scope.clone(),
                        LocalSourceForm::Apply {
                            callee: callee.clone(),
                            argument: argument.clone(),
                            source_form: tail.kind(),
                        },
                    )?;
                    if let Some(argument_node) = argument_node {
                        push(
                            &mut self.work,
                            Work::Expression(argument_node, argument, scope.clone()),
                        )?;
                    } else {
                        self.set(argument, tail, scope.clone(), LocalSourceForm::Unit)?;
                    }
                    current = callee;
                }
                if let Some(tail) = operation_tail {
                    if head.kind() != SyntaxKind::IdentifierExpression || has_recovery(tail) {
                        return Err(invalid());
                    }
                    let tokens: Vec<_> = tail
                        .children_with_tokens()
                        .filter(|e| {
                            !matches!(e.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline)
                        })
                        .collect();
                    let [separator, member] = tokens.as_slice() else {
                        return Err(invalid());
                    };
                    if separator.kind() != SyntaxKind::ColonColon
                        || member.kind() != SyntaxKind::Identifier
                    {
                        return Err(invalid());
                    }
                    let family = head.text().to_string();
                    let member: Box<str> = member.to_string().into_boxed_str();
                    use source_annotation::SourceOperationResolution;
                    let resolution = match self.counters.effect_namespace.get(&family) {
                        None => SourceOperationResolution::Unresolved,
                        Some(families) if families.len() != 1 => {
                            SourceOperationResolution::Ambiguous
                        }
                        Some(families) => match self
                            .counters
                            .operation_namespace
                            .get(&(families[0].clone(), member))
                        {
                            None => SourceOperationResolution::Unresolved,
                            Some(members) if members.len() != 1 => {
                                SourceOperationResolution::Ambiguous
                            }
                            Some(members) if members[0].visibility == HirVisibility::Private => {
                                SourceOperationResolution::Private
                            }
                            Some(members) => {
                                SourceOperationResolution::Resolved(members[0].clone())
                            }
                        },
                    };
                    self.set(
                        current,
                        tail,
                        scope,
                        LocalSourceForm::Operation { resolution },
                    )?;
                } else {
                    push(
                        &mut self.work,
                        Work::Expression(head.clone(), current, scope),
                    )?;
                }
            }
            SyntaxKind::IdentifierExpression => {
                let spelling: Box<str> = node.text().to_string().into_boxed_str();
                if !self.latest.contains_key(spelling.as_ref()) {
                    let boolean = match spelling.as_ref() {
                        "true" => Some(true),
                        "false" => Some(false),
                        _ => None,
                    };
                    if let Some(value) = boolean {
                        self.set(index, &node, scope, LocalSourceForm::Boolean(value))?;
                        return Ok(());
                    }
                }
                let resolution = self
                    .latest
                    .get(spelling.as_ref())
                    .map(|&index| self.lexical[index].resolution.clone())
                    .unwrap_or_else(|| match self.namespace.get(spelling.as_ref()) {
                        Some(ids) if ids.len() == 1 => {
                            LocalSourceResolution::ModuleDef(ids[0].clone())
                        }
                        Some(_) => LocalSourceResolution::Ambiguous,
                        None => LocalSourceResolution::Unresolved,
                    });
                self.set(
                    index,
                    &node,
                    scope,
                    LocalSourceForm::Name {
                        spelling,
                        resolution,
                    },
                )?;
            }
            SyntaxKind::IntegerLiteral => self.set(
                index,
                &node,
                scope,
                LocalSourceForm::Integer(node.text().to_string().into_boxed_str()),
            )?,
            SyntaxKind::StringLiteral => {
                if node.descendants().any(|child| child.kind() == SyntaxKind::StringInterpolation) {
                    return Err(invalid());
                }
                self.set(index, &node, scope, LocalSourceForm::String(node.text().to_string().into_boxed_str()))?;
            }
            SyntaxKind::IfExpression => self.conditional(node, index, scope)?,
            SyntaxKind::ParenthesizedExpression => {
                if node.children_with_tokens().any(|element| {
                    matches!(
                        element.kind(),
                        SyntaxKind::Comma | SyntaxKind::ExpressionDelimitedSeparator
                    )
                }) {
                    return Err(invalid());
                }
                if node.children().next().is_none() {
                    self.set(index, &node, scope, LocalSourceForm::Unit)?;
                    return Ok(());
                }
                let child = only_child(&node)?;
                let inner = self.slot()?;
                self.set(
                    index,
                    &node,
                    scope.clone(),
                    LocalSourceForm::Group {
                        inner: inner.clone(),
                    },
                )?;
                push(
                    &mut self.work,
                    Work::Expression(child, inner, scope),
                )?;
            }
            SyntaxKind::BracedStatementBlockExpression | SyntaxKind::IndentedStatementBlock => self.block(node, index, scope)?,
            _ => return Err(invalid()),
        }
        Ok(())
    }
    fn conditional(
        &mut self,
        node: SyntaxNode,
        index: LocalSourceIndex,
        scope: LocalSourceScope,
    ) -> Result<(), HirAvailabilityError> {
        let conditional_scope = LocalSourceScope::Expression(index.clone());
        let mut arms = Vec::new();
        let mut children = Vec::new();
        let mut else_branch = None;
        for arm in node.children() {
            match arm.kind() {
                SyntaxKind::IfArm if else_branch.is_none() => {
                    let parts: Vec<_> = arm.children().collect();
                    let [condition, body] = parts.as_slice() else { return Err(invalid()); };
                    if condition.kind() != SyntaxKind::Condition
                        || !matches!(body.kind(), SyntaxKind::OperatorChain | SyntaxKind::IndentedStatementBlock)
                    {
                        return Err(invalid());
                    }
                    let condition_node = only_child(condition)?;
                    if condition_node.kind() != SyntaxKind::OperatorChain { return Err(invalid()); }
                    let condition_index = self.slot()?;
                    let body_index = self.slot()?;
                    push(&mut arms, (condition_index.clone(), body_index.clone()))?;
                    push(&mut children, (condition_node, condition_index))?;
                    push(&mut children, (body.clone(), body_index))?;
                }
                SyntaxKind::ElseArm if !arms.is_empty() && else_branch.is_none() => {
                    let body = only_child(&arm)?;
                    if !matches!(body.kind(), SyntaxKind::OperatorChain | SyntaxKind::IndentedStatementBlock) {
                        return Err(invalid());
                    }
                    let body_index = self.slot()?;
                    else_branch = Some(body_index.clone());
                    push(&mut children, (body, body_index))?;
                }
                _ => return Err(invalid()),
            }
        }
        let else_branch = else_branch.ok_or_else(invalid)?;
        self.set(index, &node, scope, LocalSourceForm::If { arms, else_branch })?;
        let depth = self.lexical.len();
        // Every condition and body starts in the enclosing lexical environment.
        for (child, child_index) in children.into_iter().rev() {
            push(&mut self.work, Work::Restore(depth))?;
            push(&mut self.work, Work::Expression(child, child_index, conditional_scope.clone()))?;
        }
        Ok(())
    }
    fn block(
        &mut self,
        node: SyntaxNode,
        index: LocalSourceIndex,
        scope: LocalSourceScope,
    ) -> Result<(), HirAvailabilityError> {
        let mut statements = Vec::new();
        let mut expect_statement = true;
        for child in node.children() {
            if expect_statement && child.kind() == SyntaxKind::Statement {
                push(&mut statements, only_child(&child)?)?;
            } else if !expect_statement && child.kind() == SyntaxKind::BlockStatementSeparator {
                if child.children().next().is_some() {
                    return Err(invalid());
                }
            } else {
                return Err(invalid());
            }
            expect_statement = !expect_statement;
        }
        let final_node = statements.pop().ok_or_else(invalid)?;
        if final_node.kind() != SyntaxKind::OperatorChain {
            return Err(invalid());
        }
        let block_scope = LocalSourceScope::Expression(index.clone());
        let final_expression = self.slot()?;
        let mut bindings = Vec::new();
        let mut initializers = Vec::new();
        for statement in statements {
            if statement.kind() != SyntaxKind::BindingStatement {
                return Err(invalid());
            }
            let annotation = source_annotation::form(&statement, &self.owner, self.counters)?;
            let (visibility, name, parameters) =
                plain_binding_header(&statement, self.counters).ok_or_else(invalid)?;
            if visibility != HirVisibility::Private {
                return Err(invalid());
            }
            body(&statement)?;
            let ordinal = u32::try_from(self.bindings.len())
                .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            let id = HirLocalId {
                owner: self.owner.clone(),
                ordinal,
            };
            let header = statement
                .children()
                .find(|child| child.kind() == SyntaxKind::BindingHeader)
                .ok_or_else(invalid)?;
            let pattern = only_child(&header)?;
            let binder = pattern.children().next().ok_or_else(invalid)?;
            let binder_source = self.key(&binder)?;
            self.counters
                .source_identity
                .as_mut()
                .ok_or_else(invalid)?
                .record_local(id.clone(), binder_source.clone());
            let mut retained_parameters = Vec::new();
            let mut parameter_scope = LocalSourceScope::LocalInitializer(id.clone());
            for parameter in parameters {
                let ordinal = self.next_parameter;
                self.next_parameter = ordinal
                    .checked_add(1)
                    .ok_or(HirAvailabilityError::IdentityExhausted)?;
                let parameter_id = HirParameterId::new(self.owner.clone(), ordinal);
                let source = parameter.source.ok_or_else(invalid)?;
                let source_identity = self.counters.source_identity.as_mut().ok_or_else(invalid)?;
                source_identity.record_parameter(parameter_id.clone(), source.clone());
                source_identity
                    .local_parameter_owners
                    .insert(parameter_id.clone(), id.clone());
                push(
                    &mut retained_parameters,
                    LocalSourceParameter {
                        id: parameter_id.clone(),
                        source,
                        range: parameter.name.range,
                        spelling: parameter.name.spelling.into_boxed_str(),
                        annotation: parameter
                            .annotation
                            .as_ref()
                            .map(|node| {
                                source_annotation::parse_annotation(
                                    node,
                                    &self.owner,
                                    self.counters,
                                )
                            })
                            .transpose()?,
                        scope: parameter_scope,
                    },
                )?;
                parameter_scope = LocalSourceScope::Parameter(parameter_id);
            }
            let initializer = self.slot()?;
            push(
                &mut self.bindings,
                LocalSourceBinding {
                    annotation,
                    id,
                    binder_source,
                    range: name.range,
                    spelling: name.spelling.into_boxed_str(),
                    parameters: retained_parameters,
                    initializer,
                    scope: block_scope.clone(),
                },
            )?;
            push(&mut bindings, ordinal)?;
            push(&mut initializers, (ordinal, statement))?;
        }
        self.set(
            index,
            &node,
            scope,
            LocalSourceForm::Block {
                bindings,
                final_expression: final_expression.clone(),
            },
        )?;
        push(&mut self.work, Work::Restore(self.lexical.len()))?;
        push(
            &mut self.work,
            Work::Expression(final_node, final_expression, block_scope),
        )?;
        for (ordinal, statement) in initializers.into_iter().rev() {
            push(&mut self.work, Work::Initializer(ordinal, statement))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lower(text: &str) -> Result<HirModule, HirAvailabilityError> {
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("test", "unit.yu"))),
            &parsed,
            SemanticImports::empty(),
        )
    }

    #[test]
    fn single_ascription_retains_tail_annotation_and_child() {
        let module = lower("my value = 1 as 'a").unwrap();
        let source = module.local_sources.values().next().unwrap();
        let expr = source.expression(source.body()).unwrap();
        let LocalSourceForm::Ascription { inner, annotation } = &expr.form else {
            panic!("expected expression ascription");
        };
        assert_eq!(expr.range, 13..18);
        assert_eq!(expr.source, annotation.position);
        assert_eq!(annotation.owner, *source.definition_root());
        assert!(matches!(expr.scope, LocalSourceScope::Definition(_)));
        assert!(matches!(&annotation.ty.value,
            source_annotation::SourceAnnotationValue::Variable(name) if name.as_ref() == "'a"));
        let child = source.expression(inner).unwrap();
        assert!(matches!(&child.form, LocalSourceForm::Integer(text) if text.as_ref() == "1"));
        assert_eq!(child.range, 11..12);
        assert_ne!(expr.source, child.source);
        assert_ne!(expr.occurrence, child.occurrence);
        assert!(source.bindings().is_empty());
        assert_eq!(source.expressions().len(), 2);
        assert_eq!(source.retained_arena_bytes(),
            source.expressions.capacity() * std::mem::size_of::<LocalSourceExpr>() + 3);
    }

    #[test]
    fn chained_ascriptions_retain_distinct_tails_in_source_order() {
        let module = lower("my value = (1 as 'a) as 'b").unwrap();
        let source = module.local_sources.values().next().unwrap();
        let outer = source.expression(source.body()).unwrap();
        let LocalSourceForm::Ascription { inner, annotation } = &outer.form else {
            panic!("expected outer expression ascription");
        };
        assert_eq!(outer.range, 21..26);
        assert_eq!(annotation.position, outer.source);
        assert!(matches!(&annotation.ty.value,
            source_annotation::SourceAnnotationValue::Variable(name) if name.as_ref() == "'b"));
        let group = source.expression(inner).unwrap();
        let LocalSourceForm::Group { inner } = &group.form else {
            panic!("expected preserved parenthesized child");
        };
        let first = source.expression(inner).unwrap();
        let LocalSourceForm::Ascription { inner, annotation } = &first.form else {
            panic!("expected first expression ascription");
        };
        assert_eq!(first.range, 14..19);
        assert_eq!(annotation.position, first.source);
        assert!(matches!(&annotation.ty.value,
            source_annotation::SourceAnnotationValue::Variable(name) if name.as_ref() == "'a"));
        let child = source.expression(inner).unwrap();
        assert!(matches!(child.form, LocalSourceForm::Integer(_)));
        assert_eq!(child.range, 12..13);
        assert_ne!(outer.source, first.source);
        assert_ne!(outer.occurrence, first.occurrence);
        assert_ne!(first.source, child.source);
        assert_ne!(first.occurrence, child.occurrence);
        assert_ne!(outer.occurrence, child.occurrence);
        assert!(source.bindings().is_empty());
        assert_eq!(source.expressions().len(), 4);
        assert_eq!(source.retained_arena_bytes(),
            source.expressions.capacity() * std::mem::size_of::<LocalSourceExpr>() + 5);
    }

    #[test]
    fn ascriptions_reject_malformed_and_recovery_types() {
        for text in ["my value = 1 as", "my value = 1 as (", "my value = 1 as (int,)",
            "my value = 1 as int as"] {
            assert!(matches!(lower(text), Err(HirAvailabilityError::StructuralProjection)), "{text}");
        }
    }

    #[test]
    fn empty_call_uses_distinct_unit_and_apply_occurrences_at_call_tail() {
        let module = lower("my invoke f = f()").unwrap();
        let source = module.local_sources.values().next().unwrap();
        let apply = source
            .expressions()
            .iter()
            .find(|expr| matches!(expr.form, LocalSourceForm::Apply { .. }))
            .unwrap();
        let LocalSourceForm::Apply {
            argument,
            source_form,
            ..
        } = &apply.form
        else {
            unreachable!();
        };
        assert_eq!(*source_form, SyntaxKind::CallTail);
        let unit = source.expression(argument).unwrap();
        assert!(matches!(unit.form, LocalSourceForm::Unit));
        assert_eq!(unit.source, apply.source);
        assert_eq!(unit.range, apply.range);
        assert_eq!(unit.range, 15..17);
        assert_ne!(unit.occurrence, apply.occurrence);
        assert!(matches!(unit.scope, LocalSourceScope::Parameter(_)));
    }

    #[test]
    fn empty_parentheses_form_unit_without_admitting_tuple_or_recovery() {
        let module = lower("my value = ()").unwrap();
        let source = module.local_sources.values().next().unwrap();
        let unit = source.expression(source.body()).unwrap();
        assert!(matches!(unit.form, LocalSourceForm::Unit));
        assert_eq!(unit.range, 11..13);
        assert!(matches!(unit.scope, LocalSourceScope::Definition(_)));
        for text in ["my value = (1,)", "my value = (1, 2)", "my value = ("] {
            assert!(matches!(
                lower(text),
                Err(HirAvailabilityError::StructuralProjection)
            ));
        }
    }
}
