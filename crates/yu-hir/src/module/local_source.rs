//! Nonshipping source formation owned by the HIR lowering event.
use super::*;
use yu_syntax::SourceNodeKey;

/// Retained source availability for one already admitted ordinary binding.
#[derive(Clone, Debug)]
pub enum SourceCarrierOutcome {
    Supported(LocalSource),
    Unsupported(SourceCarrierFailure),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceCarrierFailureReason {
    Recovery,
    UnsupportedForm,
    SupportedDepth,
}
#[derive(Clone, Debug)]
pub struct SourceCarrierFailure {
    pub root: SourceRootId,
    pub source: SourceNodeKey,
    pub reason: SourceCarrierFailureReason,
}
/// Source refusal is distinct from corruption or exhaustion at the builder owner.
#[derive(Debug)]
pub(crate) enum FormationError {
    Unsupported(SourceCarrierFailureReason),
    Availability(HirAvailabilityError),
}
impl From<HirAvailabilityError> for FormationError {
    fn from(error: HirAvailabilityError) -> Self { Self::Availability(error) }
}
// The existing opt-in API retains its established refusal result.
impl From<FormationError> for HirAvailabilityError {
    fn from(error: FormationError) -> Self {
        match error {
            FormationError::Unsupported(_) => Self::StructuralProjection,
            FormationError::Availability(error) => error,
        }
    }
}
fn unsupported() -> FormationError {
    FormationError::Unsupported(SourceCarrierFailureReason::UnsupportedForm)
}


#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct LocalSourceIndex {
    owner: SourceRootId,
    ordinal: u32,
}

impl LocalSourceIndex {
    pub fn source_root(&self) -> &SourceRootId { &self.owner }
    pub fn definition_root(&self) -> Option<&DefinitionRootId> { self.owner.definition_root() }
    pub fn ordinal(&self) -> u32 {
        self.ordinal
    }
}
#[derive(Clone, Debug)]
pub struct LocalSource {
    owner: SourceRootId,
    body: LocalSourceIndex,
    expressions: Vec<LocalSourceExpr>,
    /// Inputs supplied by an enclosing source member invocation. These remain
    /// source formals and are not rewritten into synthetic Lambda expressions.
    root_parameters: Vec<LocalSourceParameter>,
    /// Original member target and raw annotation, retained with its body.
    member_header: Option<super::SourceMemberHeader>,
    bindings: Vec<LocalSourceBinding>,
    where_clauses: Vec<LocalSourceWhereClause>,
    annotation: Option<source_annotation::SourceAnnotation>,
    named_groups: Vec<LocalSourceNamedGroup>,
}
/// A declaration-owned where clause retained as exact source evidence.
/// This carrier does not resolve the type or role names in the clause.
#[derive(Clone, Debug)]
pub struct LocalSourceWhereClause {
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub text: Box<str>,
    pub subject: LocalSourceWhereType,
    pub role: LocalSourceWhereType,
}
/// One parse-owned type expression within a declaration prerequisite.
#[derive(Clone, Debug)]
pub struct LocalSourceWhereType {
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub text: Box<str>,
}
/// A named header's construction identity within one retained source.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct LocalSourceNamedGroupId {
    owner: SourceRootId,
    ordinal: u32,
}
impl LocalSourceNamedGroupId {
    pub fn source_root(&self) -> &SourceRootId { &self.owner }
    pub fn definition_root(&self) -> Option<&DefinitionRootId> { self.owner.definition_root() }
    pub fn ordinal(&self) -> u32 { self.ordinal }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LocalSourceNamedGroupOwner {
    Definition(DefinitionRootId),
    Member(super::SourceMemberRootId),
    Local(HirLocalId),
}
#[derive(Clone, Debug)]
pub struct LocalSourceNamedFormal {
    pub parameter: HirParameterId,
    pub lambda: LocalSourceIndex,
}
/// Facts retained directly from one named header, without receiver/frame policy.
#[derive(Clone, Debug)]
pub struct LocalSourceNamedGroup {
    pub id: LocalSourceNamedGroupId,
    pub owner: LocalSourceNamedGroupOwner,
    pub source: SourceNodeKey,
    pub enclosing: Option<LocalSourceNamedGroupId>,
    pub formals: Vec<LocalSourceNamedFormal>,
    pub terminal_lambda: LocalSourceIndex,
    pub terminal_body: LocalSourceIndex,
}
impl LocalSource {
    pub fn root_parameters(&self) -> &[LocalSourceParameter] { &self.root_parameters }
    pub fn member_header(&self) -> Option<&super::SourceMemberHeader> { self.member_header.as_ref() }

    fn order_occurrences(
        &mut self, plan: &RootPlan, counters: &LoweringCounters,
        artifact: &Arc<HirArtifactToken>, next: &mut u32,
        identity: &mut crate::source_identity::HirSourceIdentity,
    ) -> Result<(), HirAvailabilityError> {
        let mut by_source: HashMap<SourceNodeKey, Vec<usize>> = HashMap::new();
        by_source.try_reserve(self.expressions.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        for (index, expression) in self.expressions.iter().enumerate() {
            let indices = by_source.entry(expression.source.clone()).or_default();
            indices.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            indices.push(index);
        }
        identity.occurrences.clear();
        // The candidate worklist visits application tails before their heads.
        // Assign published IDs only now, by the source owner's child order.
        for node in plan.node.descendants() {
            let source = counters.source_nodes.get(&node)
                .ok_or(HirAvailabilityError::StructuralProjection)?;
            if let Some(indices) = by_source.remove(source) {
                for index in indices {
                    let occurrence = if index == self.body.ordinal as usize {
                        match &self.owner {
                            SourceRootId::Expression(root) => root.occurrence().clone(),
                            SourceRootId::Definition(_) | SourceRootId::Member(_) => next_occurrence(artifact, next)?,
                        }
                    } else { next_occurrence(artifact, next)? };
                    identity.record_occurrence(occurrence.clone(), source.clone());
                    self.expressions[index].occurrence = occurrence;
                }
            }
        }
        if !by_source.is_empty() { return Err(HirAvailabilityError::StructuralProjection); }
        Ok(())
    }
    pub fn named_groups(&self) -> &[LocalSourceNamedGroup] { &self.named_groups }
    pub fn named_group(&self, id: &LocalSourceNamedGroupId) -> Option<&LocalSourceNamedGroup> {
        (id.owner == self.owner).then(|| self.named_groups.get(id.ordinal as usize)).flatten()
    }
    pub fn source_root(&self) -> &SourceRootId { &self.owner }
    pub fn definition_root(&self) -> Option<&DefinitionRootId> { self.owner.definition_root() }
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
    pub fn where_clauses(&self) -> &[LocalSourceWhereClause] {
        &self.where_clauses
    }
    /// Reserved arena/vector storage and retained spelling bytes; shared source
    /// and artifact payloads and allocator overhead are excluded.
    pub fn retained_arena_bytes(&self) -> usize {
        self.annotation
            .as_ref()
            .map_or(0, |annotation| annotation.retained_arena_bytes())
            + self.expressions.capacity() * std::mem::size_of::<LocalSourceExpr>()
            + self.root_parameters.capacity() * std::mem::size_of::<LocalSourceParameter>()
            + self.root_parameters.iter().map(|parameter| {
                parameter.spelling.len()
                    + parameter.annotation.as_ref().map_or(0, |annotation| annotation.retained_arena_bytes())
            }).sum::<usize>()
            + self.member_header.as_ref().map_or(0, |header| {
                header.receiver.spelling.len() + header.method.spelling.len()
                    + header.annotation.as_ref().map_or(0, |annotation| annotation.text.len())
            })
            + self.bindings.capacity() * std::mem::size_of::<LocalSourceBinding>()
            + self.where_clauses.capacity() * std::mem::size_of::<LocalSourceWhereClause>()
            + self.where_clauses.iter().map(|clause| clause.text.len()).sum::<usize>()
            + self.where_clauses.iter().map(|clause| {
                clause.subject.text.len() + clause.role.text.len()
                    + 2 * std::mem::size_of::<LocalSourceWhereType>()
            }).sum::<usize>()
            + self.named_groups.capacity() * std::mem::size_of::<LocalSourceNamedGroup>()
            + self.named_groups.iter().map(|group| group.formals.capacity() * std::mem::size_of::<LocalSourceNamedFormal>()).sum::<usize>()
            + self
                .expressions
                .iter()
                .map(|expr| match &expr.form {
                    LocalSourceForm::Integer(text) | LocalSourceForm::String(text) => text.len(),
                    LocalSourceForm::Primitive { operation: source_annotation::PinnedPrimitiveOp::Unsupported(name) } => name.len(),
                    LocalSourceForm::Catch { arms, .. } => {
                        arms.capacity() * std::mem::size_of::<LocalSourceCatchArm>()
                            + arms.iter().map(|arm| match &arm.pattern {
                                LocalSourceCatchPattern::Value(pattern) => catch_pattern_bytes(pattern),
                                LocalSourceCatchPattern::Operation { payloads, continuation, .. } => {
                                    payloads.capacity() * std::mem::size_of::<LocalSourceCatchPayloadPattern>()
                                        + payloads.iter().map(|payload| match payload {
                                            LocalSourceCatchPayloadPattern::Value(pattern) => catch_pattern_bytes(pattern),
                                            LocalSourceCatchPayloadPattern::Unit { .. } => 0,
                                        }).sum::<usize>() + catch_pattern_bytes(continuation)
                                }
                            }).sum::<usize>()
                    }
                    LocalSourceForm::Case { arms, .. } => {
                        arms.capacity() * std::mem::size_of::<LocalSourceCaseArm>()
                            + arms.iter().map(|arm| case_pattern_bytes(&arm.pattern)).sum::<usize>()
                    }
                    LocalSourceForm::If { arms, .. } => {
                        arms.capacity() * std::mem::size_of::<(LocalSourceIndex, LocalSourceIndex)>()
                    }
                    LocalSourceForm::Sequence { items } => {
                        items.capacity() * std::mem::size_of::<LocalSourceIndex>()
                    }
                    LocalSourceForm::Tuple { elements } => {
                        elements.capacity() * std::mem::size_of::<LocalSourceIndex>()
                    }
                    LocalSourceForm::FieldTail { member, .. } => member.len(),
                    LocalSourceForm::OperatorApplication { operator, .. } => operator.spelling().len()
                        + std::mem::size_of::<SourceNodeKey>()
                        + std::mem::size_of::<crate::HirOperator>(),
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
                    LocalSourceForm::StatementBlock { statements, .. } => {
                        statements.capacity() * std::mem::size_of::<LocalSourceStatement>()
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
    pub named_group: Option<LocalSourceNamedGroupId>,
    pub occurrence: HirOccurrenceId,
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub scope: LocalSourceScope,
    pub form: LocalSourceForm,
}
/// One original statement in a block prefix, in source order. Expression
/// statements are not represented as invented local bindings.
#[derive(Clone, Debug)]
pub enum LocalSourceStatement {
    Expression(LocalSourceIndex),
    Binding(u32),
}
#[derive(Clone, Debug)]
pub enum LocalSourceForm {
    Unit,
    Primitive { operation: source_annotation::PinnedPrimitiveOp },
    Operation {
        resolution: source_annotation::SourceOperationResolution,
    },
    Integer(Box<str>),
    Boolean(bool),
    String(Box<str>),
    Catch {
        scrutinee: LocalSourceIndex,
        arms: Vec<LocalSourceCatchArm>,
    },
    Case {
        scrutinee: LocalSourceIndex,
        arms: Vec<LocalSourceCaseArm>,
    },
    If {
        arms: Vec<(LocalSourceIndex, LocalSourceIndex)>,
        else_branch: Option<LocalSourceIndex>,
    },
    Sequence { items: Vec<LocalSourceIndex> },
    StatementBlock {
        statements: Vec<LocalSourceStatement>,
        final_expression: LocalSourceIndex,
    },
    /// An ordered product formed from multiple direct parenthesized items or
    /// from one item followed by a trailing comma. Group and Unit remain
    /// separate source forms.
    Tuple { elements: Vec<LocalSourceIndex> },
    /// A parse-owned member tail. `receiver` is the full preceding expression;
    /// method or field meaning remains for a later resolver to determine.
    FieldTail {
        receiver: LocalSourceIndex,
        member: Box<str>,
        member_range: Range<usize>,
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
    /// One exact parser-associated operator use; operands retain their own source
    /// occurrences and the operator keeps its selected declaration receipt.
    OperatorApplication {
        operator_source: SourceNodeKey,
        operator: crate::HirOperator,
        left: LocalSourceIndex,
        right: Option<LocalSourceIndex>,
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
    Imported(super::source_exports::SourceExportId),
    Parameter(HirParameterId),
    CatchBinder(LocalSourceCatchBinderId),
    CaseBinder(LocalSourceCatchBinderId),
    Local(HirLocalId),
    Unresolved,
    Ambiguous,
}
#[derive(Clone, Debug)]
pub enum LocalSourceScope {
    Definition(DefinitionRootId),
    ModuleExpression(ExpressionRootId),
    SourceMember(super::SourceMemberRootId),
    Expression(LocalSourceIndex),
    Parameter(HirParameterId),
    LocalInitializer(HirLocalId),
    CatchArm { catch: LocalSourceIndex, arm: SourceNodeKey },
}
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct LocalSourceCatchBinderId {
    owner: SourceRootId,
    arm_source: SourceNodeKey,
    ordinal: u32,
}
impl LocalSourceCatchBinderId {
    pub fn source_root(&self) -> &SourceRootId { &self.owner }
    pub fn definition_root(&self) -> Option<&DefinitionRootId> { self.owner.definition_root() }
    pub fn owner(&self) -> Option<&DefinitionRootId> { self.owner.definition_root() }
    pub fn arm_source(&self) -> &SourceNodeKey { &self.arm_source }
    pub fn ordinal(&self) -> u32 { self.ordinal }
}
#[derive(Clone, Debug)]
pub struct LocalSourceCatchBinder {
    pub id: LocalSourceCatchBinderId,
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub spelling: Box<str>,
}
#[derive(Clone, Debug)]
pub enum LocalSourceCatchValuePattern {
    Binder(LocalSourceCatchBinder),
    Wildcard,
}
#[derive(Clone, Debug)]
pub enum LocalSourceCatchPayloadPattern {
    Value(LocalSourceCatchValuePattern),
    /// Empty call syntax only; this does not impose Unit payload matching.
    Unit { source: SourceNodeKey, range: Range<usize> },
}
#[derive(Clone, Debug)]
pub enum LocalSourceCatchPattern {
    Value(LocalSourceCatchValuePattern),
    Operation {
        resolution: source_annotation::SourceOperationResolution,
        operation_source: SourceNodeKey,
        payloads: Vec<LocalSourceCatchPayloadPattern>,
        continuation: LocalSourceCatchValuePattern,
    },
}
#[derive(Clone, Debug)]
pub struct LocalSourceCatchArm {
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub pattern: LocalSourceCatchPattern,
    pub body: LocalSourceIndex,
}

/// A source-owned case arm in the initial literal-pattern carrier.
#[derive(Clone, Debug)]
pub struct LocalSourceCaseArm {
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub pattern: LocalSourceCasePattern,
    pub body: LocalSourceIndex,
}

#[derive(Clone, Debug)]
pub enum LocalSourceCasePattern {
    Integer(LocalSourceIndex),
    Binder(LocalSourceCatchBinder),
    Wildcard,
    Tuple {
        source: SourceNodeKey,
        range: Range<usize>,
        elements: Vec<LocalSourceCasePatternElement>,
    },
}

#[derive(Clone, Debug)]
pub enum LocalSourceCasePatternElement {
    Binder(LocalSourceCatchBinder),
    Wildcard,
}

fn case_pattern_bytes(pattern: &LocalSourceCasePattern) -> usize {
    match pattern {
        LocalSourceCasePattern::Binder(binder) => binder.spelling.len(),
        LocalSourceCasePattern::Tuple { elements, .. } => elements.iter().map(|element| match element {
            LocalSourceCasePatternElement::Binder(binder) => binder.spelling.len(),
            LocalSourceCasePatternElement::Wildcard => 0,
        }).sum(),
        LocalSourceCasePattern::Integer(_) | LocalSourceCasePattern::Wildcard => 0,
    }
}

#[derive(Clone, Debug)]
pub struct LocalSourceParameter {
    pub id: HirParameterId,
    pub source: SourceNodeKey,
    pub range: Range<usize>,
    pub spelling: Box<str>,
    pub scope: LocalSourceScope,
    pub annotation: Option<source_annotation::SourceAnnotation>,
    /// The original empty pattern introduces an anonymous Unit-matching slot.
    /// Its spelling is empty and never enters lexical name lookup.
    pub unit_pattern: bool,
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

fn catch_pattern_bytes(pattern: &LocalSourceCatchValuePattern) -> usize {
    match pattern {
        LocalSourceCatchValuePattern::Binder(binder) => binder.spelling.len(),
        LocalSourceCatchValuePattern::Wildcard => 0,
    }
}

pub(super) enum SimpleBodyProjection {
    #[cfg(any(feature = "shadow", test))]
    Atom(crate::OwnedAtom),
    Unsupported,
}

enum Work {
    Expression(SyntaxNode, LocalSourceIndex, LocalSourceScope, Option<LocalSourceNamedGroupId>),
    Initializer(u32, SyntaxNode, Option<LocalSourceNamedGroupId>),
    Publish(u32, usize),
    Restore(usize),
    CatchArm(SyntaxNode, LocalSourceIndex, LocalSourceScope, Vec<LocalSourceCatchBinder>, Option<LocalSourceNamedGroupId>),
    CaseArm(SyntaxNode, LocalSourceIndex, LocalSourceScope, Vec<LocalSourceCatchBinder>, Option<LocalSourceNamedGroupId>),
}
struct LexicalEntry {
    spelling: Box<str>,
    resolution: LocalSourceResolution,
    previous: Option<usize>,
}
struct Builder<'a> {
    owner: &'a SourceRootId,
    namespace: &'a super::ModuleNamespace,
    counters: &'a mut LoweringCounters,
    artifact: &'a Arc<HirArtifactToken>,
    next_occurrence: &'a mut u32,
    next_parameter: u32,
    expressions: Vec<Option<LocalSourceExpr>>,
    named_groups: Vec<LocalSourceNamedGroup>,
    bindings: Vec<LocalSourceBinding>,
    where_clauses: Vec<LocalSourceWhereClause>,
    lexical: Vec<LexicalEntry>,
    latest: HashMap<Box<str>, usize>,
    work: Vec<Work>,
}
fn invalid() -> FormationError {
    FormationError::Availability(HirAvailabilityError::StructuralProjection)
}
fn push<T>(values: &mut Vec<T>, value: T) -> Result<(), FormationError> {
    values
        .try_reserve(1)
        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    values.push(value);
    Ok(())
}
fn identifier_spelling(node: &SyntaxNode) -> Result<Box<str>, FormationError> {
    let mut tokens = node.children_with_tokens().filter(|element| !matches!(
        element.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment | SyntaxKind::BlockComment,
    ));
    let token = tokens.next().and_then(|element| element.into_token()).ok_or_else(unsupported)?;
    if token.kind() != SyntaxKind::Identifier || tokens.next().is_some() { return Err(unsupported()); }
    Ok(token.text().into())
}
fn integer_spelling(node: &SyntaxNode) -> Result<Box<str>, FormationError> {
    let mut tokens = node.children_with_tokens().filter(|element| !matches!(
        element.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment | SyntaxKind::BlockComment,
    ));
    let token = tokens.next().and_then(|element| element.into_token()).ok_or_else(invalid)?;
    if token.kind() != SyntaxKind::Integer || tokens.next().is_some() { return Err(invalid()); }
    Ok(token.text().into())
}
fn string_spelling(node: &SyntaxNode) -> Result<Box<str>, FormationError> {
    let mut delimiters = node.children_with_tokens().filter_map(|element| element.into_token())
        .filter(|token| matches!(token.kind(), SyntaxKind::StringStart | SyntaxKind::StringEnd));
    let start = delimiters.next().ok_or_else(invalid)?;
    let end = delimiters.next().ok_or_else(invalid)?;
    if start.kind() != SyntaxKind::StringStart || end.kind() != SyntaxKind::StringEnd
        || delimiters.next().is_some() || start.text_range().end() > end.text_range().start()
    {
        return Err(invalid());
    }
    // Literal nodes can own exterior trivia. Delimiter coordinates retain every
    // byte inside the string, including meaningful whitespace and heredoc text.
    let origin = node.text_range().start();
    let start = usize::from(start.text_range().start() - origin);
    let end = usize::from(end.text_range().end() - origin);
    node.text().to_string().get(start..end).map(Box::<str>::from).ok_or_else(invalid)
}
fn collect_associated_range<'a>(
    expression: &'a crate::HirExpr,
    target: &Range<usize>,
    output: &mut Vec<&'a crate::HirExpr>,
) -> Result<(), FormationError> {
    let mut pending = Vec::new();
    push(&mut pending, expression)?;
    while let Some(expression) = pending.pop() {
        if expression.range() == target {
            push(output, expression)?;
        }
        match expression {
            crate::HirExpr::Apply { operands, .. } => {
                for operand in operands.iter() { push(&mut pending, operand)?; }
            }
            crate::HirExpr::Value { children, .. } | crate::HirExpr::Error { children, .. } => {
                for child in children { push(&mut pending, child)?; }
            }
        }
    }
    Ok(())
}
fn only_child(node: &SyntaxNode) -> Result<SyntaxNode, FormationError> {
    let mut children = node.children();
    let child = children.next().ok_or_else(unsupported)?;
    if children.next().is_some() {
        return Err(unsupported());
    }
    Ok(child)
}
pub(crate) fn inline_colon_argument(node: &SyntaxNode) -> Result<SyntaxNode, FormationError> {
    let child = only_child(node)?;
    if child.kind() != SyntaxKind::OperatorChain {
        return Err(unsupported());
    }
    Ok(child)
}
fn body(
    statement: &SyntaxNode,
    admitted_visibility: HirVisibility,
) -> Result<SyntaxNode, FormationError> {
    let mut nodes = Vec::new();
    for node in statement.children() {
        push(&mut nodes, node)?;
    }
    if !matches!(nodes.as_slice(), [header, body] if header.kind() == SyntaxKind::BindingHeader && body.kind() == SyntaxKind::BindingBody)
    {
        return Err(unsupported());
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
    let source_visibility = match header_kinds.next() {
        Some(SyntaxKind::MyKw) => HirVisibility::Private,
        Some(SyntaxKind::OurKw) => HirVisibility::Our,
        Some(SyntaxKind::PubKw) => HirVisibility::Public,
        _ => return Err(unsupported()),
    };
    if source_visibility != admitted_visibility
        || header_kinds.next() != Some(SyntaxKind::Pattern)
        || header_kinds.next() != Some(SyntaxKind::Equals)
        || header_kinds.next().is_some()
    {
        return Err(unsupported());
    }
    let child = only_child(&nodes[1])?;
    if !matches!(
        child.kind(),
        SyntaxKind::OperatorChain | SyntaxKind::IndentedStatementBlock
    ) {
        return Err(unsupported());
    }
    Ok(child)
}

/// Extracts only the RHS syntax of a source-backed role/implementation member.
/// The member header remains owned by its SourceMemberRootId and is never
/// lowered as a module definition. Signature-only members have no body.
pub(super) fn member_body_expression(
    member: &SyntaxNode,
) -> Result<Option<SyntaxNode>, HirAvailabilityError> {
    if has_recovery(member) { return Err(HirAvailabilityError::StructuralProjection); }
    if member.kind() != SyntaxKind::BindingStatement {
        return Ok(None);
    }
    let children = member.children().collect::<Vec<_>>();
    let body = match children.as_slice() {
        [header] if header.kind() == SyntaxKind::BindingHeader => return Ok(None),
        [header, body] if header.kind() == SyntaxKind::BindingHeader && body.kind() == SyntaxKind::BindingBody => body,
        _ => return Err(HirAvailabilityError::StructuralProjection),
    };
    let mut expressions = body.children();
    let Some(expression) = expressions.next() else {
        return Err(HirAvailabilityError::StructuralProjection);
    };
    if expressions.next().is_some()
        || !matches!(expression.kind(), SyntaxKind::OperatorChain | SyntaxKind::IndentedStatementBlock)
    {
        return Err(HirAvailabilityError::StructuralProjection);
    }
    if has_recovery(&expression) { return Err(HirAvailabilityError::StructuralProjection); }
    Ok(Some(expression))
}

/// Projects the narrow dotted Binding target used by Y2 role and impl methods.
/// All returned names and annotations remain tied to original CST nodes.
pub(super) fn member_header(
    member: &SyntaxNode,
    counters: &LoweringCounters,
) -> Result<Option<SourceMemberHeader>, HirAvailabilityError> {
    if member.kind() != SyntaxKind::BindingStatement || has_recovery(member) {
        return Ok(None);
    }
    let mut headers = member.children().filter(|node| node.kind() == SyntaxKind::BindingHeader);
    let Some(header) = headers.next() else { return Err(HirAvailabilityError::StructuralProjection); };
    if headers.next().is_some() { return Err(HirAvailabilityError::StructuralProjection); }
    // Implementation methods can bind their receiver and ordinary arguments
    // in the same header (`our x.add y = ...`). Find the exact dotted field
    // pattern in that header and keep its receiver/method source nodes; the
    // other patterns remain ordinary named formals for the body projection.
    let mut fields = header.descendants().filter(|node| node.kind() == SyntaxKind::PatternFieldTail);
    let Some(field) = fields.next() else { return Ok(None); };
    if fields.next().is_some() || has_recovery(&field) { return Ok(None); }
    let Some(pattern) = field.parent().filter(|node| node.kind() == SyntaxKind::Pattern) else {
        return Ok(None);
    };
    let field_start = crate::range_of(&field).start;
    let mut receivers = pattern.descendants().filter(|node|
        node.kind() == SyntaxKind::IdentifierPattern && crate::range_of(node).end <= field_start
    );
    let Some(receiver) = receivers.next() else { return Ok(None); };
    if receivers.next().is_some() || has_recovery(&receiver) { return Ok(None); }
    let mut annotations = pattern.children().filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation);
    let annotation = annotations.next();
    if annotations.next().is_some() { return Ok(None); }
    let receiver_spelling = identifier_spelling(&receiver)
        .map_err(|_| HirAvailabilityError::StructuralProjection)?;
    let field_end = crate::range_of(&field).end;
    let mut parameters = Vec::new();
    for tail in pattern.children().filter(|node|
        node.kind() == SyntaxKind::PatternMlApplicationTail
            && crate::range_of(node).start >= field_end
    ) {
        if has_recovery(&tail) { return Ok(None); }
        let mut argument_patterns = tail.children().filter(|node| node.kind() == SyntaxKind::Pattern);
        let Some(argument) = argument_patterns.next() else { return Ok(None); };
        if argument_patterns.next().is_some() { return Ok(None); }
        let mut significant = argument.children_with_tokens().filter(|element| !matches!(
            element.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline
                | SyntaxKind::LineComment | SyntaxKind::BlockComment,
        ));
        let Some(argument_node) = significant.next().and_then(|element| element.into_node())
            .filter(|node| node.kind() == SyntaxKind::IdentifierPattern)
        else { return Ok(None); };
        if significant.next().is_some() || has_recovery(&argument_node) { return Ok(None); }
        let spelling = identifier_spelling(&argument_node)
            .map_err(|_| HirAvailabilityError::StructuralProjection)?;
        let token = argument_node.children_with_tokens().filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::Identifier)
            .ok_or(HirAvailabilityError::StructuralProjection)?;
        parameters.try_reserve(1).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        parameters.push(SourceMemberIdentifier {
            source: counters.source_nodes.get(&argument_node).cloned()
                .ok_or(HirAvailabilityError::StructuralProjection)?,
            range: crate::range_of_token(&token),
            spelling,
        });
    }
    let mut field_tokens = field.children_with_tokens().filter(|element| !matches!(
        element.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment | SyntaxKind::BlockComment,
    ));
    let dot = field_tokens.next().and_then(|element| element.into_token());
    let method = field_tokens.next().and_then(|element| element.into_token());
    if dot.as_ref().is_none_or(|token| token.kind() != SyntaxKind::Dot)
        || method.as_ref().is_none_or(|token| token.kind() != SyntaxKind::Identifier)
        || field_tokens.next().is_some()
    { return Ok(None); }
    let receiver_token = receiver.children_with_tokens().filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::Identifier)
        .ok_or(HirAvailabilityError::StructuralProjection)?;
    let receiver_source = counters.source_nodes.get(&receiver).cloned().ok_or(HirAvailabilityError::StructuralProjection)?;
    let method_source = counters.source_nodes.get(&field).cloned().ok_or(HirAvailabilityError::StructuralProjection)?;
    let annotation = if let Some(annotation) = annotation {
        let mut types = annotation.children().filter(|node| node.kind() == SyntaxKind::TypeExpression);
        let ty = types.next().ok_or(HirAvailabilityError::StructuralProjection)?;
        if types.next().is_some() || has_recovery(&ty) { return Ok(None); }
        Some(SourceMemberType {
            source: counters.source_nodes.get(&ty).cloned().ok_or(HirAvailabilityError::StructuralProjection)?,
            range: crate::range_of(&ty),
            text: ty.text().to_string().into_boxed_str(),
        })
    } else { None };
    Ok(Some(SourceMemberHeader {
        receiver: SourceMemberIdentifier {
            source: receiver_source,
            range: crate::range_of_token(&receiver_token),
            spelling: receiver_spelling,
        },
        method: SourceMemberIdentifier {
            source: method_source,
            range: crate::range_of_token(method.as_ref().unwrap()),
            spelling: method.unwrap().text().into(),
        },
        parameters,
        annotation,
    }))
}

pub(super) fn form_ordinary(
    plan: &RootPlan,
    owner: &SourceRootId,
    parameters: &[HirParameter],
    namespace: &super::ModuleNamespace,
    counters: &mut LoweringCounters,
    artifact: &Arc<HirArtifactToken>,
    next_occurrence: &mut u32,
) -> Result<SourceCarrierOutcome, HirAvailabilityError> {
    form_ordinary_with_root_parameters(
        plan, owner, parameters, &[], None, namespace, counters, artifact, next_occurrence,
    )
}

pub(super) fn form_member(
    plan: &RootPlan,
    owner: &SourceRootId,
    header: &super::SourceMemberHeader,
    namespace: &super::ModuleNamespace,
    counters: &mut LoweringCounters,
    artifact: &Arc<HirArtifactToken>,
    next_occurrence: &mut u32,
) -> Result<SourceCarrierOutcome, HirAvailabilityError> {
    let root = owner.member_root().ok_or(HirAvailabilityError::InconsistentIdentity)?;
    let receiver = LocalSourceParameter {
        id: super::HirParameterId::new(owner.clone(), 0),
        source: header.receiver.source.clone(),
        range: header.receiver.range.clone(),
        spelling: header.receiver.spelling.clone(),
        scope: LocalSourceScope::SourceMember(root.clone()),
        annotation: None,
        unit_pattern: false,
    };
    let mut parameters = Vec::new();
    parameters.try_reserve_exact(header.parameters.len())
        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    for (index, parameter) in header.parameters.iter().enumerate() {
        let ordinal = u32::try_from(index.checked_add(1)
            .ok_or(HirAvailabilityError::IdentityExhausted)?)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        parameters.push(HirParameter {
            id: super::HirParameterId::new(owner.clone(), ordinal),
            name: super::HirName {
                spelling: parameter.spelling.to_string(),
                range: parameter.range.clone(),
            },
            range: parameter.range.clone(),
            unit_pattern: false,
        });
    }
    form_ordinary_with_root_parameters(
        plan, owner, &parameters, &[receiver], Some(header), namespace, counters, artifact, next_occurrence,
    )
}

fn form_ordinary_with_root_parameters(
    plan: &RootPlan,
    owner: &SourceRootId,
    parameters: &[HirParameter],
    root_parameters: &[LocalSourceParameter],
    member_header: Option<&super::SourceMemberHeader>,
    namespace: &super::ModuleNamespace,
    counters: &mut LoweringCounters,
    artifact: &Arc<HirArtifactToken>,
    next_occurrence: &mut u32,
) -> Result<SourceCarrierOutcome, HirAvailabilityError> {
    let mut identity = counters.source_identity.take()
        .ok_or(HirAvailabilityError::StructuralProjection)?;
    let source = counters.source_nodes.get(&plan.node).cloned()
        .ok_or(HirAvailabilityError::StructuralProjection)?;
    counters.source_identity = Some(identity.empty_stage());
    let mut staged_next = *next_occurrence;
    // Only local candidate headers use this grammar switch. All ordinary
    // admission, lowering, errors and occurrence allocation have completed.
    let previous_local_source = counters.local_source;
    counters.local_source = true;
    let result = form(
        plan, owner, parameters, root_parameters, member_header, namespace, counters, artifact, &mut staged_next,
    );
    counters.local_source = previous_local_source;
    let mut staged_identity = counters.source_identity.take()
        .ok_or(HirAvailabilityError::StructuralProjection)?;
    let outcome = match result {
        Ok((mut carrier, _)) => {
            staged_next = *next_occurrence;
            carrier.order_occurrences(plan, counters, artifact, &mut staged_next, &mut staged_identity)?;
            if let SourceRootId::Expression(root) = owner {
                if let Some(existing) = identity.occurrences.get(root.occurrence()) {
                    if staged_identity.occurrences.get(root.occurrence()) != Some(existing) {
                        counters.source_identity = Some(identity);
                        return Err(HirAvailabilityError::StructuralProjection);
                    }
                    // This authentic ordinary occurrence already has this exact
                    // source origin; reuse it rather than replacing its mapping.
                    staged_identity.occurrences.remove(root.occurrence());
                }
            }
            let merged = identity.append_stage(staged_identity);
            counters.source_identity = Some(identity);
            merged?;
            *next_occurrence = staged_next;
            return Ok(SourceCarrierOutcome::Supported(carrier));
        }
        Err(FormationError::Unsupported(reason)) => {
            Ok(SourceCarrierOutcome::Unsupported(SourceCarrierFailure {
                root: owner.clone(), source, reason,
            }))
        }
        Err(FormationError::Availability(error)) => Err(error),
    };
    counters.source_identity = Some(identity);
    outcome
}

pub(super) fn form(
    plan: &RootPlan,
    owner: &SourceRootId,
    parameters: &[HirParameter],
    root_parameters: &[LocalSourceParameter],
    member_header: Option<&super::SourceMemberHeader>,
    namespace: &super::ModuleNamespace,
    counters: &mut LoweringCounters,
    artifact: &Arc<HirArtifactToken>,
    next_occurrence: &mut u32,
) -> Result<(LocalSource, SimpleBodyProjection), FormationError> {
    if has_recovery(&plan.node) {
        return Err(FormationError::Unsupported(SourceCarrierFailureReason::Recovery));
    }
    if parameters.len() >= 128 {
        return Err(FormationError::Unsupported(SourceCarrierFailureReason::SupportedDepth));
    }
    let admitted = match &plan.kind {
        RootPlanKind::Binding(admitted) => Some(admitted),
        RootPlanKind::DirectExpression => None,
        RootPlanKind::Import | RootPlanKind::Unsupported(_) => return Err(invalid()),
    };
    let admitted_parameters = admitted.map_or(&[][..], |admitted| admitted.parameters.as_slice());
    let mut builder = Builder {
        owner,
        namespace,
        counters,
        artifact,
        next_occurrence,
        next_parameter: u32::try_from(parameters.len().checked_add(root_parameters.len())
            .ok_or(HirAvailabilityError::IdentityExhausted)?)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?,
        expressions: Vec::new(),
        named_groups: Vec::new(),
        bindings: Vec::new(),
        where_clauses: Vec::new(),
        lexical: Vec::new(),
        latest: HashMap::new(),
        work: Vec::new(),
    };
    for parameter in root_parameters {
        builder.counters.source_identity.as_mut()
            .ok_or(HirAvailabilityError::StructuralProjection)?
            .record_parameter(parameter.id.clone(), parameter.source.clone());
        builder.push_binding(
            parameter.spelling.clone(),
            LocalSourceResolution::Parameter(parameter.id.clone()),
        )?;
    }
    let root = builder.slot()?;
    let mut current = root.clone();
    let mut scope = root_parameters.first()
        .map(|parameter| LocalSourceScope::Parameter(parameter.id.clone()))
        .unwrap_or_else(|| match owner {
        SourceRootId::Definition(root) => LocalSourceScope::Definition(root.clone()),
        SourceRootId::Expression(root) => LocalSourceScope::ModuleExpression(root.clone()),
        SourceRootId::Member(root) => LocalSourceScope::SourceMember(root.clone()),
    });
    let named_group = if parameters.is_empty() { None } else { Some(builder.next_named_group()?) };
    let mut named_formals = Vec::new();
    for (index, parameter) in parameters.iter().enumerate() {
        let (parameter_source, parameter_annotation) = if let Some(admitted) = admitted_parameters.get(index) {
            (admitted.source.clone().ok_or_else(invalid)?, admitted.annotation.as_ref())
        } else if let Some(source_parameter) = member_header.and_then(|header|
            header.parameters.get(index)
        ) {
            (source_parameter.source.clone(), None)
        } else {
            return Err(invalid());
        };
        let parameter = LocalSourceParameter {
            id: parameter.id.clone(),
            source: parameter_source,
            range: parameter.range.clone(),
            spelling: parameter.name.spelling.clone().into_boxed_str(),
            unit_pattern: parameter.unit_pattern,
            scope: scope.clone(),
            annotation: parameter_annotation
                .map(|node| source_annotation::parse_annotation(node, owner, builder.counters))
                .transpose()?,
        };
        if !parameter.unit_pattern {
            builder.push_binding(
                parameter.spelling.clone(),
                LocalSourceResolution::Parameter(parameter.id.clone()),
            )?;
        }
        let next = builder.slot()?;
        push(&mut named_formals, LocalSourceNamedFormal { parameter: parameter.id.clone(), lambda: current.clone() })?;
        builder.set(
            current,
            &plan.node,
            scope,
            named_group.clone(),
            LocalSourceForm::Lambda {
                parameter: parameter.clone(),
                body: next.clone(),
            },
        )?;
        current = next;
        scope = LocalSourceScope::Parameter(parameter.id);
    }
    if let Some(id) = &named_group {
        let group_owner = match owner {
            SourceRootId::Definition(root) => LocalSourceNamedGroupOwner::Definition(root.clone()),
            SourceRootId::Member(root) => LocalSourceNamedGroupOwner::Member(root.clone()),
            SourceRootId::Expression(_) => return Err(invalid()),
        };
        builder.record_named_group(id.clone(), group_owner, &plan.node,
            None, named_formals, current.clone())?;
    }
    let body_chain = if let Some(admitted) = admitted {
        body(&plan.node, admitted.visibility)?
    } else {
        plan.node.clone()
    };
    if body_chain.kind() == SyntaxKind::IndentedStatementBlock {
        for clause in body_chain.children() {
            if clause.kind() != SyntaxKind::WhereClause {
                break;
            }
            if has_recovery(&clause) {
                return Err(FormationError::Unsupported(SourceCarrierFailureReason::Recovery));
            }
            let source = builder
                .counters
                .source_nodes
                .get(&clause)
                .cloned()
                .ok_or_else(invalid)?;
            let mut parts = clause.children_with_tokens().filter(|element| !matches!(
                element.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline
                    | SyntaxKind::LineComment | SyntaxKind::BlockComment,
            ));
            if parts.next().is_none_or(|part| part.kind() != SyntaxKind::WhereKw) {
                return Err(unsupported());
            }
            let subject = parts.next().and_then(|part| part.into_node())
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .ok_or_else(unsupported)?;
            if parts.next().is_none_or(|part| part.kind() != SyntaxKind::Colon) {
                return Err(unsupported());
            }
            let role = parts.next().and_then(|part| part.into_node())
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .ok_or_else(unsupported)?;
            if parts.next().is_some() {
                return Err(unsupported());
            }
            let retain_type = |node: &SyntaxNode| -> Result<LocalSourceWhereType, FormationError> {
                Ok(LocalSourceWhereType {
                    source: builder.counters.source_nodes.get(node).cloned().ok_or_else(invalid)?,
                    range: crate::range_of(node),
                    text: node.text().to_string().into_boxed_str(),
                })
            };
            let subject = retain_type(&subject)?;
            let role = retain_type(&role)?;
            push(
                &mut builder.where_clauses,
                LocalSourceWhereClause {
                    source,
                    range: crate::range_of(&clause),
                    text: clause.text().to_string().into_boxed_str(),
                    subject,
                    role,
                },
            )?;
        }
    }
    push(
        &mut builder.work,
        Work::Expression(body_chain.clone(), current, scope, named_group.clone()),
    )?;
    while let Some(work) = builder.work.pop() {
        match work {
            Work::Expression(node, index, scope, named_group) => {
                builder.expression(node, index, scope, named_group)?
            }
            Work::Restore(depth) => builder.restore(depth),
            Work::CatchArm(node, index, scope, binders, named_group) => {
                push(&mut builder.work, Work::Restore(builder.lexical.len()))?;
                for binder in binders {
                    builder.push_binding(binder.spelling, LocalSourceResolution::CatchBinder(binder.id))?;
                }
                push(&mut builder.work, Work::Expression(node, index, scope, named_group.clone()))?;
            }
            Work::CaseArm(node, index, scope, binders, named_group) => {
                push(&mut builder.work, Work::Restore(builder.lexical.len()))?;
                for binder in binders {
                    builder.push_binding(binder.spelling, LocalSourceResolution::CaseBinder(binder.id))?;
                }
                push(&mut builder.work, Work::Expression(node, index, scope, named_group.clone()))?;
            }
            Work::Initializer(binding, node, enclosing_named_group) => {
                let guard = builder.lexical.len();
                let data = &builder.bindings[binding as usize];
                let mut scope = LocalSourceScope::LocalInitializer(data.id.clone());
                let mut index = data.initializer.clone();
                let count = data.parameters.len();
                let group_owner = data.id.clone();
                let named_group = if count == 0 { enclosing_named_group.clone() } else { Some(builder.next_named_group()?) };
                let mut named_formals = Vec::new();
                let self_binding = (count != 0).then(|| (data.spelling.clone(), data.id.clone()));
                // The temporary self identity belongs to the initializer scope;
                // parameters may shadow it, and Publish restores then installs it.
                if let Some((spelling, id)) = self_binding {
                    builder.push_binding(spelling, LocalSourceResolution::Local(id))?;
                }
                push(&mut builder.work, Work::Publish(binding, guard))?;
                for ordinal in 0..count {
                    let parameter = builder.bindings[binding as usize].parameters[ordinal].clone();
                    if !parameter.unit_pattern {
                        builder.push_binding(
                            parameter.spelling.clone(),
                            LocalSourceResolution::Parameter(parameter.id.clone()),
                        )?;
                    }
                    let next = builder.slot()?;
                    push(&mut named_formals, LocalSourceNamedFormal { parameter: parameter.id.clone(), lambda: index.clone() })?;
                    builder.set(
                        index,
                        &node,
                        scope,
                        named_group.clone(),
                        LocalSourceForm::Lambda {
                            parameter: parameter.clone(),
                            body: next.clone(),
                        },
                    )?;
                    index = next;
                    scope = LocalSourceScope::Parameter(parameter.id);
                }
                if count != 0 {
                    builder.record_named_group(named_group.clone().ok_or_else(invalid)?, LocalSourceNamedGroupOwner::Local(group_owner), &node,
                        enclosing_named_group, named_formals, index.clone())?;
                }
                push(
                    &mut builder.work,
                    Work::Expression(body(&node, HirVisibility::Private)?, index, scope, named_group.clone()),
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
    let mut retained_root_parameters = Vec::new();
    retained_root_parameters.try_reserve_exact(root_parameters.len())
        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
    retained_root_parameters.extend(root_parameters.iter().cloned());
    let source = LocalSource {
        owner: owner.clone(),
        body: root,
        expressions,
        root_parameters: retained_root_parameters,
        member_header: member_header.cloned(),
        bindings: builder.bindings,
        where_clauses: builder.where_clauses,
        named_groups: builder.named_groups,
        annotation: if admitted.is_some() { source_annotation::form(&plan.node, owner, counters)? } else { None },
    };
    // Successful formation establishes that this actual root chain has the
    // same simple result without constructing a discarded associated tree.
    #[cfg(any(feature = "shadow", test))]
    let projection = if source.expressions().iter().any(|expr| {
        matches!(expr.form, LocalSourceForm::Boolean(_) | LocalSourceForm::String(_) | LocalSourceForm::If { .. })
    }) {
        SimpleBodyProjection::Unsupported
    } else {
        crate::direct_atom(&body_chain)
            .map_or(SimpleBodyProjection::Unsupported, SimpleBodyProjection::Atom)
    };
    #[cfg(not(any(feature = "shadow", test)))]
    let projection = SimpleBodyProjection::Unsupported;
    Ok((source, projection))
}
impl Builder<'_> {
    fn parameter_id(&mut self) -> Result<HirParameterId, FormationError> {
        let ordinal = self.next_parameter;
        self.next_parameter = ordinal.checked_add(1).ok_or(HirAvailabilityError::IdentityExhausted)?;
        Ok(HirParameterId::new(self.owner.clone(), ordinal))
    }
    fn push_binding(
        &mut self,
        spelling: Box<str>,
        resolution: LocalSourceResolution,
    ) -> Result<(), FormationError> {
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
    fn slot(&mut self) -> Result<LocalSourceIndex, FormationError> {
        let index = u32::try_from(self.expressions.len())
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        push(&mut self.expressions, None)?;
        Ok(LocalSourceIndex {
            owner: self.owner.clone(),
            ordinal: index,
        })
    }
    fn key(&self, node: &SyntaxNode) -> Result<SourceNodeKey, FormationError> {
        self.counters
            .source_nodes
            .get(node)
            .cloned()
            .ok_or_else(invalid)
    }
    fn next_named_group(&self) -> Result<LocalSourceNamedGroupId, FormationError> {
        Ok(LocalSourceNamedGroupId { owner: self.owner.clone(), ordinal: u32::try_from(self.named_groups.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)? })
    }
    fn record_named_group(&mut self, id: LocalSourceNamedGroupId, owner: LocalSourceNamedGroupOwner, node: &SyntaxNode,
        enclosing: Option<LocalSourceNamedGroupId>, formals: Vec<LocalSourceNamedFormal>, terminal_body: LocalSourceIndex,
    ) -> Result<(), FormationError> {
        let terminal_lambda = formals.last().ok_or_else(invalid)?.lambda.clone();
        let source = self.key(node)?;
        push(&mut self.named_groups, LocalSourceNamedGroup { id, owner, source, enclosing, formals, terminal_lambda, terminal_body })
    }
    fn set(
        &mut self,
        index: LocalSourceIndex,
        node: &SyntaxNode,
        scope: LocalSourceScope,
        named_group: Option<LocalSourceNamedGroupId>,
        form: LocalSourceForm,
    ) -> Result<(), FormationError> {
        self.set_at_range(index, node, range_of(node), scope, named_group, form)
    }
    fn set_at_range(
        &mut self,
        index: LocalSourceIndex,
        node: &SyntaxNode,
        range: Range<usize>,
        scope: LocalSourceScope,
        named_group: Option<LocalSourceNamedGroupId>,
        form: LocalSourceForm,
    ) -> Result<(), FormationError> {
        let source = self.key(node)?;
        let occurrence = if index.ordinal == 0 {
            match self.owner {
                SourceRootId::Expression(root) => root.occurrence().clone(),
                SourceRootId::Definition(_) | SourceRootId::Member(_) => next_occurrence(self.artifact, self.next_occurrence)?,
            }
        } else { next_occurrence(self.artifact, self.next_occurrence)? };
        self.counters
            .source_identity
            .as_mut()
            .ok_or_else(invalid)?
            .record_occurrence(occurrence.clone(), source.clone());
        self.expressions[index.ordinal as usize] = Some(LocalSourceExpr {
            occurrence,
            source,
            named_group,
            range,
            scope,
            form,
        });
        Ok(())
    }
    fn associated_operator_chain(
        &mut self,
        chain_node: SyntaxNode,
        associated: Arc<crate::HirExpr>,
        index: LocalSourceIndex,
        scope: LocalSourceScope,
        named_group: Option<LocalSourceNamedGroupId>,
        expected_operator_uses: usize,
    ) -> Result<(), FormationError> {
        let chain_range = range_of(&chain_node);
        let mut associated_nodes = Vec::new();
        collect_associated_range(&associated, &chain_range, &mut associated_nodes)?;
        let [associated_root] = associated_nodes.as_slice() else { return Err(unsupported()); };
        let mut pending = Vec::new();
        push(&mut pending, (*associated_root, index, true))?;
        let mut seen = std::collections::HashSet::<Range<usize>>::new();
        while let Some((expression, index, root)) = pending.pop() {
            match expression {
                crate::HirExpr::Apply { operator, operands, range } => {
                    let (left, right, use_kind) = match (operator.fixity(), operands.as_ref()) {
                        (crate::OperatorFixity::Infix, [left, right]) => (left, Some(right), SyntaxKind::InfixOperatorUse),
                        (crate::OperatorFixity::Prefix, [operand]) => (operand, None, SyntaxKind::PrefixOperatorUse),
                        (crate::OperatorFixity::Suffix, [operand]) => (operand, None, SyntaxKind::SuffixOperatorUse),
                        _ => return Err(unsupported()),
                    };
                    let source_range = operator.range().clone();
                    let mut operator_nodes = chain_node.descendants().filter(|node|
                        node.kind() == use_kind
                            && range_of(node) == source_range
                    );
                    let operator_node = operator_nodes.next().ok_or_else(unsupported)?;
                    if operator_nodes.next().is_some()
                        || self.counters.source_operator_uses.get(&source_range) != Some(operator)
                        || !seen.insert(source_range.clone())
                    {
                        return Err(unsupported());
                    }
                    let operator_source = self.key(&operator_node)?;
                    let left_index = self.slot()?;
                    let right_index = right.map(|_| self.slot()).transpose()?;
                    let source_node = if root { &chain_node } else { &operator_node };
                    let retained_range = if root { range_of(&chain_node) } else { range.clone() };
                    self.set_at_range(
                        index, source_node, retained_range, scope.clone(), named_group.clone(),
                        LocalSourceForm::OperatorApplication {
                            operator_source,
                            operator: operator.clone(),
                            left: left_index.clone(),
                            right: right_index.clone(),
                        },
                    )?;
                    for (operand, child_index) in right.zip(right_index).into_iter().chain(std::iter::once((left, left_index))) {
                        match operand {
                            crate::HirExpr::Apply { .. } => push(&mut pending, (operand, child_index, false))?,
                            crate::HirExpr::Value { .. } => self.associated_value(
                                operand, &chain_node, child_index, scope.clone(), named_group.clone(),
                            )?,
                            crate::HirExpr::Error { .. } => return Err(unsupported()),
                        }
                    }
                }
                crate::HirExpr::Value { .. } | crate::HirExpr::Error { .. } => {
                    return Err(unsupported());
                }
            }
        }
        if expected_operator_uses == 0 || seen.len() != expected_operator_uses {
            return Err(unsupported());
        }
        Ok(())
    }
    fn associated_value(
        &mut self,
        value: &crate::HirExpr,
        container: &SyntaxNode,
        index: LocalSourceIndex,
        scope: LocalSourceScope,
        named_group: Option<LocalSourceNamedGroupId>,
    ) -> Result<(), FormationError> {
        let mut value = value;
        let mut index = index;
        loop {
            let crate::HirExpr::Value { kind, range, children } = value else {
                return Err(unsupported());
            };
            if *kind != SyntaxKind::FieldTail {
                let mut nodes = container.descendants().filter(|node|
                    node.kind() == *kind && range_of(node) == *range
                );
                let node = nodes.next().ok_or_else(unsupported)?;
                if nodes.next().is_some() || node == *container {
                    return Err(unsupported());
                }
                return push(&mut self.work, Work::Expression(node, index, scope, named_group));
            }
            let [receiver] = children.as_slice() else { return Err(unsupported()); };
            let mut tails = container.descendants().filter(|node| {
                node.kind() == SyntaxKind::FieldTail
                    && range_of(node).end == range.end
                    && range_of(node).start >= range.start
            });
            let tail = tails.next().ok_or_else(unsupported)?;
            if tails.next().is_some() || has_recovery(&tail) {
                return Err(unsupported());
            }
            let tokens: Vec<_> = tail.children_with_tokens().filter(|element| !matches!(
                element.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline
                    | SyntaxKind::LineComment | SyntaxKind::BlockComment,
            )).collect();
            let [dot, member] = tokens.as_slice() else { return Err(unsupported()); };
            let dot = dot.as_token().ok_or_else(unsupported)?;
            let member = member.as_token().ok_or_else(unsupported)?;
            if dot.kind() != SyntaxKind::Dot || member.kind() != SyntaxKind::Identifier {
                return Err(unsupported());
            }
            let receiver_index = self.slot()?;
            self.set_at_range(
                index, &tail, range.clone(), scope.clone(), named_group.clone(),
                LocalSourceForm::FieldTail {
                    receiver: receiver_index.clone(),
                    member: member.text().into(),
                    member_range: crate::range_of_token(&member),
                },
            )?;
            value = receiver;
            index = receiver_index;
        }
    }
    fn expression(
        &mut self,
        node: SyntaxNode,
        index: LocalSourceIndex,
        scope: LocalSourceScope,
        named_group: Option<LocalSourceNamedGroupId>,
    ) -> Result<(), FormationError> {
        match node.kind() {
            SyntaxKind::OperatorChain => {
                let mut children = Vec::new();
                for child in node.children() {
                    push(&mut children, child)?;
                }
                let (head, all_tails) = children.split_first().ok_or_else(unsupported)?;
                let operator_uses = children.iter().enumerate()
                    .filter(|(_, node)| matches!(node.kind(), SyntaxKind::InfixOperatorUse | SyntaxKind::PrefixOperatorUse | SyntaxKind::SuffixOperatorUse))
                    .collect::<Vec<_>>();
                if !operator_uses.is_empty() {
                    let source_range = range_of(operator_uses[0].1);
                    let associated = self.counters.source_associated_chains
                        .get(&source_range).cloned().ok_or_else(unsupported)?;
                    self.associated_operator_chain(
                        node, associated, index, scope, named_group, operator_uses.len(),
                    )?;
                    return Ok(());
                }
                let path_tail_count = all_tails
                    .iter()
                    .take_while(|tail| tail.kind() == SyntaxKind::PathTail)
                    .count();
                let path_tails = &all_tails[..path_tail_count];
                let tails = &all_tails[path_tail_count..];
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
                            named_group.clone(),
                            LocalSourceForm::Ascription {
                                inner: inner.clone(),
                                annotation,
                            },
                        )?;
                        current = inner;
                        continue;
                    }
                    if tail.kind() == SyntaxKind::FieldTail {
                        if has_recovery(tail) {
                            return Err(unsupported());
                        }
                        let tokens: Vec<_> = tail
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
                            .collect();
                        let [dot, member] = tokens.as_slice() else {
                            return Err(unsupported());
                        };
                        let dot = dot.as_token().ok_or_else(unsupported)?;
                        let member = member.as_token().ok_or_else(unsupported)?;
                        if dot.kind() != SyntaxKind::Dot
                            || member.kind() != SyntaxKind::Identifier
                        {
                            return Err(unsupported());
                        }
                        let receiver = self.slot()?;
                        self.set(
                            current,
                            tail,
                            scope.clone(),
                            named_group.clone(),
                            LocalSourceForm::FieldTail {
                                receiver: receiver.clone(),
                                member: member.text().into(),
                                member_range: crate::range_of_token(&member),
                            },
                        )?;
                        current = receiver;
                        continue;
                    }
                    if !matches!(
                        tail.kind(),
                        SyntaxKind::MlArgument
                            | SyntaxKind::CallTail
                            | SyntaxKind::ColonApplicationTail
                    ) {
                        return Err(unsupported());
                    }
                    if tail.children_with_tokens().any(|element| {
                        matches!(
                            element.kind(),
                            SyntaxKind::Comma | SyntaxKind::ExpressionDelimitedSeparator
                        )
                    }) {
                        return Err(unsupported());
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
                        named_group.clone(),
                        LocalSourceForm::Apply {
                            callee: callee.clone(),
                            argument: argument.clone(),
                            source_form: tail.kind(),
                        },
                    )?;
                    if let Some(argument_node) = argument_node {
                        push(
                            &mut self.work,
                            Work::Expression(argument_node, argument, scope.clone(), named_group.clone()),
                        )?;
                    } else {
                        self.set(argument, tail, scope.clone(), named_group.clone(), LocalSourceForm::Unit)?;
                    }
                    current = callee;
                }
                if !path_tails.is_empty() {
                    if head.kind() != SyntaxKind::IdentifierExpression {
                        return Err(unsupported());
                    }
                    let mut path = vec![identifier_spelling(head)?];
                    for tail in path_tails {
                        if has_recovery(tail) { return Err(unsupported()); }
                        let tokens = tail.children_with_tokens().filter(|element| !matches!(
                            element.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline
                                | SyntaxKind::LineComment | SyntaxKind::BlockComment,
                        )).collect::<Vec<_>>();
                        let [separator, segment] = tokens.as_slice() else { return Err(unsupported()); };
                        let separator = separator.as_token().ok_or_else(unsupported)?;
                        let segment = segment.as_token().ok_or_else(unsupported)?;
                        if separator.kind() != SyntaxKind::ColonColon || segment.kind() != SyntaxKind::Identifier {
                            return Err(unsupported());
                        }
                        path.push(segment.text().into());
                    }
                    let qualified = path.iter().map(AsRef::as_ref).collect::<Vec<_>>().join("::");
                    #[cfg(any(feature = "shadow", test))]
                    if let Some(super::ModuleNameResolution::ImportedOperation(operation)) = self.namespace.get(&qualified) {
                        self.set(current, &node, scope, named_group.clone(), LocalSourceForm::Operation {
                            resolution: source_annotation::SourceOperationResolution::Resolved(
                                operation.operation.clone(),
                            ),
                        })?;
                        return Ok(());
                    }
                    if let Some(super::ModuleNameResolution::Imported(id)) = self.namespace.get(&qualified) {
                        self.set(current, &node, scope, named_group.clone(), LocalSourceForm::Name {
                            spelling: qualified.into(),
                            resolution: LocalSourceResolution::Imported(id.clone()),
                        })?;
                    } else if path_tails.len() == 1 {
                        let form = match source_annotation::pinned_primitive_op(path[0].as_ref(), &path[1]) {
                            Some(operation) => LocalSourceForm::Primitive { operation },
                            None => LocalSourceForm::Operation {
                                resolution: self.resolve_operation(path[0].as_ref(), path[1].clone()),
                            },
                        };
                        self.set(current, &path_tails[0], scope, named_group.clone(), form)?;
                    } else {
                        // Preserve a valid qualified name when this projection
                        // has no import receipt. Candidate admission still
                        // rejects Unresolved; no module/operation is invented.
                        self.set(current, &node, scope, named_group.clone(), LocalSourceForm::Name {
                            spelling: qualified.into(),
                            resolution: LocalSourceResolution::Unresolved,
                        })?;
                    }
                } else {
                    push(
                        &mut self.work,
                        Work::Expression(head.clone(), current, scope, named_group.clone()),
                    )?;
                }
            }
            SyntaxKind::LambdaExpression => {
                let mut elements = node.children_with_tokens().filter(|element| !matches!(
                    element.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline
                        | SyntaxKind::LineComment | SyntaxKind::BlockComment,
                ));
                let slash = elements.next().and_then(|element| element.into_token()).ok_or_else(unsupported)?;
                let binder = elements.next().and_then(|element| element.into_token()).ok_or_else(unsupported)?;
                let arrow = elements.next().and_then(|element| element.into_token()).ok_or_else(unsupported)?;
                let body_node = elements.next().and_then(|element| element.into_node()).ok_or_else(unsupported)?;
                if slash.kind() != SyntaxKind::Backslash || binder.kind() != SyntaxKind::Identifier
                    || arrow.kind() != SyntaxKind::Arrow || body_node.kind() != SyntaxKind::OperatorChain
                    || elements.next().is_some()
                {
                    return Err(unsupported());
                }
                let id = self.parameter_id()?;
                let source = self.key(&node)?;
                let range = crate::range_of_token(&binder);
                self.counters.source_identity.as_mut().ok_or_else(invalid)?
                    .record_inline_parameter(id.clone(), source.clone(), range.clone());
                let parameter = LocalSourceParameter {
                    id: id.clone(), source, range, spelling: binder.text().into(),
                    scope: scope.clone(), annotation: None,
                    unit_pattern: false,
                };
                let body = self.slot()?;
                push(&mut self.work, Work::Restore(self.lexical.len()))?;
                self.push_binding(parameter.spelling.clone(), LocalSourceResolution::Parameter(id.clone()))?;
                push(&mut self.work, Work::Expression(body_node, body.clone(), LocalSourceScope::Parameter(id), named_group.clone()))?;
                self.set(index, &node, scope, named_group, LocalSourceForm::Lambda { parameter, body })?;
            }
            SyntaxKind::IdentifierExpression => {
                let spelling = identifier_spelling(&node)?;
                if !self.latest.contains_key(spelling.as_ref()) {
                    let boolean = match spelling.as_ref() {
                        "true" => Some(true),
                        "false" => Some(false),
                        _ => None,
                    };
                    if let Some(value) = boolean {
                        self.set(index, &node, scope, named_group.clone(), LocalSourceForm::Boolean(value))?;
                        return Ok(());
                    }
                }
                let resolution = self
                    .latest
                    .get(spelling.as_ref())
                    .map(|&index| self.lexical[index].resolution.clone())
                    .unwrap_or_else(|| match self.namespace.get(spelling.as_ref()) {
                        Some(super::ModuleNameResolution::Local(id)) => {
                            LocalSourceResolution::ModuleDef(id.clone())
                        }
                        Some(super::ModuleNameResolution::Imported(id)) => {
                            LocalSourceResolution::Imported(id.clone())
                        }
                        #[cfg(any(feature = "shadow", test))]
                        Some(super::ModuleNameResolution::ImportedOperation(_)) => LocalSourceResolution::Unresolved,
                        Some(super::ModuleNameResolution::Ambiguous) => LocalSourceResolution::Ambiguous,
                        None => LocalSourceResolution::Unresolved,
                    });
                self.set(
                    index,
                    &node,
                    scope,
                    named_group.clone(),
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
                named_group.clone(),
                LocalSourceForm::Integer(integer_spelling(&node)?),
            )?,
            SyntaxKind::StringLiteral => {
                if node.descendants().any(|child| child.kind() == SyntaxKind::StringInterpolation) {
                    return Err(unsupported());
                }
                self.set(index, &node, scope, named_group.clone(), LocalSourceForm::String(string_spelling(&node)?))?;
            }
            SyntaxKind::CatchExpression => self.catch(node, index, scope, named_group.clone())?,
            SyntaxKind::CaseExpression => self.case(node, index, scope, named_group.clone())?,
            SyntaxKind::IfExpression => self.conditional(node, index, scope, named_group.clone())?,
            SyntaxKind::ParenthesizedExpression => {
                let mut children = Vec::new();
                let mut has_comma = false;
                for element in node.children_with_tokens() {
                    match element.kind() {
                        SyntaxKind::Comma => has_comma = true,
                        SyntaxKind::Whitespace
                        | SyntaxKind::Newline
                        | SyntaxKind::LineComment
                        | SyntaxKind::BlockComment
                        | SyntaxKind::LParen
                        | SyntaxKind::RParen => {}
                        SyntaxKind::ExpressionDelimitedSeparator => return Err(unsupported()),
                        _ => {
                            let Some(child) = element.into_node() else {
                                return Err(unsupported());
                            };
                            push(&mut children, child)?;
                        }
                    }
                }
                if children.is_empty() {
                    self.set(
                        index,
                        &node,
                        scope,
                        named_group.clone(),
                        LocalSourceForm::Unit,
                    )?;
                    return Ok(());
                }
                if children.len() == 1 && !has_comma {
                    let child = children.pop().ok_or_else(invalid)?;
                    let inner = self.slot()?;
                    self.set(
                        index,
                        &node,
                        scope.clone(),
                        named_group.clone(),
                        LocalSourceForm::Group {
                            inner: inner.clone(),
                        },
                    )?;
                    push(
                        &mut self.work,
                        Work::Expression(child, inner, scope, named_group.clone()),
                    )?;
                } else {
                    let mut elements = Vec::new();
                    elements
                        .try_reserve_exact(children.len())
                        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                    let mut slots = Vec::new();
                    slots
                        .try_reserve_exact(children.len())
                        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                    for _ in 0..children.len() {
                        let slot = self.slot()?;
                        elements.push(slot.clone());
                        slots.push(slot);
                    }
                    self.set(
                        index,
                        &node,
                        scope.clone(),
                        named_group.clone(),
                        LocalSourceForm::Tuple { elements },
                    )?;
                    for (child, slot) in children.into_iter().zip(slots).rev() {
                        push(
                            &mut self.work,
                            Work::Expression(child, slot, scope.clone(), named_group.clone()),
                        )?;
                    }
                }
            }
            SyntaxKind::BracedStatementBlockExpression | SyntaxKind::IndentedStatementBlock => self.block(node, index, scope, named_group.clone())?,
            _ => return Err(unsupported()),
        }
        Ok(())
    }
    fn resolve_operation(&self, family: &str, member: Box<str>) -> source_annotation::SourceOperationResolution {
        use source_annotation::SourceOperationResolution;
        match self.counters.effect_namespace.get(family) {
            None => SourceOperationResolution::Unresolved,
            Some(families) if families.len() != 1 => SourceOperationResolution::Ambiguous,
            Some(families) => match self.counters.operation_namespace.get(&(families[0].clone(), member)) {
                None => SourceOperationResolution::Unresolved,
                Some(members) if members.len() != 1 => SourceOperationResolution::Ambiguous,
                Some(members) if members[0].visibility == HirVisibility::Private => SourceOperationResolution::Private,
                Some(members) => SourceOperationResolution::Resolved(members[0].clone()),
            },
        }
    }
    fn catch_value_pattern(
        &self, pattern: &SyntaxNode, arm_source: &SourceNodeKey, ordinal: u32,
        binders: &mut Vec<LocalSourceCatchBinder>,
    ) -> Result<LocalSourceCatchValuePattern, FormationError> {
        if pattern.kind() != SyntaxKind::Pattern { return Err(unsupported()); }
        let pattern = only_child(pattern)?;
        if pattern.kind() != SyntaxKind::IdentifierPattern { return Err(unsupported()); }
        let spelling = identifier_spelling(&pattern)?;
        if spelling.as_ref() == "_" { return Ok(LocalSourceCatchValuePattern::Wildcard); }
        let binder = LocalSourceCatchBinder {
            id: LocalSourceCatchBinderId { owner: self.owner.clone(), arm_source: arm_source.clone(), ordinal },
            source: self.key(&pattern)?, range: range_of(&pattern), spelling,
        };
        push(binders, binder.clone())?;
        Ok(LocalSourceCatchValuePattern::Binder(binder))
    }
    fn catch(
        &mut self,
        node: SyntaxNode,
        index: LocalSourceIndex,
        scope: LocalSourceScope,
        named_group: Option<LocalSourceNamedGroupId>,
    ) -> Result<(), FormationError> {
        let parts: Vec<_> = node.children().collect();
        let [scrutinee, block] = parts.as_slice() else { return Err(unsupported()); };
        if scrutinee.kind() != SyntaxKind::CatchScrutinee || block.kind() != SyntaxKind::CatchBlock {
            return Err(unsupported());
        }
        let scrutinee_node = only_child(scrutinee)?;
        let scrutinee_index = self.slot()?;
        let mut arms = Vec::new();
        let mut children = Vec::new();
        for arm in block.children() {
            if arm.kind() == SyntaxKind::CatchArmSeparator { continue; }
            if arm.kind() != SyntaxKind::CatchArm { return Err(unsupported()); }
            let mut parts = Vec::new();
            for child in arm.children() { push(&mut parts, child)?; }
            let (body, patterns) = parts.split_last().ok_or_else(unsupported)?;
            if !matches!(body.kind(), SyntaxKind::OperatorChain | SyntaxKind::IndentedStatementBlock) { return Err(unsupported()); }
            let arm_source = self.key(&arm)?;
            let mut binders = Vec::new();
            let pattern = match patterns {
                [value] => LocalSourceCatchPattern::Value(self.catch_value_pattern(value, &arm_source, 0, &mut binders)?),
                [operation, continuation] => {
                    if operation.kind() != SyntaxKind::Pattern { return Err(unsupported()); }
                    let mut operation_parts = Vec::new();
                    for child in operation.children() { push(&mut operation_parts, child)?; }
                    let [head, path, call] = operation_parts.as_slice() else { return Err(unsupported()); };
                    if head.kind() != SyntaxKind::IdentifierPattern || path.kind() != SyntaxKind::PatternPathTail || call.kind() != SyntaxKind::PatternCallTail { return Err(unsupported()); }
                    let family = identifier_spelling(head)?;
                    let mut path_tokens = path.children_with_tokens().filter(|element| !matches!(element.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment | SyntaxKind::BlockComment));
                    if path_tokens.next().map(|token| token.kind()) != Some(SyntaxKind::ColonColon) { return Err(unsupported()); }
                    let member = path_tokens.next().and_then(|element| element.into_token()).ok_or_else(unsupported)?;
                    if member.kind() != SyntaxKind::Identifier || path_tokens.next().is_some() { return Err(unsupported()); }
                    let resolution = self.resolve_operation(family.as_ref(), member.text().into());
                    let mut payloads = Vec::new();
                    let mut payload_nodes = call.children();
                    match (payload_nodes.next(), payload_nodes.next()) {
                        (None, None) => push(&mut payloads, LocalSourceCatchPayloadPattern::Unit { source: self.key(call)?, range: range_of(call) })?,
                        (Some(payload), None) => push(&mut payloads, LocalSourceCatchPayloadPattern::Value(self.catch_value_pattern(&payload, &arm_source, 0, &mut binders)?))?,
                        _ => return Err(unsupported()),
                    }
                    let continuation = self.catch_value_pattern(continuation, &arm_source, 1, &mut binders)?;
                    LocalSourceCatchPattern::Operation { resolution, operation_source: self.key(operation)?, payloads, continuation }
                }
                _ => return Err(unsupported()),
            };
            let body_index = self.slot()?;
            push(&mut arms, LocalSourceCatchArm { source: arm_source.clone(), range: range_of(&arm), pattern, body: body_index.clone() })?;
            push(&mut children, (body.clone(), body_index, LocalSourceScope::CatchArm { catch: index.clone(), arm: arm_source }, binders))?;

        }
        if arms.is_empty() { return Err(unsupported()); }
        self.set(index, &node, scope.clone(), named_group.clone(), LocalSourceForm::Catch { scrutinee: scrutinee_index.clone(), arms })?;
        for (body, index, scope, binder) in children.into_iter().rev() {
            push(&mut self.work, Work::CatchArm(body, index, scope, binder, named_group.clone()))?;
        }
        push(&mut self.work, Work::Restore(self.lexical.len()))?;
        push(&mut self.work, Work::Expression(scrutinee_node, scrutinee_index, scope, named_group.clone()))?;
        Ok(())
    }
    fn case_pattern_element(
        &self,
        pattern: &SyntaxNode,
        arm_source: &SourceNodeKey,
        next_binder: &mut u32,
        binders: &mut Vec<LocalSourceCatchBinder>,
    ) -> Result<LocalSourceCasePatternElement, FormationError> {
        if pattern.kind() != SyntaxKind::IdentifierPattern || has_recovery(pattern) {
            return Err(unsupported());
        }
        let spelling = identifier_spelling(pattern)?;
        if spelling.as_ref() == "_" {
            return Ok(LocalSourceCasePatternElement::Wildcard);
        }
        let ordinal = *next_binder;
        *next_binder = ordinal.checked_add(1).ok_or_else(invalid)?;
        let binder = LocalSourceCatchBinder {
            id: LocalSourceCatchBinderId {
                owner: self.owner.clone(),
                arm_source: arm_source.clone(),
                ordinal,
            },
            source: self.key(pattern)?,
            range: range_of(pattern),
            spelling,
        };
        push(binders, binder.clone())?;
        Ok(LocalSourceCasePatternElement::Binder(binder))
    }

    fn case_pattern(
        &mut self,
        pattern: &SyntaxNode,
        arm_source: &SourceNodeKey,
        scope: &LocalSourceScope,
        named_group: Option<LocalSourceNamedGroupId>,
        next_binder: &mut u32,
        binders: &mut Vec<LocalSourceCatchBinder>,
    ) -> Result<LocalSourceCasePattern, FormationError> {
        if has_recovery(pattern) { return Err(unsupported()); }
        match pattern.kind() {
            SyntaxKind::IntegerPattern => {
                let pattern_index = self.slot()?;
                self.set(
                    pattern_index.clone(), pattern, scope.clone(), named_group,
                    LocalSourceForm::Integer(integer_spelling(pattern)?),
                )?;
                Ok(LocalSourceCasePattern::Integer(pattern_index))
            }
            SyntaxKind::IdentifierPattern => {
                let spelling = identifier_spelling(pattern)?;
                if spelling.as_ref() == "_" {
                    return Ok(LocalSourceCasePattern::Wildcard);
                }
                let ordinal = *next_binder;
                *next_binder = ordinal.checked_add(1).ok_or_else(invalid)?;
                let binder = LocalSourceCatchBinder {
                    id: LocalSourceCatchBinderId {
                        owner: self.owner.clone(), arm_source: arm_source.clone(), ordinal,
                    },
                    source: self.key(pattern)?, range: range_of(pattern), spelling,
                };
                push(binders, binder.clone())?;
                Ok(LocalSourceCasePattern::Binder(binder))
            }
            SyntaxKind::ParenthesizedPattern => {
                let mut children = Vec::new();
                let mut has_comma = false;
                for element in pattern.children_with_tokens() {
                    match element.kind() {
                        SyntaxKind::Comma => has_comma = true,
                        SyntaxKind::Whitespace | SyntaxKind::Newline
                        | SyntaxKind::LineComment | SyntaxKind::BlockComment
                        | SyntaxKind::LParen | SyntaxKind::RParen => {}
                        SyntaxKind::Pattern => {
                            let Some(child) = element.into_node() else { return Err(unsupported()); };
                            push(&mut children, only_child(&child)?)?;
                        }
                        _ => return Err(unsupported()),
                    }
                }
                if children.is_empty() { return Err(unsupported()); }
                if !has_comma {
                    if children.len() != 1 { return Err(unsupported()); }
                    return self.case_pattern(&children[0], arm_source, scope, named_group, next_binder, binders);
                }
                let mut elements = Vec::new();
                elements.try_reserve_exact(children.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                let mut binder_names = std::collections::HashSet::<Box<str>>::new();
                binder_names.try_reserve(children.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                for child in &children {
                    let element = self.case_pattern_element(child, arm_source, next_binder, binders)?;
                    if let LocalSourceCasePatternElement::Binder(binder) = &element
                        && !binder_names.insert(binder.spelling.clone())
                    {
                        return Err(unsupported());
                    }
                    elements.push(element);
                }
                Ok(LocalSourceCasePattern::Tuple {
                    source: self.key(pattern)?, range: range_of(pattern), elements,
                })
            }
            _ => Err(unsupported()),
        }
    }

    fn case(
        &mut self,
        node: SyntaxNode,
        index: LocalSourceIndex,
        scope: LocalSourceScope,
        named_group: Option<LocalSourceNamedGroupId>,
    ) -> Result<(), FormationError> {
        let parts: Vec<_> = node.children().collect();
        let [scrutinee, block] = parts.as_slice() else { return Err(unsupported()); };
        if scrutinee.kind() != SyntaxKind::CaseScrutinee || block.kind() != SyntaxKind::CaseBlock {
            return Err(unsupported());
        }
        let scrutinee_node = only_child(scrutinee)?;
        let scrutinee_index = self.slot()?;
        let mut arms = Vec::new();
        let mut children = Vec::new();
        for arm in block.children() {
            if arm.kind() == SyntaxKind::CaseArmSeparator { continue; }
            if arm.kind() != SyntaxKind::CaseArm { return Err(unsupported()); }
            let arm_parts: Vec<_> = arm.children().collect();
            let (body, patterns) = arm_parts.split_last().ok_or_else(unsupported)?;
            if !matches!(body.kind(), SyntaxKind::OperatorChain | SyntaxKind::IndentedStatementBlock)
                || patterns.len() != 1
                || patterns[0].kind() != SyntaxKind::Pattern
            {
                return Err(unsupported());
            }
            let arm_source = self.key(&arm)?;
            let mut binders = Vec::new();
            let pattern = only_child(&patterns[0])?;
            let mut next_binder = 0;
            let pattern = self.case_pattern(
                &pattern, &arm_source, &scope, named_group.clone(), &mut next_binder, &mut binders,
            )?;
            let body_index = self.slot()?;
            push(&mut arms, LocalSourceCaseArm {
                source: arm_source.clone(),
                range: range_of(&arm),
                pattern,
                body: body_index.clone(),
            })?;
            push(&mut children, (body.clone(), body_index, binders))?;
        }
        if arms.is_empty() { return Err(unsupported()); }
        self.set(index.clone(), &node, scope.clone(), named_group.clone(), LocalSourceForm::Case {
            scrutinee: scrutinee_index.clone(),
            arms,
        })?;
        let case_index = index.clone();
        let depth = self.lexical.len();
        for (body, body_index, binders) in children.into_iter().rev() {
            push(&mut self.work, Work::CaseArm(
                body,
                body_index,
                LocalSourceScope::Expression(case_index.clone()),
                binders,
                named_group.clone(),
            ))?;
        }
        push(&mut self.work, Work::Restore(depth))?;
        push(&mut self.work, Work::Expression(scrutinee_node, scrutinee_index, scope, named_group.clone()))?;
        Ok(())
    }
    fn conditional(
        &mut self,
        node: SyntaxNode,
        index: LocalSourceIndex,
        scope: LocalSourceScope,
        named_group: Option<LocalSourceNamedGroupId>,
    ) -> Result<(), FormationError> {
        let conditional_scope = LocalSourceScope::Expression(index.clone());
        let mut arms = Vec::new();
        let mut children = Vec::new();
        let mut else_branch = None;
        for arm in node.children() {
            match arm.kind() {
                SyntaxKind::IfArm if else_branch.is_none() => {
                    let parts: Vec<_> = arm.children().collect();
                    let [condition, body] = parts.as_slice() else { return Err(unsupported()); };
                    if condition.kind() != SyntaxKind::Condition
                        || !matches!(body.kind(), SyntaxKind::OperatorChain | SyntaxKind::IndentedStatementBlock | SyntaxKind::BracedStatementBlockExpression)
                    {
                        return Err(unsupported());
                    }
                    let condition_node = only_child(condition)?;
                    if condition_node.kind() != SyntaxKind::OperatorChain { return Err(unsupported()); }
                    let condition_index = self.slot()?;
                    let body_index = self.slot()?;
                    push(&mut arms, (condition_index.clone(), body_index.clone()))?;
                    push(&mut children, (condition_node, condition_index))?;
                    push(&mut children, (body.clone(), body_index))?;
                }
                SyntaxKind::ElseArm if !arms.is_empty() && else_branch.is_none() => {
                    let body = only_child(&arm)?;
                    if !matches!(body.kind(), SyntaxKind::OperatorChain | SyntaxKind::IndentedStatementBlock | SyntaxKind::BracedStatementBlockExpression) {
                        return Err(unsupported());
                    }
                    let body_index = self.slot()?;
                    else_branch = Some(body_index.clone());
                    push(&mut children, (body, body_index))?;
                }
                _ => return Err(unsupported()),
            }
        }
        if arms.is_empty() { return Err(unsupported()); }
        self.set(index, &node, scope, named_group.clone(), LocalSourceForm::If { arms, else_branch })?;
        let depth = self.lexical.len();
        // Every condition and body starts in the enclosing lexical environment.
        for (child, child_index) in children.into_iter().rev() {
            push(&mut self.work, Work::Restore(depth))?;
            if child.kind() == SyntaxKind::BracedStatementBlockExpression
                && child.children().filter(|node| node.kind() == SyntaxKind::Statement)
                    .all(|statement| statement.children().next().is_some_and(|node| node.kind() == SyntaxKind::OperatorChain)) {
                self.sequence(child, child_index, conditional_scope.clone(), named_group.clone())?;
            } else {
                push(&mut self.work, Work::Expression(child, child_index, conditional_scope.clone(), named_group.clone()))?;
            }
        }
        Ok(())
    }
    fn sequence(
        &mut self,
        node: SyntaxNode,
        index: LocalSourceIndex,
        scope: LocalSourceScope,
        named_group: Option<LocalSourceNamedGroupId>,
    ) -> Result<(), FormationError> {
        let mut statements = Vec::new();
        let mut expect_statement = true;
        for child in node.children() {
            if expect_statement && child.kind() == SyntaxKind::Statement {
                let expression = only_child(&child)?;
                if expression.kind() != SyntaxKind::OperatorChain { return Err(unsupported()); }
                push(&mut statements, expression)?;
            } else if !expect_statement && child.kind() == SyntaxKind::BlockStatementSeparator {
                if child.children().next().is_some() { return Err(unsupported()); }
            } else {
                return Err(unsupported());
            }
            expect_statement = !expect_statement;
        }
        if statements.is_empty() { return Err(unsupported()); }
        let mut items = Vec::new();
        items.try_reserve_exact(statements.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        for _ in &statements { push(&mut items, self.slot()?)?; }
        let mut retained_items = Vec::new();
        retained_items.try_reserve_exact(items.len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        retained_items.extend(items.iter().cloned());
        self.set(index.clone(), &node, scope, named_group.clone(), LocalSourceForm::Sequence { items: retained_items })?;
        let sequence_scope = LocalSourceScope::Expression(index);
        let depth = self.lexical.len();
        for (child, child_index) in statements.into_iter().zip(items).rev() {
            push(&mut self.work, Work::Restore(depth))?;
            push(&mut self.work, Work::Expression(child, child_index, sequence_scope.clone(), named_group.clone()))?;
        }
        Ok(())
    }
    fn block(
        &mut self,
        node: SyntaxNode,
        index: LocalSourceIndex,
        scope: LocalSourceScope,
        named_group: Option<LocalSourceNamedGroupId>,
    ) -> Result<(), FormationError> {
        let mut statements = Vec::new();
        let mut expect_statement = true;
        let mut seen_statement = false;
        for child in node.children() {
            if child.kind() == SyntaxKind::WhereClause {
                if seen_statement {
                    return Err(unsupported());
                }
                let source = self.key(&child)?;
                if !self
                    .where_clauses
                    .iter()
                    .any(|clause| clause.source == source)
                {
                    return Err(unsupported());
                }
                // A where clause is a preamble child, not one side of the
                // statement/separator alternation emitted for the body.
                continue;
            } else if expect_statement && child.kind() == SyntaxKind::Statement {
                seen_statement = true;
                push(&mut statements, only_child(&child)?)?;
            } else if !expect_statement && child.kind() == SyntaxKind::BlockStatementSeparator {
                if child.children().next().is_some() {
                    return Err(unsupported());
                }
            } else {
                return Err(unsupported());
            }
            expect_statement = !expect_statement;
        }
        let final_node = statements.pop().ok_or_else(unsupported)?;
        if final_node.kind() != SyntaxKind::OperatorChain {
            return Err(unsupported());
        }
        let block_scope = LocalSourceScope::Expression(index.clone());
        let final_expression = self.slot()?;
        let mut bindings = Vec::new();
        let mut prefix_work = Vec::new();
        let mut ordered = Vec::new();
        let mut has_expression = false;
        for statement in statements {
            if statement.kind() == SyntaxKind::OperatorChain {
                let expression = self.slot()?;
                push(&mut ordered, LocalSourceStatement::Expression(expression.clone()))?;
                push(&mut prefix_work, Work::Expression(statement, expression, block_scope.clone(), named_group.clone()))?;
                has_expression = true;
                continue;
            }
            if statement.kind() != SyntaxKind::BindingStatement {
                return Err(unsupported());
            }
            let annotation = source_annotation::form(&statement, &self.owner, self.counters)?;
            let (visibility, name, parameters) =
                plain_binding_header(&statement, self.counters).ok_or_else(unsupported)?;
            if visibility != HirVisibility::Private {
                return Err(unsupported());
            }
            body(&statement, HirVisibility::Private)?;
            let ordinal = u32::try_from(self.bindings.len())
                .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            let id = HirLocalId {
                owner: self.owner.clone(),
                ordinal,
            };
            let header = statement
                .children()
                .find(|child| child.kind() == SyntaxKind::BindingHeader)
                .ok_or_else(unsupported)?;
            let pattern = only_child(&header)?;
            let binder = pattern.children().next().ok_or_else(unsupported)?;
            let binder_source = self.key(&binder)?;
            self.counters
                .source_identity
                .as_mut()
                .ok_or_else(invalid)?
                .record_local(id.clone(), binder_source.clone());
            let mut retained_parameters = Vec::new();
            let mut parameter_scope = LocalSourceScope::LocalInitializer(id.clone());
            for parameter in parameters {
                let parameter_id = self.parameter_id()?;
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
                        unit_pattern: parameter.unit_pattern,
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
            push(&mut ordered, LocalSourceStatement::Binding(ordinal))?;
            push(&mut prefix_work, Work::Initializer(ordinal, statement, named_group.clone()))?;
        }
        let form = if has_expression {
            LocalSourceForm::StatementBlock { statements: ordered, final_expression: final_expression.clone() }
        } else {
            LocalSourceForm::Block { bindings, final_expression: final_expression.clone() }
        };
        self.set(
            index,
            &node,
            scope,
            named_group.clone(),
            form,
        )?;
        push(&mut self.work, Work::Restore(self.lexical.len()))?;
        push(
            &mut self.work,
            Work::Expression(final_node, final_expression, block_scope, named_group.clone()),
        )?;
        for work in prefix_work.into_iter().rev() {
            push(&mut self.work, work)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mixed_statements_keep_original_order_binders_and_lexical_lookup() {
        let text = "my outside = 9; my main = { outside; my x = outside; x; my outside = 2; x; outside }";
        let (parsed, _, module) = ordinary_fixture(text);
        let HirItem::Binding(binding) = &module.items()[1] else { panic!("main"); };
        let source = module.local_source(binding.definition_root()).unwrap().unwrap();
        let LocalSourceForm::StatementBlock { statements, final_expression } = &source.expression(source.body()).unwrap().form
            else { panic!("source statement block"); };
        assert_eq!(statements.len(), 5);
        assert_eq!(source.bindings().len(), 2);
        assert!(matches!(statements[1], LocalSourceStatement::Binding(0)));
        assert!(matches!(statements[3], LocalSourceStatement::Binding(1)));
        let mut previous_end = 0;
        for statement in statements {
            match statement {
                LocalSourceStatement::Expression(index) => {
                    let expression = source.expression(index).unwrap();
                    assert!(parsed.owns_source_key(&expression.source));
                    assert!(module.owns_occurrence(&expression.occurrence));
                    assert!(expression.range.start >= previous_end);
                    previous_end = expression.range.end;
                    match &expression.form {
                        LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::ModuleDef(_) } => assert_eq!(spelling.as_ref(), "outside"),
                        LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Local(id) } => {
                            assert_eq!(spelling.as_ref(), "x");
                            assert_eq!(id, &source.bindings()[0].id);
                        }
                        other => panic!("unexpected statement {other:?}"),
                    }
                }
                LocalSourceStatement::Binding(ordinal) => {
                    let binding = &source.bindings()[*ordinal as usize];
                    assert!(parsed.owns_source_key(&binding.binder_source));
                    assert!(binding.range.start >= previous_end);
                    previous_end = binding.range.end;
                }
            }
        }
        assert!(matches!(&source.expression(&source.bindings()[0].initializer).unwrap().form,
            LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(_), .. }));
        assert!(matches!(&source.expression(final_expression).unwrap().form,
            LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &source.bindings()[1].id));
    }

    #[test]
    fn statement_publication_is_sequential_and_branch_scopes_are_disjoint() {
        let module = lower("my main = { x; my x = 1; if true { x; my x = 2; x } else { x; x }; x }").unwrap();
        let HirItem::Binding(binding) = &module.items()[0] else { panic!("main"); };
        let source = module.local_source(binding.definition_root()).unwrap().unwrap();
        assert_eq!(source.bindings().len(), 2);
        let unresolved = source.expressions().iter().filter(|expression| matches!(&expression.form,
            LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Unresolved } if spelling.as_ref() == "x")).count();
        assert_eq!(unresolved, 1, "a future local is not visible before its initializer");
        let LocalSourceForm::StatementBlock { final_expression, .. } = &source.expression(source.body()).unwrap().form else { panic!("block"); };
        assert!(matches!(&source.expression(final_expression).unwrap().form,
            LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &source.bindings()[0].id));
        let nested_reads = source.expressions().iter().filter(|expression| matches!(&expression.form,
            LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &source.bindings()[1].id)).count();
        assert_eq!(nested_reads, 1, "the branch's local is confined to its suffix");
    }

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

    fn ordinary_fixture(text: &str) -> (ParsedFile, HirModule, HirModule) {
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(), Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new("test", "ordinary.yu")));
        let legacy = lower_module_with_counters(identity.clone(), &parsed, SemanticImports::empty(),
            &mut LoweringCounters::default()).unwrap();
        let ordinary = lower_module(identity, &parsed, SemanticImports::empty()).unwrap();
        (parsed, legacy, ordinary)
    }
    fn ordinary_occurrences(module: &HirModule) -> Vec<u32> {
        let mut work = Vec::new();
        for item in module.items() {
            match item {
                HirItem::Binding(binding) => work.push(binding.value()),
                HirItem::Expression(expression) => work.push(expression),
                HirItem::Import { .. } | HirItem::Error { .. } => {}
            }
        }
        let mut ordinals = Vec::new();
        while let Some(expression) = work.pop() {
            ordinals.push(expression.occurrence().ordinal());
            match expression {
                ResolvedExpr::Apply { callee, argument, .. } => { work.push(callee); work.push(argument); }
                ResolvedExpr::Lambda { body, .. } => work.push(body),
                ResolvedExpr::Group { inner, .. } => work.push(inner),
                _ => {}
            }
        }
        ordinals
    }
    #[test]
    fn ordinary_carriers_preserve_existing_hir_and_structural_identities() {
        for text in [
            "my x = 1; my y = x", "my f x = x; my missing = unknown",
            "my x = @; my y = 1", "my bad = (1, 2); my later = 1",
            "my x = later; my later = 1", "my x = 1; my x = 2; my y = x",
            "my f x y = x; my accepted = 1", "my x: int = 1; my accepted = 1",
            "1; my x = 1; x; my y = x", r"my value = \x -> x", "my operation = E::read",
        ] {
            let (_, legacy, ordinary) = ordinary_fixture(text);
            assert_eq!(legacy, ordinary, "{text}");
            assert_eq!(ordinary_occurrences(&legacy), ordinary_occurrences(&ordinary), "{text}");
            let old_bindings: Vec<_> = legacy.items().iter().filter_map(|item|
                if let HirItem::Binding(binding) = item { Some(binding) } else { None }).collect();
            let new_bindings: Vec<_> = ordinary.items().iter().filter_map(|item|
                if let HirItem::Binding(binding) = item { Some(binding) } else { None }).collect();
            let expected_roots: Vec<_> = ordinary.items().iter().filter_map(|item| match item {
                HirItem::Binding(binding) => Some(SourceRootId::Definition(binding.definition_root().clone())),
                HirItem::Expression(expression) => Some(SourceRootId::Expression(ordinary.expression_root(expression.occurrence()).unwrap().unwrap().clone())),
                HirItem::Import { .. } | HirItem::Error { .. } => None,
            }).collect();
            assert_eq!(ordinary.source_carrier_outcomes().iter().map(|(root, _)| root).collect::<Vec<_>>(), expected_roots.iter().collect::<Vec<_>>(), "{text}");
            for (old, new) in old_bindings.iter().zip(new_bindings) {
                assert_eq!(old.definition_root().definition, new.definition_root().definition);
                let (owner, _) = ordinary.source_carrier_outcomes().iter().find(|(root, _)| root.definition_root() == Some(new.definition_root())).unwrap();
                assert_eq!(owner.definition_root(), Some(new.definition_root()));
                assert_eq!(old.parameters().iter().map(|p| p.id().ordinal()).collect::<Vec<_>>(),
                    new.parameters().iter().map(|p| p.id().ordinal()).collect::<Vec<_>>());
            }
        }
    }
    #[test]
    fn ordinary_carrier_reuses_branded_roots_parameters_and_namespace() {
        let (_, _, module) = ordinary_fixture("my f x = x; my use = f");
        let binding = module.items().iter().find_map(|item| match item {
            HirItem::Binding(binding) => Some(binding), _ => None,
        }).expect("say binding");
        let source = module.local_source(binding.definition_root()).unwrap().unwrap();
        assert_eq!(source.definition_root(), Some(binding.definition_root()));
        let LocalSourceForm::Lambda { parameter, body } = &source.expression(source.body()).unwrap().form
            else { panic!("named lambda"); };
        assert_eq!(&parameter.id, binding.parameters()[0].id());
        assert!(module.definition_source_key(binding.definition_root()).unwrap().is_some());
        assert!(matches!(module.parameter_source_origin(&parameter.id).unwrap(),
            Some(crate::HirParameterSourceOrigin::IdentifierPattern(key)) if key == &parameter.source));
        for expression in source.expressions() {
            assert_eq!(module.occurrence_source_key(&expression.occurrence).unwrap(), Some(&expression.source));
        }

        assert!(matches!(&source.expression(body).unwrap().form,
            LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(id), .. } if id == &parameter.id));
        let (_, second) = &module.source_carrier_outcomes()[1];
        let SourceCarrierOutcome::Supported(second) = second else { panic!("supported name"); };
        assert!(matches!(&second.expression(second.body()).unwrap().form,
            LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(id), .. } if id == binding.id()));
        let (_, _, foreign) = ordinary_fixture("my f x = x");
        let HirItem::Binding(foreign) = &foreign.items()[0] else { panic!("binding"); };
        assert!(matches!(module.source_carrier(foreign.definition_root()), Err(HirAvailabilityError::InconsistentIdentity)));
        assert!(matches!(module.local_source(foreign.definition_root()), Err(HirAvailabilityError::InconsistentIdentity)));
    }

    #[test]
    fn declaration_where_preamble_is_retained_without_becoming_an_expression() {
        let text = "my display(value: 'a) =\n    where 'a: Display\n    where 'a: Fold 'item\n    value";
        let module = lower(text).expect("declaration where preamble should form a source carrier");
        let HirItem::Binding(binding) = &module.items()[0] else {
            panic!("binding");
        };
        let source = module
            .local_source(binding.definition_root())
            .unwrap()
            .expect("local source");

        assert_eq!(source.where_clauses().len(), 2);
        assert_eq!(
            source
                .where_clauses()
                .iter()
                .map(|clause| clause.text.as_ref())
                .collect::<Vec<_>>(),
            ["where 'a: Display", "where 'a: Fold 'item"]
        );
        for clause in source.where_clauses() {
            assert_eq!(&text[clause.range.clone()], clause.text.as_ref());
            assert_eq!(&text[clause.subject.range.clone()], clause.subject.text.as_ref());
            assert_eq!(&text[clause.role.range.clone()], clause.role.text.as_ref());
            assert_ne!(clause.source, clause.subject.source);
            assert_ne!(clause.source, clause.role.source);
            assert_ne!(clause.subject.source, clause.role.source);
            assert!(source
                .expressions()
                .iter()
                .all(|expression| expression.source != clause.source));
        }
        assert_eq!(source.where_clauses()[0].subject.text.trim(), "'a");
        assert_eq!(source.where_clauses()[0].role.text.trim(), "Display");
        assert_eq!(source.where_clauses()[1].subject.text.trim(), "'a");
        assert_eq!(source.where_clauses()[1].role.text.trim(), "Fold 'item");
        let LocalSourceForm::Lambda { body, .. } =
            &source.expression(source.body()).unwrap().form
        else {
            panic!("named parameter lambda");
        };
        let LocalSourceForm::Block {
            final_expression, ..
        } = &source.expression(body).unwrap().form
        else {
            panic!("declaration body block");
        };
        assert!(matches!(
            &source.expression(final_expression).unwrap().form,
            LocalSourceForm::Name { spelling, .. } if spelling.as_ref() == "value"
        ));
    }

    #[test]
    fn source_unary_operators_keep_association_arity_and_receipts() {
        let provider: Arc<yu_syntax::SourceText> = Arc::from(
            "pub prefix (-) 8.0.0 = f\npub suffix (!) 8.0.0 = g\npub infix (+) 5.0.0 5.0.1 = h",
        );
        let dependency = yu_syntax::SyntaxDependencySlot::from_index(0).unwrap();
        let environment = yu_syntax::SyntaxEnvironment::from_imported_headers(
            yu_syntax::SyntaxEnvironmentKey::from_fingerprint(19),
            [(dependency, &yu_syntax::scan_header(provider))],
            Arc::from([yu_syntax::SyntaxDependencyProvenance::new(
                Arc::from("operators.yu"), yu_syntax::SourceRevision::from_fingerprint(79),
            )]),
        ).unwrap();
        for (body, counts) in [("-12", [1, 0, 0]), ("12!", [0, 1, 0]),
            ("-12 + 3!", [1, 1, 1]), ("-(-12)", [2, 0, 0])] {
            let text: Arc<yu_syntax::SourceText> = Arc::from(format!("my value = {body}"));
            let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)), Arc::new(environment.clone()));
            assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{body}");
            let identity = ModuleIdentity::source_root(FileId::new(FileKey::new("test", "unary.yu")));
            let module = lower_module(identity, &parsed, SemanticImports::empty()).unwrap();
            let HirItem::Binding(binding) = &module.items()[0] else { panic!("binding"); };
            let Some(SourceCarrierOutcome::Supported(source)) = module.source_carrier(binding.definition_root()).unwrap() else {
                panic!("exact unary association must form: {body}");
            };
            let mut actual = [0; 3];
            for expression in source.expressions() {
                let LocalSourceForm::OperatorApplication { operator_source, operator, left, right } = &expression.form else { continue; };
                assert!(parsed.owns_source_key(operator_source));
                assert!(source.expression(left).is_some());
                assert_eq!(operator.provenance().declaration().origin(), yu_syntax::OperatorOrigin::Imported(dependency));
                let ordinal = match operator.fixity() {
                    crate::OperatorFixity::Prefix => 0,
                    crate::OperatorFixity::Suffix => 1,
                    crate::OperatorFixity::Infix => 2,
                };
                actual[ordinal] += 1;
                assert_eq!(right.is_some(), ordinal == 2);
                if let Some(right) = right { assert!(source.expression(right).is_some()); }
            }
            assert_eq!(actual, counts, "{body}");
        }
    }

    #[test]
    fn pinned_generic_say_header_and_operator_body_form_a_source_carrier() {
        let provider: Arc<yu_syntax::SourceText> = Arc::from("pub infix (+) 5.0.0 5.0.1 = f");
        let dependency = yu_syntax::SyntaxDependencySlot::from_index(0).unwrap();
        let environment = yu_syntax::SyntaxEnvironment::from_imported_headers(
            yu_syntax::SyntaxEnvironmentKey::from_fingerprint(17),
            [(dependency, &yu_syntax::scan_header(provider.clone()))],
            Arc::from([yu_syntax::SyntaxDependencyProvenance::new(
                Arc::from("lib/std/core/ops.yu"),
                yu_syntax::SourceRevision::from_fingerprint(73),
            )]),
        ).unwrap();
        let text = "pub say(value: 'a): () =\n    where 'a: Display\n    out::write: value.show + \"\\n\"";
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(), Arc::new(yu_syntax::scan_header(source)), Arc::new(environment),
        );
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new("test", "pinned-say.yu")));
        let module = lower_module(identity, &parsed, SemanticImports::empty()).unwrap();
        let HirItem::Binding(binding) = &module.items()[0] else { panic!("binding"); };
        let outcome = module.source_carrier(binding.definition_root()).unwrap();
        let Some(SourceCarrierOutcome::Supported(source)) = outcome else {
            panic!("pinned say source form must be retained: {outcome:?}");
        };
        assert_eq!(source.where_clauses().len(), 1);
        assert_eq!(source.where_clauses()[0].subject.text.trim(), "'a");
        assert_eq!(source.where_clauses()[0].role.text.trim(), "Display");
        let operator = source.expressions().iter().find_map(|expression| match &expression.form {
            LocalSourceForm::OperatorApplication { operator_source, operator, .. } => Some((operator_source, operator)),
            _ => None,
        }).expect("operator constructor retained");
        assert!(parsed.owns_source_key(operator.0));
        assert_eq!(operator.1.spelling(), "+");
        assert_eq!(operator.1.fixity(), crate::OperatorFixity::Infix);
        assert_eq!(operator.1.provenance().declaration().origin(), yu_syntax::OperatorOrigin::Imported(dependency));
    }
    #[test]
    fn ordinary_field_tails_preserve_receiver_chain_and_parse_member_identity() {
        let types_sample = "// our and pub bindings appear in the Types pane.\n\nour id x = x\npub answer = id 42\npub name = id \"Yulang\"\npub pair = (answer, name)\n\npair.say\n";
        let module = lower(types_sample).expect("the exact Types source has source carriers");
        let expression = module.items().iter().find_map(|item| match item {
            HirItem::Expression(expression) => Some(expression),
            _ => None,
        }).expect("the sample's final expression is retained");
        let root = module.expression_root(expression.occurrence()).unwrap().unwrap();
        let source = module.local_source_for(&SourceRootId::Expression(root.clone()))
            .unwrap().expect("the exact final expression has a source carrier");
        let field = source.expressions().iter().find_map(|expression| match &expression.form {
            LocalSourceForm::FieldTail { receiver, member, member_range } =>
                Some((receiver, member, member_range, expression)),
            _ => None,
        }).expect("pair.say FieldTail is retained");
        assert_eq!(field.1.as_ref(), "say");
        assert_eq!(&types_sample[field.2.clone()], "say");
        assert_eq!(module.occurrence_source_key(&field.3.occurrence).unwrap(), Some(&field.3.source));
        assert!(matches!(
            &source.expression(field.0).unwrap().form,
            LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::ModuleDef(_) }
                if spelling.as_ref() == "pair"
        ));

        let chain_source = "my chain = base.first.second";
        let chain_module = lower(chain_source).unwrap();
        let HirItem::Binding(binding) = &chain_module.items()[0] else { panic!("binding"); };
        let chain = chain_module.local_source(binding.definition_root()).unwrap().unwrap();
        let LocalSourceForm::FieldTail { receiver: first, member, member_range } =
            &chain.expression(chain.body()).unwrap().form else { panic!("outer field tail"); };
        assert_eq!(member.as_ref(), "second");
        assert_eq!(&chain_source[member_range.clone()], "second");
        let LocalSourceForm::FieldTail { receiver: base, member, member_range } =
            &chain.expression(first).unwrap().form else { panic!("inner field tail"); };
        assert_eq!(member.as_ref(), "first");
        assert_eq!(&chain_source[member_range.clone()], "first");
        assert!(matches!(
            &chain.expression(base).unwrap().form,
            LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Unresolved }
                if spelling.as_ref() == "base"
        ));
    }
    #[test]
    fn root_visibility_carrier_matches_admission_and_keeps_local_bindings_private() {
        for (text, visibility) in [
            ("my private_identity value = value", HirVisibility::Private),
            ("our our_identity value = value", HirVisibility::Our),
            ("pub public_identity value = value", HirVisibility::Public),
        ] {
            let module = lower(text).expect("admitted root visibility should form its carrier");
            let HirItem::Binding(binding) = &module.items()[0] else { panic!("binding"); };
            assert_eq!(binding.visibility(), visibility, "{text}");
            let source = module.local_source(binding.definition_root()).unwrap().unwrap();
            assert_eq!(source.definition_root(), Some(binding.definition_root()));
            assert_eq!(module.definition_source_key(binding.definition_root()).unwrap(), Some(&source.expressions()[0].source));
            assert_eq!(binding.parameters().len(), 1);
            let LocalSourceForm::Lambda { parameter, body } =
                &source.expression(source.body()).unwrap().form
            else { panic!("named lambda"); };
            assert_eq!(&parameter.id, binding.parameters()[0].id());
            assert!(matches!(
                &source.expression(body).unwrap().form,
                LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(id), .. }
                    if id == binding.parameters()[0].id()
            ));
        }

        let private_local = lower("my outer = {my local = 1; local}")
            .expect("private block bindings remain supported");
        let HirItem::Binding(binding) = &private_local.items()[0] else { panic!("binding"); };
        let source = private_local.local_source(binding.definition_root()).unwrap().unwrap();
        assert_eq!(source.bindings().len(), 1);

        for text in [
            "my outer = {our local = 1; local}",
            "my outer = {pub local = 1; local}",
        ] {
            assert!(matches!(lower(text), Err(HirAvailabilityError::StructuralProjection)), "{text}");
        }
    }
    #[test]
    fn ordinary_inline_parameter_provenance_retains_source_key_and_binder_span() {
        let (_, legacy, module) = ordinary_fixture(r"my value = \x -> x");
        assert_eq!(legacy, module);
        let SourceCarrierOutcome::Supported(source) = &module.source_carrier_outcomes()[0].1 else { panic!("supported inline lambda"); };
        let LocalSourceForm::Lambda { parameter, .. } = &source.expression(source.body()).unwrap().form
            else { panic!("inline lambda"); };
        assert!(matches!(module.parameter_source_origin(&parameter.id).unwrap(),
            Some(crate::HirParameterSourceOrigin::InlineLambda { lambda, binder_range })
                if lambda == &parameter.source && binder_range == &parameter.range));
    }
    #[test]
    fn ordinary_unsupported_roots_leave_no_partial_identity_and_later_roots_continue() {
        for text in ["my bad = @; my later = 1", "my bad = {my local x = x; @}; my later = 1"] {
            let (_, legacy, module) = ordinary_fixture(text);
            assert_eq!(legacy, module);
            assert!(matches!(&module.source_carrier_outcomes()[0].1, SourceCarrierOutcome::Unsupported(_)));
            let SourceCarrierOutcome::Supported(later) = &module.source_carrier_outcomes()[1].1 else { panic!("later supported"); };
            assert_eq!(later.expressions().len(), 1);
            assert_eq!(later.expressions()[0].occurrence.ordinal(), 2);
            let identity = module.source_identity.as_ref().unwrap();
            assert!(identity.locals.is_empty());
            assert!(identity.parameters.is_empty());
            assert!(identity.local_parameter_owners.is_empty());
            assert_eq!(identity.maximum_occurrence_ordinal(), Some(2));
        }
    }
    #[test]
    fn ordinary_source_occurrences_follow_actual_source_child_order() {
        let (parsed, _, module) = ordinary_fixture("my f x = {my g y = y; g(x)}");
        let SourceCarrierOutcome::Supported(source) = &module.source_carrier_outcomes()[0].1 else { panic!("supported"); };
        let keys = crate::source_identity::source_keys(&parsed);
        let root = SyntaxNode::new_root(parsed.green().clone());
        let ranks: HashMap<_, _> = root.descendants().enumerate().map(|(i, node)| (keys[&node].clone(), i)).collect();
        let mut expressions: Vec<_> = source.expressions().iter().collect();
        expressions.sort_by_key(|expression| expression.occurrence.ordinal());
        let source_ranks: Vec<_> = expressions.iter().map(|expression| ranks[&expression.source]).collect();
        assert!(source_ranks.windows(2).all(|pair| pair[0] <= pair[1]));
        let maximum = ordinary_occurrences(&module).into_iter().max().unwrap();
        assert!(expressions.iter().all(|expression| expression.occurrence.ordinal() > maximum));
        assert!(expressions.iter().all(|expression| module.owns_occurrence(&expression.occurrence)));
    }
    #[test]
    fn ordinary_internal_source_failure_is_availability_and_discards_staged_identities() {
        let (parsed, _, module) = ordinary_fixture("my f = {my x = 1; x}");
        let HirItem::Binding(binding) = &module.items()[0] else { panic!("binding"); };
        let mut counters = LoweringCounters::default();
        counters.source_nodes = crate::source_identity::source_keys(&parsed);
        counters.source_identity = Some(crate::source_identity::HirSourceIdentity::new(&parsed));
        let root = SyntaxNode::new_root(parsed.green().clone());
        let mut plans = vec![plan_root(root.children().next().unwrap(), 0, module.identity(), &mut counters).unwrap()];
        let namespace = namespace(&mut plans, None).unwrap();
        let missing = root.descendants().find(|node| node.kind() == SyntaxKind::IdentifierExpression).unwrap();
        counters.source_nodes.remove(&missing);
        let mut next = 10;
        assert!(matches!(form_ordinary(&plans[0], &SourceRootId::Definition(binding.definition_root().clone()), binding.parameters(), &namespace,
            &mut counters, &module.artifact, &mut next), Err(HirAvailabilityError::StructuralProjection)));
        assert_eq!(next, 10);
        let identity = counters.source_identity.as_ref().unwrap();
        assert!(identity.occurrences.is_empty());
        assert!(identity.locals.is_empty());
        assert!(identity.parameters.is_empty());
        assert!(identity.local_parameter_owners.is_empty());
        assert!(!counters.local_source);
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
        assert_eq!(&annotation.owner, source.source_root());
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
        for text in ["my value = 1 as", "my value = 1 as (", "my value = 1 as (int,,)",
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
    fn ordered_tuple_case_pattern_retains_component_binders_and_source_owner() {
        let text = "my first value = case value: (left, right) -> left";
        let module = lower(text).expect("ordered tuple case pattern should form a source carrier");
        let source = module.local_sources.values().next().unwrap();
        let LocalSourceForm::Lambda { body, .. } = &source.expression(source.body()).unwrap().form else {
            panic!("the named formal wraps the case in a lambda");
        };
        let case = source.expression(body).unwrap();
        let LocalSourceForm::Case { arms, .. } = &case.form else { panic!("case expression"); };
        let LocalSourceCasePattern::Tuple { source: pattern_source, range, elements } = &arms[0].pattern else {
            panic!("ordered tuple pattern");
        };
        assert_eq!(&text[range.clone()], "(left, right)");
        assert_eq!(module.occurrence_source_key(&case.occurrence).unwrap(), Some(&case.source));
        let [
            LocalSourceCasePatternElement::Binder(left),
            LocalSourceCasePatternElement::Binder(right),
        ] = elements.as_slice() else { panic!("two ordered binders"); };
        assert!(module.source_parsed.as_ref().unwrap().owns_source_key(pattern_source));
        let root = source.source_root();
        assert!(module.owns_tuple_case_pattern_source(root, &case.occurrence, pattern_source, 0).unwrap());
        assert!(!module.owns_tuple_case_pattern_source(root, &case.occurrence, &case.source, 0).unwrap());
        assert_eq!(&text[left.range.clone()], "left");
        assert_eq!(&text[right.range.clone()], "right");
        assert_eq!(left.id.ordinal, 0);
        assert_eq!(right.id.ordinal, 1);
        assert!(source.expressions().iter().any(|expression| matches!(
            &expression.form,
            LocalSourceForm::Name { resolution: LocalSourceResolution::CaseBinder(id), .. } if id == &left.id
        )));

        assert!(lower("my repeated value = case value: (same, same) -> same").is_err(),
            "duplicate tuple binders must fail closed instead of silently shadowing one component");
    }

    #[test]
    fn unit_formals_retain_original_patterns_without_lexical_names() {
        let text = "my f() x () = { my g() = x; g() }";
        let module = lower(text).unwrap();
        let HirItem::Binding(binding) = &module.items()[0] else { panic!("binding"); };
        let source = module.local_source(binding.definition_root()).unwrap().unwrap();
        let formals = source.expressions().iter().filter_map(|expression| match &expression.form {
            LocalSourceForm::Lambda { parameter, .. } => Some(parameter),
            _ => None,
        }).collect::<Vec<_>>();
        assert_eq!(formals.len(), 4);
        let units = formals.iter().filter(|formal| formal.unit_pattern).collect::<Vec<_>>();
        assert_eq!(units.len(), 3);
        assert_eq!(units.iter().map(|p| &p.source).collect::<std::collections::HashSet<_>>().len(), 3);
        for unit in units {
            assert_eq!(&text[unit.range.clone()], "()");
            assert!(unit.spelling.is_empty());
            assert!(unit.annotation.is_none(), "patterns must not forge written annotations");
            assert!(!source.expressions().iter().any(|e| matches!(&e.form,
                LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(id), .. } if id == &unit.id)));
        }
        let named = formals.iter().find(|p| !p.unit_pattern).unwrap();
        assert_eq!(named.spelling.as_ref(), "x");
        assert!(source.expressions().iter().any(|e| matches!(&e.form,
            LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(id), .. } if id == &named.id)));
    }

    #[test]
    fn unit_formals_retain_unresolved_qualified_body_names() {
        let text = "my invoke() = std::control::flow::next()";
        let module = lower(text).unwrap();
        let HirItem::Binding(binding) = &module.items()[0] else { panic!("binding"); };
        let source = module.local_source(binding.definition_root()).unwrap().unwrap();
        let name = source.expressions().iter().find(|expression| matches!(&expression.form,
            LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Unresolved }
                if spelling.as_ref() == "std::control::flow::next")).expect("unresolved original path");
        assert_eq!(&text[name.range.clone()], "std::control::flow::next()");
        assert!(source.expressions().iter().any(|expression|
            matches!(&expression.form, LocalSourceForm::Lambda { parameter, .. } if parameter.unit_pattern)));
    }

    #[test]
    fn empty_parentheses_form_unit_without_admitting_tuple_or_recovery() {
        let module = lower("my value = ()").unwrap();
        let source = module.local_sources.values().next().unwrap();
        let unit = source.expression(source.body()).unwrap();
        assert!(matches!(unit.form, LocalSourceForm::Unit));
        assert_eq!(unit.range, 11..13);
        assert!(matches!(unit.scope, LocalSourceScope::Definition(_)));
        for text in ["my value = (1,, 2)", "my value = (1; 2)", "my value = ("] {
            assert!(matches!(
                lower(text),
                Err(HirAvailabilityError::StructuralProjection)
            ));
        }
    }

    #[test]
    fn parenthesized_tuple_carrier_keeps_real_children_in_source_order() {
        for text in [
            "my value = (1, 2, 3)",
            "my value = (1, 2, 3,)",
            "my value = (1, 2,)",
            "my value = (\n  1\n  2\n)",
        ] {
            let (_, _, module) = ordinary_fixture(text);
            let SourceCarrierOutcome::Supported(source) = &module.source_carrier_outcomes()[0].1
            else {
                panic!("ordinary tuple source should be retained: {text}");
            };
            let tuple = source.expression(source.body()).unwrap();
            assert!(
                matches!(tuple.form, LocalSourceForm::Tuple { .. }),
                "{text}"
            );
            let LocalSourceForm::Tuple { elements } = &tuple.form else {
                unreachable!()
            };
            let values: Vec<_> = elements
                .iter()
                .map(|element| {
                    let expression = source.expression(element).unwrap();
                    let LocalSourceForm::Integer(value) = &expression.form else {
                        panic!("integer child");
                    };
                    (
                        value.as_ref(),
                        expression.range.clone(),
                        expression.occurrence.ordinal(),
                    )
                })
                .collect();
            let expected = match text {
                "my value = (1, 2, 3)" | "my value = (1, 2, 3,)" => {
                    vec!["1", "2", "3"]
                }
                _ => vec!["1", "2"],
            };
            assert_eq!(
                values.iter().map(|value| value.0).collect::<Vec<_>>(),
                expected,
                "{text}"
            );
            assert!(
                values.windows(2).all(|pair| pair[0].1.start < pair[1].1.start),
                "{text}"
            );
            assert!(
                values.windows(2).all(|pair| pair[0].2 < pair[1].2),
                "{text}"
            );
            assert!(
                source.retained_arena_bytes()
                    >= elements.capacity() * std::mem::size_of::<LocalSourceIndex>()
            );
        }
    }

    #[test]
    fn singleton_comma_is_a_one_element_tuple_and_plain_parentheses_remain_group() {
        for (text, tuple_expected) in [("my value = (1,)", true), ("my value = (1)", false)] {
            let (_, _, module) = ordinary_fixture(text);
            let SourceCarrierOutcome::Supported(source) = &module.source_carrier_outcomes()[0].1 else {
                panic!("ordinary parenthesized source should be retained: {text}");
            };
            let expression = source.expression(source.body()).unwrap();
            if tuple_expected {
                let LocalSourceForm::Tuple { elements } = &expression.form else {
                    panic!("singleton tuple");
                };
                assert_eq!(elements.len(), 1);
                assert!(matches!(
                    source.expression(&elements[0]).unwrap().form,
                    LocalSourceForm::Integer(_)
                ));
            } else {
                let LocalSourceForm::Group { inner } = &expression.form else {
                    panic!("group");
                };
                assert!(matches!(
                    source.expression(inner).unwrap().form,
                    LocalSourceForm::Integer(_)
                ));
            }
        }
    }
}
