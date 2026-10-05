//! Opt-in immutable source artifact. Syntax provenance carries no type or role judgment.
use crate::{range_of, range_of_token};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    ops::Range,
    sync::Arc,
};
use yu_syntax::{ParsedFile, SyntaxKind, SyntaxNode, SyntaxToken};

/// Complete caller-selected parse snapshot and its bounded structural projections.
#[derive(Debug)]
pub struct ShadowArtifact {
    identity: Arc<()>,
    parsed: ParsedFile,
    positions: Vec<Position>,
    annotations: Vec<AnnotationOccurrence>,
    skeleton: Result<Skeleton, ShadowError>,
}

pub const MAX_SYNTAX_DEPTH: usize = 128;
pub const MAX_RAW_ELEMENTS: usize = 65_536;

impl ShadowArtifact {
    /// Publishes atomically after iterative structural preflight. Unsupported
    /// lexical/application projection remains an error inside the complete snapshot.
    pub fn from_parsed(parsed: ParsedFile) -> Result<Self, ShadowError> {
        let root = SyntaxNode::new_root(parsed.green().clone());
        preflight(&root)?;
        if !parsed
            .syntax_diagnostics()
            .map_err(|_| ShadowError::MalformedSource)?
            .is_empty()
        {
            return Err(ShadowError::MalformedSource);
        }
        let identity = Arc::new(());
        let mut artifact = Self {
            identity: identity.clone(),
            parsed,
            positions: Vec::new(),
            annotations: Vec::new(),
            skeleton: Err(ShadowError::MalformedSource),
        };
        let positions = artifact.retain(root.clone());
        artifact.skeleton = build_skeleton(
            &artifact.parsed,
            identity,
            root,
            &positions,
            &artifact.positions,
        );
        Ok(artifact)
    }
    pub fn parsed(&self) -> &ParsedFile {
        &self.parsed
    }
    pub fn source(&self) -> &str {
        self.parsed.source()
    }
    pub fn positions(&self) -> &[Position] {
        &self.positions
    }
    pub fn root(&self) -> PositionId {
        self.position_id(0)
    }
    pub fn annotations(&self) -> &[AnnotationOccurrence] {
        &self.annotations
    }
    /// Structural/lexical result only; success makes no semantic judgment.
    pub fn skeleton(&self) -> Result<&Skeleton, &ShadowError> {
        self.skeleton.as_ref()
    }
    pub fn position(&self, id: &PositionId) -> Result<&Position, ShadowError> {
        if !Arc::ptr_eq(&self.identity, &id.0.artifact) {
            return Err(ShadowError::ForeignArtifact);
        }
        self.positions
            .get(id.0.index)
            .ok_or(ShadowError::MissingReference { index: id.0.index })
    }
    fn position_id(&self, index: usize) -> PositionId {
        PositionId(LocalId {
            artifact: self.identity.clone(),
            index,
        })
    }
    fn retain(&mut self, root: SyntaxNode) -> HashMap<SyntaxNode, Option<PositionId>> {
        // CST handles identify occurrences in this exact root, including equal text.
        // This temporary index is dropped once lexical projection is complete.
        let mut nodes = HashMap::new();
        let mut stack = vec![(RawElement::Node(root), None, 0)];
        while let Some((element, parent, ordinal)) = stack.pop() {
            let id = self.position_id(self.positions.len());
            if let Some(node) = element.as_node()
                && matches!(
                    node.kind(),
                    SyntaxKind::IdentifierPattern
                        | SyntaxKind::IdentifierExpression
                        | SyntaxKind::IntegerLiteral
                        | SyntaxKind::ParenthesizedExpression
                        | SyntaxKind::MlArgument
                        | SyntaxKind::CallTail
                        | SyntaxKind::BindingStatement
                        | SyntaxKind::BracedStatementBlockExpression
                )
            {
                // Rowan keys include a green handle and offset. Synthetic zero-width
                // duplicate nodes can share that key: reject ambiguous projection
                // rather than selecting one retained structural occurrence.
                nodes
                    .entry(node.clone())
                    .and_modify(|position| *position = None)
                    .or_insert(Some(id.clone()));
            }
            let range = element.range();
            let children = element
                .as_node()
                .map(|node| raw_children(node))
                .unwrap_or_default();
            self.positions.push(Position {
                kind: element.kind(),
                range,
                is_node: element.as_node().is_some(),
                parent: parent.clone(),
                ordinal,
                children: Vec::new(),
            });
            if let Some(parent) = parent {
                self.positions[parent.0.index].children.push(id.clone());
            }
            if matches!(
                element.kind(),
                SyntaxKind::PatternTypeAnnotation | SyntaxKind::TypeAnnotationTail
            ) {
                self.annotations.push(AnnotationOccurrence {
                    position: id.clone(),
                    correspondence: Correspondence::PendingTypedPortAndProfile,
                });
            }
            for (ordinal, child) in children.into_iter().enumerate().rev() {
                stack.push((child, Some(id.clone()), ordinal));
            }
        }
        nodes
    }
}

fn preflight(root: &SyntaxNode) -> Result<(), ShadowError> {
    let mut stack = vec![(root.clone(), 0)];
    let mut count = 1;
    while let Some((node, depth)) = stack.pop() {
        for child in node.children_with_tokens() {
            if depth + 1 > MAX_SYNTAX_DEPTH {
                return Err(ShadowError::SyntaxDepthLimit);
            }
            count += 1;
            if count > MAX_RAW_ELEMENTS {
                return Err(ShadowError::ElementLimit);
            }
            if let Some(child) = child.as_node() {
                stack.push((child.clone(), depth + 1));
            }
        }
    }
    Ok(())
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PositionId(LocalId);

#[derive(Debug)]
pub struct Position {
    kind: SyntaxKind,
    range: Range<usize>,
    is_node: bool,
    parent: Option<PositionId>,
    ordinal: usize,
    children: Vec<PositionId>,
}
impl Position {
    pub fn kind(&self) -> SyntaxKind {
        self.kind
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
    pub fn is_node(&self) -> bool {
        self.is_node
    }
    pub fn parent(&self) -> Option<&PositionId> {
        self.parent.as_ref()
    }
    /// Counts every raw child, including punctuation and trivia. Syntax only.
    pub fn ordinal(&self) -> usize {
        self.ordinal
    }
    pub fn children(&self) -> &[PositionId] {
        &self.children
    }
}
#[derive(Debug, Eq, PartialEq)]
pub enum Correspondence {
    PendingTypedPortAndProfile,
}
#[derive(Debug)]
pub struct AnnotationOccurrence {
    position: PositionId,
    correspondence: Correspondence,
}
impl AnnotationOccurrence {
    pub fn position(&self) -> &PositionId {
        &self.position
    }
    pub fn correspondence(&self) -> &Correspondence {
        &self.correspondence
    }
}
#[derive(Debug)]
pub struct Skeleton {
    identity: Arc<()>,
    pub(crate) binders: Vec<Binder>,
    pub(crate) expressions: Vec<Expression>,
    pub(crate) uses: Vec<ExprId>,
    use_positions: Vec<PositionId>,
    capture_uses: Vec<CaptureUseIncidence>,
    pub(crate) body: ExprId,
    pub(crate) pending: Vec<PendingPremise>,
}

#[derive(Clone, Debug)]
struct LocalId {
    artifact: Arc<()>,
    index: usize,
}

impl PartialEq for LocalId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.artifact, &other.artifact) && self.index == other.index
    }
}

impl Eq for LocalId {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExprId(LocalId);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinderId(LocalId);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UseId(LocalId);

/// Lexical source incidence only; this is not typed capture transport or receipt.
#[derive(Debug)]
pub struct CaptureUseIncidence {
    lambda: ExprId,
    captured: BinderId,
    occurrence: UseId,
    position: PositionId,
}

impl CaptureUseIncidence {
    pub fn lambda(&self) -> &ExprId {
        &self.lambda
    }
    pub fn captured(&self) -> &BinderId {
        &self.captured
    }
    pub fn occurrence(&self) -> &UseId {
        &self.occurrence
    }
    pub fn position(&self) -> &PositionId {
        &self.position
    }
}

#[derive(Debug)]
pub struct Binder {
    position: PositionId,
    pub(crate) name: String,
    pub(crate) range: Range<usize>,
}

#[derive(Debug)]
pub struct Expression {
    position: PositionId,
    pub(crate) range: Range<usize>,
    pub(crate) form: Form,
}

#[derive(Debug)]
pub enum Form {
    /// Header/body correspondence only; captures are resolved lexical identities.
    /// Neither this node nor its source binding selects a runtime closure policy.
    Lambda {
        binding: BinderId,
        parameter: BinderId,
        body: ExprId,
        captures: Vec<BinderId>,
        correspondence: ClosureCorrespondence,
    },
    /// The selected block's sequential local binding and final expression.
    Bind {
        binder: BinderId,
        value: ExprId,
        body: ExprId,
    },
    IntegerLiteral {
        spelling: String,
    },
    Use {
        binder: BinderId,
        occurrence: UseId,
    },
    Group {
        inner: ExprId,
    },
    Apply {
        source_form: SyntaxKind,
        callee: ExprId,
        argument: ExprId,
    },
}

/// Structural lexical retention does not discharge typed capture transport,
/// provider/receiver realization, or source/semantic adequacy.
#[derive(Debug, Eq, PartialEq)]
pub enum ClosureCorrespondence {
    PendingTypedCaptureProviderReceiverAndSemanticDischarge,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Premise {
    CallableRole,
    FullFunctionMembership,
    CallViewRealization,
}

#[derive(Debug)]
pub struct PendingPremise {
    pub(crate) call: ExprId,
    pub(crate) premise: Premise,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ShadowError {
    MalformedSource,
    SyntaxDepthLimit,
    ElementLimit,
    UnsupportedExpression {
        kind: SyntaxKind,
        range: Range<usize>,
    },
    InvalidRange {
        range: Range<usize>,
    },
    DuplicateBinder {
        range: Range<usize>,
    },
    UnboundName {
        range: Range<usize>,
    },
    ForeignArtifact,
    MissingReference {
        index: usize,
    },
    InvalidUseReference,
    InvalidCallReference,
    InvalidExpressionReference,
}

fn build_skeleton(
    parsed: &ParsedFile,
    identity: Arc<()>,
    root: SyntaxNode,
    positions: &HashMap<SyntaxNode, Option<PositionId>>,
    raw_positions: &[Position],
) -> Result<Skeleton, ShadowError> {
    let source = parsed.source();
    // The shared envelope is one direct root binding. Root trivia (the four
    // syntax trivia kinds) and the root parser's semicolon separators may
    // surround it; no sibling or enclosing semantic node is discarded.
    let mut statements = Vec::new();
    for element in root.children_with_tokens() {
        if let Some(node) = element.as_node() {
            if node.kind() != SyntaxKind::BindingStatement {
                return Err(ShadowError::MalformedSource);
            }
            statements.push(node.clone());
        } else if !matches!(
            element.kind(),
            SyntaxKind::Whitespace
                | SyntaxKind::Newline
                | SyntaxKind::LineComment
                | SyntaxKind::BlockComment
                | SyntaxKind::Semicolon
        ) {
            return Err(ShadowError::MalformedSource);
        }
    }
    let [statement] = statements.as_slice() else {
        return Err(ShadowError::MalformedSource);
    };
    let header = only_child(statement, SyntaxKind::BindingHeader)?;
    let target = only_child(&header, SyntaxKind::Pattern)?;
    let parts = target.children().collect::<Vec<_>>();
    let Some((name, parameters)) = parts.split_first() else {
        return Err(ShadowError::MalformedSource);
    };
    identifier(name, source)?;
    if parameters.is_empty() {
        return Err(ShadowError::MalformedSource);
    }

    let mut binders = Vec::<Binder>::new();
    let mut names = BTreeSet::new();
    for parameter in parameters {
        if parameter.kind() != SyntaxKind::PatternMlApplicationTail {
            return Err(ShadowError::MalformedSource);
        }
        let pattern = only_child(parameter, SyntaxKind::Pattern)?;
        let binder_node = only_child(&pattern, SyntaxKind::IdentifierPattern)?;
        let (name, range) = identifier(&binder_node, source)?;
        if !names.insert(name.clone()) {
            return Err(ShadowError::DuplicateBinder { range });
        }
        binders.push(Binder {
            name,
            range,
            position: positions
                .get(&binder_node)
                .and_then(Option::as_ref)
                .cloned()
                .ok_or(ShadowError::MalformedSource)?,
        });
    }
    let body = only_child(statement, SyntaxKind::BindingBody)?;
    let chain = only_child(&body, SyntaxKind::OperatorChain)?;
    let mut artifact = Skeleton {
        body: ExprId(LocalId {
            artifact: identity.clone(),
            index: 0,
        }),
        identity,
        binders,
        expressions: Vec::new(),
        uses: Vec::new(),
        use_positions: Vec::new(),
        capture_uses: Vec::new(),
        pending: Vec::new(),
    };
    artifact.body = if chain
        .children()
        .any(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
    {
        artifact.project_selected_nested(statement, chain, source, positions)?
    } else {
        artifact.project(chain, source, positions)?
    };
    artifact.validate()?;
    artifact.validate_positions(raw_positions)?;
    Ok(artifact)
}
fn only_child(node: &SyntaxNode, kind: SyntaxKind) -> Result<SyntaxNode, ShadowError> {
    let children = node.children().collect::<Vec<_>>();
    let matching = children
        .iter()
        .filter(|child| child.kind() == kind)
        .collect::<Vec<_>>();
    let [child] = matching.as_slice() else {
        return Err(ShadowError::MalformedSource);
    };
    // Header and statement contain other structural nodes; atomic patterns and
    // the bounded body must not hide additional source operands.
    if matches!(
        node.kind(),
        SyntaxKind::Pattern | SyntaxKind::PatternMlApplicationTail | SyntaxKind::BindingBody
    ) && children.len() != 1
    {
        return Err(ShadowError::MalformedSource);
    }
    Ok((*child).clone())
}

fn identifier(node: &SyntaxNode, source: &str) -> Result<(String, Range<usize>), ShadowError> {
    if node.kind() != SyntaxKind::IdentifierPattern {
        return Err(ShadowError::MalformedSource);
    }
    let tokens = raw_children(node);
    let [token] = tokens.as_slice() else {
        return Err(ShadowError::MalformedSource);
    };
    let RawElement::Token(token) = token else {
        return Err(ShadowError::MalformedSource);
    };
    if token.kind() != SyntaxKind::Identifier {
        return Err(ShadowError::MalformedSource);
    }
    let range = range_of_token(token);
    let text = source
        .get(range.clone())
        .ok_or_else(|| ShadowError::InvalidRange {
            range: range.clone(),
        })?;
    Ok((text.to_owned(), range))
}

impl Skeleton {
    fn id(&self, index: usize) -> LocalId {
        LocalId {
            artifact: self.identity.clone(),
            index,
        }
    }

    fn check_id(&self, id: &LocalId, length: usize) -> Result<(), ShadowError> {
        if !Arc::ptr_eq(&self.identity, &id.artifact) {
            return Err(ShadowError::ForeignArtifact);
        }
        if id.index >= length {
            return Err(ShadowError::MissingReference { index: id.index });
        }
        Ok(())
    }

    pub fn expression(&self, id: &ExprId) -> Result<&Expression, ShadowError> {
        self.check_id(&id.0, self.expressions.len())?;
        Ok(&self.expressions[id.0.index])
    }

    fn validate(&self) -> Result<(), ShadowError> {
        self.expression(&self.body)?;
        for (index, expression) in self.expressions.iter().enumerate() {
            match &expression.form {
                Form::Lambda {
                    binding,
                    parameter,
                    body,
                    captures,
                    ..
                } => {
                    self.check_id(&binding.0, self.binders.len())?;
                    self.check_id(&parameter.0, self.binders.len())?;
                    for capture in captures {
                        self.check_id(&capture.0, self.binders.len())?;
                    }
                    self.check_child(body, index)?;
                }
                Form::Bind {
                    binder,
                    value,
                    body,
                } => {
                    self.check_id(&binder.0, self.binders.len())?;
                    self.check_child(value, index)?;
                    self.check_child(body, index)?;
                }
                Form::IntegerLiteral { .. } => {}
                Form::Use { binder, occurrence } => {
                    self.check_id(&binder.0, self.binders.len())?;
                    self.check_id(&occurrence.0, self.uses.len())?;
                    if self.uses[occurrence.0.index] != ExprId(self.id(index)) {
                        return Err(ShadowError::InvalidUseReference);
                    }
                }
                Form::Group { inner } => {
                    self.check_child(inner, index)?;
                }
                Form::Apply {
                    callee, argument, ..
                } => {
                    self.check_child(callee, index)?;
                    self.check_child(argument, index)?;
                }
            }
        }
        if matches!(self.expression(&self.body)?.form, Form::Lambda { .. }) {
            self.validate_nested_scope()?;
        }
        self.validate_capture_uses()?;
        for pending in &self.pending {
            if !matches!(self.expression(&pending.call)?.form, Form::Apply { .. }) {
                return Err(ShadowError::InvalidCallReference);
            }
        }
        Ok(())
    }

    fn validate_capture_uses(&self) -> Result<(), ShadowError> {
        let mut recorded = BTreeSet::new();
        for incidence in &self.capture_uses {
            self.check_id(&incidence.captured.0, self.binders.len())?;
            let Form::Lambda { body, captures, .. } = &self.expression(&incidence.lambda)?.form
            else {
                return Err(ShadowError::InvalidExpressionReference);
            };
            let Form::Apply { callee, .. } = &self.expression(body)?.form else {
                return Err(ShadowError::InvalidCallReference);
            };
            let Form::Use { binder, occurrence } = &self.expression(callee)?.form else {
                return Err(ShadowError::InvalidUseReference);
            };
            if captures.as_slice() != std::slice::from_ref(&incidence.captured)
                || binder != &incidence.captured
                || occurrence != &incidence.occurrence
                || self.use_position(&incidence.occurrence)? != &incidence.position
                || !recorded.insert(incidence.lambda.0.index)
            {
                return Err(ShadowError::InvalidUseReference);
            }
        }
        for (index, expression) in self.expressions.iter().enumerate() {
            if matches!(&expression.form, Form::Lambda { captures, .. } if !captures.is_empty())
                && !recorded.contains(&index)
            {
                return Err(ShadowError::InvalidUseReference);
            }
        }
        Ok(())
    }

    fn validate_nested_scope(&self) -> Result<(), ShadowError> {
        // Only the selected structural slice introduces explicit lexical scope.
        // The existing ordinary projector retains its formal-only envelope.
        let mut tasks = vec![(self.body.clone(), BTreeSet::<usize>::new())];
        while let Some((id, scope)) = tasks.pop() {
            match &self.expression(&id)?.form {
                Form::Use { binder, .. } => {
                    if !scope.contains(&binder.0.index) {
                        return Err(ShadowError::InvalidExpressionReference);
                    }
                }
                Form::Lambda {
                    binding,
                    parameter,
                    body,
                    captures,
                    ..
                } => {
                    if binding == parameter {
                        return Err(ShadowError::InvalidExpressionReference);
                    }
                    let mut local = BTreeSet::from([parameter.0.index]);
                    for capture in captures {
                        if !scope.contains(&capture.0.index) || !local.insert(capture.0.index) {
                            return Err(ShadowError::InvalidExpressionReference);
                        }
                    }
                    tasks.push((body.clone(), local));
                }
                Form::Bind {
                    binder,
                    value,
                    body,
                } => {
                    if !matches!(&self.expression(value)?.form,
                        Form::Lambda { binding, .. } if binding == binder)
                    {
                        return Err(ShadowError::InvalidExpressionReference);
                    }
                    let mut after = scope.clone();
                    after.insert(binder.0.index);
                    tasks.push((body.clone(), after));
                    tasks.push((value.clone(), scope));
                }
                Form::Apply {
                    callee, argument, ..
                } => {
                    tasks.push((argument.clone(), scope.clone()));
                    tasks.push((callee.clone(), scope));
                }
                Form::Group { inner } => tasks.push((inner.clone(), scope)),
                Form::IntegerLiteral { .. } => {}
            }
        }
        Ok(())
    }

    fn validate_positions(&self, positions: &[Position]) -> Result<(), ShadowError> {
        for expression in &self.expressions {
            self.check_id(&expression.position.0, positions.len())?;
            let position = &positions[expression.position.0.index];
            let kind = match &expression.form {
                Form::Lambda { .. } => SyntaxKind::BindingStatement,
                Form::Bind { .. } => SyntaxKind::BracedStatementBlockExpression,
                Form::IntegerLiteral { .. } => SyntaxKind::IntegerLiteral,
                Form::Use { occurrence, .. } => {
                    if self.use_position(occurrence)? != &expression.position {
                        return Err(ShadowError::InvalidUseReference);
                    }
                    SyntaxKind::IdentifierExpression
                }
                Form::Group { .. } => SyntaxKind::ParenthesizedExpression,
                Form::Apply { source_form, .. } => *source_form,
            };
            if !position.is_node || position.kind != kind {
                return Err(ShadowError::InvalidExpressionReference);
            }
        }
        Ok(())
    }

    fn check_child(&self, child: &ExprId, parent: usize) -> Result<(), ShadowError> {
        self.expression(child)?;
        // Construction publishes children first. This rejects cyclic or forward
        // references before any recursive structural comparison can consume them.
        if child.0.index >= parent {
            return Err(ShadowError::InvalidExpressionReference);
        }
        Ok(())
    }
}

#[derive(Clone)]
enum RawElement {
    Node(SyntaxNode),
    Token(SyntaxToken),
}
impl RawElement {
    fn kind(&self) -> SyntaxKind {
        match self {
            Self::Node(n) => n.kind(),
            Self::Token(t) => t.kind(),
        }
    }
    fn as_node(&self) -> Option<&SyntaxNode> {
        match self {
            Self::Node(n) => Some(n),
            _ => None,
        }
    }
    fn range(&self) -> Range<usize> {
        match self {
            Self::Node(n) => range_of(n),
            Self::Token(t) => range_of_token(t),
        }
    }
}
fn raw_children(node: &SyntaxNode) -> Vec<RawElement> {
    node.children_with_tokens()
        .map(|e| {
            if let Some(n) = e.as_node() {
                RawElement::Node(n.clone())
            } else {
                RawElement::Token(e.into_token().expect("raw element token"))
            }
        })
        .collect()
}

impl ShadowArtifact {
    #[cfg(test)]
    pub(crate) fn into_skeleton(self) -> Result<Skeleton, ShadowError> {
        self.skeleton
    }
}
impl Binder {
    /// Exact retained IdentifierPattern occurrence; no typed slot is implied.
    pub fn position(&self) -> &PositionId {
        &self.position
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
}
impl Expression {
    /// Exact retained source node; applications identify their CST call tail.
    /// This syntax occurrence carries no typed slot or call-view judgment.
    pub fn position(&self) -> &PositionId {
        &self.position
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
    pub fn form(&self) -> &Form {
        &self.form
    }
}
impl PendingPremise {
    pub fn call(&self) -> &ExprId {
        &self.call
    }
    pub fn premise(&self) -> Premise {
        self.premise
    }
}
impl Skeleton {
    pub fn capture_uses(&self) -> &[CaptureUseIncidence] {
        &self.capture_uses
    }

    pub fn body(&self) -> &ExprId {
        &self.body
    }
    pub fn expressions(&self) -> &[Expression] {
        &self.expressions
    }
    pub fn binders(&self) -> &[Binder] {
        &self.binders
    }
    pub fn uses(&self) -> &[ExprId] {
        &self.uses
    }
    pub fn pending(&self) -> &[PendingPremise] {
        &self.pending
    }
    pub fn binder(&self, id: &BinderId) -> Result<&Binder, ShadowError> {
        self.check_id(&id.0, self.binders.len())?;
        Ok(&self.binders[id.0.index])
    }
    /// Exact retained IdentifierExpression occurrence for this resolved use.
    pub fn use_position(&self, id: &UseId) -> Result<&PositionId, ShadowError> {
        self.check_id(&id.0, self.uses.len())?;
        self.use_positions
            .get(id.0.index)
            .ok_or(ShadowError::InvalidUseReference)
    }
    pub fn use_expression(&self, id: &UseId) -> Result<&Expression, ShadowError> {
        self.check_id(&id.0, self.uses.len())?;
        self.expression(&self.uses[id.0.index])
    }
    #[cfg(test)]
    pub(crate) fn binder_index(&self, id: &BinderId) -> Result<usize, ShadowError> {
        self.check_id(&id.0, self.binders.len())?;
        Ok(id.0.index)
    }
    #[cfg(test)]
    pub(crate) fn use_index(&self, id: &UseId) -> Result<usize, ShadowError> {
        self.check_id(&id.0, self.uses.len())?;
        Ok(id.0.index)
    }
    #[cfg(test)]
    pub(crate) fn binder_ids(&self) -> Vec<BinderId> {
        (0..self.binders.len())
            .map(|i| BinderId(self.id(i)))
            .collect()
    }
    fn push_expression(&mut self, position: PositionId, range: Range<usize>, form: Form) -> ExprId {
        let id = ExprId(self.id(self.expressions.len()));
        if matches!(form, Form::Apply { .. }) {
            for premise in [
                Premise::CallableRole,
                Premise::FullFunctionMembership,
                Premise::CallViewRealization,
            ] {
                self.pending.push(PendingPremise {
                    call: id.clone(),
                    premise,
                });
            }
        }
        if matches!(form, Form::Use { .. }) {
            self.uses.push(id.clone());
        }
        self.expressions.push(Expression {
            position,
            range,
            form,
        });
        id
    }
    fn project_selected_nested(
        &mut self,
        outer: &SyntaxNode,
        chain: SyntaxNode,
        source: &str,
        positions: &HashMap<SyntaxNode, Option<PositionId>>,
    ) -> Result<ExprId, ShadowError> {
        // This recognizer owns only the approved lambda/bind/lambda/call/use
        // correspondence. It is not a general interpretation of brace blocks.
        let blocks = chain.children().collect::<Vec<_>>();
        let Some(block) = blocks
            .iter()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        else {
            return Err(unsupported(&chain));
        };
        let reject = || unsupported(block);
        if blocks.len() != 1 || self.binders.len() != 1 {
            return Err(reject());
        }
        let children = block.children().collect::<Vec<_>>();
        let [local_statement, separator, final_statement] = children.as_slice() else {
            return Err(reject());
        };
        if local_statement.kind() != SyntaxKind::Statement
            || separator.kind() != SyntaxKind::BlockStatementSeparator
            || final_statement.kind() != SyntaxKind::Statement
            || separator.children().next().is_some()
        {
            return Err(reject());
        }
        let separator_tokens = separator
            .children_with_tokens()
            .filter(|element| !matches!(element.kind(), SyntaxKind::Whitespace))
            .collect::<Vec<_>>();
        if separator_tokens.len() != 1 || separator_tokens[0].kind() != SyntaxKind::Semicolon {
            return Err(reject());
        }
        let local =
            only_child(local_statement, SyntaxKind::BindingStatement).map_err(|_| reject())?;
        if local_statement.children().count() != 1 || final_statement.children().count() != 1 {
            return Err(reject());
        }
        let header_nodes =
            |statement: &SyntaxNode| -> Result<(SyntaxNode, SyntaxNode), ShadowError> {
                let children = statement
                    .children()
                    .map(|node| node.kind())
                    .collect::<Vec<_>>();
                if children != [SyntaxKind::BindingHeader, SyntaxKind::BindingBody] {
                    return Err(reject());
                }
                let header = only_child(statement, SyntaxKind::BindingHeader)?;
                let header_elements = header
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
                    .map(|element| element.kind())
                    .collect::<Vec<_>>();
                if header_elements != [SyntaxKind::MyKw, SyntaxKind::Pattern, SyntaxKind::Equals] {
                    return Err(reject());
                }
                let pattern = only_child(&header, SyntaxKind::Pattern)?;
                let nodes = pattern.children().collect::<Vec<_>>();
                let [name, tail] = nodes.as_slice() else {
                    return Err(reject());
                };
                identifier(name, source)?;
                if tail.kind() != SyntaxKind::PatternMlApplicationTail {
                    return Err(reject());
                }
                let parameter = only_child(tail, SyntaxKind::Pattern)?;
                let parameter = only_child(&parameter, SyntaxKind::IdentifierPattern)?;
                Ok((name.clone(), parameter))
            };
        let (outer_name, _) = header_nodes(outer).map_err(|_| reject())?;
        let (local_name, local_parameter) = header_nodes(&local).map_err(|_| reject())?;
        let local_body = only_child(&local, SyntaxKind::BindingBody).map_err(|_| reject())?;
        let local_chain =
            only_child(&local_body, SyntaxKind::OperatorChain).map_err(|_| reject())?;
        let call_nodes = local_chain.children().collect::<Vec<_>>();
        let [callee, argument] = call_nodes.as_slice() else {
            return Err(reject());
        };
        if callee.kind() != SyntaxKind::IdentifierExpression
            || argument.kind() != SyntaxKind::MlArgument
        {
            return Err(reject());
        }
        let argument_chain =
            only_child(argument, SyntaxKind::OperatorChain).map_err(|_| reject())?;
        let arguments = argument_chain.children().collect::<Vec<_>>();
        let final_chain =
            only_child(final_statement, SyntaxKind::OperatorChain).map_err(|_| reject())?;
        let returns = final_chain.children().collect::<Vec<_>>();
        let ([argument_use], [returned_use]) = (arguments.as_slice(), returns.as_slice()) else {
            return Err(reject());
        };
        if argument_use.kind() != SyntaxKind::IdentifierExpression
            || returned_use.kind() != SyntaxKind::IdentifierExpression
        {
            return Err(reject());
        }
        let (step_name, _) = identifier(&local_name, source)?;
        let (x_name, _) = identifier(&local_parameter, source)?;
        let f_name = &self.binders[0].name;
        // Admission is deliberately bounded to the approved named source
        // candidate. These spellings select no inference or runtime behavior.
        if identifier(&outer_name, source)?.0 != "apply"
            || f_name != "f"
            || step_name != "step"
            || x_name != "x"
            || source.get(range_of(callee)) != Some(f_name.as_str())
            || source.get(range_of(argument_use)) != Some(x_name.as_str())
            || source.get(range_of(returned_use)) != Some(step_name.as_str())
            || x_name == *f_name
            || step_name == *f_name
            || step_name == x_name
        {
            return Err(reject());
        }
        let add_binder =
            |artifact: &mut Self, node: &SyntaxNode| -> Result<BinderId, ShadowError> {
                let (name, range) = identifier(node, source)?;
                let id = BinderId(artifact.id(artifact.binders.len()));
                artifact.binders.push(Binder {
                    name,
                    range,
                    position: retained_position(positions, node)?,
                });
                Ok(id)
            };
        let f = BinderId(self.id(0));
        let x = add_binder(self, &local_parameter)?;
        // Project the local initializer before publishing the sequential local
        // binder: step is unavailable in its own body. Only f and x are in scope.
        let call = self.project(local_chain, source, positions)?;
        let step = add_binder(self, &local_name)?;
        let local_lambda = self.push_expression(
            retained_position(positions, &local)?,
            range_of(&local),
            Form::Lambda {
                binding: step.clone(),
                parameter: x,
                body: call.clone(),
                captures: vec![f.clone()],
                correspondence:
                    ClosureCorrespondence::PendingTypedCaptureProviderReceiverAndSemanticDischarge,
            },
        );
        let Form::Apply { callee, .. } = &self.expression(&call)?.form else {
            return Err(ShadowError::InvalidCallReference);
        };
        let Form::Use { occurrence, .. } = &self.expression(callee)?.form else {
            return Err(ShadowError::InvalidUseReference);
        };
        self.capture_uses.push(CaptureUseIncidence {
            lambda: local_lambda.clone(),
            captured: f.clone(),
            occurrence: occurrence.clone(),
            position: self.use_position(occurrence)?.clone(),
        });
        // The recognizer requires the final use to be step; x has no use here.
        let returned = self.project(final_chain, source, positions)?;
        let bound = self.push_expression(
            retained_position(positions, block)?,
            range_of(block),
            Form::Bind {
                binder: step,
                value: local_lambda,
                body: returned,
            },
        );
        let apply = add_binder(self, &outer_name)?;
        Ok(self.push_expression(
            retained_position(positions, outer)?,
            range_of(outer),
            Form::Lambda {
                binding: apply,
                parameter: f,
                body: bound,
                captures: Vec::new(),
                correspondence:
                    ClosureCorrespondence::PendingTypedCaptureProviderReceiverAndSemanticDischarge,
            },
        ))
    }
    fn project(
        &mut self,
        root: SyntaxNode,
        source: &str,
        positions: &HashMap<SyntaxNode, Option<PositionId>>,
    ) -> Result<ExprId, ShadowError> {
        // Tasks/results hold IDs and CST handles, never recursively owned expressions.
        enum Task {
            Visit(SyntaxNode),
            Group(PositionId, Range<usize>),
            Chain(Vec<(PositionId, SyntaxKind, Range<usize>)>),
        }
        let names = self
            .binders
            .iter()
            .enumerate()
            .map(|(i, b)| (b.name.clone(), i))
            .collect::<BTreeMap<_, _>>();
        let mut tasks = vec![Task::Visit(root)];
        let mut results = Vec::<ExprId>::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(node) => {
                    match node.kind() {
                        SyntaxKind::IntegerLiteral => {
                            if node.children().next().is_some() {
                                return Err(unsupported(&node));
                            }
                            let range = range_of(&node);
                            let spelling = source.get(range.clone()).ok_or_else(|| {
                                ShadowError::InvalidRange {
                                    range: range.clone(),
                                }
                            })?;
                            results.push(self.push_expression(
                                retained_position(positions, &node)?,
                                range,
                                Form::IntegerLiteral {
                                    spelling: spelling.to_owned(),
                                },
                            ));
                        }
                        SyntaxKind::IdentifierExpression => {
                            if node.children().next().is_some() {
                                return Err(unsupported(&node));
                            }
                            let range = range_of(&node);
                            let name = source.get(range.clone()).ok_or_else(|| {
                                ShadowError::InvalidRange {
                                    range: range.clone(),
                                }
                            })?;
                            let index = names.get(name).copied().ok_or_else(|| {
                                ShadowError::UnboundName {
                                    range: range.clone(),
                                }
                            })?;
                            let position = positions
                                .get(&node)
                                .and_then(Option::as_ref)
                                .cloned()
                                .ok_or(ShadowError::MalformedSource)?;
                            self.use_positions.push(position.clone());
                            let occurrence = UseId(self.id(self.uses.len()));
                            let binder = BinderId(self.id(index));
                            results.push(self.push_expression(
                                position,
                                range,
                                Form::Use { binder, occurrence },
                            ));
                        }
                        SyntaxKind::ParenthesizedExpression => {
                            let inner = nested_chain(&node)?;
                            tasks.push(Task::Group(
                                retained_position(positions, &node)?,
                                range_of(&node),
                            ));
                            tasks.push(Task::Visit(inner));
                        }
                        SyntaxKind::OperatorChain => {
                            let children = node.children().collect::<Vec<_>>();
                            let Some((first, tails)) = children.split_first() else {
                                return Err(unsupported(&node));
                            };
                            if !matches!(
                                first.kind(),
                                SyntaxKind::IdentifierExpression
                                    | SyntaxKind::ParenthesizedExpression
                                    | SyntaxKind::IntegerLiteral
                            ) {
                                return Err(unsupported(first));
                            }
                            let mut arguments = Vec::new();
                            let mut forms = Vec::new();
                            for tail in tails {
                                if !matches!(
                                    tail.kind(),
                                    SyntaxKind::MlArgument | SyntaxKind::CallTail
                                ) {
                                    return Err(unsupported(tail));
                                }
                                arguments.push(nested_chain(tail)?);
                                forms.push((
                                    retained_position(positions, tail)?,
                                    tail.kind(),
                                    range_of(tail),
                                ));
                            }
                            tasks.push(Task::Chain(forms));
                            for argument in arguments.into_iter().rev() {
                                tasks.push(Task::Visit(argument));
                            }
                            tasks.push(Task::Visit(first.clone()));
                        }
                        _ => return Err(unsupported(&node)),
                    }
                }
                Task::Group(position, range) => {
                    let inner = results.pop().ok_or(ShadowError::MalformedSource)?;
                    results.push(self.push_expression(position, range, Form::Group { inner }));
                }
                Task::Chain(forms) => {
                    let start = results
                        .len()
                        .checked_sub(forms.len() + 1)
                        .ok_or(ShadowError::MalformedSource)?;
                    let operands = results.split_off(start);
                    let mut operands = operands.into_iter();
                    let mut callee = operands.next().ok_or(ShadowError::MalformedSource)?;
                    for ((position, source_form, tail_range), argument) in
                        forms.into_iter().zip(operands)
                    {
                        let range = self.expression(&callee)?.range.start.min(tail_range.start)
                            ..self.expression(&callee)?.range.end.max(tail_range.end);
                        callee = self.push_expression(
                            position,
                            range,
                            Form::Apply {
                                source_form,
                                callee,
                                argument,
                            },
                        );
                    }
                    results.push(callee);
                }
            }
        }
        if results.len() != 1 {
            return Err(ShadowError::MalformedSource);
        }
        Ok(results.pop().expect("one projection"))
    }
}
fn retained_position(
    positions: &HashMap<SyntaxNode, Option<PositionId>>,
    node: &SyntaxNode,
) -> Result<PositionId, ShadowError> {
    positions
        .get(node)
        .and_then(Option::as_ref)
        .cloned()
        .ok_or(ShadowError::MalformedSource)
}

fn unsupported(node: &SyntaxNode) -> ShadowError {
    ShadowError::UnsupportedExpression {
        kind: node.kind(),
        range: range_of(node),
    }
}
fn nested_chain(node: &SyntaxNode) -> Result<SyntaxNode, ShadowError> {
    // Match the existing narrow associator's nested-chain collection, without recursion.
    let mut stack = node.children().collect::<Vec<_>>();
    let mut chains = Vec::new();
    while let Some(child) = stack.pop() {
        if child.kind() == SyntaxKind::OperatorChain {
            chains.push(child);
        } else {
            stack.extend(child.children());
        }
    }
    if chains.len() != 1 {
        return Err(unsupported(node));
    }
    Ok(chains.pop().expect("one nested chain"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};
    fn parsed(source: &str) -> ParsedFile {
        let source: Arc<SourceText> = Arc::from(source);
        let header = Arc::new(scan_header(source.clone()));
        parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
    }

    const NESTED: &str = "my apply f = { my step x = f x; step }";

    #[test]
    fn selected_nested_source_preserves_binders_scope_return_and_pending_boundary() {
        let artifact = ShadowArtifact::from_parsed(parsed(NESTED)).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        let Form::Lambda {
            binding: apply,
            parameter: f,
            body: block,
            captures,
            correspondence,
        } = skeleton.expression(skeleton.body()).unwrap().form()
        else {
            panic!("outer lambda")
        };
        assert!(captures.is_empty());
        assert_eq!(
            *correspondence,
            ClosureCorrespondence::PendingTypedCaptureProviderReceiverAndSemanticDischarge
        );
        assert_eq!(skeleton.binder(apply).unwrap().name(), "apply");
        assert_eq!(skeleton.binder(f).unwrap().name(), "f");
        let Form::Bind {
            binder: step,
            value,
            body: returned,
        } = skeleton.expression(block).unwrap().form()
        else {
            panic!("sequential bind")
        };
        let Form::Lambda {
            binding,
            parameter: x,
            body: call,
            captures,
            correspondence,
        } = skeleton.expression(value).unwrap().form()
        else {
            panic!("local lambda")
        };
        assert_eq!(binding, step);
        assert_eq!(captures, &vec![f.clone()]);
        assert_eq!(
            *correspondence,
            ClosureCorrespondence::PendingTypedCaptureProviderReceiverAndSemanticDischarge
        );
        assert_eq!(skeleton.binder(x).unwrap().name(), "x");
        assert_eq!(skeleton.binder(step).unwrap().name(), "step");
        let Form::Apply {
            callee,
            argument,
            source_form,
        } = skeleton.expression(call).unwrap().form()
        else {
            panic!("f x")
        };
        assert_eq!(*source_form, SyntaxKind::MlArgument);
        let [incidence] = skeleton.capture_uses() else {
            panic!("one lexical capture-use incidence")
        };
        assert_eq!(incidence.lambda(), value);
        assert_eq!(incidence.captured(), f);
        let Form::Use { occurrence, .. } = skeleton.expression(callee).unwrap().form() else {
            panic!("callee use")
        };
        assert_eq!(incidence.occurrence(), occurrence);
        assert_eq!(
            incidence.position(),
            skeleton.use_position(occurrence).unwrap()
        );
        for (id, expected_binder, expected_range) in [
            (callee, f, 27..28),
            (argument, x, 29..30),
            (returned, step, 32..36),
        ] {
            let expression = skeleton.expression(id).unwrap();
            let Form::Use { binder, occurrence } = expression.form() else {
                panic!("resolved use")
            };
            assert_eq!(binder, expected_binder);
            assert_eq!(*expression.range(), expected_range);
            assert_eq!(
                skeleton.use_position(occurrence).unwrap(),
                expression.position()
            );
            assert_eq!(
                artifact.position(expression.position()).unwrap().kind(),
                SyntaxKind::IdentifierExpression
            );
        }
        assert_eq!(skeleton.uses().len(), 3);
        assert_eq!(skeleton.pending().len(), 3);
        for (pending, expected) in skeleton.pending().iter().zip([
            Premise::CallableRole,
            Premise::FullFunctionMembership,
            Premise::CallViewRealization,
        ]) {
            assert_eq!(pending.call(), call);
            assert_eq!(pending.premise(), expected);
        }
        for binder in skeleton.binders() {
            let position = artifact.position(binder.position()).unwrap();
            assert_eq!(position.kind(), SyntaxKind::IdentifierPattern);
            assert_eq!(position.range(), binder.range());
        }
        // A separately parsed artifact must never share identities.
        let other = ShadowArtifact::from_parsed(parsed(NESTED)).unwrap();
        assert_eq!(
            other.skeleton().unwrap().binder(f).unwrap_err(),
            ShadowError::ForeignArtifact
        );
    }

    #[test]
    fn selected_capture_use_incidence_rejects_inconsistent_links() {
        let artifact = ShadowArtifact::from_parsed(parsed(NESTED)).unwrap();
        let mut skeleton = artifact.into_skeleton().unwrap();
        let other = ShadowArtifact::from_parsed(parsed(NESTED)).unwrap();
        let other = other.skeleton().unwrap();
        let saved_lambda = skeleton.capture_uses[0].lambda.clone();
        skeleton.capture_uses[0].lambda = other.capture_uses[0].lambda.clone();
        assert_eq!(skeleton.validate(), Err(ShadowError::ForeignArtifact));
        skeleton.capture_uses[0].lambda = saved_lambda;

        let saved_binder = skeleton.capture_uses[0].captured.clone();
        skeleton.capture_uses[0].captured = BinderId(skeleton.id(1));
        assert_eq!(skeleton.validate(), Err(ShadowError::InvalidUseReference));
        skeleton.capture_uses[0].captured = saved_binder;

        let saved_use = skeleton.capture_uses[0].occurrence.clone();
        skeleton.capture_uses[0].occurrence = UseId(skeleton.id(1));
        assert_eq!(skeleton.validate(), Err(ShadowError::InvalidUseReference));
        skeleton.capture_uses[0].occurrence = saved_use;

        let saved_position = skeleton.capture_uses[0].position.clone();
        skeleton.capture_uses[0].position = skeleton.use_positions[1].clone();
        assert_eq!(skeleton.validate(), Err(ShadowError::InvalidUseReference));
        skeleton.capture_uses[0].position = saved_position;
        skeleton.validate().unwrap();
        skeleton.capture_uses.clear();
        assert_eq!(skeleton.validate(), Err(ShadowError::InvalidUseReference));
    }

    #[test]
    fn selected_nested_scope_accepts_formatting_with_approved_names_and_modifiers() {
        let source = "my  apply f  =  { my  step x  =  f  x;  step  }";
        let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        assert_eq!(skeleton.expressions().len(), 7);
        assert_eq!(skeleton.uses().len(), 3);
        assert_eq!(skeleton.pending().len(), 3);
        assert_eq!(
            skeleton
                .binders()
                .iter()
                .map(Binder::name)
                .collect::<Vec<_>>(),
            ["f", "x", "step", "apply"]
        );
    }

    #[test]
    fn selected_nested_scope_rejects_missing_capture_and_escaped_local_parameter() {
        let mut skeleton = ShadowArtifact::from_parsed(parsed(NESTED))
            .unwrap()
            .into_skeleton()
            .unwrap();
        let local = skeleton.expressions.iter().position(|expression| {
            matches!(&expression.form, Form::Lambda { captures, .. } if !captures.is_empty())
        }).unwrap();
        let Form::Lambda {
            captures,
            parameter,
            ..
        } = &mut skeleton.expressions[local].form
        else {
            panic!("local lambda")
        };
        let x = parameter.clone();
        let saved = std::mem::take(captures);
        assert_eq!(
            skeleton.validate(),
            Err(ShadowError::InvalidExpressionReference)
        );
        let Form::Lambda { captures, .. } = &mut skeleton.expressions[local].form else {
            panic!("local lambda")
        };
        *captures = saved;
        skeleton.validate().unwrap();
        let returned = skeleton.uses.last().unwrap().0.index;
        let Form::Use { binder, .. } = &mut skeleton.expressions[returned].form else {
            panic!("returned step")
        };
        *binder = x;
        assert_eq!(
            skeleton.validate(),
            Err(ShadowError::InvalidExpressionReference)
        );
    }

    #[test]
    fn selected_nested_recognizer_rejects_adjacent_brace_forms() {
        for source in [
            "my wrapper callback = { my local input = callback input; local }",
            "my wrapper f = { my step x = f x; step }",
            "my apply callback = { my step x = callback x; step }",
            "my apply f = { my local x = f x; local }",
            "my apply f = { my step input = f input; step }",
            "our apply f = { my step x = f x; step }",
            "pub apply f = { my step x = f x; step }",
            "my apply f = { our step x = f x; step }",
            "my apply f = { pub step x = f x; step }",
            "my apply f = {}",
            "my apply f = { f }",
            "my apply f = { my step x = f x; step x }",
            "my apply f = { my step x = f x; x }",
            "my apply f = { my step x = step x; step }",
            "my apply f = { my step x = f(x); step }",
            "my apply f g = { my step x = f x; step }",
            "my apply f = { my step x y = f x; step }",
            "my apply f = { my step x = f x; my other y = f y; step }",
        ] {
            let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
            assert!(
                matches!(artifact.skeleton(), Err(ShadowError::UnsupportedExpression {
                kind: SyntaxKind::BracedStatementBlockExpression, range,
            }) if *range == (source.find('{').unwrap()..source.len())),
                "{source}"
            );
            assert_eq!(artifact.source(), source);
        }
    }

    #[test]
    fn occurrence_index_rejects_ambiguous_zero_width_cst_handles() {
        let parsed = parsed("my f x = x");
        let root = SyntaxNode::new_root(parsed.green().clone());
        let leaf = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::IdentifierExpression)
            .unwrap();
        let green = leaf.green().into_owned();
        let empty = green.splice_children(0..green.children().count(), []);
        let root_green = root.green().into_owned();
        let synthetic = SyntaxNode::new_root(root_green.splice_children(
            0..root_green.children().count(),
            [empty.clone().into(), empty.into()],
        ));
        let mut artifact = ShadowArtifact::from_parsed(parsed).unwrap();
        let positions = artifact.retain(synthetic.clone());
        let leaves = synthetic.children().collect::<Vec<_>>();
        assert_eq!(leaves.len(), 2);
        assert_eq!(leaves[0], leaves[1]); // Rowan's shared green handle and offset.
        assert!(positions.get(&leaves[0]).unwrap().is_none());
    }

    #[test]
    fn expression_positions_resolve_exact_source_nodes_and_call_tails() {
        let source = "my call f x = f (x) 7(x)";
        let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        let mut kinds = Vec::new();
        let root = SyntaxNode::new_root(artifact.parsed().green().clone());
        let retained = artifact.positions();
        let tails = root
            .descendants()
            .filter(|node| matches!(node.kind(), SyntaxKind::MlArgument | SyntaxKind::CallTail))
            .map(|node| {
                let matches = retained
                    .iter()
                    .enumerate()
                    .filter(|(_, position)| {
                        position.is_node()
                            && position.kind() == node.kind()
                            && *position.range() == range_of(&node)
                    })
                    .map(|(index, _)| artifact.position_id(index))
                    .collect::<Vec<_>>();
                assert_eq!(matches.len(), 1);
                matches.into_iter().next().unwrap()
            })
            .collect::<Vec<_>>();
        let mut calls = Vec::new();
        for expression in skeleton.expressions() {
            let position = artifact.position(expression.position()).unwrap();
            assert!(position.is_node());
            kinds.push(position.kind());
            match expression.form() {
                Form::Apply { source_form, .. } => {
                    assert_eq!(position.kind(), *source_form);
                    calls.push(expression.position().clone());
                }
                Form::Use { occurrence, .. } => {
                    assert_eq!(
                        skeleton.use_position(occurrence).unwrap(),
                        expression.position()
                    );
                }
                _ => assert_eq!(position.range(), expression.range()),
            }
        }
        assert!(kinds.contains(&SyntaxKind::IntegerLiteral));
        assert!(kinds.contains(&SyntaxKind::ParenthesizedExpression));
        assert_eq!(calls.len(), tails.len());
        for tail in tails {
            assert_eq!(
                calls.iter().filter(|position| **position == tail).count(),
                1
            );
        }
    }

    #[test]
    fn expression_position_validation_rejects_foreign_missing_and_wrong_nodes() {
        let mut first = ShadowArtifact::from_parsed(parsed("my call f x = f x")).unwrap();
        let second = ShadowArtifact::from_parsed(parsed("my call f x = f x")).unwrap();
        let foreign = second.skeleton().unwrap().expressions()[0]
            .position()
            .clone();
        let missing = first.position_id(first.positions.len());
        let wrong = first.root();
        let skeleton = first.skeleton.as_mut().unwrap();
        let original = skeleton.expressions[0].position.clone();
        skeleton.expressions[0].position = foreign;
        assert_eq!(
            skeleton.validate_positions(&first.positions),
            Err(ShadowError::ForeignArtifact)
        );
        skeleton.expressions[0].position = missing;
        assert_eq!(
            skeleton.validate_positions(&first.positions),
            Err(ShadowError::MissingReference {
                index: first.positions.len()
            })
        );
        skeleton.expressions[0].position = wrong;
        assert_eq!(
            skeleton.validate_positions(&first.positions),
            Err(ShadowError::InvalidUseReference)
        );
        skeleton.expressions[0].position = original;
        skeleton.validate_positions(&first.positions).unwrap();
    }

    #[test]
    fn raw_preflight_accepts_exact_depth_and_rejects_one_more() {
        // Synthetic CST tests the adapter's structural boundary independently
        // of grammar nesting and parser resource limits. Root depth is zero.
        let mut green = parsed(";").green().clone();
        for _ in 0..MAX_SYNTAX_DEPTH - 1 {
            let length = green.children().count();
            green = green.splice_children(0..length, [green.clone().into()]);
        }
        assert_eq!(preflight(&SyntaxNode::new_root(green.clone())), Ok(()));
        let length = green.children().count();
        green = green.splice_children(0..length, [green.clone().into()]);
        assert_eq!(
            preflight(&SyntaxNode::new_root(green)),
            Err(ShadowError::SyntaxDepthLimit)
        );
    }

    #[test]
    fn raw_preflight_accepts_exact_element_count_and_rejects_one_more() {
        let green = parsed(";").green().clone();
        let token = green.children().next().unwrap().to_owned();
        let length = green.children().count();
        let boundary = green.splice_children(
            0..length,
            std::iter::repeat_n(token.clone(), MAX_RAW_ELEMENTS - 1),
        );
        assert_eq!(preflight(&SyntaxNode::new_root(boundary)), Ok(()));
        let rejected =
            green.splice_children(0..length, std::iter::repeat_n(token, MAX_RAW_ELEMENTS));
        assert_eq!(
            preflight(&SyntaxNode::new_root(rejected)),
            Err(ShadowError::ElementLimit)
        );
    }

    #[test]
    fn parsed_flat_chain_preserves_every_ordinary_application() {
        // The public boundary starts after a successful parse. Large flat
        // source chains hit the upstream parser's recursive tail path, so this
        // integration case stays within its ordinary successful envelope.
        let source = format!("my chain f x = f{}", " x".repeat(8));
        let artifact = ShadowArtifact::from_parsed(parsed(&source)).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        assert_eq!(skeleton.expressions().len(), 17);
        assert_eq!(skeleton.pending().len(), 24);
        assert_eq!(skeleton.uses().len(), 9);
        drop(artifact);
    }

    #[test]
    fn long_flat_chain_builds_and_drops_without_recursive_expressions() {
        // Construct a shallow, lossless chain from parser-produced CST pieces.
        // This tests the owning projection's 4,000-tail worklist independently
        // of the source parser's separate recursive continuation stack limit.
        let parsed = parsed("my chain f x = f x");
        let raw_root = SyntaxNode::new_root(parsed.green().clone());
        let chain = raw_root
            .descendants()
            .find(|n| n.kind() == SyntaxKind::BindingBody)
            .unwrap()
            .children()
            .find(|n| n.kind() == SyntaxKind::OperatorChain)
            .unwrap();
        assert_eq!(chain.to_string(), "f x");
        let green = chain.green().into_owned();
        let children = green.children().map(|e| e.to_owned()).collect::<Vec<_>>();
        let (callee, tail) = children.split_first().unwrap();
        let mut expanded = vec![callee.clone()];
        for _ in 0..4_000 {
            expanded.extend(tail.iter().cloned());
        }
        let synthetic = SyntaxNode::new_root(green.splice_children(0..children.len(), expanded));
        let source = format!("f{}", " x".repeat(4_000));
        assert_eq!(synthetic.to_string(), source);
        assert_eq!(preflight(&synthetic), Ok(()));
        let mut retained = ShadowArtifact::from_parsed(parsed).unwrap();
        let positions = retained.retain(synthetic.clone());
        let mut skeleton = retained.into_skeleton().unwrap();
        skeleton.expressions.clear();
        skeleton.uses.clear();
        skeleton.use_positions.clear();
        skeleton.pending.clear();
        skeleton.body = skeleton.project(synthetic, &source, &positions).unwrap();
        skeleton.validate().unwrap();
        assert_eq!(skeleton.expressions().len(), 8_001);
        assert_eq!(skeleton.pending().len(), 12_000);
        assert_eq!(skeleton.uses().len(), 4_001);
        drop(skeleton);
    }

    #[test]
    fn call_tail_preserves_one_whole_argument_and_pending_premises() {
        let artifact = ShadowArtifact::from_parsed(parsed("my call f x = f(x)")).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        let Form::Apply {
            source_form,
            argument,
            ..
        } = skeleton.expression(skeleton.body()).unwrap().form()
        else {
            panic!("ordinary call")
        };
        assert_eq!(*source_form, SyntaxKind::CallTail);
        assert!(matches!(
            skeleton.expression(argument).unwrap().form(),
            Form::Use { .. }
        ));
        assert_eq!(skeleton.pending().len(), 3);
    }

    #[test]
    fn unsupported_expression_keeps_raw_source_without_a_success_fallback() {
        let source = "my constant x = \"unsupported\"";
        let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
        assert!(matches!(
            artifact.skeleton(),
            Err(ShadowError::UnsupportedExpression {
                kind: SyntaxKind::StringLiteral,
                ..
            })
        ));
        assert_eq!(artifact.source(), source);
    }

    #[test]
    fn private_reference_validation_rejects_missing_foreign_and_cyclic_ids() {
        let mut first = ShadowArtifact::from_parsed(parsed("my compose f g x = f (g x)"))
            .unwrap()
            .into_skeleton()
            .unwrap();
        let second = ShadowArtifact::from_parsed(parsed("my compose f g x = f (g x)"))
            .unwrap()
            .into_skeleton()
            .unwrap();
        assert_eq!(
            first
                .expression(&ExprId(first.id(first.expressions.len())))
                .unwrap_err(),
            ShadowError::MissingReference {
                index: first.expressions.len()
            }
        );
        let index = first.uses[0].0.index;
        let Form::Use { binder, .. } = &mut first.expressions[index].form else {
            panic!("use")
        };
        *binder = BinderId(second.id(0));
        assert_eq!(first.validate(), Err(ShadowError::ForeignArtifact));
        let local_binder = BinderId(first.id(0));
        let Form::Use { binder, occurrence } = &mut first.expressions[index].form else {
            panic!("use")
        };
        *binder = local_binder;
        *occurrence = UseId(second.id(0));
        assert_eq!(first.validate(), Err(ShadowError::ForeignArtifact));
        let local_occurrence = UseId(first.id(0));
        let Form::Use { occurrence, .. } = &mut first.expressions[index].form else {
            panic!("use")
        };
        *occurrence = local_occurrence;
        first.validate().unwrap();
        let body = first.body.clone();
        let Form::Apply { argument, .. } = &mut first.expressions[body.0.index].form else {
            panic!("Apply")
        };
        *argument = body;
        assert_eq!(
            first.validate(),
            Err(ShadowError::InvalidExpressionReference)
        );
    }

    #[test]
    fn raw_reference_validation_rejects_missing_and_foreign_positions() {
        let first = ShadowArtifact::from_parsed(parsed("x as int")).unwrap();
        let second = ShadowArtifact::from_parsed(parsed("x as int")).unwrap();
        assert_eq!(
            first
                .position(&first.position_id(first.positions.len()))
                .unwrap_err(),
            ShadowError::MissingReference {
                index: first.positions.len()
            }
        );
        assert_eq!(
            first.position(&second.root()).unwrap_err(),
            ShadowError::ForeignArtifact
        );
    }

    #[test]
    fn failed_narrow_build_keeps_the_complete_raw_snapshot() {
        let source = "my compose f g x = f (g missing)";
        let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
        assert!(
            matches!(artifact.skeleton(), Err(ShadowError::UnboundName { range }) if *range == (24..31))
        );
        assert_eq!(artifact.source(), source);
        assert_eq!(
            *artifact.position(&artifact.root()).unwrap().range(),
            0..source.len()
        );
    }
}
