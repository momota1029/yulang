//! Opt-in immutable source artifact. Syntax provenance carries no type or role judgment.
use crate::{range_of, range_of_token};
use std::{
    collections::{BTreeMap, BTreeSet},
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
        artifact.retain(root);
        artifact.skeleton = build_skeleton(&artifact.parsed, identity);
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
    fn retain(&mut self, root: SyntaxNode) {
        let mut stack = vec![(RawElement::Node(root), None, 0)];
        while let Some((element, parent, ordinal)) = stack.pop() {
            let id = self.position_id(self.positions.len());
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

#[derive(Debug)]
pub struct Binder {
    pub(crate) name: String,
    pub(crate) range: Range<usize>,
}

#[derive(Debug)]
pub struct Expression {
    pub(crate) range: Range<usize>,
    pub(crate) form: Form,
}

#[derive(Debug)]
pub enum Form {
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

fn build_skeleton(parsed: &ParsedFile, identity: Arc<()>) -> Result<Skeleton, ShadowError> {
    let source = parsed.source();
    let root = SyntaxNode::new_root(parsed.green().clone());
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
        binders.push(Binder { name, range });
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
        pending: Vec::new(),
    };
    artifact.body = artifact.project(chain, source)?;
    artifact.validate()?;
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
        for pending in &self.pending {
            if !matches!(self.expression(&pending.call)?.form, Form::Apply { .. }) {
                return Err(ShadowError::InvalidCallReference);
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
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
}
impl Expression {
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
    fn push_expression(&mut self, range: Range<usize>, form: Form) -> ExprId {
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
        self.expressions.push(Expression { range, form });
        id
    }
    fn project(&mut self, root: SyntaxNode, source: &str) -> Result<ExprId, ShadowError> {
        // Tasks/results hold IDs and CST handles, never recursively owned expressions.
        enum Task {
            Visit(SyntaxNode),
            Group(Range<usize>),
            Chain(Vec<(SyntaxKind, Range<usize>)>),
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
                Task::Visit(node) => match node.kind() {
                    SyntaxKind::IdentifierExpression => {
                        if node.children().next().is_some() {
                            return Err(unsupported(&node));
                        }
                        let range = range_of(&node);
                        let name =
                            source
                                .get(range.clone())
                                .ok_or_else(|| ShadowError::InvalidRange {
                                    range: range.clone(),
                                })?;
                        let index =
                            names
                                .get(name)
                                .copied()
                                .ok_or_else(|| ShadowError::UnboundName {
                                    range: range.clone(),
                                })?;
                        let occurrence = UseId(self.id(self.uses.len()));
                        let binder = BinderId(self.id(index));
                        results.push(self.push_expression(range, Form::Use { binder, occurrence }));
                    }
                    SyntaxKind::ParenthesizedExpression => {
                        let inner = nested_chain(&node)?;
                        tasks.push(Task::Group(range_of(&node)));
                        tasks.push(Task::Visit(inner));
                    }
                    SyntaxKind::OperatorChain => {
                        let children = node.children().collect::<Vec<_>>();
                        let Some((first, tails)) = children.split_first() else {
                            return Err(unsupported(&node));
                        };
                        if !matches!(
                            first.kind(),
                            SyntaxKind::IdentifierExpression | SyntaxKind::ParenthesizedExpression
                        ) {
                            return Err(unsupported(first));
                        }
                        let mut arguments = Vec::new();
                        let mut forms = Vec::new();
                        for tail in tails {
                            if !matches!(tail.kind(), SyntaxKind::MlArgument | SyntaxKind::CallTail)
                            {
                                return Err(unsupported(tail));
                            }
                            arguments.push(nested_chain(tail)?);
                            forms.push((tail.kind(), range_of(tail)));
                        }
                        tasks.push(Task::Chain(forms));
                        for argument in arguments.into_iter().rev() {
                            tasks.push(Task::Visit(argument));
                        }
                        tasks.push(Task::Visit(first.clone()));
                    }
                    _ => return Err(unsupported(&node)),
                },
                Task::Group(range) => {
                    let inner = results.pop().ok_or(ShadowError::MalformedSource)?;
                    results.push(self.push_expression(range, Form::Group { inner }));
                }
                Task::Chain(forms) => {
                    let start = results
                        .len()
                        .checked_sub(forms.len() + 1)
                        .ok_or(ShadowError::MalformedSource)?;
                    let operands = results.split_off(start);
                    let mut operands = operands.into_iter();
                    let mut callee = operands.next().ok_or(ShadowError::MalformedSource)?;
                    for ((source_form, tail_range), argument) in forms.into_iter().zip(operands) {
                        let range = self.expression(&callee)?.range.start.min(tail_range.start)
                            ..self.expression(&callee)?.range.end.max(tail_range.end);
                        callee = self.push_expression(
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
        let mut skeleton = ShadowArtifact::from_parsed(parsed)
            .unwrap()
            .into_skeleton()
            .unwrap();
        skeleton.expressions.clear();
        skeleton.uses.clear();
        skeleton.pending.clear();
        skeleton.body = skeleton.project(synthetic, &source).unwrap();
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
        let source = "my constant x = 1";
        let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
        assert!(matches!(
            artifact.skeleton(),
            Err(ShadowError::UnsupportedExpression {
                kind: SyntaxKind::IntegerLiteral,
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
