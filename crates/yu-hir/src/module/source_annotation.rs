//! Source-owned nullary effect declarations and complete binding annotations.
use super::*;
use yu_syntax::SourceNodeKey;
enum SyntaxElement {
    Node(SyntaxNode),
    Token(yu_syntax::SyntaxToken),
}
impl SyntaxElement {
    fn kind(&self) -> SyntaxKind {
        match self {
            Self::Node(node) => node.kind(),
            Self::Token(token) => token.kind(),
        }
    }
    fn as_node(&self) -> Option<&SyntaxNode> {
        match self {
            Self::Node(node) => Some(node),
            _ => None,
        }
    }
}
impl std::fmt::Display for SyntaxElement {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Node(node) => write!(out, "{node}"),
            Self::Token(token) => write!(out, "{token}"),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SourceEffectId {
    pub module: Arc<ModuleId>,
    pub declaration: SourceNodeKey,
}
#[derive(Clone, Debug)]
pub struct SourceEffectDeclaration {
    pub id: SourceEffectId,
    pub spelling: Box<str>,
    pub range: Range<usize>,
    pub visibility: HirVisibility,
    pub operations: Vec<Arc<SourceOperationDeclaration>>,
    pub placeholder_errors: Vec<HirErrorId>,
}
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SourceOperationId {
    pub family: SourceEffectId,
    pub declaration: SourceNodeKey,
}
#[derive(Clone, Debug)]
pub struct SourceOperationDeclaration {
    pub id: SourceOperationId,
    pub spelling: Box<str>,
    pub visibility: HirVisibility,
    pub name_position: SourceNodeKey,
    pub signature_position: SourceNodeKey,
    pub range: Range<usize>,
    pub signature: SourceAnnotationType,
}
#[derive(Clone, Debug)]
pub enum SourceOperationResolution {
    Resolved(Arc<SourceOperationDeclaration>),
    Unresolved,
    Ambiguous,
    Private,
}
#[derive(Clone, Debug)]
pub struct SourceAnnotation {
    pub owner: DefinitionRootId,
    pub position: SourceNodeKey,
    pub ty: SourceAnnotationType,
}
#[derive(Clone, Debug)]
pub struct SourceAnnotationType {
    pub effects: Option<SourceEffectRow>,
    pub value: SourceAnnotationValue,
}
#[derive(Clone, Debug)]
pub enum SourceAnnotationValue {
    Unit,
    Int,
    Variable(Box<str>),
    Function {
        argument: Box<SourceAnnotationType>,
        result: Box<SourceAnnotationType>,
    },
}
#[derive(Clone, Debug)]
pub struct SourceEffectRow {
    pub position: SourceNodeKey,
    pub concrete: Vec<SourceEffectId>,
    pub variables: Vec<Box<str>>,
}
fn unavailable() -> HirAvailabilityError {
    HirAvailabilityError::StructuralProjection
}
fn trivia(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Whitespace
            | SyntaxKind::Newline
            | SyntaxKind::LineComment
            | SyntaxKind::BlockComment
    )
}
fn elements(node: &SyntaxNode) -> Vec<SyntaxElement> {
    node.children_with_tokens()
        .filter(|element| !trivia(element.kind()))
        .map(|element| {
            if let Some(node) = element.as_node() {
                SyntaxElement::Node(node.clone())
            } else {
                SyntaxElement::Token(element.into_token().expect("token"))
            }
        })
        .collect()
}
fn singleton_identifier(node: &SyntaxNode) -> Option<String> {
    let elements = elements(node);
    let [token] = elements.as_slice() else {
        return None;
    };
    (token.kind() == SyntaxKind::Identifier).then(|| token.to_string())
}
pub(super) fn declarations(
    root: &SyntaxNode,
    module: &ModuleId,
    counters: &mut LoweringCounters,
) -> Result<Vec<SourceEffectDeclaration>, HirAvailabilityError> {
    let mut result = Vec::new();
    let mut bodies = Vec::new();
    for node in root
        .children()
        .filter(|node| node.kind() == SyntaxKind::ActDeclaration)
    {
        if has_recovery(&node) {
            return Err(unavailable());
        }
        let mut children = elements(&node);
        children.retain(|element| element.kind() != SyntaxKind::Semicolon);
        let visibility = match children.first().map(SyntaxElement::kind) {
            Some(SyntaxKind::MyKw) => {
                children.remove(0);
                HirVisibility::Private
            }
            Some(SyntaxKind::OurKw) => {
                children.remove(0);
                HirVisibility::Our
            }
            Some(SyntaxKind::PubKw) => {
                children.remove(0);
                HirVisibility::Public
            }
            _ => HirVisibility::Our,
        };
        if children.len() < 2
            || children[0].kind() != SyntaxKind::ActKw
            || children[1].kind() != SyntaxKind::TypeExpression
        {
            return Err(unavailable());
        }
        let spelling = singleton_identifier(children[1].as_node().ok_or_else(unavailable)?)
            .ok_or_else(unavailable)?;
        let body = match &children[2..] {
            [] => None,
            [colon, body]
                if colon.kind() == SyntaxKind::Colon
                    && body.kind() == SyntaxKind::IndentedStatementBlock =>
            {
                Some(body.as_node().ok_or_else(unavailable)?.clone())
            }
            [body] if body.kind() == SyntaxKind::BracedStatementBlockExpression => {
                Some(body.as_node().ok_or_else(unavailable)?.clone())
            }
            _ => return Err(unavailable()),
        };
        result
            .try_reserve(1)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        bodies
            .try_reserve(1)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        let id = SourceEffectId {
            module: Arc::new(module.clone()),
            declaration: counters
                .source_nodes
                .get(&node)
                .ok_or_else(unavailable)?
                .clone(),
        };
        counters
            .effect_namespace
            .try_reserve(1)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        let families = counters
            .effect_namespace
            .entry(spelling.clone())
            .or_default();
        families
            .try_reserve(1)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        families.push(id.clone());
        result.push(SourceEffectDeclaration {
            id,
            spelling: spelling.into_boxed_str(),
            range: range_of(&node),
            visibility,
            operations: Vec::new(),
            placeholder_errors: Vec::new(),
        });
        bodies.push(body);
    }
    // All family headers exist before any signature row is resolved.
    for (family, body) in result.iter_mut().zip(bodies) {
        let Some(body) = body else {
            continue;
        };
        for element in elements(&body) {
            match element.kind() {
                SyntaxKind::LBrace | SyntaxKind::RBrace | SyntaxKind::Semicolon => continue,
                SyntaxKind::BlockStatementSeparator => continue,
                SyntaxKind::Statement => {}
                _ => return Err(unavailable()),
            }
            let statement = element.as_node().ok_or_else(unavailable)?;
            let mut children = statement.children();
            let member = children.next().ok_or_else(unavailable)?;
            if children.next().is_some()
                || member.kind() != SyntaxKind::BindingStatement
                || member
                    .children()
                    .any(|n| n.kind() == SyntaxKind::BindingBody)
            {
                return Err(unavailable());
            }
            let (visibility, name, parameters) =
                plain_binding_header(&member, counters).ok_or_else(unavailable)?;
            if !parameters.is_empty() {
                return Err(unavailable());
            }
            let annotation = member
                .descendants()
                .find(|n| n.kind() == SyntaxKind::PatternTypeAnnotation)
                .ok_or_else(unavailable)?;
            let parts = elements(&annotation);
            let [colon, ty] = parts.as_slice() else {
                return Err(unavailable());
            };
            if colon.kind() != SyntaxKind::Colon || ty.kind() != SyntaxKind::TypeExpression {
                return Err(unavailable());
            }
            let ty = ty.as_node().ok_or_else(unavailable)?;
            annotation_depth_preflight(ty)?;
            let signature = parse_type(ty, counters)?;
            if !matches!(signature.value, SourceAnnotationValue::Function { .. }) {
                return Err(unavailable());
            }
            let name_node = member
                .descendants()
                .find(|n| n.kind() == SyntaxKind::IdentifierPattern)
                .ok_or_else(unavailable)?;
            let declaration = Arc::new(SourceOperationDeclaration {
                id: SourceOperationId {
                    family: family.id.clone(),
                    declaration: counters
                        .source_nodes
                        .get(&member)
                        .ok_or_else(unavailable)?
                        .clone(),
                },
                spelling: name.spelling.into_boxed_str(),
                visibility,
                name_position: counters
                    .source_nodes
                    .get(&name_node)
                    .ok_or_else(unavailable)?
                    .clone(),
                signature_position: counters
                    .source_nodes
                    .get(ty)
                    .ok_or_else(unavailable)?
                    .clone(),
                range: range_of(&member),
                signature,
            });
            counters
                .operation_namespace
                .try_reserve(1)
                .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            let members = counters
                .operation_namespace
                .entry((family.id.clone(), declaration.spelling.clone()))
                .or_default();
            members
                .try_reserve(1)
                .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            members.push(declaration.clone());
            family
                .operations
                .try_reserve(1)
                .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
            family.operations.push(declaration);
        }
    }
    Ok(result)
}
pub(super) fn form(
    statement: &SyntaxNode,
    owner: &DefinitionRootId,
    counters: &LoweringCounters,
) -> Result<Option<SourceAnnotation>, HirAvailabilityError> {
    let header = statement
        .children()
        .find(|node| node.kind() == SyntaxKind::BindingHeader)
        .ok_or_else(unavailable)?;
    let pattern = header
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .ok_or_else(unavailable)?;
    let annotations: Vec<_> = pattern
        .children()
        .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
        .collect();
    if annotations.is_empty() {
        return Ok(None);
    }
    let [annotation] = annotations.as_slice() else {
        return Err(unavailable());
    };
    parse_annotation(annotation, owner, counters).map(Some)
}
pub(super) fn parse_annotation(
    annotation: &SyntaxNode,
    owner: &DefinitionRootId,
    counters: &LoweringCounters,
) -> Result<SourceAnnotation, HirAvailabilityError> {
    if has_recovery(annotation) {
        return Err(unavailable());
    }
    let children = elements(annotation);
    let [colon, ty] = children.as_slice() else {
        return Err(unavailable());
    };
    if colon.kind() != SyntaxKind::Colon || ty.kind() != SyntaxKind::TypeExpression {
        return Err(unavailable());
    }
    let ty = ty.as_node().ok_or_else(unavailable)?;
    annotation_depth_preflight(ty)?;
    Ok(SourceAnnotation {
        owner: owner.clone(),
        position: counters
            .source_nodes
            .get(annotation)
            .ok_or_else(unavailable)?
            .clone(),
        ty: parse_type(ty, counters)?,
    })
}
// Root TypeExpression has depth one. Each parenthesized-inner or arrow-result
// parse_type transition adds one; wrappers and row atoms add no extra depth.
fn annotation_depth_preflight(root: &SyntaxNode) -> Result<usize, HirAvailabilityError> {
    let mut work = vec![(root.clone(), 1usize)];
    let mut visits = 0usize;
    while let Some((node, depth)) = work.pop() {
        if depth > 128 {
            return Err(unavailable());
        }
        visits += 1;
        let recursive_child = matches!(
            node.kind(),
            SyntaxKind::ParenthesizedTypeGroup | SyntaxKind::TypeArrowTail
        );
        for child in node.children() {
            let child_depth =
                depth + usize::from(recursive_child && child.kind() == SyntaxKind::TypeExpression);
            work.push((child, child_depth));
        }
    }
    Ok(visits)
}
fn parse_type(
    node: &SyntaxNode,
    counters: &LoweringCounters,
) -> Result<SourceAnnotationType, HirAvailabilityError> {
    let mut children = elements(node);
    let effects = if children
        .first()
        .is_some_and(|child| child.kind() == SyntaxKind::BracketRow)
    {
        let first = children.remove(0);
        Some(parse_row(
            first.as_node().ok_or_else(unavailable)?,
            counters,
        )?)
    } else {
        None
    };
    let value = match children.as_slice() {
        [identifier]
            if identifier.kind() == SyntaxKind::Identifier && identifier.to_string() == "int" =>
        {
            SourceAnnotationValue::Int
        }
        [variable] if variable.kind() == SyntaxKind::SigilIdentifier => {
            SourceAnnotationValue::Variable(variable.to_string().trim().to_owned().into_boxed_str())
        }
        [group] if group.kind() == SyntaxKind::ParenthesizedTypeGroup => {
            let group = group.as_node().ok_or_else(unavailable)?;
            let nested = parse_group(group, counters)?;
            if effects.is_some() && nested.effects.is_some() {
                return Err(unavailable());
            }
            return Ok(SourceAnnotationType {
                effects: effects.or(nested.effects),
                value: nested.value,
            });
        }
        [head, arrow] if arrow.kind() == SyntaxKind::TypeArrowTail => {
            let argument = match head.kind() {
                SyntaxKind::Identifier if head.to_string() == "int" => SourceAnnotationType {
                    effects,
                    value: SourceAnnotationValue::Int,
                },
                SyntaxKind::SigilIdentifier => SourceAnnotationType {
                    effects,
                    value: SourceAnnotationValue::Variable(
                        head.to_string().trim().to_owned().into_boxed_str(),
                    ),
                },
                SyntaxKind::ParenthesizedTypeGroup => {
                    let node = head.as_node().ok_or_else(unavailable)?;
                    let mut ty = parse_group(node, counters)?;
                    if effects.is_some() && ty.effects.is_some() {
                        return Err(unavailable());
                    }
                    ty.effects = effects.or(ty.effects);
                    ty
                }
                _ => return Err(unavailable()),
            };
            let arrow = elements(arrow.as_node().ok_or_else(unavailable)?);
            let [token, result] = arrow.as_slice() else {
                return Err(unavailable());
            };
            if token.kind() != SyntaxKind::Arrow || result.kind() != SyntaxKind::TypeExpression {
                return Err(unavailable());
            }
            return Ok(SourceAnnotationType {
                effects: None,
                value: SourceAnnotationValue::Function {
                    argument: Box::new(argument),
                    result: Box::new(parse_type(
                        result.as_node().ok_or_else(unavailable)?,
                        counters,
                    )?),
                },
            });
        }
        _ => return Err(unavailable()),
    };
    Ok(SourceAnnotationType { effects, value })
}
fn parse_group(
    node: &SyntaxNode,
    counters: &LoweringCounters,
) -> Result<SourceAnnotationType, HirAvailabilityError> {
    let children = elements(node);
    match children.as_slice() {
        [open, close]
            if open.kind() == SyntaxKind::LParen && close.kind() == SyntaxKind::RParen =>
        {
            Ok(SourceAnnotationType {
                effects: None,
                value: SourceAnnotationValue::Unit,
            })
        }
        [open, inner, close]
            if open.kind() == SyntaxKind::LParen
                && inner.kind() == SyntaxKind::TypeExpression
                && close.kind() == SyntaxKind::RParen =>
        {
            parse_type(inner.as_node().ok_or_else(unavailable)?, counters)
        }
        _ => Err(unavailable()),
    }
}
fn parse_row(
    node: &SyntaxNode,
    counters: &LoweringCounters,
) -> Result<SourceEffectRow, HirAvailabilityError> {
    let mut result = SourceEffectRow {
        position: counters
            .source_nodes
            .get(node)
            .ok_or_else(unavailable)?
            .clone(),
        concrete: Vec::new(),
        variables: Vec::new(),
    };
    for element in elements(node) {
        match element.kind() {
            SyntaxKind::LBracket
            | SyntaxKind::RBracket
            | SyntaxKind::Comma
            | SyntaxKind::Semicolon
            | SyntaxKind::Pipe => {}
            SyntaxKind::TypeExpression => {
                let operand = elements(element.as_node().ok_or_else(unavailable)?);
                let [operand] = operand.as_slice() else {
                    return Err(unavailable());
                };
                if operand.kind() == SyntaxKind::SigilIdentifier {
                    result
                        .variables
                        .try_reserve(1)
                        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                    result
                        .variables
                        .push(operand.to_string().trim().to_owned().into_boxed_str());
                } else if operand.kind() == SyntaxKind::Identifier {
                    let spelling = operand.to_string();
                    let declarations = counters
                        .effect_namespace
                        .get(&spelling)
                        .ok_or_else(unavailable)?;
                    let [declaration] = declarations.as_slice() else {
                        return Err(unavailable());
                    };
                    result
                        .concrete
                        .try_reserve(1)
                        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                    result.concrete.push(declaration.clone());
                } else {
                    return Err(unavailable());
                }
            }
            _ => return Err(unavailable()),
        }
    }
    if result.variables.len() > 1 {
        return Err(unavailable());
    }
    Ok(result)
}

impl SourceOperationDeclaration {
    /// Retained spelling and signature arena storage; the record itself,
    /// shared module/source identity payloads and allocator overhead are excluded.
    pub fn retained_arena_bytes(&self) -> usize {
        self.spelling.len() + self.signature.retained_arena_bytes()
    }
}

impl SourceAnnotation {
    pub fn retained_arena_bytes(&self) -> usize {
        self.ty.retained_arena_bytes()
    }
}
impl SourceAnnotationType {
    pub fn node_count(&self) -> usize {
        1 + match &self.value {
            SourceAnnotationValue::Function { argument, result } => {
                argument.node_count() + result.node_count()
            }
            _ => 0,
        }
    }
    fn retained_arena_bytes(&self) -> usize {
        let effects = self.effects.as_ref().map_or(0, |row| {
            row.concrete.capacity() * std::mem::size_of::<SourceEffectId>()
                + row.variables.capacity() * std::mem::size_of::<Box<str>>()
                + row.variables.iter().map(|name| name.len()).sum::<usize>()
        });
        effects
            + match &self.value {
                SourceAnnotationValue::Variable(name) => name.len(),
                SourceAnnotationValue::Function { argument, result } => {
                    2 * std::mem::size_of::<SourceAnnotationType>()
                        + argument.retained_arena_bytes()
                        + result.retained_arena_bytes()
                }
                _ => 0,
            }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn annotation_type(text: &str) -> SyntaxNode {
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        assert!(parsed.structural_recoveries().is_empty());
        parsed
            .source_root()
            .syntax()
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
            .unwrap()
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeExpression)
            .unwrap()
    }
    #[test]
    fn empty_type_groups_form_unit_in_standalone_and_function_annotations() {
        let counters = LoweringCounters::default();
        for text in ["my value: () = ()", "my value: (()) = ()"] {
            let node = annotation_type(text);
            annotation_depth_preflight(&node).unwrap();
            let ty = parse_type(&node, &counters).unwrap();
            assert!(matches!(ty.value, SourceAnnotationValue::Unit));
            assert_eq!(ty.node_count(), 1);
        }
        let node = annotation_type("my value: () -> () = 1");
        let ty = parse_type(&node, &counters).unwrap();
        assert_eq!(ty.node_count(), 3);
        let SourceAnnotationValue::Function { argument, result } = ty.value else {
            panic!("expected function annotation");
        };
        assert!(matches!(argument.value, SourceAnnotationValue::Unit));
        assert!(matches!(result.value, SourceAnnotationValue::Unit));
        for text in ["my value: (int,) = 1", "my value: (int, int) = 1"] {
            let node = annotation_type(text);
            assert!(matches!(
                parse_type(&node, &counters),
                Err(HirAvailabilityError::StructuralProjection)
            ));
        }
    }
    #[test]
    fn annotation_preflight_visits_once_and_bounds_group_and_arrow_transitions() {
        // This checks the HIR guard on a parsed artifact, not default parser stack safety.
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                for depth in [1, 64, 128, 129] {
                    for ty in [
                        format!("{}int{}", "(".repeat(depth - 1), ")".repeat(depth - 1)),
                        format!("{}int", "int -> ".repeat(depth - 1)),
                    ] {
                        let node = annotation_type(&format!("my value: {ty} = 1"));
                        if depth <= 128 {
                            assert_eq!(
                                annotation_depth_preflight(&node).unwrap(),
                                node.descendants().count()
                            );
                        } else {
                            assert_eq!(
                                annotation_depth_preflight(&node),
                                Err(HirAvailabilityError::StructuralProjection)
                            );
                        }
                    }
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
