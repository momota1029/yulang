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
    pub placeholder_errors: Vec<HirErrorId>,
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
    keys: &HashMap<SyntaxNode, SourceNodeKey>,
) -> Result<Vec<SourceEffectDeclaration>, HirAvailabilityError> {
    let mut result = Vec::new();
    for node in root
        .children()
        .filter(|node| node.kind() == SyntaxKind::ActDeclaration)
    {
        if has_recovery(&node) {
            return Err(unavailable());
        }
        let children: Vec<_> = elements(&node)
            .into_iter()
            .filter(|element| element.kind() != SyntaxKind::Semicolon)
            .collect();
        let [keyword, head] = children.as_slice() else {
            return Err(unavailable());
        };
        if keyword.kind() != SyntaxKind::ActKw || head.kind() != SyntaxKind::TypeExpression {
            return Err(unavailable());
        }
        let head = head.as_node().ok_or_else(unavailable)?;
        let spelling = singleton_identifier(head).ok_or_else(unavailable)?;
        result
            .try_reserve(1)
            .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
        result.push(SourceEffectDeclaration {
            id: SourceEffectId {
                module: Arc::new(module.clone()),
                declaration: keys.get(&node).ok_or_else(unavailable)?.clone(),
            },
            spelling: spelling.into_boxed_str(),
            range: range_of(&node),
            placeholder_errors: Vec::new(),
        });
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
    Ok(Some(SourceAnnotation {
        owner: owner.clone(),
        position: counters
            .source_nodes
            .get(annotation)
            .ok_or_else(unavailable)?
            .clone(),
        ty: parse_type(ty, counters)?,
    }))
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
            let inner = group.children().collect::<Vec<_>>();
            let [inner] = inner.as_slice() else {
                return Err(unavailable());
            };
            let nested = parse_type(inner, counters)?;
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
                    let inner = node.children().collect::<Vec<_>>();
                    let [inner] = inner.as_slice() else {
                        return Err(unavailable());
                    };
                    let mut ty = parse_type(inner, counters)?;
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
                    let mut matches = counters
                        .effect_declarations
                        .iter()
                        .filter(|declaration| declaration.spelling.as_ref() == spelling);
                    let declaration = matches.next().ok_or_else(unavailable)?;
                    if matches.next().is_some() {
                        return Err(unavailable());
                    }
                    result
                        .concrete
                        .try_reserve(1)
                        .map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                    result.concrete.push(declaration.id.clone());
                } else {
                    return Err(unavailable());
                }
            }
            _ => return Err(unavailable()),
        }
    }
    Ok(result)
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
