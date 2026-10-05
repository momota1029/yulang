//! Detached raw-CST annotation retention experiment. No typed elaboration is
//! performed; remove this module and its declaration to roll it back.

use super::*;

#[derive(Clone)]
enum RawElement {
    Node(SyntaxNode),
    Token(SyntaxToken),
}

impl From<SyntaxNode> for RawElement {
    fn from(node: SyntaxNode) -> Self {
        Self::Node(node)
    }
}

impl RawElement {
    fn as_node(&self) -> Option<&SyntaxNode> {
        match self {
            Self::Node(node) => Some(node),
            Self::Token(_) => None,
        }
    }
    fn kind(&self) -> SyntaxKind {
        match self {
            Self::Node(node) => node.kind(),
            Self::Token(token) => token.kind(),
        }
    }
    fn range(&self) -> Range<usize> {
        let range = match self {
            Self::Node(node) => node.text_range(),
            Self::Token(token) => token.text_range(),
        };
        usize::from(range.start())..usize::from(range.end())
    }
    fn text(&self) -> String {
        match self {
            Self::Node(node) => node.to_string(),
            Self::Token(token) => token.to_string(),
        }
    }
    fn children(&self) -> Vec<Self> {
        self.as_node()
            .map(|node| {
                node.children_with_tokens()
                    .map(|child| {
                        if let Some(node) = child.as_node() {
                            Self::Node(node.clone())
                        } else {
                            Self::Token(child.into_token().unwrap())
                        }
                    })
                    .collect()
            })
            .unwrap_or_default()
    }
}

#[derive(Clone, Debug)]
struct PositionId {
    artifact: Arc<()>,
    index: usize,
}

impl PartialEq for PositionId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.artifact, &other.artifact) && self.index == other.index
    }
}

impl Eq for PositionId {}

#[derive(Debug)]
struct Position {
    kind: SyntaxKind,
    range: Range<usize>,
    is_node: bool,
    // Ordinals count all raw children, including trivia and punctuation.
    path: Vec<usize>,
    parent: Option<PositionId>,
    children: Vec<PositionId>,
}

#[derive(Debug, Eq, PartialEq)]
enum Correspondence {
    PendingTypedPortAndProfile,
}

#[derive(Debug)]
struct AnnotationOccurrence {
    position: PositionId,
    correspondence: Correspondence,
}

#[derive(Debug)]
struct AnnotationArtifact {
    identity: Arc<()>,
    source: String,
    positions: Vec<Position>,
    annotations: Vec<AnnotationOccurrence>,
}

impl AnnotationArtifact {
    fn id(&self, index: usize) -> PositionId {
        PositionId {
            artifact: self.identity.clone(),
            index,
        }
    }

    fn position(&self, id: &PositionId) -> Result<&Position, &'static str> {
        if !Arc::ptr_eq(&self.identity, &id.artifact) {
            return Err("foreign artifact");
        }
        self.positions.get(id.index).ok_or("missing position")
    }

    fn retain(
        &mut self,
        element: RawElement,
        parent: Option<PositionId>,
        path: Vec<usize>,
    ) -> PositionId {
        let id = self.id(self.positions.len());
        let range = element.range();
        self.positions.push(Position {
            kind: element.kind(),
            range,
            is_node: element.as_node().is_some(),
            path: path.clone(),
            parent,
            children: Vec::new(),
        });
        if matches!(
            element.kind(),
            SyntaxKind::PatternTypeAnnotation | SyntaxKind::TypeAnnotationTail
        ) {
            self.annotations.push(AnnotationOccurrence {
                position: id.clone(),
                correspondence: Correspondence::PendingTypedPortAndProfile,
            });
        }
        if element.as_node().is_some() {
            for (ordinal, child) in element.children().into_iter().enumerate() {
                let mut child_path = path.clone();
                child_path.push(ordinal);
                let child = self.retain(child, Some(id.clone()), child_path);
                self.positions[id.index].children.push(child);
            }
        }
        id
    }

    fn from_source(source: &str) -> Result<Self, &'static str> {
        let parsed = parsed(source);
        if !parsed
            .syntax_diagnostics()
            .map_err(|_| "unavailable diagnostics")?
            .is_empty()
        {
            return Err("parser diagnostics");
        }
        let root = SyntaxNode::new_root(parsed.green().clone());
        let mut artifact = Self {
            identity: Arc::new(()),
            source: source.into(),
            positions: Vec::new(),
            annotations: Vec::new(),
        };
        artifact.retain(root.into(), None, Vec::new());
        Ok(artifact)
    }
}

fn assert_whole_tree(artifact: &AnnotationArtifact) {
    let parsed = parsed(&artifact.source);
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    let root = SyntaxNode::new_root(parsed.green().clone());
    fn compare(
        artifact: &AnnotationArtifact,
        id: &PositionId,
        raw: RawElement,
        path: Vec<usize>,
        parent: Option<PositionId>,
    ) {
        let retained = artifact.position(id).unwrap();
        assert_eq!(retained.kind, raw.kind());
        assert_eq!(retained.is_node, raw.as_node().is_some());
        assert_eq!(retained.range, raw.range());
        assert_eq!(retained.path, path);
        assert_eq!(retained.parent, parent);
        assert_eq!(&artifact.source[retained.range.clone()], raw.text());
        let children = raw.children();
        assert_eq!(retained.children.len(), children.len());
        for (ordinal, (id_child, raw_child)) in retained.children.iter().zip(children).enumerate() {
            let mut child_path = path.clone();
            child_path.push(ordinal);
            compare(artifact, id_child, raw_child, child_path, Some(id.clone()));
        }
    }
    compare(artifact, &artifact.id(0), root.into(), Vec::new(), None);
    assert_eq!(artifact.positions[0].range, 0..artifact.source.len());
    let leaves = artifact
        .positions
        .iter()
        .filter(|p| !p.is_node)
        .map(|p| &artifact.source[p.range.clone()])
        .collect::<String>();
    assert_eq!(leaves, artifact.source);
}

#[test]
fn shadow_annotation_positions_preserves_whole_tree_and_distinct_row_owners() {
    // Type fixture: yu-syntax/tests/type_expr/leading_row_cst.rs. The body is
    // the already accepted compose skeleton, retained without interpreting it.
    let source = "my x: [e] F [io] -> U = f (g x)";
    assert!(parsed(source).syntax_diagnostics().unwrap().is_empty());
    let artifact = AnnotationArtifact::from_source(source).unwrap();
    assert_whole_tree(&artifact);
    assert_eq!(artifact.annotations.len(), 1);
    assert_eq!(
        artifact.annotations[0].correspondence,
        Correspondence::PendingTypedPortAndProfile
    );
    let annotation = artifact
        .position(&artifact.annotations[0].position)
        .unwrap();
    assert_eq!(annotation.kind, SyntaxKind::PatternTypeAnnotation);
    let rows = artifact
        .positions
        .iter()
        .filter(|p| p.kind == SyntaxKind::BracketRow)
        .collect::<Vec<_>>();
    assert_eq!(rows.len(), 2);
    assert_eq!(
        artifact
            .position(rows[0].parent.as_ref().unwrap())
            .unwrap()
            .kind,
        SyntaxKind::TypeExpression
    );
    assert_eq!(
        artifact
            .position(rows[1].parent.as_ref().unwrap())
            .unwrap()
            .kind,
        SyntaxKind::TypeArrowTail
    );
    assert_ne!(rows[0].path, rows[1].path);
    let calls = artifact
        .positions
        .iter()
        .filter(|p| p.kind == SyntaxKind::MlArgument)
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 2);
    assert_ne!(calls[0].path, calls[1].path);
}

#[test]
fn shadow_annotation_positions_brands_same_spelling_and_foreign_artifacts() {
    // Repeated expression annotations reuse an accepted syntax test fixture.
    let source = "x as int; x as int";
    assert!(parsed(source).syntax_diagnostics().unwrap().is_empty());
    let first = AnnotationArtifact::from_source(source).unwrap();
    let second = AnnotationArtifact::from_source(source).unwrap();
    assert_whole_tree(&first);
    assert_eq!(first.annotations.len(), 2);
    assert_ne!(first.annotations[0].position, first.annotations[1].position);
    let repeated = first
        .positions
        .iter()
        .enumerate()
        .filter(|(_, p)| !p.is_node && &first.source[p.range.clone()] == "int")
        .collect::<Vec<_>>();
    assert_eq!(repeated.len(), 2);
    assert_ne!(first.id(repeated[0].0), first.id(repeated[1].0));
    assert_ne!(repeated[0].1.path, repeated[1].1.path);
    assert_eq!(
        first.position(&second.annotations[0].position).unwrap_err(),
        "foreign artifact"
    );
    assert_ne!(
        first.annotations[0].position,
        second.annotations[0].position
    );
    assert_eq!(
        first
            .position(&first.id(first.positions.len()))
            .unwrap_err(),
        "missing position"
    );
}

#[test]
fn shadow_annotation_positions_preserves_siblings_trivia_and_rejects_diagnostics() {
    let source = " \nmy x: T = value; my y: T = value\n ";
    assert!(parsed(source).syntax_diagnostics().unwrap().is_empty());
    let artifact = AnnotationArtifact::from_source(source).unwrap();
    assert_whole_tree(&artifact);
    assert_eq!(artifact.annotations.len(), 2);
    assert_eq!(
        artifact
            .positions
            .iter()
            .filter(|p| p.kind == SyntaxKind::BindingStatement)
            .count(),
        2
    );
    assert_eq!(
        AnnotationArtifact::from_source("my x: = value").unwrap_err(),
        "parser diagnostics"
    );
}
