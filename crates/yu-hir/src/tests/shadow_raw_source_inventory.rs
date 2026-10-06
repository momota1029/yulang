//! Raw CST occurrence inventory carries no resolution or component judgment.
use super::{PositionId, ShadowArtifact, ShadowError};
use std::sync::Arc;
use yu_syntax::{SourceText, SyntaxEnvironment, SyntaxKind, parse_file, scan_header};

fn artifact(source: &str) -> ShadowArtifact {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    ShadowArtifact::from_parsed(parse_file(
        source,
        header,
        Arc::new(SyntaxEnvironment::empty()),
    ))
    .unwrap()
}

fn text<'a>(artifact: &'a ShadowArtifact, id: &PositionId) -> &'a str {
    &artifact.source()[artifact.position(id).unwrap().range().clone()]
}

#[test]
fn shadow_raw_inventory_preserves_direct_root_source_order_and_children() {
    let artifact = artifact("my first x = x; my second y = y");
    assert!(artifact.skeleton().is_err());
    let declarations = artifact.raw_declaration_positions().collect::<Vec<_>>();
    assert_eq!(declarations.len(), 2);
    assert_eq!(text(&artifact, &declarations[0]), "my first x = x");
    assert_eq!(text(&artifact, &declarations[1]), "my second y = y");
    for (declaration, name) in declarations.iter().zip(["first", "second"]) {
        let statement = artifact.position(declaration).unwrap();
        assert_eq!(statement.parent(), Some(&artifact.root()));
        let header = statement
            .children()
            .iter()
            .find(|id| artifact.position(id).unwrap().kind() == SyntaxKind::BindingHeader)
            .unwrap();
        let pattern = artifact
            .position(header)
            .unwrap()
            .children()
            .iter()
            .find(|id| artifact.position(id).unwrap().kind() == SyntaxKind::Pattern)
            .unwrap();
        let identifier = artifact
            .position(pattern)
            .unwrap()
            .children()
            .iter()
            .find(|id| artifact.position(id).unwrap().kind() == SyntaxKind::IdentifierPattern)
            .unwrap();
        assert_eq!(text(&artifact, identifier), name);
        assert!(
            statement
                .children()
                .iter()
                .any(|id| { artifact.position(id).unwrap().kind() == SyntaxKind::BindingBody })
        );
    }
    assert_eq!(
        artifact
            .raw_identifier_expression_positions()
            .map(|id| text(&artifact, &id))
            .collect::<Vec<_>>(),
        ["x", "y"]
    );
}

#[test]
fn shadow_raw_inventory_keeps_duplicate_occurrences_and_artifact_brand() {
    let first = artifact("my f x = x x");
    assert!(first.skeleton().is_ok());
    let occurrences = first
        .raw_identifier_expression_positions()
        .collect::<Vec<_>>();
    assert_eq!(occurrences.len(), 2);
    assert_ne!(occurrences[0], occurrences[1]);
    assert_eq!(text(&first, &occurrences[0]), "x");
    assert_eq!(text(&first, &occurrences[1]), "x");
    assert_ne!(
        first.position(&occurrences[0]).unwrap().range(),
        first.position(&occurrences[1]).unwrap().range()
    );
    let second = artifact(first.source());
    for id in occurrences
        .into_iter()
        .chain(first.raw_declaration_positions())
    {
        assert!(matches!(
            second.position(&id),
            Err(ShadowError::ForeignArtifact)
        ));
    }
}

#[test]
fn shadow_raw_inventory_does_not_promote_nested_bindings_to_root() {
    let artifact = artifact("my apply f = { my step x = f x; step }");
    assert_eq!(artifact.raw_declaration_positions().count(), 1);
    assert_eq!(
        artifact
            .raw_identifier_expression_positions()
            .map(|id| text(&artifact, &id))
            .collect::<Vec<_>>(),
        ["f", "x", "step"]
    );
}
