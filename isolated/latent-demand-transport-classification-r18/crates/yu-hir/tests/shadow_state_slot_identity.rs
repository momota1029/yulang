#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_hir::{
    FileId, FileKey, HirErrorKind, ModuleIdentity, SemanticImports, lower_module,
    shadow::{PositionId, ShadowArtifact, ShadowError},
};
use yu_syntax::{SourceText, SyntaxEnvironment, SyntaxKind, parse_file, scan_header};

const SOURCE: &str = "my $buffer = 0; my $buffer = 1; my backing = 1; my read = backing";

fn positions(artifact: &ShadowArtifact, kind: SyntaxKind, text: &str) -> Vec<PositionId> {
    let mut stack = vec![artifact.root()];
    let mut result = Vec::new();
    while let Some(id) = stack.pop() {
        let position = artifact.position(&id).unwrap();
        if position.is_node()
            && position.kind() == kind
            && &artifact.source()[position.range().clone()] == text
        {
            result.push(id.clone());
        }
        stack.extend(position.children().iter().rev().cloned());
    }
    result
}

#[test]
fn caller_selected_state_declaration_stays_an_unresolved_candidate() {
    let source: Arc<SourceText> = Arc::from(SOURCE);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let artifact = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let declarations = positions(&artifact, SyntaxKind::IdentifierPattern, "$buffer");
    assert_eq!(declarations.len(), 2);
    // Current expression parsing does not yet expose State read/write source
    // occurrences as recovery-free IdentifierExpression nodes. This slice
    // therefore retains declaration identity only; occurrence and role
    // classification remain pending premises.
    let pending = artifact
        .pending_state_slot_source_input(&declarations[0], &[])
        .unwrap();
    let other_pending = artifact
        .pending_state_slot_source_input(&declarations[1], &[])
        .unwrap();
    assert_eq!(pending.candidate().declaration_position(), &declarations[0]);
    assert_ne!(pending.candidate(), other_pending.candidate());
    assert!(pending.occurrences().is_empty());
    let other = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let other_declaration = positions(&other, SyntaxKind::IdentifierPattern, "$buffer");
    assert_eq!(other_declaration.len(), 2);
    assert!(matches!(
        other.pending_state_slot_source_input(&other_declaration[0], &[declarations[0].clone()]),
        Err(ShadowError::ForeignArtifact)
    ));
    let plain = positions(&artifact, SyntaxKind::IdentifierPattern, "backing");
    assert_eq!(plain.len(), 1);
    assert!(matches!(
        artifact.pending_state_slot_source_input(&plain[0], &[]),
        Err(ShadowError::InvalidUseReference)
    ));
    let plain_use = positions(&artifact, SyntaxKind::IdentifierExpression, "backing");
    assert_eq!(plain_use.len(), 1);
    assert!(matches!(
        artifact.pending_state_slot_source_input(&declarations[0], &plain_use),
        Err(ShadowError::InvalidUseReference)
    ));
    assert!(matches!(
        artifact.pending_state_slot_source_input(&declarations[0], &[declarations[0].clone()]),
        Err(ShadowError::InvalidUseReference)
    ));
    assert!(matches!(
        artifact.pending_state_slot_source_input(&plain_use[0], &[]),
        Err(ShadowError::InvalidUseReference)
    ));

    let ordinary = lower_module(
        ModuleIdentity::source_root(FileId::new(FileKey::new("test", "state-candidate.yu"))),
        &parsed,
        SemanticImports::empty(),
    )
    .unwrap();
    assert!(
        ordinary
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.kind() == HirErrorKind::UnsupportedTarget)
    );
    assert!(artifact.skeleton().is_err());
}

fn artifact(source: &str) -> Result<ShadowArtifact, ShadowError> {
    let source: Arc<SourceText> = Arc::from(source);
    ShadowArtifact::from_parsed(parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    ))
}

#[test]
fn pending_declaration_retains_exact_direct_annotation_and_opaque_initializer() {
    let source = "my $slot: Type = initializer; my $slot: Type = other";
    let artifact = artifact(source).expect("annotated sigil source must be recovery-free");
    let declarations = artifact.raw_declaration_positions().collect::<Vec<_>>();
    assert_eq!(declarations.len(), 2);
    let identifiers = positions(&artifact, SyntaxKind::IdentifierPattern, "$slot");
    let annotations = positions(&artifact, SyntaxKind::PatternTypeAnnotation, ": Type");
    assert_eq!(identifiers.len(), 2);
    assert_eq!(annotations.len(), 2);
    let mut candidates = Vec::new();
    for (index, statement) in declarations.iter().enumerate() {
        let pending = artifact.pending_state_slot_declaration(statement).unwrap();
        assert_eq!(pending.statement(), statement);
        assert_eq!(
            pending.candidate().declaration_position(),
            &identifiers[index]
        );
        assert_eq!(pending.annotation(), Some(&annotations[index]));
        let identifier = artifact.position(&identifiers[index]).unwrap();
        let annotation = artifact.position(&annotations[index]).unwrap();
        assert_eq!(identifier.parent(), annotation.parent());
        let pattern = artifact.position(identifier.parent().unwrap()).unwrap();
        assert_eq!(pattern.kind(), SyntaxKind::Pattern);
        let header = artifact.position(pattern.parent().unwrap()).unwrap();
        assert_eq!(header.kind(), SyntaxKind::BindingHeader);
        assert_eq!(header.parent(), Some(statement));
        let body = artifact.position(pending.initializer()).unwrap();
        assert_eq!(body.kind(), SyntaxKind::BindingBody);
        assert_eq!(body.parent(), Some(statement));
        assert_eq!(
            &artifact.source()[body.range().clone()],
            [" initializer", " other"][index]
        );
        candidates.push(pending.candidate().clone());
    }
    assert_ne!(candidates[0], candidates[1]);
    let foreign = self::artifact(source).unwrap();
    assert!(matches!(
        foreign.pending_state_slot_declaration(&declarations[0]),
        Err(ShadowError::ForeignArtifact)
    ));
    assert!(matches!(
        artifact.pending_state_slot_declaration(&identifiers[0]),
        Err(ShadowError::InvalidUseReference)
    ));
}

#[test]
fn pending_declaration_rejects_plain_and_unsupported_targets() {
    for source in [
        "my plain = value",
        "my ($slot) = value",
        "my $slot argument = value",
    ] {
        let artifact = artifact(source).unwrap();
        let statement = artifact.raw_declaration_positions().next().unwrap();
        assert!(
            matches!(
                artifact.pending_state_slot_declaration(&statement),
                Err(ShadowError::InvalidUseReference)
            ),
            "{source}"
        );
    }
    assert!(matches!(
        artifact("my $slot: = value"),
        Err(ShadowError::MalformedSource)
    ));
    let artifact = artifact("my $slot = value").unwrap();
    let statement = artifact.raw_declaration_positions().next().unwrap();
    let pending = artifact.pending_state_slot_declaration(&statement).unwrap();
    assert!(pending.annotation().is_none());
}
