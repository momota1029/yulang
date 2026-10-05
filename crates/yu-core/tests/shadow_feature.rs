#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{Form, Premise, ShadowArtifact, ShadowError};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, parse_file, scan_header};

fn parsed(source: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
}

#[test]
fn facade_reads_the_hir_snapshot_without_resolving_pending_judgments() {
    let input = parsed("my compose f g x = f (g x)");
    let revision = input.revision();
    let environment = input.syntax_environment();
    let selected = input.selected_syntax_environment().clone();
    let artifact = ShadowArtifact::from_parsed(input).unwrap();
    assert_eq!(artifact.parsed().revision(), revision);
    assert_eq!(artifact.parsed().syntax_environment(), environment);
    assert!(Arc::ptr_eq(
        artifact.parsed().selected_syntax_environment(),
        &selected
    ));
    let skeleton = artifact.skeleton().unwrap();
    assert!(matches!(
        skeleton.expression(skeleton.body()).unwrap().form(),
        Form::Apply { .. }
    ));
    assert_eq!(skeleton.pending().len(), 6);
    assert!(
        skeleton
            .pending()
            .iter()
            .any(|p| p.premise() == Premise::FullFunctionMembership)
    );
    let other = ShadowArtifact::from_parsed(artifact.parsed().clone()).unwrap();
    assert_eq!(
        artifact.position(&other.root()).unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        skeleton
            .expression(other.skeleton().unwrap().body())
            .unwrap_err(),
        ShadowError::ForeignArtifact
    );
}

#[test]
fn facade_retains_annotations_when_the_narrow_skeleton_is_unavailable() {
    let artifact = ShadowArtifact::from_parsed(parsed("x as int; x as int")).unwrap();
    assert_eq!(artifact.annotations().len(), 2);
    assert!(artifact.skeleton().is_err());
    assert_eq!(artifact.source(), "x as int; x as int");
}
