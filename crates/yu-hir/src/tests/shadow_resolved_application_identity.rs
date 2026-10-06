use super::*;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn parsed(source: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
}

#[test]
fn exact_application_links_and_pending_rows_survive_borrowed_lookup() {
    for source in [
        "my apply f x = f x",
        "my apply f = { my step x = f x; step }",
        "my apply f x = f (f x)",
        "my apply f x = f x x",
        "my apply f x = (f) x",
    ] {
        let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        let pending: Vec<_> = skeleton
            .pending()
            .iter()
            .map(|p| (p.call().clone(), p.premise()))
            .collect();
        let crosswalk = artifact.skeleton_source_crosswalk();
        for call in skeleton.application_source_occurrences() {
            let retained = skeleton.expression(call.expression()).unwrap();
            let found = crosswalk
                .application_at_position(call.position())
                .unwrap()
                .unwrap();
            assert!(std::ptr::eq(found, retained));
            let Form::Apply {
                source_form,
                callee,
                argument,
            } = found.form()
            else {
                panic!("Apply")
            };
            assert_eq!(*source_form, call.source_form());
            assert!(std::ptr::eq(callee, call.callee()));
            assert!(std::ptr::eq(argument, call.argument()));
            let resolution = crosswalk
                .application_direct_use_at_position(call.position())
                .unwrap();
            match skeleton.expression(callee).unwrap().form() {
                Form::Use { occurrence, binder } => {
                    let (found_use, found_binder) = resolution.unwrap();
                    assert!(std::ptr::eq(found_use, occurrence));
                    assert!(std::ptr::eq(found_binder, binder));
                }
                _ => assert!(resolution.is_none()),
            }
        }
        for expression in skeleton.expressions() {
            if !matches!(expression.form(), Form::Apply { .. }) {
                assert!(
                    crosswalk
                        .application_at_position(expression.position())
                        .unwrap()
                        .is_none()
                );
                assert!(
                    crosswalk
                        .application_direct_use_at_position(expression.position())
                        .unwrap()
                        .is_none()
                );
            }
        }
        assert_eq!(
            pending,
            skeleton
                .pending()
                .iter()
                .map(|p| (p.call().clone(), p.premise()))
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn repeated_same_binder_calls_keep_distinct_existing_identities() {
    let artifact = ShadowArtifact::from_parsed(parsed("my apply f x = f (f x)")).unwrap();
    let skeleton = artifact.skeleton().unwrap();
    let calls: Vec<_> = skeleton.resolved_call_incidences().collect();
    assert_eq!(calls.len(), 2);
    assert_eq!(calls[0].binder(), calls[1].binder());
    assert_ne!(calls[0].occurrence(), calls[1].occurrence());
    assert_ne!(
        calls[0].application().expression(),
        calls[1].application().expression()
    );
    assert_ne!(
        calls[0].application().position(),
        calls[1].application().position()
    );
    let crosswalk = artifact.skeleton_source_crosswalk();
    let first = crosswalk
        .application_at_position(calls[0].application().position())
        .unwrap()
        .unwrap();
    let second = crosswalk
        .application_at_position(calls[1].application().position())
        .unwrap()
        .unwrap();
    assert!(!std::ptr::eq(first, second));
}

#[test]
fn foreign_positions_reject_and_unsupported_projection_stays_empty() {
    let artifact = ShadowArtifact::from_parsed(parsed("my apply f x = f x")).unwrap();
    let foreign = ShadowArtifact::from_parsed(parsed("my apply f x = f x")).unwrap();
    let foreign_call = foreign
        .skeleton()
        .unwrap()
        .application_source_occurrences()
        .next()
        .unwrap();
    let crosswalk = artifact.skeleton_source_crosswalk();
    assert!(matches!(
        crosswalk.application_at_position(foreign_call.position()),
        Err(ShadowError::ForeignArtifact)
    ));
    assert_eq!(
        crosswalk.application_direct_use_at_position(foreign_call.position()),
        Err(ShadowError::ForeignArtifact)
    );
    let unsupported = ShadowArtifact::from_parsed(parsed("my f x = x; my g x = x")).unwrap();
    assert!(unsupported.skeleton().is_err());
    let empty = unsupported.skeleton_source_crosswalk();
    for index in 0..unsupported.positions.len() {
        let position = PositionId(LocalId {
            artifact: unsupported.identity.clone(),
            index,
        });
        assert!(empty.application_at_position(&position).unwrap().is_none());
        assert!(
            empty
                .application_direct_use_at_position(&position)
                .unwrap()
                .is_none()
        );
    }
}

#[test]
fn lookup_preserves_production_lowering_success_and_failure() {
    let identity = ModuleIdentity::source_root(crate::FileId::new(crate::FileKey::new(
        "test",
        "application.yu",
    )));
    let mut saw_success = false;
    let mut saw_failure = false;
    for source in [
        "my id x = x",
        "my apply f x = f x",
        "my apply f = { my step x = f x; step }",
    ] {
        let parsed = parsed(source);
        let before = crate::lower_module(identity.clone(), &parsed, SemanticImports::empty());
        let module = before.as_ref().unwrap();
        saw_success |= module.errors().is_empty();
        saw_failure |= !module.errors().is_empty();
        let artifact = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
        let crosswalk = artifact.skeleton_source_crosswalk();
        if let Ok(skeleton) = artifact.skeleton() {
            for call in skeleton.application_source_occurrences() {
                crosswalk.application_at_position(call.position()).unwrap();
                crosswalk
                    .application_direct_use_at_position(call.position())
                    .unwrap();
            }
        }
        let after =
            lower_module_with_source_identity(identity.clone(), &parsed, SemanticImports::empty());
        assert_eq!(before, after);
    }
    assert!(saw_success);
    assert!(saw_failure);
}
