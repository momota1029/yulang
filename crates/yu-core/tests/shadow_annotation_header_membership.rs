#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{Correspondence, ShadowArtifact, ShadowError};
use yu_core::shadow_derivation::RawStructuralArena;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

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

#[test]
fn annotations_and_pending_calls_borrow_exact_root_header_membership() {
    let source = "my apply x (f: T) (g: T) = x (f (g 1))";
    let first = artifact(source);
    let foreign = artifact(source);
    let skeleton = first.skeleton().unwrap();
    let header = skeleton.root_declaration_header().unwrap();
    let raw = RawStructuralArena::from_artifact(&first).unwrap();
    assert_eq!(header.parameters().len(), 3);
    assert_eq!(raw.annotations().len(), 2);
    assert_eq!(skeleton.parameter_annotations().len(), 2);
    for (index, ((annotation, occurrence), incidence)) in raw
        .annotations()
        .iter()
        .zip(first.annotations())
        .zip(skeleton.parameter_annotations())
        .enumerate()
    {
        assert!(std::ptr::eq(annotation.occurrence, occurrence));
        assert!(std::ptr::eq(annotation.parameter.unwrap(), incidence));
        assert!(std::ptr::eq(
            annotation.position,
            first.position(occurrence.position()).unwrap()
        ));
        assert_eq!(&source[annotation.position.range().clone()], ": T");
        assert_eq!(incidence.annotation(), occurrence.id());
        assert_eq!(
            occurrence.correspondence(),
            &Correspondence::PendingTypedPortAndProfile
        );
        let membership = annotation.header_parameter.as_ref().unwrap();
        assert!(std::ptr::eq(membership.header, header));
        assert!(std::ptr::eq(
            membership.parameter,
            &header.parameters()[index + 1]
        ));
        assert_eq!(membership.parameter, incidence.parameter());
        let binder = skeleton.binder(membership.parameter).unwrap();
        assert_eq!(binder.name(), ["f", "g"][index]);
        assert_eq!(
            &source[first.position(binder.position()).unwrap().range().clone()],
            binder.name()
        );
        assert_eq!(
            foreign.annotation(occurrence.id()).unwrap_err(),
            ShadowError::ForeignArtifact
        );
        assert_eq!(
            foreign.position(occurrence.position()).unwrap_err(),
            ShadowError::ForeignArtifact
        );
        assert_eq!(
            foreign
                .skeleton()
                .unwrap()
                .binder(membership.parameter)
                .unwrap_err(),
            ShadowError::ForeignArtifact
        );
        assert_eq!(
            foreign.position(binder.position()).unwrap_err(),
            ShadowError::ForeignArtifact
        );
        if index > 0 {
            assert_ne!(
                raw.annotations()[index - 1].occurrence.id(),
                occurrence.id()
            );
            assert!(
                raw.annotations()[index - 1].position.range().start
                    < annotation.position.range().start
            );
        }
    }
    let registrations = raw
        .nodes()
        .iter()
        .filter_map(|node| node.pending_source_call_registration())
        .collect::<Vec<_>>();
    assert_eq!(registrations.len(), 3);
    for registration in registrations {
        let incidences = registration
            .source_use_input
            .parameter_annotations()
            .collect::<Vec<_>>();
        let membership = registration.header_parameter.unwrap();
        assert_eq!(membership.parameter, registration.source_use_input.binder());
        assert!(std::ptr::eq(membership.header, header));
        let parameter_index = header
            .parameters()
            .iter()
            .position(|parameter| parameter == membership.parameter)
            .unwrap();
        match parameter_index {
            0 => {
                // The exact retained source annotation inventory for this
                // unannotated header binder is empty; no semantic absence
                // judgment is attached to that inventory fact.
                assert!(incidences.is_empty());
                assert_eq!(parameter_index, 0);
            }
            1 | 2 => {
                assert_eq!(incidences.len(), 1);
                let incidence = incidences[0];
                let annotation = raw
                    .annotations()
                    .iter()
                    .find(|annotation| annotation.occurrence.id() == incidence.annotation())
                    .unwrap();
                assert!(std::ptr::eq(annotation.parameter.unwrap(), incidence));
                let annotation_membership = annotation.header_parameter.as_ref().unwrap();
                assert!(std::ptr::eq(
                    membership.header,
                    annotation_membership.header
                ));
                assert!(std::ptr::eq(
                    membership.parameter,
                    annotation_membership.parameter
                ));
                assert_eq!(
                    parameter_index,
                    if raw.annotations()[0].header_parameter.unwrap().parameter
                        == membership.parameter
                    {
                        1
                    } else {
                        2
                    },
                );
            }
            index => panic!("unexpected root header parameter index {index}"),
        }
        let expected = skeleton
            .pending()
            .iter()
            .filter(|premise| premise.call() == registration.source)
            .collect::<Vec<_>>();
        assert_eq!(registration.application_premises.len(), 10);
        assert_eq!(registration.application_premises.len(), expected.len());
        for (actual, expected) in registration.application_premises.iter().zip(expected) {
            assert!(std::ptr::eq(*actual, expected));
        }
    }
}
