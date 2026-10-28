#![cfg(feature = "shadow-apply-candidate")]
#[path = "../src/shadow_candidate_source_crosswalk.rs"]
mod crosswalk;

use crosswalk::{CandidateSourceCrosswalk, CrosswalkError};
use std::sync::Arc;
use yu_hir::shadow::{
    ShadowArtifact, lower_module_with_shadow_applications,
    lower_module_with_shadow_local_binding,
};
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::{CandidateValueObservation, UNRESOLVED};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn inputs(text: &str) -> (ShadowArtifact, Arc<HirModule>) {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let artifact = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let hir = Arc::new(
        lower_module_with_shadow_applications(
            ModuleIdentity::source_root(FileId::new(FileKey::new("crosswalk", "source.yu"))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    (artifact, hir)
}
#[test]
fn exact_source_carriers_join_executed_candidate_and_whole_export() {
    for (text, calls) in [("my apply f = f 1", 1), ("my apply f = f (f 1)", 2)] {
        let (source, hir) = inputs(text);
        let HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding")
        };
        let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
        let joined =
            CandidateSourceCrosswalk::new(&source, &hir, &candidate, binding.definition_root())
                .unwrap();
        assert_eq!(joined.export().unresolved, UNRESOLVED);
        assert!(joined.export().endpoints().quantifier_count() > 0);
        assert_eq!(joined.calls().count(), calls);
        for row in joined.calls() {
            assert_eq!(row.candidate_call().unresolved, UNRESOLVED);
            assert!(row.ordinary_incoming_rows().is_none());
            let original = source
                .skeleton()
                .unwrap()
                .pending()
                .iter()
                .filter(|p| p.call() == row.source_input().application().expression())
                .collect::<Vec<_>>();
            let retained = row.pending().collect::<Vec<_>>();
            assert!(!retained.is_empty());
            assert_eq!(original.len(), retained.len());
            for (original, retained) in original.iter().zip(retained.iter()) {
                assert!(std::ptr::eq(*original, *retained));
            }
        }
        assert!(
            joined.export().endpoints().alpha_eq(
                candidate
                    .export(binding.definition_root())
                    .unwrap()
                    .endpoints()
            )
        );
    }
}

#[test]
fn captured_local_source_positions_join_the_candidate_call_and_export() {
    let text = "my apply f = { my step x = f x; step }";
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let artifact = Arc::new(ShadowArtifact::from_parsed(parsed.clone()).unwrap());
    let hir = Arc::new(
        lower_module_with_shadow_local_binding(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "crosswalk",
                "captured-local.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
            artifact.clone(),
        )
        .unwrap(),
    );
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("binding")
    };
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    let joined =
        CandidateSourceCrosswalk::new(&artifact, &hir, &candidate, binding.definition_root())
            .unwrap();
    let captured = joined.captured_input().expect("retained Bind topology");
    let [call] = candidate.calls() else {
        panic!("one candidate Apply")
    };
    let source_calls = joined.calls().collect::<Vec<_>>();
    let [source_call] = source_calls.as_slice() else {
        panic!("one source/candidate incidence")
    };
    assert_eq!(captured.call(), source_call.source_input().application().expression());
    assert_eq!(captured.callee_use(), source_call.source_input().occurrence());
    assert_eq!(captured.outer_parameter(), source_call.source_input().binder());
    assert_eq!(call.unresolved, UNRESOLVED);
    assert_eq!(source_call.candidate_call().occurrence, call.occurrence);
    assert!(source_call.ordinary_incoming_rows().is_none());
    assert_eq!(joined.export().unresolved, UNRESOLVED);
    assert!(joined
        .export()
        .endpoints()
        .alpha_eq(candidate.export(binding.definition_root()).unwrap().endpoints()));
}

#[test]
fn mismatched_parse_and_candidate_cannot_publish_crosswalk() {
    let (source, hir) = inputs("my apply f = f 1");
    let (foreign_source, foreign_hir) = inputs("my apply f = f 1");
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("binding")
    };
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    match CandidateSourceCrosswalk::new(
        &foreign_source,
        &hir,
        &candidate,
        binding.definition_root(),
    ) {
        Err(CrosswalkError::Source(error)) => {
            assert_eq!(error, yu_hir::shadow::SourceIdentityError::ForeignParse);
        }
        _ => panic!("different parse must retain the precise source identity error"),
    }
    let foreign = CandidateValueObservation::solve(foreign_hir).unwrap();
    assert!(matches!(
        CandidateSourceCrosswalk::new(&source, &hir, &foreign, binding.definition_root()),
        Err(CrosswalkError::ForeignCandidate)
    ));
}
