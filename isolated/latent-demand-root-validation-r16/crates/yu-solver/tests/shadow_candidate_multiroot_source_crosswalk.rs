#![cfg(feature = "shadow-apply-candidate")]
#[path = "../src/shadow_candidate_source_crosswalk.rs"]
mod crosswalk;

use crosswalk::{CandidateSourceCrosswalk, CrosswalkError};
use std::sync::Arc;
use yu_hir::shadow::{ShadowArtifact, lower_module_with_shadow_applications};
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

#[test]
fn independent_roots_share_observation_with_exact_selected_exports() {
    let (source, hir) = inputs("my left f = f 1; my right f = f (f 2)");
    assert!(source.skeleton().is_err());
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    let mut formals = Vec::new();
    let mut owners = std::collections::HashMap::new();
    for item in hir.items() {
        let HirItem::Binding(binding) = item else {
            panic!("binding")
        };
        let mut expressions = vec![binding.value()];
        while let Some(expression) = expressions.pop() {
            assert!(owners.insert(expression.occurrence(), binding).is_none());
            match expression {
                yu_hir::ResolvedExpr::Lambda { body, .. } => expressions.push(body),
                yu_hir::ResolvedExpr::Apply {
                    callee, argument, ..
                } => {
                    expressions.push(callee);
                    expressions.push(argument);
                }
                yu_hir::ResolvedExpr::Group { inner, .. } => expressions.push(inner),
                _ => {}
            }
        }
    }
    for item in hir.items() {
        let HirItem::Binding(binding) = item else {
            panic!("binding")
        };
        let position = source
            .definition_source_position(&hir, binding.definition_root())
            .unwrap();
        let skeleton = source.declaration_skeleton(&position).unwrap();
        let lambda = skeleton
            .expressions()
            .iter()
            .find(|expression| expression.position() == &position)
            .unwrap();
        let yu_hir::shadow::Form::Lambda { parameter, .. } = lambda.form() else {
            panic!("lambda")
        };
        formals.push(parameter.clone());
        let joined =
            CandidateSourceCrosswalk::new(&source, &hir, &candidate, binding.definition_root())
                .unwrap();
        assert_eq!(joined.calls().count(), 3);
        assert_eq!(joined.export().unresolved, UNRESOLVED);
        assert!(
            joined.export().endpoints().alpha_eq(
                candidate
                    .export(binding.definition_root())
                    .unwrap()
                    .endpoints()
            )
        );
        let mut owner_counts = [0, 0];
        for call in joined.calls() {
            assert!(call.ordinary_incoming_rows().is_none());
            assert_eq!(call.pending().count(), 10);
            let candidate_call = call.candidate_call();
            let owner = owners[&candidate_call.occurrence];
            assert!(std::ptr::eq(owners[&candidate_call.callee], owner));
            assert!(std::ptr::eq(owners[&candidate_call.argument], owner));
            let declaration = source
                .definition_source_position(&hir, owner.definition_root())
                .unwrap();
            let owner_skeleton = source.declaration_skeleton(&declaration).unwrap();
            assert_eq!(
                owner_skeleton
                    .root_declaration_header()
                    .unwrap()
                    .statement(),
                &declaration
            );
            let owner_lambda = owner_skeleton
                .expressions()
                .iter()
                .find(|expression| expression.position() == &declaration)
                .unwrap();
            let yu_hir::shadow::Form::Lambda {
                parameter: owner_formal,
                ..
            } = owner_lambda.form()
            else {
                panic!("source lambda")
            };
            let yu_hir::ResolvedExpr::Lambda {
                parameter: hir_formal,
                ..
            } = owner.value()
            else {
                panic!("HIR lambda")
            };
            let input = call.source_input();
            assert_eq!(input.binder(), owner_formal);
            assert_eq!(
                owner_skeleton.binder(input.binder()).unwrap().position(),
                &source.parameter_source_position(&hir, hir_formal).unwrap()
            );
            assert_eq!(
                input.application().position(),
                &source
                    .occurrence_source_position(&hir, &candidate_call.occurrence)
                    .unwrap()
            );
            assert_eq!(
                owner_skeleton.use_position(input.occurrence()).unwrap(),
                &source
                    .occurrence_source_position(&hir, &candidate_call.callee)
                    .unwrap()
            );
            assert_eq!(
                owner_skeleton
                    .expression(input.argument())
                    .unwrap()
                    .position(),
                &source
                    .occurrence_source_position(&hir, &candidate_call.argument)
                    .unwrap()
            );
            let owner_index = hir
                .items()
                .iter()
                .position(|item| {
                    matches!(item,
                HirItem::Binding(binding) if std::ptr::eq(binding, owner))
                })
                .unwrap();
            owner_counts[owner_index] += 1;
        }
        assert_eq!(owner_counts, [1, 2]);
    }
    assert_ne!(formals[0], formals[1]);
    for (index, item) in hir.items().iter().enumerate() {
        let HirItem::Binding(binding) = item else {
            panic!("binding")
        };
        let declaration = source
            .definition_source_position(&hir, binding.definition_root())
            .unwrap();
        assert!(matches!(
            source
                .declaration_skeleton(&declaration)
                .unwrap()
                .binder(&formals[1 - index]),
            Err(yu_hir::shadow::ShadowError::ForeignArtifact)
        ));
    }
    let (foreign_source, foreign_hir) = inputs("my left f = f 1; my right f = f (f 2)");
    let HirItem::Binding(foreign) = &foreign_hir.items()[0] else {
        panic!("binding")
    };
    let foreign_position = foreign_source
        .definition_source_position(&foreign_hir, foreign.definition_root())
        .unwrap();
    assert!(matches!(
        source.declaration_skeleton(&foreign_position),
        Err(yu_hir::shadow::ShadowError::ForeignArtifact)
    ));
    assert!(
        CandidateSourceCrosswalk::new(&source, &hir, &candidate, foreign.definition_root())
            .is_err()
    );
}
