#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

// Provisional source-attachment evidence only. No receiver expiry or Catch
// subtraction is enabled by these tests. Named provider headers replace the
// playground lambda spelling in these adapted construction controls. The
// nested capture uses the supported curried inner Lambda. The
// braced Catch scrutinee is grouped so its braces cannot start the arm list.
use std::sync::Arc;
use yu_hir::shadow::{LocalSourceForm, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(parsed.structural_recoveries().is_empty(), "{text}");
    Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "receiver-boundary",
                "source.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    )
}

const SOURCE: &str = "act signal:\n    our ping: () -> int\n\nmy g h x = catch ({ my direct = signal::ping(); h x }) { signal::ping(), _ -> 1, v -> v }\nmy callback_first i = signal::ping()\nmy callback_second i = signal::ping()\nmy first = catch g callback_first 0 { signal::ping(), _ -> 2, v -> v }\nmy second = catch g callback_second 0 { signal::ping(), _ -> 3, v -> v }";

#[test]
fn captured_formal_attaches_to_its_original_receiver_not_the_nested_lambda() {
    let hir = module(SOURCE);
    let candidate = CandidateInference::solve_scoped_experiment(hir.clone()).unwrap();
    let g = hir
        .items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "g" => Some(binding),
            _ => None,
        })
        .unwrap();
    let source = hir.local_source(g.definition_root()).unwrap().unwrap();
    let lambda = source.expression(source.body()).unwrap();
    let LocalSourceForm::Lambda { body, .. } = &lambda.form else {
        panic!("g receiver");
    };
    let body = source.expression(body).unwrap();
    let mut captured = 0;
    let mut direct = 0;
    for index in 0..candidate.source_call_count() {
        let call = candidate.source_call(index).unwrap();
        if call.lexical_formal_use().is_some_and(|name| {
            matches!(&name.form,
            LocalSourceForm::Name { spelling, .. } if spelling.as_ref() == "h")
        }) {
            let attachment = call.experimental_receiver_attachment().unwrap();
            assert_eq!(attachment.receiver_lambda(), &lambda.occurrence);
            assert_eq!(attachment.receiver_body(), &body.occurrence);
            assert_ne!(
                attachment.receiver_region(),
                attachment.lexical_region(),
                "captured h is used in the curried inner lambda region"
            );
            assert_eq!(
                call.directional_introduction().unwrap().original_lambda(),
                attachment.receiver_lambda()
            );
            let scope = attachment.original_scope();
            assert!(
                candidate
                    .scoped_scope_lineage()
                    .any(|(_, original, occurrence)| original == scope
                        && occurrence == &call.source().occurrence)
            );
            captured += 1;
        }
        if matches!(call.callee_source().form, LocalSourceForm::Operation { .. }) {
            assert!(
                call.experimental_receiver_attachment().is_none(),
                "direct body operations do not acquire a formal receiver attachment"
            );
            direct += 1;
        }
    }
    assert_eq!(captured, 1);
    assert!(direct >= 3);
}

#[test]
fn ordinary_candidate_does_not_construct_experimental_attachments() {
    let candidate = CandidateInference::solve(module(SOURCE)).unwrap();
    for index in 0..candidate.source_call_count() {
        assert!(
            candidate
                .source_call(index)
                .unwrap()
                .experimental_receiver_attachment()
                .is_none()
        );
    }
}

#[test]
fn captured_local_helper_keeps_structural_effect_copies_separate_from_value_demands() {
    let hir = module(
        "act signal:\n    our ping: () -> int\n\nmy invoke cb = cb 0\nmy g h = catch ({ my step i = h i; my direct = signal::ping(); invoke step }) { signal::ping(), _ -> 1, v -> v }\nmy callback_first i = signal::ping()\nmy callback_second i = signal::ping()\nmy first = catch g callback_first { signal::ping(), _ -> 2, v -> v }\nmy second = catch g callback_second { signal::ping(), _ -> 3, v -> v }",
    );
    let candidate = CandidateInference::solve_scoped_experiment(hir).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let mut captured = 0;
    for index in 0..candidate.source_call_count() {
        let call = candidate.source_call(index).unwrap();
        if call.lexical_formal_use().is_some_and(|name| {
            matches!(&name.form,
            LocalSourceForm::Name { spelling, .. } if spelling.as_ref() == "h")
        }) {
            let attachment = call.experimental_receiver_attachment().unwrap();
            assert_ne!(attachment.receiver_region(), attachment.lexical_region());
            assert_eq!(
                attachment.receiver_lambda(),
                call.directional_introduction().unwrap().original_lambda()
            );
            captured += 1;
        }
    }
    assert_eq!(captured, 1);
}
