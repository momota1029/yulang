#![cfg(feature = "shadow-apply-candidate")]

use std::sync::Arc;

use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution};
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports, lower_module};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const SOURCE: &str = "my id x = x; my apply f = f 1; my answer = apply id";
// SHA-256 of SOURCE bytes (UTF-8): recorded by the sprint handoff.
const SOURCE_SHA256: &str = "bdf41b8059d37dea354a6b6e45a4e0a9f5a0dc412bcee40efb44a0a8bff10ba1";

fn module(source_text: &str) -> (Arc<HirModule>, CandidateInference) {
    let source: Arc<SourceText> = Arc::from(source_text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(
        parsed.structural_recoveries().is_empty(),
        "source must parse without structural recovery"
    );
    let hir = Arc::new(
        lower_module(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "research",
                "accepted-call-vertical.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    assert!(
        hir.errors().is_empty(),
        "accepted source must produce no HIR errors"
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    (hir, candidate)
}

fn binding<'a>(hir: &'a HirModule, name: &str) -> &'a yu_hir::HirBinding {
    hir.items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding),
            _ => None,
        })
        .unwrap()
}

#[test]
fn accepted_source_generates_calls_propagates_and_reaches_fresh_uses() {
    assert!(
        !SOURCE_SHA256.is_empty(),
        "freeze the selected source literal before review"
    );
    let (hir, candidate) = module(SOURCE);

    assert!(candidate.observes_hir(&hir));
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(
        hir.source_carrier_outcomes().len(),
        3,
        "ordinary lowering forms one carrier outcome for each binding"
    );

    for name in ["id", "apply", "answer"] {
        assert!(
            candidate
                .export(binding(&hir, name).definition_root())
                .unwrap()
                .node_count()
                > 0
        );
    }

    let answer = hir
        .local_source(binding(&hir, "answer").definition_root())
        .unwrap()
        .unwrap();
    let mut authenticated_fresh_uses = 0;
    for expression in answer.expressions() {
        if matches!(
            &expression.form,
            LocalSourceForm::Name {
                resolution: LocalSourceResolution::ModuleDef(_),
                ..
            }
        ) {
            assert!(candidate.fresh_use(&expression.occurrence).is_some());
            authenticated_fresh_uses += 1;
        }
    }
    assert_eq!(
        authenticated_fresh_uses, 2,
        "answer applies the two module definitions"
    );

    // `apply f = f 1` creates the formal call; `answer = apply id` creates
    // the module-level call. Inspect both source-owned construction records.
    assert_eq!(candidate.source_call_count(), 2);
    let formal = candidate.source_call(0).unwrap();
    assert_eq!(
        formal.owner().definition_root(),
        Some(binding(&hir, "apply").definition_root())
    );
    assert!(formal.formal_registration().is_some());
    assert!(formal.lexical_formal_use().is_some());
    assert_eq!(
        formal.checking_occurrence().occurrence(),
        &formal.source().occurrence
    );
    assert_eq!(
        formal.pending_construction().source_call().native_demand(),
        formal.native_demand()
    );
    assert!(
        candidate
            .source_call(1)
            .unwrap()
            .formal_registration()
            .is_none()
    );
}
