#![cfg(feature = "shadow-apply-candidate")]

use std::sync::Arc;

use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const SOURCE: &str = "my id x = x; my apply f = f 1; my answer = apply id";
// SHA-256 of SOURCE bytes (UTF-8): recorded by the sprint handoff.
const SOURCE_SHA256: &str = "bdf41b8059d37dea354a6b6e45a4e0a9f5a0dc412bcee40efb44a0a8bff10ba1";

fn binding<'a>(hir: &'a HirModule, name: &str) -> &'a yu_hir::HirBinding {
    hir.items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding),
            _ => None,
        })
        .unwrap()
}

fn main() {
    assert!(
        !SOURCE_SHA256.is_empty(),
        "freeze the selected source literal before review"
    );
    let source: Arc<SourceText> = Arc::from(SOURCE);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(parsed.structural_recoveries().is_empty());

    let hir = Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "research",
                "accepted-call-vertical.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    assert!(hir.errors().is_empty());

    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.observes_hir(&hir));
    assert!(candidate.candidate_conflicts().is_empty());
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
    let authenticated_fresh_uses = answer
        .expressions()
        .iter()
        .filter(|expression| {
            matches!(
                &expression.form,
                LocalSourceForm::Name {
                    resolution: LocalSourceResolution::ModuleDef(_),
                    ..
                }
            )
        })
        .filter(|expression| candidate.fresh_use(&expression.occurrence).is_some())
        .count();
    assert_eq!(authenticated_fresh_uses, 2);
    assert_eq!(candidate.source_call_count(), 2);

    println!(
        "accepted source {}: 2 source calls, 3 exports, 2 authenticated fresh uses",
        SOURCE_SHA256
    );
}
