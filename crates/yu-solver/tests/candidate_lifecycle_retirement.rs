#![cfg(feature = "shadow-apply-candidate")]

use std::sync::Arc;
use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
    assert!(parsed.structural_recoveries().is_empty());
    Arc::new(lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("lifecycle", "source.yu"))),
        &parsed, SemanticImports::empty(),
    ).unwrap())
}
fn binding<'a>(hir: &'a HirModule, name: &str) -> &'a yu_hir::HirBinding {
    hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding),
        _ => None,
    }).unwrap()
}

#[test]
fn candidate_result_keeps_exports_fresh_uses_call_inputs_and_foreign_root_rejection() {
    let text = "my id x = x; my apply f = f 1; my answer = apply id";
    let hir = module(text);
    let foreign = module(text);
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.observes_hir(&hir));
    assert!(!candidate.observes_hir(&foreign));
    assert!(candidate.candidate_conflicts().is_empty());
    for name in ["id", "apply", "answer"] {
        assert!(candidate.export(binding(&hir, name).definition_root()).unwrap().node_count() > 0);
        assert!(candidate.export(binding(&foreign, name).definition_root()).is_err());
    }
    let answer = hir.local_source(binding(&hir, "answer").definition_root()).unwrap().unwrap();
    for expression in answer.expressions() {
        if matches!(&expression.form, LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(_), .. }) {
            assert!(candidate.fresh_use(&expression.occurrence).is_some());
        }
    }
    assert_eq!(candidate.source_call_count(), 2);
    let formal = candidate.source_call(0).unwrap();
    assert_eq!(formal.owner(), binding(&hir, "apply").definition_root());
    assert!(formal.formal_registration().is_some());
    assert!(formal.lexical_formal_use().is_some());
    assert_eq!(formal.checking_occurrence().occurrence(), &formal.source().occurrence);
    assert_eq!(formal.pending_construction().source_call().native_demand(), formal.native_demand());
    assert!(candidate.source_call(1).unwrap().formal_registration().is_none());
    assert!(candidate.source_call(2).is_err());
}

#[test]
fn candidate_result_preserves_actual_conflicts_and_drops_its_hir_owner() {
    let hir = module("act E\nmy ident y = y; my wrong x: int -> [E] int = ident");
    let weak = Arc::downgrade(&hir);
    let candidate = CandidateInference::solve(hir).unwrap();
    assert!(!candidate.candidate_conflicts().is_empty());
    assert!(weak.upgrade().is_some());
    drop(candidate);
    assert!(weak.upgrade().is_none());
}
