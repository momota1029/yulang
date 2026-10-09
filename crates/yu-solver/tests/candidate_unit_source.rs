#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

use std::sync::Arc;
use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution, lower_module_with_local_source};
use yu_hir::{DefinitionRootId, FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::{CandidateGraphExport, CandidateGraphLeaf, CandidateGraphNode, CandidateInference};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(source.clone(), Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()));
    assert!(parsed.structural_recoveries().is_empty(), "valid Unit fixture");
    Arc::new(lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("unit-source", "source.yu"))),
        &parsed, SemanticImports::empty()).unwrap())
}

fn root<'a>(hir: &'a HirModule, name: &str) -> &'a DefinitionRootId {
    hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding.definition_root()),
        _ => None,
    }).expect("source binding")
}

fn value_lowers<'a>(graph: &CandidateGraphExport<'a>, start: CandidateGraphNode<'a>) -> Vec<CandidateGraphNode<'a>> {
    let mut pending = vec![start];
    let mut visited: Vec<CandidateGraphNode<'a>> = Vec::new();
    while let Some(node) = pending.pop() {
        if visited.iter().any(|prior| prior.same_identity(node)) { continue; }
        visited.push(node);
        if let Some(row) = node.row() {
            for bound in graph.bounds() {
                if bound.kind() == yu_types::ComponentKind::Value
                    && bound.upper().row().is_some_and(|upper| upper.same_identity(row)) {
                    pending.push(bound.lower());
                }
            }
        }
    }
    visited
}

fn assert_unit(candidate: &CandidateInference, hir: &HirModule, name: &str) {
    let graph = candidate.export(root(hir, name)).unwrap();
    assert!(value_lowers(&graph, graph.root()).iter().any(|node|
        node.leaf() == Some(CandidateGraphLeaf::UnitPositive)),
        "{name} retains a genuine positive Unit endpoint reachable from its root");
}

#[test]
fn explicit_unit_and_empty_call_use_ordinary_application() {
    let hir = module("my unit = (); my id x = x; my answer = id()");
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.source_call_count(), 1);
    for name in ["unit", "answer"] { assert_unit(&candidate, &hir, name); }
    let source = hir.local_source(root(&hir, "answer")).unwrap().unwrap();
    assert!(source.expressions().iter().any(|expr| matches!(&expr.form, LocalSourceForm::Unit)));
    assert!(source.expressions().iter().any(|expr| matches!(&expr.form, LocalSourceForm::Apply { .. })));
}

#[test]
fn unit_annotation_without_literals_prepares_both_primitive_polarities() {
    let hir = module("my id x: () -> () = x; my alias: () -> () = id");
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.source_call_count(), 0);
    for name in ["id", "alias"] {
        let source = hir.local_source(root(&hir, name)).unwrap().unwrap();
        assert!(source.expressions().iter().all(|expr| !matches!(
            &expr.form, LocalSourceForm::Unit | LocalSourceForm::Apply { .. })));
        let graph = candidate.export(root(&hir, name)).unwrap();
        let functions: Vec<_> = value_lowers(&graph, graph.root()).into_iter()
            .filter(|node| node.polarity() == yu_solver::Polarity::Positive)
            .filter_map(|node| node.children()).collect();
        assert!(!functions.is_empty(), "{name} has a reachable positive Function");
        assert!(functions.iter().any(|children|
            children[0].leaf() == Some(CandidateGraphLeaf::UnitNegative)
                && children[3].leaf() == Some(CandidateGraphLeaf::UnitPositive)),
            "{name} retains the annotated Unit argument and result");
    }
}

#[test]
fn unit_int_and_function_annotations_reject_both_mismatch_directions() {
    for text in [
        "my wrong: () = 1",
        "my wrong: int = ()",
        "my wrong x: () = x",
        "my wrong: () -> () = ()",
    ] {
        let candidate = CandidateInference::solve(module(text)).unwrap();
        assert!(!candidate.candidate_conflicts().is_empty(), "{text}");
    }
}

#[test]
fn let_generalization_freshens_independent_unit_and_integer_uses() {
    let hir = module("my answer = { my id x = x; my first = id(); my integer = id 1; id() }");
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.source_call_count(), 3);
    assert_unit(&candidate, &hir, "answer");
    let source = hir.local_source(root(&hir, "answer")).unwrap().unwrap();
    let uses: Vec<_> = source.expressions().iter().filter(|expr| matches!(
        &expr.form, LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Local(_) }
            if spelling.as_ref() == "id")).collect();
    assert_eq!(uses.len(), 3);
    let first = candidate.fresh_use(&uses[0].occurrence).unwrap();
    let second = candidate.fresh_use(&uses[1].occurrence).unwrap();
    let a: Vec<_> = first.rows().collect();
    let b: Vec<_> = second.rows().collect();
    assert!(a.iter().any(|row| row.source_row().is_local()));
    for row in a.iter().filter(|row| row.source_row().is_local()) {
        assert!(b.iter().all(|other| !row.same_identity(other)));
    }
}
