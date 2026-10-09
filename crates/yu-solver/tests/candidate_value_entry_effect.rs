#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

use std::sync::Arc;
use yu_hir::shadow::lower_module_with_local_source;
use yu_hir::{DefinitionRootId, FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::{CandidateGraphExport, CandidateGraphLeaf, CandidateGraphNode, CandidateInference};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
    assert!(parsed.structural_recoveries().is_empty(), "valid operation fixture");
    Arc::new(lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("operation-source", "source.yu"))),
        &parsed, SemanticImports::empty(),
    ).unwrap())
}
fn root<'a>(hir: &'a HirModule, name: &str) -> &'a DefinitionRootId {
    hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding.definition_root()),
        _ => None,
    }).unwrap()
}
fn lowers<'a>(graph: &CandidateGraphExport<'a>, start: CandidateGraphNode<'a>) -> Vec<CandidateGraphNode<'a>> {
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
#[test]
fn bare_value_entry_accepts_effectful_arguments_and_preserves_result_values() {
    for (body, expected) in [
        ("my ignore x = (); my answer = ignore (tick::next())", CandidateGraphLeaf::UnitPositive),
        ("my ident x = x; my answer = ident (tick::next())", CandidateGraphLeaf::IntPositive),
        ("my ignore x = (); my alias = ignore; my answer = alias (tick::next())", CandidateGraphLeaf::UnitPositive),
        ("my ignore x = (); my pure = ignore 1; my answer = ignore (tick::next())", CandidateGraphLeaf::UnitPositive),
        ("my apply f = f (tick::next()); my ignore x = (); my answer = apply ignore", CandidateGraphLeaf::UnitPositive),
    ] {
        let hir = module(&format!("act tick:\n    our next: () -> int\n\n{body}"));
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{body}");
        let graph = candidate.export(root(&hir, "answer")).unwrap();
        let fiber = lowers(&graph, graph.root());
        assert!(fiber.iter().any(|node| node.leaf() == Some(expected)), "actual answer result: {body}");
        let incompatible = if expected == CandidateGraphLeaf::UnitPositive {
            CandidateGraphLeaf::IntPositive
        } else { CandidateGraphLeaf::UnitPositive };
        assert!(!fiber.iter().any(|node| node.leaf() == Some(incompatible) || node.children().is_some()), "precise answer result: {body}");
    }
}

#[test]
fn value_entry_still_rejects_the_wrong_argument_value() {
    for (argument, conflicts) in [("1", true), ("()", false)] {
        let hir = module(&format!("my requires x: () -> () = (); my answer = requires {argument}"));
        let candidate = CandidateInference::solve(hir).unwrap();
        assert_eq!(!candidate.candidate_conflicts().is_empty(), conflicts, "value-only argument {argument}");
    }
}
