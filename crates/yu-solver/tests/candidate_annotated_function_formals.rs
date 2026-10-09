#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]
use std::sync::Arc;
use yu_hir::shadow::{
    LocalSourceForm, LocalSourceResolution, lower_module_with_local_source,
};
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::{CandidateGraphExport, CandidateGraphLeaf, CandidateGraphNode, CandidateInference};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str) -> Result<Arc<HirModule>, yu_hir::HirAvailabilityError> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(
        parsed.structural_recoveries().is_empty(),
        "valid source fixture"
    );
    lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("effect-annotation", "source.yu"))),
        &parsed,
        SemanticImports::empty(),
    )
    .map(Arc::new)
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

// Follow only incoming value bounds at this fiber. Function children are
// separate ports, so an argument leaf cannot stand in for a result leaf.
fn value_lowers<'a>(graph: &CandidateGraphExport<'a>, start: CandidateGraphNode<'a>) -> Vec<CandidateGraphNode<'a>> {
    let mut pending = vec![start];
    let mut visited: Vec<CandidateGraphNode<'a>> = Vec::new();
    while let Some(node) = pending.pop() {
        if visited.iter().any(|prior| prior.same_identity(node)) { continue; }
        visited.push(node);
        for bound in graph.bounds() {
            if bound.kind() != yu_types::ComponentKind::Value { continue; }
            let upper = bound.upper();
            let same_row = node.row().is_some_and(|row|
                upper.row().is_some_and(|other| row.same_identity(other)));
            if upper.same_identity(node) || same_row {
                pending.push(bound.lower());
            }
        }
    }
    visited
}

fn assert_primitive_fiber<'a>(graph: &CandidateGraphExport<'a>, start: CandidateGraphNode<'a>, expected: CandidateGraphLeaf) {
    let fiber = value_lowers(graph, start);
    assert!(fiber.iter().any(|node| node.leaf() == Some(expected)), "own fiber retains {expected:?}");
    let wrong = match expected {
        CandidateGraphLeaf::IntPositive => CandidateGraphLeaf::UnitPositive,
        CandidateGraphLeaf::UnitPositive => CandidateGraphLeaf::IntPositive,
        _ => panic!("positive primitive result expected"),
    };
    assert!(fiber.iter().all(|node| node.leaf() != Some(wrong) && node.children().is_none()), "primitive result fiber excludes {wrong:?} and Function lowers");
}

fn assert_function_result(candidate: &CandidateInference, hir: &HirModule, name: &str, expected: CandidateGraphLeaf) {
    let graph = candidate.export(binding(hir, name).definition_root()).unwrap();
    let functions: Vec<_> = value_lowers(&graph, graph.root()).into_iter()
        .filter(|node| node.polarity() == yu_solver::Polarity::Positive)
        .filter_map(|node| node.children()).collect();
    assert!(!functions.is_empty(), "{name} has a positive Function reaching its export root");
    for children in functions { assert_primitive_fiber(&graph, children[3], expected); }
}

fn assert_call_result(candidate: &CandidateInference, hir: &HirModule, name: &str, expected: CandidateGraphLeaf) {
    let graph = candidate.export(binding(hir, name).definition_root()).unwrap();
    assert_primitive_fiber(&graph, graph.root(), expected);
}

#[test]
fn function_and_named_variable_formals_have_positive_source_support() {
    for text in ["my f (x:int -> int) = x", "my f (x:'a) = x"] {
        let candidate = CandidateInference::solve(module(text).unwrap()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
    }
}

#[test]
fn called_and_unused_callbacks_check_actual_providers() {
    for text in [
        "my ident x = x; my apply (f:int -> int) = f 1; my answer = apply ident",
        "my ident x = x; my ignore (f:int -> int) = 1; my answer = ignore ident",
        "my answer = { my ident x = x; my apply (f:int -> int) = f 1; apply ident }",
        "my apply (f:int -> int) = f 1; my answer = apply later; my later x = x",
        "my invoke (f:(int -> int) -> int) = f ident; my ident x = x; my apply (g:int -> int) = g 1; my answer = invoke apply",
    ] {
        let hir = module(text).unwrap();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        assert_call_result(&candidate, &hir, "answer", CandidateGraphLeaf::IntPositive);
    }
    for text in [
        "my apply (f:int -> int) = f 1; my wrong x = (); my answer = apply wrong",
        "my ignore (f:int -> int) = 1; my wrong x = (); my answer = ignore wrong",
        "my ignore (f:int -> int) = 1; my answer = ignore 1",
        "my ignore (f:int -> int) = 1; my wrong (x:()) = 1; my answer = ignore wrong",
    ] {
        assert!(!CandidateInference::solve(module(text).unwrap()).unwrap().candidate_conflicts().is_empty(), "{text}");
    }
}

#[test]
fn annotation_only_callback_results_reach_the_owning_export_fiber() {
    for (ty, expected) in [("int", CandidateGraphLeaf::IntPositive), ("()", CandidateGraphLeaf::UnitPositive)] {
        let hir = module(&format!("my apply (f:int -> {ty}) = f 1; my alias = apply; my second = apply")).unwrap();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
        for name in ["apply", "alias", "second"] { assert_function_result(&candidate, &hir, name, expected); }
        let hir = module(&format!("my ret (f:int -> {ty}) = f; my returned = ret")).unwrap();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
        let graph = candidate.export(binding(&hir, "returned").definition_root()).unwrap();
        let outer: Vec<_> = value_lowers(&graph, graph.root()).into_iter().filter_map(|node| node.children()).collect();
        assert!(!outer.is_empty());
        for function in outer {
            let inner: Vec<_> = value_lowers(&graph, function[3]).into_iter().filter_map(|node| node.children()).collect();
            assert!(!inner.is_empty());
            for callback in inner { assert_primitive_fiber(&graph, callback[3], expected); }
        }
    }
}

#[test]
fn named_variables_share_the_binding_environment_and_accept_ordinary_union_lowers() {
    for (text, leaf) in [
        ("my ident (x:'a) = x; my answer = ident 1", CandidateGraphLeaf::IntPositive),
        ("my ident (x:'a) = x; my answer = ident ()", CandidateGraphLeaf::UnitPositive),
        ("my apply (f:'a -> 'a) (x:'a) = f x; my ident x = x; my answer = apply ident 1", CandidateGraphLeaf::IntPositive),
        ("my answer = { my first (x:'a) = x; my second (x:'a) = x; my unused = first (); second 1 }", CandidateGraphLeaf::IntPositive),
        ("my ident (x:'a): 'a -> 'a = x; my answer = ident 1", CandidateGraphLeaf::IntPositive),
    ] {
        let hir = module(text).unwrap();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        assert_call_result(&candidate, &hir, "answer", leaf);
    }
    let hir = module("my choose (x:'a) (y:'a) = y; my answer = choose 1 ()").unwrap();
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty(), "ordinary variables admit distinct concrete lowers");
    let graph = candidate.export(binding(&hir, "answer").definition_root()).unwrap();
    let fiber = value_lowers(&graph, graph.root());
    for leaf in [CandidateGraphLeaf::IntPositive, CandidateGraphLeaf::UnitPositive] {
        assert!(fiber.iter().any(|node| node.leaf() == Some(leaf)), "shared row retains {leaf:?}");
    }
}

#[test]
fn two_uses_of_a_local_annotated_callback_binding_freshen_independently() {
    let hir = module("my answer = { my apply (f:'a -> 'a) (x:'a) = f x; my ident x = x; my first = apply ident (); apply ident 1 }").unwrap();
    let source = hir.local_source(binding(&hir, "answer").definition_root()).unwrap().unwrap();
    let uses: Vec<_> = source.expressions().iter().filter(|expr| matches!(&expr.form, LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Local(_) } if spelling.as_ref() == "apply")).collect();
    assert_eq!(uses.len(), 2);
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_call_result(&candidate, &hir, "answer", CandidateGraphLeaf::IntPositive);
    let first = candidate.fresh_use(&uses[0].occurrence).unwrap();
    let second = candidate.fresh_use(&uses[1].occurrence).unwrap();
    let a: Vec<_> = first.rows().collect();
    let b: Vec<_> = second.rows().collect();
    assert!(a.iter().any(|row| row.source_row().is_local()));
    for row in a.iter().filter(|row| row.source_row().is_local()) {
        assert!(b.iter().all(|other| !row.same_identity(other)), "each use owns fresh local rows");
    }
}
