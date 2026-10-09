#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]
use std::sync::Arc;
use yu_hir::shadow::{
    LocalSourceForm, LocalSourceResolution, lower_module_with_local_source,
};
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::{CandidateError, CandidateGraphExport, CandidateGraphLeaf, CandidateGraphNode, CandidateInference};
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
fn annotation_alone_supplies_primitive_body_and_exported_function_results() {
    for (ty, leaf) in [("int", CandidateGraphLeaf::IntPositive), ("()", CandidateGraphLeaf::UnitPositive)] {
        let hir = module(&format!("my ident (x:{ty}) = x; my alias = ident; my second = ident")).unwrap();
        for name in ["ident", "alias", "second"] {
            let source = hir.local_source(binding(&hir, name).definition_root()).unwrap().unwrap();
            assert!(source.expressions().iter().all(|expr| !matches!(
                &expr.form, LocalSourceForm::Integer(_) | LocalSourceForm::Unit | LocalSourceForm::Apply { .. })));
        }
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
        assert_eq!(candidate.source_call_count(), 0);
        for name in ["ident", "alias", "second"] { assert_function_result(&candidate, &hir, name, leaf); }
    }
}

#[test]
fn annotation_only_local_aliases_freshen_independently_and_keep_result_fibers() {
    for (ty, leaf) in [("int", CandidateGraphLeaf::IntPositive), ("()", CandidateGraphLeaf::UnitPositive)] {
        for returned in ["first", "second"] {
            let hir = module(&format!("my answer = {{ my ident (x:{ty}) = x; my first = ident; my second = ident; {returned} }}")).unwrap();
            let source = hir.local_source(binding(&hir, "answer").definition_root()).unwrap().unwrap();
            assert!(source.expressions().iter().all(|expr| !matches!(
                &expr.form, LocalSourceForm::Integer(_) | LocalSourceForm::Unit | LocalSourceForm::Apply { .. })));
            let uses: Vec<_> = source.expressions().iter().filter(|expr| matches!(
                &expr.form, LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Local(_) }
                    if spelling.as_ref() == "ident")).collect();
            assert_eq!(uses.len(), 2);
            let candidate = CandidateInference::solve(hir.clone()).unwrap();
            assert!(candidate.candidate_conflicts().is_empty());
            assert_eq!(candidate.source_call_count(), 0);
            assert_function_result(&candidate, &hir, "answer", leaf);
            let first = candidate.fresh_use(&uses[0].occurrence).unwrap();
            let second = candidate.fresh_use(&uses[1].occurrence).unwrap();
            let a: Vec<_> = first.rows().collect();
            let b: Vec<_> = second.rows().collect();
            assert!(a.iter().any(|row| row.source_row().is_local()));
            for row in a.iter().filter(|row| row.source_row().is_local()) {
                assert!(b.iter().all(|other| !row.same_identity(other)), "local aliases have independent fresh rows");
            }
        }
    }
}

#[test]
fn ignored_and_local_annotated_formals_check_each_actual_argument() {
    for text in [
        "my ignore (x:int) = (); my answer = ignore 1",
        "my answer = { my ignore (x:int) = (); ignore 1 }",
        "my choose (x:int) (y:()) = (); my answer = choose 1 ()",
    ] {
        let hir = module(text).unwrap();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        assert_call_result(&candidate, &hir, "answer", CandidateGraphLeaf::UnitPositive);
    }
    for text in [
        "my answer = { my ignore (x:int) = (); ignore () }",
        "my answer = { my ignore (x:()) = 1; ignore 1 }",
        "my choose (x:int) (y:()) = (); my wrong = choose () ()",
        "my choose (x:int) (y:()) = (); my wrong = choose 1 1",
        "my answer = { my choose (x:int) (y:()) = (); choose () () }",
        "my answer = { my choose (x:int) (y:()) = (); choose 1 1 }",
    ] {
        assert!(!CandidateInference::solve(module(text).unwrap()).unwrap().candidate_conflicts().is_empty(), "{text}");
    }
}

#[test]
fn annotated_value_formals_accept_effectful_actuals_without_result_pollution() {
    for (body, leaf) in [
        ("my ident (x:int) = x; my answer = ident (tick::next())", CandidateGraphLeaf::IntPositive),
        ("my ignore (x:int) = (); my answer = ignore (tick::next())", CandidateGraphLeaf::UnitPositive),
        ("my answer = { my ignore (x:int) = (); ignore (tick::next()) }", CandidateGraphLeaf::UnitPositive),
    ] {
        let hir = module(&format!("act tick:\n    our next: () -> int\n\n{body}")).unwrap();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{body}");
        assert_call_result(&candidate, &hir, "answer", leaf);
    }
}

#[test]
fn primitive_formals_constrain_arguments_and_retain_result_fibers() {
    for (ty, arg, leaf) in [("int", "1", yu_solver::shadow_apply::CandidateGraphLeaf::IntPositive), ("()", "()", yu_solver::shadow_apply::CandidateGraphLeaf::UnitPositive)] {
        let hir = module(&format!("my ident (x:{ty}) = x; my first = ident {arg}; my second = ident {arg}")).unwrap();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
        for name in ["first", "second"] {
            assert_call_result(&candidate, &hir, name, leaf);
        }
    }
    for text in ["my ident (x:int) = x; my wrong = ident ()", "my ignore (x:int) = (); my wrong = ignore ()", "my ignore (x:()) = 1; my wrong = ignore 1", "my choose (x:int) (y:()) = x; my wrong = choose 1 1"] {
        assert!(!CandidateInference::solve(module(text).unwrap()).unwrap().candidate_conflicts().is_empty(), "{text}");
    }
}

#[test]
fn local_and_multiple_formals_keep_their_actual_lambda_layers() {
    for text in ["my choose (x:int) (y:()) = x; my answer = choose 1 ()", "my answer = { my ident (x:int) = x; ident 1 }", "my answer = { my ignore (x:()) = 1; ignore () }"] {
        let hir = module(text).unwrap();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        assert_call_result(&candidate, &hir, "answer", CandidateGraphLeaf::IntPositive);
    }
}

#[test]
fn unsupported_formals_and_whole_local_annotations_are_explicitly_refused() {
    for text in ["act E\nmy f (x:[E] int) = x", "my f (x:int -> int) = x", "my f (x:'a) = x", "my f (x,y) = x", "my outer = { my local:int = 1; local }"] {
        match module(text) {
            Err(_) => {},
            Ok(hir) => assert!(matches!(CandidateInference::solve(hir), Err(CandidateError::Unsupported)), "{text}"),
        }
    }
}
