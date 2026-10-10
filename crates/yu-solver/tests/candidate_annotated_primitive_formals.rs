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
    component_lowers(graph, start, yu_types::ComponentKind::Value)
}

fn component_lowers<'a>(graph: &CandidateGraphExport<'a>, start: CandidateGraphNode<'a>, kind: yu_types::ComponentKind) -> Vec<CandidateGraphNode<'a>> {
    let mut pending = vec![start];
    let mut visited: Vec<CandidateGraphNode<'a>> = Vec::new();
    while let Some(node) = pending.pop() {
        if visited.iter().any(|prior| prior.same_identity(node)) { continue; }
        visited.push(node);
        for bound in graph.bounds() {
            if bound.kind() != kind { continue; }
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
fn unfinished_formals_and_unsupported_whole_local_annotations_are_explicitly_refused() {
    for text in ["act E\nmy f (x:[E] int) = x", "my f (x,y) = x", "my outer = { my local:_ = 1; local }", "act E\nmy outer = { my local:[E] int = 1; local }"] {
        match module(text) {
            Err(_) => {},
            Ok(hir) => assert!(matches!(CandidateInference::solve(hir), Err(CandidateError::Unsupported)), "{text}"),
        }
    }
}

#[test]
fn whole_local_primitives_check_the_whole_initializer_and_expose_the_annotation() {
    for (ty, value, leaf) in [("int", "1", CandidateGraphLeaf::IntPositive), ("()", "()", CandidateGraphLeaf::UnitPositive)] {
        let hir = module(&format!("my outer = {{ my local:{ty} = {{ {value} }}; local }}")).unwrap();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
        assert_call_result(&candidate, &hir, "outer", leaf);
    }
    for text in [
        "my outer = { my local:int = (); local }",
        "my outer = { my local:() = 1; local }",
        "my outer = { my local x:int = x; local }",
        "my outer = { my local x:() = x; local }",
    ] {
        assert!(!CandidateInference::solve(module(text).unwrap()).unwrap().candidate_conflicts().is_empty(), "{text}");
    }
}

#[test]
fn whole_local_annotation_alone_supplies_results_and_freshens_each_use() {
    for (ty, leaf) in [("int", CandidateGraphLeaf::IntPositive), ("()", CandidateGraphLeaf::UnitPositive)] {
        let hir = module(&format!("my outer x = {{ my local:{ty} = x; my first = local; my second = local; second }}")).unwrap();
        let source = hir.local_source(binding(&hir, "outer").definition_root()).unwrap().unwrap();
        assert!(source.expressions().iter().all(|expr| !matches!(expr.form, LocalSourceForm::Integer(_) | LocalSourceForm::Unit | LocalSourceForm::Apply { .. })));
        let uses: Vec<_> = source.expressions().iter().filter(|expr| matches!(&expr.form, LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Local(_) } if spelling.as_ref() == "local")).collect();
        assert_eq!(uses.len(), 2);
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
        assert_function_result(&candidate, &hir, "outer", leaf);
        let first = candidate.fresh_use(&uses[0].occurrence).unwrap();
        let second = candidate.fresh_use(&uses[1].occurrence).unwrap();
        let a: Vec<_> = first.rows().collect();
        let b: Vec<_> = second.rows().collect();
        assert!(a.iter().any(|row| row.source_row().is_local()));
        for row in a.iter().filter(|row| row.source_row().is_local()) {
            assert!(b.iter().all(|other| !row.same_identity(other)));
        }
    }
}

#[test]
fn nested_annotated_locals_preserve_shadowed_binding_identity() {
    let hir = module("my outer = { my local:int = 1; my nested:() = { my local:() = (); local }; local }").unwrap();
    let source = hir.local_source(binding(&hir, "outer").definition_root()).unwrap().unwrap();
    let locals: Vec<_> = source.bindings().iter().filter(|binding| binding.spelling.as_ref() == "local").collect();
    assert_eq!(locals.len(), 2);
    assert_ne!(locals[0].id, locals[1].id);
    for local in locals {
        assert!(source.expressions().iter().any(|expr| matches!(&expr.form, LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &local.id)));
    }
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_call_result(&candidate, &hir, "outer", CandidateGraphLeaf::IntPositive);
}

#[test]
fn effectful_whole_local_initializer_keeps_a_primitive_value_interface() {
    let hir = module("act tick:\n    our next: () -> int\n\nmy outer = { my local:int = tick::next(); my first = local; local }").unwrap();
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.source_call_count(), 1);
    assert_call_result(&candidate, &hir, "outer", CandidateGraphLeaf::IntPositive);
}

#[test]
fn whole_local_ground_functions_check_composed_argument_and_result_polarity() {
    for text in [
        "my outer = { my local x:int -> int = x; local 1 }",
        "my outer = { my local f:(int -> int) -> int = f 1; local { my ident x = x; ident } }",
        "my outer = { my local x y:int -> () -> int = x; local 1 () }",
    ] {
        let hir = module(text).unwrap();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        assert_call_result(&candidate, &hir, "outer", CandidateGraphLeaf::IntPositive);
    }
    for text in [
        "my outer = { my local:int -> int = 1; local }",
        "my outer = { my local x:int -> int = (); local }",
        "my outer = { my local f:(int -> int) -> int = f (); local }",
        "my outer = { my local x y:int -> () -> int = y; local }",
        "my outer = { my local x:int -> int = x; local () }",
    ] {
        assert!(!CandidateInference::solve(module(text).unwrap()).unwrap().candidate_conflicts().is_empty(), "{text}");
    }
}

#[test]
fn whole_local_ground_functions_freshen_uses_and_preserve_nested_shadowing() {
    let hir = module("my outer = { my local x:int -> int = x; my first = local; my second = local; my nested = { my local x:() -> () = x; local () }; second 1 }").unwrap();
    let source = hir.local_source(binding(&hir, "outer").definition_root()).unwrap().unwrap();
    let locals: Vec<_> = source.bindings().iter().filter(|binding| binding.spelling.as_ref() == "local").collect();
    assert_eq!(locals.len(), 2);
    assert_ne!(locals[0].id, locals[1].id);
    let uses: Vec<_> = source.expressions().iter().filter(|expr| matches!(&expr.form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &locals[0].id)).collect();
    assert_eq!(uses.len(), 2);
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_call_result(&candidate, &hir, "outer", CandidateGraphLeaf::IntPositive);
    let first = candidate.fresh_use(&uses[0].occurrence).unwrap();
    let second = candidate.fresh_use(&uses[1].occurrence).unwrap();
    let a: Vec<_> = first.rows().collect();
    let b: Vec<_> = second.rows().collect();
    assert!(a.iter().any(|row| row.source_row().is_local()));
    for row in a.iter().filter(|row| row.source_row().is_local()) {
        assert!(b.iter().all(|other| !row.same_identity(other)));
    }
}

#[test]
fn effectful_whole_local_function_initializer_runs_once_with_pure_lookups() {
    let hir = module("act tick:\n    our next: () -> (int -> int)\n\nmy outer = { my local:int -> int = tick::next(); my first = local; local }").unwrap();
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.source_call_count(), 1);
    assert_function_result(&candidate, &hir, "outer", CandidateGraphLeaf::IntPositive);
}


#[test]
fn whole_local_effect_annotations_keep_root_and_negative_rows_unavailable() {
    for text in [
        "my outer = { my local:[] int = 1; local }",
        "act E\nmy outer = { my local:(int -> [E] int) -> int = 1; local }",
    ] {
        let hir = module(text).unwrap();
        assert!(matches!(CandidateInference::solve(hir), Err(CandidateError::Unsupported)), "{text}");
    }
}

#[test]
fn whole_local_covariant_empty_effect_rows_are_checked_and_exposed() {
    let hir = module("my id x = x; my outer = { my local:int -> [] int = id; local }").unwrap();
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert!(candidate.export(binding(&hir, "outer").definition_root()).is_ok());

    let nested = module("my higher f = f 1; my outer = { my local:([] int -> int) -> int = higher; local }").unwrap();
    let candidate = CandidateInference::solve(nested.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty(), "{:?}", candidate.candidate_conflicts());
    assert!(candidate.export(binding(&nested, "outer").definition_root()).is_ok());
}

#[test]
fn whole_local_named_values_infer_from_initializers_and_nested_functions() {
    for text in [
        "my outer = { my local:'a = 1; local }",
        "my outer = { my local x:'a -> 'a = x; local 1 }",
        "my outer = { my local f:('a -> 'a) -> 'a = f 1; local { my ident x = x; ident } }",
        "my outer = { my local x y:'a -> () -> 'a = x; local 1 () }",
        "my outer = { my local (x:'a):'a -> 'a = x; local 1 }",
    ] {
        let hir = module(text).unwrap();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        assert_call_result(&candidate, &hir, "outer", CandidateGraphLeaf::IntPositive);
    }
    for text in [
        "my outer = { my local:int -> 'a = 1; local }",
        "my outer = { my local:('a -> int) -> int = 1; local }",
        "my outer = { my local (x:'a):'a -> () = x; local 1 }",
    ] {
        assert!(!CandidateInference::solve(module(text).unwrap()).unwrap().candidate_conflicts().is_empty(), "{text}");
    }
}

#[test]
fn whole_local_named_bindings_isolate_names_and_freshen_function_uses() {
    let hir = module("my outer = { my local (x:'a):'a -> 'a = x; my first = local; my second = local; my nested = { my local (x:'a):'a -> 'a = x; local () }; my ignored = first (); second 1 }").unwrap();
    let source = hir.local_source(binding(&hir, "outer").definition_root()).unwrap().unwrap();
    let locals: Vec<_> = source.bindings().iter().filter(|binding| binding.spelling.as_ref() == "local").collect();
    assert_eq!(locals.len(), 2);
    assert_ne!(locals[0].id, locals[1].id);
    let uses: Vec<_> = source.expressions().iter().filter(|expr| matches!(&expr.form,
        LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &locals[0].id)).collect();
    assert_eq!(uses.len(), 2);
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_call_result(&candidate, &hir, "outer", CandidateGraphLeaf::IntPositive);
    let first_use = candidate.fresh_use(&uses[0].occurrence).unwrap();
    let second_use = candidate.fresh_use(&uses[1].occurrence).unwrap();
    let first: Vec<_> = first_use.rows().collect();
    let second: Vec<_> = second_use.rows().collect();
    assert!(first.iter().any(|row| row.source_row().is_local()));
    for row in first.iter().filter(|row| row.source_row().is_local()) {
        assert!(second.iter().all(|other| !row.same_identity(other)));
    }
}

#[test]
fn whole_local_named_values_preserve_captured_provider_constraints() {
    let hir = module("my outer x = { my local:'a = x; my first = local; local }; my answer = outer 1").unwrap();
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_call_result(&candidate, &hir, "answer", CandidateGraphLeaf::IntPositive);
}

#[test]
fn effectful_whole_local_named_initializer_runs_once() {
    let hir = module("act tick:\n    our next: () -> int\n\nmy outer ignored = { my local:'a = tick::next(); my first = local; local }").unwrap();
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_function_result(&candidate, &hir, "outer", CandidateGraphLeaf::IntPositive);
    let graph = candidate.export(binding(&hir, "outer").definition_root()).unwrap();
    let functions: Vec<_> = value_lowers(&graph, graph.root()).into_iter()
        .filter(|node| node.polarity() == yu_solver::Polarity::Positive)
        .filter_map(|node| node.children()).collect();
    assert!(!functions.is_empty());
    for children in functions {
        let effects = component_lowers(&graph, children[2], yu_types::ComponentKind::Effect);
        // The public graph exposes operands by shape, but not their family.
        // Leaf, Row and Function are the other three exhaustive node forms.
        assert!(effects.iter().any(|node| node.polarity() == yu_solver::Polarity::Positive
            && node.leaf().is_none() && node.row().is_none() && node.children().is_none()),
            "the function result effect retains initializer effect support");
    }
}
