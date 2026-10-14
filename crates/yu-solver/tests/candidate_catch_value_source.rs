#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

use std::sync::Arc;
use yu_hir::shadow::{lower_module_with_local_source};
use yu_hir::{
    DefinitionRootId, FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports,
};
use yu_solver::shadow_apply::{
    CandidateGraphExport, CandidateGraphLeaf, CandidateGraphNode, CandidateInference,
};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(
        parsed.structural_recoveries().is_empty(),
        "valid Catch fixture: {text}"
    );
    Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "catch-source",
                "source.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    )
}

fn root<'a>(hir: &'a HirModule, name: &str) -> &'a DefinitionRootId {
    hir.items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == name => {
                Some(binding.definition_root())
            }
            _ => None,
        })
        .expect("source binding")
}

// Bounds can be retained as either a lower on their upper row or an upper on
// their lower row. Follow the actual directed relation across both stores.
fn value_lowers<'a>(
    graph: &CandidateGraphExport<'a>,
    start: CandidateGraphNode<'a>,
) -> Vec<CandidateGraphNode<'a>> {
    let mut pending = vec![start];
    let mut visited: Vec<CandidateGraphNode<'a>> = Vec::new();
    while let Some(node) = pending.pop() {
        if visited.iter().any(|prior| prior.same_identity(node)) {
            continue;
        }
        visited.push(node);
        for bound in graph.bounds() {
            if bound.kind() != yu_types::ComponentKind::Value {
                continue;
            }
            let upper = bound.upper();
            let same_row = node
                .row()
                .is_some_and(|row| upper.row().is_some_and(|other| row.same_identity(other)));
            if upper.same_identity(node) || same_row {
                pending.push(bound.lower());
            }
        }
    }
    visited
}

fn assert_leaves(
    candidate: &CandidateInference,
    hir: &HirModule,
    name: &str,
    expected: &[CandidateGraphLeaf],
) {
    let graph = candidate.export(root(hir, name)).unwrap();
    let lowers = value_lowers(&graph, graph.root());
    for leaf in expected {
        assert!(
            lowers.iter().any(|node| node.leaf() == Some(*leaf)),
            "{name} retains {leaf:?}"
        );
    }
}

#[test]
fn identity_and_transformed_normal_values_join_every_arm() {
    for (text, leaves) in [
        ("my result = catch 1 { x -> x }", vec![CandidateGraphLeaf::IntPositive]),
        ("my result = catch 1 { x -> \"str\" }", vec![CandidateGraphLeaf::StrPositive]),
        ("my result = catch 1 { x -> x, _ -> \"str\" }", vec![CandidateGraphLeaf::IntPositive, CandidateGraphLeaf::StrPositive]),
        ("my result = catch (if true: 1 else: \"str\") { x -> x }", vec![CandidateGraphLeaf::IntPositive, CandidateGraphLeaf::StrPositive]),
    ] {
        let hir = module(text);
        let candidate = CandidateInference::solve(hir.clone()).unwrap_or_else(|error| panic!("{text}: {error:?}"));
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        assert_leaves(&candidate, &hir, "result", &leaves);
    }
}

#[test]
fn binder_callable_alias_and_local_fresh_uses_keep_the_original_value() {
    for (text, expected) in [
        ("my id x = x; my result = catch id { f -> f 1 }", CandidateGraphLeaf::IntPositive),
        ("my id x = x; my result = catch id { f -> { my alias = f; alias 1 } }", CandidateGraphLeaf::IntPositive),
        ("my result = { my id x = catch x { y -> y }; my a:int = id 1; id \"str\" }", CandidateGraphLeaf::StrPositive),
    ] {
        let hir = module(text);
        let candidate = CandidateInference::solve(hir.clone()).unwrap_or_else(|error| panic!("{text}: {error:?}"));
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        assert_leaves(&candidate, &hir, "result", &[expected]);
        let graph = candidate.export(root(&hir, "result")).unwrap();
        let lowers = value_lowers(&graph, graph.root());
        let foreign = if expected == CandidateGraphLeaf::IntPositive { CandidateGraphLeaf::StrPositive } else { CandidateGraphLeaf::IntPositive };
        assert!(!lowers.iter().any(|node| node.leaf() == Some(foreign)), "fresh result: {text}");
    }
    let candidate = CandidateInference::solve(module("my result = { my id x = catch x { y -> y }; my a:int = id \"str\"; id 1 }")).unwrap();
    assert!(!candidate.candidate_conflicts().is_empty());
    let hir = module("my result = catch 1 { x -> catch x { x -> x }, _ -> \"str\" }");
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_leaves(&candidate, &hir, "result", &[CandidateGraphLeaf::IntPositive, CandidateGraphLeaf::StrPositive]);
}

#[test]
fn both_scrutinee_and_outside_arm_effects_reach_catch_output() {
    let declarations = "act tick:\n    our next: () -> int\nact tock:\n    our next: () -> int\n\n";
    for body in ["catch tick::next() { x -> x }", "catch 1 { x -> tock::next() }", "catch tick::next() { x -> tock::next(), _ -> 1 }"] {
        let inferred = CandidateInference::solve(module(&format!("{declarations}my result = {body}"))).unwrap_or_else(|error| panic!("{body}: {error:?}"));
        assert!(inferred.candidate_conflicts().is_empty(), "{body}");
        let constrained = CandidateInference::solve(module(&format!("{declarations}my result: [] int = {body}"))).unwrap_or_else(|error| panic!("{body}: {error:?}"));
        assert!(!constrained.candidate_conflicts().is_empty(), "effects cannot disappear: {body}");
    }
    let body = "catch tick::next() { x -> tock::next(), _ -> 1 }";
    for (row, valid) in [("[tick]", false), ("[tock]", false), ("[tick, tock]", true)] {
        let text = format!("{declarations}my result: {row} int = {body}");
        let candidate = CandidateInference::solve(module(&text)).unwrap_or_else(|error| panic!("{text}: {error:?}"));
        assert_eq!(candidate.candidate_conflicts().is_empty(), valid, "{text}");
    }

}

#[test]
fn later_total_arms_still_contribute_constraints() {
    let candidate = CandidateInference::solve(module("my consume (x:int) = x; my result = consume (catch 1 { x -> x, _ -> \"str\" })")).unwrap();
    assert!(!candidate.candidate_conflicts().is_empty());
}

#[test]
fn binder_ascriptions_check_original_values_with_and_without_group_facades() {
    for (body, valid) in [
        ("x as int", true), ("(x) as int", true),
        ("x as str", false), ("(x) as str", false),
    ] {
        let text = format!("my result = catch 1 {{ x -> {body} }}");
        let hir = module(&text);
        let candidate = CandidateInference::solve(hir.clone()).unwrap_or_else(|error| panic!("{text}: {error:?}"));
        assert_eq!(candidate.candidate_conflicts().is_empty(), valid, "{text}");
        if valid { assert_leaves(&candidate, &hir, "result", &[CandidateGraphLeaf::IntPositive]); }
    }
}

#[test]
fn names_and_operation_families_resolve_authentic_tokens_with_boundary_trivia() {
    for text in [
        "my value = 1; my result = catch /* before */ value /* after */ { x -> /* arm */ x }",
        "my value = 1; my result = catch value {\n  x -> x\n  _ -> value\n}",
        "act tick:\n    our next: () -> int\n\nmy result: [tick] int = catch /* family\n comment */ tick::next() /* suffix */ { x -> x }",
    ] {
        let hir = module(text);
        let candidate = CandidateInference::solve(hir.clone()).unwrap_or_else(|error| panic!("{text}: {error:?}"));
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        assert_leaves(&candidate, &hir, "result", &[CandidateGraphLeaf::IntPositive]);
    }
}
