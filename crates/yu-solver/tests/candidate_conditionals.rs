#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

use std::sync::Arc;
use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution, lower_module_with_local_source};
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
        "valid conditional fixture: {text}"
    );
    Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "conditional-source",
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
fn constant_conditions_keep_both_branch_lower_bounds() {
    for condition in ["true", "false"] {
        let hir = module(&format!("my example = if {condition}: 1 else: \"str\""));
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
        assert_leaves(
            &candidate,
            &hir,
            "example",
            &[
                CandidateGraphLeaf::IntPositive,
                CandidateGraphLeaf::StrPositive,
            ],
        );
    }
}

#[test]
fn homogeneous_and_elsif_branches_contribute_without_selection() {
    for text in [
        "my example = if true: 1 else: 2",
        "my example = if false: 1 elsif true: 2 else: 3",
    ] {
        let hir = module(text);
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
        assert_leaves(
            &candidate,
            &hir,
            "example",
            &[CandidateGraphLeaf::IntPositive],
        );
    }
    let hir = module("my example = if true: 1 elsif false: \"str\" else: ()");
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_leaves(
        &candidate,
        &hir,
        "example",
        &[
            CandidateGraphLeaf::IntPositive,
            CandidateGraphLeaf::StrPositive,
            CandidateGraphLeaf::UnitPositive,
        ],
    );
}

#[test]
fn every_condition_and_every_branch_reaches_its_consumer() {
    for text in [
        "my example = if 1: 1 else: 2",
        "my example = if true: 1 elsif \"str\": 2 else: 3",
        "my consume (x:int) = x; my example = consume (if true: 1 else: \"str\")",
        "my consume (x:bool) = x; my example = consume \"str\"",
        "my consume (x:str) = x; my example = consume false",
    ] {
        let candidate = CandidateInference::solve(module(text)).unwrap();
        assert!(!candidate.candidate_conflicts().is_empty(), "{text}");
    }
}

#[test]
fn boolean_and_string_annotations_prepare_leaves_without_literals() {
    let hir = module(
        "my bool_id (x:bool) = x; my str_id (x:str) = x; my b:bool -> bool = bool_id; my s:str -> str = str_id",
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    for (name, negative, positive) in [
        (
            "b",
            CandidateGraphLeaf::BoolNegative,
            CandidateGraphLeaf::BoolPositive,
        ),
        (
            "s",
            CandidateGraphLeaf::StrNegative,
            CandidateGraphLeaf::StrPositive,
        ),
    ] {
        let graph = candidate.export(root(&hir, name)).unwrap();
        let functions: Vec<_> = value_lowers(&graph, graph.root())
            .into_iter()
            .filter_map(|node| node.children())
            .collect();
        assert!(
            functions
                .iter()
                .any(|children| children[0].leaf() == Some(negative)
                    && children[3].leaf() == Some(positive)),
            "{name} retains its primitive signature"
        );
    }
}

#[test]
fn parameter_module_local_and_ascribed_branch_endpoints_use_ordinary_routes() {
    for text in [
        "my choose condition x = if condition: x else: \"str\"; my example = choose true 1",
        "my value = 1; my example = if true: value else: \"str\"",
        "my example = { my value = 1; if false: value else: (\"str\" as str) }",
        "my example = if true: (if false: 1 else: \"str\") else: ()",
        "my loop condition = if condition: 1 else: loop true; my example = loop false",
    ] {
        let hir = module(text);
        let candidate = CandidateInference::solve(hir.clone())
            .unwrap_or_else(|error| panic!("{text}: {error:?}"));
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        assert_leaves(
            &candidate,
            &hir,
            "example",
            &[CandidateGraphLeaf::IntPositive],
        );
    }
}

#[test]
fn conditional_function_generalizes_and_freshens_local_uses() {
    let hir = module(
        "my example = { my choose condition x = if condition: x else: x; my first = choose true 1; my second = choose false \"str\"; second }",
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_leaves(
        &candidate,
        &hir,
        "example",
        &[CandidateGraphLeaf::StrPositive],
    );
    let source = hir.local_source(root(&hir, "example")).unwrap().unwrap();
    let uses: Vec<_> = source
        .expressions()
        .iter()
        .filter(|expr| {
            matches!(&expr.form,
        LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Local(_) }
            if spelling.as_ref() == "choose")
        })
        .collect();
    assert_eq!(uses.len(), 2);
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
fn many_arms_keep_late_branch_evidence_without_occurrence_slot_exhaustion() {
    let mut text = String::from("my example = if true: 1");
    for _ in 0..60 {
        text.push_str(" elsif false: 2");
    }
    text.push_str(" elsif false: \"str\" else: ()");
    let hir = module(&text);
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_leaves(
        &candidate,
        &hir,
        "example",
        &[
            CandidateGraphLeaf::IntPositive,
            CandidateGraphLeaf::StrPositive,
            CandidateGraphLeaf::UnitPositive,
        ],
    );
}

#[test]
fn non_boolean_condition_after_many_arms_still_conflicts() {
    let mut text = String::from("my example = if true: 1");
    for _ in 0..60 {
        text.push_str(" elsif false: 2");
    }
    text.push_str(" elsif 1: 3 else: 4");
    let candidate = CandidateInference::solve(module(&text)).unwrap();
    assert!(!candidate.candidate_conflicts().is_empty());
}

#[test]
fn all_child_computation_effects_reach_the_conditional_effect() {
    for text in [
        "act tick:\n    our next: () -> int\n\nmy example:[] int = if true: 1 else: tick::next()",
        "act tick:\n    our next: () -> int\n\nmy example:[] int = if false: tick::next() else: 1",
        "act tick:\n    our test: () -> bool\n\nmy example:[] int = if tick::test(): 1 else: 2",
        "act tick:\n    our test: () -> bool\n\nmy example:[] int = if true: 1 elsif tick::test(): 2 else: 3",
    ] {
        let candidate = CandidateInference::solve(module(text)).unwrap();
        assert!(!candidate.candidate_conflicts().is_empty(), "{text}");
    }
    let candidate =
        CandidateInference::solve(module("my example:[] int = if true: 1 else: 2")).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
}

#[test]
fn local_fresh_uses_transport_both_captured_branch_literals() {
    let hir = module(
        "my example = { my choose condition = if condition: 1 else: \"str\"; my first = choose true; my second = choose false; second }",
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_leaves(
        &candidate,
        &hir,
        "example",
        &[
            CandidateGraphLeaf::IntPositive,
            CandidateGraphLeaf::StrPositive,
        ],
    );
    let source = hir.local_source(root(&hir, "example")).unwrap().unwrap();
    let uses: Vec<_> = source
        .expressions()
        .iter()
        .filter(|expr| {
            matches!(&expr.form,
        LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Local(_) }
            if spelling.as_ref() == "choose")
        })
        .collect();
    assert_eq!(uses.len(), 2);
    for occurrence in uses {
        assert!(candidate.fresh_use(&occurrence.occurrence).is_some());
    }

    let rejected = module(
        "my consume (x:int) = x; my example = { my choose condition = if condition: 1 else: \"str\"; my first = choose true; consume (choose false) }",
    );
    let candidate = CandidateInference::solve(rejected).unwrap();
    assert!(!candidate.candidate_conflicts().is_empty());
}
