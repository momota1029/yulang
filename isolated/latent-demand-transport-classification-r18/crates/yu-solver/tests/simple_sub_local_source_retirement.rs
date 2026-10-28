#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

use std::sync::Arc;
use yu_hir::{DefinitionRootId, FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution, ShadowArtifact,
    lower_module_with_local_source, lower_module_with_shadow_local_binding};
use yu_solver::shadow_apply::{CandidateError, CandidateGraphExport, CandidateGraphLeaf,
    CandidateGraphNode, CandidateInference, CandidateValueObservation};
use yu_solver::Polarity;
use yu_types::ComponentKind;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str, fixture: bool) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(source.clone(), Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()));
    let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
        "local-retirement", "source.yu")));
    Arc::new(if fixture {
        let artifact = Arc::new(ShadowArtifact::from_parsed(parsed.clone()).unwrap());
        lower_module_with_shadow_local_binding(identity, &parsed, SemanticImports::empty(), artifact).unwrap()
    } else {
        lower_module_with_local_source(identity, &parsed, SemanticImports::empty()).unwrap()
    })
}

fn root<'a>(hir: &'a HirModule, name: &str) -> &'a DefinitionRootId {
    hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding.definition_root()),
        _ => None,
    }).expect("source binding")
}

fn same(a: CandidateGraphNode<'_>, b: CandidateGraphNode<'_>) -> bool {
    a.same_identity(b) || matches!((a.row(), b.row()), (Some(a), Some(b)) if a.same_identity(b))
}

fn reaches<'a>(graph: &CandidateGraphExport<'a>, lower: CandidateGraphNode<'a>, upper: CandidateGraphNode<'a>) -> bool {
    let mut pending = vec![lower];
    let mut seen = Vec::new();
    while let Some(node) = pending.pop() {
        if same(node, upper) { return true; }
        if seen.iter().copied().any(|old| same(old, node)) { continue; }
        seen.push(node);
        for bound in graph.bounds().filter(|bound| bound.kind() == ComponentKind::Value) {
            if same(bound.lower(), node) { pending.push(bound.upper()); }
        }
    }
    false
}

fn assert_function_and_effect_flow(graph: &CandidateGraphExport<'_>) {
    assert!(graph.bounds().any(|bound| bound.kind() == ComponentKind::Value
        && bound.lower().children().is_some()
        && bound.lower().polarity() == Polarity::Positive
        && reaches(graph, bound.upper(), graph.root())));
    assert!(graph.rows().any(|row| row.kind() == ComponentKind::Effect));
    assert!(graph.bounds().any(|bound| bound.kind() == ComponentKind::Effect));
}

#[test]
fn fixture_only_carrier_is_historical_and_generic_source_retains_capture() {
    let text = "my apply f = { my step x = f x; step }";
    let historical = module(text, true);
    assert!(historical.shadow_local_binding(root(&historical, "apply")).unwrap().is_some());
    assert!(historical.local_source(root(&historical, "apply")).unwrap().is_none());
    assert!(CandidateValueObservation::solve(historical.clone()).is_ok());
    assert!(matches!(CandidateInference::solve(historical), Err(CandidateError::Unsupported)));

    let hir = module(text, false);
    assert!(hir.shadow_local_binding(root(&hir, "apply")).unwrap().is_none());
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let graph = candidate.export(root(&hir, "apply")).unwrap();
    assert_function_and_effect_flow(&graph);
    assert!(graph.bounds().any(|bound| bound.kind() == ComponentKind::Value
        && bound.upper().polarity() == Polarity::Negative
        && bound.upper().children().is_some()), "captured formal retains actual invocation demand");
}

#[test]
fn multiple_captures_retain_both_invocation_demands() {
    let hir = module("my compose f g = { my relay x = f (g x); relay }", false);
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let graph = candidate.export(root(&hir, "compose")).unwrap();
    assert_function_and_effect_flow(&graph);
    let mut demands = Vec::new();
    for bound in graph.bounds().filter(|bound| bound.kind() == ComponentKind::Value) {
        let node = bound.upper();
        if node.polarity() == Polarity::Negative && node.children().is_some()
            && !demands.iter().copied().any(|old| same(old, node)) {
            demands.push(node);
        }
    }
    assert!(demands.len() >= 2, "both captured functions retain separate invocation demands");
}

#[test]
fn different_initializers_and_nested_renamed_blocks_retain_integer_results() {
    for text in [
        "my value = { my seed = 1; seed }",
        "my value = { my identity x = x; identity 1 }",
        "my value = { my renamed = { my inner x = x; inner }; renamed 1 }",
    ] {
        let hir = module(text, false);
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
        let graph = candidate.export(root(&hir, "value")).unwrap();
        assert!(graph.bounds().any(|bound| bound.kind() == ComponentKind::Value
            && bound.lower().leaf() == Some(CandidateGraphLeaf::IntPositive)
            && reaches(&graph, bound.upper(), graph.root())), "{text}");
    }
}

#[test]
fn independent_local_uses_have_distinct_value_and_effect_images() {
    let hir = module("my result = { my identity x = x; my first = identity 1; identity identity }", false);
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let source = hir.local_source(root(&hir, "result")).unwrap().unwrap();
    let uses: Vec<_> = source.expressions().iter().filter(|expression| matches!(
        &expression.form, LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Local(_) }
            if spelling.as_ref() == "identity")).collect();
    assert_eq!(uses.len(), 3);
    let first = candidate.fresh_use(&uses[0].occurrence).unwrap();
    let second = candidate.fresh_use(&uses[1].occurrence).unwrap();
    let a: Vec<_> = first.rows().collect();
    let b: Vec<_> = second.rows().collect();
    for kind in [ComponentKind::Value, ComponentKind::Effect] {
        assert!(a.iter().any(|row| row.kind() == kind && row.source_row().is_local()));
        assert!(b.iter().any(|row| row.kind() == kind && row.source_row().is_local()));
    }
    for row in a.iter().filter(|row| row.source_row().is_local()) {
        assert!(b.iter().all(|other| !row.same_identity(other)));
    }
    assert_function_and_effect_flow(&candidate.export(root(&hir, "result")).unwrap());
}

#[test]
fn outer_application_later_constrains_the_live_local_scheme() {
    // The apply body installs relay before the incoming succ use constrains g.
    let hir = module("my succ x = 1; my apply g = { my relay x = g x; relay }; my answer = apply succ 1", false);
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let graph = candidate.export(root(&hir, "answer")).unwrap();
    assert!(graph.bounds().any(|bound| bound.kind() == ComponentKind::Value
        && bound.lower().leaf() == Some(CandidateGraphLeaf::IntPositive)
        && reaches(&graph, bound.upper(), graph.root())));
    let source = hir.local_source(root(&hir, "apply")).unwrap().unwrap();
    let relay = source.expressions().iter().find(|expression| matches!(&expression.form,
        LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Local(_) }
            if spelling.as_ref() == "relay")).unwrap();
    let fresh = candidate.fresh_use(&relay.occurrence).unwrap();
    assert!(fresh.rows().any(|row| row.kind() == ComponentKind::Effect));
}

#[test]
fn recursive_definition_is_fresh_at_external_uses() {
    let hir = module(
        "my loop x = loop x; my integer: int = loop 1; my identity x = x; my function: int -> int = loop identity",
        false,
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());

    let mut uses = Vec::new();
    for name in ["integer", "function"] {
        let source = hir.local_source(root(&hir, name)).unwrap().unwrap();
        uses.extend(source.expressions().iter().filter(|expression| matches!(
            &expression.form,
            LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::ModuleDef(_) }
                if spelling.as_ref() == "loop"
        )).map(|expression| candidate.fresh_use(&expression.occurrence).unwrap()));
    }
    assert_eq!(uses.len(), 2, "each external recursive use has its own source occurrence");
    let first: Vec<_> = uses[0].rows().filter(|row| row.source_row().is_local()).collect();
    let second: Vec<_> = uses[1].rows().filter(|row| row.source_row().is_local()).collect();
    assert!(!first.is_empty() && !second.is_empty(), "both uses instantiate recursive scheme rows");
    for row in first {
        assert!(second.iter().all(|other| !row.same_identity(other)), "external recursive uses receive independent row images");
    }
}

#[test]
fn mutually_recursive_definitions_accept_external_uses_at_distinct_shapes() {
    let hir = module(
        "my even x = odd x; my odd x = even x; my integer: int = even 1; my identity x = x; my function: int -> int = odd identity",
        false,
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());

    for (name, target) in [("integer", "even"), ("function", "odd")] {
        let source = hir.local_source(root(&hir, name)).unwrap().unwrap();
        let occurrence = source
            .expressions()
            .iter()
            .find(|expression| matches!(
                &expression.form,
                LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::ModuleDef(_) }
                    if spelling.as_ref() == target
            ))
            .map(|expression| &expression.occurrence)
            .unwrap();
        let use_image = candidate.fresh_use(occurrence).unwrap();
        assert!(
            use_image.rows().any(|row| row.source_row().is_local()),
            "each external member use instantiates SCC scheme rows"
        );
    }
}
