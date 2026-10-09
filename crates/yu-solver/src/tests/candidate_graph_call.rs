//! Two bounded source observations of the private candidate graph.
//! These are retained scalar relations and fresh row maps, not complete Call,
//! source admission, public scheme correspondence, or effect-label semantics.
use super::*;
use crate::shadow_apply::{
    CandidateGraphExport, CandidateGraphLeaf, CandidateGraphNode, CandidateInference,
};

fn candidate_call_hir(text: &str) -> Arc<HirModule> {
    let source: Arc<yu_syntax::SourceText> = Arc::from(text);
    let parsed = yu_syntax::parse_file(
        source.clone(),
        Arc::new(yu_syntax::scan_header(source)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()),
    );
    Arc::new(
        yu_hir::shadow::lower_module_with_shadow_applications(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "candidate-graph",
                "call.yu",
            ))),
            &parsed,
            yu_hir::SemanticImports::empty(),
        )
        .unwrap(),
    )
}

fn candidate_call_root<'a>(hir: &'a HirModule, name: &str) -> &'a DefinitionRootId {
    hir.items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == name => {
                Some(binding.definition_root())
            }
            _ => None,
        })
        .expect("actual source binding")
}

// Bounds connect opposite-polarity endpoints of one retained row. Comparing
// row identity here does not identify distinct source and fresh graph owners.
fn candidate_call_endpoint_same(a: CandidateGraphNode<'_>, b: CandidateGraphNode<'_>) -> bool {
    a.same_identity(b)
        || match (a.row(), b.row()) {
            (Some(a), Some(b)) => a.same_identity(b),
            _ => false,
        }
}

fn candidate_call_reaches<'a>(
    graph: &CandidateGraphExport<'a>,
    lower: CandidateGraphNode<'a>,
    upper: CandidateGraphNode<'a>,
    kind: ComponentKind,
) -> bool {
    let mut pending = vec![lower];
    let mut visited = Vec::new();
    while let Some(node) = pending.pop() {
        if candidate_call_endpoint_same(node, upper) {
            return true;
        }
        if visited
            .iter()
            .copied()
            .any(|old| candidate_call_endpoint_same(old, node))
        {
            continue;
        }
        visited.push(node);
        for bound in graph.bounds().filter(|bound| bound.kind() == kind) {
            if candidate_call_endpoint_same(bound.lower(), node) {
                pending.push(bound.upper());
            }
        }
    }
    false
}

fn candidate_call_function<'a>(graph: &CandidateGraphExport<'a>) -> [CandidateGraphNode<'a>; 4] {
    let function = graph
        .bounds()
        .find_map(|bound| {
            let lower = bound.lower();
            (bound.kind() == ComponentKind::Value
                && lower.polarity() == Polarity::Positive
                && lower.children().is_some()
                && candidate_call_reaches(graph, bound.upper(), graph.root(), ComponentKind::Value))
            .then_some(lower)
        })
        .expect("positive function lower reaches source definition root");
    let children = function.children().unwrap();
    for (node, kind, polarity) in [
        (children[0], ComponentKind::Value, Polarity::Negative),
        (children[2], ComponentKind::Effect, Polarity::Positive),
        (children[3], ComponentKind::Value, Polarity::Positive),
    ] {
        assert_eq!(node.polarity(), polarity);
        assert_eq!(node.row().expect("symbolic function port").kind(), kind);
    }
    assert_eq!(children[1].polarity(), Polarity::Negative);
    let entry_effect = children[1].row().expect("symbolic entry effect port");
    assert_eq!(entry_effect.kind(), ComponentKind::Effect);
    assert!(
        !entry_effect.same_identity(children[2].row().unwrap()),
        "entry and invocation effects have distinct rows"
    );
    assert!(
        candidate_call_reaches(graph, children[1], children[2], ComponentKind::Effect),
        "entry effect reaches invocation effect"
    );
    children
}

fn candidate_call_capture(candidate: &CandidateInference, root: &DefinitionRootId) {
    let graph = candidate.export(root).unwrap();
    let ports = candidate_call_function(&graph);
    let formal = ports[0].row().unwrap();
    assert!(
        !graph.bounds().any(|bound| {
            bound.kind() == ComponentKind::Value
                && bound.lower().polarity() == Polarity::Positive
                && bound.lower().children().is_some()
                && candidate_call_reaches(&graph, bound.upper(), ports[0], ComponentKind::Value)
        }),
        "capture does not supply a positive Function provider for the unknown formal"
    );
    let demand = graph
        .bounds()
        .find_map(|bound| {
            let upper = bound.upper();
            (bound.kind() == ComponentKind::Value
                && upper.polarity() == Polarity::Negative
                && upper.children().is_some()
                && bound
                    .lower()
                    .row()
                    .is_some_and(|row| row.same_identity(formal)))
            .then_some(upper)
        })
        .expect("formal row retains negative four-port invocation demand");
    let demand_ports = demand.children().unwrap();
    for (index, kind, polarity) in [
        (0, ComponentKind::Value, Polarity::Positive),
        (1, ComponentKind::Effect, Polarity::Positive),
        (2, ComponentKind::Effect, Polarity::Negative),
        (3, ComponentKind::Value, Polarity::Negative),
    ] {
        assert_eq!(demand_ports[index].polarity(), polarity);
        assert_eq!(
            demand_ports[index]
                .row()
                .expect("symbolic demand port")
                .kind(),
            kind
        );
    }
    assert!(
        graph.bounds().any(|bound| {
            bound.kind() == ComponentKind::Value
                && bound.lower().leaf() == Some(CandidateGraphLeaf::IntPositive)
                && candidate_call_reaches(
                    &graph,
                    bound.upper(),
                    demand_ports[0],
                    ComponentKind::Value,
                )
        }),
        "integer lower reaches invocation argument"
    );
    assert!(
        demand_ports[3]
            .row()
            .unwrap()
            .same_identity(ports[3].row().unwrap()),
        "invocation result is the lambda body result row"
    );
    let invocation_effect = demand_ports[2].row().unwrap();
    assert!(
        !graph.bounds().any(|bound| {
            bound.kind() == ComponentKind::Effect
                && bound.upper().leaf() == Some(CandidateGraphLeaf::EmptyEffect)
                && candidate_call_reaches(
                    &graph,
                    demand_ports[2],
                    bound.lower(),
                    ComponentKind::Effect,
                )
        }),
        "capture does not force the symbolic invocation effect to Empty"
    );
    assert!(
        graph.bounds().any(|bound| {
            bound.kind() == ComponentKind::Effect
                && bound
                    .lower()
                    .row()
                    .is_some_and(|row| row.same_identity(invocation_effect))
                && bound.lower().polarity() == Polarity::Positive
                && candidate_call_reaches(&graph, bound.upper(), ports[2], ComponentKind::Effect)
        }),
        "same symbolic invocation effect feeds application/body effect"
    );
    assert!(
        graph
            .root()
            .same_identity(candidate.export(root).unwrap().root())
    );
}

fn candidate_call_is_name(expression: &ResolvedExpr, occurrence: &HirOccurrenceId) -> bool {
    match expression {
        ResolvedExpr::Name {
            occurrence: found, ..
        } => found == occurrence,
        ResolvedExpr::Apply {
            callee, argument, ..
        } => {
            candidate_call_is_name(callee, occurrence)
                || candidate_call_is_name(argument, occurrence)
        }
        ResolvedExpr::Lambda { body, .. } => candidate_call_is_name(body, occurrence),
        ResolvedExpr::Group { inner, .. } => candidate_call_is_name(inner, occurrence),
        _ => false,
    }
}

fn candidate_call_routes(candidate: &CandidateInference, hir: &Arc<HirModule>, name: &str) {
    let root = candidate_call_root(hir, name);
    let graph = candidate.export(root).unwrap();
    // This separately collected inventory retains actual DefinitionUse Name
    // occurrences from precisely the HIR observed by CandidateInference.
    let batch = ConstraintBatch::collect_candidate_mode(hir.clone(), true, true).unwrap();
    let target = batch
        .definitions
        .iter()
        .find(|definition| &definition.root == root)
        .expect("source definition inventory");
    let uses: Vec<_> = batch
        .definition_uses()
        .iter()
        .filter(|record| record.target() == target.definition())
        .collect();
    assert_eq!(uses.len(), 2, "two actual source Name uses");
    for record in &uses {
        assert!(hir.owns_occurrence(record.occurrence()));
        assert!(
            hir.items().iter().any(|item| match item {
                HirItem::Binding(binding) =>
                    candidate_call_is_name(binding.value(), record.occurrence()),
                _ => false,
            }),
            "DefinitionUse corresponds to a retained HIR Name occurrence"
        );
    }
    let first = candidate
        .fresh_use(uses[0].occurrence())
        .expect("first retained route");
    let second = candidate
        .fresh_use(uses[1].occurrence())
        .expect("second retained route");
    assert_eq!(first.occurrence(), uses[0].occurrence());
    assert_eq!(second.occurrence(), uses[1].occurrence());
    let source: Vec<_> = graph.rows().collect();
    assert!(
        source.iter().all(|row| row.is_local()),
        "the actual empty-import source envelope produces only local rows"
    );
    let left: Vec<_> = first.rows().collect();
    let right: Vec<_> = second.rows().collect();
    let repeat = candidate.fresh_use(uses[0].occurrence()).unwrap();
    let repeated: Vec<_> = repeat.rows().collect();
    assert_eq!(left.len(), source.len());
    assert_eq!(right.len(), source.len());
    assert_eq!(repeated.len(), source.len());
    for (index, row) in source.iter().copied().enumerate() {
        assert!(left[index].source_row().same_identity(row));
        assert!(right[index].source_row().same_identity(row));
        assert_eq!(left[index].kind(), row.kind());
        assert_eq!(right[index].kind(), row.kind());
        assert!(
            left[index].same_identity(&repeated[index]),
            "reborrow retains installed image"
        );
        if row.is_local() {
            for image in &right {
                assert!(
                    !left[index].same_identity(image),
                    "all local images differ across uses"
                );
            }
        } else {
            assert!(
                left[index].same_identity(&right[index]),
                "anchors deliberately reuse identity"
            );
        }
        for other in index + 1..source.len() {
            assert!(
                !row.same_identity(source[other]),
                "one source row per map entry"
            );
            assert!(
                !left[index].same_identity(&left[other]),
                "one image per source row"
            );
            assert!(
                !right[index].same_identity(&right[other]),
                "one image per source row"
            );
        }
    }
    for kind in [ComponentKind::Value, ComponentKind::Effect] {
        assert!(
            source
                .iter()
                .any(|row| row.is_local() && row.kind() == kind)
        );
    }
    // The public observer retains maps, but does not expose installed fresh
    // bounds. No mapped runtime incidence follows from these cardinalities.
}

#[test]
fn candidate_graph_call_retains_deferred_formal_demand_and_fresh_uses() {
    let hir = candidate_call_hir("my invoke f = f 1\nmy first = invoke\nmy second = invoke");
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.observes_hir(&hir));
    assert!(candidate.candidate_conflicts().is_empty());
    candidate_call_capture(&candidate, candidate_call_root(&hir, "invoke"));
    candidate_call_routes(&candidate, &hir, "invoke");
}

#[test]
fn candidate_graph_call_retains_capture_after_identity_providers_arrive() {
    let hir = candidate_call_hir(
        "my id x = x\nmy invoke f = f 1\nmy first = invoke id\nmy second = invoke id",
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.observes_hir(&hir));
    assert!(candidate.candidate_conflicts().is_empty());
    candidate_call_capture(&candidate, candidate_call_root(&hir, "invoke"));
    candidate_call_routes(&candidate, &hir, "invoke");
    candidate_call_routes(&candidate, &hir, "id");
    for name in ["first", "second"] {
        let graph = candidate.export(candidate_call_root(&hir, name)).unwrap();
        assert!(
            graph.bounds().any(|bound| {
                bound.kind() == ComponentKind::Value
                    && bound.lower().leaf() == Some(CandidateGraphLeaf::IntPositive)
                    && candidate_call_reaches(
                        &graph,
                        bound.upper(),
                        graph.root(),
                        ComponentKind::Value,
                    )
            }),
            "integer lower reaches actual application result through retained bounds"
        );
    }
}
