//! Two bounded source observations of the private candidate graph.
//! These are retained scalar relations and fresh row maps, not complete Call,
//! source admission, public scheme correspondence, or effect-label semantics.
use super::*;
use crate::shadow_apply::{
    CandidateGraphExport, CandidateGraphLeaf, CandidateGraphNode, CandidateInference,
    CandidateReplayRouteOwner,
};
use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution};

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

fn candidate_call_hir_with_local_source(text: &str) -> Arc<HirModule> {
    let source: Arc<yu_syntax::SourceText> = Arc::from(text);
    let parsed = yu_syntax::parse_file(
        source.clone(),
        Arc::new(yu_syntax::scan_header(source)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()),
    );
    assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "healthy local-source fixture: {text}");
    assert!(parsed.structural_recoveries().is_empty(), "no parse recovery in local-source fixture: {text}");
    Arc::new(
        yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "candidate-graph-local-source",
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
fn scoped_local_callee_route_survives_a_later_local_argument_use() {
    let hir = candidate_call_hir_with_local_source("my id x = x\nmy outer = { my f = id; my a = 1; f a }");
    let source = hir.local_source(candidate_call_root(&hir, "outer")).unwrap().unwrap();
    let f = &source.bindings().iter().find(|binding| binding.spelling.as_ref() == "f").unwrap().id;
    let a = &source.bindings().iter().find(|binding| binding.spelling.as_ref() == "a").unwrap().id;
    let local_occurrence = |id: &yu_hir::HirLocalId| source.expressions().iter().find_map(|expression| {
        matches!(&expression.form, LocalSourceForm::Name {
            resolution: LocalSourceResolution::Local(found), ..
        } if found == id).then(|| expression.occurrence.clone())
    }).unwrap();
    let callee = local_occurrence(f);
    let later_argument = local_occurrence(a);

    let candidate = CandidateInference::solve_scoped_experiment(hir).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.fresh_use(&callee).unwrap().occurrence(), &callee);
    assert_eq!(candidate.fresh_use(&later_argument).unwrap().occurrence(), &later_argument);
    let call = candidate.source_call(0).unwrap();
    assert_eq!(call.callee_source().occurrence, callee);
}

#[test]
fn scoped_annotated_and_ascribed_local_callees_remain_refused() {
    let annotated = candidate_call_hir_with_local_source("my id x = x\nmy outer = { my f: int -> int = id; my a = 1; f a }");
    let source = annotated.local_source(candidate_call_root(&annotated, "outer")).unwrap().unwrap();
    assert!(source.bindings().iter().any(|binding| binding.spelling.as_ref() == "f" && binding.annotation.is_some()));
    assert!(CandidateInference::solve_scoped_experiment(annotated).is_err());

    let ascribed = candidate_call_hir_with_local_source("my id x = x\nmy outer = { my f = id; my a = 1; (f as int -> int) a }");
    let source = ascribed.local_source(candidate_call_root(&ascribed, "outer")).unwrap().unwrap();
    assert!(source.expressions().iter().any(|expression| matches!(&expression.form, LocalSourceForm::Ascription { .. })));
    assert!(CandidateInference::solve_scoped_experiment(ascribed).is_err());

    let non_local_ascription = candidate_call_hir_with_local_source("my id x = x\nmy outer = (id as int -> int) 1");
    let candidate = CandidateInference::solve_scoped_experiment(non_local_ascription).unwrap();
    let call = candidate.source_call(0).expect("the non-Local ascribed Apply remains observable");
    assert!(matches!(&call.callee_source().form,
        LocalSourceForm::Ascription { .. } | LocalSourceForm::Group { .. }));
}

#[test]
fn unscoped_candidate_collection_does_not_inherit_the_scoped_record_cap() {
    let mut text = String::from("my id x = x\n");
    for index in 0..=crate::candidate_source::SCOPED_RECORD_LIMIT {
        text.push_str(&format!("my use{index} = id 1\n"));
    }
    let hir = candidate_call_hir_with_local_source(&text);
    let batch = ConstraintBatch::collect_candidate_mode_scoped(hir, true, true, false).unwrap();
    assert!(batch.candidate_calls.calls.len() > crate::candidate_source::SCOPED_RECORD_LIMIT);
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

#[test]
fn accepted_scoped_formal_demand_replay_propagates_to_received_result() {
    const SOURCE: &str =
        "my invoke f = f 1\nmy id x = x\nmy received = invoke id";
    const SOURCE_SHA256: &str = "b9e4cc9a28de645a529ae31c7ca914b72efc73e51951bed917374f9c81c385d6";
    assert!(!SOURCE_SHA256.is_empty(), "freeze the accepted source literal");
    let source: Arc<yu_syntax::SourceText> = Arc::from(SOURCE);
    let parsed = yu_syntax::parse_file(
        source.clone(),
        Arc::new(yu_syntax::scan_header(source)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()),
    );
    assert!(
        parsed.syntax_diagnostics().unwrap().is_empty(),
        "accepted fixture has syntax diagnostics: {:?}",
        parsed.syntax_diagnostics().unwrap()
    );
    assert!(
        parsed.structural_recoveries().is_empty(),
        "accepted fixture has structural recoveries: {:?}",
        parsed.structural_recoveries()
    );
    let hir = Arc::new(
        yu_hir::lower_module(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "candidate-graph-accepted",
                "call.yu",
            ))),
            &parsed,
            yu_hir::SemanticImports::empty(),
        )
        .unwrap(),
    );
    assert!(
        hir.errors().is_empty(),
        "accepted replacement fixture must have no HIR errors: {:?}",
        hir.errors()
    );

    let invoke_root = candidate_call_root(&hir, "invoke");
    let received_root = candidate_call_root(&hir, "received");
    let invoke_owner = yu_hir::SourceRootId::Definition(invoke_root.clone());
    let received_owner = yu_hir::SourceRootId::Definition(received_root.clone());
    let invoke_source = hir.local_source(invoke_root).unwrap().unwrap();
    let received_source = hir.local_source(received_root).unwrap().unwrap();
    let formal_apply = invoke_source
        .expressions()
        .iter()
        .find(|expression| matches!(&expression.form, LocalSourceForm::Apply { .. }))
        .expect("invoke has its formal Apply");
    let received_apply = received_source
        .expressions()
        .iter()
        .find(|expression| matches!(&expression.form, LocalSourceForm::Apply { .. }))
        .expect("received has its outer Apply");
    let LocalSourceForm::Apply { callee, argument, .. } = &received_apply.form else {
        unreachable!()
    };
    let received_callee = received_source.expression(callee).unwrap();
    let received_argument = received_source.expression(argument).unwrap();
    assert!(matches!(
        &received_callee.form,
        LocalSourceForm::Name {
            resolution: LocalSourceResolution::ModuleDef(_), ..
        }
    ));
    assert!(matches!(
        &received_argument.form,
        LocalSourceForm::Name {
            resolution: LocalSourceResolution::ModuleDef(_), ..
        }
    ));

    let candidate = CandidateInference::solve_scoped_experiment(hir.clone()).unwrap();
    assert!(candidate.observes_hir(&hir));
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(
        hir.source_carrier_outcomes().len(),
        3,
        "ordinary lowering retains one source carrier outcome per binding"
    );
    let formal_index = (0..candidate.source_call_count())
        .find(|index| {
            candidate.source_call(*index).is_ok_and(|call| {
                call.owner() == &invoke_owner
                    && call.source().occurrence == formal_apply.occurrence
            })
        })
        .expect("source-owned formal Apply was admitted");
    let formal_call = candidate.source_call(formal_index).unwrap();
    let introduction = formal_call
        .directional_introduction()
        .expect("omitted formal introduction is retained");
    assert_eq!(introduction.original_owner(), &invoke_owner);
    assert_eq!(introduction.original_demand(), formal_call.native_demand());
    assert_eq!(
        introduction.checking_occurrence().occurrence(),
        &formal_apply.occurrence
    );
    assert!(formal_call.formal_registration().is_some());

    let received_index = (0..candidate.source_call_count())
        .find(|index| {
            candidate
                .source_call(*index)
                .is_ok_and(|call| {
                    call.owner() == &received_owner
                        && call.source().occurrence == received_apply.occurrence
                })
        })
        .expect("received outer Apply has an authenticated candidate call");
    let received_call = candidate.source_call(received_index).unwrap();
    assert_eq!(received_call.source().occurrence, received_apply.occurrence);
    assert_eq!(received_call.checking_occurrence().occurrence(), &received_apply.occurrence);
    assert_eq!(received_call.module_callee_target(), Some(match &received_callee.form {
        LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(id), .. } => id,
        _ => unreachable!(),
    }));

    let graph = candidate.export(received_root).unwrap();
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
        "the accepted `invoke id` result receives the propagated integer lower"
    );
    // The typed Replay row is keyed to invoke's formal Apply, whose omitted
    // formal demand is replayed; it is not keyed to received's outer Apply.
    assert_ne!(
        received_call.checking_occurrence(),
        formal_call.checking_occurrence(),
        "received Apply is distinct from invoke's formal Apply"
    );
    assert_ne!(formal_index, received_index);
}

#[test]
fn candidate_graph_call_authenticates_fresh_use_demand_transport_and_rejects_swaps() {
    let source: Arc<yu_syntax::SourceText> = Arc::from(
        "my invoke f = f 1\nmy id x = x\nmy first = invoke id\nmy second = invoke id",
    );
    let parsed = yu_syntax::parse_file(source.clone(), Arc::new(yu_syntax::scan_header(source)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()));
    let hir = Arc::new(yu_hir::lower_module(
        yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("candidate-replay-fresh-use", "call.yu"))),
        &parsed, yu_hir::SemanticImports::empty(),
    ).unwrap());
    let candidate = CandidateInference::solve_scoped_experiment(hir.clone()).unwrap();
    assert!(candidate.observes_hir(&hir));
    assert!(candidate.candidate_conflicts().is_empty());
    for name in ["first", "second"] {
        let graph = candidate.export(candidate_call_root(&hir, name)).unwrap();
        assert!(graph.bounds().any(|bound| {
            bound.kind() == ComponentKind::Value
                && bound.lower().leaf() == Some(CandidateGraphLeaf::IntPositive)
                && candidate_call_reaches(&graph, bound.upper(), graph.root(), ComponentKind::Value)
        }), "the integer lower propagates through each distinct use to {name}");
    }
    let observations: Vec<_> = candidate.scoped_replay_demand_transports()
        .filter(|row| row.route.is_some()).collect();
    assert!(observations.len() >= 2, "same source demand has two retained FreshUse Replay rows");
    let first = &observations[0];
    let second = observations.iter().find(|row| row.call_index == first.call_index && row.use_instance != first.use_instance)
        .expect("a second use of the same source has a distinct use identity");
    assert_ne!(first.route, second.route);
    for row in [first, second] {
        assert!(!row.native_root_matches, "preserve raw native root mismatch");
        assert_eq!(row.route_owner, Some(CandidateReplayRouteOwner::Module),
            "module FreshRoute ownership remains distinct from local-source routes");
        assert_eq!(row.consumer_relation, Some(row.child_relation),
            "the fixture's q→C consumer spine is authenticated as its zero-step case");
        assert_eq!(row.replay_upper_root, Some(row.copied_root),
            "the available p1→h constructor authenticates its zero-step root case");
        assert_eq!(row.consumer_root, row.replay_child_root,
            "the q→C root identity is retained explicitly");
        assert!(row.physical_fiber.is_some(), "the FreshUse admission retains its emitted fiber slot");
        assert!(row.scope_map_matches && row.input_map_matches);
        assert_eq!(row.ports_match, [true; 4]);
        assert_ne!(row.child_relation, row.upper_relation, "the demand relation and Replay upper are separately authenticated");
        let port_relations = row.port_relations.expect("authenticated four port ancestry");
        assert!(port_relations.iter().enumerate().all(|(index, relation)|
            port_relations.iter().skip(index + 1).all(|other| relation != other)),
            "four distinct FunctionPort dependencies are captured in order");
        assert!(!row.lower_input.is_empty() && !row.upper_input.is_empty());
        assert!(row.fresh_from.as_ref().is_some_and(|value| !value.is_empty())
            && row.fresh_to.as_ref().is_some_and(|value| !value.is_empty()));
        assert!(candidate.authenticate_scoped_replay_demand(row.call_index, row.use_instance, row.copied_root, Some(row.ports)));
        assert!(!candidate.authenticate_scoped_replay_demand(row.call_index, row.use_instance + 1, row.copied_root, Some(row.ports)));
        assert!(!candidate.authenticate_scoped_replay_demand(row.call_index, row.use_instance, row.native_root, Some(row.ports)));
        for left in 0..4 {
            for right in left + 1..4 {
                let mut swapped = row.ports;
                swapped.swap(left, right);
                assert!(!candidate.authenticate_scoped_replay_demand(row.call_index, row.use_instance, row.copied_root, Some(swapped)),
                    "port swap {left}<->{right} is rejected");
            }
        }
    }
}
