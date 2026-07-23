use super::*;
use infer::constraints::{
    DiagnosticExplanationCompleteness, DiagnosticTypeCauseRole, PortableExplanationBudget,
    explain_portable_subtype,
};

mod ordinary_cast_characterization;

#[test]
fn specialization_error_path_exposes_captured_subtype_failure_anchors() {
    let lowering = lower_real_source("my g(x: (int, int)) = x\ng (1, 2, 3)\n");
    let sidecar = lowering.subtype_provenance();
    let (result, failures) =
        specialize_with_captured_subtype_failures(&lowering.session.poly, sidecar);

    assert!(matches!(
        result,
        Err(SpecializeError::UnsatisfiedSubtype { origin: None, .. })
    ));
    let [failure] = failures.as_slice() else {
        panic!("expected one captured subtype failure: {failures:?}");
    };
    assert_eq!(failure.completeness, ProvenanceCompleteness::Complete);
    assert!(!failure.lower.is_empty());
    assert!(!failure.upper.is_empty());
    assert!(
        failure
            .lower
            .iter()
            .chain(&failure.upper)
            .all(|anchor| sidecar.snapshot.anchor(*anchor).is_some())
    );
}

#[test]
fn captured_failure_anchors_explain_the_real_tuple_mismatch_source() {
    const SOURCE: &str = "my g(x: (int, int)) = x\ng (1, 2, 3)\n";
    let lowering = lower_real_source(SOURCE);
    let sidecar = lowering.subtype_provenance();
    let (result, failures) =
        specialize_with_captured_subtype_failures(&lowering.session.poly, sidecar);

    assert!(matches!(
        result,
        Err(SpecializeError::UnsatisfiedSubtype { origin: None, .. })
    ));
    let [failure] = failures.as_slice() else {
        panic!("expected one captured subtype failure: {failures:?}");
    };
    let explanation = explain_portable_subtype(
        &sidecar.snapshot,
        &failure.lower,
        &failure.upper,
        PortableExplanationBudget::default(),
    );

    assert_eq!(
        explanation.completeness,
        DiagnosticExplanationCompleteness::Complete
    );
    assert_eq!(explanation.truncation, None);
    assert!(explanation.lower_sites.is_empty());
    let [cause] = explanation.upper_sites.as_slice() else {
        panic!("expected one upper source cause: {explanation:?}");
    };
    assert_eq!(cause.role, DiagnosticTypeCauseRole::RequiredByApplication);
    assert_eq!(cause.source_span.file, sources::Path::default());
    assert_eq!(cause.source_span.range.start, 26);
    assert_eq!(cause.source_span.range.end, 36);
    assert_eq!(
        &SOURCE[cause.source_span.range.start..cause.source_span.range.end],
        "(1, 2, 3)\n"
    );
}

#[test]
fn real_definition_occurrence_reaches_materialized_subtype_root() {
    let lowering = lower_real_source("my id x = x\nid(1)\n");
    let sidecar = lowering.subtype_provenance();
    let (def, anchor) = sidecar
        .occurrences
        .iter()
        .find_map(
            |(key, provenance)| match (key.owner, key.role, key.path.0.is_empty()) {
                (
                    poly::provenance::TypeOccurrenceOwner::Definition(def),
                    poly::provenance::TypeOccurrenceRole::DefinitionPredicate,
                    true,
                ) => provenance
                    .anchors
                    .first()
                    .copied()
                    .map(|anchor| (def, anchor)),
                _ => None,
            },
        )
        .expect("real definition predicate has a portable root anchor");
    let poly_expr::Def::Let {
        scheme: Some(scheme),
        ..
    } = lowering.session.poly.defs.get(def).unwrap()
    else {
        panic!("owned definition must retain its scheme");
    };
    let mut solver = TaskSolver::new(&lowering.session.poly, sidecar);
    let materialized = solver
        .instantiate_scheme_with_provenance(def, scheme)
        .unwrap();
    assert!(
        materialized
            .provenance
            .positions
            .iter()
            .any(|position| { position.path.0.is_empty() && position.anchors.contains(&anchor) })
    );
    let upper = solver.materialized_occurrence(
        Type::Any,
        poly::provenance::TypeOccurrenceOwner::Definition(def),
        poly::provenance::TypeOccurrenceRole::DefinitionPredicate,
    );
    solver
        .graph
        .constrain_materialized_subtype(materialized, upper)
        .unwrap();
    assert_graph_contains_root_anchor(&solver.graph, anchor);
}

#[test]
fn real_expression_occurrence_reaches_consumer_subtype_root() {
    let lowering = lower_real_source("my id x = x\nid(1)\n");
    let arena = &lowering.session.poly;
    let argument = arena
        .root_exprs
        .iter()
        .find_map(|expr| match arena.expr(*expr) {
            poly_expr::Expr::App(_, argument) => Some(*argument),
            _ => None,
        })
        .expect("fixture has a root application");
    let anchor = root_occurrence_anchor(
        lowering.subtype_provenance(),
        poly::provenance::TypeOccurrenceOwner::Expression(argument),
        poly::provenance::TypeOccurrenceRole::ExpressionActual,
    );
    let mut solver = TaskSolver::new(arena, lowering.subtype_provenance());
    solver.consume_expr(argument, Type::Any).unwrap();
    assert_graph_contains_root_anchor(&solver.graph, anchor);
}

#[test]
fn real_pattern_occurrence_reaches_pattern_subtype_root() {
    let lowering = lower_real_source("case true: true -> 1, false -> 2\n");
    let arena = &lowering.session.poly;
    let pat = arena
        .root_exprs
        .iter()
        .find_map(|expr| match arena.expr(*expr) {
            poly_expr::Expr::Case(_, arms) => arms.first().map(|arm| arm.pat),
            _ => None,
        })
        .expect("fixture has a literal case pattern");
    let anchor = root_occurrence_anchor(
        lowering.subtype_provenance(),
        poly::provenance::TypeOccurrenceOwner::Pattern(pat),
        poly::provenance::TypeOccurrenceRole::PatternInput,
    );
    let mut solver = TaskSolver::new(arena, lowering.subtype_provenance());
    solver.bind_pat(pat, Type::Any).unwrap();
    assert_graph_contains_root_anchor(&solver.graph, anchor);
}

#[test]
fn subtype_provenance_duplicate_roots_merge_without_semantic_requeue_and_scale_linearly() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    for occurrence in 0..8 {
        graph
            .constrain_materialized_subtype(
                materialized_root(int_type(), occurrence),
                materialized_root(Type::unit(), 100 + occurrence),
            )
            .unwrap();
    }

    assert_eq!(graph.queued_constraints.len(), 1);
    assert_eq!(graph.pending.len(), 1);
    assert_eq!(graph.subtype_provenance_records.len(), 1);
    assert_eq!(graph.subtype_provenance_records[0].incoming.len(), 8);
    assert_eq!(graph.subtype_provenance_metrics.records, 1);
    assert_eq!(graph.subtype_provenance_metrics.semantic_enqueues, 1);
    assert_eq!(graph.subtype_provenance_metrics.incoming_considered, 8);
    assert_eq!(graph.subtype_provenance_metrics.incoming_inserted, 8);
    assert_eq!(graph.subtype_provenance_metrics.incoming_deduplicated, 0);

    graph
        .constrain_materialized_subtype(
            materialized_root(int_type(), 7),
            materialized_root(Type::unit(), 107),
        )
        .unwrap();
    assert_eq!(graph.pending.len(), 1);
    assert_eq!(graph.subtype_provenance_records[0].incoming.len(), 8);
    assert_eq!(graph.subtype_provenance_metrics.semantic_enqueues, 1);
    assert_eq!(graph.subtype_provenance_metrics.incoming_deduplicated, 1);
}

#[test]
fn subtype_provenance_storage_budget_truncates_metadata_without_semantic_requeue() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    for occurrence in 0..80 {
        graph
            .constrain_materialized_subtype(
                materialized_root(int_type(), occurrence),
                materialized_root(Type::unit(), 100 + occurrence),
            )
            .unwrap();
    }

    assert_eq!(graph.queued_constraints.len(), 1);
    assert_eq!(graph.pending.len(), 1);
    assert_eq!(graph.subtype_provenance_records.len(), 1);
    assert_eq!(graph.subtype_provenance_records[0].incoming.len(), 64);
    assert_eq!(graph.subtype_provenance_metrics.semantic_enqueues, 1);
    assert_eq!(graph.subtype_provenance_metrics.incoming_considered, 80);
    assert_eq!(graph.subtype_provenance_metrics.incoming_inserted, 64);
    assert!(graph.subtype_provenance_metrics.budget_exhaustions >= 16);
    assert_eq!(
        graph.subtype_provenance_records[0].completeness,
        ProvenanceCompleteness::Incomplete
    );
}

#[test]
fn subtype_provenance_nested_tuple_failure_excludes_sibling_anchors() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let lower = Type::Tuple(vec![
        Type::Tuple(vec![int_type(), int_type()]),
        Type::unit(),
    ]);
    let upper = Type::Tuple(vec![Type::Tuple(vec![int_type()]), Type::unit()]);
    let child = TypePositionStep::TupleElement(poly::provenance::TypePositionIndex::from_usize(0));
    let sibling =
        TypePositionStep::TupleElement(poly::provenance::TypePositionIndex::from_usize(1));
    graph
        .constrain_materialized_subtype(
            materialized_paths(lower, &[(vec![child], 1), (vec![sibling], 2)]),
            materialized_paths(upper, &[(vec![child], 11), (vec![sibling], 12)]),
        )
        .unwrap();

    let error = graph.solve_constraints().unwrap_err();
    assert!(matches!(error, SpecializeError::UnsatisfiedSubtype { .. }));
    let [failure] = graph.shadow_subtype_failures.as_slice() else {
        panic!(
            "expected one shadow failure: {:?}",
            graph.shadow_subtype_failures
        );
    };
    assert_eq!(failure.lower, vec![ProvenanceAnchor::from_index(1)]);
    assert_eq!(failure.upper, vec![ProvenanceAnchor::from_index(11)]);
    assert!(!failure.lower.contains(&ProvenanceAnchor::from_index(2)));
    assert!(!failure.upper.contains(&ProvenanceAnchor::from_index(12)));
    assert!(graph.subtype_provenance_records[failure.record.index()]
        .incoming
        .iter()
        .any(|edge| matches!(edge, SpecializeProvenanceDerivation::Structural { step, .. } if *step == child)));
}

#[test]
fn subtype_provenance_record_and_variant_container_failures_keep_root_anchors() {
    let arena = poly_expr::Arena::new();

    let mut record_graph = TypeGraph::new(&arena);
    record_graph
        .constrain_materialized_subtype(
            materialized_root(Type::Record(Vec::new()), 3),
            materialized_root(Type::Record(vec![field("required", int_type(), false)]), 13),
        )
        .unwrap();
    assert!(record_graph.solve_constraints().is_err());
    assert_eq!(
        record_graph.shadow_subtype_failures[0].lower,
        vec![ProvenanceAnchor::from_index(3)]
    );
    assert_eq!(
        record_graph.shadow_subtype_failures[0].upper,
        vec![ProvenanceAnchor::from_index(13)]
    );

    let mut variant_graph = TypeGraph::new(&arena);
    variant_graph
        .constrain_materialized_subtype(
            materialized_root(Type::PolyVariant(vec![variant("missing", Vec::new())]), 4),
            materialized_root(Type::PolyVariant(vec![variant("other", Vec::new())]), 14),
        )
        .unwrap();
    assert!(variant_graph.solve_constraints().is_err());
    assert_eq!(
        variant_graph.shadow_subtype_failures[0].lower,
        vec![ProvenanceAnchor::from_index(4)]
    );
    assert_eq!(
        variant_graph.shadow_subtype_failures[0].upper,
        vec![ProvenanceAnchor::from_index(14)]
    );
}

#[test]
fn subtype_provenance_record_and_variant_children_advance_exact_paths() {
    let arena = poly_expr::Arena::new();
    let tuple_lower = Type::Tuple(vec![int_type(), int_type()]);
    let tuple_upper = Type::Tuple(vec![int_type()]);

    let record_step = TypePositionStep::RecordField {
        alternative: poly::provenance::TypePositionIndex::from_usize(0),
        field: poly::provenance::TypePositionIndex::from_usize(0),
    };
    let mut record_graph = TypeGraph::new(&arena);
    record_graph
        .constrain_materialized_subtype(
            materialized_paths(
                Type::Record(vec![field("value", tuple_lower.clone(), false)]),
                &[(vec![record_step], 5)],
            ),
            materialized_paths(
                Type::Record(vec![field("value", tuple_upper.clone(), false)]),
                &[(vec![record_step], 15)],
            ),
        )
        .unwrap();
    assert!(record_graph.solve_constraints().is_err());
    assert_eq!(
        record_graph.shadow_subtype_failures[0].lower,
        vec![ProvenanceAnchor::from_index(5)]
    );
    assert_eq!(
        record_graph.shadow_subtype_failures[0].upper,
        vec![ProvenanceAnchor::from_index(15)]
    );

    let variant_step = TypePositionStep::VariantPayload {
        alternative: poly::provenance::TypePositionIndex::from_usize(0),
        item: poly::provenance::TypePositionIndex::from_usize(0),
        payload: poly::provenance::TypePositionIndex::from_usize(0),
    };
    let mut variant_graph = TypeGraph::new(&arena);
    variant_graph
        .constrain_materialized_subtype(
            materialized_paths(
                Type::PolyVariant(vec![variant("some", vec![tuple_lower])]),
                &[(vec![variant_step], 6)],
            ),
            materialized_paths(
                Type::PolyVariant(vec![variant("some", vec![tuple_upper])]),
                &[(vec![variant_step], 16)],
            ),
        )
        .unwrap();
    assert!(variant_graph.solve_constraints().is_err());
    assert_eq!(
        variant_graph.shadow_subtype_failures[0].lower,
        vec![ProvenanceAnchor::from_index(6)]
    );
    assert_eq!(
        variant_graph.shadow_subtype_failures[0].upper,
        vec![ProvenanceAnchor::from_index(16)]
    );
}

#[test]
fn subtype_provenance_open_var_replay_is_explicitly_incomplete() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let slot = graph.fresh_value();
    graph
        .constrain_materialized_subtype(
            materialized_root(Type::Tuple(vec![int_type(), int_type()]), 20),
            materialized_root(slot.clone(), 21),
        )
        .unwrap();
    graph
        .constrain_subtype(slot, Type::Tuple(vec![int_type()]))
        .unwrap();

    assert!(graph.solve_constraints().is_err());
    let failure = graph.shadow_subtype_failures.last().unwrap();
    assert!(failure.lower.is_empty());
    assert!(failure.upper.is_empty());
    assert_eq!(failure.completeness, ProvenanceCompleteness::Incomplete);
}

fn materialized_root(ty: Type, anchor: usize) -> types::MaterializedTypeWithProvenance {
    materialized_paths(ty, &[(Vec::new(), anchor)])
}

fn materialized_paths(
    ty: Type,
    paths: &[(Vec<TypePositionStep>, usize)],
) -> types::MaterializedTypeWithProvenance {
    types::MaterializedTypeWithProvenance {
        ty,
        provenance: types::MaterializedTypeProvenance {
            positions: paths
                .iter()
                .map(|(path, anchor)| types::MaterializedPositionProvenance {
                    path: poly::provenance::TypePositionPath(path.clone()),
                    anchors: vec![ProvenanceAnchor::from_index(*anchor)],
                    completeness: ProvenanceCompleteness::Complete,
                })
                .collect(),
            completeness: ProvenanceCompleteness::Complete,
        },
    }
}

fn lower_real_source(source: &str) -> infer::lowering::BodyLowering {
    let files = sources::load(vec![sources::SourceFile {
        module_path: sources::Path::default(),
        source: source.to_string(),
    }]);
    let lowering = infer::dump::dump_loaded_files(&files)
        .expect("real provenance fixture should lower")
        .lowering;
    assert!(lowering.errors.is_empty(), "{:?}", lowering.errors);
    lowering
}

fn root_occurrence_anchor(
    sidecar: &SubtypeProvenanceSidecar,
    owner: poly::provenance::TypeOccurrenceOwner,
    role: poly::provenance::TypeOccurrenceRole,
) -> ProvenanceAnchor {
    sidecar
        .occurrences
        .get(&poly::provenance::TypeOccurrenceKey {
            owner,
            role,
            path: poly::provenance::TypePositionPath::default(),
        })
        .and_then(|occurrence| occurrence.anchors.first().copied())
        .expect("real occurrence has a portable root anchor")
}

fn assert_graph_contains_root_anchor(graph: &TypeGraph<'_>, anchor: ProvenanceAnchor) {
    assert!(graph.subtype_provenance_records.iter().any(|record| {
        record.incoming.iter().any(|derivation| match derivation {
            SpecializeProvenanceDerivation::Root { lower, upper } => {
                lower.contains(&anchor) || upper.contains(&anchor)
            }
            _ => false,
        })
    }));
}

fn callback_type(first_ret_effect: Type, final_ret_effect: Type) -> Type {
    Type::Fun {
        arg: Box::new(Type::unit()),
        arg_effect: Box::new(Type::pure_effect()),
        ret_effect: Box::new(first_ret_effect),
        ret: Box::new(Type::Fun {
            arg: Box::new(int_type()),
            arg_effect: Box::new(Type::pure_effect()),
            ret_effect: Box::new(final_ret_effect),
            ret: Box::new(Type::unit()),
        }),
    }
}

#[test]
fn same_path_lower_candidates_unify_invariant_arguments() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let left_item = graph.fresh_value();
    let right_item = graph.fresh_value();
    let joined = graph.fresh_value();
    let left_box = con(&["box"], vec![left_item.clone()]);
    let right_box = con(&["box"], vec![right_item.clone()]);

    graph
        .constrain_subtype(
            Type::Union(Box::new(left_box), Box::new(right_box)),
            joined.clone(),
        )
        .unwrap();
    graph
        .constrain_subtype(int_type(), left_item.clone())
        .unwrap();
    graph.solve_constraints().unwrap();
    let solution = graph.solve_slots().unwrap();
    let mut resolver = TypeResolver::new(&graph, &solution);

    assert_eq!(resolver.resolve(&right_item).unwrap(), int_type());
    assert_eq!(
        resolver.resolve(&joined).unwrap(),
        con(&["box"], vec![int_type()])
    );
}

#[test]
fn function_lower_candidates_do_not_unify_ret_effects_invariantly() {
    let arena = arena_with_effect_families(&[&["handled"]]);
    let mut graph = TypeGraph::new(&arena);
    let callback = graph.fresh_value();
    let effect = graph.fresh_effect();
    let handled = Type::EffectRow(vec![con(&["handled"], Vec::new())]);
    let pure_then_effectful = callback_type(Type::pure_effect(), handled.clone());
    let shared_effect = callback_type(effect.clone(), effect.clone());

    graph
        .constrain_subtype(handled.clone(), effect.clone())
        .unwrap();
    graph
        .constrain_subtype(pure_then_effectful, callback.clone())
        .unwrap();
    graph.constrain_subtype(shared_effect, callback).unwrap();
    graph.solve_constraints().unwrap();

    let solution = graph.solve_slots().unwrap();
    let mut resolver = TypeResolver::new(&graph, &solution);

    assert_eq!(resolver.resolve(&effect).unwrap(), handled);
}

#[test]
fn pinned_slot_solution_ignores_successor_fanout() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let pinned = graph.fresh_value();

    graph
        .constrain_subtype(Type::unit(), pinned.clone())
        .unwrap();
    graph
        .constrain_subtype(pinned.clone(), Type::unit())
        .unwrap();
    for _ in 0..64 {
        let successor = graph.fresh_value();
        graph.constrain_subtype(pinned.clone(), successor).unwrap();
    }

    graph.solve_constraints().unwrap();
    let solution = graph.solve_slots().unwrap();
    let mut resolver = TypeResolver::new(&graph, &solution);

    assert_eq!(resolver.resolve(&pinned).unwrap(), Type::unit());
}

#[test]
fn solve_slots_records_unread_conflicts_without_aborting() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let conflicted = graph.fresh_value();
    let resolved = graph.fresh_value();

    graph
        .constrain_subtype(int_type(), conflicted.clone())
        .unwrap();
    graph
        .constrain_subtype(Type::unit(), conflicted.clone())
        .unwrap();
    graph
        .constrain_subtype(Type::unit(), resolved.clone())
        .unwrap();
    graph
        .constrain_subtype(resolved.clone(), Type::unit())
        .unwrap();

    graph.solve_constraints().unwrap();
    let solution = graph.solve_slots().unwrap();
    let mut resolver = TypeResolver::new(&graph, &solution);

    assert_eq!(resolver.resolve(&resolved).unwrap(), Type::unit());
    assert!(matches!(
        resolver.resolve(&conflicted).unwrap_err(),
        SpecializeError::ConflictingTypeCandidates { .. }
    ));
}

#[test]
fn effect_row_candidates_merge_same_family_arguments() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let item = graph.fresh_value();
    let open_sub = con(&["effect", "sub"], vec![item]);
    let int_sub = con(&["effect", "sub"], vec![int_type()]);
    let nondet = con(&["effect", "nondet"], Vec::new());
    let open_row = Type::EffectRow(vec![open_sub, nondet.clone()]);
    let int_row = Type::EffectRow(vec![int_sub.clone(), nondet.clone()]);

    assert_eq!(
        join_type_candidates(&graph, open_row.clone(), int_row.clone()).unwrap(),
        Type::EffectRow(vec![int_sub.clone(), nondet.clone()])
    );
    assert_eq!(
        meet_type_candidates(&graph, open_row, int_row).unwrap(),
        Type::EffectRow(vec![int_sub, nondet])
    );
}

#[test]
fn effect_row_candidate_merges_single_effect_item() {
    let arena = arena_with_effect_families(&[&["effect", "item"]]);
    let graph = TypeGraph::new(&arena);
    let item = con(&["effect", "item"], vec![int_type()]);
    let row = Type::EffectRow(vec![item.clone()]);

    assert_eq!(
        join_type_candidates(&graph, row.clone(), item.clone()).unwrap(),
        row
    );
    assert_eq!(
        meet_type_candidates(&graph, item.clone(), Type::EffectRow(vec![item.clone()])).unwrap(),
        Type::EffectRow(vec![item])
    );
}

#[test]
fn partial_effect_row_resolution_preserves_unresolved_union_tail() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let left_tail = graph.fresh_effect();
    let right_tail = graph.fresh_effect();
    let tail = types::simplify_type(Type::Union(
        Box::new(left_tail.clone()),
        Box::new(right_tail.clone()),
    ));
    let row = Type::EffectRow(vec![tail]);
    let solution = Solution {
        slots: vec![SlotSolution::Unknown; graph.slots.len()],
    };
    let mut resolver = TypeResolver::new(&graph, &solution);

    assert_eq!(
        resolver.resolve_partial_candidate(&row, true).unwrap(),
        Some(row)
    );
}

#[test]
fn effect_row_union_tail_refines_open_upper() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let left_tail = graph.fresh_effect();
    let right_tail = graph.fresh_effect();
    let local = con(&["&buffer#1:0"], vec![str_type()]);
    let lower = Type::EffectRow(vec![local.clone()]);
    let upper = Type::EffectRow(vec![types::simplify_type(Type::Union(
        Box::new(left_tail),
        Box::new(right_tail),
    ))]);

    assert_eq!(
        refine_effect_lower_with_upper(&graph, &lower, &upper).unwrap(),
        Some(Type::EffectRow(vec![local]))
    );
}

#[test]
fn effect_row_bounded_intersection_tail_refines_matching_item() {
    let arena = arena_with_effect_families(&[&["&buffer#1:0"]]);
    let mut graph = TypeGraph::new(&arena);
    let tail = graph.fresh_effect();
    let local = con(&["&buffer#1:0"], vec![str_type()]);
    let lower = Type::EffectRow(vec![local.clone()]);
    let upper = Type::EffectRow(vec![types::simplify_type(Type::Intersection(
        Box::new(tail),
        Box::new(Type::EffectRow(vec![local.clone()])),
    ))]);

    assert_eq!(
        refine_effect_lower_with_upper(&graph, &lower, &upper).unwrap(),
        Some(Type::EffectRow(vec![local]))
    );
}

#[test]
fn effect_row_bounded_intersection_tail_rejects_pure_bound() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let tail = graph.fresh_effect();
    let local = con(&["&buffer#1:0"], vec![str_type()]);
    let lower = Type::EffectRow(vec![local]);
    let upper = Type::EffectRow(vec![types::simplify_type(Type::Intersection(
        Box::new(tail),
        Box::new(Type::pure_effect()),
    ))]);

    assert_eq!(
        refine_effect_lower_with_upper(&graph, &lower, &upper).unwrap(),
        None
    );
}

#[test]
fn tuple_candidates_refine_open_items_from_concrete_tuple() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let left = Type::Tuple(vec![graph.fresh_value(), graph.fresh_value()]);
    let callback = unary_type(bool_type(), int_type());
    let right = Type::Tuple(vec![callback.clone(), list_type(callback)]);

    assert_eq!(
        join_type_candidates(&graph, left.clone(), right.clone()).unwrap(),
        right
    );
    assert_eq!(
        meet_type_candidates(&graph, left, right.clone()).unwrap(),
        right
    );
}

#[test]
fn open_record_candidates_share_matching_shape() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let left = Type::Record(vec![field("name", graph.fresh_value(), false)]);
    let right = Type::Record(vec![field("name", graph.fresh_value(), false)]);

    assert!(matches!(
        merge_open_candidate_shape(&left, &right),
        Some(Type::Record(fields))
            if fields.len() == 1
                && fields[0].name == "name"
                && !fields[0].optional
                && matches!(fields[0].value, Type::OpenVar(_))
    ));
}

#[test]
fn open_candidate_shape_does_not_hide_record_field_conflicts() {
    let left = Type::Record(vec![field("name", int_type(), false)]);
    let right = Type::Record(vec![field("name", bool_type(), false)]);

    assert!(merge_open_candidate_shape(&left, &right).is_none());
}

#[test]
fn concrete_subtype_rejects_tuple_length_mismatch() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let lower = Type::Tuple(vec![int_type(), int_type(), int_type()]);
    let upper = Type::Tuple(vec![int_type(), int_type()]);

    graph
        .constrain_subtype(lower.clone(), upper.clone())
        .unwrap();
    assert_unsatisfied_subtype(graph.solve_constraints().unwrap_err(), lower, upper);
}

/// SUBP-A characterization: semantic queue ownership is currently only the
/// `(lower type, lower weight, upper type, upper weight)` key. Distinct future
/// occurrence owners for the same semantic relation would therefore converge
/// on one queued item and must merge provenance without requeueing it.
#[test]
fn subtype_constraint_queue_deduplicates_identical_semantic_occurrences() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let lower_child = Type::Tuple(vec![int_type(), int_type(), int_type()]);
    let upper_child = Type::Tuple(vec![int_type(), int_type()]);
    let lower = Type::Tuple(vec![lower_child.clone(), lower_child.clone()]);
    let upper = Type::Tuple(vec![upper_child.clone(), upper_child.clone()]);

    graph
        .constrain_subtype(lower.clone(), upper.clone())
        .unwrap();
    assert_unsatisfied_subtype(
        graph.solve_constraints().unwrap_err(),
        lower_child.clone(),
        upper_child.clone(),
    );

    // One outer relation plus one child relation: the two distinct tuple-element
    // positions generated the same semantic child key and converged in the set.
    assert_eq!(graph.queued_constraints.len(), 2);
    let queued = graph
        .queued_constraints
        .iter()
        .find(|constraint| constraint.lower == lower_child && constraint.upper == upper_child)
        .expect("one canonical child relation");
    assert!(queued.lower_weight.entries.is_empty());
    assert!(queued.upper_weight.entries.is_empty());
}

#[test]
fn concrete_subtype_rejects_missing_required_record_field() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let lower = Type::Record(vec![field("a", int_type(), false)]);
    let upper = Type::Record(vec![
        field("a", int_type(), false),
        field("b", int_type(), false),
    ]);

    graph
        .constrain_subtype(lower.clone(), upper.clone())
        .unwrap();
    assert_unsatisfied_subtype(graph.solve_constraints().unwrap_err(), lower, upper);
}

#[test]
fn record_literal_missing_required_field_reports_origin() {
    let mut arena = poly_expr::Arena::new();
    let field_value = arena.add_expr(poly_expr::Expr::Lit(poly_expr::Lit::Int(1)));
    let record = arena.add_expr(poly_expr::Expr::Record {
        fields: vec![("a".into(), field_value)],
        spread: poly_expr::RecordSpread::None,
    });
    let expected = vec![field("b", int_type(), false)];
    let sidecar = SubtypeProvenanceSidecar::empty();
    let mut solver = TaskSolver::new(&arena, &sidecar);

    let err = solver
        .expr_with_value_consumer(record, &Type::Record(expected.clone()))
        .unwrap_err();

    let SpecializeError::UnsatisfiedSubtype {
        lower,
        upper,
        origin:
            Some(UnsatisfiedSubtypeOrigin::MissingRecordField {
                field: missing_field,
                actual_fields,
                select,
            }),
    } = err
    else {
        panic!("expected missing record field origin, got {err:?}");
    };
    assert_eq!(lower, Type::Record(vec![field("a", int_type(), false)]));
    assert_eq!(upper, Type::Record(expected));
    assert_eq!(missing_field, "b");
    assert_eq!(actual_fields, vec!["a"]);
    assert_eq!(select, None);
}

#[test]
fn record_field_select_missing_required_field_retains_select_origin() {
    let mut arena = poly_expr::Arena::new();
    let field_value = arena.add_expr(poly_expr::Expr::Lit(poly_expr::Lit::Int(1)));
    let record = arena.add_expr(poly_expr::Expr::Record {
        fields: vec![("a".into(), field_value)],
        spread: poly_expr::RecordSpread::None,
    });
    let select = arena.add_select("b");
    arena.resolve_select(select, poly_expr::SelectResolution::RecordField);
    let selection = arena.add_expr(poly_expr::Expr::Select(record, select));
    let sidecar = SubtypeProvenanceSidecar::empty();
    let mut solver = TaskSolver::new(&arena, &sidecar);

    let err = solver.expr(selection).unwrap_err();

    assert!(matches!(
        err,
        SpecializeError::UnsatisfiedSubtype {
            origin: Some(UnsatisfiedSubtypeOrigin::MissingRecordField {
                field,
                actual_fields,
                select: Some(actual_select),
            }),
            ..
        } if field == "b" && actual_fields == ["a"] && actual_select == select
    ));
}

#[test]
fn concrete_subtype_allows_missing_optional_record_field() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let lower = Type::Record(vec![field("a", int_type(), false)]);
    let upper = Type::Record(vec![
        field("a", int_type(), false),
        field("b", int_type(), true),
    ]);

    graph.constrain_subtype(lower, upper).unwrap();
    graph.solve_constraints().unwrap();
}

#[test]
fn concrete_subtype_rejects_missing_poly_variant_constructor() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let lower = Type::PolyVariant(vec![variant("some", vec![int_type()])]);
    let upper = Type::PolyVariant(vec![variant("none", Vec::new())]);

    graph
        .constrain_subtype(lower.clone(), upper.clone())
        .unwrap();
    assert_unsatisfied_subtype(graph.solve_constraints().unwrap_err(), lower, upper);
}

#[test]
fn consumed_effect_row_removes_handled_item_from_tail() {
    let mut arena = poly_expr::Arena::new();
    arena.effect_operations.insert(
        poly_expr::DefId(0),
        poly_expr::EffectOperation {
            path: vec![
                "std".into(),
                "control".into(),
                "var".into(),
                "ref_update".into(),
                "update".into(),
            ],
        },
    );
    arena.effect_operations.insert(
        poly_expr::DefId(1),
        poly_expr::EffectOperation {
            path: vec!["&xs#1:0".into(), "set".into()],
        },
    );
    let mut graph = TypeGraph::new(&arena);
    let tail = graph.fresh_effect();
    let actual = Type::EffectRow(vec![
        con(
            &["std", "control", "var", "ref_update"],
            vec![list_type(int_type())],
        ),
        con(&["&xs#1:0"], vec![list_type(int_type())]),
    ]);
    let expected = Type::EffectRow(vec![
        con(&["&xs#1:0"], vec![list_type(int_type())]),
        tail.clone(),
    ]);

    graph
        .constrain_consumed_computation_effect(actual, expected)
        .unwrap();
    graph.solve_constraints().unwrap();
    let solution = graph.solve_slots().unwrap();
    let mut resolver = TypeResolver::new(&graph, &solution);

    assert_eq!(
        resolver.resolve(&tail).unwrap(),
        Type::EffectRow(vec![con(
            &["std", "control", "var", "ref_update"],
            vec![list_type(int_type())],
        )])
    );
}

#[test]
fn consumed_open_effect_slot_removes_handled_item_from_tail() {
    let mut arena = poly_expr::Arena::new();
    arena.effect_operations.insert(
        poly_expr::DefId(0),
        poly_expr::EffectOperation {
            path: vec![
                "std".into(),
                "control".into(),
                "var".into(),
                "ref_update".into(),
                "update".into(),
            ],
        },
    );
    arena.effect_operations.insert(
        poly_expr::DefId(1),
        poly_expr::EffectOperation {
            path: vec!["&x#0:0".into(), "set".into()],
        },
    );
    let mut graph = TypeGraph::new(&arena);
    let actual = graph.fresh_effect();
    let tail = graph.fresh_effect();
    graph
        .constrain_subtype(
            Type::EffectRow(vec![con(
                &["std", "control", "var", "ref_update"],
                vec![int_type()],
            )]),
            actual.clone(),
        )
        .unwrap();
    graph
        .constrain_subtype(
            Type::EffectRow(vec![con(&["&x#0:0"], vec![int_type()])]),
            actual.clone(),
        )
        .unwrap();
    graph
        .constrain_consumed_computation_effect(
            actual,
            Type::EffectRow(vec![
                con(&["std", "control", "var", "ref_update"], vec![int_type()]),
                tail.clone(),
            ]),
        )
        .unwrap();
    graph.solve_constraints().unwrap();
    let solution = graph.solve_slots().unwrap();
    let mut resolver = TypeResolver::new(&graph, &solution);

    assert_eq!(
        resolver.resolve(&tail).unwrap(),
        Type::EffectRow(vec![con(&["&x#0:0"], vec![int_type()])])
    );
}

#[test]
fn effect_row_item_payload_candidates_keep_union_and_intersection() {
    let arena = poly_expr::Arena::new();
    let graph = TypeGraph::new(&arena);
    let list_int = list_type(int_type());
    let int_payload = con(&["state"], vec![int_type()]);
    let list_payload = con(&["state"], vec![list_int.clone()]);

    assert_eq!(
        merge_effect_row_item_candidate(
            &graph,
            int_payload.clone(),
            list_payload.clone(),
            CandidateMerge::Join,
        )
        .unwrap(),
        con(
            &["state"],
            vec![types::simplify_type(Type::Union(
                Box::new(int_type()),
                Box::new(list_int.clone()),
            ))],
        )
    );
    assert_eq!(
        merge_effect_row_item_candidate(&graph, int_payload, list_payload, CandidateMerge::Meet,)
            .unwrap(),
        con(
            &["state"],
            vec![types::simplify_type(Type::Intersection(
                Box::new(int_type()),
                Box::new(list_int),
            ))],
        )
    );
}

#[test]
fn effect_slot_keeps_lower_row_when_upper_meet_collapses_to_empty() {
    let arena = arena_with_effect_families(&[
        &["std", "io", "file", "file"],
        &["std", "control", "nondet", "nondet"],
        &["std", "control", "flow", "sub"],
    ]);
    let mut graph = TypeGraph::new(&arena);
    let slot = graph.fresh_effect();
    let file = con(&["std", "io", "file", "file"], Vec::new());
    let nondet = con(&["std", "control", "nondet", "nondet"], Vec::new());
    let flow = con(
        &["std", "control", "flow", "sub"],
        vec![con(
            &["std", "control", "var", "ref"],
            vec![Type::EffectRow(vec![file.clone()]), str_type()],
        )],
    );

    graph
        .constrain_subtype(Type::EffectRow(vec![file.clone()]), slot.clone())
        .unwrap();
    graph
        .constrain_subtype(slot.clone(), Type::EffectRow(vec![file.clone()]))
        .unwrap();
    graph
        .constrain_subtype(slot.clone(), Type::EffectRow(vec![nondet, flow]))
        .unwrap();
    graph.solve_constraints().unwrap();
    let solution = graph.solve_slots().unwrap();
    let mut resolver = TypeResolver::new(&graph, &solution);

    assert_eq!(
        resolver.resolve(&slot).unwrap(),
        Type::EffectRow(vec![file])
    );
}

#[test]
fn effect_slot_keeps_lower_row_covered_by_nested_upper_payload() {
    let arena = arena_with_effect_families(&[
        &["std", "io", "file", "file"],
        &["std", "control", "nondet", "nondet"],
        &["std", "control", "flow", "sub"],
    ]);
    let mut graph = TypeGraph::new(&arena);
    let slot = graph.fresh_effect();
    let file = con(&["std", "io", "file", "file"], Vec::new());
    let nondet = con(&["std", "control", "nondet", "nondet"], Vec::new());
    let flow = con(
        &["std", "control", "flow", "sub"],
        vec![con(
            &["std", "control", "var", "ref"],
            vec![Type::EffectRow(vec![file.clone()]), str_type()],
        )],
    );
    let lower = Type::EffectRow(vec![file.clone(), nondet.clone(), flow.clone()]);
    let upper = Type::EffectRow(vec![nondet, flow.clone()]);

    graph
        .constrain_subtype(lower.clone(), slot.clone())
        .unwrap();
    graph.constrain_subtype(slot.clone(), upper).unwrap();
    graph.solve_constraints().unwrap();
    let solution = graph.solve_slots().unwrap();
    let mut resolver = TypeResolver::new(&graph, &solution);

    assert_eq!(resolver.resolve(&slot).unwrap(), lower);
}

#[test]
fn effect_slot_lower_rows_do_not_force_same_family_payloads_exact() {
    let arena = arena_with_effect_families(&[&["std", "control", "var", "ref_update"]]);
    let mut graph = TypeGraph::new(&arena);
    let effect = graph.fresh_effect();
    let list_int = list_type(int_type());
    let int_update = Type::EffectRow(vec![con(
        &["std", "control", "var", "ref_update"],
        vec![int_type()],
    )]);
    let list_update = Type::EffectRow(vec![con(
        &["std", "control", "var", "ref_update"],
        vec![list_int.clone()],
    )]);

    graph.constrain_subtype(int_update, effect.clone()).unwrap();
    graph
        .constrain_subtype(list_update, effect.clone())
        .unwrap();
    graph.solve_constraints().unwrap();
    let solution = graph.solve_slots().unwrap();
    let mut resolver = TypeResolver::new(&graph, &solution);

    assert_eq!(
        resolver.resolve(&effect).unwrap(),
        Type::EffectRow(vec![con(
            &["std", "control", "var", "ref_update"],
            vec![types::simplify_type(Type::Union(
                Box::new(int_type()),
                Box::new(list_int)
            ))],
        )])
    );
}

#[test]
fn effect_row_lower_with_tail_refines_to_closed_upper() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let tail = graph.fresh_effect();
    let next = con(&["loop", "next"], Vec::new());
    let redo = con(&["loop", "redo"], Vec::new());
    let local = con(&["local"], Vec::new());
    let lower = Type::EffectRow(vec![next.clone(), tail]);
    let upper = Type::EffectRow(vec![redo.clone(), next.clone(), local.clone()]);

    assert_eq!(
        refine_effect_lower_with_upper(&graph, &lower, &upper).unwrap(),
        Some(Type::EffectRow(vec![next, redo, local]))
    );
}

#[test]
fn effect_row_recursive_tail_refines_to_finite_closed_row() {
    let arena = arena_with_effect_families(&[
        &["std", "io", "file", "file"],
        &["std", "io", "file", "io_err"],
        &["&state"],
        &["&other"],
    ]);
    let mut graph = TypeGraph::new(&arena);
    let tail = graph.fresh_effect();
    let residual = graph.fresh_effect();
    let file = con(&["std", "io", "file", "file"], Vec::new());
    let io_err = con(&["std", "io", "file", "io_err"], Vec::new());
    let state = con(&["&state"], vec![int_type()]);
    let other = con(&["&other"], vec![int_type()]);

    graph
        .constrain_subtype(
            tail.clone(),
            Type::EffectRow(vec![state.clone(), residual.clone()]),
        )
        .unwrap();
    graph
        .constrain_subtype(residual, Type::EffectRow(vec![other.clone()]))
        .unwrap();
    graph.solve_constraints().unwrap();

    let lower = Type::EffectRow(vec![file.clone(), io_err.clone(), state.clone(), tail]);
    let upper = Type::EffectRow(vec![state.clone(), other.clone()]);

    assert_eq!(
        refine_effect_lower_with_upper(&graph, &lower, &upper).unwrap(),
        Some(Type::EffectRow(vec![file, io_err, state, other]))
    );
}

#[test]
fn effect_row_tail_does_not_refine_to_unreachable_closed_upper() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let tail = graph.fresh_effect();
    let file = con(&["std", "io", "file", "file"], Vec::new());
    let state = con(&["&state"], vec![int_type()]);
    let lower = Type::EffectRow(vec![file, tail]);
    let upper = Type::EffectRow(vec![state]);

    assert_eq!(
        refine_effect_lower_with_upper(&graph, &lower, &upper).unwrap(),
        None
    );
}

#[test]
fn function_candidate_subtype_checks_ret_effect() {
    let arena = poly_expr::Arena::new();
    let graph = TypeGraph::new(&arena);
    let effect = Type::EffectRow(vec![con(&["effect"], Vec::new())]);
    let pure = unary_effect_type(
        Type::pure_effect(),
        Type::unit(),
        Type::pure_effect(),
        int_type(),
    );
    let effectful = unary_effect_type(
        Type::pure_effect(),
        Type::unit(),
        effect.clone(),
        int_type(),
    );

    assert!(type_candidate_subtype(&graph, &pure, &effectful));
    assert!(!type_candidate_subtype(&graph, &effectful, &pure));
}

#[test]
fn function_candidate_subtype_checks_arg_effect_contravariantly() {
    let arena = poly_expr::Arena::new();
    let graph = TypeGraph::new(&arena);
    let effect = Type::EffectRow(vec![con(&["effect"], Vec::new())]);
    let pure_arg = unary_effect_type(
        Type::pure_effect(),
        Type::unit(),
        Type::pure_effect(),
        int_type(),
    );
    let effectful_arg = unary_effect_type(
        effect.clone(),
        Type::unit(),
        Type::pure_effect(),
        int_type(),
    );

    assert!(type_candidate_subtype(&graph, &effectful_arg, &pure_arg));
    assert!(!type_candidate_subtype(&graph, &pure_arg, &effectful_arg));
}

#[test]
fn function_candidates_merge_effects_by_variance() {
    let arena = poly_expr::Arena::new();
    let graph = TypeGraph::new(&arena);
    let arg_effect = Type::EffectRow(vec![con(&["arg"], Vec::new())]);
    let left_ret_effect = Type::EffectRow(vec![con(&["left"], Vec::new())]);
    let right_ret_effect = Type::EffectRow(vec![con(&["right"], Vec::new())]);
    let pure = unary_effect_type(
        Type::pure_effect(),
        Type::unit(),
        left_ret_effect.clone(),
        int_type(),
    );
    let effectful_arg = unary_effect_type(
        arg_effect.clone(),
        Type::unit(),
        right_ret_effect.clone(),
        int_type(),
    );

    assert_eq!(
        join_type_candidates(&graph, pure.clone(), effectful_arg.clone()).unwrap(),
        unary_effect_type(
            Type::pure_effect(),
            Type::unit(),
            Type::EffectRow(vec![
                con(&["left"], Vec::new()),
                con(&["right"], Vec::new())
            ]),
            int_type()
        )
    );
    assert_eq!(
        meet_type_candidates(&graph, pure, effectful_arg).unwrap(),
        unary_effect_type(arg_effect, Type::unit(), Type::pure_effect(), int_type())
    );
}

#[test]
fn function_slot_lower_candidates_join_ret_effects() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let slot = graph.fresh_value();
    let left_ret_effect = Type::EffectRow(vec![con(&["left"], Vec::new())]);
    let right_ret_effect = Type::EffectRow(vec![con(&["right"], Vec::new())]);
    let left = unary_effect_type(
        Type::pure_effect(),
        Type::unit(),
        left_ret_effect,
        int_type(),
    );
    let right = unary_effect_type(
        Type::pure_effect(),
        Type::unit(),
        right_ret_effect,
        int_type(),
    );

    graph.constrain_subtype(left, slot.clone()).unwrap();
    graph.constrain_subtype(right, slot.clone()).unwrap();
    graph.solve_constraints().unwrap();
    let solution = graph.solve_slots().unwrap();
    let mut resolver = TypeResolver::new(&graph, &solution);

    assert_eq!(
        resolver.resolve(&slot).unwrap(),
        unary_effect_type(
            Type::pure_effect(),
            Type::unit(),
            Type::EffectRow(vec![
                con(&["left"], Vec::new()),
                con(&["right"], Vec::new())
            ]),
            int_type()
        )
    );
}

#[test]
fn function_slot_upper_candidates_meet_arg_effects() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let slot = graph.fresh_value();
    let arg_effect = Type::EffectRow(vec![con(&["arg"], Vec::new())]);
    let pure_arg = unary_effect_type(
        Type::pure_effect(),
        Type::unit(),
        Type::pure_effect(),
        int_type(),
    );
    let effectful_arg = unary_effect_type(
        arg_effect.clone(),
        Type::unit(),
        Type::pure_effect(),
        int_type(),
    );

    graph.constrain_subtype(slot.clone(), pure_arg).unwrap();
    graph
        .constrain_subtype(slot.clone(), effectful_arg)
        .unwrap();
    graph.solve_constraints().unwrap();
    let solution = graph.solve_slots().unwrap();
    let mut resolver = TypeResolver::new(&graph, &solution);

    assert_eq!(
        resolver.resolve(&slot).unwrap(),
        unary_effect_type(arg_effect, Type::unit(), Type::pure_effect(), int_type())
    );
}

#[test]
fn function_subtyping_compares_split_runtime_return_shapes() {
    let arena = arena_with_effect_families(&[&["effect"]]);
    let mut graph = TypeGraph::new(&arena);
    let effect = graph.fresh_effect();
    let effect_item = con(&["effect"], Vec::new());
    let effect_row = Type::EffectRow(vec![effect_item.clone()]);
    graph
        .constrain_subtype(effect_row.clone(), effect.clone())
        .unwrap();
    let actual = Type::Fun {
        arg: Box::new(Type::unit()),
        arg_effect: Box::new(Type::pure_effect()),
        ret_effect: Box::new(Type::pure_effect()),
        ret: Box::new(types::runtime_shape(effect.clone(), Type::unit())),
    };
    let expected = Type::Fun {
        arg: Box::new(Type::unit()),
        arg_effect: Box::new(Type::pure_effect()),
        ret_effect: Box::new(effect),
        ret: Box::new(Type::unit()),
    };

    graph.constrain_exact(actual, expected).unwrap();
    graph.solve_constraints().unwrap();

    let solution = graph.solve_slots().unwrap();
    assert!(solution.slots.iter().any(|slot| {
        matches!(
            slot,
            SlotSolution::Resolved(Type::EffectRow(items)) if items == &vec![effect_item.clone()]
        )
    }));
}

fn unary_effect_type(arg_effect: Type, arg: Type, ret_effect: Type, ret: Type) -> Type {
    Type::Fun {
        arg: Box::new(arg),
        arg_effect: Box::new(arg_effect),
        ret_effect: Box::new(ret_effect),
        ret: Box::new(ret),
    }
}

fn field(name: &str, value: Type, optional: bool) -> TypeField {
    TypeField {
        name: name.into(),
        value,
        optional,
    }
}

fn variant(name: &str, payloads: Vec<Type>) -> TypeVariant {
    TypeVariant {
        name: name.into(),
        payloads,
    }
}

fn arena_with_effect_families(families: &[&[&str]]) -> poly_expr::Arena {
    let mut arena = poly_expr::Arena::new();
    for (index, family) in families.iter().enumerate() {
        let mut operation = family
            .iter()
            .map(|segment| (*segment).to_string())
            .collect::<Vec<_>>();
        operation.push("op".into());
        arena.effect_operations.insert(
            poly_expr::DefId(index as u32),
            poly_expr::EffectOperation { path: operation },
        );
    }
    arena
}

fn assert_unsatisfied_subtype(error: SpecializeError, lower: Type, upper: Type) {
    let SpecializeError::UnsatisfiedSubtype {
        lower: actual_lower,
        upper: actual_upper,
        origin: None,
    } = error
    else {
        panic!("expected unsatisfied subtype, got {error:?}");
    };
    assert_eq!(actual_lower, lower);
    assert_eq!(actual_upper, upper);
}
