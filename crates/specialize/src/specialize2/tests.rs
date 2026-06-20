use super::*;

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
    let arena = poly_expr::Arena::new();
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
    let arena = poly_expr::Arena::new();
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
fn effect_slot_lower_rows_do_not_force_same_family_payloads_exact() {
    let arena = poly_expr::Arena::new();
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
    let arena = poly_expr::Arena::new();
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

fn assert_unsatisfied_subtype(error: SpecializeError, lower: Type, upper: Type) {
    let SpecializeError::UnsatisfiedSubtype {
        lower: actual_lower,
        upper: actual_upper,
    } = error
    else {
        panic!("expected unsatisfied subtype, got {error:?}");
    };
    assert_eq!(actual_lower, lower);
    assert_eq!(actual_upper, upper);
}
