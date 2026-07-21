use super::super::*;

const SOURCE: &[&str] = &["source"];
const TARGET: &[&str] = &["target"];

#[test]
fn primary_cast_seams_characterize_zero_one_and_two_candidates() {
    for candidate_count in 0..=2 {
        let arena = arena_with_generic_casts(candidate_count);
        let actual = unary_con(SOURCE, mono_con(&["int"]));
        let expected = unary_con(TARGET, mono_con(&["int"]));
        let mut graph = TypeGraph::new(&arena);

        assert!(
            graph
                .constrain_direct_cast(
                    &path(SOURCE),
                    &path(TARGET),
                    actual.clone(),
                    expected.clone(),
                )
                .is_ok()
        );
        assert_eq!(graph.pending.len(), candidate_count);
        assert_eq!(graph.slots.len(), candidate_count);
        graph
            .solve_constraints()
            .expect("all candidates currently solve");

        let selected = direct_cast_rule(&arena, &actual, &expected).map(|rule| rule.def);
        assert_eq!(
            selected,
            (candidate_count > 0).then_some(poly_expr::DefId(0))
        );
        assert_eq!(
            type_candidate_subtype(&graph, &actual, &expected),
            candidate_count > 0
        );

        let mut emitter = Specializer2::new();
        let instance = emitter
            .cast_boundary_instance(&arena, &actual, &expected)
            .expect("current emission lookup should not report cardinality errors");
        assert_eq!(instance.is_some(), candidate_count > 0);
        assert_eq!(
            emitter.pending_instances.len(),
            usize::from(candidate_count > 0)
        );
        if candidate_count > 0 {
            assert_eq!(emitter.pending_instances[0].def, poly_expr::DefId(0));
        }

        // Future oracle by candidate_count: 0 = Missing, 1 = Unique, 2 = Ambiguous. Only Unique
        // should constrain, provide boolean evidence, or enqueue an emitted cast instance. Current
        // specialize2 is empty-success / all-constraints / any-evidence / first-match emission.
    }
}

#[test]
fn primary_ambiguous_emission_selection_reverses_with_registry_order() {
    let forward = arena_with_generic_casts(2);
    let mut reversed = forward.clone();
    reversed.cast_rules.reverse();
    let actual = unary_con(SOURCE, mono_con(&["int"]));
    let expected = unary_con(TARGET, mono_con(&["int"]));

    let forward_def = emission_selected_def(&forward, &actual, &expected);
    let reversed_def = emission_selected_def(&reversed, &actual, &expected);

    assert_eq!(forward_def, poly_expr::DefId(0));
    assert_eq!(reversed_def, poly_expr::DefId(1));
    assert_ne!(forward_def, reversed_def);

    // Future oracle: Ambiguous in both orders. Neither registry order may select a cast instance.
}

#[test]
fn apparently_disjoint_same_pair_schemes_are_not_filtered_for_applicability() {
    for reverse in [false, true] {
        let mut arena = arena_with_concrete_argument_casts(&["int", "bool"]);
        if reverse {
            arena.cast_rules.reverse();
        }
        let actual = unary_con(SOURCE, mono_con(&["int"]));
        let expected = unary_con(TARGET, mono_con(&["int"]));
        let mut graph = TypeGraph::new(&arena);

        graph
            .constrain_direct_cast(
                &path(SOURCE),
                &path(TARGET),
                actual.clone(),
                expected.clone(),
            )
            .unwrap();
        graph
            .solve_constraints()
            .expect("current solver applies both disjoint-looking schemes permissively");
        assert!(type_candidate_subtype(&graph, &actual, &expected));

        let selected = direct_cast_rule(&arena, &actual, &expected)
            .expect("current lookup chooses the first same-pair declaration");
        assert_eq!(
            selected.def,
            if reverse {
                poly_expr::DefId(1)
            } else {
                poly_expr::DefId(0)
            }
        );

        // Future oracle: Ambiguous before applicability, in either order. Section 5 intentionally
        // does not ask whether the int-argument or bool-argument scheme would fit this use site.
    }
}

#[test]
fn poly_value_cast_adapter_matches_the_ocast_a_cardinality_oracle() {
    for candidate_count in 0..=3 {
        let arena = arena_with_generic_casts(candidate_count);
        let (outcome, candidate_defs) =
            cast_resolution_witness(arena.resolve_value_cast(&path(SOURCE), &path(TARGET)));

        assert_eq!(outcome, expected_shadow_outcome(candidate_count));
        assert_eq!(
            candidate_defs,
            (0..candidate_count)
                .map(|index| poly_expr::DefId(index as u32))
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn poly_value_cast_adapter_filters_kind_and_exact_paths_before_classification() {
    let mut arena = arena_with_generic_casts(1);
    let exact = arena.cast_rules[0].clone();
    let mut effect_up = exact.clone();
    effect_up.kind = poly_expr::CastRuleKind::EffectUp;
    let mut other_source = exact.clone();
    other_source.source = path(&["other-source"]);
    let mut other_target = exact.clone();
    other_target.target = path(&["other-target"]);
    arena
        .cast_rules
        .extend([effect_up, other_source, other_target]);

    let (outcome, candidate_defs) =
        cast_resolution_witness(arena.resolve_value_cast(&path(SOURCE), &path(TARGET)));

    assert_eq!(outcome, OrdinaryCastShadowOutcome::Unique);
    assert_eq!(candidate_defs, vec![exact.def]);
}

#[test]
fn primary_cast_seam_shadows_match_the_ocast_a_cardinality_oracle() {
    for candidate_count in 0..=3 {
        let arena = arena_with_generic_casts(candidate_count);
        let actual = unary_con(SOURCE, mono_con(&["int"]));
        let expected = unary_con(TARGET, mono_con(&["int"]));
        let expected_outcome = expected_shadow_outcome(candidate_count);
        let expected_defs = (0..candidate_count)
            .map(|index| poly_expr::DefId(index as u32))
            .collect::<Vec<_>>();

        begin_ordinary_cast_shadow_capture();
        let mut graph = TypeGraph::new(&arena);
        graph
            .constrain_direct_cast(
                &path(SOURCE),
                &path(TARGET),
                actual.clone(),
                expected.clone(),
            )
            .expect("shadow observation must not change permissive constraint behavior");
        assert_eq!(
            type_candidate_subtype(&graph, &actual, &expected),
            candidate_count > 0
        );
        let mut emitter = Specializer2::new();
        let instance = emitter
            .cast_boundary_instance(&arena, &actual, &expected)
            .expect("shadow observation must not change first-match emission behavior");
        assert_eq!(instance.is_some(), candidate_count > 0);
        let witnesses = finish_ordinary_cast_shadow_capture();

        assert_primary_shadow_witnesses(&witnesses, expected_outcome, &expected_defs);
    }
}

#[test]
fn primary_ambiguous_shadows_stay_ambiguous_under_registry_order_reversal() {
    let mut selected_defs = Vec::new();
    for reverse in [false, true] {
        let mut arena = arena_with_generic_casts(2);
        if reverse {
            arena.cast_rules.reverse();
        }
        let actual = unary_con(SOURCE, mono_con(&["int"]));
        let expected = unary_con(TARGET, mono_con(&["int"]));
        let expected_defs = if reverse {
            vec![poly_expr::DefId(1), poly_expr::DefId(0)]
        } else {
            vec![poly_expr::DefId(0), poly_expr::DefId(1)]
        };
        let (adapter_outcome, adapter_defs) =
            cast_resolution_witness(arena.resolve_value_cast(&path(SOURCE), &path(TARGET)));
        assert_eq!(adapter_outcome, OrdinaryCastShadowOutcome::Ambiguous);
        assert_eq!(adapter_defs, expected_defs);

        begin_ordinary_cast_shadow_capture();
        let mut graph = TypeGraph::new(&arena);
        graph
            .constrain_direct_cast(
                &path(SOURCE),
                &path(TARGET),
                actual.clone(),
                expected.clone(),
            )
            .expect("current constraint behavior still instantiates every candidate");
        assert!(type_candidate_subtype(&graph, &actual, &expected));
        selected_defs.push(emission_selected_def(&arena, &actual, &expected));
        let witnesses = finish_ordinary_cast_shadow_capture();

        assert_primary_shadow_witnesses(
            &witnesses,
            OrdinaryCastShadowOutcome::Ambiguous,
            &expected_defs,
        );
    }

    assert_eq!(
        selected_defs,
        vec![poly_expr::DefId(0), poly_expr::DefId(1)]
    );
}

#[test]
fn missing_source_boundaries_reach_current_primary_runtime_ir() {
    let cases = [
        (
            "struct-field",
            "struct S { x: bool }\nS { x: 42 }\n",
            "adapter[{x: bool} -> S => {x: int} -> S",
            "{x: 42}",
        ),
        (
            "function-result",
            "my f(): bool = 42\nf()\n",
            "m0 = d0 : unit -> int | bool",
            "\\() -> 42",
        ),
    ];

    for (name, source, type_fragment, value_fragment) in cases {
        let lowering = lower_source(source);
        assert!(lowering.errors.is_empty(), "{name}: {:?}", lowering.errors);
        let program = crate::specialize(&lowering.session.poly)
            .unwrap_or_else(|error| panic!("{name}: current specialization failed: {error}"));
        let dump = mono::dump::dump_program(&program);

        assert!(dump.contains(type_fragment), "{name}: {dump}");
        assert!(dump.contains(value_fragment), "{name}: {dump}");

        // Future oracle: Missing. Today the struct field reaches a runtime adapter boundary (the
        // evidence VM reports `runtime boundary`), while the annotated function returns Int(42).
    }
}

#[test]
fn source_declaration_order_changes_the_current_selected_runtime_cast() {
    let forward = mono_dump_for_source(&ambiguous_source("1", "2"));
    let reversed = mono_dump_for_source(&ambiguous_source("2", "1"));

    assert!(forward.contains("den: 1"), "{forward}");
    assert!(!forward.contains("den: 2"), "{forward}");
    assert!(reversed.contains("den: 2"), "{reversed}");
    assert!(!reversed.contains("den: 1"), "{reversed}");

    // Future oracle: Ambiguous for both source orders. Current first-match emission makes the
    // evidence-VM values differ (`den: 1` versus `den: 2`); the future classifier must emit neither.
}

fn arena_with_generic_casts(count: usize) -> poly_expr::Arena {
    let mut arena = poly_expr::Arena::new();
    for _ in 0..count {
        let scheme = generic_unary_cast_scheme(&mut arena.typ, path(SOURCE), path(TARGET));
        push_cast_rule(&mut arena, scheme);
    }
    arena
}

fn arena_with_concrete_argument_casts(arguments: &[&str]) -> poly_expr::Arena {
    let mut arena = poly_expr::Arena::new();
    for argument in arguments {
        let scheme = concrete_unary_cast_scheme(
            &mut arena.typ,
            path(SOURCE),
            path(TARGET),
            vec![(*argument).to_string()],
        );
        push_cast_rule(&mut arena, scheme);
    }
    arena
}

fn push_cast_rule(arena: &mut poly_expr::Arena, scheme: poly::types::Scheme) {
    let body = arena.add_expr(poly_expr::Expr::Lit(poly_expr::Lit::Unit));
    let def = arena.defs.fresh();
    arena.defs.set(
        def,
        poly_expr::Def::Let {
            vis: poly_expr::Vis::Pub,
            scheme: Some(scheme.clone()),
            body: Some(body),
            children: Vec::new(),
        },
    );
    arena.cast_rules.push(poly_expr::CastRule {
        def,
        source: path(SOURCE),
        target: path(TARGET),
        scheme,
        kind: poly_expr::CastRuleKind::Value,
    });
}

fn generic_unary_cast_scheme(
    types: &mut poly::types::TypeArena,
    source: Vec<String>,
    target: Vec<String>,
) -> poly::types::Scheme {
    let variable = poly::types::TypeVar(0);
    let source_arg = poly_var_neu(types, variable);
    let target_arg = poly_var_neu(types, variable);
    cast_scheme(
        types,
        source,
        source_arg,
        target,
        target_arg,
        vec![variable],
    )
}

fn concrete_unary_cast_scheme(
    types: &mut poly::types::TypeArena,
    source: Vec<String>,
    target: Vec<String>,
    argument: Vec<String>,
) -> poly::types::Scheme {
    let source_arg = poly_con_neu(types, &argument);
    let target_arg = poly_con_neu(types, &argument);
    cast_scheme(types, source, source_arg, target, target_arg, Vec::new())
}

fn cast_scheme(
    types: &mut poly::types::TypeArena,
    source: Vec<String>,
    source_arg: poly::types::NeuId,
    target: Vec<String>,
    target_arg: poly::types::NeuId,
    quantifiers: Vec<poly::types::TypeVar>,
) -> poly::types::Scheme {
    let arg = types.alloc_neg(poly::types::Neg::Con(source, vec![source_arg]));
    let arg_effect = types.alloc_neg(poly::types::Neg::Bot);
    let ret_effect = types.alloc_pos(poly::types::Pos::Bot);
    let ret = types.alloc_pos(poly::types::Pos::Con(target, vec![target_arg]));
    let predicate = types.alloc_pos(poly::types::Pos::Fun {
        arg,
        arg_eff: arg_effect,
        ret_eff: ret_effect,
        ret,
    });
    poly::types::Scheme {
        quantifiers,
        role_predicates: Vec::new(),
        recursive_bounds: Vec::new(),
        stack_quantifiers: Vec::new(),
        predicate,
    }
}

fn poly_var_neu(
    types: &mut poly::types::TypeArena,
    variable: poly::types::TypeVar,
) -> poly::types::NeuId {
    let lower = types.alloc_pos(poly::types::Pos::Var(variable));
    let upper = types.alloc_neg(poly::types::Neg::Var(variable));
    types.alloc_neu(poly::types::Neu::Bounds(lower, upper))
}

fn poly_con_neu(types: &mut poly::types::TypeArena, path: &[String]) -> poly::types::NeuId {
    let lower = types.alloc_pos(poly::types::Pos::Con(path.to_vec(), Vec::new()));
    let upper = types.alloc_neg(poly::types::Neg::Con(path.to_vec(), Vec::new()));
    types.alloc_neu(poly::types::Neu::Bounds(lower, upper))
}

fn emission_selected_def(
    arena: &poly_expr::Arena,
    actual: &Type,
    expected: &Type,
) -> poly_expr::DefId {
    let mut emitter = Specializer2::new();
    emitter
        .cast_boundary_instance(arena, actual, expected)
        .expect("current emission lookup")
        .expect("same-pair candidate should enqueue an instance");
    emitter.pending_instances[0].def
}

fn expected_shadow_outcome(candidate_count: usize) -> OrdinaryCastShadowOutcome {
    match candidate_count {
        0 => OrdinaryCastShadowOutcome::Missing,
        1 => OrdinaryCastShadowOutcome::Unique,
        _ => OrdinaryCastShadowOutcome::Ambiguous,
    }
}

fn cast_resolution_witness(
    resolution: poly::cast_resolution::OrdinaryCastResolution<&poly_expr::CastRule>,
) -> (OrdinaryCastShadowOutcome, Vec<poly_expr::DefId>) {
    match resolution {
        poly::cast_resolution::OrdinaryCastResolution::Missing => {
            (OrdinaryCastShadowOutcome::Missing, Vec::new())
        }
        poly::cast_resolution::OrdinaryCastResolution::Unique(rule) => {
            (OrdinaryCastShadowOutcome::Unique, vec![rule.def])
        }
        poly::cast_resolution::OrdinaryCastResolution::Ambiguous(rules) => (
            OrdinaryCastShadowOutcome::Ambiguous,
            rules.into_iter().map(|rule| rule.def).collect(),
        ),
    }
}

fn assert_primary_shadow_witnesses(
    witnesses: &[OrdinaryCastShadowWitness],
    expected_outcome: OrdinaryCastShadowOutcome,
    expected_defs: &[poly_expr::DefId],
) {
    assert_eq!(witnesses.len(), 3, "one witness per specialize2 seam");
    for seam in [
        OrdinaryCastShadowSeam::TypeGraphConstraint,
        OrdinaryCastShadowSeam::EmissionSelection,
        OrdinaryCastShadowSeam::BooleanSubtypeEvidence,
    ] {
        let matching = witnesses
            .iter()
            .filter(|witness| witness.seam == seam)
            .collect::<Vec<_>>();
        assert_eq!(matching.len(), 1, "one witness for {seam:?}");
        let witness = matching[0];
        assert_eq!(witness.source, path(SOURCE));
        assert_eq!(witness.target, path(TARGET));
        assert_eq!(witness.outcome, expected_outcome);
        assert_eq!(witness.candidate_defs, expected_defs);
    }
}

fn unary_con(path_segments: &[&str], argument: Type) -> Type {
    Type::Con {
        path: path(path_segments),
        args: vec![argument],
    }
}

fn mono_con(path_segments: &[&str]) -> Type {
    Type::Con {
        path: path(path_segments),
        args: Vec::new(),
    }
}

fn lower_source(source: &str) -> infer::lowering::BodyLowering {
    let files = sources::load(vec![sources::SourceFile {
        module_path: sources::Path::default(),
        source: source.to_string(),
    }]);
    infer::dump::dump_loaded_files(&files)
        .expect("source should lower")
        .lowering
}

fn mono_dump_for_source(source: &str) -> String {
    let lowering = lower_source(source);
    assert!(lowering.errors.is_empty(), "{:?}", lowering.errors);
    let program =
        crate::specialize(&lowering.session.poly).expect("current source should specialize");
    mono::dump::dump_program(&program)
}

fn ambiguous_source(first_denominator: &str, second_denominator: &str) -> String {
    format!(
        concat!(
            "struct frac {{ num: int, den: int }}\n",
            "pub cast(x: int): frac = frac {{ num: x, den: {} }}\n",
            "pub cast(x: int): frac = frac {{ num: x, den: {} }}\n",
            "my y: frac = 1\n",
            "y\n",
        ),
        first_denominator, second_denominator,
    )
}

fn path(segments: &[&str]) -> Vec<String> {
    segments
        .iter()
        .map(|segment| (*segment).to_string())
        .collect()
}
