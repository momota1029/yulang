use super::super::*;

const SOURCE: &[&str] = &["source"];
const TARGET: &[&str] = &["target"];

#[test]
fn legacy_direct_cast_constraint_characterizes_zero_one_and_two_candidates() {
    for candidate_count in 0..=2 {
        let arena = arena_with_generic_casts(candidate_count);
        let actual = unary_con(SOURCE, mono_con(&["int"]));
        let expected = unary_con(TARGET, mono_con(&["int"]));
        let mut graph = ConstraintGraph::new(&arena);

        assert!(
            graph
                .constrain_direct_cast(&path(SOURCE), &path(TARGET), actual, expected,)
                .is_ok()
        );
        assert_eq!(graph.pending.len(), candidate_count);
        assert_eq!(graph.slots.len(), candidate_count);
        graph
            .solve_constraints()
            .expect("legacy applies every candidate");

        // Future oracle by candidate_count: 0 = Missing, 1 = Unique, 2 = Ambiguous. The legacy
        // graph currently matches specialize2's empty-success/all-candidates constraint policy.
    }
}

#[test]
fn legacy_closed_candidate_evidence_is_any_closed_rule() {
    for candidate_count in 0..=2 {
        let arena = arena_with_closed_casts(candidate_count);
        let lower = mono_con(SOURCE);
        let upper = mono_con(TARGET);
        let graph = ConstraintGraph::new(&arena);

        assert_eq!(
            graph.direct_closed_cast_subtype(&lower, &upper),
            candidate_count > 0
        );
        assert_eq!(
            type_candidate_subtype(&graph, &lower, &upper),
            candidate_count > 0
        );

        // Future oracle by candidate_count: 0 = Missing/false, 1 = Unique/true,
        // 2 = Ambiguous/false. Current legacy evidence, like specialize2, uses `.any(...)` for
        // cardinality, but unlike specialize2 it only admits closed cast schemes here.
    }
}

#[test]
fn legacy_specialize_roots_emits_a_bare_boundary_even_for_a_unique_cast() {
    let lowering = super::lower_source(concat!(
        "struct target { value: int }\n",
        "pub cast(x: int): target = target { value: x }\n",
        "my y: target = 1\n",
        "y\n",
    ));
    let arena = &lowering.session.poly;
    let [poly::expr::RuntimeRoot::Expr(expr)] = arena.runtime_roots.as_slice() else {
        panic!(
            "expected one expression root, got {:?}",
            arena.runtime_roots
        )
    };
    let poly::expr::Expr::Var(reference) = arena.expr(*expr) else {
        panic!("expected root reference")
    };
    let root = arena.ref_target(*reference).expect("resolved y definition");

    let legacy = crate::specialize_roots(arena, [root]).expect("legacy unique cast route");
    let primary = crate::specialize(arena, lowering.subtype_provenance())
        .expect("primary unique cast route");
    let legacy = mono::dump::dump_program(&legacy);
    let primary = mono::dump::dump_program(&primary);

    assert!(legacy.contains("coerce[int => target](1)"), "{legacy}");
    assert!(!legacy.contains("int -> target"), "{legacy}");
    assert!(primary.contains("int -> target"), "{primary}");
    assert!(!primary.contains("coerce[int => target](1)"), "{primary}");

    // Future oracle: Unique. This separately records the legacy-route difference: its constraint
    // graph accepts the declaration, but its emission does not materialize the cast definition,
    // whereas primary specialize2 emits an application of the unique rule.
}

fn arena_with_generic_casts(count: usize) -> poly_expr::Arena {
    let mut arena = poly_expr::Arena::new();
    for index in 0..count {
        let scheme = generic_unary_cast_scheme(&mut arena.typ, path(SOURCE), path(TARGET));
        arena.cast_rules.push(poly_expr::CastRule {
            def: poly_expr::DefId(index as u32),
            source: path(SOURCE),
            target: path(TARGET),
            scheme,
            kind: poly_expr::CastRuleKind::Value,
        });
    }
    arena
}

fn arena_with_closed_casts(count: usize) -> poly_expr::Arena {
    let mut arena = poly_expr::Arena::new();
    for index in 0..count {
        let scheme = closed_cast_scheme(&mut arena.typ, path(SOURCE), path(TARGET));
        arena.cast_rules.push(poly_expr::CastRule {
            def: poly_expr::DefId(index as u32),
            source: path(SOURCE),
            target: path(TARGET),
            scheme,
            kind: poly_expr::CastRuleKind::Value,
        });
    }
    arena
}

fn generic_unary_cast_scheme(
    types: &mut poly::types::TypeArena,
    source: Vec<String>,
    target: Vec<String>,
) -> poly::types::Scheme {
    let variable = poly::types::TypeVar(0);
    let source_arg = poly_var_neu(types, variable);
    let target_arg = poly_var_neu(types, variable);
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
        quantifiers: vec![variable],
        role_predicates: Vec::new(),
        recursive_bounds: Vec::new(),
        stack_quantifiers: Vec::new(),
        predicate,
    }
}

fn closed_cast_scheme(
    types: &mut poly::types::TypeArena,
    source: Vec<String>,
    target: Vec<String>,
) -> poly::types::Scheme {
    let arg = types.alloc_neg(poly::types::Neg::Con(source, Vec::new()));
    let arg_effect = types.alloc_neg(poly::types::Neg::Bot);
    let ret_effect = types.alloc_pos(poly::types::Pos::Bot);
    let ret = types.alloc_pos(poly::types::Pos::Con(target, Vec::new()));
    let predicate = types.alloc_pos(poly::types::Pos::Fun {
        arg,
        arg_eff: arg_effect,
        ret_eff: ret_effect,
        ret,
    });
    poly::types::Scheme {
        quantifiers: Vec::new(),
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

fn path(segments: &[&str]) -> Vec<String> {
    segments
        .iter()
        .map(|segment| (*segment).to_string())
        .collect()
}
