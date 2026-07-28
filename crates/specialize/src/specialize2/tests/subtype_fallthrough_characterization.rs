use super::*;

use std::fs;
use std::path::PathBuf;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FixedHead {
    Con,
    Fun,
    Tuple,
    Record,
    PolyVariant,
    EffectRow,
}

impl FixedHead {
    const ALL: [Self; 6] = [
        Self::Con,
        Self::Fun,
        Self::Tuple,
        Self::Record,
        Self::PolyVariant,
        Self::EffectRow,
    ];

    const fn index(self) -> usize {
        self as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MatrixExpectation {
    Accepts,
    Rejects,
}

use MatrixExpectation::{Accepts, Rejects};

// Rows are lower heads and columns are upper heads in FixedHead::ALL order.
const CURRENT_FIXED_HEAD_MATRIX: [[Option<MatrixExpectation>; 6]; 6] = [
    [
        None,
        Some(Rejects),
        Some(Rejects),
        Some(Rejects),
        Some(Rejects),
        Some(Rejects),
    ],
    [
        Some(Rejects),
        None,
        Some(Rejects),
        Some(Rejects),
        Some(Rejects),
        Some(Rejects),
    ],
    [
        Some(Rejects),
        Some(Rejects),
        None,
        Some(Rejects),
        Some(Rejects),
        Some(Rejects),
    ],
    [
        Some(Rejects),
        Some(Rejects),
        Some(Rejects),
        None,
        Some(Rejects),
        Some(Rejects),
    ],
    [
        Some(Rejects),
        Some(Rejects),
        Some(Rejects),
        Some(Rejects),
        None,
        Some(Rejects),
    ],
    [
        Some(Rejects),
        Some(Rejects),
        Some(Rejects),
        Some(Rejects),
        Some(Rejects),
        None,
    ],
];

#[test]
fn stf_f_surface_fixtures_reject_cross_shape_subtypes_during_specialize() {
    for fixture in [
        "subtype_fallthrough_con_to_fun.yu",
        "subtype_fallthrough_fun_to_con.yu",
        "subtype_fallthrough_tuple_to_con.yu",
        "subtype_fallthrough_polyvariant_to_con.yu",
        "subtype_fallthrough_record_to_fun.yu",
        "subtype_fallthrough_record_to_nominal.yu",
    ] {
        let source = fs::read_to_string(runtime_fixture(fixture))
            .unwrap_or_else(|error| panic!("{fixture}: {error}"));
        let lowering = lower_real_source_even_with_inference_diagnostics(&source);
        assert!(
            matches!(
                specialize(&lowering.session.poly, lowering.subtype_provenance()),
                Err(SpecializeError::UnsatisfiedSubtype { .. })
            ),
            "{fixture} must reject during specialization",
        );
    }
}

#[test]
fn stf_g_specialize_fixed_head_matrix_rejects_all_ungated_off_diagonal_pairs() {
    let mut visited = 0;
    for lower in FixedHead::ALL {
        for upper in FixedHead::ALL {
            let Some(expected) = CURRENT_FIXED_HEAD_MATRIX[lower.index()][upper.index()] else {
                continue;
            };
            visited += 1;
            assert_eq!(
                characterize_fixed_head_pair(lower, upper),
                expected,
                "{lower:?} <: {upper:?}",
            );
        }
    }
    assert_eq!(visited, 30);
}

#[test]
fn stf_h_emission_classifier_rejects_every_fixed_head_matrix_reject_pair() {
    let mut visited = 0;
    for lower in FixedHead::ALL {
        for upper in FixedHead::ALL {
            if CURRENT_FIXED_HEAD_MATRIX[lower.index()][upper.index()] != Some(Rejects) {
                continue;
            }
            visited += 1;
            assert_eq!(
                ValueBoundaryKind::classify(&fixed_type(lower), &fixed_type(upper)),
                ValueBoundaryKind::Unsupported,
                "{lower:?} => {upper:?} must not emit generic Coerce",
            );
        }
    }
    assert_eq!(visited, 30);
}

#[test]
fn stf_a_specialize_keeps_open_and_unresolved_alternative_controls() {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let lower_open = graph.fresh_value();
    let upper_open = graph.fresh_value();
    graph
        .constrain_subtype(lower_open, Type::Tuple(vec![Type::unit()]))
        .unwrap();
    graph
        .constrain_subtype(Type::Tuple(vec![Type::unit()]), upper_open)
        .unwrap();

    let union_open = graph.fresh_value();
    graph
        .constrain_subtype(
            Type::Union(
                Box::new(union_open),
                Box::new(Type::Tuple(vec![Type::unit()])),
            ),
            Type::Tuple(vec![Type::unit()]),
        )
        .unwrap();

    let intersection_open = graph.fresh_value();
    graph
        .constrain_subtype(
            Type::Tuple(vec![Type::unit()]),
            Type::Intersection(
                Box::new(intersection_open),
                Box::new(Type::Tuple(vec![Type::unit()])),
            ),
        )
        .unwrap();
    graph.solve_constraints().unwrap();
}

#[test]
fn stf_a_specialize_keeps_top_bottom_and_all_six_same_shape_controls() {
    let arena = arena_with_effect_families(&[&["tick"]]);
    let mut top_bottom = TypeGraph::new(&arena);
    top_bottom
        .constrain_subtype(Type::Never, int_type())
        .unwrap();
    top_bottom.constrain_subtype(int_type(), Type::Any).unwrap();
    top_bottom.solve_constraints().unwrap();

    for head in FixedHead::ALL {
        let mut graph = TypeGraph::new(&arena);
        let (lower, upper) = valid_same_shape_pair(&mut graph, head);
        graph.constrain_subtype(lower, upper).unwrap();
        graph
            .solve_constraints()
            .unwrap_or_else(|error| panic!("{head:?} same-shape control failed: {error}"));
    }
}

#[test]
fn stf_g_specialize_preserves_effect_family_bridge_control() {
    let arena = arena_with_effect_families(&[&["tick"]]);
    let mut graph = TypeGraph::new(&arena);
    let item = con(&["tick"], Vec::new());
    graph
        .constrain_subtype(item.clone(), Type::EffectRow(vec![item]))
        .unwrap();
    graph.solve_constraints().unwrap();

    let lowering = lower_real_source(concat!(
        "act tick:\n",
        "  pub ping: () -> unit\n",
        "tick::ping()\n",
    ));
    specialize(&lowering.session.poly, lowering.subtype_provenance())
        .expect("real effect-family use should specialize");
}

#[test]
fn stf_g_specialize_preserves_generic_nominal_field_projection_control() {
    let lowering = lower_real_source(concat!(
        "struct box 'a { value: 'a }\n",
        "my get(p: box int): int = p.value\n",
        "get (box { value: 2 })\n",
    ));
    specialize(&lowering.session.poly, lowering.subtype_provenance())
        .expect("nominal field projection remains valid");
}

#[test]
fn stf_g_weighted_effect_family_item_preserves_existing_stack_filter_semantics() {
    let arena = arena_with_effect_families(&[&["tick"]]);
    let lower = con(&["tick"], vec![Type::Tuple(vec![Type::unit()])]);
    let upper = con(
        &["tick"],
        vec![Type::Tuple(vec![Type::unit(), Type::unit()])],
    );

    let mut unweighted = TypeGraph::new(&arena);
    unweighted
        .constrain_subtype(lower.clone(), upper.clone())
        .unwrap();
    assert!(matches!(
        unweighted.solve_constraints(),
        Err(SpecializeError::UnsatisfiedSubtype { .. })
    ));

    let excluding_tick = StackWeight {
        entries: vec![StackWeightEntry {
            id: 0,
            pops: 0,
            floor: vec![EffectFamilies::AllExcept(vec![EffectFamily {
                path: vec!["tick".into()],
                args: Vec::new(),
            }])],
            stack: Vec::new(),
        }],
    };
    let mut weighted = TypeGraph::new(&arena);
    weighted
        .constrain_weighted_subtype(lower, excluding_tick, upper, empty_stack_weight())
        .unwrap();
    weighted.solve_constraints().unwrap();
}

#[test]
fn stf_g_nominal_record_bridge_instantiates_generic_projection_with_weight_and_provenance() {
    let arena = arena_with_generic_nominal_record(&["model", "box"], "value");
    let owner = con(
        &["model", "box"],
        vec![Type::Tuple(vec![int_type(), int_type()])],
    );
    let required = Type::Record(vec![field("value", Type::Tuple(vec![int_type()]), false)]);
    let weight = excluding_effect_weight("unrelated");
    let mut weighted = TypeGraph::new(&arena);
    weighted
        .constrain_weighted_subtype(
            owner.clone(),
            weight.clone(),
            required.clone(),
            empty_stack_weight(),
        )
        .unwrap();
    assert!(matches!(
        weighted.solve_constraints(),
        Err(SpecializeError::UnsatisfiedSubtype { .. })
    ));
    assert!(weighted.subtype_provenance_records.iter().any(|record| {
        record.semantic_key.lower_weight == weight
            && record.incoming.iter().any(|incoming| {
                matches!(incoming, SpecializeProvenanceDerivation::Structural { .. })
            })
    }));

    let field_step = TypePositionStep::RecordField {
        alternative: poly::provenance::TypePositionIndex::from_usize(0),
        field: poly::provenance::TypePositionIndex::from_usize(0),
    };
    let mut provenance = TypeGraph::new(&arena);
    provenance
        .constrain_materialized_subtype(
            materialized_root(owner, 31),
            materialized_paths(required, &[(vec![field_step], 41)]),
        )
        .unwrap();
    assert!(matches!(
        provenance.solve_constraints(),
        Err(SpecializeError::UnsatisfiedSubtype { .. })
    ));
    let failure = provenance.shadow_subtype_failures.last().unwrap();
    assert_eq!(failure.lower, vec![ProvenanceAnchor::from_index(31)]);
    assert_eq!(failure.upper, vec![ProvenanceAnchor::from_index(41)]);
}

#[test]
fn stf_g_nominal_record_bridge_accepts_generic_and_missing_optional_fields() {
    let arena = arena_with_generic_nominal_record(&["model", "box"], "value");
    let owner = con(&["model", "box"], vec![int_type()]);
    let upper = Type::Record(vec![
        field("value", int_type(), false),
        field("label", str_type(), true),
    ]);
    let mut graph = TypeGraph::new(&arena);

    graph.constrain_subtype(owner, upper).unwrap();
    graph.solve_constraints().unwrap();
}

#[test]
fn stf_g_direct_type_graph_rejects_reverse_missing_field_and_non_effect_bridges() {
    let arena = arena_with_generic_nominal_record(&["model", "box"], "value");
    let owner = con(&["model", "box"], vec![int_type()]);

    let unknown_owner = con(&["model", "unknown"], vec![int_type()]);
    let unknown_upper = Type::Record(vec![field("value", int_type(), false)]);
    let mut unknown = TypeGraph::new(&arena);
    unknown
        .constrain_subtype(unknown_owner.clone(), unknown_upper.clone())
        .unwrap();
    assert_unsatisfied_subtype(
        unknown.solve_constraints().unwrap_err(),
        unknown_owner,
        unknown_upper,
    );

    let reverse_lower = Type::Record(vec![field("value", int_type(), false)]);
    let mut reverse = TypeGraph::new(&arena);
    reverse
        .constrain_subtype(reverse_lower.clone(), owner.clone())
        .unwrap();
    assert_unsatisfied_subtype(
        reverse.solve_constraints().unwrap_err(),
        reverse_lower,
        owner.clone(),
    );

    let missing_upper = Type::Record(vec![field("missing", int_type(), false)]);
    let mut missing = TypeGraph::new(&arena);
    missing
        .constrain_subtype(owner.clone(), missing_upper.clone())
        .unwrap();
    assert_unsatisfied_subtype(
        missing.solve_constraints().unwrap_err(),
        owner.clone(),
        missing_upper,
    );

    let non_effect_upper = Type::EffectRow(vec![con(&["real", "effect"], Vec::new())]);
    let mut non_effect = TypeGraph::new(&arena);
    non_effect
        .constrain_subtype(owner.clone(), non_effect_upper.clone())
        .unwrap();
    assert_unsatisfied_subtype(
        non_effect.solve_constraints().unwrap_err(),
        owner,
        non_effect_upper,
    );
}

#[test]
fn stf_g_imported_generic_record_certificate_matches_cold_specialization() {
    let prefix_files = vec![
        source_file(&[], "mod models;\npub use models::*\n"),
        source_file(&["models"], "pub struct box 'a { value: 'a }\n"),
    ];
    let suffix_source = concat!(
        "my get(p: box int): int = p.value\n",
        "get (box { value: 7 })\n",
    );
    let cold_files = vec![
        source_file(
            &[],
            &format!("mod models;\npub use models::*\n{suffix_source}"),
        ),
        source_file(&["models"], "pub struct box 'a { value: 'a }\n"),
    ];
    let cold = infer::lowering::lower_loaded_files(&sources::load(cold_files)).unwrap();

    let prefix_loaded = sources::load(prefix_files);
    let compiled = infer::lowering::lower_loaded_files(&prefix_loaded).unwrap();
    let namespace = infer::CompiledNamespaceSurface::from_module_table(&compiled.modules);
    let lowering = infer::CompiledLoweringSurface::from_module_table(&compiled.modules, &namespace);
    let runtime =
        infer::CompiledRuntimeSurface::from_lowering_with_namespace(&compiled, &namespace);
    let prefix = infer::lowering::BodyLoweringPrefix::from_compiled_unit_surfaces(
        &namespace, &lowering, &runtime,
    )
    .expect("compiled prefix should import");
    let suffix = sources::load(vec![source_file(&[], suffix_source)])
        .into_iter()
        .next()
        .unwrap();
    let imported = infer::lowering::lower_root_loaded_file_with_prefix(&prefix, &suffix).unwrap();

    assert!(cold.errors.is_empty(), "{:?}", cold.errors);
    assert!(imported.errors.is_empty(), "{:?}", imported.errors);
    let path = vec!["models".to_string(), "box".to_string()];
    let imported_shape = imported
        .session
        .poly
        .nominal_record_shapes
        .get(&path)
        .expect("imported prefix should retain the generic record certificate");
    assert_eq!(imported_shape.fields.len(), 1);
    assert!(matches!(
        imported
            .session
            .poly
            .defs
            .get(imported_shape.fields[0].projection),
        Some(poly_expr::Def::Let {
            scheme: Some(_),
            ..
        })
    ));

    let cold_program = specialize(&cold.session.poly, cold.subtype_provenance()).unwrap();
    let imported_program =
        specialize(&imported.session.poly, imported.subtype_provenance()).unwrap();
    assert_eq!(
        normalize_dump_def_ids(&mono::dump::dump_program(&imported_program)),
        normalize_dump_def_ids(&mono::dump::dump_program(&cold_program))
    );
}

fn characterize_fixed_head_pair(lower_head: FixedHead, upper_head: FixedHead) -> MatrixExpectation {
    let arena = poly_expr::Arena::new();
    let mut graph = TypeGraph::new(&arena);
    let lower = fixed_type(lower_head);
    let upper = fixed_type(upper_head);
    graph
        .constrain_subtype(lower.clone(), upper.clone())
        .unwrap();
    match graph.solve_constraints() {
        Ok(()) => Accepts,
        Err(SpecializeError::UnsatisfiedSubtype {
            lower: rejected_lower,
            upper: rejected_upper,
            ..
        }) => {
            assert_eq!(rejected_lower, lower);
            assert_eq!(rejected_upper, upper);
            Rejects
        }
        Err(error) => panic!("{lower_head:?} <: {upper_head:?}: unexpected error {error}"),
    }
}

fn fixed_type(head: FixedHead) -> Type {
    match head {
        FixedHead::Con => con(&["matrix"], Vec::new()),
        FixedHead::Fun => types::pure_function_type(Type::unit(), Type::unit()),
        FixedHead::Tuple => Type::Tuple(vec![Type::unit()]),
        FixedHead::Record => Type::Record(vec![field("x", Type::unit(), false)]),
        FixedHead::PolyVariant => Type::PolyVariant(vec![variant("some", vec![Type::unit()])]),
        FixedHead::EffectRow => Type::EffectRow(Vec::new()),
    }
}

fn valid_same_shape_pair(graph: &mut TypeGraph<'_>, head: FixedHead) -> (Type, Type) {
    match head {
        FixedHead::Con => (
            con(&["box"], vec![graph.fresh_value()]),
            con(&["box"], vec![graph.fresh_value()]),
        ),
        FixedHead::Fun => (
            Type::Fun {
                arg: Box::new(Type::Any),
                arg_effect: Box::new(Type::pure_effect()),
                ret_effect: Box::new(Type::pure_effect()),
                ret: Box::new(Type::Never),
            },
            Type::Fun {
                arg: Box::new(Type::Never),
                arg_effect: Box::new(Type::pure_effect()),
                ret_effect: Box::new(Type::pure_effect()),
                ret: Box::new(Type::Any),
            },
        ),
        FixedHead::Tuple => (Type::Tuple(vec![Type::Never]), Type::Tuple(vec![Type::Any])),
        FixedHead::Record => (
            Type::Record(vec![field("x", Type::Never, false)]),
            Type::Record(vec![field("x", Type::Any, false)]),
        ),
        FixedHead::PolyVariant => (
            Type::PolyVariant(vec![variant("some", vec![Type::Never])]),
            Type::PolyVariant(vec![variant("some", vec![Type::Any])]),
        ),
        FixedHead::EffectRow => {
            let item = con(&["tick"], Vec::new());
            let tail = graph.fresh_effect();
            (
                Type::EffectRow(vec![item.clone()]),
                Type::EffectRow(vec![item, tail]),
            )
        }
    }
}

fn runtime_fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/yulang/regressions/runtime")
        .join(name)
}

fn lower_real_source_even_with_inference_diagnostics(
    source: &str,
) -> infer::lowering::BodyLowering {
    let files = sources::load(vec![sources::SourceFile {
        module_path: sources::Path::default(),
        source: source.to_string(),
    }]);
    infer::dump::dump_loaded_files(&files)
        .expect("real subtype fixture should lower")
        .lowering
}

fn arena_with_generic_nominal_record(owner_path: &[&str], field_name: &str) -> poly_expr::Arena {
    let mut arena = poly_expr::Arena::new();
    let owner_path = owner_path
        .iter()
        .map(|segment| (*segment).to_string())
        .collect::<Vec<_>>();
    let variable = poly::types::TypeVar(0);
    let lower = arena.typ.alloc_pos(poly::types::Pos::Var(variable));
    let upper = arena.typ.alloc_neg(poly::types::Neg::Var(variable));
    let argument = arena.typ.alloc_neu(poly::types::Neu::Bounds(lower, upper));
    let receiver = arena
        .typ
        .alloc_neg(poly::types::Neg::Con(owner_path.clone(), vec![argument]));
    let argument_effect = arena.typ.alloc_neg(poly::types::Neg::Bot);
    let return_effect = arena.typ.alloc_pos(poly::types::Pos::Bot);
    let result = arena.typ.alloc_pos(poly::types::Pos::Var(variable));
    let predicate = arena.typ.alloc_pos(poly::types::Pos::Fun {
        arg: receiver,
        arg_eff: argument_effect,
        ret_eff: return_effect,
        ret: result,
    });
    let scheme = poly::types::Scheme {
        quantifiers: vec![variable],
        role_predicates: Vec::new(),
        recursive_bounds: Vec::new(),
        stack_quantifiers: Vec::new(),
        predicate,
    };
    let projection = arena.defs.fresh();
    arena.defs.set(
        projection,
        poly_expr::Def::Let {
            vis: poly_expr::Vis::Pub,
            scheme: Some(scheme),
            body: None,
            children: Vec::new(),
        },
    );
    arena.field_projections.insert(projection);
    arena.nominal_record_shapes.insert(
        owner_path.clone(),
        poly_expr::NominalRecordShape {
            owner_path,
            fields: vec![poly_expr::NominalRecordField {
                name: field_name.to_string(),
                projection,
            }],
        },
    );
    arena
}

fn excluding_effect_weight(path: &str) -> StackWeight {
    StackWeight {
        entries: vec![StackWeightEntry {
            id: 0,
            pops: 0,
            floor: vec![EffectFamilies::AllExcept(vec![EffectFamily {
                path: vec![path.to_string()],
                args: Vec::new(),
            }])],
            stack: Vec::new(),
        }],
    }
}

fn source_file(module: &[&str], source: &str) -> sources::SourceFile {
    sources::SourceFile {
        module_path: sources::Path {
            segments: module
                .iter()
                .map(|segment| sources::Name((*segment).to_string()))
                .collect(),
        },
        source: source.to_string(),
    }
}

fn normalize_dump_def_ids(text: &str) -> String {
    let mut normalized = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.next() {
        normalized.push(ch);
        if ch != 'd' || !chars.peek().is_some_and(char::is_ascii_digit) {
            continue;
        }
        normalized.push('#');
        while chars.peek().is_some_and(char::is_ascii_digit) {
            chars.next();
        }
    }
    normalized
}
