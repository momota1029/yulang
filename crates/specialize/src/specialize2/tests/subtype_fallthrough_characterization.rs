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
// STF-F can flip individual cells while retaining the same exhaustive sweep.
const CURRENT_FIXED_HEAD_MATRIX: [[Option<MatrixExpectation>; 6]; 6] = [
    [
        None,
        Some(Accepts),
        Some(Rejects),
        Some(Accepts),
        Some(Accepts),
        Some(Accepts),
    ],
    [
        Some(Accepts),
        None,
        Some(Rejects),
        Some(Accepts),
        Some(Accepts),
        Some(Accepts),
    ],
    [
        Some(Accepts),
        Some(Accepts),
        None,
        Some(Accepts),
        Some(Accepts),
        Some(Accepts),
    ],
    [
        Some(Accepts),
        Some(Accepts),
        Some(Rejects),
        None,
        Some(Accepts),
        Some(Accepts),
    ],
    [
        Some(Accepts),
        Some(Accepts),
        Some(Rejects),
        Some(Accepts),
        None,
        Some(Accepts),
    ],
    [
        Some(Accepts),
        Some(Accepts),
        Some(Rejects),
        Some(Accepts),
        Some(Accepts),
        None,
    ],
];

#[test]
fn stf_a_surface_fixtures_reach_the_current_specialize_fail_open_paths() {
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
        let lowering = lower_real_source(&source);
        specialize(&lowering.session.poly, lowering.subtype_provenance()).unwrap_or_else(|error| {
            panic!("{fixture} must remain a known gap until STF-F/G: {error}")
        });
    }
}

#[test]
fn stf_a_specialize_fixed_head_matrix_characterizes_all_thirty_ordered_pairs() {
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
fn stf_a_specialize_keeps_effect_family_and_nominal_field_projection_controls() {
    let arena = arena_with_effect_families(&[&["tick"]]);
    let mut graph = TypeGraph::new(&arena);
    let item = con(&["tick"], Vec::new());
    graph
        .constrain_subtype(item.clone(), Type::EffectRow(vec![item]))
        .unwrap();
    graph.solve_constraints().unwrap();

    let lowering = lower_real_source(concat!(
        "struct point { x: int }\n",
        "my get(p: point): int = p.x\n",
        "get (point { x: 2 })\n",
    ));
    specialize(&lowering.session.poly, lowering.subtype_provenance())
        .expect("nominal field projection remains valid");
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
