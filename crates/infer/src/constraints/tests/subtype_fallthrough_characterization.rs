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
    NominalRecordObligation,
    Rejects,
}

// Rows are lower heads and columns are upper heads in FixedHead::ALL order.
// STF-E routes the nominal-record cell to analysis and gates the effect-row cell by registry.
const CURRENT_FIXED_HEAD_MATRIX: [[Option<MatrixExpectation>; 6]; 6] = [
    [
        None,
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::NominalRecordObligation),
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
    ],
    [
        Some(MatrixExpectation::Rejects),
        None,
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
    ],
    [
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        None,
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
    ],
    [
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        None,
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
    ],
    [
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        None,
        Some(MatrixExpectation::Rejects),
    ],
    [
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        Some(MatrixExpectation::Rejects),
        None,
    ],
];

#[test]
fn stf_d_surface_fixtures_reject_the_six_confirmed_counterexamples() {
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
        let output = lower_source(&source);
        assert!(
            output.errors.iter().any(|error| matches!(
                error,
                crate::lowering::BodyLoweringError::Analysis(
                    crate::analysis::AnalysisDiagnostic::UnsatisfiedSubtypeShape { .. }
                )
            )),
            "{fixture} must be rejected as an unsatisfied fixed-head subtype: {:?}",
            output.errors
        );
    }
}

#[test]
fn stf_a_infer_fixed_head_matrix_characterizes_all_thirty_ordered_pairs() {
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
fn stf_a_infer_keeps_open_and_unresolved_alternative_controls() {
    let mut lower_open = ConstraintMachine::new();
    let lower = lower_open.alloc_pos(Pos::Var(TypeVar(0)));
    let upper = fixed_neg(&mut lower_open, FixedHead::Tuple);
    lower_open.subtype(lower, upper, OriginId::unknown_internal());
    assert!(matches!(
        lower_open.events(),
        [ConstraintEvent::UpperBoundAdded {
            var: TypeVar(0),
            ..
        }]
    ));

    let mut upper_open = ConstraintMachine::new();
    let lower = fixed_pos(&mut upper_open, FixedHead::Tuple);
    let upper = upper_open.alloc_neg(Neg::Var(TypeVar(1)));
    upper_open.subtype(lower, upper, OriginId::unknown_internal());
    assert!(matches!(
        upper_open.events(),
        [ConstraintEvent::LowerBoundAdded {
            var: TypeVar(1),
            ..
        }]
    ));

    let mut union = ConstraintMachine::new();
    let open = union.alloc_pos(Pos::Var(TypeVar(2)));
    let tuple = fixed_pos(&mut union, FixedHead::Tuple);
    let lower = union.alloc_pos(Pos::Union(open, tuple));
    let upper = fixed_neg(&mut union, FixedHead::Tuple);
    union.subtype(lower, upper, OriginId::unknown_internal());
    assert!(union.events().iter().any(|event| matches!(
        event,
        ConstraintEvent::UpperBoundAdded {
            var: TypeVar(2),
            ..
        }
    )));

    let mut intersection = ConstraintMachine::new();
    let lower = fixed_pos(&mut intersection, FixedHead::Tuple);
    let open = intersection.alloc_neg(Neg::Var(TypeVar(3)));
    let tuple = fixed_neg(&mut intersection, FixedHead::Tuple);
    let upper = intersection.alloc_neg(Neg::Intersection(open, tuple));
    intersection.subtype(lower, upper, OriginId::unknown_internal());
    assert!(intersection.events().iter().any(|event| matches!(
        event,
        ConstraintEvent::LowerBoundAdded {
            var: TypeVar(3),
            ..
        }
    )));
}

#[test]
fn stf_a_infer_keeps_top_bottom_and_all_six_same_shape_controls() {
    let mut top_bottom = ConstraintMachine::new();
    let never = top_bottom.alloc_pos(Pos::Bot);
    let con_upper = fixed_neg(&mut top_bottom, FixedHead::Con);
    top_bottom.subtype(never, con_upper, OriginId::unknown_internal());
    let con_lower = fixed_pos(&mut top_bottom, FixedHead::Con);
    let any = top_bottom.alloc_neg(Neg::Top);
    top_bottom.subtype(con_lower, any, OriginId::unknown_internal());
    assert!(top_bottom.events().is_empty());

    for head in FixedHead::ALL {
        let mut machine = ConstraintMachine::new();
        let lower = fixed_pos(&mut machine, head);
        let upper = fixed_neg(&mut machine, head);
        machine.subtype(lower, upper, OriginId::unknown_internal());
        assert!(
            machine.events().is_empty(),
            "{head:?} same-shape control emitted an unexpected event: {:?}",
            machine.events()
        );
    }
}

#[test]
fn stf_a_infer_keeps_effect_family_and_nominal_field_projection_controls() {
    let mut machine = ConstraintMachine::new();
    machine.register_effect_family_path(vec!["tick".into()]);
    let lower = machine.alloc_pos(Pos::Con(vec!["tick".into()], Vec::new()));
    let item = machine.alloc_neg(Neg::Con(vec!["tick".into()], Vec::new()));
    let tail = machine.alloc_neg(Neg::Top);
    let upper = machine.alloc_neg(Neg::Row(vec![item], tail));
    machine.subtype(lower, upper, OriginId::unknown_internal());
    assert!(machine.events().is_empty());

    let projection = lower_source(concat!(
        "struct point { x: int }\n",
        "my get(p: point): int = p.x\n",
        "get (point { x: 2 })\n",
    ));
    assert!(
        projection.errors.is_empty(),
        "nominal field projection remains valid: {:?}",
        projection.errors
    );
}

#[test]
fn stf_e_nominal_record_bridge_accepts_generic_nested_optional_and_renamed_shapes() {
    for (case, source) in [
        (
            "generic field",
            concat!(
                "struct box 'a { value: 'a }\n",
                "my unpack({value}) = value\n",
                "my got: int = unpack (box { value: 2 })\n",
            ),
        ),
        (
            "nested field type",
            concat!(
                "struct inner { number: int }\n",
                "struct outer { payload: inner }\n",
                "my read({payload: {number}}) = number\n",
                "my got: int = read (outer { payload: inner { number: 2 } })\n",
            ),
        ),
        (
            "missing optional field",
            concat!(
                "struct marker { other: int }\n",
                "my optional({value = 7}) = value\n",
                "my got: int = optional (marker { other: 2 })\n",
            ),
        ),
        (
            "renamed owner and field",
            concat!(
                "struct parcel 'item { content: 'item }\n",
                "my extract({content}) = content\n",
                "my got: int = extract (parcel { content: 2 })\n",
            ),
        ),
        (
            "renamed module path",
            concat!(
                "mod catalog:\n",
                "  pub struct packet 'item { body: 'item }\n",
                "my extract({body}) = body\n",
                "my got: int = extract (catalog::packet { body: 2 })\n",
            ),
        ),
    ] {
        let output = lower_source(source);
        assert!(output.errors.is_empty(), "{case}: {:?}", output.errors);
    }
}

#[test]
fn stf_e_nominal_record_bridge_rejects_missing_and_nested_mismatching_fields() {
    for (case, source) in [
        (
            "non-struct constructor",
            concat!("my required({value}) = value\n", "required 1\n",),
        ),
        (
            "missing required field",
            concat!(
                "struct marker { other: int }\n",
                "my required({value}) = value\n",
                "required (marker { other: 2 })\n",
            ),
        ),
        (
            "nested field mismatch",
            concat!(
                "struct pair { value: (int, int) }\n",
                "my scalar({value}): int = value\n",
                "scalar (pair { value: (1, 2) })\n",
            ),
        ),
    ] {
        let output = lower_source(source);
        assert!(
            output.errors.iter().any(|error| matches!(
                error,
                crate::lowering::BodyLoweringError::Analysis(
                    crate::analysis::AnalysisDiagnostic::UnsatisfiedSubtypeShape { .. }
                )
            )),
            "{case}: {:?}",
            output.errors
        );
    }
}

#[test]
fn stf_e_effect_family_gate_uses_registry_and_rejects_non_effect_constructors() {
    let mut effect = ConstraintMachine::new();
    effect.register_effect_family_path(vec!["renamed".into(), "pulse".into()]);
    let lower = effect.alloc_pos(Pos::Con(vec!["renamed".into(), "pulse".into()], Vec::new()));
    let item = effect.alloc_neg(Neg::Con(vec!["renamed".into(), "pulse".into()], Vec::new()));
    let tail = effect.alloc_neg(Neg::Top);
    let upper = effect.alloc_neg(Neg::Row(vec![item], tail));
    effect.subtype(lower, upper, OriginId::unknown_internal());
    assert!(
        effect.events().is_empty(),
        "registered effect family should use the existing row comparison: {:?}",
        effect.events()
    );

    let mut value = ConstraintMachine::new();
    let lower = value.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let tail = value.alloc_neg(Neg::Top);
    let upper = value.alloc_neg(Neg::Row(Vec::new(), tail));
    value.subtype(lower, upper, OriginId::unknown_internal());
    assert!(matches!(
        value.events(),
        [ConstraintEvent::UnsatisfiedSubtypeShape(_)]
    ));

    let mut poly = poly::expr::Arena::new();
    poly.register_effect_family_path(vec!["imported".into(), "pulse".into()]);
    let mut session = crate::analysis::AnalysisSession::new(poly);
    let lower = session.infer.alloc_pos(Pos::Con(
        vec!["imported".into(), "pulse".into()],
        Vec::new(),
    ));
    let item = session.infer.alloc_neg(Neg::Con(
        vec!["imported".into(), "pulse".into()],
        Vec::new(),
    ));
    let tail = session.infer.alloc_neg(Neg::Top);
    let upper = session.infer.alloc_neg(Neg::Row(vec![item], tail));
    session
        .infer
        .subtype(lower, upper, OriginId::unknown_internal());
    session.route_constraint_events();
    assert!(
        session.take_diagnostics().is_empty(),
        "poly effect-family certificate should seed the inference registry"
    );
}

fn characterize_fixed_head_pair(lower_head: FixedHead, upper_head: FixedHead) -> MatrixExpectation {
    let mut machine = ConstraintMachine::new();
    let lower = fixed_pos(&mut machine, lower_head);
    let upper = fixed_neg(&mut machine, upper_head);
    machine.subtype(lower, upper, OriginId::unknown_internal());
    assert!(
        machine.canonical_constraint_count() >= 1,
        "{lower_head:?} <: {upper_head:?} must reach the constraint machine"
    );
    match machine.events() {
        [] => MatrixExpectation::Accepts,
        [ConstraintEvent::NominalRecordShapeObligation(_)] => {
            MatrixExpectation::NominalRecordObligation
        }
        [ConstraintEvent::UnsatisfiedSubtypeShape(_)] => MatrixExpectation::Rejects,
        events => panic!("unexpected events for {lower_head:?} <: {upper_head:?}: {events:?}"),
    }
}

fn fixed_pos(machine: &mut ConstraintMachine, head: FixedHead) -> PosId {
    match head {
        FixedHead::Con => machine.alloc_pos(Pos::Con(vec!["matrix".into()], Vec::new())),
        FixedHead::Fun => {
            let arg = machine.alloc_neg(Neg::Top);
            let arg_eff = machine.alloc_neg(Neg::Top);
            let ret_eff = machine.alloc_pos(Pos::Bot);
            let ret = machine.alloc_pos(Pos::Bot);
            machine.alloc_pos(Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            })
        }
        FixedHead::Tuple => {
            let item = machine.alloc_pos(Pos::Bot);
            machine.alloc_pos(Pos::Tuple(vec![item]))
        }
        FixedHead::Record => {
            let value = machine.alloc_pos(Pos::Bot);
            machine.alloc_pos(Pos::Record(vec![RecordField {
                name: "x".into(),
                value,
                optional: false,
            }]))
        }
        FixedHead::PolyVariant => {
            let payload = machine.alloc_pos(Pos::Bot);
            machine.alloc_pos(Pos::PolyVariant(vec![("some".into(), vec![payload])]))
        }
        FixedHead::EffectRow => machine.alloc_pos(Pos::Row(Vec::new())),
    }
}

fn fixed_neg(machine: &mut ConstraintMachine, head: FixedHead) -> NegId {
    match head {
        FixedHead::Con => machine.alloc_neg(Neg::Con(vec!["matrix".into()], Vec::new())),
        FixedHead::Fun => {
            let arg = machine.alloc_pos(Pos::Bot);
            let arg_eff = machine.alloc_pos(Pos::Bot);
            let ret_eff = machine.alloc_neg(Neg::Top);
            let ret = machine.alloc_neg(Neg::Top);
            machine.alloc_neg(Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            })
        }
        FixedHead::Tuple => {
            let item = machine.alloc_neg(Neg::Top);
            machine.alloc_neg(Neg::Tuple(vec![item]))
        }
        FixedHead::Record => {
            let value = machine.alloc_neg(Neg::Top);
            machine.alloc_neg(Neg::Record(vec![RecordField {
                name: "x".into(),
                value,
                optional: false,
            }]))
        }
        FixedHead::PolyVariant => {
            let payload = machine.alloc_neg(Neg::Top);
            machine.alloc_neg(Neg::PolyVariant(vec![("some".into(), vec![payload])]))
        }
        FixedHead::EffectRow => {
            let tail = machine.alloc_neg(Neg::Top);
            machine.alloc_neg(Neg::Row(Vec::new(), tail))
        }
    }
}

fn lower_source(source: &str) -> crate::lowering::BodyLowering {
    let root = rowan::SyntaxNode::new_root(parser::parse_module_to_green(source));
    let lower = crate::lower_module_map(&root);
    crate::lowering::lower_binding_bodies(&root, lower)
}

fn runtime_fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/yulang/regressions/runtime")
        .join(name)
}
