use super::*;

use crate::constraints::explain::{ExplanationBudget, ExplanationCompleteness, ExplanationNode};
use crate::lowering::{BodyLowering, lower_loaded_files};
use poly::types::{Neg, Pos};
use specialize::mono::Type as MonoType;
use specialize::{SpecializeError, UnsatisfiedSubtypeOrigin};

/// Characterizes the identity gap between infer's persistent derivation graph and
/// specialize's general structural-subtype errors.
///
/// The test deliberately retains `BodyLowering`, so it can inspect the original
/// constraint machine after specializing its adjacent `poly::Arena`. Production's
/// `BuildPolyOutput` retains only the poly arena and sparse source side tables; the
/// structural correlation performed here is therefore not available to production.
#[test]
fn general_subtype_failures_have_infer_analogs_but_carry_no_record_identity() {
    let cases = [
        CharacterizationCase {
            name: "tuple-arity",
            source: "my g(x: (int, int)) = x\ng (1, 2, 3)\n",
            mismatch: StructuralMismatch::TupleArity { lower: 3, upper: 2 },
            expected: Baseline {
                canonical_constraints: 53,
                lower_bounds: 35,
                upper_bounds: 37,
                record: ConstraintRecordId(45),
                explanation_nodes: 36,
                explanation_edges: 48,
                origins: &[
                    ConstraintOriginKind::UnknownInternal,
                    ConstraintOriginKind::Internal,
                    ConstraintOriginKind::Annotation,
                    ConstraintOriginKind::ApplicationArgument,
                ],
            },
        },
        CharacterizationCase {
            name: "tuple-arity-through-generic",
            source: "my id x = x\nmy g(x: (int, int)) = x\ng (id (1, 2, 3))\n",
            mismatch: StructuralMismatch::TupleArity { lower: 3, upper: 2 },
            expected: Baseline {
                canonical_constraints: 90,
                lower_bounds: 65,
                upper_bounds: 67,
                record: ConstraintRecordId(89),
                explanation_nodes: 71,
                explanation_edges: 94,
                origins: &[
                    ConstraintOriginKind::UnknownInternal,
                    ConstraintOriginKind::Internal,
                    ConstraintOriginKind::ApplicationArgument,
                    ConstraintOriginKind::Annotation,
                    ConstraintOriginKind::ApplicationArgument,
                ],
            },
        },
        CharacterizationCase {
            name: "nested-tuple-arity",
            source: "my g(x: ((int, int), int)) = x\ng ((1, 2, 3), 4)\n",
            mismatch: StructuralMismatch::TupleArity { lower: 3, upper: 2 },
            expected: Baseline {
                canonical_constraints: 70,
                lower_bounds: 46,
                upper_bounds: 50,
                record: ConstraintRecordId(69),
                explanation_nodes: 41,
                explanation_edges: 53,
                origins: &[
                    ConstraintOriginKind::UnknownInternal,
                    ConstraintOriginKind::Internal,
                    ConstraintOriginKind::Annotation,
                    ConstraintOriginKind::ApplicationArgument,
                ],
            },
        },
        CharacterizationCase {
            name: "poly-variant-tag",
            source: "case :some 1:\n  :none -> 0\n",
            mismatch: StructuralMismatch::PolyVariant {
                lower: "none",
                upper: "some",
            },
            expected: Baseline {
                canonical_constraints: 28,
                lower_bounds: 14,
                upper_bounds: 16,
                record: ConstraintRecordId(21),
                explanation_nodes: 16,
                explanation_edges: 18,
                origins: &[ConstraintOriginKind::UnknownInternal],
            },
        },
    ];

    for case in cases {
        let output = lower(case.source);
        assert!(
            output.errors.is_empty(),
            "{}: {:?}",
            case.name,
            output.errors
        );

        // Exhaustive destructuring documents the specialize-side payload: the
        // mismatching mono types survive, but no infer record identity does.
        let SpecializeError::UnsatisfiedSubtype {
            lower,
            upper,
            origin,
        } = specialize::specialize(&output.session.poly).expect_err(case.name)
        else {
            panic!("{}: expected UnsatisfiedSubtype", case.name);
        };
        assert_eq!(origin, None, "{}", case.name);
        assert_mono_mismatch(case.name, case.mismatch, &lower, &upper);

        let machine = output.session.infer.constraints();
        let timing = machine.timing();
        assert_eq!(
            (
                timing.canonical_subtype_constraints,
                timing.lower_bounds_added,
                timing.upper_bounds_added,
                timing.nominal_cast_events,
            ),
            (
                case.expected.canonical_constraints,
                case.expected.lower_bounds,
                case.expected.upper_bounds,
                0,
            ),
            "{}",
            case.name,
        );

        // The only available correlation is an independent structural search
        // over the retained infer graph. No such key is carried by the error.
        let matching_records = machine
            .constraint_records
            .iter()
            .enumerate()
            .filter_map(|(index, record)| {
                infer_record_matches(machine, record, case.mismatch)
                    .then_some(ConstraintRecordId(index as u32))
            })
            .collect::<Vec<_>>();
        assert_eq!(matching_records, [case.expected.record], "{}", case.name);

        let explanation = machine
            .why_constraint(case.expected.record, ExplanationBudget::default())
            .expect("characterized record must remain queryable");
        let origins = explanation
            .nodes
            .iter()
            .filter_map(|node| match node {
                ExplanationNode::Origin { kind, .. } => Some(*kind),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(explanation.completeness, ExplanationCompleteness::Complete);
        assert_eq!(
            (explanation.nodes.len(), explanation.edges.len()),
            (
                case.expected.explanation_nodes,
                case.expected.explanation_edges,
            ),
            "{}",
            case.name,
        );
        assert_eq!(origins, case.expected.origins, "{}", case.name);
    }
}

/// The common record-literal failure is not part of the general `origin: None`
/// gap: the task solver already attaches its dedicated source-oriented origin.
#[test]
fn missing_record_field_remains_the_existing_covered_control() {
    let output = lower("my f {a, b} = a\nf {a: 1}\n");
    assert!(output.errors.is_empty(), "{:?}", output.errors);

    let SpecializeError::UnsatisfiedSubtype { origin, .. } =
        specialize::specialize(&output.session.poly).expect_err("missing field must fail")
    else {
        panic!("expected UnsatisfiedSubtype");
    };
    assert_eq!(
        origin,
        Some(UnsatisfiedSubtypeOrigin::MissingRecordField {
            field: "b".to_string(),
            actual_fields: vec!["a".to_string()],
            select: None,
        }),
    );
}

#[derive(Clone, Copy)]
struct CharacterizationCase {
    name: &'static str,
    source: &'static str,
    mismatch: StructuralMismatch,
    expected: Baseline,
}

#[derive(Clone, Copy)]
struct Baseline {
    canonical_constraints: usize,
    lower_bounds: usize,
    upper_bounds: usize,
    record: ConstraintRecordId,
    explanation_nodes: usize,
    explanation_edges: usize,
    origins: &'static [ConstraintOriginKind],
}

#[derive(Clone, Copy)]
enum StructuralMismatch {
    TupleArity {
        lower: usize,
        upper: usize,
    },
    PolyVariant {
        lower: &'static str,
        upper: &'static str,
    },
}

fn assert_mono_mismatch(
    name: &str,
    mismatch: StructuralMismatch,
    lower: &MonoType,
    upper: &MonoType,
) {
    match (mismatch, lower, upper) {
        (
            StructuralMismatch::TupleArity {
                lower: expected_lower,
                upper: expected_upper,
            },
            MonoType::Tuple(lower),
            MonoType::Tuple(upper),
        ) => {
            assert_eq!(lower.len(), expected_lower, "{name}");
            assert_eq!(upper.len(), expected_upper, "{name}");
        }
        (
            StructuralMismatch::PolyVariant {
                lower: expected_lower,
                upper: expected_upper,
            },
            MonoType::PolyVariant(lower),
            MonoType::PolyVariant(upper),
        ) => {
            assert_eq!(
                lower
                    .iter()
                    .map(|variant| variant.name.as_str())
                    .collect::<Vec<_>>(),
                [expected_lower],
                "{name}",
            );
            assert_eq!(
                upper
                    .iter()
                    .map(|variant| variant.name.as_str())
                    .collect::<Vec<_>>(),
                [expected_upper],
                "{name}",
            );
        }
        _ => panic!("{name}: unexpected specialize mismatch {lower:?} <: {upper:?}"),
    }
}

fn infer_record_matches(
    machine: &ConstraintMachine,
    record: &ConstraintRecord,
    mismatch: StructuralMismatch,
) -> bool {
    match (
        mismatch,
        machine.types().pos(record.key.lower),
        machine.types().neg(record.key.upper),
    ) {
        (
            StructuralMismatch::TupleArity {
                lower: expected_lower,
                upper: expected_upper,
            },
            Pos::Tuple(lower),
            Neg::Tuple(upper),
        ) => lower.len() == expected_lower && upper.len() == expected_upper,
        (
            StructuralMismatch::PolyVariant {
                lower: expected_lower,
                upper: expected_upper,
            },
            Pos::PolyVariant(lower),
            Neg::PolyVariant(upper),
        ) => {
            lower.len() == 1
                && lower[0].0 == expected_lower
                && upper.len() == 1
                && upper[0].0 == expected_upper
        }
        _ => false,
    }
}

fn lower(source: &str) -> BodyLowering {
    let loaded = sources::load(vec![sources::SourceFile {
        module_path: sources::Path::default(),
        source: source.to_string(),
    }]);
    lower_loaded_files(&loaded).expect("lower characterization source")
}
