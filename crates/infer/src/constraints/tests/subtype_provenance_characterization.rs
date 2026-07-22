use super::*;

use std::time::{Duration, Instant};

use crate::constraints::explain::{
    ExplanationBudget, ExplanationCompleteness, ExplanationNode, PortableProvenanceExportBudget,
    PortableProvenanceExportRoot,
};
use crate::lowering::{
    BodyLowering, lower_loaded_files, lower_loaded_files_prefix, lower_loaded_files_with_prefix,
};
use poly::expr::{Def, Expr, Pat};
use poly::provenance::{
    PortableBodyRequirementKind, PortableByteRange, PortableConstraintOriginKind,
    PortableProvenanceNodeKind, PortableProvenanceTruncation, PortableSourceLocation,
    ProvenanceCompleteness as PortableCompleteness,
};
use poly::types::{Neg, Pos};
use rustc_hash::FxHashSet;
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
            endpoints: EndpointCharacterization::expression_to_scheme(
                IdentityLossPoint::ConsumeExpressionValue,
                None,
            ),
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
            endpoints: EndpointCharacterization::expression_to_scheme(
                IdentityLossPoint::ConsumeExpressionValue,
                None,
            ),
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
            endpoints: EndpointCharacterization::expression_to_scheme(
                IdentityLossPoint::ConsumeExpressionValue,
                Some(StructuralLossPoint::TupleElement),
            ),
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
            endpoints: EndpointCharacterization {
                lower: Endpoint {
                    occurrence: EndpointOccurrenceKind::PatternGenerated,
                    first_identity_loss: IdentityLossPoint::BindPattern,
                },
                upper: Endpoint {
                    occurrence: EndpointOccurrenceKind::ExpressionGenerated,
                    first_identity_loss: IdentityLossPoint::CaseScrutineeToPattern,
                },
                later_structural_loss: None,
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
        assert_endpoint_owners(&output, case.name, case.endpoints);

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

/// Extends the original four-case corpus with the endpoint classes and cache/open-variable
/// controls required before a portable sidecar can be designed.
#[test]
fn subp_a_characterizes_record_open_var_and_prefix_cache_controls() {
    let record_source = "my g ({a, b}, z) = a\ng ({a: 1}, 2)\n";
    let output = lower(record_source);
    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let SpecializeError::UnsatisfiedSubtype {
        lower: lower_mono,
        upper: upper_mono,
        origin,
    } = specialize::specialize(&output.session.poly).expect_err("nested record must fail")
    else {
        panic!("expected general UnsatisfiedSubtype");
    };
    assert_eq!(origin, None);
    assert_mono_mismatch(
        "record-field-through-tuple",
        StructuralMismatch::RecordFields {
            lower: &["a"],
            upper: &["a", "b"],
        },
        &lower_mono,
        &upper_mono,
    );
    let endpoints = EndpointCharacterization::expression_to_scheme(
        IdentityLossPoint::ConsumeExpressionValue,
        Some(StructuralLossPoint::TupleElement),
    );
    assert_endpoint_owners(&output, "record-field-through-tuple", endpoints);
    assert_eq!(
        exact_matching_records(
            &output,
            StructuralMismatch::RecordFields {
                lower: &["a"],
                upper: &["a", "b"],
            }
        )
        .len(),
        1,
    );

    // The generic case is also the OpenVar control: `id` has a quantified scheme, so
    // specialize creates fresh OpenVar endpoints. Those endpoints are specialize-generated;
    // the eventual concrete tuple mismatch remains expression-to-scheme owned.
    let generic = lower("my id x = x\nmy g(x: (int, int)) = x\ng (id (1, 2, 3))\n");
    assert!(generic.errors.is_empty(), "{:?}", generic.errors);
    assert!(generic.session.poly.defs.iter().any(|(_, def)| matches!(
        def,
        Def::Let { scheme: Some(scheme), .. } if !scheme.quantifiers.is_empty()
    )));
    let open_var_endpoint = Endpoint {
        occurrence: EndpointOccurrenceKind::SpecializeGenerated,
        first_identity_loss: IdentityLossPoint::CreatedInSpecialize,
    };
    assert_eq!(
        open_var_endpoint,
        Endpoint {
            occurrence: EndpointOccurrenceKind::SpecializeGenerated,
            first_identity_loss: IdentityLossPoint::CreatedInSpecialize,
        }
    );

    const PREFIX: &str = concat!(
        "mod std:\n",
        "  pub mod control:\n",
        "    pub mod junction:\n",
        "      pub mod junction:\n",
        "        pub junction value = value\n",
        "pub g(x: (int, int)) = x\n",
    );
    let prefix = sources::load(vec![source_file(PREFIX)]);
    let cached = lower_loaded_files_prefix(&prefix).expect("compile prefix cache");
    let suffix = sources::load(vec![source_file("g (1, 2, 3)\n")]);
    let cached_call = lower_loaded_files_with_prefix(&cached, &suffix).expect("lower cached call");
    let SpecializeError::UnsatisfiedSubtype { origin, .. } =
        specialize::specialize(&cached_call.session.poly).expect_err("cached call must fail")
    else {
        panic!("expected cached UnsatisfiedSubtype");
    };
    assert_eq!(origin, None);
    assert!(
        cached_call
            .session
            .infer
            .constraints()
            .timing()
            .scheme_instantiations
            .imported_without_bridge
            > 0,
    );
    assert_eq!(
        EndpointCharacterization::expression_to_imported_scheme(),
        EndpointCharacterization {
            lower: Endpoint {
                occurrence: EndpointOccurrenceKind::ExpressionGenerated,
                first_identity_loss: IdentityLossPoint::ConsumeExpressionValue,
            },
            upper: Endpoint {
                occurrence: EndpointOccurrenceKind::SchemeGenerated,
                first_identity_loss: IdentityLossPoint::ImportedBeforeCurrentSession,
            },
            later_structural_loss: None,
        }
    );
}

#[test]
fn subp_b_portable_exports_match_local_explanation_topology() {
    let cases = [
        (
            "tuple-arity",
            "my g(x: (int, int)) = x\ng (1, 2, 3)\n",
            ConstraintRecordId(45),
        ),
        (
            "tuple-arity-through-generic",
            "my id x = x\nmy g(x: (int, int)) = x\ng (id (1, 2, 3))\n",
            ConstraintRecordId(89),
        ),
        (
            "nested-tuple-arity",
            "my g(x: ((int, int), int)) = x\ng ((1, 2, 3), 4)\n",
            ConstraintRecordId(69),
        ),
        (
            "poly-variant-tag",
            "case :some 1:\n  :none -> 0\n",
            ConstraintRecordId(21),
        ),
    ];
    for (name, source, record) in cases {
        assert_portable_export_parity(name, source, record);
    }

    let record_source = "my g ({a, b}, z) = a\ng ({a: 1}, 2)\n";
    let output = lower(record_source);
    let record_matches = exact_matching_records(
        &output,
        StructuralMismatch::RecordFields {
            lower: &["a"],
            upper: &["a", "b"],
        },
    );
    let [record] = record_matches.as_slice() else {
        panic!("record control must retain one exact canonical record");
    };
    assert_portable_export_parity("record-field-through-tuple", record_source, *record);
}

#[test]
fn subp_b_multi_root_export_deduplicates_shared_ancestry() {
    let output = lower("my id x = x\nmy g(x: (int, int)) = x\ng (id (1, 2, 3))\n");
    let machine = output.session.infer.constraints();
    let root = ConstraintRecordId(89);
    let first = machine
        .why_constraint(root, ExplanationBudget::default())
        .expect("constraint query");
    let (bound, owner, direction) = first
        .nodes
        .iter()
        .find_map(|node| match node {
            ExplanationNode::Bound {
                id,
                owner,
                direction,
                ..
            } => Some((*id, *owner, *direction)),
            _ => None,
        })
        .expect("replay explanation contains a bound");
    let second = match direction {
        BoundDirection::Lower => {
            machine.why_lower_bound(owner, bound, ExplanationBudget::default())
        }
        BoundDirection::Upper => {
            machine.why_upper_bound(owner, bound, ExplanationBudget::default())
        }
    }
    .expect("bound query");
    let expected_nodes = first
        .nodes
        .iter()
        .chain(&second.nodes)
        .map(ExplanationNode::id)
        .collect::<FxHashSet<_>>();
    let expected_edges = first
        .edges
        .iter()
        .chain(&second.edges)
        .cloned()
        .collect::<FxHashSet<_>>();
    let export = machine
        .export_portable_provenance(
            &[
                PortableProvenanceExportRoot::Constraint(root),
                PortableProvenanceExportRoot::Bound(bound),
            ],
            PortableProvenanceExportBudget::default(),
            |boundary, kind| portable_source_location(&output, boundary, kind),
        )
        .expect("multi-root export");

    assert_eq!(export.snapshot.nodes().len(), expected_nodes.len());
    assert_eq!(export.snapshot.edges().len(), expected_edges.len());
    assert_eq!(export.root_anchors.len(), 2);
    assert!(export.root_anchors.iter().all(Option::is_some));
    assert!(export.metrics.node_references_deduplicated > 0);
    assert!(export.metrics.edge_references_deduplicated > 0);
    assert!(export.metrics.shared_parent_nodes > 0);
    assert_eq!(
        export
            .snapshot
            .nodes()
            .iter()
            .map(|node| node.id)
            .collect::<FxHashSet<_>>()
            .len(),
        export.snapshot.nodes().len(),
    );
}

#[test]
fn subp_b_forced_budget_exhaustion_is_prompt_and_explicit() {
    let output = lower("my id x = x\nmy g(x: (int, int)) = x\ng (id (1, 2, 3))\n");
    let machine = output.session.infer.constraints();
    let budget = PortableProvenanceExportBudget {
        max_nodes_per_anchor: 1,
        ..PortableProvenanceExportBudget::default()
    };
    let started = Instant::now();
    let export = machine
        .export_portable_provenance(
            &[PortableProvenanceExportRoot::Constraint(
                ConstraintRecordId(89),
            )],
            budget,
            |boundary, kind| portable_source_location(&output, boundary, kind),
        )
        .expect("bounded export");

    assert!(started.elapsed() < Duration::from_millis(100));
    assert_eq!(
        export.snapshot.completeness(),
        PortableCompleteness::Incomplete
    );
    assert_eq!(
        export.snapshot.truncation(),
        Some(PortableProvenanceTruncation::NodeBudget { limit: 1 })
    );
    let anchor = export.root_anchors[0].expect("root node fits in one-node budget");
    assert_eq!(
        export.snapshot.anchor(anchor).unwrap().completeness,
        PortableCompleteness::Incomplete,
    );
    assert_eq!(export.snapshot.nodes().len(), 1);
    assert!(export.snapshot.edges().is_empty());
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
    endpoints: EndpointCharacterization,
    expected: Baseline,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EndpointOccurrenceKind {
    SchemeGenerated,
    ExpressionGenerated,
    PatternGenerated,
    SpecializeGenerated,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum IdentityLossPoint {
    /// `types/mod.rs:107` calls `SchemeMaterializer::materialize_pos`; the returned mono type
    /// retains no `DefId`, poly node ID, or generalized witness identity.
    SchemeMaterializer,
    /// `task_solver.rs:150` passes only `(actual_value, consumer)` into `TypeGraph`.
    ConsumeExpressionValue,
    /// `task_solver/control.rs:15` passes the scrutinee `Type`, but not its `ExprId`, to a pattern.
    CaseScrutineeToPattern,
    /// `task_solver/control.rs:383-389` passes the constructed variant type without its `PatId`.
    BindPattern,
    /// `type_graph.rs:27-39` allocates a fresh mono `OpenVar`; it has no infer occurrence owner.
    CreatedInSpecialize,
    /// `compiled_typed.rs:871-897` exports schemes/types without the originating session graph;
    /// suffix lowering later recognizes that imported state at `session/instantiate.rs:383-390`.
    ImportedBeforeCurrentSession,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StructuralLossPoint {
    /// `type_graph.rs:386-392` synthesizes child constraints without retaining tuple indices.
    TupleElement,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Endpoint {
    occurrence: EndpointOccurrenceKind,
    first_identity_loss: IdentityLossPoint,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct EndpointCharacterization {
    lower: Endpoint,
    upper: Endpoint,
    later_structural_loss: Option<StructuralLossPoint>,
}

impl EndpointCharacterization {
    const fn expression_to_scheme(
        lower_loss: IdentityLossPoint,
        later_structural_loss: Option<StructuralLossPoint>,
    ) -> Self {
        Self {
            lower: Endpoint {
                occurrence: EndpointOccurrenceKind::ExpressionGenerated,
                first_identity_loss: lower_loss,
            },
            upper: Endpoint {
                occurrence: EndpointOccurrenceKind::SchemeGenerated,
                first_identity_loss: IdentityLossPoint::SchemeMaterializer,
            },
            later_structural_loss,
        }
    }

    const fn expression_to_imported_scheme() -> Self {
        Self {
            lower: Endpoint {
                occurrence: EndpointOccurrenceKind::ExpressionGenerated,
                first_identity_loss: IdentityLossPoint::ConsumeExpressionValue,
            },
            upper: Endpoint {
                occurrence: EndpointOccurrenceKind::SchemeGenerated,
                first_identity_loss: IdentityLossPoint::ImportedBeforeCurrentSession,
            },
            later_structural_loss: None,
        }
    }
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
    RecordFields {
        lower: &'static [&'static str],
        upper: &'static [&'static str],
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
        (
            StructuralMismatch::RecordFields {
                lower: expected_lower,
                upper: expected_upper,
            },
            MonoType::Record(lower),
            MonoType::Record(upper),
        ) => {
            assert_eq!(
                lower
                    .iter()
                    .map(|field| field.name.as_str())
                    .collect::<Vec<_>>(),
                expected_lower,
                "{name}",
            );
            assert_eq!(
                upper
                    .iter()
                    .map(|field| field.name.as_str())
                    .collect::<Vec<_>>(),
                expected_upper,
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
        (
            StructuralMismatch::RecordFields {
                lower: expected_lower,
                upper: expected_upper,
            },
            Pos::Record(lower),
            Neg::Record(upper),
        ) => {
            lower
                .iter()
                .map(|field| field.name.as_str())
                .collect::<Vec<_>>()
                == expected_lower
                && upper
                    .iter()
                    .map(|field| field.name.as_str())
                    .collect::<Vec<_>>()
                    == expected_upper
        }
        _ => false,
    }
}

fn exact_matching_records(
    output: &BodyLowering,
    mismatch: StructuralMismatch,
) -> Vec<ConstraintRecordId> {
    let machine = output.session.infer.constraints();
    machine
        .constraint_records
        .iter()
        .enumerate()
        .filter_map(|(index, record)| {
            infer_record_matches(machine, record, mismatch)
                .then_some(ConstraintRecordId(index as u32))
        })
        .collect()
}

fn assert_endpoint_owners(output: &BodyLowering, name: &str, endpoints: EndpointCharacterization) {
    assert_eq!(
        endpoints,
        match name {
            "poly-variant-tag" => EndpointCharacterization {
                lower: Endpoint {
                    occurrence: EndpointOccurrenceKind::PatternGenerated,
                    first_identity_loss: IdentityLossPoint::BindPattern,
                },
                upper: Endpoint {
                    occurrence: EndpointOccurrenceKind::ExpressionGenerated,
                    first_identity_loss: IdentityLossPoint::CaseScrutineeToPattern,
                },
                later_structural_loss: None,
            },
            "nested-tuple-arity" | "record-field-through-tuple" => {
                EndpointCharacterization::expression_to_scheme(
                    IdentityLossPoint::ConsumeExpressionValue,
                    Some(StructuralLossPoint::TupleElement),
                )
            }
            _ => EndpointCharacterization::expression_to_scheme(
                IdentityLossPoint::ConsumeExpressionValue,
                None,
            ),
        },
    );

    if name == "poly-variant-tag" {
        let case = output
            .session
            .poly
            .root_exprs
            .iter()
            .find_map(|expr| match output.session.poly.expr(*expr) {
                Expr::Case(scrutinee, arms) => Some((*scrutinee, arms)),
                _ => None,
            })
            .expect("variant fixture has a source-owned case expression");
        assert!(matches!(
            output.session.poly.expr(case.0),
            Expr::PolyVariant(tag, _) if tag == "some"
        ));
        assert!(matches!(
            output.session.poly.pat(case.1[0].pat),
            Pat::PolyVariant(tag, _) if tag == "none"
        ));
    } else {
        assert!(
            output
                .session
                .poly
                .root_exprs
                .iter()
                .any(|expr| { matches!(output.session.poly.expr(*expr), Expr::App(_, _)) })
        );
        assert!(output.session.poly.defs.iter().any(|(_, def)| matches!(
            def,
            Def::Let {
                scheme: Some(_),
                ..
            }
        )));
    }
}

fn assert_portable_export_parity(name: &str, source: &str, record: ConstraintRecordId) {
    let output = lower(source);
    let machine = output.session.infer.constraints();
    let local = machine
        .why_constraint(record, ExplanationBudget::default())
        .expect("local explanation");
    let export = machine
        .export_portable_provenance(
            &[PortableProvenanceExportRoot::Constraint(record)],
            PortableProvenanceExportBudget::default(),
            |boundary, kind| portable_source_location(&output, boundary, kind),
        )
        .expect("portable export");
    assert_eq!(
        local.completeness,
        ExplanationCompleteness::Complete,
        "{name}"
    );
    assert_eq!(
        export.snapshot.completeness(),
        PortableCompleteness::Complete,
        "{name}"
    );
    assert_eq!(export.snapshot.nodes().len(), local.nodes.len(), "{name}");
    assert_eq!(export.snapshot.edges().len(), local.edges.len(), "{name}");
    let local_source_boundaries = local
        .source_leaves
        .iter()
        .map(|leaf| leaf.boundary)
        .collect::<FxHashSet<_>>();
    assert_eq!(
        export.snapshot.source_sites().len(),
        local_source_boundaries.len(),
        "{name}",
    );
    let local_origins = local
        .nodes
        .iter()
        .filter_map(|node| match node {
            ExplanationNode::Origin { kind, .. } => Some(portable_test_origin(*kind)),
            _ => None,
        })
        .collect::<Vec<_>>();
    let portable_origins = export
        .snapshot
        .nodes()
        .iter()
        .filter_map(|node| match node.kind {
            PortableProvenanceNodeKind::Origin { kind, .. } => Some(kind),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(portable_origins, local_origins, "{name}");
    let anchor = export.root_anchors[0].expect("one exported anchor");
    let anchor = export.snapshot.anchor(anchor).unwrap();
    assert_eq!(
        anchor.completeness,
        PortableCompleteness::Complete,
        "{name}"
    );
    assert!(matches!(
        export.snapshot.node(anchor.node).unwrap().kind,
        PortableProvenanceNodeKind::Constraint { .. }
    ));
    assert_eq!(
        export.metrics.nodes.constraints
            + export.metrics.nodes.bounds
            + export.metrics.nodes.origins
            + export.metrics.nodes.row_derivations
            + export.metrics.nodes.subtract_facts
            + export.metrics.nodes.lower_filters
            + export.metrics.nodes.bound_dispositions
            + export.metrics.nodes.generalized_witnesses,
        export.snapshot.nodes().len(),
        "{name}",
    );
    assert_eq!(
        export.metrics.logical_bytes_proxy,
        export.snapshot.logical_bytes_proxy(),
        "{name}",
    );
}

fn portable_source_location(
    output: &BodyLowering,
    boundary: SourceBoundaryId,
    kind: ConstraintOriginKind,
) -> Option<PortableSourceLocation> {
    let span = match kind {
        ConstraintOriginKind::ApplicationArgument => output
            .session
            .source_boundary_provenance
            .application_argument(boundary)
            .map(|provenance| &provenance.argument_span),
        ConstraintOriginKind::BodyRequirement(_) => output
            .session
            .source_boundary_provenance
            .body_requirement(boundary)
            .map(|provenance| &provenance.use_span),
        _ => None,
    }?;
    Some(PortableSourceLocation {
        module: span
            .file
            .segments
            .iter()
            .map(|name| name.0.clone())
            .collect(),
        range: PortableByteRange {
            start: u32::try_from(span.range.start).ok()?,
            end: u32::try_from(span.range.end).ok()?,
        },
    })
}

fn portable_test_origin(kind: ConstraintOriginKind) -> PortableConstraintOriginKind {
    match kind {
        ConstraintOriginKind::ApplicationArgument => {
            PortableConstraintOriginKind::ApplicationArgument
        }
        ConstraintOriginKind::Annotation => PortableConstraintOriginKind::Annotation,
        ConstraintOriginKind::Return => PortableConstraintOriginKind::Return,
        ConstraintOriginKind::Field => PortableConstraintOriginKind::Field,
        ConstraintOriginKind::Assignment => PortableConstraintOriginKind::Assignment,
        ConstraintOriginKind::BodyRequirement(kind) => {
            PortableConstraintOriginKind::BodyRequirement(match kind {
                BodyRequirementKind::BooleanCondition => {
                    PortableBodyRequirementKind::BooleanCondition
                }
                BodyRequirementKind::OperatorOperand { operand } => {
                    PortableBodyRequirementKind::OperatorOperand { operand: operand.0 }
                }
                BodyRequirementKind::PatternGuard => PortableBodyRequirementKind::PatternGuard,
                BodyRequirementKind::CalleeArgument { argument } => {
                    PortableBodyRequirementKind::CalleeArgument {
                        argument: argument.0,
                    }
                }
            })
        }
        ConstraintOriginKind::Internal => PortableConstraintOriginKind::Internal,
        ConstraintOriginKind::UnknownInternal => PortableConstraintOriginKind::UnknownInternal,
    }
}

fn lower(source: &str) -> BodyLowering {
    let loaded = sources::load(vec![source_file(source)]);
    lower_loaded_files(&loaded).expect("lower characterization source")
}

fn source_file(source: &str) -> sources::SourceFile {
    sources::SourceFile {
        module_path: sources::Path::default(),
        source: source.to_string(),
    }
}
