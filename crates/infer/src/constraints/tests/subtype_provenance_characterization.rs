use super::*;

use std::time::{Duration, Instant};

use crate::constraints::explain::{
    ExplanationBudget, ExplanationCompleteness, ExplanationEdge, ExplanationEdgeKind,
    ExplanationNode, ExplanationNodeId, PortableProvenanceExportBudget,
    PortableProvenanceExportRoot,
};
use crate::lowering::{
    BodyLowering, lower_loaded_files, lower_loaded_files_prefix, lower_loaded_files_with_prefix,
};
use poly::expr::{Def, Expr, Pat};
use poly::provenance::{
    PortableBodyRequirementKind, PortableByteRange, PortableConstraintOriginKind,
    PortableProvenanceEdgeKind, PortableProvenanceNodeKind, PortableProvenanceTruncation,
    PortableSourceLocation, ProvenanceCompleteness as PortableCompleteness, TypeOccurrenceKey,
    TypeOccurrenceOwner, TypeOccurrenceRole, TypePositionPath,
};
use poly::types::{Neg, Pos};
use rustc_hash::{FxHashMap, FxHashSet};
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
    // Exact-set fixtures below are authoritative: the added nodes/edges are certificate-typed
    // bound views, not a return to unfiltered raw-bound expansion.
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
                explanation_nodes: 17,
                explanation_edges: 18,
                origins: &[
                    ConstraintOriginKind::UnknownInternal,
                    ConstraintOriginKind::Pattern,
                ],
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
            ..
        } = specialize::specialize(&output.session.poly, output.subtype_provenance())
            .expect_err(case.name)
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
        ..
    } = specialize::specialize(&output.session.poly, output.subtype_provenance())
        .expect_err("nested record must fail")
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
        specialize::specialize(&cached_call.session.poly, cached_call.subtype_provenance())
            .expect_err("cached call must fail")
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
fn gwcb_0_motivating_replay_bridge_is_present_by_exact_node_and_edge_set() {
    let output = lower("my g(x: (int, int)) = x\ng (1, 2, 3)\n");
    let machine = output.session.infer.constraints();
    let local = machine
        .why_constraint(ConstraintRecordId(45), ExplanationBudget::default())
        .expect("motivating constraint explanation");
    let bridge = machine
        .proof_store
        .gwcb0_claimed_replay_bridges_for_test()
        .into_iter()
        .find(|bridge| {
            local.edges.iter().any(|edge| {
                matches!(edge.kind, ExplanationEdgeKind::Generalization(_))
                    && edge
                        .parents
                        .contains(&ExplanationNodeId::Bound(bridge.bound))
                    && local.edges.contains(&ExplanationEdge {
                        child: ExplanationNodeId::Bound(bridge.bound),
                        kind: ExplanationEdgeKind::Bound(BoundDerivation::Constraint(
                            bridge.result,
                        )),
                        parents: vec![ExplanationNodeId::Constraint(bridge.result)],
                    })
            })
        })
        .expect("the explanation retains the decisive claimed replay bridge");
    assert_eq!(bridge.coverage_root, bridge.representative_claim);
    assert_eq!(bridge.carrier.lower, bridge.lower);
    assert_eq!(bridge.carrier.upper, bridge.upper);
    let logical = machine.logical_proof_snapshot();
    let canonical_parent = logical
        .generalized
        .witnesses
        .iter()
        .flat_map(|witness| &witness.incoming)
        .flat_map(|edge| &edge.parents)
        .find(|parent| {
            matches!(
                parent,
                crate::constraints::logical_proof_snapshot::CanonicalGeneralizationParent::BoundClaimProjectionProof {
                    bound,
                    coverage_root,
                    ..
                } if *bound == bridge.bound.0 as usize
                    && *coverage_root == bridge.coverage_root.0 as usize
            )
        })
        .expect("logical snapshot retains the normalized decisive certificate");
    assert_eq!(
        canonical_parent,
        &crate::constraints::logical_proof_snapshot::CanonicalGeneralizationParent::BoundClaimProjectionProof {
            bound: bridge.bound.0 as usize,
            coverage_root: bridge.coverage_root.0 as usize,
            proof: crate::constraints::logical_proof_snapshot::CanonicalClaimedProjectionProof::ReplayConjunction {
                bound: bridge.bound.0 as usize,
                coverage_root: bridge.coverage_root.0 as usize,
                carrier: crate::constraints::logical_proof_snapshot::CanonicalCarrier::Replay {
                    result: Some(bridge.result.0 as usize),
                    pivot: bridge.carrier.pivot.0 as usize,
                    lower: bridge.lower.0 as usize,
                    upper: bridge.upper.0 as usize,
                    rule: format!("{:?}", bridge.carrier.rule),
                },
                lower_premise: bridge.lower.0 as usize,
                upper_premise: bridge.upper.0 as usize,
                attribution: crate::constraints::logical_proof_snapshot::CanonicalClaimedProjectionProofAttribution::ReplayConstraint {
                    result: bridge.result.0 as usize,
                },
            },
        },
        "logical identity must use the normalized root and exact replay carrier",
    );
    assert_eq!(
        machine.logical_proof_snapshot().generalized,
        logical.generalized,
        "canonical parent ordering and debug-hash input must be stable across reconstruction",
    );

    let expected_nodes = FxHashSet::from_iter([
        ExplanationNodeId::Bound(bridge.bound),
        ExplanationNodeId::Constraint(bridge.result),
        ExplanationNodeId::Bound(bridge.lower),
        ExplanationNodeId::Bound(bridge.upper),
    ]);
    let expected_edges = FxHashSet::from_iter([
        ExplanationEdge {
            child: ExplanationNodeId::Bound(bridge.bound),
            kind: ExplanationEdgeKind::Bound(BoundDerivation::Constraint(bridge.result)),
            parents: vec![ExplanationNodeId::Constraint(bridge.result)],
        },
        ExplanationEdge {
            child: ExplanationNodeId::Constraint(bridge.result),
            kind: ExplanationEdgeKind::BinaryReplay(bridge.carrier),
            parents: vec![
                ExplanationNodeId::Bound(bridge.lower),
                ExplanationNodeId::Bound(bridge.upper),
            ],
        },
        ExplanationEdge {
            child: ExplanationNodeId::Bound(bridge.upper),
            kind: ExplanationEdgeKind::Bound(BoundDerivation::Constraint(bridge.producer)),
            parents: vec![ExplanationNodeId::Constraint(bridge.producer)],
        },
    ]);
    let actual_nodes = local
        .nodes
        .iter()
        .map(ExplanationNode::id)
        .collect::<FxHashSet<_>>();
    let actual_edges = local.edges.iter().cloned().collect::<FxHashSet<_>>();
    let missing_nodes = expected_nodes.difference(&actual_nodes).collect::<Vec<_>>();
    let missing_edges = expected_edges.difference(&actual_edges).collect::<Vec<_>>();
    assert!(
        missing_nodes.is_empty() && missing_edges.is_empty(),
        "missing exact GWCB nodes: {missing_nodes:?}; edges: {missing_edges:?}",
    );
    let filtered_bound_edges = local
        .edges
        .iter()
        .filter(|edge| edge.child == ExplanationNodeId::Bound(bridge.bound))
        .cloned()
        .collect::<FxHashSet<_>>();
    assert_eq!(
        filtered_bound_edges,
        FxHashSet::from_iter([ExplanationEdge {
            child: ExplanationNodeId::Bound(bridge.bound),
            kind: ExplanationEdgeKind::Bound(BoundDerivation::Constraint(bridge.result)),
            parents: vec![ExplanationNodeId::Constraint(bridge.result)],
        }]),
        "the filtered mixed bound must expose only its decisive certificate",
    );
}

#[test]
fn gwcb_0_motivating_bound_keeps_filtered_and_raw_reach_distinct() {
    let output = lower("my g(x: (int, int)) = x\ng (1, 2, 3)\n");
    let machine = output.session.infer.constraints();
    let local = machine
        .why_constraint(ConstraintRecordId(45), ExplanationBudget::default())
        .expect("motivating constraint explanation");
    let bridge = machine
        .proof_store
        .gwcb0_claimed_replay_bridges_for_test()
        .into_iter()
        .find(|bridge| {
            local.edges.iter().any(|edge| {
                matches!(edge.kind, ExplanationEdgeKind::Generalization(_))
                    && edge
                        .parents
                        .contains(&ExplanationNodeId::Bound(bridge.bound))
            })
        })
        .expect("the proof store retains the claimed replay bridge");
    let proof = machine
        .generalized_scheme_records_iter()
        .flat_map(|(_, scheme)| scheme.witnesses.iter())
        .filter_map(|witness| machine.generalized_scheme_witness(*witness))
        .flat_map(|witness| witness.incoming.iter())
        .flat_map(|edge| edge.parents.iter())
        .find_map(|parent| match parent {
            GeneralizationParent::BoundClaimProjectionProof {
                bound,
                proof,
                ..
            } if *bound == bridge.bound
                && matches!(
                    proof.kind(),
                    crate::constraints::proof::ClaimedProjectionProofKind::ReplayConjunction {
                        attribution:
                            crate::constraints::proof::ClaimedProjectionProofAttribution::ReplayConstraint {
                                result,
                            },
                        ..
                    } if result == bridge.result
                ) => Some(**proof),
            _ => None,
        })
        .expect("generalization retains the exact claimed replay certificate");
    let bound = machine.bounds.record(bridge.bound).expect("bridge bound");
    assert!(
        bound
            .derivations
            .contains(&BoundDerivation::Constraint(bridge.result))
    );
    let formula = machine
        .proof_store
        .projection_formula_for_test(bridge.bound)
        .expect("claimed replay projection formula");
    let filtered_clause = crate::constraints::proof::ProjectionClause::ReplayConjunction {
        support: SchemeProjectionProofSupport::Claimed(bridge.representative_claim),
        carrier: bridge.carrier,
        lower: bridge.lower,
        upper: bridge.upper,
        attribution: Some(crate::constraints::proof::ProjectionLineage::ReplayConstraint),
    };
    assert!(formula.contains(&filtered_clause));

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    enum View {
        Raw(BoundRecordId),
        Filtered(BoundRecordId, BinaryReplayDerivation),
    }
    let expanded_views = FxHashSet::from_iter([
        View::Raw(bridge.bound),
        View::Filtered(bridge.bound, bridge.carrier),
    ]);
    let emitted_nodes = expanded_views
        .iter()
        .map(|view| match view {
            View::Raw(bound) | View::Filtered(bound, _) => ExplanationNodeId::Bound(*bound),
        })
        .collect::<FxHashSet<_>>();
    assert_eq!(
        expanded_views.len(),
        2,
        "raw and filtered reach stay distinct"
    );
    assert_eq!(
        emitted_nodes.len(),
        1,
        "both views share one graph node identity"
    );

    let raw_first = machine
        .why_bound_raw_and_claimed_views_for_test(
            bridge.bound,
            proof,
            true,
            ExplanationBudget::default(),
        )
        .expect("raw-first dual-view query");
    let filtered_first = machine
        .why_bound_raw_and_claimed_views_for_test(
            bridge.bound,
            proof,
            false,
            ExplanationBudget::default(),
        )
        .expect("filtered-first dual-view query");
    assert_eq!(raw_first.completeness, filtered_first.completeness);
    assert_eq!(raw_first.truncation, filtered_first.truncation);
    assert_eq!(
        raw_first
            .nodes
            .iter()
            .map(ExplanationNode::id)
            .collect::<FxHashSet<_>>(),
        filtered_first
            .nodes
            .iter()
            .map(ExplanationNode::id)
            .collect::<FxHashSet<_>>(),
    );
    assert_eq!(
        raw_first.edges.iter().collect::<FxHashSet<_>>(),
        filtered_first.edges.iter().collect::<FxHashSet<_>>(),
        "raw/filtered traversal order must not change the semantic edge set",
    );

    for budget in [
        ExplanationBudget {
            max_nodes: 0,
            ..ExplanationBudget::default()
        },
        ExplanationBudget {
            max_edges: 0,
            ..ExplanationBudget::default()
        },
        ExplanationBudget {
            max_depth: 0,
            ..ExplanationBudget::default()
        },
    ] {
        let raw_first = machine
            .why_bound_raw_and_claimed_views_for_test(bridge.bound, proof, true, budget)
            .expect("budgeted raw-first dual-view query");
        let filtered_first = machine
            .why_bound_raw_and_claimed_views_for_test(bridge.bound, proof, false, budget)
            .expect("budgeted filtered-first dual-view query");
        assert_eq!(raw_first.completeness, filtered_first.completeness);
        assert_eq!(raw_first.truncation, filtered_first.truncation);
    }
}

#[test]
fn gwcb_0_records_local_raw_deduplicated_and_portable_edge_baselines() {
    let output = lower("my g(x: (int, int)) = x\ng (1, 2, 3)\n");
    let machine = output.session.infer.constraints();
    let local = machine
        .why_constraint(ConstraintRecordId(45), ExplanationBudget::default())
        .expect("local explanation");
    let local_deduplicated = local.edges.iter().collect::<FxHashSet<_>>();
    let portable = machine
        .export_portable_provenance(
            &[PortableProvenanceExportRoot::Constraint(
                ConstraintRecordId(45),
            )],
            PortableProvenanceExportBudget::default(),
            |boundary, kind| portable_source_location(&output, boundary, kind),
        )
        .expect("portable explanation");

    assert_eq!(
        local.edges.len(),
        48,
        "local keeps raw edge-vector multiplicity"
    );
    assert_eq!(
        local_deduplicated.len(),
        48,
        "typed filtered parents keep the formerly-collapsed edges distinct",
    );
    assert_eq!(
        portable.snapshot.edges().len(),
        48,
        "portable export preserves the recovered deduplicated topology",
    );
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

#[test]
fn subp_d_fresh_expression_and_pattern_occurrences_resolve_portable_anchors() {
    let tuple = lower("my g(x: (int, int)) = x\ng (1, 2, 3)\n");
    let argument = tuple
        .session
        .poly
        .root_exprs
        .iter()
        .find_map(|expr| match tuple.session.poly.expr(*expr) {
            Expr::App(_, argument) => Some(*argument),
            _ => None,
        })
        .expect("tuple fixture has a source application argument");
    for role in [
        TypeOccurrenceRole::ExpressionActual,
        TypeOccurrenceRole::ExpressionExpected,
    ] {
        let provenance = tuple
            .subtype_provenance()
            .occurrences
            .get(&TypeOccurrenceKey {
                owner: TypeOccurrenceOwner::Expression(argument),
                role,
                path: TypePositionPath::default(),
            })
            .expect("fresh argument occurrence is owned");
        assert!(!provenance.anchors.is_empty(), "{role:?}: {provenance:?}");
        assert!(provenance.anchors.iter().all(|anchor| {
            tuple
                .subtype_provenance()
                .snapshot
                .anchor(*anchor)
                .is_some()
        }));
    }

    let variant = lower("case :some 1:\n  :none -> 0\n");
    let (scrutinee, pat) = variant
        .session
        .poly
        .root_exprs
        .iter()
        .find_map(|expr| match variant.session.poly.expr(*expr) {
            Expr::Case(scrutinee, arms) => Some((*scrutinee, arms[0].pat)),
            _ => None,
        })
        .expect("variant fixture has a source case");
    for (owner, role) in [
        (
            TypeOccurrenceOwner::Expression(scrutinee),
            TypeOccurrenceRole::ExpressionActual,
        ),
        (
            TypeOccurrenceOwner::Pattern(pat),
            TypeOccurrenceRole::PatternRequirement,
        ),
        (
            TypeOccurrenceOwner::Pattern(pat),
            TypeOccurrenceRole::PatternInput,
        ),
    ] {
        let provenance = variant
            .subtype_provenance()
            .occurrences
            .get(&TypeOccurrenceKey {
                owner,
                role,
                path: TypePositionPath::default(),
            })
            .expect("fresh case occurrence is owned");
        assert!(!provenance.anchors.is_empty());
    }
}

#[test]
fn subp_d_occurrence_identity_does_not_collapse_equal_expression_types() {
    let output = lower("(1, 1)\n");
    assert_eq!(
        (0..output.session.infer.constraints().types().pos_len())
            .filter(|index| matches!(
                output
                    .session
                    .infer
                    .constraints()
                    .types()
                    .pos(poly::types::PosId(*index as u32)),
                Pos::Con(path, _) if path.len() == 1 && path[0] == "int"
            ))
            .count(),
        1,
        "both literal occurrences share the one hash-consed int node",
    );
    let tuple = output
        .session
        .poly
        .root_exprs
        .iter()
        .find_map(|expr| match output.session.poly.expr(*expr) {
            Expr::Tuple(items) => Some(items.clone()),
            _ => None,
        })
        .expect("fixture has tuple expression");
    assert_eq!(tuple.len(), 2);
    let keys = tuple
        .iter()
        .map(|expr| TypeOccurrenceKey {
            owner: TypeOccurrenceOwner::Expression(*expr),
            role: TypeOccurrenceRole::ExpressionActual,
            path: TypePositionPath::default(),
        })
        .collect::<Vec<_>>();
    assert_ne!(keys[0], keys[1]);
    assert!(
        keys.iter()
            .all(|key| output.subtype_provenance().occurrences.get(key).is_some())
    );
}

/// The common record-literal failure is not part of the general `origin: None`
/// gap: the task solver already attaches its dedicated source-oriented origin.
#[test]
fn missing_record_field_remains_the_existing_covered_control() {
    let output = lower("my f {a, b} = a\nf {a: 1}\n");
    assert!(output.errors.is_empty(), "{:?}", output.errors);

    let SpecializeError::UnsatisfiedSubtype { origin, .. } =
        specialize::specialize(&output.session.poly, output.subtype_provenance())
            .expect_err("missing field must fail")
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
    // Portable snapshots export each shared derivation edge once, while local
    // queries may retain repeated references to the same exact edge.
    let local_edges = local.edges.iter().collect::<FxHashSet<_>>();
    assert_eq!(export.snapshot.edges().len(), local_edges.len(), "{name}");
    let local_node_indices = local
        .nodes
        .iter()
        .enumerate()
        .map(|(index, node)| (node.id(), index))
        .collect::<FxHashMap<_, _>>();
    assert_eq!(
        local.nodes.iter().map(local_node_tag).collect::<Vec<_>>(),
        export
            .snapshot
            .nodes()
            .iter()
            .map(|node| portable_node_tag(node.kind))
            .collect::<Vec<_>>(),
        "{name}: portable nodes must retain local node kind and order",
    );
    let local_topology = local_edges
        .iter()
        .map(|edge| PortableTopologyEdge {
            child: local_node_indices[&edge.child],
            kind: local_edge_tag(&edge.kind),
            parents: edge
                .parents
                .iter()
                .map(|parent| local_node_indices[parent])
                .collect(),
        })
        .collect::<FxHashSet<_>>();
    let portable_topology = export
        .snapshot
        .edges()
        .iter()
        .map(|edge| PortableTopologyEdge {
            child: edge.child.index(),
            kind: portable_edge_tag(edge.kind),
            parents: edge.parents.iter().map(|parent| parent.index()).collect(),
        })
        .collect::<FxHashSet<_>>();
    assert_eq!(
        local_topology.len(),
        local_edges.len(),
        "{name}: the test topology key must not collapse distinct local edges",
    );
    assert_eq!(
        portable_topology.len(),
        export.snapshot.edges().len(),
        "{name}: portable shared edges must be exported once",
    );
    assert_eq!(
        portable_topology, local_topology,
        "{name}: portable edges must equal the deduplicated local topology",
    );
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct PortableTopologyEdge {
    child: usize,
    kind: &'static str,
    parents: Vec<usize>,
}

fn local_node_tag(node: &ExplanationNode) -> &'static str {
    match node {
        ExplanationNode::Constraint { .. } => "constraint",
        ExplanationNode::Bound { .. } => "bound",
        ExplanationNode::Origin { .. } => "origin",
        ExplanationNode::RowDerivation { .. } => "row-derivation",
        ExplanationNode::SubtractFact { .. } => "subtract-fact",
        ExplanationNode::LowerFilter { .. } => "lower-filter",
        ExplanationNode::BoundDisposition { .. } => "bound-disposition",
        ExplanationNode::GeneralizedWitness { .. } => "generalized-witness",
    }
}

fn portable_node_tag(node: PortableProvenanceNodeKind) -> &'static str {
    match node {
        PortableProvenanceNodeKind::Constraint { .. } => "constraint",
        PortableProvenanceNodeKind::Bound { .. } => "bound",
        PortableProvenanceNodeKind::Origin { .. } => "origin",
        PortableProvenanceNodeKind::RowDerivation { .. } => "row-derivation",
        PortableProvenanceNodeKind::SubtractFact { .. } => "subtract-fact",
        PortableProvenanceNodeKind::LowerFilter => "lower-filter",
        PortableProvenanceNodeKind::BoundDisposition { .. } => "bound-disposition",
        PortableProvenanceNodeKind::GeneralizedWitness { .. } => "generalized-witness",
    }
}

fn local_edge_tag(kind: &ExplanationEdgeKind) -> &'static str {
    match kind {
        ExplanationEdgeKind::RootOrigin => "root-origin",
        ExplanationEdgeKind::Structural(_) => "structural",
        ExplanationEdgeKind::BinaryReplay(_) => "binary-replay",
        ExplanationEdgeKind::RowResult(_) => "row-result",
        ExplanationEdgeKind::Canonicalization(_) => "canonicalization",
        ExplanationEdgeKind::Bound(_) => "bound",
        ExplanationEdgeKind::Row(_) => "row",
        ExplanationEdgeKind::LowerFilter => "lower-filter",
        ExplanationEdgeKind::SubtractFact(_) => "subtract-fact",
        ExplanationEdgeKind::BoundDisposition(_) => "bound-disposition",
        ExplanationEdgeKind::Generalization(_) => "generalization",
        ExplanationEdgeKind::SchemeInstantiation(_) => "scheme-instantiation",
    }
}

fn portable_edge_tag(kind: PortableProvenanceEdgeKind) -> &'static str {
    match kind {
        PortableProvenanceEdgeKind::RootOrigin => "root-origin",
        PortableProvenanceEdgeKind::Structural(_) => "structural",
        PortableProvenanceEdgeKind::BinaryReplay => "binary-replay",
        PortableProvenanceEdgeKind::RowResult => "row-result",
        PortableProvenanceEdgeKind::Canonicalization => "canonicalization",
        PortableProvenanceEdgeKind::Bound(_) => "bound",
        PortableProvenanceEdgeKind::Row(_) => "row",
        PortableProvenanceEdgeKind::LowerFilter => "lower-filter",
        PortableProvenanceEdgeKind::SubtractFact(_) => "subtract-fact",
        PortableProvenanceEdgeKind::BoundDisposition(_) => "bound-disposition",
        PortableProvenanceEdgeKind::Generalization(_) => "generalization",
        PortableProvenanceEdgeKind::SchemeInstantiation => "scheme-instantiation",
    }
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
        ConstraintOriginKind::Pattern => PortableConstraintOriginKind::Pattern,
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
