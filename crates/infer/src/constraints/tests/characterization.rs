use super::*;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path as FsPath, PathBuf};

use crate::constraints::explain::{
    ExplanationBudget, ExplanationCompleteness, ExplanationEdgeKind, ExplanationNode,
    ExplanationNodeId, ExplanationTruncationReason,
};
use crate::constraints::ocast_eligibility::OcastEligibilityOutcome;
use crate::constraints::timing::{
    begin_nominal_cast_pair_capture, finish_nominal_cast_pair_capture,
};
use crate::lowering::{BodyLowering, lower_loaded_files};

#[test]
fn cprov_a_characterizes_constraints_replay_std_and_regressions() {
    let cases = [
        CharacterizationCase::std_only(),
        CharacterizationCase::fixture(
            "effect-callback-residual",
            "tests/yulang/regressions/effect/for_callback_residual_with_println.yu",
        ),
        CharacterizationCase::fixture(
            "ref-update-local-buffer",
            "tests/yulang/regressions/runtime/ref_update_local_buffer_public.yu",
        ),
        CharacterizationCase::fixture(
            "config-read-false-positive-repro",
            "examples/config-file-text/config_read.yu",
        ),
        CharacterizationCase::fixture(
            "file-rollback-false-positive-repro",
            "tests/yulang/regressions/runtime/file_mock_text_with_rollback_on_error.yu",
        ),
    ];

    let mut actual = Vec::new();
    for case in cases {
        begin_nominal_cast_pair_capture();
        let output = case.lower();
        let nominal_pairs = finish_nominal_cast_pair_capture();
        assert!(
            output.errors.is_empty(),
            "{} lowering errors: {:?}",
            case.name,
            output.errors
        );
        let nominal_events = output.session.infer.constraint_timing().nominal_cast_events;
        let ocast = output.session.ocast_eligibility_metrics();
        assert_eq!(
            ocast.classified, nominal_events,
            "{}: every routed nominal event remains visible at quiescence",
            case.name,
        );
        assert_eq!(
            ocast.classified,
            ocast.eligible_source_boundary + ocast.internal_only + ocast.incomplete,
            "{}: shadow classifications partition the pending producers",
            case.name,
        );
        if matches!(
            case.name,
            "config-read-false-positive-repro" | "file-rollback-false-positive-repro"
        ) {
            assert_eq!(ocast.incomplete, 0);
            assert_eq!(ocast.eligible_source_boundary, 0);
            assert_eq!(ocast.internal_only, nominal_events);
            assert!(output.session.ocast_eligibility_shadow().iter().all(
                |classification| matches!(
                    classification.outcome,
                    OcastEligibilityOutcome::InternalOnly { .. }
                )
            ));
        }
        actual.push(ConstraintCharacterization::capture(
            case.name,
            &output,
            nominal_pairs,
        ));
    }

    assert_eq!(actual, expected_characterization());
}

#[test]
fn cprov_h_real_std_budget_truncates_without_solver_side_effects() {
    let output = CharacterizationCase::std_only().lower();
    assert!(output.errors.is_empty());
    let machine = output.session.infer.constraints();
    let record = machine
        .constraint_records
        .iter()
        .position(|record| !record.replay_derivations.is_empty())
        .map(|index| ConstraintRecordId(index as u32))
        .expect("repository std has replay-derived constraints");
    let semantic_epoch = machine.epoch();
    let provenance_epoch = machine.provenance_epoch();
    let semantic_count = machine.canonical_constraint_count();

    let node_limited = machine
        .why_constraint(
            record,
            ExplanationBudget {
                max_nodes: 0,
                max_edges: 4,
                max_depth: 4,
            },
        )
        .unwrap();
    assert_eq!(
        node_limited.completeness,
        ExplanationCompleteness::TruncatedByBudget
    );
    assert_eq!(
        node_limited.truncation,
        Some(ExplanationTruncationReason::NodeBudget { limit: 0 })
    );
    assert!(node_limited.nodes.is_empty());
    assert!(node_limited.edges.is_empty());

    let edge_limited = machine
        .why_constraint(
            record,
            ExplanationBudget {
                max_nodes: 4,
                max_edges: 0,
                max_depth: 4,
            },
        )
        .unwrap();
    assert_eq!(
        edge_limited.completeness,
        ExplanationCompleteness::TruncatedByBudget
    );
    assert_eq!(
        edge_limited.truncation,
        Some(ExplanationTruncationReason::EdgeBudget { limit: 0 })
    );
    assert_eq!(edge_limited.nodes.len(), 1);
    assert!(edge_limited.edges.is_empty());

    let depth_limited = machine
        .why_constraint(
            record,
            ExplanationBudget {
                max_nodes: 4,
                max_edges: 4,
                max_depth: 0,
            },
        )
        .unwrap();
    assert_eq!(
        depth_limited.completeness,
        ExplanationCompleteness::TruncatedByBudget
    );
    assert_eq!(
        depth_limited.truncation,
        Some(ExplanationTruncationReason::DepthBudget { limit: 0 })
    );
    assert_eq!(depth_limited.nodes.len(), 1);
    assert!(depth_limited.edges.is_empty());

    assert_eq!(machine.epoch(), semantic_epoch);
    assert_eq!(machine.provenance_epoch(), provenance_epoch);
    assert_eq!(machine.canonical_constraint_count(), semantic_count);
}

#[test]
fn sound_a_unknown_origins_are_tied_to_exact_lowering_roots() {
    let function = lower_source("my f(): bool = 42\nf()\n");
    assert!(unknown_root_shapes_for_incomplete_events(&function).is_empty());
    let [classification] = function.session.ocast_eligibility_shadow() else {
        panic!("plain function has one nominal producer")
    };
    assert!(matches!(
        classification.outcome,
        OcastEligibilityOutcome::EligibleSourceBoundary {
            kind: ConstraintOriginKind::Return,
            ..
        }
    ));

    let field = lower_source("struct S { x: bool }\nS { x: 42 }\n");
    assert!(
        unknown_root_shapes_for_incomplete_events(&field).is_empty(),
        "the five audited constructor/record roots are complete internal ancestry"
    );
    assert_eq!(
        count_direct_unknown_roots(&field, |lower, upper| matches!(
            (lower, upper),
            (Pos::Var(_), Neg::Con(path, args))
                if path == &["bool".to_string()] && args.is_empty()
        )),
        0,
        "the declared field-signature root is no longer origin-incomplete",
    );
    assert_eq!(
        count_direct_roots(
            &field,
            ConstraintOriginKind::Internal,
            |lower, upper| matches!(
                (lower, upper),
                (Pos::Var(_), Neg::Con(path, args))
                    if path == &["bool".to_string()] && args.is_empty()
            ),
        ),
        1,
        "connect_constructor_arg_signatures retains the unique field-value <: bool root as \
         internal ancestry, not a new source boundary",
    );

    let receiver = lower_source(concat!(
        "struct target { value: int }\n",
        "role Read 'subject:\n",
        "  type value\n",
        "  our x.read: value\n",
        "impl int: Read:\n",
        "  type value = target\n",
        "  our x.read: target = 1\n",
    ));
    assert_eq!(
        unknown_root_shapes_for_incomplete_events(&receiver),
        vec![UnknownRootShape::IntLiteralUpper],
    );

    for (source, expected) in [
        (
            "struct actual;\nstruct expected;\nmy f(): expected = actual\nf()\n",
            vec![],
        ),
        (
            concat!(
                "struct actual;\n",
                "struct expected;\n",
                "struct holder { value: expected }\n",
                "holder { value: actual }\n",
            ),
            vec![],
        ),
        (
            concat!(
                "struct actual;\n",
                "struct expected;\n",
                "struct box 'a { value: 'a }\n",
                "my f(): box expected = box { value: actual }\n",
                "f()\n",
            ),
            vec![
                UnknownRootShape::SchemeRecursiveBoundsCloneLower,
                UnknownRootShape::SchemeRecursiveBoundsCloneLower,
            ],
        ),
        (
            concat!(
                "struct marker;\n",
                "struct actual 'a;\n",
                "struct expected 'a;\n",
                "struct holder { value: expected marker }\n",
                "holder { value: actual }\n",
            ),
            vec![],
        ),
    ] {
        assert_eq!(
            unknown_root_shapes_for_incomplete_events(&lower_source(source)),
            expected,
        );
    }
}

#[test]
fn sound_b1e_companion_method_result_has_return_owned_value_root() {
    let expected_value_upper = |lower: &Pos, upper: &Neg| {
        matches!(
            (lower, upper),
            (Pos::Var(_), Neg::Con(path, args))
                if path == &["bool".to_string()] && args.is_empty()
        )
    };
    let function = lower_source("my f(): bool = 42\nf()\n");
    assert_eq!(
        count_direct_roots(
            &function,
            ConstraintOriginKind::Return,
            expected_value_upper,
        ),
        1,
        "the plain function has a concrete result-annotation root",
    );

    let forms = [
        ("value", "our x.m: bool = 42", "(s { v: 1 }).m"),
        ("parameterised", "our x.m(): bool = 42", "(s { v: 1 }).m()"),
    ];
    for (name, method, call) in forms {
        let output = lower_source(&format!(
            "struct s {{ v: int }} with:\n  {method}\n\n{call}\n"
        ));
        assert!(
            matches!(
                output.errors.as_slice(),
                [crate::lowering::BodyLoweringError::Analysis(
                    crate::analysis::AnalysisDiagnostic::MissingImplicitCast {
                        source,
                        target,
                        ..
                    }
                )] if source == &["int".to_string()] && target == &["bool".to_string()]
            ),
            "{name}: {:?}",
            output.errors,
        );
        let [incomplete, eligible] = output.session.ocast_eligibility_shadow() else {
            panic!("{name}: one incomplete and one eligible producer exist")
        };
        assert!(matches!(
            incomplete.outcome,
            OcastEligibilityOutcome::Incomplete {
                reason: crate::constraints::ocast_eligibility::OcastIncompleteReason::UnknownOrigin(
                    origin,
                ),
            } if origin == OriginId::unknown_internal()
        ));
        assert!(matches!(
            eligible.outcome,
            OcastEligibilityOutcome::EligibleSourceBoundary {
                kind: ConstraintOriginKind::Return,
                ..
            }
        ));
        assert_eq!(
            count_direct_roots(&output, ConstraintOriginKind::Return, expected_value_upper,),
            1,
            "{name}: companion result lowering creates a Return-owned value root",
        );
        assert_eq!(
            unknown_root_shapes_for_incomplete_events(&output),
            vec![UnknownRootShape::IntLiteralUpper],
            "{name}: the alternate incomplete producer has the literal-upper root",
        );
    }
}

#[test]
fn sound_a_full_ref_effect_false_positives_are_absent() {
    let cases = [
        ("config-read", "examples/config-file-text/config_read.yu"),
        ("ref-replay", "examples/02_refs.yu"),
        (
            "file-rollback",
            "tests/yulang/regressions/runtime/file_mock_text_with_rollback_on_error.yu",
        ),
    ];

    for (name, path) in cases {
        let output = CharacterizationCase::fixture(name, path).lower();
        assert!(output.errors.is_empty(), "{name}: {:?}", output.errors);
        let shadow = output.session.ocast_eligibility_shadow();
        assert_eq!(
            shadow.len(),
            1,
            "{name}: only repository std's int -> float control should remain"
        );
        assert!(shadow.iter().all(|classification| matches!(
            classification.outcome,
            OcastEligibilityOutcome::InternalOnly { .. }
        )));
        let metrics = output.session.ocast_eligibility_metrics();
        assert_eq!(metrics.internal_only, shadow.len());
        assert_eq!(metrics.eligible_source_boundary, 0);
        assert_eq!(metrics.incomplete, 0);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UnknownRootShape {
    // lower_defined_lambda_params_with_anchors: body.value -> skeleton.body_value.
    DefinedLambdaBodyToSkeleton,
    // constrain_constructor_arg_shapes: record lower -> constructor argument value.
    ConstructorArgRecordLowerShape,
    // lower_constructor_def: constructed function type -> registered definition root.
    ConstructorDefinitionToRoot,
    // lower_constructor_def: nullary constructed value -> registered definition root.
    ConstructorValueToRoot,
    // constrain_constructor_arg_shapes: constructor argument value -> record upper.
    ConstructorArgRecordUpperShape,
    // int_value via constrain_upper: literal value -> int.
    IntLiteralUpper,
    // instantiate::clone_recursive_bounds: cloned invariant lower -> target variable upper.
    SchemeRecursiveBoundsCloneLower,
}

fn unknown_root_shapes_for_incomplete_events(output: &BodyLowering) -> Vec<UnknownRootShape> {
    let machine = output.session.infer.constraints();
    output
        .session
        .ocast_eligibility_shadow()
        .iter()
        .filter(|classification| {
            matches!(
                classification.outcome,
                OcastEligibilityOutcome::Incomplete {
                    reason: crate::constraints::ocast_eligibility::OcastIncompleteReason::UnknownOrigin(
                        origin,
                    ),
                } if origin == OriginId::unknown_internal()
            )
        })
        .flat_map(|classification| {
            let query = machine
                .why_constraint(classification.producer, ExplanationBudget::ocast_classifier())
                .expect("query nominal producer");
            query
                .edges
                .iter()
                .filter_map(|edge| {
                    if edge.kind != ExplanationEdgeKind::RootOrigin
                        || edge.parents != [ExplanationNodeId::Origin(OriginId::unknown_internal())]
                    {
                        return None;
                    }
                    let ExplanationNodeId::Constraint(record) = edge.child else {
                        return None;
                    };
                    let key = query.nodes.iter().find_map(|node| match node {
                        ExplanationNode::Constraint { id, key, .. } if *id == record => Some(key),
                        _ => None,
                    })?;
                    Some(match (machine.types().pos(key.lower), machine.types().neg(key.upper)) {
                        (Pos::Var(_), Neg::Var(_)) => {
                            UnknownRootShape::DefinedLambdaBodyToSkeleton
                        }
                        (Pos::Record(_), Neg::Var(_)) => {
                            UnknownRootShape::ConstructorArgRecordLowerShape
                        }
                        (Pos::Fun { .. }, Neg::Var(_)) => {
                            UnknownRootShape::ConstructorDefinitionToRoot
                        }
                        (Pos::Con(_, _), Neg::Var(_)) => {
                            UnknownRootShape::ConstructorValueToRoot
                        }
                        (Pos::Var(_), Neg::Record(_)) => {
                            UnknownRootShape::ConstructorArgRecordUpperShape
                        }
                        (Pos::Var(_), Neg::Con(path, args))
                            if path == &["int".to_string()] && args.is_empty() =>
                        {
                            UnknownRootShape::IntLiteralUpper
                        }
                        (Pos::Union(_, _), Neg::Con(_, _)) => {
                            UnknownRootShape::SchemeRecursiveBoundsCloneLower
                        }
                        (lower, upper) => {
                            panic!("unidentified SOUND-A root: {lower:?} <: {upper:?}")
                        }
                    })
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

fn count_direct_unknown_roots(
    output: &BodyLowering,
    predicate: impl FnMut(&Pos, &Neg) -> bool,
) -> usize {
    count_direct_roots(output, ConstraintOriginKind::UnknownInternal, predicate)
}

fn count_direct_roots(
    output: &BodyLowering,
    origin_kind: ConstraintOriginKind,
    mut predicate: impl FnMut(&Pos, &Neg) -> bool,
) -> usize {
    let machine = output.session.infer.constraints();
    machine
        .constraint_records
        .iter()
        .enumerate()
        .filter(|(index, record)| {
            let query = machine
                .why_constraint(
                    ConstraintRecordId(*index as u32),
                    ExplanationBudget::default(),
                )
                .expect("query existing constraint");
            query.edges.iter().any(|edge| {
                let [ExplanationNodeId::Origin(origin)] = edge.parents.as_slice() else {
                    return false;
                };
                edge.child == ExplanationNodeId::Constraint(ConstraintRecordId(*index as u32))
                    && edge.kind == ExplanationEdgeKind::RootOrigin
                    && query.nodes.iter().any(|node| {
                        matches!(
                            node,
                            ExplanationNode::Origin { id, kind, .. }
                                if id == origin && *kind == origin_kind
                        )
                    })
            }) && predicate(
                machine.types().pos(record.key.lower),
                machine.types().neg(record.key.upper),
            )
        })
        .count()
}

fn lower_source(source: &str) -> BodyLowering {
    let root = rowan::SyntaxNode::new_root(parser::parse_module_to_green(source));
    let lower = crate::lower_module_map(&root);
    crate::lowering::lower_binding_bodies(&root, lower)
}

#[derive(Clone, Copy)]
struct CharacterizationCase {
    name: &'static str,
    relative_path: Option<&'static str>,
}

impl CharacterizationCase {
    fn std_only() -> Self {
        Self {
            name: "repository-std-only",
            relative_path: None,
        }
    }

    fn fixture(name: &'static str, relative_path: &'static str) -> Self {
        Self {
            name,
            relative_path: Some(relative_path),
        }
    }

    fn lower(self) -> BodyLowering {
        let mut root_source = String::from("use std::prelude::*\nmod std;\n");
        if let Some(relative_path) = self.relative_path {
            root_source.push_str(
                &fs::read_to_string(repository_root().join(relative_path))
                    .unwrap_or_else(|error| panic!("read {relative_path}: {error}")),
            );
        }
        let loaded = repository_std_loaded(&root_source);
        lower_loaded_files(&loaded)
            .unwrap_or_else(|error| panic!("lower CPROV-A case {}: {error:?}", self.name))
    }
}

#[derive(Debug, PartialEq, Eq)]
struct ConstraintCharacterization {
    name: &'static str,
    origin_coverage: ConstraintOriginCoverage,
    body_requirement_coverage: BodyRequirementOriginCoverage,
    structural_coverage: StructuralDerivationCoverage,
    row_coverage: RowDerivationCoverage,
    bound_disposition_coverage: BoundDispositionCoverage,
    stable_record_coverage: StableRecordCoverage,
    replay_derivation_coverage: ReplayDerivationCoverage,
    provenance_epoch: u64,
    canonical_subtype_constraints: usize,
    subtype_duplicate_admissions: usize,
    subtype_trivial_admissions: usize,
    ordinary_lower_bounds_added: usize,
    ordinary_upper_bounds_added: usize,
    row_upper_bounds_added_without_replay: usize,
    evidence_lower_bounds_added: usize,
    evidence_upper_bounds_added: usize,
    subtract_fact_calls: usize,
    subtract_facts_added: usize,
    row_residuals_created: usize,
    row_residuals_reused: usize,
    lower_replay: ReplayCharacterization,
    upper_replay: ReplayCharacterization,
    nominal_cast_events: usize,
    nominal_cast_pairs: Vec<(String, String, usize)>,
    poly_dump_fnv1a64: u64,
    check_report_fnv1a64: u64,
}

impl ConstraintCharacterization {
    fn capture(
        name: &'static str,
        output: &BodyLowering,
        nominal_pairs: Vec<(Vec<String>, Vec<String>)>,
    ) -> Self {
        let timing = output.timing.constraint;
        assert_cprov_f_replay_witnesses(name, output);
        let nominal_cast_pairs = aggregate_nominal_pairs(nominal_pairs);
        assert_eq!(
            nominal_cast_pairs
                .iter()
                .map(|(_, _, count)| count)
                .sum::<usize>(),
            timing.nominal_cast_events,
            "{name}: pair capture and event counter diverged"
        );
        let poly_dump = poly::dump::dump_arena_with_labels(&output.session.poly, &output.labels);
        let check_report = format!("{:?}", crate::check::summarize_lowering(output));
        assert_eq!(
            timing.structural_derivations.unknown_rule, 0,
            "{name}: structural decomposition escaped the typed rule taxonomy"
        );
        let considered_binary_replay_derivations = timing.lower_replay_accepted
            + timing.upper_replay_accepted
            + timing.lower_replay_duplicate
            + timing.upper_replay_duplicate;
        let stored_binary_replay_derivations = considered_binary_replay_derivations
            .checked_sub(timing.replay_derivations.deduplicated)
            .expect("deduplicated replay derivations are a subset of considered derivations");
        let expected_replay_bytes_proxy = stored_binary_replay_derivations
            * std::mem::size_of::<BinaryReplayDerivation>()
            + (timing.lower_replay_trivial + timing.upper_replay_trivial)
                * (std::mem::size_of::<ReplayDropRecord>() * 2
                    + std::mem::size_of::<ReplayDropRecordId>());
        assert_eq!(
            timing.replay_derivation_storage.bytes_proxy, expected_replay_bytes_proxy,
            "{name}: replay storage proxy"
        );
        assert!(!timing.replay_derivation_storage.session_incomplete);
        assert_eq!(timing.replay_derivation_storage.incomplete_records, 0);
        assert_eq!(timing.replay_derivations.budget_dropped, 0);
        Self {
            name,
            origin_coverage: timing.root_origins,
            body_requirement_coverage: timing.body_requirement_origins,
            structural_coverage: timing.structural_derivations,
            row_coverage: timing.row_derivations,
            bound_disposition_coverage: timing.bound_dispositions,
            stable_record_coverage: timing.stable_records,
            replay_derivation_coverage: timing.replay_derivations,
            provenance_epoch: timing.provenance_epoch,
            canonical_subtype_constraints: timing.canonical_subtype_constraints,
            subtype_duplicate_admissions: timing.subtype_duplicate_admissions,
            subtype_trivial_admissions: timing.subtype_trivial_admissions,
            ordinary_lower_bounds_added: timing.lower_bounds_added,
            ordinary_upper_bounds_added: timing.upper_bounds_added,
            row_upper_bounds_added_without_replay: timing.row_upper_bounds_added_without_replay,
            evidence_lower_bounds_added: timing.evidence_lower_bounds_added,
            evidence_upper_bounds_added: timing.evidence_upper_bounds_added,
            subtract_fact_calls: timing.subtract_fact_calls,
            subtract_facts_added: timing.subtract_facts_added,
            row_residuals_created: timing.row_residuals_created,
            row_residuals_reused: timing.row_residuals_reused,
            lower_replay: ReplayCharacterization::lower(timing),
            upper_replay: ReplayCharacterization::upper(timing),
            nominal_cast_events: timing.nominal_cast_events,
            nominal_cast_pairs,
            poly_dump_fnv1a64: fnv1a64(poly_dump.as_bytes()),
            check_report_fnv1a64: fnv1a64(check_report.as_bytes()),
        }
    }
}

fn assert_cprov_f_replay_witnesses(name: &str, output: &BodyLowering) {
    if name == "effect-callback-residual" {
        let witness = output
            .session
            .infer
            .constraints()
            .debug_first_shared_source_replay_witness()
            .expect("existing fixture has a coherent replay chain");
        assert!(
            witness
                .lower
                .source_origins
                .iter()
                .any(|origin| witness.upper.source_origins.contains(origin))
        );
        return;
    }
    let Some((source, target, expected_count)) = (match name {
        "config-read-false-positive-repro" => Some(("&blanks#3:3", "&comments#3:2", 0usize)),
        "file-rollback-false-positive-repro" => Some(("&buffer#5:0", "&store#6:0", 0)),
        _ => None,
    }) else {
        return;
    };
    let witnesses = output
        .session
        .infer
        .constraints()
        .debug_nominal_replay_witnesses(&[source.to_string()], &[target.to_string()]);
    assert_eq!(witnesses.len(), expected_count, "{name}: replay witnesses");
    for witness in witnesses {
        assert_eq!(witness.lower.bound, witness.edge.derivation.lower);
        assert_eq!(witness.upper.bound, witness.edge.derivation.upper);
        assert_eq!(witness.lower.owner, witness.edge.derivation.pivot);
        assert_eq!(witness.upper.owner, witness.edge.derivation.pivot);
        assert!(matches!(witness.lower.endpoint, BoundEndpoint::Lower(_)));
        assert!(matches!(witness.upper.endpoint, BoundEndpoint::Upper(_)));
        assert_ne!(witness.lower.bound, witness.upper.bound);
        assert_ne!(witness.lower.derivations, witness.upper.derivations);
        assert!(!witness.lower.origins.is_empty());
        assert!(!witness.upper.origins.is_empty());
        assert!(
            witness.lower.origins.contains(&OriginId::internal())
                && witness.upper.origins.contains(&OriginId::internal()),
            "{name}: synthetic ref/state parents retain Internal roots: lower={:?} upper={:?}",
            witness.lower.origins,
            witness.upper.origins,
        );
        // Source-origin coverage is intentionally partial in CPROV-C. When present, retain it in
        // the query result; exact stable bound parents remain available even for unknown roots.
        assert!(
            witness.lower.source_origins.len() <= witness.lower.origins.len()
                && witness.upper.source_origins.len() <= witness.upper.origins.len()
        );
    }
}

#[derive(Debug, PartialEq, Eq)]
struct ReplayCharacterization {
    inputs: usize,
    generated: usize,
    accepted: usize,
    evidence_only: usize,
    duplicate: usize,
    trivial: usize,
    prefiltered: usize,
}

impl ReplayCharacterization {
    fn lower(timing: ConstraintTiming) -> Self {
        // The existing `*_replay_enqueued` field is populated from
        // `BoundReplayPlan::generated`, before accepted/duplicate disposition.
        Self {
            inputs: timing.lower_replay_inputs,
            generated: timing.lower_replay_enqueued,
            accepted: timing.lower_replay_accepted,
            evidence_only: timing.lower_replay_evidence_only,
            duplicate: timing.lower_replay_duplicate,
            trivial: timing.lower_replay_trivial,
            prefiltered: timing.lower_replay_prefiltered,
        }
    }

    fn upper(timing: ConstraintTiming) -> Self {
        Self {
            inputs: timing.upper_replay_inputs,
            generated: timing.upper_replay_enqueued,
            accepted: timing.upper_replay_accepted,
            evidence_only: timing.upper_replay_evidence_only,
            duplicate: timing.upper_replay_duplicate,
            trivial: timing.upper_replay_trivial,
            prefiltered: timing.upper_replay_prefiltered,
        }
    }
}

fn aggregate_nominal_pairs(pairs: Vec<(Vec<String>, Vec<String>)>) -> Vec<(String, String, usize)> {
    let mut counts = BTreeMap::new();
    for (source, target) in pairs {
        *counts
            .entry((source.join("::"), target.join("::")))
            .or_insert(0usize) += 1;
    }
    counts
        .into_iter()
        .map(|((source, target), count)| (source, target, count))
        .collect()
}

fn fnv1a64(bytes: &[u8]) -> u64 {
    const OFFSET: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x100000001b3;
    bytes.iter().fold(OFFSET, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(PRIME)
    })
}

fn replay_derivations(
    considered: usize,
    deduplicated: usize,
    semantic_duplicate_results: usize,
) -> ReplayDerivationCoverage {
    ReplayDerivationCoverage {
        considered,
        inserted: considered
            .checked_sub(deduplicated)
            .expect("deduplicated replay derivations are a subset of considered derivations"),
        deduplicated,
        budget_dropped: 0,
        semantic_duplicate_results,
    }
}

fn row_coverage(
    residual_created: usize,
    unweighted_multi_parent: usize,
    row_item_match: usize,
    filter_invariant: usize,
    payload_invariant: usize,
    subtract_fact_transformation: usize,
    edges_inserted: usize,
    edges_deduplicated: usize,
    unexplained_propagation_paths: usize,
) -> RowDerivationCoverage {
    RowDerivationCoverage {
        residual_created,
        residual_reused: 0,
        unweighted_multi_parent,
        row_item_match,
        filter_invariant,
        payload_invariant,
        subtract_fact_transformation,
        store_without_replay: 0,
        edges_inserted,
        edges_deduplicated,
        unexplained_propagation_paths,
    }
}

fn bound_dispositions(
    inserted: usize,
    equivalent: usize,
    subsumed: usize,
    tombstones: usize,
) -> BoundDispositionCoverage {
    BoundDispositionCoverage {
        inserted,
        equivalent,
        subsumed,
        trivial: 0,
        tombstones,
    }
}

fn expected_characterization() -> Vec<ConstraintCharacterization> {
    // Five std companion methods now connect real result-value obligations: ref.update,
    // str.lines, listener.accept, listener.port, and request.respond. Their bidirectional value
    // connections add 10 Return roots; the bound, replay, and epoch deltas below derive from them.
    // Plain defined functions with declared results now label the audited body-value ->
    // skeleton-value root and both skeleton-layer value directions as Internal. That moves only
    // UnknownInternal/Internal origin coverage; the three relabel sites account for the uniform
    // provenance epoch +2/+1/+1 below.
    // The five audited nominal-field constructor/record sites likewise move only the root-origin
    // census from UnknownInternal to Internal. Poly/check hashes, structural and row coverage,
    // constraint totals, replay totals, and nominal-event counts remain pinned below.
    // std.testing adds two annotated operation results and their assertion wrappers. The uniform
    // deltas below are the resulting repository-std census; fixture-specific structure stays
    // unchanged.
    // STF-D0a resolves the two `str_error` method annotations through the explicit `(int, int)`
    // associated assignment instead of a nominal `pos` declaration. Across positive and negative
    // annotation bounds this adds eight tuple derivations, four lower bounds, and their replay
    // records uniformly to every std-backed case. Check diagnostics remain unchanged.
    // STF-D0b stops applying local function result annotations to the whole curried function value.
    // The uniform decreases below remove those duplicate annotation roots and their derived bounds;
    // check diagnostics remain unchanged while the poly dumps retain the corrected local schemes.
    // URR-B keeps initially matched unweighted row reductions live for later lowers. Repository std
    // has 27 incremental routes: 13 matched (11 accepted, 2 prefiltered duplicate) and 14 unmatched
    // (10 accepted, 4 prefiltered trivial). They replace reduction-owned generic replay routes and
    // are counted explicitly here; the earlier 493_009 trial total omitted those 27 audit inputs.
    // URR v3-v5 makes claim coverage the live generic-replay decision. The census below records the
    // resulting replay suppression and real derivation deduplication; poly/check hashes stay pinned
    // to the pre-live-wiring values because final type-checking results are unchanged.
    vec![
        ConstraintCharacterization {
            name: "repository-std-only",
            origin_coverage: origins(1_855, 416, 1_468, 803, 294, 10_843, 22_755),
            body_requirement_coverage: body_requirements(98),
            structural_coverage: structural(
                31_730, 330, 14_534, 13_612, 2_438, 484, 196, 0, 136, 64,
            ),
            row_coverage: row_coverage(70, 77, 136, 337, 43, 43, 638, 85, 0),
            bound_disposition_coverage: bound_dispositions(231_701, 35, 1_875, 0),
            stable_record_coverage: stable_records(113_489, 118_212, 35, 14, 107),
            replay_derivation_coverage: replay_derivations(880_958, 0, 768_515),
            provenance_epoch: 3_439_479,
            canonical_subtype_constraints: 143_163,
            subtype_duplicate_admissions: 13_146,
            subtype_trivial_admissions: 12_133,
            ordinary_lower_bounds_added: 113_489,
            ordinary_upper_bounds_added: 118_149,
            row_upper_bounds_added_without_replay: 63,
            evidence_lower_bounds_added: 0,
            evidence_upper_bounds_added: 0,
            subtract_fact_calls: 107,
            subtract_facts_added: 107,
            row_residuals_created: 70,
            row_residuals_reused: 0,
            lower_replay: replay(493_036, 493_036, 27_938, 0, 457_371, 7_727, 465_060),
            upper_replay: replay(387_922, 387_922, 69_060, 0, 311_144, 7_718, 318_824),
            nominal_cast_events: 1,
            nominal_cast_pairs: vec![pair("int", "float", 1)],
            poly_dump_fnv1a64: 8_557_020_867_750_974_498,
            check_report_fnv1a64: 5_811_326_162_228_699_395,
        },
        ConstraintCharacterization {
            name: "effect-callback-residual",
            origin_coverage: origins(1_858, 416, 1_468, 803, 297, 10_893, 22_822),
            body_requirement_coverage: body_requirements(99),
            structural_coverage: structural(
                31_795, 331, 14_542, 13_656, 2_438, 484, 196, 0, 148, 74,
            ),
            row_coverage: row_coverage(70, 87, 158, 337, 43, 43, 661, 97, 0),
            bound_disposition_coverage: bound_dispositions(232_350, 35, 1_892, 0),
            stable_record_coverage: stable_records(113_786, 118_564, 35, 14, 108),
            replay_derivation_coverage: replay_derivations(881_686, 0, 768_970),
            provenance_epoch: 3_442_890,
            canonical_subtype_constraints: 143_608,
            subtype_duplicate_admissions: 13_218,
            subtype_trivial_admissions: 12_162,
            ordinary_lower_bounds_added: 113_786,
            ordinary_upper_bounds_added: 118_491,
            row_upper_bounds_added_without_replay: 73,
            evidence_lower_bounds_added: 0,
            evidence_upper_bounds_added: 0,
            subtract_fact_calls: 108,
            subtract_facts_added: 108,
            row_residuals_created: 70,
            row_residuals_reused: 0,
            lower_replay: replay(493_435, 493_435, 28_036, 0, 457_666, 7_733, 465_361),
            upper_replay: replay(388_251, 388_251, 69_223, 0, 311_304, 7_724, 318_990),
            nominal_cast_events: 2,
            nominal_cast_pairs: vec![
                pair("int", "float", 1),
                pair("int", "std::text::str::str", 1),
            ],
            poly_dump_fnv1a64: 11_851_711_006_157_111_264,
            check_report_fnv1a64: 15_043_926_579_654_723_785,
        },
        ConstraintCharacterization {
            name: "ref-update-local-buffer",
            origin_coverage: origins(1_871, 416, 1_475, 807, 294, 10_956, 22_995),
            body_requirement_coverage: body_requirements(98),
            structural_coverage: structural(
                33_248, 332, 15_744, 13_756, 2_558, 484, 200, 0, 174, 91,
            ),
            row_coverage: row_coverage(71, 156, 329, 337, 43, 43, 797, 199, 0),
            bound_disposition_coverage: bound_dispositions(234_908, 35, 1_901, 5),
            stable_record_coverage: stable_records(115_098, 119_810, 35, 70, 108),
            replay_derivation_coverage: replay_derivations(897_306, 0, 782_883),
            provenance_epoch: 3_506_820,
            canonical_subtype_constraints: 145_701,
            subtype_duplicate_admissions: 14_298,
            subtype_trivial_admissions: 12_316,
            ordinary_lower_bounds_added: 115_098,
            ordinary_upper_bounds_added: 119_724,
            row_upper_bounds_added_without_replay: 86,
            evidence_lower_bounds_added: 0,
            evidence_upper_bounds_added: 0,
            subtract_fact_calls: 108,
            subtract_facts_added: 108,
            row_residuals_created: 71,
            row_residuals_reused: 0,
            lower_replay: replay(500_383, 500_383, 28_499, 0, 463_888, 7_996, 471_846),
            upper_replay: replay(396_923, 396_923, 69_944, 0, 318_995, 7_984, 326_941),
            nominal_cast_events: 1,
            nominal_cast_pairs: vec![pair("int", "float", 1)],
            poly_dump_fnv1a64: 10_414_515_087_808_807_663,
            check_report_fnv1a64: 9_910_688_348_905_276_119,
        },
        ConstraintCharacterization {
            name: "config-read-false-positive-repro",
            origin_coverage: origins(1_909, 430, 1_494, 825, 303, 11_311, 23_745),
            body_requirement_coverage: body_requirements(101),
            structural_coverage: structural(
                33_228, 338, 14_848, 14_124, 2_822, 508, 204, 0, 384, 149,
            ),
            row_coverage: row_coverage(74, 297, 539, 337, 43, 43, 1_086, 264, 0),
            bound_disposition_coverage: bound_dispositions(241_064, 35, 1_923, 0),
            stable_record_coverage: stable_records(118_158, 122_906, 35, 189, 111),
            replay_derivation_coverage: replay_derivations(906_177, 0, 788_432),
            provenance_epoch: 3_542_890,
            canonical_subtype_constraints: 149_363,
            subtype_duplicate_admissions: 14_600,
            subtype_trivial_admissions: 12_809,
            ordinary_lower_bounds_added: 118_158,
            ordinary_upper_bounds_added: 122_798,
            row_upper_bounds_added_without_replay: 108,
            evidence_lower_bounds_added: 0,
            evidence_upper_bounds_added: 0,
            subtract_fact_calls: 111,
            subtract_facts_added: 111,
            row_residuals_created: 74,
            row_residuals_reused: 0,
            lower_replay: replay(504_858, 504_858, 29_115, 0, 467_437, 8_306, 475_705),
            upper_replay: replay(401_319, 401_319, 72_039, 0, 320_995, 8_285, 329_242),
            nominal_cast_events: 1,
            nominal_cast_pairs: vec![pair("int", "float", 1)],
            poly_dump_fnv1a64: 2_651_795_298_064_615_825,
            check_report_fnv1a64: 9_427_357_688_901_659_345,
        },
        ConstraintCharacterization {
            name: "file-rollback-false-positive-repro",
            origin_coverage: origins(1_886, 418, 1_485, 813, 294, 11_088, 23_329),
            body_requirement_coverage: body_requirements(98),
            structural_coverage: structural(
                33_389, 337, 15_598, 13_880, 2_654, 488, 202, 0, 230, 113,
            ),
            row_coverage: row_coverage(73, 192, 434, 337, 44, 44, 874, 268, 0),
            bound_disposition_coverage: bound_dispositions(236_512, 35, 1_901, 5),
            stable_record_coverage: stable_records(115_906, 120_606, 35, 96, 111),
            replay_derivation_coverage: replay_derivations(894_084, 0, 778_943),
            provenance_epoch: 3_494_499,
            canonical_subtype_constraints: 146_763,
            subtype_duplicate_admissions: 14_535,
            subtype_trivial_admissions: 12_513,
            ordinary_lower_bounds_added: 115_906,
            ordinary_upper_bounds_added: 120_510,
            row_upper_bounds_added_without_replay: 96,
            evidence_lower_bounds_added: 0,
            evidence_upper_bounds_added: 0,
            subtract_fact_calls: 111,
            subtract_facts_added: 111,
            row_residuals_created: 73,
            row_residuals_reused: 0,
            lower_replay: replay(499_044, 499_044, 28_556, 0, 462_412, 8_076, 470_450),
            upper_replay: replay(395_040, 395_040, 70_448, 0, 316_531, 8_061, 324_554),
            nominal_cast_events: 1,
            nominal_cast_pairs: vec![pair("int", "float", 1)],
            poly_dump_fnv1a64: 5_327_582_227_547_795_948,
            check_report_fnv1a64: 13_315_066_750_332_096_975,
        },
    ]
}

fn origins(
    application_argument: usize,
    pattern: usize,
    annotation: usize,
    return_: usize,
    body_requirement: usize,
    internal: usize,
    unknown_internal: usize,
) -> ConstraintOriginCoverage {
    ConstraintOriginCoverage {
        application_argument,
        pattern,
        annotation,
        return_,
        body_requirement,
        internal,
        unknown_internal,
        ..ConstraintOriginCoverage::default()
    }
}

fn body_requirements(boolean_condition: usize) -> BodyRequirementOriginCoverage {
    BodyRequirementOriginCoverage {
        boolean_condition,
        ..BodyRequirementOriginCoverage::default()
    }
}

#[allow(clippy::too_many_arguments)]
fn structural(
    full_unary: usize,
    normalization: usize,
    union_intersection: usize,
    function: usize,
    constructor: usize,
    tuple: usize,
    record: usize,
    variant: usize,
    row: usize,
    deferred_multi_parent: usize,
) -> StructuralDerivationCoverage {
    StructuralDerivationCoverage {
        full_unary,
        normalization,
        union_intersection,
        function,
        constructor,
        tuple,
        record,
        variant,
        row,
        deferred_multi_parent,
        unknown_rule: 0,
    }
}

fn stable_records(
    ordinary_lower_created: usize,
    ordinary_upper_created: usize,
    lower_duplicate_provenance_merges: usize,
    upper_duplicate_provenance_merges: usize,
    subtract_fact_records_created: usize,
) -> StableRecordCoverage {
    StableRecordCoverage {
        ordinary_lower_created,
        ordinary_upper_created,
        lower_duplicate_provenance_merges,
        upper_duplicate_provenance_merges,
        subtract_fact_records_created,
        ..StableRecordCoverage::default()
    }
}

fn replay(
    inputs: usize,
    generated: usize,
    accepted: usize,
    evidence_only: usize,
    duplicate: usize,
    trivial: usize,
    prefiltered: usize,
) -> ReplayCharacterization {
    ReplayCharacterization {
        inputs,
        generated,
        accepted,
        evidence_only,
        duplicate,
        trivial,
        prefiltered,
    }
}

fn pair(source: &str, target: &str, count: usize) -> (String, String, usize) {
    (source.to_string(), target.to_string(), count)
}

fn repository_std_loaded(root_source: &str) -> Vec<sources::LoadedFile> {
    let repository = repository_root();
    let lib = repository.join("lib");
    let mut paths = vec![lib.join("std.yu")];
    collect_yu_files(&lib.join("std"), &mut paths);
    paths.sort();

    let mut files = vec![source_file(&[], root_source)];
    files.extend(paths.into_iter().map(|path| {
        let relative = path.strip_prefix(&lib).expect("std path below lib");
        let mut module = relative.to_path_buf();
        module.set_extension("");
        let segments = module
            .components()
            .map(|component| {
                let std::path::Component::Normal(segment) = component else {
                    panic!("normal std module path component")
                };
                segment.to_str().expect("utf-8 std path")
            })
            .collect::<Vec<_>>();
        source_file(
            &segments,
            &fs::read_to_string(path).expect("read std source"),
        )
    }));
    sources::load(files)
}

fn repository_root() -> PathBuf {
    FsPath::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("canonical repository root")
}

fn collect_yu_files(directory: &FsPath, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).expect("read repository std directory") {
        let path = entry.expect("read repository std entry").path();
        if path.is_dir() {
            collect_yu_files(&path, files);
        } else if path.extension().and_then(|extension| extension.to_str()) == Some("yu") {
            files.push(path);
        }
    }
}

fn source_file(path: &[&str], source: &str) -> sources::SourceFile {
    sources::SourceFile {
        module_path: sources::Path {
            segments: path
                .iter()
                .map(|segment| sources::Name((*segment).to_string()))
                .collect(),
        },
        source: source.to_string(),
    }
}
