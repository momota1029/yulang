use super::*;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path as FsPath, PathBuf};

use crate::constraints::explain::{
    ExplanationBudget, ExplanationCompleteness, ExplanationTruncationReason,
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
        let expected_replay_bytes_proxy = (timing.lower_replay_accepted
            + timing.upper_replay_accepted
            + timing.lower_replay_duplicate
            + timing.upper_replay_duplicate)
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
        "config-read-false-positive-repro" => Some(("&blanks#3:3", "&comments#3:2", 9usize)),
        "file-rollback-false-positive-repro" => Some(("&buffer#5:0", "&store#6:0", 3)),
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
    considered_and_inserted: usize,
    semantic_duplicate_results: usize,
) -> ReplayDerivationCoverage {
    ReplayDerivationCoverage {
        considered: considered_and_inserted,
        inserted: considered_and_inserted,
        deduplicated: 0,
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
    vec![
        ConstraintCharacterization {
            name: "repository-std-only",
            origin_coverage: origins(1_852, 1_480, 791, 9_496, 24_664),
            structural_coverage: structural(
                31_698, 330, 14_562, 13_568, 2_470, 468, 196, 0, 104, 51,
            ),
            row_coverage: row_coverage(70, 51, 102, 343, 43, 43, 592, 77, 0),
            bound_disposition_coverage: bound_dispositions(231_493, 35, 1_875, 0),
            stable_record_coverage: stable_records(113_398, 118_095, 35, 105),
            replay_derivation_coverage: replay_derivations(880_497, 768_170),
            provenance_epoch: 1_406_624,
            canonical_subtype_constraints: 143_046,
            subtype_duplicate_admissions: 13_114,
            subtype_trivial_admissions: 12_098,
            ordinary_lower_bounds_added: 113_398,
            ordinary_upper_bounds_added: 118_044,
            row_upper_bounds_added_without_replay: 51,
            evidence_lower_bounds_added: 0,
            evidence_upper_bounds_added: 0,
            subtract_fact_calls: 105,
            subtract_facts_added: 105,
            row_residuals_created: 70,
            row_residuals_reused: 0,
            lower_replay: replay(492_650, 492_650, 27_917, 0, 457_021, 7_712, 464_695),
            upper_replay: replay(387_847, 387_847, 68_993, 0, 311_149, 7_705, 318_816),
            nominal_cast_events: 1,
            nominal_cast_pairs: vec![pair("int", "float", 1)],
            poly_dump_fnv1a64: 10_725_720_872_346_840_585,
            check_report_fnv1a64: 14_957_516_635_621_855_563,
        },
        ConstraintCharacterization {
            name: "effect-callback-residual",
            origin_coverage: origins(1_855, 1_480, 791, 9_546, 24_733),
            structural_coverage: structural(
                31_763, 331, 14_570, 13_612, 2_470, 468, 196, 0, 116, 61,
            ),
            row_coverage: row_coverage(70, 61, 124, 343, 43, 43, 615, 89, 0),
            bound_disposition_coverage: bound_dispositions(232_142, 35, 1_892, 0),
            stable_record_coverage: stable_records(113_695, 118_447, 35, 106),
            replay_derivation_coverage: replay_derivations(881_247, 768_646),
            provenance_epoch: 1_408_951,
            canonical_subtype_constraints: 143_492,
            subtype_duplicate_admissions: 13_186,
            subtype_trivial_admissions: 12_127,
            ordinary_lower_bounds_added: 113_695,
            ordinary_upper_bounds_added: 118_386,
            row_upper_bounds_added_without_replay: 61,
            evidence_lower_bounds_added: 0,
            evidence_upper_bounds_added: 0,
            subtract_fact_calls: 106,
            subtract_facts_added: 106,
            row_residuals_created: 70,
            row_residuals_reused: 0,
            lower_replay: replay(493_050, 493_050, 28_016, 0, 457_316, 7_718, 464_996),
            upper_replay: replay(388_197, 388_197, 69_156, 0, 311_330, 7_711, 319_003),
            nominal_cast_events: 2,
            nominal_cast_pairs: vec![
                pair("int", "float", 1),
                pair("int", "std::text::str::str", 1),
            ],
            poly_dump_fnv1a64: 12_977_017_262_933_715_556,
            check_report_fnv1a64: 9_834_333_167_365_965_178,
        },
        ConstraintCharacterization {
            name: "ref-update-local-buffer",
            origin_coverage: origins(1_868, 1_487, 795, 9_601, 24_913),
            structural_coverage: structural(
                33_225, 332, 15_782, 13_712, 2_592, 468, 200, 0, 139, 74,
            ),
            row_coverage: row_coverage(71, 74, 231, 343, 43, 43, 639, 183, 0),
            bound_disposition_coverage: bound_dispositions(234_727, 35, 1_898, 5),
            stable_record_coverage: stable_records(115_034, 119_693, 35, 106),
            replay_derivation_coverage: replay_derivations(897_161, 782_849),
            provenance_epoch: 1_431_813,
            canonical_subtype_constraints: 145_614,
            subtype_duplicate_admissions: 14_132,
            subtype_trivial_admissions: 12_249,
            ordinary_lower_bounds_added: 115_034,
            ordinary_upper_bounds_added: 119_627,
            row_upper_bounds_added_without_replay: 66,
            evidence_lower_bounds_added: 0,
            evidence_upper_bounds_added: 0,
            subtract_fact_calls: 106,
            subtract_facts_added: 106,
            row_residuals_created: 71,
            row_residuals_reused: 0,
            lower_replay: replay(500_063, 500_063, 28_475, 0, 463_596, 7_992, 471_550),
            upper_replay: replay(397_098, 397_098, 69_874, 0, 319_253, 7_971, 327_186),
            nominal_cast_events: 1,
            nominal_cast_pairs: vec![pair("int", "float", 1)],
            poly_dump_fnv1a64: 15_412_163_049_658_336_559,
            check_report_fnv1a64: 9_159_354_204_402_972_170,
        },
        ConstraintCharacterization {
            name: "config-read-false-positive-repro",
            origin_coverage: origins(1_906, 1_506, 813, 9_927, 25_715),
            structural_coverage: structural(
                33_260, 338, 14_922, 14_080, 2_934, 492, 204, 0, 290, 91,
            ),
            row_coverage: row_coverage(74, 91, 231, 343, 43, 43, 680, 162, 0),
            bound_disposition_coverage: bound_dispositions(240_968, 35, 1_883, 0),
            stable_record_coverage: stable_records(118_159, 122_809, 35, 109),
            replay_derivation_coverage: replay_derivations(906_567, 788_687),
            provenance_epoch: 1_454_568,
            canonical_subtype_constraints: 149_487,
            subtype_duplicate_admissions: 13_938,
            subtype_trivial_admissions: 12_622,
            ordinary_lower_bounds_added: 118_159,
            ordinary_upper_bounds_added: 122_718,
            row_upper_bounds_added_without_replay: 91,
            evidence_lower_bounds_added: 0,
            evidence_upper_bounds_added: 0,
            subtract_fact_calls: 109,
            subtract_facts_added: 109,
            row_residuals_created: 74,
            row_residuals_reused: 0,
            lower_replay: replay(504_714, 504_714, 29_174, 0, 467_166, 8_374, 475_502),
            upper_replay: replay(401_853, 401_853, 72_060, 0, 321_521, 8_272, 329_755),
            nominal_cast_events: 109,
            nominal_cast_pairs: vec![
                pair("&blanks#3:3", "&comments#3:2", 9),
                pair("&blanks#3:3", "&entries#3:1", 9),
                pair("&blanks#3:3", "&port#3:0", 9),
                pair("&comments#3:2", "&blanks#3:3", 9),
                pair("&comments#3:2", "&entries#3:1", 9),
                pair("&comments#3:2", "&port#3:0", 9),
                pair("&entries#3:1", "&blanks#3:3", 9),
                pair("&entries#3:1", "&comments#3:2", 9),
                pair("&entries#3:1", "&port#3:0", 9),
                pair("&port#3:0", "&blanks#3:3", 9),
                pair("&port#3:0", "&comments#3:2", 9),
                pair("&port#3:0", "&entries#3:1", 9),
                pair("int", "float", 1),
            ],
            poly_dump_fnv1a64: 17_962_835_939_841_197_455,
            check_report_fnv1a64: 9_542_933_224_538_196_032,
        },
        ConstraintCharacterization {
            name: "file-rollback-false-positive-repro",
            origin_coverage: origins(1_883, 1_497, 801, 9_725, 25_256),
            structural_coverage: structural(
                33_199, 337, 15_466, 13_836, 2_710, 472, 202, 0, 176, 82,
            ),
            row_coverage: row_coverage(73, 82, 246, 343, 44, 44, 660, 190, 0),
            bound_disposition_coverage: bound_dispositions(236_385, 35, 1_885, 5),
            stable_record_coverage: stable_records(115_881, 120_504, 35, 109),
            replay_derivation_coverage: replay_derivations(894_141, 779_036),
            provenance_epoch: 1_432_477,
            canonical_subtype_constraints: 146_636,
            subtype_duplicate_admissions: 14_072,
            subtype_trivial_admissions: 12_396,
            ordinary_lower_bounds_added: 115_881,
            ordinary_upper_bounds_added: 120_422,
            row_upper_bounds_added_without_replay: 82,
            evidence_lower_bounds_added: 0,
            evidence_upper_bounds_added: 0,
            subtract_fact_calls: 109,
            subtract_facts_added: 109,
            row_residuals_created: 73,
            row_residuals_reused: 0,
            lower_replay: replay(498_916, 498_916, 28_559, 0, 462_254, 8_103, 470_319),
            upper_replay: replay(395_225, 395_225, 70_393, 0, 316_782, 8_050, 324_794),
            nominal_cast_events: 7,
            nominal_cast_pairs: vec![
                pair("&buffer#5:0", "&store#6:0", 3),
                pair("&store#6:0", "&buffer#5:0", 3),
                pair("int", "float", 1),
            ],
            poly_dump_fnv1a64: 8_080_528_548_088_044_678,
            check_report_fnv1a64: 10_008_233_950_265_717_320,
        },
    ]
}

fn origins(
    application_argument: usize,
    annotation: usize,
    return_: usize,
    internal: usize,
    unknown_internal: usize,
) -> ConstraintOriginCoverage {
    ConstraintOriginCoverage {
        application_argument,
        annotation,
        return_,
        internal,
        unknown_internal,
        ..ConstraintOriginCoverage::default()
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
    subtract_fact_records_created: usize,
) -> StableRecordCoverage {
    StableRecordCoverage {
        ordinary_lower_created,
        ordinary_upper_created,
        lower_duplicate_provenance_merges,
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
