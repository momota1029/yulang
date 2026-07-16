use super::*;

use super::stage0_tests::{fixture_source, repository_std_loaded, root_value_def};
use crate::analysis::{
    GeneralizeSnapshotCharacterizationReport,
    with_generalize_snapshot_characterization_for_new_sessions,
};

#[test]
fn stage0_characterizes_exact_generalize_role_snapshots_across_the_acceptance_set() {
    let cases = [
        CharacterizationCase::fixture(
            "markdown",
            "std_prefix_yumark_markdown_workload.yu",
            Some("proof"),
        ),
        CharacterizationCase::fixture("html", "std_prefix_yumark_html_fallback.yu", Some("proof")),
        CharacterizationCase::repository_std_only(),
        CharacterizationCase::showcase(),
        CharacterizationCase::source(
            "metamorphic-rename-before",
            concat!(
                "use std::prelude::*\n",
                "mod std;\n",
                "mod container:\n",
                "  pub value = 1\n",
                "my selected = container::value\n",
            ),
        ),
        CharacterizationCase::source(
            "metamorphic-rename-after",
            concat!(
                "use std::prelude::*\n",
                "mod std;\n",
                "mod container:\n",
                "  pub renamed = 1\n",
                "my selected = container::renamed\n",
            ),
        ),
        CharacterizationCase::source(
            "metamorphic-module-move",
            concat!(
                "use std::prelude::*\n",
                "mod std;\n",
                "mod moved:\n",
                "  pub value = 1\n",
                "my selected = moved::value\n",
            ),
        ),
        CharacterizationCase::standalone(
            "ordinary-non-role-control",
            "my plain(value: int): int = value\nmy result: int = plain 42\n",
        ),
        CharacterizationCase::standalone(
            "small-role-control",
            "role Display 'a:\n  our x.display: unit\nmy show = \\x -> x.display\n",
        ),
    ];

    let mut cases_with_repeats = 0usize;
    let mut roots_with_repeats = 0usize;
    let mut non_proof_roots_with_repeats = 0usize;
    let mut proof_witness_checked = false;
    for case in cases {
        let baseline_started = Instant::now();
        let baseline = case.lower();
        let baseline_wall = baseline_started.elapsed();
        assert!(
            baseline.errors.is_empty(),
            "{} baseline: {:?}",
            case.name,
            baseline.errors
        );
        let output = with_generalize_snapshot_characterization_for_new_sessions(|| case.lower());
        assert!(
            output.errors.is_empty(),
            "{}: {:?}",
            case.name,
            output.errors
        );
        let report = output
            .session
            .generalize_snapshot_characterization_report()
            .expect("enabled session must carry exact-snapshot characterization");
        assert_report_invariants(case.name, &report);

        let proof = case.proof.map(|name| root_value_def(&output.modules, name));
        if let Some(proof) = proof {
            let proof_report = report
                .root(proof)
                .expect("Yumark proof root must be characterized");
            if case.name == "markdown" {
                assert_markdown_proof_witness(proof_report);
                proof_witness_checked = true;
            }
        }

        let repeated_roots = report
            .roots
            .iter()
            .filter(|root| root.exact_repeats > 0)
            .count();
        cases_with_repeats += usize::from(repeated_roots > 0);
        roots_with_repeats += repeated_roots;
        non_proof_roots_with_repeats += report
            .roots
            .iter()
            .filter(|root| Some(root.def) != proof && root.exact_repeats > 0)
            .count();
        print_case_report(case.name, &output, &report, &baseline, baseline_wall);
    }

    assert!(proof_witness_checked);
    assert!(
        cases_with_repeats > 1,
        "exact repeats must occur in more than the single Markdown fixture"
    );
    assert!(
        roots_with_repeats > 1 && non_proof_roots_with_repeats > 0,
        "exact repeats must occur in multiple roots, including a non-proof root"
    );
}

fn assert_report_invariants(case: &str, report: &GeneralizeSnapshotCharacterizationReport) {
    assert!(!report.roots.is_empty(), "{case}");
    for root in &report.roots {
        assert_eq!(
            root.exact_result_mismatches, 0,
            "{case} {:?}: equal E/A/M/D/C changed the pure result",
            root.def
        );
        assert_eq!(
            (
                root.shadow_disposition_mismatches,
                root.shadow_state_delta_mismatches,
                root.shadow_full_path_mismatches,
            ),
            (0, 0, 0),
            "{case} {:?}: exact snapshot shadow application diverged",
            root.def,
        );
        assert_eq!(
            root.would_be_hits, root.exact_repeats,
            "{case} {:?}: every would-be hit must verify exactly",
            root.def,
        );
        assert!(
            root.solve_boundaries.iter().all(|boundary| {
                boundary.exact_repeat_count == 0
                    || (boundary.pending_constraint_work == 0
                        && boundary.pending_constraint_events == 0)
            }),
            "{case} {:?}: an exact repeat crossed pending constraint state",
            root.def
        );
        assert_eq!(
            root.demands
                .iter()
                .map(|demand| demand.solves)
                .sum::<usize>(),
            root.exact_repeats + root.necessary_solves,
            "{case} {:?}",
            root.def
        );
        assert!(
            root.peak_entries <= root.demands.len(),
            "{case} {:?}",
            root.def
        );
        for demand in &root.demands {
            assert_eq!(
                demand.solves,
                demand.exact_repeats + demand.necessary_solves,
                "{case} {:?} slot {}",
                root.def,
                demand.slot
            );
        }
    }
}

fn assert_markdown_proof_witness(root: &crate::analysis::GeneralizeSnapshotRootReport) {
    let iteration_2 = root
        .solve_boundaries
        .iter()
        .find(|boundary| boundary.iteration == 2)
        .expect("Markdown proof iteration 2 solve boundary");
    let iteration_3 = root
        .solve_boundaries
        .iter()
        .find(|boundary| boundary.iteration == 3)
        .expect("Markdown proof iteration 3 solve boundary");
    let iteration_4 = root
        .solve_boundaries
        .iter()
        .find(|boundary| boundary.iteration == 4)
        .expect("Markdown proof iteration 4 solve boundary");
    assert!(iteration_2.new_resolution_count > 0);
    assert!(iteration_3.new_resolution_count > 0);
    assert_eq!(iteration_4.new_resolution_count, 0);
    assert!(iteration_4.exact_repeat_count > 0);
    assert_eq!(iteration_3.constraint_epoch, iteration_4.constraint_epoch);
    assert_eq!(
        iteration_3.role_solve_supplemental_epoch,
        iteration_4.role_solve_supplemental_epoch
    );
    assert_eq!(iteration_3.candidate_guard, iteration_4.candidate_guard);
    assert!(root.demands.iter().any(|demand| {
        demand.observations.iter().any(|observation| {
            observation.iteration == 4
                && observation.boundary_eligible
                && observation.would_be_hit
                && observation.exact_repeat
                && observation.demand_equal
                && observation.epoch_equal
                && observation.supplemental_epoch_equal
                && observation.main_equal
                && observation.candidate_guard_equal
                && observation.result_equal
                && observation.disposition_equal
                && observation.state_delta_equal
                && observation.full_path_equal
        })
    }));
}

fn print_case_report(
    case: &str,
    output: &BodyLowering,
    report: &GeneralizeSnapshotCharacterizationReport,
    baseline: &BodyLowering,
    baseline_wall: Duration,
) {
    let roots_with_solves = report
        .roots
        .iter()
        .filter(|root| !root.solve_boundaries.is_empty())
        .collect::<Vec<_>>();
    let exact_repeats = roots_with_solves
        .iter()
        .map(|root| root.exact_repeats)
        .sum::<usize>();
    let necessary = roots_with_solves
        .iter()
        .map(|root| root.necessary_solves)
        .sum::<usize>();
    let peak_entries = roots_with_solves
        .iter()
        .map(|root| root.peak_entries)
        .max()
        .unwrap_or(0);
    let peak_bytes = roots_with_solves
        .iter()
        .map(|root| root.peak_retained_debug_bytes)
        .max()
        .unwrap_or(0);
    let exact_repeat_solve_time = roots_with_solves
        .iter()
        .map(|root| root.exact_repeat_solve_time)
        .sum::<Duration>();
    let necessary_solve_time = roots_with_solves
        .iter()
        .map(|root| root.necessary_solve_time)
        .sum::<Duration>();
    let demand_comparisons = roots_with_solves
        .iter()
        .map(|root| root.comparison_cost.demand_comparisons)
        .sum::<usize>();
    let demand_comparison_time = roots_with_solves
        .iter()
        .map(|root| root.comparison_cost.demand_time)
        .sum::<Duration>();
    let epoch_comparisons = roots_with_solves
        .iter()
        .map(|root| root.comparison_cost.epoch_comparisons)
        .sum::<usize>();
    let epoch_comparison_time = roots_with_solves
        .iter()
        .map(|root| root.comparison_cost.epoch_time)
        .sum::<Duration>();
    let main_comparisons = roots_with_solves
        .iter()
        .map(|root| root.comparison_cost.main_comparisons)
        .sum::<usize>();
    let main_comparison_time = roots_with_solves
        .iter()
        .map(|root| root.comparison_cost.main_time)
        .sum::<Duration>();
    let candidate_guard_comparisons = roots_with_solves
        .iter()
        .map(|root| root.comparison_cost.candidate_guard_comparisons)
        .sum::<usize>();
    let candidate_guard_comparison_time = roots_with_solves
        .iter()
        .map(|root| root.comparison_cost.candidate_guard_time)
        .sum::<Duration>();
    let snapshots = roots_with_solves
        .iter()
        .map(|root| root.clone_cost.snapshots)
        .sum::<usize>();
    let main_clone_time = roots_with_solves
        .iter()
        .map(|root| root.clone_cost.main_time)
        .sum::<Duration>();
    let demand_clone_time = roots_with_solves
        .iter()
        .map(|root| root.clone_cost.demand_time)
        .sum::<Duration>();
    let result_clone_time = roots_with_solves
        .iter()
        .map(|root| root.clone_cost.result_time)
        .sum::<Duration>();
    eprintln!(
        "generalize snapshot case {case}: roots={}, solves={{necessary:{necessary}, exact-repeat:{exact_repeats}, necessary-time:{necessary_solve_time:?}, exact-repeat-time:{exact_repeat_solve_time:?}}}, compare={{demand:{demand_comparisons}/{demand_comparison_time:?}, epoch:{epoch_comparisons}/{epoch_comparison_time:?}, main:{main_comparisons}/{main_comparison_time:?}, candidate:{candidate_guard_comparisons}/{candidate_guard_comparison_time:?}}}, retention={{snapshots:{snapshots}, main-clone:{main_clone_time:?}, demand-clone:{demand_clone_time:?}, result-clone:{result_clone_time:?}}}, peaks={{entries:{peak_entries}, retained-debug-bytes:{peak_bytes}}}, baseline={{wall:{baseline_wall:?}, measured-total:{:?}, generalize-role-solve:{:?}}}",
        roots_with_solves.len(),
        baseline.timing.total,
        baseline.timing.analysis.generalize_resolve_roles,
    );
    for root in roots_with_solves {
        let label = output.labels.def_label(root.def).unwrap_or("<unlabeled>");
        eprintln!(
            "generalize snapshot root {case}: def={:?} label={label:?} loop-iterations={} boundaries={} demands={} solves={{necessary:{}, exact-repeat:{}}} times={{necessary:{:?}, exact-repeat:{:?}, batch:{:?}, compare:{:?}, clone:{:?}, retention-accounting:{:?}}} peaks={{entries:{}, retained-debug-bytes:{}, retained-main-nodes:{}}} pending={{constraint-work:{}, constraint-events:{}, analysis-work:{}}}",
            root.def,
            root.loop_iterations,
            root.solve_boundaries.len(),
            root.demands.len(),
            root.necessary_solves,
            root.exact_repeats,
            root.necessary_solve_time,
            root.exact_repeat_solve_time,
            root.full_batch_solve_time,
            root.comparison_cost,
            root.clone_cost,
            root.retention_accounting_time,
            root.peak_entries,
            root.peak_retained_debug_bytes,
            root.peak_retained_main_nodes,
            root.boundaries_with_pending_constraint_work,
            root.boundaries_with_pending_constraint_events,
            root.boundaries_with_pending_analysis_work,
        );
        for demand in &root.demands {
            eprintln!(
                "generalize snapshot demand {case}: def={:?} slot={} role={:?} solves={} necessary={} exact-repeat={} times={{necessary:{:?}, exact-repeat:{:?}}} max-debug-bytes={{demand:{}, result:{}}}",
                root.def,
                demand.slot,
                demand.role,
                demand.solves,
                demand.necessary_solves,
                demand.exact_repeats,
                demand.necessary_solve_time,
                demand.exact_repeat_solve_time,
                demand.max_demand_debug_bytes,
                demand.max_result_debug_bytes,
            );
        }
        if label == "proof" {
            for boundary in &root.solve_boundaries {
                eprintln!(
                    "generalize snapshot proof-boundary {case}: iteration={} epoch={:?} supplemental-epoch={:?} candidate={} demands={} new={} exact-repeat={} main={{debug-bytes:{}, nodes:{}}} pending={{constraint-work:{}, constraint-events:{}, analysis-work:{}}}",
                    boundary.iteration,
                    boundary.constraint_epoch,
                    boundary.role_solve_supplemental_epoch,
                    boundary.candidate_guard,
                    boundary.demand_count,
                    boundary.new_resolution_count,
                    boundary.exact_repeat_count,
                    boundary.main_debug_bytes,
                    boundary.main_nodes,
                    boundary.pending_constraint_work,
                    boundary.pending_constraint_events,
                    boundary.pending_analysis_work,
                );
            }
        }
    }
}

struct CharacterizationCase {
    name: &'static str,
    source: String,
    proof: Option<&'static str>,
    standalone: bool,
}

impl CharacterizationCase {
    fn fixture(name: &'static str, fixture: &str, proof: Option<&'static str>) -> Self {
        Self {
            name,
            source: fixture_source(fixture),
            proof,
            standalone: false,
        }
    }

    fn source(name: &'static str, source: &str) -> Self {
        Self {
            name,
            source: source.to_string(),
            proof: None,
            standalone: false,
        }
    }

    fn standalone(name: &'static str, source: &str) -> Self {
        Self {
            name,
            source: source.to_string(),
            proof: None,
            standalone: true,
        }
    }

    fn lower(&self) -> BodyLowering {
        if self.standalone {
            crate::dump::dump_source(&self.source).lowering
        } else {
            let loaded = repository_std_loaded(&self.source);
            lower_loaded_files(&loaded).expect("lower exact-snapshot characterization fixture")
        }
    }

    fn repository_std_only() -> Self {
        Self::source("repository-std-only", "use std::prelude::*\nmod std;\n")
    }

    fn showcase() -> Self {
        let showcase = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .join("examples/showcase.yu"),
        )
        .expect("read repository showcase");
        Self::source(
            "repository-showcase",
            &format!("use std::prelude::*\nmod std;\n{showcase}"),
        )
    }
}
