use super::*;

use super::stage0_tests::{fixture_source, repository_std_loaded, root_value_def};
use crate::Arena;
use crate::analysis::with_shadow_dirty_oracle_for_new_sessions;
use crate::constraints::{ConstraintWeights, LeftConstraintWeight, RightConstraintWeight};

#[test]
fn shadow_dirty_oracle_characterizes_yumark_and_repository_std_owner_checks() {
    let cases = [
        ShadowOracleCase::fixture(
            "markdown",
            "std_prefix_yumark_markdown_workload.yu",
            Some("proof"),
            Some("render_markdown_doc"),
            100,
            7_526,
            7_359,
        ),
        ShadowOracleCase::fixture(
            "html",
            "std_prefix_yumark_html_fallback.yu",
            Some("proof"),
            Some("render_html_doc"),
            100,
            7_526,
            7_359,
        ),
        ShadowOracleCase {
            name: "repository-std-only",
            source: "use std::prelude::*\nmod std;\n".to_string(),
            target: None,
            workload_owner_label: None,
            expected_forced_passes: 91,
            expected_owner_checks: 6_480,
            expected_predicted_clean: 6_317,
        },
    ];
    let mut fingerprint_inventory_coverage = [false; 13];

    for case in cases {
        let loaded = repository_std_loaded(&case.source);
        let output = with_shadow_dirty_oracle_for_new_sessions(|| {
            lower_loaded_files(&loaded).expect("lower shadow dirty oracle fixture")
        });
        assert!(
            output.errors.is_empty(),
            "{}: {:?}",
            case.name,
            output.errors
        );
        let report = output
            .session
            .shadow_dirty_oracle_report()
            .expect("fixture lowering session must carry the enabled oracle");
        assert_eq!(
            report.predicted_clean + report.predicted_dirty,
            report.owner_checks,
            "{}",
            case.name
        );
        assert!(report.owner_checks > 0, "{}", case.name);
        assert!(report.predicted_clean > 0, "{}", case.name);
        assert_eq!(
            report.forced_passes, case.expected_forced_passes,
            "{} forced-pass characterization drifted",
            case.name
        );
        assert_eq!(
            report.owner_checks, case.expected_owner_checks,
            "{} owner-check characterization drifted",
            case.name
        );
        assert_eq!(
            report.predicted_clean, case.expected_predicted_clean,
            "{} clean characterization drifted",
            case.name
        );
        assert_eq!(
            report.root_available_predicted_clean + report.root_available_predicted_dirty,
            report.root_available_checks,
            "{}",
            case.name
        );
        assert_eq!(
            report.root_available_checks, report.owner_checks,
            "{}",
            case.name
        );
        assert_eq!(report.root_unavailable_outcomes, 0, "{}", case.name);
        assert_eq!(
            report.root_unavailable_outcomes
                + report.no_progress_outcomes
                + report.progress_outcomes,
            report.owner_checks,
            "{}",
            case.name
        );
        assert_eq!(
            report.predicted_clean_owner_solve_time + report.predicted_dirty_owner_solve_time,
            report.owner_solve_time,
            "{}",
            case.name
        );
        assert!(report.owner_solve_time > Duration::ZERO, "{}", case.name);
        assert!(
            report.method_taint_rebuild_time > Duration::ZERO,
            "{}",
            case.name
        );
        assert!(
            report.method_role_loop_time >= report.owner_solve_time,
            "{}: per-owner solve time {:?} exceeded enclosing owner loop {:?}",
            case.name,
            report.owner_solve_time,
            report.method_role_loop_time,
        );
        assert_eq!(
            report.dependency_cardinalities.len(),
            report.owner_checks,
            "{}",
            case.name
        );

        let target = case.target.map(|name| {
            let def = root_value_def(&output.modules, name);
            (def, report.owner(def).cloned())
        });
        if let Some((_, owner)) = &target {
            assert!(
                owner.is_none(),
                "{} proof target must not be conflated with SelectionUse.parent",
                case.name
            );
        }
        let workload_owner = case.workload_owner_label.and_then(|label| {
            report
                .owners
                .iter()
                .find(|owner| output.labels.def_label(owner.owner) == Some(label))
                .cloned()
                .or_else(|| {
                    report
                        .owners
                        .iter()
                        .find(|owner| {
                            output
                                .labels
                                .def_label(owner.owner)
                                .is_some_and(|owner_label| owner_label.ends_with(label))
                        })
                        .cloned()
                })
        });
        if case.workload_owner_label.is_some() {
            assert!(
                workload_owner.is_some(),
                "{} workload owner must be observed",
                case.name
            );
            let workload_owner = workload_owner.as_ref().expect("checked above");
            assert_eq!(workload_owner.owner_checks, 95, "{}", case.name);
            assert_eq!(workload_owner.predicted_clean, 94, "{}", case.name);
        }
        let dependency_summary = dependency_cardinality_summary(&report.dependency_cardinalities);
        let clean_time_percentage = duration_percentage(
            report.predicted_clean_owner_solve_time,
            report.owner_solve_time,
        );
        let taint_share = duration_percentage(
            report.method_taint_rebuild_time,
            report.method_taint_rebuild_time + report.owner_solve_time,
        );
        eprintln!(
            "shadow dirty oracle {}: passes={}, owner-checks={}, clean={}/{} ({:.2}%), root-available-clean={}/{} ({:.2}%), outcomes={{root-unavailable:{}, no-progress:{}, progress:{}}}, owner-solve={:?}, clean-owner-solve={:?} ({:.2}%), dirty-owner-solve={:?}, method-taint={:?}, method-taint-share={:.2}%, owner-loop={:?}, dependency-cardinality={{min:{}, mean:{:.2}, median:{}, p95:{}, max:{}}}, dependency-inventory={:?}, target={:?}, workload-owner={:?}, mismatches={:?}",
            case.name,
            report.forced_passes,
            report.owner_checks,
            report.predicted_clean,
            report.owner_checks,
            percentage(report.predicted_clean, report.owner_checks),
            report.root_available_predicted_clean,
            report.root_available_checks,
            percentage(
                report.root_available_predicted_clean,
                report.root_available_checks,
            ),
            report.root_unavailable_outcomes,
            report.no_progress_outcomes,
            report.progress_outcomes,
            report.owner_solve_time,
            report.predicted_clean_owner_solve_time,
            clean_time_percentage,
            report.predicted_dirty_owner_solve_time,
            report.method_taint_rebuild_time,
            taint_share,
            report.method_role_loop_time,
            dependency_summary.min,
            dependency_summary.mean,
            dependency_summary.median,
            dependency_summary.p95,
            dependency_summary.max,
            report.dependency_inventory,
            target,
            workload_owner,
            report.mismatches,
        );
        let inventory = report.dependency_inventory;
        for (covered, count) in fingerprint_inventory_coverage.iter_mut().zip([
            inventory.scc_roots,
            inventory.owner_raw_roles,
            inventory.owner_selections,
            inventory.constraint_bounds,
            inventory.constraint_neighbors,
            inventory.constraint_subtract_facts,
            inventory.constraint_levels,
            inventory.constraint_birth_levels,
            inventory.constraint_pre_pop_families,
            inventory.candidate_buckets,
            inventory.method_taint_entries,
            inventory.projection_selections,
            inventory.applied_resolutions,
        ]) {
            *covered |= count > 0;
        }
        assert!(
            report.mismatches.is_empty(),
            "{} clean prediction changed under the real solve: {:#?}",
            case.name,
            report.mismatches
        );
    }

    let inventory_names = [
        "scc-root",
        "owner-raw-roles",
        "owner-selections",
        "constraint-bounds",
        "constraint-neighbors",
        "constraint-subtract-facts",
        "constraint-levels",
        "constraint-birth-levels",
        "constraint-pre-pop-families",
        "candidate-buckets",
        "method-taint-entries",
        "projection-selections",
        "applied-resolutions",
    ];
    let missing = inventory_names
        .into_iter()
        .zip(fingerprint_inventory_coverage)
        .filter_map(|(name, covered)| (!covered).then_some(name))
        .collect::<Vec<_>>();
    assert_eq!(
        missing,
        ["constraint-neighbors", "constraint-birth-levels"],
        "three-fixture fingerprint inventory drifted; the two absent hooks have focused coverage"
    );
}

#[test]
fn shadow_dirty_oracle_constraint_fingerprint_read_hooks_are_complete() {
    let mut infer = Arena::new();
    let var = infer.fresh_type_var();
    assert_eq!(
        infer
            .constraints()
            .shadow_dirty_oracle_constraint_read_hook_inventory_for_test(var),
        [true; 6],
        "bounds, neighbors, subtract facts, level, birth level, and pre-pop families must all reach the owner-read frontier"
    );
}

#[test]
fn upper_row_pruning_can_escape_the_current_bounds_epoch_fingerprint() {
    let mut infer = Arena::new();
    let source = infer.fresh_type_var();
    let leaf_var = infer.fresh_type_var();
    let source_pos = infer.alloc_pos(Pos::Var(source));
    let leaf = infer.alloc_neg(Neg::Var(leaf_var));
    let inner_item = infer.alloc_neg(Neg::Con(vec!["inner".into()], Vec::new()));
    let stale_item = infer.alloc_neg(Neg::Con(vec!["stale".into()], Vec::new()));
    let follower_item = infer.alloc_neg(Neg::Con(vec!["follower".into()], Vec::new()));
    let inner = infer.alloc_neg(Neg::Row(vec![inner_item], leaf));
    let stale = infer.alloc_neg(Neg::Row(vec![stale_item], inner));
    let follower = infer.alloc_neg(Neg::Row(vec![follower_item], stale));

    infer.subtype(source_pos, stale);
    infer.subtype(source_pos, inner);
    infer.subtype(source_pos, leaf);
    infer.subtype(source_pos, follower);

    let before = infer
        .constraints()
        .bounds()
        .of(source)
        .expect("source bounds before pruning");
    let before_epoch = before.epoch();
    let before_uppers = before.uppers().to_vec();
    assert!(before_uppers.iter().any(|upper| upper.neg == follower));
    let retry_source_pos = infer.alloc_pos(Pos::Var(source));
    let oracle_detected_change = infer
        .constraints_mut()
        .shadow_dirty_oracle_detects_bound_mutation_for_test(source, |machine| {
            machine.weighted_subtype(
                retry_source_pos,
                ConstraintWeights {
                    left: LeftConstraintWeight::filter(Subtractability::Empty),
                    right: RightConstraintWeight::empty(),
                },
                stale,
            );
        });

    let after = infer
        .constraints()
        .bounds()
        .of(source)
        .expect("source bounds after pruning");
    assert_eq!(after.epoch(), before_epoch);
    assert_ne!(after.uppers(), before_uppers);
    assert!(!after.uppers().iter().any(|upper| upper.neg == follower));
    assert!(
        !oracle_detected_change,
        "the current oracle stores only the bounds epoch, so exact-vector pruning must expose its blind spot"
    );
}

#[test]
fn row_effect_no_replay_prune_and_insert_escapes_the_current_bounds_epoch_fingerprint() {
    let mut infer = Arena::new();
    let source = infer.fresh_type_var();
    let tail_var = infer.fresh_type_var();
    let matched_path = vec!["matched".into()];
    let stale_path = vec!["stale".into()];
    let matched_pos = infer.alloc_pos(Pos::Con(matched_path.clone(), Vec::new()));
    let matched_row = infer.alloc_pos(Pos::Row(vec![matched_pos]));
    let matched_neg = infer.alloc_neg(Neg::Con(matched_path, Vec::new()));
    let stale_neg = infer.alloc_neg(Neg::Con(stale_path, Vec::new()));
    let source_neg = infer.alloc_neg(Neg::Var(source));
    let source_pos = infer.alloc_pos(Pos::Var(source));
    let tail = infer.alloc_neg(Neg::Var(tail_var));
    let stale_row = infer.alloc_neg(Neg::Row(vec![stale_neg], tail));
    let matching_row = infer.alloc_neg(Neg::Row(vec![matched_neg], tail));

    infer.subtype(matched_row, source_neg);
    infer.subtype(source_pos, stale_row);

    let before = infer
        .constraints()
        .bounds()
        .of(source)
        .expect("source bounds before no-replay store");
    let before_epoch = before.epoch();
    let before_uppers = before.uppers().to_vec();
    assert!(before_uppers.iter().any(|upper| upper.neg == stale_row));
    let oracle_detected_change = infer
        .constraints_mut()
        .shadow_dirty_oracle_detects_bound_mutation_for_test(source, |machine| {
            machine.subtype(source_pos, matching_row);
        });

    let after = infer
        .constraints()
        .bounds()
        .of(source)
        .expect("source bounds after no-replay store");
    assert_eq!(after.epoch(), before_epoch);
    assert_ne!(after.uppers(), before_uppers);
    assert!(!after.uppers().iter().any(|upper| upper.neg == stale_row));
    assert!(after.uppers().iter().any(|upper| upper.neg == tail));
    assert!(
        !oracle_detected_change,
        "the row-effect no-replay path changes exact uppers without changing the epoch fingerprint"
    );
}

struct ShadowOracleCase {
    name: &'static str,
    source: String,
    target: Option<&'static str>,
    workload_owner_label: Option<&'static str>,
    expected_forced_passes: usize,
    expected_owner_checks: usize,
    expected_predicted_clean: usize,
}

impl ShadowOracleCase {
    fn fixture(
        name: &'static str,
        fixture: &str,
        target: Option<&'static str>,
        workload_owner_label: Option<&'static str>,
        expected_forced_passes: usize,
        expected_owner_checks: usize,
        expected_predicted_clean: usize,
    ) -> Self {
        Self {
            name,
            source: fixture_source(fixture),
            target,
            workload_owner_label,
            expected_forced_passes,
            expected_owner_checks,
            expected_predicted_clean,
        }
    }
}

#[derive(Debug)]
struct DependencyCardinalitySummary {
    min: usize,
    mean: f64,
    median: usize,
    p95: usize,
    max: usize,
}

fn dependency_cardinality_summary(samples: &[usize]) -> DependencyCardinalitySummary {
    assert!(!samples.is_empty());
    let mut sorted = samples.to_vec();
    sorted.sort_unstable();
    DependencyCardinalitySummary {
        min: sorted[0],
        mean: sorted.iter().sum::<usize>() as f64 / sorted.len() as f64,
        median: sorted[(sorted.len() - 1) / 2],
        p95: sorted[(sorted.len() - 1) * 95 / 100],
        max: *sorted.last().expect("non-empty dependency samples"),
    }
}

fn percentage(numerator: usize, denominator: usize) -> f64 {
    if denominator == 0 {
        return 0.0;
    }
    numerator as f64 * 100.0 / denominator as f64
}

fn duration_percentage(numerator: Duration, denominator: Duration) -> f64 {
    if denominator.is_zero() {
        return 0.0;
    }
    numerator.as_secs_f64() * 100.0 / denominator.as_secs_f64()
}
