use super::*;

use super::stage0_tests::{fixture_source, repository_std_loaded, root_value_def};
use crate::analysis::{
    GeneralizeSnapshotCharacterizationReport,
    with_generalize_role_snapshot_always_solve_for_new_sessions,
    with_generalize_snapshot_characterization_for_new_sessions,
};
use poly::expr::SelectId;
use poly::types::RolePredicate;

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
    let mut measurements = AcceptanceSetMeasurements::default();
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
        measurements.record(&report);
        assert_eq!(
            finalized_scheme_snapshot(&output),
            finalized_scheme_snapshot(&baseline),
            "{}: enabling the shadow oracle changed production-selected schemes",
            case.name,
        );

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
    measurements.print();
}

#[test]
fn stage2_production_snapshot_reuse_has_exact_isolated_always_solve_parity() {
    let cases = [
        CharacterizationCase::fixture(
            "markdown",
            "std_prefix_yumark_markdown_workload.yu",
            Some("proof"),
        ),
        CharacterizationCase::fixture("html", "std_prefix_yumark_html_fallback.yu", Some("proof")),
    ];

    for case in cases {
        // These are deliberately separate full lowering invocations. The always-solve branch
        // cannot observe any cache entry or applied-state mutation owned by the production branch.
        let mut production = case.lower();
        assert!(
            production
                .session
                .generalize_snapshot_characterization_report()
                .is_none(),
            "{}: production unexpectedly enabled the test-only shadow oracle",
            case.name,
        );
        let production_timing = production.session.timing();
        assert!(
            production_timing.generalize_role_snapshot_hits > 0,
            "{}: production run did not exercise an exact hit",
            case.name,
        );
        if case.name == "markdown" {
            assert!(
                production_timing.generalize_role_snapshot_hits > 100,
                "Markdown production reuse missed the characterized proof-root repeats",
            );
            assert!(
                production_timing.generalize_role_snapshot_peak_retained_debug_bytes > 20_000_000,
                "Markdown production reuse never retained the characterized large proof snapshot",
            );
        }

        let mut always_solve =
            with_generalize_role_snapshot_always_solve_for_new_sessions(|| case.lower());
        let always_solve_timing = always_solve.session.timing();
        assert_eq!(
            always_solve_timing.generalize_role_snapshot_hits, 0,
            "{}: rollback control unexpectedly reused a snapshot",
            case.name,
        );
        assert!(
            always_solve_timing.generalize_role_snapshot_full_solves
                > production_timing.generalize_role_snapshot_full_solves,
            "{}: exact production hits did not remove recursive full solves",
            case.name,
        );

        let production = ProductionParitySnapshot::capture(&mut production);
        let always_solve = ProductionParitySnapshot::capture(&mut always_solve);
        production.assert_eq(case.name, &always_solve);
    }
}

#[derive(Default)]
struct AcceptanceSetMeasurements {
    would_be_hits: usize,
    exact_matches: usize,
    result_mismatches: usize,
    disposition_mismatches: usize,
    state_delta_mismatches: usize,
    full_path_mismatches: usize,
    epoch_misses: usize,
    supplemental_epoch_misses: usize,
    main_misses: usize,
    demand_misses: usize,
    candidate_misses: usize,
    cap_misses: usize,
    lifecycle_misses: usize,
    peak_entries: usize,
    peak_retained_debug_bytes: usize,
}

impl AcceptanceSetMeasurements {
    fn record(&mut self, report: &GeneralizeSnapshotCharacterizationReport) {
        for root in &report.roots {
            self.would_be_hits += root.would_be_hits;
            self.exact_matches += root.exact_repeats;
            self.result_mismatches += root.exact_result_mismatches;
            self.disposition_mismatches += root.shadow_disposition_mismatches;
            self.state_delta_mismatches += root.shadow_state_delta_mismatches;
            self.full_path_mismatches += root.shadow_full_path_mismatches;
            self.epoch_misses += root.epoch_misses();
            self.supplemental_epoch_misses += root.supplemental_epoch_misses();
            self.main_misses += root.main_misses();
            self.demand_misses += root.demand_misses();
            self.candidate_misses += root.candidate_misses();
            self.cap_misses += root.cap_misses();
            self.lifecycle_misses += root.lifecycle_misses();
            self.peak_entries = self.peak_entries.max(root.peak_entries);
            self.peak_retained_debug_bytes = self
                .peak_retained_debug_bytes
                .max(root.peak_retained_debug_bytes);
        }
    }

    fn print(&self) {
        let mismatches = self.result_mismatches
            + self.disposition_mismatches
            + self.state_delta_mismatches
            + self.full_path_mismatches;
        eprintln!(
            "generalize snapshot acceptance total: would-be-hits={} exact-matches={} mismatches={} mismatch-dimensions={{result:{}, disposition:{}, state-delta:{}, full-path:{}}} misses={{epoch:{}, supplemental-epoch:{}, main:{}, demand:{}, candidate:{}, cap:{}, lifecycle:{}}} peaks={{entries:{}, retained-debug-bytes:{}}}",
            self.would_be_hits,
            self.exact_matches,
            mismatches,
            self.result_mismatches,
            self.disposition_mismatches,
            self.state_delta_mismatches,
            self.full_path_mismatches,
            self.epoch_misses,
            self.supplemental_epoch_misses,
            self.main_misses,
            self.demand_misses,
            self.candidate_misses,
            self.cap_misses,
            self.lifecycle_misses,
            self.peak_entries,
            self.peak_retained_debug_bytes,
        );
    }
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
        assert_eq!(
            root.cap_exhaustions, 0,
            "{case} {:?}: approved shadow budget rejected an acceptance-set root",
            root.def,
        );
        assert!(root.retained_entries_at_finish <= root.peak_entries);
        assert!(root.retained_debug_bytes_at_finish <= root.peak_retained_debug_bytes);
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
            assert!(demand.observations.iter().all(|observation| {
                observation.exact_repeat == observation.miss_reason.is_none()
            }));
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
                && observation.miss_reason.is_none()
        })
    }));
}

fn finalized_scheme_snapshot(output: &BodyLowering) -> Vec<(DefId, String, String)> {
    let mut schemes = output
        .session
        .poly
        .defs
        .iter()
        .filter_map(|(def, item)| match item {
            Def::Let {
                scheme: Some(scheme),
                ..
            } => Some((
                def,
                poly::dump::format_scheme(&output.session.poly.typ, scheme),
                poly::dump::dump_scheme_raw(&output.session.poly.typ, scheme),
            )),
            Def::Mod { .. } | Def::Let { .. } | Def::Arg => None,
        })
        .collect::<Vec<_>>();
    schemes.sort_by_key(|(def, _, _)| def.0);
    schemes
}

struct ProductionParitySnapshot {
    finalized_schemes: Vec<(DefId, String, String)>,
    residual_role_predicates: Vec<(DefId, Vec<RolePredicate>)>,
    unresolved_selections: Vec<(SelectId, SelectionUse)>,
    generalization_restarts: GeneralizationRestartCensus,
    scc_stats: crate::scc::SccStats,
    scc_events: Vec<crate::scc::SccEvent>,
    lowering_errors: Vec<BodyLoweringError>,
    diagnostics: crate::check::PolyCheckReport,
    poly_dump: String,
    poly_raw_dump: String,
    namespace: crate::CompiledNamespaceSurface,
    lowering_surface: crate::CompiledLoweringSurface,
    runtime_arena_dump: String,
    runtime_raw_arena_dump: String,
    runtime_boundary: crate::CompiledBoundaryInterface,
    runtime_labels: poly::dump::DumpLabels,
    runtime_modules: Vec<crate::CompiledRuntimeModuleDef>,
    runtime_values: Vec<crate::CompiledRuntimeValueDef>,
}

impl ProductionParitySnapshot {
    fn capture(output: &mut BodyLowering) -> Self {
        let finalized_schemes = finalized_scheme_snapshot(output);
        let mut residual_role_predicates = output
            .session
            .poly
            .defs
            .iter()
            .filter_map(|(def, item)| match item {
                Def::Let {
                    scheme: Some(scheme),
                    ..
                } => Some((def, scheme.role_predicates.clone())),
                Def::Mod { .. } | Def::Let { .. } | Def::Arg => None,
            })
            .collect::<Vec<_>>();
        residual_role_predicates.sort_by_key(|(def, _)| def.0);

        let mut unresolved_selections = output
            .session
            .selections
            .iter()
            .map(|(select, use_site)| (select, *use_site))
            .collect::<Vec<_>>();
        unresolved_selections.sort_by_key(|(select, _)| select.0);

        let timing = output.session.timing();
        let generalization_restarts = GeneralizationRestartCensus::from_timing(timing);
        let scc_stats = output.session.scc.stats();
        let lowering_errors = output.errors.clone();
        let diagnostics = crate::check::summarize_lowering(output);
        let poly_dump = poly::dump::dump_arena_with_labels(&output.session.poly, &output.labels);
        let poly_raw_dump =
            poly::dump::dump_arena_raw_with_labels(&output.session.poly, &output.labels);
        let namespace = crate::CompiledNamespaceSurface::from_module_table(&output.modules);
        let lowering_surface =
            crate::CompiledLoweringSurface::from_module_table(&output.modules, &namespace);
        let runtime =
            crate::CompiledRuntimeSurface::from_lowering_with_namespace(output, &namespace);
        let runtime_arena_dump =
            poly::dump::dump_arena_with_labels(&runtime.arena, &runtime.labels);
        let runtime_raw_arena_dump =
            poly::dump::dump_arena_raw_with_labels(&runtime.arena, &runtime.labels);
        let scc_events = output.session.take_scc_events();

        Self {
            finalized_schemes,
            residual_role_predicates,
            unresolved_selections,
            generalization_restarts,
            scc_stats,
            scc_events,
            lowering_errors,
            diagnostics,
            poly_dump,
            poly_raw_dump,
            namespace,
            lowering_surface,
            runtime_arena_dump,
            runtime_raw_arena_dump,
            runtime_boundary: runtime.boundary,
            runtime_labels: runtime.labels,
            runtime_modules: runtime.modules,
            runtime_values: runtime.values,
        }
    }

    fn assert_eq(&self, case: &str, with_shadow: &Self) {
        assert_eq!(
            with_shadow.finalized_schemes, self.finalized_schemes,
            "{case}: finalized schemes diverged"
        );
        assert_eq!(
            with_shadow.residual_role_predicates, self.residual_role_predicates,
            "{case}: residual role predicates diverged"
        );
        assert_eq!(
            with_shadow.unresolved_selections, self.unresolved_selections,
            "{case}: selections diverged"
        );
        assert_eq!(
            with_shadow.generalization_restarts, self.generalization_restarts,
            "{case}: generalization restart census diverged"
        );
        assert_eq!(
            with_shadow.scc_stats, self.scc_stats,
            "{case}: SCC scheduling counters diverged"
        );
        assert_eq!(
            with_shadow.scc_events, self.scc_events,
            "{case}: SCC event order diverged"
        );
        assert_eq!(
            with_shadow.lowering_errors, self.lowering_errors,
            "{case}: lowering errors diverged"
        );
        assert_eq!(
            with_shadow.diagnostics, self.diagnostics,
            "{case}: diagnostics diverged"
        );
        assert_text_eq(
            case,
            "poly surface dump",
            &self.poly_dump,
            &with_shadow.poly_dump,
        );
        assert_text_eq(
            case,
            "poly raw dump",
            &self.poly_raw_dump,
            &with_shadow.poly_raw_dump,
        );
        assert_eq!(
            with_shadow.namespace, self.namespace,
            "{case}: compiled namespace surface diverged"
        );
        assert_eq!(
            with_shadow.lowering_surface, self.lowering_surface,
            "{case}: compiled lowering surface diverged"
        );
        assert_text_eq(
            case,
            "compiled runtime arena",
            &self.runtime_arena_dump,
            &with_shadow.runtime_arena_dump,
        );
        assert_text_eq(
            case,
            "compiled runtime raw arena",
            &self.runtime_raw_arena_dump,
            &with_shadow.runtime_raw_arena_dump,
        );
        assert_eq!(
            with_shadow.runtime_boundary, self.runtime_boundary,
            "{case}: compiled runtime boundary diverged"
        );
        assert_eq!(
            with_shadow.runtime_labels, self.runtime_labels,
            "{case}: compiled runtime labels diverged"
        );
        assert_eq!(
            with_shadow.runtime_modules, self.runtime_modules,
            "{case}: compiled runtime modules diverged"
        );
        assert_eq!(
            with_shadow.runtime_values, self.runtime_values,
            "{case}: compiled runtime values diverged"
        );
    }
}

#[derive(Debug, PartialEq, Eq)]
struct GeneralizationRestartCensus {
    iterations: usize,
    merge_restarts: usize,
    subtype_restarts: usize,
    cast_restarts: usize,
    role_restarts: usize,
    roots_with_restarts: usize,
    max_iterations_per_root: usize,
    max_restarts_per_root: usize,
    top_root: Option<DefId>,
    top_iterations: usize,
    top_constraint_epoch_start: u64,
    top_constraint_epoch_end: u64,
    top_role_epoch_start: u64,
    top_role_epoch_end: u64,
    top_total_restarts: usize,
    top_merge_restarts: usize,
    top_subtype_restarts: usize,
    top_cast_restarts: usize,
    top_role_restarts: usize,
}

impl GeneralizationRestartCensus {
    fn from_timing(timing: crate::analysis::AnalysisTiming) -> Self {
        Self {
            iterations: timing.generalize_iterations,
            merge_restarts: timing.generalize_merge_restarts,
            subtype_restarts: timing.generalize_subtype_restarts,
            cast_restarts: timing.generalize_cast_restarts,
            role_restarts: timing.generalize_role_restarts,
            roots_with_restarts: timing.quantify_generalize_roots_with_restarts,
            max_iterations_per_root: timing.quantify_generalize_max_iterations_per_root,
            max_restarts_per_root: timing.quantify_generalize_max_restarts_per_root,
            top_root: timing.generalize_top_restart_root,
            top_iterations: timing.generalize_top_restart_iterations,
            top_constraint_epoch_start: timing.generalize_top_restart_constraint_epoch_start,
            top_constraint_epoch_end: timing.generalize_top_restart_constraint_epoch_end,
            top_role_epoch_start: timing.generalize_top_restart_role_epoch_start,
            top_role_epoch_end: timing.generalize_top_restart_role_epoch_end,
            top_total_restarts: timing.generalize_top_restart_total_restarts,
            top_merge_restarts: timing.generalize_top_restart_merge_restarts,
            top_subtype_restarts: timing.generalize_top_restart_subtype_restarts,
            top_cast_restarts: timing.generalize_top_restart_cast_restarts,
            top_role_restarts: timing.generalize_top_restart_role_restarts,
        }
    }
}

fn assert_text_eq(case: &str, dimension: &str, without_shadow: &str, with_shadow: &str) {
    if without_shadow == with_shadow {
        return;
    }
    let line = without_shadow
        .lines()
        .zip(with_shadow.lines())
        .position(|(without_shadow, with_shadow)| without_shadow != with_shadow)
        .unwrap_or_else(|| {
            without_shadow
                .lines()
                .count()
                .min(with_shadow.lines().count())
        });
    let without_shadow_line = without_shadow.lines().nth(line).unwrap_or("<end>");
    let with_shadow_line = with_shadow.lines().nth(line).unwrap_or("<end>");
    panic!(
        "{case}: {dimension} diverged at line {}\nwithout shadow: {without_shadow_line}\nwith shadow: {with_shadow_line}",
        line + 1,
    );
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
                    "generalize snapshot proof-boundary {case}: iteration={} epoch={:?} supplemental-epoch={:?} candidate={:?} demands={} new={} exact-repeat={} main={{debug-bytes:{}, nodes:{}}} pending={{constraint-work:{}, constraint-events:{}, analysis-work:{}}}",
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
