//! Test-only exact-snapshot characterization for generalization role solving.
//!
//! Every production solve still runs. This oracle retains exact E/M/D/C/A-shaped snapshots only to
//! measure repeat opportunities, structural equality cost, cloning cost, and bounded-lifetime
//! storage. Debug byte lengths are an explicit structural proxy, not allocator-retained bytes.

#![allow(
    dead_code,
    reason = "the characterization report intentionally exposes raw measurement dimensions"
)]

use super::*;

use std::cell::Cell;
use std::mem::size_of;

use crate::constraints::RoleSolveSupplementalEpoch;
use crate::role_solve::{
    PureRoleDemandObservation, PureRoleDemandOutcome, RoleDemandDisposition,
    RoleResolveDispositionOutput, ShadowRoleDemandApplication, apply_pure_role_demand_outcome,
    shadow_applications_from_full_solve,
};

thread_local! {
    static ENABLE_NEW_ORACLES: Cell<bool> = const { Cell::new(false) };
}

#[derive(Debug, Clone, Default)]
pub(crate) struct GeneralizeSnapshotCharacterizationReport {
    pub(crate) roots: Vec<GeneralizeSnapshotRootReport>,
}

impl GeneralizeSnapshotCharacterizationReport {
    pub(crate) fn root(&self, def: DefId) -> Option<&GeneralizeSnapshotRootReport> {
        self.roots.iter().find(|root| root.def == def)
    }
}

#[derive(Debug, Clone)]
pub(crate) struct GeneralizeSnapshotRootReport {
    pub(crate) def: DefId,
    pub(crate) loop_iterations: usize,
    pub(crate) solve_boundaries: Vec<GeneralizeSnapshotSolveBoundary>,
    pub(crate) demands: Vec<GeneralizeSnapshotDemandReport>,
    pub(crate) exact_repeats: usize,
    pub(crate) necessary_solves: usize,
    pub(crate) exact_repeat_solve_time: Duration,
    pub(crate) necessary_solve_time: Duration,
    pub(crate) full_batch_solve_time: Duration,
    pub(crate) comparison_cost: GeneralizeSnapshotComparisonCost,
    pub(crate) clone_cost: GeneralizeSnapshotCloneCost,
    pub(crate) retention_accounting_time: Duration,
    pub(crate) peak_entries: usize,
    pub(crate) peak_retained_debug_bytes: usize,
    pub(crate) peak_retained_main_nodes: usize,
    pub(crate) would_be_hits: usize,
    pub(crate) exact_result_mismatches: usize,
    pub(crate) shadow_disposition_mismatches: usize,
    pub(crate) shadow_state_delta_mismatches: usize,
    pub(crate) shadow_full_path_mismatches: usize,
    pub(crate) boundaries_with_pending_constraint_work: usize,
    pub(crate) boundaries_with_pending_constraint_events: usize,
    pub(crate) boundaries_with_pending_analysis_work: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct GeneralizeSnapshotSolveBoundary {
    pub(crate) iteration: usize,
    pub(crate) constraint_epoch: ConstraintEpoch,
    pub(crate) role_solve_supplemental_epoch: RoleSolveSupplementalEpoch,
    pub(crate) candidate_guard: u64,
    pub(crate) demand_count: usize,
    pub(crate) new_resolution_count: usize,
    pub(crate) exact_repeat_count: usize,
    pub(crate) batch_solve_time: Duration,
    pub(crate) main_debug_bytes: usize,
    pub(crate) main_nodes: usize,
    pub(crate) pending_constraint_work: usize,
    pub(crate) pending_constraint_events: usize,
    pub(crate) pending_analysis_work: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct GeneralizeSnapshotDemandReport {
    pub(crate) slot: usize,
    pub(crate) role: Vec<String>,
    pub(crate) solves: usize,
    pub(crate) exact_repeats: usize,
    pub(crate) necessary_solves: usize,
    pub(crate) exact_repeat_solve_time: Duration,
    pub(crate) necessary_solve_time: Duration,
    pub(crate) max_demand_debug_bytes: usize,
    pub(crate) max_result_debug_bytes: usize,
    pub(crate) observations: Vec<GeneralizeSnapshotDemandSolve>,
}

#[derive(Debug, Clone)]
pub(crate) struct GeneralizeSnapshotDemandSolve {
    pub(crate) iteration: usize,
    pub(crate) boundary_eligible: bool,
    pub(crate) would_be_hit: bool,
    pub(crate) exact_repeat: bool,
    pub(crate) demand_equal: bool,
    pub(crate) epoch_equal: bool,
    pub(crate) supplemental_epoch_equal: bool,
    pub(crate) main_equal: bool,
    pub(crate) candidate_guard_equal: bool,
    pub(crate) result_equal: bool,
    pub(crate) disposition_equal: bool,
    pub(crate) state_delta_equal: bool,
    pub(crate) full_path_equal: bool,
    pub(crate) solve_time: Duration,
    pub(crate) disposition: &'static str,
    pub(crate) candidate_bucket_count: usize,
}

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct GeneralizeSnapshotComparisonCost {
    pub(crate) demand_comparisons: usize,
    pub(crate) demand_time: Duration,
    pub(crate) epoch_comparisons: usize,
    pub(crate) epoch_time: Duration,
    pub(crate) main_comparisons: usize,
    pub(crate) main_time: Duration,
    pub(crate) candidate_guard_comparisons: usize,
    pub(crate) candidate_guard_time: Duration,
    pub(crate) result_comparisons: usize,
    pub(crate) result_time: Duration,
    pub(crate) fresh_applied_filters: usize,
    pub(crate) fresh_applied_filter_time: Duration,
    pub(crate) disposition_comparisons: usize,
    pub(crate) disposition_time: Duration,
    pub(crate) state_delta_comparisons: usize,
    pub(crate) state_delta_time: Duration,
}

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct GeneralizeSnapshotCloneCost {
    pub(crate) snapshots: usize,
    pub(crate) main_time: Duration,
    pub(crate) demand_time: Duration,
    pub(crate) result_time: Duration,
}

#[derive(Debug, Default)]
pub(crate) struct GeneralizeSnapshotCharacterizationOracle {
    roots: Vec<GeneralizeSnapshotRootReport>,
}

impl GeneralizeSnapshotCharacterizationOracle {
    pub(crate) fn for_new_session() -> Option<Self> {
        ENABLE_NEW_ORACLES.with(Cell::get).then(Self::default)
    }

    pub(crate) fn publish(&mut self, root: GeneralizeSnapshotRootObservation) {
        self.roots.push(root.finish());
    }

    fn report(&self) -> GeneralizeSnapshotCharacterizationReport {
        GeneralizeSnapshotCharacterizationReport {
            roots: self.roots.clone(),
        }
    }
}

pub(crate) fn with_generalize_snapshot_characterization_for_new_sessions<T>(
    run: impl FnOnce() -> T,
) -> T {
    ENABLE_NEW_ORACLES.with(|enabled| {
        let previous = enabled.replace(true);
        struct Restore<'a> {
            enabled: &'a Cell<bool>,
            previous: bool,
        }
        impl Drop for Restore<'_> {
            fn drop(&mut self) {
                self.enabled.set(self.previous);
            }
        }
        let _restore = Restore { enabled, previous };
        run()
    })
}

pub(crate) struct GeneralizeSnapshotRootObservation {
    def: DefId,
    loop_iterations: usize,
    entries: Vec<ExactSnapshotEntry>,
    demand_identities: Vec<CompactRoleConstraint>,
    demands: Vec<GeneralizeSnapshotDemandReport>,
    solve_boundaries: Vec<GeneralizeSnapshotSolveBoundary>,
    exact_repeats: usize,
    necessary_solves: usize,
    exact_repeat_solve_time: Duration,
    necessary_solve_time: Duration,
    full_batch_solve_time: Duration,
    comparison_cost: GeneralizeSnapshotComparisonCost,
    clone_cost: GeneralizeSnapshotCloneCost,
    retention_accounting_time: Duration,
    retained_debug_bytes: usize,
    retained_main_nodes: usize,
    peak_entries: usize,
    peak_retained_debug_bytes: usize,
    peak_retained_main_nodes: usize,
    would_be_hits: usize,
    exact_result_mismatches: usize,
    shadow_disposition_mismatches: usize,
    shadow_state_delta_mismatches: usize,
    shadow_full_path_mismatches: usize,
    boundaries_with_pending_constraint_work: usize,
    boundaries_with_pending_constraint_events: usize,
    boundaries_with_pending_analysis_work: usize,
}

impl GeneralizeSnapshotRootObservation {
    pub(crate) fn new(def: DefId) -> Self {
        Self {
            def,
            loop_iterations: 0,
            entries: Vec::new(),
            demand_identities: Vec::new(),
            demands: Vec::new(),
            solve_boundaries: Vec::new(),
            exact_repeats: 0,
            necessary_solves: 0,
            exact_repeat_solve_time: Duration::ZERO,
            necessary_solve_time: Duration::ZERO,
            full_batch_solve_time: Duration::ZERO,
            comparison_cost: GeneralizeSnapshotComparisonCost::default(),
            clone_cost: GeneralizeSnapshotCloneCost::default(),
            retention_accounting_time: Duration::ZERO,
            retained_debug_bytes: 0,
            retained_main_nodes: 0,
            peak_entries: 0,
            peak_retained_debug_bytes: 0,
            peak_retained_main_nodes: 0,
            would_be_hits: 0,
            exact_result_mismatches: 0,
            shadow_disposition_mismatches: 0,
            shadow_state_delta_mismatches: 0,
            shadow_full_path_mismatches: 0,
            boundaries_with_pending_constraint_work: 0,
            boundaries_with_pending_constraint_events: 0,
            boundaries_with_pending_analysis_work: 0,
        }
    }

    pub(crate) fn record_loop_iteration(&mut self, iteration: usize) {
        self.loop_iterations = self.loop_iterations.max(iteration);
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn observe_solve_boundary(
        &mut self,
        iteration: usize,
        constraint_epoch: ConstraintEpoch,
        role_solve_supplemental_epoch: RoleSolveSupplementalEpoch,
        candidate_guard: u64,
        main: &CompactRoot,
        normalized_demands: &[CompactRoleConstraint],
        pure: &[PureRoleDemandObservation],
        resolved: &RoleResolveDispositionOutput,
        applied: &FxHashSet<crate::role_solve::RoleResolutionKey>,
        batch_solve_time: Duration,
        pending_constraint_work: usize,
        pending_constraint_events: usize,
        pending_analysis_work: usize,
    ) {
        assert_eq!(normalized_demands.len(), pure.len());
        assert_eq!(normalized_demands.len(), resolved.dispositions.len());
        self.full_batch_solve_time += batch_solve_time;
        self.boundaries_with_pending_constraint_work += usize::from(pending_constraint_work > 0);
        self.boundaries_with_pending_constraint_events +=
            usize::from(pending_constraint_events > 0);
        self.boundaries_with_pending_analysis_work += usize::from(pending_analysis_work > 0);

        let main_debug_bytes = format!("{main:?}").len();
        let main_nodes = super::compact_shape_metrics(main).nodes;
        let boundary_eligible = constraint_epoch.can_witness_unchanged_state()
            && role_solve_supplemental_epoch.can_witness_unchanged_state()
            && pending_constraint_work == 0
            && pending_constraint_events == 0;
        let full_applications = shadow_applications_from_full_solve(
            &resolved.dispositions,
            &resolved.output.resolutions,
        );
        let mut boundary_exact_repeats = 0;
        for (index, ((demand, pure), disposition)) in normalized_demands
            .iter()
            .zip(pure)
            .zip(&resolved.dispositions)
            .enumerate()
        {
            assert_eq!(demand, &pure.demand);
            let observation = self.observe_demand(
                iteration,
                constraint_epoch,
                role_solve_supplemental_epoch,
                candidate_guard,
                main,
                main_nodes,
                pure,
                disposition,
                full_applications
                    .as_ref()
                    .and_then(|applications| applications.get(index)),
                applied,
                boundary_eligible,
            );
            boundary_exact_repeats += usize::from(observation.exact_repeat);
        }
        self.solve_boundaries.push(GeneralizeSnapshotSolveBoundary {
            iteration,
            constraint_epoch,
            role_solve_supplemental_epoch,
            candidate_guard,
            demand_count: normalized_demands.len(),
            new_resolution_count: resolved.output.resolutions.len(),
            exact_repeat_count: boundary_exact_repeats,
            batch_solve_time,
            main_debug_bytes,
            main_nodes,
            pending_constraint_work,
            pending_constraint_events,
            pending_analysis_work,
        });
    }

    #[allow(clippy::too_many_arguments)]
    fn observe_demand(
        &mut self,
        iteration: usize,
        constraint_epoch: ConstraintEpoch,
        role_solve_supplemental_epoch: RoleSolveSupplementalEpoch,
        candidate_guard: u64,
        main: &CompactRoot,
        main_nodes: usize,
        pure: &PureRoleDemandObservation,
        disposition: &RoleDemandDisposition,
        full_application: Option<&ShadowRoleDemandApplication>,
        applied: &FxHashSet<crate::role_solve::RoleResolutionKey>,
        boundary_eligible: bool,
    ) -> GeneralizeSnapshotDemandSolve {
        let mut matching_index = None;
        for (index, entry) in self.entries.iter().enumerate() {
            let started = Instant::now();
            let equal = entry.demand == pure.demand;
            self.comparison_cost.demand_time += started.elapsed();
            self.comparison_cost.demand_comparisons += 1;
            if equal {
                matching_index = Some(index);
                break;
            }
        }

        let demand_equal = matching_index.is_some();
        let mut epoch_equal = false;
        let mut supplemental_epoch_equal = false;
        let mut main_equal = false;
        let mut candidate_guard_equal = false;
        let mut result_equal = false;
        let mut disposition_equal = false;
        let mut state_delta_equal = false;
        let mut full_path_equal = false;
        if let Some(index) = matching_index {
            let entry = &self.entries[index];
            let started = Instant::now();
            epoch_equal = entry.constraint_epoch == constraint_epoch;
            supplemental_epoch_equal =
                entry.role_solve_supplemental_epoch == role_solve_supplemental_epoch;
            self.comparison_cost.epoch_time += started.elapsed();
            self.comparison_cost.epoch_comparisons += 1;

            let started = Instant::now();
            main_equal = entry.main == *main;
            self.comparison_cost.main_time += started.elapsed();
            self.comparison_cost.main_comparisons += 1;

            let started = Instant::now();
            candidate_guard_equal = entry.candidate_guard == candidate_guard;
            self.comparison_cost.candidate_guard_time += started.elapsed();
            self.comparison_cost.candidate_guard_comparisons += 1;

            let would_be_hit = boundary_eligible
                && epoch_equal
                && supplemental_epoch_equal
                && main_equal
                && candidate_guard_equal;
            if would_be_hit {
                self.would_be_hits += 1;
                let started = Instant::now();
                result_equal = entry.result == pure.outcome;
                self.comparison_cost.result_time += started.elapsed();
                self.comparison_cost.result_comparisons += 1;
                self.exact_result_mismatches += usize::from(!result_equal);

                let started = Instant::now();
                let cached_application = apply_pure_role_demand_outcome(&entry.result, applied);
                let fresh_application = apply_pure_role_demand_outcome(&pure.outcome, applied);
                self.comparison_cost.fresh_applied_filter_time += started.elapsed();
                self.comparison_cost.fresh_applied_filters += 2;

                let started = Instant::now();
                disposition_equal = full_application
                    .is_some_and(|full| cached_application.disposition == full.disposition);
                self.comparison_cost.disposition_time += started.elapsed();
                self.comparison_cost.disposition_comparisons += 1;
                self.shadow_disposition_mismatches += usize::from(!disposition_equal);

                let started = Instant::now();
                state_delta_equal = full_application
                    .is_some_and(|full| cached_application.state_delta == full.state_delta);
                self.comparison_cost.state_delta_time += started.elapsed();
                self.comparison_cost.state_delta_comparisons += 1;
                self.shadow_state_delta_mismatches += usize::from(!state_delta_equal);

                full_path_equal = full_application.is_some_and(|full| fresh_application == *full);
                self.shadow_full_path_mismatches += usize::from(!full_path_equal);
            }
        }
        let would_be_hit = boundary_eligible
            && demand_equal
            && epoch_equal
            && supplemental_epoch_equal
            && main_equal
            && candidate_guard_equal;
        let exact_repeat = would_be_hit && result_equal;
        let exact_repeat =
            exact_repeat && disposition_equal && state_delta_equal && full_path_equal;

        let slot = if let Some(index) = matching_index {
            self.entries[index].slot
        } else if let Some(index) = self
            .demand_identities
            .iter()
            .position(|demand| demand == &pure.demand)
        {
            index
        } else {
            self.demands.len()
        };
        let demand_debug_bytes = format!("{:?}", pure.demand).len();
        let result_debug_bytes = format!("{:?}", pure.outcome).len();
        let demand_report = if let Some(report) = self.demands.get_mut(slot) {
            report
        } else {
            assert_eq!(slot, self.demands.len());
            self.demand_identities.push(pure.demand.clone());
            self.demands.push(GeneralizeSnapshotDemandReport {
                slot,
                role: pure.demand.role.clone(),
                solves: 0,
                exact_repeats: 0,
                necessary_solves: 0,
                exact_repeat_solve_time: Duration::ZERO,
                necessary_solve_time: Duration::ZERO,
                max_demand_debug_bytes: 0,
                max_result_debug_bytes: 0,
                observations: Vec::new(),
            });
            self.demands
                .last_mut()
                .expect("new demand report must be present")
        };
        demand_report.solves += 1;
        demand_report.max_demand_debug_bytes =
            demand_report.max_demand_debug_bytes.max(demand_debug_bytes);
        demand_report.max_result_debug_bytes =
            demand_report.max_result_debug_bytes.max(result_debug_bytes);
        if exact_repeat {
            self.exact_repeats += 1;
            self.exact_repeat_solve_time += pure.solve_time;
            demand_report.exact_repeats += 1;
            demand_report.exact_repeat_solve_time += pure.solve_time;
        } else {
            self.necessary_solves += 1;
            self.necessary_solve_time += pure.solve_time;
            demand_report.necessary_solves += 1;
            demand_report.necessary_solve_time += pure.solve_time;
        }
        let observation = GeneralizeSnapshotDemandSolve {
            iteration,
            boundary_eligible,
            would_be_hit,
            exact_repeat,
            demand_equal,
            epoch_equal,
            supplemental_epoch_equal,
            main_equal,
            candidate_guard_equal,
            result_equal,
            disposition_equal,
            state_delta_equal,
            full_path_equal,
            solve_time: pure.solve_time,
            disposition: disposition_name(disposition),
            candidate_bucket_count: pure.candidate_buckets.len(),
        };
        demand_report.observations.push(observation.clone());

        if !would_be_hit && boundary_eligible {
            self.retain_snapshot(
                matching_index,
                slot,
                constraint_epoch,
                role_solve_supplemental_epoch,
                candidate_guard,
                main,
                main_nodes,
                pure,
            );
        }
        observation
    }

    #[allow(clippy::too_many_arguments)]
    fn retain_snapshot(
        &mut self,
        matching_index: Option<usize>,
        slot: usize,
        constraint_epoch: ConstraintEpoch,
        role_solve_supplemental_epoch: RoleSolveSupplementalEpoch,
        candidate_guard: u64,
        main: &CompactRoot,
        main_nodes: usize,
        pure: &PureRoleDemandObservation,
    ) {
        let started = Instant::now();
        let main = main.clone();
        self.clone_cost.main_time += started.elapsed();
        let started = Instant::now();
        let demand = pure.demand.clone();
        self.clone_cost.demand_time += started.elapsed();
        let started = Instant::now();
        let result = pure.outcome.clone();
        self.clone_cost.result_time += started.elapsed();
        self.clone_cost.snapshots += 1;

        let accounting_started = Instant::now();
        let debug_bytes = size_of::<ConstraintEpoch>()
            + size_of::<RoleSolveSupplementalEpoch>()
            + size_of::<u64>()
            + format!("{main:?}").len()
            + format!("{demand:?}").len()
            + format!("{result:?}").len();
        self.retention_accounting_time += accounting_started.elapsed();
        let entry = ExactSnapshotEntry {
            slot,
            constraint_epoch,
            role_solve_supplemental_epoch,
            main,
            demand,
            candidate_guard,
            result,
            retained_debug_bytes: debug_bytes,
            retained_main_nodes: main_nodes,
        };
        let retained_index = if let Some(index) = matching_index {
            let previous = std::mem::replace(&mut self.entries[index], entry);
            self.retained_debug_bytes = self
                .retained_debug_bytes
                .saturating_sub(previous.retained_debug_bytes);
            self.retained_main_nodes = self
                .retained_main_nodes
                .saturating_sub(previous.retained_main_nodes);
            index
        } else {
            self.entries.push(entry);
            self.entries.len() - 1
        };
        let retained = &self.entries[retained_index];
        self.retained_debug_bytes = self
            .retained_debug_bytes
            .saturating_add(retained.retained_debug_bytes);
        self.retained_main_nodes = self
            .retained_main_nodes
            .saturating_add(retained.retained_main_nodes);
        self.peak_entries = self.peak_entries.max(self.entries.len());
        self.peak_retained_debug_bytes = self
            .peak_retained_debug_bytes
            .max(self.retained_debug_bytes);
        self.peak_retained_main_nodes = self.peak_retained_main_nodes.max(self.retained_main_nodes);
    }

    fn finish(self) -> GeneralizeSnapshotRootReport {
        GeneralizeSnapshotRootReport {
            def: self.def,
            loop_iterations: self.loop_iterations,
            solve_boundaries: self.solve_boundaries,
            demands: self.demands,
            exact_repeats: self.exact_repeats,
            necessary_solves: self.necessary_solves,
            exact_repeat_solve_time: self.exact_repeat_solve_time,
            necessary_solve_time: self.necessary_solve_time,
            full_batch_solve_time: self.full_batch_solve_time,
            comparison_cost: self.comparison_cost,
            clone_cost: self.clone_cost,
            retention_accounting_time: self.retention_accounting_time,
            peak_entries: self.peak_entries,
            peak_retained_debug_bytes: self.peak_retained_debug_bytes,
            peak_retained_main_nodes: self.peak_retained_main_nodes,
            would_be_hits: self.would_be_hits,
            exact_result_mismatches: self.exact_result_mismatches,
            shadow_disposition_mismatches: self.shadow_disposition_mismatches,
            shadow_state_delta_mismatches: self.shadow_state_delta_mismatches,
            shadow_full_path_mismatches: self.shadow_full_path_mismatches,
            boundaries_with_pending_constraint_work: self.boundaries_with_pending_constraint_work,
            boundaries_with_pending_constraint_events: self
                .boundaries_with_pending_constraint_events,
            boundaries_with_pending_analysis_work: self.boundaries_with_pending_analysis_work,
        }
    }
}

struct ExactSnapshotEntry {
    slot: usize,
    constraint_epoch: ConstraintEpoch,
    role_solve_supplemental_epoch: RoleSolveSupplementalEpoch,
    main: CompactRoot,
    demand: CompactRoleConstraint,
    candidate_guard: u64,
    result: PureRoleDemandOutcome,
    retained_debug_bytes: usize,
    retained_main_nodes: usize,
}

fn disposition_name(disposition: &RoleDemandDisposition) -> &'static str {
    match disposition {
        RoleDemandDisposition::NewlyResolved { .. } => "newly-resolved",
        RoleDemandDisposition::AlreadyApplied { .. } => "already-applied",
        RoleDemandDisposition::Unresolved { .. } => "unresolved",
    }
}

impl AnalysisSession {
    pub(crate) fn generalize_snapshot_characterization_report(
        &self,
    ) -> Option<GeneralizeSnapshotCharacterizationReport> {
        self.generalize_snapshot_characterization
            .as_ref()
            .map(GeneralizeSnapshotCharacterizationOracle::report)
    }
}
