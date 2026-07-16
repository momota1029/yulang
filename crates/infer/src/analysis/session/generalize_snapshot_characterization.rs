//! Independent test-only exact-snapshot audit for generalization role solving.
//!
//! The audit scope forces the always-full-solve control, then retains its own E/M/D/C/A-shaped
//! snapshots to compare every would-be hit with the fresh recursive result. Debug byte lengths are
//! an explicit structural proxy, not allocator-retained bytes.

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

/// Stage 0 observed at most 6 entries in one root. The owner scheduler's established 8-10x
/// practice therefore rounds this loop-local limit up to 64 entries.
const MAX_RETAINED_SNAPSHOT_ENTRIES: usize = 64;

/// Stage 0's structural retained-byte proxy peaked at 20,653,120 bytes. 128 MiB leaves about 6.5x
/// headroom while still placing an absolute bound around the large owned compact trees seen in the
/// Markdown witness.
const MAX_RETAINED_SNAPSHOT_DEBUG_BYTES: usize = 128 * 1024 * 1024;

const SNAPSHOT_MISS_REASON_COUNT: usize = 14;

thread_local! {
    static ENABLE_NEW_ORACLES: Cell<bool> = const { Cell::new(false) };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GeneralizeSnapshotConstraintEpoch {
    Witness(ConstraintEpoch),
    Unavailable,
}

impl GeneralizeSnapshotConstraintEpoch {
    pub(crate) fn capture(epoch: ConstraintEpoch) -> Self {
        if epoch.can_witness_unchanged_state() {
            Self::Witness(epoch)
        } else {
            Self::Unavailable
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GeneralizeSnapshotSupplementalEpoch {
    Witness(RoleSolveSupplementalEpoch),
    Unavailable,
}

impl GeneralizeSnapshotSupplementalEpoch {
    pub(crate) fn capture(epoch: RoleSolveSupplementalEpoch) -> Self {
        if epoch.can_witness_unchanged_state() {
            Self::Witness(epoch)
        } else {
            Self::Unavailable
        }
    }
}

/// The test-only generation is complete because every mutation API for `IndexedRoleImplTable`
/// advances it. `Unavailable` represents a future boundary where that invariant cannot be proven;
/// `Overflowed` prevents a saturated generation from authorizing equality forever.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GeneralizeSnapshotCandidateGuard {
    Generation(u64),
    Unavailable,
    Overflowed,
}

impl GeneralizeSnapshotCandidateGuard {
    pub(crate) fn capture_generation(generation: u64) -> Self {
        if generation == u64::MAX {
            Self::Overflowed
        } else {
            Self::Generation(generation)
        }
    }
}

#[repr(usize)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GeneralizeSnapshotMissReason {
    ConstraintEpochUnwitnessable,
    SupplementalEpochUnwitnessable,
    PendingConstraintWork,
    PendingConstraintEvents,
    CandidateGuardUnavailable,
    CandidateGuardOverflow,
    BudgetExhausted,
    DemandMismatch,
    IncompleteEntry,
    ConstraintEpochMismatch,
    SupplementalEpochMismatch,
    MainMismatch,
    CandidateGuardMismatch,
    ShadowVerificationMismatch,
}

impl GeneralizeSnapshotMissReason {
    fn index(self) -> usize {
        self as usize
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct GeneralizeSnapshotMissReasonCounts {
    counts: [usize; SNAPSHOT_MISS_REASON_COUNT],
}

impl GeneralizeSnapshotMissReasonCounts {
    fn record(&mut self, reason: GeneralizeSnapshotMissReason) {
        self.counts[reason.index()] += 1;
    }

    pub(crate) fn count(&self, reason: GeneralizeSnapshotMissReason) -> usize {
        self.counts[reason.index()]
    }
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
    pub(crate) retained_entries_at_finish: usize,
    pub(crate) retained_debug_bytes_at_finish: usize,
    pub(crate) cap_exhaustions: usize,
    pub(crate) miss_reasons: GeneralizeSnapshotMissReasonCounts,
    pub(crate) would_be_hits: usize,
    pub(crate) exact_result_mismatches: usize,
    pub(crate) shadow_disposition_mismatches: usize,
    pub(crate) shadow_state_delta_mismatches: usize,
    pub(crate) shadow_full_path_mismatches: usize,
    pub(crate) boundaries_with_pending_constraint_work: usize,
    pub(crate) boundaries_with_pending_constraint_events: usize,
    pub(crate) boundaries_with_pending_analysis_work: usize,
}

impl GeneralizeSnapshotRootReport {
    pub(crate) fn epoch_misses(&self) -> usize {
        self.miss_reasons
            .count(GeneralizeSnapshotMissReason::ConstraintEpochUnwitnessable)
            + self
                .miss_reasons
                .count(GeneralizeSnapshotMissReason::ConstraintEpochMismatch)
    }

    pub(crate) fn supplemental_epoch_misses(&self) -> usize {
        self.miss_reasons
            .count(GeneralizeSnapshotMissReason::SupplementalEpochUnwitnessable)
            + self
                .miss_reasons
                .count(GeneralizeSnapshotMissReason::SupplementalEpochMismatch)
    }

    pub(crate) fn main_misses(&self) -> usize {
        self.miss_reasons
            .count(GeneralizeSnapshotMissReason::MainMismatch)
    }

    pub(crate) fn demand_misses(&self) -> usize {
        self.miss_reasons
            .count(GeneralizeSnapshotMissReason::DemandMismatch)
    }

    pub(crate) fn candidate_misses(&self) -> usize {
        self.miss_reasons
            .count(GeneralizeSnapshotMissReason::CandidateGuardUnavailable)
            + self
                .miss_reasons
                .count(GeneralizeSnapshotMissReason::CandidateGuardOverflow)
            + self
                .miss_reasons
                .count(GeneralizeSnapshotMissReason::CandidateGuardMismatch)
    }

    pub(crate) fn cap_misses(&self) -> usize {
        self.miss_reasons
            .count(GeneralizeSnapshotMissReason::BudgetExhausted)
    }

    pub(crate) fn lifecycle_misses(&self) -> usize {
        self.miss_reasons
            .count(GeneralizeSnapshotMissReason::PendingConstraintWork)
            + self
                .miss_reasons
                .count(GeneralizeSnapshotMissReason::PendingConstraintEvents)
            + self
                .miss_reasons
                .count(GeneralizeSnapshotMissReason::IncompleteEntry)
    }
}

#[derive(Debug, Clone)]
pub(crate) struct GeneralizeSnapshotSolveBoundary {
    pub(crate) iteration: usize,
    pub(crate) constraint_epoch: GeneralizeSnapshotConstraintEpoch,
    pub(crate) role_solve_supplemental_epoch: GeneralizeSnapshotSupplementalEpoch,
    pub(crate) candidate_guard: GeneralizeSnapshotCandidateGuard,
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
    pub(crate) miss_reason: Option<GeneralizeSnapshotMissReason>,
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
    // The independent audit must always observe a fresh full solve. Production activation is
    // verified separately through isolated enabled/always-solve parity, so this scope disables
    // production reuse while retaining the Stage 1 oracle as an independent result comparison.
    with_generalize_role_snapshot_always_solve_for_new_sessions(|| {
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
    })
}

#[derive(Debug, Clone, Copy)]
struct GeneralizeSnapshotBudget {
    max_entries: usize,
    max_retained_debug_bytes: usize,
}

impl Default for GeneralizeSnapshotBudget {
    fn default() -> Self {
        Self {
            max_entries: MAX_RETAINED_SNAPSHOT_ENTRIES,
            max_retained_debug_bytes: MAX_RETAINED_SNAPSHOT_DEBUG_BYTES,
        }
    }
}

#[derive(Default)]
struct GeneralizeSnapshotDemandComparison {
    matching_index: Option<usize>,
    demand_equal: bool,
    epoch_equal: bool,
    supplemental_epoch_equal: bool,
    main_equal: bool,
    candidate_guard_equal: bool,
    result_equal: bool,
    disposition_equal: bool,
    state_delta_equal: bool,
    full_path_equal: bool,
    would_be_hit: bool,
    exact_repeat: bool,
    boundary_miss_reason: Option<GeneralizeSnapshotMissReason>,
    miss_reason: Option<GeneralizeSnapshotMissReason>,
}

pub(crate) struct GeneralizeSnapshotRootObservation {
    def: DefId,
    loop_iterations: usize,
    budget: GeneralizeSnapshotBudget,
    reuse_disabled: Option<GeneralizeSnapshotMissReason>,
    entries: Vec<ExactSnapshotEntry>,
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
    cap_exhaustions: usize,
    miss_reasons: GeneralizeSnapshotMissReasonCounts,
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
        Self::with_budget(def, GeneralizeSnapshotBudget::default())
    }

    fn with_budget(def: DefId, budget: GeneralizeSnapshotBudget) -> Self {
        Self {
            def,
            loop_iterations: 0,
            budget,
            reuse_disabled: None,
            entries: Vec::new(),
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
            cap_exhaustions: 0,
            miss_reasons: GeneralizeSnapshotMissReasonCounts::default(),
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
        constraint_epoch: GeneralizeSnapshotConstraintEpoch,
        role_solve_supplemental_epoch: GeneralizeSnapshotSupplementalEpoch,
        candidate_guard: GeneralizeSnapshotCandidateGuard,
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
        let boundary_miss_reason = boundary_miss_reason(
            constraint_epoch,
            role_solve_supplemental_epoch,
            candidate_guard,
            pending_constraint_work,
            pending_constraint_events,
        );
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
                main_debug_bytes,
                boundary_miss_reason,
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
        constraint_epoch: GeneralizeSnapshotConstraintEpoch,
        role_solve_supplemental_epoch: GeneralizeSnapshotSupplementalEpoch,
        candidate_guard: GeneralizeSnapshotCandidateGuard,
        main: &CompactRoot,
        main_nodes: usize,
        pure: &PureRoleDemandObservation,
        disposition: &RoleDemandDisposition,
        full_application: Option<&ShadowRoleDemandApplication>,
        applied: &FxHashSet<crate::role_solve::RoleResolutionKey>,
        main_debug_bytes: usize,
        boundary_miss_reason: Option<GeneralizeSnapshotMissReason>,
    ) -> GeneralizeSnapshotDemandSolve {
        let mut comparison = GeneralizeSnapshotDemandComparison {
            boundary_miss_reason,
            miss_reason: self.reuse_disabled.or(boundary_miss_reason),
            ..GeneralizeSnapshotDemandComparison::default()
        };
        if comparison.miss_reason.is_none() {
            for (index, entry) in self.entries.iter().enumerate() {
                let started = Instant::now();
                let equal = entry.demand == pure.demand;
                self.comparison_cost.demand_time += started.elapsed();
                self.comparison_cost.demand_comparisons += 1;
                if equal {
                    comparison.matching_index = Some(index);
                    break;
                }
            }
        }
        comparison.demand_equal = comparison.matching_index.is_some();

        if comparison.miss_reason.is_none()
            && let Some(index) = comparison.matching_index
        {
            let entry = &self.entries[index];
            let Some(cached_result) = entry.result.complete() else {
                comparison.miss_reason = Some(GeneralizeSnapshotMissReason::IncompleteEntry);
                return self.finish_demand_observation(
                    iteration,
                    constraint_epoch,
                    role_solve_supplemental_epoch,
                    candidate_guard,
                    main,
                    main_nodes,
                    main_debug_bytes,
                    pure,
                    disposition,
                    comparison,
                );
            };
            if let (
                GeneralizeSnapshotConstraintEpoch::Witness(current_constraint_epoch),
                GeneralizeSnapshotSupplementalEpoch::Witness(current_supplemental_epoch),
                GeneralizeSnapshotCandidateGuard::Generation(current_candidate_generation),
            ) = (
                constraint_epoch,
                role_solve_supplemental_epoch,
                candidate_guard,
            ) {
                let started = Instant::now();
                comparison.epoch_equal = entry.constraint_epoch == current_constraint_epoch;
                comparison.supplemental_epoch_equal =
                    entry.role_solve_supplemental_epoch == current_supplemental_epoch;
                self.comparison_cost.epoch_time += started.elapsed();
                self.comparison_cost.epoch_comparisons += 1;

                let started = Instant::now();
                comparison.main_equal = entry.main == *main;
                self.comparison_cost.main_time += started.elapsed();
                self.comparison_cost.main_comparisons += 1;

                let started = Instant::now();
                comparison.candidate_guard_equal =
                    entry.candidate_generation == current_candidate_generation;
                self.comparison_cost.candidate_guard_time += started.elapsed();
                self.comparison_cost.candidate_guard_comparisons += 1;
            }

            comparison.miss_reason = if !comparison.epoch_equal {
                Some(GeneralizeSnapshotMissReason::ConstraintEpochMismatch)
            } else if !comparison.supplemental_epoch_equal {
                Some(GeneralizeSnapshotMissReason::SupplementalEpochMismatch)
            } else if !comparison.main_equal {
                Some(GeneralizeSnapshotMissReason::MainMismatch)
            } else if !comparison.candidate_guard_equal {
                Some(GeneralizeSnapshotMissReason::CandidateGuardMismatch)
            } else {
                None
            };

            if comparison.miss_reason.is_none() {
                comparison.would_be_hit = true;
                self.would_be_hits += 1;
                let started = Instant::now();
                comparison.result_equal = cached_result == &pure.outcome;
                self.comparison_cost.result_time += started.elapsed();
                self.comparison_cost.result_comparisons += 1;
                self.exact_result_mismatches += usize::from(!comparison.result_equal);

                let started = Instant::now();
                let cached_application = apply_pure_role_demand_outcome(cached_result, applied);
                let fresh_application = apply_pure_role_demand_outcome(&pure.outcome, applied);
                self.comparison_cost.fresh_applied_filter_time += started.elapsed();
                self.comparison_cost.fresh_applied_filters += 2;

                let started = Instant::now();
                comparison.disposition_equal = full_application
                    .is_some_and(|full| cached_application.disposition == full.disposition);
                self.comparison_cost.disposition_time += started.elapsed();
                self.comparison_cost.disposition_comparisons += 1;
                self.shadow_disposition_mismatches += usize::from(!comparison.disposition_equal);

                let started = Instant::now();
                comparison.state_delta_equal = full_application
                    .is_some_and(|full| cached_application.state_delta == full.state_delta);
                self.comparison_cost.state_delta_time += started.elapsed();
                self.comparison_cost.state_delta_comparisons += 1;
                self.shadow_state_delta_mismatches += usize::from(!comparison.state_delta_equal);

                comparison.full_path_equal =
                    full_application.is_some_and(|full| fresh_application == *full);
                self.shadow_full_path_mismatches += usize::from(!comparison.full_path_equal);

                comparison.exact_repeat = comparison.result_equal
                    && comparison.disposition_equal
                    && comparison.state_delta_equal
                    && comparison.full_path_equal;
                if comparison.exact_repeat {
                    comparison.miss_reason = None;
                } else {
                    comparison.miss_reason =
                        Some(GeneralizeSnapshotMissReason::ShadowVerificationMismatch);
                    self.disable_reuse(GeneralizeSnapshotMissReason::ShadowVerificationMismatch);
                }
            }
        } else if comparison.miss_reason.is_none() {
            comparison.miss_reason = Some(GeneralizeSnapshotMissReason::DemandMismatch);
        }

        self.finish_demand_observation(
            iteration,
            constraint_epoch,
            role_solve_supplemental_epoch,
            candidate_guard,
            main,
            main_nodes,
            main_debug_bytes,
            pure,
            disposition,
            comparison,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn finish_demand_observation(
        &mut self,
        iteration: usize,
        constraint_epoch: GeneralizeSnapshotConstraintEpoch,
        role_solve_supplemental_epoch: GeneralizeSnapshotSupplementalEpoch,
        candidate_guard: GeneralizeSnapshotCandidateGuard,
        main: &CompactRoot,
        main_nodes: usize,
        main_debug_bytes: usize,
        pure: &PureRoleDemandObservation,
        disposition: &RoleDemandDisposition,
        mut comparison: GeneralizeSnapshotDemandComparison,
    ) -> GeneralizeSnapshotDemandSolve {
        let slot = comparison
            .matching_index
            .and_then(|index| self.entries.get(index).map(|entry| entry.slot))
            .unwrap_or(self.demands.len());
        let demand_debug_bytes = format!("{:?}", pure.demand).len();
        let result_debug_bytes = format!("{:?}", pure.outcome).len();

        if !comparison.would_be_hit
            && comparison.boundary_miss_reason.is_none()
            && self.reuse_disabled.is_none()
            && !self.retain_snapshot(
                comparison.matching_index,
                slot,
                constraint_epoch,
                role_solve_supplemental_epoch,
                candidate_guard,
                main,
                main_nodes,
                main_debug_bytes,
                demand_debug_bytes,
                result_debug_bytes,
                pure,
            )
        {
            comparison.miss_reason = Some(GeneralizeSnapshotMissReason::BudgetExhausted);
        }

        if let Some(reason) = comparison.miss_reason {
            self.miss_reasons.record(reason);
        }
        let boundary_eligible =
            self.reuse_disabled.is_none() && comparison.boundary_miss_reason.is_none();
        let demand_report = if let Some(report) = self.demands.get_mut(slot) {
            report
        } else {
            assert_eq!(slot, self.demands.len());
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
        if comparison.exact_repeat {
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
            would_be_hit: comparison.would_be_hit,
            miss_reason: comparison.miss_reason,
            exact_repeat: comparison.exact_repeat,
            demand_equal: comparison.demand_equal,
            epoch_equal: comparison.epoch_equal,
            supplemental_epoch_equal: comparison.supplemental_epoch_equal,
            main_equal: comparison.main_equal,
            candidate_guard_equal: comparison.candidate_guard_equal,
            result_equal: comparison.result_equal,
            disposition_equal: comparison.disposition_equal,
            state_delta_equal: comparison.state_delta_equal,
            full_path_equal: comparison.full_path_equal,
            solve_time: pure.solve_time,
            disposition: disposition_name(disposition),
            candidate_bucket_count: pure.candidate_buckets.len(),
        };
        demand_report.observations.push(observation.clone());
        observation
    }

    #[allow(clippy::too_many_arguments)]
    fn retain_snapshot(
        &mut self,
        matching_index: Option<usize>,
        slot: usize,
        constraint_epoch: GeneralizeSnapshotConstraintEpoch,
        role_solve_supplemental_epoch: GeneralizeSnapshotSupplementalEpoch,
        candidate_guard: GeneralizeSnapshotCandidateGuard,
        main: &CompactRoot,
        main_nodes: usize,
        main_debug_bytes: usize,
        demand_debug_bytes: usize,
        result_debug_bytes: usize,
        pure: &PureRoleDemandObservation,
    ) -> bool {
        let (
            GeneralizeSnapshotConstraintEpoch::Witness(constraint_epoch),
            GeneralizeSnapshotSupplementalEpoch::Witness(role_solve_supplemental_epoch),
            GeneralizeSnapshotCandidateGuard::Generation(candidate_generation),
        ) = (
            constraint_epoch,
            role_solve_supplemental_epoch,
            candidate_guard,
        )
        else {
            return false;
        };

        let accounting_started = Instant::now();
        let debug_bytes = [
            size_of::<ConstraintEpoch>(),
            size_of::<RoleSolveSupplementalEpoch>(),
            size_of::<GeneralizeSnapshotCandidateGuard>(),
            main_debug_bytes,
            demand_debug_bytes,
            result_debug_bytes,
        ]
        .into_iter()
        .try_fold(0usize, usize::checked_add);
        let previous_debug_bytes = matching_index
            .and_then(|index| self.entries.get(index))
            .map(|entry| entry.retained_debug_bytes)
            .unwrap_or(0);
        let projected_entries = if matching_index.is_some() {
            Some(self.entries.len())
        } else {
            self.entries.len().checked_add(1)
        };
        let projected_debug_bytes = debug_bytes.and_then(|debug_bytes| {
            self.retained_debug_bytes
                .checked_sub(previous_debug_bytes)
                .and_then(|retained| retained.checked_add(debug_bytes))
        });
        self.retention_accounting_time += accounting_started.elapsed();
        let within_budget =
            projected_entries
                .zip(projected_debug_bytes)
                .is_some_and(|(entries, bytes)| {
                    entries <= self.budget.max_entries
                        && bytes <= self.budget.max_retained_debug_bytes
                });
        if !within_budget {
            self.cap_exhaustions += 1;
            self.disable_reuse(GeneralizeSnapshotMissReason::BudgetExhausted);
            return false;
        }

        let started = Instant::now();
        let main = main.clone();
        self.clone_cost.main_time += started.elapsed();
        let started = Instant::now();
        let demand = pure.demand.clone();
        self.clone_cost.demand_time += started.elapsed();
        let started = Instant::now();
        let result = ExactSnapshotResult::Complete(pure.outcome.clone());
        self.clone_cost.result_time += started.elapsed();
        self.clone_cost.snapshots += 1;

        let debug_bytes = debug_bytes.expect("validated snapshot byte projection");
        let entry = ExactSnapshotEntry {
            slot,
            constraint_epoch,
            role_solve_supplemental_epoch,
            main,
            demand,
            candidate_generation,
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
        true
    }

    fn disable_reuse(&mut self, reason: GeneralizeSnapshotMissReason) {
        self.entries.clear();
        self.retained_debug_bytes = 0;
        self.retained_main_nodes = 0;
        self.reuse_disabled = Some(reason);
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
            retained_entries_at_finish: self.entries.len(),
            retained_debug_bytes_at_finish: self.retained_debug_bytes,
            cap_exhaustions: self.cap_exhaustions,
            miss_reasons: self.miss_reasons,
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
    candidate_generation: u64,
    result: ExactSnapshotResult,
    retained_debug_bytes: usize,
    retained_main_nodes: usize,
}

enum ExactSnapshotResult {
    Complete(PureRoleDemandOutcome),
    Incomplete,
}

impl ExactSnapshotResult {
    fn complete(&self) -> Option<&PureRoleDemandOutcome> {
        match self {
            Self::Complete(result) => Some(result),
            Self::Incomplete => None,
        }
    }
}

fn boundary_miss_reason(
    constraint_epoch: GeneralizeSnapshotConstraintEpoch,
    supplemental_epoch: GeneralizeSnapshotSupplementalEpoch,
    candidate_guard: GeneralizeSnapshotCandidateGuard,
    pending_constraint_work: usize,
    pending_constraint_events: usize,
) -> Option<GeneralizeSnapshotMissReason> {
    if constraint_epoch == GeneralizeSnapshotConstraintEpoch::Unavailable {
        Some(GeneralizeSnapshotMissReason::ConstraintEpochUnwitnessable)
    } else if supplemental_epoch == GeneralizeSnapshotSupplementalEpoch::Unavailable {
        Some(GeneralizeSnapshotMissReason::SupplementalEpochUnwitnessable)
    } else if pending_constraint_work > 0 {
        Some(GeneralizeSnapshotMissReason::PendingConstraintWork)
    } else if pending_constraint_events > 0 {
        Some(GeneralizeSnapshotMissReason::PendingConstraintEvents)
    } else if candidate_guard == GeneralizeSnapshotCandidateGuard::Unavailable {
        Some(GeneralizeSnapshotMissReason::CandidateGuardUnavailable)
    } else if candidate_guard == GeneralizeSnapshotCandidateGuard::Overflowed {
        Some(GeneralizeSnapshotMissReason::CandidateGuardOverflow)
    } else {
        None
    }
}

fn disposition_name(disposition: &RoleDemandDisposition) -> &'static str {
    match disposition {
        RoleDemandDisposition::NewlyResolved { .. } => "newly-resolved",
        RoleDemandDisposition::AlreadyApplied { .. } => "already-applied",
        RoleDemandDisposition::Unresolved { .. } => "unresolved",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::role_solve::{RoleResolveOutput, RoleResolveStats};

    #[test]
    fn unwitnessable_epochs_and_non_quiescent_boundaries_never_become_would_be_hits() {
        let demand = demand("epoch-boundary");
        let mut observation = GeneralizeSnapshotRootObservation::new(DefId(0));
        observe_unresolved(
            &mut observation,
            1,
            &demand,
            GeneralizeSnapshotConstraintEpoch::Witness(ConstraintEpoch::default()),
            GeneralizeSnapshotSupplementalEpoch::Witness(RoleSolveSupplementalEpoch::default()),
            GeneralizeSnapshotCandidateGuard::Generation(0),
            0,
            0,
        );

        let adversaries = [
            (
                GeneralizeSnapshotConstraintEpoch::Unavailable,
                GeneralizeSnapshotSupplementalEpoch::Witness(RoleSolveSupplementalEpoch::default()),
                0,
                0,
                GeneralizeSnapshotMissReason::ConstraintEpochUnwitnessable,
            ),
            (
                GeneralizeSnapshotConstraintEpoch::Witness(ConstraintEpoch::default()),
                GeneralizeSnapshotSupplementalEpoch::Unavailable,
                0,
                0,
                GeneralizeSnapshotMissReason::SupplementalEpochUnwitnessable,
            ),
            (
                GeneralizeSnapshotConstraintEpoch::Witness(ConstraintEpoch::default()),
                GeneralizeSnapshotSupplementalEpoch::Witness(RoleSolveSupplementalEpoch::default()),
                1,
                0,
                GeneralizeSnapshotMissReason::PendingConstraintWork,
            ),
            (
                GeneralizeSnapshotConstraintEpoch::Witness(ConstraintEpoch::default()),
                GeneralizeSnapshotSupplementalEpoch::Witness(RoleSolveSupplementalEpoch::default()),
                0,
                1,
                GeneralizeSnapshotMissReason::PendingConstraintEvents,
            ),
        ];
        for (offset, (epoch, supplemental, pending_work, pending_events, reason)) in
            adversaries.into_iter().enumerate()
        {
            observe_unresolved(
                &mut observation,
                offset + 2,
                &demand,
                epoch,
                supplemental,
                GeneralizeSnapshotCandidateGuard::Generation(0),
                pending_work,
                pending_events,
            );
            let observed = last_observation(&observation);
            assert!(!observed.boundary_eligible);
            assert!(!observed.would_be_hit);
            assert!(!observed.exact_repeat);
            assert_eq!(observed.miss_reason, Some(reason));
            assert_eq!(observation.miss_reasons.count(reason), 1);
        }
        assert_eq!(observation.would_be_hits, 0);
        assert_eq!(observation.entries.len(), 1);
    }

    #[test]
    fn unavailable_and_overflowed_candidate_guards_fail_closed() {
        let demand = demand("candidate-guard");
        let mut observation = GeneralizeSnapshotRootObservation::new(DefId(0));
        observe_default(&mut observation, 1, &demand);

        for (iteration, guard, reason) in [
            (
                2,
                GeneralizeSnapshotCandidateGuard::Unavailable,
                GeneralizeSnapshotMissReason::CandidateGuardUnavailable,
            ),
            (
                3,
                GeneralizeSnapshotCandidateGuard::capture_generation(u64::MAX),
                GeneralizeSnapshotMissReason::CandidateGuardOverflow,
            ),
        ] {
            observe_unresolved(
                &mut observation,
                iteration,
                &demand,
                GeneralizeSnapshotConstraintEpoch::Witness(ConstraintEpoch::default()),
                GeneralizeSnapshotSupplementalEpoch::Witness(RoleSolveSupplementalEpoch::default()),
                guard,
                0,
                0,
            );
            let observed = last_observation(&observation);
            assert!(!observed.boundary_eligible);
            assert!(!observed.would_be_hit);
            assert_eq!(observed.miss_reason, Some(reason));
            assert_eq!(observation.miss_reasons.count(reason), 1);
        }
        assert_eq!(observation.entries.len(), 1);
    }

    #[test]
    fn incomplete_entry_is_rejected_then_atomically_replaced_by_the_full_result() {
        let demand = demand("partial-entry");
        let mut observation = GeneralizeSnapshotRootObservation::new(DefId(0));
        observe_default(&mut observation, 1, &demand);
        observation.entries[0].result = ExactSnapshotResult::Incomplete;

        observe_default(&mut observation, 2, &demand);
        let rejected = last_observation(&observation);
        assert!(!rejected.would_be_hit);
        assert_eq!(
            rejected.miss_reason,
            Some(GeneralizeSnapshotMissReason::IncompleteEntry)
        );
        assert_eq!(observation.comparison_cost.result_comparisons, 0);
        assert_eq!(
            observation
                .miss_reasons
                .count(GeneralizeSnapshotMissReason::IncompleteEntry),
            1
        );
        assert!(observation.entries[0].result.complete().is_some());

        observe_default(&mut observation, 3, &demand);
        let verified = last_observation(&observation);
        assert!(verified.would_be_hit);
        assert!(verified.exact_repeat);
        assert_eq!(verified.miss_reason, None);
    }

    #[test]
    fn entry_and_byte_caps_clear_and_disable_the_root_cache() {
        let first = demand("first");
        let second = demand("second");
        let mut entry_capped = GeneralizeSnapshotRootObservation::with_budget(
            DefId(0),
            GeneralizeSnapshotBudget {
                max_entries: 1,
                max_retained_debug_bytes: usize::MAX,
            },
        );
        observe_default(&mut entry_capped, 1, &first);
        assert_eq!(entry_capped.entries.len(), 1);
        observe_default(&mut entry_capped, 2, &second);
        assert!(entry_capped.entries.is_empty());
        assert_eq!(entry_capped.retained_debug_bytes, 0);
        assert_eq!(entry_capped.cap_exhaustions, 1);
        assert_eq!(
            last_observation(&entry_capped).miss_reason,
            Some(GeneralizeSnapshotMissReason::BudgetExhausted)
        );
        observe_default(&mut entry_capped, 3, &first);
        assert!(!last_observation(&entry_capped).would_be_hit);
        assert_eq!(
            last_observation(&entry_capped).miss_reason,
            Some(GeneralizeSnapshotMissReason::BudgetExhausted)
        );
        assert!(entry_capped.entries.is_empty());
        assert_eq!(
            entry_capped
                .miss_reasons
                .count(GeneralizeSnapshotMissReason::BudgetExhausted),
            2
        );

        let mut byte_capped = GeneralizeSnapshotRootObservation::with_budget(
            DefId(1),
            GeneralizeSnapshotBudget {
                max_entries: MAX_RETAINED_SNAPSHOT_ENTRIES,
                max_retained_debug_bytes: 0,
            },
        );
        observe_default(&mut byte_capped, 1, &first);
        assert_eq!(byte_capped.cap_exhaustions, 1);
        assert!(byte_capped.entries.is_empty());
        assert_eq!(
            last_observation(&byte_capped).miss_reason,
            Some(GeneralizeSnapshotMissReason::BudgetExhausted)
        );
    }

    #[test]
    fn cache_identity_is_only_the_exact_structural_emadc_values() {
        let demand = demand("typed-demand-path");
        let separately_allocated_equal_demand = demand.clone();
        let reporting_def = DefId(37);
        let mut observation = GeneralizeSnapshotRootObservation::new(reporting_def);
        observe_default(&mut observation, 1, &demand);

        {
            // Keep this exhaustive: adding a new retained field makes the audit fail to compile
            // until its identity role is reviewed. `slot`, `result`, and retained sizes are
            // payload/accounting; the exact key is E/A/M/D/C below.
            let ExactSnapshotEntry {
                slot,
                constraint_epoch,
                role_solve_supplemental_epoch,
                main,
                demand: retained_demand,
                candidate_generation,
                result,
                retained_debug_bytes,
                retained_main_nodes,
            } = &mut observation.entries[0];
            assert_eq!(*slot, 0);
            assert_eq!(*constraint_epoch, ConstraintEpoch::default());
            assert_eq!(
                *role_solve_supplemental_epoch,
                RoleSolveSupplementalEpoch::default()
            );
            assert_eq!(main, &CompactRoot::default());
            assert_eq!(retained_demand, &separately_allocated_equal_demand);
            assert_eq!(*candidate_generation, 0);
            assert!(result.complete().is_some());

            // Debug-derived values are budget telemetry only. Deliberately corrupting them must
            // not affect exact identity or the shadow comparison.
            *retained_debug_bytes = usize::MAX;
            *retained_main_nodes = usize::MAX;
        }

        observe_default(&mut observation, 2, &separately_allocated_equal_demand);
        let repeated = last_observation(&observation);
        assert!(repeated.would_be_hit);
        assert!(repeated.exact_repeat);
        assert_eq!(observation.def, reporting_def);
    }

    fn observe_default(
        observation: &mut GeneralizeSnapshotRootObservation,
        iteration: usize,
        demand: &CompactRoleConstraint,
    ) {
        observe_unresolved(
            observation,
            iteration,
            demand,
            GeneralizeSnapshotConstraintEpoch::Witness(ConstraintEpoch::default()),
            GeneralizeSnapshotSupplementalEpoch::Witness(RoleSolveSupplementalEpoch::default()),
            GeneralizeSnapshotCandidateGuard::Generation(0),
            0,
            0,
        );
    }

    #[allow(clippy::too_many_arguments)]
    fn observe_unresolved(
        observation: &mut GeneralizeSnapshotRootObservation,
        iteration: usize,
        demand: &CompactRoleConstraint,
        constraint_epoch: GeneralizeSnapshotConstraintEpoch,
        supplemental_epoch: GeneralizeSnapshotSupplementalEpoch,
        candidate_guard: GeneralizeSnapshotCandidateGuard,
        pending_work: usize,
        pending_events: usize,
    ) {
        let pure = [PureRoleDemandObservation {
            demand: demand.clone(),
            outcome: PureRoleDemandOutcome::Unresolved {
                candidate_matches: 0,
            },
            candidate_buckets: vec![demand.role.clone()],
            solve_time: Duration::ZERO,
        }];
        let resolved = RoleResolveDispositionOutput {
            output: RoleResolveOutput {
                resolutions: Vec::new(),
                stats: RoleResolveStats::default(),
            },
            dispositions: vec![RoleDemandDisposition::Unresolved {
                candidate_matches: 0,
            }],
        };
        observation.observe_solve_boundary(
            iteration,
            constraint_epoch,
            supplemental_epoch,
            candidate_guard,
            &CompactRoot::default(),
            std::slice::from_ref(demand),
            &pure,
            &resolved,
            &FxHashSet::default(),
            Duration::ZERO,
            pending_work,
            pending_events,
            0,
        );
    }

    fn last_observation(
        observation: &GeneralizeSnapshotRootObservation,
    ) -> &GeneralizeSnapshotDemandSolve {
        observation
            .demands
            .iter()
            .flat_map(|demand| &demand.observations)
            .max_by_key(|observation| observation.iteration)
            .expect("one demand observation")
    }

    fn demand(name: &str) -> CompactRoleConstraint {
        CompactRoleConstraint {
            role: vec![name.into()],
            inputs: Vec::new(),
            associated: Vec::new(),
        }
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
