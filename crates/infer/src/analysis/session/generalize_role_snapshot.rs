//! Fail-closed loop-local exact snapshots for generalization role solving.
//!
//! One root owns one cache. Every hit proves exact E/A/M/D/C equality and returns only the pure
//! recursive result; the role solver reevaluates live `applied` membership and preserves the
//! existing disposition/publication path.

use super::*;

use std::cell::Cell;
use std::mem::size_of;

use crate::constraints::RoleSolveSupplementalEpoch;
use crate::role_solve::{ExactRoleSolveSnapshots, PureRoleDemandOutcome};

thread_local! {
    static NEW_SESSION_MODE: Cell<GeneralizeRoleSnapshotMode> = const {
        Cell::new(GeneralizeRoleSnapshotMode::AlwaysSolve)
    };
}

/// Run newly created sessions through the unchanged always-full-solve generalization path.
///
/// Always-solve is currently the production default because Stage 2's release gate failed. This
/// explicit, default-confirming scope remains available as a stable rollback and paired-verification
/// control; it changes only exact snapshot eligibility.
pub fn with_generalize_role_snapshot_always_solve_for_new_sessions<T>(
    run: impl FnOnce() -> T,
) -> T {
    with_new_session_mode(GeneralizeRoleSnapshotMode::AlwaysSolve, run)
}

/// Opt newly created sessions into exact role-snapshot reuse for experiments and benchmarks.
///
/// The implementation and telemetry are retained for follow-up work, but reuse is held behind this
/// explicit scope because Stage 2's production release gate failed.
pub fn with_generalize_role_snapshot_reuse_enabled_for_new_sessions<T>(
    run: impl FnOnce() -> T,
) -> T {
    with_new_session_mode(GeneralizeRoleSnapshotMode::ReuseEnabled, run)
}

pub(crate) fn generalize_role_snapshot_reuse_enabled_for_new_session() -> bool {
    NEW_SESSION_MODE.with(|mode| mode.get() == GeneralizeRoleSnapshotMode::ReuseEnabled)
}

/// Stage 0 observed at most 6 entries in one root; the approved production cap retains the 64-entry
/// headroom used by the Stage 1 oracle.
const MAX_RETAINED_SNAPSHOT_ENTRIES: usize = 64;

/// Approved Stage 0/1 structural Debug-size proxy cap.
const MAX_RETAINED_SNAPSHOT_DEBUG_BYTES: usize = 128 * 1024 * 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GeneralizeRoleSnapshotMode {
    ReuseEnabled,
    AlwaysSolve,
}

fn with_new_session_mode<T>(mode: GeneralizeRoleSnapshotMode, run: impl FnOnce() -> T) -> T {
    struct ModeGuard(GeneralizeRoleSnapshotMode);

    impl Drop for ModeGuard {
        fn drop(&mut self) {
            NEW_SESSION_MODE.with(|current| current.set(self.0));
        }
    }

    let previous = NEW_SESSION_MODE.with(|current| current.replace(mode));
    let _guard = ModeGuard(previous);
    run()
}

#[derive(Debug, Clone, Copy)]
struct GeneralizeRoleSnapshotBudget {
    max_entries: usize,
    max_retained_debug_bytes: usize,
}

impl Default for GeneralizeRoleSnapshotBudget {
    fn default() -> Self {
        Self {
            max_entries: MAX_RETAINED_SNAPSHOT_ENTRIES,
            max_retained_debug_bytes: MAX_RETAINED_SNAPSHOT_DEBUG_BYTES,
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct GeneralizeRoleSnapshotRootReport {
    pub(crate) misses: usize,
    pub(crate) cap_fallbacks: usize,
    pub(crate) peak_entries: usize,
    pub(crate) peak_retained_debug_bytes: usize,
}

pub(crate) struct GeneralizeRoleSnapshotRoot {
    reuse_enabled: bool,
    reuse_disabled: bool,
    budget: GeneralizeRoleSnapshotBudget,
    entries: Vec<ExactSnapshotEntry>,
    retained_debug_bytes: usize,
    report: GeneralizeRoleSnapshotRootReport,
}

impl GeneralizeRoleSnapshotRoot {
    pub(super) fn new(reuse_enabled: bool) -> Self {
        Self::with_budget(reuse_enabled, GeneralizeRoleSnapshotBudget::default())
    }

    fn with_budget(reuse_enabled: bool, budget: GeneralizeRoleSnapshotBudget) -> Self {
        Self {
            reuse_enabled,
            reuse_disabled: false,
            budget,
            entries: Vec::new(),
            retained_debug_bytes: 0,
            report: GeneralizeRoleSnapshotRootReport::default(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn boundary(
        &mut self,
        constraint_epoch: ConstraintEpoch,
        role_solve_supplemental_epoch: RoleSolveSupplementalEpoch,
        candidate_generation: u64,
        pending_constraint_work: usize,
        pending_constraint_events: usize,
    ) -> GeneralizeRoleSnapshotBoundary<'_> {
        // The session analysis queue is deliberately absent here: the pure recursive solver
        // cannot read it, and Stage 0 tracked its length only as observational context. Constraint
        // work and events are solver-state boundary guards and must remain drained.
        let guard = if !constraint_epoch.can_witness_unchanged_state()
            || !role_solve_supplemental_epoch.can_witness_unchanged_state()
            || pending_constraint_work != 0
            || pending_constraint_events != 0
        {
            None
        } else {
            match ExactSnapshotCandidateGuard::capture(candidate_generation) {
                candidate_guard @ ExactSnapshotCandidateGuard::Generation(_) => {
                    Some(ExactSnapshotBoundaryGuard {
                        constraint_epoch,
                        role_solve_supplemental_epoch,
                        candidate_guard,
                    })
                }
                ExactSnapshotCandidateGuard::Overflowed => None,
            }
        };
        GeneralizeRoleSnapshotBoundary {
            root: self,
            guard,
            main_debug_bytes: None,
        }
    }

    pub(super) fn report(&self) -> GeneralizeRoleSnapshotRootReport {
        self.report
    }

    fn disable_reuse_after_cap(&mut self) {
        self.entries.clear();
        self.retained_debug_bytes = 0;
        self.reuse_disabled = true;
        self.report.cap_fallbacks += 1;
    }
}

pub(super) struct GeneralizeRoleSnapshotBoundary<'a> {
    root: &'a mut GeneralizeRoleSnapshotRoot,
    guard: Option<ExactSnapshotBoundaryGuard>,
    main_debug_bytes: Option<usize>,
}

impl ExactRoleSolveSnapshots for GeneralizeRoleSnapshotBoundary<'_> {
    fn lookup(
        &mut self,
        main: &CompactRoot,
        demand: &CompactRoleConstraint,
    ) -> Option<PureRoleDemandOutcome> {
        let Some(guard) = self.guard else {
            self.root.report.misses += 1;
            return None;
        };
        if !self.root.reuse_enabled || self.root.reuse_disabled {
            self.root.report.misses += 1;
            return None;
        }
        let hit = self.root.entries.iter().find(|entry| {
            entry.demand == *demand
                && entry.constraint_epoch == guard.constraint_epoch
                && entry.role_solve_supplemental_epoch == guard.role_solve_supplemental_epoch
                && entry.main == *main
                && entry.candidate_guard == guard.candidate_guard
        });
        if let Some(entry) = hit {
            Some(entry.outcome.clone())
        } else {
            self.root.report.misses += 1;
            None
        }
    }

    fn retain(
        &mut self,
        main: &CompactRoot,
        demand: &CompactRoleConstraint,
        outcome: &PureRoleDemandOutcome,
    ) {
        let Some(guard) = self.guard else {
            return;
        };
        if !self.root.reuse_enabled || self.root.reuse_disabled {
            return;
        }

        let matching_index = self
            .root
            .entries
            .iter()
            .position(|entry| entry.demand == *demand);
        let main_debug_bytes = *self
            .main_debug_bytes
            .get_or_insert_with(|| format!("{main:?}").len());
        let retained_debug_bytes = [
            size_of::<ConstraintEpoch>(),
            size_of::<RoleSolveSupplementalEpoch>(),
            size_of::<ExactSnapshotCandidateGuard>(),
            main_debug_bytes,
            format!("{demand:?}").len(),
            format!("{outcome:?}").len(),
        ]
        .into_iter()
        .try_fold(0usize, usize::checked_add);
        let previous_debug_bytes = matching_index
            .and_then(|index| self.root.entries.get(index))
            .map(|entry| entry.retained_debug_bytes)
            .unwrap_or(0);
        let projected_entries = if matching_index.is_some() {
            Some(self.root.entries.len())
        } else {
            self.root.entries.len().checked_add(1)
        };
        let projected_debug_bytes = retained_debug_bytes.and_then(|bytes| {
            self.root
                .retained_debug_bytes
                .checked_sub(previous_debug_bytes)
                .and_then(|retained| retained.checked_add(bytes))
        });
        let within_budget =
            projected_entries
                .zip(projected_debug_bytes)
                .is_some_and(|(entries, bytes)| {
                    entries <= self.root.budget.max_entries
                        && bytes <= self.root.budget.max_retained_debug_bytes
                });
        if !within_budget {
            self.root.disable_reuse_after_cap();
            return;
        }

        let entry = ExactSnapshotEntry {
            constraint_epoch: guard.constraint_epoch,
            role_solve_supplemental_epoch: guard.role_solve_supplemental_epoch,
            main: main.clone(),
            demand: demand.clone(),
            candidate_guard: guard.candidate_guard,
            outcome: outcome.clone(),
            retained_debug_bytes: retained_debug_bytes.expect("validated snapshot byte projection"),
        };
        let retained_index = if let Some(index) = matching_index {
            let previous = std::mem::replace(&mut self.root.entries[index], entry);
            self.root.retained_debug_bytes = self
                .root
                .retained_debug_bytes
                .saturating_sub(previous.retained_debug_bytes);
            index
        } else {
            self.root.entries.push(entry);
            self.root.entries.len() - 1
        };
        self.root.retained_debug_bytes = self
            .root
            .retained_debug_bytes
            .saturating_add(self.root.entries[retained_index].retained_debug_bytes);
        self.root.report.peak_entries = self.root.report.peak_entries.max(self.root.entries.len());
        self.root.report.peak_retained_debug_bytes = self
            .root
            .report
            .peak_retained_debug_bytes
            .max(self.root.retained_debug_bytes);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ExactSnapshotBoundaryGuard {
    constraint_epoch: ConstraintEpoch,
    role_solve_supplemental_epoch: RoleSolveSupplementalEpoch,
    candidate_guard: ExactSnapshotCandidateGuard,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExactSnapshotCandidateGuard {
    Generation(u64),
    Overflowed,
}

impl ExactSnapshotCandidateGuard {
    fn capture(generation: u64) -> Self {
        if generation == u64::MAX {
            Self::Overflowed
        } else {
            Self::Generation(generation)
        }
    }
}

struct ExactSnapshotEntry {
    constraint_epoch: ConstraintEpoch,
    role_solve_supplemental_epoch: RoleSolveSupplementalEpoch,
    main: CompactRoot,
    demand: CompactRoleConstraint,
    candidate_guard: ExactSnapshotCandidateGuard,
    outcome: PureRoleDemandOutcome,
    retained_debug_bytes: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_snapshot_hit_reuses_only_a_complete_emadc_match() {
        let mut root = GeneralizeRoleSnapshotRoot::new(true);
        let main = CompactRoot::default();
        let demand = demand("Display");
        let outcome = PureRoleDemandOutcome::Unresolved {
            candidate_matches: 0,
        };
        let mut first = root.boundary(
            ConstraintEpoch::default(),
            RoleSolveSupplementalEpoch::default(),
            7,
            0,
            0,
        );
        assert!(first.lookup(&main, &demand).is_none());
        first.retain(&main, &demand, &outcome);
        drop(first);

        let mut same = root.boundary(
            ConstraintEpoch::default(),
            RoleSolveSupplementalEpoch::default(),
            7,
            0,
            0,
        );
        assert_eq!(same.lookup(&main, &demand), Some(outcome.clone()));
        drop(same);

        let mut changed_candidate = root.boundary(
            ConstraintEpoch::default(),
            RoleSolveSupplementalEpoch::default(),
            8,
            0,
            0,
        );
        assert!(changed_candidate.lookup(&main, &demand).is_none());
    }

    #[test]
    fn non_quiescent_and_capped_roots_fail_closed() {
        let main = CompactRoot::default();
        let demand = demand("Display");
        let outcome = PureRoleDemandOutcome::Unresolved {
            candidate_matches: 0,
        };
        let mut root = GeneralizeRoleSnapshotRoot::with_budget(
            true,
            GeneralizeRoleSnapshotBudget {
                max_entries: 64,
                max_retained_debug_bytes: 0,
            },
        );
        let mut non_quiescent = root.boundary(
            ConstraintEpoch::default(),
            RoleSolveSupplementalEpoch::default(),
            0,
            1,
            0,
        );
        non_quiescent.retain(&main, &demand, &outcome);
        assert!(non_quiescent.lookup(&main, &demand).is_none());
        drop(non_quiescent);

        let mut capped = root.boundary(
            ConstraintEpoch::default(),
            RoleSolveSupplementalEpoch::default(),
            0,
            0,
            0,
        );
        capped.retain(&main, &demand, &outcome);
        assert!(capped.lookup(&main, &demand).is_none());
        drop(capped);
        assert_eq!(root.report().cap_fallbacks, 1);
        assert_eq!(root.report().peak_entries, 0);
    }

    #[test]
    fn new_sessions_default_to_always_solve_and_mode_scopes_are_unwind_safe() {
        assert!(!generalize_role_snapshot_reuse_enabled_for_new_session());
        with_generalize_role_snapshot_always_solve_for_new_sessions(|| {
            assert!(!generalize_role_snapshot_reuse_enabled_for_new_session());
        });
        with_generalize_role_snapshot_reuse_enabled_for_new_sessions(|| {
            assert!(generalize_role_snapshot_reuse_enabled_for_new_session());
            let unwind = std::panic::catch_unwind(|| {
                with_generalize_role_snapshot_always_solve_for_new_sessions(|| {
                    assert!(!generalize_role_snapshot_reuse_enabled_for_new_session());
                    panic!("exercise exact snapshot always-solve override cleanup");
                });
            });
            assert!(unwind.is_err());
            assert!(generalize_role_snapshot_reuse_enabled_for_new_session());
        });
        assert!(!generalize_role_snapshot_reuse_enabled_for_new_session());
    }

    fn demand(role: &str) -> CompactRoleConstraint {
        CompactRoleConstraint {
            role: vec![role.to_string()],
            inputs: Vec::new(),
            associated: Vec::new(),
        }
    }
}
