//! Test-only observation of the pure per-demand recursive result.
//!
//! The production solver still performs every solve and chooses every disposition. This module
//! records the result immediately before the live `applied` membership read, so characterization
//! can prove that recursive candidate construction is independent of applied-state timing.

use super::*;

use std::cell::RefCell;

thread_local! {
    static ACTIVE: RefCell<Option<ActiveObservation>> = const { RefCell::new(None) };
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PureRoleDemandObservation {
    pub(crate) demand: CompactRoleConstraint,
    pub(crate) outcome: PureRoleDemandOutcome,
    pub(crate) candidate_buckets: Vec<Vec<String>>,
    pub(crate) solve_time: crate::time::Duration,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PureRoleDemandOutcome {
    Resolved(RoleResolution),
    Unresolved { candidate_matches: usize },
}

#[derive(Default)]
struct ActiveObservation {
    completed: Vec<PureRoleDemandObservation>,
    current: Option<ActiveDemand>,
}

struct ActiveDemand {
    demand: CompactRoleConstraint,
    candidate_buckets: Vec<Vec<String>>,
    started_at: crate::time::Instant,
}

pub(crate) fn capture_pure_role_demand_observations<T>(
    solve: impl FnOnce() -> T,
) -> (T, Vec<PureRoleDemandObservation>) {
    ACTIVE.with(|active| {
        assert!(
            active
                .borrow_mut()
                .replace(ActiveObservation::default())
                .is_none(),
            "pure role-demand observation must not nest"
        );
    });
    let mut guard = ObservationGuard { active: true };
    let output = solve();
    let observation = ACTIVE.with(|active| {
        active
            .borrow_mut()
            .take()
            .expect("active pure role-demand observation")
    });
    guard.active = false;
    assert!(
        observation.current.is_none(),
        "every observed role demand must publish one pure outcome"
    );
    (output, observation.completed)
}

pub(super) fn begin_demand(demand: &CompactRoleConstraint) {
    ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        let Some(active) = active.as_mut() else {
            return;
        };
        assert!(
            active.current.is_none(),
            "top-level role demand observations are sequential"
        );
        active.current = Some(ActiveDemand {
            demand: demand.clone(),
            candidate_buckets: Vec::new(),
            started_at: crate::time::Instant::now(),
        });
    });
}

pub(super) fn record_candidate_bucket(role: &[String]) {
    ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        let Some(current) = active
            .as_mut()
            .and_then(|observation| observation.current.as_mut())
        else {
            return;
        };
        if !current
            .candidate_buckets
            .iter()
            .any(|observed| observed == role)
        {
            current.candidate_buckets.push(role.to_vec());
        }
    });
}

pub(super) fn record_unresolved(candidate_matches: usize) {
    let Some(solve_time) = current_solve_time() else {
        return;
    };
    finish_demand(
        PureRoleDemandOutcome::Unresolved { candidate_matches },
        solve_time,
    );
}

pub(super) fn record_resolved(
    key: &RoleResolutionKey,
    demand: &CompactRoleConstraint,
    candidate: &CompactRoleConstraint,
    solved_prerequisites: &[RoleResolution],
    residual_prerequisites: &[CompactRoleConstraint],
) {
    let Some(solve_time) = current_solve_time() else {
        return;
    };
    finish_demand(
        PureRoleDemandOutcome::Resolved(RoleResolution {
            key: key.clone(),
            demand: demand.clone(),
            candidate: candidate.clone(),
            solved_prerequisites: solved_prerequisites.to_vec(),
            residual_prerequisites: residual_prerequisites.to_vec(),
        }),
        solve_time,
    );
}

fn current_solve_time() -> Option<crate::time::Duration> {
    ACTIVE.with(|active| {
        active
            .borrow()
            .as_ref()
            .and_then(|observation| observation.current.as_ref())
            .map(|current| current.started_at.elapsed())
    })
}

fn finish_demand(outcome: PureRoleDemandOutcome, solve_time: crate::time::Duration) {
    ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        let Some(active) = active.as_mut() else {
            return;
        };
        let current = active
            .current
            .take()
            .expect("observed role demand must have a start");
        active.completed.push(PureRoleDemandObservation {
            demand: current.demand,
            outcome,
            candidate_buckets: current.candidate_buckets,
            solve_time,
        });
    });
}

struct ObservationGuard {
    active: bool,
}

impl Drop for ObservationGuard {
    fn drop(&mut self) {
        if self.active {
            ACTIVE.with(|active| {
                active.borrow_mut().take();
            });
        }
    }
}
