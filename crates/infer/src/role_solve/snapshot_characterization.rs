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

/// The live disposition and publication delta obtained by applying one pure recursive result to
/// the current `applied` set.
///
/// This is deliberately derived afresh on every shadow lookup. The retained snapshot owns only
/// the recursive result; it never retains an old newly-resolved/already-applied classification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ShadowRoleDemandApplication {
    pub(crate) disposition: RoleDemandDisposition,
    pub(crate) state_delta: ShadowRoleStateDelta,
}

/// Exact inputs that the unchanged generalization disposition path would publish for one demand.
///
/// `resolutions` is the top-level production delta. The remaining fields make the recursive
/// applied-membership and constraint-publication consequences explicit for shadow comparison.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ShadowRoleStateDelta {
    pub(crate) resolutions: Vec<RoleResolution>,
    pub(crate) applied_resolution_keys: Vec<RoleResolutionKey>,
    pub(crate) applied_demands: Vec<CompactRoleConstraint>,
    pub(crate) residual_prerequisites: Vec<CompactRoleConstraint>,
    pub(crate) equal_role_args: Vec<(CompactRoleArg, CompactRoleArg)>,
}

pub(crate) fn apply_pure_role_demand_outcome(
    outcome: &PureRoleDemandOutcome,
    applied: &FxHashSet<RoleResolutionKey>,
) -> ShadowRoleDemandApplication {
    match outcome {
        PureRoleDemandOutcome::Unresolved { candidate_matches } => ShadowRoleDemandApplication {
            disposition: RoleDemandDisposition::Unresolved {
                candidate_matches: *candidate_matches,
            },
            state_delta: ShadowRoleStateDelta::default(),
        },
        PureRoleDemandOutcome::Resolved(resolution) if applied.contains(&resolution.key) => {
            ShadowRoleDemandApplication {
                disposition: RoleDemandDisposition::AlreadyApplied {
                    key: resolution.key.clone(),
                },
                state_delta: ShadowRoleStateDelta::default(),
            }
        }
        PureRoleDemandOutcome::Resolved(resolution) => ShadowRoleDemandApplication {
            disposition: RoleDemandDisposition::NewlyResolved {
                key: resolution.key.clone(),
            },
            state_delta: shadow_state_delta(std::slice::from_ref(resolution)),
        },
    }
}

pub(crate) fn shadow_applications_from_full_solve(
    dispositions: &[RoleDemandDisposition],
    resolutions: &[RoleResolution],
) -> Option<Vec<ShadowRoleDemandApplication>> {
    let mut resolutions = resolutions.iter();
    let mut applications = Vec::with_capacity(dispositions.len());
    for disposition in dispositions {
        let demand_resolutions = match disposition {
            RoleDemandDisposition::NewlyResolved { key } => {
                let resolution = resolutions.next()?;
                if resolution.key != *key {
                    return None;
                }
                vec![resolution.clone()]
            }
            RoleDemandDisposition::AlreadyApplied { .. }
            | RoleDemandDisposition::Unresolved { .. } => Vec::new(),
        };
        applications.push(ShadowRoleDemandApplication {
            disposition: disposition.clone(),
            state_delta: shadow_state_delta(&demand_resolutions),
        });
    }
    resolutions.next().is_none().then_some(applications)
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

fn shadow_state_delta(resolutions: &[RoleResolution]) -> ShadowRoleStateDelta {
    let mut delta = ShadowRoleStateDelta {
        resolutions: resolutions.to_vec(),
        ..ShadowRoleStateDelta::default()
    };
    for resolution in resolutions {
        delta.applied_resolution_keys.push(resolution.key.clone());
        collect_applied_demands(resolution, &mut delta.applied_demands);
        collect_publication_delta(resolution, &mut delta);
    }
    delta
}

fn collect_applied_demands(
    resolution: &RoleResolution,
    applied_demands: &mut Vec<CompactRoleConstraint>,
) {
    applied_demands.push(resolution.demand.clone());
    for prerequisite in &resolution.solved_prerequisites {
        collect_applied_demands(prerequisite, applied_demands);
    }
}

fn collect_publication_delta(resolution: &RoleResolution, delta: &mut ShadowRoleStateDelta) {
    for prerequisite in &resolution.solved_prerequisites {
        collect_publication_delta(prerequisite, delta);
    }
    delta
        .residual_prerequisites
        .extend(resolution.residual_prerequisites.iter().cloned());
    delta.equal_role_args.extend(
        resolution
            .demand
            .inputs
            .iter()
            .zip(&resolution.candidate.inputs)
            .map(|(demand, candidate)| (demand.clone(), candidate.clone())),
    );
    delta
        .equal_role_args
        .extend(resolution.demand.associated.iter().filter_map(|demand| {
            resolution
                .candidate
                .associated
                .iter()
                .find(|candidate| candidate.name == demand.name)
                .map(|candidate| (demand.value.clone(), candidate.value.clone()))
        }));
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
