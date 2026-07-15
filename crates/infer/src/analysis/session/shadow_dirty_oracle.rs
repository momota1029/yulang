//! Test-only oracle for measuring owner-level method-role pass dirtiness.
//!
//! The production solver always runs. This module records only the state that an owner's real
//! solve read, predicts whether that state is unchanged on the next forced pass, and checks the
//! prediction against the real outcome.

use super::*;

use std::cell::{Cell, RefCell};

use crate::constraints::{ConstraintEffectFamily, SubtractFact};

thread_local! {
    static ENABLE_NEW_ORACLES: Cell<bool> = const { Cell::new(false) };
    static ACTIVE_OWNER_READS: RefCell<Option<OwnerReadFrontier>> = const { RefCell::new(None) };
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ShadowDirtyOracleReport {
    pub(crate) forced_passes: usize,
    pub(crate) owner_checks: usize,
    pub(crate) predicted_clean: usize,
    pub(crate) predicted_dirty: usize,
    pub(crate) root_available_checks: usize,
    pub(crate) root_available_predicted_clean: usize,
    pub(crate) root_available_predicted_dirty: usize,
    pub(crate) owners: Vec<ShadowDirtyOracleOwnerReport>,
    pub(crate) mismatches: Vec<ShadowDirtyOracleMismatch>,
}

impl ShadowDirtyOracleReport {
    pub(crate) fn owner(&self, owner: DefId) -> Option<&ShadowDirtyOracleOwnerReport> {
        self.owners.iter().find(|metrics| metrics.owner == owner)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ShadowDirtyOracleOwnerReport {
    pub(crate) owner: DefId,
    pub(crate) owner_checks: usize,
    pub(crate) predicted_clean: usize,
    pub(crate) predicted_dirty: usize,
    pub(crate) root_available_checks: usize,
    pub(crate) root_available_predicted_clean: usize,
    pub(crate) root_available_predicted_dirty: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ShadowDirtyOracleMismatch {
    pub(crate) pass: usize,
    pub(crate) owner: DefId,
    pub(crate) expected: &'static str,
    pub(crate) actual: &'static str,
}

#[derive(Debug, Default)]
pub(crate) struct ShadowDirtyOracle {
    pass: usize,
    candidate_epoch: u64,
    candidate_bucket_epochs: FxHashMap<Vec<String>, u64>,
    cached_no_progress: FxHashMap<DefId, CachedOwnerSolve>,
    current_predictions: FxHashMap<DefId, OwnerPrediction>,
    owner_metrics: FxHashMap<DefId, OwnerMetrics>,
    owner_checks: usize,
    predicted_clean: usize,
    predicted_dirty: usize,
    root_available_checks: usize,
    root_available_predicted_clean: usize,
    root_available_predicted_dirty: usize,
    mismatches: Vec<ShadowDirtyOracleMismatch>,
}

impl ShadowDirtyOracle {
    pub(super) fn for_new_session() -> Option<Self> {
        ENABLE_NEW_ORACLES.with(Cell::get).then(Self::default)
    }

    fn begin_pass(
        &mut self,
        session: &AnalysisSession,
        owners: &[DefId],
        method_taint: &MethodTaintIndex,
    ) {
        debug_assert!(self.current_predictions.is_empty());
        self.pass += 1;
        for owner in owners {
            let root_available = session.scc.root_of(*owner).is_some();
            let clean = self.cached_no_progress.get(owner).is_some_and(|cached| {
                cached.fingerprint.matches(
                    session,
                    *owner,
                    method_taint,
                    &self.candidate_bucket_epochs,
                )
            });
            self.owner_checks += 1;
            let metrics = self.owner_metrics.entry(*owner).or_default();
            metrics.owner_checks += 1;
            if root_available {
                self.root_available_checks += 1;
                metrics.root_available_checks += 1;
            }
            if clean {
                self.predicted_clean += 1;
                metrics.predicted_clean += 1;
                if root_available {
                    self.root_available_predicted_clean += 1;
                    metrics.root_available_predicted_clean += 1;
                }
            } else {
                self.predicted_dirty += 1;
                metrics.predicted_dirty += 1;
                if root_available {
                    self.root_available_predicted_dirty += 1;
                    metrics.root_available_predicted_dirty += 1;
                }
            }
            self.current_predictions.insert(
                *owner,
                OwnerPrediction {
                    clean,
                    cached_outcome: self
                        .cached_no_progress
                        .get(owner)
                        .map(|cached| cached.outcome),
                },
            );
        }
    }

    fn finish_owner(
        &mut self,
        session: &AnalysisSession,
        owner: DefId,
        root: Option<TypeVar>,
        progressed: bool,
        method_taint: &MethodTaintIndex,
        reads: OwnerReadFrontier,
    ) {
        let outcome = OwnerSolveOutcome::from_solve(root, progressed);
        let prediction = self
            .current_predictions
            .remove(&owner)
            .expect("every observed owner must have a pre-solve prediction");
        if prediction.clean && prediction.cached_outcome != Some(outcome) {
            self.mismatches.push(ShadowDirtyOracleMismatch {
                pass: self.pass,
                owner,
                expected: prediction
                    .cached_outcome
                    .map(OwnerSolveOutcome::as_str)
                    .unwrap_or("missing-cache"),
                actual: outcome.as_str(),
            });
        }
        if outcome.cacheable() {
            let fingerprint = OwnerDependencyFingerprint::capture(
                session,
                owner,
                root,
                method_taint,
                reads,
                &self.candidate_bucket_epochs,
            );
            self.cached_no_progress.insert(
                owner,
                CachedOwnerSolve {
                    fingerprint,
                    outcome,
                },
            );
        }
    }

    fn bump_candidate_buckets(&mut self, roles: impl IntoIterator<Item = Vec<String>>) {
        let Some(next) = self.candidate_epoch.checked_add(1) else {
            self.candidate_epoch = 0;
            self.candidate_bucket_epochs.clear();
            self.cached_no_progress.clear();
            return;
        };
        self.candidate_epoch = next;
        for role in roles {
            self.candidate_bucket_epochs.insert(role, next);
        }
    }

    fn report(&self) -> ShadowDirtyOracleReport {
        let mut owners = self
            .owner_metrics
            .iter()
            .map(|(owner, metrics)| ShadowDirtyOracleOwnerReport {
                owner: *owner,
                owner_checks: metrics.owner_checks,
                predicted_clean: metrics.predicted_clean,
                predicted_dirty: metrics.predicted_dirty,
                root_available_checks: metrics.root_available_checks,
                root_available_predicted_clean: metrics.root_available_predicted_clean,
                root_available_predicted_dirty: metrics.root_available_predicted_dirty,
            })
            .collect::<Vec<_>>();
        owners.sort_by_key(|metrics| metrics.owner.0);
        ShadowDirtyOracleReport {
            forced_passes: self.pass,
            owner_checks: self.owner_checks,
            predicted_clean: self.predicted_clean,
            predicted_dirty: self.predicted_dirty,
            root_available_checks: self.root_available_checks,
            root_available_predicted_clean: self.root_available_predicted_clean,
            root_available_predicted_dirty: self.root_available_predicted_dirty,
            owners,
            mismatches: self.mismatches.clone(),
        }
    }
}

#[derive(Debug, Clone)]
struct CachedOwnerSolve {
    fingerprint: OwnerDependencyFingerprint,
    outcome: OwnerSolveOutcome,
}

#[derive(Debug, Clone, Copy)]
struct OwnerPrediction {
    clean: bool,
    cached_outcome: Option<OwnerSolveOutcome>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OwnerSolveOutcome {
    RootUnavailable,
    NoProgress,
    Progress,
}

impl OwnerSolveOutcome {
    fn from_solve(root: Option<TypeVar>, progressed: bool) -> Self {
        match (root, progressed) {
            (None, _) => Self::RootUnavailable,
            (Some(_), false) => Self::NoProgress,
            (Some(_), true) => Self::Progress,
        }
    }

    fn cacheable(self) -> bool {
        self != Self::Progress
    }

    fn as_str(self) -> &'static str {
        match self {
            Self::RootUnavailable => "root-unavailable",
            Self::NoProgress => "no-progress",
            Self::Progress => "progress",
        }
    }
}

#[derive(Debug, Clone, Default)]
struct OwnerMetrics {
    owner_checks: usize,
    predicted_clean: usize,
    predicted_dirty: usize,
    root_available_checks: usize,
    root_available_predicted_clean: usize,
    root_available_predicted_dirty: usize,
}

#[derive(Debug, Clone)]
struct OwnerDependencyFingerprint {
    root: Option<TypeVar>,
    raw_role_epoch: RoleEpoch,
    owner_selections: Vec<(SelectId, SelectionUse)>,
    constraint: ConstraintDependencyFingerprint,
    candidate_buckets: Vec<(Vec<String>, u64)>,
    taint_projection: Vec<(TypeVar, Option<Vec<SelectId>>)>,
    projection_selections: Vec<(SelectId, SelectionUse)>,
    applied_resolution_reads: FxHashMap<RoleResolutionKey, bool>,
}

impl OwnerDependencyFingerprint {
    fn capture(
        session: &AnalysisSession,
        owner: DefId,
        root: Option<TypeVar>,
        method_taint: &MethodTaintIndex,
        reads: OwnerReadFrontier,
        candidate_bucket_epochs: &FxHashMap<Vec<String>, u64>,
    ) -> Self {
        let owner_selections = owner_selection_snapshot(session, owner);
        let constraint = ConstraintDependencyFingerprint::capture(session, &reads);
        let candidate_buckets =
            candidate_bucket_snapshot(reads.candidate_buckets, candidate_bucket_epochs);
        let taint_projection = taint_projection_snapshot(method_taint, reads.taint_vars);
        let projection_selections = projection_selection_snapshot(session, &taint_projection);
        Self {
            root,
            raw_role_epoch: session.roles.epoch_for_owner(owner),
            owner_selections,
            constraint,
            candidate_buckets,
            taint_projection,
            projection_selections,
            applied_resolution_reads: reads.applied_resolution_reads,
        }
    }

    fn matches(
        &self,
        session: &AnalysisSession,
        owner: DefId,
        method_taint: &MethodTaintIndex,
        candidate_bucket_epochs: &FxHashMap<Vec<String>, u64>,
    ) -> bool {
        self.root == session.scc.root_of(owner)
            && self.raw_role_epoch == session.roles.epoch_for_owner(owner)
            && self.owner_selections == owner_selection_snapshot(session, owner)
            && self.constraint.matches(session)
            && self.candidate_buckets.iter().all(|(role, epoch)| {
                candidate_bucket_epochs
                    .get(role)
                    .copied()
                    .unwrap_or_default()
                    == *epoch
            })
            && self.taint_projection
                == taint_projection_snapshot(
                    method_taint,
                    self.taint_projection.iter().map(|(var, _)| *var),
                )
            && self.projection_selections
                == projection_selection_snapshot(session, &self.taint_projection)
            && self
                .applied_resolution_reads
                .iter()
                .all(|(key, was_applied)| {
                    session.applied_method_role_resolutions.contains(key) == *was_applied
                })
    }
}

#[derive(Debug, Clone)]
struct ConstraintDependencyFingerprint {
    bounds: Vec<(TypeVar, Option<ConstraintEpoch>)>,
    neighbors: Vec<(TypeVar, Vec<TypeVar>)>,
    subtract_facts: Vec<(TypeVar, Vec<SubtractFact>)>,
    levels: Vec<(TypeVar, TypeLevel)>,
    birth_levels: Vec<(TypeVar, TypeLevel)>,
    pre_pop_effect_families: Vec<(TypeVar, Vec<ConstraintEffectFamily>)>,
}

impl ConstraintDependencyFingerprint {
    fn capture(session: &AnalysisSession, reads: &OwnerReadFrontier) -> Self {
        let machine = session.infer.constraints();
        let mut bounds = reads
            .bound_vars
            .iter()
            .map(|var| (*var, machine.bounds().of(*var).map(|bounds| bounds.epoch())))
            .collect::<Vec<_>>();
        bounds.sort_by_key(|(var, _)| var.0);
        let mut neighbors = reads
            .neighbor_vars
            .iter()
            .map(|var| {
                let mut neighbors = machine.var_neighbors(*var).collect::<Vec<_>>();
                neighbors.sort_by_key(|neighbor| neighbor.0);
                (*var, neighbors)
            })
            .collect::<Vec<_>>();
        neighbors.sort_by_key(|(var, _)| var.0);
        let mut subtract_facts = reads
            .subtract_vars
            .iter()
            .map(|var| (*var, machine.subtracts().facts(*var).to_vec()))
            .collect::<Vec<_>>();
        subtract_facts.sort_by_key(|(var, _)| var.0);
        let mut levels = reads
            .level_vars
            .iter()
            .map(|var| (*var, machine.level_of(*var)))
            .collect::<Vec<_>>();
        levels.sort_by_key(|(var, _)| var.0);
        let mut birth_levels = reads
            .birth_level_vars
            .iter()
            .map(|var| (*var, machine.birth_level_of(*var)))
            .collect::<Vec<_>>();
        birth_levels.sort_by_key(|(var, _)| var.0);
        let mut pre_pop_effect_families = reads
            .pre_pop_vars
            .iter()
            .map(|var| (*var, machine.pre_pop_effect_families(*var).to_vec()))
            .collect::<Vec<_>>();
        pre_pop_effect_families.sort_by_key(|(var, _)| var.0);
        Self {
            bounds,
            neighbors,
            subtract_facts,
            levels,
            birth_levels,
            pre_pop_effect_families,
        }
    }

    fn matches(&self, session: &AnalysisSession) -> bool {
        let reads = OwnerReadFrontier {
            bound_vars: self.bounds.iter().map(|(var, _)| *var).collect(),
            neighbor_vars: self.neighbors.iter().map(|(var, _)| *var).collect(),
            subtract_vars: self.subtract_facts.iter().map(|(var, _)| *var).collect(),
            level_vars: self.levels.iter().map(|(var, _)| *var).collect(),
            birth_level_vars: self.birth_levels.iter().map(|(var, _)| *var).collect(),
            pre_pop_vars: self
                .pre_pop_effect_families
                .iter()
                .map(|(var, _)| *var)
                .collect(),
            ..OwnerReadFrontier::default()
        };
        let current = Self::capture(session, &reads);
        self.bounds == current.bounds
            && self.neighbors == current.neighbors
            && self.subtract_facts == current.subtract_facts
            && self.levels == current.levels
            && self.birth_levels == current.birth_levels
            && self.pre_pop_effect_families == current.pre_pop_effect_families
    }
}

#[derive(Debug, Default)]
pub(crate) struct OwnerReadFrontier {
    bound_vars: FxHashSet<TypeVar>,
    neighbor_vars: FxHashSet<TypeVar>,
    subtract_vars: FxHashSet<TypeVar>,
    level_vars: FxHashSet<TypeVar>,
    birth_level_vars: FxHashSet<TypeVar>,
    pre_pop_vars: FxHashSet<TypeVar>,
    candidate_buckets: FxHashSet<Vec<String>>,
    taint_vars: FxHashSet<TypeVar>,
    applied_resolution_reads: FxHashMap<RoleResolutionKey, bool>,
}

pub(crate) struct ShadowOwnerReadGuard {
    active: bool,
}

impl ShadowOwnerReadGuard {
    pub(crate) fn finish(mut self) -> OwnerReadFrontier {
        let reads = ACTIVE_OWNER_READS.with(|active| {
            active
                .borrow_mut()
                .take()
                .expect("active shadow owner observation")
        });
        self.active = false;
        reads
    }
}

impl Drop for ShadowOwnerReadGuard {
    fn drop(&mut self) {
        if self.active {
            ACTIVE_OWNER_READS.with(|active| {
                active.borrow_mut().take();
            });
        }
    }
}

pub(crate) fn with_shadow_dirty_oracle_for_new_sessions<T>(f: impl FnOnce() -> T) -> T {
    struct EnableGuard(bool);
    impl Drop for EnableGuard {
        fn drop(&mut self) {
            ENABLE_NEW_ORACLES.with(|enabled| enabled.set(self.0));
        }
    }

    let previous = ENABLE_NEW_ORACLES.with(|enabled| enabled.replace(true));
    let _guard = EnableGuard(previous);
    f()
}

pub(crate) fn begin_shadow_owner_reads() -> ShadowOwnerReadGuard {
    ACTIVE_OWNER_READS.with(|active| {
        assert!(
            active
                .borrow_mut()
                .replace(OwnerReadFrontier::default())
                .is_none(),
            "shadow owner read observation must not nest"
        );
    });
    ShadowOwnerReadGuard { active: true }
}

pub(crate) fn record_shadow_bound_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.bound_vars.insert(var);
    });
}

pub(crate) fn record_shadow_neighbor_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.neighbor_vars.insert(var);
    });
}

pub(crate) fn record_shadow_subtract_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.subtract_vars.insert(var);
    });
}

pub(crate) fn record_shadow_level_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.level_vars.insert(var);
    });
}

pub(crate) fn record_shadow_birth_level_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.birth_level_vars.insert(var);
    });
}

pub(crate) fn record_shadow_pre_pop_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.pre_pop_vars.insert(var);
    });
}

pub(crate) fn record_shadow_candidate_bucket_read(role: &[String]) {
    with_active_owner_reads(|reads| {
        reads.candidate_buckets.insert(role.to_vec());
    });
}

pub(crate) fn record_shadow_method_taint_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.taint_vars.insert(var);
    });
}

pub(crate) fn record_shadow_applied_resolution_read(key: &RoleResolutionKey, was_applied: bool) {
    with_active_owner_reads(|reads| {
        reads
            .applied_resolution_reads
            .insert(key.clone(), was_applied);
    });
}

fn with_active_owner_reads(f: impl FnOnce(&mut OwnerReadFrontier)) {
    ACTIVE_OWNER_READS.with(|active| {
        if let Some(reads) = active.borrow_mut().as_mut() {
            f(reads);
        }
    });
}

fn owner_selection_snapshot(
    session: &AnalysisSession,
    owner: DefId,
) -> Vec<(SelectId, SelectionUse)> {
    let mut selections = session
        .selections
        .iter()
        .filter(|(_, use_site)| use_site.parent == owner)
        .map(|(select, use_site)| (select, *use_site))
        .collect::<Vec<_>>();
    selections.sort_by_key(|(select, _)| select.0);
    selections
}

fn candidate_bucket_snapshot(
    roles: impl IntoIterator<Item = Vec<String>>,
    candidate_bucket_epochs: &FxHashMap<Vec<String>, u64>,
) -> Vec<(Vec<String>, u64)> {
    let mut buckets = roles
        .into_iter()
        .map(|role| {
            let epoch = candidate_bucket_epochs
                .get(&role)
                .copied()
                .unwrap_or_default();
            (role, epoch)
        })
        .collect::<Vec<_>>();
    buckets.sort_by(|(left, _), (right, _)| left.cmp(right));
    buckets
}

fn taint_projection_snapshot(
    method_taint: &MethodTaintIndex,
    vars: impl IntoIterator<Item = TypeVar>,
) -> Vec<(TypeVar, Option<Vec<SelectId>>)> {
    let mut projection = vars
        .into_iter()
        .map(|var| {
            let mut selects = method_taint.get(&var).cloned();
            if let Some(selects) = &mut selects {
                selects.sort_by_key(|select| select.0);
            }
            (var, selects)
        })
        .collect::<Vec<_>>();
    projection.sort_by_key(|(var, _)| var.0);
    projection
}

fn projection_selection_snapshot(
    session: &AnalysisSession,
    projection: &[(TypeVar, Option<Vec<SelectId>>)],
) -> Vec<(SelectId, SelectionUse)> {
    let mut select_ids = projection
        .iter()
        .filter_map(|(_, selects)| selects.as_ref())
        .flatten()
        .copied()
        .collect::<Vec<_>>();
    select_ids.sort_by_key(|select| select.0);
    select_ids.dedup();
    select_ids
        .into_iter()
        .filter_map(|select| {
            session
                .selections
                .get(select)
                .copied()
                .map(|use_site| (select, use_site))
        })
        .collect()
}

impl AnalysisSession {
    pub(super) fn shadow_dirty_oracle_begin_pass(
        &mut self,
        owners: &[DefId],
        method_taint: &MethodTaintIndex,
    ) {
        let Some(mut oracle) = self.shadow_dirty_oracle.take() else {
            return;
        };
        oracle.begin_pass(self, owners, method_taint);
        self.shadow_dirty_oracle = Some(oracle);
    }

    pub(super) fn shadow_dirty_oracle_finish_owner(
        &mut self,
        owner: DefId,
        root: Option<TypeVar>,
        progressed: bool,
        method_taint: &MethodTaintIndex,
        reads: OwnerReadFrontier,
    ) {
        let Some(mut oracle) = self.shadow_dirty_oracle.take() else {
            return;
        };
        oracle.finish_owner(self, owner, root, progressed, method_taint, reads);
        self.shadow_dirty_oracle = Some(oracle);
    }

    pub(super) fn shadow_dirty_oracle_candidate_inserted(&mut self, role: Vec<String>) {
        if let Some(oracle) = &mut self.shadow_dirty_oracle {
            oracle.bump_candidate_buckets([role]);
        }
    }

    pub(super) fn shadow_dirty_oracle_prerequisites_extended(&mut self, impl_def: DefId) {
        let Some(oracle) = &mut self.shadow_dirty_oracle else {
            return;
        };
        let roles = self
            .role_impls
            .iter()
            .filter(|candidate| candidate.impl_def == Some(impl_def))
            .map(|candidate| candidate.role.clone())
            .collect::<FxHashSet<_>>();
        oracle.bump_candidate_buckets(roles);
    }

    pub(crate) fn shadow_dirty_oracle_report(&self) -> Option<ShadowDirtyOracleReport> {
        self.shadow_dirty_oracle
            .as_ref()
            .map(ShadowDirtyOracle::report)
    }
}
