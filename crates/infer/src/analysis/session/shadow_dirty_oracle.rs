//! Test-only oracle for measuring owner-level method-role pass dirtiness.
//!
//! The production solver always runs. This module records only the state that an owner's real
//! solve read, predicts whether that state is unchanged on the next forced pass, and checks the
//! prediction against the real outcome.

use super::*;

use std::cell::{Cell, RefCell};

use crate::constraints::{ConstraintEffectFamily, SubtractFact};

use super::dirty_scheduling_contract::{DependencyKey, DependencyKeyKind};

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
    pub(crate) root_unavailable_outcomes: usize,
    pub(crate) no_progress_outcomes: usize,
    pub(crate) progress_outcomes: usize,
    pub(crate) owner_solve_time: Duration,
    pub(crate) predicted_clean_owner_solve_time: Duration,
    pub(crate) predicted_dirty_owner_solve_time: Duration,
    pub(crate) method_taint_rebuild_time: Duration,
    pub(crate) method_role_loop_time: Duration,
    pub(crate) dependency_cardinalities: Vec<usize>,
    pub(crate) dependency_inventory: ShadowDirtyDependencyInventory,
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
    pub(crate) root_unavailable_outcomes: usize,
    pub(crate) no_progress_outcomes: usize,
    pub(crate) progress_outcomes: usize,
    pub(crate) owner_solve_time: Duration,
    pub(crate) predicted_clean_owner_solve_time: Duration,
    pub(crate) predicted_dirty_owner_solve_time: Duration,
    pub(crate) dependency_cardinality_total: usize,
    pub(crate) dependency_cardinality_min: usize,
    pub(crate) dependency_cardinality_max: usize,
}

/// Counts the dependency-key-shaped entries observed across owner solves.
///
/// Root, raw-role, and owner-selection snapshots each correspond to one future journal key. The
/// remaining fields count the exact variables, buckets, selections, or resolution keys queried by
/// the current fingerprint. This makes the total a Stage 2 subscription-cost estimate rather than
/// a byte count of the test oracle's exact value snapshots.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct ShadowDirtyDependencyInventory {
    pub(crate) scc_roots: usize,
    pub(crate) owner_raw_roles: usize,
    pub(crate) owner_selections: usize,
    pub(crate) constraint_bounds: usize,
    pub(crate) constraint_neighbors: usize,
    pub(crate) constraint_subtract_facts: usize,
    pub(crate) constraint_levels: usize,
    pub(crate) constraint_birth_levels: usize,
    pub(crate) constraint_pre_pop_families: usize,
    pub(crate) candidate_buckets: usize,
    pub(crate) method_taint_entries: usize,
    pub(crate) projection_selections: usize,
    pub(crate) applied_resolutions: usize,
}

impl ShadowDirtyDependencyInventory {
    pub(crate) fn total(self) -> usize {
        self.scc_roots
            + self.owner_raw_roles
            + self.owner_selections
            + self.constraint_bounds
            + self.constraint_neighbors
            + self.constraint_subtract_facts
            + self.constraint_levels
            + self.constraint_birth_levels
            + self.constraint_pre_pop_families
            + self.candidate_buckets
            + self.method_taint_entries
            + self.projection_selections
            + self.applied_resolutions
    }

    /// Typed Stage 1 mapping for every field/read represented by the exact-value oracle.
    pub(crate) fn typed_key_kind_counts(self) -> [(DependencyKeyKind, usize); 13] {
        [
            (DependencyKeyKind::SccRoot, self.scc_roots),
            (DependencyKeyKind::OwnerRawRoles, self.owner_raw_roles),
            (DependencyKeyKind::OwnerSelections, self.owner_selections),
            (DependencyKeyKind::Selection, self.projection_selections),
            (DependencyKeyKind::ConstraintBounds, self.constraint_bounds),
            (
                DependencyKeyKind::ConstraintNeighbors,
                self.constraint_neighbors,
            ),
            (
                DependencyKeyKind::ConstraintSubtractFacts,
                self.constraint_subtract_facts,
            ),
            (DependencyKeyKind::ConstraintLevel, self.constraint_levels),
            (
                DependencyKeyKind::ConstraintBirthLevel,
                self.constraint_birth_levels,
            ),
            (
                DependencyKeyKind::ConstraintPrePopFamilies,
                self.constraint_pre_pop_families,
            ),
            (DependencyKeyKind::MethodTaint, self.method_taint_entries),
            (DependencyKeyKind::CandidateBucket, self.candidate_buckets),
            (
                DependencyKeyKind::AppliedResolution,
                self.applied_resolutions,
            ),
        ]
    }

    fn absorb(&mut self, other: Self) {
        self.scc_roots += other.scc_roots;
        self.owner_raw_roles += other.owner_raw_roles;
        self.owner_selections += other.owner_selections;
        self.constraint_bounds += other.constraint_bounds;
        self.constraint_neighbors += other.constraint_neighbors;
        self.constraint_subtract_facts += other.constraint_subtract_facts;
        self.constraint_levels += other.constraint_levels;
        self.constraint_birth_levels += other.constraint_birth_levels;
        self.constraint_pre_pop_families += other.constraint_pre_pop_families;
        self.candidate_buckets += other.candidate_buckets;
        self.method_taint_entries += other.method_taint_entries;
        self.projection_selections += other.projection_selections;
        self.applied_resolutions += other.applied_resolutions;
    }

    fn for_reads(
        session: &AnalysisSession,
        method_taint: &MethodTaintIndex,
        reads: &OwnerReadFrontier,
    ) -> Self {
        let taint_projection =
            taint_projection_snapshot(method_taint, reads.taint_vars.iter().copied());
        Self {
            scc_roots: 1,
            owner_raw_roles: 1,
            owner_selections: 1,
            constraint_bounds: reads.bound_vars.len(),
            constraint_neighbors: reads.neighbor_vars.len(),
            constraint_subtract_facts: reads.subtract_vars.len(),
            constraint_levels: reads.level_vars.len(),
            constraint_birth_levels: reads.birth_level_vars.len(),
            constraint_pre_pop_families: reads.pre_pop_vars.len(),
            candidate_buckets: reads.candidate_buckets.len(),
            method_taint_entries: reads.taint_vars.len(),
            projection_selections: projection_selection_snapshot(session, &taint_projection).len(),
            applied_resolutions: reads.applied_resolution_reads.len(),
        }
    }
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
    root_unavailable_outcomes: usize,
    no_progress_outcomes: usize,
    progress_outcomes: usize,
    owner_solve_time: Duration,
    predicted_clean_owner_solve_time: Duration,
    predicted_dirty_owner_solve_time: Duration,
    dependency_cardinalities: Vec<usize>,
    dependency_inventory: ShadowDirtyDependencyInventory,
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
        let dependency_inventory =
            ShadowDirtyDependencyInventory::for_reads(session, method_taint, &reads);
        let dependency_cardinality = dependency_inventory.total();
        let solve_duration = reads.solve_duration;

        self.owner_solve_time += solve_duration;
        self.dependency_cardinalities.push(dependency_cardinality);
        self.dependency_inventory.absorb(dependency_inventory);
        if prediction.clean {
            self.predicted_clean_owner_solve_time += solve_duration;
        } else {
            self.predicted_dirty_owner_solve_time += solve_duration;
        }
        match outcome {
            OwnerSolveOutcome::RootUnavailable => self.root_unavailable_outcomes += 1,
            OwnerSolveOutcome::NoProgress => self.no_progress_outcomes += 1,
            OwnerSolveOutcome::Progress => self.progress_outcomes += 1,
        }
        let metrics = self.owner_metrics.entry(owner).or_default();
        metrics.record_outcome(outcome);
        metrics.owner_solve_time += solve_duration;
        metrics.dependency_cardinality_total += dependency_cardinality;
        metrics.dependency_cardinality_min = metrics
            .dependency_cardinality_min
            .min(dependency_cardinality);
        metrics.dependency_cardinality_max = metrics
            .dependency_cardinality_max
            .max(dependency_cardinality);
        if prediction.clean {
            metrics.predicted_clean_owner_solve_time += solve_duration;
        } else {
            metrics.predicted_dirty_owner_solve_time += solve_duration;
        }
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

    fn report(
        &self,
        method_taint_rebuild_time: Duration,
        method_role_loop_time: Duration,
    ) -> ShadowDirtyOracleReport {
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
                root_unavailable_outcomes: metrics.root_unavailable_outcomes,
                no_progress_outcomes: metrics.no_progress_outcomes,
                progress_outcomes: metrics.progress_outcomes,
                owner_solve_time: metrics.owner_solve_time,
                predicted_clean_owner_solve_time: metrics.predicted_clean_owner_solve_time,
                predicted_dirty_owner_solve_time: metrics.predicted_dirty_owner_solve_time,
                dependency_cardinality_total: metrics.dependency_cardinality_total,
                dependency_cardinality_min: metrics.dependency_cardinality_min,
                dependency_cardinality_max: metrics.dependency_cardinality_max,
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
            root_unavailable_outcomes: self.root_unavailable_outcomes,
            no_progress_outcomes: self.no_progress_outcomes,
            progress_outcomes: self.progress_outcomes,
            owner_solve_time: self.owner_solve_time,
            predicted_clean_owner_solve_time: self.predicted_clean_owner_solve_time,
            predicted_dirty_owner_solve_time: self.predicted_dirty_owner_solve_time,
            method_taint_rebuild_time,
            method_role_loop_time,
            dependency_cardinalities: self.dependency_cardinalities.clone(),
            dependency_inventory: self.dependency_inventory,
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
pub(super) struct OwnerPrediction {
    pub(super) clean: bool,
    pub(super) cached_outcome: Option<OwnerSolveOutcome>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OwnerSolveOutcome {
    RootUnavailable,
    NoProgress,
    Progress,
}

impl OwnerSolveOutcome {
    pub(super) fn from_solve(root: Option<TypeVar>, progressed: bool) -> Self {
        match (root, progressed) {
            (None, _) => Self::RootUnavailable,
            (Some(_), false) => Self::NoProgress,
            (Some(_), true) => Self::Progress,
        }
    }

    pub(super) fn cacheable(self) -> bool {
        self != Self::Progress
    }

    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::RootUnavailable => "root-unavailable",
            Self::NoProgress => "no-progress",
            Self::Progress => "progress",
        }
    }
}

#[derive(Debug, Clone)]
struct OwnerMetrics {
    owner_checks: usize,
    predicted_clean: usize,
    predicted_dirty: usize,
    root_available_checks: usize,
    root_available_predicted_clean: usize,
    root_available_predicted_dirty: usize,
    root_unavailable_outcomes: usize,
    no_progress_outcomes: usize,
    progress_outcomes: usize,
    owner_solve_time: Duration,
    predicted_clean_owner_solve_time: Duration,
    predicted_dirty_owner_solve_time: Duration,
    dependency_cardinality_total: usize,
    dependency_cardinality_min: usize,
    dependency_cardinality_max: usize,
}

impl Default for OwnerMetrics {
    fn default() -> Self {
        Self {
            owner_checks: 0,
            predicted_clean: 0,
            predicted_dirty: 0,
            root_available_checks: 0,
            root_available_predicted_clean: 0,
            root_available_predicted_dirty: 0,
            root_unavailable_outcomes: 0,
            no_progress_outcomes: 0,
            progress_outcomes: 0,
            owner_solve_time: Duration::ZERO,
            predicted_clean_owner_solve_time: Duration::ZERO,
            predicted_dirty_owner_solve_time: Duration::ZERO,
            dependency_cardinality_total: 0,
            dependency_cardinality_min: usize::MAX,
            dependency_cardinality_max: 0,
        }
    }
}

impl OwnerMetrics {
    fn record_outcome(&mut self, outcome: OwnerSolveOutcome) {
        match outcome {
            OwnerSolveOutcome::RootUnavailable => self.root_unavailable_outcomes += 1,
            OwnerSolveOutcome::NoProgress => self.no_progress_outcomes += 1,
            OwnerSolveOutcome::Progress => self.progress_outcomes += 1,
        }
    }
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
        Self::capture_machine(session.infer.constraints(), reads)
    }

    fn capture_machine(
        machine: &crate::constraints::ConstraintMachine,
        reads: &OwnerReadFrontier,
    ) -> Self {
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
        self.matches_machine(session.infer.constraints())
    }

    fn matches_machine(&self, machine: &crate::constraints::ConstraintMachine) -> bool {
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
        let current = Self::capture_machine(machine, &reads);
        self.bounds == current.bounds
            && self.neighbors == current.neighbors
            && self.subtract_facts == current.subtract_facts
            && self.levels == current.levels
            && self.birth_levels == current.birth_levels
            && self.pre_pop_effect_families == current.pre_pop_effect_families
    }
}

impl crate::constraints::ConstraintMachine {
    /// Confirms that every constraint read API represented in the fingerprint reaches its hook.
    pub(crate) fn shadow_dirty_oracle_constraint_read_hook_inventory_for_test(
        &self,
        var: TypeVar,
    ) -> [bool; 6] {
        let guard = begin_shadow_owner_reads();
        let _ = self.bounds().of(var);
        let _ = self.var_neighbors(var).count();
        let _ = self.subtracts().facts(var);
        let _ = self.level_of(var);
        let _ = self.birth_level_of(var);
        let _ = self.pre_pop_effect_families(var);
        let reads = guard.finish();
        [
            reads.bound_vars.contains(&var),
            reads.neighbor_vars.contains(&var),
            reads.subtract_vars.contains(&var),
            reads.level_vars.contains(&var),
            reads.birth_level_vars.contains(&var),
            reads.pre_pop_vars.contains(&var),
        ]
    }

    /// Returns the typed Stage 1 keys reached through the six real constraint read hooks.
    pub(crate) fn shadow_dirty_oracle_constraint_dependency_keys_for_test(
        &self,
        var: TypeVar,
    ) -> Vec<DependencyKey> {
        let guard = begin_shadow_owner_reads();
        let _ = self.bounds().of(var);
        let _ = self.var_neighbors(var).count();
        let _ = self.subtracts().facts(var);
        let _ = self.level_of(var);
        let _ = self.birth_level_of(var);
        let _ = self.pre_pop_effect_families(var);
        guard.finish().constraint_dependency_keys()
    }

    /// Runs a focused mutation against the same bounds fingerprint used by the owner oracle.
    pub(crate) fn shadow_dirty_oracle_detects_bound_mutation_for_test(
        &mut self,
        var: TypeVar,
        mutate: impl FnOnce(&mut Self),
    ) -> bool {
        let reads = OwnerReadFrontier {
            bound_vars: [var].into_iter().collect(),
            ..OwnerReadFrontier::default()
        };
        let fingerprint = ConstraintDependencyFingerprint::capture_machine(self, &reads);
        mutate(self);
        !fingerprint.matches_machine(self)
    }
}

#[derive(Debug, Clone, Default)]
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
    solve_duration: Duration,
}

impl OwnerReadFrontier {
    fn constraint_dependency_keys(&self) -> Vec<DependencyKey> {
        let mut keys = Vec::new();
        keys.extend(
            self.bound_vars
                .iter()
                .copied()
                .map(DependencyKey::ConstraintBounds),
        );
        keys.extend(
            self.neighbor_vars
                .iter()
                .copied()
                .map(DependencyKey::ConstraintNeighbors),
        );
        keys.extend(
            self.subtract_vars
                .iter()
                .copied()
                .map(DependencyKey::ConstraintSubtractFacts),
        );
        keys.extend(
            self.level_vars
                .iter()
                .copied()
                .map(DependencyKey::ConstraintLevel),
        );
        keys.extend(
            self.birth_level_vars
                .iter()
                .copied()
                .map(DependencyKey::ConstraintBirthLevel),
        );
        keys.extend(
            self.pre_pop_vars
                .iter()
                .copied()
                .map(DependencyKey::ConstraintPrePopFamilies),
        );
        keys.sort_by_key(|key| key.kind().index());
        keys
    }

    pub(super) fn owner_dependency_keys(
        &self,
        owner: DefId,
        method_taint: &MethodTaintIndex,
    ) -> Vec<DependencyKey> {
        let mut keys = vec![
            DependencyKey::SccRoot(owner),
            DependencyKey::OwnerRawRoles(owner),
            DependencyKey::OwnerSelections(owner),
        ];
        keys.extend(self.constraint_dependency_keys());
        keys.extend(
            self.candidate_buckets
                .iter()
                .cloned()
                .map(DependencyKey::CandidateBucket),
        );
        for var in &self.taint_vars {
            keys.push(DependencyKey::MethodTaint(*var));
            if let Some(selects) = method_taint.get(var) {
                keys.extend(selects.iter().copied().map(DependencyKey::Selection));
            }
        }
        keys.extend(
            self.applied_resolution_reads
                .keys()
                .cloned()
                .map(DependencyKey::AppliedResolution),
        );
        keys
    }

    pub(super) fn solve_duration(&self) -> Duration {
        self.solve_duration
    }
}

pub(crate) struct ShadowOwnerReadGuard {
    active: bool,
    started_at: Instant,
}

impl ShadowOwnerReadGuard {
    pub(crate) fn finish(mut self) -> OwnerReadFrontier {
        let mut reads = ACTIVE_OWNER_READS.with(|active| {
            active
                .borrow_mut()
                .take()
                .expect("active shadow owner observation")
        });
        reads.solve_duration = self.started_at.elapsed();
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
    ShadowOwnerReadGuard {
        active: true,
        started_at: Instant::now(),
    }
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
    pub(super) fn shadow_dirty_oracle_prediction(&self, owner: DefId) -> Option<OwnerPrediction> {
        self.shadow_dirty_oracle
            .as_ref()
            .and_then(|oracle| oracle.current_predictions.get(&owner).copied())
    }

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
        let timing = self.timing();
        self.shadow_dirty_oracle
            .as_ref()
            .map(|oracle| oracle.report(timing.method_taint, timing.method_role_solve))
    }
}
