//! Journal-backed owner scheduler for production method-role passes.
//!
//! Maintained contract: `docs/infer-solver-invariants.md`,
//! `Owner-Level Dirty Scheduling`.
//!
//! Stage 6 enables clean terminal owner reuse for every new session. Tests retain explicit
//! always-solve and Stage 3 shadow modes, and the independent exact-snapshot oracle remains a
//! separate check on production scheduler predictions.

use super::*;

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::mem::size_of;
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

use crate::constraints::mutation::{
    InvalidateAllReason, MethodRoleMutationSubscriptions, MutationGeneration, MutationSerial,
};

thread_local! {
    static NEW_SESSION_MODE: Cell<OwnerDirtySchedulingMode> = const {
        Cell::new(OwnerDirtySchedulingMode::ProductionSkips)
    };
    static ACTIVE_OWNER_READS: RefCell<Option<OwnerReadFrontier>> = const {
        RefCell::new(None)
    };
}

/// Avoid touching TLS/`RefCell` on the default and non-owner hot paths.
///
/// A count rather than a boolean keeps concurrent scoped compilations correct: an unrelated
/// thread may see a non-zero count, but its own TLS slot remains empty and records nothing.
static ACTIVE_OWNER_READ_CAPTURE_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Scheduling route inherited by sessions created inside one explicit scoped call.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
enum OwnerDirtySchedulingMode {
    #[default]
    ProductionSkips,
    Disabled,
    #[cfg(test)]
    ShadowAlwaysSolve,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct ExactOwnerPrediction {
    pub(super) clean: bool,
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

/// Dependencies observed while the unchanged owner solver runs.
#[derive(Debug, Clone, Default)]
pub(crate) struct OwnerReadFrontier {
    /// Constraint dependencies collected by the production scheduler's explicit compact walk.
    ///
    /// Test builds separately populate test-only typed fields through the Stage 3 exact read
    /// hooks. Keeping the two sources disjoint preserves the shadow oracle's independence from
    /// the production-shaped conservative collector.
    pub(super) production_constraint_dependencies: FxHashSet<DependencyKey>,
    #[cfg(test)]
    pub(super) bound_vars: FxHashSet<TypeVar>,
    #[cfg(test)]
    pub(super) neighbor_vars: FxHashSet<TypeVar>,
    #[cfg(test)]
    pub(super) subtract_vars: FxHashSet<TypeVar>,
    #[cfg(test)]
    pub(super) level_vars: FxHashSet<TypeVar>,
    #[cfg(test)]
    pub(super) birth_level_vars: FxHashSet<TypeVar>,
    #[cfg(test)]
    pub(super) pre_pop_vars: FxHashSet<TypeVar>,
    pub(super) candidate_buckets: FxHashSet<Vec<String>>,
    pub(super) taint_vars: FxHashSet<TypeVar>,
    pub(super) applied_resolution_reads: FxHashMap<RoleResolutionKey, bool>,
    pub(super) solve_duration: Duration,
}

impl OwnerReadFrontier {
    #[cfg(test)]
    pub(super) fn constraint_dependency_keys(&self) -> Vec<DependencyKey> {
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
        keys
    }

    fn scheduler_owner_dependency_keys(
        &self,
        owner: DefId,
        method_taint: &MethodTaintIndex,
    ) -> Vec<DependencyKey> {
        self.owner_dependency_keys_with_constraints(
            owner,
            method_taint,
            self.production_constraint_dependencies.iter().cloned(),
        )
    }

    fn owner_dependency_keys_with_constraints(
        &self,
        owner: DefId,
        method_taint: &MethodTaintIndex,
        constraint_dependencies: impl IntoIterator<Item = DependencyKey>,
    ) -> Vec<DependencyKey> {
        let mut keys = vec![
            DependencyKey::SccRoot(owner),
            DependencyKey::OwnerRawRoles(owner),
            DependencyKey::OwnerSelections(owner),
        ];
        keys.extend(constraint_dependencies);
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

pub(crate) struct OwnerReadGuard {
    active: bool,
    started_at: Instant,
}

impl OwnerReadGuard {
    pub(crate) fn finish(mut self) -> OwnerReadFrontier {
        let mut reads = ACTIVE_OWNER_READS.with(|active| {
            active
                .borrow_mut()
                .take()
                .expect("active owner dependency capture")
        });
        reads.solve_duration = self.started_at.elapsed();
        ACTIVE_OWNER_READ_CAPTURE_COUNT.fetch_sub(1, AtomicOrdering::Relaxed);
        self.active = false;
        reads
    }
}

impl Drop for OwnerReadGuard {
    fn drop(&mut self) {
        if self.active {
            ACTIVE_OWNER_READS.with(|active| {
                active.borrow_mut().take();
            });
            ACTIVE_OWNER_READ_CAPTURE_COUNT.fetch_sub(1, AtomicOrdering::Relaxed);
        }
    }
}

pub(crate) fn begin_owner_dependency_reads() -> OwnerReadGuard {
    ACTIVE_OWNER_READS.with(|active| {
        assert!(
            active
                .borrow_mut()
                .replace(OwnerReadFrontier::default())
                .is_none(),
            "owner dependency capture must not nest"
        );
    });
    ACTIVE_OWNER_READ_CAPTURE_COUNT.fetch_add(1, AtomicOrdering::Relaxed);
    OwnerReadGuard {
        active: true,
        started_at: Instant::now(),
    }
}

#[cfg(test)]
pub(crate) fn record_owner_bound_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.bound_vars.insert(var);
    });
}

pub(crate) fn record_owner_dependency_read(key: DependencyKey) {
    match key {
        key @ (DependencyKey::ConstraintBounds(_)
        | DependencyKey::ConstraintNeighbors(_)
        | DependencyKey::ConstraintSubtractFacts(_)
        | DependencyKey::ConstraintLevel(_)
        | DependencyKey::ConstraintBirthLevel(_)
        | DependencyKey::ConstraintPrePopFamilies(_)) => {
            with_active_owner_reads(|reads| {
                reads.production_constraint_dependencies.insert(key);
            });
        }
        DependencyKey::SccRoot(_)
        | DependencyKey::OwnerRawRoles(_)
        | DependencyKey::OwnerSelections(_)
        | DependencyKey::Selection(_)
        | DependencyKey::MethodTaint(_)
        | DependencyKey::CandidateBucket(_)
        | DependencyKey::AppliedResolution(_) => {
            panic!("explicit owner constraint capture received a non-constraint dependency")
        }
    }
}

#[cfg(test)]
pub(crate) fn record_owner_neighbor_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.neighbor_vars.insert(var);
    });
}

#[cfg(test)]
pub(crate) fn record_owner_subtract_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.subtract_vars.insert(var);
    });
}

#[cfg(test)]
pub(crate) fn record_owner_level_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.level_vars.insert(var);
    });
}

#[cfg(test)]
pub(crate) fn record_owner_birth_level_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.birth_level_vars.insert(var);
    });
}

#[cfg(test)]
pub(crate) fn record_owner_pre_pop_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.pre_pop_vars.insert(var);
    });
}

pub(crate) fn record_owner_candidate_bucket_read(role: &[String]) {
    with_active_owner_reads(|reads| {
        reads.candidate_buckets.insert(role.to_vec());
    });
}

pub(crate) fn record_owner_method_taint_read(var: TypeVar) {
    with_active_owner_reads(|reads| {
        reads.taint_vars.insert(var);
    });
}

pub(crate) fn record_owner_applied_resolution_read(key: &RoleResolutionKey, was_applied: bool) {
    with_active_owner_reads(|reads| {
        reads
            .applied_resolution_reads
            .insert(key.clone(), was_applied);
    });
}

#[inline]
fn with_active_owner_reads(f: impl FnOnce(&mut OwnerReadFrontier)) {
    if ACTIVE_OWNER_READ_CAPTURE_COUNT.load(AtomicOrdering::Relaxed) == 0 {
        return;
    }
    ACTIVE_OWNER_READS.with(|active| {
        if let Some(reads) = active.borrow_mut().as_mut() {
            f(reads);
        }
    });
}

/// Session-owned record, reverse-subscription, and dirty state for method-role owners.
#[derive(Debug, Default)]
pub(crate) struct MethodRoleOwnerDirtyScheduler {
    permit_owner_skips: bool,
    budget: OwnerDirtySchedulerBudget,
    records: FxHashMap<DefId, CachedOwnerTerminal>,
    reverse_subscriptions: FxHashMap<DependencyKey, FxHashSet<DefId>>,
    mutation_subscriptions: MethodRoleMutationSubscriptions,
    dirty: FxHashSet<DefId>,
    generations: FxHashMap<DependencyKey, MutationGeneration>,
    drained_mutation_serial: MutationSerial,
    method_taint_snapshot: MethodTaintIndex,
    current_predictions: FxHashMap<DefId, JournalOwnerPrediction>,
    last_journal_window_end: Option<MethodRolePassInputSnapshot>,
    inactive_window_changed: bool,
    force_all_dirty_this_pass: bool,
    prepared_this_pass: FxHashSet<DefId>,
    metrics: OwnerDirtySchedulerMetrics,
}

/// Approved Stage 5 hard limits, with roughly 8-10x headroom over representative fixture peaks.
#[derive(Debug, Clone, Copy)]
struct OwnerDirtySchedulerBudget {
    max_owners: Option<usize>,
    max_dependencies_per_owner: Option<usize>,
    max_dependency_keys: Option<usize>,
    max_reverse_edges: Option<usize>,
    max_journal_burst: Option<usize>,
    max_retained_bytes: Option<usize>,
}

impl Default for OwnerDirtySchedulerBudget {
    fn default() -> Self {
        Self {
            max_owners: Some(1_000),
            max_dependencies_per_owner: Some(2_000),
            max_dependency_keys: Some(250_000),
            max_reverse_edges: Some(25_000),
            max_journal_burst: Some(500_000),
            max_retained_bytes: Some(33_554_432),
        }
    }
}

#[cfg(test)]
thread_local! {
    static NEW_SESSION_BUDGET_OVERRIDE: Cell<Option<OwnerDirtySchedulerBudget>> = const {
        Cell::new(None)
    };
}

impl MethodRoleOwnerDirtyScheduler {
    pub(super) fn for_new_session() -> Option<Self> {
        match NEW_SESSION_MODE.with(Cell::get) {
            OwnerDirtySchedulingMode::ProductionSkips => Some(Self {
                permit_owner_skips: true,
                budget: budget_for_new_session(),
                ..Self::default()
            }),
            OwnerDirtySchedulingMode::Disabled => None,
            #[cfg(test)]
            OwnerDirtySchedulingMode::ShadowAlwaysSolve => Some(Self::default()),
        }
    }

    fn begin_journal_window(&mut self, current: MethodRolePassInputSnapshot) {
        self.inactive_window_changed = self.last_journal_window_end.is_some_and(|previous| {
            if previous.constraint_epoch != current.constraint_epoch {
                self.metrics.inactive_constraint_epoch_changes += 1;
            }
            if previous.role_epoch != current.role_epoch {
                self.metrics.inactive_role_epoch_changes += 1;
            }
            if previous.input_generation != current.input_generation {
                self.metrics.inactive_input_generation_changes += 1;
            }
            if previous.contract_generation != current.contract_generation {
                self.metrics.inactive_contract_generation_changes += 1;
            }
            previous != current
        });
    }

    fn finish_journal_window(&mut self, current: MethodRolePassInputSnapshot) {
        self.last_journal_window_end = Some(current);
    }

    fn begin_pass(
        &mut self,
        owners: &[DefId],
        method_taint: &MethodTaintIndex,
    ) -> Vec<DependencyKey> {
        let taint_diff_start = Instant::now();
        debug_assert!(self.current_predictions.is_empty());
        self.prepared_this_pass.clear();
        self.metrics.forced_passes += 1;
        self.force_all_dirty_this_pass = false;

        let current_owners = owners.iter().copied().collect::<FxHashSet<_>>();
        let stale = self
            .records
            .keys()
            .copied()
            .filter(|owner| !current_owners.contains(owner))
            .collect::<Vec<_>>();
        for owner in stale {
            self.remove_owner(owner);
        }

        if self.inactive_window_changed {
            self.invalidate_all_for_pass(InvalidateAllReason::UnrecognizedMutation {
                site: "inactive method-role journal window",
            });
        }
        self.inactive_window_changed = false;

        let changed = diff_method_taint(&self.method_taint_snapshot, method_taint);
        self.method_taint_snapshot = normalized_method_taint(method_taint);
        let mutations = changed
            .into_iter()
            .map(DependencyKey::MethodTaint)
            .collect();
        self.metrics.method_taint_diff_time += taint_diff_start.elapsed();
        mutations
    }

    fn drain_mutations(&mut self, mutations: Vec<MethodRoleMutation>, owner_eligibility: bool) {
        let drain_start = Instant::now();
        let burst = mutations.len();
        if burst > 0 {
            self.metrics.journal_bursts += 1;
            self.metrics.journal_mutations += burst;
            self.metrics.peak_journal_burst = self.metrics.peak_journal_burst.max(burst);
        }
        if self.budget.max_journal_burst.is_some_and(|cap| burst > cap) {
            self.fallback_for_global_cap();
            self.metrics.journal_drain_time += drain_start.elapsed();
            return;
        }
        for mutation in mutations {
            match mutation {
                MethodRoleMutation::Changed { serial, key } => {
                    if !self.observe_changed_serial(serial) {
                        self.invalidate_all_for_pass(InvalidateAllReason::JournalTruncated);
                        continue;
                    }
                    let generation = self.generations.get(&key).copied().unwrap_or_default();
                    let Some(next) = generation.checked_next() else {
                        self.invalidate_all_for_pass(
                            InvalidateAllReason::MutationGenerationOverflow,
                        );
                        continue;
                    };
                    self.generations.insert(key.clone(), next);
                    if let Some(owners) = self.reverse_subscriptions.get(&key) {
                        self.dirty.extend(owners.iter().copied());
                    }
                    self.metrics.changed_mutations += 1;
                }
                MethodRoleMutation::InvalidateAll { serial, reason } => {
                    if serial >= self.drained_mutation_serial {
                        self.drained_mutation_serial = serial;
                    }
                    self.invalidate_all_for_pass(reason);
                }
            }
        }
        if !owner_eligibility && !self.force_all_dirty_this_pass {
            self.invalidate_all_for_pass(InvalidateAllReason::AuditFenceDisagreement {
                site: "MethodRoleMutationOutbox::owner_eligibility",
            });
        }
        self.metrics.journal_drain_time += drain_start.elapsed();
        self.update_memory_peaks();
    }

    fn prepare_owner(
        &mut self,
        owner: DefId,
        root_available: bool,
        exact: Option<ExactOwnerPrediction>,
    ) -> OwnerScheduleDecision {
        let skip_check_start = Instant::now();
        assert!(
            self.prepared_this_pass.insert(owner),
            "one owner must not be scheduled more than once in a forced method-role pass"
        );
        let prediction = self.prediction(owner);
        self.metrics.owner_checks += 1;
        let owner_metrics = self.metrics.owners.entry(owner).or_default();
        owner_metrics.owner_checks += 1;
        if root_available {
            self.metrics.root_available_checks += 1;
            owner_metrics.root_available_checks += 1;
        }
        if prediction.clean {
            self.metrics.predicted_clean += 1;
            owner_metrics.predicted_clean += 1;
            if root_available {
                self.metrics.root_available_predicted_clean += 1;
                owner_metrics.root_available_predicted_clean += 1;
            }
        } else {
            self.metrics.predicted_dirty += 1;
            owner_metrics.predicted_dirty += 1;
            if root_available {
                self.metrics.root_available_predicted_dirty += 1;
                owner_metrics.root_available_predicted_dirty += 1;
            }
        }

        if let Some(exact) = exact {
            match (prediction.clean, exact.clean) {
                (true, true) | (false, false) => self.metrics.oracle_agreements += 1,
                (false, true) => {
                    self.metrics
                        .conservative_divergences
                        .push(OwnerPredictionDivergence {
                            pass: self.metrics.forced_passes,
                            owner,
                            journal_clean: false,
                            exact_clean: true,
                            reason: prediction.reason,
                        })
                }
                (true, false) => {
                    self.metrics
                        .permissive_divergences
                        .push(OwnerPredictionDivergence {
                            pass: self.metrics.forced_passes,
                            owner,
                            journal_clean: true,
                            exact_clean: false,
                            reason: prediction.reason,
                        })
                }
            }
        }

        if self.permit_owner_skips && prediction.clean {
            let outcome = prediction
                .cached_outcome
                .expect("a clean owner prediction must carry its cached terminal outcome");
            assert!(
                outcome.cacheable(),
                "only RootUnavailable/NoProgress terminal outcomes may be replayed"
            );
            self.metrics.clean_skips += 1;
            self.metrics.clean_skip_time += skip_check_start.elapsed();
            owner_metrics.clean_skips += 1;
            owner_metrics.record_reused_outcome(outcome);
            return OwnerScheduleDecision::Reuse(outcome);
        }

        self.metrics.real_solves += 1;
        owner_metrics.real_solves += 1;
        self.current_predictions.insert(owner, prediction);
        self.detach_record(owner);
        self.dirty.remove(&owner);
        OwnerScheduleDecision::Solve
    }

    fn finish_owner(
        &mut self,
        owner: DefId,
        outcome: OwnerSolveOutcome,
        dependencies: Vec<DependencyKey>,
        solve_duration: Duration,
        still_unresolved: bool,
    ) {
        let prediction = self
            .current_predictions
            .remove(&owner)
            .expect("every journal-backed owner observation has a prediction");
        self.metrics.owner_solve_time += solve_duration;
        let owner_metrics = self.metrics.owners.entry(owner).or_default();
        owner_metrics.owner_solve_time += solve_duration;
        owner_metrics.record_outcome(outcome);
        if prediction.clean {
            self.metrics.predicted_clean_owner_solve_time += solve_duration;
            owner_metrics.predicted_clean_owner_solve_time += solve_duration;
            if prediction.cached_outcome == Some(outcome) {
                self.metrics.would_have_been_clean_hits += 1;
                owner_metrics.would_have_been_clean_hits += 1;
            } else {
                self.metrics.would_have_been_clean_misses += 1;
                owner_metrics.would_have_been_clean_misses += 1;
                self.metrics.mismatches.push(OwnerDirtySchedulerMismatch {
                    pass: self.metrics.forced_passes,
                    owner,
                    expected: prediction
                        .cached_outcome
                        .map(OwnerSolveOutcome::as_str)
                        .unwrap_or("missing-cache"),
                    actual: outcome.as_str(),
                });
            }
        } else {
            self.metrics.predicted_dirty_owner_solve_time += solve_duration;
            owner_metrics.predicted_dirty_owner_solve_time += solve_duration;
        }

        if outcome.cacheable() && still_unresolved {
            self.publish_record(owner, outcome, dependencies);
        }
    }

    fn prediction(&mut self, owner: DefId) -> JournalOwnerPrediction {
        if self.force_all_dirty_this_pass {
            return JournalOwnerPrediction::dirty(OwnerPredictionReason::FullInvalidation);
        }
        let Some(record) = self.records.get(&owner) else {
            return JournalOwnerPrediction::dirty(OwnerPredictionReason::MissingRecord);
        };
        if self.dirty.contains(&owner) {
            return JournalOwnerPrediction::dirty(OwnerPredictionReason::TouchedDependency);
        }
        if !record.fingerprint.dependencies.iter().all(|stamp| {
            self.generations
                .get(&stamp.key)
                .copied()
                .unwrap_or_default()
                == stamp.generation
        }) {
            self.invalidate_all_for_pass(InvalidateAllReason::AuditFenceDisagreement {
                site: "MethodRoleOwnerDirtyScheduler::dependency_stamp",
            });
            return JournalOwnerPrediction::dirty(OwnerPredictionReason::GenerationMismatch);
        }
        JournalOwnerPrediction {
            clean: true,
            cached_outcome: Some(record.outcome),
            reason: OwnerPredictionReason::CleanRecord,
        }
    }

    fn publish_record(
        &mut self,
        owner: DefId,
        outcome: OwnerSolveOutcome,
        dependencies: Vec<DependencyKey>,
    ) {
        assert!(
            outcome.cacheable(),
            "progressing owner outcomes must never enter the terminal cache"
        );
        let dependencies = normalize_dependencies(dependencies);
        self.metrics.peak_dependencies_per_owner = self
            .metrics
            .peak_dependencies_per_owner
            .max(dependencies.len());
        if self
            .budget
            .max_dependencies_per_owner
            .is_some_and(|cap| dependencies.len() > cap)
        {
            self.metrics.per_owner_cap_rejections += 1;
            return;
        }
        let stamps = dependencies
            .iter()
            .map(|key| DependencyStamp {
                key: key.clone(),
                generation: self.generations.get(key).copied().unwrap_or_default(),
            })
            .collect::<Vec<_>>();
        let record = CachedOwnerTerminal {
            outcome,
            fingerprint: JournalOwnerDependencyFingerprint {
                dependencies: stamps,
                capture_serial: self.drained_mutation_serial,
            },
        };

        if self.detach_record(owner).is_some() {
            self.metrics.record_replacements += 1;
        }
        for key in &dependencies {
            let subscribed = self
                .reverse_subscriptions
                .entry(key.clone())
                .or_default()
                .insert(owner);
            if subscribed {
                self.mutation_subscriptions.insert(key.clone());
            }
        }
        self.records.insert(owner, record);
        self.dirty.remove(&owner);
        self.update_memory_peaks();
        if self.global_budget_exceeded() {
            self.fallback_for_global_cap();
        }
    }

    fn remove_owner(&mut self, owner: DefId) {
        if self.detach_record(owner).is_some() {
            self.metrics.lifecycle_evictions += 1;
        }
        self.dirty.remove(&owner);
        self.current_predictions.remove(&owner);
    }

    fn detach_record(&mut self, owner: DefId) -> Option<CachedOwnerTerminal> {
        let record = self.records.remove(&owner)?;
        for stamp in &record.fingerprint.dependencies {
            let remove_key = if let Some(owners) = self.reverse_subscriptions.get_mut(&stamp.key) {
                owners.remove(&owner);
                owners.is_empty()
            } else {
                false
            };
            if remove_key {
                self.reverse_subscriptions.remove(&stamp.key);
                self.mutation_subscriptions.remove(&stamp.key);
            }
        }
        Some(record)
    }

    fn invalidate_all_for_pass(&mut self, reason: InvalidateAllReason) {
        if !self.force_all_dirty_this_pass {
            self.metrics.full_fallbacks += 1;
        }
        self.force_all_dirty_this_pass = true;
        self.dirty.extend(self.records.keys().copied());
        self.metrics.invalidate_all_reasons.push(reason);
    }

    fn observe_changed_serial(&mut self, serial: MutationSerial) -> bool {
        if serial == self.drained_mutation_serial {
            return true;
        }
        if self.drained_mutation_serial.checked_next() != Some(serial) {
            return false;
        }
        self.drained_mutation_serial = serial;
        true
    }

    fn reverse_edge_count(&self) -> usize {
        self.reverse_subscriptions
            .values()
            .map(FxHashSet::len)
            .sum()
    }

    fn global_budget_exceeded(&self) -> bool {
        self.budget
            .max_owners
            .is_some_and(|cap| self.records.len() > cap)
            || self
                .budget
                .max_dependency_keys
                .is_some_and(|cap| self.generations.len() > cap)
            || self
                .budget
                .max_reverse_edges
                .is_some_and(|cap| self.reverse_edge_count() > cap)
            || self
                .budget
                .max_retained_bytes
                .is_some_and(|cap| self.retained_bytes() > cap)
    }

    fn fallback_for_global_cap(&mut self) {
        if !self.force_all_dirty_this_pass {
            self.metrics.full_fallbacks += 1;
        }
        self.metrics.global_cap_fallbacks += 1;
        self.force_all_dirty_this_pass = true;
        self.records.clear();
        self.reverse_subscriptions.clear();
        self.mutation_subscriptions.clear();
        self.dirty.clear();
        self.update_memory_peaks();
    }

    fn update_memory_peaks(&mut self) {
        self.metrics.peak_records = self.metrics.peak_records.max(self.records.len());
        self.metrics.peak_dependency_keys = self
            .metrics
            .peak_dependency_keys
            .max(self.reverse_subscriptions.len());
        self.metrics.peak_generation_keys = self
            .metrics
            .peak_generation_keys
            .max(self.generations.len());
        self.metrics.peak_reverse_edges = self
            .metrics
            .peak_reverse_edges
            .max(self.reverse_edge_count());
        self.metrics.peak_retained_bytes =
            self.metrics.peak_retained_bytes.max(self.retained_bytes());
    }

    /// Stable retained-byte estimate for scheduler tables and visible nested buffers.
    ///
    /// Allocator control bytes and heap buffers hidden inside compound key fields are unavailable
    /// through stable APIs. The same explicit accounting is used for measurement and cap checks,
    /// so the proposed byte cap is tied to this estimate rather than allocator RSS.
    fn retained_bytes(&self) -> usize {
        let mut bytes = size_of::<Self>();
        bytes += map_capacity_bytes::<DefId, CachedOwnerTerminal>(self.records.capacity());
        bytes += map_capacity_bytes::<DependencyKey, FxHashSet<DefId>>(
            self.reverse_subscriptions.capacity(),
        );
        bytes += set_capacity_bytes::<DefId>(self.dirty.capacity());
        bytes +=
            map_capacity_bytes::<DependencyKey, MutationGeneration>(self.generations.capacity());
        bytes +=
            map_capacity_bytes::<TypeVar, Vec<SelectId>>(self.method_taint_snapshot.capacity());
        bytes += map_capacity_bytes::<DefId, JournalOwnerPrediction>(
            self.current_predictions.capacity(),
        );
        bytes += set_capacity_bytes::<DefId>(self.prepared_this_pass.capacity());
        bytes += map_capacity_bytes::<DefId, OwnerDirtySchedulerOwnerMetrics>(
            self.metrics.owners.capacity(),
        );
        bytes += self.metrics.conservative_divergences.capacity()
            * size_of::<OwnerPredictionDivergence>();
        bytes +=
            self.metrics.permissive_divergences.capacity() * size_of::<OwnerPredictionDivergence>();
        bytes += self.metrics.mismatches.capacity() * size_of::<OwnerDirtySchedulerMismatch>();
        bytes += self.metrics.invalidate_all_reasons.capacity() * size_of::<InvalidateAllReason>();

        for record in self.records.values() {
            bytes += record.fingerprint.dependencies.capacity() * size_of::<DependencyStamp>();
            bytes += record
                .fingerprint
                .dependencies
                .iter()
                .map(|stamp| dependency_key_heap_bytes(&stamp.key))
                .sum::<usize>();
        }
        for (key, owners) in &self.reverse_subscriptions {
            bytes += dependency_key_heap_bytes(key);
            bytes += set_capacity_bytes::<DefId>(owners.capacity());
        }
        let mutation_subscriptions = self.mutation_subscriptions.keys();
        bytes += set_capacity_bytes::<DependencyKey>(mutation_subscriptions.capacity());
        bytes += mutation_subscriptions
            .iter()
            .map(dependency_key_heap_bytes)
            .sum::<usize>();
        for key in self.generations.keys() {
            bytes += dependency_key_heap_bytes(key);
        }
        for selects in self.method_taint_snapshot.values() {
            bytes += selects.capacity() * size_of::<SelectId>();
        }
        bytes
    }

    pub(super) fn record_timing(&self, timing: &mut AnalysisTiming) {
        timing.owner_dirty_skip = self.metrics.clean_skip_time;
        timing.owner_dirty_owner_solve = self.metrics.owner_solve_time;
        timing.owner_dirty_journal_drain = self.metrics.journal_drain_time;
        timing.owner_dirty_method_taint_diff = self.metrics.method_taint_diff_time;
        timing.owner_dirty_clean_owner_skips = self.metrics.clean_skips;
        timing.owner_dirty_dirty_solves = self.metrics.real_solves;
        timing.owner_dirty_full_fallbacks = self.metrics.full_fallbacks;
        timing.owner_dirty_journal_bursts = self.metrics.journal_bursts;
        timing.owner_dirty_journal_mutations = self.metrics.journal_mutations;
        timing.owner_dirty_peak_journal_burst = self.metrics.peak_journal_burst;
        timing.owner_dirty_peak_owners = self.metrics.peak_records;
        timing.owner_dirty_peak_dependency_keys = self.metrics.peak_generation_keys;
        timing.owner_dirty_peak_dependencies_per_owner = self.metrics.peak_dependencies_per_owner;
        timing.owner_dirty_peak_reverse_edges = self.metrics.peak_reverse_edges;
        timing.owner_dirty_peak_retained_bytes = self.metrics.peak_retained_bytes;
        timing.owner_dirty_live_owners = self.records.len();
        timing.owner_dirty_live_dependency_keys = self.generations.len();
        timing.owner_dirty_live_reverse_edges = self.reverse_edge_count();
        timing.owner_dirty_live_retained_bytes = self.retained_bytes();
        timing.owner_dirty_per_owner_cap_rejections = self.metrics.per_owner_cap_rejections;
        timing.owner_dirty_global_cap_fallbacks = self.metrics.global_cap_fallbacks;
    }

    #[cfg(test)]
    fn report(&self) -> OwnerDirtySchedulerReport {
        let mut owners = self
            .metrics
            .owners
            .iter()
            .map(|(owner, metrics)| OwnerDirtySchedulerOwnerReport {
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
                would_have_been_clean_hits: metrics.would_have_been_clean_hits,
                would_have_been_clean_misses: metrics.would_have_been_clean_misses,
                real_solves: metrics.real_solves,
                clean_skips: metrics.clean_skips,
                reused_root_unavailable: metrics.reused_root_unavailable,
                reused_no_progress: metrics.reused_no_progress,
            })
            .collect::<Vec<_>>();
        owners.sort_by_key(|metrics| metrics.owner.0);
        OwnerDirtySchedulerReport {
            forced_passes: self.metrics.forced_passes,
            owner_checks: self.metrics.owner_checks,
            predicted_clean: self.metrics.predicted_clean,
            predicted_dirty: self.metrics.predicted_dirty,
            root_available_checks: self.metrics.root_available_checks,
            root_available_predicted_clean: self.metrics.root_available_predicted_clean,
            root_available_predicted_dirty: self.metrics.root_available_predicted_dirty,
            owner_solve_time: self.metrics.owner_solve_time,
            predicted_clean_owner_solve_time: self.metrics.predicted_clean_owner_solve_time,
            predicted_dirty_owner_solve_time: self.metrics.predicted_dirty_owner_solve_time,
            would_have_been_clean_hits: self.metrics.would_have_been_clean_hits,
            would_have_been_clean_misses: self.metrics.would_have_been_clean_misses,
            real_solves: self.metrics.real_solves,
            clean_skips: self.metrics.clean_skips,
            changed_mutations: self.metrics.changed_mutations,
            oracle_agreements: self.metrics.oracle_agreements,
            conservative_divergences: self.metrics.conservative_divergences.clone(),
            permissive_divergences: self.metrics.permissive_divergences.clone(),
            mismatches: self.metrics.mismatches.clone(),
            invalidate_all_reasons: self.metrics.invalidate_all_reasons.clone(),
            lifecycle_evictions: self.metrics.lifecycle_evictions,
            record_replacements: self.metrics.record_replacements,
            peak_records: self.metrics.peak_records,
            peak_dependency_keys: self.metrics.peak_dependency_keys,
            peak_reverse_edges: self.metrics.peak_reverse_edges,
            live_records: self.records.len(),
            live_dependency_keys: self.reverse_subscriptions.len(),
            live_reverse_edges: self.reverse_edge_count(),
            inactive_constraint_epoch_changes: self.metrics.inactive_constraint_epoch_changes,
            inactive_role_epoch_changes: self.metrics.inactive_role_epoch_changes,
            inactive_input_generation_changes: self.metrics.inactive_input_generation_changes,
            inactive_contract_generation_changes: self.metrics.inactive_contract_generation_changes,
            owners,
        }
    }
}

fn budget_for_new_session() -> OwnerDirtySchedulerBudget {
    #[cfg(test)]
    if let Some(budget) = NEW_SESSION_BUDGET_OVERRIDE.with(Cell::get) {
        return budget;
    }
    OwnerDirtySchedulerBudget::default()
}

#[derive(Debug, Clone)]
struct CachedOwnerTerminal {
    outcome: OwnerSolveOutcome,
    fingerprint: JournalOwnerDependencyFingerprint,
}

#[derive(Debug, Clone)]
struct JournalOwnerDependencyFingerprint {
    dependencies: Vec<DependencyStamp>,
    #[allow(
        dead_code,
        reason = "retained for serial audit and always-solve eligibility assertions"
    )]
    capture_serial: MutationSerial,
}

#[derive(Debug, Clone)]
struct DependencyStamp {
    key: DependencyKey,
    generation: MutationGeneration,
}

#[derive(Debug, Clone, Copy)]
struct JournalOwnerPrediction {
    clean: bool,
    cached_outcome: Option<OwnerSolveOutcome>,
    reason: OwnerPredictionReason,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OwnerScheduleDecision {
    Solve,
    Reuse(OwnerSolveOutcome),
}

impl JournalOwnerPrediction {
    fn dirty(reason: OwnerPredictionReason) -> Self {
        Self {
            clean: false,
            cached_outcome: None,
            reason,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum OwnerPredictionReason {
    CleanRecord,
    MissingRecord,
    TouchedDependency,
    FullInvalidation,
    GenerationMismatch,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OwnerDirtySchedulerMismatch {
    pub(crate) pass: usize,
    pub(crate) owner: DefId,
    pub(crate) expected: &'static str,
    pub(crate) actual: &'static str,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OwnerPredictionDivergence {
    pub(crate) pass: usize,
    pub(crate) owner: DefId,
    pub(crate) journal_clean: bool,
    pub(crate) exact_clean: bool,
    pub(crate) reason: OwnerPredictionReason,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[cfg(test)]
pub(crate) struct OwnerDirtySchedulerReport {
    pub(crate) forced_passes: usize,
    pub(crate) owner_checks: usize,
    pub(crate) predicted_clean: usize,
    pub(crate) predicted_dirty: usize,
    pub(crate) root_available_checks: usize,
    pub(crate) root_available_predicted_clean: usize,
    pub(crate) root_available_predicted_dirty: usize,
    pub(crate) owner_solve_time: Duration,
    pub(crate) predicted_clean_owner_solve_time: Duration,
    pub(crate) predicted_dirty_owner_solve_time: Duration,
    pub(crate) would_have_been_clean_hits: usize,
    pub(crate) would_have_been_clean_misses: usize,
    pub(crate) real_solves: usize,
    pub(crate) clean_skips: usize,
    pub(crate) changed_mutations: usize,
    pub(crate) oracle_agreements: usize,
    pub(crate) conservative_divergences: Vec<OwnerPredictionDivergence>,
    pub(crate) permissive_divergences: Vec<OwnerPredictionDivergence>,
    pub(crate) mismatches: Vec<OwnerDirtySchedulerMismatch>,
    pub(crate) invalidate_all_reasons: Vec<InvalidateAllReason>,
    pub(crate) lifecycle_evictions: usize,
    pub(crate) record_replacements: usize,
    pub(crate) peak_records: usize,
    pub(crate) peak_dependency_keys: usize,
    pub(crate) peak_reverse_edges: usize,
    pub(crate) live_records: usize,
    pub(crate) live_dependency_keys: usize,
    pub(crate) live_reverse_edges: usize,
    pub(crate) inactive_constraint_epoch_changes: usize,
    pub(crate) inactive_role_epoch_changes: usize,
    pub(crate) inactive_input_generation_changes: usize,
    pub(crate) inactive_contract_generation_changes: usize,
    pub(crate) owners: Vec<OwnerDirtySchedulerOwnerReport>,
}

#[cfg(test)]
impl OwnerDirtySchedulerReport {
    pub(crate) fn owner(&self, owner: DefId) -> Option<&OwnerDirtySchedulerOwnerReport> {
        self.owners.iter().find(|metrics| metrics.owner == owner)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg(test)]
pub(crate) struct OwnerDirtySchedulerOwnerReport {
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
    pub(crate) would_have_been_clean_hits: usize,
    pub(crate) would_have_been_clean_misses: usize,
    pub(crate) real_solves: usize,
    pub(crate) clean_skips: usize,
    pub(crate) reused_root_unavailable: usize,
    pub(crate) reused_no_progress: usize,
}

#[derive(Debug, Default)]
struct OwnerDirtySchedulerMetrics {
    forced_passes: usize,
    owner_checks: usize,
    predicted_clean: usize,
    predicted_dirty: usize,
    root_available_checks: usize,
    root_available_predicted_clean: usize,
    root_available_predicted_dirty: usize,
    owner_solve_time: Duration,
    predicted_clean_owner_solve_time: Duration,
    predicted_dirty_owner_solve_time: Duration,
    would_have_been_clean_hits: usize,
    would_have_been_clean_misses: usize,
    real_solves: usize,
    clean_skips: usize,
    clean_skip_time: Duration,
    method_taint_diff_time: Duration,
    full_fallbacks: usize,
    journal_drain_time: Duration,
    journal_bursts: usize,
    journal_mutations: usize,
    peak_journal_burst: usize,
    changed_mutations: usize,
    oracle_agreements: usize,
    conservative_divergences: Vec<OwnerPredictionDivergence>,
    permissive_divergences: Vec<OwnerPredictionDivergence>,
    mismatches: Vec<OwnerDirtySchedulerMismatch>,
    invalidate_all_reasons: Vec<InvalidateAllReason>,
    lifecycle_evictions: usize,
    record_replacements: usize,
    peak_records: usize,
    peak_dependency_keys: usize,
    peak_generation_keys: usize,
    peak_dependencies_per_owner: usize,
    peak_reverse_edges: usize,
    peak_retained_bytes: usize,
    per_owner_cap_rejections: usize,
    global_cap_fallbacks: usize,
    inactive_constraint_epoch_changes: usize,
    inactive_role_epoch_changes: usize,
    inactive_input_generation_changes: usize,
    inactive_contract_generation_changes: usize,
    owners: FxHashMap<DefId, OwnerDirtySchedulerOwnerMetrics>,
}

#[derive(Debug, Default)]
struct OwnerDirtySchedulerOwnerMetrics {
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
    would_have_been_clean_hits: usize,
    would_have_been_clean_misses: usize,
    real_solves: usize,
    clean_skips: usize,
    reused_root_unavailable: usize,
    reused_no_progress: usize,
}

impl OwnerDirtySchedulerOwnerMetrics {
    fn record_outcome(&mut self, outcome: OwnerSolveOutcome) {
        match outcome {
            OwnerSolveOutcome::RootUnavailable => self.root_unavailable_outcomes += 1,
            OwnerSolveOutcome::NoProgress => self.no_progress_outcomes += 1,
            OwnerSolveOutcome::Progress => self.progress_outcomes += 1,
        }
    }

    fn record_reused_outcome(&mut self, outcome: OwnerSolveOutcome) {
        match outcome {
            OwnerSolveOutcome::RootUnavailable => self.reused_root_unavailable += 1,
            OwnerSolveOutcome::NoProgress => self.reused_no_progress += 1,
            OwnerSolveOutcome::Progress => {
                panic!("a progressing owner outcome must never be replayed")
            }
        }
    }
}

impl AnalysisSession {
    pub(super) fn owner_dirty_scheduler_install_mutation_subscriptions(&mut self) {
        let Some(subscriptions) = self
            .owner_dirty_scheduler
            .as_ref()
            .map(|scheduler| scheduler.mutation_subscriptions.clone())
        else {
            return;
        };
        self.method_role_mutations
            .set_subscriptions(subscriptions.clone());
        self.infer
            .constraints_mut()
            .set_method_role_mutation_subscriptions(subscriptions.clone());
        self.roles
            .set_method_role_mutation_subscriptions(subscriptions.clone());
        self.role_impls
            .set_method_role_mutation_subscriptions(subscriptions);
    }

    pub(super) fn owner_dirty_scheduler_begin_journal_window(&mut self) {
        let snapshot = self.method_role_pass_input_snapshot();
        if let Some(scheduler) = &mut self.owner_dirty_scheduler {
            scheduler.begin_journal_window(snapshot);
        }
    }

    pub(super) fn owner_dirty_scheduler_finish_journal_window(&mut self) {
        if self.owner_dirty_scheduler.is_none() {
            return;
        }
        self.owner_dirty_scheduler_drain_journal();
        let snapshot = self.method_role_pass_input_snapshot();
        if let Some(scheduler) = &mut self.owner_dirty_scheduler {
            scheduler.finish_journal_window(snapshot);
        }
    }

    pub(super) fn owner_dirty_scheduler_begin_pass(
        &mut self,
        owners: &[DefId],
        method_taint: &MethodTaintIndex,
    ) {
        let Some(mut scheduler) = self.owner_dirty_scheduler.take() else {
            return;
        };
        let taint_mutations = scheduler.begin_pass(owners, method_taint);
        self.owner_dirty_scheduler = Some(scheduler);
        self.method_role_mutations.record_many(taint_mutations);
        self.owner_dirty_scheduler_drain_journal();
    }

    pub(super) fn owner_dirty_scheduler_prepare_owner(
        &mut self,
        owner: DefId,
        root_available: bool,
    ) -> OwnerScheduleDecision {
        if self.owner_dirty_scheduler.is_none() {
            return OwnerScheduleDecision::Solve;
        }
        self.owner_dirty_scheduler_drain_journal();
        #[cfg(test)]
        let exact = self.shadow_dirty_oracle_prediction(owner);
        #[cfg(not(test))]
        let exact = None;
        if let Some(scheduler) = &mut self.owner_dirty_scheduler {
            return scheduler.prepare_owner(owner, root_available, exact);
        }
        OwnerScheduleDecision::Solve
    }

    pub(super) fn owner_dirty_scheduler_finish_owner(
        &mut self,
        owner: DefId,
        outcome: OwnerSolveOutcome,
        method_taint: &MethodTaintIndex,
        reads: &OwnerReadFrontier,
    ) {
        if self.owner_dirty_scheduler.is_none() {
            return;
        }
        let dependencies = reads.scheduler_owner_dependency_keys(owner, method_taint);
        let solve_duration = reads.solve_duration();
        self.owner_dirty_scheduler_drain_journal();
        let still_unresolved = self
            .selections
            .iter()
            .any(|(_, use_site)| use_site.parent == owner);
        if let Some(scheduler) = &mut self.owner_dirty_scheduler {
            scheduler.finish_owner(
                owner,
                outcome,
                dependencies,
                solve_duration,
                still_unresolved,
            );
        }
    }

    pub(super) fn owner_dirty_scheduler_remove_owner(&mut self, owner: DefId) {
        if let Some(scheduler) = &mut self.owner_dirty_scheduler {
            scheduler.remove_owner(owner);
        }
    }

    pub(super) fn owner_dirty_scheduler_drain_journal(&mut self) {
        if self.owner_dirty_scheduler.is_none() {
            return;
        }
        let mutations = self.take_method_role_mutations();
        let owner_eligibility = self.method_role_owner_eligibility();
        if let Some(scheduler) = &mut self.owner_dirty_scheduler {
            scheduler.drain_mutations(mutations, owner_eligibility);
        }
    }

    #[cfg(test)]
    pub(crate) fn owner_dirty_scheduler_report(&self) -> Option<OwnerDirtySchedulerReport> {
        self.owner_dirty_scheduler
            .as_ref()
            .map(MethodRoleOwnerDirtyScheduler::report)
    }
}

fn with_new_session_mode<T>(mode: OwnerDirtySchedulingMode, f: impl FnOnce() -> T) -> T {
    struct ModeGuard(OwnerDirtySchedulingMode);
    impl Drop for ModeGuard {
        fn drop(&mut self) {
            NEW_SESSION_MODE.with(|current| current.set(self.0));
        }
    }

    let previous = NEW_SESSION_MODE.with(|current| current.replace(mode));
    let _guard = ModeGuard(previous);
    f()
}

#[cfg(test)]
pub(crate) fn with_owner_dirty_scheduler_for_new_sessions<T>(f: impl FnOnce() -> T) -> T {
    with_new_session_mode(OwnerDirtySchedulingMode::ShadowAlwaysSolve, f)
}

/// Run newly created sessions through the unchanged always-solve owner loop.
///
/// This is the explicit rollback/control route for scheduler regression debugging and paired
/// performance measurements. It does not alter the default production mode.
pub fn with_owner_dirty_scheduler_disabled_for_new_sessions<T>(f: impl FnOnce() -> T) -> T {
    with_new_session_mode(OwnerDirtySchedulingMode::Disabled, f)
}

fn normalized_method_taint(method_taint: &MethodTaintIndex) -> MethodTaintIndex {
    method_taint
        .iter()
        .map(|(var, selects)| {
            let mut selects = selects.clone();
            selects.sort_by_key(|select| select.0);
            selects.dedup();
            (*var, selects)
        })
        .collect()
}

fn diff_method_taint(previous: &MethodTaintIndex, current: &MethodTaintIndex) -> Vec<TypeVar> {
    let mut vars = previous
        .keys()
        .chain(current.keys())
        .copied()
        .collect::<Vec<_>>();
    vars.sort_by_key(|var| var.0);
    vars.dedup();
    vars.retain(|var| {
        let mut previous = previous.get(var).cloned().unwrap_or_default();
        let mut current = current.get(var).cloned().unwrap_or_default();
        previous.sort_by_key(|select| select.0);
        previous.dedup();
        current.sort_by_key(|select| select.0);
        current.dedup();
        previous != current
    });
    vars
}

fn normalize_dependencies(dependencies: Vec<DependencyKey>) -> Vec<DependencyKey> {
    let mut seen = FxHashSet::default();
    let mut dependencies = dependencies
        .into_iter()
        .filter(|key| seen.insert(key.clone()))
        .collect::<Vec<_>>();
    dependencies.sort_by(dependency_key_cmp);
    dependencies
}

fn map_capacity_bytes<K, V>(capacity: usize) -> usize {
    capacity.saturating_mul(size_of::<K>() + size_of::<V>() + 1)
}

fn set_capacity_bytes<T>(capacity: usize) -> usize {
    capacity.saturating_mul(size_of::<T>() + 1)
}

fn dependency_key_heap_bytes(key: &DependencyKey) -> usize {
    match key {
        DependencyKey::CandidateBucket(path) => {
            path.capacity() * size_of::<String>()
                + path.iter().map(|segment| segment.capacity()).sum::<usize>()
        }
        DependencyKey::SccRoot(_)
        | DependencyKey::OwnerRawRoles(_)
        | DependencyKey::OwnerSelections(_)
        | DependencyKey::Selection(_)
        | DependencyKey::ConstraintBounds(_)
        | DependencyKey::ConstraintNeighbors(_)
        | DependencyKey::ConstraintSubtractFacts(_)
        | DependencyKey::ConstraintLevel(_)
        | DependencyKey::ConstraintBirthLevel(_)
        | DependencyKey::ConstraintPrePopFamilies(_)
        | DependencyKey::MethodTaint(_)
        | DependencyKey::AppliedResolution(_) => 0,
    }
}

fn dependency_key_cmp(left: &DependencyKey, right: &DependencyKey) -> Ordering {
    use DependencyKey::*;
    let rank = |key: &DependencyKey| match key {
        SccRoot(_) => 0,
        OwnerRawRoles(_) => 1,
        OwnerSelections(_) => 2,
        Selection(_) => 3,
        ConstraintBounds(_) => 4,
        ConstraintNeighbors(_) => 5,
        ConstraintSubtractFacts(_) => 6,
        ConstraintLevel(_) => 7,
        ConstraintBirthLevel(_) => 8,
        ConstraintPrePopFamilies(_) => 9,
        MethodTaint(_) => 10,
        CandidateBucket(_) => 11,
        AppliedResolution(_) => 12,
    };
    rank(left)
        .cmp(&rank(right))
        .then_with(|| match (left, right) {
            (SccRoot(left), SccRoot(right))
            | (OwnerRawRoles(left), OwnerRawRoles(right))
            | (OwnerSelections(left), OwnerSelections(right)) => left.0.cmp(&right.0),
            (Selection(left), Selection(right)) => left.0.cmp(&right.0),
            (ConstraintBounds(left), ConstraintBounds(right))
            | (ConstraintNeighbors(left), ConstraintNeighbors(right))
            | (ConstraintSubtractFacts(left), ConstraintSubtractFacts(right))
            | (ConstraintLevel(left), ConstraintLevel(right))
            | (ConstraintBirthLevel(left), ConstraintBirthLevel(right))
            | (ConstraintPrePopFamilies(left), ConstraintPrePopFamilies(right))
            | (MethodTaint(left), MethodTaint(right)) => left.0.cmp(&right.0),
            (CandidateBucket(left), CandidateBucket(right)) => left.cmp(right),
            (AppliedResolution(left), AppliedResolution(right)) => {
                format!("{left:?}").cmp(&format!("{right:?}"))
            }
            _ => Ordering::Equal,
        })
}

#[cfg(test)]
mod tests;
