//! Journal-backed owner scheduler running in Stage 3 shadow mode.
//!
//! The scheduler consumes the production mutation journal and maintains the records which a later
//! stage could use to skip terminal owner solves. Stage 3 deliberately never acts on a clean
//! prediction: the unchanged owner solve always runs, and its real terminal outcome is compared
//! with both this scheduler and the independent exact-snapshot oracle.

use super::*;

use std::cell::Cell;
use std::cmp::Ordering;

use crate::constraints::mutation::{InvalidateAllReason, MutationGeneration, MutationSerial};

use super::shadow_dirty_oracle::{
    OwnerPrediction as ExactOwnerPrediction, OwnerReadFrontier, OwnerSolveOutcome,
};

thread_local! {
    static ENABLE_NEW_SCHEDULERS: Cell<bool> = const { Cell::new(false) };
}

/// Session-owned record, reverse-subscription, and dirty state for method-role owners.
#[derive(Debug, Default)]
pub(crate) struct MethodRoleOwnerDirtyScheduler {
    records: FxHashMap<DefId, CachedOwnerTerminal>,
    reverse_subscriptions: FxHashMap<DependencyKey, FxHashSet<DefId>>,
    dirty: FxHashSet<DefId>,
    generations: FxHashMap<DependencyKey, MutationGeneration>,
    drained_mutation_serial: MutationSerial,
    method_taint_snapshot: MethodTaintIndex,
    current_predictions: FxHashMap<DefId, JournalOwnerPrediction>,
    last_journal_window_end: Option<MethodRolePassInputSnapshot>,
    inactive_window_changed: bool,
    force_all_dirty_this_pass: bool,
    metrics: OwnerDirtySchedulerMetrics,
}

impl MethodRoleOwnerDirtyScheduler {
    pub(super) fn for_new_session() -> Option<Self> {
        ENABLE_NEW_SCHEDULERS.with(Cell::get).then(Self::default)
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
        debug_assert!(self.current_predictions.is_empty());
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
        changed
            .into_iter()
            .map(DependencyKey::MethodTaint)
            .collect()
    }

    fn drain_mutations(&mut self, mutations: Vec<MethodRoleMutation>, owner_eligibility: bool) {
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
    }

    fn prepare_owner(
        &mut self,
        owner: DefId,
        root_available: bool,
        exact: Option<ExactOwnerPrediction>,
    ) {
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

        self.current_predictions.insert(owner, prediction);
        self.detach_record(owner);
        self.dirty.remove(&owner);
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
        let dependencies = normalize_dependencies(dependencies);
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
            self.reverse_subscriptions
                .entry(key.clone())
                .or_default()
                .insert(owner);
        }
        self.records.insert(owner, record);
        self.dirty.remove(&owner);
        self.metrics.peak_records = self.metrics.peak_records.max(self.records.len());
        self.metrics.peak_dependency_keys = self
            .metrics
            .peak_dependency_keys
            .max(self.reverse_subscriptions.len());
        self.metrics.peak_reverse_edges = self
            .metrics
            .peak_reverse_edges
            .max(self.reverse_edge_count());
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
            }
        }
        Some(record)
    }

    fn invalidate_all_for_pass(&mut self, reason: InvalidateAllReason) {
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
        reason = "retained for serial audit and Stage 4 eligibility assertions"
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

impl OwnerDirtySchedulerReport {
    pub(crate) fn owner(&self, owner: DefId) -> Option<&OwnerDirtySchedulerOwnerReport> {
        self.owners.iter().find(|metrics| metrics.owner == owner)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
    peak_reverse_edges: usize,
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
}

impl OwnerDirtySchedulerOwnerMetrics {
    fn record_outcome(&mut self, outcome: OwnerSolveOutcome) {
        match outcome {
            OwnerSolveOutcome::RootUnavailable => self.root_unavailable_outcomes += 1,
            OwnerSolveOutcome::NoProgress => self.no_progress_outcomes += 1,
            OwnerSolveOutcome::Progress => self.progress_outcomes += 1,
        }
    }
}

impl AnalysisSession {
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
    ) {
        if self.owner_dirty_scheduler.is_none() {
            return;
        }
        self.owner_dirty_scheduler_drain_journal();
        let exact = self.shadow_dirty_oracle_prediction(owner);
        if let Some(scheduler) = &mut self.owner_dirty_scheduler {
            scheduler.prepare_owner(owner, root_available, exact);
        }
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
        let dependencies = reads.owner_dependency_keys(owner, method_taint);
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

    pub(crate) fn owner_dirty_scheduler_report(&self) -> Option<OwnerDirtySchedulerReport> {
        self.owner_dirty_scheduler
            .as_ref()
            .map(MethodRoleOwnerDirtyScheduler::report)
    }
}

pub(crate) fn with_owner_dirty_scheduler_for_new_sessions<T>(f: impl FnOnce() -> T) -> T {
    struct EnableGuard(bool);
    impl Drop for EnableGuard {
        fn drop(&mut self) {
            ENABLE_NEW_SCHEDULERS.with(|enabled| enabled.set(self.0));
        }
    }

    let previous = ENABLE_NEW_SCHEDULERS.with(|enabled| enabled.replace(true));
    let _guard = EnableGuard(previous);
    f()
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
