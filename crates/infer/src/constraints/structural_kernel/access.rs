//! Attempt capability, terminal latch, preparation scopes, and opaque query shells.

mod sealing;

#[cfg(test)]
use std::cell::Cell;
use std::cell::RefCell;
use std::collections::HashSet;
use std::marker::PhantomData;

use super::commands::{CommittedStructuralMutation, StructuralMutationIntent};
use super::gateway::{PreparationScopeNonce, PreparedMutationSlotId, ProofStructuralState};
use super::read_view::ScopedQueryView;
pub(in crate::constraints) use crate::constraints::proof::ProofAttemptNonce;
use crate::constraints::proof::{ProofFailure, ProofOperation, mint_proof_attempt_nonce};
use crate::constraints::{ConstraintMachine, record_proof_terminal_failure};
use poly::types::TypeArena;

use sealing::RoundReuseSlot;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::constraints) enum ProofAccessError {
    Terminal(ProofFailure),
    TerminalLatchBusy,
    ForeignAttemptRoundState {
        expected: Option<ProofAttemptNonce>,
        actual: Option<ProofAttemptNonce>,
    },
    StructuralResourceExhausted,
    StructuralSnapshotExhausted,
    InvalidPreparedHandle,
    InvalidReservedOperation,
    InjectedShadowFailure,
}

pub(in crate::constraints) struct ProofAttemptKernel {
    attempt_nonce: Option<ProofAttemptNonce>,
    reuse_disabled: bool,
    terminal_failure: RefCell<Option<ProofFailure>>,
    structural: ProofStructuralState,
    #[cfg(test)]
    injected_query_scope_failure: RefCell<Option<ProofFailure>>,
    #[cfg(test)]
    injected_post_scope_failure: RefCell<Option<ProofFailure>>,
    #[cfg(test)]
    query_trace: QueryAccessTrace,
}

#[cfg(test)]
#[derive(Debug, Default)]
struct QueryAccessTrace {
    active_checks: Cell<usize>,
    round_authentications: Cell<usize>,
    authenticated_round_state_entries: Cell<usize>,
    scope_entries: Cell<usize>,
    post_scope_checks: Cell<usize>,
}

impl ProofAttemptKernel {
    pub(in crate::constraints) fn new() -> Self {
        let attempt_nonce = mint_proof_attempt_nonce();
        Self {
            attempt_nonce,
            reuse_disabled: attempt_nonce.is_none(),
            terminal_failure: RefCell::new(None),
            structural: ProofStructuralState::default(),
            #[cfg(test)]
            injected_query_scope_failure: RefCell::new(None),
            #[cfg(test)]
            injected_post_scope_failure: RefCell::new(None),
            #[cfg(test)]
            query_trace: QueryAccessTrace::default(),
        }
    }

    pub(in crate::constraints) fn terminal_failure(&self) -> Option<ProofFailure> {
        self.terminal_failure.borrow().clone()
    }

    pub(in crate::constraints) fn mark_terminal_failure(
        &self,
        operation: ProofOperation,
        failure: ProofFailure,
    ) {
        let mut terminal = self.terminal_failure.borrow_mut();
        if terminal.is_none() {
            record_proof_terminal_failure(operation, &failure);
            *terminal = Some(failure);
        }
    }

    pub(in crate::constraints) fn try_with_structural_preparation_scope<R>(
        &mut self,
        f: impl for<'scope> FnOnce(
            &mut StructuralPreparationScope<'scope>,
        ) -> Result<R, ProofAccessError>,
    ) -> Result<R, ProofAccessError> {
        let active = ActiveProofAttempt::new(
            &self.terminal_failure,
            self.attempt_nonce,
            self.reuse_disabled,
        )?;
        let scope_nonce = self.structural.next_scope_nonce();
        let mut scope = StructuralPreparationScope {
            active,
            structural: &mut self.structural,
            scope_nonce,
            live_slots: Vec::new(),
        };
        f(&mut scope)
    }

    fn new_projection_evaluation_round(&self) -> ProjectionEvaluationRoundState {
        ProjectionEvaluationRoundState {
            attempt_nonce: self.attempt_nonce,
            reuse_disabled: self.reuse_disabled,
            terminal_failure: None,
            reuse: RoundReuseSlot::sealing_incomplete(),
        }
    }

    fn new_publication_evaluation_round(&self) -> CpkPublicationEvaluationRoundState {
        CpkPublicationEvaluationRoundState {
            attempt_nonce: self.attempt_nonce,
            reuse_disabled: self.reuse_disabled,
            reuse: RoundReuseSlot::sealing_incomplete(),
        }
    }

    fn ensure_query_kernel_active(&self) -> Result<(), ProofFailure> {
        #[cfg(test)]
        self.query_trace
            .active_checks
            .set(self.query_trace.active_checks.get() + 1);
        let terminal = self
            .terminal_failure
            .try_borrow()
            .map_err(|_| ProofFailure::TerminalLatchBusy)?;
        match terminal.as_ref() {
            Some(failure) => Err(failure.clone()),
            None => Ok(()),
        }
    }

    fn authenticate_round(
        &self,
        actual: Option<ProofAttemptNonce>,
        round_reuse_disabled: bool,
    ) -> Result<AuthenticatedRoundAccess, ProofFailure> {
        #[cfg(test)]
        self.query_trace
            .round_authentications
            .set(self.query_trace.round_authentications.get() + 1);
        match (
            self.attempt_nonce,
            self.reuse_disabled,
            actual,
            round_reuse_disabled,
        ) {
            (Some(expected), false, Some(actual), false) if expected == actual => {
                Ok(AuthenticatedRoundAccess::Bound)
            }
            (None, true, None, true) => Ok(AuthenticatedRoundAccess::ReuseDisabled),
            (expected, _, actual, _) => {
                Err(ProofFailure::ForeignAttemptRoundState { expected, actual })
            }
        }
    }

    fn with_projection_query<R>(
        &mut self,
        type_shapes: &TypeArena,
        round: &mut ProjectionEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedProjectionQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure> {
        // 1. Current-kernel authority is checked before any caller-owned round field.
        self.ensure_query_kernel_active()?;
        // 2. Only attempt identity participates in authentication.
        let access = self.authenticate_round(round.attempt_nonce, round.reuse_disabled)?;
        #[cfg(test)]
        self.query_trace
            .authenticated_round_state_entries
            .set(self.query_trace.authenticated_round_state_entries.get() + 1);
        // 3. A foreign round can never import its sticky failure into this attempt.
        if access == AuthenticatedRoundAccess::Bound {
            if let Some(failure) = &round.terminal_failure {
                return Err(failure.clone());
            }
        }
        // 4. SS1-RF has no Sealed constructor; every reachable branch is ephemeral.
        debug_assert!(round.reuse.is_sealing_incomplete());
        // 5. Construction and the query closure share one authenticated failure path.
        let result: Result<QueryCompletion<R>, ProofFailure> = (|| {
            #[cfg(test)]
            if let Some(failure) = self.injected_query_scope_failure.borrow_mut().take() {
                return Err(failure);
            }
            let scope = ScopedProjectionQuery::try_new(
                self.structural.query_data(),
                super::read_view::ImmutableTypeShapeView::new(type_shapes),
            )?;
            #[cfg(test)]
            self.query_trace
                .scope_entries
                .set(self.query_trace.scope_entries.get() + 1);
            query(scope)
        })();

        match result {
            Ok(completion) => {
                // 6. Re-check authority and binding after all scope borrows are dead.
                #[cfg(test)]
                self.activate_injected_post_scope_failure();
                #[cfg(test)]
                self.query_trace
                    .post_scope_checks
                    .set(self.query_trace.post_scope_checks.get() + 1);
                self.ensure_query_kernel_active()?;
                let post_access =
                    self.authenticate_round(round.attempt_nonce, round.reuse_disabled)?;
                if post_access == AuthenticatedRoundAccess::Bound {
                    if let Some(failure) = &round.terminal_failure {
                        return Err(failure.clone());
                    }
                }
                Ok(completion.into_value())
            }
            Err(failure) => {
                if failure.requires_attempt_terminal() {
                    if access == AuthenticatedRoundAccess::Bound && round.terminal_failure.is_none()
                    {
                        round.terminal_failure = Some(failure.clone());
                    }
                    self.mark_terminal_failure(
                        ProofOperation::ProjectLowerEvaluation,
                        failure.clone(),
                    );
                }
                Err(failure)
            }
        }
    }

    fn with_publication_projection_query<R>(
        &mut self,
        type_shapes: &TypeArena,
        round: &mut CpkPublicationEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedPublicationProjectionQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure> {
        // Steps 1--3: current kernel, attempt identity, publication's no-op round latch.
        self.ensure_query_kernel_active()?;
        let access = self.authenticate_round(round.attempt_nonce, round.reuse_disabled)?;
        #[cfg(test)]
        self.query_trace
            .authenticated_round_state_entries
            .set(self.query_trace.authenticated_round_state_entries.get() + 1);
        debug_assert!(round.reuse.is_sealing_incomplete());
        // Steps 4--5: fresh invocation-local state and one HRTB scope.
        let result: Result<QueryCompletion<R>, ProofFailure> = (|| {
            #[cfg(test)]
            if let Some(failure) = self.injected_query_scope_failure.borrow_mut().take() {
                return Err(failure);
            }
            let scope = ScopedPublicationProjectionQuery::try_new(
                self.structural.query_data(),
                super::read_view::ImmutableTypeShapeView::new(type_shapes),
            )?;
            #[cfg(test)]
            self.query_trace
                .scope_entries
                .set(self.query_trace.scope_entries.get() + 1);
            query(scope)
        })();

        match result {
            Ok(completion) => {
                // Step 6: no candidate can publish until authority is re-authenticated.
                #[cfg(test)]
                self.activate_injected_post_scope_failure();
                #[cfg(test)]
                self.query_trace
                    .post_scope_checks
                    .set(self.query_trace.post_scope_checks.get() + 1);
                self.ensure_query_kernel_active()?;
                self.authenticate_round(round.attempt_nonce, round.reuse_disabled)?;
                let _ = access;
                Ok(completion.into_value())
            }
            Err(failure) => {
                if failure.requires_attempt_terminal() {
                    self.mark_terminal_failure(
                        ProofOperation::ProjectLowerEvaluation,
                        failure.clone(),
                    );
                }
                Err(failure)
            }
        }
    }

    #[cfg(test)]
    pub(super) fn shadow_state(&self) -> &ProofStructuralState {
        &self.structural
    }

    #[cfg(test)]
    fn activate_injected_post_scope_failure(&self) {
        if let Some(failure) = self.injected_post_scope_failure.borrow_mut().take() {
            *self.terminal_failure.borrow_mut() = Some(failure);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AuthenticatedRoundAccess {
    Bound,
    ReuseDisabled,
}

pub(in crate::constraints::structural_kernel) struct ActiveProofAttempt<'attempt> {
    terminal_failure: &'attempt RefCell<Option<ProofFailure>>,
    attempt_nonce: Option<ProofAttemptNonce>,
    reuse_disabled: bool,
}

impl<'attempt> ActiveProofAttempt<'attempt> {
    fn new(
        terminal_failure: &'attempt RefCell<Option<ProofFailure>>,
        attempt_nonce: Option<ProofAttemptNonce>,
        reuse_disabled: bool,
    ) -> Result<Self, ProofAccessError> {
        let active = Self {
            terminal_failure,
            attempt_nonce,
            reuse_disabled,
        };
        active.ensure_active()?;
        Ok(active)
    }

    pub(in crate::constraints::structural_kernel) fn ensure_active(
        &self,
    ) -> Result<(), ProofAccessError> {
        let terminal = self
            .terminal_failure
            .try_borrow()
            .map_err(|_| ProofAccessError::TerminalLatchBusy)?;
        match terminal.as_ref() {
            Some(failure) => Err(ProofAccessError::Terminal(failure.clone())),
            None => Ok(()),
        }
    }

    #[allow(dead_code)]
    pub(super) fn identity(&self) -> (Option<ProofAttemptNonce>, bool) {
        (self.attempt_nonce, self.reuse_disabled)
    }

    #[cfg(test)]
    fn inject_terminal_failure(&self, failure: ProofFailure) {
        *self.terminal_failure.borrow_mut() = Some(failure);
    }
}

pub(in crate::constraints) struct StructuralPreparationScope<'scope> {
    active: ActiveProofAttempt<'scope>,
    structural: &'scope mut ProofStructuralState,
    scope_nonce: PreparationScopeNonce,
    live_slots: Vec<PreparedMutationSlotId>,
}

impl<'scope> StructuralPreparationScope<'scope> {
    pub(in crate::constraints) fn prepare(
        &mut self,
        intent: StructuralMutationIntent,
    ) -> Result<PreparedStructuralMutationHandle<'scope>, ProofAccessError> {
        self.live_slots
            .try_reserve(1)
            .map_err(|_| ProofAccessError::StructuralResourceExhausted)?;
        let slot = self
            .structural
            .prepare(&self.active, self.scope_nonce, intent)?;
        self.live_slots.push(slot);
        Ok(PreparedStructuralMutationHandle {
            slot,
            scope_nonce: self.scope_nonce,
            _invariant: PhantomData,
        })
    }

    pub(in crate::constraints) fn commit(
        &mut self,
        handle: PreparedStructuralMutationHandle<'scope>,
    ) -> Result<CommittedStructuralMutation, ProofAccessError> {
        let position = self.live_slot_position(handle.slot, handle.scope_nonce)?;
        let result = self
            .structural
            .commit(&self.active, self.scope_nonce, handle.slot);
        self.live_slots.swap_remove(position);
        result
    }

    pub(in crate::constraints) fn cancel(
        &mut self,
        handle: PreparedStructuralMutationHandle<'scope>,
    ) -> Result<(), ProofAccessError> {
        let position = self.live_slot_position(handle.slot, handle.scope_nonce)?;
        let result = self.structural.cancel_slot(self.scope_nonce, handle.slot);
        if result.is_ok() {
            self.live_slots.swap_remove(position);
        }
        result
    }

    fn live_slot_position(
        &self,
        slot: PreparedMutationSlotId,
        scope_nonce: PreparationScopeNonce,
    ) -> Result<usize, ProofAccessError> {
        if scope_nonce != self.scope_nonce {
            return Err(ProofAccessError::InvalidPreparedHandle);
        }
        self.live_slots
            .iter()
            .position(|candidate| *candidate == slot)
            .ok_or(ProofAccessError::InvalidPreparedHandle)
    }

    #[cfg(test)]
    pub(super) fn commit_with_injected_exit(
        &mut self,
        handle: PreparedStructuralMutationHandle<'scope>,
        early_error: bool,
        panic_mid_commit: bool,
    ) -> Result<CommittedStructuralMutation, ProofAccessError> {
        let position = self.live_slot_position(handle.slot, handle.scope_nonce)?;
        let result = self.structural.commit_with_injected_exit(
            &self.active,
            self.scope_nonce,
            handle.slot,
            early_error,
            panic_mid_commit,
        );
        self.live_slots.swap_remove(position);
        result
    }

    #[cfg(test)]
    pub(super) fn inject_terminal_failure(&self, failure: ProofFailure) {
        self.active.inject_terminal_failure(failure);
    }

    #[cfg(test)]
    pub(super) fn shadow_counts(&self) -> ([u64; 5], u64, usize, usize, usize, usize) {
        self.structural.shadow_counts()
    }

    #[cfg(test)]
    pub(super) fn corrupt_first_reserved_domain_for_test(
        &mut self,
        handle: &PreparedStructuralMutationHandle<'scope>,
    ) -> Result<(), ProofAccessError> {
        self.live_slot_position(handle.slot, handle.scope_nonce)?;
        self.structural
            .corrupt_first_reserved_domain_for_test(self.scope_nonce, handle.slot)
    }

    #[cfg(test)]
    pub(super) fn corrupt_projection_formula_secondary_domain_for_test(
        &mut self,
        handle: &PreparedStructuralMutationHandle<'scope>,
    ) -> Result<(), ProofAccessError> {
        self.live_slot_position(handle.slot, handle.scope_nonce)?;
        self.structural
            .corrupt_projection_formula_secondary_domain_for_test(self.scope_nonce, handle.slot)
    }

    #[cfg(test)]
    pub(super) fn exhaust_snapshot_for_test(&mut self) {
        self.structural.exhaust_snapshot_for_test();
    }
}

impl Drop for StructuralPreparationScope<'_> {
    fn drop(&mut self) {
        self.structural
            .cancel_scope_slots_and_release_tickets(self.scope_nonce, &mut self.live_slots);
    }
}

pub(in crate::constraints) struct PreparedStructuralMutationHandle<'scope> {
    slot: PreparedMutationSlotId,
    scope_nonce: PreparationScopeNonce,
    _invariant: PhantomData<&'scope mut ()>,
}

#[derive(Debug, Default)]
struct SuccessfulValidationCandidates;

#[derive(Debug, Default)]
struct ProjectionReusableRoundState {
    _checked_targets: HashSet<u64>,
}

#[derive(Debug, Default)]
struct PublicationReusableRoundState {
    _memoized_targets: HashSet<u64>,
}

#[derive(Debug, Default)]
struct ProjectionInvocationState {
    checked_targets: HashSet<u64>,
    canonical_reads: usize,
    hits: usize,
}

#[derive(Debug, Default)]
struct PublicationInvocationState {
    memoized_targets: HashSet<u64>,
    canonical_reads: usize,
    hits: usize,
}

pub(in crate::constraints) struct QueryCompletion<R> {
    value: R,
    candidates: SuccessfulValidationCandidates,
}

pub(in crate::constraints) struct ScopedProjectionQuery<'query> {
    view: ScopedQueryView<'query>,
    candidates: SuccessfulValidationCandidates,
    invocation: ProjectionInvocationState,
}

pub(in crate::constraints) struct ScopedPublicationProjectionQuery<'query> {
    view: ScopedQueryView<'query>,
    candidates: SuccessfulValidationCandidates,
    invocation: PublicationInvocationState,
}

macro_rules! query_shell {
    ($name:ident) => {
        impl $name<'_> {
            pub(in crate::constraints) fn view(&self) -> &ScopedQueryView<'_> {
                &self.view
            }

            pub(in crate::constraints) fn complete<R>(self, value: R) -> QueryCompletion<R> {
                QueryCompletion {
                    value,
                    candidates: self.candidates,
                }
            }
        }
    };
}

query_shell!(ScopedProjectionQuery);
query_shell!(ScopedPublicationProjectionQuery);

impl<'query> ScopedProjectionQuery<'query> {
    fn try_new(
        data: &'query super::gateway::StructuralData,
        type_shapes: super::read_view::ImmutableTypeShapeView<'query>,
    ) -> Result<Self, ProofFailure> {
        Ok(Self {
            view: ScopedQueryView::new(data, type_shapes),
            candidates: SuccessfulValidationCandidates,
            invocation: ProjectionInvocationState::default(),
        })
    }

    #[cfg(cpk_sv_d_ss1_rf_ui_raw_escape)]
    pub(in crate::constraints) fn raw_shadow_probe(&self) -> &'query u64 {
        self.view.raw_shadow_probe()
    }

    #[cfg(cpk_sv_d_ss1_rf_ui_cursor_escape)]
    pub(in crate::constraints) fn shadow_cursor(
        &self,
    ) -> super::read_view::ShadowQueryCursor<'query> {
        self.view.shadow_cursor()
    }

    #[cfg(cpk_sv_d_ss1_rf_ui_round_view_storage)]
    pub(in crate::constraints) fn complete_with_owned_view<R>(
        self,
        finish: impl FnOnce(ScopedQueryView<'query>) -> R,
    ) -> QueryCompletion<R> {
        let Self {
            view,
            candidates,
            invocation,
        } = self;
        let _ = invocation;
        QueryCompletion {
            value: finish(view),
            candidates,
        }
    }

    #[cfg(test)]
    pub(super) fn shadow_check_target(&mut self, target: u64) -> bool {
        if self.invocation.checked_targets.insert(target) {
            self.invocation.canonical_reads += 1;
            false
        } else {
            self.invocation.hits += 1;
            true
        }
    }

    #[cfg(test)]
    pub(super) fn shadow_stats(&self) -> (usize, usize) {
        (self.invocation.canonical_reads, self.invocation.hits)
    }
}

impl<'query> ScopedPublicationProjectionQuery<'query> {
    fn try_new(
        data: &'query super::gateway::StructuralData,
        type_shapes: super::read_view::ImmutableTypeShapeView<'query>,
    ) -> Result<Self, ProofFailure> {
        Ok(Self {
            view: ScopedQueryView::new(data, type_shapes),
            candidates: SuccessfulValidationCandidates,
            invocation: PublicationInvocationState::default(),
        })
    }

    #[cfg(test)]
    pub(super) fn shadow_check_target(&mut self, target: u64) -> bool {
        if self.invocation.memoized_targets.insert(target) {
            self.invocation.canonical_reads += 1;
            false
        } else {
            self.invocation.hits += 1;
            true
        }
    }

    #[cfg(test)]
    pub(super) fn shadow_stats(&self) -> (usize, usize) {
        (self.invocation.canonical_reads, self.invocation.hits)
    }
}

#[derive(Debug)]
pub(in crate::constraints) struct ProjectionEvaluationRoundState {
    attempt_nonce: Option<ProofAttemptNonce>,
    reuse_disabled: bool,
    terminal_failure: Option<ProofFailure>,
    reuse: RoundReuseSlot<ProjectionReusableRoundState>,
}

#[derive(Debug)]
pub(in crate::constraints) struct CpkPublicationEvaluationRoundState {
    attempt_nonce: Option<ProofAttemptNonce>,
    reuse_disabled: bool,
    reuse: RoundReuseSlot<PublicationReusableRoundState>,
}

impl<R> QueryCompletion<R> {
    fn into_value(self) -> R {
        let Self { value, candidates } = self;
        let _ = candidates;
        value
    }
}

impl ConstraintMachine {
    pub(in crate::constraints) fn new_projection_evaluation_round(
        &self,
    ) -> ProjectionEvaluationRoundState {
        self.proof_attempt.new_projection_evaluation_round()
    }

    pub(in crate::constraints) fn new_publication_evaluation_round(
        &self,
    ) -> CpkPublicationEvaluationRoundState {
        self.proof_attempt.new_publication_evaluation_round()
    }

    #[deny(private_bounds, private_interfaces)]
    pub(in crate::constraints) fn with_projection_query<R>(
        &mut self,
        round: &mut ProjectionEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedProjectionQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure> {
        let type_shapes = &self.types;
        self.proof_attempt
            .with_projection_query(type_shapes, round, query)
    }

    #[deny(private_bounds, private_interfaces)]
    pub(in crate::constraints) fn with_publication_projection_query<R>(
        &mut self,
        round: &mut CpkPublicationEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedPublicationProjectionQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure> {
        let type_shapes = &self.types;
        self.proof_attempt
            .with_publication_projection_query(type_shapes, round, query)
    }
}

#[cfg(test)]
impl ProjectionEvaluationRoundState {
    pub(super) fn attempt_nonce_for_test(&self) -> Option<ProofAttemptNonce> {
        self.attempt_nonce
    }

    pub(super) fn inject_terminal_failure_for_test(&mut self, failure: ProofFailure) {
        self.terminal_failure = Some(failure);
    }
}

#[cfg(test)]
impl CpkPublicationEvaluationRoundState {
    pub(super) fn attempt_nonce_for_test(&self) -> Option<ProofAttemptNonce> {
        self.attempt_nonce
    }
}

#[cfg(test)]
impl ProofAttemptKernel {
    pub(super) fn new_reuse_disabled_for_test() -> Self {
        Self {
            attempt_nonce: None,
            reuse_disabled: true,
            terminal_failure: RefCell::new(None),
            structural: ProofStructuralState::default(),
            injected_query_scope_failure: RefCell::new(None),
            injected_post_scope_failure: RefCell::new(None),
            query_trace: QueryAccessTrace::default(),
        }
    }

    pub(super) fn shadow_snapshot_value(&self) -> u64 {
        self.structural.shadow_snapshot_value()
    }

    pub(super) fn inject_query_scope_failure(&self, failure: ProofFailure) {
        *self.injected_query_scope_failure.borrow_mut() = Some(failure);
    }

    pub(super) fn inject_post_scope_failure(&self, failure: ProofFailure) {
        *self.injected_post_scope_failure.borrow_mut() = Some(failure);
    }

    pub(super) fn query_trace(&self) -> (usize, usize, usize, usize, usize) {
        (
            self.query_trace.active_checks.get(),
            self.query_trace.round_authentications.get(),
            self.query_trace.authenticated_round_state_entries.get(),
            self.query_trace.scope_entries.get(),
            self.query_trace.post_scope_checks.get(),
        )
    }

    pub(super) fn reset_query_trace(&self) {
        self.query_trace.active_checks.set(0);
        self.query_trace.round_authentications.set(0);
        self.query_trace.authenticated_round_state_entries.set(0);
        self.query_trace.scope_entries.set(0);
        self.query_trace.post_scope_checks.set(0);
    }

    pub(super) fn query_latch_busy_failure_for_test(&self) -> ProofFailure {
        let _held = self.terminal_failure.borrow_mut();
        self.ensure_query_kernel_active()
            .expect_err("held query terminal latch must reject access")
    }
}
