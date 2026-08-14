//! Attempt capability, terminal latch, preparation scopes, and opaque query shells.

mod legacy_read_view;
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
use crate::constraints::proof::{self, ProofFailure, ProofOperation, mint_proof_attempt_nonce};
use crate::constraints::{
    ConstraintMachine, SchemeProjectableLower, SchemeProjectableLowerReason,
    record_proof_terminal_failure,
};
use poly::types::{PosId, TypeArena, TypeVar};

use sealing::RoundReuseSlot;

use legacy_read_view::{
    LegacyConstraintReplayReadSources, LegacyIdentityReadSources, LegacyOnlyQueryView,
    LegacyOnlyReadSources, LegacyRowReadSources,
};

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

    #[allow(
        dead_code,
        reason = "SS2 final cutover connects the sealed projection query wrapper"
    )]
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

    fn with_legacy_projection_query<'legacy, R>(
        &mut self,
        type_shapes: &'legacy TypeArena,
        sources: LegacyOnlyReadSources<'legacy>,
        round: &mut ProjectionEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedLegacyProjectionQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure> {
        // 1. Authenticate the current kernel before inspecting caller-owned round state.
        self.ensure_query_kernel_active()?;
        // 2. A legacy read route still belongs to exactly one proof attempt.
        let access = self.authenticate_round(round.attempt_nonce, round.reuse_disabled)?;
        #[cfg(test)]
        self.query_trace
            .authenticated_round_state_entries
            .set(self.query_trace.authenticated_round_state_entries.get() + 1);
        // 3. Only an authenticated round may contribute its sticky failure.
        if access == AuthenticatedRoundAccess::Bound {
            if let Some(failure) = &round.terminal_failure {
                return Err(failure.clone());
            }
        }
        // 4. P0 remains SealingIncomplete and never binds persistent success state.
        debug_assert!(round.reuse.is_sealing_incomplete());
        // 5. The all-legacy sources and all invocation state live inside this HRTB call.
        let result: Result<QueryCompletion<R>, ProofFailure> = (|| {
            #[cfg(test)]
            if let Some(failure) = self.injected_query_scope_failure.borrow_mut().take() {
                return Err(failure);
            }
            let scope = ScopedLegacyProjectionQuery::try_new(
                sources,
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
                // 6. No candidate leaves the scope before kernel and round authentication repeat.
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

    fn with_legacy_publication_query<'legacy, R>(
        &mut self,
        type_shapes: &'legacy TypeArena,
        sources: LegacyOnlyReadSources<'legacy>,
        round: &mut CpkPublicationEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedLegacyPublicationQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure> {
        // Steps 1--3: kernel authority, attempt identity, publication's no-op round latch.
        self.ensure_query_kernel_active()?;
        let access = self.authenticate_round(round.attempt_nonce, round.reuse_disabled)?;
        #[cfg(test)]
        self.query_trace
            .authenticated_round_state_entries
            .set(self.query_trace.authenticated_round_state_entries.get() + 1);
        debug_assert!(round.reuse.is_sealing_incomplete());
        // Steps 4--5: P0 sources and publication memo state are invocation-local.
        let result: Result<QueryCompletion<R>, ProofFailure> = (|| {
            #[cfg(test)]
            if let Some(failure) = self.injected_query_scope_failure.borrow_mut().take() {
                return Err(failure);
            }
            let scope = ScopedLegacyPublicationQuery::try_new(
                sources,
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
                // Step 6: candidate publication remains behind a post-scope recheck.
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

pub(crate) struct QueryCompletion<R> {
    value: R,
    candidates: SuccessfulValidationCandidates,
}

#[allow(
    dead_code,
    reason = "SS2 final cutover consumes the sealed projection query facade"
)]
pub(crate) struct ScopedProjectionQuery<'query> {
    view: ScopedQueryView<'query>,
    candidates: SuccessfulValidationCandidates,
    invocation: ProjectionInvocationState,
}

pub(in crate::constraints) struct ScopedPublicationProjectionQuery<'query> {
    view: ScopedQueryView<'query>,
    candidates: SuccessfulValidationCandidates,
    invocation: PublicationInvocationState,
}

/// P0 projection facade backed exclusively by current production-owned legacy storage.
pub(crate) struct ScopedLegacyProjectionQuery<'query> {
    view: LegacyOnlyQueryView<'query>,
    candidates: SuccessfulValidationCandidates,
    invocation: ProjectionInvocationState,
}

/// P0 publication facade backed exclusively by current production-owned legacy storage.
pub(in crate::constraints) struct ScopedLegacyPublicationQuery<'query> {
    view: LegacyOnlyQueryView<'query>,
    candidates: SuccessfulValidationCandidates,
    invocation: PublicationInvocationState,
}

macro_rules! query_shell {
    ($(#[$implementation_attribute:meta])* $name:ident, $complete_visibility:vis) => {
        $(#[$implementation_attribute])*
        impl $name<'_> {
            pub(in crate::constraints) fn view(&self) -> &ScopedQueryView<'_> {
                &self.view
            }

            $complete_visibility fn complete<R>(self, value: R) -> QueryCompletion<R> {
                QueryCompletion {
                    value,
                    candidates: self.candidates,
                }
            }
        }
    };
}

query_shell!(
    #[allow(
        dead_code,
        reason = "SS2 final cutover consumes the sealed projection query accessors"
    )]
    ScopedProjectionQuery,
    pub(crate)
);
query_shell!(
    ScopedPublicationProjectionQuery,
    pub(in crate::constraints)
);

impl<'query> ScopedProjectionQuery<'query> {
    #[allow(
        dead_code,
        reason = "SS2 final cutover constructs the sealed projection query facade"
    )]
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

    #[allow(
        dead_code,
        reason = "SS2 final cutover resolves projection variables through the sealed facade"
    )]
    pub(crate) fn pos_var_in_scope(&self, pos: PosId) -> Option<TypeVar> {
        self.view.type_shapes().pos_var(pos)
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

impl<'query> ScopedLegacyProjectionQuery<'query> {
    fn try_new(
        sources: LegacyOnlyReadSources<'query>,
        type_shapes: super::read_view::ImmutableTypeShapeView<'query>,
    ) -> Result<Self, ProofFailure> {
        Ok(Self {
            view: LegacyOnlyQueryView::new(sources, type_shapes),
            candidates: SuccessfulValidationCandidates,
            invocation: ProjectionInvocationState::default(),
        })
    }

    pub(crate) fn complete<R>(self, value: R) -> QueryCompletion<R> {
        QueryCompletion {
            value,
            candidates: self.candidates,
        }
    }

    pub(crate) fn scheme_projectable_lowers_in_scope<'scope>(
        &'scope self,
        var: TypeVar,
        round: &mut proof::ProjectionEvaluationRound<'scope>,
    ) -> Result<Vec<SchemeProjectableLower<'scope>>, ProofFailure> {
        let records = self.view.projection_lower_records(var);
        let mut lowers = Vec::new();
        for (record, bound) in records {
            let decision = self.view.project_lower(record, round)?;
            let (reason, projection_evidence) = match decision {
                proof::ProjectionDecision::Excluded => continue,
                proof::ProjectionDecision::Unclaimed => {
                    (SchemeProjectableLowerReason::Unclaimed, None)
                }
                proof::ProjectionDecision::Included { supports, evidence } => (
                    SchemeProjectableLowerReason::Qualified {
                        uncovered_claims: supports
                            .uncovered_claims
                            .into_iter()
                            .map(|support| support.representative_claim)
                            .collect(),
                        independent_supports: supports.independent_supports,
                    },
                    Some(evidence),
                ),
            };
            lowers.push(SchemeProjectableLower {
                record,
                bound,
                reason,
                projection_evidence,
            });
        }
        Ok(lowers)
    }

    pub(crate) fn pos_var_in_scope(&self, pos: PosId) -> Option<TypeVar> {
        self.view.pos_var(pos)
    }

    #[cfg(test)]
    pub(super) fn legacy_storage_census(&self) -> legacy_read_view::LegacyStorageCensus {
        self.view.storage_census()
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

    #[cfg(cpk_sv_d_ss2_p0_ui_legacy_view_storage)]
    fn complete_with_owned_view<R>(
        self,
        finish: impl FnOnce(LegacyOnlyQueryView<'query>) -> R,
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
}

impl<'query> ScopedLegacyPublicationQuery<'query> {
    fn try_new(
        sources: LegacyOnlyReadSources<'query>,
        type_shapes: super::read_view::ImmutableTypeShapeView<'query>,
    ) -> Result<Self, ProofFailure> {
        Ok(Self {
            view: LegacyOnlyQueryView::new(sources, type_shapes),
            candidates: SuccessfulValidationCandidates,
            invocation: PublicationInvocationState::default(),
        })
    }

    pub(in crate::constraints) fn complete<R>(self, value: R) -> QueryCompletion<R> {
        QueryCompletion {
            value,
            candidates: self.candidates,
        }
    }

    pub(in crate::constraints) fn cpk_projection_evaluator(
        &self,
    ) -> proof::CpkProjectionEvaluator<'_> {
        self.view.cpk_projection_evaluator()
    }

    pub(in crate::constraints) fn active_projection_record_owner(
        &self,
        record: crate::constraints::BoundRecordId,
    ) -> Option<TypeVar> {
        self.view.active_projection_record_owner(record)
    }

    #[cfg(test)]
    pub(super) fn legacy_storage_census(&self) -> legacy_read_view::LegacyStorageCensus {
        self.view.storage_census()
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
}

#[cfg(cpk_sv_d_ss2_p0_ui_legacy_view_storage)]
struct UiLegacyRoundViewHolder<'query> {
    view: LegacyOnlyQueryView<'query>,
}

#[cfg(cpk_sv_d_ss2_p0_ui_legacy_view_storage)]
fn ui_legacy_view_cannot_be_stored_in_round<'machine>(
    machine: &'machine mut ConstraintMachine,
    round: &'machine mut ProjectionEvaluationRoundState,
) -> Result<UiLegacyRoundViewHolder<'machine>, ProofFailure> {
    machine.with_legacy_projection_query(round, |query| {
        Ok(query.complete_with_owned_view(|view| UiLegacyRoundViewHolder { view }))
    })
}

#[derive(Debug)]
pub(crate) struct ProjectionEvaluationRoundState {
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

/// One disjoint borrow of the machine fields required by the P0 all-legacy route.
struct LegacyQueryMachineFields<'machine> {
    type_shapes: &'machine TypeArena,
    proof_attempt: &'machine mut ProofAttemptKernel,
    sources: LegacyOnlyReadSources<'machine>,
}

impl<'machine> LegacyQueryMachineFields<'machine> {
    fn split(machine: &'machine mut ConstraintMachine) -> Self {
        let ConstraintMachine {
            types,
            bounds,
            proof_store,
            proof_attempt,
            row_residuals,
            row_residual_record_ids,
            row_residual_records,
            unweighted_row_reductions_by_source,
            unweighted_row_reduction_owners_by_upper,
            unweighted_row_reduction_records,
            row_derivations,
            row_derivation_index,
            lower_filters,
            lower_filter_record_ids,
            lower_filter_records,
            canonical_constraints,
            constraint_records,
            replay_drop_records,
            replay_drop_index,
            replay_derivation_budget,
            replay_derivation_storage,
            origins,
            source_boundaries,
            generalized_schemes,
            generalized_witnesses,
            scheme_instantiations,
            scheme_instantiation_index,
            // Non-routed machine orchestration and diagnostic sidecars are explicit so a newly
            // added field makes this census non-exhaustive until its authority is classified.
            queue: _,
            var_adjacency: _,
            subtracts: _,
            levels: _,
            next_internal_type_var: _,
            bound_dispositions: _,
            declared_subtracts: _,
            effect_family_paths: _,
            row_tail_vars: _,
            pre_pop_effect_families: _,
            effect_filter_violations: _,
            events: _,
            method_role_mutations: _,
            timing: _,
            epoch: _,
            provenance_epoch: _,
            role_solve_supplemental_epoch: _,
            replay_frontier_shadow: _,
            replay_routing_shadow: _,
            #[cfg(test)]
                cdm_lower_delta_census: _,
            #[cfg(test)]
                semantic_execution_trace: _,
        } = machine;

        let constraints_replay = LegacyConstraintReplayReadSources::new(
            canonical_constraints,
            constraint_records,
            replay_drop_records,
            replay_drop_index,
            replay_derivation_budget,
            replay_derivation_storage,
        );
        let rows = LegacyRowReadSources::new(
            row_residuals,
            row_residual_record_ids,
            row_residual_records,
            unweighted_row_reductions_by_source,
            unweighted_row_reduction_owners_by_upper,
            unweighted_row_reduction_records,
            row_derivations,
            row_derivation_index,
            lower_filters,
            lower_filter_record_ids,
            lower_filter_records,
        );
        let identities = LegacyIdentityReadSources::new(
            origins,
            source_boundaries,
            generalized_schemes,
            generalized_witnesses,
            scheme_instantiations,
            scheme_instantiation_index,
        );

        Self {
            type_shapes: types,
            proof_attempt,
            sources: LegacyOnlyReadSources::new(
                proof_store,
                bounds,
                constraints_replay,
                rows,
                identities,
            ),
        }
    }
}

impl ConstraintMachine {
    pub(crate) fn new_projection_evaluation_round(&self) -> ProjectionEvaluationRoundState {
        self.proof_attempt.new_projection_evaluation_round()
    }

    pub(in crate::constraints) fn new_publication_evaluation_round(
        &self,
    ) -> CpkPublicationEvaluationRoundState {
        self.proof_attempt.new_publication_evaluation_round()
    }

    #[deny(private_bounds, private_interfaces)]
    #[allow(
        dead_code,
        reason = "SS2 final cutover connects production callers to the sealed projection facade"
    )]
    pub(crate) fn with_projection_query<R>(
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

    #[deny(private_bounds, private_interfaces)]
    pub(crate) fn with_legacy_projection_query<R>(
        &mut self,
        round: &mut ProjectionEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedLegacyProjectionQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure> {
        let LegacyQueryMachineFields {
            type_shapes,
            proof_attempt,
            sources,
        } = LegacyQueryMachineFields::split(self);
        proof_attempt.with_legacy_projection_query(type_shapes, sources, round, query)
    }

    #[deny(private_bounds, private_interfaces)]
    pub(in crate::constraints) fn with_legacy_publication_query<R>(
        &mut self,
        round: &mut CpkPublicationEvaluationRoundState,
        query: impl for<'query> FnOnce(
            ScopedLegacyPublicationQuery<'query>,
        ) -> Result<QueryCompletion<R>, ProofFailure>,
    ) -> Result<R, ProofFailure> {
        let LegacyQueryMachineFields {
            type_shapes,
            proof_attempt,
            sources,
        } = LegacyQueryMachineFields::split(self);
        proof_attempt.with_legacy_publication_query(type_shapes, sources, round, query)
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
