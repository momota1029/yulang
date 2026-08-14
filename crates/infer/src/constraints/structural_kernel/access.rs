//! Attempt capability, terminal latch, preparation scopes, and opaque query shells.

use std::cell::RefCell;
use std::marker::PhantomData;
use std::num::NonZeroU64;
use std::sync::atomic::{AtomicU64, Ordering};

use super::commands::{CommittedStructuralMutation, StructuralMutationIntent};
use super::gateway::{PreparationScopeNonce, PreparedMutationSlotId, ProofStructuralState};
use super::read_view::ScopedQueryView;
use crate::constraints::proof::{ProofFailure, ProofOperation};
use crate::constraints::record_proof_terminal_failure;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::constraints) struct ProofAttemptNonce(NonZeroU64);

static NEXT_PROOF_ATTEMPT_NONCE: AtomicU64 = AtomicU64::new(1);

fn mint_proof_attempt_nonce() -> Option<ProofAttemptNonce> {
    NEXT_PROOF_ATTEMPT_NONCE
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
            next.checked_add(1)
        })
        .ok()
        .and_then(NonZeroU64::new)
        .map(ProofAttemptNonce)
}

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
}

impl ProofAttemptKernel {
    pub(in crate::constraints) fn new() -> Self {
        let attempt_nonce = mint_proof_attempt_nonce();
        Self {
            attempt_nonce,
            reuse_disabled: attempt_nonce.is_none(),
            terminal_failure: RefCell::new(None),
            structural: ProofStructuralState::default(),
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

    #[cfg(test)]
    pub(super) fn shadow_state(&self) -> &ProofStructuralState {
        &self.structural
    }
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

pub(in crate::constraints) struct QueryCompletion<R> {
    value: R,
    candidates: SuccessfulValidationCandidates,
}

pub(in crate::constraints) struct ScopedProjectionQuery<'query> {
    view: ScopedQueryView<'query>,
    candidates: SuccessfulValidationCandidates,
}

pub(in crate::constraints) struct ScopedPublicationProjectionQuery<'query> {
    view: ScopedQueryView<'query>,
    candidates: SuccessfulValidationCandidates,
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

#[derive(Debug)]
pub(in crate::constraints) struct ProjectionEvaluationRoundState {
    attempt_nonce: Option<ProofAttemptNonce>,
    reuse_disabled: bool,
}

#[derive(Debug)]
pub(in crate::constraints) struct CpkPublicationEvaluationRoundState {
    attempt_nonce: Option<ProofAttemptNonce>,
    reuse_disabled: bool,
}

impl<R> QueryCompletion<R> {
    #[allow(dead_code)]
    fn into_parts(self) -> (R, SuccessfulValidationCandidates) {
        (self.value, self.candidates)
    }
}
