//! Private round-reuse typestate for the partial-sealing window.

use crate::constraints::proof::ProofStructuralSnapshotId;

#[derive(Debug)]
enum RoundReuseState<T> {
    SealingIncomplete,
    #[allow(dead_code, reason = "SS6 installs the witness-consuming constructor")]
    Sealed {
        snapshot: ProofStructuralSnapshotId,
        reusable: T,
    },
}

/// Opaque to `access.rs`: only this module can name or construct the inner state.
#[derive(Debug)]
pub(super) struct RoundReuseSlot<T>(RoundReuseState<T>);

impl<T> RoundReuseSlot<T> {
    pub(super) fn sealing_incomplete() -> Self {
        Self(RoundReuseState::SealingIncomplete)
    }

    pub(super) fn is_sealing_incomplete(&self) -> bool {
        matches!(self.0, RoundReuseState::SealingIncomplete)
    }

    // SS6 adds the sole `sealed(witness, reusable)` constructor here. Keeping it absent in
    // SS1-RF makes premature activation impossible rather than exposing a placeholder bypass.
}
