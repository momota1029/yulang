//! Generic attempt-quarantine channel retained after the RCPF shell removal.
//!
//! The publication fence can still fail capacity preflight, and lowering must discard that whole
//! attempt. CPK-8G-12 owns the later telemetry/name consolidation into the CPK hard-failure channel.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplayFactoredShadowFailure {
    AllocationFailed,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) enum ReplayFactoredShadowStatus {
    #[default]
    Active,
    Failed(ReplayFactoredShadowFailure),
}

pub(super) type ReplayFactoredResult<T> = Result<T, ReplayFactoredShadowFailure>;
