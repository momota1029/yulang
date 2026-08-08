//! RCPF attempt-quarantine shell retained until CPK-8G-10.

#![allow(dead_code)]

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplayFactoredShadowFailure {
    AllocationFailed,
    #[cfg(any(test, debug_assertions))]
    OracleMismatch(ReplayFactoredOracleMismatch),
}

#[cfg(any(test, debug_assertions))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplayFactoredOracleMismatch {
    ExactParentRelation,
    QualifiedReplayCarriers,
    ClauseMapping,
    ExactClauseLinks,
    AttributedRoots,
    ClaimedAttributionUnion,
    ReplayDependencyEdges,
    DerivedReplayLineage,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) enum ReplayFactoredShadowStatus {
    #[default]
    Active,
    Failed(ReplayFactoredShadowFailure),
}

pub(super) type ReplayFactoredResult<T> = Result<T, ReplayFactoredShadowFailure>;
