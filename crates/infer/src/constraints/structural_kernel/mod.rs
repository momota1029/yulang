//! Shadow-only sealed structural kernel introduced by CPK-SV-D-SS1.
//!
//! Production proof storage and reads remain in their pre-SS1 owners. This module establishes the
//! closed command, capability, reservation, and visibility boundaries before any family migrates.

mod access;
mod commands;
mod families;
mod gateway;
mod read_view;

pub(in crate::constraints) use access::{
    CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle,
    ProjectionEvaluationRoundState, ProofAccessError, ProofAttemptKernel, ProofAttemptNonce,
    QueryCompletion, ScopedProjectionQuery, ScopedPublicationProjectionQuery,
    StructuralPreparationScope,
};
pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};

#[cfg(test)]
mod tests;
