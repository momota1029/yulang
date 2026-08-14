//! Shadow-only sealed structural kernel introduced by CPK-SV-D-SS1.
//!
//! Production proof storage and reads remain in their pre-SS1 owners. This module establishes the
//! closed command, capability, reservation, and visibility boundaries before any family migrates.

#![allow(unexpected_cfgs)]
#![deny(private_bounds, private_interfaces)]

mod access;
mod commands;
mod families;
mod gateway;
mod read_view;

pub(in crate::constraints) use access::{
    CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle,
    ProjectionEvaluationRoundState, ProofAccessError, ProofAttemptKernel, ProofAttemptNonce,
    ProofQueryError, QueryCompletion, ScopedProjectionQuery, ScopedPublicationProjectionQuery,
    StructuralPreparationScope,
};
pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};

#[cfg(test)]
mod tests;

#[cfg(cpk_sv_d_ss1_rf_ui_raw_escape)]
fn ui_query_raw_reference_escape_is_rejected<'a>(
    machine: &'a mut crate::constraints::ConstraintMachine,
    round: &'a mut ProjectionEvaluationRoundState,
) -> Result<&'a u64, ProofQueryError> {
    machine.with_projection_query(round, |query| {
        let escaped = query.view().raw_shadow_probe();
        Ok(query.complete(escaped))
    })
}

#[cfg(cpk_sv_d_ss1_rf_ui_same_kernel_mutation)]
fn ui_same_kernel_mutation_inside_scope_is_rejected(
    machine: &mut crate::constraints::ConstraintMachine,
    round: &mut ProjectionEvaluationRoundState,
) {
    let _ = machine.with_projection_query(round, |query| {
        machine.mark_proof_terminal_failure(
            crate::constraints::proof::ProofOperation::ProjectLowerEvaluation,
            crate::constraints::proof::ProofFailure::ResourceExhausted {
                operation: crate::constraints::proof::ProofOperation::ProjectLowerEvaluation,
            },
        );
        Ok(query.complete(()))
    });
}
