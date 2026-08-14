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
    CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
    ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery, ScopedProjectionQuery,
    ScopedPublicationProjectionQuery, StructuralPreparationScope,
};
pub(crate) use access::{
    ProjectionEvaluationRoundState, QueryCompletion, ScopedLegacyProjectionQuery,
};
pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};

#[cfg(test)]
mod tests;

#[cfg(cpk_sv_d_ss1_rf_ui_raw_escape)]
fn ui_query_raw_reference_escape_is_rejected<'a>(
    machine: &'a mut crate::constraints::ConstraintMachine,
    round: &'a mut ProjectionEvaluationRoundState,
) -> Result<&'a u64, crate::constraints::proof::ProofFailure> {
    machine.with_projection_query(round, |query| {
        let escaped = query.raw_shadow_probe();
        Ok(query.complete(escaped))
    })
}

#[cfg(cpk_sv_d_ss1_rf_ui_cursor_escape)]
fn ui_query_cursor_escape_is_rejected<'a>(
    machine: &'a mut crate::constraints::ConstraintMachine,
    round: &'a mut ProjectionEvaluationRoundState,
) -> Result<read_view::ShadowQueryCursor<'a>, crate::constraints::proof::ProofFailure> {
    machine.with_projection_query(round, |query| {
        let escaped = query.shadow_cursor();
        let _ = escaped.value();
        Ok(query.complete(escaped))
    })
}

#[cfg(cpk_sv_d_ss1_rf_ui_round_view_storage)]
struct UiRoundViewHolder<'a> {
    view: ScopedQueryView<'a>,
}

#[cfg(cpk_sv_d_ss1_rf_ui_round_view_storage)]
fn ui_query_view_cannot_be_stored_in_round<'a>(
    machine: &'a mut crate::constraints::ConstraintMachine,
    round: &'a mut ProjectionEvaluationRoundState,
) -> Result<UiRoundViewHolder<'a>, crate::constraints::proof::ProofFailure> {
    machine.with_projection_query(round, |query| {
        Ok(query.complete_with_owned_view(|view| UiRoundViewHolder { view }))
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

#[cfg(cpk_sv_d_ss1_rf_ui_nonce_forge)]
fn ui_constraints_sibling_cannot_forge_attempt_nonce() -> ProofAttemptNonce {
    ProofAttemptNonce(std::num::NonZeroU64::new(7).unwrap())
}
