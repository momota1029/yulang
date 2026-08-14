//! Sibling family handlers. They can name gateway-issued ports, but no raw gateway storage.

#![allow(unexpected_cfgs)]

pub(super) mod bounds;
pub(super) mod constraints;
pub(super) mod identities;
pub(super) mod proof;
pub(super) mod rows;

// These four probes are compiled one at a time by the SS1 UI gate. Each is
// deliberately ill-formed; keeping it next to the sibling family modules makes
// the visibility boundary under test identical to the production layout.
#[cfg(cpk_sv_d_ss1_ui_prepared_command)]
fn ui_prepared_command_literal_is_rejected() {
    let _ = super::gateway::PreparedStructuralCommand {};
}

#[cfg(cpk_sv_d_ss1_ui_prepared_payload)]
fn ui_prepared_payload_is_rejected() {
    let _ = super::gateway::PreparedPayload::MoveUpperClaim;
}

#[cfg(cpk_sv_d_ss1_ui_active_capability)]
fn ui_active_capability_construction_is_rejected() {
    let _ = super::access::ActiveProofAttempt {
        terminal_failure: unreachable!(),
        attempt_nonce: None,
        reuse_disabled: false,
    };
}

#[cfg(cpk_sv_d_ss1_ui_capability_ticket)]
fn ui_ticket_and_reserved_operation_construction_is_rejected() {
    let _ = super::gateway::reservation::ReservationTicketId(unreachable!());
    let _ = super::gateway::reservation::ReservedOperation {
        ticket: unreachable!(),
        domain: unreachable!(),
    };
}

#[cfg(cpk_sv_d_ss1_ui_raw_structural_data)]
fn ui_raw_structural_data_is_rejected(data: &mut super::gateway::StructuralData) {
    let _ = &mut data.proof;
}
