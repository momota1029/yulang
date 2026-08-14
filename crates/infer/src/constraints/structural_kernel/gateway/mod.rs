//! Sealed shadow gateway. No production proof read or write is routed here in SS1.

mod reservation;
mod storage;
mod unchanged;
mod write_ports;

use super::access::{ActiveProofAttempt, ProofAccessError};
use super::commands::{CommittedStructuralMutation, StructuralMutationIntent};
use super::families;
use reservation::{
    ReservationClaim, ReservationTicketId, ReservedOperation, StructuralReservationLedger,
    StructuralReservationTicket, StructuralResourceDomainKey, VerifiedReservedOperation,
};
use unchanged::ExplicitNoOpProof;

pub(in crate::constraints::structural_kernel) use storage::StructuralData;
pub(in crate::constraints::structural_kernel) use write_ports::{
    BoundsPublishPort, ConstraintsPublishPort, IdentitiesPublishPort, ProofPublishPort,
    RowsPublishPort,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct PreparedMutationSlotId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct PreparationScopeNonce(u64);

#[derive(Debug)]
enum PreparedPayload {
    AppendProofOccurrence,
    AdmitProjectionSupport,
    AdmitProjectionFormulaClause,
    AdmitProjectionIndex,
    AdmitOriginalClaim,
    DecideDerivedClaim,
    MoveUpperClaim,
    BindReductionClaim,
    TransitionLiveCoverage,
    AdmitReplayRelation,
    AdmitReplayQualifiedParents,
    AdmitQualifiedParents,
    AdmitBound,
    PromoteBound,
    TombstoneBound,
    ExtendBoundDerivation,
    AdmitConstraint,
    ExtendConstraintProof,
    UpdateReplayCompleteness,
    AdmitReplayDrop,
    AdmitRowResidual,
    AdmitRowDerivation,
    AdmitRowReduction,
    AdvanceRowReductionMatched,
    AdvanceRowReductionUnmatched,
    UpdateRowReductionOwner,
    AdmitLowerFilter,
    AdmitStructuralIdentity,
    AdmitSchemeInstantiation,
}

#[derive(Debug)]
pub(in crate::constraints::structural_kernel) struct PreparedStructuralCommand {
    payload: PreparedPayload,
    ticket: StructuralReservationTicket,
    reserved_operations: Vec<ReservedOperation>,
}

#[derive(Debug)]
struct PreparedStructuralMutation {
    scope: PreparationScopeNonce,
    command: PreparedStructuralCommand,
}

#[derive(Debug, Default)]
struct PreparedMutationArena {
    entries: Vec<Option<PreparedStructuralMutation>>,
}

#[derive(Debug)]
enum StructuralMutationDisposition {
    Changed,
    Unchanged(ExplicitNoOpProof),
}

#[derive(Debug, Default)]
pub(in crate::constraints::structural_kernel) struct ProofStructuralState {
    data: StructuralData,
    shadow_snapshot: u64,
    reservations: StructuralReservationLedger,
    prepared: PreparedMutationArena,
    next_scope_nonce: u64,
}

impl ProofStructuralState {
    pub(super) fn next_scope_nonce(&mut self) -> PreparationScopeNonce {
        let nonce = PreparationScopeNonce(self.next_scope_nonce);
        self.next_scope_nonce = self.next_scope_nonce.saturating_add(1);
        nonce
    }

    pub(in crate::constraints::structural_kernel) fn prepare(
        &mut self,
        active: &ActiveProofAttempt<'_>,
        scope: PreparationScopeNonce,
        intent: StructuralMutationIntent,
    ) -> Result<PreparedMutationSlotId, ProofAccessError> {
        active.ensure_active()?;
        self.try_reserve_arena_slot()?;
        let payload = prepare_payload(intent);
        let claims = reservation_plan(&payload)?;
        let (ticket, reserved_operations) = self
            .reservations
            .reserve(&claims)
            .map_err(|_| ProofAccessError::StructuralResourceExhausted)?;
        let command = PreparedStructuralCommand {
            payload,
            ticket,
            reserved_operations,
        };
        let entry = PreparedStructuralMutation { scope, command };
        if let Some((index, slot)) = self
            .prepared
            .entries
            .iter_mut()
            .enumerate()
            .find(|(_, entry)| entry.is_none())
        {
            *slot = Some(entry);
            return Ok(PreparedMutationSlotId(index));
        }
        let index = self.prepared.entries.len();
        self.prepared.entries.push(Some(entry));
        Ok(PreparedMutationSlotId(index))
    }

    fn try_reserve_arena_slot(&mut self) -> Result<(), ProofAccessError> {
        if self.prepared.entries.iter().any(Option::is_none) {
            return Ok(());
        }
        self.prepared
            .entries
            .try_reserve(1)
            .map_err(|_| ProofAccessError::StructuralResourceExhausted)
    }

    pub(in crate::constraints::structural_kernel) fn commit(
        &mut self,
        active: &ActiveProofAttempt<'_>,
        scope: PreparationScopeNonce,
        slot: PreparedMutationSlotId,
    ) -> Result<CommittedStructuralMutation, ProofAccessError> {
        let mut guard = InFlightCommitGuard::take(self, scope, slot)?;
        active.ensure_active()?;
        guard.commit(false, false)
    }

    #[cfg(test)]
    pub(super) fn commit_with_injected_exit(
        &mut self,
        active: &ActiveProofAttempt<'_>,
        scope: PreparationScopeNonce,
        slot: PreparedMutationSlotId,
        early_error: bool,
        panic_mid_commit: bool,
    ) -> Result<CommittedStructuralMutation, ProofAccessError> {
        let mut guard = InFlightCommitGuard::take(self, scope, slot)?;
        active.ensure_active()?;
        guard.pin_first_reserved_domain_for_cleanup_probe();
        guard.commit(early_error, panic_mid_commit)
    }

    pub(super) fn cancel_scope_slots_and_release_tickets(
        &mut self,
        scope: PreparationScopeNonce,
        live_slots: &mut Vec<PreparedMutationSlotId>,
    ) {
        for slot in live_slots.drain(..) {
            let Some(entry) = self.prepared.entries.get_mut(slot.0).and_then(Option::take) else {
                continue;
            };
            if entry.scope == scope {
                self.release_prepared(entry);
            } else {
                self.prepared.entries[slot.0] = Some(entry);
            }
        }
    }

    pub(super) fn cancel_slot(
        &mut self,
        scope: PreparationScopeNonce,
        slot: PreparedMutationSlotId,
    ) -> Result<(), ProofAccessError> {
        let entry = self
            .prepared
            .entries
            .get_mut(slot.0)
            .and_then(Option::take)
            .ok_or(ProofAccessError::InvalidPreparedHandle)?;
        if entry.scope != scope {
            self.prepared.entries[slot.0] = Some(entry);
            return Err(ProofAccessError::InvalidPreparedHandle);
        }
        self.release_prepared(entry);
        Ok(())
    }

    fn release_prepared(&mut self, prepared: PreparedStructuralMutation) {
        self.reservations.release(prepared.command.ticket);
    }

    #[cfg(test)]
    pub(super) fn shadow_counts(&self) -> ([u64; 5], u64, usize, usize, usize, usize) {
        let (tickets, outstanding, pins) = self.reservations.counts();
        (
            self.data.shadow_publication_counts(),
            self.shadow_snapshot,
            self.prepared.entries.iter().flatten().count(),
            tickets,
            outstanding,
            pins,
        )
    }

    #[cfg(test)]
    pub(super) fn corrupt_first_reserved_domain_for_test(
        &mut self,
        scope: PreparationScopeNonce,
        slot: PreparedMutationSlotId,
    ) -> Result<(), ProofAccessError> {
        let prepared = self
            .prepared
            .entries
            .get_mut(slot.0)
            .and_then(Option::as_mut)
            .filter(|prepared| prepared.scope == scope)
            .ok_or(ProofAccessError::InvalidPreparedHandle)?;
        prepared
            .command
            .reserved_operations
            .first_mut()
            .ok_or(ProofAccessError::InvalidReservedOperation)?
            .replace_domain_for_test(StructuralResourceDomainKey::BoundRecords);
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn corrupt_projection_formula_secondary_domain_for_test(
        &mut self,
        scope: PreparationScopeNonce,
        slot: PreparedMutationSlotId,
    ) -> Result<(), ProofAccessError> {
        let prepared = self
            .prepared
            .entries
            .get_mut(slot.0)
            .and_then(Option::as_mut)
            .filter(|prepared| prepared.scope == scope)
            .ok_or(ProofAccessError::InvalidPreparedHandle)?;
        prepared
            .command
            .reserved_operations
            .iter_mut()
            .find(|operation| {
                operation.domain() == StructuralResourceDomainKey::ProjectionLowerByConstraint
            })
            .ok_or(ProofAccessError::InvalidReservedOperation)?
            .replace_domain_for_test(StructuralResourceDomainKey::BoundRecords);
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn exhaust_snapshot_for_test(&mut self) {
        self.shadow_snapshot = u64::MAX;
    }
}

struct InFlightCommitGuard<'state> {
    state: &'state mut ProofStructuralState,
    prepared: Option<PreparedStructuralMutation>,
}

impl<'state> InFlightCommitGuard<'state> {
    fn take(
        state: &'state mut ProofStructuralState,
        scope: PreparationScopeNonce,
        slot: PreparedMutationSlotId,
    ) -> Result<Self, ProofAccessError> {
        let prepared = state
            .prepared
            .entries
            .get_mut(slot.0)
            .and_then(Option::take)
            .ok_or(ProofAccessError::InvalidPreparedHandle)?;
        if prepared.scope != scope {
            state.prepared.entries[slot.0] = Some(prepared);
            return Err(ProofAccessError::InvalidPreparedHandle);
        }
        Ok(Self {
            state,
            prepared: Some(prepared),
        })
    }

    fn commit(
        &mut self,
        early_error: bool,
        panic_mid_commit: bool,
    ) -> Result<CommittedStructuralMutation, ProofAccessError> {
        if early_error {
            return Err(ProofAccessError::InjectedShadowFailure);
        }
        if panic_mid_commit {
            panic!("CPK-SV-D-SS1 deliberate mid-commit panic");
        }
        let prepared = self.prepared.as_mut().expect("in-flight command");
        let disposition = try_prove_unchanged(&prepared.command.payload).map_or(
            StructuralMutationDisposition::Changed,
            StructuralMutationDisposition::Unchanged,
        );
        let receipt = match disposition {
            StructuralMutationDisposition::Changed => {
                let command = &mut prepared.command;
                // Snapshot exhaustion is checked before the first publication. Once cache reads
                // become authoritative, a changed write must never complete without a fresh ID.
                let next_snapshot = self
                    .state
                    .shadow_snapshot
                    .checked_add(1)
                    .ok_or(ProofAccessError::StructuralSnapshotExhausted)?;
                let plan = verify_changed_publication(
                    &command.payload,
                    command.ticket.id,
                    &mut command.reserved_operations,
                )?;
                let receipt = publish_verified_plan(plan, &mut self.state.data);
                self.state.shadow_snapshot = next_snapshot;
                receipt
            }
            StructuralMutationDisposition::Unchanged(proof) => match proof {},
        };
        let prepared = self.prepared.take().expect("in-flight command");
        self.state.reservations.release(prepared.command.ticket);
        Ok(receipt)
    }

    #[cfg(test)]
    fn pin_first_reserved_domain_for_cleanup_probe(&mut self) {
        let domain = self
            .prepared
            .as_ref()
            .and_then(|prepared| prepared.command.reserved_operations.first())
            .map(ReservedOperation::domain);
        if let Some(domain) = domain {
            self.state.reservations.mark_pending_empty_prune(domain);
        }
    }
}

impl Drop for InFlightCommitGuard<'_> {
    fn drop(&mut self) {
        if let Some(prepared) = self.prepared.take() {
            self.state.release_prepared(prepared);
        }
    }
}

fn prepare_payload(intent: StructuralMutationIntent) -> PreparedPayload {
    match intent {
        StructuralMutationIntent::AppendProofOccurrence => PreparedPayload::AppendProofOccurrence,
        StructuralMutationIntent::AdmitProjectionSupport => PreparedPayload::AdmitProjectionSupport,
        StructuralMutationIntent::AdmitProjectionFormulaClause => {
            PreparedPayload::AdmitProjectionFormulaClause
        }
        StructuralMutationIntent::AdmitProjectionIndex => PreparedPayload::AdmitProjectionIndex,
        StructuralMutationIntent::AdmitOriginalClaim => PreparedPayload::AdmitOriginalClaim,
        StructuralMutationIntent::DecideDerivedClaim => PreparedPayload::DecideDerivedClaim,
        StructuralMutationIntent::MoveUpperClaim => PreparedPayload::MoveUpperClaim,
        StructuralMutationIntent::BindReductionClaim => PreparedPayload::BindReductionClaim,
        StructuralMutationIntent::TransitionLiveCoverage => PreparedPayload::TransitionLiveCoverage,
        StructuralMutationIntent::AdmitReplayRelation => PreparedPayload::AdmitReplayRelation,
        StructuralMutationIntent::AdmitReplayQualifiedParents => {
            PreparedPayload::AdmitReplayQualifiedParents
        }
        StructuralMutationIntent::AdmitQualifiedParents => PreparedPayload::AdmitQualifiedParents,
        StructuralMutationIntent::AdmitBound => PreparedPayload::AdmitBound,
        StructuralMutationIntent::PromoteBound => PreparedPayload::PromoteBound,
        StructuralMutationIntent::TombstoneBound => PreparedPayload::TombstoneBound,
        StructuralMutationIntent::ExtendBoundDerivation => PreparedPayload::ExtendBoundDerivation,
        StructuralMutationIntent::AdmitConstraint => PreparedPayload::AdmitConstraint,
        StructuralMutationIntent::ExtendConstraintProof => PreparedPayload::ExtendConstraintProof,
        StructuralMutationIntent::UpdateReplayCompleteness => {
            PreparedPayload::UpdateReplayCompleteness
        }
        StructuralMutationIntent::AdmitReplayDrop => PreparedPayload::AdmitReplayDrop,
        StructuralMutationIntent::AdmitRowResidual => PreparedPayload::AdmitRowResidual,
        StructuralMutationIntent::AdmitRowDerivation => PreparedPayload::AdmitRowDerivation,
        StructuralMutationIntent::AdmitRowReduction => PreparedPayload::AdmitRowReduction,
        StructuralMutationIntent::AdvanceRowReductionMatched => {
            PreparedPayload::AdvanceRowReductionMatched
        }
        StructuralMutationIntent::AdvanceRowReductionUnmatched => {
            PreparedPayload::AdvanceRowReductionUnmatched
        }
        StructuralMutationIntent::UpdateRowReductionOwner => {
            PreparedPayload::UpdateRowReductionOwner
        }
        StructuralMutationIntent::AdmitLowerFilter => PreparedPayload::AdmitLowerFilter,
        StructuralMutationIntent::AdmitStructuralIdentity => {
            PreparedPayload::AdmitStructuralIdentity
        }
        StructuralMutationIntent::AdmitSchemeInstantiation => {
            PreparedPayload::AdmitSchemeInstantiation
        }
    }
}

fn try_prove_unchanged(payload: &PreparedPayload) -> Option<ExplicitNoOpProof> {
    match payload {
        PreparedPayload::AppendProofOccurrence => None,
        PreparedPayload::AdmitProjectionSupport => None,
        PreparedPayload::AdmitProjectionFormulaClause => None,
        PreparedPayload::AdmitProjectionIndex => None,
        PreparedPayload::AdmitOriginalClaim => None,
        PreparedPayload::DecideDerivedClaim => None,
        PreparedPayload::MoveUpperClaim => None,
        PreparedPayload::BindReductionClaim => None,
        PreparedPayload::TransitionLiveCoverage => None,
        PreparedPayload::AdmitReplayRelation => None,
        PreparedPayload::AdmitReplayQualifiedParents => None,
        PreparedPayload::AdmitQualifiedParents => None,
        PreparedPayload::AdmitBound => None,
        PreparedPayload::PromoteBound => None,
        PreparedPayload::TombstoneBound => None,
        PreparedPayload::ExtendBoundDerivation => None,
        PreparedPayload::AdmitConstraint => None,
        PreparedPayload::ExtendConstraintProof => None,
        PreparedPayload::UpdateReplayCompleteness => None,
        PreparedPayload::AdmitReplayDrop => None,
        PreparedPayload::AdmitRowResidual => None,
        PreparedPayload::AdmitRowDerivation => None,
        PreparedPayload::AdmitRowReduction => None,
        PreparedPayload::AdvanceRowReductionMatched => None,
        PreparedPayload::AdvanceRowReductionUnmatched => None,
        PreparedPayload::UpdateRowReductionOwner => None,
        PreparedPayload::AdmitLowerFilter => None,
        PreparedPayload::AdmitStructuralIdentity => None,
        PreparedPayload::AdmitSchemeInstantiation => None,
    }
}

type ShadowPublisher =
    fn(&mut StructuralData, VerifiedReservedOperation, StructuralResourceDomainKey);

struct VerifiedPublication {
    domain: StructuralResourceDomainKey,
    reserved: VerifiedReservedOperation,
    publisher: ShadowPublisher,
}

enum VerifiedPublicationPlan {
    Single {
        receipt: CommittedStructuralMutation,
        publication: VerifiedPublication,
    },
    ProjectionFormula {
        formula: VerifiedPublication,
        lower_index: VerifiedPublication,
    },
}

fn verify_changed_publication(
    payload: &PreparedPayload,
    ticket: ReservationTicketId,
    operations: &mut Vec<ReservedOperation>,
) -> Result<VerifiedPublicationPlan, ProofAccessError> {
    macro_rules! publish {
        ($family:path, $port:ident, $receipt:ident) => {{
            let domain = primary_domain(payload);
            let reserved = take_verified_operation(operations, ticket, domain)?;
            VerifiedPublicationPlan::Single {
                receipt: CommittedStructuralMutation::$receipt,
                publication: VerifiedPublication {
                    domain,
                    reserved,
                    publisher: |data, reserved, expected| {
                        $family($port::new(data, reserved, expected));
                    },
                },
            }
        }};
    }
    let plan = match payload {
        PreparedPayload::AppendProofOccurrence => publish!(
            families::proof::publish_shadow,
            ProofPublishPort,
            AppendProofOccurrence
        ),
        PreparedPayload::AdmitProjectionSupport => publish!(
            families::proof::publish_shadow,
            ProofPublishPort,
            AdmitProjectionSupport
        ),
        PreparedPayload::AdmitProjectionFormulaClause => {
            let formula_domain = StructuralResourceDomainKey::ProjectionFormulaByRecordMap;
            let lower_domain = StructuralResourceDomainKey::ProjectionLowerByConstraint;
            let formula = take_verified_operation(operations, ticket, formula_domain)?;
            let lower_index = take_verified_operation(operations, ticket, lower_domain)?;
            VerifiedPublicationPlan::ProjectionFormula {
                formula: VerifiedPublication {
                    domain: formula_domain,
                    reserved: formula,
                    publisher: |data, reserved, expected| {
                        families::proof::publish_shadow(ProofPublishPort::new(
                            data, reserved, expected,
                        ));
                    },
                },
                lower_index: VerifiedPublication {
                    domain: lower_domain,
                    reserved: lower_index,
                    publisher: |data, reserved, expected| {
                        families::proof::publish_shadow(ProofPublishPort::new(
                            data, reserved, expected,
                        ));
                    },
                },
            }
        }
        PreparedPayload::AdmitProjectionIndex => publish!(
            families::proof::publish_shadow,
            ProofPublishPort,
            AdmitProjectionIndex
        ),
        PreparedPayload::AdmitOriginalClaim => publish!(
            families::proof::publish_shadow,
            ProofPublishPort,
            AdmitOriginalClaim
        ),
        PreparedPayload::DecideDerivedClaim => publish!(
            families::proof::publish_shadow,
            ProofPublishPort,
            DecideDerivedClaim
        ),
        PreparedPayload::MoveUpperClaim => publish!(
            families::proof::publish_shadow,
            ProofPublishPort,
            MoveUpperClaim
        ),
        PreparedPayload::BindReductionClaim => publish!(
            families::proof::publish_shadow,
            ProofPublishPort,
            BindReductionClaim
        ),
        PreparedPayload::TransitionLiveCoverage => publish!(
            families::proof::publish_shadow,
            ProofPublishPort,
            TransitionLiveCoverage
        ),
        PreparedPayload::AdmitReplayRelation => publish!(
            families::proof::publish_shadow,
            ProofPublishPort,
            AdmitReplayRelation
        ),
        PreparedPayload::AdmitReplayQualifiedParents => publish!(
            families::proof::publish_shadow,
            ProofPublishPort,
            AdmitReplayQualifiedParents
        ),
        PreparedPayload::AdmitQualifiedParents => publish!(
            families::proof::publish_shadow,
            ProofPublishPort,
            AdmitQualifiedParents
        ),
        PreparedPayload::AdmitBound => publish!(
            families::bounds::publish_shadow,
            BoundsPublishPort,
            AdmitBound
        ),
        PreparedPayload::PromoteBound => publish!(
            families::bounds::publish_shadow,
            BoundsPublishPort,
            PromoteBound
        ),
        PreparedPayload::TombstoneBound => publish!(
            families::bounds::publish_shadow,
            BoundsPublishPort,
            TombstoneBound
        ),
        PreparedPayload::ExtendBoundDerivation => publish!(
            families::bounds::publish_shadow,
            BoundsPublishPort,
            ExtendBoundDerivation
        ),
        PreparedPayload::AdmitConstraint => publish!(
            families::constraints::publish_shadow,
            ConstraintsPublishPort,
            AdmitConstraint
        ),
        PreparedPayload::ExtendConstraintProof => publish!(
            families::constraints::publish_shadow,
            ConstraintsPublishPort,
            ExtendConstraintProof
        ),
        PreparedPayload::UpdateReplayCompleteness => publish!(
            families::constraints::publish_shadow,
            ConstraintsPublishPort,
            UpdateReplayCompleteness
        ),
        PreparedPayload::AdmitReplayDrop => publish!(
            families::constraints::publish_shadow,
            ConstraintsPublishPort,
            AdmitReplayDrop
        ),
        PreparedPayload::AdmitRowResidual => publish!(
            families::rows::publish_shadow,
            RowsPublishPort,
            AdmitRowResidual
        ),
        PreparedPayload::AdmitRowDerivation => publish!(
            families::rows::publish_shadow,
            RowsPublishPort,
            AdmitRowDerivation
        ),
        PreparedPayload::AdmitRowReduction => publish!(
            families::rows::publish_shadow,
            RowsPublishPort,
            AdmitRowReduction
        ),
        PreparedPayload::AdvanceRowReductionMatched => publish!(
            families::rows::publish_shadow,
            RowsPublishPort,
            AdvanceRowReductionMatched
        ),
        PreparedPayload::AdvanceRowReductionUnmatched => publish!(
            families::rows::publish_shadow,
            RowsPublishPort,
            AdvanceRowReductionUnmatched
        ),
        PreparedPayload::UpdateRowReductionOwner => publish!(
            families::rows::publish_shadow,
            RowsPublishPort,
            UpdateRowReductionOwner
        ),
        PreparedPayload::AdmitLowerFilter => publish!(
            families::rows::publish_shadow,
            RowsPublishPort,
            AdmitLowerFilter
        ),
        PreparedPayload::AdmitStructuralIdentity => publish!(
            families::identities::publish_shadow,
            IdentitiesPublishPort,
            AdmitStructuralIdentity
        ),
        PreparedPayload::AdmitSchemeInstantiation => publish!(
            families::identities::publish_shadow,
            IdentitiesPublishPort,
            AdmitSchemeInstantiation
        ),
    };
    if !operations.is_empty() {
        return Err(ProofAccessError::InvalidReservedOperation);
    }
    Ok(plan)
}

fn publish_verified(publication: VerifiedPublication, data: &mut StructuralData) {
    (publication.publisher)(data, publication.reserved, publication.domain);
}

fn publish_verified_plan(
    plan: VerifiedPublicationPlan,
    data: &mut StructuralData,
) -> CommittedStructuralMutation {
    match plan {
        VerifiedPublicationPlan::Single {
            receipt,
            publication,
        } => {
            publish_verified(publication, data);
            receipt
        }
        VerifiedPublicationPlan::ProjectionFormula {
            formula,
            lower_index,
        } => {
            // Both exact domains and absence of residual operations were proved before this first
            // write. Publication contains no fallible reservation checks.
            publish_verified(formula, data);
            publish_verified(lower_index, data);
            CommittedStructuralMutation::AdmitProjectionFormulaClause
        }
    }
}

fn take_verified_operation(
    operations: &mut Vec<ReservedOperation>,
    ticket: ReservationTicketId,
    expected: StructuralResourceDomainKey,
) -> Result<VerifiedReservedOperation, ProofAccessError> {
    let position = operations
        .iter()
        .position(|operation| operation.domain() == expected)
        .ok_or(ProofAccessError::InvalidReservedOperation)?;
    operations
        .swap_remove(position)
        .verify(ticket, expected)
        .map_err(|_| ProofAccessError::InvalidReservedOperation)
}

fn primary_domain(payload: &PreparedPayload) -> StructuralResourceDomainKey {
    use StructuralResourceDomainKey as D;
    match payload {
        PreparedPayload::AppendProofOccurrence => D::ProofOccurrences,
        PreparedPayload::AdmitProjectionSupport => D::ProjectionSupportsByRecord,
        PreparedPayload::AdmitProjectionFormulaClause => D::ProjectionFormulaByRecordMap,
        PreparedPayload::AdmitProjectionIndex => D::DependentRecordsByPremiseMap,
        PreparedPayload::AdmitOriginalClaim
        | PreparedPayload::DecideDerivedClaim
        | PreparedPayload::MoveUpperClaim => D::UpperClaimArena,
        PreparedPayload::BindReductionClaim => D::ReductionClaimIndex,
        PreparedPayload::TransitionLiveCoverage => D::LiveCoverageFlat,
        PreparedPayload::AdmitReplayRelation => D::ReplayFiniteMapArena,
        PreparedPayload::AdmitReplayQualifiedParents | PreparedPayload::AdmitQualifiedParents => {
            D::ReplayQualifiedArmResultMap
        }
        PreparedPayload::AdmitBound
        | PreparedPayload::PromoteBound
        | PreparedPayload::TombstoneBound
        | PreparedPayload::ExtendBoundDerivation => D::BoundRecords,
        PreparedPayload::AdmitConstraint
        | PreparedPayload::ExtendConstraintProof
        | PreparedPayload::UpdateReplayCompleteness => D::ConstraintRecords,
        PreparedPayload::AdmitReplayDrop => D::ReplayDropRecords,
        PreparedPayload::AdmitRowResidual => D::RowResidualRecords,
        PreparedPayload::AdmitRowDerivation => D::RowDerivationArena,
        PreparedPayload::AdmitRowReduction
        | PreparedPayload::AdvanceRowReductionMatched
        | PreparedPayload::AdvanceRowReductionUnmatched => D::RowReductionRecords,
        PreparedPayload::UpdateRowReductionOwner => D::RowReductionOwnerMap,
        PreparedPayload::AdmitLowerFilter => D::LowerFilterRecords,
        PreparedPayload::AdmitStructuralIdentity => {
            D::IdentityRecords(reservation::IdentityFamily::Origin)
        }
        PreparedPayload::AdmitSchemeInstantiation => {
            D::IdentityRecords(reservation::IdentityFamily::SchemeInstantiation)
        }
    }
}

fn reservation_plan(payload: &PreparedPayload) -> Result<Vec<ReservationClaim>, ProofAccessError> {
    let count = usize::from(matches!(
        payload,
        PreparedPayload::AdmitProjectionFormulaClause
    )) + 1;
    let mut claims = Vec::new();
    claims
        .try_reserve(count)
        .map_err(|_| ProofAccessError::StructuralResourceExhausted)?;
    claims.push(ReservationClaim {
        domain: primary_domain(payload),
        units: 1,
    });
    if matches!(payload, PreparedPayload::AdmitProjectionFormulaClause) {
        claims.push(ReservationClaim {
            domain: StructuralResourceDomainKey::ProjectionLowerByConstraint,
            units: 1,
        });
    }
    Ok(claims)
}
