//! Sealed shadow gateway. No production proof read or write is routed here in SS1.

mod reservation;
mod storage;
mod unchanged;
mod write_ports;

use super::access::{ActiveProofAttempt, ProofAccessError};
use super::commands::{CommittedStructuralMutation, StructuralMutationIntent};
use super::families;
use reservation::{
    BoundRecordsDomain, ConstraintRecordsDomain, DependentRecordsByPremiseDomain,
    LiveCoverageFlatDomain, LowerFilterRecordsDomain, OriginIdentityRecordsDomain,
    ProjectionFormulaByRecordDomain, ProjectionLowerByConstraintDomain,
    ProjectionSupportsByRecordDomain, ProofOccurrencesDomain, ReductionClaimIndexDomain,
    ReplayDropRecordsDomain, ReplayFiniteMapArenaDomain, ReplayQualifiedArmResultDomain,
    ReservationClaim, ReservationTicketId, ReservedOperation, ResourceDomainMarker,
    RowDerivationArenaDomain, RowReductionOwnerDomain, RowReductionRecordsDomain,
    RowResidualRecordsDomain, SchemeInstantiationIdentityRecordsDomain,
    StructuralReservationLedger, StructuralReservationTicket, StructuralResourceDomainKey,
    UpperClaimArenaDomain, VerifiedReservedOperation,
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

enum VerifiedPublicationPlan {
    AppendProofOccurrence(VerifiedReservedOperation<ProofOccurrencesDomain>),
    AdmitProjectionSupport(VerifiedReservedOperation<ProjectionSupportsByRecordDomain>),
    AdmitProjectionFormulaClause {
        formula: VerifiedReservedOperation<ProjectionFormulaByRecordDomain>,
        lower_index: VerifiedReservedOperation<ProjectionLowerByConstraintDomain>,
    },
    AdmitProjectionIndex(VerifiedReservedOperation<DependentRecordsByPremiseDomain>),
    AdmitOriginalClaim(VerifiedReservedOperation<UpperClaimArenaDomain>),
    DecideDerivedClaim(VerifiedReservedOperation<UpperClaimArenaDomain>),
    MoveUpperClaim(VerifiedReservedOperation<UpperClaimArenaDomain>),
    BindReductionClaim(VerifiedReservedOperation<ReductionClaimIndexDomain>),
    TransitionLiveCoverage(VerifiedReservedOperation<LiveCoverageFlatDomain>),
    AdmitReplayRelation(VerifiedReservedOperation<ReplayFiniteMapArenaDomain>),
    AdmitReplayQualifiedParents(VerifiedReservedOperation<ReplayQualifiedArmResultDomain>),
    AdmitQualifiedParents(VerifiedReservedOperation<ReplayQualifiedArmResultDomain>),
    AdmitBound(VerifiedReservedOperation<BoundRecordsDomain>),
    PromoteBound(VerifiedReservedOperation<BoundRecordsDomain>),
    TombstoneBound(VerifiedReservedOperation<BoundRecordsDomain>),
    ExtendBoundDerivation(VerifiedReservedOperation<BoundRecordsDomain>),
    AdmitConstraint(VerifiedReservedOperation<ConstraintRecordsDomain>),
    ExtendConstraintProof(VerifiedReservedOperation<ConstraintRecordsDomain>),
    UpdateReplayCompleteness(VerifiedReservedOperation<ConstraintRecordsDomain>),
    AdmitReplayDrop(VerifiedReservedOperation<ReplayDropRecordsDomain>),
    AdmitRowResidual(VerifiedReservedOperation<RowResidualRecordsDomain>),
    AdmitRowDerivation(VerifiedReservedOperation<RowDerivationArenaDomain>),
    AdmitRowReduction(VerifiedReservedOperation<RowReductionRecordsDomain>),
    AdvanceRowReductionMatched(VerifiedReservedOperation<RowReductionRecordsDomain>),
    AdvanceRowReductionUnmatched(VerifiedReservedOperation<RowReductionRecordsDomain>),
    UpdateRowReductionOwner(VerifiedReservedOperation<RowReductionOwnerDomain>),
    AdmitLowerFilter(VerifiedReservedOperation<LowerFilterRecordsDomain>),
    AdmitStructuralIdentity(VerifiedReservedOperation<OriginIdentityRecordsDomain>),
    AdmitSchemeInstantiation(VerifiedReservedOperation<SchemeInstantiationIdentityRecordsDomain>),
}

fn verify_changed_publication(
    payload: &PreparedPayload,
    ticket: ReservationTicketId,
    operations: &mut Vec<ReservedOperation>,
) -> Result<VerifiedPublicationPlan, ProofAccessError> {
    macro_rules! verified {
        ($domain:ty) => {
            take_verified_operation::<$domain>(operations, ticket, ())?
        };
    }
    let plan = match payload {
        PreparedPayload::AppendProofOccurrence => {
            VerifiedPublicationPlan::AppendProofOccurrence(verified!(ProofOccurrencesDomain))
        }
        PreparedPayload::AdmitProjectionSupport => VerifiedPublicationPlan::AdmitProjectionSupport(
            verified!(ProjectionSupportsByRecordDomain),
        ),
        PreparedPayload::AdmitProjectionFormulaClause => {
            VerifiedPublicationPlan::AdmitProjectionFormulaClause {
                formula: verified!(ProjectionFormulaByRecordDomain),
                lower_index: verified!(ProjectionLowerByConstraintDomain),
            }
        }
        PreparedPayload::AdmitProjectionIndex => VerifiedPublicationPlan::AdmitProjectionIndex(
            verified!(DependentRecordsByPremiseDomain),
        ),
        PreparedPayload::AdmitOriginalClaim => {
            VerifiedPublicationPlan::AdmitOriginalClaim(verified!(UpperClaimArenaDomain))
        }
        PreparedPayload::DecideDerivedClaim => {
            VerifiedPublicationPlan::DecideDerivedClaim(verified!(UpperClaimArenaDomain))
        }
        PreparedPayload::MoveUpperClaim => {
            VerifiedPublicationPlan::MoveUpperClaim(verified!(UpperClaimArenaDomain))
        }
        PreparedPayload::BindReductionClaim => {
            VerifiedPublicationPlan::BindReductionClaim(verified!(ReductionClaimIndexDomain))
        }
        PreparedPayload::TransitionLiveCoverage => {
            VerifiedPublicationPlan::TransitionLiveCoverage(verified!(LiveCoverageFlatDomain))
        }
        PreparedPayload::AdmitReplayRelation => {
            VerifiedPublicationPlan::AdmitReplayRelation(verified!(ReplayFiniteMapArenaDomain))
        }
        PreparedPayload::AdmitReplayQualifiedParents => {
            VerifiedPublicationPlan::AdmitReplayQualifiedParents(verified!(
                ReplayQualifiedArmResultDomain
            ))
        }
        PreparedPayload::AdmitQualifiedParents => VerifiedPublicationPlan::AdmitQualifiedParents(
            verified!(ReplayQualifiedArmResultDomain),
        ),
        PreparedPayload::AdmitBound => {
            VerifiedPublicationPlan::AdmitBound(verified!(BoundRecordsDomain))
        }
        PreparedPayload::PromoteBound => {
            VerifiedPublicationPlan::PromoteBound(verified!(BoundRecordsDomain))
        }
        PreparedPayload::TombstoneBound => {
            VerifiedPublicationPlan::TombstoneBound(verified!(BoundRecordsDomain))
        }
        PreparedPayload::ExtendBoundDerivation => {
            VerifiedPublicationPlan::ExtendBoundDerivation(verified!(BoundRecordsDomain))
        }
        PreparedPayload::AdmitConstraint => {
            VerifiedPublicationPlan::AdmitConstraint(verified!(ConstraintRecordsDomain))
        }
        PreparedPayload::ExtendConstraintProof => {
            VerifiedPublicationPlan::ExtendConstraintProof(verified!(ConstraintRecordsDomain))
        }
        PreparedPayload::UpdateReplayCompleteness => {
            VerifiedPublicationPlan::UpdateReplayCompleteness(verified!(ConstraintRecordsDomain))
        }
        PreparedPayload::AdmitReplayDrop => {
            VerifiedPublicationPlan::AdmitReplayDrop(verified!(ReplayDropRecordsDomain))
        }
        PreparedPayload::AdmitRowResidual => {
            VerifiedPublicationPlan::AdmitRowResidual(verified!(RowResidualRecordsDomain))
        }
        PreparedPayload::AdmitRowDerivation => {
            VerifiedPublicationPlan::AdmitRowDerivation(verified!(RowDerivationArenaDomain))
        }
        PreparedPayload::AdmitRowReduction => {
            VerifiedPublicationPlan::AdmitRowReduction(verified!(RowReductionRecordsDomain))
        }
        PreparedPayload::AdvanceRowReductionMatched => {
            VerifiedPublicationPlan::AdvanceRowReductionMatched(verified!(
                RowReductionRecordsDomain
            ))
        }
        PreparedPayload::AdvanceRowReductionUnmatched => {
            VerifiedPublicationPlan::AdvanceRowReductionUnmatched(verified!(
                RowReductionRecordsDomain
            ))
        }
        PreparedPayload::UpdateRowReductionOwner => {
            VerifiedPublicationPlan::UpdateRowReductionOwner(verified!(RowReductionOwnerDomain))
        }
        PreparedPayload::AdmitLowerFilter => {
            VerifiedPublicationPlan::AdmitLowerFilter(verified!(LowerFilterRecordsDomain))
        }
        PreparedPayload::AdmitStructuralIdentity => {
            VerifiedPublicationPlan::AdmitStructuralIdentity(verified!(OriginIdentityRecordsDomain))
        }
        PreparedPayload::AdmitSchemeInstantiation => {
            VerifiedPublicationPlan::AdmitSchemeInstantiation(verified!(
                SchemeInstantiationIdentityRecordsDomain
            ))
        }
    };
    if !operations.is_empty() {
        return Err(ProofAccessError::InvalidReservedOperation);
    }
    Ok(plan)
}

fn publish_verified_plan(
    plan: VerifiedPublicationPlan,
    data: &mut StructuralData,
) -> CommittedStructuralMutation {
    match plan {
        VerifiedPublicationPlan::AppendProofOccurrence(reserved) => {
            families::proof::publish_shadow(ProofPublishPort::proof_occurrences(data, reserved));
            CommittedStructuralMutation::AppendProofOccurrence
        }
        VerifiedPublicationPlan::AdmitProjectionSupport(reserved) => {
            families::proof::publish_shadow(ProofPublishPort::projection_support(data, reserved));
            CommittedStructuralMutation::AdmitProjectionSupport
        }
        VerifiedPublicationPlan::AdmitProjectionFormulaClause {
            formula,
            lower_index,
        } => {
            families::proof::publish_shadow(ProofPublishPort::projection_formula(data, formula));
            families::proof::publish_shadow(ProofPublishPort::projection_lower(data, lower_index));
            CommittedStructuralMutation::AdmitProjectionFormulaClause
        }
        VerifiedPublicationPlan::AdmitProjectionIndex(reserved) => {
            families::proof::publish_shadow(ProofPublishPort::dependent_records(data, reserved));
            CommittedStructuralMutation::AdmitProjectionIndex
        }
        VerifiedPublicationPlan::AdmitOriginalClaim(reserved) => {
            families::proof::publish_shadow(ProofPublishPort::upper_claim(data, reserved));
            CommittedStructuralMutation::AdmitOriginalClaim
        }
        VerifiedPublicationPlan::DecideDerivedClaim(reserved) => {
            families::proof::publish_shadow(ProofPublishPort::upper_claim(data, reserved));
            CommittedStructuralMutation::DecideDerivedClaim
        }
        VerifiedPublicationPlan::MoveUpperClaim(reserved) => {
            families::proof::publish_shadow(ProofPublishPort::upper_claim(data, reserved));
            CommittedStructuralMutation::MoveUpperClaim
        }
        VerifiedPublicationPlan::BindReductionClaim(reserved) => {
            families::proof::publish_shadow(ProofPublishPort::reduction_claim(data, reserved));
            CommittedStructuralMutation::BindReductionClaim
        }
        VerifiedPublicationPlan::TransitionLiveCoverage(reserved) => {
            families::proof::publish_shadow(ProofPublishPort::live_coverage(data, reserved));
            CommittedStructuralMutation::TransitionLiveCoverage
        }
        VerifiedPublicationPlan::AdmitReplayRelation(reserved) => {
            families::proof::publish_shadow(ProofPublishPort::replay_finite_map(data, reserved));
            CommittedStructuralMutation::AdmitReplayRelation
        }
        VerifiedPublicationPlan::AdmitReplayQualifiedParents(reserved) => {
            families::proof::publish_shadow(ProofPublishPort::replay_qualified(data, reserved));
            CommittedStructuralMutation::AdmitReplayQualifiedParents
        }
        VerifiedPublicationPlan::AdmitQualifiedParents(reserved) => {
            families::proof::publish_shadow(ProofPublishPort::replay_qualified(data, reserved));
            CommittedStructuralMutation::AdmitQualifiedParents
        }
        VerifiedPublicationPlan::AdmitBound(reserved) => {
            families::bounds::publish_shadow(BoundsPublishPort::bound_records(data, reserved));
            CommittedStructuralMutation::AdmitBound
        }
        VerifiedPublicationPlan::PromoteBound(reserved) => {
            families::bounds::publish_shadow(BoundsPublishPort::bound_records(data, reserved));
            CommittedStructuralMutation::PromoteBound
        }
        VerifiedPublicationPlan::TombstoneBound(reserved) => {
            families::bounds::publish_shadow(BoundsPublishPort::bound_records(data, reserved));
            CommittedStructuralMutation::TombstoneBound
        }
        VerifiedPublicationPlan::ExtendBoundDerivation(reserved) => {
            families::bounds::publish_shadow(BoundsPublishPort::bound_records(data, reserved));
            CommittedStructuralMutation::ExtendBoundDerivation
        }
        VerifiedPublicationPlan::AdmitConstraint(reserved) => {
            families::constraints::publish_shadow(ConstraintsPublishPort::constraint_records(
                data, reserved,
            ));
            CommittedStructuralMutation::AdmitConstraint
        }
        VerifiedPublicationPlan::ExtendConstraintProof(reserved) => {
            families::constraints::publish_shadow(ConstraintsPublishPort::constraint_records(
                data, reserved,
            ));
            CommittedStructuralMutation::ExtendConstraintProof
        }
        VerifiedPublicationPlan::UpdateReplayCompleteness(reserved) => {
            families::constraints::publish_shadow(ConstraintsPublishPort::constraint_records(
                data, reserved,
            ));
            CommittedStructuralMutation::UpdateReplayCompleteness
        }
        VerifiedPublicationPlan::AdmitReplayDrop(reserved) => {
            families::constraints::publish_shadow(ConstraintsPublishPort::replay_drop(
                data, reserved,
            ));
            CommittedStructuralMutation::AdmitReplayDrop
        }
        VerifiedPublicationPlan::AdmitRowResidual(reserved) => {
            families::rows::publish_shadow(RowsPublishPort::row_residual(data, reserved));
            CommittedStructuralMutation::AdmitRowResidual
        }
        VerifiedPublicationPlan::AdmitRowDerivation(reserved) => {
            families::rows::publish_shadow(RowsPublishPort::row_derivation(data, reserved));
            CommittedStructuralMutation::AdmitRowDerivation
        }
        VerifiedPublicationPlan::AdmitRowReduction(reserved) => {
            families::rows::publish_shadow(RowsPublishPort::row_reduction(data, reserved));
            CommittedStructuralMutation::AdmitRowReduction
        }
        VerifiedPublicationPlan::AdvanceRowReductionMatched(reserved) => {
            families::rows::publish_shadow(RowsPublishPort::row_reduction(data, reserved));
            CommittedStructuralMutation::AdvanceRowReductionMatched
        }
        VerifiedPublicationPlan::AdvanceRowReductionUnmatched(reserved) => {
            families::rows::publish_shadow(RowsPublishPort::row_reduction(data, reserved));
            CommittedStructuralMutation::AdvanceRowReductionUnmatched
        }
        VerifiedPublicationPlan::UpdateRowReductionOwner(reserved) => {
            families::rows::publish_shadow(RowsPublishPort::row_owner(data, reserved));
            CommittedStructuralMutation::UpdateRowReductionOwner
        }
        VerifiedPublicationPlan::AdmitLowerFilter(reserved) => {
            families::rows::publish_shadow(RowsPublishPort::lower_filter(data, reserved));
            CommittedStructuralMutation::AdmitLowerFilter
        }
        VerifiedPublicationPlan::AdmitStructuralIdentity(reserved) => {
            families::identities::publish_shadow(IdentitiesPublishPort::origin(data, reserved));
            CommittedStructuralMutation::AdmitStructuralIdentity
        }
        VerifiedPublicationPlan::AdmitSchemeInstantiation(reserved) => {
            families::identities::publish_shadow(IdentitiesPublishPort::scheme_instantiation(
                data, reserved,
            ));
            CommittedStructuralMutation::AdmitSchemeInstantiation
        }
    }
}

fn take_verified_operation<D: ResourceDomainMarker>(
    operations: &mut Vec<ReservedOperation>,
    ticket: ReservationTicketId,
    target: D::Target,
) -> Result<VerifiedReservedOperation<D>, ProofAccessError> {
    let expected = D::key(target);
    let position = operations
        .iter()
        .position(|operation| operation.domain() == expected)
        .ok_or(ProofAccessError::InvalidReservedOperation)?;
    operations
        .swap_remove(position)
        .verify::<D>(ticket, target)
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
