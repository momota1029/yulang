//! Attempt-local shadow capacity ledger.

use std::collections::TryReserveError;
use std::marker::PhantomData;
use std::num::NonZeroU64;

use rustc_hash::FxHashMap;

use crate::constraints::{
    BoundRecordId, ConstraintRecordId, ProofPremise, TypeVar, UnweightedRowReductionRecordId,
    UpperReplayClaimId,
};

#[derive(Debug)]
pub(super) enum ReservationError {
    Allocation,
    ArithmeticOverflow,
    DomainMismatch,
    TicketIdExhausted,
}

impl From<TryReserveError> for ReservationError {
    fn from(_: TryReserveError) -> Self {
        Self::Allocation
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::constraints::structural_kernel) enum IdentityFamily {
    Origin,
    SourceBoundary,
    GeneralizedScheme,
    GeneralizedWitness,
    SchemeInstantiation,
}

/// SS0's closed inventory of persistent containers which may consume capacity at commit time.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    ProofOccurrences,
    DependencyOccurrenceResultMap,
    DependencyOccurrencesForResult(ConstraintRecordId),
    ProjectionCarrierOccurrenceIndex,
    RowDerivationOccurrenceIndex,
    ReplayFiniteMapArena,
    ReplayFiniteMapIndex,
    ReplayResultMap,
    ReplayOccurrencesForResult(ConstraintRecordId),
    ReplayParentChunkNodes,
    ReplayParentChunkEntries(u32),
    ReplayQualifiedArmResultMap,
    ReplayQualifiedArmNodes(ConstraintRecordId),
    CanonicalQualifiedRootNodes(ConstraintRecordId),
    NonReplayQualifiedParentArena,
    NonReplayQualifiedParentResultMap,
    NonReplayQualifiedParentsForResult(ConstraintRecordId),
    ReplayAdmissions,
    FirstReplayWitnesses,
    UpperClaimArena,
    UpperClaimIndex,
    OriginalClaimIndex,
    DerivedClaimIndex,
    RootClaimProducerIndex,
    ReductionClaimIndex,
    ClaimsByUpperRecordMap,
    ClaimsInUpperRecord(BoundRecordId),
    LiveCoverageFlat,
    LiveStatesByCoverageRootMap,
    LiveStatesInCoverageRoot(UpperReplayClaimId),
    ProjectionSupportsByRecord,
    ClaimedParentsByLowerRecord,
    ProjectionRootMemberships,
    ProjectionLowerRecordsByRootMap,
    ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    ProjectionFormulaByRecordMap,
    ProjectionFormulaEntries(BoundRecordId),
    ProjectionFormulaEntryIndex(BoundRecordId),
    ProjectionSupportGroups(BoundRecordId),
    ProjectionSupportGroupIndex(BoundRecordId),
    ProjectionExactLinks(BoundRecordId),
    ProjectionCanonicalRuns(BoundRecordId),
    ProjectionCanonicalRunNodes(BoundRecordId),
    ProjectionCanonicalRunEntries(BoundRecordId),
    ProjectionValidationActions(BoundRecordId),
    ProjectionValidationMembership(BoundRecordId),
    ProjectionNormalizedSupportKeys(BoundRecordId),
    ProjectionAttributedRoots(BoundRecordId),
    ProjectionLowerByConstraint,
    ProjectionLowerByReplay,
    DependentRecordsByPremiseMap,
    DependentsForPremise(ProofPremise),
    BoundVarSlots,
    BoundLowerEntries(TypeVar),
    BoundUpperEntries(TypeVar),
    BoundEvidenceLowerEntries(TypeVar),
    BoundEvidenceUpperEntries(TypeVar),
    BoundCanonicalIndex,
    BoundRecords,
    BoundDerivations(BoundRecordId),
    ConstraintCanonicalIndex,
    ConstraintRecords,
    ConstraintRootOrigins(ConstraintRecordId),
    ConstraintStructuralDerivations(ConstraintRecordId),
    ConstraintRowDerivations(ConstraintRecordId),
    ConstraintReplayDerivations(ConstraintRecordId),
    ConstraintSchemeDerivations(ConstraintRecordId),
    ConstraintSchemeRoutes(ConstraintRecordId),
    ReplayDropRecords,
    ReplayDropIndex,
    RowResidualMap,
    RowResidualRecordIndex,
    RowResidualRecords,
    RowResidualDerivations(u32),
    RowDerivationArena,
    RowDerivationIndex,
    RowReductionBySourceMap,
    RowReductionsForSource(TypeVar),
    RowReductionOwnerMap,
    RowReductionOwnersForUpper(BoundRecordId),
    RowReductionRecords,
    RowProcessedLowers(UnweightedRowReductionRecordId),
    LowerFilterMap,
    LowerFilterRecordIndex,
    LowerFilterRecords,
    LowerFilterDerivations(u32),
    IdentityRecords(IdentityFamily),
}

mod domain_sealed {
    pub trait Sealed {}
}

/// A typed view of one runtime reservation-domain kind.
///
/// SS1 declares only the kinds used by its 29-command shadow vocabulary. SS2+ adds markers as
/// additional parameterized storage domains move behind the gateway; their runtime key remains in
/// `StructuralResourceDomainKey`, while `Target` carries values such as a record/root ID.
pub(super) trait ResourceDomainMarker: domain_sealed::Sealed {
    type Target: Copy;

    fn key(target: Self::Target) -> StructuralResourceDomainKey;
}

macro_rules! unit_domain_markers {
    ($($marker:ident => $key:expr),+ $(,)?) => {
        $(
            #[derive(Debug)]
            pub(super) struct $marker;

            impl domain_sealed::Sealed for $marker {}

            impl ResourceDomainMarker for $marker {
                type Target = ();

                fn key((): Self::Target) -> StructuralResourceDomainKey {
                    $key
                }
            }
        )+
    };
}

unit_domain_markers! {
    ProofOccurrencesDomain => StructuralResourceDomainKey::ProofOccurrences,
    ProjectionSupportsByRecordDomain => StructuralResourceDomainKey::ProjectionSupportsByRecord,
    ProjectionFormulaByRecordDomain => StructuralResourceDomainKey::ProjectionFormulaByRecordMap,
    ProjectionLowerByConstraintDomain => StructuralResourceDomainKey::ProjectionLowerByConstraint,
    DependentRecordsByPremiseDomain => StructuralResourceDomainKey::DependentRecordsByPremiseMap,
    UpperClaimArenaDomain => StructuralResourceDomainKey::UpperClaimArena,
    ReductionClaimIndexDomain => StructuralResourceDomainKey::ReductionClaimIndex,
    LiveCoverageFlatDomain => StructuralResourceDomainKey::LiveCoverageFlat,
    ReplayFiniteMapArenaDomain => StructuralResourceDomainKey::ReplayFiniteMapArena,
    ReplayQualifiedArmResultDomain => StructuralResourceDomainKey::ReplayQualifiedArmResultMap,
    BoundRecordsDomain => StructuralResourceDomainKey::BoundRecords,
    ConstraintRecordsDomain => StructuralResourceDomainKey::ConstraintRecords,
    ReplayDropRecordsDomain => StructuralResourceDomainKey::ReplayDropRecords,
    RowResidualRecordsDomain => StructuralResourceDomainKey::RowResidualRecords,
    RowDerivationArenaDomain => StructuralResourceDomainKey::RowDerivationArena,
    RowReductionRecordsDomain => StructuralResourceDomainKey::RowReductionRecords,
    RowReductionOwnerDomain => StructuralResourceDomainKey::RowReductionOwnerMap,
    LowerFilterRecordsDomain => StructuralResourceDomainKey::LowerFilterRecords,
    OriginIdentityRecordsDomain => StructuralResourceDomainKey::IdentityRecords(IdentityFamily::Origin),
    SchemeInstantiationIdentityRecordsDomain => StructuralResourceDomainKey::IdentityRecords(IdentityFamily::SchemeInstantiation),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub(super) struct ReservationTicketId(NonZeroU64);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ReservationClaim {
    pub(super) domain: StructuralResourceDomainKey,
    pub(super) units: usize,
}

#[derive(Debug, Default)]
pub(super) struct ReservationDomainState {
    pub(super) physical_spare: usize,
    pub(super) outstanding_units: usize,
    pub(super) pending_empty_prune: bool,
}

#[derive(Debug)]
struct ActiveReservationTicket {
    claims: Vec<ReservationClaim>,
}

#[derive(Debug)]
pub(super) struct StructuralReservationTicket {
    pub(super) id: ReservationTicketId,
}

/// One-shot proof that a prepared command owns one reserved unit in a concrete domain.
#[derive(Debug)]
pub(super) struct ReservedOperation {
    ticket: ReservationTicketId,
    domain: StructuralResourceDomainKey,
}

/// A one-shot operation whose ticket and exact target domain were checked before publication.
#[derive(Debug)]
pub(super) struct VerifiedReservedOperation<D: ResourceDomainMarker> {
    target: D::Target,
    _domain: PhantomData<fn() -> D>,
}

#[derive(Debug)]
pub(super) struct StructuralReservationLedger {
    next_ticket_id: Option<NonZeroU64>,
    domains: FxHashMap<StructuralResourceDomainKey, ReservationDomainState>,
    active_tickets: FxHashMap<ReservationTicketId, ActiveReservationTicket>,
}

impl Default for StructuralReservationLedger {
    fn default() -> Self {
        Self {
            next_ticket_id: NonZeroU64::new(1),
            domains: FxHashMap::default(),
            active_tickets: FxHashMap::default(),
        }
    }
}

impl StructuralReservationLedger {
    pub(super) fn reserve(
        &mut self,
        claims: &[ReservationClaim],
    ) -> Result<(StructuralReservationTicket, Vec<ReservedOperation>), ReservationError> {
        let mut aggregated = FxHashMap::default();
        aggregated.try_reserve(claims.len())?;
        for claim in claims {
            let units = aggregated.entry(claim.domain).or_insert(0usize);
            *units = units
                .checked_add(claim.units)
                .ok_or(ReservationError::ArithmeticOverflow)?;
        }

        self.domains.try_reserve(aggregated.len())?;
        self.active_tickets.try_reserve(1)?;
        let mut owned_claims = Vec::new();
        owned_claims.try_reserve(aggregated.len())?;
        let operation_count = aggregated.values().try_fold(0usize, |total, units| {
            total
                .checked_add(*units)
                .ok_or(ReservationError::ArithmeticOverflow)
        })?;
        let mut operations = Vec::new();
        operations.try_reserve(operation_count)?;
        let mut staged_domains = Vec::new();
        staged_domains.try_reserve(aggregated.len())?;
        for (&domain, &units) in &aggregated {
            owned_claims.push(ReservationClaim { domain, units });
            let outstanding = self
                .domains
                .get(&domain)
                .map_or(0, |state| state.outstanding_units);
            let required = outstanding
                .checked_add(units)
                .ok_or(ReservationError::ArithmeticOverflow)?;
            staged_domains.push((domain, units, required));
        }

        // All fallible allocation and checked arithmetic ends before ID issuance. The pushes and
        // map insertions below consume capacity reserved above and cannot grow their containers.
        let id = self.take_next_ticket_id()?;
        for &(domain, units, _) in &staged_domains {
            for _ in 0..units {
                operations.push(ReservedOperation { ticket: id, domain });
            }
        }
        for (domain, _units, required) in staged_domains {
            let state = self.domains.entry(domain).or_default();
            state.physical_spare = state.physical_spare.max(required);
            state.outstanding_units = required;
        }
        let previous = self.active_tickets.insert(
            id,
            ActiveReservationTicket {
                claims: owned_claims,
            },
        );
        debug_assert!(previous.is_none());
        Ok((StructuralReservationTicket { id }, operations))
    }

    fn take_next_ticket_id(&mut self) -> Result<ReservationTicketId, ReservationError> {
        let raw = self
            .next_ticket_id
            .take()
            .ok_or(ReservationError::TicketIdExhausted)?;
        self.next_ticket_id = raw.get().checked_add(1).and_then(NonZeroU64::new);
        Ok(ReservationTicketId(raw))
    }

    pub(super) fn release(&mut self, ticket: StructuralReservationTicket) {
        let Some(active) = self.active_tickets.remove(&ticket.id) else {
            return;
        };
        for claim in active.claims {
            let state = self.domains.get_mut(&claim.domain).expect("active domain");
            state.outstanding_units -= claim.units;
            if state.outstanding_units == 0 && state.pending_empty_prune {
                state.pending_empty_prune = false;
            }
        }
    }

    pub(super) fn mark_pending_empty_prune(&mut self, domain: StructuralResourceDomainKey) {
        self.domains.entry(domain).or_default().pending_empty_prune = true;
    }

    #[cfg(test)]
    pub(super) fn counts(&self) -> (usize, usize, usize) {
        let outstanding = self
            .domains
            .values()
            .map(|state| state.outstanding_units)
            .sum();
        let pins = self
            .domains
            .values()
            .filter(|state| state.pending_empty_prune)
            .count();
        (self.active_tickets.len(), outstanding, pins)
    }

    #[cfg(test)]
    pub(super) fn spare_and_outstanding(
        &self,
        domain: StructuralResourceDomainKey,
    ) -> (usize, usize) {
        self.domains
            .get(&domain)
            .map(|state| (state.physical_spare, state.outstanding_units))
            .unwrap_or_default()
    }
}

impl ReservedOperation {
    pub(super) fn domain(&self) -> StructuralResourceDomainKey {
        self.domain
    }

    pub(super) fn verify<D: ResourceDomainMarker>(
        self,
        ticket: ReservationTicketId,
        target: D::Target,
    ) -> Result<VerifiedReservedOperation<D>, ReservationError> {
        let expected = D::key(target);
        if self.ticket != ticket || self.domain != expected {
            return Err(ReservationError::DomainMismatch);
        }
        Ok(VerifiedReservedOperation {
            target,
            _domain: PhantomData,
        })
    }

    #[cfg(test)]
    pub(super) fn replace_domain_for_test(&mut self, domain: StructuralResourceDomainKey) {
        self.domain = domain;
    }
}

impl<D: ResourceDomainMarker> VerifiedReservedOperation<D> {
    #[allow(dead_code)]
    pub(super) fn target(&self) -> D::Target {
        self.target
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn claim(domain: StructuralResourceDomainKey, units: usize) -> ReservationClaim {
        ReservationClaim { domain, units }
    }

    #[test]
    fn cpk_sv_d_ss1_outstanding_tickets_do_not_share_one_spare_slot() {
        let domain = StructuralResourceDomainKey::ProofOccurrences;
        let mut ledger = StructuralReservationLedger::default();
        let (first, _) = ledger.reserve(&[claim(domain, 1)]).unwrap();
        assert_eq!(ledger.spare_and_outstanding(domain), (1, 1));
        let (second, _) = ledger.reserve(&[claim(domain, 1)]).unwrap();
        assert_eq!(ledger.spare_and_outstanding(domain), (2, 2));
        ledger.release(first);
        ledger.release(second);
        assert_eq!(ledger.counts(), (0, 0, 0));
    }

    #[test]
    fn cpk_sv_d_ss1_ticket_ids_are_attempt_global_and_multi_domain_has_one_entry() {
        let mut ledger = StructuralReservationLedger::default();
        let (claim_ticket, _) = ledger
            .reserve(&[claim(StructuralResourceDomainKey::UpperClaimArena, 1)])
            .unwrap();
        let (formula_ticket, operations) = ledger
            .reserve(&[
                claim(StructuralResourceDomainKey::ProjectionFormulaByRecordMap, 1),
                claim(
                    StructuralResourceDomainKey::ProjectionFormulaEntries(BoundRecordId(0)),
                    2,
                ),
            ])
            .unwrap();
        assert_ne!(claim_ticket.id, formula_ticket.id);
        assert_eq!(operations.len(), 3);
        assert_eq!(ledger.counts(), (2, 4, 0));
        ledger.release(claim_ticket);
        ledger.release(formula_ticket);
        assert_eq!(ledger.counts(), (0, 0, 0));
    }

    #[test]
    fn cpk_sv_d_ss1_pending_prune_is_pinned_until_last_ticket_release() {
        let domain = StructuralResourceDomainKey::LiveCoverageFlat;
        let mut ledger = StructuralReservationLedger::default();
        let (ticket, _) = ledger.reserve(&[claim(domain, 1)]).unwrap();
        ledger.mark_pending_empty_prune(domain);
        assert_eq!(ledger.counts(), (1, 1, 1));
        ledger.release(ticket);
        assert_eq!(ledger.counts(), (0, 0, 0));
    }

    #[test]
    fn cpk_sv_d_ss1_reserved_operation_rejects_a_different_domain() {
        let reserved = StructuralResourceDomainKey::ProofOccurrences;
        let mut ledger = StructuralReservationLedger::default();
        let (ticket, mut operations) = ledger.reserve(&[claim(reserved, 1)]).unwrap();
        let operation = operations.pop().unwrap();
        assert!(matches!(
            operation.verify::<BoundRecordsDomain>(ticket.id, ()),
            Err(ReservationError::DomainMismatch)
        ));
        ledger.release(ticket);
        assert_eq!(ledger.counts(), (0, 0, 0));
    }

    #[test]
    fn cpk_sv_d_ss1_reservation_arithmetic_overflow_is_typed_and_atomic() {
        let domain = StructuralResourceDomainKey::ProofOccurrences;
        let mut ledger = StructuralReservationLedger::default();
        let result = ledger.reserve(&[claim(domain, usize::MAX), claim(domain, 1)]);
        assert!(matches!(result, Err(ReservationError::ArithmeticOverflow)));
        assert_eq!(ledger.counts(), (0, 0, 0));
        assert_eq!(ledger.spare_and_outstanding(domain), (0, 0));
        let (first_ticket, _) = ledger.reserve(&[claim(domain, 1)]).unwrap();
        assert_eq!(
            first_ticket.id,
            ReservationTicketId(NonZeroU64::new(1).unwrap())
        );
        ledger.release(first_ticket);
    }
}
