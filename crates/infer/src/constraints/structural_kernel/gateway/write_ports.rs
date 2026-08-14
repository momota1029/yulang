//! Gateway-constructed, family-specific shadow publication ports.

use super::reservation::{StructuralResourceDomainKey, VerifiedReservedOperation};
use super::storage::StructuralData;

macro_rules! shadow_port {
    ($name:ident, $method:ident) => {
        pub(in crate::constraints::structural_kernel) struct $name<'write> {
            data: &'write mut StructuralData,
            reserved: VerifiedReservedOperation,
        }

        impl<'write> $name<'write> {
            pub(super) fn new(
                data: &'write mut StructuralData,
                reserved: VerifiedReservedOperation,
                expected_domain: StructuralResourceDomainKey,
            ) -> Self {
                reserved.assert_domain(expected_domain);
                Self { data, reserved }
            }

            pub(in crate::constraints::structural_kernel) fn publish_shadow(self) {
                let _consumed_one_shot_authority = self.reserved;
                self.data.$method();
            }
        }
    };
}

shadow_port!(ProofPublishPort, record_proof_shadow);
shadow_port!(BoundsPublishPort, record_bounds_shadow);
shadow_port!(ConstraintsPublishPort, record_constraints_shadow);
shadow_port!(RowsPublishPort, record_rows_shadow);
shadow_port!(IdentitiesPublishPort, record_identities_shadow);

#[cfg(test)]
mod tests {
    use std::panic::{AssertUnwindSafe, catch_unwind};

    use super::super::reservation::{
        ReservationClaim, StructuralReservationLedger, StructuralResourceDomainKey,
    };
    use super::*;

    #[test]
    fn cpk_sv_d_ss1_write_port_rechecks_the_exact_reserved_domain() {
        let reserved_domain = StructuralResourceDomainKey::BoundRecords;
        let mut ledger = StructuralReservationLedger::default();
        let (ticket, mut operations) = ledger
            .reserve(&[ReservationClaim {
                domain: reserved_domain,
                units: 1,
            }])
            .unwrap();
        let verified = operations
            .pop()
            .unwrap()
            .verify(ticket.id, reserved_domain)
            .unwrap();
        let mut data = StructuralData::default();

        let mismatch = catch_unwind(AssertUnwindSafe(|| {
            let _ = ProofPublishPort::new(
                &mut data,
                verified,
                StructuralResourceDomainKey::ProofOccurrences,
            );
        }));
        assert!(mismatch.is_err());
        assert_eq!(data.shadow_publication_counts(), [0; 5]);
        ledger.release(ticket);
        assert_eq!(ledger.counts(), (0, 0, 0));
    }
}
