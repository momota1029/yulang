//! Gateway-constructed, family-specific shadow publication ports.

use super::reservation::ReservedOperation;
use super::storage::StructuralData;

macro_rules! shadow_port {
    ($name:ident, $method:ident) => {
        pub(in crate::constraints::structural_kernel) struct $name<'write> {
            data: &'write mut StructuralData,
            reserved: ReservedOperation,
        }

        impl<'write> $name<'write> {
            pub(super) fn new(
                data: &'write mut StructuralData,
                reserved: ReservedOperation,
            ) -> Self {
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
