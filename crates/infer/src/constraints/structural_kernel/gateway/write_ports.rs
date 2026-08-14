//! Gateway-constructed, domain-typed shadow publication ports.

#![allow(unexpected_cfgs)]

use super::reservation::{
    BoundRecordsDomain, ConstraintRecordsDomain, DependentRecordsByPremiseDomain,
    LiveCoverageFlatDomain, LowerFilterRecordsDomain, OriginIdentityRecordsDomain,
    ProjectionFormulaByRecordDomain, ProjectionLowerByConstraintDomain,
    ProjectionSupportsByRecordDomain, ProofOccurrencesDomain, ReductionClaimIndexDomain,
    ReplayDropRecordsDomain, ReplayFiniteMapArenaDomain, ReplayQualifiedArmResultDomain,
    RowDerivationArenaDomain, RowReductionOwnerDomain, RowReductionRecordsDomain,
    RowResidualRecordsDomain, SchemeInstantiationIdentityRecordsDomain, UpperClaimArenaDomain,
    VerifiedReservedOperation,
};
use super::storage::StructuralData;

macro_rules! shadow_port {
    (
        $port:ident,
        $authority:ident,
        $publish:ident,
        { $( $constructor:ident => $variant:ident($domain:ty) ),+ $(,)? }
    ) => {
        enum $authority {
            $( $variant(VerifiedReservedOperation<$domain>), )+
        }

        pub(in crate::constraints::structural_kernel) struct $port<'write> {
            data: &'write mut StructuralData,
            reserved: $authority,
        }

        impl<'write> $port<'write> {
            $(
                pub(super) fn $constructor(
                    data: &'write mut StructuralData,
                    reserved: VerifiedReservedOperation<$domain>,
                ) -> Self {
                    Self {
                        data,
                        reserved: $authority::$variant(reserved),
                    }
                }
            )+

            pub(in crate::constraints::structural_kernel) fn publish_shadow(self) {
                match self.reserved {
                    $( $authority::$variant(_reserved) => {}, )+
                }
                self.data.$publish();
            }
        }
    };
}

shadow_port!(
    ProofPublishPort,
    ProofReservedOperation,
    record_proof_shadow,
    {
        proof_occurrences => ProofOccurrences(ProofOccurrencesDomain),
        projection_support => ProjectionSupport(ProjectionSupportsByRecordDomain),
        projection_formula => ProjectionFormula(ProjectionFormulaByRecordDomain),
        projection_lower => ProjectionLower(ProjectionLowerByConstraintDomain),
        dependent_records => DependentRecords(DependentRecordsByPremiseDomain),
        upper_claim => UpperClaim(UpperClaimArenaDomain),
        reduction_claim => ReductionClaim(ReductionClaimIndexDomain),
        live_coverage => LiveCoverage(LiveCoverageFlatDomain),
        replay_finite_map => ReplayFiniteMap(ReplayFiniteMapArenaDomain),
        replay_qualified => ReplayQualified(ReplayQualifiedArmResultDomain),
    }
);

shadow_port!(
    BoundsPublishPort,
    BoundsReservedOperation,
    record_bounds_shadow,
    { bound_records => BoundRecords(BoundRecordsDomain) }
);

shadow_port!(
    ConstraintsPublishPort,
    ConstraintsReservedOperation,
    record_constraints_shadow,
    {
        constraint_records => ConstraintRecords(ConstraintRecordsDomain),
        replay_drop => ReplayDrop(ReplayDropRecordsDomain),
    }
);

shadow_port!(
    RowsPublishPort,
    RowsReservedOperation,
    record_rows_shadow,
    {
        row_residual => RowResidual(RowResidualRecordsDomain),
        row_derivation => RowDerivation(RowDerivationArenaDomain),
        row_reduction => RowReduction(RowReductionRecordsDomain),
        row_owner => RowOwner(RowReductionOwnerDomain),
        lower_filter => LowerFilter(LowerFilterRecordsDomain),
    }
);

shadow_port!(
    IdentitiesPublishPort,
    IdentitiesReservedOperation,
    record_identities_shadow,
    {
        origin => Origin(OriginIdentityRecordsDomain),
        scheme_instantiation => SchemeInstantiation(SchemeInstantiationIdentityRecordsDomain),
    }
);

// Compiled by the SS1 UI gate. The typed authority for the formula map cannot enter the
// proof-occurrence port; this is a type error before any publication code exists.
#[cfg(cpk_sv_d_ss1_ui_domain_port_mismatch)]
fn ui_domain_port_mismatch_is_rejected(
    data: &mut StructuralData,
    reserved: VerifiedReservedOperation<ProjectionFormulaByRecordDomain>,
) {
    let _ = ProofPublishPort::proof_occurrences(data, reserved);
}
