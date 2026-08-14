//! Data-only public intents and opaque committed receipts.

/// The closed SS0 command vocabulary. Payload-bearing forms are added when their storage family
/// migrates; SS1 deliberately records only command identity in its shadow path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::constraints) enum StructuralMutationIntent {
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

/// Data-only command identity returned by the shadow single finalizer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::constraints) enum CommittedStructuralMutation {
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

impl CommittedStructuralMutation {
    pub(in crate::constraints) fn was_changed(self) -> bool {
        true
    }
}
