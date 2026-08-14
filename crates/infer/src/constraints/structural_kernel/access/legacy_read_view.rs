//! Scope-private read routing over the pre-sealing production owners.

use poly::types::{PosId, Subtractability, TypeVar};
use rustc_hash::{FxHashMap, FxHashSet};

use super::super::read_view::ImmutableTypeShapeView;
use crate::constraints::proof::{
    CpkProjectionEvaluator, ProjectionDecision, ProjectionEvaluationRound, ProofFailure,
    ProofOccurrenceStore, SemanticBoundRecordRef, SemanticConstraintRecordRef, SemanticFactView,
    SemanticRowReductionRecordRef,
};
use crate::constraints::{
    BoundRecordId, BoundSemanticKey, ConstraintRecord, ConstraintRecordId, GeneralizedSchemeRecord,
    GeneralizedSchemeWitness, LowerFilterRecord, LowerFilterRecordId, OriginRecord,
    ReplayDerivationBudget, ReplayDerivationStorage, ReplayDropRecord, ReplayDropRecordId,
    RowDerivation, RowDerivationId, RowResidualKey, RowResidualRecord, RowResidualRecordId,
    SchemeInstantiationId, SchemeInstantiationKey, SchemeInstantiationRecord, SourceBoundaryRecord,
    SubtypeConstraintKey, TypeBounds, UnweightedRowReductionOwner, UnweightedRowReductionRecord,
    UnweightedRowReductionRecordId,
};

/// All production read authorities before any family has been sealed.
///
/// This type is visible only to its parent `access` module. It owns no result state and has no
/// snapshot or reuse identity, so it cannot become a persistent round facade.
#[allow(
    dead_code,
    reason = "SS2-P0 callers consume these family reads incrementally"
)]
pub(super) struct LegacyOnlyReadSources<'query> {
    proof: &'query ProofOccurrenceStore,
    bounds: &'query TypeBounds,
    constraints_replay: LegacyConstraintReplayReadSources<'query>,
    rows: LegacyRowReadSources<'query>,
    identities: LegacyIdentityReadSources<'query>,
}

#[allow(
    dead_code,
    reason = "SS2-P0 callers consume these family reads incrementally"
)]
pub(super) struct LegacyConstraintReplayReadSources<'query> {
    canonical_constraints: &'query FxHashMap<SubtypeConstraintKey, ConstraintRecordId>,
    constraint_records: &'query [ConstraintRecord],
    replay_drop_records: &'query [ReplayDropRecord],
    replay_drop_index: &'query FxHashMap<ReplayDropRecord, ReplayDropRecordId>,
    replay_derivation_budget: &'query ReplayDerivationBudget,
    replay_derivation_storage: &'query ReplayDerivationStorage,
}

#[allow(
    dead_code,
    reason = "SS2-P0 callers consume these family reads incrementally"
)]
pub(super) struct LegacyRowReadSources<'query> {
    row_residuals: &'query FxHashMap<RowResidualKey, TypeVar>,
    row_residual_record_ids: &'query FxHashMap<RowResidualKey, RowResidualRecordId>,
    row_residual_records: &'query [RowResidualRecord],
    unweighted_row_reductions_by_source:
        &'query FxHashMap<TypeVar, Vec<UnweightedRowReductionRecordId>>,
    unweighted_row_reduction_owners_by_upper:
        &'query FxHashMap<BoundRecordId, Vec<UnweightedRowReductionOwner>>,
    unweighted_row_reduction_records: &'query [UnweightedRowReductionRecord],
    row_derivations: &'query [RowDerivation],
    row_derivation_index: &'query FxHashMap<RowDerivation, RowDerivationId>,
    lower_filters: &'query FxHashMap<TypeVar, FxHashSet<Subtractability>>,
    lower_filter_record_ids: &'query FxHashMap<(TypeVar, Subtractability), LowerFilterRecordId>,
    lower_filter_records: &'query [LowerFilterRecord],
}

#[allow(
    dead_code,
    reason = "SS2-P0 callers consume these family reads incrementally"
)]
pub(super) struct LegacyIdentityReadSources<'query> {
    origins: &'query [OriginRecord],
    source_boundaries: &'query [SourceBoundaryRecord],
    generalized_schemes: &'query [GeneralizedSchemeRecord],
    generalized_witnesses: &'query [GeneralizedSchemeWitness],
    scheme_instantiations: &'query [SchemeInstantiationRecord],
    scheme_instantiation_index: &'query FxHashMap<SchemeInstantiationKey, SchemeInstantiationId>,
}

/// Immutable facade constructed once per legacy HRTB query invocation.
pub(super) struct LegacyOnlyQueryView<'query> {
    sources: LegacyOnlyReadSources<'query>,
    type_shapes: ImmutableTypeShapeView<'query>,
}

impl<'query> LegacyOnlyReadSources<'query> {
    pub(super) fn new(
        proof: &'query ProofOccurrenceStore,
        bounds: &'query TypeBounds,
        constraints_replay: LegacyConstraintReplayReadSources<'query>,
        rows: LegacyRowReadSources<'query>,
        identities: LegacyIdentityReadSources<'query>,
    ) -> Self {
        Self {
            proof,
            bounds,
            constraints_replay,
            rows,
            identities,
        }
    }
}

impl<'query> LegacyConstraintReplayReadSources<'query> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        canonical_constraints: &'query FxHashMap<SubtypeConstraintKey, ConstraintRecordId>,
        constraint_records: &'query [ConstraintRecord],
        replay_drop_records: &'query [ReplayDropRecord],
        replay_drop_index: &'query FxHashMap<ReplayDropRecord, ReplayDropRecordId>,
        replay_derivation_budget: &'query ReplayDerivationBudget,
        replay_derivation_storage: &'query ReplayDerivationStorage,
    ) -> Self {
        Self {
            canonical_constraints,
            constraint_records,
            replay_drop_records,
            replay_drop_index,
            replay_derivation_budget,
            replay_derivation_storage,
        }
    }
}

impl<'query> LegacyRowReadSources<'query> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        row_residuals: &'query FxHashMap<RowResidualKey, TypeVar>,
        row_residual_record_ids: &'query FxHashMap<RowResidualKey, RowResidualRecordId>,
        row_residual_records: &'query [RowResidualRecord],
        unweighted_row_reductions_by_source: &'query FxHashMap<
            TypeVar,
            Vec<UnweightedRowReductionRecordId>,
        >,
        unweighted_row_reduction_owners_by_upper: &'query FxHashMap<
            BoundRecordId,
            Vec<UnweightedRowReductionOwner>,
        >,
        unweighted_row_reduction_records: &'query [UnweightedRowReductionRecord],
        row_derivations: &'query [RowDerivation],
        row_derivation_index: &'query FxHashMap<RowDerivation, RowDerivationId>,
        lower_filters: &'query FxHashMap<TypeVar, FxHashSet<Subtractability>>,
        lower_filter_record_ids: &'query FxHashMap<(TypeVar, Subtractability), LowerFilterRecordId>,
        lower_filter_records: &'query [LowerFilterRecord],
    ) -> Self {
        Self {
            row_residuals,
            row_residual_record_ids,
            row_residual_records,
            unweighted_row_reductions_by_source,
            unweighted_row_reduction_owners_by_upper,
            unweighted_row_reduction_records,
            row_derivations,
            row_derivation_index,
            lower_filters,
            lower_filter_record_ids,
            lower_filter_records,
        }
    }
}

impl<'query> LegacyIdentityReadSources<'query> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        origins: &'query [OriginRecord],
        source_boundaries: &'query [SourceBoundaryRecord],
        generalized_schemes: &'query [GeneralizedSchemeRecord],
        generalized_witnesses: &'query [GeneralizedSchemeWitness],
        scheme_instantiations: &'query [SchemeInstantiationRecord],
        scheme_instantiation_index: &'query FxHashMap<
            SchemeInstantiationKey,
            SchemeInstantiationId,
        >,
    ) -> Self {
        Self {
            origins,
            source_boundaries,
            generalized_schemes,
            generalized_witnesses,
            scheme_instantiations,
            scheme_instantiation_index,
        }
    }
}

impl<'query> LegacyOnlyQueryView<'query> {
    pub(super) fn new(
        sources: LegacyOnlyReadSources<'query>,
        type_shapes: ImmutableTypeShapeView<'query>,
    ) -> Self {
        Self {
            sources,
            type_shapes,
        }
    }

    pub(super) fn projection_lower_records(
        &self,
        var: TypeVar,
    ) -> impl Iterator<Item = (BoundRecordId, &crate::constraints::WeightedLowerBound)> {
        self.sources
            .bounds
            .of(var)
            .into_iter()
            .flat_map(crate::constraints::VarBounds::projection_lower_records)
    }

    pub(super) fn project_lower<'a>(
        &'a self,
        record: BoundRecordId,
        round: &mut ProjectionEvaluationRound<'a>,
    ) -> Result<ProjectionDecision, ProofFailure> {
        self.sources.proof.project_lower(self, record, round)
    }

    pub(super) fn pos_var(&self, id: PosId) -> Option<TypeVar> {
        self.type_shapes.pos_var(id)
    }

    pub(super) fn cpk_projection_evaluator(&self) -> CpkProjectionEvaluator<'_> {
        CpkProjectionEvaluator::new(self, self.sources.proof)
    }

    pub(super) fn active_projection_record_owner(&self, record: BoundRecordId) -> Option<TypeVar> {
        self.bound(record)
            .filter(|record| record.state() != crate::constraints::BoundRecordState::Tombstone)
            .map(SemanticBoundRecordRef::owner)
    }

    #[cfg(test)]
    pub(super) fn storage_census(&self) -> LegacyStorageCensus {
        let _ = self.type_shapes;
        LegacyStorageCensus {
            proof_occurrences: self.sources.proof.occurrences.len(),
            bound_canonical: self.sources.bounds.canonical.len(),
            bound_records: self.sources.bounds.records.len(),
            constraint_canonical: self.sources.constraints_replay.canonical_constraints.len(),
            constraint_records: self.sources.constraints_replay.constraint_records.len(),
            replay_drop_index: self.sources.constraints_replay.replay_drop_index.len(),
            row_records: self.sources.rows.row_residual_records.len()
                + self.sources.rows.unweighted_row_reduction_records.len()
                + self.sources.rows.row_derivations.len()
                + self.sources.rows.lower_filter_records.len(),
            row_lower_filter_map: self.sources.rows.lower_filters.len(),
            row_lower_filter_index: self.sources.rows.lower_filter_record_ids.len(),
            identity_records: self.sources.identities.origins.len()
                + self.sources.identities.source_boundaries.len()
                + self.sources.identities.generalized_schemes.len()
                + self.sources.identities.generalized_witnesses.len()
                + self.sources.identities.scheme_instantiations.len(),
            scheme_instantiations: self.sources.identities.scheme_instantiations.len(),
            scheme_instantiation_index: self.sources.identities.scheme_instantiation_index.len(),
        }
    }
}

impl SemanticFactView for LegacyOnlyQueryView<'_> {
    fn constraint(&self, id: ConstraintRecordId) -> Option<SemanticConstraintRecordRef<'_>> {
        self.sources
            .constraints_replay
            .constraint_records
            .get(id.0 as usize)
            .map(ConstraintRecord::semantic_ref)
    }

    fn bound(&self, id: BoundRecordId) -> Option<SemanticBoundRecordRef<'_>> {
        self.sources
            .bounds
            .records
            .get(id.0 as usize)
            .map(crate::constraints::BoundRecord::semantic_ref)
    }

    fn row_reduction(
        &self,
        id: UnweightedRowReductionRecordId,
    ) -> Option<SemanticRowReductionRecordRef<'_>> {
        self.sources
            .rows
            .unweighted_row_reduction_records
            .get(id.0 as usize)
            .map(crate::constraints::UnweightedRowReductionRecord::semantic_ref)
    }

    fn lower_record_for_constraint(&self, id: ConstraintRecordId) -> Option<BoundRecordId> {
        if let Some(record) = self
            .sources
            .proof
            .projection_lower_record_for_constraint(id)
        {
            return Some(record);
        }
        let constraint = &self
            .sources
            .constraints_replay
            .constraint_records
            .get(id.0 as usize)?
            .key;
        let target = self.type_shapes.neg_var(constraint.upper)?;
        self.sources
            .bounds
            .canonical
            .get(&BoundSemanticKey::Lower {
                owner: target,
                endpoint: constraint.lower,
                weights: constraint.weights.clone(),
            })
            .copied()
    }

    fn is_var_pos(&self, id: poly::types::PosId) -> bool {
        self.type_shapes.is_var_pos(id)
    }
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::constraints::structural_kernel) struct LegacyStorageCensus {
    pub(in crate::constraints::structural_kernel) proof_occurrences: usize,
    pub(in crate::constraints::structural_kernel) bound_canonical: usize,
    pub(in crate::constraints::structural_kernel) bound_records: usize,
    pub(in crate::constraints::structural_kernel) constraint_canonical: usize,
    pub(in crate::constraints::structural_kernel) constraint_records: usize,
    pub(in crate::constraints::structural_kernel) replay_drop_index: usize,
    pub(in crate::constraints::structural_kernel) row_records: usize,
    pub(in crate::constraints::structural_kernel) row_lower_filter_map: usize,
    pub(in crate::constraints::structural_kernel) row_lower_filter_index: usize,
    pub(in crate::constraints::structural_kernel) identity_records: usize,
    pub(in crate::constraints::structural_kernel) scheme_instantiations: usize,
    pub(in crate::constraints::structural_kernel) scheme_instantiation_index: usize,
}
