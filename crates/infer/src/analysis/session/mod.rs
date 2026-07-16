use super::*;

mod candidate_settlement;
#[cfg(test)]
mod dirty_scheduling_contract;
#[cfg(test)]
mod early_fallback_classifier;
mod generalize;
#[cfg(test)]
mod generalize_snapshot_characterization;
mod instantiate;
mod lifecycle;
mod owner_dirty_scheduler;
mod selection;
#[cfg(test)]
mod shadow_dirty_oracle;
#[cfg(test)]
mod stage0_support;

pub(super) use candidate_settlement::CandidateSettlementFact;
#[cfg(test)]
pub(crate) use candidate_settlement::CandidateSettlementSafetyWitness;

#[cfg(test)]
pub(crate) use dirty_scheduling_contract::DependencyKeyKind;

#[cfg(test)]
pub(crate) use early_fallback_classifier::{
    CandidateIndependentFallbackClassification, CandidateIndependentFallbackRejection,
    CandidateIndependentFallbackSelection,
};
#[cfg(test)]
pub(crate) use generalize_snapshot_characterization::{
    GeneralizeSnapshotCharacterizationOracle, GeneralizeSnapshotCharacterizationReport,
    GeneralizeSnapshotRootObservation, GeneralizeSnapshotRootReport,
    with_generalize_snapshot_characterization_for_new_sessions,
};
pub(super) use owner_dirty_scheduler::OwnerScheduleDecision;
pub use owner_dirty_scheduler::with_owner_dirty_scheduler_disabled_for_new_sessions;
pub(crate) use owner_dirty_scheduler::{
    MethodRoleOwnerDirtyScheduler, OwnerSolveOutcome, begin_owner_dependency_reads,
    record_owner_applied_resolution_read, record_owner_candidate_bucket_read,
    record_owner_dependency_read, record_owner_method_taint_read,
};
#[cfg(test)]
pub(crate) use owner_dirty_scheduler::{
    OwnerPredictionReason, with_owner_dirty_scheduler_for_new_sessions,
};
#[cfg(test)]
pub(crate) use owner_dirty_scheduler::{
    record_owner_birth_level_read, record_owner_bound_read, record_owner_level_read,
    record_owner_neighbor_read, record_owner_pre_pop_read, record_owner_subtract_read,
};
#[cfg(test)]
pub(crate) use shadow_dirty_oracle::{
    ShadowDirtyOracle, with_shadow_dirty_oracle_for_new_sessions,
};
#[cfg(test)]
pub(crate) use stage0_support::{Stage0PendingWorkInventory, Stage0QuantifyEvent};

#[cfg(test)]
impl AnalysisSession {
    pub(crate) fn enqueue_candidate_independent_fallback_frontier_resolutions(
        &mut self,
        components: &[crate::scc::CandidateIndependentFallbackComponent],
    ) -> bool {
        let mut ready = Vec::new();
        for component in components {
            let CandidateIndependentFallbackClassification::Eligible { selections } =
                self.classify_candidate_independent_fallback_component(component)
            else {
                continue;
            };
            ready.extend(selections.into_iter().map(|selection| {
                (
                    selection.select_id,
                    SelectionTarget::TypeclassMethod {
                        member: selection.target,
                    },
                )
            }));
        }
        self.enqueue_structured_selection_resolutions(ready)
    }
}
