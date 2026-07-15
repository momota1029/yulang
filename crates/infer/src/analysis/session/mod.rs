use super::*;

mod candidate_settlement;
#[cfg(test)]
mod early_fallback_classifier;
mod generalize;
mod instantiate;
mod lifecycle;
mod selection;
#[cfg(test)]
mod shadow_dirty_oracle;
#[cfg(test)]
mod stage0_support;

pub(super) use candidate_settlement::CandidateSettlementFact;
#[cfg(test)]
pub(crate) use candidate_settlement::CandidateSettlementSafetyWitness;

#[cfg(test)]
pub(crate) use early_fallback_classifier::{
    CandidateIndependentFallbackClassification, CandidateIndependentFallbackRejection,
    CandidateIndependentFallbackSelection,
};
#[cfg(test)]
pub(crate) use shadow_dirty_oracle::{
    ShadowDirtyOracle, begin_shadow_owner_reads, record_shadow_applied_resolution_read,
    record_shadow_birth_level_read, record_shadow_bound_read, record_shadow_candidate_bucket_read,
    record_shadow_level_read, record_shadow_method_taint_read, record_shadow_neighbor_read,
    record_shadow_pre_pop_read, record_shadow_subtract_read,
    with_shadow_dirty_oracle_for_new_sessions,
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
