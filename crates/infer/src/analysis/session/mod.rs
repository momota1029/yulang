use super::*;

mod candidate_settlement;
#[cfg(test)]
mod early_fallback_classifier;
mod generalize;
mod instantiate;
mod lifecycle;
mod selection;

pub(super) use candidate_settlement::CandidateSettlementFact;
#[cfg(test)]
pub(crate) use candidate_settlement::CandidateSettlementSafetyWitness;

#[cfg(test)]
pub(crate) use early_fallback_classifier::{
    CandidateIndependentFallbackClassification, CandidateIndependentFallbackRejection,
    CandidateIndependentFallbackSelection,
};

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
