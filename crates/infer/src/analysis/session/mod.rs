use super::*;

#[cfg(test)]
mod early_fallback_classifier;
mod generalize;
mod instantiate;
mod lifecycle;
mod selection;

#[cfg(test)]
pub(crate) use early_fallback_classifier::{
    CandidateIndependentFallbackClassification, CandidateIndependentFallbackRejection,
    CandidateIndependentFallbackSelection,
};
