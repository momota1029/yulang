use super::{EffectConstraintWeights, Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};

impl Infer {
    pub(super) fn add_lower_bound(
        &self,
        target: TypeVar,
        pos: PosId,
        weights: EffectConstraintWeights,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) -> bool {
        let start = crate::profile::ProfileClock::now();
        let added = self.add_weighted_lower_raw(target, pos, weights);
        if added.unweighted {
            self.resolve_deferred_selections_for(target);
            self.resolve_deferred_selection_dependents_for(target);
            self.solve_handler_matches_for(target, cause, cache);
        }
        self.record_profile(start, |profile, elapsed| {
            profile.add_lower_bound += elapsed;
        });
        added.weighted
    }

    pub(super) fn add_upper_bound(
        &self,
        source: TypeVar,
        neg: NegId,
        weights: EffectConstraintWeights,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) -> bool {
        let start = crate::profile::ProfileClock::now();
        let added = self.add_weighted_upper_raw(source, neg, weights);
        if added.unweighted {
            self.solve_handler_matches_for(source, cause, cache);
        }
        self.record_profile(start, |profile, elapsed| {
            profile.add_upper_bound += elapsed;
        });
        added.weighted
    }

    pub(super) fn propagate_lower_to_uppers(
        &self,
        target: TypeVar,
        pos: PosId,
        weights: EffectConstraintWeights,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        for upper in self.weighted_upper_bounds_of(target) {
            self.constrain_step_with_hint_weighted(
                pos,
                upper.neg,
                weights.union(&upper.weights),
                cause,
                Some(target),
                cache,
            );
        }
    }

    pub(super) fn propagate_upper_to_lowers(
        &self,
        source: TypeVar,
        neg: NegId,
        weights: EffectConstraintWeights,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        for lower in self.weighted_lower_bounds_of(source) {
            self.constrain_step_with_hint_weighted(
                lower.pos,
                neg,
                lower.weights.union(&weights),
                cause,
                Some(source),
                cache,
            );
        }
        for instance in self.compact_lower_instances_of(source) {
            self.constrain_compact_instance_to_neg_weighted(
                &instance,
                neg,
                weights.clone(),
                cause,
                Some(source),
                cache,
            );
        }
    }
}
