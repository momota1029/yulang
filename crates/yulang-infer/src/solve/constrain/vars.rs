use super::{EffectConstraintWeights, Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};

impl Infer {
    pub(super) fn constrain_var_to_var(
        &self,
        pos: PosId,
        source: TypeVar,
        neg: NegId,
        target: TypeVar,
        weights: EffectConstraintWeights,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        self.propagate_effect_non_subtracts_to_var(source, target);
        self.propagate_effect_non_subtracts_to_var(target, source);
        self.record_effect_non_subtracts_to_var(source, &weights.left);
        self.record_effect_non_subtracts_to_var(target, &weights.right);

        let ep = self.extrude_pos(pos, self.level_of(target));
        let en = self.extrude_neg(neg, self.level_of(source));
        let added_lower = self.add_lower_bound(target, ep, weights.clone(), cause, cache);
        let added_upper = self.add_upper_bound(source, en, weights.clone(), cause, cache);

        if added_lower || self.should_revisit_lower(cause, target, ep) {
            self.propagate_lower_to_uppers(target, ep, weights.clone(), cause, cache);
        }
        if added_upper || self.should_revisit_upper(cause, source, en) {
            self.propagate_upper_to_lowers(source, en, weights, cause, cache);
        }
    }

    pub(super) fn constrain_to_neg_var(
        &self,
        pos: PosId,
        target: TypeVar,
        weights: EffectConstraintWeights,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        self.propagate_effect_non_subtracts_to_pos(target, pos);
        self.record_effect_non_subtracts_to_pos(pos, &weights.left);

        let ep = self.extrude_pos(pos, self.level_of(target));
        if self.add_lower_bound(target, ep, weights.clone(), cause, cache)
            || self.should_revisit_lower(cause, target, ep)
        {
            self.propagate_lower_to_uppers(target, ep, weights, cause, cache);
        }
    }

    pub(super) fn constrain_pos_var_to(
        &self,
        source: TypeVar,
        neg: NegId,
        weights: EffectConstraintWeights,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        self.propagate_effect_non_subtracts_to_neg(source, neg);
        self.record_effect_non_subtracts_to_neg(neg, &weights.right);

        let en = self.extrude_neg(neg, self.level_of(source));
        if self.add_upper_bound(source, en, weights.clone(), cause, cache)
            || self.should_revisit_upper(cause, source, en)
        {
            self.propagate_upper_to_lowers(source, en, weights, cause, cache);
        }
    }

    fn should_revisit_lower(&self, cause: &ConstraintCause, target: TypeVar, pos: PosId) -> bool {
        super::errors::should_revisit_existing_constraint(cause)
            && self.lower_members.borrow().contains(&(target, pos))
    }

    fn should_revisit_upper(&self, cause: &ConstraintCause, source: TypeVar, neg: NegId) -> bool {
        super::errors::should_revisit_existing_constraint(cause)
            && self.upper_members.borrow().contains(&(source, neg))
    }
}
