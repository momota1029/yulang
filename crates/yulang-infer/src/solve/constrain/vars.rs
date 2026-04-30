use super::{Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};

impl Infer {
    pub(super) fn constrain_var_to_var(
        &self,
        pos: PosId,
        source: TypeVar,
        neg: NegId,
        target: TypeVar,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        if self.is_through(source) && !self.is_through(target) {
            self.constrain_through_var_to_var(pos, target, cause, cache);
            return;
        }

        let ep = self.extrude_pos(pos, self.level_of(target));
        let en = self.extrude_neg(neg, self.level_of(source));
        let added_lower = self.add_lower_bound(target, ep, cause, cache);
        let added_upper = self.add_upper_bound(source, en, cause, cache);

        if added_lower || self.should_revisit_lower(cause, target, ep) {
            self.propagate_lower_to_uppers(target, ep, cause, cache);
        }
        if added_upper || self.should_revisit_upper(cause, source, en) {
            self.propagate_upper_to_lowers(source, en, cause, cache);
        }
    }

    pub(super) fn constrain_to_neg_var(
        &self,
        pos: PosId,
        target: TypeVar,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        let ep = self.extrude_pos(pos, self.level_of(target));
        if self.add_lower_bound(target, ep, cause, cache)
            || self.should_revisit_lower(cause, target, ep)
        {
            self.propagate_lower_to_uppers(target, ep, cause, cache);
        }
    }

    pub(super) fn constrain_pos_var_to(
        &self,
        source: TypeVar,
        neg: NegId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        let en = self.extrude_neg(neg, self.level_of(source));
        if self.add_upper_bound(source, en, cause, cache)
            || self.should_revisit_upper(cause, source, en)
        {
            self.propagate_upper_to_lowers(source, en, cause, cache);
        }
    }

    fn constrain_through_var_to_var(
        &self,
        pos: PosId,
        target: TypeVar,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        let ep = self.extrude_pos(pos, self.level_of(target));
        if self.add_lower(target, ep) {
            self.propagate_lower_to_uppers(target, ep, cause, cache);
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
