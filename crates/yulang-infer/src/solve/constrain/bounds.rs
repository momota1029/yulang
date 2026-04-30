use super::{Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};
use crate::types::{Neg, Pos};

impl Infer {
    pub(super) fn add_lower_bound(
        &self,
        target: TypeVar,
        pos: PosId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) -> bool {
        let added = self.add_lower(target, pos);
        if added {
            self.update_through_after_lower(target, pos, cause, cache);
        }
        added
    }

    pub(super) fn add_upper_bound(
        &self,
        source: TypeVar,
        neg: NegId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) -> bool {
        let added = self.add_upper(source, neg);
        if added {
            if let Neg::Var(target) = self.arena.get_neg(neg) {
                self.propagate_through(source, target, cause, cache);
            }
        }
        added
    }

    pub(super) fn propagate_lower_to_uppers(
        &self,
        target: TypeVar,
        pos: PosId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        for upper in self.upper_refs_of(target) {
            self.constrain_step_with_hint(pos, upper, cause, Some(target), cache);
        }
    }

    pub(super) fn propagate_upper_to_lowers(
        &self,
        source: TypeVar,
        neg: NegId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        for lower in self.lower_refs_of(source) {
            self.constrain_step_with_hint(lower, neg, cause, Some(source), cache);
        }
        for instance in self.compact_lower_instances_of(source) {
            self.constrain_compact_instance_to_neg(&instance, neg, cause, Some(source), cache);
        }
    }

    pub(super) fn update_through_after_lower(
        &self,
        target: TypeVar,
        pos: PosId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        if let Pos::Var(source) = self.arena.get_pos(pos) {
            if !self.is_through(source) {
                self.clear_through(target);
            }
            self.propagate_through(source, target, cause, cache);
        } else if !self.lower_preserves_through_id(pos) {
            self.clear_through(target);
        }
    }
}
