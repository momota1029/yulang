use super::{Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};

impl Infer {
    pub(super) fn add_lower_bound(
        &self,
        target: TypeVar,
        pos: PosId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) -> bool {
        let start = crate::profile::ProfileClock::now();
        let added = self.add_lower(target, pos);
        if added {
            self.solve_handler_matches_for(target, cause, cache);
        }
        self.record_profile(start, |profile, elapsed| {
            profile.add_lower_bound += elapsed;
        });
        added
    }

    pub(super) fn add_upper_bound(
        &self,
        source: TypeVar,
        neg: NegId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) -> bool {
        let start = crate::profile::ProfileClock::now();
        let added = self.add_upper(source, neg);
        if added {
            self.solve_handler_matches_for(source, cause, cache);
        }
        self.record_profile(start, |profile, elapsed| {
            profile.add_upper_bound += elapsed;
        });
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
}
