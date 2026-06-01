use super::{Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};
use crate::solve::EffectSubtractability;
use crate::types::Pos;

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
            if let Some(subtractability) = self.effect_lower_subtractability(pos, false) {
                self.record_effect_subtractability(target, subtractability);
            }
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

    fn effect_lower_subtractability(
        &self,
        pos: PosId,
        allow_var_metadata: bool,
    ) -> Option<EffectSubtractability> {
        match self.arena.get_pos(pos) {
            Pos::Atom(atom) => Some(EffectSubtractability::set(vec![atom.clone()])),
            Pos::Union(lhs, rhs) => union_subtractability(
                self.effect_lower_subtractability(lhs, true),
                self.effect_lower_subtractability(rhs, true),
            ),
            Pos::Row(items, tail) => {
                let mut out = self.effect_lower_subtractability(tail, true);
                for item in items {
                    out = union_subtractability(out, self.effect_lower_subtractability(item, true));
                }
                out
            }
            Pos::Var(tv) | Pos::Raw(tv) if allow_var_metadata => {
                if self.effect_is_all_subtractable(tv) {
                    Some(EffectSubtractability::All)
                } else {
                    self.effect_subtractability(tv)
                }
            }
            _ => None,
        }
    }
}

fn union_subtractability(
    lhs: Option<EffectSubtractability>,
    rhs: Option<EffectSubtractability>,
) -> Option<EffectSubtractability> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(lhs.union(rhs)),
        (Some(subtractability), None) | (None, Some(subtractability)) => Some(subtractability),
        (None, None) => None,
    }
}
