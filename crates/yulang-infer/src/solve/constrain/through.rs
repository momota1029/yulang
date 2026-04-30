use super::util::{neg_id_direct_var, pos_id_direct_var};
use super::{Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};
use crate::types::{Neg, Pos};

impl Infer {
    pub(super) fn propagate_through(
        &self,
        from: TypeVar,
        to: TypeVar,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        if self.is_through(from) && !self.is_through(to) {
            self.mark_through(to);
            for upper in self.upper_refs_of(to) {
                if let Neg::Row(_, tail) = self.arena.get_neg(upper) {
                    let var_pos = self.arena.alloc_pos(Pos::Var(to));
                    self.constrain_step(var_pos, tail, cause, cache);
                }
            }
        }
    }

    pub(super) fn lower_preserves_through_id(&self, pos: PosId) -> bool {
        match self.arena.get_pos(pos) {
            Pos::Bot => true,
            Pos::Row(items, tail) if items.is_empty() => match self.arena.get_pos(tail) {
                Pos::Bot => true,
                Pos::Var(tv) | Pos::Raw(tv) => self.is_through(tv),
                _ => self.lower_preserves_through_id(tail),
            },
            Pos::Union(lhs, rhs) => {
                self.lower_preserves_through_id(lhs) && self.lower_preserves_through_id(rhs)
            }
            _ => false,
        }
    }

    pub(super) fn propagate_invariant_arg_through(
        &self,
        pp: PosId,
        pn: NegId,
        np: PosId,
        nn: NegId,
    ) {
        let vars = [
            pos_id_direct_var(&self.arena.get_pos(pp)),
            neg_id_direct_var(&self.arena.get_neg(pn)),
            pos_id_direct_var(&self.arena.get_pos(np)),
            neg_id_direct_var(&self.arena.get_neg(nn)),
        ];
        if vars.into_iter().flatten().any(|tv| self.is_through(tv)) {
            for tv in vars.into_iter().flatten() {
                self.mark_through(tv);
            }
        }
    }
}
