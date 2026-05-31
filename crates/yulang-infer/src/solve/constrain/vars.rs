use super::{Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};
use crate::types::{EffectAtom, Neg, Pos};

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
        if source != target {
            self.constrain_eff_bind_source_lowers_to_var(source, target, cause, cache);
        }

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
        self.constrain_eff_bind_lower_to_var(pos, target, cause, cache);
        let ep = self.extrude_pos(pos, self.level_of(target));
        if self.add_lower_bound(target, ep, cause, cache)
            || self.should_revisit_lower(cause, target, ep)
        {
            self.propagate_lower_to_uppers(target, ep, cause, cache);
        }
    }

    fn constrain_eff_bind_lower_to_var(
        &self,
        pos: PosId,
        target: TypeVar,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        let handled = self.eff_binds_of(target);
        if handled.is_empty() {
            return;
        }
        let Pos::Row(pos_items, pos_tail) = self.arena.get_pos(pos).clone() else {
            return;
        };

        let mut matched = Vec::new();
        let mut unmatched = pos_items;
        for handled_atom in handled {
            if let Some(index) = unmatched.iter().position(|pos_item| {
                self.effect_row_item_matches_bound_atom(*pos_item, &handled_atom)
            }) {
                let pos_item = unmatched.remove(index);
                let neg_item = self.arena.alloc_neg(Neg::Atom(handled_atom));
                self.constrain_row_item_match(pos_item, neg_item, cause, cache);
                matched.push(pos_item);
            }
        }

        if matched.is_empty() {
            return;
        }

        let transformed_tail = if unmatched.is_empty() {
            self.arena.empty_pos_row
        } else {
            self.arena
                .alloc_pos(Pos::Row(unmatched.clone(), self.arena.bot))
        };
        let transformed = self.arena.alloc_pos(Pos::Row(matched, transformed_tail));
        if self.add_lower_bound(target, transformed, cause, cache)
            || self.should_revisit_lower(cause, target, transformed)
        {
            self.propagate_lower_to_uppers(target, transformed, cause, cache);
        }

        for upper in self.upper_refs_of(target) {
            let Neg::Row(neg_items, neg_tail) = self.arena.get_neg(upper).clone() else {
                continue;
            };
            if neg_items.is_empty() {
                continue;
            }

            let mut matched_this_row = false;
            for neg_item in neg_items {
                if let Some(index) = unmatched
                    .iter()
                    .position(|pos_item| self.effect_row_items_match(*pos_item, neg_item))
                {
                    let pos_item = unmatched.remove(index);
                    self.constrain_row_item_match(pos_item, neg_item, cause, cache);
                    matched_this_row = true;
                }
            }
            if !matched_this_row {
                continue;
            }

            let residual = if unmatched.is_empty() {
                pos_tail
            } else {
                self.arena.alloc_pos(Pos::Row(unmatched.clone(), pos_tail))
            };
            self.constrain_step(residual, neg_tail, cause, cache);
        }
    }

    fn effect_row_items_match(&self, pos: PosId, neg: NegId) -> bool {
        match (self.arena.get_pos(pos), self.arena.get_neg(neg)) {
            (Pos::Atom(pos_atom), Neg::Atom(neg_atom)) => {
                pos_atom.path == neg_atom.path && pos_atom.args.len() == neg_atom.args.len()
            }
            _ => false,
        }
    }

    fn effect_row_item_matches_bound_atom(&self, pos: PosId, bound: &EffectAtom) -> bool {
        match self.arena.get_pos(pos) {
            Pos::Atom(pos_atom) => {
                pos_atom.path == bound.path && pos_atom.args.len() == bound.args.len()
            }
            _ => false,
        }
    }

    fn constrain_eff_bind_source_lowers_to_var(
        &self,
        source: TypeVar,
        target: TypeVar,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        if !self.is_eff_bound(target) {
            return;
        }
        for lower in self.lower_refs_of(source) {
            self.constrain_eff_bind_lower_to_var(lower, target, cause, cache);
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
