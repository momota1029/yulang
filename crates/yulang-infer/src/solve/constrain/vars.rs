use super::{Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};
use crate::solve::EffectSubtractability;
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
        if std::env::var_os("YULANG_DEBUG_VAR_CONSTRAINTS").is_some() {
            eprintln!(
                "VAR_CONSTRAINT {:?} <: {:?} cause={:?}",
                source, target, cause
            );
        }
        if source != target {
            self.constrain_eff_bind_source_lowers_to_var(source, target, cause, cache);
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
        if self.constrain_eff_bind_lower_to_var(pos, target, cause, cache) {
            return;
        }
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
    ) -> bool {
        self.constrain_eff_bind_lower_to_var_with_subtractability(
            pos,
            target,
            self.effect_subtractability(target),
            cause,
            cache,
        )
    }

    fn row_upper_mentions_bound_effect(&self, neg_items: &[NegId], target: TypeVar) -> bool {
        let handled = self.eff_binds_of(target);
        neg_items
            .iter()
            .any(|item| match self.arena.get_neg(*item) {
                Neg::Atom(atom) => handled
                    .iter()
                    .any(|bound| atom.path == bound.path && atom.args.len() == bound.args.len()),
                _ => false,
            })
    }

    fn project_eff_bind_target_items(
        &self,
        subtractability: Option<EffectSubtractability>,
        items: Vec<PosId>,
    ) -> Vec<PosId> {
        match subtractability {
            Some(EffectSubtractability::All) => items,
            Some(EffectSubtractability::Set(paths)) => items
                .into_iter()
                .filter(|item| match self.arena.get_pos(*item) {
                    Pos::Atom(atom) => paths.iter().any(|path| path == &atom.path),
                    _ => true,
                })
                .collect(),
            Some(EffectSubtractability::Empty) | None => Vec::new(),
        }
    }

    fn closed_row_lower(&self, items: Vec<PosId>) -> PosId {
        if items.is_empty() {
            self.arena.bot
        } else {
            self.arena.alloc_pos(Pos::Row(items, self.arena.bot))
        }
    }

    fn open_row_lower(&self, items: Vec<PosId>, tail: PosId) -> Option<PosId> {
        if items.is_empty() {
            return (!self.eff_bind_pos_tail_is_empty_row(tail)).then_some(tail);
        }
        Some(self.arena.alloc_pos(Pos::Row(items, tail)))
    }

    fn eff_bind_pos_tail_is_empty_row(&self, tail: PosId) -> bool {
        match self.arena.get_pos(tail) {
            Pos::Bot => true,
            Pos::Row(items, row_tail) if items.is_empty() => {
                self.eff_bind_pos_tail_is_empty_row(row_tail)
            }
            Pos::Row(items, row_tail) => {
                items.is_empty() && self.eff_bind_pos_tail_is_empty_row(row_tail)
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
            self.constrain_eff_bind_lower_to_var_with_subtractability(
                lower,
                target,
                self.effect_subtractability(target),
                cause,
                cache,
            );
        }
    }

    fn constrain_eff_bind_lower_to_var_with_subtractability(
        &self,
        pos: PosId,
        target: TypeVar,
        subtractability: Option<EffectSubtractability>,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) -> bool {
        let handled = self.eff_binds_of(target);
        if handled.is_empty() {
            return false;
        }
        let Pos::Row(pos_items, pos_tail) = self.arena.get_pos(pos).clone() else {
            return false;
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

        let target_items = self.project_eff_bind_target_items(subtractability, unmatched.clone());
        let target_residual = self.closed_row_lower(target_items);
        if !matched.is_empty() || !self.eff_bind_pos_tail_is_empty_row(target_residual) {
            let transformed = if matched.is_empty() {
                target_residual
            } else {
                self.arena.alloc_pos(Pos::Row(matched, target_residual))
            };
            if self.add_lower_bound(target, transformed, cause, cache)
                || self.should_revisit_lower(cause, target, transformed)
            {
                self.propagate_lower_to_uppers(target, transformed, cause, cache);
            }
        }

        let residual = self.open_row_lower(unmatched, pos_tail);
        let Some(residual) = residual else {
            return true;
        };

        for upper in self.upper_refs_of(target) {
            let Neg::Row(neg_items, neg_tail) = self.arena.get_neg(upper).clone() else {
                continue;
            };
            if !self.row_upper_mentions_bound_effect(&neg_items, target) {
                continue;
            }
            self.constrain_step(residual, neg_tail, cause, cache);
        }

        true
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

    fn should_revisit_lower(&self, cause: &ConstraintCause, target: TypeVar, pos: PosId) -> bool {
        super::errors::should_revisit_existing_constraint(cause)
            && self.lower_members.borrow().contains(&(target, pos))
    }

    fn should_revisit_upper(&self, cause: &ConstraintCause, source: TypeVar, neg: NegId) -> bool {
        super::errors::should_revisit_existing_constraint(cause)
            && self.upper_members.borrow().contains(&(source, neg))
    }
}
