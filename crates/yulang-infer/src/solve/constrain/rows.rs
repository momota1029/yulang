use super::util::same_row_tail_var_nodes;
use super::{Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};
use crate::types::{Neg, Pos};

impl Infer {
    pub(super) fn constrain_row_item_to_row(
        &self,
        pos: PosId,
        neg_items: Vec<NegId>,
        neg_tail: NegId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        if let Some(matched) = neg_items
            .into_iter()
            .find(|&item| self.row_items_can_cancel(pos, item))
        {
            self.constrain_row_item_match(pos, matched, cause, cache);
            return;
        }
        self.constrain_step(pos, neg_tail, cause, cache);
    }

    pub(super) fn constrain_row(
        &self,
        pos_items: Vec<PosId>,
        pos_tail: PosId,
        neg_items: Vec<NegId>,
        neg_tail: NegId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        let original_neg_items = neg_items.clone();
        let original_neg_tail = neg_tail;
        let mut pos_diff = pos_items;
        let mut neg_unmatched: Vec<NegId> = Vec::new();

        for item in neg_items {
            if let Some(idx) = pos_diff
                .iter()
                .position(|&candidate| self.row_items_can_cancel(candidate, item))
            {
                let matched = pos_diff.remove(idx);
                self.constrain_row_item_match(matched, item, cause, cache);
            } else {
                neg_unmatched.push(item);
            }
        }

        let mut concrete_diff: Vec<PosId> = Vec::new();
        for item in pos_diff {
            match self.arena.get_pos(item) {
                Pos::Var(tv) | Pos::Raw(tv) => {
                    self.constrain_row_var_to_row(
                        tv,
                        original_neg_items.clone(),
                        original_neg_tail,
                        cause,
                        cache,
                    );
                }
                _ => concrete_diff.push(item),
            }
        }

        let pos_tail_node = self.arena.get_pos(pos_tail);
        let neg_tail_node = self.arena.get_neg(neg_tail);
        let tail_is_var = matches!(pos_tail_node, Pos::Var(_) | Pos::Raw(_));
        let concrete_tail = if tail_is_var {
            self.arena.bot
        } else {
            pos_tail
        };

        if !concrete_diff.is_empty() && !same_row_tail_var_nodes(&pos_tail_node, &neg_tail_node) {
            let residual = self.pos_effect_union(concrete_diff, concrete_tail);
            self.constrain_step(residual, neg_tail, cause, cache);
        }

        match pos_tail_node {
            Pos::Var(tv) | Pos::Raw(tv) => self.constrain_row_var_to_row(
                tv,
                neg_unmatched,
                original_neg_tail,
                cause,
                cache,
            ),
            _ => {
                let neg_row = self.arena.alloc_neg(Neg::Row(neg_unmatched, neg_tail));
                self.constrain_step(pos_tail, neg_row, cause, cache);
            }
        }
    }

    fn constrain_row_var_to_row(
        &self,
        tv: TypeVar,
        neg_items: Vec<NegId>,
        neg_tail: NegId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        let pos = self.arena.alloc_pos(Pos::Var(tv));
        let neg = self.arena.alloc_neg(Neg::Row(neg_items, neg_tail));
        self.constrain_step(pos, neg, cause, cache);
    }

    fn row_items_can_cancel(&self, pos: PosId, neg: NegId) -> bool {
        let result = match (self.arena.get_pos(pos), self.arena.get_neg(neg)) {
            (Pos::Atom(pa), Neg::Atom(na)) => pa.path == na.path && pa.args.len() == na.args.len(),
            (Pos::Var(a), Neg::Var(b)) => a == b,
            (Pos::Bot, Neg::Top) => true,
            _ => false,
        };
        if std::env::var("YULANG_DBG").is_ok() {
            let pos_desc = match self.arena.get_pos(pos) {
                Pos::Atom(a) => format!("atom{:?}", a.path.segments),
                Pos::Var(t) | Pos::Raw(t) => format!("var{}", t.0),
                other => format!("{other:?}"),
            };
            let neg_desc = match self.arena.get_neg(neg) {
                Neg::Atom(a) => format!("atom{:?}", a.path.segments),
                Neg::Var(t) => format!("var{}", t.0),
                other => format!("{other:?}"),
            };
            eprintln!("[can_cancel] pos={pos_desc} vs neg={neg_desc} -> {result}");
        }
        result
    }

    pub(super) fn constrain_row_item_match(
        &self,
        pos: PosId,
        neg: NegId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        let pos_node = self.arena.get_pos(pos);
        let neg_node = self.arena.get_neg(neg);
        match (pos_node, neg_node) {
            (Pos::Atom(pos_atom), Neg::Atom(neg_atom))
                if pos_atom.path == neg_atom.path && pos_atom.args.len() == neg_atom.args.len() =>
            {
                for ((pos_pos, pos_neg), (neg_pos, neg_neg)) in
                    pos_atom.args.into_iter().zip(neg_atom.args)
                {
                    let pp = self.arena.alloc_pos(Pos::Var(pos_pos));
                    let nn = self.arena.alloc_neg(Neg::Var(neg_neg));
                    self.constrain_step(pp, nn, cause, cache);
                    let np = self.arena.alloc_pos(Pos::Var(neg_pos));
                    let pn = self.arena.alloc_neg(Neg::Var(pos_neg));
                    self.constrain_step(np, pn, cause, cache);
                }
            }
            _ => {}
        }
    }
}
