use super::{Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};
use crate::solve::{HandlerMatchEdge, ShiftKeep};
use crate::symbols::Path;
use crate::types::{Neg, Pos};

impl Infer {
    pub fn record_effect_boundary_keep(&self, effect: TypeVar, keep: ShiftKeep) {
        self.effect_boundary_keeps.borrow_mut().insert(effect, keep);
    }

    pub fn effect_boundary_keep(&self, effect: TypeVar) -> ShiftKeep {
        self.effect_boundary_keeps
            .borrow()
            .get(&effect)
            .cloned()
            .unwrap_or(ShiftKeep::Surface)
    }

    pub fn record_handler_match(
        &self,
        actual: TypeVar,
        handled: Vec<NegId>,
        residual: TypeVar,
        cause: ConstraintCause,
    ) {
        let keep = self.effect_boundary_keep(actual);
        let captures_any = handled
            .iter()
            .any(|handled| self.shift_keep_captures_neg(&keep, *handled));

        if handled.is_empty() || !captures_any {
            self.constrain(Pos::Var(actual), Neg::Var(residual));
        }

        let index = {
            let mut edges = self.handler_matches.borrow_mut();
            let index = edges.len();
            edges.push(HandlerMatchEdge {
                actual,
                keep,
                handled,
                residual,
                cause: cause.clone(),
            });
            index
        };
        self.handler_match_dependents
            .borrow_mut()
            .entry(actual)
            .or_default()
            .push(index);

        let mut cache = StepCache::default();
        self.solve_handler_match_edge(index, &cause, &mut cache);
    }

    pub(super) fn solve_handler_matches_for(
        &self,
        actual: TypeVar,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        let dependents = self
            .handler_match_dependents
            .borrow()
            .get(&actual)
            .cloned()
            .unwrap_or_default();
        for edge in dependents {
            self.solve_handler_match_edge(edge, cause, cache);
        }
    }

    fn solve_handler_match_edge(
        &self,
        index: usize,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        let Some(edge) = self.handler_matches.borrow().get(index).cloned() else {
            return;
        };

        for lower in self.lower_refs_of(edge.actual) {
            if let Some(residual) = self.solve_handler_match_pos_lower(&edge, lower, cause, cache) {
                self.constrain_step_with_hint(
                    residual,
                    self.arena.alloc_neg(Neg::Var(edge.residual)),
                    cause,
                    Some(edge.actual),
                    cache,
                );
            }
        }

        // Do not solve from upper bounds or compact instances yet. Those are
        // summary views, not a concrete source surface, and using them here
        // would make handler_match invent residual row shape indirectly.
    }

    fn solve_handler_match_pos_lower(
        &self,
        edge: &HandlerMatchEdge,
        lower: PosId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) -> Option<PosId> {
        if matches!(edge.keep, ShiftKeep::Set(_)) {
            return None;
        }
        let Pos::Row(items, tail) = self.arena.get_pos(lower) else {
            return None;
        };
        if !matches!(self.arena.get_pos(tail), Pos::Bot) {
            return None;
        }
        let mut kept = Vec::new();
        let mut removed_any = false;
        for item in items {
            if let Some(handled) =
                self.capturing_handler_for_pos_item(&edge.keep, &edge.handled, item)
            {
                removed_any = true;
                self.constrain_row_item_match(item, handled, cause, cache);
            } else {
                kept.push(item);
            }
        }
        removed_any.then(|| self.arena.alloc_pos(Pos::Row(kept, tail)))
    }

    fn capturing_handler_for_pos_item(
        &self,
        keep: &ShiftKeep,
        handled: &[NegId],
        item: PosId,
    ) -> Option<NegId> {
        let Pos::Atom(pos_atom) = self.arena.get_pos(item) else {
            return None;
        };
        if !pos_atom.args.is_empty() {
            return None;
        }
        handled.iter().copied().find(|handled| {
            self.shift_keep_captures_neg(keep, *handled)
                && matches!(
                    self.arena.get_neg(*handled),
                    Neg::Atom(neg_atom)
                        if neg_atom.path == pos_atom.path
                            && neg_atom.args.len() == pos_atom.args.len()
                )
        })
    }

    fn shift_keep_captures_neg(&self, keep: &ShiftKeep, handled: NegId) -> bool {
        match keep {
            ShiftKeep::None | ShiftKeep::CallBoundary => false,
            ShiftKeep::Surface => true,
            ShiftKeep::Set(paths) => self
                .neg_effect_path(handled)
                .is_some_and(|path| paths.iter().any(|allowed| allowed == &path)),
        }
    }

    fn neg_effect_path(&self, handled: NegId) -> Option<Path> {
        match self.arena.get_neg(handled) {
            Neg::Atom(atom) => Some(atom.path),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostic::ConstraintCause;
    use crate::fresh_type_var;
    use crate::symbols::Name;
    use crate::types::EffectAtom;

    #[test]
    fn handler_match_subtracts_closed_surface_row() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        let atom = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(atom.clone()))],
                infer.arena.bot,
            ),
            Neg::Var(actual),
        );

        infer.record_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(atom))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            infer.lower_refs_of(residual).into_iter().any(|lower| {
                matches!(
                    infer.arena.get_pos(lower),
                    Pos::Row(items, tail)
                        if items.is_empty() && matches!(infer.arena.get_pos(tail), Pos::Bot)
                )
            }),
            "closed surface subtraction should add an empty residual row"
        );
    }

    #[test]
    fn handler_match_does_not_open_naked_actual_var() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();

        infer.record_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(EffectAtom {
                path: path("io"),
                args: Vec::new(),
            }))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            infer.lower_refs_of(residual).is_empty(),
            "naked handler_match actual must stay pending"
        );
    }

    fn path(name: &str) -> Path {
        Path {
            segments: vec![Name(name.to_string())],
        }
    }
}
