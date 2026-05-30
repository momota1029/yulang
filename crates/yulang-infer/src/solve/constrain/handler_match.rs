use std::collections::HashSet;

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
        self.record_handler_match_inner(actual, handled, residual, false, cause);
    }

    pub fn record_open_handler_match(
        &self,
        actual: TypeVar,
        handled: Vec<NegId>,
        residual: TypeVar,
        cause: ConstraintCause,
    ) {
        self.record_handler_match_inner(actual, handled, residual, true, cause);
    }

    fn record_handler_match_inner(
        &self,
        actual: TypeVar,
        handled: Vec<NegId>,
        residual: TypeVar,
        solve_open_rows: bool,
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
                solve_open_rows,
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

        let mut seen = HashSet::new();
        for lower in self.lower_refs_of(edge.actual) {
            for residual in
                self.solve_handler_match_pos_lower(&edge, lower, cause, cache, &mut seen)
            {
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
        seen: &mut HashSet<TypeVar>,
    ) -> Vec<PosId> {
        let lower = self.arena.get_pos(lower).clone();
        let Pos::Row(items, tail) = lower else {
            let Pos::Var(source) = lower else {
                return Vec::new();
            };
            if !seen.insert(source) {
                return Vec::new();
            }
            return self
                .lower_refs_of(source)
                .into_iter()
                .flat_map(|lower| {
                    self.solve_handler_match_pos_lower(edge, lower, cause, cache, seen)
                })
                .collect();
        };
        let mut kept = Vec::new();
        let mut removed_any = false;
        for item in &items {
            if let Some(handled) =
                self.capturing_handler_for_pos_item(&edge.keep, &edge.handled, *item)
            {
                removed_any = true;
                self.constrain_row_item_match(*item, handled, cause, cache);
            } else {
                kept.push(*item);
            }
        }
        if !edge.solve_open_rows && !matches!(self.arena.get_pos(tail), Pos::Bot) {
            return Vec::new();
        }
        removed_any
            .then(|| {
                if kept.is_empty() && !matches!(self.arena.get_pos(tail), Pos::Bot) {
                    tail
                } else {
                    self.arena.alloc_pos(Pos::Row(kept, tail))
                }
            })
            .into_iter()
            .collect()
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
    fn handler_match_subtracts_indirect_lower_row() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let source = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let atom = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        infer.constrain(Pos::Var(source), Neg::Var(actual));
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(atom.clone()))],
                infer.arena.alloc_pos(Pos::Var(tail)),
            ),
            Neg::Var(source),
        );

        infer.record_open_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(atom))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            infer.upper_refs_of(tail).into_iter().any(|upper| {
                matches!(infer.arena.get_neg(upper), Neg::Var(open_residual) if open_residual == residual)
            }),
            "handler_match should chase variable lower bounds before subtracting handled rows"
        );
    }

    #[test]
    fn handler_match_subtracts_indirect_through_lower_row() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let source = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let atom = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        infer.mark_through(tail);
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(atom.clone()))],
                infer.arena.alloc_pos(Pos::Var(tail)),
            ),
            Neg::Var(source),
        );
        infer.constrain(Pos::Var(source), Neg::Var(actual));

        infer.record_open_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(atom))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            infer.lower_refs_of(residual).into_iter().any(|lower| {
                matches!(infer.arena.get_pos(lower), Pos::Var(open_tail) if open_tail == tail)
            }),
            "handler_match should expose through tails as residual lower bounds"
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

    #[test]
    fn handler_match_subtracts_open_surface_row_to_tail() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let atom = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(atom.clone()))],
                infer.arena.alloc_pos(Pos::Var(tail)),
            ),
            Neg::Var(actual),
        );

        infer.record_open_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(atom))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            infer.upper_refs_of(tail).into_iter().any(|upper| {
                matches!(infer.arena.get_neg(upper), Neg::Var(open_residual) if open_residual == residual)
            }),
            "open surface subtraction should expose the row tail as the residual"
        );
    }

    #[test]
    fn handler_match_set_keep_subtracts_captured_path_to_tail() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let atom = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        infer.record_effect_boundary_keep(actual, ShiftKeep::Set(vec![path("io")]));
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(atom.clone()))],
                infer.arena.alloc_pos(Pos::Var(tail)),
            ),
            Neg::Var(actual),
        );

        infer.record_open_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(atom))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            infer.upper_refs_of(tail).into_iter().any(|upper| {
                matches!(infer.arena.get_neg(upper), Neg::Var(open_residual) if open_residual == residual)
            }),
            "a path-limited handler still exposes the source tail after subtracting a captured path"
        );
    }

    #[test]
    fn handler_match_keeps_open_surface_rows_pending_by_default() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let atom = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(atom.clone()))],
                infer.arena.alloc_pos(Pos::Var(tail)),
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
            infer.lower_refs_of(residual).is_empty(),
            "default handler_match should not solve from open surface rows"
        );
    }

    #[test]
    fn handler_match_constrains_atom_args_from_open_rows() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let actual_pos = fresh_type_var();
        let actual_neg = fresh_type_var();
        let handled_pos = fresh_type_var();
        let handled_neg = fresh_type_var();
        let effect_path = path("parse");

        infer.record_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(EffectAtom {
                path: effect_path.clone(),
                args: vec![(handled_pos, handled_neg)],
            }))],
            residual,
            ConstraintCause::unknown(),
        );
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(EffectAtom {
                    path: effect_path,
                    args: vec![(actual_pos, actual_neg)],
                }))],
                infer.arena.alloc_pos(Pos::Var(tail)),
            ),
            Neg::Var(actual),
        );

        assert!(
            infer.upper_refs_of(actual_pos).into_iter().any(|upper| {
                matches!(infer.arena.get_neg(upper), Neg::Var(tv) if tv == handled_neg)
            }),
            "matched atom args should connect the source pos side to the handler neg side"
        );
        assert!(
            infer.upper_refs_of(handled_pos).into_iter().any(|upper| {
                matches!(infer.arena.get_neg(upper), Neg::Var(tv) if tv == actual_neg)
            }),
            "matched atom args should connect the handler pos side to the source neg side"
        );
        assert!(
            infer.lower_refs_of(residual).is_empty(),
            "open surface rows still keep residual subtraction pending by default"
        );
    }

    fn path(name: &str) -> Path {
        Path {
            segments: vec![Name(name.to_string())],
        }
    }
}
