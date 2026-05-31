use super::{Infer, StepCache};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, TypeVar};
use crate::solve::{HandlerMatchEdge, ShiftKeep};
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
        let mut cache = StepCache::default();
        let residual_tail = self.arena.alloc_neg(Neg::Var(residual));
        let upper = if handled.is_empty() {
            residual_tail
        } else {
            self.arena
                .alloc_neg(Neg::Row(handled.clone(), residual_tail))
        };

        {
            let mut edges = self.handler_matches.borrow_mut();
            edges.push(HandlerMatchEdge {
                actual,
                keep,
                handled,
                residual,
                solve_open_rows,
                cause: cause.clone(),
            });
        }

        self.constrain_step(
            self.arena.alloc_pos(Pos::Var(actual)),
            upper,
            &cause,
            &mut cache,
        );
    }

    pub(super) fn solve_handler_matches_for(
        &self,
        actual: TypeVar,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        let _ = (actual, cause, cache);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostic::ConstraintCause;
    use crate::fresh_type_var;
    use crate::symbols::{Name, Path};
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
            has_handler_row_upper(&infer, actual, residual, "io"),
            "handler_match should encode subtraction as an ordinary row upper bound"
        );
        assert!(
            infer.lower_refs_of(residual).is_empty(),
            "closed empty residual is represented by bottom, not by a synthetic empty row lower"
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
            tail_flows_to_residual(&infer, tail, residual),
            "ordinary row constraints should propagate an open tail to the residual"
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
            tail_flows_to_residual(&infer, tail, residual),
            "open surface subtraction should be handled by row decomposition"
        );
    }

    #[test]
    fn handler_match_passes_unhandled_open_row_items_to_residual() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        let tail = fresh_type_var();
        let handled = EffectAtom {
            path: path("io"),
            args: Vec::new(),
        };
        let unhandled = EffectAtom {
            path: path("outer"),
            args: Vec::new(),
        };
        infer.constrain(
            Pos::Row(
                vec![infer.arena.alloc_pos(Pos::Atom(unhandled.clone()))],
                infer.arena.alloc_pos(Pos::Var(tail)),
            ),
            Neg::Var(actual),
        );

        infer.record_open_handler_match(
            actual,
            vec![infer.arena.alloc_neg(Neg::Atom(handled))],
            residual,
            ConstraintCause::unknown(),
        );

        assert!(
            infer.lower_refs_of(residual).into_iter().any(|lower| {
                matches!(
                    infer.arena.get_pos(lower),
                    Pos::Row(items, row_tail)
                        if items.iter().any(|item| matches!(
                            infer.arena.get_pos(*item),
                            Pos::Atom(atom) if atom == unhandled
                        )) && matches!(infer.arena.get_pos(row_tail), Pos::Var(tv) if tv == tail)
                )
            }),
            "open handler_match must pass unhandled row items through to the residual"
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
            tail_flows_to_residual(&infer, tail, residual),
            "boundary keep metadata should not change the ordinary row constraint"
        );
        assert!(
            matches!(
                infer.handler_matches.borrow().first().map(|edge| &edge.keep),
                Some(ShiftKeep::Set(paths)) if paths == &vec![path("io")]
            ),
            "boundary keep should remain available as exported evidence"
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

    fn has_handler_row_upper(
        infer: &Infer,
        actual: crate::ids::TypeVar,
        residual: crate::ids::TypeVar,
        path_name: &str,
    ) -> bool {
        infer.upper_refs_of(actual).into_iter().any(|upper| {
            let Neg::Row(items, tail) = infer.arena.get_neg(upper) else {
                return false;
            };
            matches!(infer.arena.get_neg(tail), Neg::Var(tv) if tv == residual)
                && items.iter().any(|item| {
                    matches!(
                        infer.arena.get_neg(*item),
                        Neg::Atom(atom) if atom.path == path(path_name)
                    )
                })
        })
    }

    fn tail_flows_to_residual(
        infer: &Infer,
        tail: crate::ids::TypeVar,
        residual: crate::ids::TypeVar,
    ) -> bool {
        infer
            .upper_refs_of(tail)
            .into_iter()
            .any(|upper| match infer.arena.get_neg(upper) {
                Neg::Var(tv) => tv == residual,
                Neg::Row(items, row_tail) => {
                    items.is_empty()
                        && matches!(infer.arena.get_neg(row_tail), Neg::Var(tv) if tv == residual)
                }
                _ => false,
            })
    }
}
