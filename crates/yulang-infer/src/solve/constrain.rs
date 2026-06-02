use rustc_hash::FxHashSet;

use super::{Infer, IntoNegId, IntoPosId};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};
use crate::scheme::OwnedSchemeInstance;
use crate::types::{Neg, Pos};

mod bounds;
mod compact;
mod errors;
pub(crate) mod extrude;
mod frozen;
mod handler_match;
mod records;
mod rows;
mod shape;
mod util;
mod vars;

enum RowUpperProjection {
    Original,
    Project(Vec<NegId>),
    TailOnly,
}

#[derive(Debug, Default)]
struct StepCache {
    seen: FxHashSet<(PosId, NegId)>,
    pending: Vec<ConstraintStep>,
    depth: usize,
}

#[derive(Debug, Clone, Copy)]
struct ConstraintStep {
    pos: PosId,
    neg: NegId,
    origin_hint: Option<TypeVar>,
}

type FrozenStepCache = FxHashSet<(usize, PosId, NegId)>;
const MAX_INLINE_CONSTRAINT_DEPTH: usize = 128;

impl Infer {
    // ── constrain ────────────────────────────────────────────────────────────

    /// pos <: neg の制約を追加し、推移的に伝播させる。
    pub fn constrain<P: IntoPosId, N: IntoNegId>(&self, pos: P, neg: N) {
        let pos = pos.into_pos_id(self);
        let neg = neg.into_neg_id(self);
        self.constrain_with_cause(pos, neg, ConstraintCause::unknown());
    }

    pub fn constrain_with_cause<P: IntoPosId, N: IntoNegId>(
        &self,
        pos: P,
        neg: N,
        cause: ConstraintCause,
    ) {
        let start = crate::profile::ProfileClock::now();
        let pos = pos.into_pos_id(self);
        let neg = neg.into_neg_id(self);
        let mut cache = StepCache::default();
        self.constrain_step(pos, neg, &cause, &mut cache);
        self.record_profile(start, |profile, elapsed| {
            profile.constrain += elapsed;
        });
    }

    pub fn constrain_instantiated_ref(&self, pos: PosId, target: TypeVar) {
        let start = crate::profile::ProfileClock::now();
        let cause = ConstraintCause::unknown();
        let pos = self.extrude_pos(pos, self.level_of(target));
        let mut cache = StepCache::default();
        if self.add_lower_bound(target, pos, &cause, &mut cache) {
            let uppers = self.upper_refs_of(target);
            if !uppers.is_empty() {
                for upper in uppers {
                    self.constrain_step_with_hint(pos, upper, &cause, Some(target), &mut cache);
                }
            }
        }
        self.record_profile(start, |profile, elapsed| {
            profile.constrain_instantiated_ref += elapsed;
        });
    }

    pub fn constrain_instantiated_ref_instance(
        &self,
        instance: OwnedSchemeInstance,
        target: TypeVar,
    ) {
        let start = crate::profile::ProfileClock::now();
        let cause = ConstraintCause::unknown();
        let target_lvl = self.level_of(target);
        if self.max_level_scheme_instance(&instance) > target_lvl {
            let body = self.materialize_compact_lower_instance(&instance);
            self.constrain_instantiated_ref(body, target);
            self.constrain_instantiated_ref_root_uppers(&instance, target, &cause);
            self.record_profile(start, |profile, elapsed| {
                profile.constrain_instantiated_ref_instance += elapsed;
            });
            return;
        }
        if self.add_compact_lower_instance(target, instance.clone()) {
            {
                let mut cache = StepCache::default();
                self.solve_handler_matches_for(target, &cause, &mut cache);
            }

            let uppers = self.upper_refs_of(target);
            if !uppers.is_empty() {
                let mut cache = FxHashSet::default();
                for upper in uppers {
                    self.constrain_frozen_instance_to_neg(
                        &instance,
                        upper,
                        &cause,
                        Some(target),
                        &mut cache,
                    );
                }
            }
            self.constrain_instantiated_ref_root_uppers(&instance, target, &cause);
        }
        self.record_profile(start, |profile, elapsed| {
            profile.constrain_instantiated_ref_instance += elapsed;
        });
    }

    fn constrain_instantiated_ref_root_uppers(
        &self,
        instance: &OwnedSchemeInstance,
        target: TypeVar,
        cause: &ConstraintCause,
    ) {
        let mut cache = StepCache::default();
        for upper in self.compact_instance_root_upper_parts(instance) {
            if self.add_upper_bound(target, upper, cause, &mut cache) {
                self.propagate_upper_to_lowers(target, upper, cause, &mut cache);
            }
        }
    }

    fn constrain_step(
        &self,
        pos: PosId,
        neg: NegId,
        cause: &ConstraintCause,
        cache: &mut StepCache,
    ) {
        self.constrain_step_with_hint(pos, neg, cause, None, cache);
    }

    fn constrain_step_with_hint(
        &self,
        pos: PosId,
        neg: NegId,
        cause: &ConstraintCause,
        origin_hint: Option<TypeVar>,
        cache: &mut StepCache,
    ) {
        if !cache.seen.insert((pos, neg)) {
            return;
        }
        cache.pending.push(ConstraintStep {
            pos,
            neg,
            origin_hint,
        });
        if cache.depth >= MAX_INLINE_CONSTRAINT_DEPTH {
            return;
        }

        while let Some(step) = cache.pending.pop() {
            cache.depth += 1;
            self.constrain_step_now(step.pos, step.neg, cause, step.origin_hint, cache);
            cache.depth -= 1;
            if cache.depth > 0 {
                break;
            }
        }
    }

    fn constrain_step_now(
        &self,
        pos: PosId,
        neg: NegId,
        cause: &ConstraintCause,
        origin_hint: Option<TypeVar>,
        cache: &mut StepCache,
    ) {
        let pos_node = self.arena.get_pos(pos);
        let neg_node = self.arena.get_neg(neg);
        match (pos_node, neg_node) {
            (Pos::Var(a), Neg::Var(b)) if a == b => {}
            (Pos::Bot, _) | (_, Neg::Top) => {}
            (Pos::Forall(..), _) | (_, Neg::Forall(..)) => {}

            // Union / Intersection を分配
            (Pos::Union(a, b), _) => {
                self.constrain_step(a, neg, cause, cache);
                self.constrain_step(b, neg, cause, cache);
            }
            (_, Neg::Intersection(a, b)) => {
                self.constrain_step(pos, a, cause, cache);
                self.constrain_step(pos, b, cause, cache);
            }

            (Pos::Var(a), Neg::Var(b)) => {
                self.constrain_var_to_var(pos, a, neg, b, cause, cache);
            }
            (_, Neg::Var(b)) => {
                self.constrain_to_neg_var(pos, b, cause, cache);
            }
            (Pos::Var(a) | Pos::Raw(a), Neg::Row(items, tail)) => {
                match self.row_upper_projection(a, &items, tail, origin_hint) {
                    RowUpperProjection::Original => {
                        self.constrain_pos_var_to(a, neg, cause, cache);
                    }
                    RowUpperProjection::Project(projected_items) => {
                        let projected = self.arena.alloc_neg(Neg::Row(projected_items, tail));
                        self.constrain_pos_var_to(a, projected, cause, cache);
                    }
                    RowUpperProjection::TailOnly => {
                        self.constrain_step(pos, tail, cause, cache);
                    }
                }
            }
            (Pos::Atom(_), Neg::Row(items, tail)) => {
                self.constrain_row_item_to_row(pos, items, tail, cause, cache);
            }
            (Pos::Var(a), _) => {
                self.constrain_pos_var_to(a, neg, cause, cache);
            }

            _ => self.constrain_shape(pos, neg, cause, origin_hint, cache),
        }
    }

    fn row_upper_projection(
        &self,
        effect: TypeVar,
        items: &[NegId],
        tail: NegId,
        _origin_hint: Option<TypeVar>,
    ) -> RowUpperProjection {
        if !items.is_empty()
            && let Neg::Var(tail_var) = self.arena.get_neg(tail)
        {
            self.copy_effect_subtractability(effect, tail_var);
        }

        match self.effect_subtractability(effect) {
            Some(super::EffectSubtractability::All) if !items.is_empty() => {
                RowUpperProjection::Original
            }
            Some(super::EffectSubtractability::All) => RowUpperProjection::TailOnly,
            Some(
                subtractability @ (super::EffectSubtractability::AllExcept(_)
                | super::EffectSubtractability::Set(_)),
            ) => {
                let projected = items
                    .iter()
                    .copied()
                    .filter(|item| {
                        matches!(self.arena.get_neg(*item), Neg::Atom(atom) if subtractability.allows_atom_family(&atom))
                    })
                    .collect::<Vec<_>>();
                if projected.is_empty() {
                    RowUpperProjection::TailOnly
                } else {
                    RowUpperProjection::Project(projected)
                }
            }
            Some(super::EffectSubtractability::Empty) => RowUpperProjection::TailOnly,
            None if !items.is_empty() => RowUpperProjection::Original,
            None => RowUpperProjection::TailOnly,
        }
    }
}

#[cfg(test)]
mod tests {
    use rowan::TextRange;

    use crate::diagnostic::{
        ConstraintCause, ConstraintReason, ExpectedShape, TypeErrorKind, TypeOrigin, TypeOriginKind,
    };
    use crate::ids::{NegId, fresh_type_var};
    use crate::solve::{EffectSubtractability, Infer};
    use crate::symbols::{Name, Path};
    use crate::types::RecordField;
    use crate::types::{EffectAtom, Neg, Pos};

    #[test]
    fn constructor_mismatch_reports_cause_and_origin() {
        let infer = Infer::new();
        let tv = fresh_type_var();
        infer.register_level(tv, 0);
        infer.register_origin(
            tv,
            TypeOrigin {
                span: Some(TextRange::new(0.into(), 1.into())),
                file_span: None,
                kind: TypeOriginKind::Literal,
                label: Some("1".to_string()),
            },
        );

        let int_pos = infer.alloc_pos(prim("int"));
        let tv_neg = infer.alloc_neg(Neg::Var(tv));
        infer.constrain(int_pos, tv_neg);

        let tv_pos = infer.alloc_pos(Pos::Var(tv));
        let bool_neg = infer.alloc_neg(neg_prim("bool"));
        infer.constrain_with_cause(
            tv_pos,
            bool_neg,
            ConstraintCause {
                span: Some(TextRange::new(4.into(), 8.into())),
                reason: ConstraintReason::Annotation,
            },
        );

        let errors = infer.type_errors();
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].kind, TypeErrorKind::ConstructorMismatch);
        assert_eq!(errors[0].cause.reason, ConstraintReason::Annotation);
        assert_eq!(
            errors[0].cause.span,
            Some(TextRange::new(4.into(), 8.into()))
        );
        assert_eq!(errors[0].origins.len(), 1);
        assert_eq!(
            errors[0].origins[0].span,
            Some(TextRange::new(0.into(), 1.into()))
        );
        assert_eq!(errors[0].origins[0].kind, TypeOriginKind::Literal);
    }

    fn prim(name: &str) -> Pos {
        Pos::Con(
            Path {
                segments: vec![Name(name.to_string())],
            },
            vec![],
        )
    }

    fn neg_prim(name: &str) -> Neg {
        Neg::Con(
            Path {
                segments: vec![Name(name.to_string())],
            },
            vec![],
        )
    }

    fn effect_atom(name: &str) -> EffectAtom {
        EffectAtom {
            path: Path {
                segments: vec![Name(name.to_string())],
            },
            args: Vec::new(),
        }
    }

    fn row_items_match(infer: &Infer, items: &[NegId], atoms: &[&EffectAtom]) -> bool {
        items.len() == atoms.len()
            && atoms
                .iter()
                .all(|atom| row_items_contain_atom(infer, items, atom))
    }

    fn row_items_contain_atom(infer: &Infer, items: &[NegId], atom: &EffectAtom) -> bool {
        items
            .iter()
            .any(|item| matches!(infer.arena.get_neg(*item), Neg::Atom(found) if found == *atom))
    }

    fn record_name() -> Name {
        Name("a".to_string())
    }

    #[test]
    fn optional_record_accepts_missing_field() {
        let infer = Infer::new();
        let pos = infer.alloc_pos(Pos::Record(vec![]));
        let neg = infer.alloc_neg(Neg::Record(vec![RecordField::optional(
            record_name(),
            infer.alloc_neg(neg_prim("int")),
        )]));
        infer.constrain(pos, neg);
        assert!(infer.type_errors().is_empty());
    }

    #[test]
    fn expected_function_reports_for_record_source() {
        let infer = Infer::new();
        let pos = infer.alloc_pos(Pos::Record(vec![]));
        let neg = infer.alloc_neg(Neg::Fun {
            arg: infer.alloc_pos(prim("int")),
            arg_eff: infer.alloc_pos(Pos::Row(vec![], infer.arena.empty_pos_row)),
            ret_eff: infer.alloc_neg(Neg::Top),
            ret: infer.alloc_neg(neg_prim("int")),
        });
        infer.constrain(pos, neg);
        assert_eq!(
            infer.type_errors().first().map(|e| &e.kind),
            Some(&TypeErrorKind::ExpectedShape {
                expected: ExpectedShape::Function,
            }),
        );
    }

    #[test]
    fn expected_tuple_reports_for_constructor_source() {
        let infer = Infer::new();
        let pos = infer.alloc_pos(prim("int"));
        let neg = infer.alloc_neg(Neg::Tuple(vec![
            infer.alloc_neg(neg_prim("int")),
            infer.alloc_neg(neg_prim("int")),
        ]));
        infer.constrain(pos, neg);
        assert_eq!(
            infer.type_errors().first().map(|e| &e.kind),
            Some(&TypeErrorKind::ExpectedShape {
                expected: ExpectedShape::Tuple,
            }),
        );
    }

    #[test]
    fn expected_record_reports_for_constructor_source() {
        let infer = Infer::new();
        let pos = infer.alloc_pos(prim("int"));
        let neg = infer.alloc_neg(Neg::Record(vec![RecordField::required(
            record_name(),
            infer.alloc_neg(neg_prim("int")),
        )]));
        infer.constrain(pos, neg);
        assert_eq!(
            infer.type_errors().first().map(|e| &e.kind),
            Some(&TypeErrorKind::ExpectedShape {
                expected: ExpectedShape::Record,
            }),
        );
    }

    #[test]
    fn expected_constructor_reports_for_record_source() {
        let infer = Infer::new();
        let pos = infer.alloc_pos(Pos::Record(vec![]));
        let neg = infer.alloc_neg(neg_prim("int"));
        infer.constrain(pos, neg);
        assert_eq!(
            infer.type_errors().first().map(|e| &e.kind),
            Some(&TypeErrorKind::ExpectedShape {
                expected: ExpectedShape::Constructor,
            }),
        );
    }

    #[test]
    fn constructor_arity_mismatch_reports_constructor_mismatch() {
        let infer = Infer::new();
        let pos = infer.alloc_pos(Pos::Con(
            Path {
                segments: vec![Name("box".to_string())],
            },
            vec![(
                infer.alloc_pos(prim("int")),
                infer.alloc_neg(neg_prim("int")),
            )],
        ));
        let neg = infer.alloc_neg(Neg::Con(
            Path {
                segments: vec![Name("box".to_string())],
            },
            vec![],
        ));

        infer.constrain(pos, neg);

        assert_eq!(
            infer.type_errors().first().map(|e| &e.kind),
            Some(&TypeErrorKind::ConstructorMismatch),
        );
    }

    #[test]
    fn extrude_copies_effect_atom_argument_vars_at_target_level() {
        let infer = Infer::new();
        let pos_arg = fresh_type_var();
        let neg_arg = fresh_type_var();
        infer.register_level(pos_arg, 3);
        infer.register_level(neg_arg, 3);
        let atom = infer.alloc_pos(Pos::Atom(EffectAtom {
            path: Path {
                segments: vec![Name("io".to_string())],
            },
            args: vec![(pos_arg, neg_arg)],
        }));

        let extruded = infer.extrude_pos(atom, 1);

        assert_eq!(infer.level_of(pos_arg), 3);
        assert_eq!(infer.level_of(neg_arg), 3);
        let Pos::Atom(atom) = infer.arena.get_pos(extruded) else {
            panic!("extruded atom should stay an atom");
        };
        let [(pos_copy, neg_copy)] = atom.args.as_slice() else {
            panic!("extruded atom should keep its arity");
        };
        assert_ne!(*pos_copy, pos_arg);
        assert_ne!(*neg_copy, neg_arg);
        assert_eq!(infer.level_of(*pos_copy), 1);
        assert_eq!(infer.level_of(*neg_copy), 1);
        assert!(
            infer
                .uppers_of(pos_arg)
                .iter()
                .any(|upper| matches!(upper, Neg::Var(tv) if *tv == *pos_copy))
        );
        assert!(
            infer
                .lowers_of(neg_arg)
                .iter()
                .any(|lower| matches!(lower, Pos::Var(tv) if *tv == *neg_copy))
        );
    }

    #[test]
    fn extrude_copies_high_level_var_bounds_without_lowering_source() {
        let infer = Infer::new();
        let source = fresh_type_var();
        infer.register_level(source, 3);
        let int_lower = infer.alloc_pos(prim("int"));
        infer.add_lower(source, int_lower);

        let extruded = infer.extrude_pos(infer.alloc_pos(Pos::Var(source)), 1);

        assert_eq!(infer.level_of(source), 3);
        let Pos::Var(copy) = infer.arena.get_pos(extruded) else {
            panic!("extruded variable should stay a variable");
        };
        assert_ne!(copy, source);
        assert_eq!(infer.level_of(copy), 1);
        assert!(
            infer
                .uppers_of(source)
                .iter()
                .any(|upper| matches!(upper, Neg::Var(tv) if *tv == copy))
        );
        assert!(
            infer.lower_refs_of(copy).contains(&int_lower),
            "positive extrusion should copy lower bounds onto the approximation"
        );
    }

    #[test]
    fn compact_instance_extrudes_high_level_subst_without_lowering_source() {
        let infer = Infer::new();
        let quantified = fresh_type_var();
        let source = fresh_type_var();
        let target = fresh_type_var();
        infer.register_level(source, 3);
        infer.register_level(target, 1);

        let scheme_arena = std::rc::Rc::new(crate::types::arena::TypeArena::new());
        let body = scheme_arena.alloc_pos(Pos::Var(quantified));
        let scheme = std::rc::Rc::new(crate::scheme::Scheme {
            arena: scheme_arena,
            compact: crate::simplify::compact::CompactTypeScheme {
                cty: crate::simplify::compact::CompactBounds {
                    self_var: None,
                    lower: crate::simplify::compact::CompactType {
                        vars: std::collections::HashSet::from([quantified]),
                        ..crate::simplify::compact::CompactType::default()
                    },
                    upper: crate::simplify::compact::CompactType::default(),
                },
                rec_vars: std::collections::HashMap::new(),
            },
            body,
            quantified: vec![quantified],
            quantified_sources: smallvec::smallvec![(quantified, quantified)],
            effect_subtractabilities: Vec::new(),
        });
        let instance = crate::scheme::OwnedSchemeInstance {
            scheme,
            subst: smallvec::smallvec![(quantified, source)],
            level: 3,
        };

        infer.constrain_instantiated_ref_instance(instance, target);

        assert_eq!(infer.level_of(source), 3);
        assert!(
            infer.lower_refs_of(target).into_iter().any(|lower| {
                matches!(
                    infer.arena.get_pos(lower),
                    Pos::Var(copy) if copy != source && infer.level_of(copy) == 1
                )
            }),
            "compact instance should materialize through extrusion at the target level"
        );
    }

    #[test]
    fn row_tail_receives_only_unmatched_negative_items() {
        let infer = Infer::new();
        let tail = fresh_type_var();
        infer.register_level(tail, 0);
        let handled = EffectAtom {
            path: Path {
                segments: vec![Name("io".to_string())],
            },
            args: Vec::new(),
        };
        let unhandled = EffectAtom {
            path: Path {
                segments: vec![Name("net".to_string())],
            },
            args: Vec::new(),
        };
        let pos_item = infer.alloc_pos(Pos::Atom(handled.clone()));
        let handled_neg = infer.alloc_neg(Neg::Atom(handled.clone()));
        let unhandled_neg = infer.alloc_neg(Neg::Atom(unhandled.clone()));
        let pos = infer.alloc_pos(Pos::Row(vec![pos_item], infer.alloc_pos(Pos::Var(tail))));
        let neg = infer.alloc_neg(Neg::Row(
            vec![handled_neg, unhandled_neg],
            infer.arena.empty_neg_row,
        ));

        infer.constrain(pos, neg);

        let uppers = infer.uppers_of(tail);
        assert!(
            uppers.iter().any(|upper| {
                matches!(
                    upper,
                    Neg::Row(items, row_tail)
                        if row_items_match(&infer, items, &[&unhandled])
                            && matches!(infer.arena.get_neg(*row_tail), Neg::Row(empty, _) if empty.is_empty())
                )
            }),
            "tail should receive only unmatched row items, got {uppers:?}",
        );
        assert!(
            !uppers.iter().any(|upper| {
                matches!(
                    upper,
                    Neg::Row(items, _) if row_items_contain_atom(&infer, items, &handled)
                )
            }),
            "matched row item should not be required again from the tail, got {uppers:?}",
        );
    }

    #[test]
    fn row_item_upper_matches_handled_atom_args_without_tail_flow() {
        let infer = Infer::new();
        let tail = fresh_type_var();
        let actual_pos = fresh_type_var();
        let actual_neg = fresh_type_var();
        let handled_pos = fresh_type_var();
        let handled_neg = fresh_type_var();
        let effect_path = Path {
            segments: vec![Name("parse".to_string())],
        };
        let pos = infer.alloc_pos(Pos::Atom(EffectAtom {
            path: effect_path.clone(),
            args: vec![(actual_pos, actual_neg)],
        }));
        let handled = infer.alloc_neg(Neg::Atom(EffectAtom {
            path: effect_path,
            args: vec![(handled_pos, handled_neg)],
        }));
        let neg = infer.alloc_neg(Neg::Row(vec![handled], infer.alloc_neg(Neg::Var(tail))));

        infer.constrain(pos, neg);

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
            infer.lower_refs_of(tail).is_empty(),
            "matched atoms must not flow to the row tail"
        );
    }

    #[test]
    fn row_item_upper_passes_unmatched_atom_to_tail() {
        let infer = Infer::new();
        let tail = fresh_type_var();
        let actual = effect_atom("io");
        let handled = effect_atom("parse");
        let pos = infer.alloc_pos(Pos::Atom(actual.clone()));
        let handled = infer.alloc_neg(Neg::Atom(handled));
        let neg = infer.alloc_neg(Neg::Row(vec![handled], infer.alloc_neg(Neg::Var(tail))));

        infer.constrain(pos, neg);

        assert!(
            infer.lower_refs_of(tail).into_iter().any(|lower| {
                matches!(infer.arena.get_pos(lower), Pos::Atom(atom) if atom == actual)
            }),
            "unmatched atoms should flow to the row tail"
        );
    }

    #[test]
    fn effect_lower_bound_does_not_create_subtractability_metadata() {
        let infer = Infer::new();
        let target = fresh_type_var();
        let lower_tail = fresh_type_var();
        infer.register_level(target, 0);
        infer.register_level(lower_tail, 0);

        let io = effect_atom("io");
        infer.record_effect_subtractability(lower_tail, EffectSubtractability::All);
        let lower = infer.alloc_pos(Pos::Row(
            vec![infer.alloc_pos(Pos::Atom(io))],
            infer.alloc_pos(Pos::Var(lower_tail)),
        ));

        infer.constrain(lower, Neg::Var(target));

        assert_eq!(
            infer.effect_subtractability(target),
            None,
            "effect lower bounds must not turn concrete row items or tail metadata into target subtractability"
        );
    }

    #[test]
    fn subtractable_var_row_upper_projects_before_registering_bound() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        infer.register_level(actual, 0);
        infer.register_level(residual, 0);

        let io = effect_atom("io");
        let local = effect_atom("local");
        infer.record_effect_subtractability(actual, EffectSubtractability::set(vec![io.clone()]));
        let io_neg = infer.alloc_neg(Neg::Atom(io.clone()));
        let local_neg = infer.alloc_neg(Neg::Atom(local.clone()));
        let row = infer.alloc_neg(Neg::Row(
            vec![io_neg, local_neg],
            infer.alloc_neg(Neg::Var(residual)),
        ));

        infer.constrain(Pos::Var(actual), row);

        let uppers = infer.uppers_of(actual);
        assert!(
            uppers.iter().any(|upper| {
                matches!(
                    upper,
                    Neg::Row(items, tail)
                        if row_items_match(&infer, items, &[&io])
                            && matches!(infer.arena.get_neg(*tail), Neg::Var(tv) if tv == residual)
                )
            }),
            "actual should receive only the intersection of handled row items and subtractability, got {uppers:?}"
        );
        assert!(
            !uppers.iter().any(|upper| {
                matches!(
                    upper,
                    Neg::Row(items, _) if row_items_contain_atom(&infer, items, &local)
                )
            }),
            "unsubtractable row items must not be registered on the source variable, got {uppers:?}"
        );
        assert_eq!(
            infer.effect_subtractability(residual),
            Some(EffectSubtractability::set(vec![io])),
            "row tail should inherit the source subtractability"
        );
    }

    #[test]
    fn subtractable_var_row_upper_uses_tail_when_projection_is_empty() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        infer.register_level(actual, 0);
        infer.register_level(residual, 0);

        let io = effect_atom("io");
        let local = effect_atom("local");
        infer.record_effect_subtractability(actual, EffectSubtractability::set(vec![io.clone()]));
        let local_neg = infer.alloc_neg(Neg::Atom(local.clone()));
        let row = infer.alloc_neg(Neg::Row(
            vec![local_neg],
            infer.alloc_neg(Neg::Var(residual)),
        ));

        infer.constrain(Pos::Var(actual), row);

        let uppers = infer.uppers_of(actual);
        assert!(
            uppers
                .iter()
                .any(|upper| matches!(upper, Neg::Var(tv) if *tv == residual)),
            "empty projection should register only the row tail, got {uppers:?}"
        );
        assert!(
            !uppers.iter().any(|upper| {
                matches!(
                    upper,
                    Neg::Row(items, _) if row_items_contain_atom(&infer, items, &local)
                )
            }),
            "the original handled row must not be registered when intersection is empty, got {uppers:?}"
        );
        assert_eq!(
            infer.effect_subtractability(residual),
            Some(EffectSubtractability::set(vec![io])),
            "row tail should inherit the source subtractability even when no items remain"
        );
    }

    #[test]
    fn empty_subtractable_var_row_upper_uses_tail_for_handled_row() {
        let infer = Infer::new();
        let actual = fresh_type_var();
        let residual = fresh_type_var();
        infer.register_level(actual, 0);
        infer.register_level(residual, 0);

        let io = effect_atom("io");
        infer.record_effect_subtractability(actual, EffectSubtractability::Empty);
        let io_neg = infer.alloc_neg(Neg::Atom(io.clone()));
        let row = infer.alloc_neg(Neg::Row(vec![io_neg], infer.alloc_neg(Neg::Var(residual))));

        infer.constrain(Pos::Var(actual), row);

        let uppers = infer.uppers_of(actual);
        assert!(
            uppers
                .iter()
                .any(|upper| matches!(upper, Neg::Var(tv) if *tv == residual)),
            "Empty subtractability should make handled row intersection empty, got {uppers:?}"
        );
        assert!(
            !uppers.iter().any(|upper| {
                matches!(
                    upper,
                    Neg::Row(items, _) if row_items_contain_atom(&infer, items, &io)
                )
            }),
            "handled row items must not be registered when source subtractability is Empty, got {uppers:?}"
        );
        assert_eq!(
            infer.effect_subtractability(residual),
            Some(EffectSubtractability::Empty),
            "row tail should inherit Empty subtractability from the source"
        );
    }

    #[test]
    fn empty_subtractable_source_projects_row_upper_propagated_through_alias() {
        let infer = Infer::new();
        let source = fresh_type_var();
        let alias = fresh_type_var();
        let residual = fresh_type_var();
        infer.register_level(source, 0);
        infer.register_level(alias, 0);
        infer.register_level(residual, 0);

        let io = effect_atom("io");
        infer.record_effect_subtractability(source, EffectSubtractability::Empty);
        infer.constrain(Pos::Var(source), Neg::Var(alias));
        infer.constrain(
            Pos::Var(alias),
            Neg::Row(
                vec![infer.alloc_neg(Neg::Atom(io.clone()))],
                infer.alloc_neg(Neg::Var(residual)),
            ),
        );

        let uppers = infer.uppers_of(source);
        assert!(
            uppers
                .iter()
                .any(|upper| matches!(upper, Neg::Var(tv) if *tv == residual)),
            "source should project propagated row upper with Empty subtractability, got {uppers:?}"
        );
        assert!(
            !uppers.iter().any(|upper| {
                matches!(
                    upper,
                    Neg::Row(items, _) if row_items_contain_atom(&infer, items, &io)
                )
            }),
            "handled row items must not stay on the Empty-subtractable source, got {uppers:?}"
        );
    }

    #[test]
    fn optional_record_accepts_required_field_with_matching_type() {
        let infer = Infer::new();
        let pos = infer.alloc_pos(Pos::Record(vec![RecordField::required(
            record_name(),
            infer.alloc_pos(prim("int")),
        )]));
        let neg = infer.alloc_neg(Neg::Record(vec![RecordField::optional(
            record_name(),
            infer.alloc_neg(neg_prim("int")),
        )]));
        infer.constrain(pos, neg);
        assert!(infer.type_errors().is_empty());
    }

    #[test]
    fn optional_record_rejects_required_field_with_wrong_type() {
        let infer = Infer::new();
        let pos = infer.alloc_pos(Pos::Record(vec![RecordField::required(
            record_name(),
            infer.alloc_pos(prim("string")),
        )]));
        let neg = infer.alloc_neg(Neg::Record(vec![RecordField::optional(
            record_name(),
            infer.alloc_neg(neg_prim("int")),
        )]));
        infer.constrain(pos, neg);
        assert_eq!(infer.type_errors().len(), 1);
    }

    #[test]
    fn required_record_rejects_optional_source_field() {
        let infer = Infer::new();
        let pos = infer.alloc_pos(Pos::Record(vec![RecordField::optional(
            record_name(),
            infer.alloc_pos(prim("int")),
        )]));
        let neg = infer.alloc_neg(Neg::Record(vec![RecordField::required(
            record_name(),
            infer.alloc_neg(neg_prim("int")),
        )]));
        infer.constrain(pos, neg);
        assert_eq!(
            infer.type_errors().first().map(|e| &e.kind),
            Some(&TypeErrorKind::MissingRecordField {
                name: "a".to_string(),
            }),
        );
    }

    #[test]
    fn tail_spread_constrains_tail_with_optional_shadowed_field() {
        let infer = Infer::new();
        let tail_tv = fresh_type_var();
        let pos = infer.alloc_pos(Pos::RecordTailSpread {
            fields: vec![RecordField::required(
                record_name(),
                infer.alloc_pos(prim("int")),
            )],
            tail: infer.alloc_pos(Pos::Var(tail_tv)),
        });
        let neg = infer.alloc_neg(Neg::Record(vec![RecordField::required(
            record_name(),
            infer.alloc_neg(neg_prim("int")),
        )]));

        infer.constrain(pos, neg);

        let uppers = infer.uppers_of(tail_tv);
        assert!(
            uppers.iter().any(|upper| matches!(
                upper,
                Neg::Record(fields)
                    if matches!(
                        fields.as_slice(),
                        [field] if field.name == record_name() && field.optional
                    )
            )),
            "tail spread should constrain tail with optionalized shadowed field, got {uppers:?}",
        );
    }

    #[test]
    fn head_spread_does_not_constrain_tail_when_local_field_shadows_target() {
        let infer = Infer::new();
        let tail_tv = fresh_type_var();
        let pos = infer.alloc_pos(Pos::RecordHeadSpread {
            tail: infer.alloc_pos(Pos::Var(tail_tv)),
            fields: vec![RecordField::required(
                record_name(),
                infer.alloc_pos(prim("int")),
            )],
        });
        let neg = infer.alloc_neg(Neg::Record(vec![RecordField::required(
            record_name(),
            infer.alloc_neg(neg_prim("int")),
        )]));

        infer.constrain(pos, neg);

        assert!(
            infer.uppers_of(tail_tv).is_empty(),
            "head spread should not constrain tail for a shadowed field",
        );
    }

    #[test]
    fn head_spread_constrains_tail_when_target_field_is_missing_locally() {
        let infer = Infer::new();
        let tail_tv = fresh_type_var();
        let pos = infer.alloc_pos(Pos::RecordHeadSpread {
            tail: infer.alloc_pos(Pos::Var(tail_tv)),
            fields: vec![RecordField::required(
                Name("b".to_string()),
                infer.alloc_pos(prim("int")),
            )],
        });
        let neg = infer.alloc_neg(Neg::Record(vec![RecordField::required(
            record_name(),
            infer.alloc_neg(neg_prim("int")),
        )]));

        infer.constrain(pos, neg);

        let uppers = infer.uppers_of(tail_tv);
        assert!(
            uppers.iter().any(|upper| matches!(
                upper,
                Neg::Record(fields)
                    if matches!(
                        fields.as_slice(),
                        [field] if field.name == record_name() && !field.optional
                    )
            )),
            "head spread should constrain tail with required field when local field is missing, got {uppers:?}",
        );
    }
}
