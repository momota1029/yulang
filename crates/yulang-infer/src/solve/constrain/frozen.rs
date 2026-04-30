use rustc_hash::FxHashSet;

use super::util::{
    find_record_field, is_builtin_numeric_widening, live_neg_var_is_empty_row, neg_id_direct_var,
    optionalized_neg_field, pos_id_direct_var, singleton_neg_record,
};
use super::{FrozenStepCache, Infer};
use crate::diagnostic::{ConstraintCause, ExpectedShape, TypeErrorKind};
use crate::ids::{NegId, PosId, TypeVar};
use crate::scheme::{OwnedSchemeInstance, read_neg_with_subst, read_pos_with_subst};
use crate::simplify::compact::subst_lookup_small;
use crate::types::arena::TypeArena;
use crate::types::{Neg, Pos};

impl Infer {
    pub(super) fn constrain_frozen_instance_to_neg(
        &self,
        instance: &OwnedSchemeInstance,
        neg: NegId,
        cause: &ConstraintCause,
        origin_hint: Option<TypeVar>,
        cache: &mut FrozenStepCache,
    ) {
        self.constrain_frozen_pos_to_neg(
            &instance.scheme.arena,
            instance.scheme.body,
            instance.subst.as_slice(),
            neg,
            cause,
            origin_hint,
            cache,
        );
    }

    fn constrain_frozen_pos_to_neg(
        &self,
        arena: &TypeArena,
        pos: PosId,
        subst: &[(TypeVar, TypeVar)],
        neg: NegId,
        cause: &ConstraintCause,
        origin_hint: Option<TypeVar>,
        cache: &mut FrozenStepCache,
    ) {
        let cache_key = ((arena as *const TypeArena) as usize, pos, neg);
        if !cache.insert(cache_key) {
            return;
        }

        let pos_node = arena.get_pos(pos);
        let neg_node = self.arena.get_neg(neg);
        match (pos_node, neg_node) {
            (Pos::Var(tv), _) | (Pos::Raw(tv), _) => {
                let live_pos = self.alloc_pos(Pos::Var(subst_lookup_small(subst, tv)));
                let mut live_cache = FxHashSet::default();
                self.constrain_step_with_hint(live_pos, neg, cause, origin_hint, &mut live_cache);
            }
            (Pos::Bot, _) | (_, Neg::Top) => {}
            (Pos::Forall(..), _) | (_, Neg::Forall(..)) => {}
            (Pos::Union(a, b), _) => {
                self.constrain_frozen_pos_to_neg(arena, a, subst, neg, cause, origin_hint, cache);
                self.constrain_frozen_pos_to_neg(arena, b, subst, neg, cause, origin_hint, cache);
            }
            (_, Neg::Intersection(a, b)) => {
                self.constrain_frozen_pos_to_neg(arena, pos, subst, a, cause, origin_hint, cache);
                self.constrain_frozen_pos_to_neg(arena, pos, subst, b, cause, origin_hint, cache);
            }
            (
                Pos::Fun {
                    arg: arg_neg,
                    arg_eff: arg_eff_neg,
                    ret_eff: ret_eff_pos,
                    ret: ret_pos,
                },
                Neg::Fun {
                    arg: arg_pos,
                    arg_eff: arg_eff_pos,
                    ret_eff: ret_eff_neg,
                    ret: ret_neg,
                },
            ) => {
                self.constrain_pos_to_frozen_neg(arg_pos, arena, arg_neg, subst, cause);
                let arg_eff_pure = frozen_neg_is_empty_row(
                    self,
                    arena,
                    arg_eff_neg,
                    subst,
                    &mut FxHashSet::default(),
                );
                if arg_eff_pure {
                    let mut live_cache = FxHashSet::default();
                    self.constrain_step(arg_eff_pos, ret_eff_neg, cause, &mut live_cache);
                } else {
                    self.constrain_pos_to_frozen_neg(arg_eff_pos, arena, arg_eff_neg, subst, cause);
                }
                self.constrain_frozen_pos_to_neg(
                    arena,
                    ret_eff_pos,
                    subst,
                    ret_eff_neg,
                    cause,
                    origin_hint,
                    cache,
                );
                self.constrain_frozen_pos_to_neg(
                    arena,
                    ret_pos,
                    subst,
                    ret_neg,
                    cause,
                    origin_hint,
                    cache,
                );
            }
            (Pos::Record(pos_fields), Neg::Record(neg_fields)) => {
                for neg_field in &neg_fields {
                    if let Some(pos_field) =
                        find_record_field(pos_fields.as_slice(), &neg_field.name)
                    {
                        if pos_field.optional && !neg_field.optional {
                            let live_pos = materialize_frozen_pos(self, arena, pos, subst);
                            self.report_type_error(
                                live_pos,
                                neg,
                                cause,
                                origin_hint,
                                TypeErrorKind::MissingRecordField {
                                    name: neg_field.name.0.clone(),
                                },
                            );
                        } else {
                            self.constrain_frozen_pos_to_neg(
                                arena,
                                pos_field.value,
                                subst,
                                neg_field.value,
                                cause,
                                origin_hint,
                                cache,
                            );
                        }
                    } else if !neg_field.optional {
                        let live_pos = materialize_frozen_pos(self, arena, pos, subst);
                        self.report_type_error(
                            live_pos,
                            neg,
                            cause,
                            origin_hint,
                            TypeErrorKind::MissingRecordField {
                                name: neg_field.name.0.clone(),
                            },
                        );
                    }
                }
            }
            (Pos::RecordTailSpread { fields, tail }, Neg::Record(neg_fields)) => {
                self.constrain_frozen_record_tail_spread_to_neg_record(
                    arena,
                    fields.as_slice(),
                    tail,
                    subst,
                    neg_fields.as_slice(),
                    cause,
                    origin_hint,
                    cache,
                );
            }
            (Pos::RecordHeadSpread { tail, fields }, Neg::Record(neg_fields)) => {
                self.constrain_frozen_record_head_spread_to_neg_record(
                    arena,
                    tail,
                    fields.as_slice(),
                    subst,
                    neg_fields.as_slice(),
                    cause,
                    origin_hint,
                    cache,
                );
            }
            (Pos::PolyVariant(pos_items), Neg::PolyVariant(neg_items)) => {
                for (name, pos_payloads) in &pos_items {
                    let Some((_, neg_payloads)) = neg_items.iter().find(|(n, _)| n == name) else {
                        continue;
                    };
                    if pos_payloads.len() == neg_payloads.len() {
                        for (p, n) in pos_payloads.iter().zip(neg_payloads.iter()) {
                            self.constrain_frozen_pos_to_neg(
                                arena,
                                *p,
                                subst,
                                *n,
                                cause,
                                origin_hint,
                                cache,
                            );
                        }
                    }
                }
            }
            (Pos::Tuple(pos_items), Neg::Tuple(neg_items)) => {
                let pos_len = pos_items.len();
                let neg_len = neg_items.len();
                if pos_len != neg_len {
                    let materialized = materialize_frozen_pos(self, arena, pos, subst);
                    self.report_type_error(
                        materialized,
                        neg,
                        cause,
                        origin_hint,
                        TypeErrorKind::TupleArityMismatch { pos_len, neg_len },
                    );
                } else {
                    for (p, n) in pos_items.iter().zip(neg_items.iter()) {
                        self.constrain_frozen_pos_to_neg(
                            arena,
                            *p,
                            subst,
                            *n,
                            cause,
                            origin_hint,
                            cache,
                        );
                    }
                }
            }
            (Pos::Con(p_path, p_args), Neg::Con(n_path, n_args)) if p_path == n_path => {
                let variances = self.variances.get(&p_path).cloned().unwrap_or_else(|| {
                    vec![crate::types::Variance::Invariant; p_args.len().min(n_args.len())]
                });
                let pairs: Vec<_> = p_args.iter().copied().zip(n_args.iter().copied()).collect();
                for (variance, (pa, na)) in variances.into_iter().zip(pairs) {
                    match variance {
                        crate::types::Variance::Invariant => {
                            propagate_invariant_arg_through_frozen(
                                self, arena, pa.0, pa.1, subst, na.0, na.1,
                            );
                            self.constrain_frozen_pos_to_neg(
                                arena,
                                pa.0,
                                subst,
                                na.1,
                                cause,
                                origin_hint,
                                cache,
                            );
                            self.constrain_pos_to_frozen_neg(na.0, arena, pa.1, subst, cause);
                        }
                        crate::types::Variance::Covariant => {
                            self.constrain_frozen_pos_to_neg(
                                arena,
                                pa.0,
                                subst,
                                na.1,
                                cause,
                                origin_hint,
                                cache,
                            );
                        }
                        crate::types::Variance::Contravariant => {
                            self.constrain_pos_to_frozen_neg(na.0, arena, pa.1, subst, cause);
                        }
                    }
                }
            }
            (Pos::Con(p_path, p_args), Neg::Con(n_path, n_args))
                if p_args.is_empty()
                    && n_args.is_empty()
                    && is_builtin_numeric_widening(&p_path, &n_path) => {}

            (Pos::Con(p_path, _), Neg::Con(n_path, _))
                if !p_path.segments.is_empty()
                    && !n_path.segments.is_empty()
                    && p_path != n_path =>
            {
                let materialized = materialize_frozen_pos(self, arena, pos, subst);
                self.report_type_error(
                    materialized,
                    neg,
                    cause,
                    origin_hint,
                    TypeErrorKind::ConstructorMismatch,
                );
            }
            (Pos::Row(..), Neg::Row(..)) => {
                let materialized = materialize_frozen_pos(self, arena, pos, subst);
                let mut live_cache = FxHashSet::default();
                self.constrain_step_with_hint(
                    materialized,
                    neg,
                    cause,
                    origin_hint,
                    &mut live_cache,
                );
            }
            (pos_node, Neg::Fun { .. })
                if super::errors::should_report_expected_function(&pos_node) =>
            {
                let materialized = materialize_frozen_pos(self, arena, pos, subst);
                self.report_type_error(
                    materialized,
                    neg,
                    cause,
                    origin_hint,
                    TypeErrorKind::ExpectedShape {
                        expected: ExpectedShape::Function,
                    },
                );
            }
            (pos_node, Neg::Tuple(_)) if super::errors::should_report_expected_tuple(&pos_node) => {
                let materialized = materialize_frozen_pos(self, arena, pos, subst);
                self.report_type_error(
                    materialized,
                    neg,
                    cause,
                    origin_hint,
                    TypeErrorKind::ExpectedShape {
                        expected: ExpectedShape::Tuple,
                    },
                );
            }
            (pos_node, Neg::Record(_))
                if super::errors::should_report_expected_record(&pos_node) =>
            {
                let materialized = materialize_frozen_pos(self, arena, pos, subst);
                self.report_type_error(
                    materialized,
                    neg,
                    cause,
                    origin_hint,
                    TypeErrorKind::ExpectedShape {
                        expected: ExpectedShape::Record,
                    },
                );
            }
            (pos_node, Neg::Con(n_path, _))
                if !n_path.segments.is_empty()
                    && super::errors::should_report_expected_constructor(&pos_node) =>
            {
                let materialized = materialize_frozen_pos(self, arena, pos, subst);
                self.report_type_error(
                    materialized,
                    neg,
                    cause,
                    origin_hint,
                    TypeErrorKind::ExpectedShape {
                        expected: ExpectedShape::Constructor,
                    },
                );
            }
            _ => {}
        }
    }

    fn constrain_pos_to_frozen_neg(
        &self,
        pos: PosId,
        arena: &TypeArena,
        neg: NegId,
        subst: &[(TypeVar, TypeVar)],
        cause: &ConstraintCause,
    ) {
        let materialized = materialize_frozen_neg(self, arena, neg, subst);
        let mut live_cache = FxHashSet::default();
        self.constrain_step(pos, materialized, cause, &mut live_cache);
    }

    fn constrain_frozen_record_tail_spread_to_neg_record(
        &self,
        arena: &TypeArena,
        fields: &[crate::types::RecordField<PosId>],
        tail: PosId,
        subst: &[(TypeVar, TypeVar)],
        neg_fields: &[crate::types::RecordField<NegId>],
        cause: &ConstraintCause,
        origin_hint: Option<TypeVar>,
        cache: &mut FrozenStepCache,
    ) {
        for neg_field in neg_fields {
            if let Some(pos_field) = find_record_field(fields, &neg_field.name) {
                if pos_field.optional && !neg_field.optional {
                    let live_pos = self.alloc_pos(Pos::RecordTailSpread {
                        fields: fields.to_vec(),
                        tail,
                    });
                    self.report_type_error(
                        live_pos,
                        singleton_neg_record(self, neg_field.clone()),
                        cause,
                        origin_hint,
                        TypeErrorKind::MissingRecordField {
                            name: neg_field.name.0.clone(),
                        },
                    );
                } else {
                    self.constrain_frozen_pos_to_neg(
                        arena,
                        pos_field.value,
                        subst,
                        neg_field.value,
                        cause,
                        origin_hint,
                        cache,
                    );
                }
                self.constrain_frozen_pos_to_neg(
                    arena,
                    tail,
                    subst,
                    singleton_neg_record(self, optionalized_neg_field(neg_field.clone())),
                    cause,
                    origin_hint,
                    cache,
                );
            } else {
                self.constrain_frozen_pos_to_neg(
                    arena,
                    tail,
                    subst,
                    singleton_neg_record(self, neg_field.clone()),
                    cause,
                    origin_hint,
                    cache,
                );
            }
        }
    }

    fn constrain_frozen_record_head_spread_to_neg_record(
        &self,
        arena: &TypeArena,
        tail: PosId,
        fields: &[crate::types::RecordField<PosId>],
        subst: &[(TypeVar, TypeVar)],
        neg_fields: &[crate::types::RecordField<NegId>],
        cause: &ConstraintCause,
        origin_hint: Option<TypeVar>,
        cache: &mut FrozenStepCache,
    ) {
        for neg_field in neg_fields {
            if let Some(pos_field) = find_record_field(fields, &neg_field.name) {
                if pos_field.optional && !neg_field.optional {
                    let live_pos = self.alloc_pos(Pos::RecordHeadSpread {
                        tail,
                        fields: fields.to_vec(),
                    });
                    self.report_type_error(
                        live_pos,
                        singleton_neg_record(self, neg_field.clone()),
                        cause,
                        origin_hint,
                        TypeErrorKind::MissingRecordField {
                            name: neg_field.name.0.clone(),
                        },
                    );
                } else {
                    self.constrain_frozen_pos_to_neg(
                        arena,
                        pos_field.value,
                        subst,
                        neg_field.value,
                        cause,
                        origin_hint,
                        cache,
                    );
                }
            } else {
                self.constrain_frozen_pos_to_neg(
                    arena,
                    tail,
                    subst,
                    singleton_neg_record(self, neg_field.clone()),
                    cause,
                    origin_hint,
                    cache,
                );
            }
        }
    }
}

fn frozen_neg_is_empty_row(
    infer: &Infer,
    arena: &TypeArena,
    neg: NegId,
    subst: &[(TypeVar, TypeVar)],
    seen: &mut FxHashSet<TypeVar>,
) -> bool {
    match arena.get_neg(neg) {
        Neg::Row(items, tail) => items.is_empty() && matches!(arena.get_neg(tail), Neg::Top),
        Neg::Var(tv) => live_neg_var_is_empty_row(infer, subst_lookup_small(subst, tv), seen),
        _ => false,
    }
}

fn materialize_frozen_pos(
    infer: &Infer,
    arena: &TypeArena,
    pos: PosId,
    subst: &[(TypeVar, TypeVar)],
) -> PosId {
    infer.alloc_pos(read_pos_with_subst(arena, infer, pos, subst))
}

fn materialize_frozen_neg(
    infer: &Infer,
    arena: &TypeArena,
    neg: NegId,
    subst: &[(TypeVar, TypeVar)],
) -> NegId {
    infer.alloc_neg(read_neg_with_subst(arena, infer, neg, subst))
}

fn propagate_invariant_arg_through_frozen(
    infer: &Infer,
    arena: &TypeArena,
    pp: PosId,
    pn: NegId,
    subst: &[(TypeVar, TypeVar)],
    np: PosId,
    nn: NegId,
) {
    let vars = [
        frozen_pos_direct_var(arena, pp, subst),
        frozen_neg_direct_var(arena, pn, subst),
        pos_id_direct_var(&infer.arena.get_pos(np)),
        neg_id_direct_var(&infer.arena.get_neg(nn)),
    ];
    if vars.into_iter().flatten().any(|tv| infer.is_through(tv)) {
        for tv in vars.into_iter().flatten() {
            infer.mark_through(tv);
        }
    }
}

fn frozen_pos_direct_var(
    arena: &TypeArena,
    pos: PosId,
    subst: &[(TypeVar, TypeVar)],
) -> Option<TypeVar> {
    match arena.get_pos(pos) {
        Pos::Var(tv) | Pos::Raw(tv) => Some(subst_lookup_small(subst, tv)),
        _ => None,
    }
}

fn frozen_neg_direct_var(
    arena: &TypeArena,
    neg: NegId,
    subst: &[(TypeVar, TypeVar)],
) -> Option<TypeVar> {
    match arena.get_neg(neg) {
        Neg::Var(tv) => Some(subst_lookup_small(subst, tv)),
        _ => None,
    }
}
