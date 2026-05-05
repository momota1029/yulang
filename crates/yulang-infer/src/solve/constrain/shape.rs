use rustc_hash::FxHashSet;

use super::util::{find_record_field, is_builtin_numeric_widening, live_neg_is_empty_row};
use super::{Infer, StepCache};
use crate::diagnostic::{ConstraintCause, ExpectedShape, TypeErrorKind};
use crate::ids::{NegId, PosId, TypeVar};
use crate::types::{Neg, Pos};

impl Infer {
    pub(super) fn constrain_shape(
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
                self.constrain_step(arg_pos, arg_neg, cause, cache);
                let arg_eff_pure =
                    live_neg_is_empty_row(self, arg_eff_neg, &mut FxHashSet::default());
                if arg_eff_pure {
                    self.constrain_step(arg_eff_pos, ret_eff_neg, cause, cache);
                } else {
                    self.constrain_step(arg_eff_pos, arg_eff_neg, cause, cache);
                }
                self.constrain_step(ret_eff_pos, ret_eff_neg, cause, cache);
                self.constrain_step(ret_pos, ret_neg, cause, cache);
            }
            (Pos::Record(pos_fields), Neg::Record(neg_fields)) => {
                for neg_field in &neg_fields {
                    if let Some(pos_field) =
                        find_record_field(pos_fields.as_slice(), &neg_field.name)
                    {
                        if pos_field.optional && !neg_field.optional {
                            self.report_type_error(
                                pos,
                                neg,
                                cause,
                                origin_hint,
                                TypeErrorKind::MissingRecordField {
                                    name: neg_field.name.0.clone(),
                                },
                            );
                        } else {
                            self.constrain_step(pos_field.value, neg_field.value, cause, cache);
                        }
                    } else if !neg_field.optional {
                        self.report_type_error(
                            pos,
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
                self.constrain_pos_record_tail_spread_to_neg_record(
                    fields.as_slice(),
                    tail,
                    neg_fields.as_slice(),
                    cause,
                    origin_hint,
                    cache,
                );
            }
            (Pos::RecordHeadSpread { tail, fields }, Neg::Record(neg_fields)) => {
                self.constrain_pos_record_head_spread_to_neg_record(
                    tail,
                    fields.as_slice(),
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
                            self.constrain_step(*p, *n, cause, cache);
                        }
                    }
                }
            }
            (Pos::Tuple(pos_items), Neg::Tuple(neg_items)) => {
                let pos_len = pos_items.len();
                let neg_len = neg_items.len();
                if pos_len != neg_len {
                    self.report_type_error(
                        pos,
                        neg,
                        cause,
                        origin_hint,
                        TypeErrorKind::TupleArityMismatch { pos_len, neg_len },
                    );
                } else {
                    for (p, n) in pos_items.iter().zip(neg_items.iter()) {
                        self.constrain_step(*p, *n, cause, cache);
                    }
                }
            }
            (Pos::Con(p_path, p_args), Neg::Con(n_path, n_args)) if p_path == n_path => {
                let variances = self.variances.get(&p_path);
                for (index, (pa, na)) in p_args
                    .iter()
                    .copied()
                    .zip(n_args.iter().copied())
                    .enumerate()
                {
                    let variance = variances
                        .and_then(|items| items.get(index))
                        .copied()
                        .unwrap_or(crate::types::Variance::Invariant);
                    match variance {
                        crate::types::Variance::Invariant => {
                            self.propagate_invariant_arg_through(pa.0, pa.1, na.0, na.1);
                            self.constrain_step(pa.0, na.1, cause, cache);
                            self.constrain_step(na.0, pa.1, cause, cache);
                        }
                        crate::types::Variance::Covariant => {
                            self.constrain_step(pa.0, na.1, cause, cache);
                        }
                        crate::types::Variance::Contravariant => {
                            self.constrain_step(na.0, pa.1, cause, cache);
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
                self.report_type_error(
                    pos,
                    neg,
                    cause,
                    origin_hint,
                    TypeErrorKind::ConstructorMismatch,
                );
            }
            (Pos::Row(pos_items, pos_tail), Neg::Row(neg_items, neg_tail)) => {
                self.constrain_row(pos_items, pos_tail, neg_items, neg_tail, cause, cache);
            }
            (pos_node, Neg::Fun { .. })
                if super::errors::should_report_expected_function(&pos_node) =>
            {
                self.report_type_error(
                    pos,
                    neg,
                    cause,
                    origin_hint,
                    TypeErrorKind::ExpectedShape {
                        expected: ExpectedShape::Function,
                    },
                );
            }
            (pos_node, Neg::Tuple(_)) if super::errors::should_report_expected_tuple(&pos_node) => {
                self.report_type_error(
                    pos,
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
                self.report_type_error(
                    pos,
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
                self.report_type_error(
                    pos,
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
}
