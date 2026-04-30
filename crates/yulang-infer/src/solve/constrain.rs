use rustc_hash::FxHashSet;

use super::{Infer, IntoNegId, IntoPosId};
use crate::diagnostic::ConstraintCause;
use crate::ids::{NegId, PosId, TypeVar};
use crate::scheme::OwnedSchemeInstance;
use crate::types::{Neg, Pos};

mod bounds;
mod compact;
mod errors;
mod extrude;
mod frozen;
mod records;
mod rows;
mod shape;
mod through;
mod util;
mod vars;

use compact::compact_instance_direct_var;
type StepCache = FxHashSet<(PosId, NegId)>;
type FrozenStepCache = FxHashSet<(usize, PosId, NegId)>;

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
        let pos = pos.into_pos_id(self);
        let neg = neg.into_neg_id(self);
        let mut cache = FxHashSet::default();
        self.constrain_step(pos, neg, &cause, &mut cache);
    }

    pub fn constrain_instantiated_ref(&self, pos: PosId, target: TypeVar) {
        let cause = ConstraintCause::unknown();
        let pos = self.extrude_pos(pos, self.level_of(target));
        let mut cache = FxHashSet::default();
        if self.add_lower_bound(target, pos, &cause, &mut cache) {
            let uppers = self.upper_refs_of(target);
            if !uppers.is_empty() {
                for upper in uppers {
                    self.constrain_step_with_hint(pos, upper, &cause, Some(target), &mut cache);
                }
            }
        }
    }

    pub fn constrain_instantiated_ref_instance(
        &self,
        instance: OwnedSchemeInstance,
        target: TypeVar,
    ) {
        let cause = ConstraintCause::unknown();
        self.lower_levels_scheme_instance(&instance, self.level_of(target));
        if self.add_compact_lower_instance(target, instance.clone()) {
            if let Some(source) = compact_instance_direct_var(&instance) {
                if !self.is_through(source) {
                    self.clear_through(target);
                }
                let mut cache = FxHashSet::default();
                self.propagate_through(source, target, &cause, &mut cache);
            } else if !self.compact_instance_preserves_through(&instance) {
                self.clear_through(target);
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
        if !cache.insert((pos, neg)) {
            return;
        }
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
            (Pos::Var(a), Neg::Row(_, tail)) if self.is_through(a) => {
                self.constrain_step(pos, tail, cause, cache);
            }
            (Pos::Var(a), _) => {
                self.constrain_pos_var_to(a, neg, cause, cache);
            }

            _ => self.constrain_shape(pos, neg, cause, origin_hint, cache),
        }
    }
}

#[cfg(test)]
mod tests {
    use rowan::TextRange;

    use crate::diagnostic::{
        ConstraintCause, ConstraintReason, ExpectedShape, TypeErrorKind, TypeOrigin, TypeOriginKind,
    };
    use crate::ids::fresh_type_var;
    use crate::solve::Infer;
    use crate::symbols::{Name, Path};
    use crate::types::RecordField;
    use crate::types::{Neg, Pos};

    #[test]
    fn constructor_mismatch_reports_cause_and_origin() {
        let infer = Infer::new();
        let tv = fresh_type_var();
        infer.register_level(tv, 0);
        infer.register_origin(
            tv,
            TypeOrigin {
                span: Some(TextRange::new(0.into(), 1.into())),
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
