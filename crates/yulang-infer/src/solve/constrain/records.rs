use super::util::{find_record_field, optionalized_neg_field, singleton_neg_record};
use super::{Infer, StepCache};
use crate::diagnostic::{ConstraintCause, TypeErrorKind};
use crate::ids::{NegId, PosId, TypeVar};
use crate::types::Pos;

impl Infer {
    pub(super) fn constrain_pos_record_tail_spread_to_neg_record(
        &self,
        fields: &[crate::types::RecordField<PosId>],
        tail: PosId,
        neg_fields: &[crate::types::RecordField<NegId>],
        cause: &ConstraintCause,
        origin_hint: Option<TypeVar>,
        cache: &mut StepCache,
    ) {
        for neg_field in neg_fields {
            if let Some(pos_field) = find_record_field(fields, &neg_field.name) {
                if pos_field.optional && !neg_field.optional {
                    let missing = self.alloc_pos(Pos::RecordTailSpread {
                        fields: fields.to_vec(),
                        tail,
                    });
                    self.report_type_error(
                        missing,
                        singleton_neg_record(self, neg_field.clone()),
                        cause,
                        origin_hint,
                        TypeErrorKind::MissingRecordField {
                            name: neg_field.name.0.clone(),
                        },
                    );
                } else {
                    self.constrain_step(pos_field.value, neg_field.value, cause, cache);
                }
                self.constrain_step(
                    tail,
                    singleton_neg_record(self, optionalized_neg_field(neg_field.clone())),
                    cause,
                    cache,
                );
            } else {
                self.constrain_step(
                    tail,
                    singleton_neg_record(self, neg_field.clone()),
                    cause,
                    cache,
                );
            }
        }
    }

    pub(super) fn constrain_pos_record_head_spread_to_neg_record(
        &self,
        tail: PosId,
        fields: &[crate::types::RecordField<PosId>],
        neg_fields: &[crate::types::RecordField<NegId>],
        cause: &ConstraintCause,
        origin_hint: Option<TypeVar>,
        cache: &mut StepCache,
    ) {
        for neg_field in neg_fields {
            if let Some(pos_field) = find_record_field(fields, &neg_field.name) {
                if pos_field.optional && !neg_field.optional {
                    let missing = self.alloc_pos(Pos::RecordHeadSpread {
                        tail,
                        fields: fields.to_vec(),
                    });
                    self.report_type_error(
                        missing,
                        singleton_neg_record(self, neg_field.clone()),
                        cause,
                        origin_hint,
                        TypeErrorKind::MissingRecordField {
                            name: neg_field.name.0.clone(),
                        },
                    );
                } else {
                    self.constrain_step(pos_field.value, neg_field.value, cause, cache);
                }
            } else {
                self.constrain_step(
                    tail,
                    singleton_neg_record(self, neg_field.clone()),
                    cause,
                    cache,
                );
            }
        }
    }
}
