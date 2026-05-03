use super::Infer;
use crate::diagnostic::{
    ConstraintCause, ConstraintReason, TypeError, TypeErrorKind, TypeOrigin, origin_vars,
};
use crate::ids::{NegId, PosId, TypeVar};
use crate::types::Pos;

impl Infer {
    pub(super) fn report_type_error(
        &self,
        pos: PosId,
        neg: NegId,
        cause: &ConstraintCause,
        origin_hint: Option<TypeVar>,
        kind: TypeErrorKind,
    ) {
        let origin_tvs = origin_vars(self, pos, neg);
        let mut all_tvs = origin_tvs;
        if let Some(tv) = origin_hint {
            if !all_tvs.contains(&tv) {
                all_tvs.push(tv);
            }
        }
        let origins = all_tvs
            .into_iter()
            .filter_map(|tv| self.origin_of(tv))
            .fold(Vec::<TypeOrigin>::new(), |mut out, origin| {
                if !out.contains(&origin) {
                    out.push(origin);
                }
                out
            });
        let error = TypeError {
            cause: cause.clone(),
            kind,
            pos,
            neg,
            origins,
        };
        let mut errors = self.errors.borrow_mut();
        if let Some(existing) = errors.iter_mut().find(|existing| {
            existing.kind == error.kind && existing.pos == error.pos && existing.neg == error.neg
        }) {
            if constraint_reason_priority(error.cause.reason.clone())
                > constraint_reason_priority(existing.cause.reason.clone())
            {
                existing.cause = error.cause.clone();
            }
            for origin in error.origins {
                if !existing.origins.contains(&origin) {
                    existing.origins.push(origin);
                }
            }
        } else {
            errors.push(error);
        }
    }
}

pub(super) fn should_report_expected_function(pos: &Pos) -> bool {
    matches!(
        pos,
        Pos::Con(..)
            | Pos::Record(..)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(..)
            | Pos::Tuple(..)
            | Pos::Row(..)
            | Pos::Atom(..)
    )
}

pub(super) fn should_report_expected_tuple(pos: &Pos) -> bool {
    matches!(
        pos,
        Pos::Con(..)
            | Pos::Record(..)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(..)
            | Pos::Fun { .. }
            | Pos::Row(..)
            | Pos::Atom(..)
    )
}

pub(super) fn should_report_expected_record(pos: &Pos) -> bool {
    matches!(
        pos,
        Pos::Con(..)
            | Pos::PolyVariant(..)
            | Pos::Fun { .. }
            | Pos::Tuple(..)
            | Pos::Row(..)
            | Pos::Atom(..)
    )
}

pub(super) fn should_report_expected_constructor(pos: &Pos) -> bool {
    matches!(
        pos,
        Pos::Record(..)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(..)
            | Pos::Fun { .. }
            | Pos::Tuple(..)
            | Pos::Row(..)
            | Pos::Atom(..)
    )
}

fn constraint_reason_priority(reason: ConstraintReason) -> u8 {
    match reason {
        ConstraintReason::Annotation => 5,
        ConstraintReason::ApplyArg
        | ConstraintReason::ApplyFunction
        | ConstraintReason::RepresentationCoerce
        | ConstraintReason::ImplMember
        | ConstraintReason::IfCondition
        | ConstraintReason::IfBranch
        | ConstraintReason::MatchGuard
        | ConstraintReason::MatchBranch
        | ConstraintReason::CatchGuard
        | ConstraintReason::CatchBranch
        | ConstraintReason::AssignmentValue
        | ConstraintReason::FieldSelection => 4,
        ConstraintReason::Structural | ConstraintReason::RowCompare => 3,
        ConstraintReason::BindingBody => 2,
        ConstraintReason::Unknown => 1,
    }
}

pub(super) fn should_revisit_existing_constraint(cause: &ConstraintCause) -> bool {
    constraint_reason_priority(cause.reason.clone())
        > constraint_reason_priority(ConstraintReason::Unknown)
}
