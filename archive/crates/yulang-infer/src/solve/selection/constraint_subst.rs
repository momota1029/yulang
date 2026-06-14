use crate::ids::TypeVar;
use crate::scheme::{subst_neg_id, subst_pos_id};

use super::{Infer, RoleConstraint, RoleConstraintArg};

pub(super) fn subst_role_constraint(
    infer: &Infer,
    constraint: &RoleConstraint,
    subst: &[(TypeVar, TypeVar)],
) -> RoleConstraint {
    RoleConstraint {
        role: constraint.role.clone(),
        args: constraint
            .args
            .iter()
            .map(|arg| RoleConstraintArg {
                pos: subst_pos_id(infer, arg.pos, subst),
                neg: subst_neg_id(infer, arg.neg, subst),
            })
            .collect(),
    }
}
