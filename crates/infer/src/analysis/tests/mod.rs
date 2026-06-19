use crate::compact::compact_type_var;
use poly::expr::SelectResolution;

use super::*;
use crate::constraints::{ConstraintWeight, ConstraintWeights};
use crate::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleImplCandidate,
};
use crate::uses::{RefUse, SelectionUse};
use poly::expr::{Arena as PolyArena, Expr, Lit, Vis};
use poly::types::{
    Neg, Neu, NeuId, Pos, Scheme, SchemeRecursiveBound, StackWeight, SubtractId, Subtractability,
    TypeVar,
};

mod case_01;
mod case_02;
mod case_03;

use case_03::{
    assert_concrete_role_residual_missing, assert_var_has_exact_bound,
    assert_var_lacks_exact_bound, generic_unary_cast_scheme, infer_bounds_neu,
    monomorphic_cast_scheme, role_exact_arg, role_left_concrete_var_arg, role_unary_con_exact_arg,
    role_unary_con_open_arg, role_unary_con_open_or_var_arg, role_unary_con_var_and_extra_arg,
    role_unary_con_var_arg, role_var_arg,
};
