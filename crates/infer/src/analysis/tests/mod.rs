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
    Neg, Neu, NeuId, Pos, Scheme, SchemeRecursiveBound, SubtractId, Subtractability, TypeVar,
};

mod case_01;
mod case_02;
mod case_03;
