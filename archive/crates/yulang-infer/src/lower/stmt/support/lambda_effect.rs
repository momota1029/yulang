use crate::ast::expr::TypedExpr;
use crate::ids::{DefId, TypeVar};
use crate::lower::LowerState;

pub(crate) fn lambda_expr_eff_tv(
    state: &mut LowerState,
    _body: &TypedExpr,
    _local_defs: &[DefId],
) -> TypeVar {
    state.fresh_exact_pure_eff_tv()
}
