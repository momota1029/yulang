use super::*;

pub(super) fn value_hir_type(ty: &RuntimeType) -> &RuntimeType {
    match ty {
        RuntimeType::Thunk { value, .. } => value,
        other => other,
    }
}

pub(super) fn value_core_type(ty: &RuntimeType) -> &core_ir::Type {
    core_type(value_hir_type(ty))
}

pub(super) fn force_value_expr(expr: Expr) -> (Expr, RuntimeType) {
    let value_ty = value_hir_type(&expr.ty).clone();
    let expr = bind_here_if_thunk(expr, value_ty.clone());
    (expr, value_ty)
}

pub(super) fn force_core_value_expr(expr: Expr) -> (Expr, core_ir::Type) {
    let (expr, ty) = force_value_expr(expr);
    let ty = core_type(&ty).clone();
    (expr, ty)
}
