use super::*;

impl RefineRewriter {
    pub(super) fn initial_expr_type(
        &self,
        expr: &Expr,
        expected: Option<&RuntimeType>,
    ) -> RuntimeType {
        let original_ty = substitute_hir_type(&expr.ty, &self.substitutions);
        let constructor_expected = is_expected_nullary_constructor(expr, expected);
        let local_ty = expr_var_path(expr).and_then(|path| self.locals.get(path).cloned());
        let binding_ty = expr_var_path(expr)
            .filter(|path| {
                !constructor_expected && local_ty.is_none() && !is_data_constructor_path(path)
            })
            .and_then(|path| self.binding_types.get(path).cloned());
        let original_ty = local_ty.or(binding_ty.clone()).unwrap_or(original_ty);
        refine_expr_type_from_context(
            original_ty,
            binding_ty.as_ref(),
            expected,
            constructor_expected,
            &self.substitutions,
        )
    }
}

fn is_expected_nullary_constructor(expr: &Expr, expected: Option<&RuntimeType>) -> bool {
    match (&expr.kind, expected) {
        (ExprKind::Var(path), Some(expected)) => {
            is_nullary_constructor_path_for_type(path, expected)
        }
        _ => false,
    }
}

fn expr_var_path(expr: &Expr) -> Option<&core_ir::Path> {
    match &expr.kind {
        ExprKind::Var(path) => Some(path),
        _ => None,
    }
}

fn refine_expr_type_from_context(
    original_ty: RuntimeType,
    binding_ty: Option<&RuntimeType>,
    expected: Option<&RuntimeType>,
    constructor_expected: bool,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> RuntimeType {
    if constructor_expected {
        return expected
            .map(|expected| substitute_hir_type(expected, substitutions))
            .unwrap_or(original_ty);
    }
    if binding_ty.is_some_and(hir_type_has_vars) {
        return expected
            .map(|expected| substitute_hir_type(expected, substitutions))
            .filter(|expected| !hir_type_has_vars(expected) && !hir_type_is_core_never(expected))
            .unwrap_or(original_ty);
    }
    if binding_ty.is_some() {
        return original_ty;
    }
    expected
        .map(|expected| substitute_hir_type(expected, substitutions))
        .filter(|expected| {
            !hir_type_has_vars(expected)
                && !hir_type_is_core_never(&original_ty)
                && hir_type_compatible(expected, &original_ty)
        })
        .map(|expected| refine_expected_expr_type(&expected, &original_ty))
        .unwrap_or(original_ty)
}
