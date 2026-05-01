use super::*;

impl RefineRewriter {
    pub(super) fn cast_if_needed(&self, expr: Expr, expected: Option<&RuntimeType>) -> Expr {
        let Some(expected) = expected else {
            return expr;
        };
        let expected = substitute_hir_type(expected, &self.substitutions);
        let (expected_core, actual_core) = match (&expected, &expr.ty) {
            (RuntimeType::Core(expected_core), RuntimeType::Core(actual_core)) => {
                (expected_core.clone(), actual_core.clone())
            }
            _ => return expr,
        };
        if expected_core == actual_core || type_compatible(&expected_core, &actual_core) {
            return expr;
        }
        if !needs_runtime_coercion(&expected_core, &actual_core) {
            return expr;
        }
        Expr {
            ty: expected,
            kind: ExprKind::Coerce {
                from: actual_core,
                to: expected_core,
                expr: Box::new(expr),
            },
        }
    }
}
