use super::*;

impl RefineRewriter {
    pub(super) fn stmt(&mut self, stmt: Stmt) -> Stmt {
        match stmt {
            Stmt::Let { pattern, value } => {
                let pattern = self.pattern(pattern);
                let expected = pattern_type(&pattern);
                Stmt::Let {
                    pattern,
                    value: self.expr(value, expected.as_ref()),
                }
            }
            Stmt::Expr(expr) => Stmt::Expr(self.expr(expr, None)),
            Stmt::Module { def, body } => {
                let body_ty = substitute_hir_type(&body.ty, &self.substitutions);
                let previous = push_binding(&mut self.locals, def.clone(), body_ty.clone());
                let body = self.expr(body, Some(&body_ty));
                pop_bindings(&mut self.locals, previous);
                Stmt::Module { def, body }
            }
        }
    }
}
