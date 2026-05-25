use super::*;

impl RefineRewriter {
    pub(super) fn force_protected_thunk_result(&self, expr: Expr) -> Option<Expr> {
        let RuntimeType::Thunk { value, .. } = &expr.ty else {
            return None;
        };
        let expected_value = value.as_ref();
        match expr.kind {
            ExprKind::LocalPushId { id, body } => {
                let body = self.force_protected_thunk_body(*body, expected_value)?;
                Some(Expr {
                    ty: body.ty.clone(),
                    kind: ExprKind::LocalPushId {
                        id,
                        body: Box::new(body),
                    },
                })
            }
            _ => None,
        }
    }

    pub(super) fn force_protected_thunk_body(
        &self,
        expr: Expr,
        expected_value: &RuntimeType,
    ) -> Option<Expr> {
        match expr.kind {
            ExprKind::Block {
                stmts,
                tail: Some(tail),
            } => {
                let forced = self.force_protected_thunk_expr(*tail, expected_value)?;
                let ty = forced.ty.clone();
                Some(Expr {
                    ty,
                    kind: ExprKind::Block {
                        stmts,
                        tail: Some(Box::new(forced)),
                    },
                })
            }
            ExprKind::Block { mut stmts, tail } if tail.is_none() => {
                let last = stmts.pop()?;
                let Stmt::Expr(last) = last else {
                    return None;
                };
                let forced = self.force_protected_thunk_expr(last, expected_value)?;
                let ty = forced.ty.clone();
                stmts.push(Stmt::Expr(forced));
                Some(Expr {
                    ty,
                    kind: ExprKind::Block { stmts, tail: None },
                })
            }
            _ => self.force_protected_thunk_expr(expr, expected_value),
        }
    }

    pub(super) fn force_protected_thunk_expr(
        &self,
        expr: Expr,
        expected_value: &RuntimeType,
    ) -> Option<Expr> {
        let ExprKind::AddId { allowed, thunk, .. } = &expr.kind else {
            return None;
        };
        let RuntimeType::Thunk { value, .. } = &thunk.ty else {
            return None;
        };
        if !hir_type_compatible(expected_value, value) {
            return None;
        }
        let ExprKind::Thunk { expr: inner, .. } = &thunk.kind else {
            return None;
        };
        let head = applied_head_path(inner)?;
        let consumed = self.pure_handler_bindings.get(&head)?;
        let allowed = effect_paths(allowed);
        if !effect_path_sets_intersect(&allowed, consumed) {
            return None;
        }
        if !hir_type_produces_value(&inner.ty, expected_value) {
            return None;
        }
        Some(Expr {
            ty: expected_value.clone(),
            kind: ExprKind::BindHere {
                expr: Box::new(expr),
            },
        })
    }
}
