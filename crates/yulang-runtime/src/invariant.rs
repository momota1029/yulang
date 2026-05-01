use yulang_core_ir as core_ir;

use crate::diagnostic::{RuntimeError, RuntimeResult};
use crate::ir::{
    Expr, ExprKind, MatchArm, Module, Pattern, RecordExprField, RecordPatternField,
    RecordSpreadExpr, RecordSpreadPattern, Stmt, Type as RuntimeType,
};
use crate::types::effect_is_empty;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeStage {
    Lowered,
    Monomorphized,
    BeforeVm,
}

impl RuntimeStage {
    fn name(self) -> &'static str {
        match self {
            RuntimeStage::Lowered => "runtime lowering",
            RuntimeStage::Monomorphized => "monomorphization",
            RuntimeStage::BeforeVm => "VM erase",
        }
    }
}

pub fn check_runtime_invariants(module: &Module, stage: RuntimeStage) -> RuntimeResult<()> {
    let mut checker = InvariantChecker { stage };
    for binding in &module.bindings {
        checker.expr(
            &binding.body,
            format!("binding {}", path_name(&binding.name)),
        )?;
    }
    for (index, expr) in module.root_exprs.iter().enumerate() {
        checker.expr(expr, format!("root #{index}"))?;
    }
    Ok(())
}

struct InvariantChecker {
    stage: RuntimeStage,
}

impl InvariantChecker {
    fn expr(&mut self, expr: &Expr, context: String) -> RuntimeResult<()> {
        match &expr.kind {
            ExprKind::Lambda { body, .. } => self.expr(body, format!("{context}/lambda")),
            ExprKind::Apply { callee, arg, .. } => {
                self.expr(callee, format!("{context}/apply.callee"))?;
                self.expr(arg, format!("{context}/apply.arg"))
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.expr(cond, format!("{context}/if.cond"))?;
                self.expr(then_branch, format!("{context}/if.then"))?;
                self.expr(else_branch, format!("{context}/if.else"))
            }
            ExprKind::Tuple(items) => {
                for (index, item) in items.iter().enumerate() {
                    self.expr(item, format!("{context}/tuple[{index}]"))?;
                }
                Ok(())
            }
            ExprKind::Record { fields, spread } => {
                for RecordExprField { name, value } in fields {
                    self.expr(value, format!("{context}/record.{}", name.0))?;
                }
                self.record_spread(spread, context)
            }
            ExprKind::Variant { value, .. } => {
                if let Some(value) = value {
                    self.expr(value, format!("{context}/variant"))?;
                }
                Ok(())
            }
            ExprKind::Select { base, .. } => self.expr(base, format!("{context}/select")),
            ExprKind::Match {
                scrutinee, arms, ..
            } => {
                self.expr(scrutinee, format!("{context}/match.scrutinee"))?;
                for (index, arm) in arms.iter().enumerate() {
                    self.match_arm(arm, format!("{context}/match.arm[{index}]"))?;
                }
                Ok(())
            }
            ExprKind::Block { stmts, tail } => {
                for (index, stmt) in stmts.iter().enumerate() {
                    self.stmt(stmt, format!("{context}/stmt[{index}]"))?;
                }
                if let Some(tail) = tail {
                    self.expr(tail, format!("{context}/tail"))?;
                }
                Ok(())
            }
            ExprKind::Handle {
                body,
                arms,
                handler,
                ..
            } => {
                if !handler.consumes.is_empty() && !matches!(body.ty, RuntimeType::Thunk { .. }) {
                    return self.fail(context, "effectful handler body must be a thunk");
                }
                self.expr(body, format!("{context}/handle.body"))?;
                for (index, arm) in arms.iter().enumerate() {
                    self.pattern(
                        &arm.payload,
                        format!("{context}/handle.arm[{index}].payload"),
                    )?;
                    if let Some(guard) = &arm.guard {
                        self.expr(guard, format!("{context}/handle.arm[{index}].guard"))?;
                    }
                    self.expr(&arm.body, format!("{context}/handle.arm[{index}].body"))?;
                }
                Ok(())
            }
            ExprKind::BindHere { expr: inner } => {
                if !matches!(inner.ty, RuntimeType::Thunk { .. }) {
                    return self.fail(context, "bind_here must force a thunk");
                }
                self.expr(inner, format!("{context}/bind_here"))
            }
            ExprKind::Thunk {
                effect,
                value,
                expr: inner,
            } => {
                match &expr.ty {
                    RuntimeType::Thunk {
                        effect: ty_effect,
                        value: ty_value,
                    } if ty_effect == effect && ty_value.as_ref() == value => {}
                    RuntimeType::Thunk { .. } => {
                        return self.fail(context, "thunk node type must match thunk payload");
                    }
                    _ => return self.fail(context, "thunk node must have thunk type"),
                }
                self.expr(inner, format!("{context}/thunk"))
            }
            ExprKind::LocalPushId { body, .. } => {
                self.expr(body, format!("{context}/local_push_id"))
            }
            ExprKind::AddId { allowed, thunk, .. } => {
                if matches!(thunk.ty, RuntimeType::Thunk { .. }) {
                    if effect_is_empty(allowed) {
                        return self.fail(context, "add_id allowed effect must not be empty");
                    }
                    self.expr(thunk, format!("{context}/add_id"))
                } else {
                    self.fail(context, "add_id must wrap a thunk")
                }
            }
            ExprKind::Coerce { expr: inner, .. } => self.expr(inner, format!("{context}/coerce")),
            ExprKind::Pack { expr: inner, .. } => self.expr(inner, format!("{context}/pack")),
            ExprKind::Var(_)
            | ExprKind::EffectOp(_)
            | ExprKind::PrimitiveOp(_)
            | ExprKind::Lit(_)
            | ExprKind::PeekId
            | ExprKind::FindId { .. } => Ok(()),
        }
    }

    fn stmt(&mut self, stmt: &Stmt, context: String) -> RuntimeResult<()> {
        match stmt {
            Stmt::Let { pattern, value } => {
                self.pattern(pattern, format!("{context}/pattern"))?;
                self.expr(value, format!("{context}/let.value"))
            }
            Stmt::Expr(expr) => self.expr(expr, context),
            Stmt::Module { body, .. } => self.expr(body, format!("{context}/module")),
        }
    }

    fn match_arm(&mut self, arm: &MatchArm, context: String) -> RuntimeResult<()> {
        self.pattern(&arm.pattern, format!("{context}/pattern"))?;
        if let Some(guard) = &arm.guard {
            self.expr(guard, format!("{context}/guard"))?;
        }
        self.expr(&arm.body, format!("{context}/body"))
    }

    fn pattern(&mut self, pattern: &Pattern, context: String) -> RuntimeResult<()> {
        match pattern {
            Pattern::Tuple { items, .. } | Pattern::List { prefix: items, .. } => {
                for (index, item) in items.iter().enumerate() {
                    self.pattern(item, format!("{context}[{index}]"))?;
                }
                if let Pattern::List { spread, suffix, .. } = pattern {
                    if let Some(spread) = spread {
                        self.pattern(spread, format!("{context}/spread"))?;
                    }
                    for (index, item) in suffix.iter().enumerate() {
                        self.pattern(item, format!("{context}/suffix[{index}]"))?;
                    }
                }
                Ok(())
            }
            Pattern::Record { fields, spread, .. } => {
                for RecordPatternField {
                    name,
                    pattern,
                    default,
                } in fields
                {
                    self.pattern(pattern, format!("{context}.{}", name.0))?;
                    if let Some(default) = default {
                        self.expr(default, format!("{context}.{}.default", name.0))?;
                    }
                }
                self.record_pattern_spread(spread, context)
            }
            Pattern::Variant { value, .. } => {
                if let Some(value) = value {
                    self.pattern(value, format!("{context}/variant"))?;
                }
                Ok(())
            }
            Pattern::Or { left, right, .. } => {
                self.pattern(left, format!("{context}/or.left"))?;
                self.pattern(right, format!("{context}/or.right"))
            }
            Pattern::As { pattern, .. } => self.pattern(pattern, format!("{context}/as")),
            Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => Ok(()),
        }
    }

    fn record_spread(
        &mut self,
        spread: &Option<RecordSpreadExpr>,
        context: String,
    ) -> RuntimeResult<()> {
        match spread {
            Some(RecordSpreadExpr::Head(expr)) => self.expr(expr, format!("{context}/spread.head")),
            Some(RecordSpreadExpr::Tail(expr)) => self.expr(expr, format!("{context}/spread.tail")),
            None => Ok(()),
        }
    }

    fn record_pattern_spread(
        &mut self,
        spread: &Option<RecordSpreadPattern>,
        context: String,
    ) -> RuntimeResult<()> {
        match spread {
            Some(RecordSpreadPattern::Head(pattern)) => {
                self.pattern(pattern, format!("{context}/spread.head"))
            }
            Some(RecordSpreadPattern::Tail(pattern)) => {
                self.pattern(pattern, format!("{context}/spread.tail"))
            }
            None => Ok(()),
        }
    }

    fn fail<T>(&self, context: String, message: &'static str) -> RuntimeResult<T> {
        Err(RuntimeError::InvariantViolation {
            stage: self.stage.name(),
            context,
            message,
        })
    }
}

fn path_name(path: &core_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Binding, EffectIdRef, Root};

    #[test]
    fn rejects_add_id_that_does_not_wrap_thunk() {
        let module = module_with_expr(Expr::typed(
            ExprKind::AddId {
                id: EffectIdRef::Peek,
                allowed: named("io"),
                thunk: Box::new(Expr::typed(ExprKind::Lit(core_ir::Lit::Unit), unit())),
            },
            unit(),
        ));

        let err = check_runtime_invariants(&module, RuntimeStage::Lowered).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "add_id must wrap a thunk",
                ..
            }
        ));
    }

    #[test]
    fn rejects_bind_here_that_does_not_force_thunk() {
        let module = module_with_expr(Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(Expr::typed(ExprKind::Lit(core_ir::Lit::Unit), unit())),
            },
            unit(),
        ));

        let err = check_runtime_invariants(&module, RuntimeStage::Lowered).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "bind_here must force a thunk",
                ..
            }
        ));
    }

    #[test]
    fn rejects_thunk_node_with_mismatched_type() {
        let module = module_with_expr(Expr::typed(
            ExprKind::Thunk {
                effect: named("io"),
                value: RuntimeType::core(unit()),
                expr: Box::new(Expr::typed(ExprKind::Lit(core_ir::Lit::Unit), unit())),
            },
            RuntimeType::thunk(named("other"), RuntimeType::core(unit())),
        ));

        let err = check_runtime_invariants(&module, RuntimeStage::Lowered).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "thunk node type must match thunk payload",
                ..
            }
        ));
    }

    fn module_with_expr(expr: Expr) -> Module {
        Module {
            path: core_ir::Path::default(),
            bindings: vec![Binding {
                name: core_ir::Path::from_name(core_ir::Name("main".to_string())),
                type_params: Vec::new(),
                scheme: core_ir::Scheme {
                    requirements: Vec::new(),
                    body: unit(),
                },
                body: expr,
            }],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(core_ir::Path::from_name(core_ir::Name(
                "main".to_string(),
            )))],
        }
    }

    fn unit() -> core_ir::Type {
        named("unit")
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }
}
