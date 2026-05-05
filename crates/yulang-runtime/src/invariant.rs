use yulang_core_ir as core_ir;

use crate::diagnostic::{RuntimeError, RuntimeResult};
use crate::ir::{
    Expr, ExprKind, MatchArm, Module, Pattern, RecordExprField, RecordPatternField,
    RecordSpreadExpr, RecordSpreadPattern, Stmt, Type as RuntimeType,
};
use crate::types::{core_type_is_runtime_projection_fallback, effect_is_empty};

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
    let mut checker = InvariantChecker {
        stage,
        strict_value_types: false,
    };
    for binding in &module.bindings {
        if matches!(stage, RuntimeStage::BeforeVm) && !binding.type_params.is_empty() {
            return Err(RuntimeError::InvariantViolation {
                stage: stage.name(),
                context: format!("binding {}", path_name(&binding.name)),
                message: "VM input binding must be monomorphic",
            });
        }
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

pub fn check_strict_runtime_value_types(module: &Module, stage: RuntimeStage) -> RuntimeResult<()> {
    let mut checker = InvariantChecker {
        stage,
        strict_value_types: true,
    };
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
    strict_value_types: bool,
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
                if self.strict_value_types
                    && matches!(self.stage, RuntimeStage::BeforeVm)
                    && runtime_type_has_runtime_fallback_in_value_position(value)
                {
                    return self.fail(
                        context,
                        "VM thunk value type must not contain runtime fallback Any",
                    );
                }
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
            ExprKind::Coerce {
                expr: inner,
                from,
                to,
            } => {
                if self.strict_value_types
                    && matches!(self.stage, RuntimeStage::BeforeVm)
                    && (core_type_has_runtime_fallback_in_value_position(from, false)
                        || core_type_has_runtime_fallback_in_value_position(to, false))
                {
                    return self.fail(
                        context,
                        "VM coerce type must not contain runtime fallback Any",
                    );
                }
                self.expr(inner, format!("{context}/coerce"))
            }
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

fn runtime_type_has_runtime_fallback_in_value_position(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => true,
        RuntimeType::Core(ty) => core_type_has_runtime_fallback_in_value_position(ty, false),
        RuntimeType::Fun { param, ret } => {
            runtime_type_has_runtime_fallback_in_value_position(param)
                || runtime_type_has_runtime_fallback_in_value_position(ret)
        }
        RuntimeType::Thunk { value, .. } => {
            runtime_type_has_runtime_fallback_in_value_position(value)
        }
    }
}

fn core_type_has_runtime_fallback_in_value_position(ty: &core_ir::Type, effect_slot: bool) -> bool {
    match ty {
        core_ir::Type::Unknown => !effect_slot,
        core_ir::Type::Any => !effect_slot && core_type_is_runtime_projection_fallback(ty),
        core_ir::Type::Named { args, .. } => {
            args.iter().any(|arg| match arg {
                core_ir::TypeArg::Type(ty) => {
                    core_type_has_runtime_fallback_in_value_position(ty, false)
                }
                core_ir::TypeArg::Bounds(bounds) => {
                    bounds.lower.as_deref().is_some_and(|ty| {
                        core_type_has_runtime_fallback_in_value_position(ty, false)
                    }) || bounds.upper.as_deref().is_some_and(|ty| {
                        core_type_has_runtime_fallback_in_value_position(ty, false)
                    })
                }
            })
        }
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_has_runtime_fallback_in_value_position(param, false)
                || core_type_has_runtime_fallback_in_value_position(param_effect, true)
                || core_type_has_runtime_fallback_in_value_position(ret_effect, true)
                || core_type_has_runtime_fallback_in_value_position(ret, false)
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            items
                .iter()
                .any(|item| core_type_has_runtime_fallback_in_value_position(item, false))
        }
        core_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_type_has_runtime_fallback_in_value_position(&field.value, false))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        core_type_has_runtime_fallback_in_value_position(ty, false)
                    }
                })
        }
        core_ir::Type::Variant(variant) => {
            variant.cases.iter().any(|case| {
                case.payloads
                    .iter()
                    .any(|payload| core_type_has_runtime_fallback_in_value_position(payload, false))
            }) || variant
                .tail
                .as_deref()
                .is_some_and(|tail| core_type_has_runtime_fallback_in_value_position(tail, false))
        }
        core_ir::Type::Row { items, tail } => {
            items
                .iter()
                .any(|item| core_type_has_runtime_fallback_in_value_position(item, true))
                || core_type_has_runtime_fallback_in_value_position(tail, true)
        }
        core_ir::Type::Recursive { body, .. } => {
            core_type_has_runtime_fallback_in_value_position(body, effect_slot)
        }
        core_ir::Type::Var(_) | core_ir::Type::Never => false,
    }
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

    #[test]
    fn rejects_polymorphic_binding_before_vm() {
        let mut module = module_with_expr(Expr::typed(ExprKind::Lit(core_ir::Lit::Unit), unit()));
        module.bindings[0].type_params = vec![core_ir::TypeVar("a".to_string())];

        let err = check_runtime_invariants(&module, RuntimeStage::BeforeVm).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "VM input binding must be monomorphic",
                ..
            }
        ));
    }

    #[test]
    fn rejects_any_thunk_value_type_before_vm() {
        let module = module_with_expr(Expr::typed(
            ExprKind::Thunk {
                effect: named("io"),
                value: RuntimeType::core(core_ir::Type::Unknown),
                expr: Box::new(Expr::typed(ExprKind::Lit(core_ir::Lit::Unit), unit())),
            },
            RuntimeType::thunk(named("io"), RuntimeType::core(core_ir::Type::Unknown)),
        ));

        let err = check_strict_runtime_value_types(&module, RuntimeStage::BeforeVm).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "VM thunk value type must not contain runtime fallback Any",
                ..
            }
        ));
    }

    #[test]
    fn rejects_any_coerce_type_before_vm() {
        let module = module_with_expr(Expr::typed(
            ExprKind::Coerce {
                from: unit(),
                to: core_ir::Type::Unknown,
                expr: Box::new(Expr::typed(ExprKind::Lit(core_ir::Lit::Unit), unit())),
            },
            unit(),
        ));

        let err = check_strict_runtime_value_types(&module, RuntimeStage::BeforeVm).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "VM coerce type must not contain runtime fallback Any",
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
