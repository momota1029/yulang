use std::collections::{HashMap, HashSet};

use yulang_runtime_ir::{Binding, Expr, ExprKind, Module, Root, Stmt, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::diagnostic::{FinalizeDiagnostic, FinalizeError, FinalizeResult, ValidationReason};
use crate::effect::{handler_output_type, runtime_value_type, should_thunk_effect};
use crate::output::FinalizeOutput;
use crate::types::runtime_types_match;

pub fn validate_finalized_output(output: &FinalizeOutput) -> FinalizeResult<()> {
    let bindings = output
        .module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    let mut checked = HashSet::new();
    for root in &output.report.root_instances {
        checked.insert(root.alias.clone());
        let Some(binding) = bindings.get(&root.alias) else {
            return validation_err(ValidationReason::MissingBinding {
                binding: root.alias.clone(),
            });
        };
        validate_closed_binding(binding, &bindings)?;
    }
    for root in &output.module.roots {
        match root {
            Root::Binding(path) if checked.contains(path) => {}
            Root::Binding(path) if !bindings.contains_key(path) => {
                return validation_err(ValidationReason::MissingBinding {
                    binding: path.clone(),
                });
            }
            Root::Binding(_) => {}
            Root::Expr(index) => {
                let Some(expr) = output.module.root_exprs.get(*index) else {
                    return validation_err(ValidationReason::InvalidRootExpr { index: *index });
                };
                validate_expr(expr, &bindings, &mut HashMap::new())?;
            }
        }
    }
    Ok(())
}

pub fn validate_closed_module(module: &Module) -> FinalizeResult<()> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    for binding in &module.bindings {
        if binding.type_params.is_empty() {
            validate_closed_binding(binding, &bindings)?;
        }
    }
    for (index, expr) in module.root_exprs.iter().enumerate() {
        validate_expr(expr, &bindings, &mut HashMap::new()).map_err(|_| {
            FinalizeError::Diagnostic(FinalizeDiagnostic::Validation {
                reason: ValidationReason::InvalidRootExpr { index },
            })
        })?;
    }
    Ok(())
}

fn validate_closed_binding(
    binding: &Binding,
    bindings: &HashMap<typed_ir::Path, &Binding>,
) -> FinalizeResult<()> {
    if !binding.type_params.is_empty() {
        return Ok(());
    }
    require_closed_runtime_type(&binding.body.ty)?;
    require_closed_core_type(&binding.scheme.body)?;
    let expected = runtime_type_from_scheme(&binding.scheme.body);
    require_runtime_type(&expected, &binding.body.ty)?;
    validate_expr(&binding.body, bindings, &mut HashMap::new())
}

fn validate_expr(
    expr: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
) -> FinalizeResult<()> {
    require_closed_runtime_type(&expr.ty)?;
    match &expr.kind {
        ExprKind::Var(path) => {
            if let Some(expected) = locals
                .get(path)
                .cloned()
                .or_else(|| bindings.get(path).map(|binding| binding.body.ty.clone()))
            {
                require_runtime_type(&expected, &expr.ty)?;
            } else {
                return validation_err(ValidationReason::UnboundVariable { path: path.clone() });
            }
        }
        ExprKind::EffectOp(path) => {
            if path.segments.is_empty() {
                return validation_err(ValidationReason::UnboundVariable { path: path.clone() });
            }
        }
        ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
        ExprKind::Lambda { param, body, .. } => {
            let RuntimeType::Fun {
                param: param_ty,
                ret,
            } = &expr.ty
            else {
                return validation_err(ValidationReason::NonFunctionCallee {
                    ty: expr.ty.clone(),
                });
            };
            let local = typed_ir::Path::from_name(param.clone());
            let previous = locals.insert(local.clone(), param_ty.as_ref().clone());
            validate_expr(body, bindings, locals)?;
            require_runtime_type(ret, &body.ty)?;
            restore_local(locals, local, previous);
        }
        ExprKind::Apply { callee, arg, .. } => {
            validate_expr(callee, bindings, locals)?;
            validate_expr(arg, bindings, locals)?;
            let RuntimeType::Fun { param, ret } = &callee.ty else {
                return validation_err(ValidationReason::NonFunctionCallee {
                    ty: callee.ty.clone(),
                });
            };
            require_runtime_type(param, &arg.ty)?;
            require_runtime_type(ret, &expr.ty)?;
        }
        ExprKind::Tuple(items) => {
            for item in items {
                validate_expr(item, bindings, locals)?;
            }
        }
        ExprKind::Block { stmts, tail } => {
            let mut block_locals = locals.clone();
            for stmt in stmts {
                validate_stmt(stmt, bindings, &mut block_locals)?;
            }
            if let Some(tail) = tail {
                validate_expr(tail, bindings, &mut block_locals)?;
                require_runtime_type(&expr.ty, &tail.ty)?;
            }
        }
        ExprKind::Thunk {
            effect,
            value,
            expr: inner,
        } => {
            require_closed_core_type(effect)?;
            require_closed_runtime_type(value)?;
            validate_expr(inner, bindings, locals)?;
            require_runtime_type(value, &inner.ty)?;
            require_runtime_type(
                &RuntimeType::Thunk {
                    effect: effect.clone(),
                    value: Box::new(value.clone()),
                },
                &expr.ty,
            )?;
        }
        ExprKind::BindHere { expr: inner } => {
            validate_expr(inner, bindings, locals)?;
            let RuntimeType::Thunk { value, .. } = &inner.ty else {
                return validation_err(ValidationReason::ExpectedThunk {
                    ty: inner.ty.clone(),
                });
            };
            require_runtime_type(value, &expr.ty)?;
        }
        ExprKind::Handle {
            body,
            arms,
            handler,
            ..
        } => {
            validate_expr(body, bindings, locals)?;
            if !handler.consumes.is_empty() && !matches!(body.ty, RuntimeType::Thunk { .. }) {
                return validation_err(ValidationReason::ExpectedThunk {
                    ty: body.ty.clone(),
                });
            }
            for arm in arms {
                let mut arm_locals = locals.clone();
                validate_pattern(&arm.payload, &mut arm_locals)?;
                if let Some(resume) = &arm.resume {
                    require_closed_runtime_type(&resume.ty)?;
                    arm_locals.insert(
                        typed_ir::Path::from_name(resume.name.clone()),
                        resume.ty.clone(),
                    );
                }
                if let Some(guard) = &arm.guard {
                    validate_expr(guard, bindings, &mut arm_locals)?;
                }
                validate_expr(&arm.body, bindings, &mut arm_locals)?;
            }
            require_runtime_type(&handler_output_type(&body.ty, handler), &expr.ty)?;
        }
        ExprKind::LocalPushId { body, .. } => {
            validate_expr(body, bindings, locals)?;
            require_runtime_type(&body.ty, &expr.ty)?;
        }
        ExprKind::AddId { allowed, thunk, .. } => {
            require_closed_core_type(allowed)?;
            validate_expr(thunk, bindings, locals)?;
            require_runtime_type(&thunk.ty, &expr.ty)?;
        }
        ExprKind::Coerce {
            from,
            to,
            expr: inner,
        } => {
            require_closed_core_type(from)?;
            require_closed_core_type(to)?;
            validate_expr(inner, bindings, locals)?;
            require_runtime_type(&RuntimeType::Core(to.clone()), &expr.ty)?;
        }
        ExprKind::Pack { expr: inner, .. } => {
            validate_expr(inner, bindings, locals)?;
            require_runtime_type(&inner.ty, &expr.ty)?;
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                validate_expr(&field.value, bindings, locals)?;
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_runtime_ir::RecordSpreadExpr::Head(expr)
                    | yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => {
                        validate_expr(expr, bindings, locals)?;
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                validate_expr(value, bindings, locals)?;
            }
        }
        ExprKind::Select { base, .. } => validate_expr(base, bindings, locals)?,
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => {
            validate_expr(cond, bindings, locals)?;
            validate_expr(then_branch, bindings, locals)?;
            validate_expr(else_branch, bindings, locals)?;
            let expected_value = runtime_value_type(&expr.ty);
            if let Some(evidence) = evidence {
                require_closed_core_type(&evidence.result)?;
                require_runtime_type(&RuntimeType::Core(evidence.result.clone()), &expected_value)?;
            }
            require_join_branch_type(&expected_value, &then_branch.ty)?;
            require_join_branch_type(&expected_value, &else_branch.ty)?;
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            validate_expr(scrutinee, bindings, locals)?;
            for arm in arms {
                let mut arm_locals = locals.clone();
                validate_pattern(&arm.pattern, &mut arm_locals)?;
                if let Some(guard) = &arm.guard {
                    validate_expr(guard, bindings, &mut arm_locals)?;
                }
                validate_expr(&arm.body, bindings, &mut arm_locals)?;
                require_runtime_type(&expr.ty, &arm.body.ty)?;
            }
        }
    }
    Ok(())
}

fn validate_stmt(
    stmt: &Stmt,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
) -> FinalizeResult<()> {
    match stmt {
        Stmt::Let { pattern, value } => {
            validate_expr(value, bindings, locals)?;
            validate_pattern(pattern, locals)
        }
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => validate_expr(expr, bindings, locals),
    }
}

fn validate_pattern(
    pattern: &yulang_runtime_ir::Pattern,
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
) -> FinalizeResult<()> {
    require_closed_runtime_type(pattern_type(pattern))?;
    match pattern {
        yulang_runtime_ir::Pattern::Bind { name, ty } => {
            locals.insert(typed_ir::Path::from_name(name.clone()), ty.clone());
        }
        yulang_runtime_ir::Pattern::Tuple { items, .. } => {
            for item in items {
                validate_pattern(item, locals)?;
            }
        }
        yulang_runtime_ir::Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                validate_pattern(value, locals)?;
            }
        }
        yulang_runtime_ir::Pattern::As { pattern, name, ty } => {
            validate_pattern(pattern, locals)?;
            locals.insert(typed_ir::Path::from_name(name.clone()), ty.clone());
        }
        yulang_runtime_ir::Pattern::Wildcard { .. }
        | yulang_runtime_ir::Pattern::Lit { .. }
        | yulang_runtime_ir::Pattern::List { .. }
        | yulang_runtime_ir::Pattern::Record { .. }
        | yulang_runtime_ir::Pattern::Or { .. } => {}
    }
    Ok(())
}

fn runtime_type_from_scheme(ty: &typed_ir::Type) -> RuntimeType {
    match ty {
        typed_ir::Type::Fun {
            param,
            ret_effect,
            ret,
            ..
        } => {
            let ret = runtime_type_from_scheme(ret);
            let ret = if should_thunk_effect(ret_effect) {
                RuntimeType::Thunk {
                    effect: ret_effect.as_ref().clone(),
                    value: Box::new(ret),
                }
            } else {
                ret
            };
            RuntimeType::Fun {
                param: Box::new(RuntimeType::Core(param.as_ref().clone())),
                ret: Box::new(ret),
            }
        }
        ty => RuntimeType::Core(ty.clone()),
    }
}

fn pattern_type(pattern: &yulang_runtime_ir::Pattern) -> &RuntimeType {
    match pattern {
        yulang_runtime_ir::Pattern::Wildcard { ty }
        | yulang_runtime_ir::Pattern::Bind { ty, .. }
        | yulang_runtime_ir::Pattern::Lit { ty, .. }
        | yulang_runtime_ir::Pattern::Tuple { ty, .. }
        | yulang_runtime_ir::Pattern::List { ty, .. }
        | yulang_runtime_ir::Pattern::Record { ty, .. }
        | yulang_runtime_ir::Pattern::Variant { ty, .. }
        | yulang_runtime_ir::Pattern::Or { ty, .. }
        | yulang_runtime_ir::Pattern::As { ty, .. } => ty,
    }
}

fn require_runtime_type(expected: &RuntimeType, actual: &RuntimeType) -> FinalizeResult<()> {
    if runtime_types_match(expected, actual) {
        Ok(())
    } else {
        validation_err(ValidationReason::TypeMismatch {
            expected: expected.clone(),
            actual: actual.clone(),
        })
    }
}

fn require_join_branch_type(expected: &RuntimeType, actual: &RuntimeType) -> FinalizeResult<()> {
    let actual_value = runtime_value_type(actual);
    if runtime_types_match(expected, &actual_value)
        || matches!(actual_value, RuntimeType::Core(typed_ir::Type::Never))
    {
        Ok(())
    } else {
        validation_err(ValidationReason::TypeMismatch {
            expected: expected.clone(),
            actual: actual.clone(),
        })
    }
}

fn require_closed_runtime_type(ty: &RuntimeType) -> FinalizeResult<()> {
    if runtime_type_is_closed_strict(ty) {
        Ok(())
    } else {
        validation_err(ValidationReason::OpenRuntimeType { ty: ty.clone() })
    }
}

fn require_closed_core_type(ty: &typed_ir::Type) -> FinalizeResult<()> {
    if core_type_is_closed_strict(ty) {
        Ok(())
    } else {
        validation_err(ValidationReason::OpenCoreType { ty: ty.clone() })
    }
}

fn runtime_type_is_closed_strict(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => false,
        RuntimeType::Core(ty) => core_type_is_closed_strict(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_type_is_closed_strict(param) && runtime_type_is_closed_strict(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            core_type_is_closed_strict(effect) && runtime_type_is_closed_strict(value)
        }
    }
}

fn core_type_is_closed_strict(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Never => true,
        typed_ir::Type::Named { args, .. } => args.iter().all(type_arg_is_closed_strict),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_is_closed_strict(param)
                && core_type_is_closed_strict(param_effect)
                && core_type_is_closed_strict(ret_effect)
                && core_type_is_closed_strict(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().all(core_type_is_closed_strict),
        typed_ir::Type::Row { items, tail } => {
            items.iter().all(core_type_is_closed_strict) && core_type_is_closed_strict(tail)
        }
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .all(|field| core_type_is_closed_strict(&field.value))
                && record.spread.as_ref().is_none_or(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        core_type_is_closed_strict(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .all(|case| case.payloads.iter().all(core_type_is_closed_strict))
                && variant
                    .tail
                    .as_ref()
                    .is_none_or(|tail| core_type_is_closed_strict(tail))
        }
        typed_ir::Type::Recursive { body, .. } => core_type_is_closed_strict(body),
    }
}

fn type_arg_is_closed_strict(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => core_type_is_closed_strict(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_ref()
                .is_none_or(|ty| core_type_is_closed_strict(ty))
                && bounds
                    .upper
                    .as_ref()
                    .is_none_or(|ty| core_type_is_closed_strict(ty))
        }
    }
}

fn restore_local(
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
    local: typed_ir::Path,
    previous: Option<RuntimeType>,
) {
    match previous {
        Some(previous) => {
            locals.insert(local, previous);
        }
        None => {
            locals.remove(&local);
        }
    }
}

fn validation_err<T>(reason: ValidationReason) -> FinalizeResult<T> {
    Err(FinalizeError::Diagnostic(FinalizeDiagnostic::Validation {
        reason,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validator_accepts_closed_effectful_binding() {
        let module = Module {
            path: path(&["test"]),
            bindings: vec![effectful_binding()],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(path(&["effectful"]))],
            role_impls: Vec::new(),
        };

        validate_closed_module(&module).unwrap();
    }

    #[test]
    fn validator_accepts_effectful_if_condition_lifted_to_thunk() {
        let effect = io_effect();
        let expr = Expr::typed(
            ExprKind::Thunk {
                effect: effect.clone(),
                value: RuntimeType::Core(int_type()),
                expr: Box::new(Expr::typed(
                    ExprKind::If {
                        cond: Box::new(Expr::typed(
                            ExprKind::BindHere {
                                expr: Box::new(Expr::typed(
                                    ExprKind::Lit(typed_ir::Lit::Bool(true)),
                                    RuntimeType::Thunk {
                                        effect: effect.clone(),
                                        value: Box::new(RuntimeType::Core(bool_type())),
                                    },
                                )),
                            },
                            RuntimeType::Core(bool_type()),
                        )),
                        then_branch: Box::new(Expr::typed(
                            ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                            RuntimeType::Core(int_type()),
                        )),
                        else_branch: Box::new(Expr::typed(
                            ExprKind::Lit(typed_ir::Lit::Int("0".into())),
                            RuntimeType::Core(int_type()),
                        )),
                        evidence: Some(yulang_runtime_ir::JoinEvidence { result: int_type() }),
                    },
                    RuntimeType::Core(int_type()),
                )),
            },
            RuntimeType::Thunk {
                effect,
                value: Box::new(RuntimeType::Core(int_type())),
            },
        );
        let module = Module {
            path: path(&["test"]),
            bindings: Vec::new(),
            root_exprs: vec![expr],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        validate_closed_module(&module).unwrap();
    }

    #[test]
    fn validator_rejects_open_runtime_type() {
        let module = Module {
            path: path(&["test"]),
            bindings: vec![Binding {
                name: path(&["open"]),
                type_params: Vec::new(),
                scheme: typed_ir::Scheme {
                    requirements: Vec::new(),
                    body: function_type(
                        typed_ir::Type::Var(typed_ir::TypeVar("a".into())),
                        typed_ir::Type::Never,
                        int_type(),
                    ),
                },
                body: Expr::typed(
                    ExprKind::Lambda {
                        param: typed_ir::Name("x".into()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path(&["x"])),
                            RuntimeType::Core(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                        )),
                    },
                    RuntimeType::Fun {
                        param: Box::new(RuntimeType::Core(typed_ir::Type::Var(typed_ir::TypeVar(
                            "a".into(),
                        )))),
                        ret: Box::new(RuntimeType::Core(int_type())),
                    },
                ),
            }],
            root_exprs: Vec::new(),
            roots: Vec::new(),
            role_impls: Vec::new(),
        };

        let err = validate_closed_module(&module).unwrap_err();

        assert!(matches!(
            err,
            FinalizeError::Diagnostic(FinalizeDiagnostic::Validation {
                reason: ValidationReason::OpenRuntimeType { .. }
            })
        ));
    }

    #[test]
    fn validator_rejects_apply_result_mismatch() {
        let expr = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(path(&["id"])),
                    RuntimeType::Fun {
                        param: Box::new(RuntimeType::Core(int_type())),
                        ret: Box::new(RuntimeType::Core(int_type())),
                    },
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                    RuntimeType::Core(int_type()),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::Core(bool_type()),
        );
        let module = Module {
            path: path(&["test"]),
            bindings: vec![id_binding()],
            root_exprs: vec![expr],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let err = validate_closed_module(&module).unwrap_err();

        assert!(matches!(
            err,
            FinalizeError::Diagnostic(FinalizeDiagnostic::Validation {
                reason: ValidationReason::InvalidRootExpr { index: 0 }
            })
        ));
    }

    fn effectful_binding() -> Binding {
        Binding {
            name: path(&["effectful"]),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(int_type(), io_effect(), int_type()),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("x".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Thunk {
                            effect: io_effect(),
                            value: RuntimeType::Core(int_type()),
                            expr: Box::new(Expr::typed(
                                ExprKind::Var(path(&["x"])),
                                RuntimeType::Core(int_type()),
                            )),
                        },
                        RuntimeType::Thunk {
                            effect: io_effect(),
                            value: Box::new(RuntimeType::Core(int_type())),
                        },
                    )),
                },
                RuntimeType::Fun {
                    param: Box::new(RuntimeType::Core(int_type())),
                    ret: Box::new(RuntimeType::Thunk {
                        effect: io_effect(),
                        value: Box::new(RuntimeType::Core(int_type())),
                    }),
                },
            ),
        }
    }

    fn id_binding() -> Binding {
        Binding {
            name: path(&["id"]),
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: function_type(int_type(), typed_ir::Type::Never, int_type()),
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("x".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Var(path(&["x"])),
                        RuntimeType::Core(int_type()),
                    )),
                },
                RuntimeType::Fun {
                    param: Box::new(RuntimeType::Core(int_type())),
                    ret: Box::new(RuntimeType::Core(int_type())),
                },
            ),
        }
    }

    fn function_type(
        param: typed_ir::Type,
        ret_effect: typed_ir::Type,
        ret: typed_ir::Type,
    ) -> typed_ir::Type {
        typed_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(ret_effect),
            ret: Box::new(ret),
        }
    }

    fn int_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "int", "Int"]),
            args: Vec::new(),
        }
    }

    fn bool_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "bool", "Bool"]),
            args: Vec::new(),
        }
    }

    fn io_effect() -> typed_ir::Type {
        typed_ir::Type::Row {
            items: vec![typed_ir::Type::Named {
                path: path(&["io"]),
                args: Vec::new(),
            }],
            tail: Box::new(typed_ir::Type::Never),
        }
    }

    fn path(segments: &[&str]) -> typed_ir::Path {
        typed_ir::Path::new(
            segments
                .iter()
                .map(|segment| typed_ir::Name((*segment).into()))
                .collect(),
        )
    }
}
