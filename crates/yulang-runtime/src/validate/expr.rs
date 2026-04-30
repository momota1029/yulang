use super::*;

pub(super) fn validate_expr(
    expr: &Expr,
    bindings: &HashMap<core_ir::Path, BindingInfo>,
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
) -> RuntimeResult<()> {
    validate_hir_type_no_any(&expr.ty, TypeSource::Validation)?;
    match &expr.kind {
        ExprKind::Var(path) => {
            if let Some(expected) = locals
                .get(path)
                .or_else(|| bindings.get(path).map(|binding| &binding.ty))
            {
                if !is_constructor_path_for_type(path, &expr.ty) {
                    require_same_hir_type(expected, &expr.ty, TypeSource::Local)?;
                }
            } else if !is_qualified_runtime_path(path) {
                return Err(RuntimeError::UnboundVariable { path: path.clone() });
            }
        }
        ExprKind::EffectOp(path) => {
            if path.segments.is_empty() {
                return Err(RuntimeError::UnboundVariable { path: path.clone() });
            }
        }
        ExprKind::PrimitiveOp(_) | ExprKind::Lit(_) => {}
        ExprKind::Lambda { param, body, .. } => {
            let (param_ty, ret) = validate_lambda_type(&expr.ty)?;
            let local = core_ir::Path::from_name(param.clone());
            let previous = locals.insert(local.clone(), param_ty);
            validate_expr(body, bindings, locals)?;
            require_same_hir_type(&ret, &body.ty, TypeSource::Expected)?;
            restore_local(locals, local, previous);
        }
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => {
            validate_expr(callee, bindings, locals)?;
            validate_expr(arg, bindings, locals)?;
            if let Some(instantiation) = instantiation {
                validate_type_instantiation(instantiation, bindings)?;
            }
            match &callee.ty {
                RuntimeType::Fun { param, ret } => {
                    require_same_hir_type(param, &arg.ty, TypeSource::ApplyEvidence)?;
                    require_same_hir_type(ret, &expr.ty, TypeSource::ApplyEvidence)?;
                }
                RuntimeType::Core(core_ir::Type::Fun { param, ret, .. }) => {
                    require_same_type(param, core_type(&arg.ty), TypeSource::ApplyEvidence)?;
                    require_same_type(
                        ret,
                        &diagnostic_core_type(&expr.ty),
                        TypeSource::ApplyEvidence,
                    )?;
                }
                RuntimeType::Core(core_ir::Type::Var(_) | core_ir::Type::Any) => {
                    if let Some(evidence) = evidence {
                        if let Some(arg_ty) =
                            choose_bounds_type(&evidence.arg, BoundsChoice::ValidationEvidence)
                        {
                            require_same_type(
                                &arg_ty,
                                core_type(&arg.ty),
                                TypeSource::ApplyEvidence,
                            )?;
                        }
                        if let Some(result_ty) =
                            choose_bounds_type(&evidence.result, BoundsChoice::ValidationEvidence)
                        {
                            require_same_type(
                                &result_ty,
                                hir_value_core_type(&expr.ty),
                                TypeSource::ApplyEvidence,
                            )?;
                        }
                    }
                }
                other => {
                    return Err(RuntimeError::NonFunctionCallee {
                        ty: diagnostic_core_type(other),
                    });
                }
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            validate_expr(cond, bindings, locals)?;
            require_same_type(&bool_type(), core_type(&cond.ty), TypeSource::Expected)?;
            validate_expr(then_branch, bindings, locals)?;
            validate_expr(else_branch, bindings, locals)?;
            require_same_hir_type(&expr.ty, &then_branch.ty, TypeSource::JoinEvidence)?;
            require_same_hir_type(&expr.ty, &else_branch.ty, TypeSource::JoinEvidence)?;
        }
        ExprKind::Tuple(items) => {
            for item in items {
                validate_expr(item, bindings, locals)?;
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                validate_expr(&field.value, bindings, locals)?;
            }
            validate_record_spread_expr(spread, bindings, locals)?;
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                validate_expr(value, bindings, locals)?;
            }
        }
        ExprKind::Select { base, .. } => {
            validate_expr(base, bindings, locals)?;
        }
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => {
            validate_expr(scrutinee, bindings, locals)?;
            require_same_type(
                &evidence.result,
                hir_value_core_type(&expr.ty),
                TypeSource::JoinEvidence,
            )?;
            for arm in arms {
                validate_match_arm(
                    arm,
                    hir_value_core_type(&scrutinee.ty),
                    hir_value_core_type(&expr.ty),
                    bindings,
                    locals,
                )?;
            }
        }
        ExprKind::Block { stmts, tail } => {
            let mut block_locals = locals.clone();
            for stmt in stmts {
                if let Stmt::Let { pattern, .. } = stmt {
                    validate_hir_pattern(pattern, pattern_ty(pattern), &mut block_locals)?;
                }
            }
            for stmt in stmts {
                validate_stmt(stmt, bindings, &mut block_locals)?;
            }
            if let Some(tail) = tail {
                validate_expr(tail, bindings, &mut block_locals)?;
                require_same_hir_type(&expr.ty, &tail.ty, TypeSource::Expected)?;
            }
        }
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => {
            validate_expr(body, bindings, locals)?;
            require_same_type(
                &evidence.result,
                hir_value_core_type(&expr.ty),
                TypeSource::JoinEvidence,
            )?;
            validate_handle_effect(handler, arms)?;
            for arm in arms {
                validate_handle_arm(
                    arm,
                    hir_value_core_type(&body.ty),
                    hir_value_core_type(&expr.ty),
                    bindings,
                    locals,
                )?;
            }
        }
        ExprKind::BindHere { expr: inner } => {
            validate_expr(inner, bindings, locals)?;
            match &inner.ty {
                RuntimeType::Thunk { value, .. } => {
                    require_same_hir_type(&expr.ty, value, TypeSource::Expected)?;
                }
                _ => {
                    return Err(RuntimeError::ExpectedThunk {
                        ty: diagnostic_core_type(&inner.ty),
                    });
                }
            }
        }
        ExprKind::Thunk {
            effect,
            value,
            expr: inner,
        } => {
            validate_expr(inner, bindings, locals)?;
            require_same_hir_type(value, &inner.ty, TypeSource::Expected)?;
            require_same_hir_type(
                &expr.ty,
                &RuntimeType::thunk(effect.clone(), value.clone()),
                TypeSource::Expected,
            )?;
        }
        ExprKind::LocalPushId { body, .. } => {
            validate_expr(body, bindings, locals)?;
            require_same_hir_type(&expr.ty, &body.ty, TypeSource::Expected)?;
        }
        ExprKind::PeekId => {
            require_same_hir_type(
                &expr.ty,
                &RuntimeType::core(effect_id_type()),
                TypeSource::Expected,
            )?;
        }
        ExprKind::FindId { .. } => {
            require_same_type(&bool_type(), core_type(&expr.ty), TypeSource::Expected)?;
        }
        ExprKind::AddId { allowed, thunk, .. } => {
            validate_expr(thunk, bindings, locals)?;
            if !matches!(thunk.ty, RuntimeType::Thunk { .. }) {
                return Err(RuntimeError::ExpectedThunk {
                    ty: diagnostic_core_type(&thunk.ty),
                });
            }
            require_same_hir_type(&expr.ty, &thunk.ty, TypeSource::Expected)?;
            validate_effect_type_no_any(allowed, TypeSource::Validation)?;
        }
        ExprKind::Coerce {
            from,
            to,
            expr: inner,
        } => {
            validate_expr(inner, bindings, locals)?;
            require_same_type(from, core_type(&inner.ty), TypeSource::Validation)?;
            require_same_type(to, core_type(&expr.ty), TypeSource::Validation)?;
        }
        ExprKind::Pack { expr: inner, .. } => {
            validate_expr(inner, bindings, locals)?;
        }
    }
    Ok(())
}

pub(super) fn validate_stmt(
    stmt: &Stmt,
    bindings: &HashMap<core_ir::Path, BindingInfo>,
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
) -> RuntimeResult<()> {
    match stmt {
        Stmt::Let { pattern, value } => {
            validate_expr(value, bindings, locals)?;
            validate_hir_pattern(pattern, &value.ty, locals)
        }
        Stmt::Expr(expr) => validate_expr(expr, bindings, locals),
        Stmt::Module { def, body } => {
            validate_expr(body, bindings, locals)?;
            locals.insert(def.clone(), body.ty.clone());
            Ok(())
        }
    }
}

pub(super) fn validate_match_arm(
    arm: &MatchArm,
    scrutinee_ty: &core_ir::Type,
    result_ty: &core_ir::Type,
    bindings: &HashMap<core_ir::Path, BindingInfo>,
    locals: &HashMap<core_ir::Path, RuntimeType>,
) -> RuntimeResult<()> {
    let mut arm_locals = locals.clone();
    validate_pattern(&arm.pattern, scrutinee_ty, &mut arm_locals)?;
    if let Some(guard) = &arm.guard {
        validate_expr(guard, bindings, &mut arm_locals)?;
        require_same_type(&bool_type(), core_type(&guard.ty), TypeSource::Expected)?;
    }
    validate_expr(&arm.body, bindings, &mut arm_locals)?;
    require_same_type(
        result_ty,
        &diagnostic_core_type(&arm.body.ty),
        TypeSource::JoinEvidence,
    )
}

pub(super) fn validate_handle_arm(
    arm: &HandleArm,
    body_ty: &core_ir::Type,
    result_ty: &core_ir::Type,
    bindings: &HashMap<core_ir::Path, BindingInfo>,
    locals: &HashMap<core_ir::Path, RuntimeType>,
) -> RuntimeResult<()> {
    let mut arm_locals = locals.clone();
    let payload_ty = if arm.effect == core_ir::Path::default() {
        body_ty.clone()
    } else {
        core_ir::Type::Any
    };
    validate_pattern(&arm.payload, &payload_ty, &mut arm_locals)?;
    if let Some(resume) = &arm.resume {
        validate_resume_binding(resume, body_ty)?;
        arm_locals.insert(
            core_ir::Path::from_name(resume.name.clone()),
            resume.ty.clone(),
        );
    }
    if let Some(guard) = &arm.guard {
        validate_expr(guard, bindings, &mut arm_locals)?;
        require_same_type(&bool_type(), core_type(&guard.ty), TypeSource::Expected)?;
    }
    validate_expr(&arm.body, bindings, &mut arm_locals)?;
    require_same_type(
        result_ty,
        &diagnostic_core_type(&arm.body.ty),
        TypeSource::JoinEvidence,
    )
}

pub(super) fn validate_handle_effect(
    effect: &HandleEffect,
    _arms: &[HandleArm],
) -> RuntimeResult<()> {
    for consumed in &effect.consumes {
        if consumed.segments.is_empty() {
            return Err(RuntimeError::UnboundVariable {
                path: consumed.clone(),
            });
        }
    }
    Ok(())
}

pub(super) fn validate_resume_binding(
    resume: &ResumeBinding,
    body_ty: &core_ir::Type,
) -> RuntimeResult<()> {
    match &resume.ty {
        RuntimeType::Fun { ret, .. } => {
            require_same_type(body_ty, hir_value_core_type(ret), TypeSource::Expected)
        }
        RuntimeType::Core(core_ir::Type::Fun { ret, .. }) => {
            require_same_type(body_ty, ret, TypeSource::Expected)
        }
        other => Err(RuntimeError::NonFunctionCallee {
            ty: diagnostic_core_type(other),
        }),
    }
}

pub(super) fn validate_lambda_type(ty: &RuntimeType) -> RuntimeResult<(RuntimeType, RuntimeType)> {
    match ty {
        RuntimeType::Fun { param, ret } => Ok((param.as_ref().clone(), ret.as_ref().clone())),
        RuntimeType::Thunk { value, .. } => validate_lambda_type(value),
        RuntimeType::Core(core_ir::Type::Fun { param, ret, .. }) => Ok((
            RuntimeType::core(param.as_ref().clone()),
            RuntimeType::core(ret.as_ref().clone()),
        )),
        other => Err(RuntimeError::NonFunctionCallee {
            ty: diagnostic_core_type(other),
        }),
    }
}

pub(super) fn validate_type_instantiation(
    instantiation: &TypeInstantiation,
    bindings: &HashMap<core_ir::Path, BindingInfo>,
) -> RuntimeResult<()> {
    let Some(info) = bindings.get(&instantiation.target) else {
        if is_qualified_runtime_path(&instantiation.target) {
            for arg in &instantiation.args {
                validate_substitution_type_no_any(&arg.ty, TypeSource::ApplyEvidence)?;
            }
            return Ok(());
        }
        return Err(RuntimeError::UnboundVariable {
            path: instantiation.target.clone(),
        });
    };
    let mut substitutions = BTreeMap::new();
    for arg in &instantiation.args {
        if !info.type_params.contains(&arg.var) {
            if info.type_params.is_empty() {
                validate_substitution_type_no_any(&arg.ty, TypeSource::ApplyEvidence)?;
                continue;
            }
            return Err(RuntimeError::TypeMismatch {
                expected: diagnostic_core_type(&info.ty),
                actual: arg.ty.clone(),
                source: TypeSource::ApplyEvidence,
            });
        }
        validate_substitution_type_no_any(&arg.ty, TypeSource::ApplyEvidence)?;
        substitutions.insert(arg.var.clone(), arg.ty.clone());
    }
    let _ = substitutions;
    Ok(())
}
