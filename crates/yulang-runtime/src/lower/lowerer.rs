use super::*;

impl Lowerer<'_> {
    pub(super) fn lower_binding(
        &mut self,
        binding: core_ir::PrincipalBinding,
    ) -> RuntimeResult<Binding> {
        let body_ty = self.binding_runtime_type(&binding);
        let alias_runtime_ty = self.alias_target_runtime_type(&binding);
        reject_non_runtime_hir_type(&body_ty, TypeSource::BindingScheme)?;
        let body = self.lower_expr(
            binding.body,
            Some(&body_ty),
            &mut HashMap::new(),
            TypeSource::BindingScheme,
        )?;
        require_same_hir_type(&body_ty, &body.ty, TypeSource::BindingScheme)?;
        let type_params = principal_hir_type_params(&body.ty);
        let mut scheme = binding.scheme;
        if alias_runtime_ty.is_some() || has_added_wildcard_thunk(&body_ty, &body.ty) {
            scheme.body = runtime_core_type(&body.ty);
        }
        self.env.insert(binding.name.clone(), body.ty.clone());
        self.binding_infos.insert(
            binding.name.clone(),
            BindingInfo {
                ty: body.ty.clone(),
                type_params: type_params.clone(),
                requirements: scheme.requirements.clone(),
            },
        );
        Ok(Binding {
            name: binding.name,
            type_params,
            scheme,
            body,
        })
    }

    pub(super) fn lower_root_expr(
        &mut self,
        index: usize,
        expr: core_ir::Expr,
    ) -> RuntimeResult<Expr> {
        let ty = self
            .root_expr_type(index, &expr)
            .ok_or(RuntimeError::MissingRootType { index })?;
        let ty = RuntimeType::core(ty);
        self.lower_expr(expr, Some(&ty), &mut HashMap::new(), TypeSource::RootGraph)
    }

    pub(super) fn lower_expr(
        &mut self,
        expr: core_ir::Expr,
        expected: Option<&RuntimeType>,
        locals: &mut HashMap<core_ir::Path, RuntimeType>,
        expected_source: TypeSource,
    ) -> RuntimeResult<Expr> {
        match expr {
            core_ir::Expr::Var(path) => {
                let local_ty = locals.get(&path).cloned();
                let resolved_path = if local_ty.is_none() {
                    self.resolve_alias_path(&path)
                } else {
                    path.clone()
                };
                let stored_ty = local_ty
                    .clone()
                    .or_else(|| self.env.get(&path).cloned())
                    .or_else(|| self.env.get(&resolved_path).cloned());
                let is_bound = local_ty.is_some() || self.env.contains_key(&resolved_path);
                let ty = if local_ty.is_none()
                    && self
                        .binding_infos
                        .get(&path)
                        .is_some_and(|info| !info.type_params.is_empty())
                {
                    choose_polymorphic_binding_type_hint(stored_ty.clone(), expected.cloned())
                } else {
                    choose_local_type_hint(stored_ty.clone(), expected.cloned())
                }
                .ok_or_else(|| RuntimeError::UnboundVariable { path: path.clone() })?;
                if locals.contains_key(&path) && stored_ty.as_ref() != Some(&ty) {
                    locals.insert(path.clone(), ty.clone());
                }
                reject_non_runtime_hir_type(&ty, TypeSource::Local)?;
                let kind = if is_bound {
                    ExprKind::Var(resolved_path)
                } else if self.runtime_symbol_kind(&resolved_path)
                    == Some(core_ir::RuntimeSymbolKind::EffectOperation)
                {
                    ExprKind::EffectOp(resolved_path)
                } else {
                    ExprKind::Var(resolved_path)
                };
                Ok(Expr::typed(kind, ty))
            }
            core_ir::Expr::PrimitiveOp(op) => {
                let ty = expected
                    .cloned()
                    .unwrap_or_else(|| RuntimeType::core(core_ir::Type::Any));
                reject_non_runtime_hir_type(&ty, expected_source)?;
                Ok(Expr::typed(ExprKind::PrimitiveOp(op), ty))
            }
            core_ir::Expr::Lit(lit) => {
                let ty = lit_type(&lit);
                if let Some(expected) = expected {
                    if matches!(expected, RuntimeType::Thunk { .. }) {
                        let expr = Expr::typed(ExprKind::Lit(lit), ty);
                        return prepare_expr_for_expected(expr, expected, expected_source);
                    }
                    let expected_core = core_type(expected);
                    require_same_type(expected_core, &ty, expected_source)?;
                    if needs_runtime_coercion(expected_core, &ty) {
                        let expr = Expr::typed(ExprKind::Lit(lit), ty);
                        return Ok(Expr::typed(
                            ExprKind::Coerce {
                                from: core_type(&expr.ty).clone(),
                                to: expected_core.clone(),
                                expr: Box::new(expr),
                            },
                            expected.clone(),
                        ));
                    }
                }
                Ok(Expr::typed(ExprKind::Lit(lit), ty))
            }
            core_ir::Expr::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body,
            } => {
                let expected = expected
                    .cloned()
                    .map(|ty| self.normalize_expected_hir_type(ty));
                let expected_value = expected.as_ref().map(value_hir_type);
                let (param_ty, ret_expected) = match expected_value {
                    Some(RuntimeType::Fun { param, ret }) => {
                        ((**param).clone(), Some(ret.as_ref()))
                    }
                    Some(RuntimeType::Core(core_ir::Type::Any)) | None => {
                        (RuntimeType::core(core_ir::Type::Any), None)
                    }
                    Some(other) => {
                        return Err(RuntimeError::NonFunctionCallee {
                            ty: diagnostic_core_type(other),
                        });
                    }
                };
                let param_ty = apply_param_allowed_effect(
                    param_ty,
                    param_effect_annotation.as_ref(),
                    param_function_allowed_effects.as_ref(),
                );
                let local = core_ir::Path::from_name(param.clone());
                let previous = locals.insert(local.clone(), param_ty.clone());
                let body_expected = match ret_expected {
                    Some(ret) => Some(ret.clone()),
                    None => None,
                };
                let body =
                    self.lower_expr(*body, body_expected.as_ref(), locals, TypeSource::Expected)?;
                let actual_param_ty = locals.get(&local).cloned().unwrap_or(param_ty);
                restore_local(locals, local, previous);
                let body = self.protect_function_body(body);
                let actual_ty = RuntimeType::fun(actual_param_ty, body.ty.clone());
                let ty = match expected.as_ref() {
                    Some(expected @ RuntimeType::Fun { .. }) => {
                        refine_lambda_hir_type(expected, &actual_ty)
                    }
                    _ => actual_ty,
                };
                Ok(Expr::typed(
                    ExprKind::Lambda {
                        param,
                        param_effect_annotation,
                        param_function_allowed_effects,
                        body: Box::new(body),
                    },
                    ty,
                ))
            }
            core_ir::Expr::Apply {
                callee,
                arg,
                evidence,
            } => {
                let mut callee_expr = Some(*callee);
                let mut arg_expr = Some(*arg);
                let callee_is_effect_operation = callee_expr
                    .as_ref()
                    .is_some_and(|expr| self.core_expr_is_effect_operation(expr, locals));
                let evidence_callee = evidence.as_ref().and_then(|evidence| {
                    if callee_is_effect_operation {
                        self.tir_declared_runtime_hir_type(&evidence.callee)
                    } else {
                        self.tir_evidence_runtime_hir_type(&evidence.callee)
                    }
                });
                let evidence_arg = evidence
                    .as_ref()
                    .and_then(|evidence| self.tir_evidence_runtime_type(&evidence.arg))
                    .map(RuntimeType::core);
                let evidence_arg_lower = evidence
                    .as_ref()
                    .and_then(|evidence| self.tir_argument_runtime_type(&evidence.arg))
                    .map(RuntimeType::core);
                let evidence_result = evidence
                    .as_ref()
                    .and_then(|evidence| self.tir_evidence_runtime_type(&evidence.result))
                    .map(RuntimeType::core);
                let callee_local_hint = match callee_expr.as_ref() {
                    Some(core_ir::Expr::Var(path)) => locals.get(path).cloned(),
                    _ => None,
                };
                let callee_stored_hint =
                    callee_local_hint
                        .clone()
                        .or_else(|| match callee_expr.as_ref() {
                            Some(core_ir::Expr::Var(path)) => self.env.get(path).cloned(),
                            _ => None,
                        });
                let callee_hint =
                    choose_apply_callee_type(evidence_callee, callee_stored_hint.clone());
                let mut callee = None;
                let mut fun_parts = callee_hint
                    .as_ref()
                    .and_then(|ty| function_parts(ty).ok())
                    .or_else(|| {
                        callee_stored_hint
                            .as_ref()
                            .and_then(|ty| function_parts(ty).ok())
                    });
                if fun_parts.is_none()
                    && evidence_arg.is_none()
                    && !matches!(
                        callee_expr.as_ref(),
                        Some(core_ir::Expr::Var(path)) if self.is_external_runtime_path(path, locals)
                    )
                    && !matches!(callee_expr.as_ref(), Some(core_ir::Expr::Apply { .. }))
                {
                    let callee_expected =
                        callee_hint.as_ref().and_then(|callee_ty| match callee_ty {
                            RuntimeType::Core(core_ir::Type::Var(_)) => None,
                            other => Some(other),
                        });
                    let lowered = self.lower_expr(
                        callee_expr.take().expect("callee should be present"),
                        callee_expected,
                        locals,
                        TypeSource::ApplyEvidence,
                    )?;
                    let (lowered, lowered_ty) = force_value_expr(lowered);
                    fun_parts = function_parts(&lowered_ty).ok();
                    callee = Some(lowered);
                }
                let ret_hint = fun_parts.as_ref().map(|parts| parts.ret.clone());
                let result_ty = choose_apply_result_type(
                    evidence_result,
                    ret_hint,
                    callee_local_hint.is_some(),
                )
                .and_then(|ty| choose_expected_hir_type(ty, expected.cloned()))
                .or_else(|| expected.cloned())
                .unwrap_or_else(|| RuntimeType::core(self.fresh_type_var("apply_result")));
                if let Some(expected) = expected {
                    require_apply_result_compatible(expected, &result_ty, expected_source)?;
                }
                let mut arg = None;
                let param_hint = fun_parts.as_ref().map(|parts| parts.param.clone());
                let arg_ty = match choose_apply_arg_type(evidence_arg, param_hint) {
                    Some(arg_ty) => arg_ty,
                    None => {
                        let lowered = self.lower_expr(
                            arg_expr.take().expect("arg should be present"),
                            None,
                            locals,
                            TypeSource::ApplyEvidence,
                        )?;
                        let (lowered, arg_ty) = match lowered.ty {
                            RuntimeType::Thunk { .. } => {
                                let arg_ty = lowered.ty.clone();
                                (lowered, arg_ty)
                            }
                            _ => force_value_expr(lowered),
                        };
                        arg = Some(lowered);
                        arg_ty
                    }
                };
                let callee = match callee {
                    Some(callee) => callee,
                    None => {
                        let callee_expected = match callee_hint.as_ref() {
                            Some(ty @ RuntimeType::Fun { .. }) => Some(ty.clone()),
                            None => callee_stored_hint.clone().or_else(|| {
                                Some(erased_fun_type(arg_ty.clone(), result_ty.clone()))
                            }),
                            Some(RuntimeType::Core(core_ir::Type::Any | core_ir::Type::Var(_))) => {
                                Some(erased_fun_type(arg_ty.clone(), result_ty.clone()))
                            }
                            Some(other) => Some(other.clone()),
                        };
                        self.lower_expr(
                            callee_expr.take().expect("callee should be present"),
                            callee_expected.as_ref(),
                            locals,
                            TypeSource::ApplyEvidence,
                        )?
                    }
                };
                let (mut callee, _) = force_value_expr(callee);
                let arg = match arg {
                    Some(arg) => arg,
                    None => {
                        let expected_arg = if callee_is_effect_operation
                            && matches!(arg_ty, RuntimeType::Thunk { .. })
                        {
                            let value_arg_ty = value_hir_type(&arg_ty);
                            if hir_type_has_type_vars(value_arg_ty) {
                                None
                            } else {
                                Some(value_arg_ty)
                            }
                        } else if matches!(arg_ty, RuntimeType::Thunk { .. }) {
                            Some(&arg_ty)
                        } else if let Some(lower_arg_ty) =
                            evidence_arg_lower.as_ref().filter(|_| {
                                can_push_expected_arg_through(
                                    arg_expr
                                        .as_ref()
                                        .expect("arg should be present before lowering"),
                                )
                            })
                        {
                            Some(lower_arg_ty)
                        } else if hir_type_has_type_vars(&arg_ty)
                            && !can_push_expected_arg_through(
                                arg_expr
                                    .as_ref()
                                    .expect("arg should be present before lowering"),
                            )
                        {
                            None
                        } else {
                            Some(&arg_ty)
                        };
                        self.lower_expr(
                            arg_expr.take().expect("arg should be present"),
                            expected_arg,
                            locals,
                            TypeSource::ApplyEvidence,
                        )?
                    }
                };
                let actual_arg_ty = arg.ty.clone();
                if matches!(
                    callee.ty,
                    RuntimeType::Core(core_ir::Type::Any | core_ir::Type::Var(_))
                ) {
                    callee.ty = erased_fun_type(arg_ty.clone(), result_ty.clone());
                }
                let final_fun_parts = function_parts(&callee.ty)?;
                let instantiation_arg_ty = if hir_type_is_hole(&actual_arg_ty)
                    || hir_type_has_type_vars(&actual_arg_ty) && !hir_type_has_type_vars(&arg_ty)
                {
                    &arg_ty
                } else {
                    &actual_arg_ty
                };
                let instantiation = self.instantiate_callee(
                    &mut callee,
                    callee_hint.as_ref(),
                    instantiation_arg_ty,
                    &result_ty,
                );
                let mut final_fun_parts = function_parts(&callee.ty).unwrap_or(final_fun_parts);
                let arg = if matches!(callee.kind, ExprKind::EffectOp(_)) {
                    prepare_effect_operation_arg(
                        arg,
                        &final_fun_parts.param,
                        TypeSource::ApplyEvidence,
                    )?
                } else {
                    prepare_expr_for_expected(
                        arg,
                        &final_fun_parts.param,
                        TypeSource::ApplyEvidence,
                    )?
                };
                require_apply_arg_compatible(
                    &final_fun_parts.param,
                    &arg.ty,
                    TypeSource::ApplyEvidence,
                )?;
                if let ExprKind::EffectOp(path) = &callee.kind
                    && let Some(effect) =
                        effect_operation_effect(path, core_type(value_hir_type(&arg.ty)))
                    && let RuntimeType::Thunk { value, .. } = &final_fun_parts.ret
                {
                    final_fun_parts.ret = RuntimeType::thunk(effect, value.as_ref().clone());
                    callee.ty =
                        erased_fun_type(final_fun_parts.param.clone(), final_fun_parts.ret.clone());
                }
                let effect_operation = match &callee.kind {
                    ExprKind::EffectOp(path) => {
                        Some((path.clone(), core_type(value_hir_type(&arg.ty)).clone()))
                    }
                    _ => None,
                };
                let apply_ty = match &final_fun_parts.ret {
                    RuntimeType::Core(core_ir::Type::Any | core_ir::Type::Var(_)) => result_ty,
                    _ => final_fun_parts.ret,
                };
                let mut apply = Expr::typed(
                    ExprKind::Apply {
                        callee: Box::new(callee),
                        arg: Box::new(arg),
                        evidence,
                        instantiation,
                    },
                    apply_ty,
                );
                if let Some((path, arg_ty)) = effect_operation
                    && !matches!(apply.ty, RuntimeType::Thunk { .. })
                {
                    if let Some(effect) = effect_operation_effect(&path, &arg_ty) {
                        apply = attach_expr_effect(apply, effect);
                    }
                }
                finalize_effectful_expr(apply, expected, expected_source)
            }
            core_ir::Expr::If {
                cond,
                then_branch,
                else_branch,
                evidence,
            } => {
                let result_ty = self.join_result_type(evidence.as_ref(), expected, "if")?;
                let result_hir_ty = RuntimeType::core(result_ty.clone());
                let cond = self.lower_expr(
                    *cond,
                    Some(&RuntimeType::core(bool_type())),
                    locals,
                    TypeSource::Expected,
                )?;
                let then_branch = self.lower_expr(
                    *then_branch,
                    Some(&result_hir_ty),
                    locals,
                    TypeSource::JoinEvidence,
                )?;
                let else_branch = self.lower_expr(
                    *else_branch,
                    Some(&result_hir_ty),
                    locals,
                    TypeSource::JoinEvidence,
                )?;
                let evidence = evidence.map(|_| JoinEvidence {
                    result: result_ty.clone(),
                });
                let expr = Expr::typed(
                    ExprKind::If {
                        cond: Box::new(cond),
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                        evidence,
                    },
                    result_ty,
                );
                finalize_effectful_expr(expr, expected, expected_source)
            }
            core_ir::Expr::Tuple(items) => {
                let expected_items = match expected.and_then(RuntimeType::as_core) {
                    Some(core_ir::Type::Tuple(items)) => Some(items.as_slice()),
                    Some(_) => None,
                    None => None,
                };
                let items = items
                    .into_iter()
                    .enumerate()
                    .map(|(index, item)| {
                        let expected_item = expected_items
                            .and_then(|items| items.get(index))
                            .cloned()
                            .map(RuntimeType::core);
                        self.lower_expr(item, expected_item.as_ref(), locals, TypeSource::Expected)
                            .map(|expr| force_core_value_expr(expr).0)
                    })
                    .collect::<RuntimeResult<Vec<_>>>()?;
                let ty = core_ir::Type::Tuple(
                    items
                        .iter()
                        .map(|item| core_type(&item.ty).clone())
                        .collect(),
                );
                let expr = Expr::typed(ExprKind::Tuple(items), ty);
                finalize_effectful_expr(expr, expected, expected_source)
            }
            core_ir::Expr::Record { fields, spread } => {
                let fields = fields
                    .into_iter()
                    .map(|field| {
                        let expected = record_field_expected(
                            expected.and_then(RuntimeType::as_core),
                            &field.name,
                        )
                        .map(RuntimeType::core);
                        Ok(RecordExprField {
                            name: field.name,
                            value: force_value_expr(self.lower_expr(
                                field.value,
                                expected.as_ref(),
                                locals,
                                TypeSource::Expected,
                            )?)
                            .0,
                        })
                    })
                    .collect::<RuntimeResult<Vec<_>>>()?;
                let spread = spread
                    .map(|spread| self.lower_record_spread_expr(spread, locals))
                    .transpose()?;
                let ty = core_ir::Type::Record(core_ir::RecordType {
                    fields: fields
                        .iter()
                        .map(|field| core_ir::RecordField {
                            name: field.name.clone(),
                            value: diagnostic_core_type(&field.value.ty),
                            optional: false,
                        })
                        .collect(),
                    spread: None,
                });
                let expr = Expr::typed(ExprKind::Record { fields, spread }, ty);
                finalize_effectful_expr(expr, expected, expected_source)
            }
            core_ir::Expr::Variant { tag, value } => {
                let expected_payload =
                    variant_payload_expected(expected.and_then(RuntimeType::as_core), &tag)
                        .map(RuntimeType::core);
                let value = value
                    .map(|value| {
                        self.lower_expr(
                            *value,
                            expected_payload.as_ref(),
                            locals,
                            TypeSource::Expected,
                        )
                        .map(|expr| force_core_value_expr(expr).0)
                        .map(Box::new)
                    })
                    .transpose()?;
                let ty = expected
                    .and_then(RuntimeType::as_core)
                    .cloned()
                    .unwrap_or_else(|| {
                        core_ir::Type::Variant(core_ir::VariantType {
                            cases: vec![core_ir::VariantCase {
                                name: tag.clone(),
                                payloads: value
                                    .iter()
                                    .map(|value| core_type(&value.ty).clone())
                                    .collect(),
                            }],
                            tail: None,
                        })
                    });
                let expr = Expr::typed(ExprKind::Variant { tag, value }, ty);
                finalize_effectful_expr(expr, expected, expected_source)
            }
            core_ir::Expr::Select { base, field } => {
                let base = self.lower_expr(*base, None, locals, TypeSource::Expected)?;
                let (base, base_ty) = force_core_value_expr(base);
                let ty = match select_field_type(&base_ty, &field) {
                    Ok(ty) => ty,
                    Err(error) => match expected {
                        Some(expected) => diagnostic_core_type(expected),
                        None => return Err(error),
                    },
                };
                if let Some(expected) = expected {
                    require_same_type(&diagnostic_core_type(expected), &ty, expected_source)?;
                }
                let expr = Expr::typed(
                    ExprKind::Select {
                        base: Box::new(base),
                        field,
                    },
                    ty,
                );
                finalize_effectful_expr(expr, expected, expected_source)
            }
            core_ir::Expr::Match {
                scrutinee,
                arms,
                evidence,
            } => {
                let result_ty = self.join_result_type(evidence.as_ref(), expected, "match")?;
                let result_hir_ty = RuntimeType::core(result_ty.clone());
                let scrutinee = self.lower_expr(*scrutinee, None, locals, TypeSource::Expected)?;
                let (scrutinee, scrutinee_ty) = force_core_value_expr(scrutinee);
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let mut arm_locals = locals.clone();
                        let pattern =
                            lower_pattern(self, arm.pattern, &scrutinee_ty, &mut arm_locals)?;
                        let guard = arm
                            .guard
                            .map(|guard| {
                                self.lower_expr(
                                    guard,
                                    Some(&RuntimeType::core(bool_type())),
                                    &mut arm_locals,
                                    TypeSource::Expected,
                                )
                            })
                            .transpose()?;
                        let body = self.lower_expr(
                            arm.body,
                            Some(&result_hir_ty),
                            &mut arm_locals,
                            TypeSource::JoinEvidence,
                        )?;
                        Ok(MatchArm {
                            pattern,
                            guard,
                            body,
                        })
                    })
                    .collect::<RuntimeResult<Vec<_>>>()?;
                let expr = Expr::typed(
                    ExprKind::Match {
                        scrutinee: Box::new(scrutinee),
                        arms,
                        evidence: JoinEvidence {
                            result: result_ty.clone(),
                        },
                    },
                    result_ty,
                );
                finalize_effectful_expr(expr, expected, expected_source)
            }
            core_ir::Expr::Block { mut stmts, tail } => {
                let mut block_locals = locals.clone();
                for stmt in &stmts {
                    self.prebind_block_local(stmt, &mut block_locals);
                }
                let tail = tail.or_else(|| match stmts.last() {
                    Some(core_ir::Stmt::Expr(_)) => match stmts.pop() {
                        Some(core_ir::Stmt::Expr(expr)) => Some(Box::new(expr)),
                        _ => None,
                    },
                    _ => None,
                });
                let stmt_expected = expected.and_then(|ty| match ty {
                    RuntimeType::Thunk { .. } => Some(RuntimeType::core(unit_type())),
                    _ => None,
                });
                let stmts = stmts
                    .into_iter()
                    .map(|stmt| {
                        self.lower_stmt_with_expected(
                            stmt,
                            &mut block_locals,
                            stmt_expected.as_ref(),
                        )
                    })
                    .collect::<RuntimeResult<Vec<_>>>()?;
                let tail_expected = expected.map(|ty| value_hir_type(ty).clone());
                let tail = tail
                    .map(|tail| {
                        self.lower_expr(
                            *tail,
                            tail_expected.as_ref(),
                            &mut block_locals,
                            expected_source,
                        )
                        .map(Box::new)
                    })
                    .transpose()?;
                let ty = tail
                    .as_ref()
                    .map(|tail| tail.ty.clone())
                    .unwrap_or_else(|| RuntimeType::core(unit_type()));
                propagate_refined_locals(locals, &block_locals);
                let expr = Expr {
                    ty,
                    kind: ExprKind::Block { stmts, tail },
                };
                finalize_effectful_expr(expr, expected, expected_source)
            }
            core_ir::Expr::Handle {
                body,
                arms,
                evidence,
            } => {
                let result_hint = self.join_result_type(evidence.as_ref(), expected, "handle")?;
                let result_ty = if expected.is_none() && core_type_is_hole(&result_hint) {
                    self.visible_handle_result_type(&arms)
                        .unwrap_or(result_hint)
                } else {
                    result_hint
                };
                let body = self.lower_expr(*body, None, locals, TypeSource::Expected)?;
                let handled = handler_consumes_from_core_arms(&arms, &result_ty)
                    .unwrap_or_else(|| handler_consumes_from_body_type(&body.ty));
                let body_effect_before =
                    expr_forced_effect(&body).or_else(|| thunk_effect(&body.ty));
                let resume_effect = body_effect_before
                    .as_ref()
                    .map(|effect| handler_body_residual(effect, &handled));
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        self.lower_handle_arm(
                            arm,
                            value_core_type(&body.ty),
                            resume_effect.as_ref(),
                            &result_ty,
                            locals,
                        )
                    })
                    .collect::<RuntimeResult<Vec<_>>>()?;
                let handler = handle_effect_for_arms(&arms, body_effect_before, handled);
                let expr = Expr::typed(
                    ExprKind::Handle {
                        body: Box::new(body),
                        arms,
                        evidence: JoinEvidence {
                            result: result_ty.clone(),
                        },
                        handler,
                    },
                    result_ty,
                );
                finalize_handler_expr(expr, expected, expected_source)
            }
            core_ir::Expr::Coerce { expr } => {
                let expr = self.lower_expr(*expr, None, locals, TypeSource::Expected)?;
                let (expr, from) = force_core_value_expr(expr);
                let ty = expected
                    .cloned()
                    .unwrap_or_else(|| RuntimeType::core(from.clone()));
                let expr = Expr::typed(
                    ExprKind::Coerce {
                        from,
                        to: core_type(&ty).clone(),
                        expr: Box::new(expr),
                    },
                    ty,
                );
                finalize_effectful_expr(expr, expected, expected_source)
            }
            core_ir::Expr::Pack { var, expr } => {
                let expr = self.lower_expr(*expr, expected, locals, expected_source)?;
                let (expr, value_ty) = force_value_expr(expr);
                let ty = expected.cloned().unwrap_or(value_ty);
                let expr = Expr::typed(
                    ExprKind::Pack {
                        var,
                        expr: Box::new(expr),
                    },
                    ty,
                );
                finalize_effectful_expr(expr, expected, expected_source)
            }
        }
    }

    fn prebind_block_local(
        &self,
        stmt: &core_ir::Stmt,
        locals: &mut HashMap<core_ir::Path, RuntimeType>,
    ) {
        let core_ir::Stmt::Let { pattern, value } = stmt else {
            return;
        };
        let Some(name) = single_bound_name(pattern) else {
            return;
        };
        let Some(ty) = self
            .visible_expr_type(value)
            .or_else(|| self.lambda_hint_type(value))
        else {
            return;
        };
        locals.insert(
            core_ir::Path::from_name(name),
            project_runtime_hir_type_with_vars(&ty, &self.principal_vars),
        );
    }

    fn lambda_hint_type(&self, expr: &core_ir::Expr) -> Option<core_ir::Type> {
        let core_ir::Expr::Lambda { body, .. } = expr else {
            return None;
        };
        let ret = self
            .lambda_hint_type(body)
            .or_else(|| self.visible_expr_type(body))?;
        Some(core_ir::Type::Fun {
            param: Box::new(core_ir::Type::Any),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(core_ir::Type::Never),
            ret: Box::new(ret),
        })
    }

    pub(super) fn lower_stmt_with_expected(
        &mut self,
        stmt: core_ir::Stmt,
        locals: &mut HashMap<core_ir::Path, RuntimeType>,
        expected: Option<&RuntimeType>,
    ) -> RuntimeResult<Stmt> {
        match stmt {
            core_ir::Stmt::Let { pattern, value } => {
                let value = self.lower_expr(value, None, locals, TypeSource::Expected)?;
                let (value, value_ty) = force_value_expr(value);
                let pattern = lower_hir_pattern(self, pattern, &value_ty, locals)?;
                Ok(Stmt::Let { pattern, value })
            }
            core_ir::Stmt::Expr(expr) => {
                let expr = self.lower_expr(expr, expected, locals, TypeSource::Expected)?;
                Ok(Stmt::Expr(force_value_expr(expr).0))
            }
            core_ir::Stmt::Module { def, body } => {
                let expected = self.env.get(&def).cloned();
                let body =
                    self.lower_expr(*body, expected.as_ref(), locals, TypeSource::Expected)?;
                locals.insert(def.clone(), body.ty.clone());
                Ok(Stmt::Module { def, body })
            }
        }
    }

    pub(super) fn lower_handle_arm(
        &mut self,
        arm: core_ir::HandleArm,
        body_ty: &core_ir::Type,
        body_effect: Option<&core_ir::Type>,
        result_ty: &core_ir::Type,
        locals: &HashMap<core_ir::Path, RuntimeType>,
    ) -> RuntimeResult<HandleArm> {
        let mut arm_locals = locals.clone();
        let payload_ty = if arm.effect == core_ir::Path::default() {
            body_ty.clone()
        } else {
            infer_handle_payload_type(&arm.payload, arm.guard.as_ref(), &arm.body, result_ty)
                .unwrap_or(core_ir::Type::Any)
        };
        let payload = lower_pattern(self, arm.payload, &payload_ty, &mut arm_locals)?;
        let resume_ty = arm.resume.as_ref().map(|resume| {
            let param_ty = infer_resume_param_type(resume, arm.guard.as_ref(), &arm.body)
                .unwrap_or(core_ir::Type::Any);
            let ret = body_effect
                .filter(|effect| should_thunk_effect(effect))
                .cloned()
                .map(|effect| RuntimeType::thunk(effect, RuntimeType::core(body_ty.clone())))
                .unwrap_or_else(|| RuntimeType::core(body_ty.clone()));
            erased_fun_type(RuntimeType::core(param_ty), ret)
        });
        if let Some(resume) = &arm.resume {
            arm_locals.insert(
                core_ir::Path::from_name(resume.clone()),
                resume_ty
                    .clone()
                    .unwrap_or(RuntimeType::core(core_ir::Type::Any)),
            );
        }
        let guard = arm
            .guard
            .map(|guard| {
                self.lower_expr(
                    guard,
                    Some(&RuntimeType::core(bool_type())),
                    &mut arm_locals,
                    TypeSource::Expected,
                )
            })
            .transpose()?;
        let body = self.lower_expr(
            arm.body,
            Some(&RuntimeType::core(result_ty.clone())),
            &mut arm_locals,
            TypeSource::JoinEvidence,
        )?;
        Ok(HandleArm {
            effect: arm.effect,
            payload,
            resume: arm.resume.map(|name| ResumeBinding {
                name,
                ty: resume_ty.unwrap_or(RuntimeType::core(core_ir::Type::Any)),
            }),
            guard,
            body,
        })
    }

    pub(super) fn lower_record_spread_expr(
        &mut self,
        spread: core_ir::RecordSpreadExpr,
        locals: &mut HashMap<core_ir::Path, RuntimeType>,
    ) -> RuntimeResult<RecordSpreadExpr> {
        match spread {
            core_ir::RecordSpreadExpr::Head(expr) => {
                let expr = self.lower_expr(*expr, None, locals, TypeSource::Expected)?;
                Ok(RecordSpreadExpr::Head(Box::new(
                    force_core_value_expr(expr).0,
                )))
            }
            core_ir::RecordSpreadExpr::Tail(expr) => {
                let expr = self.lower_expr(*expr, None, locals, TypeSource::Expected)?;
                Ok(RecordSpreadExpr::Tail(Box::new(
                    force_core_value_expr(expr).0,
                )))
            }
        }
    }

    pub(super) fn binding_graph_type(&self, path: &core_ir::Path) -> Option<core_ir::Type> {
        self.graph
            .bindings
            .iter()
            .find(|node| node.binding == *path)
            .and_then(|node| self.tir_evidence_runtime_type(&node.body_bounds))
    }

    pub(super) fn root_graph_type(&self, index: usize) -> Option<core_ir::Type> {
        self.graph
            .root_exprs
            .iter()
            .find(|node| node.owner == core_ir::GraphOwner::RootExpr(index))
            .and_then(|node| project_runtime_bounds(&node.bounds))
    }

    pub(super) fn root_expr_type(
        &self,
        index: usize,
        expr: &core_ir::Expr,
    ) -> Option<core_ir::Type> {
        match (self.root_graph_type(index), self.visible_expr_type(expr)) {
            (Some(graph), Some(visible)) if should_use_visible_root_type(&graph, &visible) => {
                Some(visible)
            }
            (Some(graph), _) => Some(graph),
            (None, Some(visible)) if can_use_visible_root_type_without_graph(expr, &visible) => {
                Some(visible)
            }
            (None, _) => None,
        }
    }

    pub(super) fn binding_runtime_type(&self, binding: &core_ir::PrincipalBinding) -> RuntimeType {
        if let Some(alias_ty) = self.alias_target_runtime_type(binding) {
            return alias_ty;
        }
        let scheme_ty = project_runtime_type_with_vars(&binding.scheme.body, &self.principal_vars);
        match self.binding_graph_type(&binding.name) {
            Some(graph_ty) if should_use_graph_binding_type(&scheme_ty, &graph_ty) => {
                RuntimeType::core(graph_ty)
            }
            _ => project_runtime_hir_type_with_vars(&binding.scheme.body, &self.principal_vars),
        }
    }

    fn alias_target_runtime_type(
        &self,
        binding: &core_ir::PrincipalBinding,
    ) -> Option<RuntimeType> {
        let core_ir::Expr::Var(target) = &binding.body else {
            return None;
        };
        let target_ty = self.env.get(target)?;
        let scheme_ty =
            project_runtime_hir_type_with_vars(&binding.scheme.body, &self.principal_vars);
        prefer_alias_target_runtime_type(&scheme_ty, target_ty).then(|| target_ty.clone())
    }

    pub(super) fn tir_evidence_runtime_type(
        &self,
        bounds: &core_ir::TypeBounds,
    ) -> Option<core_ir::Type> {
        choose_bounds_type(bounds, BoundsChoice::TirEvidence)
            .map(|ty| project_runtime_type_with_vars(&ty, &self.principal_vars))
    }

    pub(super) fn tir_argument_runtime_type(
        &self,
        bounds: &core_ir::TypeBounds,
    ) -> Option<core_ir::Type> {
        choose_bounds_type(bounds, BoundsChoice::MonomorphicExpected)
            .map(|ty| project_runtime_type_with_vars(&ty, &self.principal_vars))
    }

    pub(super) fn tir_evidence_runtime_hir_type(
        &self,
        bounds: &core_ir::TypeBounds,
    ) -> Option<RuntimeType> {
        choose_bounds_type(bounds, BoundsChoice::TirEvidence)
            .map(|ty| project_runtime_hir_type_with_vars(&ty, &self.principal_vars))
    }

    pub(super) fn tir_declared_runtime_hir_type(
        &self,
        bounds: &core_ir::TypeBounds,
    ) -> Option<RuntimeType> {
        choose_bounds_type(bounds, BoundsChoice::MonomorphicExpected)
            .map(|ty| project_runtime_hir_type_with_vars(&ty, &self.principal_vars))
    }

    pub(super) fn core_expr_is_effect_operation(
        &self,
        expr: &core_ir::Expr,
        locals: &HashMap<core_ir::Path, RuntimeType>,
    ) -> bool {
        let core_ir::Expr::Var(path) = expr else {
            return false;
        };
        if locals.contains_key(path) {
            return false;
        }
        let resolved_path = self.resolve_alias_path(path);
        self.runtime_symbol_kind(&resolved_path)
            == Some(core_ir::RuntimeSymbolKind::EffectOperation)
    }

    pub(super) fn visible_principal_bounds_type(
        &self,
        bounds: &core_ir::TypeBounds,
    ) -> Option<core_ir::Type> {
        choose_bounds_type(bounds, BoundsChoice::VisiblePrincipal)
            .map(|ty| project_runtime_type_with_vars(&ty, &self.principal_vars))
    }

    pub(super) fn visible_handle_result_type(
        &self,
        arms: &[core_ir::HandleArm],
    ) -> Option<core_ir::Type> {
        arms.iter()
            .filter_map(|arm| self.visible_expr_type(&arm.body))
            .reduce(|left, right| choose_core_type(left, right, TypeChoice::VisiblePrincipal))
            .filter(|ty| !core_type_is_hole(ty))
    }

    pub(super) fn visible_expr_type(&self, expr: &core_ir::Expr) -> Option<core_ir::Type> {
        match expr {
            core_ir::Expr::Var(path) => self.env.get(path).map(diagnostic_core_type),
            core_ir::Expr::PrimitiveOp(_) => None,
            core_ir::Expr::Lit(lit) => Some(lit_type(lit)),
            core_ir::Expr::Apply {
                callee,
                arg,
                evidence,
            } => evidence
                .as_ref()
                .and_then(|evidence| self.visible_principal_bounds_type(&evidence.result))
                .or_else(|| {
                    let callee_ty = self.visible_expr_type(callee);
                    let arg_ty = self.visible_expr_type(arg);
                    callee_ty
                        .as_ref()
                        .and_then(|callee_ty| visible_apply_result_type(callee_ty, arg_ty.as_ref()))
                        .or(callee_ty)
                        .or(arg_ty)
                }),
            core_ir::Expr::Lambda { .. } => None,
            core_ir::Expr::If {
                then_branch,
                else_branch,
                evidence,
                ..
            } => evidence
                .as_ref()
                .and_then(|evidence| self.visible_principal_bounds_type(&evidence.result))
                .or_else(|| {
                    merge_visible_type_options(
                        self.visible_expr_type(then_branch),
                        self.visible_expr_type(else_branch),
                    )
                }),
            core_ir::Expr::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.visible_expr_type(item))
                    .collect::<Option<Vec<_>>>()?;
                Some(core_ir::Type::Tuple(items))
            }
            core_ir::Expr::Record { .. }
            | core_ir::Expr::Variant { .. }
            | core_ir::Expr::Select { .. } => None,
            core_ir::Expr::Match { arms, evidence, .. } => evidence
                .as_ref()
                .and_then(|evidence| self.visible_principal_bounds_type(&evidence.result))
                .or_else(|| {
                    arms.iter()
                        .filter_map(|arm| self.visible_expr_type(&arm.body))
                        .reduce(|left, right| {
                            choose_core_type(left, right, TypeChoice::VisiblePrincipal)
                        })
                }),
            core_ir::Expr::Block { tail, .. } => tail
                .as_deref()
                .and_then(|tail| self.visible_expr_type(tail)),
            core_ir::Expr::Handle { arms, evidence, .. } => evidence
                .as_ref()
                .and_then(|evidence| self.visible_principal_bounds_type(&evidence.result))
                .or_else(|| self.visible_handle_result_type(arms)),
            core_ir::Expr::Coerce { expr } | core_ir::Expr::Pack { expr, .. } => {
                self.visible_expr_type(expr)
            }
        }
    }

    pub(super) fn runtime_symbol_kind(
        &self,
        path: &core_ir::Path,
    ) -> Option<core_ir::RuntimeSymbolKind> {
        self.runtime_symbols.get(path).copied()
    }

    pub(super) fn is_external_runtime_path(
        &self,
        path: &core_ir::Path,
        locals: &HashMap<core_ir::Path, RuntimeType>,
    ) -> bool {
        !locals.contains_key(path)
            && !self.env.contains_key(path)
            && (self.runtime_symbols.contains_key(path) || is_qualified_runtime_path(path))
    }

    pub(super) fn resolve_alias_path(&self, path: &core_ir::Path) -> core_ir::Path {
        let mut current = path.clone();
        for _ in 0..self.aliases.len() {
            let Some(next) = self.aliases.get(&current) else {
                break;
            };
            if next == &current {
                break;
            }
            current = next.clone();
        }
        current
    }

    pub(super) fn fresh_type_var(&mut self, prefix: &str) -> core_ir::Type {
        let index = self.next_synthetic_type_var;
        self.next_synthetic_type_var += 1;
        core_ir::Type::Var(core_ir::TypeVar(format!("runtime_{prefix}_{index}")))
    }

    pub(super) fn fresh_effect_id_var(&mut self) -> EffectIdVar {
        let id = EffectIdVar(self.next_effect_id_var);
        self.next_effect_id_var += 1;
        id
    }

    pub(super) fn protect_function_body(&mut self, body: Expr) -> Expr {
        let body = add_id_to_created_thunks(body);
        if !contains_peek_add_id(&body) {
            return body;
        }
        Expr::typed(
            ExprKind::LocalPushId {
                id: self.fresh_effect_id_var(),
                body: Box::new(body.clone()),
            },
            body.ty,
        )
    }

    pub(super) fn normalize_expected_hir_type(&self, ty: RuntimeType) -> RuntimeType {
        match ty {
            RuntimeType::Core(core @ core_ir::Type::Fun { .. }) => {
                project_runtime_hir_type_with_vars(&core, &self.principal_vars)
            }
            RuntimeType::Fun { param, ret } => RuntimeType::fun(
                self.normalize_expected_hir_type(*param),
                self.normalize_expected_hir_type(*ret),
            ),
            RuntimeType::Thunk { effect, value } => {
                RuntimeType::thunk(effect, self.normalize_expected_hir_type(*value))
            }
            other => other,
        }
    }

    pub(super) fn join_result_type(
        &self,
        evidence: Option<&core_ir::JoinEvidence>,
        expected: Option<&RuntimeType>,
        node: &'static str,
    ) -> RuntimeResult<core_ir::Type> {
        let evidence_ty = evidence
            .and_then(|evidence| self.tir_evidence_runtime_type(&evidence.result))
            .filter(|ty| !core_type_is_hole(ty));
        evidence_ty
            .or_else(|| expected.map(value_core_type).cloned())
            .ok_or(RuntimeError::MissingJoinEvidence { node })
    }

    pub(super) fn instantiate_callee(
        &self,
        callee: &mut Expr,
        callee_hint: Option<&RuntimeType>,
        arg_ty: &RuntimeType,
        result_ty: &RuntimeType,
    ) -> Option<TypeInstantiation> {
        let (target, template_ty, mut substitutions) = match &callee.kind {
            ExprKind::Var(target) | ExprKind::EffectOp(target) => {
                (target.clone(), callee.ty.clone(), BTreeMap::new())
            }
            ExprKind::Apply {
                instantiation: Some(instantiation),
                ..
            } => {
                let substitutions = instantiation
                    .args
                    .iter()
                    .map(|arg| (arg.var.clone(), arg.ty.clone()))
                    .collect::<BTreeMap<_, _>>();
                (
                    instantiation.target.clone(),
                    callee.ty.clone(),
                    substitutions,
                )
            }
            _ => return None,
        };
        let info = self.binding_infos.get(&target)?;
        if info.type_params.is_empty() {
            return None;
        }
        let params = info.type_params.iter().cloned().collect::<BTreeSet<_>>();
        let actual_callee_ty = erased_fun_type(arg_ty.clone(), result_ty.clone());
        infer_hir_type_substitutions(&template_ty, &actual_callee_ty, &params, &mut substitutions);
        if let Some(callee_hint) = callee_hint {
            infer_hir_type_substitutions(&template_ty, callee_hint, &params, &mut substitutions);
        }
        infer_role_requirement_substitutions(&info.requirements, &params, &mut substitutions);
        let substituted_ty = substitute_hir_type(&template_ty, &substitutions);
        let args = info
            .type_params
            .iter()
            .filter_map(|var| {
                let ty = substitutions.get(var)?;
                if matches!(ty, core_ir::Type::Var(actual) if actual == var) {
                    return None;
                }
                Some(TypeSubstitution {
                    var: var.clone(),
                    ty: ty.clone(),
                })
            })
            .collect::<Vec<_>>();
        if args.is_empty() {
            return None;
        }
        callee.ty = substituted_ty;
        Some(TypeInstantiation { target, args })
    }
}

fn has_added_wildcard_thunk(expected: &RuntimeType, actual: &RuntimeType) -> bool {
    match (expected, actual) {
        (
            RuntimeType::Fun {
                param: expected_param,
                ret: expected_ret,
            },
            RuntimeType::Fun {
                param: actual_param,
                ret: actual_ret,
            },
        ) => {
            has_added_wildcard_thunk(expected_param, actual_param)
                || has_added_wildcard_thunk(expected_ret, actual_ret)
        }
        (
            expected,
            RuntimeType::Thunk {
                effect,
                value: actual_value,
            },
        ) if !matches!(expected, RuntimeType::Thunk { .. })
            && matches!(effect, core_ir::Type::Any)
            && (hir_type_compatible(expected, actual_value)
                || hir_type_compatible(actual_value, expected)) =>
        {
            true
        }
        (
            RuntimeType::Thunk {
                value: expected_value,
                ..
            },
            RuntimeType::Thunk {
                value: actual_value,
                ..
            },
        ) => has_added_wildcard_thunk(expected_value, actual_value),
        _ => false,
    }
}

fn handler_consumes_from_core_arms(
    arms: &[core_ir::HandleArm],
    result_ty: &core_ir::Type,
) -> Option<core_ir::Type> {
    let items = arms
        .iter()
        .filter_map(|arm| consumed_effect_from_core_arm(arm, result_ty))
        .collect::<Vec<_>>();
    (!items.is_empty()).then(|| effect_row_from_items(items))
}

fn consumed_effect_from_core_arm(
    arm: &core_ir::HandleArm,
    result_ty: &core_ir::Type,
) -> Option<core_ir::Type> {
    if arm.effect.segments.is_empty() {
        return None;
    }
    let effect_path = core_ir::Path {
        segments: arm
            .effect
            .segments
            .iter()
            .take(arm.effect.segments.len().saturating_sub(1))
            .cloned()
            .collect(),
    };
    if effect_path.segments.is_empty() {
        return None;
    }
    let payload_ty =
        infer_handle_payload_type(&arm.payload, arm.guard.as_ref(), &arm.body, result_ty);
    let args = payload_ty
        .filter(|ty| !matches!(ty, core_ir::Type::Any | core_ir::Type::Var(_)))
        .map(|ty| vec![core_ir::TypeArg::Type(ty)])
        .unwrap_or_default();
    Some(core_ir::Type::Named {
        path: effect_path,
        args,
    })
}

fn prepare_effect_operation_arg(
    arg: Expr,
    expected: &RuntimeType,
    source: TypeSource,
) -> RuntimeResult<Expr> {
    match (expected, &arg.ty) {
        (
            RuntimeType::Core(core_ir::Type::Any | core_ir::Type::Var(_)),
            RuntimeType::Thunk { .. },
        ) => Ok(force_value_expr(arg).0),
        _ => prepare_expr_for_expected(arg, expected, source),
    }
}

fn can_push_expected_arg_through(expr: &core_ir::Expr) -> bool {
    matches!(
        expr,
        core_ir::Expr::Lambda { .. }
            | core_ir::Expr::Tuple(_)
            | core_ir::Expr::Record { .. }
            | core_ir::Expr::Variant { .. }
            | core_ir::Expr::Block { .. }
    )
}
