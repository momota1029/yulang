use super::*;

impl Lowerer<'_> {
    pub(super) fn lower_binding(
        &mut self,
        binding: typed_ir::PrincipalBinding,
    ) -> RuntimeResult<Binding> {
        let body_is_constructor_variant = is_constructor_variant_expr(&binding.body);
        let old_binding = self.current_binding.replace(binding.name.clone());
        let body_ty = self.binding_runtime_type(&binding);
        let alias_runtime_ty = self.alias_target_runtime_type(&binding);
        reject_non_runtime_hir_type(&body_ty, TypeSource::BindingScheme)?;
        let body_result = self.lower_expr(
            binding.body,
            Some(&body_ty),
            &mut HashMap::new(),
            TypeSource::BindingScheme,
        );
        self.current_binding = old_binding;
        let body = body_result?;
        require_same_hir_type(&body_ty, &body.ty, TypeSource::BindingScheme)?;
        let core_type_params = if body_is_constructor_variant {
            principal_core_constructor_type_params(&binding.scheme.body)
        } else {
            principal_core_type_params(&binding.scheme.body)
        };
        let core_type_params_empty = core_type_params.is_empty();
        let stored_ty = if core_type_params_empty {
            body.ty.clone()
        } else {
            body_ty.clone()
        };
        let runtime_type_params = principal_runtime_type_params(
            &binding.scheme.body,
            &stored_ty,
            body_is_constructor_variant,
        );
        let type_params = if core_type_params_empty {
            principal_hir_type_params(&stored_ty)
        } else {
            core_type_params
        };
        let mut scheme = binding.scheme;
        if alias_runtime_ty.is_some() || has_added_wildcard_thunk(&body_ty, &body.ty) {
            scheme.body = runtime_core_type(&body.ty);
        }
        self.env.insert(binding.name.clone(), stored_ty.clone());
        self.binding_infos.insert(
            binding.name.clone(),
            BindingInfo {
                ty: stored_ty,
                type_params: runtime_type_params,
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
        expr: typed_ir::Expr,
    ) -> RuntimeResult<Expr> {
        let ty = self
            .root_expr_type(index, &expr)
            .ok_or(RuntimeError::MissingRootType { index })?;
        let ty = RuntimeType::core(ty);
        self.lower_expr(expr, Some(&ty), &mut HashMap::new(), TypeSource::RootGraph)
    }

    pub(super) fn lower_expr(
        &mut self,
        expr: typed_ir::Expr,
        expected: Option<&RuntimeType>,
        locals: &mut HashMap<typed_ir::Path, RuntimeType>,
        expected_source: TypeSource,
    ) -> RuntimeResult<Expr> {
        match expr {
            typed_ir::Expr::Var(path) => {
                let local_ty = locals.get(&path).cloned();
                let resolved_path = if local_ty.is_none() {
                    self.resolve_alias_path(&path)
                } else {
                    path.clone()
                };
                let runtime_symbol_kind = self.runtime_symbol_kind(&resolved_path);
                let stored_ty = local_ty
                    .clone()
                    .or_else(|| self.env.get(&path).cloned())
                    .or_else(|| self.env.get(&resolved_path).cloned())
                    .or_else(|| match runtime_symbol_kind {
                        Some(typed_ir::RuntimeSymbolKind::EffectOperation) => {
                            // The operation's exported signature template (from
                            // `effect_op_signatures`) carries a proper
                            // `Type::Var(..)` payload, but it does NOT carry
                            // the effect row (the effect is contributed by the
                            // call site, not the op declaration). `expected` —
                            // when present — usually has the effect baked in
                            // but may leave the payload as `Unknown`. Merge
                            // them so we keep effect info from `expected` and
                            // payload vars from the signature; whichever is
                            // present.
                            //
                            // Note: the type vars in the signature template are
                            // the *operation's* hygienic vars, which are not
                            // generally the same identifiers as the surrounding
                            // binding's principal vars. Mono substitutions at
                            // finalize time therefore won't always resolve them
                            // — that's a known limitation tracked separately.
                            let sig = self
                                .effect_op_signatures
                                .get(&resolved_path)
                                .or_else(|| self.effect_op_signatures.get(&path));
                            let sig_ty = sig
                                .map(|scheme| RuntimeType::core(scheme.body.clone()));
                            match (expected.cloned(), sig_ty) {
                                (Some(exp), Some(sig)) => {
                                    Some(merge_effect_op_runtime_type(&exp, &sig))
                                }
                                (Some(exp), None) => Some(exp),
                                (None, Some(sig)) => Some(sig),
                                (None, None) => Some(RuntimeType::unknown()),
                            }
                        }
                        Some(typed_ir::RuntimeSymbolKind::RoleMethod) => {
                            expected.cloned().or_else(|| Some(RuntimeType::unknown()))
                        }
                        Some(typed_ir::RuntimeSymbolKind::Value) | None => None,
                    });
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
                .ok_or_else(|| {
                    if std::env::var_os("YULANG_DEBUG_RUNTIME_TYPE").is_some() {
                        eprintln!(
                            "lower unbound var path={path:?} resolved={resolved_path:?} expected={expected:?} stored={stored_ty:?} symbol={:?}",
                            runtime_symbol_kind
                        );
                    }
                    RuntimeError::UnboundVariable { path: path.clone() }
                })?;
                let is_effect_op =
                    runtime_symbol_kind == Some(typed_ir::RuntimeSymbolKind::EffectOperation);
                let ty = if reject_non_runtime_hir_type(&ty, TypeSource::Local).is_err() {
                    if is_effect_op {
                        // Don't strip the operation's signature Vars to Unknown
                        // here — they need to survive to runtime-finalize so
                        // monomorphization substitutions can resolve them.
                        ty
                    } else {
                        project_runtime_hir_runtime_type_with_vars(ty, &self.principal_vars)
                    }
                } else {
                    ty
                };
                if !is_effect_op {
                    reject_non_runtime_hir_type(&ty, TypeSource::Local)?;
                }
                let kind =
                    if runtime_symbol_kind == Some(typed_ir::RuntimeSymbolKind::EffectOperation) {
                        ExprKind::EffectOp(resolved_path)
                    } else if is_bound
                        || runtime_symbol_kind == Some(typed_ir::RuntimeSymbolKind::RoleMethod)
                    {
                        ExprKind::Var(resolved_path)
                    } else {
                        ExprKind::Var(resolved_path)
                    };
                let expr = Expr::typed(kind, ty);
                if local_ty.is_some()
                    && let Some(boundary) = self.local_param_boundaries.get(&path).cloned()
                {
                    if matches!(expr.ty, RuntimeType::Thunk { .. }) && boundary.applies_to_thunk_var
                    {
                        return Ok(add_boundary_id(
                            expr,
                            EffectIdRef::Var(boundary.id),
                            boundary.effect.clone(),
                        ));
                    }
                    if let Some(protected) = self.protect_local_function_value(
                        path.clone(),
                        expr.clone(),
                        &boundary,
                        expected,
                    ) {
                        return Ok(protected);
                    }
                }
                if let Some(stored) = local_ty.as_ref()
                    && should_refine_local_from_argument_expected(stored, &expr.ty, expected_source)
                {
                    locals.insert(path, expr.ty.clone());
                }
                Ok(expr)
            }
            typed_ir::Expr::PrimitiveOp(op) => {
                let ty = expected.cloned().unwrap_or_else(RuntimeType::unknown);
                reject_non_runtime_hir_type(&ty, expected_source)?;
                Ok(Expr::typed(ExprKind::PrimitiveOp(op), ty))
            }
            typed_ir::Expr::Lit(lit) => {
                let ty = self.primitive_paths.lit_type(&lit);
                if let Some(expected) = expected {
                    if matches!(expected, RuntimeType::Unknown) {
                        return Ok(Expr::typed(ExprKind::Lit(lit), ty));
                    }
                    if matches!(expected, RuntimeType::Thunk { .. }) {
                        let expr = Expr::typed(ExprKind::Lit(lit), ty);
                        return prepare_expr_for_expected_with_adapter_source_profiled(
                            expr,
                            expected,
                            expected_source,
                            &mut self.runtime_adapter_profile,
                            self.current_runtime_adapter_source.clone(),
                        );
                    }
                    let expected_core = core_type(expected);
                    require_same_type(expected_core, &ty, expected_source)?;
                    if self
                        .primitive_paths
                        .needs_runtime_coercion(expected_core, &ty)
                    {
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
            typed_ir::Expr::Lambda {
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
                    Some(RuntimeType::Unknown)
                    | Some(RuntimeType::Core(typed_ir::Type::Never))
                    | None => (RuntimeType::unknown(), None),
                    Some(RuntimeType::Core(typed_ir::Type::Any)) => {
                        (RuntimeType::core(typed_ir::Type::Any), None)
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
                let local = typed_ir::Path::from_name(param.clone());
                let previous = locals.insert(local.clone(), param_ty.clone());
                let boundary_id = self.fresh_effect_id_var();
                let boundary_effect = runtime_boundary_effect_for_param(
                    param_effect_annotation.as_ref(),
                    param_function_allowed_effects.as_ref(),
                    &param_ty,
                )
                .map(|effect| project_runtime_effect(&effect));
                let applies_to_thunk_var =
                    param_effect_annotation.is_some() || param_function_allowed_effects.is_some();
                let applies_to_call_outside_handler = applies_to_thunk_var
                    || !ret_expected.is_some_and(runtime_type_returns_function);
                let previous_boundary = match boundary_effect {
                    Some(effect) => self.local_param_boundaries.insert(
                        local.clone(),
                        LocalParamBoundary {
                            id: boundary_id,
                            effect,
                            applies_to_thunk_var,
                            applies_to_call_outside_handler,
                        },
                    ),
                    None => self.local_param_boundaries.remove(&local),
                };
                let previous_function_boundary =
                    self.current_function_boundary.replace(boundary_id);
                let body_expected = match ret_expected {
                    Some(ret) => Some(ret.clone()),
                    None => None,
                };
                let body =
                    self.lower_expr(*body, body_expected.as_ref(), locals, TypeSource::Expected)?;
                self.current_function_boundary = previous_function_boundary;
                let actual_param_ty = locals
                    .get(&local)
                    .cloned()
                    .unwrap_or_else(|| param_ty.clone());
                restore_local(locals, local, previous);
                restore_local_param_boundary(
                    &mut self.local_param_boundaries,
                    typed_ir::Path::from_name(param.clone()),
                    previous_boundary,
                );
                let body = self.protect_function_body(body, boundary_id);
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
            typed_ir::Expr::Apply {
                callee,
                arg,
                evidence,
            } => {
                if let Some(evidence) = &evidence {
                    self.validate_apply_callee_source_edge(evidence.callee_source_edge);
                    self.validate_apply_arg_source_edge(evidence.arg_source_edge);
                }
                let mut callee_expr = Some(*callee);
                let mut arg_expr = Some(*arg);
                let apply_target = callee_expr.as_ref().and_then(core_apply_head_target);
                let apply_label = callee_expr.as_ref().and_then(core_apply_head_label);
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
                let evidence_expected_callee = evidence
                    .as_ref()
                    .and_then(|evidence| evidence.expected_callee.as_ref())
                    .and_then(|bounds| self.tir_declared_runtime_hir_type(bounds));
                let evidence_arg = evidence
                    .as_ref()
                    .and_then(|evidence| self.tir_evidence_runtime_type(&evidence.arg))
                    .map(RuntimeType::core);
                let evidence_arg_lower = evidence
                    .as_ref()
                    .and_then(|evidence| self.tir_argument_runtime_type(&evidence.arg))
                    .map(RuntimeType::core);
                let evidence_expected_arg = self
                    .expected_arg_evidence_runtime_type(
                        evidence
                            .as_ref()
                            .and_then(|evidence| evidence.arg_source_edge),
                        evidence
                            .as_ref()
                            .and_then(|evidence| evidence.expected_arg.as_ref()),
                    )
                    .or_else(|| {
                        self.use_principal_elaboration
                            .then(|| {
                                evidence
                                    .as_ref()
                                    .and_then(|evidence| {
                                        self.visible_apply_evidence_arg_type(evidence)
                                    })
                                    .map(RuntimeType::core)
                                    .filter(expected_arg_evidence_runtime_usable)
                            })
                            .flatten()
                    });
                let evidence_result = evidence
                    .as_ref()
                    .and_then(|evidence| {
                        self.visible_apply_evidence_result_type(evidence)
                            .or_else(|| self.tir_evidence_runtime_type(&evidence.result))
                    })
                    .map(RuntimeType::core);
                let has_evidence_result = evidence_result.is_some();
                let callee_local_hint = match callee_expr.as_ref() {
                    Some(typed_ir::Expr::Var(path)) => locals.get(path).cloned(),
                    _ => None,
                };
                let callee_boundary = match callee_expr.as_ref() {
                    Some(typed_ir::Expr::Var(path)) => {
                        self.local_param_boundaries.get(path).and_then(|boundary| {
                            (boundary.applies_to_call_outside_handler
                                || self.handler_body_depth > 0)
                                .then(|| boundary.clone())
                        })
                    }
                    _ => None,
                };
                let callee_boundary_effect = callee_boundary
                    .as_ref()
                    .map(|boundary| boundary.effect.clone());
                let callee_stored_hint =
                    callee_local_hint
                        .clone()
                        .or_else(|| match callee_expr.as_ref() {
                            Some(typed_ir::Expr::Var(path)) => self.env.get(path).cloned(),
                            _ => None,
                        });
                let callee_is_polymorphic_binding = callee_expr.as_ref().is_some_and(|expr| {
                    let typed_ir::Expr::Var(path) = expr else {
                        return false;
                    };
                    self.binding_infos
                        .get(path)
                        .is_some_and(|info| !info.type_params.is_empty())
                });
                let polymorphic_arg_hint = evidence_expected_arg.clone().filter(|hint| {
                    callee_is_polymorphic_binding
                        && self.use_principal_elaboration
                        && expected_arg_evidence_runtime_usable(hint)
                        && matches!(hint, RuntimeType::Core(typed_ir::Type::Variant(_)))
                        && callee_stored_hint
                            .as_ref()
                            .and_then(|ty| function_parts(ty).ok())
                            .is_none_or(|parts| should_use_polymorphic_arg_hint(&parts.param, hint))
                });
                let use_polymorphic_arg_hint = polymorphic_arg_hint.is_some();
                let callee_hint = if polymorphic_arg_hint.is_some() {
                    None
                } else {
                    choose_apply_callee_type(evidence_callee, callee_stored_hint.clone())
                };
                let mut callee = None;
                let mut fun_parts = callee_hint
                    .as_ref()
                    .and_then(|ty| function_parts(ty).ok())
                    .or_else(|| {
                        if use_polymorphic_arg_hint {
                            return None;
                        }
                        callee_stored_hint
                            .as_ref()
                            .and_then(|ty| function_parts(ty).ok())
                    });
                if fun_parts.is_none()
                    && evidence_arg.is_none()
                    && !matches!(
                        callee_expr.as_ref(),
                        Some(typed_ir::Expr::Var(path)) if self.is_external_runtime_path(path, locals)
                    )
                    && !matches!(callee_expr.as_ref(), Some(typed_ir::Expr::Apply { .. }))
                {
                    let callee_expected =
                        callee_hint.as_ref().and_then(|callee_ty| match callee_ty {
                            RuntimeType::Core(typed_ir::Type::Var(_)) => None,
                            other if hir_type_contains_unknown(other) => None,
                            other => Some(other),
                        });
                    let adapter_source = self.runtime_adapter_source_for_apply(
                        RuntimeApplyAdapterPhase::LowerCallee,
                        evidence.as_ref(),
                        apply_target.as_ref(),
                    );
                    let lowered = self.lower_expr_with_runtime_adapter_source(
                        callee_expr.take().expect("callee should be present"),
                        callee_expected,
                        locals,
                        TypeSource::ApplyCalleeEvidence,
                        adapter_source,
                    )?;
                    let (lowered, lowered_ty) =
                        force_value_expr_profiled(lowered, &mut self.runtime_adapter_profile);
                    fun_parts = function_parts(&lowered_ty).ok();
                    callee = Some(lowered);
                }
                let ret_hint = fun_parts.as_ref().map(|parts| parts.ret.clone());
                let boundary_stored_ret_hint = if callee_boundary_effect.is_some() {
                    callee_stored_hint
                        .as_ref()
                        .and_then(|ty| function_parts(ty).ok())
                        .map(|parts| parts.ret)
                } else {
                    None
                };
                let boundary_thunk_result_hint = if callee_boundary_effect.is_some() {
                    ret_hint
                        .as_ref()
                        .filter(|ty| matches!(ty, RuntimeType::Thunk { .. }))
                        .cloned()
                        .or_else(|| {
                            boundary_stored_ret_hint
                                .as_ref()
                                .filter(|ty| matches!(ty, RuntimeType::Thunk { .. }))
                                .cloned()
                        })
                } else {
                    None
                };
                let boundary_result_hint = boundary_thunk_result_hint;
                let preserve_boundary_thunk_result = boundary_result_hint.is_some();
                let has_apply_result_hint = has_evidence_result || ret_hint.is_some();
                let structural_result_hint = callee_expr
                    .as_ref()
                    .zip(arg_expr.as_ref())
                    .and_then(|(callee, arg)| self.visible_structural_apply_type(callee, arg))
                    .filter(|ty| {
                        is_concrete_visible_root_type(ty) && !contains_non_runtime_type(ty)
                    })
                    .map(RuntimeType::core);
                let result_ty = choose_apply_result_type(
                    evidence_result,
                    ret_hint,
                    callee_local_hint.is_some(),
                )
                .and_then(|ty| choose_expected_hir_type(ty, expected.cloned()))
                .or_else(|| expected.cloned())
                .unwrap_or_else(|| RuntimeType::core(self.fresh_type_var("apply_result")));
                let result_ty = match (expected, structural_result_hint.as_ref()) {
                    (Some(expected), Some(structural))
                        if !hir_type_compatible(expected, &result_ty)
                            && hir_type_compatible(expected, structural) =>
                    {
                        expected.clone()
                    }
                    (Some(expected), _)
                        if has_apply_result_hint
                            && matches!(
                                expected_source,
                                TypeSource::BindingScheme | TypeSource::RootGraph
                            )
                            && !runtime_type_is_imprecise_runtime_slot(expected)
                            && !hir_type_contains_unknown(expected)
                            && !hir_type_compatible(expected, &result_ty) =>
                    {
                        expected.clone()
                    }
                    (Some(expected), _)
                        if apply_target.is_some()
                            && callee_stored_hint
                                .as_ref()
                                .is_some_and(hir_type_has_type_vars)
                            && !runtime_type_is_imprecise_runtime_slot(expected)
                            && !hir_type_contains_unknown(expected)
                            && !hir_type_compatible(expected, &result_ty) =>
                    {
                        expected.clone()
                    }
                    _ => result_ty,
                };
                let result_ty = boundary_result_hint.unwrap_or(result_ty);
                if let Some(expected) = expected
                    && !preserve_boundary_thunk_result
                {
                    require_apply_result_compatible(expected, &result_ty, expected_source)
                        .map_err(|error| {
                            error.with_type_mismatch_context(apply_type_mismatch_context(
                                apply_label.clone(),
                                evidence.as_ref(),
                                TypeMismatchPhase::ApplyResult,
                            ))
                        })?;
                }
                let mut arg = None;
                let param_hint = fun_parts.as_ref().map(|parts| parts.param.clone());
                let expected_callee_param_hint = self
                    .use_principal_elaboration
                    .then(|| {
                        evidence_expected_callee
                            .as_ref()
                            .and_then(|ty| function_parts(ty).ok())
                            .map(|parts| parts.param)
                            .or_else(|| {
                                evidence
                                    .as_ref()
                                    .and_then(|evidence| {
                                        self.visible_apply_evidence_arg_type(evidence)
                                    })
                                    .map(RuntimeType::core)
                                    .filter(expected_arg_evidence_runtime_usable)
                            })
                    })
                    .flatten();
                let expected_callee_param_hint_for_imprecise = expected_callee_param_hint.clone();
                let evidence_expected_arg_for_imprecise = evidence_expected_arg
                    .clone()
                    .filter(|_| self.use_expected_arg_evidence || self.use_principal_elaboration);
                let param_or_expected_arg_hint = match (param_hint, evidence_expected_arg.clone()) {
                    (_, _)
                        if callee_local_hint.is_some()
                            && matches!(
                                expected_callee_param_hint,
                                Some(RuntimeType::Thunk { .. })
                            ) =>
                    {
                        expected_callee_param_hint
                    }
                    (Some(RuntimeType::Core(typed_ir::Type::Any | typed_ir::Type::Var(_))), _) => {
                        expected_callee_param_hint
                    }
                    (Some(param_hint), _)
                        if runtime_type_is_imprecise_runtime_slot(&param_hint) =>
                    {
                        expected_callee_param_hint_for_imprecise
                            .or(evidence_expected_arg_for_imprecise)
                            .or(Some(param_hint))
                    }
                    (Some(param_hint), Some(expected_arg))
                        if self.use_principal_elaboration
                            && should_use_variant_arg_hint(&param_hint, &expected_arg) =>
                    {
                        Some(expected_arg)
                    }
                    (Some(param_hint), _) => Some(param_hint),
                    (None, Some(expected_arg)) if self.use_expected_arg_evidence => {
                        self.expected_arg_evidence_profile.used_as_arg_type_hint += 1;
                        Some(expected_arg)
                    }
                    (None, _) => polymorphic_arg_hint.or(expected_callee_param_hint),
                };
                let selected_arg_hint = param_or_expected_arg_hint.clone();
                let arg_ty = match choose_apply_arg_type(evidence_arg, param_or_expected_arg_hint) {
                    Some(arg_ty) => arg_ty,
                    None => {
                        let adapter_source = self.runtime_adapter_source_for_apply(
                            RuntimeApplyAdapterPhase::LowerArgument,
                            evidence.as_ref(),
                            apply_target.as_ref(),
                        );
                        let lowered = self.lower_expr_with_runtime_adapter_source(
                            arg_expr.take().expect("arg should be present"),
                            None,
                            locals,
                            TypeSource::ApplyArgumentEvidence,
                            adapter_source,
                        )?;
                        let (lowered, arg_ty) = match lowered.ty {
                            RuntimeType::Thunk { .. } => {
                                let arg_ty = lowered.ty.clone();
                                (lowered, arg_ty)
                            }
                            _ => force_value_expr_profiled(
                                lowered,
                                &mut self.runtime_adapter_profile,
                            ),
                        };
                        arg = Some(lowered);
                        arg_ty
                    }
                };
                let callee = match callee {
                    Some(callee) => callee,
                    None => {
                        let callee_expected = match callee_hint.as_ref() {
                            Some(ty)
                                if !hir_type_contains_unknown(ty)
                                    && function_parts(ty).ok().is_none_or(|parts| {
                                        hir_type_compatible(&parts.ret, &result_ty)
                                    }) =>
                            {
                                Some(ty.clone())
                            }
                            Some(ty)
                                if !hir_type_contains_unknown(ty) && function_parts(ty).is_ok() =>
                            {
                                Some(erased_fun_type(arg_ty.clone(), result_ty.clone()))
                            }
                            None if use_polymorphic_arg_hint => {
                                Some(erased_fun_type(arg_ty.clone(), result_ty.clone()))
                            }
                            None => callee_stored_hint.clone().or_else(|| {
                                Some(erased_fun_type(arg_ty.clone(), result_ty.clone()))
                            }),
                            Some(RuntimeType::Core(
                                typed_ir::Type::Any | typed_ir::Type::Var(_),
                            )) => Some(erased_fun_type(arg_ty.clone(), result_ty.clone())),
                            Some(other) if hir_type_contains_unknown(other) => None,
                            Some(other) => Some(other.clone()),
                        };
                        let adapter_source = self.runtime_adapter_source_for_apply(
                            RuntimeApplyAdapterPhase::LowerCallee,
                            evidence.as_ref(),
                            apply_target.as_ref(),
                        );
                        self.lower_expr_with_runtime_adapter_source(
                            callee_expr.take().expect("callee should be present"),
                            callee_expected.as_ref(),
                            locals,
                            TypeSource::ApplyCalleeEvidence,
                            adapter_source,
                        )?
                    }
                };
                let (mut callee, _) =
                    force_value_expr_profiled(callee, &mut self.runtime_adapter_profile);
                let arg = match arg {
                    Some(arg) => arg,
                    None => {
                        let arg_source = if evidence
                            .as_ref()
                            .is_some_and(|evidence| evidence.arg_source_edge.is_some())
                        {
                            TypeSource::ApplyArgumentSourceEdge
                        } else {
                            TypeSource::ApplyArgumentEvidence
                        };
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
                        } else {
                            let pending_arg = arg_expr
                                .as_ref()
                                .expect("arg should be present before lowering");
                            let can_push = can_push_expected_arg_through(pending_arg);
                            let can_push_expected_evidence =
                                can_push_expected_arg_evidence_through(pending_arg);
                            if let Some(expected_arg_ty) = evidence_expected_arg
                                .as_ref()
                                .filter(|_| {
                                    self.use_expected_arg_evidence && can_push_expected_evidence
                                })
                                .filter(|ty| runtime_type_can_be_pushed_as_lowering_expected(ty))
                            {
                                self.expected_arg_evidence_profile.used_as_lowering_expected += 1;
                                Some(expected_arg_ty)
                            } else {
                                if self.use_expected_arg_evidence
                                    && evidence_expected_arg.is_some()
                                    && !can_push_expected_evidence
                                {
                                    self.expected_arg_evidence_profile.ignored_no_push += 1;
                                }
                                if let Some(lower_arg_ty) = evidence_arg_lower
                                    .as_ref()
                                    .filter(|_| can_push)
                                    .filter(|ty| {
                                        runtime_type_can_be_pushed_as_lowering_expected(ty)
                                    })
                                {
                                    Some(lower_arg_ty)
                                } else if hir_type_has_type_vars(&arg_ty) && !can_push
                                    || !runtime_type_can_be_pushed_as_lowering_expected(&arg_ty)
                                {
                                    None
                                } else {
                                    Some(&arg_ty)
                                }
                            }
                        };
                        let adapter_source = self.runtime_adapter_source_for_apply(
                            RuntimeApplyAdapterPhase::LowerArgument,
                            evidence.as_ref(),
                            apply_target.as_ref(),
                        );
                        self.lower_expr_with_runtime_adapter_source(
                            arg_expr.take().expect("arg should be present"),
                            expected_arg,
                            locals,
                            arg_source,
                            adapter_source,
                        )?
                    }
                };
                let actual_arg_ty = arg.ty.clone();
                if matches!(
                    callee.ty,
                    RuntimeType::Unknown
                        | RuntimeType::Core(
                            typed_ir::Type::Never | typed_ir::Type::Any | typed_ir::Type::Var(_),
                        )
                ) {
                    let fallback_param = if matches!(callee.kind, ExprKind::EffectOp(_)) {
                        effect_operation_payload_param_hint(&arg_ty, &actual_arg_ty)
                    } else if runtime_type_is_imprecise_runtime_slot(&arg_ty) {
                        actual_arg_ty.clone()
                    } else {
                        arg_ty.clone()
                    };
                    callee.ty = erased_fun_type(fallback_param, result_ty.clone());
                }
                let final_fun_parts = function_parts(&callee.ty)?;
                let instantiation_arg_ty = if runtime_type_is_imprecise_runtime_slot(&actual_arg_ty)
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
                let mut final_param = choose_final_apply_param(
                    &final_fun_parts.param,
                    selected_arg_hint.as_ref(),
                    callee_local_hint.is_some(),
                );
                if runtime_type_is_imprecise_runtime_slot(&final_param)
                    && !matches!(callee.kind, ExprKind::EffectOp(_))
                    && !runtime_type_is_imprecise_runtime_slot(&actual_arg_ty)
                {
                    final_param = actual_arg_ty.clone();
                }
                if matches!(callee.kind, ExprKind::EffectOp(_))
                    && runtime_type_is_irrelevant_unit_value(&final_param)
                    && !runtime_type_is_imprecise_runtime_slot(&actual_arg_ty)
                {
                    final_param = actual_arg_ty.clone();
                }
                if evidence
                    .as_ref()
                    .is_some_and(|evidence| evidence.role_method)
                    && !runtime_type_is_imprecise_runtime_slot(&actual_arg_ty)
                    && !hir_type_contains_unknown(&actual_arg_ty)
                    && !hir_type_compatible(&final_param, &actual_arg_ty)
                {
                    final_param = actual_arg_ty.clone();
                }
                if self.use_principal_elaboration
                    && !runtime_type_is_imprecise_runtime_slot(&actual_arg_ty)
                    && !hir_type_contains_unknown(&actual_arg_ty)
                    && !hir_type_compatible(&final_param, &actual_arg_ty)
                    && widened_apply_arg_evidence_accepts_actual(
                        evidence_expected_arg.as_ref(),
                        evidence_arg_lower.as_ref(),
                        &actual_arg_ty,
                    )
                {
                    final_param = actual_arg_ty.clone();
                    final_fun_parts.param = final_param.clone();
                    callee.ty =
                        erased_fun_type(final_fun_parts.param.clone(), final_fun_parts.ret.clone());
                }
                if self.use_principal_elaboration
                    && callee_local_hint.is_some()
                    && matches!(final_param, RuntimeType::Thunk { .. })
                {
                    final_fun_parts.param = final_param.clone();
                    callee.ty =
                        erased_fun_type(final_fun_parts.param.clone(), final_fun_parts.ret.clone());
                }
                let apply_arg_adapter_source = Some(self.runtime_adapter_source_for_apply(
                    RuntimeApplyAdapterPhase::PrepareFinalArgument,
                    evidence.as_ref(),
                    apply_target.as_ref(),
                ));
                let arg = if matches!(callee.kind, ExprKind::EffectOp(_)) {
                    let apply_effect_adapter_source =
                        apply_arg_adapter_source.clone().map(|mut source| {
                            source.phase = RuntimeApplyAdapterPhase::PrepareEffectOperationArgument;
                            source
                        });
                    prepare_effect_operation_arg(
                        arg,
                        &final_param,
                        if apply_arg_adapter_source
                            .as_ref()
                            .is_some_and(|source| source.has_apply_arg_source_edge)
                        {
                            TypeSource::ApplyArgumentSourceEdge
                        } else {
                            TypeSource::ApplyEvidence
                        },
                        &mut self.runtime_adapter_profile,
                        apply_effect_adapter_source,
                    )
                    .map_err(|error| {
                        error.with_type_mismatch_context(apply_type_mismatch_context(
                            apply_label.clone(),
                            evidence.as_ref(),
                            TypeMismatchPhase::ApplyArgument,
                        ))
                    })?
                } else {
                    prepare_expr_for_expected_with_adapter_source_profiled(
                        arg,
                        &final_param,
                        if apply_arg_adapter_source
                            .as_ref()
                            .is_some_and(|source| source.has_apply_arg_source_edge)
                        {
                            TypeSource::ApplyArgumentSourceEdge
                        } else {
                            TypeSource::ApplyEvidence
                        },
                        &mut self.runtime_adapter_profile,
                        apply_arg_adapter_source,
                    )
                    .map_err(|error| {
                        error.with_type_mismatch_context(apply_type_mismatch_context(
                            apply_label.clone(),
                            evidence.as_ref(),
                            TypeMismatchPhase::ApplyArgument,
                        ))
                    })?
                };
                let arg_eval_effect = (!matches!(final_fun_parts.param, RuntimeType::Thunk { .. }))
                    .then(|| expr_forced_effect(&arg))
                    .flatten();
                if let Some(effect) = arg_eval_effect {
                    final_fun_parts.ret =
                        attach_effect_to_hir_type(final_fun_parts.ret.clone(), effect);
                    callee.ty =
                        erased_fun_type(final_fun_parts.param.clone(), final_fun_parts.ret.clone());
                }
                if !runtime_type_is_imprecise_runtime_slot(&final_param)
                    && !hir_type_contains_unknown(&final_param)
                {
                    require_apply_arg_compatible(&final_param, &arg.ty, TypeSource::ApplyEvidence)
                        .map_err(|error| {
                            error.with_type_mismatch_context(apply_type_mismatch_context(
                                apply_label.clone(),
                                evidence.as_ref(),
                                TypeMismatchPhase::ApplyArgument,
                            ))
                        })?;
                }
                let arg_value_core = runtime_core_type(value_hir_type(&arg.ty));
                if let ExprKind::EffectOp(path) = &callee.kind
                    && let Some(effect) =
                        effect_operation_effect(&self.primitive_paths, path, &arg_value_core)
                {
                    final_fun_parts.ret =
                        attach_effect_to_hir_type(final_fun_parts.ret.clone(), effect);
                    callee.ty =
                        erased_fun_type(final_fun_parts.param.clone(), final_fun_parts.ret.clone());
                }
                let effect_operation = match &callee.kind {
                    ExprKind::EffectOp(path) => Some((path.clone(), arg_value_core)),
                    _ => None,
                };
                let (apply_ty, apply_ty_overrides_ret) = match &final_fun_parts.ret {
                    ret if preserve_boundary_thunk_result
                        && matches!(ret, RuntimeType::Thunk { .. }) =>
                    {
                        (ret.clone(), false)
                    }
                    RuntimeType::Unknown
                    | RuntimeType::Core(
                        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_),
                    ) => (result_ty, true),
                    ret if expected.is_some_and(|expected| {
                        !hir_type_compatible(expected, ret)
                            && hir_type_compatible(expected, &result_ty)
                    }) =>
                    {
                        (result_ty, true)
                    }
                    _ => (final_fun_parts.ret.clone(), false),
                };
                if apply_ty_overrides_ret {
                    final_fun_parts.ret = apply_ty.clone();
                    callee.ty =
                        erased_fun_type(final_fun_parts.param.clone(), final_fun_parts.ret.clone());
                }
                let boundary_allowed = callee_boundary_effect.map(|allowed| {
                    (
                        callee_boundary.as_ref().map(|boundary| boundary.id),
                        allowed,
                    )
                });
                let boundary_ret_effect = boundary_allowed
                    .as_ref()
                    .and_then(|_| apply_evidence_ret_effect(evidence.as_ref()));
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
                    if let Some(effect) =
                        effect_operation_effect(&self.primitive_paths, &path, &arg_ty)
                    {
                        apply = attach_expr_effect(apply, effect);
                    }
                }
                if let Some((boundary_id, allowed)) = boundary_allowed {
                    if !matches!(apply.ty, RuntimeType::Thunk { .. }) {
                        if let Some(effect) = boundary_ret_effect {
                            apply = attach_expr_effect(apply, effect);
                        } else if local_callback_boundary_needs_wildcard_effect(
                            &final_fun_parts.ret,
                        ) {
                            apply = attach_expr_effect(apply, wildcard_effect_type());
                        }
                    }
                    let Some(boundary_id) = boundary_id else {
                        apply = add_boundary_id_with_peek(apply, allowed);
                        return finalize_effectful_expr_profiled(
                            apply,
                            expected,
                            expected_source,
                            &mut self.runtime_adapter_profile,
                            self.current_runtime_adapter_source.clone(),
                        );
                    };
                    apply = add_boundary_id(apply, EffectIdRef::Var(boundary_id), allowed);
                }
                finalize_effectful_expr_profiled(
                    apply,
                    expected,
                    expected_source,
                    &mut self.runtime_adapter_profile,
                    self.current_runtime_adapter_source.clone(),
                )
            }
            typed_ir::Expr::If {
                cond,
                then_branch,
                else_branch,
                evidence,
            } => {
                let result_ty = self.join_result_type(evidence.as_ref(), expected, "if")?;
                let result_hir_ty = RuntimeType::core(result_ty.clone());
                let cond = self.lower_expr(
                    *cond,
                    Some(&RuntimeType::core(self.primitive_paths.bool_type())),
                    locals,
                    TypeSource::Expected,
                )?;
                let then_branch =
                    self.lower_expr(*then_branch, None, locals, TypeSource::JoinEvidence)?;
                let then_branch = self.prepare_lowered_expr_for_expected(
                    then_branch,
                    &result_hir_ty,
                    TypeSource::JoinEvidence,
                )?;
                let else_branch =
                    self.lower_expr(*else_branch, None, locals, TypeSource::JoinEvidence)?;
                let else_branch = self.prepare_lowered_expr_for_expected(
                    else_branch,
                    &result_hir_ty,
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
                finalize_effectful_expr_profiled(
                    expr,
                    expected,
                    expected_source,
                    &mut self.runtime_adapter_profile,
                    self.current_runtime_adapter_source.clone(),
                )
            }
            typed_ir::Expr::Tuple(items) => {
                let expected_items = match expected.and_then(RuntimeType::as_core) {
                    Some(typed_ir::Type::Tuple(items)) => Some(items.as_slice()),
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
                            .map(|expr| {
                                force_core_value_expr_profiled(
                                    expr,
                                    &mut self.runtime_adapter_profile,
                                )
                                .0
                            })
                    })
                    .collect::<RuntimeResult<Vec<_>>>()?;
                let ty = typed_ir::Type::Tuple(
                    items
                        .iter()
                        .map(|item| core_type(&item.ty).clone())
                        .collect(),
                );
                let expr = Expr::typed(ExprKind::Tuple(items), ty);
                finalize_effectful_expr_profiled(
                    expr,
                    expected,
                    expected_source,
                    &mut self.runtime_adapter_profile,
                    self.current_runtime_adapter_source.clone(),
                )
            }
            typed_ir::Expr::Record { fields, spread } => {
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
                            value: {
                                let value = self.lower_expr(
                                    field.value,
                                    expected.as_ref(),
                                    locals,
                                    TypeSource::Expected,
                                )?;
                                force_value_expr_profiled(value, &mut self.runtime_adapter_profile)
                                    .0
                            },
                        })
                    })
                    .collect::<RuntimeResult<Vec<_>>>()?;
                let spread = spread
                    .map(|spread| self.lower_record_spread_expr(spread, locals))
                    .transpose()?;
                let ty = typed_ir::Type::Record(typed_ir::RecordType {
                    fields: fields
                        .iter()
                        .map(|field| typed_ir::RecordField {
                            name: field.name.clone(),
                            value: diagnostic_core_type(&field.value.ty),
                            optional: false,
                        })
                        .collect(),
                    spread: None,
                });
                let expr = Expr::typed(ExprKind::Record { fields, spread }, ty);
                finalize_effectful_expr_profiled(
                    expr,
                    expected,
                    expected_source,
                    &mut self.runtime_adapter_profile,
                    self.current_runtime_adapter_source.clone(),
                )
            }
            typed_ir::Expr::Variant {
                tag,
                value,
                source: _,
            } => {
                let expected_core = expected.and_then(RuntimeType::as_core);
                let expected_payload =
                    variant_payload_expected(self, expected_core, &tag).map(RuntimeType::core);
                let value = value
                    .map(|value| {
                        self.lower_expr(
                            *value,
                            expected_payload.as_ref(),
                            locals,
                            TypeSource::Expected,
                        )
                        .map(|expr| {
                            force_core_value_expr_profiled(expr, &mut self.runtime_adapter_profile)
                                .0
                        })
                        .map(Box::new)
                    })
                    .transpose()?;
                let ty = expected
                    .and_then(RuntimeType::as_core)
                    .cloned()
                    .unwrap_or_else(|| {
                        typed_ir::Type::Variant(typed_ir::VariantType {
                            cases: vec![typed_ir::VariantCase {
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
                finalize_effectful_expr_profiled(
                    expr,
                    expected,
                    expected_source,
                    &mut self.runtime_adapter_profile,
                    self.current_runtime_adapter_source.clone(),
                )
            }
            typed_ir::Expr::Select { base, field } => {
                let base = self.lower_expr(*base, None, locals, TypeSource::Expected)?;
                let (base, base_ty) =
                    force_core_value_expr_profiled(base, &mut self.runtime_adapter_profile);
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
                finalize_effectful_expr_profiled(
                    expr,
                    expected,
                    expected_source,
                    &mut self.runtime_adapter_profile,
                    self.current_runtime_adapter_source.clone(),
                )
            }
            typed_ir::Expr::Match {
                scrutinee,
                arms,
                evidence,
            } => {
                let result_ty = self.join_result_type(evidence.as_ref(), expected, "match")?;
                let result_hir_ty = RuntimeType::core(result_ty.clone());
                let scrutinee = self.lower_expr(*scrutinee, None, locals, TypeSource::Expected)?;
                let (scrutinee, scrutinee_ty) =
                    force_core_value_expr_profiled(scrutinee, &mut self.runtime_adapter_profile);
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
                                    Some(&RuntimeType::core(self.primitive_paths.bool_type())),
                                    &mut arm_locals,
                                    TypeSource::Expected,
                                )
                            })
                            .transpose()?;
                        let body = self.lower_expr(
                            arm.body,
                            None,
                            &mut arm_locals,
                            TypeSource::JoinEvidence,
                        )?;
                        let body = self.prepare_lowered_expr_for_expected(
                            body,
                            &result_hir_ty,
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
                finalize_effectful_expr_profiled(
                    expr,
                    expected,
                    expected_source,
                    &mut self.runtime_adapter_profile,
                    self.current_runtime_adapter_source.clone(),
                )
            }
            typed_ir::Expr::Block { mut stmts, tail } => {
                let mut block_locals = locals.clone();
                for stmt in &stmts {
                    self.prebind_block_local(stmt, &mut block_locals);
                }
                let tail = tail.or_else(|| match stmts.last() {
                    Some(typed_ir::Stmt::Expr(_)) => match stmts.pop() {
                        Some(typed_ir::Stmt::Expr(expr)) => Some(Box::new(expr)),
                        _ => None,
                    },
                    _ => None,
                });
                let stmt_expected = expected.and_then(|ty| match ty {
                    RuntimeType::Thunk { .. } => {
                        Some(RuntimeType::core(self.primitive_paths.unit_type()))
                    }
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
                    .unwrap_or_else(|| RuntimeType::core(self.primitive_paths.unit_type()));
                propagate_refined_locals(locals, &block_locals);
                let expr = Expr {
                    ty,
                    kind: ExprKind::Block { stmts, tail },
                };
                finalize_effectful_expr_profiled(
                    expr,
                    expected,
                    expected_source,
                    &mut self.runtime_adapter_profile,
                    self.current_runtime_adapter_source.clone(),
                )
            }
            typed_ir::Expr::BindHere { expr } => {
                let expr = self.lower_expr(*expr, None, locals, TypeSource::Expected)?;
                let value_ty = match &expr.ty {
                    RuntimeType::Thunk { value, .. } => value.as_ref().clone(),
                    _ => expected.cloned().unwrap_or_else(|| expr.ty.clone()),
                };
                let expr = bind_here_if_thunk(expr, value_ty);
                finalize_effectful_expr_profiled(
                    expr,
                    expected,
                    expected_source,
                    &mut self.runtime_adapter_profile,
                    self.current_runtime_adapter_source.clone(),
                )
            }
            typed_ir::Expr::Handle {
                body,
                arms,
                evidence,
            } => {
                let (result_hint, missing_join_evidence) =
                    match self.join_result_type(evidence.as_ref(), expected, "handle") {
                        Ok(result) => (result, false),
                        Err(RuntimeError::MissingJoinEvidence { node: "handle" }) => (
                            self.visible_handle_result_type(&arms)
                                .unwrap_or(typed_ir::Type::Unknown),
                            true,
                        ),
                        Err(error) => return Err(error),
                    };
                let result_ty =
                    if expected.is_none() && core_type_is_imprecise_runtime_slot(&result_hint) {
                        self.visible_handle_result_type(&arms)
                            .unwrap_or(result_hint)
                    } else {
                        result_hint
                    };
                let body_expected = (missing_join_evidence
                    && handle_body_is_imprecise_local_value(&body, locals))
                .then(|| {
                    self.handler_consumes_from_core_arms(&arms, &result_ty, None)
                        .map(|effect| {
                            RuntimeType::thunk(effect, RuntimeType::core(result_ty.clone()))
                        })
                })
                .flatten();
                self.handler_body_depth += 1;
                let body_result =
                    self.lower_expr(*body, body_expected.as_ref(), locals, TypeSource::Expected);
                self.handler_body_depth -= 1;
                let body = body_result?;
                let body_effect_before =
                    expr_forced_effect(&body).or_else(|| thunk_effect(&body.ty));
                let handled = self
                    .handler_consumes_from_core_arms(&arms, &result_ty, body_effect_before.as_ref())
                    .unwrap_or_else(|| handler_consumes_from_body_type(&body.ty));
                let handled = canonicalize_handled_effects(handled, body_effect_before.as_ref());
                let resume_effect = body_effect_before
                    .as_ref()
                    .map(|effect| handler_body_residual(effect, &handled));
                let body =
                    thunk_handler_body_if_needed(body, body_effect_before.as_ref(), &handled);
                let body_value_ty = runtime_core_type(value_hir_type(&body.ty));
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        self.lower_handle_arm(
                            arm,
                            &body_value_ty,
                            resume_effect.as_ref(),
                            &result_ty,
                            &handled,
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
                finalize_handler_expr_profiled(
                    expr,
                    expected,
                    expected_source,
                    &mut self.runtime_adapter_profile,
                    self.current_runtime_adapter_source.clone(),
                )
            }
            typed_ir::Expr::Coerce { expr, evidence } => {
                if let Some(evidence) = &evidence {
                    self.validate_coerce_source_edge(evidence.source_edge);
                }
                let evidence_actual = evidence
                    .as_ref()
                    .and_then(|evidence| self.tir_evidence_runtime_type(&evidence.actual))
                    .map(RuntimeType::core);
                let evidence_expected = evidence
                    .as_ref()
                    .and_then(|evidence| self.tir_evidence_runtime_type(&evidence.expected))
                    .map(RuntimeType::core);
                let expr = self.lower_expr(*expr, None, locals, TypeSource::Expected)?;
                let (expr, from) =
                    force_core_value_expr_profiled(expr, &mut self.runtime_adapter_profile);
                let evidence_from = evidence_actual
                    .as_ref()
                    .filter(|ty| !hir_type_has_type_vars(ty))
                    .and_then(RuntimeType::as_core)
                    .cloned();
                let ty = expected
                    .cloned()
                    .or_else(|| evidence_expected.filter(|ty| !hir_type_has_type_vars(ty)))
                    .unwrap_or_else(|| RuntimeType::core(from.clone()));
                let value_ty = value_hir_type(&ty).clone();
                let to = runtime_core_type(&value_ty);
                let from = if self.implicit_cast_method_path(&from, &to).is_some() {
                    from
                } else {
                    evidence_from.unwrap_or(from)
                };
                if let Some(cast) = self.implicit_cast_method_path(&from, &to) {
                    let callee_ty = self.env.get(&cast).cloned().unwrap_or_else(|| {
                        RuntimeType::fun(
                            RuntimeType::core(from.clone()),
                            RuntimeType::core(to.clone()),
                        )
                    });
                    let callee = Expr::typed(ExprKind::Var(cast), callee_ty);
                    let expr = Expr::typed(
                        ExprKind::Apply {
                            callee: Box::new(callee),
                            arg: Box::new(expr),
                            evidence: None,
                            instantiation: None,
                        },
                        RuntimeType::core(to),
                    );
                    return finalize_effectful_expr_profiled(
                        expr,
                        expected,
                        expected_source,
                        &mut self.runtime_adapter_profile,
                        self.current_runtime_adapter_source.clone(),
                    );
                }
                let expr = Expr::typed(
                    ExprKind::Coerce {
                        from,
                        to,
                        expr: Box::new(expr),
                    },
                    ty,
                );
                finalize_effectful_expr_profiled(
                    expr,
                    expected,
                    expected_source,
                    &mut self.runtime_adapter_profile,
                    self.current_runtime_adapter_source.clone(),
                )
            }
            typed_ir::Expr::Pack { var, expr } => {
                let expr = self.lower_expr(*expr, expected, locals, expected_source)?;
                let (expr, value_ty) =
                    force_value_expr_profiled(expr, &mut self.runtime_adapter_profile);
                let ty = expected.cloned().unwrap_or(value_ty);
                let expr = Expr::typed(
                    ExprKind::Pack {
                        var,
                        expr: Box::new(expr),
                    },
                    ty,
                );
                finalize_effectful_expr_profiled(
                    expr,
                    expected,
                    expected_source,
                    &mut self.runtime_adapter_profile,
                    self.current_runtime_adapter_source.clone(),
                )
            }
        }
    }

    fn lower_expr_with_runtime_adapter_source(
        &mut self,
        expr: typed_ir::Expr,
        expected: Option<&RuntimeType>,
        locals: &mut HashMap<typed_ir::Path, RuntimeType>,
        expected_source: TypeSource,
        adapter_source: RuntimeAdapterSource,
    ) -> RuntimeResult<Expr> {
        let context = type_mismatch_context_for_adapter_source(&adapter_source);
        let old_source = self.current_runtime_adapter_source.replace(adapter_source);
        let result = self
            .lower_expr(expr, expected, locals, expected_source)
            .map_err(|error| error.with_type_mismatch_context(context));
        self.current_runtime_adapter_source = old_source;
        result
    }

    fn runtime_adapter_source_for_apply(
        &self,
        phase: RuntimeApplyAdapterPhase,
        evidence: Option<&typed_ir::ApplyEvidence>,
        apply_target: Option<&typed_ir::Path>,
    ) -> RuntimeAdapterSource {
        RuntimeAdapterSource {
            phase,
            has_apply_evidence: evidence.is_some(),
            has_apply_callee_source_edge: evidence
                .is_some_and(|evidence| evidence.callee_source_edge.is_some()),
            has_apply_arg_source_edge: evidence
                .is_some_and(|evidence| evidence.arg_source_edge.is_some()),
            callee_source_edge: evidence.and_then(|evidence| evidence.callee_source_edge),
            arg_source_edge: evidence.and_then(|evidence| evidence.arg_source_edge),
            owner: self.current_binding.clone(),
            apply_target: apply_target.cloned(),
        }
    }

    fn prebind_block_local(
        &self,
        stmt: &typed_ir::Stmt,
        locals: &mut HashMap<typed_ir::Path, RuntimeType>,
    ) {
        let typed_ir::Stmt::Let { pattern, value } = stmt else {
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
            typed_ir::Path::from_name(name),
            project_runtime_hir_type_with_vars(&ty, &self.principal_vars),
        );
    }

    fn lambda_hint_type(&self, expr: &typed_ir::Expr) -> Option<typed_ir::Type> {
        let typed_ir::Expr::Lambda { body, .. } = expr else {
            return None;
        };
        let ret = self
            .lambda_hint_type(body)
            .or_else(|| self.visible_expr_type(body))?;
        Some(typed_ir::Type::Fun {
            param: Box::new(typed_ir::Type::Any),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(ret),
        })
    }

    pub(super) fn lower_stmt_with_expected(
        &mut self,
        stmt: typed_ir::Stmt,
        locals: &mut HashMap<typed_ir::Path, RuntimeType>,
        expected: Option<&RuntimeType>,
    ) -> RuntimeResult<Stmt> {
        match stmt {
            typed_ir::Stmt::Let { pattern, value } => {
                let value = self.lower_expr(value, None, locals, TypeSource::Expected)?;
                let (value, value_ty) =
                    force_value_expr_profiled(value, &mut self.runtime_adapter_profile);
                let pattern = lower_hir_pattern(self, pattern, &value_ty, locals)?;
                Ok(Stmt::Let { pattern, value })
            }
            typed_ir::Stmt::Expr(expr) => {
                let expr = self.lower_expr(expr, expected, locals, TypeSource::Expected)?;
                Ok(Stmt::Expr(
                    force_value_expr_profiled(expr, &mut self.runtime_adapter_profile).0,
                ))
            }
            typed_ir::Stmt::Module { def, body } => {
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
        arm: typed_ir::HandleArm,
        body_ty: &typed_ir::Type,
        body_effect: Option<&typed_ir::Type>,
        result_ty: &typed_ir::Type,
        handled: &typed_ir::Type,
        locals: &HashMap<typed_ir::Path, RuntimeType>,
    ) -> RuntimeResult<HandleArm> {
        let mut arm_locals = locals.clone();
        let payload_ty = if arm.effect == typed_ir::Path::default() {
            body_ty.clone()
        } else {
            infer_handle_payload_type(
                &self.primitive_paths,
                &arm.payload,
                arm.guard.as_ref(),
                &arm.body,
                result_ty,
            )
            .unwrap_or(typed_ir::Type::Unknown)
        };
        let payload = lower_pattern(self, arm.payload, &payload_ty, &mut arm_locals)?;
        let resume_ty = arm.resume.as_ref().map(|resume| {
            let param_ty = infer_resume_param_type(
                &self.primitive_paths,
                resume,
                arm.guard.as_ref(),
                &arm.body,
                &arm_locals,
            )
            .unwrap_or(typed_ir::Type::Unknown);
            let ret = body_effect
                .filter(|effect| should_thunk_effect(effect))
                .cloned()
                .map(|effect| RuntimeType::thunk(effect, RuntimeType::core(body_ty.clone())))
                .unwrap_or_else(|| RuntimeType::core(body_ty.clone()));
            erased_fun_type(RuntimeType::core(param_ty), ret)
        });
        if let Some(resume) = &arm.resume {
            arm_locals.insert(
                typed_ir::Path::from_name(resume.clone()),
                resume_ty.clone().unwrap_or(RuntimeType::unknown()),
            );
        }
        let guard = arm
            .guard
            .map(|guard| {
                self.lower_expr(
                    guard,
                    Some(&RuntimeType::core(self.primitive_paths.bool_type())),
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
            effect: self.resolve_handle_effect_operation_path_for_handle(&arm.effect, handled),
            payload,
            resume: arm.resume.map(|name| ResumeBinding {
                name,
                ty: resume_ty.unwrap_or(RuntimeType::unknown()),
            }),
            guard,
            body,
        })
    }

    fn resolve_handle_effect_operation_path_for_handle(
        &self,
        path: &typed_ir::Path,
        handled: &typed_ir::Type,
    ) -> typed_ir::Path {
        let resolved = self.resolve_handle_effect_operation_path(path);
        if self.runtime_symbol_kind(&resolved) == Some(typed_ir::RuntimeSymbolKind::EffectOperation)
        {
            return resolved;
        }
        let Some(op) = path.segments.last() else {
            return resolved;
        };
        let namespace = typed_ir::Path {
            segments: path
                .segments
                .iter()
                .take(path.segments.len().saturating_sub(1))
                .cloned()
                .collect(),
        };
        for consumed in effect_paths(handled) {
            let namespace_matches_consumed = namespace == consumed
                || (namespace.segments.len() == 1
                    && consumed
                        .segments
                        .last()
                        .is_some_and(|name| Some(name) == namespace.segments.last()));
            if namespace_matches_consumed {
                let mut candidate = consumed.clone();
                candidate
                    .segments
                    .push(typed_ir::Name(format!("{}#effect", op.0)));
                if self.runtime_symbol_kind(&candidate)
                    == Some(typed_ir::RuntimeSymbolKind::EffectOperation)
                {
                    return candidate;
                }
            }
        }
        resolved
    }

    fn handler_consumes_from_core_arms(
        &self,
        arms: &[typed_ir::HandleArm],
        result_ty: &typed_ir::Type,
        body_effect: Option<&typed_ir::Type>,
    ) -> Option<typed_ir::Type> {
        let items = arms
            .iter()
            .filter_map(|arm| self.consumed_effect_from_core_arm(arm, result_ty, body_effect))
            .collect::<Vec<_>>();
        (!items.is_empty()).then(|| effect_row_from_items(items))
    }

    fn consumed_effect_from_core_arm(
        &self,
        arm: &typed_ir::HandleArm,
        result_ty: &typed_ir::Type,
        body_effect: Option<&typed_ir::Type>,
    ) -> Option<typed_ir::Type> {
        let effect =
            self.resolve_core_handle_arm_effect_operation_path(&arm.effect, body_effect)?;
        if effect.segments.is_empty() {
            return None;
        }
        let effect_path = typed_ir::Path {
            segments: effect
                .segments
                .iter()
                .take(effect.segments.len().saturating_sub(1))
                .cloned()
                .collect(),
        };
        if effect_path.segments.is_empty() {
            return None;
        }
        let payload_ty = infer_handle_payload_type(
            &self.primitive_paths,
            &arm.payload,
            arm.guard.as_ref(),
            &arm.body,
            result_ty,
        );
        let args = payload_ty
            .filter(|ty| !matches!(ty, typed_ir::Type::Any | typed_ir::Type::Var(_)))
            .map(|ty| vec![typed_ir::TypeArg::Type(ty)])
            .unwrap_or_default();
        Some(typed_ir::Type::Named {
            path: effect_path,
            args,
        })
    }

    fn resolve_core_handle_arm_effect_operation_path(
        &self,
        path: &typed_ir::Path,
        body_effect: Option<&typed_ir::Type>,
    ) -> Option<typed_ir::Path> {
        if path.segments.len() != 1 {
            return Some(self.resolve_handle_effect_operation_path(path));
        }
        let op = path.segments.first()?;
        if let Some(owner) = self.current_binding.as_ref() {
            let mut namespace = owner.clone();
            namespace.segments.pop();
            if !namespace.segments.is_empty() {
                let mut candidate = namespace.clone();
                candidate.segments.push(op.clone());
                if self.runtime_symbol_kind(&candidate)
                    == Some(typed_ir::RuntimeSymbolKind::EffectOperation)
                {
                    return Some(candidate);
                }
                namespace
                    .segments
                    .push(typed_ir::Name(format!("{}#effect", op.0)));
                if self.runtime_symbol_kind(&namespace)
                    == Some(typed_ir::RuntimeSymbolKind::EffectOperation)
                {
                    return Some(namespace);
                }
            }
        }
        let body_effect = body_effect?;
        let mut candidates = Vec::new();
        for namespace in effect_paths(body_effect) {
            let mut candidate = namespace.clone();
            candidate.segments.push(op.clone());
            if self.runtime_symbol_kind(&candidate)
                == Some(typed_ir::RuntimeSymbolKind::EffectOperation)
                && !candidates.contains(&candidate)
            {
                candidates.push(candidate);
            }
            let mut effect_suffix_candidate = namespace;
            effect_suffix_candidate
                .segments
                .push(typed_ir::Name(format!("{}#effect", op.0)));
            if self.runtime_symbol_kind(&effect_suffix_candidate)
                == Some(typed_ir::RuntimeSymbolKind::EffectOperation)
                && !candidates.contains(&effect_suffix_candidate)
            {
                candidates.push(effect_suffix_candidate);
            }
        }
        match candidates.as_slice() {
            [candidate] => Some(candidate.clone()),
            _ => None,
        }
    }

    pub(super) fn lower_record_spread_expr(
        &mut self,
        spread: typed_ir::RecordSpreadExpr,
        locals: &mut HashMap<typed_ir::Path, RuntimeType>,
    ) -> RuntimeResult<RecordSpreadExpr> {
        match spread {
            typed_ir::RecordSpreadExpr::Head(expr) => {
                let expr = self.lower_expr(*expr, None, locals, TypeSource::Expected)?;
                Ok(RecordSpreadExpr::Head(Box::new(
                    force_core_value_expr_profiled(expr, &mut self.runtime_adapter_profile).0,
                )))
            }
            typed_ir::RecordSpreadExpr::Tail(expr) => {
                let expr = self.lower_expr(*expr, None, locals, TypeSource::Expected)?;
                Ok(RecordSpreadExpr::Tail(Box::new(
                    force_core_value_expr_profiled(expr, &mut self.runtime_adapter_profile).0,
                )))
            }
        }
    }

    pub(super) fn binding_graph_type(&self, path: &typed_ir::Path) -> Option<typed_ir::Type> {
        self.graph
            .bindings
            .iter()
            .find(|node| node.binding == *path)
            .and_then(|node| self.tir_evidence_runtime_type(&node.body_bounds))
    }

    pub(super) fn root_graph_type(&self, index: usize) -> Option<typed_ir::Type> {
        self.graph
            .root_exprs
            .iter()
            .find(|node| node.owner == typed_ir::GraphOwner::RootExpr(index))
            .and_then(|node| project_runtime_bounds(&node.bounds))
    }

    pub(super) fn root_expr_type(
        &self,
        index: usize,
        expr: &typed_ir::Expr,
    ) -> Option<typed_ir::Type> {
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

    pub(super) fn binding_runtime_type(&self, binding: &typed_ir::PrincipalBinding) -> RuntimeType {
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
        binding: &typed_ir::PrincipalBinding,
    ) -> Option<RuntimeType> {
        let typed_ir::Expr::Var(target) = &binding.body else {
            return None;
        };
        let target_ty = self.env.get(target)?;
        let scheme_ty =
            project_runtime_hir_type_with_vars(&binding.scheme.body, &self.principal_vars);
        prefer_alias_target_runtime_type(&scheme_ty, target_ty).then(|| target_ty.clone())
    }

    pub(super) fn tir_evidence_runtime_type(
        &self,
        bounds: &typed_ir::TypeBounds,
    ) -> Option<typed_ir::Type> {
        choose_bounds_type(bounds, BoundsChoice::TirEvidence)
            .map(|ty| project_runtime_hint_type_with_vars(&ty, &self.principal_vars))
    }

    pub(super) fn tir_argument_runtime_type(
        &self,
        bounds: &typed_ir::TypeBounds,
    ) -> Option<typed_ir::Type> {
        choose_bounds_type(bounds, BoundsChoice::MonomorphicExpected)
            .map(|ty| project_runtime_hint_type_with_vars(&ty, &self.principal_vars))
    }

    pub(super) fn tir_evidence_runtime_hir_type(
        &self,
        bounds: &typed_ir::TypeBounds,
    ) -> Option<RuntimeType> {
        choose_bounds_type(bounds, BoundsChoice::TirEvidence)
            .map(|ty| project_runtime_hir_type_with_vars(&ty, &self.principal_vars))
    }

    pub(super) fn tir_declared_runtime_hir_type(
        &self,
        bounds: &typed_ir::TypeBounds,
    ) -> Option<RuntimeType> {
        choose_bounds_type(bounds, BoundsChoice::MonomorphicExpected)
            .map(|ty| project_runtime_hir_type_with_vars(&ty, &self.principal_vars))
    }

    fn expected_arg_evidence_runtime_type(
        &mut self,
        source_edge: Option<u32>,
        bounds: Option<&typed_ir::TypeBounds>,
    ) -> Option<RuntimeType> {
        let Some(bounds) = bounds else {
            self.expected_arg_evidence_profile.ignored_no_expected_arg += 1;
            return None;
        };
        self.expected_arg_evidence_profile.present += 1;
        let Some(ty) = self
            .tir_argument_runtime_type(bounds)
            .map(RuntimeType::core)
        else {
            self.expected_arg_evidence_profile.ignored_not_convertible += 1;
            return None;
        };
        self.expected_arg_evidence_profile.converted += 1;
        let usable = match source_edge.and_then(|id| self.expected_edge(id).cloned()) {
            Some(edge) => {
                debug_assert_eq!(edge.kind, typed_ir::ExpectedEdgeKind::ApplicationArgument);
                self.profile_expected_arg_table_usability(bounds, &ty)
            }
            None => self.profile_expected_arg_bounds_usability(&ty),
        };
        if usable {
            Some(ty)
        } else {
            self.expected_arg_evidence_profile.ignored_unusable += 1;
            None
        }
    }

    fn validate_coerce_source_edge(&self, source_edge: Option<u32>) {
        if let Some(edge) = source_edge.and_then(|id| self.expected_edge(id)) {
            debug_assert_eq!(edge.kind, typed_ir::ExpectedEdgeKind::RepresentationCoerce);
        }
    }

    fn profile_expected_arg_table_usability(
        &mut self,
        bounds: &typed_ir::TypeBounds,
        ty: &RuntimeType,
    ) -> bool {
        let expected_closed = type_bounds_closed(bounds);
        let expected_informative = type_bounds_informative(bounds);
        let expected_runtime_usable = expected_arg_evidence_runtime_usable(ty);
        if expected_closed && expected_informative && expected_runtime_usable {
            self.expected_arg_evidence_profile.usable_by_table += 1;
            return true;
        }
        if !expected_closed {
            self.expected_arg_evidence_profile.ignored_table_open += 1;
        }
        if !expected_informative {
            self.expected_arg_evidence_profile
                .ignored_table_uninformative += 1;
        }
        if expected_closed && expected_informative && !expected_runtime_usable {
            self.expected_arg_evidence_profile
                .ignored_table_not_runtime_usable += 1;
        }
        false
    }

    fn profile_expected_arg_bounds_usability(&mut self, ty: &RuntimeType) -> bool {
        let usable = expected_arg_evidence_runtime_usable(ty);
        if usable {
            self.expected_arg_evidence_profile.usable_by_bounds += 1;
        } else {
            self.expected_arg_evidence_profile.ignored_bounds_unusable += 1;
        }
        usable
    }

    fn validate_apply_callee_source_edge(&self, source_edge: Option<u32>) {
        if let Some(edge) = source_edge.and_then(|id| self.expected_edge(id)) {
            debug_assert_eq!(edge.kind, typed_ir::ExpectedEdgeKind::ApplicationCallee);
        }
    }

    fn validate_apply_arg_source_edge(&self, source_edge: Option<u32>) {
        if let Some(edge) = source_edge.and_then(|id| self.expected_edge(id)) {
            debug_assert_eq!(edge.kind, typed_ir::ExpectedEdgeKind::ApplicationArgument);
        }
    }

    fn expected_edge(&self, id: u32) -> Option<&typed_ir::ExpectedEdgeEvidence> {
        self.expected_edges_by_id.get(&id).copied()
    }

    pub(super) fn core_expr_is_effect_operation(
        &self,
        expr: &typed_ir::Expr,
        locals: &HashMap<typed_ir::Path, RuntimeType>,
    ) -> bool {
        let typed_ir::Expr::Var(path) = expr else {
            return false;
        };
        if locals.contains_key(path) {
            return false;
        }
        let resolved_path = self.resolve_alias_path(path);
        self.runtime_symbol_kind(&resolved_path)
            == Some(typed_ir::RuntimeSymbolKind::EffectOperation)
    }

    pub(super) fn visible_principal_bounds_type(
        &self,
        bounds: &typed_ir::TypeBounds,
    ) -> Option<typed_ir::Type> {
        choose_bounds_type(bounds, BoundsChoice::VisiblePrincipal)
            .map(|ty| project_runtime_type_with_vars(&ty, &self.principal_vars))
    }

    fn visible_apply_evidence_result_type(
        &self,
        evidence: &typed_ir::ApplyEvidence,
    ) -> Option<typed_ir::Type> {
        let plan_result = evidence
            .principal_elaboration
            .as_ref()
            .and_then(|plan| self.visible_principal_plan_result_type(plan));
        let principal_result = evidence.principal_callee.as_ref().and_then(|principal| {
            self.visible_principal_callee_result_type(principal, &evidence.substitutions, 1)
        });
        let evidence_result = self.visible_principal_bounds_type(&evidence.result);
        [plan_result, principal_result, evidence_result]
            .into_iter()
            .flatten()
            .reduce(|left, right| choose_core_type(left, right, TypeChoice::VisiblePrincipal))
    }

    fn visible_apply_evidence_arg_type(
        &self,
        evidence: &typed_ir::ApplyEvidence,
    ) -> Option<typed_ir::Type> {
        let plan_arg = evidence.principal_elaboration.as_ref().and_then(|plan| {
            self.visible_principal_plan_arg_type(plan, 0, evidence.principal_callee.as_ref())
        });
        let principal_arg = evidence.principal_callee.as_ref().and_then(|principal| {
            self.visible_principal_callee_param_type(principal, &evidence.substitutions)
        });
        let expected_arg = evidence
            .expected_arg
            .as_ref()
            .and_then(|bounds| self.visible_principal_bounds_type(bounds));
        let evidence_arg = self.visible_principal_bounds_type(&evidence.arg);
        [plan_arg, principal_arg, expected_arg, evidence_arg]
            .into_iter()
            .flatten()
            .reduce(|left, right| choose_core_type(left, right, TypeChoice::VisiblePrincipal))
    }

    fn visible_principal_plan_result_type(
        &self,
        plan: &typed_ir::PrincipalElaborationPlan,
    ) -> Option<typed_ir::Type> {
        let substitutions = type_substitution_map(&plan.substitutions);
        let expected = plan
            .result
            .expected_runtime
            .as_ref()
            .map(|ty| substitute_type(ty, &substitutions));
        let contextual = plan
            .result
            .contextual
            .as_ref()
            .and_then(|bounds| self.visible_substituted_bounds_type(bounds, &substitutions));
        let intrinsic =
            self.visible_substituted_bounds_type(&plan.result.intrinsic, &substitutions);
        [expected, contextual, intrinsic]
            .into_iter()
            .flatten()
            .map(|ty| project_runtime_type_with_vars(&ty, &self.principal_vars))
            .reduce(|left, right| choose_core_type(left, right, TypeChoice::VisiblePrincipal))
    }

    fn visible_principal_plan_arg_type(
        &self,
        plan: &typed_ir::PrincipalElaborationPlan,
        index: usize,
        principal_hint: Option<&typed_ir::Type>,
    ) -> Option<typed_ir::Type> {
        let arg = plan.args.iter().find(|arg| arg.index == index)?;
        let principal = principal_hint.unwrap_or(&plan.principal_callee);
        let substitutions =
            visible_principal_arg_substitution_map(principal, &plan.substitutions, index);
        let expected = arg
            .expected_runtime
            .as_ref()
            .map(|ty| substitute_type(ty, &substitutions));
        let contextual = arg
            .contextual
            .as_ref()
            .and_then(|bounds| self.visible_substituted_bounds_type(bounds, &substitutions));
        let intrinsic = self.visible_substituted_bounds_type(&arg.intrinsic, &substitutions);
        [expected, contextual, intrinsic]
            .into_iter()
            .flatten()
            .map(|ty| project_runtime_type_with_vars(&ty, &self.principal_vars))
            .reduce(|left, right| choose_core_type(left, right, TypeChoice::VisiblePrincipal))
    }

    fn visible_principal_callee_result_type(
        &self,
        principal: &typed_ir::Type,
        substitutions: &[typed_ir::TypeSubstitution],
        arg_count: usize,
    ) -> Option<typed_ir::Type> {
        let substitutions = type_substitution_map(substitutions);
        let principal = substitute_type(principal, &substitutions);
        principal_result_after_args(&principal, arg_count)
            .cloned()
            .map(|ty| project_runtime_type_with_vars(&ty, &self.principal_vars))
    }

    fn visible_principal_callee_param_type(
        &self,
        principal: &typed_ir::Type,
        substitutions: &[typed_ir::TypeSubstitution],
    ) -> Option<typed_ir::Type> {
        let substitutions = visible_principal_arg_substitution_map(principal, substitutions, 0);
        let principal = substitute_type(principal, &substitutions);
        let typed_ir::Type::Fun { param, .. } = principal else {
            return None;
        };
        Some(project_runtime_type_with_vars(&param, &self.principal_vars))
    }

    fn visible_substituted_bounds_type(
        &self,
        bounds: &typed_ir::TypeBounds,
        substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    ) -> Option<typed_ir::Type> {
        let bounds = substitute_bounds(bounds.clone(), substitutions);
        self.visible_principal_bounds_type(&bounds)
    }

    pub(super) fn visible_handle_result_type(
        &self,
        arms: &[typed_ir::HandleArm],
    ) -> Option<typed_ir::Type> {
        arms.iter()
            .filter_map(|arm| self.visible_expr_type(&arm.body))
            .reduce(|left, right| choose_core_type(left, right, TypeChoice::VisiblePrincipal))
            .filter(|ty| !core_type_is_imprecise_runtime_slot(ty))
    }

    pub(super) fn visible_expr_type(&self, expr: &typed_ir::Expr) -> Option<typed_ir::Type> {
        match expr {
            typed_ir::Expr::Var(path) => self.env.get(path).map(diagnostic_core_type),
            typed_ir::Expr::PrimitiveOp(_) => None,
            typed_ir::Expr::Lit(lit) => Some(self.primitive_paths.lit_type(lit)),
            typed_ir::Expr::Apply {
                callee,
                arg,
                evidence,
            } => {
                let evidence_ty = evidence
                    .as_ref()
                    .and_then(|evidence| self.visible_apply_evidence_result_type(evidence));
                let structural_ty = self.visible_structural_apply_type(callee, arg);
                structural_ty
                    .clone()
                    .filter(|ty| {
                        is_concrete_visible_root_type(ty) && !contains_non_runtime_type(ty)
                    })
                    .or(evidence_ty)
                    .or(structural_ty)
            }
            typed_ir::Expr::Lambda { .. } => None,
            typed_ir::Expr::If {
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
            typed_ir::Expr::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.visible_expr_type(item))
                    .collect::<Option<Vec<_>>>()?;
                Some(typed_ir::Type::Tuple(items))
            }
            typed_ir::Expr::Record { .. }
            | typed_ir::Expr::Variant { .. }
            | typed_ir::Expr::Select { .. } => None,
            typed_ir::Expr::Match { arms, evidence, .. } => evidence
                .as_ref()
                .and_then(|evidence| self.visible_principal_bounds_type(&evidence.result))
                .or_else(|| {
                    arms.iter()
                        .filter_map(|arm| self.visible_expr_type(&arm.body))
                        .reduce(|left, right| {
                            choose_core_type(left, right, TypeChoice::VisiblePrincipal)
                        })
                }),
            typed_ir::Expr::Block { tail, .. } => tail
                .as_deref()
                .and_then(|tail| self.visible_expr_type(tail)),
            typed_ir::Expr::BindHere { expr } => self.visible_expr_type(expr),
            typed_ir::Expr::Handle { arms, evidence, .. } => evidence
                .as_ref()
                .and_then(|evidence| self.visible_principal_bounds_type(&evidence.result))
                .or_else(|| self.visible_handle_result_type(arms)),
            typed_ir::Expr::Coerce { expr, .. } | typed_ir::Expr::Pack { expr, .. } => {
                self.visible_expr_type(expr)
            }
        }
    }

    fn visible_structural_expr_type(&self, expr: &typed_ir::Expr) -> Option<typed_ir::Type> {
        match expr {
            typed_ir::Expr::Apply { callee, arg, .. } => {
                self.visible_structural_apply_type(callee, arg)
            }
            typed_ir::Expr::If {
                then_branch,
                else_branch,
                ..
            } => merge_visible_type_options(
                self.visible_structural_expr_type(then_branch),
                self.visible_structural_expr_type(else_branch),
            ),
            typed_ir::Expr::Match { arms, .. } => arms
                .iter()
                .filter_map(|arm| self.visible_structural_expr_type(&arm.body))
                .reduce(|left, right| choose_core_type(left, right, TypeChoice::VisiblePrincipal)),
            typed_ir::Expr::Handle { arms, .. } => arms
                .iter()
                .filter_map(|arm| self.visible_structural_expr_type(&arm.body))
                .reduce(|left, right| choose_core_type(left, right, TypeChoice::VisiblePrincipal))
                .filter(|ty| !core_type_is_imprecise_runtime_slot(ty)),
            typed_ir::Expr::Block { tail, .. } => tail
                .as_deref()
                .and_then(|tail| self.visible_structural_expr_type(tail)),
            typed_ir::Expr::BindHere { expr }
            | typed_ir::Expr::Coerce { expr, .. }
            | typed_ir::Expr::Pack { expr, .. } => self.visible_structural_expr_type(expr),
            _ => self.visible_expr_type(expr),
        }
    }

    fn visible_structural_apply_type(
        &self,
        callee: &typed_ir::Expr,
        arg: &typed_ir::Expr,
    ) -> Option<typed_ir::Type> {
        let callee_ty = self.visible_structural_expr_type(callee);
        let arg_ty = self.visible_structural_expr_type(arg);
        callee_ty
            .as_ref()
            .and_then(|callee_ty| visible_apply_result_type(callee_ty, arg_ty.as_ref()))
            .or(callee_ty)
            .or(arg_ty)
    }

    pub(super) fn runtime_symbol_kind(
        &self,
        path: &typed_ir::Path,
    ) -> Option<typed_ir::RuntimeSymbolKind> {
        self.runtime_symbols.get(path).copied()
    }

    pub(super) fn is_external_runtime_path(
        &self,
        path: &typed_ir::Path,
        locals: &HashMap<typed_ir::Path, RuntimeType>,
    ) -> bool {
        !locals.contains_key(path)
            && !self.env.contains_key(path)
            && (self.runtime_symbols.contains_key(path) || is_qualified_runtime_path(path))
    }

    pub(super) fn resolve_alias_path(&self, path: &typed_ir::Path) -> typed_ir::Path {
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

    fn resolve_handle_effect_operation_path(&self, path: &typed_ir::Path) -> typed_ir::Path {
        let resolved = self.resolve_alias_path(path);
        let Some(op) = resolved.segments.last() else {
            return path.clone();
        };
        if self.runtime_symbol_kind(&resolved) == Some(typed_ir::RuntimeSymbolKind::EffectOperation)
        {
            return resolved;
        }
        let hidden_op = typed_ir::Name(format!("{}#effect", op.0));
        let mut hidden_path = resolved.clone();
        if let Some(last) = hidden_path.segments.last_mut() {
            *last = hidden_op.clone();
        }
        if self.runtime_symbols.contains_key(&hidden_path) {
            return hidden_path;
        }
        let mut local_hidden_path = path.clone();
        if let Some(local_op) = path.segments.last() {
            if let Some(last) = local_hidden_path.segments.last_mut() {
                *last = typed_ir::Name(format!("{}#effect", local_op.0));
            }
            let resolved_hidden = self.resolve_alias_path(&local_hidden_path);
            if self.runtime_symbol_kind(&resolved_hidden)
                == Some(typed_ir::RuntimeSymbolKind::EffectOperation)
            {
                return resolved_hidden;
            }
        }
        resolved
    }

    pub(super) fn fresh_type_var(&mut self, prefix: &str) -> typed_ir::Type {
        let index = self.next_synthetic_type_var;
        self.next_synthetic_type_var += 1;
        typed_ir::Type::Var(typed_ir::TypeVar(format!("runtime_{prefix}_{index}")))
    }

    pub(super) fn fresh_effect_id_var(&mut self) -> EffectIdVar {
        let id = EffectIdVar(self.next_effect_id_var);
        self.next_effect_id_var += 1;
        id
    }

    pub(super) fn protect_function_body(&mut self, body: Expr, boundary_id: EffectIdVar) -> Expr {
        let body = add_id_to_created_thunks(body);
        if !contains_peek_add_id(&body) && !contains_effect_id_var(&body, boundary_id) {
            return body;
        }
        Expr::typed(
            ExprKind::LocalPushId {
                id: boundary_id,
                body: Box::new(body.clone()),
            },
            body.ty,
        )
    }

    fn protect_local_function_value(
        &mut self,
        path: typed_ir::Path,
        expr: Expr,
        boundary: &LocalParamBoundary,
        expected: Option<&RuntimeType>,
    ) -> Option<Expr> {
        if apply_callee_expected(expected) {
            return None;
        }
        if self
            .current_runtime_adapter_source
            .as_ref()
            .is_some_and(|source| source.apply_target.is_some())
        {
            return None;
        }
        let (callee, parts, wrap_in_thunk) = match &expr.ty {
            RuntimeType::Thunk { effect, value } => {
                let parts = function_parts(value).ok()?;
                let callee = Expr::typed(
                    ExprKind::BindHere {
                        expr: Box::new(Expr::typed(ExprKind::Var(path), expr.ty.clone())),
                    },
                    value.as_ref().clone(),
                );
                (callee, parts, Some(effect.clone()))
            }
            RuntimeType::Fun { .. } | RuntimeType::Unknown | RuntimeType::Core(_) => return None,
        };
        let arg_name = typed_ir::Name(format!("local_boundary_arg_{}", self.next_effect_id_var));
        let arg_path = typed_ir::Path::from_name(arg_name.clone());
        let arg = Expr::typed(ExprKind::Var(arg_path), parts.param.clone());
        if !function_return_can_cross_handler_boundary(&parts.ret) {
            return None;
        }
        let apply = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(callee),
                arg: Box::new(arg),
                evidence: None,
                instantiation: None,
            },
            parts.ret.clone(),
        );
        let thunk = match parts.ret {
            RuntimeType::Thunk { effect, value } => {
                let forced = Expr::typed(
                    ExprKind::BindHere {
                        expr: Box::new(apply),
                    },
                    value.as_ref().clone(),
                );
                Expr::typed(
                    ExprKind::Thunk {
                        effect: effect.clone(),
                        value: value.as_ref().clone(),
                        expr: Box::new(forced),
                    },
                    RuntimeType::thunk(effect.clone(), value.as_ref().clone()),
                )
            }
            value => Expr::typed(
                ExprKind::Thunk {
                    effect: typed_ir::Type::Unknown,
                    value: value.clone(),
                    expr: Box::new(apply),
                },
                RuntimeType::thunk(typed_ir::Type::Unknown, value),
            ),
        };
        let protected = add_boundary_id(
            thunk,
            EffectIdRef::Var(boundary.id),
            boundary.effect.clone(),
        );
        let lambda_ty = RuntimeType::fun(parts.param, protected.ty.clone());
        let lambda = Expr::typed(
            ExprKind::Lambda {
                param: arg_name,
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(protected.clone()),
            },
            lambda_ty.clone(),
        );
        match wrap_in_thunk {
            Some(effect) => Some(Expr::typed(
                ExprKind::Thunk {
                    effect: effect.clone(),
                    value: lambda_ty.clone(),
                    expr: Box::new(lambda),
                },
                RuntimeType::thunk(effect, lambda_ty),
            )),
            None => Some(lambda),
        }
    }

    pub(super) fn normalize_expected_hir_type(&self, ty: RuntimeType) -> RuntimeType {
        match ty {
            RuntimeType::Core(core @ typed_ir::Type::Fun { .. }) => {
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
        evidence: Option<&typed_ir::JoinEvidence>,
        expected: Option<&RuntimeType>,
        node: &'static str,
    ) -> RuntimeResult<typed_ir::Type> {
        let evidence_ty = evidence
            .and_then(|evidence| self.tir_evidence_runtime_type(&evidence.result))
            .filter(|ty| !matches!(ty, typed_ir::Type::Never));
        let concrete_evidence_ty = evidence_ty
            .clone()
            .filter(|ty| !core_type_is_imprecise_runtime_slot(ty))
            .filter(|ty| !contains_non_runtime_type(ty));
        let fallback_evidence_ty = evidence_ty.map(|ty| {
            if core_type_is_imprecise_runtime_slot(&ty) || contains_non_runtime_type(&ty) {
                typed_ir::Type::Unknown
            } else {
                ty
            }
        });
        concrete_evidence_ty
            .or_else(|| match expected.map(value_hir_type) {
                Some(RuntimeType::Core(ty)) => Some(ty.clone()),
                Some(RuntimeType::Thunk { value, .. }) => Some(runtime_core_type(value)),
                Some(RuntimeType::Unknown) => Some(typed_ir::Type::Unknown),
                Some(RuntimeType::Fun { .. }) | None => None,
            })
            .or(fallback_evidence_ty)
            .or_else(|| evidence.is_some().then_some(typed_ir::Type::Unknown))
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
        infer_hir_type_substitutions_prefer_non_never(
            &template_ty,
            &actual_callee_ty,
            &params,
            &mut substitutions,
        );
        if let Some(callee_hint) = callee_hint {
            infer_hir_type_substitutions_prefer_non_never(
                &template_ty,
                callee_hint,
                &params,
                &mut substitutions,
            );
        }
        infer_role_requirement_substitutions(
            &info.requirements,
            &self.graph.role_impls,
            &params,
            &mut substitutions,
        );
        close_type_substitution_map_recursively(&mut substitutions);
        let substituted_ty = substitute_hir_type(&template_ty, &substitutions);
        let value_params = hir_value_type_params(&info.ty)
            .into_iter()
            .collect::<BTreeSet<_>>();
        let args = info
            .type_params
            .iter()
            .filter_map(|var| {
                let ty = substitutions.get(var)?;
                if !value_params.contains(var) && matches!(ty, typed_ir::Type::Never) {
                    return None;
                }
                if matches!(ty, typed_ir::Type::Var(actual) if actual == var) {
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

    fn prepare_lowered_expr_for_expected(
        &mut self,
        expr: Expr,
        expected: &RuntimeType,
        source: TypeSource,
    ) -> RuntimeResult<Expr> {
        if hir_type_contains_unknown(expected) {
            return Ok(expr);
        }
        let expected_core = match value_hir_type(expected) {
            RuntimeType::Core(ty) => Some(ty.clone()),
            _ => None,
        };
        let actual_core = match value_hir_type(&expr.ty) {
            RuntimeType::Core(ty) => Some(ty.clone()),
            _ => None,
        };
        if let (Some(actual_core), Some(expected_core)) = (actual_core, expected_core) {
            if let Some(cast) = self.implicit_cast_method_path(&actual_core, &expected_core) {
                let (arg, _) = force_value_expr_profiled(expr, &mut self.runtime_adapter_profile);
                let callee_ty = self.env.get(&cast).cloned().unwrap_or_else(|| {
                    RuntimeType::fun(
                        RuntimeType::core(actual_core.clone()),
                        RuntimeType::core(expected_core.clone()),
                    )
                });
                let callee = Expr::typed(ExprKind::Var(cast), callee_ty);
                return Ok(Expr::typed(
                    ExprKind::Apply {
                        callee: Box::new(callee),
                        arg: Box::new(arg),
                        evidence: None,
                        instantiation: None,
                    },
                    expected.clone(),
                ));
            }
            if self
                .primitive_paths
                .needs_runtime_coercion(&expected_core, &actual_core)
            {
                let (expr, _) = force_value_expr_profiled(expr, &mut self.runtime_adapter_profile);
                return Ok(Expr::typed(
                    ExprKind::Coerce {
                        from: actual_core.clone(),
                        to: expected_core.clone(),
                        expr: Box::new(expr),
                    },
                    expected.clone(),
                ));
            }
        }
        prepare_expr_for_expected_with_adapter_source_profiled(
            expr,
            expected,
            source,
            &mut self.runtime_adapter_profile,
            self.current_runtime_adapter_source.clone(),
        )
    }

    fn implicit_cast_method_path(
        &self,
        actual: &typed_ir::Type,
        expected: &typed_ir::Type,
    ) -> Option<typed_ir::Path> {
        if implicit_cast_endpoint_is_open(actual) || implicit_cast_endpoint_is_open(expected) {
            return None;
        }
        if core_types_compatible(actual, expected) && core_types_compatible(expected, actual) {
            return None;
        }
        self.graph
            .role_impls
            .iter()
            .filter(|role_impl| {
                role_impl
                    .role
                    .segments
                    .last()
                    .is_some_and(|name| name.0 == "Cast")
            })
            .find_map(|role_impl| {
                let input = role_impl.inputs.first()?;
                let input = choose_bounds_type(input, BoundsChoice::ValidationEvidence)?;
                if !core_types_compatible(&input, actual) || !core_types_compatible(actual, &input)
                {
                    return None;
                }
                let target = role_impl
                    .associated_types
                    .iter()
                    .find(|associated| associated.name.0 == "to")?;
                let target = choose_bounds_type(&target.value, BoundsChoice::ValidationEvidence)?;
                if !core_types_compatible(&target, expected)
                    || !core_types_compatible(expected, &target)
                {
                    return None;
                }
                role_impl
                    .members
                    .iter()
                    .find(|member| member.name.0 == "cast")
                    .map(|member| member.value.clone())
            })
    }
}

/// Merge an `expected` runtime type (from apply context) with the operation's
/// exported `sig` runtime type. `expected` typically carries the effect row
/// from the calling context but may have `Unknown` in payload positions; `sig`
/// carries `Type::Var(..)` payloads but lacks effect info. Walk both in
/// parallel and prefer the more concrete leaf at each position.
fn merge_effect_op_runtime_type(expected: &RuntimeType, sig: &RuntimeType) -> RuntimeType {
    match (expected, sig) {
        (RuntimeType::Unknown, other) | (other, RuntimeType::Unknown) => other.clone(),
        (
            RuntimeType::Fun {
                param: a_p,
                ret: a_r,
            },
            RuntimeType::Fun {
                param: b_p,
                ret: b_r,
            },
        ) => RuntimeType::fun(
            merge_effect_op_runtime_type(a_p, b_p),
            merge_effect_op_runtime_type(a_r, b_r),
        ),
        (
            RuntimeType::Thunk {
                effect: a_e,
                value: a_v,
            },
            RuntimeType::Thunk {
                effect: b_e,
                value: b_v,
            },
        ) => RuntimeType::thunk(
            merge_effect_op_core(a_e, b_e),
            merge_effect_op_runtime_type(a_v, b_v),
        ),
        (RuntimeType::Thunk { effect, value }, sig) => RuntimeType::thunk(
            effect.clone(),
            merge_effect_op_runtime_type(value, sig),
        ),
        (expected, RuntimeType::Thunk { value, .. }) => {
            merge_effect_op_runtime_type(expected, value)
        }
        (RuntimeType::Core(a), RuntimeType::Core(b)) => {
            RuntimeType::core(merge_effect_op_core(a, b))
        }
        // Mixed Core/Fun: prefer the Fun form (it has richer structure).
        (RuntimeType::Fun { .. }, RuntimeType::Core(_)) => expected.clone(),
        (RuntimeType::Core(_), RuntimeType::Fun { .. }) => sig.clone(),
    }
}

fn merge_effect_op_core(expected: &typed_ir::Type, sig: &typed_ir::Type) -> typed_ir::Type {
    match (expected, sig) {
        (typed_ir::Type::Unknown, other) | (other, typed_ir::Type::Unknown) => other.clone(),
        (typed_ir::Type::Var(_), other) => other.clone(),
        (other, typed_ir::Type::Var(v)) if !matches!(other, typed_ir::Type::Unknown) => {
            // Sig's Var is the operation's payload type variable; if expected
            // already has something more concrete (not Unknown), keep it.
            if matches!(other, typed_ir::Type::Var(_)) {
                typed_ir::Type::Var(v.clone())
            } else {
                other.clone()
            }
        }
        (
            typed_ir::Type::Fun {
                param: a_p,
                param_effect: a_pe,
                ret_effect: a_re,
                ret: a_r,
            },
            typed_ir::Type::Fun {
                param: b_p,
                param_effect: b_pe,
                ret_effect: b_re,
                ret: b_r,
            },
        ) => typed_ir::Type::Fun {
            param: Box::new(merge_effect_op_core(a_p, b_p)),
            param_effect: Box::new(merge_effect_op_core(a_pe, b_pe)),
            ret_effect: Box::new(merge_effect_op_core(a_re, b_re)),
            ret: Box::new(merge_effect_op_core(a_r, b_r)),
        },
        _ => expected.clone(),
    }
}

fn project_runtime_hir_runtime_type_with_vars(
    ty: RuntimeType,
    allowed_vars: &BTreeSet<typed_ir::TypeVar>,
) -> RuntimeType {
    match ty {
        RuntimeType::Unknown => RuntimeType::Unknown,
        RuntimeType::Core(core) => project_runtime_hir_type_with_vars(&core, allowed_vars),
        RuntimeType::Fun { param, ret } => RuntimeType::fun(
            project_runtime_hir_runtime_type_with_vars(*param, allowed_vars),
            project_runtime_hir_runtime_type_with_vars(*ret, allowed_vars),
        ),
        RuntimeType::Thunk { effect, value } => RuntimeType::thunk(
            project_runtime_effect(&effect),
            project_runtime_hir_runtime_type_with_vars(*value, allowed_vars),
        ),
    }
}

fn implicit_cast_endpoint_is_open(ty: &typed_ir::Type) -> bool {
    // An open endpoint is not enough evidence for a semantic Cast. After
    // substitution it may normalize to identity, as in generic branch joins.
    core_type_is_imprecise_runtime_slot(ty)
        || core_type_has_vars(ty)
        || core_type_contains_unknown(ty)
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
            && matches!(effect, typed_ir::Type::Any)
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

fn canonicalize_handled_effects(
    handled: typed_ir::Type,
    body_effect_before: Option<&typed_ir::Type>,
) -> typed_ir::Type {
    let Some(body_effect_before) = body_effect_before else {
        return handled;
    };
    let body_paths = effect_paths(&project_runtime_effect(body_effect_before));
    replace_unqualified_effect_paths(handled, &body_paths)
}

fn thunk_handler_body_if_needed(
    body: Expr,
    body_effect_before: Option<&typed_ir::Type>,
    handled: &typed_ir::Type,
) -> Expr {
    if effect_paths(handled).is_empty() || matches!(body.ty, RuntimeType::Thunk { .. }) {
        return body;
    }
    let effect = match body_effect_before {
        Some(effect) => merge_effect_rows(project_runtime_effect(effect), handled.clone()),
        None => handled.clone(),
    };
    attach_expr_effect(body, project_runtime_effect(&effect))
}

fn replace_unqualified_effect_paths(
    effect: typed_ir::Type,
    canonical_paths: &[typed_ir::Path],
) -> typed_ir::Type {
    match effect {
        typed_ir::Type::Named { path, args }
            if path.segments.len() == 1
                && let Some(canonical) = unique_canonical_effect_suffix(&path, canonical_paths) =>
        {
            typed_ir::Type::Named {
                path: canonical,
                args,
            }
        }
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items
                .into_iter()
                .map(|item| replace_unqualified_effect_paths(item, canonical_paths))
                .collect(),
            tail: Box::new(replace_unqualified_effect_paths(*tail, canonical_paths)),
        },
        other => other,
    }
}

fn unique_canonical_effect_suffix(
    path: &typed_ir::Path,
    canonical_paths: &[typed_ir::Path],
) -> Option<typed_ir::Path> {
    let suffix = path.segments.last()?;
    let mut matches = canonical_paths
        .iter()
        .filter(|canonical| canonical.segments.last().is_some_and(|name| name == suffix))
        .cloned();
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
}

fn prepare_effect_operation_arg(
    arg: Expr,
    expected: &RuntimeType,
    source: TypeSource,
    profile: &mut RuntimeAdapterProfile,
    adapter_source: Option<RuntimeAdapterSource>,
) -> RuntimeResult<Expr> {
    match (expected, &arg.ty) {
        (
            RuntimeType::Unknown
            | RuntimeType::Core(
                typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_),
            ),
            RuntimeType::Thunk { .. },
        ) => Ok(force_value_expr_profiled(arg, profile).0),
        _ => prepare_expr_for_expected_with_adapter_source_profiled(
            arg,
            expected,
            source,
            profile,
            adapter_source,
        ),
    }
}

fn attach_effect_to_hir_type(ty: RuntimeType, effect: typed_ir::Type) -> RuntimeType {
    let effect = project_runtime_effect(&effect);
    if !should_thunk_effect(&effect) {
        return ty;
    }
    match ty {
        RuntimeType::Thunk {
            effect: existing,
            value,
        } => RuntimeType::thunk(
            project_runtime_effect(&merge_effect_rows(effect, existing)),
            *value,
        ),
        value => RuntimeType::thunk(effect, value),
    }
}

fn apply_evidence_ret_effect(evidence: Option<&typed_ir::ApplyEvidence>) -> Option<typed_ir::Type> {
    let evidence = evidence?;
    evidence
        .expected_callee
        .as_ref()
        .and_then(bounds_ret_effect)
        .or_else(|| bounds_ret_effect(&evidence.callee))
        .map(|effect| project_runtime_effect(&effect))
        .filter(|effect| !effect_is_empty(effect))
}

fn bounds_ret_effect(bounds: &typed_ir::TypeBounds) -> Option<typed_ir::Type> {
    bounds
        .upper
        .as_deref()
        .and_then(type_ret_effect)
        .or_else(|| bounds.lower.as_deref().and_then(type_ret_effect))
}

fn type_ret_effect(ty: &typed_ir::Type) -> Option<typed_ir::Type> {
    match ty {
        typed_ir::Type::Fun { ret_effect, .. } => Some((**ret_effect).clone()),
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            items.iter().find_map(type_ret_effect)
        }
        typed_ir::Type::Recursive { body, .. } => type_ret_effect(body),
        _ => None,
    }
}

fn runtime_type_returns_function(ty: &RuntimeType) -> bool {
    matches!(value_hir_type(ty), RuntimeType::Fun { .. })
}

fn local_callback_boundary_needs_wildcard_effect(ty: &RuntimeType) -> bool {
    runtime_type_is_imprecise_runtime_slot(ty)
}

fn choose_final_apply_param(
    final_param: &RuntimeType,
    selected_arg_hint: Option<&RuntimeType>,
    callee_is_local: bool,
) -> RuntimeType {
    match (selected_arg_hint, final_param) {
        (Some(hint @ RuntimeType::Thunk { .. }), _) if callee_is_local => hint.clone(),
        (Some(hint), param) if should_use_variant_arg_hint(param, hint) => hint.clone(),
        (Some(hint), param) if runtime_type_is_imprecise_runtime_slot(param) => hint.clone(),
        _ => final_param.clone(),
    }
}

fn should_use_variant_arg_hint(param: &RuntimeType, hint: &RuntimeType) -> bool {
    let RuntimeType::Core(typed_ir::Type::Variant(hint_variant)) = hint else {
        return false;
    };
    if !expected_arg_evidence_runtime_usable(hint) {
        return false;
    }
    match param {
        RuntimeType::Core(typed_ir::Type::Variant(param_variant)) => {
            !variant_hint_drops_cases(param_variant, hint_variant)
        }
        RuntimeType::Core(typed_ir::Type::Inter(items)) => items.iter().any(|item| {
            matches!(item, typed_ir::Type::Variant(_))
                && (core_types_compatible(item, &diagnostic_core_type(hint))
                    || core_types_compatible(&diagnostic_core_type(hint), item))
        }),
        _ => false,
    }
}

fn should_use_polymorphic_arg_hint(param: &RuntimeType, hint: &RuntimeType) -> bool {
    runtime_type_is_imprecise_runtime_slot(param) || should_use_variant_arg_hint(param, hint)
}

fn variant_hint_drops_cases(param: &typed_ir::VariantType, hint: &typed_ir::VariantType) -> bool {
    hint.cases.len() < param.cases.len()
        && hint
            .cases
            .iter()
            .all(|hint_case| param.cases.iter().any(|case| case.name == hint_case.name))
}

fn is_constructor_variant_expr(expr: &typed_ir::Expr) -> bool {
    matches!(
        expr,
        typed_ir::Expr::Variant {
            source: typed_ir::VariantExprSource::Constructor,
            ..
        }
    )
}

fn effect_operation_payload_param_hint(
    arg_ty: &RuntimeType,
    actual_arg_ty: &RuntimeType,
) -> RuntimeType {
    let candidate = if runtime_type_is_imprecise_runtime_slot(arg_ty) {
        actual_arg_ty
    } else {
        arg_ty
    };
    match candidate {
        RuntimeType::Thunk { value, .. } => value.as_ref().clone(),
        candidate => candidate.clone(),
    }
}

fn type_substitution_map(
    substitutions: &[typed_ir::TypeSubstitution],
) -> BTreeMap<typed_ir::TypeVar, typed_ir::Type> {
    substitutions
        .iter()
        .map(|substitution| (substitution.var.clone(), substitution.ty.clone()))
        .collect()
}

fn visible_principal_arg_substitution_map(
    principal: &typed_ir::Type,
    substitutions: &[typed_ir::TypeSubstitution],
    index: usize,
) -> BTreeMap<typed_ir::TypeVar, typed_ir::Type> {
    let mut substitutions = type_substitution_map(substitutions);
    if index == 0
        && let Some(var) = direct_principal_param_var(principal)
        && substitutions
            .get(&var)
            .is_some_and(is_runtime_irrelevant_value_substitution)
    {
        substitutions.remove(&var);
    }
    substitutions
}

fn widened_apply_arg_evidence_accepts_actual(
    expected_arg: Option<&RuntimeType>,
    evidence_arg: Option<&RuntimeType>,
    actual_arg: &RuntimeType,
) -> bool {
    [expected_arg, evidence_arg]
        .into_iter()
        .flatten()
        .any(|hint| {
            !runtime_type_is_imprecise_runtime_slot(hint)
                && !hir_type_contains_unknown(hint)
                && hir_type_compatible(hint, actual_arg)
        })
}

fn runtime_type_can_be_pushed_as_lowering_expected(ty: &RuntimeType) -> bool {
    !runtime_type_contains_value_choice(ty)
}

fn should_refine_local_from_argument_expected(
    stored: &RuntimeType,
    candidate: &RuntimeType,
    source: TypeSource,
) -> bool {
    matches!(source, TypeSource::ApplyArgumentSourceEdge)
        && runtime_type_is_imprecise_runtime_slot(stored)
        && expected_arg_evidence_runtime_usable(candidate)
        && (hir_type_compatible(candidate, stored) || hir_type_compatible(stored, candidate))
}

fn runtime_type_contains_value_choice(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => false,
        RuntimeType::Core(ty) => core_type_contains_value_choice(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_type_contains_value_choice(param) || runtime_type_contains_value_choice(ret)
        }
        RuntimeType::Thunk { value, .. } => runtime_type_contains_value_choice(value),
    }
}

fn core_type_contains_value_choice(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Union(_) | typed_ir::Type::Inter(_) => true,
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_contains_value_choice),
        typed_ir::Type::Fun {
            param,
            param_effect: _,
            ret_effect: _,
            ret,
        } => core_type_contains_value_choice(param) || core_type_contains_value_choice(ret),
        typed_ir::Type::Tuple(items) => items.iter().any(core_type_contains_value_choice),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_type_contains_value_choice(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        core_type_contains_value_choice(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(core_type_contains_value_choice))
                || variant
                    .tail
                    .as_deref()
                    .is_some_and(core_type_contains_value_choice)
        }
        typed_ir::Type::Row { .. } => false,
        typed_ir::Type::Recursive { body, .. } => core_type_contains_value_choice(body),
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Var(_) => false,
    }
}

fn type_arg_contains_value_choice(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => core_type_contains_value_choice(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_deref()
                .is_some_and(core_type_contains_value_choice)
                || bounds
                    .upper
                    .as_deref()
                    .is_some_and(core_type_contains_value_choice)
        }
    }
}

fn direct_principal_param_var(principal: &typed_ir::Type) -> Option<typed_ir::TypeVar> {
    let typed_ir::Type::Fun { param, .. } = principal else {
        return None;
    };
    match param.as_ref() {
        typed_ir::Type::Var(var) => Some(var.clone()),
        _ => None,
    }
}

fn is_runtime_irrelevant_value_substitution(ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Never)
        || matches!(ty, typed_ir::Type::Tuple(items) if items.is_empty())
}

fn runtime_type_is_irrelevant_unit_value(ty: &RuntimeType) -> bool {
    matches!(ty, RuntimeType::Core(typed_ir::Type::Tuple(items)) if items.is_empty())
}

fn hir_type_contains_unknown(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => true,
        RuntimeType::Core(ty) => core_type_contains_unknown(ty),
        RuntimeType::Fun { param, ret } => {
            hir_type_contains_unknown(param) || hir_type_contains_unknown(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            core_type_contains_unknown(effect) || hir_type_contains_unknown(value)
        }
    }
}

fn core_type_contains_unknown(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown => true,
        typed_ir::Type::Never | typed_ir::Type::Any | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_contains_unknown),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_contains_unknown(param)
                || core_type_contains_unknown(param_effect)
                || core_type_contains_unknown(ret_effect)
                || core_type_contains_unknown(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(core_type_contains_unknown),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_type_contains_unknown(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        core_type_contains_unknown(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(core_type_contains_unknown))
                || variant
                    .tail
                    .as_deref()
                    .is_some_and(core_type_contains_unknown)
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(core_type_contains_unknown) || core_type_contains_unknown(tail)
        }
        typed_ir::Type::Recursive { body, .. } => core_type_contains_unknown(body),
    }
}

fn type_arg_contains_unknown(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => core_type_contains_unknown(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_deref()
                .is_some_and(core_type_contains_unknown)
                || bounds
                    .upper
                    .as_deref()
                    .is_some_and(core_type_contains_unknown)
        }
    }
}

fn principal_result_after_args(
    principal: &typed_ir::Type,
    arg_count: usize,
) -> Option<&typed_ir::Type> {
    let mut current = principal;
    for _ in 0..arg_count {
        current = match current {
            typed_ir::Type::Fun { ret, .. } => ret,
            typed_ir::Type::Recursive { body, .. } => body,
            _ => return None,
        };
    }
    Some(current)
}

fn core_apply_head_target(expr: &typed_ir::Expr) -> Option<typed_ir::Path> {
    match expr {
        typed_ir::Expr::Var(path) => Some(path.clone()),
        typed_ir::Expr::Apply { callee, .. } => core_apply_head_target(callee),
        _ => None,
    }
}

fn core_apply_head_label(expr: &typed_ir::Expr) -> Option<RuntimeCalleeLabel> {
    match expr {
        typed_ir::Expr::Var(path) => Some(RuntimeCalleeLabel::Path(path.clone())),
        typed_ir::Expr::PrimitiveOp(op) => Some(RuntimeCalleeLabel::Primitive(*op)),
        typed_ir::Expr::Apply { callee, .. } => core_apply_head_label(callee),
        _ => None,
    }
}

fn apply_type_mismatch_context(
    callee: Option<RuntimeCalleeLabel>,
    evidence: Option<&typed_ir::ApplyEvidence>,
    phase: TypeMismatchPhase,
) -> TypeMismatchContext {
    TypeMismatchContext {
        callee,
        phase,
        callee_source_edge: evidence.and_then(|evidence| evidence.callee_source_edge),
        arg_source_edge: evidence.and_then(|evidence| evidence.arg_source_edge),
    }
}

fn type_mismatch_context_for_adapter_source(source: &RuntimeAdapterSource) -> TypeMismatchContext {
    TypeMismatchContext {
        callee: source.apply_target.clone().map(RuntimeCalleeLabel::Path),
        phase: type_mismatch_phase_for_runtime_apply_phase(source.phase),
        callee_source_edge: source.callee_source_edge,
        arg_source_edge: source.arg_source_edge,
    }
}

fn type_mismatch_phase_for_runtime_apply_phase(
    phase: RuntimeApplyAdapterPhase,
) -> TypeMismatchPhase {
    match phase {
        RuntimeApplyAdapterPhase::LowerCallee => TypeMismatchPhase::ApplyCallee,
        RuntimeApplyAdapterPhase::LowerArgument
        | RuntimeApplyAdapterPhase::PrepareFinalArgument
        | RuntimeApplyAdapterPhase::PrepareEffectOperationArgument => {
            TypeMismatchPhase::ApplyArgument
        }
    }
}

fn restore_local_param_boundary(
    boundaries: &mut HashMap<typed_ir::Path, LocalParamBoundary>,
    local: typed_ir::Path,
    previous: Option<LocalParamBoundary>,
) {
    match previous {
        Some(previous) => {
            boundaries.insert(local, previous);
        }
        None => {
            boundaries.remove(&local);
        }
    }
}

fn apply_callee_expected(expected: Option<&RuntimeType>) -> bool {
    match expected {
        Some(RuntimeType::Fun { .. } | RuntimeType::Core(typed_ir::Type::Fun { .. })) => true,
        Some(RuntimeType::Thunk { value, .. }) => apply_callee_expected(Some(value)),
        Some(RuntimeType::Unknown | RuntimeType::Core(_)) | None => false,
    }
}

fn handle_body_is_imprecise_local_value(
    body: &typed_ir::Expr,
    locals: &HashMap<typed_ir::Path, RuntimeType>,
) -> bool {
    match body {
        typed_ir::Expr::Var(path) => locals
            .get(path)
            .is_none_or(runtime_type_is_imprecise_runtime_slot),
        typed_ir::Expr::BindHere { expr } | typed_ir::Expr::Coerce { expr, .. } => {
            handle_body_is_imprecise_local_value(expr, locals)
        }
        _ => false,
    }
}

fn function_return_can_cross_handler_boundary(ret: &RuntimeType) -> bool {
    match ret {
        RuntimeType::Thunk { effect, value } => {
            should_thunk_effect(effect) || function_return_can_cross_handler_boundary(value)
        }
        RuntimeType::Fun { ret, .. } => function_return_can_cross_handler_boundary(ret),
        RuntimeType::Core(typed_ir::Type::Fun {
            ret, ret_effect, ..
        }) => {
            should_thunk_effect(ret_effect)
                || function_return_can_cross_handler_boundary(&RuntimeType::core(
                    ret.as_ref().clone(),
                ))
        }
        RuntimeType::Unknown | RuntimeType::Core(_) => false,
    }
}

fn type_bounds_closed(bounds: &typed_ir::TypeBounds) -> bool {
    (bounds.lower.is_some() || bounds.upper.is_some())
        && bounds
            .lower
            .as_deref()
            .is_none_or(|ty| !core_type_has_vars(ty))
        && bounds
            .upper
            .as_deref()
            .is_none_or(|ty| !core_type_has_vars(ty))
}

fn type_bounds_informative(bounds: &typed_ir::TypeBounds) -> bool {
    bounds.lower.as_deref().is_some_and(type_informative)
        || bounds.upper.as_deref().is_some_and(type_informative)
}

fn type_informative(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Named { .. }
        | typed_ir::Type::Fun { .. }
        | typed_ir::Type::Tuple(_)
        | typed_ir::Type::Record(_)
        | typed_ir::Type::Variant(_) => true,
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(type_informative) || type_informative(tail)
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            items.iter().any(type_informative)
        }
        typed_ir::Type::Recursive { body, .. } => type_informative(body),
    }
}

fn can_push_expected_arg_through(expr: &typed_ir::Expr) -> bool {
    matches!(
        expr,
        typed_ir::Expr::Lambda { .. }
            | typed_ir::Expr::Tuple(_)
            | typed_ir::Expr::Record { .. }
            | typed_ir::Expr::Variant { .. }
            | typed_ir::Expr::Block { .. }
    )
}

fn can_push_expected_arg_evidence_through(expr: &typed_ir::Expr) -> bool {
    matches!(expr, typed_ir::Expr::Var(_)) || can_push_expected_arg_through(expr)
}
