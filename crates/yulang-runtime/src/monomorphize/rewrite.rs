use super::*;

pub(super) struct Monomorphizer {
    pub(super) originals: HashMap<core_ir::Path, Binding>,
    pub(super) cache: HashMap<String, core_ir::Path>,
    pub(super) failed_specializations: HashSet<String>,
    pub(super) specialized_types: HashMap<core_ir::Path, RuntimeType>,
    pub(super) specialized: Vec<Binding>,
    pub(super) locals: HashMap<core_ir::Path, RuntimeType>,
    pub(super) next_specialization: usize,
}

impl Monomorphizer {
    pub(super) fn new(module: &Module) -> Self {
        let next_specialization = module
            .bindings
            .iter()
            .filter_map(|binding| specialization_suffix(&binding.name))
            .max()
            .map(|suffix| suffix + 1)
            .unwrap_or(0);
        Self {
            originals: module
                .bindings
                .iter()
                .map(|binding| {
                    (
                        binding.name.clone(),
                        binding_with_complete_type_params(binding.clone()),
                    )
                })
                .collect(),
            cache: HashMap::new(),
            failed_specializations: HashSet::new(),
            specialized_types: HashMap::new(),
            specialized: Vec::new(),
            locals: HashMap::new(),
            next_specialization,
        }
    }

    pub(super) fn rewrite_exprs(&mut self, exprs: Vec<Expr>) -> Vec<Expr> {
        exprs
            .into_iter()
            .map(|expr| {
                let expected = expr.ty.clone();
                self.rewrite_expr_with_expected(expr, Some(&expected))
            })
            .collect()
    }

    pub(super) fn rewrite_expr(&mut self, expr: Expr) -> Expr {
        self.rewrite_expr_with_expected(expr, None)
    }

    pub(super) fn rewrite_expr_with_expected(
        &mut self,
        expr: Expr,
        expected: Option<&RuntimeType>,
    ) -> Expr {
        let mut ty = expr.ty;
        let original_ty = ty.clone();
        if let Some(expected) = expected.filter(|expected| !hir_type_is_hole(expected)) {
            if hir_type_has_vars(&ty) || hir_type_compatible(expected, &ty) {
                ty = expected.clone();
            }
        }
        let kind = match expr.kind {
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            } => {
                let evidence_result_ty = evidence
                    .as_ref()
                    .and_then(|evidence| bounds_hir_type(&evidence.result));
                let evidence_callee_ty = evidence.as_ref().and_then(|evidence| {
                    choose_hir_bounds_type(&evidence.callee, BoundsChoice::ValidationEvidence)
                });
                let evidence_arg_ty = evidence
                    .as_ref()
                    .and_then(|evidence| bounds_hir_type(&evidence.arg));
                let fallback_result_ty =
                    rewrite_child_expected(evidence_result_ty.clone(), expected, &ty);
                let mut callee =
                    self.rewrite_expr_with_expected(*callee, evidence_callee_ty.as_ref());
                let mut instantiation = instantiation;
                let param_expected = self.callee_param_expected(&callee);
                let concrete_param_expected = param_expected
                    .as_ref()
                    .filter(|param| !hir_type_has_vars(param));
                let concrete_evidence_arg = evidence_arg_ty
                    .as_ref()
                    .filter(|arg| !hir_type_has_vars(arg));
                let arg_expected = concrete_param_expected.or(concrete_evidence_arg);
                let mut arg = match arg_expected {
                    Some(param) => self.rewrite_expr_with_expected(*arg, Some(param)),
                    None => self.rewrite_expr(*arg),
                };
                let call_result_ty = match apply_result_type(&callee.ty) {
                    Some(ret) => apply_result_expected(ret, fallback_result_ty),
                    None => fallback_result_ty,
                };
                ty = call_result_ty.clone();
                if let Some(ret) = specialize_constructor_apply(&mut callee, &arg, &call_result_ty)
                {
                    ty = ret.clone();
                    self.specialize_callee_from_call(&mut callee, &arg.ty, &ret);
                    instantiation = None;
                } else if let Some(ret) = specialize_primitive_apply(&mut callee, &arg) {
                    ty = ret;
                    instantiation = None;
                } else if self.specialize_callee_from_call(&mut callee, &arg.ty, &call_result_ty) {
                    instantiation = None;
                } else if let Some(current_instantiation) = instantiation.take() {
                    if let Some(target) = self.specialize(&current_instantiation) {
                        self.replace_instantiated_head(
                            &mut callee,
                            &current_instantiation.target,
                            &target,
                        );
                    } else {
                        instantiation = Some(current_instantiation);
                    }
                }
                if let Some(ret) = apply_result_type(&callee.ty) {
                    ty = apply_result_expected(ret, call_result_ty);
                }
                if let Some(param) = function_param_type(&callee.ty) {
                    arg = force_arg_for_param(arg, &param);
                }
                ExprKind::Apply {
                    callee: Box::new(callee),
                    arg: Box::new(arg),
                    evidence,
                    instantiation,
                }
            }
            ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body,
            } => {
                if let Some(expected) = expected.filter(|expected| is_function_like(expected)) {
                    ty = expected.clone();
                }
                let body_expected = match &ty {
                    RuntimeType::Fun { ret, .. } => Some(ret.as_ref()),
                    _ => None,
                };
                let param_ty = function_param_type(&ty);
                let local = core_ir::Path::from_name(param.clone());
                let previous = param_ty
                    .clone()
                    .map(|param_ty| self.locals.insert(local.clone(), param_ty));
                let body = self.rewrite_expr_with_expected(*body, body_expected);
                restore_local_type(&mut self.locals, local, previous);
                if let Some(refined) = refine_lambda_type_from_body(&ty, &body) {
                    ty = refined;
                }
                ExprKind::Lambda {
                    param,
                    param_effect_annotation,
                    param_function_allowed_effects,
                    body: Box::new(body),
                }
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                mut evidence,
            } => {
                let evidence_expected = evidence
                    .as_ref()
                    .map(|evidence| RuntimeType::core(evidence.result.clone()));
                let branch_expected = rewrite_child_expected(evidence_expected, expected, &ty);
                ty = branch_expected.clone();
                if let Some(evidence) = &mut evidence {
                    evidence.result = core_value_type(&branch_expected);
                }
                ExprKind::If {
                    cond: Box::new(self.rewrite_expr(*cond)),
                    then_branch: Box::new(
                        self.rewrite_expr_with_expected(*then_branch, Some(&branch_expected)),
                    ),
                    else_branch: Box::new(
                        self.rewrite_expr_with_expected(*else_branch, Some(&branch_expected)),
                    ),
                    evidence,
                }
            }
            ExprKind::Tuple(items) => ExprKind::Tuple(self.rewrite_exprs(items)),
            ExprKind::Record { fields, spread } => ExprKind::Record {
                fields: fields
                    .into_iter()
                    .map(|field| RecordExprField {
                        name: field.name,
                        value: self.rewrite_expr(field.value),
                    })
                    .collect(),
                spread: spread.map(|spread| match spread {
                    RecordSpreadExpr::Head(expr) => {
                        RecordSpreadExpr::Head(Box::new(self.rewrite_expr(*expr)))
                    }
                    RecordSpreadExpr::Tail(expr) => {
                        RecordSpreadExpr::Tail(Box::new(self.rewrite_expr(*expr)))
                    }
                }),
            },
            ExprKind::Variant { tag, value } => {
                if let Some(expected) = expected.filter(|expected| !hir_type_is_hole(expected)) {
                    ty = expected.clone();
                }
                let value_expected = variant_payload_expected(&tag, &ty);
                ExprKind::Variant {
                    tag,
                    value: value.map(|value| {
                        Box::new(self.rewrite_expr_with_expected(*value, value_expected.as_ref()))
                    }),
                }
            }
            ExprKind::Select { base, field } => ExprKind::Select {
                base: Box::new(self.rewrite_expr(*base)),
                field,
            },
            ExprKind::Match {
                scrutinee,
                arms,
                mut evidence,
            } => {
                let body_expected = rewrite_child_expected(
                    Some(RuntimeType::core(evidence.result.clone())),
                    expected,
                    &ty,
                );
                ty = body_expected.clone();
                evidence.result = core_value_type(&body_expected);
                let scrutinee = self.rewrite_expr(*scrutinee);
                ExprKind::Match {
                    scrutinee: Box::new(scrutinee),
                    arms: arms
                        .into_iter()
                        .map(|arm| {
                            let bindings = pattern_bindings(&arm.pattern);
                            let previous = push_local_types(&mut self.locals, &bindings);
                            let guard = arm.guard.map(|guard| self.rewrite_expr(guard));
                            let body =
                                self.rewrite_expr_with_expected(arm.body, Some(&body_expected));
                            pop_local_types(&mut self.locals, previous);
                            MatchArm {
                                pattern: arm.pattern,
                                guard,
                                body,
                            }
                        })
                        .collect(),
                    evidence,
                }
            }
            ExprKind::Block { stmts, tail } => {
                if let Some(expected) = expected.filter(|expected| !hir_type_is_hole(expected)) {
                    ty = expected.clone();
                }
                let saved_locals = self.locals.clone();
                let original_stmts = stmts;
                for stmt in &original_stmts {
                    push_stmt_locals(&mut self.locals, stmt);
                }
                let mut stmts = Vec::with_capacity(original_stmts.len());
                for stmt in original_stmts {
                    let stmt = self.rewrite_stmt(stmt);
                    push_stmt_locals(&mut self.locals, &stmt);
                    stmts.push(stmt);
                }
                let rewritten_tail =
                    tail.map(|tail| Box::new(self.rewrite_expr_with_expected(*tail, Some(&ty))));
                if let Some(tail) = rewritten_tail.as_deref() {
                    ty = refine_block_type_from_tail(ty, &tail.ty);
                }
                self.locals = saved_locals;
                ExprKind::Block {
                    stmts: remove_dead_lambda_lets(stmts, rewritten_tail.as_deref()),
                    tail: rewritten_tail,
                }
            }
            ExprKind::Handle {
                body,
                arms,
                mut evidence,
                handler,
            } => {
                if matches!(original_ty, RuntimeType::Core(_)) {
                    ty = original_ty.clone();
                }
                let body_expected = rewrite_child_expected(
                    Some(RuntimeType::core(evidence.result.clone())),
                    expected,
                    &ty,
                );
                ty = body_expected.clone();
                evidence.result = core_value_type(&body_expected);
                ExprKind::Handle {
                    body: Box::new(self.rewrite_expr(*body)),
                    arms: arms
                        .into_iter()
                        .map(|arm| {
                            let mut bindings = pattern_bindings(&arm.payload);
                            if let Some(resume) = &arm.resume {
                                bindings.push((
                                    core_ir::Path::from_name(resume.name.clone()),
                                    resume.ty.clone(),
                                ));
                            }
                            let previous = push_local_types(&mut self.locals, &bindings);
                            let guard = arm.guard.map(|guard| self.rewrite_expr(guard));
                            let body =
                                self.rewrite_expr_with_expected(arm.body, Some(&body_expected));
                            pop_local_types(&mut self.locals, previous);
                            HandleArm {
                                effect: arm.effect,
                                payload: arm.payload,
                                resume: arm.resume.map(|resume| ResumeBinding {
                                    name: resume.name,
                                    ty: resume.ty,
                                }),
                                guard,
                                body,
                            }
                        })
                        .collect(),
                    evidence,
                    handler,
                }
            }
            ExprKind::BindHere { expr } => {
                let expected_value = expected
                    .filter(|expected| !hir_type_is_hole(expected))
                    .filter(|expected| !matches!(expected, RuntimeType::Thunk { .. }))
                    .cloned();
                let inner_expected = bind_here_inner_expected(&expr.ty, expected_value.as_ref());
                let mut inner = self.rewrite_expr_with_expected(*expr, inner_expected.as_ref());
                if let (Some(expected_value), RuntimeType::Thunk { effect, .. }) =
                    (&expected_value, &inner.ty)
                {
                    let expected_inner = RuntimeType::thunk(effect.clone(), expected_value.clone());
                    if !hir_type_compatible(&inner.ty, &expected_inner) {
                        inner = self.rewrite_expr_with_expected(inner, Some(&expected_inner));
                    }
                }
                if let RuntimeType::Thunk { value, .. } = &inner.ty {
                    ty = value.as_ref().clone();
                }
                ExprKind::BindHere {
                    expr: Box::new(inner),
                }
            }
            ExprKind::Thunk {
                effect,
                value,
                expr,
            } => {
                let (effect, expected_value) = match expected {
                    Some(RuntimeType::Thunk { effect, value }) => {
                        (effect.clone(), value.as_ref().clone())
                    }
                    _ => (effect, value.clone()),
                };
                let rewritten = self.rewrite_expr_with_expected(*expr, Some(&expected_value));
                let (effect, body_ty, rewritten) = flatten_nested_thunk_body(effect, rewritten);
                let value = refine_thunk_value_from_body(expected_value, &body_ty);
                let effect = specialize_sub_effect_payload_from_value(effect, &value);
                ty = RuntimeType::thunk(effect.clone(), value.clone());
                ExprKind::Thunk {
                    effect,
                    value,
                    expr: Box::new(rewritten),
                }
            }
            ExprKind::LocalPushId { id, body } => {
                let body = self.rewrite_expr(*body);
                ty = body.ty.clone();
                ExprKind::LocalPushId {
                    id,
                    body: Box::new(body),
                }
            }
            ExprKind::PeekId => ExprKind::PeekId,
            ExprKind::FindId { id } => ExprKind::FindId { id },
            ExprKind::AddId { id, allowed, thunk } => {
                let thunk_expected = expected
                    .filter(|expected| matches!(expected, RuntimeType::Thunk { .. }))
                    .cloned();
                let thunk = self.rewrite_expr_with_expected(*thunk, thunk_expected.as_ref());
                let allowed = match &thunk.ty {
                    RuntimeType::Thunk { value, .. } => {
                        specialize_sub_effect_payload_from_value(allowed, value)
                    }
                    _ => allowed,
                };
                ty = thunk.ty.clone();
                ExprKind::AddId {
                    id,
                    allowed,
                    thunk: Box::new(thunk),
                }
            }
            ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
                from,
                to,
                expr: Box::new(self.rewrite_expr(*expr)),
            },
            ExprKind::Pack { var, expr } => ExprKind::Pack {
                var,
                expr: Box::new(self.rewrite_expr(*expr)),
            },
            ExprKind::Var(path) => {
                let is_local = if let Some(local_ty) = self.locals.get(&path).cloned() {
                    ty = refine_local_occurrence_type(local_ty, expected);
                    true
                } else {
                    false
                };
                if !is_local && !matches!(ty, RuntimeType::Core(core_ir::Type::Never)) {
                    if let Some(expected) = expected.filter(|expected| !hir_type_is_hole(expected))
                    {
                        let expected_constructor =
                            is_nullary_constructor_path_for_type(&path, expected);
                        if !self.originals.contains_key(&path)
                            || self
                                .originals
                                .get(&path)
                                .is_some_and(|binding| !binding.type_params.is_empty())
                            || expected_constructor
                        {
                            ty = expected.clone();
                        }
                    }
                }
                let mut path = path;
                if let Some(specialized) = self.specialize_path_for_type(path.clone(), &ty) {
                    path = specialized;
                }
                let expected_constructor = expected
                    .filter(|expected| !hir_type_is_hole(expected))
                    .is_some_and(|expected| is_nullary_constructor_path_for_type(&path, expected));
                if !expected_constructor && let Some(binding_ty) = self.concrete_binding_type(&path)
                {
                    ty = binding_ty;
                }
                ExprKind::Var(path)
            }
            ExprKind::EffectOp(path) => {
                let mut resolved = self.resolve_role_method_var(path.clone(), &ty);
                if resolved == path {
                    ExprKind::EffectOp(path)
                } else {
                    if let Some(specialized) = self.specialize_path_for_type(resolved.clone(), &ty)
                    {
                        resolved = specialized;
                    }
                    if let Some(binding_ty) = self.concrete_binding_type(&resolved) {
                        ty = binding_ty;
                    }
                    ExprKind::Var(resolved)
                }
            }
            ExprKind::PrimitiveOp(_) | ExprKind::Lit(_) => expr.kind,
        };
        simplify_rewritten_expr(Expr { ty, kind })
    }

    pub(super) fn rewrite_stmt(&mut self, stmt: Stmt) -> Stmt {
        match stmt {
            Stmt::Let { pattern, value } => {
                let expected = pattern_type(&pattern);
                Stmt::Let {
                    pattern,
                    value: self.rewrite_expr_with_expected(value, Some(&expected)),
                }
            }
            Stmt::Expr(expr) => Stmt::Expr(self.rewrite_expr(expr)),
            Stmt::Module { def, body } => Stmt::Module {
                def,
                body: self.rewrite_expr(body),
            },
        }
    }
}
