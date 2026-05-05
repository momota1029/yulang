use super::*;
use crate::types::{
    core_type_contains_unknown, core_type_is_imprecise_runtime_slot, effect_compatible,
    effect_paths, effect_paths_match, normalize_principal_elaboration_plan_with_requirements,
    project_closed_substitutions_from_type, project_runtime_type_with_vars, runtime_core_type,
    substitute_bounds, type_compatible,
};

pub(super) fn principal_unify_module_profiled(
    module: Module,
) -> (Module, SubstitutionSpecializeProfile) {
    PrincipalUnifier::new(module).run()
}

struct PrincipalUnifier {
    module: Module,
    bindings_by_path: HashMap<core_ir::Path, Binding>,
    generic_bindings: HashMap<core_ir::Path, Binding>,
    role_impls: HashMap<core_ir::Name, Vec<Binding>>,
    specializations: HashMap<String, core_ir::Path>,
    root_specializations: HashMap<core_ir::Path, Vec<core_ir::Path>>,
    role_method_rewrites: HashMap<core_ir::Path, Vec<core_ir::Path>>,
    emitted: Vec<Binding>,
    active_specializations: Vec<ActivePrincipalSpecialization>,
    local_use_contexts: Vec<LocalUseContextScope>,
    local_value_contexts: Vec<BTreeMap<core_ir::Name, RuntimeType>>,
    next_index: usize,
    stats: HashMap<&'static str, usize>,
    target_skips: HashMap<core_ir::Path, HashMap<&'static str, usize>>,
    target_missing_vars: HashMap<core_ir::Path, HashMap<core_ir::TypeVar, usize>>,
}

#[derive(Debug, Clone)]
struct ActivePrincipalSpecialization {
    target: core_ir::Path,
    substitutions: BTreeMap<core_ir::TypeVar, core_ir::Type>,
    path: core_ir::Path,
    handler_plan: Option<HandlerAdapterPlan>,
}

#[derive(Default)]
struct LocalUseContextScope {
    uses: BTreeMap<core_ir::Name, core_ir::Type>,
    conflicts: BTreeSet<core_ir::Name>,
}

impl PrincipalUnifier {
    fn new(module: Module) -> Self {
        let bindings_by_path = module
            .bindings
            .iter()
            .map(|binding| (binding.name.clone(), binding.clone()))
            .collect::<HashMap<_, _>>();
        let generic_bindings = module
            .bindings
            .iter()
            .filter(|binding| !binding_required_vars(binding).is_empty())
            .map(|binding| (binding.name.clone(), binding.clone()))
            .collect::<HashMap<_, _>>();
        let role_impls = principal_unify_role_impls(&module);
        let next_index = next_principal_unify_index(&module);
        Self {
            module,
            bindings_by_path,
            generic_bindings,
            role_impls,
            specializations: HashMap::new(),
            root_specializations: HashMap::new(),
            role_method_rewrites: HashMap::new(),
            emitted: Vec::new(),
            active_specializations: Vec::new(),
            local_use_contexts: Vec::new(),
            local_value_contexts: Vec::new(),
            next_index,
            stats: HashMap::new(),
            target_skips: HashMap::new(),
            target_missing_vars: HashMap::new(),
        }
    }

    fn run(mut self) -> (Module, SubstitutionSpecializeProfile) {
        let mut module = std::mem::replace(&mut self.module, empty_module());
        module.root_exprs = module
            .root_exprs
            .into_iter()
            .map(|expr| {
                let expr = refresh_local_expr_types(expr);
                project_runtime_expr_types(self.rewrite_expr(expr, None))
            })
            .collect();
        module.bindings = module
            .bindings
            .into_iter()
            .map(|binding| Binding {
                body: {
                    let body = refresh_local_expr_types(binding.body);
                    project_runtime_expr_types(self.rewrite_expr(body, None))
                },
                ..binding
            })
            .collect();
        module.bindings.extend(std::mem::take(&mut self.emitted));
        module.root_exprs = module
            .root_exprs
            .into_iter()
            .map(|expr| {
                let expr = refresh_local_expr_types(expr);
                project_runtime_expr_types(self.rewrite_expr(expr, None))
            })
            .collect();
        module.bindings = module
            .bindings
            .into_iter()
            .map(|binding| Binding {
                body: {
                    let body = refresh_local_expr_types(binding.body);
                    project_runtime_expr_types(self.rewrite_expr(body, None))
                },
                ..binding
            })
            .collect();
        module.bindings.extend(std::mem::take(&mut self.emitted));
        add_single_specialization_aliases(&mut module, &self.root_specializations);
        rewrite_contextual_specialization_refs(&mut module, &self.root_specializations);
        rewrite_single_specialization_refs(&mut module, &self.root_specializations);
        remove_specialized_generic_originals(&mut module, &self.root_specializations);
        module.roots = module
            .roots
            .into_iter()
            .map(|root| self.rewrite_root_binding(root))
            .collect();
        let profile = self.finish_profile();
        (module, profile)
    }

    fn bump(&mut self, key: &'static str) {
        *self.stats.entry(key).or_default() += 1;
    }

    fn bump_skip(&mut self, target: &core_ir::Path, reason: &'static str) {
        debug_principal_unify_skip(target, reason);
        self.bump(reason);
        *self
            .target_skips
            .entry(target.clone())
            .or_default()
            .entry(reason)
            .or_default() += 1;
    }

    fn bump_missing_vars(
        &mut self,
        target: &core_ir::Path,
        binding: &Binding,
        substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
    ) {
        let entry = self.target_missing_vars.entry(target.clone()).or_default();
        for var in missing_required_vars(binding, substitutions) {
            *entry.entry(var).or_default() += 1;
        }
    }

    fn rewrite_root_binding(&self, root: Root) -> Root {
        let Root::Binding(path) = root else {
            return root;
        };
        let Some(specialized) = self.root_specializations.get(&path) else {
            return Root::Binding(path);
        };
        if specialized.len() != 1 {
            return Root::Binding(path);
        }
        Root::Binding(specialized.first().cloned().unwrap_or(path))
    }

    fn finish_profile(self) -> SubstitutionSpecializeProfile {
        let mut target_missing_vars = self.target_missing_vars;
        let mut target_skips = self
            .target_skips
            .into_iter()
            .map(|(target, reasons)| {
                let mut reasons = reasons
                    .into_iter()
                    .map(|(reason, count)| SubstitutionSpecializeSkipCount { reason, count })
                    .collect::<Vec<_>>();
                reasons.sort_by(|left, right| {
                    right
                        .count
                        .cmp(&left.count)
                        .then_with(|| left.reason.cmp(right.reason))
                });
                let mut missing_vars = target_missing_vars
                    .remove(&target)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|(var, count)| SubstitutionSpecializeMissingVarCount { var, count })
                    .collect::<Vec<_>>();
                missing_vars.sort_by(|left, right| {
                    right
                        .count
                        .cmp(&left.count)
                        .then_with(|| left.var.0.cmp(&right.var.0))
                });
                SubstitutionSpecializeTargetSkips {
                    target,
                    survives_final_prune: None,
                    actionable: reasons
                        .iter()
                        .any(|reason| !principal_unify_skip_reason_benign(reason.reason)),
                    reasons,
                    missing_vars,
                    no_complete_causes: Vec::new(),
                }
            })
            .collect::<Vec<_>>();
        target_skips.sort_by(|left, right| {
            let left_total = left
                .reasons
                .iter()
                .map(|reason| reason.count)
                .sum::<usize>();
            let right_total = right
                .reasons
                .iter()
                .map(|reason| reason.count)
                .sum::<usize>();
            right_total
                .cmp(&left_total)
                .then_with(|| canonical_path(&left.target).cmp(&canonical_path(&right.target)))
        });
        SubstitutionSpecializeProfile {
            stats: self.stats,
            target_skips,
            target_inferences: Vec::new(),
        }
    }

    fn rewrite_expr(&mut self, expr: Expr, result_context: Option<core_ir::TypeBounds>) -> Expr {
        let mut ty = expr.ty;
        let kind = match expr.kind {
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            } => {
                let original_apply = Expr {
                    ty: ty.clone(),
                    kind: ExprKind::Apply {
                        callee: callee.clone(),
                        arg: arg.clone(),
                        evidence: evidence.clone(),
                        instantiation: instantiation.clone(),
                    },
                };
                if let Some(spine) = principal_unify_apply_spine(&original_apply)
                    && !self.generic_bindings.contains_key(spine.target)
                    && let Some(rewritten) = self.rewrite_role_method_from_receiver(
                        &original_apply,
                        &spine,
                        result_context.as_ref(),
                    )
                {
                    return rewritten;
                }
                let callee_context = evidence
                    .as_ref()
                    .and_then(|evidence| evidence.expected_callee.clone());
                let callee = self.rewrite_expr(*callee, callee_context);
                let callee = force_rebuilt_thunked_function_callee(callee);
                let evidence_arg_context = evidence
                    .as_ref()
                    .and_then(|evidence| evidence.expected_arg.clone());
                let evidence_param_effect = evidence.as_ref().and_then(apply_evidence_param_effect);
                let callee_param_slot = runtime_function_param_slot(&callee.ty)
                    .or_else(|| forced_callee_function_param_slot(&callee));
                let arg_context = match (evidence_param_effect, callee_param_slot) {
                    (Some(effect), _) if principal_param_effect_requires_thunk(&effect) => None,
                    (_, Some((_param, effect)))
                        if principal_param_effect_requires_thunk(&effect) =>
                    {
                        None
                    }
                    (_, Some((param, _effect))) => Some(core_ir::TypeBounds::exact(param)),
                    (None, None)
                        if closed_type_from_bounds(evidence_arg_context.as_ref()).is_some() =>
                    {
                        evidence_arg_context
                    }
                    (None, None) => runtime_function_param_type(&callee.ty)
                        .map(core_ir::TypeBounds::exact)
                        .or(evidence_arg_context),
                    (Some(_), None) => runtime_function_param_type(&callee.ty)
                        .map(core_ir::TypeBounds::exact)
                        .or(evidence_arg_context),
                };
                let arg = self.rewrite_expr(*arg, arg_context);
                let instantiation = instantiation.and_then(|instantiation| {
                    self.single_local_emitted_specialization(&instantiation.target)
                        .is_none()
                        .then_some(instantiation)
                });
                let expr = Expr {
                    ty,
                    kind: ExprKind::Apply {
                        callee: Box::new(callee),
                        arg: Box::new(arg),
                        evidence,
                        instantiation,
                    },
                };
                let expr = project_runtime_expr_types(adapt_apply_argument_from_callee(expr));
                let expr = if self.apply_is_ready_for_principal_rewrite(&expr) {
                    self.rewrite_apply_from_principal_plan(&expr, result_context.as_ref())
                        .unwrap_or(expr)
                } else {
                    expr
                };
                return adapt_apply_result_from_evidence(expr, result_context.as_ref());
            }
            ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body,
            } => {
                let context_ty = runtime_context_function_type(result_context.as_ref());
                let had_context = context_ty.is_some();
                if let Some(context_ty) = context_ty {
                    ty = context_ty;
                }
                let body = if had_context {
                    refresh_lambda_body_local_types(
                        ty.clone(),
                        param.clone(),
                        param_effect_annotation.clone(),
                        param_function_allowed_effects.clone(),
                        *body,
                    )
                } else {
                    *body
                };
                let body_context = runtime_lambda_return_value_context(&ty);
                self.local_use_contexts
                    .push(LocalUseContextScope::default());
                self.push_local_value_type(param.clone(), lambda_param_runtime_type(&ty));
                let mut body = self.rewrite_expr(body, body_context);
                self.local_value_contexts.pop();
                let local_use_contexts = self
                    .local_use_contexts
                    .pop()
                    .map(local_use_context_scope_into_contexts)
                    .unwrap_or_default();
                if let Some(param_context) = local_use_contexts.get(&param)
                    && let Some(param_ty) = closed_type_from_bounds(Some(param_context))
                    && let Some(updated_ty) = runtime_function_type_with_param(ty.clone(), param_ty)
                    && updated_ty != ty
                {
                    ty = updated_ty;
                    body = refresh_lambda_body_local_types(
                        ty.clone(),
                        param.clone(),
                        param_effect_annotation.clone(),
                        param_function_allowed_effects.clone(),
                        body,
                    );
                    let body_context = runtime_lambda_return_value_context(&ty);
                    self.push_local_value_type(param.clone(), lambda_param_runtime_type(&ty));
                    body = self.rewrite_expr(body, body_context);
                    self.local_value_contexts.pop();
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
                evidence,
            } => {
                let branch_context = evidence
                    .as_ref()
                    .map(|evidence| core_ir::TypeBounds::exact(evidence.result.clone()))
                    .or(result_context.clone());
                ExprKind::If {
                    cond: Box::new(self.rewrite_expr(*cond, None)),
                    then_branch: Box::new(self.rewrite_expr(*then_branch, branch_context.clone())),
                    else_branch: Box::new(self.rewrite_expr(*else_branch, branch_context)),
                    evidence,
                }
            }
            ExprKind::Tuple(items) => ExprKind::Tuple(
                items
                    .into_iter()
                    .map(|item| self.rewrite_expr(item, None))
                    .collect(),
            ),
            ExprKind::Record { fields, spread } => ExprKind::Record {
                fields: fields
                    .into_iter()
                    .map(|field| RecordExprField {
                        name: field.name,
                        value: self.rewrite_expr(field.value, None),
                    })
                    .collect(),
                spread: spread.map(|spread| match spread {
                    RecordSpreadExpr::Head(expr) => {
                        RecordSpreadExpr::Head(Box::new(self.rewrite_expr(*expr, None)))
                    }
                    RecordSpreadExpr::Tail(expr) => {
                        RecordSpreadExpr::Tail(Box::new(self.rewrite_expr(*expr, None)))
                    }
                }),
            },
            ExprKind::Variant { tag, value } => ExprKind::Variant {
                tag,
                value: value.map(|value| Box::new(self.rewrite_expr(*value, None))),
            },
            ExprKind::Select { base, field } => ExprKind::Select {
                base: Box::new(self.rewrite_expr(*base, None)),
                field,
            },
            ExprKind::Match {
                scrutinee,
                arms,
                evidence,
            } => {
                let scrutinee_context =
                    Some(core_ir::TypeBounds::exact(runtime_core_type(&scrutinee.ty)));
                let arm_context = Some(core_ir::TypeBounds::exact(evidence.result.clone()));
                ExprKind::Match {
                    scrutinee: Box::new(self.rewrite_expr(*scrutinee, scrutinee_context)),
                    arms: arms
                        .into_iter()
                        .map(|arm| MatchArm {
                            pattern: arm.pattern,
                            guard: arm.guard.map(|guard| self.rewrite_expr(guard, None)),
                            body: {
                                let body_context = self
                                    .expr_is_nullary_generic_var(&arm.body)
                                    .then(|| arm_context.clone())
                                    .flatten();
                                self.rewrite_expr(arm.body, body_context)
                            },
                        })
                        .collect(),
                    evidence,
                }
            }
            ExprKind::Block { stmts, tail } => {
                let stmts = stmts
                    .into_iter()
                    .map(|stmt| self.rewrite_stmt(stmt))
                    .collect();
                let stmts = self.rewrite_block_module_stmt_types(stmts);
                let kind = ExprKind::Block {
                    stmts,
                    tail: tail
                        .map(|tail| Box::new(self.rewrite_expr(*tail, result_context.clone()))),
                };
                let refreshed =
                    project_runtime_expr_types(refresh_local_expr_types(Expr { ty, kind }));
                return self.rewrite_refreshed_block_once(refreshed, result_context.as_ref());
            }
            ExprKind::Handle {
                body,
                arms,
                evidence,
                handler,
            } => {
                let arm_context = Some(core_ir::TypeBounds::exact(evidence.result.clone()));
                let body = self.rewrite_expr(*body, None);
                let body = unwrap_handler_body_bind_here(body, &handler);
                let body = ensure_effectful_handler_body_thunk(body, &handler);
                ExprKind::Handle {
                    body: Box::new(body),
                    arms: arms
                        .into_iter()
                        .map(|arm| HandleArm {
                            effect: arm.effect,
                            payload: arm.payload,
                            resume: arm.resume,
                            guard: arm.guard.map(|guard| self.rewrite_expr(guard, None)),
                            body: self.rewrite_expr(arm.body, arm_context.clone()),
                        })
                        .collect(),
                    evidence,
                    handler,
                }
            }
            ExprKind::BindHere { expr } => {
                let expr = self.rewrite_expr(*expr, None);
                if !matches!(expr.ty, RuntimeType::Thunk { .. }) {
                    return expr;
                }
                ExprKind::BindHere {
                    expr: Box::new(expr),
                }
            }
            ExprKind::Thunk {
                effect,
                value,
                expr,
            } => {
                let initial_value =
                    if let Some(context) = closed_type_from_bounds(result_context.as_ref()) {
                        RuntimeType::core(context)
                    } else {
                        match &ty {
                            RuntimeType::Thunk {
                                value: ty_value, ..
                            } => ty_value.as_ref().clone(),
                            _ => value,
                        }
                    };
                let value_context = core_ir::TypeBounds::exact(runtime_core_type(&initial_value));
                let expr = self.rewrite_expr(*expr, Some(value_context));
                let value = if runtime_type_shape_usable(&expr.ty) {
                    expr.ty.clone()
                } else {
                    initial_value
                };
                ty = RuntimeType::thunk(effect.clone(), value.clone());
                ExprKind::Thunk {
                    effect,
                    value,
                    expr: Box::new(expr),
                }
            }
            ExprKind::LocalPushId { id, body } => {
                let body = self.rewrite_expr(*body, result_context);
                ty = body.ty.clone();
                ExprKind::LocalPushId {
                    id,
                    body: Box::new(body),
                }
            }
            ExprKind::AddId { id, allowed, thunk } => {
                let thunk = self.rewrite_expr(*thunk, result_context);
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
                expr: Box::new(self.rewrite_expr(*expr, None)),
            },
            ExprKind::Pack { var, expr } => ExprKind::Pack {
                var,
                expr: Box::new(self.rewrite_expr(*expr, None)),
            },
            ExprKind::Var(path) => {
                if let Some(local_ty) = self.local_value_type(&path) {
                    ty = local_ty;
                } else if let Some(binding_ty) = self.known_binding_runtime_type(&path) {
                    ty = binding_ty;
                }
                self.record_local_var_context(&path, result_context.as_ref());
                if self
                    .generic_bindings
                    .get(&path)
                    .is_some_and(|binding| core_fun_spine_exact(&binding.scheme.body, 1).is_none())
                    && let Some((specialized, ty)) = self.single_emitted_specialization(&path)
                {
                    return Expr::typed(ExprKind::Var(specialized), ty);
                }
                let inferred_context =
                    closed_runtime_value_type(&ty).map(core_ir::TypeBounds::exact);
                let nullary_context = result_context.as_ref().or(inferred_context.as_ref());
                if let Some(rewritten) =
                    self.rewrite_nullary_generic_from_context(&path, nullary_context)
                {
                    return rewritten;
                }
                ExprKind::Var(path)
            }
            ExprKind::EffectOp(_)
            | ExprKind::PrimitiveOp(_)
            | ExprKind::Lit(_)
            | ExprKind::PeekId
            | ExprKind::FindId { .. } => expr.kind,
        };
        ty = principal_rewrite_type_from_kind(ty, &kind);
        Expr { ty, kind }
    }

    fn record_local_var_context(
        &mut self,
        path: &core_ir::Path,
        result_context: Option<&core_ir::TypeBounds>,
    ) {
        let [name] = path.segments.as_slice() else {
            return;
        };
        let Some(context) = closed_type_from_bounds(result_context) else {
            return;
        };
        let Some(scope) = self.local_use_contexts.last_mut() else {
            return;
        };
        insert_local_use_context(&mut scope.uses, &mut scope.conflicts, name.clone(), context);
    }

    fn local_value_type(&self, path: &core_ir::Path) -> Option<RuntimeType> {
        let [name] = path.segments.as_slice() else {
            return None;
        };
        self.local_value_contexts
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn record_local_value_type(&mut self, pattern: &Pattern, ty: &RuntimeType) {
        let Some(name) = pattern_bind_name(pattern) else {
            return;
        };
        let Some(scope) = self.local_value_contexts.last_mut() else {
            return;
        };
        debug_principal_unify_local_value(name, ty);
        scope.insert(name.clone(), ty.clone());
    }

    fn push_local_value_type(&mut self, name: core_ir::Name, ty: Option<RuntimeType>) {
        let mut scope = BTreeMap::new();
        if let Some(ty) = ty {
            debug_principal_unify_local_value(&name, &ty);
            scope.insert(name, ty);
        }
        self.local_value_contexts.push(scope);
    }

    fn rewrite_stmt(&mut self, stmt: Stmt) -> Stmt {
        match stmt {
            Stmt::Let { pattern, value } => {
                let value_context = pattern_value_context(&pattern);
                let value = self.rewrite_expr(value, value_context);
                self.record_local_value_type(&pattern, &value.ty);
                Stmt::Let { pattern, value }
            }
            Stmt::Expr(expr) => Stmt::Expr(self.rewrite_expr(expr, None)),
            Stmt::Module { def, body } => {
                if let Some((specialized, ty)) = self.single_local_emitted_specialization(&def) {
                    return Stmt::Module {
                        def,
                        body: Expr::typed(ExprKind::Var(specialized), ty),
                    };
                }
                let body_context = self
                    .monomorphic_binding_type(&def)
                    .map(|ty| core_ir::TypeBounds::exact(runtime_core_type(&ty)));
                let body = self.rewrite_expr(body, body_context);
                Stmt::Module { def, body }
            }
        }
    }

    fn rewrite_refreshed_block_once(
        &mut self,
        expr: Expr,
        result_context: Option<&core_ir::TypeBounds>,
    ) -> Expr {
        let Expr {
            ty,
            kind: ExprKind::Block { stmts, tail },
        } = expr
        else {
            return expr;
        };
        self.local_use_contexts
            .push(LocalUseContextScope::default());
        self.local_value_contexts.push(BTreeMap::new());
        let stmts = stmts
            .into_iter()
            .map(|stmt| self.rewrite_stmt(stmt))
            .collect();
        let stmts = self.rewrite_block_module_stmt_types(stmts);
        let kind = ExprKind::Block {
            stmts,
            tail: tail.map(|tail| Box::new(self.rewrite_expr(*tail, result_context.cloned()))),
        };
        let local_use_contexts = self
            .local_use_contexts
            .pop()
            .map(local_use_context_scope_into_contexts)
            .unwrap_or_default();
        self.local_value_contexts.pop();
        let refreshed = refresh_local_expr_types(Expr { ty, kind });
        let refreshed =
            self.rewrite_refreshed_block_let_initializers(refreshed, local_use_contexts);
        project_runtime_expr_types(refresh_local_expr_types(refreshed))
    }

    fn rewrite_refreshed_block_let_initializers(
        &mut self,
        expr: Expr,
        mut local_use_contexts: BTreeMap<core_ir::Name, core_ir::TypeBounds>,
    ) -> Expr {
        let Expr {
            ty,
            kind: ExprKind::Block { stmts, tail },
        } = expr
        else {
            return expr;
        };
        merge_local_use_contexts(
            &mut local_use_contexts,
            collect_block_local_use_contexts(&stmts, tail.as_deref()),
        );
        self.local_value_contexts.push(BTreeMap::new());
        let stmts = stmts
            .into_iter()
            .map(|stmt| match stmt {
                Stmt::Let { pattern, value } => {
                    let value_context = pattern_value_context(&pattern).or_else(|| {
                        pattern_bind_name(&pattern)
                            .and_then(|name| local_use_contexts.get(name))
                            .cloned()
                    });
                    let value = self.rewrite_expr(value, value_context);
                    self.record_local_value_type(&pattern, &value.ty);
                    Stmt::Let { pattern, value }
                }
                Stmt::Expr(expr) => Stmt::Expr(self.rewrite_expr(expr, None)),
                Stmt::Module { def, body } => {
                    let body_context = self
                        .monomorphic_binding_type(&def)
                        .map(|ty| core_ir::TypeBounds::exact(runtime_core_type(&ty)));
                    let body = self.rewrite_expr(body, body_context);
                    Stmt::Module { def, body }
                }
            })
            .collect();
        let tail = tail.map(|tail| Box::new(self.rewrite_expr(*tail, None)));
        self.local_value_contexts.pop();
        Expr {
            ty,
            kind: ExprKind::Block { stmts, tail },
        }
    }

    fn rewrite_block_module_stmt_types(&self, stmts: Vec<Stmt>) -> Vec<Stmt> {
        stmts
            .into_iter()
            .map(|stmt| match stmt {
                Stmt::Module { def, mut body } => {
                    if let Some(ty) = self.monomorphic_binding_type(&def) {
                        body.ty = ty;
                    }
                    Stmt::Module { def, body }
                }
                stmt => stmt,
            })
            .collect()
    }

    fn rewrite_apply_from_principal_plan(
        &mut self,
        expr: &Expr,
        result_context: Option<&core_ir::TypeBounds>,
    ) -> Option<Expr> {
        self.bump("principal-unify-apply");
        let spine = principal_unify_apply_spine(expr)?;
        let Some(original) = self.generic_bindings.get(spine.target).cloned() else {
            if let Some(original) = self.bindings_by_path.get(spine.target).cloned()
                && let Some(expr) =
                    self.rewrite_non_generic_effect_context_call(original, &spine, &expr.ty)
            {
                return Some(expr);
            }
            if let Some(expr) = self.rewrite_role_method_from_receiver(expr, &spine, result_context)
            {
                return Some(expr);
            }
            self.bump_skip(spine.target, "skip-non-generic-callee");
            return None;
        };
        if let Some(active) = self.active_specialization_for(spine.target).cloned()
            && let Some(expr) =
                self.rewrite_active_recursive_call(original.clone(), active, &spine, &expr.ty)
        {
            return Some(expr);
        }
        if handler_binding_info(&original).is_some()
            && spine.args.len() < core_fun_arity(&original.scheme.body)
            && runtime_type_value_is_function(&expr.ty)
        {
            self.bump_skip(spine.target, "defer-partial-handler-application");
            return None;
        }
        let Some(mut plan) = principal_elaboration_plan_for_expr(expr, &original, result_context)
        else {
            self.bump_skip(spine.target, "missing-principal-elaboration-plan");
            return None;
        };
        if let Some(active_substitutions) = self.active_context_substitutions() {
            debug_principal_unify_active(spine.target, &active_substitutions);
            plan = substitute_principal_plan_context_slots(plan, &active_substitutions);
            let active_substitutions_for_plan = active_substitutions.clone();
            merge_plan_substitutions(&mut plan, active_substitutions);
            plan = normalize_principal_elaboration_plan_with_requirements(
                plan,
                &[],
                &original.scheme.requirements,
            );
            merge_plan_substitutions(&mut plan, active_substitutions_for_plan);
            debug_principal_unify_normalized_plan(&plan);
        }
        if let Some(active) = self.active_specialization_for(spine.target).cloned() {
            debug_principal_unify_active(spine.target, &active.substitutions);
            merge_plan_substitutions(&mut plan, active.substitutions);
            plan = normalize_principal_elaboration_plan_with_requirements(
                plan,
                &[],
                &original.scheme.requirements,
            );
        }
        if let Some(completed) = self.complete_plan_from_principal_callee(&original, &plan) {
            self.bump("principal-unify-principal-callee-completed-plan");
            plan = completed;
        }
        if let Some(completed) = self.complete_plan_from_binding_scheme_slots(&original, &plan) {
            self.bump("principal-unify-binding-scheme-slots-completed-plan");
            plan = completed;
        }
        let binding_required_vars = binding_required_vars(&original);
        if !plan.complete
            || !missing_required_vars(&original, &plan_substitution_map(&plan)).is_empty()
        {
            let projection_result_ty = result_context
                .as_ref()
                .and_then(|bounds| closed_type_from_bounds(Some(bounds)))
                .map(RuntimeType::core)
                .unwrap_or_else(|| expr.ty.clone());
            if let Some(completed) = self.complete_plan_from_runtime_effect_slots(
                &plan,
                &original,
                &spine.args,
                &projection_result_ty,
                &binding_required_vars,
                &original.scheme.requirements,
            ) {
                self.bump("principal-unify-runtime-effect-completed-plan");
                plan = completed;
            }
        }
        if !plan.complete
            && let Some(completed) = self.complete_plan_from_substituted_body(&original, &plan)
        {
            self.bump("principal-unify-body-result-completed-plan");
            plan = completed;
        }
        if !plan.complete
            && handler_binding_info(&original).is_some()
            && plan_only_lacks_handler_boundary(&plan)
        {
            for var in missing_required_vars(&original, &plan_substitution_map(&plan)) {
                plan.substitutions.push(core_ir::TypeSubstitution {
                    var,
                    ty: core_ir::Type::Never,
                });
            }
            plan = normalize_principal_elaboration_plan_with_requirements(
                plan,
                &[],
                &original.scheme.requirements,
            );
        }
        if !plan.complete
            && handler_binding_info(&original).is_some()
            && plan_only_lacks_handler_boundary(&plan)
            && missing_required_vars(&original, &plan_substitution_map(&plan)).is_empty()
        {
            self.bump("principal-unify-handler-boundary-plan-completed");
            plan.complete = true;
            plan.incomplete_reasons.clear();
        }
        if !plan.complete
            && missing_required_vars(&original, &plan_substitution_map(&plan)).is_empty()
            && plan_only_lacks_open_slot_precision(&plan)
        {
            self.bump("principal-unify-open-slot-plan-completed");
            plan.complete = true;
            plan.incomplete_reasons.clear();
        }
        if !plan.complete {
            if let Some(expr) = self.rewrite_single_emitted_specialized_call(&spine, &expr.ty) {
                return Some(expr);
            }
            self.bump_skip(spine.target, "incomplete-principal-elaboration-plan");
            let substitutions = plan_substitution_map(&plan);
            self.bump_missing_vars(spine.target, &original, &substitutions);
            return None;
        }
        if !plan.adapters.is_empty() {
            self.bump_skip(spine.target, "missing-adapter-hole-execution");
            return None;
        }
        let substitutions = plan_substitution_map(&plan);
        let Some(binding_substitutions) =
            complete_required_substitutions(&original, &substitutions)
        else {
            self.bump_skip(spine.target, "incomplete-binding-substitution");
            self.bump_missing_vars(spine.target, &original, &substitutions);
            return None;
        };
        if original.name.segments.len() == 1
            && binding_substitutions_are_only_top(&original, &binding_substitutions)
        {
            self.bump_skip(spine.target, "imprecise-principal-specialization");
            return None;
        }
        let callee_ty = substitute_type(&original.scheme.body, &binding_substitutions);
        let Some((params, _ret, _ret_effect)) =
            core_fun_spine_parts_exact(&callee_ty, spine.args.len())
        else {
            self.bump_skip(spine.target, "non-function-principal");
            return None;
        };
        let handler_info = handler_binding_info(&original);
        let is_handler_binding = handler_info.is_some();
        if handler_info.is_none() && !args_fit_without_adapter(&spine.args, &params) {
            self.bump_skip(spine.target, "missing-adapter-hole");
            return None;
        }
        let handler_plan = handler_info.map(|info| {
            let boundary = handler_call_boundary(&info, &spine.args, &expr.ty);
            let plan = handler_adapter_plan(&info, &boundary);
            let plan = substitute_handler_adapter_plan(&plan, &substitutions);
            (boundary, plan)
        });
        if let Some((boundary, plan)) = handler_plan.as_ref() {
            debug_principal_unify_handler_plan(spine.target, boundary, plan);
        }
        if let Some((boundary, plan)) = handler_plan.as_ref()
            && !handler_plan_is_supported(boundary, plan)
        {
            self.bump_skip(spine.target, "missing-handler-adapter-hole");
            return None;
        }
        let final_context_ty = if is_handler_binding {
            expr.ty.clone()
        } else {
            result_context
                .and_then(|bounds| closed_type_from_bounds(Some(bounds)))
                .map(RuntimeType::core)
                .unwrap_or_else(|| expr.ty.clone())
        };
        let handler_adapter_plan = handler_plan.as_ref().map(|(_, plan)| plan.clone());
        let call_callee_ty = handler_adapter_plan
            .as_ref()
            .and_then(|plan| {
                let substituted = substitute_binding(original.clone(), &binding_substitutions);
                Some(
                    apply_handler_adapter_plan_to_binding(substituted, plan)
                        .scheme
                        .body,
                )
            })
            .unwrap_or_else(|| callee_ty.clone());
        let path =
            self.intern_specialization(original, binding_substitutions, handler_adapter_plan)?;
        self.bump("principal-unify-rewrite");
        debug_principal_unify_rewrite(spine.target, &path);
        let final_arg_effect = handler_plan
            .as_ref()
            .and_then(|(_, plan)| plan.residual_before.as_ref())
            .filter(|effect| !effect_is_empty(effect));
        Some(rebuild_apply_call_with_final_arg_effect(
            path,
            call_callee_ty,
            &spine.args,
            &final_context_ty,
            final_arg_effect,
        )?)
    }

    fn complete_plan_from_principal_callee(
        &mut self,
        original: &Binding,
        plan: &core_ir::PrincipalElaborationPlan,
    ) -> Option<core_ir::PrincipalElaborationPlan> {
        let required_vars = binding_required_vars(original);
        if required_vars.is_empty() {
            return None;
        }
        let before = plan_substitution_map(plan);
        if missing_required_vars(original, &before).is_empty() && plan.complete {
            return None;
        }
        let mut substitutions = before.clone();
        let mut conflicts = BTreeSet::new();
        let plan_principal = substitute_type(&plan.principal_callee, &before);
        project_closed_substitutions_from_type(
            &original.scheme.body,
            &plan_principal,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
            false,
            64,
        );
        if substitutions == before
            && let Some(suffix) =
                principal_callee_scheme_suffix(&original.scheme.body, &plan_principal)
        {
            project_closed_substitutions_from_type(
                &suffix,
                &plan_principal,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                false,
                64,
            );
        }
        if !conflicts.is_empty() || substitutions == before {
            return None;
        }
        let projected_substitutions = substitutions.clone();
        let mut plan = plan.clone();
        plan.substitutions = substitutions
            .into_iter()
            .map(|(var, ty)| core_ir::TypeSubstitution { var, ty })
            .collect();
        let mut normalized = normalize_principal_elaboration_plan_with_requirements(
            plan,
            &[],
            &original.scheme.requirements,
        );
        preserve_projected_substitutions_if_normalized_empty(
            &mut normalized,
            projected_substitutions,
        );
        debug_principal_unify_normalized_plan(&normalized);
        Some(normalized)
    }

    fn complete_plan_from_binding_scheme_slots(
        &mut self,
        original: &Binding,
        plan: &core_ir::PrincipalElaborationPlan,
    ) -> Option<core_ir::PrincipalElaborationPlan> {
        let required_vars = binding_required_vars(original);
        if required_vars.is_empty() {
            return None;
        }
        let before = plan_substitution_map(plan);
        if missing_required_vars(original, &before).is_empty() {
            return None;
        }
        let mut substitutions = before.clone();
        let mut conflicts = BTreeSet::new();
        let template = substitute_type(&original.scheme.body, &substitutions);
        let Some((params, ret, _ret_effect)) =
            core_fun_spine_parts_exact(&template, plan.args.len())
        else {
            return None;
        };
        for arg in &plan.args {
            let Some((param, _effect)) = params.get(arg.index) else {
                continue;
            };
            if let Some(actual) = principal_plan_arg_closed_type(arg, &substitutions) {
                project_closed_substitutions_from_type(
                    param,
                    &actual,
                    &required_vars,
                    &mut substitutions,
                    &mut conflicts,
                    false,
                    64,
                );
            }
        }
        if let Some(actual) =
            principal_plan_result_closed_type_with_substitutions(&plan.result, &substitutions)
        {
            project_closed_substitutions_from_type(
                &ret,
                &actual,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                false,
                64,
            );
        }
        if !conflicts.is_empty() || substitutions == before {
            return None;
        }
        let projected_substitutions = substitutions.clone();
        let mut plan = plan.clone();
        plan.substitutions = substitutions
            .into_iter()
            .map(|(var, ty)| core_ir::TypeSubstitution { var, ty })
            .collect();
        let mut normalized = normalize_principal_elaboration_plan_with_requirements(
            plan,
            &[],
            &original.scheme.requirements,
        );
        preserve_projected_substitutions_if_normalized_empty(
            &mut normalized,
            projected_substitutions,
        );
        debug_principal_unify_normalized_plan(&normalized);
        Some(normalized)
    }

    fn rewrite_role_method_from_receiver(
        &mut self,
        expr: &Expr,
        spine: &PrincipalUnifyApplySpine<'_>,
        result_context: Option<&core_ir::TypeBounds>,
    ) -> Option<Expr> {
        let method = spine.target.segments.last()?;
        if !is_role_method_path(spine.target) || spine.args.is_empty() {
            return None;
        }
        let active_substitutions = self.active_context_substitutions();
        let receiver_ty = active_substitutions
            .as_ref()
            .map(|substitutions| {
                substitute_type(&runtime_core_type(&spine.args[0].ty), substitutions)
            })
            .unwrap_or_else(|| runtime_core_type(&spine.args[0].ty));
        let candidates = self.role_impls.get(method)?.clone();
        if runtime_type_value_is_function(&expr.ty) && !closed_slot_type_usable(&receiver_ty, false)
        {
            if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_some() {
                eprintln!(
                    "principal-unify partial-role-skip {:?} receiver={receiver_ty:?} active={active_substitutions:?}",
                    spine.target
                );
            }
            self.bump_skip(spine.target, "skip-partial-role-call");
            return None;
        }
        debug_principal_unify_role_candidates(
            spine.target,
            &receiver_ty,
            candidates.iter().map(|candidate| &candidate.name),
        );
        let role_result_ty = result_context
            .and_then(|bounds| closed_type_from_bounds(Some(bounds)))
            .map(RuntimeType::core)
            .unwrap_or_else(|| expr.ty.clone());
        let mut matches = candidates
            .iter()
            .filter_map(|candidate| {
                let substitutions = role_impl_closed_substitutions(
                    candidate,
                    spine,
                    &role_result_ty,
                    active_substitutions.as_ref(),
                )?;
                let score = role_impl_match_score(
                    candidate,
                    spine,
                    &role_result_ty,
                    &substitutions,
                    active_substitutions.as_ref(),
                );
                Some((candidate.clone(), substitutions, score))
            })
            .collect::<Vec<_>>();
        if let Some(best) = matches.iter().map(|(_, _, score)| *score).max() {
            matches.retain(|(_, _, score)| *score == best);
        }
        if matches.len() != 1 {
            if runtime_type_value_is_function(&expr.ty)
                && let Some(expr) = self.rewrite_role_method_head_from_receiver(
                    spine.target,
                    &candidates,
                    spine,
                    active_substitutions.as_ref(),
                    &role_result_ty,
                )
            {
                return Some(expr);
            }
            if let Some(expr) = self.rewrite_single_emitted_role_specialization(
                spine.target,
                &candidates,
                &spine.args,
                &role_result_ty,
            ) {
                self.bump("principal-unify-role-single-emitted-rewrite");
                return Some(expr);
            }
            if matches.len() > 1 {
                debug_principal_unify_role_ambiguous(
                    spine.target,
                    &receiver_ty,
                    matches
                        .iter()
                        .map(|(binding, substitutions, _score)| (&binding.name, substitutions)),
                );
                self.bump_skip(spine.target, "skip-ambiguous-role-impl");
            }
            return None;
        }
        let (original, substitutions, _score) = matches.pop()?;
        let impl_ty = substitute_type(&original.scheme.body, &substitutions);
        let Some((params, _ret, _ret_effect)) =
            core_fun_spine_parts_exact(&impl_ty, spine.args.len())
        else {
            debug_principal_unify_role_candidate_rejected(
                &original.name,
                "non-function-role-impl",
                &substitutions,
                &missing_required_vars(&original, &substitutions),
            );
            self.bump_skip(spine.target, "non-function-role-impl");
            return None;
        };
        let rewritten_args = spine
            .args
            .iter()
            .zip(&params)
            .map(|(arg, (param, _param_effect))| {
                self.rewrite_expr(
                    (*arg).clone(),
                    Some(core_ir::TypeBounds::exact(param.clone())),
                )
            })
            .collect::<Vec<_>>();
        if !owned_args_fit_without_adapter(&rewritten_args, &params) {
            debug_principal_unify_role_candidate_rejected(
                &original.name,
                "missing-role-adapter-hole",
                &substitutions,
                &missing_required_vars(&original, &substitutions),
            );
            self.bump_skip(spine.target, "missing-role-adapter-hole");
            return None;
        }
        let call_effect = final_ty_effect_context(&role_result_ty).or_else(|| {
            (!runtime_type_value_is_function(&role_result_ty))
                .then(|| {
                    combined_forced_argument_effect(&rewritten_args)
                        .or_else(|| combined_forced_argument_effect_refs(&spine.args))
                })
                .flatten()
        });
        let effect_context = call_effect.and_then(|effect| {
            let substituted = substitute_binding(original.clone(), &substitutions);
            let wrapped = match wrap_non_generic_binding_return_effect(
                substituted,
                spine.args.len(),
                effect.clone(),
            ) {
                Some(wrapped) => wrapped,
                None => {
                    self.bump_skip(spine.target, "missing-role-effect-wrapper");
                    return None;
                }
            };
            let impl_ty = wrapped.scheme.body.clone();
            let path = match self.intern_effect_context_specialization(
                wrapped,
                spine.args.len(),
                &effect,
                &substitutions,
            ) {
                Some(path) => path,
                None => {
                    self.bump_skip(spine.target, "missing-role-effect-specialization");
                    return None;
                }
            };
            let (_params, ret) = match core_fun_spine_exact(&impl_ty, spine.args.len()) {
                Some(parts) => parts,
                None => {
                    self.bump_skip(spine.target, "missing-role-effect-return");
                    return None;
                }
            };
            let final_ty = RuntimeType::thunk(effect, RuntimeType::core(ret));
            Some((path, impl_ty, final_ty))
        });
        let (path, impl_ty, final_ty) = if let Some(effect_context) = effect_context {
            effect_context
        } else {
            let path = self.intern_specialization(original, substitutions, None)?;
            (path, impl_ty, role_result_ty)
        };
        self.bump("principal-unify-role-rewrite");
        debug_principal_unify_rewrite(spine.target, &path);
        let role_rewrites = self
            .role_method_rewrites
            .entry(spine.target.clone())
            .or_default();
        if !role_rewrites.iter().any(|existing| existing == &path) {
            role_rewrites.push(path.clone());
        }
        Some(rebuild_apply_call_owned(
            path,
            impl_ty,
            rewritten_args,
            &final_ty,
        )?)
    }

    fn rewrite_role_method_head_from_receiver(
        &mut self,
        role_method: &core_ir::Path,
        candidates: &[Binding],
        spine: &PrincipalUnifyApplySpine<'_>,
        ambient_substitutions: Option<&BTreeMap<core_ir::TypeVar, core_ir::Type>>,
        final_ty: &RuntimeType,
    ) -> Option<Expr> {
        let mut matches = candidates
            .iter()
            .filter_map(|candidate| {
                let substitutions = role_impl_receiver_dispatch_substitutions(
                    candidate,
                    spine,
                    ambient_substitutions,
                )?;
                let impl_ty = substitute_type(&candidate.scheme.body, &substitutions);
                let _ = core_fun_spine_exact(&impl_ty, spine.args.len())?;
                Some((candidate, substitutions, impl_ty))
            })
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return None;
        }
        let (candidate, substitutions, impl_ty) = matches.pop()?;
        self.bump("principal-unify-role-head-dispatch");
        debug_principal_unify_rewrite(role_method, &candidate.name);
        let (target, impl_ty) = if substitutions.is_empty() {
            (candidate.name.clone(), impl_ty)
        } else {
            let path =
                self.intern_specialization(candidate.clone(), substitutions.clone(), None)?;
            let impl_ty = self
                .emitted
                .iter()
                .find(|binding| binding.name == path)
                .or_else(|| self.bindings_by_path.get(&path))
                .map(|binding| binding.scheme.body.clone())
                .unwrap_or_else(|| substitute_type(&candidate.scheme.body, &substitutions));
            let role_rewrites = self
                .role_method_rewrites
                .entry(role_method.clone())
                .or_default();
            if !role_rewrites.iter().any(|existing| existing == &path) {
                role_rewrites.push(path.clone());
            }
            (path, impl_ty)
        };
        let rewritten = rebuild_apply_call(target, impl_ty, &spine.args, final_ty)?;
        if !runtime_type_value_is_function(final_ty)
            && let Some(rewritten_spine) = principal_unify_apply_spine(&rewritten)
            && self.generic_bindings.contains_key(rewritten_spine.target)
            && let Some(specialized) = self.rewrite_apply_from_principal_plan(&rewritten, None)
        {
            return Some(specialized);
        }
        if !candidate.type_params.is_empty()
            || !missing_required_vars(candidate, &substitutions).is_empty()
        {
            self.bump_skip(role_method, "skip-generic-role-head-without-specialization");
            return None;
        }
        Some(rewritten)
    }

    fn rewrite_single_emitted_role_specialization(
        &self,
        role_method: &core_ir::Path,
        candidates: &[Binding],
        args: &[&Expr],
        final_ty: &RuntimeType,
    ) -> Option<Expr> {
        let mut matches = Vec::new();
        if let Some(paths) = self.role_method_rewrites.get(role_method) {
            for path in paths {
                let Some(binding) = self
                    .emitted
                    .iter()
                    .find(|binding| &binding.name == path)
                    .or_else(|| self.bindings_by_path.get(path))
                else {
                    continue;
                };
                if core_fun_spine_parts_exact(&binding.scheme.body, args.len()).is_some() {
                    matches.push((path.clone(), binding.scheme.body.clone()));
                }
            }
        }
        for candidate in candidates {
            let Some(paths) = self.root_specializations.get(&candidate.name) else {
                continue;
            };
            for path in paths {
                let Some(binding) = self.emitted.iter().find(|binding| &binding.name == path)
                else {
                    continue;
                };
                let Some((_params, _ret, _ret_effect)) =
                    core_fun_spine_parts_exact(&binding.scheme.body, args.len())
                else {
                    continue;
                };
                matches.push((path.clone(), binding.scheme.body.clone()));
            }
        }
        let [(path, callee_ty)] = matches.as_slice() else {
            return None;
        };
        rebuild_apply_call(path.clone(), callee_ty.clone(), args, final_ty)
    }

    fn rewrite_active_recursive_call(
        &mut self,
        original: Binding,
        active: ActivePrincipalSpecialization,
        spine: &PrincipalUnifyApplySpine<'_>,
        final_ty: &RuntimeType,
    ) -> Option<Expr> {
        let substitutions = active.substitutions;
        let callee_ty = if let Some(plan) = active.handler_plan.as_ref() {
            let substituted = substitute_binding(original.clone(), &substitutions);
            apply_handler_adapter_plan_to_binding(substituted, plan)
                .scheme
                .body
        } else {
            substitute_type(&original.scheme.body, &substitutions)
        };
        let Some((params, _ret, _ret_effect)) =
            core_fun_spine_parts_exact(&callee_ty, spine.args.len())
        else {
            return None;
        };
        let rewritten_args = spine
            .args
            .iter()
            .zip(&params)
            .map(|(arg, (param, _param_effect))| {
                self.rewrite_expr(
                    (*arg).clone(),
                    Some(core_ir::TypeBounds::exact(param.clone())),
                )
            })
            .collect::<Vec<_>>();
        if !owned_args_fit_without_adapter(&rewritten_args, &params) {
            return None;
        }
        self.bump("principal-unify-recursive-rewrite");
        debug_principal_unify_rewrite(spine.target, &active.path);
        rebuild_apply_call_owned(active.path, callee_ty, rewritten_args, final_ty)
    }

    fn rewrite_single_emitted_specialized_call(
        &mut self,
        spine: &PrincipalUnifyApplySpine<'_>,
        final_ty: &RuntimeType,
    ) -> Option<Expr> {
        let original = self.generic_bindings.get(spine.target)?;
        if spine.args.len() != core_fun_arity(&original.scheme.body) {
            return None;
        }
        let (specialized, _ty) = self.single_emitted_specialization(spine.target)?;
        let binding = self
            .emitted
            .iter()
            .find(|binding| binding.name == specialized)
            .cloned()?;
        let callee_ty = binding.scheme.body.clone();
        let Some((params, ret, ret_effect)) =
            core_fun_spine_parts_exact(&callee_ty, spine.args.len())
        else {
            return None;
        };
        let rewritten_args = spine
            .args
            .iter()
            .zip(&params)
            .map(|(arg, (param, _param_effect))| {
                self.rewrite_expr(
                    (*arg).clone(),
                    Some(core_ir::TypeBounds::exact(param.clone())),
                )
            })
            .collect::<Vec<_>>();
        if !owned_args_fit_without_adapter(&rewritten_args, &params) {
            return None;
        }
        if !runtime_type_has_vars(final_ty) {
            let (actual_ret, actual_ret_effect) = runtime_value_and_effect(final_ty);
            if !type_compatible(&actual_ret, &ret)
                || !type_compatible(&actual_ret_effect, &ret_effect)
            {
                return None;
            }
        }
        self.bump("principal-unify-single-specialization-rewrite");
        debug_principal_unify_rewrite(spine.target, &specialized);
        rebuild_apply_call_owned(specialized, callee_ty, rewritten_args, final_ty)
    }

    fn spine_is_full_generic_call(&self, spine: &PrincipalUnifyApplySpine<'_>) -> bool {
        self.generic_bindings
            .get(spine.target)
            .is_some_and(|binding| spine.args.len() == core_fun_arity(&binding.scheme.body))
    }

    fn apply_is_ready_for_principal_rewrite(&self, expr: &Expr) -> bool {
        let Some(spine) = principal_unify_apply_spine(expr) else {
            return false;
        };
        if self.generic_bindings.contains_key(spine.target) {
            return self.spine_is_full_generic_call(&spine);
        }
        true
    }

    fn rewrite_non_generic_effect_context_call(
        &mut self,
        original: Binding,
        spine: &PrincipalUnifyApplySpine<'_>,
        final_ty: &RuntimeType,
    ) -> Option<Expr> {
        if !binding_required_vars(&original).is_empty() {
            return None;
        }
        let RuntimeType::Thunk { effect, value } = final_ty else {
            return None;
        };
        if effect_is_empty(effect) || matches!(value.as_ref(), RuntimeType::Fun { .. }) {
            return None;
        }
        let (_params, ret) = core_fun_spine_exact(&original.scheme.body, spine.args.len())?;
        let expected = runtime_core_type(value);
        if ret != expected && !type_compatible(&expected, &ret) {
            return None;
        }
        let wrapped =
            wrap_non_generic_binding_return_effect(original, spine.args.len(), effect.clone())?;
        let callee_ty = wrapped.scheme.body.clone();
        let path = self.intern_effect_context_specialization(
            wrapped,
            spine.args.len(),
            &effect,
            &BTreeMap::new(),
        )?;
        self.bump("principal-unify-effect-context-rewrite");
        debug_principal_unify_rewrite(spine.target, &path);
        rebuild_apply_call(path, callee_ty, &spine.args, final_ty)
    }

    fn complete_plan_from_runtime_effect_slots(
        &mut self,
        plan: &core_ir::PrincipalElaborationPlan,
        original: &Binding,
        args: &[&Expr],
        result_ty: &RuntimeType,
        extra_required_vars: &BTreeSet<core_ir::TypeVar>,
        requirements: &[core_ir::RoleRequirement],
    ) -> Option<core_ir::PrincipalElaborationPlan> {
        if !plan.adapters.is_empty() {
            self.bump("principal-unify-runtime-effect-skip-adapter");
            return None;
        }
        let mut substitutions = plan_substitution_map(plan);
        let mut required_vars = BTreeSet::new();
        collect_core_type_vars(&plan.principal_callee, &mut required_vars);
        required_vars.extend(extra_required_vars.iter().cloned());
        if required_vars.is_empty() {
            self.bump("principal-unify-runtime-effect-skip-no-vars");
            return None;
        }
        let before = substitutions.len();
        let mut conflicts = BTreeSet::new();
        let projection_substitutions = substitutions
            .iter()
            .filter(|(_, ty)| !matches!(ty, core_ir::Type::Unknown | core_ir::Type::Any))
            .map(|(var, ty)| (var.clone(), ty.clone()))
            .collect::<BTreeMap<_, _>>();
        let substituted_principal =
            substitute_type(&original.scheme.body, &projection_substitutions);
        let (params, ret, ret_effect) =
            match core_fun_spine_parts_exact(&substituted_principal, args.len()) {
                Some(parts) => parts,
                None => {
                    self.bump("principal-unify-runtime-effect-skip-non-function");
                    return None;
                }
            };
        for (index, (arg, (param, param_effect))) in args.iter().zip(&params).enumerate() {
            let (actual, actual_effect) = runtime_value_and_effect(&arg.ty);
            debug_principal_unify_runtime_projection(
                "arg",
                plan.target.as_ref(),
                param,
                &actual,
                param_effect,
                &actual_effect,
            );
            project_closed_substitutions_from_type(
                param,
                &actual,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                false,
                64,
            );
            project_closed_substitutions_from_type(
                param_effect,
                &actual_effect,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                true,
                64,
            );
            if let Some(plan_arg) = plan.args.iter().find(|plan_arg| plan_arg.index == index)
                && let Some(contextual_actual) =
                    principal_plan_arg_closed_type(plan_arg, &substitutions)
            {
                project_closed_substitutions_from_type(
                    param,
                    &contextual_actual,
                    &required_vars,
                    &mut substitutions,
                    &mut conflicts,
                    false,
                    64,
                );
            }
        }
        let (actual_ret, actual_ret_effect) = runtime_value_and_effect(result_ty);
        debug_principal_unify_runtime_projection(
            "result",
            plan.target.as_ref(),
            &ret,
            &actual_ret,
            &ret_effect,
            &actual_ret_effect,
        );
        project_closed_substitutions_from_type(
            &ret,
            &actual_ret,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
            false,
            64,
        );
        project_closed_substitutions_from_type(
            &ret_effect,
            &actual_ret_effect,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
            true,
            64,
        );
        if let Some(info) = handler_binding_info(original)
            && let Some(active_residual_effect) = self.active_handler_residual_effect(&info)
        {
            debug_principal_unify_runtime_projection(
                "active-handler-residual",
                plan.target.as_ref(),
                &ret,
                &actual_ret,
                &ret_effect,
                &active_residual_effect,
            );
            project_closed_substitutions_from_type(
                &ret_effect,
                &active_residual_effect,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                true,
                64,
            );
        }
        if let Some(contextual_ret) =
            principal_plan_result_closed_type_with_substitutions(&plan.result, &substitutions)
        {
            project_closed_substitutions_from_type(
                &ret,
                &contextual_ret,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                false,
                64,
            );
        }
        let required_vars_closed = required_vars
            .iter()
            .all(|var| substitutions.contains_key(var));
        if !conflicts.is_empty() || (substitutions.len() == before && !required_vars_closed) {
            if !conflicts.is_empty() {
                self.bump("principal-unify-runtime-effect-conflict");
                debug_principal_unify_projection_outcome(
                    "conflict",
                    plan.target.as_ref(),
                    &substitutions,
                    &conflicts,
                );
            } else {
                self.bump("principal-unify-runtime-effect-no-new-substitution");
                debug_principal_unify_projection_outcome(
                    "no-new-substitution",
                    plan.target.as_ref(),
                    &substitutions,
                    &conflicts,
                );
            }
            return None;
        }
        if substitutions.len() == before {
            self.bump("principal-unify-runtime-effect-filled-slots");
        }
        debug_principal_unify_projection_outcome(
            "projected",
            plan.target.as_ref(),
            &substitutions,
            &conflicts,
        );
        let normalized_substitutions = substitutions.clone();
        let mut plan = plan.clone();
        plan.substitutions = substitutions
            .into_iter()
            .map(|(var, ty)| core_ir::TypeSubstitution { var, ty })
            .collect();
        fill_plan_runtime_slots_from_principal(&mut plan, args.len());
        fill_effectful_input_runtime_slot_from_result(&mut plan, args.len());
        let mut normalized =
            normalize_principal_elaboration_plan_with_requirements(plan, &[], requirements);
        if normalized.complete && normalized.substitutions.is_empty() {
            normalized.substitutions = normalized_substitutions
                .into_iter()
                .map(|(var, ty)| core_ir::TypeSubstitution { var, ty })
                .collect();
        }
        debug_principal_unify_normalized_plan(&normalized);
        Some(normalized)
    }

    fn active_handler_residual_effect(&self, info: &HandlerBindingInfo) -> Option<core_ir::Type> {
        let mut residual = None::<core_ir::Type>;
        for active in self.active_specializations.iter().rev() {
            for effect in active
                .substitutions
                .values()
                .filter_map(runtime_effect_row_candidate)
            {
                let Some(preserved) = handler_preserved_residual_effect(effect, &info.consumes)
                else {
                    continue;
                };
                residual = Some(match residual {
                    Some(existing) => merge_handler_residual_effects(existing, preserved),
                    None => preserved,
                });
            }
            if let Some(plan) = &active.handler_plan
                && let Some(after) = plan.residual_after.as_ref()
                && let Some(preserved) = handler_preserved_residual_effect(after, &info.consumes)
            {
                residual = Some(match residual {
                    Some(existing) => merge_handler_residual_effects(existing, preserved),
                    None => preserved,
                });
            }
        }
        residual
    }

    fn complete_plan_from_substituted_body(
        &mut self,
        original: &Binding,
        plan: &core_ir::PrincipalElaborationPlan,
    ) -> Option<core_ir::PrincipalElaborationPlan> {
        if !plan.adapters.is_empty() {
            self.bump("principal-unify-body-result-skip-adapter");
            return None;
        }
        let substitutions = plan_substitution_map(plan);
        if substitutions.is_empty() {
            self.bump("principal-unify-body-result-skip-no-substitutions");
            return None;
        }
        let substituted = substitute_binding(original.clone(), &substitutions);
        let Some(body) = binding_body_after_applied_args(&substituted.body, plan.args.len()) else {
            self.bump("principal-unify-body-result-skip-no-body");
            return None;
        };
        let Some(body_spine) = principal_unify_apply_spine(body) else {
            self.bump("principal-unify-body-result-skip-no-spine");
            return None;
        };
        let Some(inner) = self.generic_bindings.get(body_spine.target).cloned() else {
            self.bump("principal-unify-body-result-skip-non-generic-inner");
            return None;
        };
        let Some(inner_plan) = principal_elaboration_plan_for_expr(body, &inner, None) else {
            self.bump("principal-unify-body-result-skip-no-inner-plan");
            return None;
        };
        if !inner_plan.adapters.is_empty() {
            self.bump("principal-unify-body-result-skip-inner-adapter");
            return None;
        }
        let body_ret = if inner_plan.complete {
            let inner_substitutions = plan_substitution_map(&inner_plan);
            let inner_callee = substitute_type(&inner_plan.principal_callee, &inner_substitutions);
            let (_, body_ret) = core_fun_spine_exact(&inner_callee, body_spine.args.len())?;
            body_ret
        } else {
            let Some(body_ret) = principal_plan_result_closed_type(&inner_plan.result) else {
                self.bump("principal-unify-body-result-skip-open-inner-result");
                return None;
            };
            body_ret
        };

        let mut plan = plan.clone();
        plan.result.expected_runtime = Some(body_ret);
        let normalized = normalize_principal_elaboration_plan_with_requirements(
            plan,
            &[],
            &original.scheme.requirements,
        );
        if normalized.complete {
            Some(normalized)
        } else {
            self.bump("principal-unify-body-result-still-incomplete");
            None
        }
    }

    fn intern_specialization(
        &mut self,
        original: Binding,
        substitutions: BTreeMap<core_ir::TypeVar, core_ir::Type>,
        handler_plan: Option<HandlerAdapterPlan>,
    ) -> Option<core_ir::Path> {
        if substitutions.is_empty() && handler_plan.is_none() {
            return Some(original.name);
        }
        let key = principal_unify_key(&original.name, &substitutions, handler_plan.as_ref());
        if let Some(path) = self.specializations.get(&key) {
            return Some(path.clone());
        }
        let path = principal_unified_path(&original.name, self.next_index);
        self.next_index += 1;
        self.specializations.insert(key, path.clone());
        self.root_specializations
            .entry(original.name.clone())
            .or_default()
            .push(path.clone());
        debug_principal_unify_emit(&original.name, &path, &substitutions);
        let original_name = original.name.clone();
        let mut binding = substitute_binding(original, &substitutions);
        let active_handler_plan = handler_plan.clone();
        binding.name = path.clone();
        binding.type_params.clear();
        binding.body = refresh_local_expr_types(binding.body);
        self.active_specializations
            .push(ActivePrincipalSpecialization {
                target: original_name.clone(),
                substitutions: substitutions.clone(),
                path: path.clone(),
                handler_plan: active_handler_plan,
            });
        let binding_body_context = handler_plan
            .as_ref()
            .map(|plan| {
                apply_handler_adapter_plan_to_binding(binding.clone(), plan)
                    .scheme
                    .body
            })
            .unwrap_or_else(|| binding.scheme.body.clone());
        let binding_body_context = core_ir::TypeBounds::exact(binding_body_context);
        binding.body = self.rewrite_expr(binding.body, Some(binding_body_context));
        self.active_specializations.pop();
        if let Some(plan) = handler_plan {
            binding = apply_handler_adapter_plan_to_binding(binding, &plan);
        }
        binding.body = refresh_local_expr_types(binding.body);
        binding.body = project_runtime_expr_types(binding.body);
        binding.scheme.body =
            project_runtime_type_with_vars(&runtime_core_type(&binding.body.ty), &BTreeSet::new());
        self.emitted.push(binding);
        Some(path)
    }

    fn intern_effect_context_specialization(
        &mut self,
        mut binding: Binding,
        arity: usize,
        effect: &core_ir::Type,
        substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
    ) -> Option<core_ir::Path> {
        let key = format!(
            "{}|effect-context-arity={arity}|effect={effect:?}|subst={substitutions:?}",
            canonical_path(&binding.name),
        );
        if let Some(path) = self.specializations.get(&key) {
            return Some(path.clone());
        }
        let original_name = binding.name.clone();
        let path = principal_unified_path(&binding.name, self.next_index);
        self.next_index += 1;
        self.specializations.insert(key, path.clone());
        debug_principal_unify_emit(&original_name, &path, &BTreeMap::new());
        binding.name = path.clone();
        binding.type_params.clear();
        binding.body = refresh_local_expr_types(binding.body);
        self.active_specializations
            .push(ActivePrincipalSpecialization {
                target: original_name,
                substitutions: substitutions.clone(),
                path: path.clone(),
                handler_plan: None,
            });
        let binding_body_context = core_ir::TypeBounds::exact(binding.scheme.body.clone());
        binding.body = self.rewrite_expr(binding.body, Some(binding_body_context));
        self.active_specializations.pop();
        binding.body = refresh_local_expr_types(binding.body);
        binding.body = project_runtime_expr_types(binding.body);
        binding.scheme.body = runtime_core_type(&binding.body.ty);
        self.emitted.push(binding);
        Some(path)
    }

    fn active_specialization_for(
        &self,
        target: &core_ir::Path,
    ) -> Option<&ActivePrincipalSpecialization> {
        self.active_specializations
            .iter()
            .rev()
            .find(|active| &active.target == target)
    }

    fn active_context_substitutions(&self) -> Option<BTreeMap<core_ir::TypeVar, core_ir::Type>> {
        let mut substitutions = BTreeMap::new();
        for active in &self.active_specializations {
            for (var, ty) in &active.substitutions {
                substitutions.insert(var.clone(), ty.clone());
            }
        }
        (!substitutions.is_empty()).then_some(substitutions)
    }

    fn monomorphic_binding_type(&self, path: &core_ir::Path) -> Option<RuntimeType> {
        let binding = self.bindings_by_path.get(path)?;
        if !closed_slot_type_usable(&binding.scheme.body, false) {
            return None;
        }
        Some(RuntimeType::core(binding.scheme.body.clone()))
    }

    fn known_binding_runtime_type(&self, path: &core_ir::Path) -> Option<RuntimeType> {
        self.emitted
            .iter()
            .find(|binding| &binding.name == path)
            .map(|binding| binding.body.ty.clone())
    }

    fn single_emitted_specialization(
        &self,
        path: &core_ir::Path,
    ) -> Option<(core_ir::Path, RuntimeType)> {
        let specializations = self.root_specializations.get(path)?;
        let [specialized] = specializations.as_slice() else {
            return None;
        };
        let binding = self
            .emitted
            .iter()
            .find(|binding| &binding.name == specialized)?;
        Some((specialized.clone(), binding.body.ty.clone()))
    }

    fn single_local_emitted_specialization(
        &self,
        path: &core_ir::Path,
    ) -> Option<(core_ir::Path, RuntimeType)> {
        (path.segments.len() == 1)
            .then(|| self.single_emitted_specialization(path))
            .flatten()
    }

    fn rewrite_nullary_generic_from_context(
        &mut self,
        path: &core_ir::Path,
        result_context: Option<&core_ir::TypeBounds>,
    ) -> Option<Expr> {
        let original = self.generic_bindings.get(path).cloned()?;
        if core_fun_spine_exact(&original.scheme.body, 1).is_some() {
            return None;
        }
        let required = binding_required_vars(&original);
        if required.is_empty() {
            return None;
        }
        let context = closed_type_from_bounds(result_context)?;
        let mut substitutions = BTreeMap::new();
        let mut conflicts = BTreeSet::new();
        project_closed_substitutions_from_type(
            &original.scheme.body,
            &context,
            &required,
            &mut substitutions,
            &mut conflicts,
            false,
            64,
        );
        if !conflicts.is_empty() {
            self.bump_skip(path, "nullary-context-conflict");
            return None;
        }
        let substitutions = complete_required_substitutions(&original, &substitutions)?;
        let specialized_ty = substitute_type(&original.scheme.body, &substitutions);
        let specialized = self.intern_specialization(original, substitutions, None)?;
        self.bump("principal-unify-nullary-context-rewrite");
        Some(Expr::typed(
            ExprKind::Var(specialized),
            RuntimeType::core(specialized_ty),
        ))
    }

    fn expr_is_nullary_generic_var(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Var(path) => self
                .generic_bindings
                .get(path)
                .is_some_and(|binding| core_fun_spine_exact(&binding.scheme.body, 1).is_none()),
            ExprKind::Thunk { expr, .. }
            | ExprKind::LocalPushId { body: expr, .. }
            | ExprKind::Pack { expr, .. }
            | ExprKind::BindHere { expr }
            | ExprKind::Coerce { expr, .. } => self.expr_is_nullary_generic_var(expr),
            ExprKind::Block {
                tail: Some(tail), ..
            } => self.expr_is_nullary_generic_var(tail),
            ExprKind::AddId { thunk, .. } => self.expr_is_nullary_generic_var(thunk),
            _ => false,
        }
    }
}

struct PrincipalUnifyApplySpine<'a> {
    target: &'a core_ir::Path,
    args: Vec<&'a Expr>,
    evidences: Vec<Option<&'a core_ir::ApplyEvidence>>,
}

fn principal_unify_apply_spine(expr: &Expr) -> Option<PrincipalUnifyApplySpine<'_>> {
    let mut current = expr;
    let mut args = Vec::new();
    let mut evidences = Vec::new();
    loop {
        match &current.kind {
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                ..
            } => {
                args.push(arg.as_ref());
                evidences.push(evidence.as_ref());
                current = callee;
            }
            ExprKind::BindHere { expr } => {
                current = expr;
            }
            _ => break,
        }
    }
    let target = match &current.kind {
        ExprKind::Var(target) | ExprKind::EffectOp(target) => target,
        _ => return None,
    };
    args.reverse();
    evidences.reverse();
    Some(PrincipalUnifyApplySpine {
        target,
        args,
        evidences,
    })
}

fn binding_body_after_applied_args(expr: &Expr, arity: usize) -> Option<&Expr> {
    let mut body = expr;
    for _ in 0..arity {
        let ExprKind::Lambda { body: next, .. } = &body.kind else {
            return None;
        };
        body = next;
    }
    Some(block_tail_expr(body))
}

fn block_tail_expr(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let ExprKind::Block {
        stmts,
        tail: Some(tail),
    } = &current.kind
    {
        if !stmts.is_empty() {
            break;
        }
        current = tail;
    }
    current
}

fn plan_substitution_map(
    plan: &core_ir::PrincipalElaborationPlan,
) -> BTreeMap<core_ir::TypeVar, core_ir::Type> {
    plan.substitutions
        .iter()
        .map(|substitution| (substitution.var.clone(), substitution.ty.clone()))
        .collect()
}

fn add_single_specialization_aliases(
    module: &mut Module,
    root_specializations: &HashMap<core_ir::Path, Vec<core_ir::Path>>,
) {
    let binding_types_by_path = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding.body.ty.clone()))
        .collect::<HashMap<_, _>>();
    let mut aliases = Vec::new();
    for (original, specializations) in root_specializations {
        if original.segments.len() != 1 {
            continue;
        }
        let [specialized] = specializations.as_slice() else {
            continue;
        };
        let Some(ty) = binding_types_by_path.get(specialized).cloned() else {
            continue;
        };
        let alias = Binding {
            name: original.clone(),
            type_params: Vec::new(),
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: runtime_core_type(&ty),
            },
            body: Expr::typed(ExprKind::Var(specialized.clone()), ty),
        };
        if let Some(existing) = module
            .bindings
            .iter_mut()
            .find(|binding| &binding.name == original)
        {
            *existing = alias;
        } else {
            aliases.push(alias);
        }
    }
    module.bindings.extend(aliases);
}

fn rewrite_single_specialization_refs(
    module: &mut Module,
    root_specializations: &HashMap<core_ir::Path, Vec<core_ir::Path>>,
) {
    let handler_originals = handler_specialization_originals(module, root_specializations);
    let rewrites = root_specializations
        .iter()
        .filter_map(|(original, specializations)| {
            if handler_originals.contains(original) {
                return None;
            }
            let [specialized] = specializations.as_slice() else {
                return None;
            };
            Some((original.clone(), specialized.clone()))
        })
        .collect::<HashMap<_, _>>();
    if rewrites.is_empty() {
        return;
    }
    for expr in &mut module.root_exprs {
        rewrite_single_specialization_refs_expr(expr, &rewrites);
    }
    for binding in &mut module.bindings {
        if rewrites.contains_key(&binding.name) {
            continue;
        }
        rewrite_single_specialization_refs_expr(&mut binding.body, &rewrites);
    }
}

fn rewrite_contextual_specialization_refs(
    module: &mut Module,
    root_specializations: &HashMap<core_ir::Path, Vec<core_ir::Path>>,
) {
    let binding_types = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding.scheme.body.clone()))
        .collect::<HashMap<_, _>>();
    for expr in &mut module.root_exprs {
        rewrite_contextual_specialization_refs_expr(expr, root_specializations, &binding_types);
    }
    for binding in &mut module.bindings {
        rewrite_contextual_specialization_refs_expr(
            &mut binding.body,
            root_specializations,
            &binding_types,
        );
    }
}

fn remove_specialized_generic_originals(
    module: &mut Module,
    root_specializations: &HashMap<core_ir::Path, Vec<core_ir::Path>>,
) {
    module.bindings.retain(|binding| {
        binding.type_params.is_empty() || !root_specializations.contains_key(&binding.name)
    });
}

fn handler_specialization_originals(
    module: &Module,
    root_specializations: &HashMap<core_ir::Path, Vec<core_ir::Path>>,
) -> HashSet<core_ir::Path> {
    module
        .bindings
        .iter()
        .filter(|binding| {
            root_specializations.contains_key(&binding.name)
                && handler_binding_info(binding).is_some()
        })
        .map(|binding| binding.name.clone())
        .collect()
}

fn rewrite_single_specialization_refs_expr(
    expr: &mut Expr,
    rewrites: &HashMap<core_ir::Path, core_ir::Path>,
) {
    rewrite_single_specialization_refs_expr_inner(expr, rewrites, &mut BTreeSet::new());
}

fn rewrite_contextual_specialization_refs_expr(
    expr: &mut Expr,
    root_specializations: &HashMap<core_ir::Path, Vec<core_ir::Path>>,
    binding_types: &HashMap<core_ir::Path, core_ir::Type>,
) {
    rewrite_contextual_specialization_refs_expr_inner(
        expr,
        root_specializations,
        binding_types,
        &mut BTreeSet::new(),
    );
}

fn rewrite_contextual_specialization_refs_expr_inner(
    expr: &mut Expr,
    root_specializations: &HashMap<core_ir::Path, Vec<core_ir::Path>>,
    binding_types: &HashMap<core_ir::Path, core_ir::Type>,
    shadowed: &mut BTreeSet<core_ir::Name>,
) {
    rewrite_contextual_specialization_refs_children(
        expr,
        root_specializations,
        binding_types,
        shadowed,
    );
    let Some(spine) = principal_unify_apply_spine(expr) else {
        return;
    };
    if spine
        .target
        .segments
        .as_slice()
        .first()
        .is_some_and(|name| spine.target.segments.len() == 1 && shadowed.contains(name))
    {
        return;
    }
    let Some(candidates) = root_specializations.get(spine.target) else {
        return;
    };
    let args = spine
        .args
        .iter()
        .map(|arg| (*arg).clone())
        .collect::<Vec<_>>();
    let mut matches = candidates
        .iter()
        .filter_map(|path| {
            let ty = binding_types.get(path)?;
            core_fun_spine_parts_exact(ty, args.len())?;
            let context_score =
                rebuilt_specialization_call_score(ty, args.len(), &expr.ty, &spine.evidences)
                    .unwrap_or(0);
            let precision_score = rebuilt_specialization_precision_score(ty, args.len());
            Some((path, ty, context_score, precision_score))
        })
        .collect::<Vec<_>>();
    if let Some(best) = matches.iter().map(|(_, _, score, _)| *score).max() {
        matches.retain(|(_, _, score, _)| *score == best);
    }
    if let Some(best) = matches.iter().map(|(_, _, _, score)| *score).max() {
        matches.retain(|(_, _, _, score)| *score == best);
    }
    debug_principal_unify_contextual_candidates(spine.target, &matches);
    if matches.len() > 1
        && matches
            .first()
            .is_some_and(|(_, first_ty, _, _)| matches.iter().all(|(_, ty, _, _)| ty == first_ty))
    {
        let last = matches.pop().expect("non-empty contextual matches");
        matches.clear();
        matches.push(last);
    }
    if matches.len() != 1 {
        return;
    }
    let (path, ty, _context_score, _precision_score) =
        matches.pop().expect("single contextual specialization");
    if let Some(rewritten) = rebuild_apply_call_owned(path.clone(), ty.clone(), args, &expr.ty) {
        *expr = rewritten;
    }
}

fn rewrite_contextual_specialization_refs_children(
    expr: &mut Expr,
    root_specializations: &HashMap<core_ir::Path, Vec<core_ir::Path>>,
    binding_types: &HashMap<core_ir::Path, core_ir::Type>,
    shadowed: &mut BTreeSet<core_ir::Name>,
) {
    match &mut expr.kind {
        ExprKind::Apply { callee, arg, .. } => {
            rewrite_contextual_specialization_refs_expr_inner(
                callee,
                root_specializations,
                binding_types,
                shadowed,
            );
            rewrite_contextual_specialization_refs_expr_inner(
                arg,
                root_specializations,
                binding_types,
                shadowed,
            );
        }
        ExprKind::Lambda { param, body, .. } => {
            let inserted = shadowed.insert(param.clone());
            rewrite_contextual_specialization_refs_expr_inner(
                body,
                root_specializations,
                binding_types,
                shadowed,
            );
            if inserted {
                shadowed.remove(param);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            rewrite_contextual_specialization_refs_expr_inner(
                cond,
                root_specializations,
                binding_types,
                shadowed,
            );
            rewrite_contextual_specialization_refs_expr_inner(
                then_branch,
                root_specializations,
                binding_types,
                shadowed,
            );
            rewrite_contextual_specialization_refs_expr_inner(
                else_branch,
                root_specializations,
                binding_types,
                shadowed,
            );
        }
        ExprKind::Tuple(items) => {
            for item in items {
                rewrite_contextual_specialization_refs_expr_inner(
                    item,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                rewrite_contextual_specialization_refs_expr_inner(
                    &mut field.value,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
            }
            if let Some(spread) = spread {
                let spread = match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => expr,
                };
                rewrite_contextual_specialization_refs_expr_inner(
                    spread,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                rewrite_contextual_specialization_refs_expr_inner(
                    value,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
            }
        }
        ExprKind::Select { base, .. } => {
            rewrite_contextual_specialization_refs_expr_inner(
                base,
                root_specializations,
                binding_types,
                shadowed,
            );
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            rewrite_contextual_specialization_refs_expr_inner(
                scrutinee,
                root_specializations,
                binding_types,
                shadowed,
            );
            for arm in arms {
                let inserted = pattern_bind_name(&arm.pattern)
                    .map(|name| (name.clone(), shadowed.insert(name.clone())));
                if let Some(guard) = &mut arm.guard {
                    rewrite_contextual_specialization_refs_expr_inner(
                        guard,
                        root_specializations,
                        binding_types,
                        shadowed,
                    );
                }
                rewrite_contextual_specialization_refs_expr_inner(
                    &mut arm.body,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
                if let Some((name, true)) = inserted {
                    shadowed.remove(&name);
                }
            }
        }
        ExprKind::Block { stmts, tail } => {
            let saved = shadowed.clone();
            for stmt in stmts {
                match stmt {
                    Stmt::Let { pattern, value } => {
                        rewrite_contextual_specialization_refs_expr_inner(
                            value,
                            root_specializations,
                            binding_types,
                            shadowed,
                        );
                        if let Some(name) = pattern_bind_name(pattern) {
                            shadowed.insert(name.clone());
                        }
                    }
                    Stmt::Module { def, body } => {
                        rewrite_contextual_specialization_refs_expr_inner(
                            body,
                            root_specializations,
                            binding_types,
                            shadowed,
                        );
                        if let [name] = def.segments.as_slice() {
                            shadowed.insert(name.clone());
                        }
                    }
                    Stmt::Expr(body) => rewrite_contextual_specialization_refs_expr_inner(
                        body,
                        root_specializations,
                        binding_types,
                        shadowed,
                    ),
                }
            }
            if let Some(tail) = tail {
                rewrite_contextual_specialization_refs_expr_inner(
                    tail,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
            }
            *shadowed = saved;
        }
        ExprKind::Handle { body, arms, .. } => {
            rewrite_contextual_specialization_refs_expr_inner(
                body,
                root_specializations,
                binding_types,
                shadowed,
            );
            for arm in arms {
                let payload_inserted = pattern_bind_name(&arm.payload)
                    .map(|name| (name.clone(), shadowed.insert(name.clone())));
                let resume_inserted = arm
                    .resume
                    .as_ref()
                    .map(|resume| (resume.name.clone(), shadowed.insert(resume.name.clone())));
                if let Some(guard) = &mut arm.guard {
                    rewrite_contextual_specialization_refs_expr_inner(
                        guard,
                        root_specializations,
                        binding_types,
                        shadowed,
                    );
                }
                rewrite_contextual_specialization_refs_expr_inner(
                    &mut arm.body,
                    root_specializations,
                    binding_types,
                    shadowed,
                );
                if let Some((name, true)) = resume_inserted {
                    shadowed.remove(&name);
                }
                if let Some((name, true)) = payload_inserted {
                    shadowed.remove(&name);
                }
            }
        }
        ExprKind::AddId { thunk, .. } => rewrite_contextual_specialization_refs_expr_inner(
            thunk,
            root_specializations,
            binding_types,
            shadowed,
        ),
        ExprKind::LocalPushId { body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::BindHere { expr: body } => rewrite_contextual_specialization_refs_expr_inner(
            body,
            root_specializations,
            binding_types,
            shadowed,
        ),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn rebuilt_specialization_call_score(
    callee_ty: &core_ir::Type,
    arity: usize,
    final_ty: &RuntimeType,
    evidences: &[Option<&core_ir::ApplyEvidence>],
) -> Option<usize> {
    let final_score =
        core_fun_spine_parts_exact(callee_ty, arity).and_then(|(_params, ret, ret_effect)| {
            let expected = runtime_type_from_core_value_and_effect(ret, ret_effect);
            runtime_rebuilt_type_score(final_ty, &expected)
        });
    let evidence_score = rebuilt_specialization_evidence_score(callee_ty, evidences);
    let effect_context_score =
        rebuilt_specialization_effect_context_score(callee_ty, arity, final_ty);
    match (final_score, evidence_score, effect_context_score) {
        (Some(final_score), Some(evidence_score), Some(effect_context_score)) => {
            Some(final_score + evidence_score + effect_context_score)
        }
        (Some(final_score), Some(evidence_score), None) => Some(final_score + evidence_score),
        (Some(final_score), None, Some(effect_context_score)) => {
            Some(final_score + effect_context_score)
        }
        (None, Some(evidence_score), Some(effect_context_score)) => {
            Some(evidence_score + effect_context_score)
        }
        (Some(final_score), None, None) => Some(final_score),
        (None, Some(evidence_score), None) => Some(evidence_score),
        (None, None, Some(effect_context_score)) => Some(effect_context_score),
        (None, None, None) => None,
    }
}

fn rebuilt_specialization_effect_context_score(
    callee_ty: &core_ir::Type,
    arity: usize,
    final_ty: &RuntimeType,
) -> Option<usize> {
    let (_params, candidate_ret, candidate_ret_effect) =
        core_fun_spine_parts_exact(callee_ty, arity)?;
    let (actual_ret, actual_ret_effect) = runtime_value_and_effect(final_ty);
    let candidate_paths = core_result_effect_paths(&candidate_ret, &candidate_ret_effect);
    let actual_paths = core_result_effect_paths(&actual_ret, &actual_ret_effect);
    if actual_paths.is_empty() {
        return None;
    }
    if actual_paths.iter().any(|actual| {
        !candidate_paths
            .iter()
            .any(|candidate| effect_paths_match(candidate, actual))
    }) {
        return None;
    }
    let extra = candidate_paths
        .iter()
        .filter(|candidate| {
            !actual_paths
                .iter()
                .any(|actual| effect_paths_match(candidate, actual))
        })
        .count();
    Some(512usize.saturating_sub(extra * 16))
}

fn rebuilt_specialization_precision_score(callee_ty: &core_ir::Type, arity: usize) -> usize {
    let Some((_params, ret, ret_effect)) = core_fun_spine_parts_exact(callee_ty, arity) else {
        return 0;
    };
    let effect_paths = core_result_effect_paths(&ret, &ret_effect).len();
    let imprecise = core_type_imprecision_score(&ret) + core_type_imprecision_score(&ret_effect);
    1024usize.saturating_sub(effect_paths * 8 + imprecise * 16)
}

fn core_type_imprecision_score(ty: &core_ir::Type) -> usize {
    match ty {
        core_ir::Type::Unknown | core_ir::Type::Any | core_ir::Type::Var(_) => 1,
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_imprecision_score(param)
                + core_type_imprecision_score(param_effect)
                + core_type_imprecision_score(ret_effect)
                + core_type_imprecision_score(ret)
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            items.iter().map(core_type_imprecision_score).sum()
        }
        core_ir::Type::Record(record) => {
            let fields = record
                .fields
                .iter()
                .map(|field| core_type_imprecision_score(&field.value))
                .sum::<usize>();
            let spread = record
                .spread
                .as_ref()
                .map(|spread| match spread {
                    core_ir::RecordSpread::Head(spread) | core_ir::RecordSpread::Tail(spread) => {
                        core_type_imprecision_score(spread)
                    }
                })
                .unwrap_or(0);
            fields + spread
        }
        core_ir::Type::Variant(variant) => {
            let payloads = variant
                .cases
                .iter()
                .flat_map(|case| &case.payloads)
                .map(core_type_imprecision_score)
                .sum::<usize>();
            let tail = variant
                .tail
                .as_ref()
                .map(|tail| core_type_imprecision_score(tail))
                .unwrap_or(0);
            payloads + tail
        }
        core_ir::Type::Named { args, .. } => args
            .iter()
            .map(|arg| match arg {
                core_ir::TypeArg::Type(ty) => core_type_imprecision_score(ty),
                core_ir::TypeArg::Bounds(bounds) => {
                    bounds
                        .lower
                        .as_deref()
                        .map(core_type_imprecision_score)
                        .unwrap_or(0)
                        + bounds
                            .upper
                            .as_deref()
                            .map(core_type_imprecision_score)
                            .unwrap_or(0)
                }
            })
            .sum(),
        core_ir::Type::Row { items, tail } => {
            items.iter().map(core_type_imprecision_score).sum::<usize>()
                + core_type_imprecision_score(tail)
        }
        core_ir::Type::Recursive { body, .. } => core_type_imprecision_score(body),
        core_ir::Type::Never => 0,
    }
}

fn rebuilt_specialization_evidence_score(
    callee_ty: &core_ir::Type,
    evidences: &[Option<&core_ir::ApplyEvidence>],
) -> Option<usize> {
    let mut current = callee_ty.clone();
    let mut score = 0usize;
    for evidence in evidences {
        let core_ir::Type::Fun {
            ret_effect, ret, ..
        } = current
        else {
            return (score > 0).then_some(score);
        };
        if let Some(evidence) = evidence.as_ref().copied() {
            score += evidence_result_score(ret.as_ref(), ret_effect.as_ref(), &evidence.result);
        }
        current = ret.as_ref().clone();
    }
    (score > 0).then_some(score)
}

fn evidence_result_score(
    candidate_value: &core_ir::Type,
    candidate_effect: &core_ir::Type,
    result: &core_ir::TypeBounds,
) -> usize {
    result
        .lower
        .iter()
        .chain(result.upper.iter())
        .map(|expected| rebuilt_core_result_score(candidate_value, candidate_effect, expected))
        .max()
        .unwrap_or(0)
}

fn rebuilt_core_result_score(
    candidate_value: &core_ir::Type,
    candidate_effect: &core_ir::Type,
    expected: &core_ir::Type,
) -> usize {
    let mut score = 0usize;
    if candidate_value == expected {
        score += 16;
    } else if type_compatible(expected, candidate_value) {
        score += 4;
    }
    let candidate_paths = core_result_effect_paths(candidate_value, candidate_effect);
    let expected_paths = core_result_effect_paths(expected, &core_ir::Type::Never);
    if !candidate_paths.is_empty() && !expected_paths.is_empty() {
        if expected_paths.iter().any(|expected| {
            !candidate_paths
                .iter()
                .any(|candidate| effect_paths_match(candidate, expected))
        }) {
            return 0;
        }
        let extra = candidate_paths
            .iter()
            .filter(|candidate| {
                !expected_paths
                    .iter()
                    .any(|expected| effect_paths_match(candidate, expected))
            })
            .count();
        score += 64usize.saturating_sub(extra * 4);
    }
    score
}

fn core_result_effect_paths(
    value: &core_ir::Type,
    application_effect: &core_ir::Type,
) -> Vec<core_ir::Path> {
    let mut paths = effect_paths(application_effect);
    collect_core_type_effect_paths(value, &mut paths);
    paths
}

fn collect_core_type_effect_paths(ty: &core_ir::Type, paths: &mut Vec<core_ir::Path>) {
    match ty {
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_unique_effect_paths(param_effect, paths);
            collect_unique_effect_paths(ret_effect, paths);
            collect_core_type_effect_paths(param, paths);
            collect_core_type_effect_paths(ret, paths);
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            for item in items {
                collect_core_type_effect_paths(item, paths);
            }
        }
        core_ir::Type::Named { args, .. } => {
            for arg in args {
                match arg {
                    core_ir::TypeArg::Type(ty) => collect_core_type_effect_paths(ty, paths),
                    core_ir::TypeArg::Bounds(bounds) => {
                        if let Some(lower) = bounds.lower.as_deref() {
                            collect_core_type_effect_paths(lower, paths);
                        }
                        if let Some(upper) = bounds.upper.as_deref() {
                            collect_core_type_effect_paths(upper, paths);
                        }
                    }
                }
            }
        }
        core_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_core_type_effect_paths(&field.value, paths);
            }
            if let Some(spread) = &record.spread {
                let spread = match spread {
                    core_ir::RecordSpread::Head(spread) | core_ir::RecordSpread::Tail(spread) => {
                        spread
                    }
                };
                collect_core_type_effect_paths(spread, paths);
            }
        }
        core_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_core_type_effect_paths(payload, paths);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_core_type_effect_paths(tail, paths);
            }
        }
        core_ir::Type::Row { items, tail } => {
            for item in items {
                collect_core_type_effect_paths(item, paths);
            }
            collect_core_type_effect_paths(tail, paths);
        }
        core_ir::Type::Recursive { body, .. } => collect_core_type_effect_paths(body, paths),
        core_ir::Type::Var(_)
        | core_ir::Type::Never
        | core_ir::Type::Any
        | core_ir::Type::Unknown => {}
    }
}

fn collect_unique_effect_paths(effect: &core_ir::Type, paths: &mut Vec<core_ir::Path>) {
    for path in effect_paths(effect) {
        if !paths
            .iter()
            .any(|existing| effect_paths_match(existing, &path))
        {
            paths.push(path);
        }
    }
}

fn runtime_rebuilt_type_score(actual: &RuntimeType, expected: &RuntimeType) -> Option<usize> {
    if actual == expected {
        return Some(8);
    }
    let (actual_value, actual_effect) = runtime_value_and_effect(actual);
    let (expected_value, expected_effect) = runtime_value_and_effect(expected);
    if !type_compatible(&expected_value, &actual_value)
        || !effect_compatible(&expected_effect, &actual_effect)
    {
        return None;
    }
    let value_score = usize::from(expected_value == actual_value) * 2;
    let effect_score = usize::from(expected_effect == actual_effect) * 4;
    Some(1 + value_score + effect_score)
}

fn rewrite_single_specialization_refs_expr_inner(
    expr: &mut Expr,
    rewrites: &HashMap<core_ir::Path, core_ir::Path>,
    shadowed: &mut BTreeSet<core_ir::Name>,
) {
    match &mut expr.kind {
        ExprKind::Var(path) => {
            if path
                .segments
                .as_slice()
                .first()
                .is_some_and(|name| path.segments.len() == 1 && shadowed.contains(name))
            {
                return;
            }
            if let Some(specialized) = rewrites.get(path) {
                *path = specialized.clone();
            }
        }
        ExprKind::Apply { callee, arg, .. } => {
            rewrite_single_specialization_refs_expr_inner(callee, rewrites, shadowed);
            rewrite_single_specialization_refs_expr_inner(arg, rewrites, shadowed);
        }
        ExprKind::Lambda { param, body, .. } => {
            let inserted = shadowed.insert(param.clone());
            rewrite_single_specialization_refs_expr_inner(body, rewrites, shadowed);
            if inserted {
                shadowed.remove(param);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            rewrite_single_specialization_refs_expr_inner(cond, rewrites, shadowed);
            rewrite_single_specialization_refs_expr_inner(then_branch, rewrites, shadowed);
            rewrite_single_specialization_refs_expr_inner(else_branch, rewrites, shadowed);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                rewrite_single_specialization_refs_expr_inner(item, rewrites, shadowed);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                rewrite_single_specialization_refs_expr_inner(&mut field.value, rewrites, shadowed);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        rewrite_single_specialization_refs_expr_inner(expr, rewrites, shadowed);
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                rewrite_single_specialization_refs_expr_inner(value, rewrites, shadowed);
            }
        }
        ExprKind::Select { base, .. } => {
            rewrite_single_specialization_refs_expr_inner(base, rewrites, shadowed);
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            rewrite_single_specialization_refs_expr_inner(scrutinee, rewrites, shadowed);
            for arm in arms {
                let inserted = pattern_bind_name(&arm.pattern)
                    .map(|name| (name.clone(), shadowed.insert(name.clone())));
                if let Some(guard) = &mut arm.guard {
                    rewrite_single_specialization_refs_expr_inner(guard, rewrites, shadowed);
                }
                rewrite_single_specialization_refs_expr_inner(&mut arm.body, rewrites, shadowed);
                if let Some((name, true)) = inserted {
                    shadowed.remove(&name);
                }
            }
        }
        ExprKind::Block { stmts, tail } => {
            let saved = shadowed.clone();
            for stmt in stmts {
                match stmt {
                    Stmt::Let { pattern, value } => {
                        rewrite_single_specialization_refs_expr_inner(value, rewrites, shadowed);
                        if let Some(name) = pattern_bind_name(pattern) {
                            shadowed.insert(name.clone());
                        }
                    }
                    Stmt::Module { def, body } => {
                        rewrite_single_specialization_refs_expr_inner(body, rewrites, shadowed);
                        if let [name] = def.segments.as_slice() {
                            shadowed.insert(name.clone());
                        }
                    }
                    Stmt::Expr(body) => {
                        rewrite_single_specialization_refs_expr_inner(body, rewrites, shadowed);
                    }
                }
            }
            if let Some(tail) = tail {
                rewrite_single_specialization_refs_expr_inner(tail, rewrites, shadowed);
            }
            *shadowed = saved;
        }
        ExprKind::Handle { body, arms, .. } => {
            rewrite_single_specialization_refs_expr_inner(body, rewrites, shadowed);
            for arm in arms {
                let payload_inserted = pattern_bind_name(&arm.payload)
                    .map(|name| (name.clone(), shadowed.insert(name.clone())));
                let resume_inserted = arm
                    .resume
                    .as_ref()
                    .map(|resume| (resume.name.clone(), shadowed.insert(resume.name.clone())));
                if let Some(guard) = &mut arm.guard {
                    rewrite_single_specialization_refs_expr_inner(guard, rewrites, shadowed);
                }
                rewrite_single_specialization_refs_expr_inner(&mut arm.body, rewrites, shadowed);
                if let Some((name, true)) = resume_inserted {
                    shadowed.remove(&name);
                }
                if let Some((name, true)) = payload_inserted {
                    shadowed.remove(&name);
                }
            }
        }
        ExprKind::AddId { thunk, .. } => {
            rewrite_single_specialization_refs_expr_inner(thunk, rewrites, shadowed);
        }
        ExprKind::LocalPushId { body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::BindHere { expr: body } => {
            rewrite_single_specialization_refs_expr_inner(body, rewrites, shadowed);
        }
        ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn pattern_value_context(pattern: &Pattern) -> Option<core_ir::TypeBounds> {
    let ty = runtime_core_type(pattern_runtime_type(pattern));
    closed_slot_type_usable(&ty, false).then(|| core_ir::TypeBounds::exact(ty))
}

fn pattern_bind_name(pattern: &Pattern) -> Option<&core_ir::Name> {
    match pattern {
        Pattern::Bind { name, .. } => Some(name),
        Pattern::As { name, .. } => Some(name),
        _ => None,
    }
}

fn collect_block_local_use_contexts(
    stmts: &[Stmt],
    tail: Option<&Expr>,
) -> BTreeMap<core_ir::Name, core_ir::TypeBounds> {
    let mut uses = BTreeMap::<core_ir::Name, core_ir::Type>::new();
    let mut conflicts = BTreeSet::<core_ir::Name>::new();
    for stmt in stmts {
        collect_stmt_local_use_contexts(stmt, &mut uses, &mut conflicts);
    }
    if let Some(tail) = tail {
        collect_expr_local_use_contexts(tail, &mut uses, &mut conflicts);
    }
    for conflict in conflicts {
        uses.remove(&conflict);
    }
    uses.into_iter()
        .map(|(name, ty)| (name, core_ir::TypeBounds::exact(ty)))
        .collect()
}

fn local_use_context_scope_into_contexts(
    mut scope: LocalUseContextScope,
) -> BTreeMap<core_ir::Name, core_ir::TypeBounds> {
    for conflict in scope.conflicts {
        scope.uses.remove(&conflict);
    }
    scope
        .uses
        .into_iter()
        .map(|(name, ty)| (name, core_ir::TypeBounds::exact(ty)))
        .collect()
}

fn merge_local_use_contexts(
    target: &mut BTreeMap<core_ir::Name, core_ir::TypeBounds>,
    source: BTreeMap<core_ir::Name, core_ir::TypeBounds>,
) {
    for (name, bounds) in source {
        match target.get(&name) {
            Some(existing) if existing != &bounds => {
                target.remove(&name);
            }
            Some(_) => {}
            None => {
                target.insert(name, bounds);
            }
        }
    }
}

fn collect_stmt_local_use_contexts(
    stmt: &Stmt,
    uses: &mut BTreeMap<core_ir::Name, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::Name>,
) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_expr_local_use_contexts(value, uses, conflicts);
        }
    }
}

fn collect_expr_local_use_contexts(
    expr: &Expr,
    uses: &mut BTreeMap<core_ir::Name, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::Name>,
) {
    if let ExprKind::Var(path) = &expr.kind
        && let [name] = path.segments.as_slice()
        && let Some(ty) = closed_runtime_value_type(&expr.ty)
    {
        insert_local_use_context(uses, conflicts, name.clone(), ty);
    }

    match &expr.kind {
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::Pack { expr: body, .. }
        | ExprKind::Coerce { expr: body, .. } => {
            collect_expr_local_use_contexts(body, uses, conflicts);
        }
        ExprKind::Apply { callee, arg, .. } => {
            collect_expr_local_use_contexts(callee, uses, conflicts);
            collect_expr_local_use_contexts(arg, uses, conflicts);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_local_use_contexts(cond, uses, conflicts);
            collect_expr_local_use_contexts(then_branch, uses, conflicts);
            collect_expr_local_use_contexts(else_branch, uses, conflicts);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_local_use_contexts(item, uses, conflicts);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_local_use_contexts(&field.value, uses, conflicts);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        collect_expr_local_use_contexts(expr, uses, conflicts);
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_local_use_contexts(value, uses, conflicts);
            }
        }
        ExprKind::Select { base, .. } => {
            collect_expr_local_use_contexts(base, uses, conflicts);
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_local_use_contexts(scrutinee, uses, conflicts);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_local_use_contexts(guard, uses, conflicts);
                }
                collect_expr_local_use_contexts(&arm.body, uses, conflicts);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt_local_use_contexts(stmt, uses, conflicts);
            }
            if let Some(tail) = tail {
                collect_expr_local_use_contexts(tail, uses, conflicts);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_expr_local_use_contexts(body, uses, conflicts);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_local_use_contexts(guard, uses, conflicts);
                }
                collect_expr_local_use_contexts(&arm.body, uses, conflicts);
            }
        }
        ExprKind::Thunk { expr, .. } | ExprKind::AddId { thunk: expr, .. } => {
            collect_expr_local_use_contexts(expr, uses, conflicts);
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn insert_local_use_context(
    uses: &mut BTreeMap<core_ir::Name, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::Name>,
    name: core_ir::Name,
    ty: core_ir::Type,
) {
    if conflicts.contains(&name) {
        return;
    }
    match uses.get(&name) {
        Some(existing)
            if matches!(existing, core_ir::Type::Unknown | core_ir::Type::Any)
                && !matches!(ty, core_ir::Type::Unknown | core_ir::Type::Any) =>
        {
            uses.insert(name, ty);
        }
        Some(_) if matches!(ty, core_ir::Type::Unknown | core_ir::Type::Any) => {}
        Some(existing) if existing != &ty => {
            uses.remove(&name);
            conflicts.insert(name);
        }
        Some(_) => {}
        None => {
            uses.insert(name, ty);
        }
    }
}

fn pattern_runtime_type(pattern: &Pattern) -> &RuntimeType {
    match pattern {
        Pattern::Tuple { ty, .. }
        | Pattern::List { ty, .. }
        | Pattern::Record { ty, .. }
        | Pattern::Variant { ty, .. }
        | Pattern::Lit { ty, .. }
        | Pattern::Bind { ty, .. }
        | Pattern::Wildcard { ty }
        | Pattern::Or { ty, .. }
        | Pattern::As { ty, .. } => ty,
    }
}

fn principal_rewrite_type_from_kind(fallback: RuntimeType, kind: &ExprKind) -> RuntimeType {
    match kind {
        ExprKind::Tuple(items) => RuntimeType::core(core_ir::Type::Tuple(
            items
                .iter()
                .map(|item| runtime_core_type(&item.ty))
                .collect(),
        )),
        ExprKind::If {
            then_branch,
            else_branch,
            ..
        } if then_branch.ty == else_branch.ty => then_branch.ty.clone(),
        ExprKind::Match { arms, .. } => arms
            .first()
            .map(|arm| arm.body.ty.clone())
            .unwrap_or(fallback),
        ExprKind::Block {
            tail: Some(tail), ..
        } => tail.ty.clone(),
        ExprKind::BindHere { expr } => match &expr.ty {
            RuntimeType::Thunk { value, .. } => value.as_ref().clone(),
            _ => fallback,
        },
        ExprKind::Thunk { effect, value, .. } => RuntimeType::thunk(effect.clone(), value.clone()),
        ExprKind::LocalPushId { body, .. } => body.ty.clone(),
        ExprKind::AddId { thunk, .. } => thunk.ty.clone(),
        ExprKind::Coerce { to, .. } => RuntimeType::core(to.clone()),
        _ => fallback,
    }
}

fn fill_plan_runtime_slots_from_principal(
    plan: &mut core_ir::PrincipalElaborationPlan,
    arg_count: usize,
) {
    let substitutions = plan_substitution_map(plan);
    let callee = substitute_type(&plan.principal_callee, &substitutions);
    let Some((params, ret)) = core_fun_spine_exact(&callee, arg_count) else {
        return;
    };
    for arg in &mut plan.args {
        if arg.expected_runtime.is_none()
            && let Some(param) = params.get(arg.index)
            && closed_slot_type_usable(param, false)
        {
            arg.expected_runtime = Some(param.clone());
        }
    }
    if plan.result.expected_runtime.is_none() && closed_slot_type_usable(&ret, false) {
        plan.result.expected_runtime = Some(ret);
    }
}

fn fill_effectful_input_runtime_slot_from_result(
    plan: &mut core_ir::PrincipalElaborationPlan,
    arg_count: usize,
) {
    if arg_count != 1 || plan.args.len() != 1 || plan.args[0].expected_runtime.is_some() {
        return;
    }
    let Some(result) = principal_plan_result_closed_type(&plan.result) else {
        return;
    };
    if !closed_slot_type_usable(&result, false) {
        return;
    }
    let substitutions = plan_substitution_map(plan);
    let callee = substitute_type(&plan.principal_callee, &substitutions);
    let Some((params, ret, _ret_effect)) = core_fun_spine_parts_exact(&callee, arg_count) else {
        return;
    };
    let Some((param, param_effect)) = params.first() else {
        return;
    };
    if !matches!(param, core_ir::Type::Unknown | core_ir::Type::Any)
        || effect_is_empty(param_effect)
    {
        return;
    }
    if ret != result && !type_compatible(&result, &ret) {
        return;
    }
    plan.args[0].expected_runtime = Some(result);
}

fn merge_plan_substitutions(
    plan: &mut core_ir::PrincipalElaborationPlan,
    substitutions: BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    for (var, ty) in substitutions {
        if plan
            .substitutions
            .iter()
            .any(|substitution| substitution.var == var)
        {
            continue;
        }
        plan.substitutions
            .push(core_ir::TypeSubstitution { var, ty });
    }
}

fn substitute_principal_plan_context_slots(
    mut plan: core_ir::PrincipalElaborationPlan,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> core_ir::PrincipalElaborationPlan {
    for substitution in &mut plan.substitutions {
        substitution.ty = substitute_type(&substitution.ty, substitutions);
    }
    for arg in &mut plan.args {
        arg.intrinsic = substitute_bounds(arg.intrinsic.clone(), substitutions);
        arg.contextual = arg
            .contextual
            .take()
            .map(|bounds| substitute_bounds(bounds, substitutions));
        arg.expected_runtime = arg
            .expected_runtime
            .take()
            .map(|ty| substitute_type(&ty, substitutions));
    }
    plan.result.intrinsic = substitute_bounds(plan.result.intrinsic, substitutions);
    plan.result.contextual = plan
        .result
        .contextual
        .take()
        .map(|bounds| substitute_bounds(bounds, substitutions));
    plan.result.expected_runtime = plan
        .result
        .expected_runtime
        .take()
        .map(|ty| substitute_type(&ty, substitutions));
    for adapter in &mut plan.adapters {
        adapter.actual = substitute_type(&adapter.actual, substitutions);
        adapter.expected = substitute_type(&adapter.expected, substitutions);
    }
    plan
}

fn preserve_projected_substitutions_if_normalized_empty(
    plan: &mut core_ir::PrincipalElaborationPlan,
    substitutions: BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    if !plan.complete || !plan.substitutions.is_empty() {
        return;
    }
    plan.substitutions = substitutions
        .into_iter()
        .map(|(var, ty)| core_ir::TypeSubstitution { var, ty })
        .collect();
}

fn principal_callee_scheme_suffix(
    scheme: &core_ir::Type,
    principal_callee: &core_ir::Type,
) -> Option<core_ir::Type> {
    let scheme_arity = core_fun_arity(scheme);
    let principal_arity = core_fun_arity(principal_callee);
    if principal_arity == 0 || principal_arity >= scheme_arity {
        return None;
    }
    drop_core_fun_params(scheme, scheme_arity - principal_arity)
}

fn drop_core_fun_params(ty: &core_ir::Type, count: usize) -> Option<core_ir::Type> {
    if count == 0 {
        return Some(ty.clone());
    }
    let core_ir::Type::Fun { ret, .. } = ty else {
        return None;
    };
    drop_core_fun_params(ret, count - 1)
}

fn binding_required_vars(binding: &Binding) -> BTreeSet<core_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    vars.extend(binding.type_params.iter().cloned());
    collect_binding_type_params(binding, &mut vars);
    vars
}

fn principal_unify_skip_reason_benign(reason: &str) -> bool {
    matches!(
        reason,
        "skip-non-generic-callee"
            | "skip-local-leaf-specialization"
            | "skip-recursive-leaf-specialization"
            | "skip-partial-role-call"
    )
}

fn missing_required_vars(
    binding: &Binding,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Vec<core_ir::TypeVar> {
    let effect_only_vars = binding_effect_only_vars(binding);
    let mut vars = binding_required_vars(binding)
        .into_iter()
        .filter(|var| {
            substitutions
                .get(var)
                .is_none_or(|ty| !substitution_is_complete_for_var(var, ty, &effect_only_vars))
        })
        .collect::<Vec<_>>();
    vars.sort_by(|left, right| left.0.cmp(&right.0));
    vars
}

fn complete_required_substitutions(
    binding: &Binding,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Option<BTreeMap<core_ir::TypeVar, core_ir::Type>> {
    let effect_only_vars = binding_effect_only_vars(binding);
    binding_required_vars(binding)
        .into_iter()
        .map(|var| {
            let ty = substitutions.get(&var)?;
            substitution_is_complete_for_var(&var, ty, &effect_only_vars).then(|| (var, ty.clone()))
        })
        .collect()
}

fn substitution_is_complete_for_var(
    var: &core_ir::TypeVar,
    ty: &core_ir::Type,
    effect_only_vars: &BTreeSet<core_ir::TypeVar>,
) -> bool {
    if matches!(
        ty,
        core_ir::Type::Unknown | core_ir::Type::Any | core_ir::Type::Var(_)
    ) || core_type_has_vars(ty)
    {
        return false;
    }
    effect_only_vars.contains(var) || !core_type_contains_unknown(ty)
}

fn binding_substitutions_are_only_top(
    binding: &Binding,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> bool {
    let required = binding_required_vars(binding);
    !required.is_empty()
        && required.iter().all(|var| {
            substitutions
                .get(var)
                .is_some_and(|ty| matches!(ty, core_ir::Type::Unknown | core_ir::Type::Any))
        })
}

fn args_fit_without_adapter(args: &[&Expr], params: &[(core_ir::Type, core_ir::Type)]) -> bool {
    args.iter()
        .zip(params)
        .all(|(arg, (param, effect))| principal_arg_adapter(arg, param, effect).is_some())
}

fn owned_args_fit_without_adapter(
    args: &[Expr],
    params: &[(core_ir::Type, core_ir::Type)],
) -> bool {
    args.iter()
        .zip(params)
        .all(|(arg, (param, effect))| principal_arg_adapter(arg, param, effect).is_some())
}

fn handler_plan_is_supported(boundary: &HandlerCallBoundary, plan: &HandlerAdapterPlan) -> bool {
    (boundary.consumes_input_effect
        && plan
            .residual_after
            .as_ref()
            .is_none_or(|effect| effect_is_empty(effect) || plan.return_wrapper_effect.is_some()))
        || (boundary.consumes_input_effect
            && boundary.output_effect.as_ref().is_none_or(effect_is_empty)
            && plan.return_wrapper_effect.is_none())
        || (!boundary.consumes_input_effect
            && boundary.output_effect.as_ref().is_none_or(effect_is_empty)
            && plan.return_wrapper_effect.is_none())
        || (!boundary.consumes_input_effect
            && boundary.preserves_output_effect
            && plan.return_wrapper_effect.is_none())
        || (boundary.output_effect.as_ref().is_none_or(effect_is_empty)
            && plan.return_wrapper_effect.is_none()
            && plan.residual_before == plan.residual_after)
}

fn plan_only_lacks_handler_boundary(plan: &core_ir::PrincipalElaborationPlan) -> bool {
    !plan.incomplete_reasons.is_empty()
        && plan.incomplete_reasons.iter().all(|reason| {
            matches!(
                reason,
                core_ir::PrincipalElaborationIncompleteReason::HandlerBoundaryWithoutPlan
            )
        })
}

fn plan_only_lacks_open_slot_precision(plan: &core_ir::PrincipalElaborationPlan) -> bool {
    !plan.incomplete_reasons.is_empty()
        && plan.incomplete_reasons.iter().all(|reason| {
            matches!(
                reason,
                core_ir::PrincipalElaborationIncompleteReason::OpenArgType(_)
                    | core_ir::PrincipalElaborationIncompleteReason::OpenResultType
            )
        })
}

fn rebuild_apply_call(
    path: core_ir::Path,
    callee_ty: core_ir::Type,
    args: &[&Expr],
    final_ty: &RuntimeType,
) -> Option<Expr> {
    rebuild_apply_call_with_final_arg_effect(path, callee_ty, args, final_ty, None)
}

fn rebuild_apply_call_with_final_arg_effect(
    path: core_ir::Path,
    callee_ty: core_ir::Type,
    args: &[&Expr],
    final_ty: &RuntimeType,
    final_arg_effect: Option<&core_ir::Type>,
) -> Option<Expr> {
    let mut call = Expr::typed(
        ExprKind::Var(path.clone()),
        normalize_hir_function_type(RuntimeType::core(callee_ty.clone())),
    );
    let mut current = callee_ty;
    for (index, arg) in args.iter().enumerate() {
        if index > 0 {
            call = force_rebuilt_thunked_function_callee(call);
        }
        let (param, param_effect, next, ret_effect) = core_fun_parts_with_effects_exact(&current)?;
        let param_effect = final_arg_effect
            .filter(|_| index + 1 == args.len() && matches!(arg.ty, RuntimeType::Thunk { .. }))
            .unwrap_or(&param_effect);
        let arg = principal_arg_adapter(arg, &param, param_effect)?;
        let specialized_ret = runtime_type_from_core_value_and_effect(next.clone(), ret_effect);
        let ty = if index + 1 == args.len() {
            closed_rebuilt_apply_type(final_ty, &specialized_ret)
        } else {
            specialized_ret
        };
        call = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(call),
                arg: Box::new(arg),
                evidence: None,
                instantiation: None,
            },
            ty,
        );
        current = next;
    }
    Some(adapt_rebuilt_result_to_context(call, final_ty))
}

fn rebuild_apply_call_owned(
    path: core_ir::Path,
    callee_ty: core_ir::Type,
    args: Vec<Expr>,
    final_ty: &RuntimeType,
) -> Option<Expr> {
    let mut call = Expr::typed(
        ExprKind::Var(path),
        normalize_hir_function_type(RuntimeType::core(callee_ty.clone())),
    );
    let mut current = callee_ty;
    let arity = args.len();
    for (index, arg) in args.into_iter().enumerate() {
        if index > 0 {
            call = force_rebuilt_thunked_function_callee(call);
        }
        let (param, param_effect, next, ret_effect) = core_fun_parts_with_effects_exact(&current)?;
        let arg = principal_arg_adapter(&arg, &param, &param_effect)?;
        let specialized_ret = runtime_type_from_core_value_and_effect(next.clone(), ret_effect);
        let ty = if index + 1 == arity {
            closed_rebuilt_apply_type(final_ty, &specialized_ret)
        } else {
            specialized_ret
        };
        call = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(call),
                arg: Box::new(arg),
                evidence: None,
                instantiation: None,
            },
            ty,
        );
        current = next;
    }
    Some(adapt_rebuilt_result_to_context(call, final_ty))
}

fn force_rebuilt_thunked_function_callee(call: Expr) -> Expr {
    let value = match &call.ty {
        RuntimeType::Thunk { value, .. } if matches!(value.as_ref(), RuntimeType::Fun { .. }) => {
            value.as_ref().clone()
        }
        _ => return call,
    };
    Expr::typed(
        ExprKind::BindHere {
            expr: Box::new(call),
        },
        value,
    )
}

fn wrap_non_generic_binding_return_effect(
    mut binding: Binding,
    arity: usize,
    effect: core_ir::Type,
) -> Option<Binding> {
    binding.scheme.body =
        core_fun_spine_with_final_ret_effect(&binding.scheme.body, arity, &effect)?;
    binding.body = wrap_runtime_fun_spine_return_effect(binding.body, arity, &effect)?;
    Some(binding)
}

fn final_ty_effect_context(ty: &RuntimeType) -> Option<core_ir::Type> {
    let RuntimeType::Thunk { effect, value } = ty else {
        return None;
    };
    (!effect_is_empty(effect) && !matches!(value.as_ref(), RuntimeType::Fun { .. }))
        .then(|| effect.clone())
}

fn runtime_type_value_is_function(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => false,
        RuntimeType::Fun { .. } => true,
        RuntimeType::Thunk { value, .. } => runtime_type_value_is_function(value),
        RuntimeType::Core(core_ir::Type::Fun { .. }) => true,
        RuntimeType::Core(_) => false,
    }
}

fn combined_forced_argument_effect(args: &[Expr]) -> Option<core_ir::Type> {
    args.iter()
        .filter_map(forced_argument_effect)
        .reduce(merge_effects)
}

fn combined_forced_argument_effect_refs(args: &[&Expr]) -> Option<core_ir::Type> {
    args.iter()
        .filter_map(|arg| forced_argument_effect(arg))
        .reduce(merge_effects)
}

fn forced_argument_effect(arg: &Expr) -> Option<core_ir::Type> {
    let ExprKind::BindHere { expr } = &arg.kind else {
        return None;
    };
    let RuntimeType::Thunk { effect, .. } = &expr.ty else {
        return None;
    };
    (!effect_is_empty(effect)).then(|| effect.clone())
}

fn merge_effects(left: core_ir::Type, right: core_ir::Type) -> core_ir::Type {
    if effect_is_empty(&left) {
        return right;
    }
    if effect_is_empty(&right) || left == right {
        return left;
    }
    let mut items = effect_items(left);
    for item in effect_items(right) {
        if !items.iter().any(|existing| existing == &item) {
            items.push(item);
        }
    }
    if items.len() == 1 {
        items.pop().unwrap()
    } else {
        core_ir::Type::Row {
            items,
            tail: Box::new(core_ir::Type::Never),
        }
    }
}

fn effect_items(effect: core_ir::Type) -> Vec<core_ir::Type> {
    match effect {
        core_ir::Type::Never => Vec::new(),
        core_ir::Type::Row { mut items, tail } => {
            if !effect_is_empty(&tail) {
                items.push(*tail);
            }
            items
        }
        other => vec![other],
    }
}

fn core_fun_spine_with_final_ret_effect(
    ty: &core_ir::Type,
    arity: usize,
    effect: &core_ir::Type,
) -> Option<core_ir::Type> {
    if arity == 0 {
        return Some(ty.clone());
    }
    let core_ir::Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
    } = ty
    else {
        return None;
    };
    let ret = if arity == 1 {
        ret.as_ref().clone()
    } else {
        core_fun_spine_with_final_ret_effect(ret, arity - 1, effect)?
    };
    Some(core_ir::Type::Fun {
        param: param.clone(),
        param_effect: param_effect.clone(),
        ret_effect: Box::new(if arity == 1 {
            effect.clone()
        } else {
            ret_effect.as_ref().clone()
        }),
        ret: Box::new(ret),
    })
}

fn wrap_runtime_fun_spine_return_effect(
    expr: Expr,
    arity: usize,
    effect: &core_ir::Type,
) -> Option<Expr> {
    if arity == 0 {
        return Some(wrap_expr_in_effect_thunk(expr, effect));
    }
    if let Expr {
        ty: _,
        kind: ExprKind::Block {
            stmts,
            tail: Some(tail),
        },
    } = expr
    {
        let tail = wrap_runtime_fun_spine_return_effect(*tail, arity, effect)?;
        let ty = tail.ty.clone();
        return Some(Expr::typed(
            ExprKind::Block {
                stmts,
                tail: Some(Box::new(tail)),
            },
            ty,
        ));
    }
    let Expr {
        ty,
        kind:
            ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body,
            },
    } = expr
    else {
        return None;
    };
    let RuntimeType::Fun {
        param: param_ty, ..
    } = ty
    else {
        return None;
    };
    let body = wrap_runtime_fun_spine_return_effect(*body, arity - 1, effect)?;
    let ty = RuntimeType::fun(*param_ty, body.ty.clone());
    Some(Expr::typed(
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(body),
        },
        ty,
    ))
}

fn wrap_expr_in_effect_thunk(expr: Expr, effect: &core_ir::Type) -> Expr {
    if let RuntimeType::Thunk {
        effect: existing, ..
    } = &expr.ty
        && existing == effect
    {
        return expr;
    }
    let value = expr.ty.clone();
    Expr::typed(
        ExprKind::Thunk {
            effect: effect.clone(),
            value: value.clone(),
            expr: Box::new(expr),
        },
        RuntimeType::thunk(effect.clone(), value),
    )
}

fn closed_rebuilt_apply_type(final_ty: &RuntimeType, specialized_ret: &RuntimeType) -> RuntimeType {
    if (runtime_type_has_vars(final_ty)
        || runtime_type_contains_any(final_ty)
        || should_keep_specialized_runtime_type(final_ty, specialized_ret))
        && !runtime_type_has_vars(specialized_ret)
    {
        specialized_ret.clone()
    } else {
        final_ty.clone()
    }
}

fn should_keep_specialized_runtime_type(final_ty: &RuntimeType, specialized: &RuntimeType) -> bool {
    match (final_ty, specialized) {
        (RuntimeType::Core(expected), RuntimeType::Thunk { effect, value })
            if !effect_is_empty(effect) =>
        {
            let actual = runtime_core_type(value);
            actual == *expected || type_compatible(expected, &actual)
        }
        _ => false,
    }
}

fn runtime_type_from_core_value_and_effect(
    value: core_ir::Type,
    effect: core_ir::Type,
) -> RuntimeType {
    let value = normalize_hir_function_type(RuntimeType::core(value));
    if effect_is_empty(&effect) {
        value
    } else {
        RuntimeType::thunk(effect, value)
    }
}

fn principal_arg_adapter(
    arg: &Expr,
    param: &core_ir::Type,
    param_effect: &core_ir::Type,
) -> Option<Expr> {
    let actual = runtime_core_type(&arg.ty);
    if core_type_contains_unknown(param) || core_type_contains_unknown(&actual) {
        return Some(arg.clone());
    }
    if actual != *param && !type_compatible(param, &actual) {
        return None;
    }
    if matches!(
        param,
        core_ir::Type::Unknown | core_ir::Type::Any | core_ir::Type::Var(_)
    ) && matches!(arg.ty, RuntimeType::Thunk { .. })
        && erased_param_should_preserve_thunk_arg(arg)
    {
        return Some(arg.clone());
    }
    let param_requires_thunk = principal_param_effect_requires_thunk(param_effect);
    match (&arg.ty, param_requires_thunk) {
        (RuntimeType::Thunk { effect, value }, false) if !effect_is_empty(effect) => {
            Some(Expr::typed(
                ExprKind::BindHere {
                    expr: Box::new(arg.clone()),
                },
                value.as_ref().clone(),
            ))
        }
        (
            RuntimeType::Thunk {
                effect: actual_effect,
                value: _,
            },
            true,
        ) => {
            if actual_effect == param_effect {
                return Some(arg.clone());
            }
            let value = normalize_hir_function_type(RuntimeType::core(param.clone()));
            if let Some(thunk) = nested_thunk_with_effect(arg, param_effect, &value) {
                return Some(thunk);
            }
            if let Some(thunk) = retag_nested_imprecise_thunk_effect(arg, param_effect, &value) {
                return Some(thunk);
            }
            let body = force_expr_to_runtime_value(arg.clone(), &value)?;
            Some(Expr::typed(
                ExprKind::Thunk {
                    effect: param_effect.clone(),
                    value: value.clone(),
                    expr: Box::new(body),
                },
                RuntimeType::thunk(param_effect.clone(), value),
            ))
        }
        (_, true) => {
            let value = arg.ty.clone();
            if let Some(thunk) = retag_nested_imprecise_thunk_effect(arg, param_effect, &value) {
                return Some(thunk);
            }
            Some(Expr::typed(
                ExprKind::Thunk {
                    effect: param_effect.clone(),
                    value: value.clone(),
                    expr: Box::new(arg.clone()),
                },
                RuntimeType::thunk(param_effect.clone(), value),
            ))
        }
        (_, false) => Some(arg.clone()),
    }
}

fn retag_nested_imprecise_thunk_effect(
    expr: &Expr,
    expected_effect: &core_ir::Type,
    expected_value: &RuntimeType,
) -> Option<Expr> {
    if let Some(retagged) = retag_imprecise_thunk_effect(expr, expected_effect, expected_value) {
        return Some(retagged);
    }
    match &expr.kind {
        ExprKind::Thunk { expr, .. } | ExprKind::BindHere { expr } => {
            retag_nested_imprecise_thunk_effect(expr, expected_effect, expected_value)
        }
        _ => None,
    }
}

fn retag_imprecise_thunk_effect(
    expr: &Expr,
    expected_effect: &core_ir::Type,
    expected_value: &RuntimeType,
) -> Option<Expr> {
    let RuntimeType::Thunk { effect, value } = &expr.ty else {
        return None;
    };
    if !core_type_is_imprecise_runtime_slot(effect)
        || effect_paths(expected_effect).is_empty()
        || runtime_core_type(value) != runtime_core_type(expected_value)
    {
        return None;
    }
    let ExprKind::Thunk { expr: body, .. } = &expr.kind else {
        return None;
    };
    Some(Expr::typed(
        ExprKind::Thunk {
            effect: expected_effect.clone(),
            value: expected_value.clone(),
            expr: body.clone(),
        },
        RuntimeType::thunk(expected_effect.clone(), expected_value.clone()),
    ))
}

fn nested_thunk_with_effect(
    expr: &Expr,
    expected_effect: &core_ir::Type,
    expected_value: &RuntimeType,
) -> Option<Expr> {
    if let RuntimeType::Thunk { effect, value } = &expr.ty
        && effect == expected_effect
        && runtime_core_type(value) == runtime_core_type(expected_value)
    {
        return Some(expr.clone());
    }
    match &expr.kind {
        ExprKind::Thunk { expr, .. } | ExprKind::BindHere { expr } => {
            nested_thunk_with_effect(expr, expected_effect, expected_value)
        }
        _ => None,
    }
}

fn force_expr_to_runtime_value(mut expr: Expr, expected: &RuntimeType) -> Option<Expr> {
    for _ in 0..8 {
        if &expr.ty == expected {
            return Some(expr);
        }
        let RuntimeType::Thunk { value, .. } = &expr.ty else {
            return None;
        };
        let value = value.as_ref().clone();
        if runtime_core_type(&value) != runtime_core_type(expected) {
            return None;
        }
        expr = Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(expr),
            },
            value,
        );
    }
    None
}

fn principal_param_effect_requires_thunk(effect: &core_ir::Type) -> bool {
    !effect_is_empty(effect) && !effect_paths(effect).is_empty()
}

fn erased_param_should_preserve_thunk_arg(arg: &Expr) -> bool {
    match &arg.kind {
        ExprKind::Var(path) => path.segments.len() == 1,
        ExprKind::Apply { callee, .. } => local_apply_head(callee),
        _ => false,
    }
}

fn local_apply_head(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Var(path) => path.segments.len() == 1,
        ExprKind::Apply { callee, .. } => local_apply_head(callee),
        ExprKind::BindHere { expr } => local_apply_head(expr),
        _ => false,
    }
}

fn adapt_rebuilt_result_to_context(call: Expr, final_ty: &RuntimeType) -> Expr {
    match (&call.ty, final_ty) {
        (RuntimeType::Thunk { effect, value }, RuntimeType::Core(expected))
            if !effect_is_empty(effect) =>
        {
            let actual = runtime_core_type(value);
            if actual == *expected || type_compatible(expected, &actual) {
                return Expr::typed(
                    ExprKind::BindHere {
                        expr: Box::new(call),
                    },
                    final_ty.clone(),
                );
            }
            call
        }
        _ => call,
    }
}

fn runtime_type_has_vars(ty: &RuntimeType) -> bool {
    let mut vars = BTreeSet::new();
    collect_hir_type_vars(ty, &mut vars);
    !vars.is_empty()
}

fn runtime_type_shape_usable(ty: &RuntimeType) -> bool {
    !runtime_type_has_vars(ty) && !runtime_type_contains_any(ty)
}

fn runtime_type_contains_any(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => true,
        RuntimeType::Core(ty) => core_type_contains_any(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_type_contains_any(param) || runtime_type_contains_any(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            core_type_contains_any(effect) || runtime_type_contains_any(value)
        }
    }
}

fn core_type_contains_any(ty: &core_ir::Type) -> bool {
    match ty {
        core_ir::Type::Any => true,
        core_ir::Type::Unknown | core_ir::Type::Never | core_ir::Type::Var(_) => false,
        core_ir::Type::Named { args, .. } => args.iter().any(core_type_arg_contains_any),
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_contains_any(param)
                || core_type_contains_any(param_effect)
                || core_type_contains_any(ret_effect)
                || core_type_contains_any(ret)
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            items.iter().any(core_type_contains_any)
        }
        core_ir::Type::Row { items, tail } => {
            items.iter().any(core_type_contains_any) || core_type_contains_any(tail)
        }
        core_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_type_contains_any(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        core_type_contains_any(ty)
                    }
                })
        }
        core_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(core_type_contains_any))
                || variant
                    .tail
                    .as_ref()
                    .is_some_and(|tail| core_type_contains_any(tail))
        }
        core_ir::Type::Recursive { body, .. } => core_type_contains_any(body),
    }
}

fn core_type_arg_contains_any(arg: &core_ir::TypeArg) -> bool {
    match arg {
        core_ir::TypeArg::Type(ty) => core_type_contains_any(ty),
        core_ir::TypeArg::Bounds(bounds) => {
            bounds.lower.as_deref().is_some_and(core_type_contains_any)
                || bounds.upper.as_deref().is_some_and(core_type_contains_any)
        }
    }
}

fn core_fun_spine_exact(
    ty: &core_ir::Type,
    arity: usize,
) -> Option<(Vec<core_ir::Type>, core_ir::Type)> {
    let mut params = Vec::with_capacity(arity);
    let mut current = ty.clone();
    for _ in 0..arity {
        let (param, ret) = core_fun_parts_exact(&current)?;
        params.push(param);
        current = ret;
    }
    Some((params, current))
}

fn core_fun_spine_parts_exact(
    ty: &core_ir::Type,
    arity: usize,
) -> Option<(
    Vec<(core_ir::Type, core_ir::Type)>,
    core_ir::Type,
    core_ir::Type,
)> {
    let mut params = Vec::with_capacity(arity);
    let mut current = ty.clone();
    let mut current_ret_effect = core_ir::Type::Never;
    for _ in 0..arity {
        let core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } = current
        else {
            return None;
        };
        params.push((*param, *param_effect));
        current_ret_effect = *ret_effect;
        current = *ret;
    }
    Some((params, current, current_ret_effect))
}

fn core_fun_arity(ty: &core_ir::Type) -> usize {
    let mut arity = 0;
    let mut current = ty;
    while let core_ir::Type::Fun { ret, .. } = current {
        arity += 1;
        current = ret;
    }
    arity
}

fn core_fun_parts_with_effects_exact(
    ty: &core_ir::Type,
) -> Option<(core_ir::Type, core_ir::Type, core_ir::Type, core_ir::Type)> {
    let core_ir::Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
    } = ty
    else {
        return None;
    };
    Some((
        param.as_ref().clone(),
        param_effect.as_ref().clone(),
        ret.as_ref().clone(),
        ret_effect.as_ref().clone(),
    ))
}

fn core_fun_parts_exact(ty: &core_ir::Type) -> Option<(core_ir::Type, core_ir::Type)> {
    let core_ir::Type::Fun { param, ret, .. } = ty else {
        return None;
    };
    Some((param.as_ref().clone(), ret.as_ref().clone()))
}

fn runtime_value_and_effect(ty: &RuntimeType) -> (core_ir::Type, core_ir::Type) {
    match ty {
        RuntimeType::Thunk { effect, value } => (runtime_core_type(value), effect.clone()),
        other => (runtime_core_type(other), core_ir::Type::Never),
    }
}

fn runtime_effect_row_candidate(ty: &core_ir::Type) -> Option<&core_ir::Type> {
    match ty {
        core_ir::Type::Row { .. } => Some(ty),
        _ => None,
    }
}

fn debug_principal_unify_runtime_projection(
    slot: &str,
    target: Option<&core_ir::Path>,
    template_value: &core_ir::Type,
    actual_value: &core_ir::Type,
    template_effect: &core_ir::Type,
    actual_effect: &core_ir::Type,
) {
    if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_none() {
        return;
    }
    let target = target
        .map(canonical_path)
        .unwrap_or_else(|| "<unknown>".to_string());
    eprintln!(
        "principal-unify runtime-slot {target} {slot}: value {template_value:?} <= {actual_value:?}; effect {template_effect:?} <= {actual_effect:?}"
    );
}

fn debug_principal_unify_skip(target: &core_ir::Path, reason: &str) {
    if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_none() {
        return;
    }
    eprintln!(
        "principal-unify skip {} reason={reason}",
        canonical_path(target)
    );
}

fn debug_principal_unify_handler_plan(
    target: &core_ir::Path,
    boundary: &HandlerCallBoundary,
    plan: &HandlerAdapterPlan,
) {
    if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_none() {
        return;
    }
    eprintln!(
        "principal-unify handler-plan {} consumes={:?} input_effect={:?} output_effect={:?} consumes_input={} preserves_output={} residual_before={:?} residual_after={:?} return_wrapper={:?}",
        canonical_path(target),
        boundary.consumes,
        boundary.input_effect,
        boundary.output_effect,
        boundary.consumes_input_effect,
        boundary.preserves_output_effect,
        plan.residual_before,
        plan.residual_after,
        plan.return_wrapper_effect
    );
}

fn debug_principal_unify_projection_outcome(
    outcome: &str,
    target: Option<&core_ir::Path>,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &BTreeSet<core_ir::TypeVar>,
) {
    if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_none() {
        return;
    }
    let target = target
        .map(canonical_path)
        .unwrap_or_else(|| "<unknown>".to_string());
    eprintln!(
        "principal-unify runtime-slot {target} {outcome}: substitutions={substitutions:?}; conflicts={conflicts:?}"
    );
}

fn debug_principal_unify_emit(
    original: &core_ir::Path,
    path: &core_ir::Path,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_none() {
        return;
    }
    eprintln!(
        "principal-unify emit {} <= {} substitutions={substitutions:?}",
        canonical_path(path),
        canonical_path(original)
    );
}

fn debug_principal_unify_rewrite(original: &core_ir::Path, path: &core_ir::Path) {
    if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_none() {
        return;
    }
    eprintln!(
        "principal-unify rewrite {} -> {}",
        canonical_path(original),
        canonical_path(path)
    );
}

fn debug_principal_unify_contextual_candidates(
    target: &core_ir::Path,
    matches: &[(&core_ir::Path, &core_ir::Type, usize, usize)],
) {
    if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY_CONTEXTUAL").is_none() {
        return;
    }
    let rendered = matches
        .iter()
        .map(|(path, _, context, precision)| {
            format!("{}:{context}/{precision}", canonical_path(path))
        })
        .collect::<Vec<_>>()
        .join(", ");
    eprintln!(
        "principal-unify contextual {} remaining={} candidates=[{}]",
        canonical_path(target),
        matches.len(),
        rendered
    );
}

fn debug_principal_unify_active(
    target: &core_ir::Path,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_none() {
        return;
    }
    eprintln!(
        "principal-unify active {} substitutions={substitutions:?}",
        canonical_path(target)
    );
}

fn debug_principal_unify_normalized_plan(plan: &core_ir::PrincipalElaborationPlan) {
    if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_none() {
        return;
    }
    let target = plan
        .target
        .as_ref()
        .map(canonical_path)
        .unwrap_or_else(|| "<unknown>".to_string());
    eprintln!(
        "principal-unify normalized {target}: complete={} substitutions={:?} reasons={:?}",
        plan.complete, plan.substitutions, plan.incomplete_reasons
    );
}

fn debug_principal_unify_role_candidates<'a>(
    target: &core_ir::Path,
    receiver_ty: &core_ir::Type,
    candidates: impl IntoIterator<Item = &'a core_ir::Path>,
) {
    if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_none() {
        return;
    }
    let candidates = candidates
        .into_iter()
        .map(canonical_path)
        .collect::<Vec<_>>();
    eprintln!(
        "principal-unify role-candidates {} receiver={receiver_ty:?} candidates={candidates:?}",
        canonical_path(target)
    );
}

fn debug_principal_unify_role_ambiguous<'a>(
    target: &core_ir::Path,
    receiver_ty: &core_ir::Type,
    matches: impl IntoIterator<
        Item = (
            &'a core_ir::Path,
            &'a BTreeMap<core_ir::TypeVar, core_ir::Type>,
        ),
    >,
) {
    if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_none() {
        return;
    }
    let matches = matches
        .into_iter()
        .map(|(path, substitutions)| format!("{} {substitutions:?}", canonical_path(path)))
        .collect::<Vec<_>>();
    eprintln!(
        "principal-unify role-ambiguous {} receiver={receiver_ty:?} matches={matches:?}",
        canonical_path(target)
    );
}

fn debug_principal_unify_role_candidate_rejected(
    candidate: &core_ir::Path,
    reason: &str,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
    missing: &[core_ir::TypeVar],
) {
    if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_none() {
        return;
    }
    eprintln!(
        "principal-unify role-reject {} reason={reason} substitutions={substitutions:?} missing={missing:?}",
        canonical_path(candidate)
    );
}

fn debug_principal_unify_local_value(name: &core_ir::Name, ty: &RuntimeType) {
    if std::env::var_os("YULANG_DEBUG_PRINCIPAL_UNIFY").is_none() {
        return;
    }
    eprintln!("principal-unify local-value {name:?} = {ty:?}");
}

fn runtime_function_param_type(ty: &RuntimeType) -> Option<core_ir::Type> {
    match ty {
        RuntimeType::Core(core_ir::Type::Fun { param, .. }) => Some(param.as_ref().clone()),
        RuntimeType::Fun { param, .. } => Some(runtime_core_type(param)),
        RuntimeType::Unknown | RuntimeType::Thunk { .. } | RuntimeType::Core(_) => None,
    }
}

fn runtime_lambda_return_value_context(ty: &RuntimeType) -> Option<core_ir::TypeBounds> {
    let RuntimeType::Fun { ret, .. } = ty else {
        return None;
    };
    Some(core_ir::TypeBounds::exact(runtime_core_type(ret)))
}

fn runtime_function_type_with_param(ty: RuntimeType, param: core_ir::Type) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { ret, .. } => Some(RuntimeType::Fun {
            param: Box::new(RuntimeType::core(param)),
            ret,
        }),
        RuntimeType::Thunk { effect, value } => runtime_function_type_with_param(*value, param)
            .map(|value| RuntimeType::thunk(effect, value)),
        RuntimeType::Core(core_ir::Type::Fun {
            param_effect,
            ret_effect,
            ret,
            ..
        }) => Some(normalize_hir_function_type(RuntimeType::core(
            core_ir::Type::Fun {
                param: Box::new(param),
                param_effect,
                ret_effect,
                ret,
            },
        ))),
        RuntimeType::Unknown | RuntimeType::Core(_) => None,
    }
}

fn runtime_context_function_type(bounds: Option<&core_ir::TypeBounds>) -> Option<RuntimeType> {
    let ty = closed_type_from_bounds(bounds)?;
    let ty = normalize_hir_function_type(RuntimeType::core(ty));
    matches!(ty, RuntimeType::Fun { .. }).then_some(ty)
}

fn closed_runtime_value_type(ty: &RuntimeType) -> Option<core_ir::Type> {
    let ty = runtime_core_type(ty);
    closed_slot_type_usable(&ty, false).then_some(ty)
}

fn runtime_function_param_slot(ty: &RuntimeType) -> Option<(core_ir::Type, core_ir::Type)> {
    match ty {
        RuntimeType::Core(core_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) => Some((param.as_ref().clone(), param_effect.as_ref().clone())),
        RuntimeType::Fun { param, .. } => {
            let (value, effect) = runtime_value_and_effect(param);
            Some((value, effect))
        }
        RuntimeType::Unknown | RuntimeType::Thunk { .. } | RuntimeType::Core(_) => None,
    }
}

fn adapt_apply_argument_from_callee(expr: Expr) -> Expr {
    let Expr { ty, kind } = expr;
    let ExprKind::Apply {
        callee,
        arg,
        evidence,
        instantiation,
    } = kind
    else {
        return Expr::typed(kind, ty);
    };
    let Some((param, param_effect)) = runtime_function_param_slot(&callee.ty)
        .or_else(|| forced_callee_function_param_slot(&callee))
    else {
        if let Some(arg) = force_thunk_arg_after_forced_callee(&callee, &arg) {
            return Expr::typed(
                ExprKind::Apply {
                    callee,
                    arg: Box::new(arg),
                    evidence,
                    instantiation,
                },
                ty,
            );
        }
        return Expr::typed(
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            },
            ty,
        );
    };
    let Some(arg) = principal_arg_adapter(&arg, &param, &param_effect) else {
        return Expr::typed(
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            },
            ty,
        );
    };
    Expr::typed(
        ExprKind::Apply {
            callee,
            arg: Box::new(arg),
            evidence,
            instantiation,
        },
        ty,
    )
}

fn lambda_param_runtime_type(ty: &RuntimeType) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { param, .. } => Some(param.as_ref().clone()),
        RuntimeType::Core(core_ir::Type::Fun { param, .. }) => {
            Some(RuntimeType::core(*param.clone()))
        }
        _ => None,
    }
}

fn adapt_apply_result_from_evidence(
    expr: Expr,
    result_context: Option<&core_ir::TypeBounds>,
) -> Expr {
    let Some(expected) = closed_type_from_bounds(result_context) else {
        return expr;
    };
    let Expr { ty, kind } = expr;
    if matches!(ty, RuntimeType::Thunk { .. }) {
        return Expr::typed(kind, ty);
    }
    let ExprKind::Apply {
        callee,
        arg,
        evidence,
        instantiation,
    } = kind
    else {
        return Expr::typed(kind, ty);
    };
    let Some(effect) = evidence
        .as_ref()
        .and_then(apply_evidence_return_effect)
        .filter(|effect| !effect_is_empty(effect))
    else {
        return Expr::typed(
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            },
            ty,
        );
    };
    let actual = runtime_core_type(&ty);
    if actual != expected && !type_compatible(&expected, &actual) {
        return Expr::typed(
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            },
            ty,
        );
    }
    let inner_ty = RuntimeType::thunk(effect, RuntimeType::core(expected));
    let inner = Expr::typed(
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        },
        inner_ty,
    );
    Expr::typed(
        ExprKind::BindHere {
            expr: Box::new(inner),
        },
        ty,
    )
}

fn unwrap_handler_body_bind_here(body: Expr, handler: &crate::ir::HandleEffect) -> Expr {
    let Expr {
        ty,
        kind: ExprKind::BindHere { expr },
    } = body
    else {
        return body;
    };
    let RuntimeType::Thunk { effect, .. } = &expr.ty else {
        return Expr::typed(ExprKind::BindHere { expr }, ty);
    };
    let paths = effect_paths(effect);
    if paths.iter().any(|path| {
        handler
            .consumes
            .iter()
            .any(|consumed| effect_paths_match(consumed, path))
    }) {
        return *expr;
    }
    Expr::typed(ExprKind::BindHere { expr }, ty)
}

fn ensure_effectful_handler_body_thunk(body: Expr, handler: &crate::ir::HandleEffect) -> Expr {
    if handler.consumes.is_empty() || matches!(body.ty, RuntimeType::Thunk { .. }) {
        return body;
    }
    let effect = handler
        .residual_before
        .clone()
        .filter(|effect| !effect_is_empty(effect))
        .unwrap_or_else(|| core_ir::Type::Row {
            items: handler
                .consumes
                .iter()
                .cloned()
                .map(|path| core_ir::Type::Named {
                    path,
                    args: Vec::new(),
                })
                .collect(),
            tail: Box::new(core_ir::Type::Never),
        });
    let value = body.ty.clone();
    Expr::typed(
        ExprKind::Thunk {
            effect: effect.clone(),
            value: value.clone(),
            expr: Box::new(body),
        },
        RuntimeType::thunk(effect, value),
    )
}

fn apply_evidence_return_effect(evidence: &core_ir::ApplyEvidence) -> Option<core_ir::Type> {
    closed_type_from_bounds(evidence.expected_callee.as_ref())
        .or_else(|| closed_type_from_bounds(Some(&evidence.callee)))
        .and_then(|ty| match ty {
            core_ir::Type::Fun { ret_effect, .. } => Some(*ret_effect),
            _ => None,
        })
}

fn apply_evidence_param_effect(evidence: &core_ir::ApplyEvidence) -> Option<core_ir::Type> {
    closed_type_from_bounds(evidence.expected_callee.as_ref())
        .or_else(|| closed_type_from_bounds(Some(&evidence.callee)))
        .and_then(|ty| match ty {
            core_ir::Type::Fun { param_effect, .. } => Some(*param_effect),
            _ => None,
        })
}

fn forced_callee_function_param_slot(callee: &Expr) -> Option<(core_ir::Type, core_ir::Type)> {
    let ExprKind::BindHere { expr } = &callee.kind else {
        return None;
    };
    let RuntimeType::Thunk { value, .. } = &expr.ty else {
        return None;
    };
    runtime_function_param_slot(value)
}

fn force_thunk_arg_after_forced_callee(callee: &Expr, arg: &Expr) -> Option<Expr> {
    if !matches!(callee.kind, ExprKind::BindHere { .. }) {
        return None;
    }
    let RuntimeType::Thunk { effect, value } = &arg.ty else {
        return None;
    };
    if effect_is_empty(effect) {
        return None;
    }
    Some(Expr::typed(
        ExprKind::BindHere {
            expr: Box::new(arg.clone()),
        },
        value.as_ref().clone(),
    ))
}

fn principal_plan_result_closed_type(
    result: &core_ir::PrincipalElaborationResult,
) -> Option<core_ir::Type> {
    result
        .expected_runtime
        .clone()
        .or_else(|| closed_type_from_bounds(result.contextual.as_ref()))
        .or_else(|| closed_type_from_bounds(Some(&result.intrinsic)))
}

fn principal_plan_arg_closed_type(
    arg: &core_ir::PrincipalElaborationArg,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Option<core_ir::Type> {
    choose_precise_closed_type([
        arg.expected_runtime
            .as_ref()
            .map(|ty| substitute_type(ty, substitutions))
            .filter(|ty| closed_slot_type_usable(ty, false)),
        arg.contextual
            .as_ref()
            .and_then(|bounds| substituted_closed_type_from_bounds(bounds, substitutions)),
        substituted_closed_type_from_bounds(&arg.intrinsic, substitutions),
    ])
}

fn principal_plan_result_closed_type_with_substitutions(
    result: &core_ir::PrincipalElaborationResult,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Option<core_ir::Type> {
    choose_precise_closed_type([
        result
            .expected_runtime
            .as_ref()
            .map(|ty| substitute_type(ty, substitutions))
            .filter(|ty| closed_slot_type_usable(ty, false)),
        result
            .contextual
            .as_ref()
            .and_then(|bounds| substituted_closed_type_from_bounds(bounds, substitutions)),
        substituted_closed_type_from_bounds(&result.intrinsic, substitutions),
    ])
}

fn choose_precise_closed_type(
    candidates: impl IntoIterator<Item = Option<core_ir::Type>>,
) -> Option<core_ir::Type> {
    let mut fallback = None;
    for candidate in candidates.into_iter().flatten() {
        if matches!(candidate, core_ir::Type::Unknown | core_ir::Type::Any) {
            fallback.get_or_insert(candidate);
        } else {
            return Some(candidate);
        }
    }
    fallback
}

fn substituted_closed_type_from_bounds(
    bounds: &core_ir::TypeBounds,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Option<core_ir::Type> {
    let bounds = substitute_bounds(bounds.clone(), substitutions);
    closed_type_from_bounds(Some(&bounds))
}

fn closed_type_from_bounds(bounds: Option<&core_ir::TypeBounds>) -> Option<core_ir::Type> {
    let bounds = bounds?;
    let lower = bounds
        .lower
        .as_deref()
        .cloned()
        .map(collapse_repeated_top_choice_type);
    let upper = bounds
        .upper
        .as_deref()
        .cloned()
        .map(collapse_repeated_top_choice_type);
    let choice = match (lower, upper) {
        (Some(lower), Some(upper)) if lower == upper => lower,
        (Some(ty), None) | (None, Some(ty)) => ty,
        _ => return None,
    };
    closed_slot_type_usable(&choice, false).then_some(choice)
}

fn refresh_lambda_body_local_types(
    ty: RuntimeType,
    param: core_ir::Name,
    param_effect_annotation: Option<core_ir::ParamEffectAnnotation>,
    param_function_allowed_effects: Option<core_ir::FunctionSigAllowedEffects>,
    body: Expr,
) -> Expr {
    let refreshed = refresh_local_expr_types(Expr {
        ty,
        kind: ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(body),
        },
    });
    let ExprKind::Lambda { body, .. } = refreshed.kind else {
        return refreshed;
    };
    *body
}

fn closed_slot_type_usable(ty: &core_ir::Type, allow_never: bool) -> bool {
    if matches!(ty, core_ir::Type::Unknown) || (!allow_never && core_type_contains_unknown(ty)) {
        return false;
    }
    if core_type_has_vars(ty) {
        return false;
    }
    allow_never || !matches!(ty, core_ir::Type::Never)
}

fn principal_unify_role_impls(module: &Module) -> HashMap<core_ir::Name, Vec<Binding>> {
    let mut out: HashMap<core_ir::Name, Vec<Binding>> = HashMap::new();
    for binding in &module.bindings {
        if !is_impl_method_path(&binding.name) {
            continue;
        }
        let Some(method) = binding.name.segments.last() else {
            continue;
        };
        out.entry(method.clone()).or_default().push(binding.clone());
    }
    for candidates in out.values_mut() {
        candidates.sort_by_key(|candidate| canonical_path(&candidate.name));
    }
    out
}

fn role_impl_closed_substitutions(
    binding: &Binding,
    spine: &PrincipalUnifyApplySpine<'_>,
    result_ty: &RuntimeType,
    ambient_substitutions: Option<&BTreeMap<core_ir::TypeVar, core_ir::Type>>,
) -> Option<BTreeMap<core_ir::TypeVar, core_ir::Type>> {
    let required_vars = binding_required_vars(binding);
    let Some((params, ret, ret_effect)) =
        core_fun_spine_parts_exact(&binding.scheme.body, spine.args.len())
    else {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "non-function-role-impl",
            &BTreeMap::new(),
            &missing_required_vars(binding, &BTreeMap::new()),
        );
        return None;
    };
    let (receiver_param, _) = params.first()?;
    let Some(first_arg) = spine.args.first() else {
        return None;
    };
    let first_evidence = spine.evidences.first().copied().flatten();
    let receiver_types =
        role_impl_arg_projection_types(first_arg, first_evidence, ambient_substitutions);
    let receiver_ty = receiver_types
        .iter()
        .find(|ty| !matches!(ty, core_ir::Type::Unknown | core_ir::Type::Any))
        .cloned()
        .unwrap_or_else(|| {
            ambient_substitutions
                .map(|substitutions| {
                    substitute_type(&runtime_core_type(&first_arg.ty), substitutions)
                })
                .unwrap_or_else(|| runtime_core_type(&first_arg.ty))
        });
    let mut substitutions = BTreeMap::new();
    let mut conflicts = BTreeSet::new();
    for (index, (arg, (param, _param_effect))) in spine.args.iter().zip(&params).enumerate() {
        let evidence = spine.evidences.get(index).copied().flatten();
        for actual in role_impl_arg_projection_types(arg, evidence, ambient_substitutions) {
            project_closed_value_substitutions_from_type(
                param,
                &actual,
                &required_vars,
                &mut substitutions,
                &mut conflicts,
                64,
            );
        }
    }
    for actual_ret in role_impl_result_projection_types(spine, result_ty, ambient_substitutions) {
        project_closed_value_substitutions_from_type(
            &ret,
            &actual_ret,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
            64,
        );
    }
    if matches!(result_ty, RuntimeType::Thunk { .. }) {
        let (_actual_ret, actual_ret_effect) = runtime_value_and_effect(result_ty);
        let actual_ret_effect = ambient_substitutions
            .map(|substitutions| substitute_type(&actual_ret_effect, substitutions))
            .unwrap_or(actual_ret_effect);
        project_closed_substitutions_from_type(
            &ret_effect,
            &actual_ret_effect,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
            true,
            64,
        );
    }
    let effect_only_vars = binding_effect_only_vars(binding);
    if conflicts.iter().any(|var| !effect_only_vars.contains(var)) {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "conflict",
            &substitutions,
            &missing_required_vars(binding, &substitutions),
        );
        return None;
    } else if !conflicts.is_empty() {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "effect-conflict-kept",
            &substitutions,
            &missing_required_vars(binding, &substitutions),
        );
    }
    let substituted_receiver = substitute_type(receiver_param, &substitutions);
    if !receiver_type_matches_impl(&substituted_receiver, &receiver_ty)
        && !matches!(receiver_ty, core_ir::Type::Unknown | core_ir::Type::Any)
    {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "receiver-mismatch",
            &substitutions,
            &missing_required_vars(binding, &substitutions),
        );
        return None;
    }
    if !role_impl_closed_slots_match(
        &params,
        &ret,
        spine,
        result_ty,
        &substitutions,
        ambient_substitutions,
    ) {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "slot-mismatch",
            &substitutions,
            &missing_required_vars(binding, &substitutions),
        );
        return None;
    }
    let completed = complete_required_substitutions(binding, &substitutions);
    if completed.is_none() {
        debug_principal_unify_role_candidate_rejected(
            &binding.name,
            "incomplete-substitution",
            &substitutions,
            &missing_required_vars(binding, &substitutions),
        );
    }
    completed
}

fn role_impl_receiver_dispatch_substitutions(
    binding: &Binding,
    spine: &PrincipalUnifyApplySpine<'_>,
    ambient_substitutions: Option<&BTreeMap<core_ir::TypeVar, core_ir::Type>>,
) -> Option<BTreeMap<core_ir::TypeVar, core_ir::Type>> {
    let required_vars = binding_required_vars(binding);
    let Some((params, _ret, _ret_effect)) =
        core_fun_spine_parts_exact(&binding.scheme.body, spine.args.len())
    else {
        return None;
    };
    let (receiver_param, _) = params.first()?;
    let first_arg = spine.args.first()?;
    let first_evidence = spine.evidences.first().copied().flatten();
    let receiver_types =
        role_impl_arg_projection_types(first_arg, first_evidence, ambient_substitutions);
    let mut substitutions = BTreeMap::new();
    let mut conflicts = BTreeSet::new();
    for receiver_ty in &receiver_types {
        project_closed_value_substitutions_from_type(
            receiver_param,
            receiver_ty,
            &required_vars,
            &mut substitutions,
            &mut conflicts,
            64,
        );
    }
    if !conflicts.is_empty() {
        return None;
    }
    let substituted_receiver = substitute_type(receiver_param, &substitutions);
    let receiver_matches = receiver_types
        .iter()
        .filter(|receiver_ty| !matches!(receiver_ty, core_ir::Type::Unknown | core_ir::Type::Any))
        .any(|receiver_ty| receiver_type_matches_impl(&substituted_receiver, receiver_ty));
    receiver_matches.then_some(substitutions)
}

fn role_impl_closed_slots_match(
    params: &[(core_ir::Type, core_ir::Type)],
    ret: &core_ir::Type,
    spine: &PrincipalUnifyApplySpine<'_>,
    result_ty: &RuntimeType,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
    ambient_substitutions: Option<&BTreeMap<core_ir::TypeVar, core_ir::Type>>,
) -> bool {
    for (index, (arg, (param, _param_effect))) in spine.args.iter().zip(params).enumerate() {
        let evidence = spine.evidences.get(index).copied().flatten();
        let actuals = role_impl_arg_projection_types(arg, evidence, ambient_substitutions);
        if actuals
            .iter()
            .all(|actual| matches!(actual, core_ir::Type::Unknown | core_ir::Type::Any))
        {
            continue;
        }
        let param = substitute_type(param, substitutions);
        if actuals
            .iter()
            .filter(|actual| !matches!(actual, core_ir::Type::Unknown | core_ir::Type::Any))
            .any(|actual| {
                if index == 0 {
                    !receiver_type_matches_impl(&param, actual)
                } else {
                    !type_compatible(&param, actual)
                }
            })
        {
            return false;
        }
    }
    let actual_rets = role_impl_result_projection_types(spine, result_ty, ambient_substitutions);
    if actual_rets
        .iter()
        .all(|actual_ret| matches!(actual_ret, core_ir::Type::Unknown | core_ir::Type::Any))
    {
        return true;
    }
    let ret = substitute_type(ret, substitutions);
    actual_rets
        .iter()
        .filter(|actual_ret| !matches!(actual_ret, core_ir::Type::Unknown | core_ir::Type::Any))
        .all(|actual_ret| type_compatible(&ret, actual_ret))
}

fn role_impl_match_score(
    binding: &Binding,
    spine: &PrincipalUnifyApplySpine<'_>,
    result_ty: &RuntimeType,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
    ambient_substitutions: Option<&BTreeMap<core_ir::TypeVar, core_ir::Type>>,
) -> usize {
    let Some((params, ret, _ret_effect)) =
        core_fun_spine_parts_exact(&binding.scheme.body, spine.args.len())
    else {
        return 0;
    };
    let mut score = 0;
    for (index, (arg, (param, _param_effect))) in spine.args.iter().zip(params).enumerate() {
        let evidence = spine.evidences.get(index).copied().flatten();
        let param = substitute_type(&param, substitutions);
        score += role_impl_arg_projection_types(arg, evidence, ambient_substitutions)
            .iter()
            .filter(|actual| !matches!(actual, core_ir::Type::Unknown | core_ir::Type::Any))
            .map(|actual| role_impl_slot_score(&param, actual))
            .max()
            .unwrap_or(0);
    }
    let ret = substitute_type(&ret, substitutions);
    score += role_impl_result_projection_types(spine, result_ty, ambient_substitutions)
        .iter()
        .filter(|actual_ret| !matches!(actual_ret, core_ir::Type::Unknown | core_ir::Type::Any))
        .map(|actual_ret| role_impl_slot_score(&ret, actual_ret))
        .max()
        .unwrap_or(0);
    score
}

fn role_impl_arg_projection_types(
    arg: &Expr,
    evidence: Option<&core_ir::ApplyEvidence>,
    ambient_substitutions: Option<&BTreeMap<core_ir::TypeVar, core_ir::Type>>,
) -> Vec<core_ir::Type> {
    let mut out = Vec::new();
    push_role_impl_expr_projection_types(&mut out, arg, ambient_substitutions);
    if let Some(evidence) = evidence {
        push_role_impl_bounds_projection_type(&mut out, &evidence.arg, ambient_substitutions);
        if let Some(expected_arg) = &evidence.expected_arg {
            push_role_impl_bounds_projection_type(&mut out, expected_arg, ambient_substitutions);
        }
    }
    out
}

fn push_role_impl_expr_projection_types(
    out: &mut Vec<core_ir::Type>,
    expr: &Expr,
    ambient_substitutions: Option<&BTreeMap<core_ir::TypeVar, core_ir::Type>>,
) {
    let (actual, _effect) = runtime_value_and_effect(&expr.ty);
    push_role_impl_projection_type(out, actual, ambient_substitutions);
    match &expr.kind {
        ExprKind::BindHere { expr } => {
            if let RuntimeType::Thunk { value, .. } = &expr.ty {
                push_role_impl_projection_type(
                    out,
                    runtime_core_type(value),
                    ambient_substitutions,
                );
            }
            push_role_impl_expr_projection_types(out, expr, ambient_substitutions);
        }
        ExprKind::Coerce { expr, to, .. } => {
            push_role_impl_projection_type(out, to.clone(), ambient_substitutions);
            push_role_impl_expr_projection_types(out, expr, ambient_substitutions);
        }
        _ => {}
    }
}

fn role_impl_result_projection_types(
    spine: &PrincipalUnifyApplySpine<'_>,
    result_ty: &RuntimeType,
    ambient_substitutions: Option<&BTreeMap<core_ir::TypeVar, core_ir::Type>>,
) -> Vec<core_ir::Type> {
    let (actual, _effect) = runtime_value_and_effect(result_ty);
    let mut out = Vec::new();
    push_role_impl_projection_type(&mut out, actual, ambient_substitutions);
    if let Some(evidence) = spine.evidences.last().copied().flatten() {
        push_role_impl_bounds_projection_type(&mut out, &evidence.result, ambient_substitutions);
    }
    out
}

fn push_role_impl_bounds_projection_type(
    out: &mut Vec<core_ir::Type>,
    bounds: &core_ir::TypeBounds,
    ambient_substitutions: Option<&BTreeMap<core_ir::TypeVar, core_ir::Type>>,
) {
    if let Some(ty) = closed_type_from_bounds(Some(bounds)) {
        push_role_impl_projection_type(out, ty, ambient_substitutions);
        return;
    }
    if let Some(substitutions) = ambient_substitutions {
        let bounds = substitute_bounds(bounds.clone(), substitutions);
        if let Some(ty) = closed_type_from_bounds(Some(&bounds)) {
            push_role_impl_projection_type(out, ty, None);
        }
    }
}

fn push_role_impl_projection_type(
    out: &mut Vec<core_ir::Type>,
    ty: core_ir::Type,
    ambient_substitutions: Option<&BTreeMap<core_ir::TypeVar, core_ir::Type>>,
) {
    let ty = ambient_substitutions
        .map(|substitutions| substitute_type(&ty, substitutions))
        .unwrap_or(ty);
    if !closed_slot_type_usable(&ty, false) {
        return;
    }
    if !out.iter().any(|existing| existing == &ty) {
        out.push(ty);
    }
}

fn role_impl_slot_score(expected: &core_ir::Type, actual: &core_ir::Type) -> usize {
    if expected == actual {
        return 4;
    }
    if receiver_type_matches_impl(expected, actual) {
        return 3;
    }
    if type_compatible(expected, actual) {
        return 1;
    }
    0
}

fn project_closed_value_substitutions_from_type(
    template: &core_ir::Type,
    actual: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
    depth: usize,
) {
    if depth == 0 {
        return;
    }
    match (template, actual) {
        (core_ir::Type::Var(var), actual) if params.contains(var) => {
            let actual = normalize_projected_value_substitution_type(actual, substitutions);
            if closed_slot_type_usable(&actual, false) {
                insert_projected_value_substitution(substitutions, conflicts, var.clone(), actual);
            }
        }
        (
            core_ir::Type::Named { path, args },
            core_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => {
            for (template_arg, actual_arg) in args.iter().zip(actual_args) {
                project_closed_value_substitutions_from_type_arg(
                    template_arg,
                    actual_arg,
                    params,
                    substitutions,
                    conflicts,
                    depth - 1,
                );
            }
        }
        (
            core_ir::Type::Fun {
                param,
                ret_effect,
                ret,
                ..
            },
            core_ir::Type::Fun {
                param: actual_param,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
                ..
            },
        ) => {
            project_closed_value_substitutions_from_type(
                param,
                actual_param,
                params,
                substitutions,
                conflicts,
                depth - 1,
            );
            project_closed_substitutions_from_type(
                ret_effect,
                actual_ret_effect,
                params,
                substitutions,
                conflicts,
                true,
                depth - 1,
            );
            project_closed_value_substitutions_from_type(
                ret,
                actual_ret,
                params,
                substitutions,
                conflicts,
                depth - 1,
            );
        }
        (core_ir::Type::Tuple(items), core_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            for (item, actual_item) in items.iter().zip(actual_items) {
                project_closed_value_substitutions_from_type(
                    item,
                    actual_item,
                    params,
                    substitutions,
                    conflicts,
                    depth - 1,
                );
            }
        }
        (core_ir::Type::Union(items) | core_ir::Type::Inter(items), actual)
            if closed_slot_type_usable(
                &normalize_projected_value_substitution_type(actual, substitutions),
                false,
            ) =>
        {
            let actual = normalize_projected_value_substitution_type(actual, substitutions);
            for item in items {
                project_closed_value_substitutions_from_type(
                    item,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    depth - 1,
                );
            }
        }
        _ => {}
    }
}

fn project_closed_value_substitutions_from_type_arg(
    template: &core_ir::TypeArg,
    actual: &core_ir::TypeArg,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
    depth: usize,
) {
    match (template, actual) {
        (core_ir::TypeArg::Type(template), core_ir::TypeArg::Type(actual)) => {
            project_closed_value_substitutions_from_type(
                template,
                actual,
                params,
                substitutions,
                conflicts,
                depth,
            );
        }
        (core_ir::TypeArg::Type(template), core_ir::TypeArg::Bounds(actual)) => {
            let actual_bounds = substitute_bounds(actual.clone(), substitutions);
            if let Some(actual) = closed_type_from_bounds(Some(&actual_bounds)) {
                project_closed_value_substitutions_from_type(
                    template,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    depth,
                );
            }
        }
        (core_ir::TypeArg::Bounds(template), core_ir::TypeArg::Type(actual)) => {
            let actual = normalize_projected_value_substitution_type(actual, substitutions);
            if !closed_slot_type_usable(&actual, false) {
                return;
            }
            project_closed_value_substitutions_from_bounds(
                template,
                &actual,
                params,
                substitutions,
                conflicts,
                depth,
            );
        }
        (core_ir::TypeArg::Bounds(template), core_ir::TypeArg::Bounds(actual)) => {
            let actual_bounds = substitute_bounds(actual.clone(), substitutions);
            if let Some(actual) = closed_type_from_bounds(Some(&actual_bounds)) {
                project_closed_value_substitutions_from_bounds(
                    template,
                    &actual,
                    params,
                    substitutions,
                    conflicts,
                    depth,
                );
            }
        }
    }
}

fn project_closed_value_substitutions_from_bounds(
    template: &core_ir::TypeBounds,
    actual: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
    depth: usize,
) {
    if !closed_slot_type_usable(actual, false) {
        return;
    }

    if let Some(lower) = template.lower.as_deref() {
        project_closed_value_substitutions_from_type(
            lower,
            actual,
            params,
            substitutions,
            conflicts,
            depth,
        );
    }
    if let Some(upper) = template.upper.as_deref() {
        project_closed_value_substitutions_from_type(
            upper,
            actual,
            params,
            substitutions,
            conflicts,
            depth,
        );
    }
}

fn insert_projected_value_substitution(
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: &mut BTreeSet<core_ir::TypeVar>,
    var: core_ir::TypeVar,
    ty: core_ir::Type,
) {
    if let Some(existing) = substitutions.get(&var) {
        if let Some(merged) = merge_projected_value_type_precision(existing, &ty) {
            substitutions.insert(var, merged);
        } else if existing != &ty {
            conflicts.insert(var);
        }
    } else {
        substitutions.insert(var, ty);
    }
}

fn merge_projected_value_type_precision(
    existing: &core_ir::Type,
    incoming: &core_ir::Type,
) -> Option<core_ir::Type> {
    if existing == incoming {
        return Some(existing.clone());
    }
    match (existing, incoming) {
        (core_ir::Type::Unknown, incoming) => Some(incoming.clone()),
        (existing, core_ir::Type::Unknown) => Some(existing.clone()),
        (core_ir::Type::Any, incoming) => Some(incoming.clone()),
        (existing, core_ir::Type::Any) => Some(existing.clone()),
        (
            core_ir::Type::Named {
                path: existing_path,
                args: existing_args,
            },
            core_ir::Type::Named {
                path: incoming_path,
                args: incoming_args,
            },
        ) if existing_path == incoming_path && existing_args.len() == incoming_args.len() => {
            let args = existing_args
                .iter()
                .zip(incoming_args)
                .map(|(existing, incoming)| merge_projected_type_arg_precision(existing, incoming))
                .collect::<Option<Vec<_>>>()?;
            Some(core_ir::Type::Named {
                path: existing_path.clone(),
                args,
            })
        }
        (core_ir::Type::Tuple(existing_items), core_ir::Type::Tuple(incoming_items))
            if existing_items.len() == incoming_items.len() =>
        {
            let items = existing_items
                .iter()
                .zip(incoming_items)
                .map(|(existing, incoming)| {
                    merge_projected_value_type_precision(existing, incoming)
                })
                .collect::<Option<Vec<_>>>()?;
            Some(core_ir::Type::Tuple(items))
        }
        (
            core_ir::Type::Fun {
                param: existing_param,
                param_effect: existing_param_effect,
                ret_effect: existing_ret_effect,
                ret: existing_ret,
            },
            core_ir::Type::Fun {
                param: incoming_param,
                param_effect: incoming_param_effect,
                ret_effect: incoming_ret_effect,
                ret: incoming_ret,
            },
        ) => Some(core_ir::Type::Fun {
            param: Box::new(merge_projected_value_type_precision(
                existing_param,
                incoming_param,
            )?),
            param_effect: Box::new(merge_projected_value_type_precision(
                existing_param_effect,
                incoming_param_effect,
            )?),
            ret_effect: Box::new(merge_projected_value_type_precision(
                existing_ret_effect,
                incoming_ret_effect,
            )?),
            ret: Box::new(merge_projected_value_type_precision(
                existing_ret,
                incoming_ret,
            )?),
        }),
        _ => None,
    }
}

fn merge_projected_type_arg_precision(
    existing: &core_ir::TypeArg,
    incoming: &core_ir::TypeArg,
) -> Option<core_ir::TypeArg> {
    match (existing, incoming) {
        (core_ir::TypeArg::Type(existing), core_ir::TypeArg::Type(incoming)) => Some(
            core_ir::TypeArg::Type(merge_projected_value_type_precision(existing, incoming)?),
        ),
        (core_ir::TypeArg::Bounds(existing), core_ir::TypeArg::Bounds(incoming)) => Some(
            core_ir::TypeArg::Bounds(merge_projected_bounds_precision(existing, incoming)?),
        ),
        (core_ir::TypeArg::Bounds(existing), core_ir::TypeArg::Type(incoming))
        | (core_ir::TypeArg::Type(incoming), core_ir::TypeArg::Bounds(existing)) => {
            let existing = closed_type_from_bounds(Some(existing))?;
            Some(core_ir::TypeArg::Type(
                merge_projected_value_type_precision(&existing, incoming)?,
            ))
        }
    }
}

fn merge_projected_bounds_precision(
    existing: &core_ir::TypeBounds,
    incoming: &core_ir::TypeBounds,
) -> Option<core_ir::TypeBounds> {
    let lower = match (existing.lower.as_deref(), incoming.lower.as_deref()) {
        (Some(existing), Some(incoming)) => Some(Box::new(merge_projected_value_type_precision(
            existing, incoming,
        )?)),
        (Some(existing), None) => Some(Box::new(existing.clone())),
        (None, Some(incoming)) => Some(Box::new(incoming.clone())),
        (None, None) => None,
    };
    let upper = match (existing.upper.as_deref(), incoming.upper.as_deref()) {
        (Some(existing), Some(incoming)) => Some(Box::new(merge_projected_value_type_precision(
            existing, incoming,
        )?)),
        (Some(existing), None) => Some(Box::new(existing.clone())),
        (None, Some(incoming)) => Some(Box::new(incoming.clone())),
        (None, None) => None,
    };
    Some(core_ir::TypeBounds { lower, upper })
}

fn normalize_projected_value_substitution_type(
    ty: &core_ir::Type,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> core_ir::Type {
    collapse_repeated_top_choice_type(substitute_type(ty, substitutions))
}

fn collapse_repeated_top_choice_type(ty: core_ir::Type) -> core_ir::Type {
    match ty {
        core_ir::Type::Union(items) => {
            collapse_repeated_top_choice_items(items, core_ir::Type::Union)
        }
        core_ir::Type::Inter(items) => {
            collapse_repeated_top_choice_items(items, core_ir::Type::Inter)
        }
        other => other,
    }
}

fn collapse_repeated_top_choice_items(
    items: Vec<core_ir::Type>,
    rebuild: impl FnOnce(Vec<core_ir::Type>) -> core_ir::Type,
) -> core_ir::Type {
    let mut unique = Vec::<core_ir::Type>::new();
    for item in items {
        if !unique.iter().any(|existing| existing == &item) {
            unique.push(item);
        }
    }
    if unique.len() == 1 {
        unique.pop().expect("single projected value choice item")
    } else {
        rebuild(unique)
    }
}

fn binding_effect_only_vars(binding: &Binding) -> BTreeSet<core_ir::TypeVar> {
    let mut usage = BTreeMap::<core_ir::TypeVar, (bool, bool)>::new();
    collect_type_var_effect_usage(&binding.scheme.body, false, &mut usage);
    binding_required_vars(binding)
        .into_iter()
        .filter(|var| {
            usage
                .get(var)
                .is_some_and(|(value, effect)| !*value && *effect)
        })
        .collect()
}

fn collect_type_var_effect_usage(
    ty: &core_ir::Type,
    in_effect: bool,
    usage: &mut BTreeMap<core_ir::TypeVar, (bool, bool)>,
) {
    match ty {
        core_ir::Type::Var(var) => {
            let entry = usage.entry(var.clone()).or_default();
            if in_effect {
                entry.1 = true;
            } else {
                entry.0 = true;
            }
        }
        core_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_type_arg_effect_usage(arg, in_effect, usage);
            }
        }
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_type_var_effect_usage(param, in_effect, usage);
            collect_type_var_effect_usage(param_effect, true, usage);
            collect_type_var_effect_usage(ret_effect, true, usage);
            collect_type_var_effect_usage(ret, in_effect, usage);
        }
        core_ir::Type::Tuple(items)
        | core_ir::Type::Union(items)
        | core_ir::Type::Inter(items)
        | core_ir::Type::Row { items, .. } => {
            for item in items {
                collect_type_var_effect_usage(item, in_effect, usage);
            }
            if let core_ir::Type::Row { tail, .. } = ty {
                collect_type_var_effect_usage(tail, in_effect, usage);
            }
        }
        core_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_type_var_effect_usage(&field.value, in_effect, usage);
            }
        }
        core_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_type_var_effect_usage(payload, in_effect, usage);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_type_var_effect_usage(tail, in_effect, usage);
            }
        }
        core_ir::Type::Recursive { body, .. } => {
            collect_type_var_effect_usage(body, in_effect, usage);
        }
        core_ir::Type::Unknown | core_ir::Type::Never | core_ir::Type::Any => {}
    }
}

fn collect_type_arg_effect_usage(
    arg: &core_ir::TypeArg,
    in_effect: bool,
    usage: &mut BTreeMap<core_ir::TypeVar, (bool, bool)>,
) {
    match arg {
        core_ir::TypeArg::Type(ty) => collect_type_var_effect_usage(ty, in_effect, usage),
        core_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = bounds.lower.as_deref() {
                collect_type_var_effect_usage(lower, in_effect, usage);
            }
            if let Some(upper) = bounds.upper.as_deref() {
                collect_type_var_effect_usage(upper, in_effect, usage);
            }
        }
    }
}

fn receiver_type_matches_impl(
    impl_receiver: &core_ir::Type,
    actual_receiver: &core_ir::Type,
) -> bool {
    match (impl_receiver, actual_receiver) {
        (left, right) if left == right => true,
        (
            core_ir::Type::Named {
                path: left_path,
                args: left_args,
            },
            core_ir::Type::Named {
                path: right_path,
                args: right_args,
            },
        ) => {
            left_path == right_path
                && left_args.len() == right_args.len()
                && left_args
                    .iter()
                    .zip(right_args)
                    .all(|(left, right)| receiver_type_arg_matches_impl(left, right))
        }
        (core_ir::Type::Tuple(left_items), core_ir::Type::Tuple(right_items)) => {
            left_items.len() == right_items.len()
                && left_items
                    .iter()
                    .zip(right_items)
                    .all(|(left, right)| receiver_type_matches_impl(left, right))
        }
        (
            core_ir::Type::Fun {
                param: left_param,
                param_effect: left_param_effect,
                ret_effect: left_ret_effect,
                ret: left_ret,
            },
            core_ir::Type::Fun {
                param: right_param,
                param_effect: right_param_effect,
                ret_effect: right_ret_effect,
                ret: right_ret,
            },
        ) => {
            receiver_type_matches_impl(left_param, right_param)
                && receiver_type_matches_impl(left_param_effect, right_param_effect)
                && receiver_type_matches_impl(left_ret_effect, right_ret_effect)
                && receiver_type_matches_impl(left_ret, right_ret)
        }
        _ => false,
    }
}

fn receiver_type_arg_matches_impl(left: &core_ir::TypeArg, right: &core_ir::TypeArg) -> bool {
    match (left, right) {
        (core_ir::TypeArg::Type(left), core_ir::TypeArg::Type(right)) => {
            receiver_type_matches_impl(left, right)
        }
        (core_ir::TypeArg::Type(left), core_ir::TypeArg::Bounds(right))
        | (core_ir::TypeArg::Bounds(right), core_ir::TypeArg::Type(left)) => {
            receiver_bounds_contains_type(right, left)
        }
        (core_ir::TypeArg::Bounds(left), core_ir::TypeArg::Bounds(right)) => {
            receiver_bounds_match(left, right)
        }
    }
}

fn receiver_bounds_contains_type(bounds: &core_ir::TypeBounds, ty: &core_ir::Type) -> bool {
    bounds
        .lower
        .as_deref()
        .is_some_and(|lower| receiver_type_matches_impl(lower, ty))
        || bounds
            .upper
            .as_deref()
            .is_some_and(|upper| receiver_type_matches_impl(upper, ty))
}

fn receiver_bounds_match(left: &core_ir::TypeBounds, right: &core_ir::TypeBounds) -> bool {
    match (
        left.lower.as_deref(),
        left.upper.as_deref(),
        right.lower.as_deref(),
        right.upper.as_deref(),
    ) {
        (Some(left_lower), _, Some(right_lower), _) => {
            receiver_type_matches_impl(left_lower, right_lower)
        }
        (_, Some(left_upper), _, Some(right_upper)) => {
            receiver_type_matches_impl(left_upper, right_upper)
        }
        (Some(left_lower), _, _, Some(right_upper)) => {
            receiver_type_matches_impl(left_lower, right_upper)
        }
        (_, Some(left_upper), Some(right_lower), _) => {
            receiver_type_matches_impl(left_upper, right_lower)
        }
        _ => false,
    }
}

fn is_impl_method_path(path: &core_ir::Path) -> bool {
    path.segments
        .iter()
        .any(|segment| segment.0.starts_with("&impl#"))
}

fn principal_unify_key(
    target: &core_ir::Path,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
    handler_plan: Option<&HandlerAdapterPlan>,
) -> String {
    let mut key = canonical_path(target);
    for (var, ty) in substitutions {
        key.push('|');
        key.push_str(&var.0);
        key.push('=');
        canonical_type(ty, &mut key);
    }
    if let Some(plan) = handler_plan {
        if let Some(effect) = &plan.residual_before {
            key.push_str("|handler-before=");
            canonical_type(effect, &mut key);
        }
        if let Some(effect) = &plan.residual_after {
            key.push_str("|handler-after=");
            canonical_type(effect, &mut key);
        }
        if let Some(effect) = &plan.return_wrapper_effect {
            key.push_str("|handler-return=");
            canonical_type(effect, &mut key);
        }
    }
    key
}

fn principal_unified_path(target: &core_ir::Path, index: usize) -> core_ir::Path {
    let mut path = target.clone();
    match path.segments.last_mut() {
        Some(name) => name.0 = format!("{}__mono{index}", name.0),
        None => path.segments.push(core_ir::Name(format!("__mono{index}"))),
    }
    path
}

fn next_principal_unify_index(module: &Module) -> usize {
    module
        .bindings
        .iter()
        .filter_map(|binding| specialization_suffix(&binding.name))
        .max()
        .map(|index| index + 1)
        .unwrap_or(0)
}

fn empty_module() -> Module {
    Module {
        path: core_ir::Path::default(),
        bindings: Vec::new(),
        root_exprs: Vec::new(),
        roots: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rewrites_complete_principal_plan_without_runtime_inference() {
        let t = core_ir::TypeVar("t".to_string());
        let int = named("int");
        let id_path = path(&["id"]);
        let id_scheme = core_ir::Scheme {
            requirements: Vec::new(),
            body: fun(core_ir::Type::Var(t.clone()), core_ir::Type::Var(t.clone())),
        };
        let binding = Binding {
            name: id_path.clone(),
            type_params: vec![t.clone()],
            scheme: id_scheme.clone(),
            body: Expr::typed(
                ExprKind::Lambda {
                    param: name("x"),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Var(path(&["x"])),
                        RuntimeType::core(core_ir::Type::Var(t.clone())),
                    )),
                },
                RuntimeType::core(id_scheme.body.clone()),
            ),
        };
        let evidence = core_ir::ApplyEvidence {
            callee_source_edge: None,
            arg_source_edge: None,
            callee: core_ir::TypeBounds::exact(id_scheme.body.clone()),
            expected_callee: None,
            arg: core_ir::TypeBounds::exact(int.clone()),
            expected_arg: Some(core_ir::TypeBounds::exact(int.clone())),
            result: core_ir::TypeBounds::exact(int.clone()),
            principal_callee: Some(id_scheme.body.clone()),
            substitutions: vec![core_ir::TypeSubstitution {
                var: t.clone(),
                ty: int.clone(),
            }],
            substitution_candidates: Vec::new(),
            role_method: false,
            principal_elaboration: Some(core_ir::PrincipalElaborationPlan {
                target: Some(id_path.clone()),
                principal_callee: id_scheme.body.clone(),
                substitutions: vec![core_ir::TypeSubstitution {
                    var: t.clone(),
                    ty: int.clone(),
                }],
                args: vec![core_ir::PrincipalElaborationArg {
                    index: 0,
                    intrinsic: core_ir::TypeBounds::exact(int.clone()),
                    contextual: Some(core_ir::TypeBounds::exact(int.clone())),
                    expected_runtime: Some(int.clone()),
                    source_edge: None,
                }],
                result: core_ir::PrincipalElaborationResult {
                    intrinsic: core_ir::TypeBounds::exact(int.clone()),
                    contextual: Some(core_ir::TypeBounds::exact(int.clone())),
                    expected_runtime: Some(int.clone()),
                },
                adapters: Vec::new(),
                complete: true,
                incomplete_reasons: Vec::new(),
            }),
        };
        let module = Module {
            path: path(&["test"]),
            bindings: vec![binding],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(id_path.clone()),
                        RuntimeType::core(id_scheme.body),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(int.clone()),
                    )),
                    evidence: Some(evidence),
                    instantiation: None,
                },
                RuntimeType::core(int),
            )],
            roots: vec![Root::Expr(0)],
        };

        let (module, profile) = principal_unify_module_profiled(module);

        assert!(
            profile
                .stats
                .get("principal-unify-rewrite")
                .is_some_and(|count| *count == 1)
        );
        assert!(
            module
                .bindings
                .iter()
                .any(|binding| canonical_path(&binding.name) == "id__mono0")
        );
        let ExprKind::Apply { callee, .. } = &module.root_exprs[0].kind else {
            panic!("root should stay an apply");
        };
        let ExprKind::Var(path) = &callee.kind else {
            panic!("callee should be rewritten to specialized binding");
        };
        assert_eq!(canonical_path(path), "id__mono0");
    }

    #[test]
    fn materializes_contextual_thunk_type_when_expression_does_not_return_thunk() {
        let bool_ty = named("bool");
        let unit_ty = named("unit");
        let effect = named("std::junction::junction");
        let callee_ty = fun(unit_ty.clone(), bool_ty.clone());
        let arg = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(path(&["f"])),
                    RuntimeType::core(callee_ty),
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Unit),
                    RuntimeType::core(unit_ty),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::thunk(effect.clone(), RuntimeType::core(bool_ty.clone())),
        );

        let adapted = principal_arg_adapter(&arg, &bool_ty, &effect).expect("adapter");

        assert!(matches!(
            adapted.ty,
            RuntimeType::Thunk {
                effect: ref actual,
                ..
            } if actual == &effect
        ));
    }

    #[test]
    fn erased_effect_param_does_not_thunk_value_argument() {
        let bool_ty = named("bool");
        let arg = Expr::typed(
            ExprKind::Lit(core_ir::Lit::Bool(true)),
            RuntimeType::core(bool_ty.clone()),
        );

        let adapted = principal_arg_adapter(&arg, &bool_ty, &core_ir::Type::Any).expect("adapter");

        assert!(matches!(
            adapted.kind,
            ExprKind::Lit(core_ir::Lit::Bool(true))
        ));
        assert_eq!(adapted.ty, RuntimeType::core(bool_ty));
    }

    #[test]
    fn erased_row_effect_param_does_not_thunk_value_argument() {
        let bool_ty = named("bool");
        let effect = core_ir::Type::Row {
            items: Vec::new(),
            tail: Box::new(core_ir::Type::Any),
        };
        let arg = Expr::typed(
            ExprKind::Lit(core_ir::Lit::Bool(true)),
            RuntimeType::core(bool_ty.clone()),
        );

        let adapted = principal_arg_adapter(&arg, &bool_ty, &effect).expect("adapter");

        assert!(matches!(
            adapted.kind,
            ExprKind::Lit(core_ir::Lit::Bool(true))
        ));
        assert_eq!(adapted.ty, RuntimeType::core(bool_ty));
    }

    #[test]
    fn keeps_apply_that_really_returns_effect_thunk() {
        let bool_ty = named("bool");
        let unit_ty = named("unit");
        let effect = named("std::junction::junction");
        let callee_ty = fun_with_effect(
            unit_ty.clone(),
            core_ir::Type::Never,
            bool_ty.clone(),
            effect.clone(),
        );
        let arg = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(path(&["f"])),
                    RuntimeType::core(callee_ty),
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Unit),
                    RuntimeType::core(unit_ty),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::thunk(effect.clone(), RuntimeType::core(bool_ty.clone())),
        );

        let adapted = principal_arg_adapter(&arg, &bool_ty, &effect).expect("adapter");

        assert!(matches!(adapted.kind, ExprKind::Apply { .. }));
    }

    fn fun(param: core_ir::Type, ret: core_ir::Type) -> core_ir::Type {
        fun_with_effect(param, core_ir::Type::Never, ret, core_ir::Type::Never)
    }

    fn fun_with_effect(
        param: core_ir::Type,
        param_effect: core_ir::Type,
        ret: core_ir::Type,
        ret_effect: core_ir::Type,
    ) -> core_ir::Type {
        core_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(param_effect),
            ret_effect: Box::new(ret_effect),
            ret: Box::new(ret),
        }
    }

    fn named(value: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: path(&[value]),
            args: Vec::new(),
        }
    }

    fn path(segments: &[&str]) -> core_ir::Path {
        core_ir::Path::new(segments.iter().map(|segment| name(segment)).collect())
    }

    fn name(value: &str) -> core_ir::Name {
        core_ir::Name(value.to_string())
    }
}
