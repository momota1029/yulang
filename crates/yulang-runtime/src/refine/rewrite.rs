use super::*;

pub(super) struct RefineRewriter {
    pub(super) substitutions: BTreeMap<core_ir::TypeVar, core_ir::Type>,
    pub(super) binding_types: HashMap<core_ir::Path, RuntimeType>,
    pub(super) locals: HashMap<core_ir::Path, RuntimeType>,
    pub(super) pure_handler_bindings: HashMap<core_ir::Path, Vec<core_ir::Path>>,
}

impl RefineRewriter {
    pub(super) fn module(&mut self, module: Module) -> Module {
        let bindings = module
            .bindings
            .into_iter()
            .map(|binding| self.binding(binding))
            .collect();
        let root_exprs = module
            .root_exprs
            .into_iter()
            .map(|expr| self.expr(expr, None))
            .collect();
        Module {
            path: module.path,
            bindings,
            root_exprs,
            roots: module.roots,
        }
    }

    pub(super) fn binding(&mut self, binding: Binding) -> Binding {
        if is_principal_polymorphic_binding(&binding) {
            self.binding_types
                .insert(binding.name.clone(), binding.body.ty.clone());
            return binding;
        }

        let scheme = substitute_scheme(binding.scheme, &self.substitutions);
        let params = binding.type_params.iter().cloned().collect::<BTreeSet<_>>();
        let expected = project_runtime_hir_type_with_vars(&scheme.body, &params);
        let body = self.expr(binding.body, Some(&expected));
        let mut body_vars = BTreeSet::new();
        collect_hir_type_vars(&body.ty, &mut body_vars);
        let scheme_vars = core_type_vars(&scheme.body);
        let type_params = binding
            .type_params
            .into_iter()
            .filter(|param| body_vars.contains(param) || scheme_vars.contains(param))
            .collect();
        let binding = Binding {
            name: binding.name.clone(),
            type_params,
            scheme,
            body,
        };
        self.binding_types
            .insert(binding.name.clone(), binding.body.ty.clone());
        binding
    }

    pub(super) fn expr(&mut self, expr: Expr, expected: Option<&RuntimeType>) -> Expr {
        let original_ty = substitute_hir_type(&expr.ty, &self.substitutions);
        let constructor_expected = match (&expr.kind, expected) {
            (ExprKind::Var(path), Some(expected)) => {
                is_nullary_constructor_path_for_type(path, expected)
            }
            _ => false,
        };
        let local_ty = match &expr.kind {
            ExprKind::Var(path) => self.locals.get(path).cloned(),
            _ => None,
        };
        let binding_ty = match &expr.kind {
            ExprKind::Var(path) if !constructor_expected && !is_data_constructor_path(path) => {
                local_ty
                    .is_none()
                    .then(|| self.binding_types.get(path).cloned())
                    .flatten()
            }
            _ => None,
        };
        let original_ty = local_ty
            .clone()
            .or(binding_ty.clone())
            .unwrap_or(original_ty);
        let mut ty = if constructor_expected {
            expected
                .map(|expected| substitute_hir_type(expected, &self.substitutions))
                .unwrap_or(original_ty)
        } else if binding_ty.as_ref().is_some_and(hir_type_has_vars) {
            expected
                .map(|expected| substitute_hir_type(expected, &self.substitutions))
                .filter(|expected| {
                    !hir_type_has_vars(expected) && !hir_type_is_core_never(expected)
                })
                .unwrap_or(original_ty)
        } else if binding_ty.is_some() {
            original_ty
        } else {
            expected
                .map(|expected| substitute_hir_type(expected, &self.substitutions))
                .filter(|expected| {
                    !hir_type_has_vars(expected)
                        && !hir_type_is_core_never(&original_ty)
                        && hir_type_compatible(expected, &original_ty)
                })
                .map(|expected| refine_expected_expr_type(&expected, &original_ty))
                .unwrap_or(original_ty)
        };

        let kind = match expr.kind {
            ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body,
            } => {
                let (param_ty, body_expected) = match &ty {
                    RuntimeType::Fun { param, ret } => {
                        (Some((**param).clone()), Some((**ret).clone()))
                    }
                    _ => (None, None),
                };
                let local = core_ir::Path::from_name(param.clone());
                let previous = param_ty.map(|ty| push_binding(&mut self.locals, local, ty));
                let mut body = self.expr(*body, body_expected.as_ref());
                if let Some(previous) = previous {
                    pop_bindings(&mut self.locals, previous);
                }
                if let Some(forced_body) = self.force_protected_thunk_result(body.clone()) {
                    if let RuntimeType::Fun { param, .. } = &ty {
                        ty = RuntimeType::fun(param.as_ref().clone(), forced_body.ty.clone());
                    }
                    body = forced_body;
                }
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
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            } => {
                let arg = self.expr(*arg, None);
                let callee_expected = RuntimeType::fun(arg.ty.clone(), ty.clone());
                let callee = self.expr(*callee, Some(&callee_expected));
                let arg = match function_param_type(&callee.ty) {
                    Some(param) => bind_thunk_for_expected(self.expr(arg, Some(&param)), &param),
                    None => arg,
                };
                let actual_ty = function_result_type(&callee.ty).unwrap_or_else(|| ty.clone());
                let apply = Expr {
                    ty: actual_ty,
                    kind: ExprKind::Apply {
                        callee: Box::new(callee),
                        arg: Box::new(arg),
                        evidence: evidence.map(|evidence| {
                            substitute_apply_evidence(evidence, &self.substitutions)
                        }),
                        instantiation,
                    },
                };
                let apply = bind_thunk_for_expected(apply, &ty);
                return self.cast_if_needed(apply, expected);
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                evidence,
            } => ExprKind::If {
                cond: Box::new(self.expr(*cond, None)),
                then_branch: Box::new(self.expr(*then_branch, Some(&ty))),
                else_branch: Box::new(self.expr(*else_branch, Some(&ty))),
                evidence: evidence
                    .map(|evidence| substitute_join_evidence(evidence, &self.substitutions)),
            },
            ExprKind::Tuple(items) => ExprKind::Tuple(
                items
                    .into_iter()
                    .enumerate()
                    .map(|(index, item)| {
                        let expected = tuple_item_type(&ty, index);
                        self.expr(item, expected.as_ref())
                    })
                    .collect(),
            ),
            ExprKind::Record { fields, spread } => ExprKind::Record {
                fields: fields
                    .into_iter()
                    .map(|field| {
                        let expected = record_field_type(&ty, &field.name);
                        RecordExprField {
                            name: field.name,
                            value: self.expr(field.value, expected.as_ref()),
                        }
                    })
                    .collect(),
                spread: spread.map(|spread| match spread {
                    RecordSpreadExpr::Head(expr) => {
                        RecordSpreadExpr::Head(Box::new(self.expr(*expr, None)))
                    }
                    RecordSpreadExpr::Tail(expr) => {
                        RecordSpreadExpr::Tail(Box::new(self.expr(*expr, None)))
                    }
                }),
            },
            ExprKind::Variant { tag, value } => ExprKind::Variant {
                tag,
                value: value.map(|value| Box::new(self.expr(*value, None))),
            },
            ExprKind::Select { base, field } => ExprKind::Select {
                base: Box::new(self.expr(*base, None)),
                field,
            },
            ExprKind::Match {
                scrutinee,
                arms,
                evidence,
            } => {
                let scrutinee = self.expr(*scrutinee, None);
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let pattern = self.pattern(arm.pattern);
                        let bindings = pattern_bindings(&pattern);
                        let previous = push_bindings(&mut self.locals, &bindings);
                        let guard = arm.guard.map(|guard| self.expr(guard, None));
                        let body = self.expr(arm.body, Some(&ty));
                        pop_bindings(&mut self.locals, previous);
                        MatchArm {
                            pattern,
                            guard,
                            body,
                        }
                    })
                    .collect();
                ExprKind::Match {
                    scrutinee: Box::new(scrutinee),
                    arms,
                    evidence: substitute_join_evidence(evidence, &self.substitutions),
                }
            }
            ExprKind::Block { stmts, tail } => {
                let saved = self.locals.clone();
                let stmts = stmts
                    .into_iter()
                    .map(|stmt| {
                        let stmt = self.stmt(stmt);
                        push_stmt_bindings(&mut self.locals, &stmt);
                        stmt
                    })
                    .collect();
                let tail = tail.map(|tail| Box::new(self.expr(*tail, Some(&ty))));
                if let Some(tail) = tail.as_deref() {
                    ty = refine_type_from_tail(ty, &tail.ty);
                }
                self.locals = saved;
                ExprKind::Block { stmts, tail }
            }
            ExprKind::Handle {
                body,
                arms,
                evidence,
                handler,
            } => {
                let body = self.expr(*body, None);
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let payload = self.pattern(arm.payload);
                        let resume = arm.resume.map(|resume| ResumeBinding {
                            name: resume.name,
                            ty: substitute_hir_type(&resume.ty, &self.substitutions),
                        });
                        let mut bindings = pattern_bindings(&payload);
                        if let Some(resume) = &resume {
                            bindings.push((
                                core_ir::Path::from_name(resume.name.clone()),
                                resume.ty.clone(),
                            ));
                        }
                        let previous = push_bindings(&mut self.locals, &bindings);
                        let guard = arm.guard.map(|guard| self.expr(guard, None));
                        let body = self.expr(arm.body, Some(&ty));
                        pop_bindings(&mut self.locals, previous);
                        HandleArm {
                            effect: arm.effect,
                            payload,
                            resume,
                            guard,
                            body,
                        }
                    })
                    .collect();
                ExprKind::Handle {
                    body: Box::new(body),
                    arms,
                    evidence: substitute_join_evidence(evidence, &self.substitutions),
                    handler,
                }
            }
            ExprKind::BindHere { expr } => {
                let expr = self.expr(*expr, None);
                if !matches!(expr.ty, RuntimeType::Thunk { .. }) {
                    return self.cast_if_needed(expr, expected);
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
                let (effect, value) = match &ty {
                    RuntimeType::Thunk { effect, value } => {
                        (effect.clone(), value.as_ref().clone())
                    }
                    _ => (
                        substitute_type(&effect, &self.substitutions),
                        substitute_hir_type(&value, &self.substitutions),
                    ),
                };
                let expr = self.expr(*expr, Some(&value));
                let (effect, value, expr) = flatten_nested_thunk_body(effect, value, expr);
                ty = RuntimeType::thunk(effect.clone(), value.clone());
                ExprKind::Thunk {
                    effect,
                    value,
                    expr: Box::new(expr),
                }
            }
            ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
                id,
                body: Box::new(self.expr(*body, Some(&ty))),
            },
            ExprKind::PeekId => ExprKind::PeekId,
            ExprKind::FindId { id } => ExprKind::FindId { id },
            ExprKind::AddId { id, allowed, thunk } => {
                let thunk = self.expr(*thunk, Some(&ty));
                ty = thunk.ty.clone();
                ExprKind::AddId {
                    id,
                    allowed: substitute_type(&allowed, &self.substitutions),
                    thunk: Box::new(thunk),
                }
            }
            ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
                from: substitute_type(&from, &self.substitutions),
                to: substitute_type(&to, &self.substitutions),
                expr: Box::new(self.expr(*expr, None)),
            },
            ExprKind::Pack { var, expr } => ExprKind::Pack {
                var,
                expr: Box::new(self.expr(*expr, Some(&ty))),
            },
            ExprKind::Var(path) => ExprKind::Var(path),
            ExprKind::EffectOp(path) => ExprKind::EffectOp(path),
            ExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(op),
            ExprKind::Lit(lit) => ExprKind::Lit(lit),
        };

        self.cast_if_needed(Expr { ty, kind }, expected)
    }

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

    pub(super) fn pattern(&mut self, pattern: Pattern) -> Pattern {
        match pattern {
            Pattern::Wildcard { ty } => Pattern::Wildcard {
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::Bind { name, ty } => Pattern::Bind {
                name,
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::Lit { lit, ty } => Pattern::Lit {
                lit,
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::Tuple { items, ty } => Pattern::Tuple {
                items: items.into_iter().map(|item| self.pattern(item)).collect(),
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::List {
                prefix,
                spread,
                suffix,
                ty,
            } => Pattern::List {
                prefix: prefix.into_iter().map(|item| self.pattern(item)).collect(),
                spread: spread.map(|spread| Box::new(self.pattern(*spread))),
                suffix: suffix.into_iter().map(|item| self.pattern(item)).collect(),
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::Record { fields, spread, ty } => Pattern::Record {
                fields: fields
                    .into_iter()
                    .map(|field| RecordPatternField {
                        name: field.name,
                        pattern: self.pattern(field.pattern),
                        default: field.default.map(|default| self.expr(default, None)),
                    })
                    .collect(),
                spread: spread.map(|spread| match spread {
                    RecordSpreadPattern::Head(pattern) => {
                        RecordSpreadPattern::Head(Box::new(self.pattern(*pattern)))
                    }
                    RecordSpreadPattern::Tail(pattern) => {
                        RecordSpreadPattern::Tail(Box::new(self.pattern(*pattern)))
                    }
                }),
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::Variant { tag, value, ty } => Pattern::Variant {
                tag,
                value: value.map(|value| Box::new(self.pattern(*value))),
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::Or { left, right, ty } => Pattern::Or {
                left: Box::new(self.pattern(*left)),
                right: Box::new(self.pattern(*right)),
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::As { pattern, name, ty } => Pattern::As {
                pattern: Box::new(self.pattern(*pattern)),
                name,
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
        }
    }

    pub(super) fn cast_if_needed(&self, expr: Expr, expected: Option<&RuntimeType>) -> Expr {
        let Some(expected) = expected else {
            return expr;
        };
        let expected = substitute_hir_type(expected, &self.substitutions);
        let (expected_core, actual_core) = match (&expected, &expr.ty) {
            (RuntimeType::Core(expected_core), RuntimeType::Core(actual_core)) => {
                (expected_core.clone(), actual_core.clone())
            }
            _ => return expr,
        };
        if expected_core == actual_core || type_compatible(&expected_core, &actual_core) {
            return expr;
        }
        if !needs_runtime_coercion(&expected_core, &actual_core) {
            return expr;
        }
        Expr {
            ty: expected,
            kind: ExprKind::Coerce {
                from: actual_core,
                to: expected_core,
                expr: Box::new(expr),
            },
        }
    }
}
