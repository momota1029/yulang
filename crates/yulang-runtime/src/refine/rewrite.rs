use super::*;

pub(super) struct RefineRewriter {
    pub(super) substitutions: BTreeMap<core_ir::TypeVar, core_ir::Type>,
    pub(super) binding_types: HashMap<core_ir::Path, RuntimeType>,
    pub(super) locals: HashMap<core_ir::Path, RuntimeType>,
    pub(super) pure_handler_bindings: HashMap<core_ir::Path, Vec<core_ir::Path>>,
}

impl RefineRewriter {
    pub(super) fn module(&mut self, module: Module) -> RefineModuleOutput {
        let mut report = RefineReport::default();
        let bindings = module
            .bindings
            .into_iter()
            .map(|binding| {
                let original = binding.clone();
                let refined = self.binding(binding);
                if refined != original {
                    report.changed_bindings += 1;
                }
                refined
            })
            .collect();
        let root_exprs = module
            .root_exprs
            .into_iter()
            .map(|expr| {
                let original = expr.clone();
                let refined = self.expr(expr, None);
                if refined != original {
                    report.changed_roots += 1;
                }
                refined
            })
            .collect();
        let module = Module {
            path: module.path,
            bindings,
            root_exprs,
            roots: module.roots,
        };
        RefineModuleOutput { module, report }
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
        let mut ty = self.initial_expr_type(&expr, expected);

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
}
