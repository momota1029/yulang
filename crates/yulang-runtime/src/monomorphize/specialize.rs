use super::*;

impl Monomorphizer {
    pub(super) fn specialize(
        &mut self,
        instantiation: &TypeInstantiation,
    ) -> Option<core_ir::Path> {
        if !self.originals.contains_key(&instantiation.target) || instantiation.args.is_empty() {
            return None;
        }
        let original = self.originals.get(&instantiation.target)?.clone();
        let effect_params = effect_position_vars(&original.scheme.body);
        let params = original.type_params.iter().cloned().collect();
        let mut substitutions = instantiation
            .args
            .iter()
            .map(|arg| (arg.var.clone(), arg.ty.clone()))
            .collect::<BTreeMap<_, _>>();
        infer_role_requirement_substitutions(
            &original.scheme.requirements,
            &params,
            &mut substitutions,
        );
        let instantiation = TypeInstantiation {
            target: instantiation.target.clone(),
            args: original
                .type_params
                .iter()
                .filter_map(|var| {
                    substitutions
                        .get(var)
                        .map(|ty| crate::ir::TypeSubstitution {
                            var: var.clone(),
                            ty: ty.clone(),
                        })
                })
                .collect(),
        };
        let instantiation = normalize_type_instantiation(&instantiation, &effect_params)?;
        if is_effect_only_role_specialization(&original, &instantiation, &effect_params) {
            return None;
        }
        let key = specialization_key(&instantiation);
        if let Some(path) = self.cache.get(&key) {
            return Some(path.clone());
        }

        let path = self.fresh_specialized_path(&instantiation.target);
        self.cache.insert(key, path.clone());

        let substitutions = instantiation
            .args
            .iter()
            .map(|arg| (arg.var.clone(), arg.ty.clone()))
            .collect::<BTreeMap<_, _>>();
        let mut binding = substitute_binding(original, &substitutions);
        let mut associated_substitutions = BTreeMap::new();
        infer_role_requirement_substitutions(
            &binding.scheme.requirements,
            &binding.type_params.iter().cloned().collect(),
            &mut associated_substitutions,
        );
        infer_direct_associated_requirement_substitutions(
            &binding.scheme.requirements,
            &binding.type_params.iter().cloned().collect(),
            &mut associated_substitutions,
        );
        normalize_substitutions(&mut associated_substitutions);
        if !associated_substitutions.is_empty() {
            binding = substitute_binding(binding, &associated_substitutions);
        }
        binding.name = path.clone();
        refresh_binding_body_type_from_scheme(&mut binding);
        let mut refreshed_associated_substitutions = BTreeMap::new();
        infer_direct_associated_requirement_substitutions(
            &binding.scheme.requirements,
            &binding.type_params.iter().cloned().collect(),
            &mut refreshed_associated_substitutions,
        );
        normalize_substitutions(&mut refreshed_associated_substitutions);
        if !refreshed_associated_substitutions.is_empty() {
            binding = substitute_binding(binding, &refreshed_associated_substitutions);
            refresh_binding_body_type_from_scheme(&mut binding);
        }
        let body_ty = binding.body.ty.clone();
        binding.body = self.rewrite_expr_with_expected(binding.body, Some(&body_ty));
        refresh_binding_type_params(&mut binding);
        binding = fill_residual_effect_params(binding);
        refresh_specialized_scheme_from_body(&mut binding);
        self.specialized_types.insert(
            path.clone(),
            normalize_hir_function_type(binding.body.ty.clone()),
        );
        if !binding.type_params.is_empty() {
            self.originals.insert(path.clone(), binding.clone());
        }
        self.specialized.push(binding);
        Some(path)
    }

    pub(super) fn callee_param_expected(&self, callee: &Expr) -> Option<RuntimeType> {
        if let Some((target, _)) = applied_head(callee) {
            if self
                .originals
                .get(&target)
                .is_some_and(|binding| !binding.type_params.is_empty())
            {
                return None;
            }
            if unspecialized_path(&target).is_some_and(|base| {
                self.originals
                    .get(&base)
                    .is_some_and(|binding| !binding.type_params.is_empty())
            }) {
                return None;
            }
        }
        function_param_type(&callee.ty)
    }

    pub(super) fn specialize_callee_from_call(
        &mut self,
        callee: &mut Expr,
        arg_ty: &RuntimeType,
        result_ty: &RuntimeType,
    ) -> bool {
        let (target, applied_args) = match applied_head(callee) {
            Some(head) => head,
            None => return false,
        };
        let already_applied_args = applied_arg_types(callee);
        let receiver_ty = already_applied_args.first().or_else(|| {
            if already_applied_args.is_empty() {
                Some(arg_ty)
            } else {
                None
            }
        });
        let Some(path) = self
            .resolve_role_method_call_before_generic_specialization(
                target.clone(),
                already_applied_args.len(),
                receiver_ty,
                arg_ty,
                result_ty,
            )
            .or_else(|| {
                self.specialize_path_for_call(target.clone(), applied_args, arg_ty, result_ty)
            })
            .or_else(|| {
                if self.originals.contains_key(&target) {
                    None
                } else {
                    self.resolve_role_method_call(
                        target.clone(),
                        already_applied_args.len(),
                        receiver_ty,
                        arg_ty,
                        result_ty,
                        false,
                    )
                }
            })
            .or_else(|| {
                let base = unspecialized_path(&target)?;
                self.specialize_path_for_call(base, applied_args, arg_ty, result_ty)
            })
        else {
            return false;
        };
        self.replace_instantiated_head(callee, &target, &path);
        true
    }

    pub(super) fn resolve_role_callee_from_call(
        &mut self,
        callee: &mut Expr,
        arg_ty: &RuntimeType,
        result_ty: &RuntimeType,
    ) -> bool {
        let Some((target, _)) = applied_head(callee) else {
            return false;
        };
        if target
            .segments
            .last()
            .is_none_or(|name| name.0.as_str() != "fold")
        {
            return false;
        }
        if !is_role_method_path(&target) {
            return false;
        }
        let already_applied_args = applied_arg_types(callee);
        let receiver_ty = already_applied_args.first().or_else(|| {
            if already_applied_args.is_empty() {
                Some(arg_ty)
            } else {
                None
            }
        });
        let Some(path) = self.resolve_role_method_call(
            target.clone(),
            already_applied_args.len(),
            receiver_ty,
            arg_ty,
            result_ty,
            true,
        ) else {
            return false;
        };
        self.replace_instantiated_head(callee, &target, &path);
        true
    }

    fn resolve_role_method_call_before_generic_specialization(
        &mut self,
        target: core_ir::Path,
        applied_args: usize,
        receiver_ty: Option<&RuntimeType>,
        arg_ty: &RuntimeType,
        result_ty: &RuntimeType,
    ) -> Option<core_ir::Path> {
        if !is_role_method_path(&target) {
            return None;
        }
        self.resolve_role_method_call(target, applied_args, receiver_ty, arg_ty, result_ty, false)
    }

    pub(super) fn specialize_path_for_type(
        &mut self,
        target: core_ir::Path,
        actual_ty: &RuntimeType,
    ) -> Option<core_ir::Path> {
        let original = self.originals.get(&target)?;
        if original.type_params.is_empty() {
            return None;
        }
        let mut substitutions = BTreeMap::new();
        infer_hir_type_substitutions(
            &original.body.ty,
            actual_ty,
            &original.type_params,
            &mut substitutions,
        );
        if substitutions.is_empty() {
            let principal = binding_principal_hir_type(original);
            infer_hir_type_substitutions(
                &principal,
                actual_ty,
                &original.type_params,
                &mut substitutions,
            );
        }
        normalize_substitutions(&mut substitutions);
        if substitutions.is_empty() {
            return None;
        }
        let instantiation = TypeInstantiation {
            target,
            args: original
                .type_params
                .iter()
                .filter_map(|var| {
                    substitutions
                        .get(var)
                        .map(|ty| crate::ir::TypeSubstitution {
                            var: var.clone(),
                            ty: ty.clone(),
                        })
                })
                .collect(),
        };
        self.specialize(&instantiation)
    }

    pub(super) fn specialize_path_for_call(
        &mut self,
        target: core_ir::Path,
        applied_args: usize,
        arg_ty: &RuntimeType,
        result_ty: &RuntimeType,
    ) -> Option<core_ir::Path> {
        let original = self.originals.get(&target)?;
        if original.type_params.is_empty() {
            return None;
        }
        let template = unapplied_hir_type(&original.body.ty, applied_args)?;
        let actual = RuntimeType::fun(arg_ty.clone(), result_ty.clone());
        let mut substitutions = BTreeMap::new();
        infer_hir_call_type_substitutions(
            template,
            &actual,
            &original.type_params,
            &mut substitutions,
        );
        if let Some(principal_template) = unapplied_core_type(&original.scheme.body, applied_args) {
            infer_effectful_type_substitutions(
                principal_template,
                &effected_function_core_type(arg_ty, result_ty),
                &original.type_params.iter().cloned().collect(),
                &mut substitutions,
            );
        }
        let effect_params = effect_position_vars(&original.scheme.body);
        fill_call_effect_substitutions(&mut substitutions, &effect_params, &[arg_ty, result_ty]);
        normalize_call_substitutions(&mut substitutions, &effect_params);
        if substitutions.is_empty() {
            return None;
        }
        let instantiation = TypeInstantiation {
            target,
            args: original
                .type_params
                .iter()
                .filter_map(|var| {
                    substitutions
                        .get(var)
                        .map(|ty| crate::ir::TypeSubstitution {
                            var: var.clone(),
                            ty: ty.clone(),
                        })
                })
                .collect(),
        };
        self.specialize(&instantiation)
    }

    pub(super) fn replace_instantiated_head(
        &self,
        expr: &mut Expr,
        target: &core_ir::Path,
        replacement: &core_ir::Path,
    ) {
        match &mut expr.kind {
            ExprKind::Var(path) if path == target => {
                *path = replacement.clone();
                if let Some(ty) = self.binding_type(replacement) {
                    expr.ty = ty;
                }
            }
            ExprKind::EffectOp(path) if path == target => {
                *expr = Expr {
                    ty: self
                        .binding_type(replacement)
                        .unwrap_or_else(|| expr.ty.clone()),
                    kind: ExprKind::Var(replacement.clone()),
                };
            }
            ExprKind::Apply { callee, .. } => {
                self.replace_instantiated_head(callee, target, replacement);
                if let Some(ret) = apply_result_type(&callee.ty) {
                    expr.ty = ret;
                }
            }
            _ => {}
        }
    }

    pub(super) fn binding_type(&self, path: &core_ir::Path) -> Option<RuntimeType> {
        self.specialized
            .iter()
            .find(|binding| binding.name == *path)
            .map(|binding| normalize_hir_function_type(binding.body.ty.clone()))
            .or_else(|| self.specialized_types.get(path).cloned())
            .or_else(|| self.originals.get(path).map(binding_principal_hir_type))
    }

    pub(super) fn concrete_binding_type(&self, path: &core_ir::Path) -> Option<RuntimeType> {
        self.specialized
            .iter()
            .find(|binding| binding.name == *path)
            .map(|binding| normalize_hir_function_type(binding.body.ty.clone()))
            .or_else(|| self.specialized_types.get(path).cloned())
            .or_else(|| {
                self.originals.get(path).and_then(|binding| {
                    if binding.type_params.is_empty() {
                        Some(binding_principal_hir_type(binding))
                    } else {
                        None
                    }
                })
            })
    }

    pub(super) fn resolve_role_method_var(
        &mut self,
        path: core_ir::Path,
        expected: &RuntimeType,
    ) -> core_ir::Path {
        if self.originals.contains_key(&path) {
            return path;
        }
        if hir_type_has_vars(expected) {
            return path;
        }
        if function_param(expected).is_none_or(hir_type_is_hole) {
            return path;
        }
        let Some(method) = path.segments.last() else {
            return path;
        };
        let mut candidates = self
            .originals
            .iter()
            .filter(|(candidate, _)| {
                is_impl_method_path(candidate, method) && !is_specialized_path(candidate)
            })
            .map(|(candidate, binding)| (candidate.clone(), binding.clone()))
            .collect::<Vec<_>>();
        candidates.sort_by_key(|(path, _)| path_key(path));

        for (candidate, binding) in candidates {
            let template = binding_principal_hir_type(&binding);
            let mut substitutions = BTreeMap::new();
            infer_hir_type_substitutions(
                &template,
                expected,
                &binding.type_params,
                &mut substitutions,
            );
            normalize_substitutions(&mut substitutions);
            let ty = substitute_hir_type(template.clone(), &substitutions);
            if !hir_type_compatible(expected, &ty) {
                continue;
            }
            if substitutions.is_empty() {
                return candidate;
            }
            let instantiation = TypeInstantiation {
                target: candidate.clone(),
                args: binding
                    .type_params
                    .into_iter()
                    .filter_map(|var| {
                        substitutions
                            .get(&var)
                            .map(|ty| crate::ir::TypeSubstitution {
                                var,
                                ty: ty.clone(),
                            })
                    })
                    .collect(),
            };
            return self.specialize(&instantiation).unwrap_or(candidate);
        }

        path
    }

    pub(super) fn resolve_role_method_call(
        &mut self,
        target: core_ir::Path,
        applied_args: usize,
        receiver_ty: Option<&RuntimeType>,
        arg_ty: &RuntimeType,
        result_ty: &RuntimeType,
        infer_effects: bool,
    ) -> Option<core_ir::Path> {
        if hir_type_is_hole(arg_ty) {
            return None;
        }
        if receiver_ty.is_some_and(hir_type_has_vars) {
            return None;
        }
        let method = target.segments.last()?.clone();
        let actual = RuntimeType::fun(arg_ty.clone(), result_ty.clone());
        let mut candidates = self
            .originals
            .iter()
            .filter(|(candidate, _)| {
                is_impl_method_path(candidate, &method) && !is_specialized_path(candidate)
            })
            .map(|(candidate, binding)| (candidate.clone(), binding.clone()))
            .collect::<Vec<_>>();
        candidates.sort_by_key(|(path, _)| path_key(path));

        let mut best = None;
        for (candidate, binding) in candidates {
            let binding_ty = binding_principal_hir_type(&binding);
            if let Some(receiver_ty) = receiver_ty
                && !binding_receiver_matches(&binding_ty, receiver_ty)
            {
                continue;
            }
            let Some(template) = unapplied_hir_type(&binding_ty, applied_args) else {
                continue;
            };
            let mut substitutions = BTreeMap::new();
            infer_hir_type_substitutions(
                template,
                &actual,
                &binding.type_params,
                &mut substitutions,
            );
            if infer_effects {
                if let Some(principal_template) =
                    unapplied_core_type(&binding.scheme.body, applied_args)
                {
                    infer_effectful_type_substitutions(
                        principal_template,
                        &effected_function_core_type(arg_ty, result_ty),
                        &binding.type_params.iter().cloned().collect(),
                        &mut substitutions,
                    );
                }
                let effect_params = effect_position_vars(&binding.scheme.body);
                fill_call_effect_substitutions(
                    &mut substitutions,
                    &effect_params,
                    &[arg_ty, result_ty],
                );
                normalize_call_substitutions(&mut substitutions, &effect_params);
            } else {
                normalize_substitutions(&mut substitutions);
            }
            let ty = substitute_hir_type(template.clone(), &substitutions);
            if !hir_type_compatible(&ty, &actual) && !receiver_type_matches(&ty, arg_ty) {
                continue;
            }
            let score = role_method_candidate_score(&ty, &actual);
            match &best {
                Some((best_score, _, _)) if *best_score >= score => {}
                _ => best = Some((score, candidate, substitutions)),
            }
        }

        let (_, candidate, substitutions) = best?;
        if substitutions.is_empty() {
            return Some(candidate);
        }
        let binding = self.originals.get(&candidate)?;
        let instantiation = TypeInstantiation {
            target: candidate.clone(),
            args: binding
                .type_params
                .iter()
                .filter_map(|var| {
                    substitutions
                        .get(var)
                        .map(|ty| crate::ir::TypeSubstitution {
                            var: var.clone(),
                            ty: ty.clone(),
                        })
                })
                .collect(),
        };
        self.specialize(&instantiation).or(Some(candidate))
    }

    pub(super) fn fresh_specialized_path(&mut self, target: &core_ir::Path) -> core_ir::Path {
        let mut path = target.clone();
        let suffix = self.next_specialization;
        self.next_specialization += 1;
        if let Some(name) = path.segments.last_mut() {
            name.0 = format!("{}__mono{}", name.0, suffix);
        }
        path
    }
}

pub(super) fn is_impl_method_path(path: &core_ir::Path, method: &core_ir::Name) -> bool {
    path.segments.last() == Some(method)
        && path
            .segments
            .iter()
            .any(|segment| segment.0.starts_with("&impl#"))
}

fn is_effect_only_role_specialization(
    original: &Binding,
    instantiation: &TypeInstantiation,
    effect_params: &BTreeSet<core_ir::TypeVar>,
) -> bool {
    !original.scheme.requirements.is_empty()
        && instantiation
            .args
            .iter()
            .all(|arg| effect_params.contains(&arg.var))
}

pub(super) fn is_role_method_path(path: &core_ir::Path) -> bool {
    let Some(role) = path.segments.iter().rev().nth(1) else {
        return false;
    };
    role.0.chars().next().is_some_and(char::is_uppercase)
}

pub(super) fn is_specialized_path(path: &core_ir::Path) -> bool {
    path.segments
        .last()
        .is_some_and(|segment| segment.0.contains("__mono"))
}

pub(super) fn specialization_suffix(path: &core_ir::Path) -> Option<usize> {
    path.segments
        .last()?
        .0
        .rsplit_once("__mono")?
        .1
        .parse()
        .ok()
}

pub(super) fn unspecialized_path(path: &core_ir::Path) -> Option<core_ir::Path> {
    let mut path = path.clone();
    let name = &mut path.segments.last_mut()?.0;
    let index = name.find("__mono")?;
    name.truncate(index);
    Some(path)
}

pub(super) fn specialization_key(instantiation: &TypeInstantiation) -> String {
    let mut key = canonical_path(&instantiation.target);
    key.push('|');
    for arg in &instantiation.args {
        key.push_str(&arg.var.0);
        key.push('=');
        canonical_type(&arg.ty, &mut key);
        key.push(';');
    }
    key
}

pub(super) fn canonical_path(path: &core_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

pub(super) fn canonical_type(ty: &core_ir::Type, out: &mut String) {
    match ty {
        core_ir::Type::Any => out.push('_'),
        core_ir::Type::Never => out.push('!'),
        core_ir::Type::Var(var) => out.push_str(&var.0),
        core_ir::Type::Named { path, args } => {
            out.push_str(&canonical_path(path));
            if !args.is_empty() {
                out.push('<');
                for (index, arg) in args.iter().enumerate() {
                    if index > 0 {
                        out.push(',');
                    }
                    canonical_type_arg(arg, out);
                }
                out.push('>');
            }
        }
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            out.push('(');
            canonical_type(param, out);
            out.push('-');
            canonical_type(param_effect, out);
            out.push('/');
            canonical_type(ret_effect, out);
            out.push_str("->");
            canonical_type(ret, out);
            out.push(')');
        }
        core_ir::Type::Tuple(items) => canonical_type_list("(", ")", items, out),
        core_ir::Type::Record(record) => {
            out.push('{');
            for field in &record.fields {
                out.push_str(&field.name.0);
                out.push(':');
                canonical_type(&field.value, out);
                out.push(',');
            }
            out.push('}');
        }
        core_ir::Type::Variant(variant) => {
            out.push('[');
            for case in &variant.cases {
                out.push_str(&case.name.0);
                canonical_type_list("(", ")", &case.payloads, out);
                out.push(',');
            }
            out.push(']');
        }
        core_ir::Type::Row { items, tail } => {
            canonical_type_list("[", "]", items, out);
            out.push('|');
            canonical_type(tail, out);
        }
        core_ir::Type::Union(items) => canonical_type_list("union(", ")", items, out),
        core_ir::Type::Inter(items) => canonical_type_list("inter(", ")", items, out),
        core_ir::Type::Recursive { var, body } => {
            out.push_str("rec ");
            out.push_str(&var.0);
            out.push('.');
            canonical_type(body, out);
        }
    }
}

pub(super) fn canonical_type_arg(arg: &core_ir::TypeArg, out: &mut String) {
    match arg {
        core_ir::TypeArg::Type(ty) => canonical_type(ty, out),
        core_ir::TypeArg::Bounds(bounds) => {
            out.push_str("bounds(");
            if let Some(lower) = bounds.lower.as_deref() {
                canonical_type(lower, out);
            }
            out.push_str("..");
            if let Some(upper) = bounds.upper.as_deref() {
                canonical_type(upper, out);
            }
            out.push(')');
        }
    }
}

pub(super) fn canonical_type_list(
    open: &str,
    close: &str,
    items: &[core_ir::Type],
    out: &mut String,
) {
    out.push_str(open);
    for (index, item) in items.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        canonical_type(item, out);
    }
    out.push_str(close);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Root;

    #[test]
    pub(super) fn monomorphizes_instantiated_direct_call_once() {
        let a = core_ir::TypeVar("a".to_string());
        let id_path = core_ir::Path::from_name(core_ir::Name("id".to_string()));
        let int = named_type("int");
        let id_ty = RuntimeType::fun(
            RuntimeType::core(core_ir::Type::Var(a.clone())),
            RuntimeType::core(core_ir::Type::Var(a.clone())),
        );
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![Binding {
                name: id_path.clone(),
                type_params: vec![a.clone()],
                scheme: core_ir::Scheme {
                    requirements: Vec::new(),
                    body: core_ir::Type::Fun {
                        param: Box::new(core_ir::Type::Var(a.clone())),
                        param_effect: Box::new(core_ir::Type::Never),
                        ret_effect: Box::new(core_ir::Type::Never),
                        ret: Box::new(core_ir::Type::Var(a.clone())),
                    },
                },
                body: Expr::typed(
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Var(core_ir::Path::from_name(core_ir::Name("x".to_string()))),
                            RuntimeType::core(core_ir::Type::Var(a.clone())),
                        )),
                    },
                    id_ty.clone(),
                ),
            }],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(ExprKind::Var(id_path.clone()), id_ty)),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        int.clone(),
                    )),
                    evidence: None,
                    instantiation: Some(TypeInstantiation {
                        target: id_path.clone(),
                        args: vec![crate::ir::TypeSubstitution {
                            var: a,
                            ty: int.clone(),
                        }],
                    }),
                },
                int.clone(),
            )],
            roots: vec![Root::Expr(0)],
        };

        let module = monomorphize_module(module).expect("monomorphized");

        assert_eq!(module.bindings.len(), 1);
        let specialized = &module.bindings[0];
        assert!(specialized.type_params.is_empty());
        let ExprKind::Apply {
            callee,
            instantiation,
            ..
        } = &module.root_exprs[0].kind
        else {
            panic!("root should be an apply");
        };
        assert!(instantiation.is_none());
        assert!(matches!(&callee.kind, ExprKind::Var(path) if path == &specialized.name));
    }

    #[test]
    pub(super) fn reuses_specialization_for_same_type_arguments() {
        let a = core_ir::TypeVar("a".to_string());
        let id_path = core_ir::Path::from_name(core_ir::Name("id".to_string()));
        let int = named_type("int");
        let id_ty = RuntimeType::fun(
            RuntimeType::core(core_ir::Type::Var(a.clone())),
            RuntimeType::core(core_ir::Type::Var(a.clone())),
        );
        let instantiation = TypeInstantiation {
            target: id_path.clone(),
            args: vec![crate::ir::TypeSubstitution {
                var: a.clone(),
                ty: int.clone(),
            }],
        };
        let call = || {
            Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(ExprKind::Var(id_path.clone()), id_ty.clone())),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        int.clone(),
                    )),
                    evidence: None,
                    instantiation: Some(instantiation.clone()),
                },
                int.clone(),
            )
        };
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![Binding {
                name: id_path.clone(),
                type_params: vec![a.clone()],
                scheme: core_ir::Scheme {
                    requirements: Vec::new(),
                    body: core_ir::Type::Fun {
                        param: Box::new(core_ir::Type::Var(a.clone())),
                        param_effect: Box::new(core_ir::Type::Never),
                        ret_effect: Box::new(core_ir::Type::Never),
                        ret: Box::new(core_ir::Type::Var(a.clone())),
                    },
                },
                body: Expr::typed(
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Var(core_ir::Path::from_name(core_ir::Name("x".to_string()))),
                            RuntimeType::core(core_ir::Type::Var(a)),
                        )),
                    },
                    id_ty.clone(),
                ),
            }],
            root_exprs: vec![call(), call()],
            roots: vec![Root::Expr(0), Root::Expr(1)],
        };

        let module = monomorphize_module(module).expect("monomorphized");

        assert_eq!(module.bindings.len(), 1);
        let specialized = &module.bindings[0].name;
        for root in &module.root_exprs {
            let ExprKind::Apply { callee, .. } = &root.kind else {
                panic!("root should be an apply");
            };
            assert!(matches!(&callee.kind, ExprKind::Var(path) if path == specialized));
        }
    }

    pub(super) fn named_type(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }
}
