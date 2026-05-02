use super::*;
use crate::types::{
    diagnostic_core_type, infer_type_substitutions, needs_runtime_coercion, runtime_core_type,
    type_compatible,
};

pub(super) fn substitute_specialize_module(module: Module) -> Module {
    SubstitutionSpecializer::new(module).run()
}

struct SubstitutionSpecializer {
    module: Module,
    generic_bindings: HashMap<core_ir::Path, Binding>,
    specializations: HashMap<String, core_ir::Path>,
    emitted: Vec<Binding>,
    next_index: usize,
    stats: HashMap<&'static str, usize>,
    specialization_body_depth: usize,
}

impl SubstitutionSpecializer {
    fn new(module: Module) -> Self {
        let generic_bindings = module
            .bindings
            .iter()
            .filter(|binding| !binding_substitution_vars(binding).is_empty())
            .map(|binding| (binding.name.clone(), binding.clone()))
            .collect::<HashMap<_, _>>();
        let next_index = next_substitution_specialization_index(&module);
        Self {
            module,
            generic_bindings,
            specializations: HashMap::new(),
            emitted: Vec::new(),
            next_index,
            stats: HashMap::new(),
            specialization_body_depth: 0,
        }
    }

    fn run(mut self) -> Module {
        let mut module = std::mem::replace(&mut self.module, empty_module());
        module.root_exprs = module
            .root_exprs
            .into_iter()
            .map(|expr| self.rewrite_expr(expr))
            .collect();
        module.bindings = module
            .bindings
            .into_iter()
            .map(|binding| Binding {
                body: self.rewrite_expr(binding.body),
                ..binding
            })
            .collect();
        self.debug_stats();
        module.bindings.extend(self.emitted);
        module
    }

    fn bump(&mut self, key: &'static str) {
        *self.stats.entry(key).or_default() += 1;
    }

    fn debug_stats(&self) {
        if std::env::var_os("YULANG_DEBUG_SUBST_SPECIALIZE").is_none() {
            return;
        }
        let mut stats = self.stats.iter().collect::<Vec<_>>();
        stats.sort_by_key(|(key, _)| **key);
        for (key, value) in stats {
            eprintln!("subst specialize {key}: {value}");
        }
    }

    fn rewrite_expr(&mut self, expr: Expr) -> Expr {
        let ty = expr.ty;
        let kind = match expr.kind {
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            } => {
                let callee = self.rewrite_expr(*callee);
                let arg = self.rewrite_expr(*arg);
                let expr = Expr {
                    ty,
                    kind: ExprKind::Apply {
                        callee: Box::new(callee),
                        arg: Box::new(arg),
                        evidence,
                        instantiation,
                    },
                };
                return self.rewrite_direct_generic_apply(expr);
            }
            ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body,
            } => ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body: Box::new(self.rewrite_expr(*body)),
            },
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                evidence,
            } => ExprKind::If {
                cond: Box::new(self.rewrite_expr(*cond)),
                then_branch: Box::new(self.rewrite_expr(*then_branch)),
                else_branch: Box::new(self.rewrite_expr(*else_branch)),
                evidence,
            },
            ExprKind::Tuple(items) => ExprKind::Tuple(
                items
                    .into_iter()
                    .map(|item| self.rewrite_expr(item))
                    .collect(),
            ),
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
            ExprKind::Variant { tag, value } => ExprKind::Variant {
                tag,
                value: value.map(|value| Box::new(self.rewrite_expr(*value))),
            },
            ExprKind::Select { base, field } => ExprKind::Select {
                base: Box::new(self.rewrite_expr(*base)),
                field,
            },
            ExprKind::Match {
                scrutinee,
                arms,
                evidence,
            } => ExprKind::Match {
                scrutinee: Box::new(self.rewrite_expr(*scrutinee)),
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        guard: arm.guard.map(|guard| self.rewrite_expr(guard)),
                        body: self.rewrite_expr(arm.body),
                    })
                    .collect(),
                evidence,
            },
            ExprKind::Block { stmts, tail } => ExprKind::Block {
                stmts: stmts
                    .into_iter()
                    .map(|stmt| self.rewrite_stmt(stmt))
                    .collect(),
                tail: tail.map(|tail| Box::new(self.rewrite_expr(*tail))),
            },
            ExprKind::Handle {
                body,
                arms,
                evidence,
                handler,
            } => ExprKind::Handle {
                body: Box::new(self.rewrite_expr(*body)),
                arms: arms
                    .into_iter()
                    .map(|arm| HandleArm {
                        effect: arm.effect,
                        payload: arm.payload,
                        resume: arm.resume,
                        guard: arm.guard.map(|guard| self.rewrite_expr(guard)),
                        body: self.rewrite_expr(arm.body),
                    })
                    .collect(),
                evidence,
                handler,
            },
            ExprKind::BindHere { expr } => ExprKind::BindHere {
                expr: Box::new(self.rewrite_expr(*expr)),
            },
            ExprKind::Thunk {
                effect,
                value,
                expr,
            } => ExprKind::Thunk {
                effect,
                value,
                expr: Box::new(self.rewrite_expr(*expr)),
            },
            ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
                id,
                body: Box::new(self.rewrite_expr(*body)),
            },
            ExprKind::AddId { id, allowed, thunk } => ExprKind::AddId {
                id,
                allowed,
                thunk: Box::new(self.rewrite_expr(*thunk)),
            },
            ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
                from,
                to,
                expr: Box::new(self.rewrite_expr(*expr)),
            },
            ExprKind::Pack { var, expr } => ExprKind::Pack {
                var,
                expr: Box::new(self.rewrite_expr(*expr)),
            },
            ExprKind::Var(_)
            | ExprKind::EffectOp(_)
            | ExprKind::PrimitiveOp(_)
            | ExprKind::Lit(_)
            | ExprKind::PeekId
            | ExprKind::FindId { .. } => expr.kind,
        };
        Expr { ty, kind }
    }

    fn rewrite_stmt(&mut self, stmt: Stmt) -> Stmt {
        match stmt {
            Stmt::Let { pattern, value } => Stmt::Let {
                pattern,
                value: self.rewrite_expr(value),
            },
            Stmt::Expr(expr) => Stmt::Expr(self.rewrite_expr(expr)),
            Stmt::Module { def, body } => Stmt::Module {
                def,
                body: self.rewrite_expr(body),
            },
        }
    }

    fn rewrite_direct_generic_apply(&mut self, expr: Expr) -> Expr {
        self.bump("apply");
        self.rewrite_generic_apply_spine(&expr).unwrap_or(expr)
    }

    fn rewrite_generic_apply_spine(&mut self, expr: &Expr) -> Option<Expr> {
        let Some(spine) = apply_spine(expr) else {
            self.bump("skip-non-var-spine");
            return None;
        };
        let Some(original) = self.generic_bindings.get(spine.target).cloned() else {
            self.bump("skip-non-generic-callee");
            return None;
        };
        let initial_substitutions =
            substitutions_from_instantiation(spine.instantiation, &original)
                .or_else(|| {
                    spine
                        .evidence
                        .and_then(|evidence| substitutions_from_evidence(evidence, &original))
                })
                .or_else(|| (self.specialization_body_depth > 0).then(BTreeMap::new));
        let Some(initial_substitutions) = initial_substitutions else {
            self.bump("skip-no-complete-substitution");
            debug_subst_specialize_skip("no-complete-substitution", spine.target, None);
            return None;
        };
        let principal_callee = spine
            .evidence
            .and_then(|evidence| evidence.principal_callee.as_ref())
            .unwrap_or(&original.scheme.body);
        let mut principal_substitutions = spine
            .evidence
            .map(evidence_substitution_map)
            .unwrap_or_default();
        principal_substitutions.extend(initial_substitutions);
        let mut callee_ty = substitute_type(principal_callee, &principal_substitutions);
        let Some((_params, ret)) = core_fun_spine(&callee_ty, spine.args.len()) else {
            self.bump("skip-non-function-principal");
            return None;
        };
        let actual_ret = diagnostic_core_type(&expr.ty);
        infer_direct_param_substitution(&ret, &actual_ret, &mut principal_substitutions);
        let mut ret_vars = BTreeSet::new();
        collect_core_type_vars(&ret, &mut ret_vars);
        infer_type_substitutions(&ret, &actual_ret, &ret_vars, &mut principal_substitutions);
        callee_ty = substitute_type(principal_callee, &principal_substitutions);
        let Some((params, ret)) = core_fun_spine(&callee_ty, spine.args.len()) else {
            self.bump("skip-non-function-principal");
            return None;
        };
        let params = if type_compatible(&ret, &actual_ret) {
            params
        } else {
            let mut vars = BTreeSet::new();
            collect_core_type_vars(&ret, &mut vars);
            infer_type_substitutions(&ret, &actual_ret, &vars, &mut principal_substitutions);
            callee_ty = substitute_type(principal_callee, &principal_substitutions);
            let Some((params, ret)) = core_fun_spine(&callee_ty, spine.args.len()) else {
                self.bump("skip-non-function-principal");
                return None;
            };
            if !type_compatible(&ret, &actual_ret) {
                self.bump("skip-ret-mismatch");
                debug_subst_specialize_skip(
                    "ret-mismatch",
                    spine.target,
                    Some((&actual_ret, &ret)),
                );
                return None;
            }
            params
        };
        for (arg, param) in spine.args.iter().zip(&params) {
            infer_direct_param_substitution(
                param,
                &runtime_core_type(&arg.ty),
                &mut principal_substitutions,
            );
            let mut vars = BTreeSet::new();
            collect_core_type_vars(param, &mut vars);
            infer_type_substitutions(
                param,
                &runtime_core_type(&arg.ty),
                &vars,
                &mut principal_substitutions,
            );
        }
        callee_ty = substitute_type(principal_callee, &principal_substitutions);
        let Some((params, ret)) = core_fun_spine(&callee_ty, spine.args.len()) else {
            self.bump("skip-non-function-principal");
            return None;
        };
        if !type_compatible(&ret, &actual_ret) {
            self.bump("skip-ret-mismatch");
            debug_subst_specialize_skip("ret-mismatch", spine.target, Some((&actual_ret, &ret)));
            return None;
        }
        let mut adapted_args = adapt_args_to_params(&spine.args, &params);
        if adapted_args.is_none() {
            for (arg, param) in spine.args.iter().zip(&params) {
                let mut vars = BTreeSet::new();
                collect_core_type_vars(param, &mut vars);
                infer_type_substitutions(
                    param,
                    &runtime_core_type(&arg.ty),
                    &vars,
                    &mut principal_substitutions,
                );
            }
            callee_ty = substitute_type(principal_callee, &principal_substitutions);
            let Some((params, ret)) = core_fun_spine(&callee_ty, spine.args.len()) else {
                self.bump("skip-non-function-principal");
                return None;
            };
            if actual_ret != ret {
                self.bump("skip-ret-mismatch");
                debug_subst_specialize_skip(
                    "ret-mismatch",
                    spine.target,
                    Some((&actual_ret, &ret)),
                );
                return None;
            }
            adapted_args = adapt_args_to_params(&spine.args, &params);
        }
        if std::env::var_os("YULANG_SUBST_SPECIALIZE_ADAPT_ARGS").is_none()
            && !args_already_match_params(&spine.args, &params)
        {
            self.bump("skip-arg-adaptation");
            debug_arg_mismatch(spine.target, &spine.args, &params);
            return None;
        }
        let Some(adapted_args) = adapted_args else {
            self.bump("skip-arg-mismatch");
            debug_arg_mismatch(spine.target, &spine.args, &params);
            return None;
        };

        let binding_substitutions =
            complete_binding_substitutions(&original, &principal_substitutions)?;
        let path = self.intern_specialization(original, binding_substitutions)?;
        self.bump("rewrite");
        let mut call = Expr::typed(ExprKind::Var(path), RuntimeType::core(callee_ty.clone()));
        let mut current = callee_ty;
        for (index, arg) in adapted_args.into_iter().enumerate() {
            let (_, next) = core_fun_parts(&current)?;
            let ty = if index + 1 == spine.args.len() {
                expr.ty.clone()
            } else {
                RuntimeType::core(next.clone())
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
        Some(call)
    }

    fn intern_specialization(
        &mut self,
        original: Binding,
        substitutions: BTreeMap<core_ir::TypeVar, core_ir::Type>,
    ) -> Option<core_ir::Path> {
        let key = substitution_key(&original.name, &substitutions);
        if let Some(path) = self.specializations.get(&key) {
            return Some(path.clone());
        }
        if std::env::var_os("YULANG_SUBST_SPECIALIZE_LEAF").is_none()
            && !binding_body_has_generic_apply(
                &original.body,
                &self.generic_bindings,
                Some(&original.name),
            )
        {
            self.bump("skip-leaf-specialization");
            return None;
        }
        let path = substitution_specialized_path(&original.name, self.next_index);
        self.next_index += 1;
        self.specializations.insert(key, path.clone());
        let mut binding = substitute_binding(original, &substitutions);
        binding.name = path.clone();
        binding.type_params.clear();
        self.specialization_body_depth += 1;
        binding.body = self.rewrite_expr(binding.body);
        self.specialization_body_depth -= 1;
        self.emitted.push(binding);
        Some(path)
    }
}

struct ApplySpine<'a> {
    target: &'a core_ir::Path,
    args: Vec<&'a Expr>,
    evidence: Option<&'a core_ir::ApplyEvidence>,
    instantiation: Option<&'a TypeInstantiation>,
}

fn apply_spine(expr: &Expr) -> Option<ApplySpine<'_>> {
    let mut current = expr;
    let mut args = Vec::new();
    let mut selected_evidence = None;
    let mut selected_instantiation = None;
    while let ExprKind::Apply {
        callee,
        arg,
        evidence,
        instantiation,
        ..
    } = &current.kind
    {
        args.push(arg.as_ref());
        if evidence
            .as_ref()
            .is_some_and(|evidence| evidence.principal_callee.is_some())
        {
            selected_evidence = evidence.as_ref();
        }
        if instantiation.is_some() {
            selected_instantiation = instantiation.as_ref();
        }
        current = callee;
    }
    let ExprKind::Var(target) = &current.kind else {
        return None;
    };
    args.reverse();
    Some(ApplySpine {
        target,
        args,
        evidence: selected_evidence,
        instantiation: selected_instantiation,
    })
}

fn binding_body_has_generic_apply(
    expr: &Expr,
    generic_bindings: &HashMap<core_ir::Path, Binding>,
    ignored_target: Option<&core_ir::Path>,
) -> bool {
    if apply_spine(expr).is_some_and(|spine| {
        generic_bindings.contains_key(spine.target) && ignored_target != Some(spine.target)
    }) {
        return true;
    }
    match &expr.kind {
        ExprKind::Apply { callee, arg, .. } => {
            binding_body_has_generic_apply(callee, generic_bindings, ignored_target)
                || binding_body_has_generic_apply(arg, generic_bindings, ignored_target)
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => {
            binding_body_has_generic_apply(body, generic_bindings, ignored_target)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            binding_body_has_generic_apply(cond, generic_bindings, ignored_target)
                || binding_body_has_generic_apply(then_branch, generic_bindings, ignored_target)
                || binding_body_has_generic_apply(else_branch, generic_bindings, ignored_target)
        }
        ExprKind::Tuple(items) => items
            .iter()
            .any(|item| binding_body_has_generic_apply(item, generic_bindings, ignored_target)),
        ExprKind::Record { fields, spread } => {
            fields.iter().any(|field| {
                binding_body_has_generic_apply(&field.value, generic_bindings, ignored_target)
            }) || spread.as_ref().is_some_and(|spread| match spread {
                RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                    binding_body_has_generic_apply(expr, generic_bindings, ignored_target)
                }
            })
        }
        ExprKind::Variant { value, .. } => value.as_ref().is_some_and(|value| {
            binding_body_has_generic_apply(value, generic_bindings, ignored_target)
        }),
        ExprKind::Select { base, .. } => {
            binding_body_has_generic_apply(base, generic_bindings, ignored_target)
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            binding_body_has_generic_apply(scrutinee, generic_bindings, ignored_target)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(|guard| {
                        binding_body_has_generic_apply(guard, generic_bindings, ignored_target)
                    }) || binding_body_has_generic_apply(
                        &arm.body,
                        generic_bindings,
                        ignored_target,
                    )
                })
        }
        ExprKind::Block { stmts, tail } => {
            stmts
                .iter()
                .any(|stmt| stmt_has_generic_apply(stmt, generic_bindings, ignored_target))
                || tail.as_ref().is_some_and(|tail| {
                    binding_body_has_generic_apply(tail, generic_bindings, ignored_target)
                })
        }
        ExprKind::Handle { body, arms, .. } => {
            binding_body_has_generic_apply(body, generic_bindings, ignored_target)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(|guard| {
                        binding_body_has_generic_apply(guard, generic_bindings, ignored_target)
                    }) || binding_body_has_generic_apply(
                        &arm.body,
                        generic_bindings,
                        ignored_target,
                    )
                })
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => false,
    }
}

fn stmt_has_generic_apply(
    stmt: &Stmt,
    generic_bindings: &HashMap<core_ir::Path, Binding>,
    ignored_target: Option<&core_ir::Path>,
) -> bool {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            binding_body_has_generic_apply(value, generic_bindings, ignored_target)
        }
    }
}

fn substitutions_from_instantiation(
    instantiation: Option<&TypeInstantiation>,
    binding: &Binding,
) -> Option<BTreeMap<core_ir::TypeVar, core_ir::Type>> {
    let instantiation = instantiation?;
    if instantiation.target != binding.name {
        return None;
    }
    let params = binding_substitution_vars(binding);
    let substitutions = instantiation
        .args
        .iter()
        .filter(|substitution| params.contains(&substitution.var))
        .map(|substitution| (substitution.var.clone(), substitution.ty.clone()))
        .collect::<BTreeMap<_, _>>();
    if params.is_empty() {
        return None;
    }
    if substitutions.len() == params.len()
        && substitutions.values().all(|ty| !core_type_has_vars(ty))
    {
        Some(substitutions)
    } else {
        None
    }
}

fn debug_subst_specialize_skip(
    reason: &str,
    target: &core_ir::Path,
    types: Option<(&core_ir::Type, &core_ir::Type)>,
) {
    if std::env::var_os("YULANG_DEBUG_SUBST_SPECIALIZE").is_none() {
        return;
    }
    if let Some((actual, expected)) = types {
        eprintln!(
            "subst specialize skip {reason} {target:?}: actual={actual:?} expected={expected:?}"
        );
    } else {
        eprintln!("subst specialize skip {reason} {target:?}");
    }
}

fn debug_arg_mismatch(target: &core_ir::Path, args: &[&Expr], params: &[core_ir::Type]) {
    if std::env::var_os("YULANG_DEBUG_SUBST_SPECIALIZE").is_none() {
        return;
    }
    for (index, (arg, param)) in args.iter().zip(params).enumerate() {
        let actual = runtime_core_type(&arg.ty);
        if actual != *param {
            eprintln!(
                "subst specialize skip arg-mismatch {target:?}[{index}]: actual={actual:?} expected={param:?}"
            );
        }
    }
}

fn evidence_substitution_map(
    evidence: &core_ir::ApplyEvidence,
) -> BTreeMap<core_ir::TypeVar, core_ir::Type> {
    evidence
        .substitutions
        .iter()
        .map(|substitution| (substitution.var.clone(), substitution.ty.clone()))
        .collect()
}

fn substitutions_from_evidence(
    evidence: &core_ir::ApplyEvidence,
    binding: &Binding,
) -> Option<BTreeMap<core_ir::TypeVar, core_ir::Type>> {
    if evidence.principal_callee.is_none() || evidence.substitutions.is_empty() {
        return None;
    }
    let params = binding_substitution_vars(binding);
    let substitutions = evidence
        .substitutions
        .iter()
        .filter(|substitution| params.contains(&substitution.var))
        .map(|substitution| (substitution.var.clone(), substitution.ty.clone()))
        .collect::<BTreeMap<_, _>>();
    if substitutions.values().all(|ty| !core_type_has_vars(ty))
        && (!substitutions.is_empty()
            || params.is_empty()
            || binding.type_params.is_empty()
            || substitutions.len() == params.len())
        && (binding.type_params.is_empty() || substitutions.len() == params.len())
    {
        Some(substitutions)
    } else {
        None
    }
}

fn complete_binding_substitutions(
    binding: &Binding,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Option<BTreeMap<core_ir::TypeVar, core_ir::Type>> {
    let params = binding_substitution_vars(binding);
    let out = params
        .into_iter()
        .map(|var| {
            let ty = substitutions.get(&var)?;
            (!core_type_has_vars(ty)).then(|| (var, ty.clone()))
        })
        .collect::<Option<BTreeMap<_, _>>>()?;
    (!out.is_empty()).then_some(out)
}

fn infer_direct_param_substitution(
    param: &core_ir::Type,
    actual: &core_ir::Type,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    if let core_ir::Type::Var(var) = param
        && !core_type_has_vars(actual)
    {
        substitutions
            .entry(var.clone())
            .or_insert_with(|| actual.clone());
    }
}

fn binding_substitution_vars(binding: &Binding) -> HashSet<core_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_binding_type_params(binding, &mut vars);
    vars.into_iter().collect()
}

fn adapt_value_to_core(expr: Expr, expected: &core_ir::Type) -> Option<Expr> {
    let actual = runtime_core_type(&expr.ty);
    if actual == *expected {
        return Some(expr);
    }
    if needs_runtime_coercion(expected, &actual) {
        return Some(Expr::typed(
            ExprKind::Coerce {
                from: actual,
                to: expected.clone(),
                expr: Box::new(expr),
            },
            RuntimeType::core(expected.clone()),
        ));
    }
    type_compatible(expected, &actual).then_some(expr)
}

fn adapt_args_to_params(args: &[&Expr], params: &[core_ir::Type]) -> Option<Vec<Expr>> {
    let mut out = Vec::with_capacity(args.len());
    for (arg, param) in args.iter().zip(params) {
        out.push(adapt_value_to_core((*arg).clone(), param)?);
    }
    Some(out)
}

fn args_already_match_params(args: &[&Expr], params: &[core_ir::Type]) -> bool {
    args.iter()
        .zip(params)
        .all(|(arg, param)| type_matches_exact_bounds(&runtime_core_type(&arg.ty), param))
}

fn type_matches_exact_bounds(actual: &core_ir::Type, expected: &core_ir::Type) -> bool {
    if actual == expected {
        return true;
    }
    match (actual, expected) {
        (
            core_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
            core_ir::Type::Named {
                path: expected_path,
                args: expected_args,
            },
        ) => {
            actual_path == expected_path
                && actual_args.len() == expected_args.len()
                && actual_args
                    .iter()
                    .zip(expected_args)
                    .all(|(actual, expected)| type_arg_matches_exact_bounds(actual, expected))
        }
        (
            core_ir::Type::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
            core_ir::Type::Fun {
                param: expected_param,
                param_effect: expected_param_effect,
                ret_effect: expected_ret_effect,
                ret: expected_ret,
            },
        ) => {
            type_matches_exact_bounds(actual_param, expected_param)
                && type_matches_exact_bounds(actual_param_effect, expected_param_effect)
                && type_matches_exact_bounds(actual_ret_effect, expected_ret_effect)
                && type_matches_exact_bounds(actual_ret, expected_ret)
        }
        (core_ir::Type::Tuple(actual), core_ir::Type::Tuple(expected))
        | (core_ir::Type::Union(actual), core_ir::Type::Union(expected))
        | (core_ir::Type::Inter(actual), core_ir::Type::Inter(expected)) => {
            type_list_matches_exact_bounds(actual, expected)
        }
        (
            core_ir::Type::Row { items, tail },
            core_ir::Type::Row {
                items: expected_items,
                tail: expected_tail,
            },
        ) => {
            type_list_matches_exact_bounds(items, expected_items)
                && type_matches_exact_bounds(tail, expected_tail)
        }
        _ => false,
    }
}

fn type_list_matches_exact_bounds(actual: &[core_ir::Type], expected: &[core_ir::Type]) -> bool {
    actual.len() == expected.len()
        && actual
            .iter()
            .zip(expected)
            .all(|(actual, expected)| type_matches_exact_bounds(actual, expected))
}

fn type_arg_matches_exact_bounds(actual: &core_ir::TypeArg, expected: &core_ir::TypeArg) -> bool {
    if actual == expected {
        return true;
    }
    match (actual, expected) {
        (core_ir::TypeArg::Type(actual), core_ir::TypeArg::Bounds(expected)) => {
            bounds_are_exact_type(expected, actual)
        }
        (core_ir::TypeArg::Bounds(actual), core_ir::TypeArg::Type(expected)) => {
            bounds_are_exact_type(actual, expected)
        }
        (core_ir::TypeArg::Bounds(actual), core_ir::TypeArg::Bounds(expected)) => {
            match (
                exact_type_from_bounds(actual),
                exact_type_from_bounds(expected),
            ) {
                (Some(actual), Some(expected)) => type_matches_exact_bounds(actual, expected),
                _ => false,
            }
        }
        _ => false,
    }
}

fn bounds_are_exact_type(bounds: &core_ir::TypeBounds, ty: &core_ir::Type) -> bool {
    exact_type_from_bounds(bounds).is_some_and(|exact| type_matches_exact_bounds(exact, ty))
}

fn exact_type_from_bounds(bounds: &core_ir::TypeBounds) -> Option<&core_ir::Type> {
    match (bounds.lower.as_deref(), bounds.upper.as_deref()) {
        (Some(lower), None) => Some(lower),
        (Some(lower), Some(upper)) if type_matches_exact_bounds(lower, upper) => Some(lower),
        _ => None,
    }
}

fn empty_module() -> Module {
    Module {
        path: core_ir::Path::default(),
        bindings: Vec::new(),
        root_exprs: Vec::new(),
        roots: Vec::new(),
    }
}

fn core_fun_parts(ty: &core_ir::Type) -> Option<(core_ir::Type, core_ir::Type)> {
    let core_ir::Type::Fun { param, ret, .. } = ty else {
        return None;
    };
    Some((param.as_ref().clone(), ret.as_ref().clone()))
}

fn core_fun_spine(ty: &core_ir::Type, arity: usize) -> Option<(Vec<core_ir::Type>, core_ir::Type)> {
    let mut params = Vec::with_capacity(arity);
    let mut current = ty.clone();
    for _ in 0..arity {
        let (param, ret) = core_fun_parts(&current)?;
        params.push(param);
        current = ret;
    }
    Some((params, current))
}

fn substitution_key(
    target: &core_ir::Path,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> String {
    let mut key = canonical_path(target);
    for (var, ty) in substitutions {
        key.push('|');
        key.push_str(&var.0);
        key.push('=');
        canonical_type(ty, &mut key);
    }
    key
}

fn substitution_specialized_path(target: &core_ir::Path, index: usize) -> core_ir::Path {
    let mut path = target.clone();
    match path.segments.last_mut() {
        Some(name) => name.0 = format!("{}__mono{index}", name.0),
        None => path.segments.push(core_ir::Name(format!("__mono{index}"))),
    }
    path
}

fn next_substitution_specialization_index(module: &Module) -> usize {
    module
        .bindings
        .iter()
        .filter_map(|binding| specialization_suffix(&binding.name))
        .max()
        .map(|index| index + 1)
        .unwrap_or(0)
}
