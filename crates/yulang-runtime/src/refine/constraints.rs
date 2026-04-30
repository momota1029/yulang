use super::*;

pub(super) struct TypeConstraints {
    pub(super) binding_types: HashMap<core_ir::Path, RuntimeType>,
    locals: HashMap<core_ir::Path, RuntimeType>,
    substitutions: BTreeMap<core_ir::TypeVar, core_ir::Type>,
}

impl TypeConstraints {
    pub(super) fn new(module: &Module) -> Self {
        Self {
            binding_types: module
                .bindings
                .iter()
                .map(|binding| {
                    let params = binding.type_params.iter().cloned().collect::<BTreeSet<_>>();
                    (
                        binding.name.clone(),
                        project_runtime_hir_type_with_vars(&binding.scheme.body, &params),
                    )
                })
                .collect(),
            locals: HashMap::new(),
            substitutions: BTreeMap::new(),
        }
    }

    pub(super) fn collect_expr(&mut self, expr: &Expr, expected: Option<&RuntimeType>) {
        if let Some(expected) = expected {
            self.unify_hir(&expr.ty, expected);
        }

        match &expr.kind {
            ExprKind::Var(path) => {
                if let Some(local_ty) = self.locals.get(path).cloned() {
                    self.unify_hir(&expr.ty, &local_ty);
                    if let Some(expected) = expected {
                        self.unify_hir(&local_ty, expected);
                    }
                    return;
                }
                if let Some(binding_ty) = self.binding_types.get(path).cloned() {
                    if !hir_type_has_vars(&binding_ty) {
                        self.unify_hir(&expr.ty, &binding_ty);
                        if let Some(expected) = expected {
                            self.unify_hir(&binding_ty, expected);
                        }
                    }
                }
            }
            ExprKind::EffectOp(_) | ExprKind::PrimitiveOp(_) | ExprKind::Lit(_) => {}
            ExprKind::Lambda {
                param: param_name,
                body,
                ..
            } => {
                if let RuntimeType::Fun { param, ret } = self.resolve_hir(&expr.ty) {
                    let local = core_ir::Path::from_name(param_name.clone());
                    let previous = push_binding(&mut self.locals, local, *param);
                    self.collect_expr(body, Some(&ret));
                    pop_bindings(&mut self.locals, previous);
                } else {
                    self.collect_expr(body, None);
                }
            }
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                ..
            } => {
                let expected_callee = RuntimeType::fun(arg.ty.clone(), expr.ty.clone());
                self.unify_hir(&callee.ty, &expected_callee);
                if let Some(evidence) = evidence {
                    self.unify_hir_bounds(&callee.ty, &evidence.callee);
                    self.unify_hir_bounds(&arg.ty, &evidence.arg);
                    self.unify_hir_bounds(&expr.ty, &evidence.result);
                }
                self.collect_expr(callee, Some(&expected_callee));
                self.collect_expr(arg, None);
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                evidence,
            } => {
                if let Some(evidence) = evidence {
                    self.unify_core(core_type(&expr.ty), &evidence.result);
                }
                self.collect_expr(cond, None);
                self.collect_expr(then_branch, Some(&expr.ty));
                self.collect_expr(else_branch, Some(&expr.ty));
            }
            ExprKind::Tuple(items) => {
                if let RuntimeType::Core(core_ir::Type::Tuple(expected_items)) = &expr.ty {
                    for (item, expected) in items.iter().zip(expected_items) {
                        self.collect_expr(item, Some(&RuntimeType::core(expected.clone())));
                    }
                } else {
                    for item in items {
                        self.collect_expr(item, None);
                    }
                }
            }
            ExprKind::Record { fields, spread } => {
                for field in fields {
                    let expected = record_field_type(&expr.ty, &field.name);
                    self.collect_expr(&field.value, expected.as_ref());
                }
                if let Some(spread) = spread {
                    match spread {
                        RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                            self.collect_expr(expr, None);
                        }
                    }
                }
            }
            ExprKind::Variant { value, .. } => {
                if let Some(value) = value {
                    self.collect_expr(value, None);
                }
            }
            ExprKind::Select { base, .. } => self.collect_expr(base, None),
            ExprKind::Match {
                scrutinee,
                arms,
                evidence,
            } => {
                self.unify_core_bounds(
                    core_type(&expr.ty),
                    &core_ir::TypeBounds::exact(evidence.result.clone()),
                );
                self.collect_expr(scrutinee, None);
                for arm in arms {
                    self.collect_pattern(&arm.pattern, Some(&scrutinee.ty));
                    let bindings = pattern_bindings(&arm.pattern);
                    let previous = push_bindings(&mut self.locals, &bindings);
                    if let Some(guard) = &arm.guard {
                        self.collect_expr(guard, None);
                    }
                    self.collect_expr(&arm.body, Some(&expr.ty));
                    pop_bindings(&mut self.locals, previous);
                }
            }
            ExprKind::Block { stmts, tail } => {
                let saved = self.locals.clone();
                for stmt in stmts {
                    self.collect_stmt(stmt);
                    push_stmt_bindings(&mut self.locals, stmt);
                }
                if let Some(tail) = tail {
                    self.collect_expr(tail, Some(&expr.ty));
                }
                self.locals = saved;
            }
            ExprKind::Handle {
                body,
                arms,
                evidence,
                ..
            } => {
                self.unify_core_bounds(
                    core_type(&expr.ty),
                    &core_ir::TypeBounds::exact(evidence.result.clone()),
                );
                self.collect_expr(body, None);
                for arm in arms {
                    self.collect_pattern(&arm.payload, None);
                    let mut bindings = pattern_bindings(&arm.payload);
                    if let Some(resume) = &arm.resume {
                        bindings.push((
                            core_ir::Path::from_name(resume.name.clone()),
                            resume.ty.clone(),
                        ));
                    }
                    let previous = push_bindings(&mut self.locals, &bindings);
                    if let Some(guard) = &arm.guard {
                        self.collect_expr(guard, None);
                    }
                    self.collect_expr(&arm.body, Some(&expr.ty));
                    pop_bindings(&mut self.locals, previous);
                }
            }
            ExprKind::BindHere { expr: inner } => {
                if let RuntimeType::Thunk { value, .. } = &inner.ty {
                    self.unify_hir(&expr.ty, value);
                    self.collect_expr(
                        inner,
                        Some(&RuntimeType::thunk(
                            thunk_effect(&inner.ty).unwrap(),
                            value.as_ref().clone(),
                        )),
                    );
                } else {
                    self.collect_expr(inner, Some(&expr.ty));
                }
            }
            ExprKind::Thunk {
                effect,
                value,
                expr: inner,
            } => {
                let (expected_effect, expected_value) = match &expr.ty {
                    RuntimeType::Thunk {
                        effect: expr_effect,
                        value: expr_value,
                    } => {
                        self.unify_core(effect, expr_effect);
                        self.unify_hir(value, expr_value);
                        (expr_effect.clone(), expr_value.as_ref().clone())
                    }
                    _ => (effect.clone(), value.clone()),
                };
                self.unify_hir(
                    &expr.ty,
                    &RuntimeType::thunk(expected_effect, expected_value.clone()),
                );
                self.collect_expr(inner, Some(&expected_value));
            }
            ExprKind::LocalPushId { body, .. } => self.collect_expr(body, Some(&expr.ty)),
            ExprKind::PeekId | ExprKind::FindId { .. } => {}
            ExprKind::AddId { thunk, .. } => self.collect_expr(thunk, Some(&expr.ty)),
            ExprKind::Coerce { from, to, expr } => {
                self.unify_core_bounds(
                    core_type(&expr.ty),
                    &core_ir::TypeBounds::exact(to.clone()),
                );
                self.collect_expr(expr, Some(&RuntimeType::core(from.clone())));
            }
            ExprKind::Pack { expr: inner, .. } => self.collect_expr(inner, Some(&expr.ty)),
        }
    }

    pub(super) fn collect_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Let { pattern, value } => {
                self.collect_pattern(pattern, Some(&value.ty));
                self.collect_expr(value, pattern_type(pattern).as_ref());
            }
            Stmt::Expr(expr) => self.collect_expr(expr, None),
            Stmt::Module { def, body } => {
                let previous = push_binding(&mut self.locals, def.clone(), body.ty.clone());
                self.collect_expr(body, Some(&body.ty));
                pop_bindings(&mut self.locals, previous);
            }
        }
    }

    pub(super) fn collect_pattern(&mut self, pattern: &Pattern, expected: Option<&RuntimeType>) {
        if let Some(expected) = expected {
            if let Some(ty) = pattern_type(pattern) {
                self.unify_hir(&ty, expected);
            }
        }
        match pattern {
            Pattern::Tuple { items, .. } => {
                for item in items {
                    self.collect_pattern(item, None);
                }
            }
            Pattern::List {
                prefix,
                spread,
                suffix,
                ..
            } => {
                for item in prefix {
                    self.collect_pattern(item, None);
                }
                if let Some(spread) = spread {
                    self.collect_pattern(spread, None);
                }
                for item in suffix {
                    self.collect_pattern(item, None);
                }
            }
            Pattern::Record { fields, spread, .. } => {
                for field in fields {
                    self.collect_pattern(&field.pattern, None);
                    if let Some(default) = &field.default {
                        self.collect_expr(default, pattern_type(&field.pattern).as_ref());
                    }
                }
                if let Some(spread) = spread {
                    match spread {
                        RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                            self.collect_pattern(pattern, None)
                        }
                    }
                }
            }
            Pattern::Variant { value, .. } => {
                if let Some(value) = value {
                    self.collect_pattern(value, None);
                }
            }
            Pattern::Or { left, right, .. } => {
                self.collect_pattern(left, None);
                self.collect_pattern(right, None);
            }
            Pattern::As { pattern, .. } => self.collect_pattern(pattern, None),
            Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => {}
        }
    }

    pub(super) fn unify_hir_bounds(&mut self, actual: &RuntimeType, bounds: &core_ir::TypeBounds) {
        if let Some(ty) = project_runtime_bounds(bounds) {
            self.unify_hir(
                actual,
                &project_runtime_hir_type_with_vars(&ty, &all_type_vars(&ty)),
            );
        }
    }

    pub(super) fn unify_core_bounds(
        &mut self,
        actual: &core_ir::Type,
        bounds: &core_ir::TypeBounds,
    ) {
        if let Some(ty) = project_runtime_bounds(bounds) {
            self.unify_core(actual, &ty);
        }
    }

    pub(super) fn unify_hir(&mut self, left: &RuntimeType, right: &RuntimeType) {
        match (self.resolve_hir(left), self.resolve_hir(right)) {
            (RuntimeType::Core(left), RuntimeType::Core(right)) => self.unify_core(&left, &right),
            (
                RuntimeType::Fun { param, ret },
                RuntimeType::Fun {
                    param: right_param,
                    ret: right_ret,
                },
            ) => {
                self.unify_hir(&param, &right_param);
                self.unify_hir(&ret, &right_ret);
            }
            (
                RuntimeType::Thunk { effect, value },
                RuntimeType::Thunk {
                    effect: right_effect,
                    value: right_value,
                },
            ) => {
                self.unify_core(&effect, &right_effect);
                self.unify_hir(&value, &right_value);
            }
            (RuntimeType::Thunk { value, .. }, other)
            | (other, RuntimeType::Thunk { value, .. }) => {
                self.unify_hir(&value, &other);
            }
            (RuntimeType::Fun { .. }, RuntimeType::Core(core_ir::Type::Fun { .. }))
            | (RuntimeType::Core(core_ir::Type::Fun { .. }), RuntimeType::Fun { .. }) => {
                let left = core_function_as_hir_type(&left);
                let right = core_function_as_hir_type(&right);
                self.unify_hir(&left, &right);
            }
            _ => {}
        }
    }

    pub(super) fn unify_core(&mut self, left: &core_ir::Type, right: &core_ir::Type) {
        let left = self.resolve_core(left);
        let right = self.resolve_core(right);
        if left == right
            || matches!(left, core_ir::Type::Any)
            || matches!(right, core_ir::Type::Any)
        {
            return;
        }
        match (&left, &right) {
            (core_ir::Type::Var(var), ty) => self.bind_var(var.clone(), ty.clone()),
            (ty, core_ir::Type::Var(var)) => self.bind_var(var.clone(), ty.clone()),
            (
                core_ir::Type::Named { path, args },
                core_ir::Type::Named {
                    path: right_path,
                    args: right_args,
                },
            ) if path == right_path && args.len() == right_args.len() => {
                for (arg, right_arg) in args.iter().zip(right_args) {
                    self.unify_type_arg(arg, right_arg);
                }
            }
            (
                core_ir::Type::Fun {
                    param,
                    param_effect,
                    ret_effect,
                    ret,
                },
                core_ir::Type::Fun {
                    param: right_param,
                    param_effect: right_param_effect,
                    ret_effect: right_ret_effect,
                    ret: right_ret,
                },
            ) => {
                self.unify_core(param, right_param);
                self.unify_core(param_effect, right_param_effect);
                self.unify_core(ret_effect, right_ret_effect);
                self.unify_core(ret, right_ret);
            }
            (core_ir::Type::Tuple(items), core_ir::Type::Tuple(right_items))
                if items.len() == right_items.len() =>
            {
                for (item, right_item) in items.iter().zip(right_items) {
                    self.unify_core(item, right_item);
                }
            }
            (core_ir::Type::Record(record), core_ir::Type::Record(right_record)) => {
                for field in &record.fields {
                    if let Some(right_field) = right_record
                        .fields
                        .iter()
                        .find(|right_field| right_field.name == field.name)
                    {
                        self.unify_core(&field.value, &right_field.value);
                    }
                }
            }
            (
                core_ir::Type::Row { items, tail },
                core_ir::Type::Row {
                    items: right_items,
                    tail: right_tail,
                },
            ) => self.unify_effect_row(items, tail, right_items, right_tail),
            (core_ir::Type::Union(items), ty) | (ty, core_ir::Type::Union(items)) => {
                if matches!(ty, core_ir::Type::Never) {
                    return;
                }
                for item in items
                    .iter()
                    .filter(|item| !matches!(item, core_ir::Type::Never))
                {
                    self.unify_core(item, ty);
                }
            }
            (core_ir::Type::Inter(items), ty) | (ty, core_ir::Type::Inter(items)) => {
                for item in items {
                    self.unify_core(item, ty);
                }
            }
            (core_ir::Type::Recursive { body, .. }, ty)
            | (ty, core_ir::Type::Recursive { body, .. }) => self.unify_core(body, ty),
            _ => {}
        }
    }

    pub(super) fn unify_type_arg(&mut self, left: &core_ir::TypeArg, right: &core_ir::TypeArg) {
        match (left, right) {
            (core_ir::TypeArg::Type(left), core_ir::TypeArg::Type(right)) => {
                self.unify_core(left, right);
            }
            (core_ir::TypeArg::Type(left), core_ir::TypeArg::Bounds(right)) => {
                self.unify_core_bounds(left, right);
            }
            (core_ir::TypeArg::Bounds(left), core_ir::TypeArg::Type(right)) => {
                self.unify_core_bounds(right, left);
            }
            (core_ir::TypeArg::Bounds(left), core_ir::TypeArg::Bounds(right)) => {
                if let (Some(left), Some(right)) =
                    (project_runtime_bounds(left), project_runtime_bounds(right))
                {
                    self.unify_core(&left, &right);
                }
            }
        }
    }

    pub(super) fn unify_effect_row(
        &mut self,
        items: &[core_ir::Type],
        tail: &core_ir::Type,
        right_items: &[core_ir::Type],
        right_tail: &core_ir::Type,
    ) {
        let mut matched_right = vec![false; right_items.len()];
        let mut left_row_vars = Vec::new();
        for item in items {
            match item {
                core_ir::Type::Var(var) => left_row_vars.push(var.clone()),
                _ => {
                    for (index, right_item) in right_items.iter().enumerate() {
                        if matched_right[index] || !same_effect_head(item, right_item) {
                            continue;
                        }
                        self.unify_core(item, right_item);
                        matched_right[index] = true;
                        break;
                    }
                }
            }
        }
        let residual = effect_row(
            right_items
                .iter()
                .enumerate()
                .filter_map(|(index, item)| (!matched_right[index]).then_some(item.clone()))
                .collect(),
            right_tail.clone(),
        );
        for var in left_row_vars {
            self.bind_var(var, residual.clone());
        }
        self.unify_core(tail, &residual);
    }

    pub(super) fn bind_var(&mut self, var: core_ir::TypeVar, ty: core_ir::Type) {
        let ty = self.resolve_core(&ty);
        if matches!(&ty, core_ir::Type::Var(actual) if actual == &var)
            || matches!(ty, core_ir::Type::Any)
        {
            return;
        }
        if occurs_in(&var, &ty) {
            return;
        }
        match self.substitutions.get(&var).cloned() {
            Some(existing) => {
                self.substitutions
                    .insert(var, choose_refined_substitution(existing, ty));
            }
            None => {
                self.substitutions.insert(var, ty);
            }
        }
    }

    pub(super) fn resolve_hir(&self, ty: &RuntimeType) -> RuntimeType {
        substitute_hir_type(ty, &self.substitutions)
    }

    pub(super) fn resolve_core(&self, ty: &core_ir::Type) -> core_ir::Type {
        substitute_type(ty, &self.substitutions)
    }

    pub(super) fn into_substitutions(self) -> BTreeMap<core_ir::TypeVar, core_ir::Type> {
        self.substitutions
            .iter()
            .map(|(var, ty)| (var.clone(), substitute_type(ty, &self.substitutions)))
            .collect()
    }
}
