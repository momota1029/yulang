use super::*;

pub(super) fn canonicalize_equivalent_specializations(mut module: Module) -> Module {
    let residual_originals = module
        .bindings
        .iter()
        .filter(|binding| {
            !is_specialized_path(&binding.name)
                && (!binding.type_params.is_empty() || is_role_method_path(&binding.name))
        })
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    let mut groups: HashMap<String, Vec<usize>> = HashMap::new();
    for (index, binding) in module.bindings.iter().enumerate() {
        let Some(base) = unspecialized_path(&binding.name) else {
            continue;
        };
        if hir_type_has_vars(&binding.body.ty) {
            continue;
        }
        let mut key = canonical_path(&base);
        key.push('|');
        canonical_hir_type(&binding.body.ty, &mut key);
        groups.entry(key).or_default().push(index);
    }

    let mut replacements = HashMap::new();
    for indexes in groups.values() {
        let Some(best) = indexes.iter().min_by_key(|index| {
            specialization_quality(&module.bindings[**index], &residual_originals)
        }) else {
            continue;
        };
        let best_path = module.bindings[*best].name.clone();
        for index in indexes {
            let path = &module.bindings[*index].name;
            if path != &best_path {
                replacements.insert(path.clone(), best_path.clone());
            }
        }
    }
    if replacements.is_empty() {
        return module;
    }

    for binding in &mut module.bindings {
        rewrite_expr_paths(&mut binding.body, &replacements);
    }
    for expr in &mut module.root_exprs {
        rewrite_expr_paths(expr, &replacements);
    }
    for root in &mut module.roots {
        if let Root::Binding(path) = root
            && let Some(replacement) = replacements.get(path)
        {
            *path = replacement.clone();
        }
    }
    module
}

pub(super) fn inline_polymorphic_nullary_constructors(mut module: Module) -> Module {
    let constructors = module
        .bindings
        .iter()
        .filter_map(|binding| {
            if binding.type_params.is_empty() {
                return None;
            }
            let tag = nullary_constructor_tag(&binding.body)?;
            Some((binding.name.clone(), tag.clone()))
        })
        .collect::<HashMap<_, _>>();
    if constructors.is_empty() {
        return module;
    }
    for binding in &mut module.bindings {
        inline_constructor_expr(&mut binding.body, &constructors);
    }
    for expr in &mut module.root_exprs {
        inline_constructor_expr(expr, &constructors);
    }
    module
}

fn nullary_constructor_tag(expr: &Expr) -> Option<&core_ir::Name> {
    match &expr.kind {
        ExprKind::Variant { tag, value: None } => Some(tag),
        ExprKind::Coerce { expr, .. } => nullary_constructor_tag(expr),
        _ => None,
    }
}

fn specialization_quality(
    binding: &Binding,
    polymorphic_originals: &HashSet<core_ir::Path>,
) -> (usize, usize, usize) {
    let residual_refs = count_residual_refs(&binding.body, polymorphic_originals);
    let mut vars = BTreeSet::new();
    collect_expr_type_vars(&binding.body, &mut vars);
    let suffix = specialization_suffix(&binding.name).unwrap_or(usize::MAX);
    (residual_refs, vars.len(), usize::MAX - suffix)
}

fn count_residual_refs(expr: &Expr, residual_originals: &HashSet<core_ir::Path>) -> usize {
    let own = match &expr.kind {
        ExprKind::Var(path) | ExprKind::EffectOp(path) => {
            usize::from(residual_originals.contains(path))
        }
        _ => 0,
    };
    own + count_residual_child_refs(expr, residual_originals)
}

fn count_residual_child_refs(expr: &Expr, residual_originals: &HashSet<core_ir::Path>) -> usize {
    match &expr.kind {
        ExprKind::Lambda { body, .. } => count_residual_refs(body, residual_originals),
        ExprKind::Apply { callee, arg, .. } => {
            count_residual_refs(callee, residual_originals)
                + count_residual_refs(arg, residual_originals)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            count_residual_refs(cond, residual_originals)
                + count_residual_refs(then_branch, residual_originals)
                + count_residual_refs(else_branch, residual_originals)
        }
        ExprKind::Tuple(items) => items
            .iter()
            .map(|item| count_residual_refs(item, residual_originals))
            .sum(),
        ExprKind::Record { fields, spread } => {
            let fields = fields
                .iter()
                .map(|field| count_residual_refs(&field.value, residual_originals))
                .sum::<usize>();
            fields
                + spread
                    .as_ref()
                    .map(|spread| match spread {
                        RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                            count_residual_refs(expr, residual_originals)
                        }
                    })
                    .unwrap_or(0)
        }
        ExprKind::Variant {
            value: Some(value), ..
        }
        | ExprKind::Select { base: value, .. } => count_residual_refs(value, residual_originals),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            count_residual_refs(scrutinee, residual_originals)
                + arms
                    .iter()
                    .map(|arm| {
                        arm.guard
                            .as_ref()
                            .map(|guard| count_residual_refs(guard, residual_originals))
                            .unwrap_or(0)
                            + count_residual_refs(&arm.body, residual_originals)
                    })
                    .sum::<usize>()
        }
        ExprKind::Block { stmts, tail } => {
            stmts
                .iter()
                .map(|stmt| count_residual_stmt_refs(stmt, residual_originals))
                .sum::<usize>()
                + tail
                    .as_ref()
                    .map(|tail| count_residual_refs(tail, residual_originals))
                    .unwrap_or(0)
        }
        ExprKind::Handle { body, arms, .. } => {
            count_residual_refs(body, residual_originals)
                + arms
                    .iter()
                    .map(|arm| {
                        arm.guard
                            .as_ref()
                            .map(|guard| count_residual_refs(guard, residual_originals))
                            .unwrap_or(0)
                            + count_residual_refs(&arm.body, residual_originals)
                    })
                    .sum::<usize>()
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => count_residual_refs(expr, residual_originals),
        ExprKind::LocalPushId { body, .. } => count_residual_refs(body, residual_originals),
        ExprKind::AddId { thunk, .. } => count_residual_refs(thunk, residual_originals),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::Variant { value: None, .. }
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => 0,
    }
}

fn count_residual_stmt_refs(stmt: &Stmt, residual_originals: &HashSet<core_ir::Path>) -> usize {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            count_residual_refs(value, residual_originals)
        }
    }
}

fn inline_constructor_expr(expr: &mut Expr, constructors: &HashMap<core_ir::Path, core_ir::Name>) {
    if let ExprKind::Var(path) = &expr.kind
        && let Some(tag) = constructors.get(path)
    {
        expr.kind = ExprKind::Variant {
            tag: tag.clone(),
            value: None,
        };
        return;
    }
    match &mut expr.kind {
        ExprKind::Lambda { body, .. } => inline_constructor_expr(body, constructors),
        ExprKind::Apply { callee, arg, .. } => {
            inline_constructor_expr(callee, constructors);
            inline_constructor_expr(arg, constructors);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            inline_constructor_expr(cond, constructors);
            inline_constructor_expr(then_branch, constructors);
            inline_constructor_expr(else_branch, constructors);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                inline_constructor_expr(item, constructors);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                inline_constructor_expr(&mut field.value, constructors);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        inline_constructor_expr(expr, constructors);
                    }
                }
            }
        }
        ExprKind::Variant {
            value: Some(value), ..
        } => inline_constructor_expr(value, constructors),
        ExprKind::Select { base, .. } => inline_constructor_expr(base, constructors),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            inline_constructor_expr(scrutinee, constructors);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    inline_constructor_expr(guard, constructors);
                }
                inline_constructor_expr(&mut arm.body, constructors);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                inline_constructor_stmt(stmt, constructors);
            }
            if let Some(tail) = tail {
                inline_constructor_expr(tail, constructors);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            inline_constructor_expr(body, constructors);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    inline_constructor_expr(guard, constructors);
                }
                inline_constructor_expr(&mut arm.body, constructors);
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => inline_constructor_expr(expr, constructors),
        ExprKind::LocalPushId { body, .. } => inline_constructor_expr(body, constructors),
        ExprKind::AddId { thunk, .. } => inline_constructor_expr(thunk, constructors),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::Variant { value: None, .. }
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn inline_constructor_stmt(stmt: &mut Stmt, constructors: &HashMap<core_ir::Path, core_ir::Name>) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            inline_constructor_expr(value, constructors);
        }
    }
}

fn rewrite_expr_paths(expr: &mut Expr, replacements: &HashMap<core_ir::Path, core_ir::Path>) {
    match &mut expr.kind {
        ExprKind::Var(path) | ExprKind::EffectOp(path) => {
            if let Some(replacement) = replacements.get(path) {
                *path = replacement.clone();
            }
        }
        ExprKind::Lambda { body, .. } => rewrite_expr_paths(body, replacements),
        ExprKind::Apply { callee, arg, .. } => {
            rewrite_expr_paths(callee, replacements);
            rewrite_expr_paths(arg, replacements);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            rewrite_expr_paths(cond, replacements);
            rewrite_expr_paths(then_branch, replacements);
            rewrite_expr_paths(else_branch, replacements);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                rewrite_expr_paths(item, replacements);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                rewrite_expr_paths(&mut field.value, replacements);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        rewrite_expr_paths(expr, replacements);
                    }
                }
            }
        }
        ExprKind::Variant {
            value: Some(value), ..
        } => rewrite_expr_paths(value, replacements),
        ExprKind::Select { base, .. } => rewrite_expr_paths(base, replacements),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            rewrite_expr_paths(scrutinee, replacements);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    rewrite_expr_paths(guard, replacements);
                }
                rewrite_expr_paths(&mut arm.body, replacements);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                rewrite_stmt_paths(stmt, replacements);
            }
            if let Some(tail) = tail {
                rewrite_expr_paths(tail, replacements);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            rewrite_expr_paths(body, replacements);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    rewrite_expr_paths(guard, replacements);
                }
                rewrite_expr_paths(&mut arm.body, replacements);
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => rewrite_expr_paths(expr, replacements),
        ExprKind::LocalPushId { body, .. } => rewrite_expr_paths(body, replacements),
        ExprKind::AddId { thunk, .. } => rewrite_expr_paths(thunk, replacements),
        ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::Variant { value: None, .. }
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn rewrite_stmt_paths(stmt: &mut Stmt, replacements: &HashMap<core_ir::Path, core_ir::Path>) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            rewrite_expr_paths(value, replacements);
        }
    }
}

fn canonical_hir_type(ty: &RuntimeType, out: &mut String) {
    match ty {
        RuntimeType::Core(ty) => canonical_type(ty, out),
        RuntimeType::Fun { param, ret } => {
            out.push('(');
            canonical_hir_type(param, out);
            out.push_str(")->");
            canonical_hir_type(ret, out);
        }
        RuntimeType::Thunk { effect, value } => {
            out.push_str("Thunk[");
            canonical_type(effect, out);
            out.push(',');
            canonical_hir_type(value, out);
            out.push(']');
        }
    }
}
