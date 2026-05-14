use super::*;

#[derive(Default)]
pub(super) struct LocalUseContextScope {
    pub(super) uses: BTreeMap<typed_ir::Name, typed_ir::Type>,
    pub(super) conflicts: BTreeSet<typed_ir::Name>,
}

pub(super) fn collect_block_local_use_contexts(
    stmts: &[Stmt],
    tail: Option<&Expr>,
) -> BTreeMap<typed_ir::Name, typed_ir::TypeBounds> {
    let mut uses = BTreeMap::<typed_ir::Name, typed_ir::Type>::new();
    let mut conflicts = BTreeSet::<typed_ir::Name>::new();
    for stmt in stmts {
        collect_stmt_local_use_contexts(stmt, &mut uses, &mut conflicts);
    }
    if let Some(tail) = tail {
        collect_expr_local_use_contexts(tail, &mut uses, &mut conflicts);
    }
    propagate_block_alias_local_use_contexts(stmts, &mut uses, &mut conflicts);
    for conflict in conflicts {
        uses.remove(&conflict);
    }
    uses.into_iter()
        .map(|(name, ty)| (name, typed_ir::TypeBounds::exact(ty)))
        .collect()
}

pub(super) fn local_use_context_scope_into_contexts(
    mut scope: LocalUseContextScope,
) -> BTreeMap<typed_ir::Name, typed_ir::TypeBounds> {
    for conflict in scope.conflicts {
        scope.uses.remove(&conflict);
    }
    scope
        .uses
        .into_iter()
        .map(|(name, ty)| (name, typed_ir::TypeBounds::exact(ty)))
        .collect()
}

pub(super) fn merge_local_use_contexts(
    target: &mut BTreeMap<typed_ir::Name, typed_ir::TypeBounds>,
    source: BTreeMap<typed_ir::Name, typed_ir::TypeBounds>,
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
    uses: &mut BTreeMap<typed_ir::Name, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::Name>,
) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_expr_local_use_contexts(value, uses, conflicts);
        }
    }
}

fn collect_expr_local_use_contexts(
    expr: &Expr,
    uses: &mut BTreeMap<typed_ir::Name, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::Name>,
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
            collect_apply_arg_local_use_context(callee, arg, uses, conflicts);
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
            let block_uses = collect_block_local_use_contexts(stmts, tail.as_deref());
            merge_collected_local_use_contexts(uses, conflicts, block_uses);
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

fn collect_apply_arg_local_use_context(
    callee: &Expr,
    arg: &Expr,
    uses: &mut BTreeMap<typed_ir::Name, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::Name>,
) {
    let ExprKind::Var(path) = &arg.kind else {
        return;
    };
    let [name] = path.segments.as_slice() else {
        return;
    };
    let Some(param) = runtime_function_param_type(&callee.ty) else {
        return;
    };
    if closed_slot_type_usable(&param, false) {
        insert_local_use_context(uses, conflicts, name.clone(), param);
    }
}

fn propagate_block_alias_local_use_contexts(
    stmts: &[Stmt],
    uses: &mut BTreeMap<typed_ir::Name, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::Name>,
) {
    for stmt in stmts.iter().rev() {
        let Stmt::Let { pattern, value } = stmt else {
            continue;
        };
        let Some(alias) = pattern_bind_name(pattern) else {
            continue;
        };
        let Some(alias_ty) = uses.get(alias).cloned() else {
            continue;
        };
        let ExprKind::Var(path) = &value.kind else {
            continue;
        };
        let [source] = path.segments.as_slice() else {
            continue;
        };
        insert_local_use_context(uses, conflicts, source.clone(), alias_ty);
    }
}

fn merge_collected_local_use_contexts(
    uses: &mut BTreeMap<typed_ir::Name, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::Name>,
    source: BTreeMap<typed_ir::Name, typed_ir::TypeBounds>,
) {
    for (name, bounds) in source {
        if let Some(ty) = closed_type_from_bounds(Some(&bounds)) {
            insert_local_use_context(uses, conflicts, name, ty);
        }
    }
}

pub(super) fn insert_local_use_context(
    uses: &mut BTreeMap<typed_ir::Name, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::Name>,
    name: typed_ir::Name,
    ty: typed_ir::Type,
) {
    if conflicts.contains(&name) {
        return;
    }
    match uses.get(&name) {
        Some(existing) => {
            if let Some(merged) = merge_projected_value_type_precision(existing, &ty) {
                uses.insert(name, merged);
            } else {
                uses.remove(&name);
                conflicts.insert(name);
            }
        }
        None => {
            uses.insert(name, ty);
        }
    }
}
