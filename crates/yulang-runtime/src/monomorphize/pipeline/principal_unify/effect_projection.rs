use super::*;

pub(super) fn merge_effects(left: typed_ir::Type, right: typed_ir::Type) -> typed_ir::Type {
    if effect_is_empty(&left) {
        return right;
    }
    if effect_is_empty(&right) || left == right {
        return left;
    }
    let mut items = effect_items(left);
    for item in effect_items(right) {
        merge_effect_item_into(&mut items, item);
    }
    if items.len() == 1 {
        items.pop().unwrap()
    } else {
        typed_ir::Type::Row {
            items,
            tail: Box::new(typed_ir::Type::Never),
        }
    }
}

pub(super) fn effect_payload_type_for_operation(
    effect: &typed_ir::Type,
    operation: &typed_ir::Path,
) -> Option<typed_ir::Type> {
    effect_operation_namespace(operation)
        .and_then(|namespace| effect_payload_type_for_namespace(effect, &namespace))
        .or_else(|| effect_payload_type_for_namespace(effect, operation))
        .or_else(|| relative_operation_payload_type(effect, operation))
}

pub(super) fn effect_payload_type_for_namespace(
    effect: &typed_ir::Type,
    namespace: &typed_ir::Path,
) -> Option<typed_ir::Type> {
    match effect {
        typed_ir::Type::Named { path, args } if path == namespace => {
            effect_payload_type_from_args(args)
        }
        typed_ir::Type::Row { items, tail } => {
            let payloads = items
                .iter()
                .chain(std::iter::once(tail.as_ref()))
                .filter_map(|item| effect_payload_type_for_namespace(item, namespace))
                .collect::<Vec<_>>();
            choose_effect_payload_type(payloads)
        }
        _ => None,
    }
}

pub(super) fn project_effect_payload_substitutions_from_expr(
    template_effect: &typed_ir::Type,
    expr: &Expr,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: &mut BTreeSet<typed_ir::TypeVar>,
) {
    let mut slots = Vec::new();
    collect_effect_payload_var_slots(template_effect, required_vars, &mut slots);
    for (namespace, var) in slots {
        let Some(payload) = effect_payload_type_for_namespace_in_expr(expr, &namespace) else {
            continue;
        };
        if !specialization_shape_usable(&payload) {
            continue;
        }
        insert_projected_value_substitution(substitutions, conflicts, var, payload);
    }
}

fn merge_effect_item_into(items: &mut Vec<typed_ir::Type>, incoming: typed_ir::Type) {
    for existing in items.iter_mut() {
        let Some(merged) = merge_same_effect_item(existing, &incoming) else {
            continue;
        };
        *existing = merged;
        return;
    }
    items.push(incoming);
}

fn merge_same_effect_item(
    existing: &typed_ir::Type,
    incoming: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    if existing == incoming {
        return Some(existing.clone());
    }
    let (
        typed_ir::Type::Named {
            path: existing_path,
            args: existing_args,
        },
        typed_ir::Type::Named {
            path: incoming_path,
            args: incoming_args,
        },
    ) = (existing, incoming)
    else {
        return None;
    };
    if existing_path != incoming_path || existing_args.len() != incoming_args.len() {
        return None;
    }
    let mut changed = false;
    let mut args = Vec::with_capacity(existing_args.len());
    for (existing_arg, incoming_arg) in existing_args.iter().zip(incoming_args) {
        let merged = merge_same_effect_arg(existing_arg, incoming_arg)?;
        changed |= &merged != existing_arg;
        args.push(merged);
    }
    Some(if changed {
        typed_ir::Type::Named {
            path: existing_path.clone(),
            args,
        }
    } else {
        existing.clone()
    })
}

fn merge_same_effect_arg(
    existing: &typed_ir::TypeArg,
    incoming: &typed_ir::TypeArg,
) -> Option<typed_ir::TypeArg> {
    match (existing, incoming) {
        (typed_ir::TypeArg::Type(existing), typed_ir::TypeArg::Type(incoming)) => {
            merge_same_effect_payload(existing, incoming).map(typed_ir::TypeArg::Type)
        }
        _ if existing == incoming => Some(existing.clone()),
        _ => None,
    }
}

fn merge_same_effect_payload(
    existing: &typed_ir::Type,
    incoming: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    if existing == incoming {
        return Some(existing.clone());
    }
    match (
        core_type_is_imprecise_runtime_slot(existing),
        core_type_is_imprecise_runtime_slot(incoming),
    ) {
        (true, false) => Some(incoming.clone()),
        (false, true) => Some(existing.clone()),
        _ => None,
    }
}

fn effect_items(effect: typed_ir::Type) -> Vec<typed_ir::Type> {
    match effect {
        typed_ir::Type::Never => Vec::new(),
        typed_ir::Type::Row { mut items, tail } => {
            if !effect_is_empty(&tail) {
                items.push(*tail);
            }
            items
        }
        other => vec![other],
    }
}

fn effect_operation_namespace(operation: &typed_ir::Path) -> Option<typed_ir::Path> {
    (operation.segments.len() > 1).then(|| typed_ir::Path {
        segments: operation.segments[..operation.segments.len() - 1].to_vec(),
    })
}

fn collect_effect_payload_var_slots(
    effect: &typed_ir::Type,
    required_vars: &BTreeSet<typed_ir::TypeVar>,
    out: &mut Vec<(typed_ir::Path, typed_ir::TypeVar)>,
) {
    match effect {
        typed_ir::Type::Named { path, args } => {
            for arg in args {
                let typed_ir::TypeArg::Type(typed_ir::Type::Var(var)) = arg else {
                    continue;
                };
                if required_vars.contains(var) {
                    out.push((path.clone(), var.clone()));
                }
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_effect_payload_var_slots(item, required_vars, out);
            }
            collect_effect_payload_var_slots(tail, required_vars, out);
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_effect_payload_var_slots(param, required_vars, out);
            collect_effect_payload_var_slots(param_effect, required_vars, out);
            collect_effect_payload_var_slots(ret_effect, required_vars, out);
            collect_effect_payload_var_slots(ret, required_vars, out);
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_effect_payload_var_slots(item, required_vars, out);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_effect_payload_var_slots(&field.value, required_vars, out);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        collect_effect_payload_var_slots(ty, required_vars, out);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_effect_payload_var_slots(payload, required_vars, out);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_effect_payload_var_slots(tail, required_vars, out);
            }
        }
        typed_ir::Type::Recursive { body, .. } => {
            collect_effect_payload_var_slots(body, required_vars, out);
        }
        typed_ir::Type::Var(_)
        | typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any => {}
    }
}

fn effect_payload_type_for_namespace_in_expr(
    expr: &Expr,
    namespace: &typed_ir::Path,
) -> Option<typed_ir::Type> {
    let mut payloads = Vec::new();
    collect_effect_payload_types_for_namespace_in_expr(expr, namespace, &mut payloads);
    let mut unique_payloads = Vec::new();
    for payload in payloads {
        if !unique_payloads.contains(&payload) {
            unique_payloads.push(payload);
        }
    }
    choose_effect_payload_type(unique_payloads)
}

fn collect_effect_payload_types_for_namespace_in_expr(
    expr: &Expr,
    namespace: &typed_ir::Path,
    out: &mut Vec<typed_ir::Type>,
) {
    let (_value, effect) = runtime_value_and_effect(&expr.ty);
    if let Some(payload) = effect_payload_type_for_namespace(&effect, namespace) {
        out.push(payload);
    }
    match &expr.kind {
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::Pack { expr: body, .. }
        | ExprKind::Coerce { expr: body, .. } => {
            collect_effect_payload_types_for_namespace_in_expr(body, namespace, out);
        }
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            ..
        } => {
            if let Some(payload) =
                effect_payload_type_from_apply_evidence(evidence.as_ref(), arg, namespace)
            {
                out.push(payload);
            }
            collect_effect_payload_types_for_namespace_in_expr(callee, namespace, out);
            collect_effect_payload_types_for_namespace_in_expr(arg, namespace, out);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_effect_payload_types_for_namespace_in_expr(cond, namespace, out);
            collect_effect_payload_types_for_namespace_in_expr(then_branch, namespace, out);
            collect_effect_payload_types_for_namespace_in_expr(else_branch, namespace, out);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_effect_payload_types_for_namespace_in_expr(item, namespace, out);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_effect_payload_types_for_namespace_in_expr(&field.value, namespace, out);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        collect_effect_payload_types_for_namespace_in_expr(expr, namespace, out);
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_effect_payload_types_for_namespace_in_expr(value, namespace, out);
            }
        }
        ExprKind::Select { base, .. } => {
            collect_effect_payload_types_for_namespace_in_expr(base, namespace, out);
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_effect_payload_types_for_namespace_in_expr(scrutinee, namespace, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_effect_payload_types_for_namespace_in_expr(guard, namespace, out);
                }
                collect_effect_payload_types_for_namespace_in_expr(&arm.body, namespace, out);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_effect_payload_types_for_namespace_in_stmt(stmt, namespace, out);
            }
            if let Some(tail) = tail {
                collect_effect_payload_types_for_namespace_in_expr(tail, namespace, out);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_effect_payload_types_for_namespace_in_expr(body, namespace, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_effect_payload_types_for_namespace_in_expr(guard, namespace, out);
                }
                collect_effect_payload_types_for_namespace_in_expr(&arm.body, namespace, out);
            }
        }
        ExprKind::AddId { thunk, .. } => {
            collect_effect_payload_types_for_namespace_in_expr(thunk, namespace, out);
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn effect_payload_type_from_apply_evidence(
    evidence: Option<&typed_ir::ApplyEvidence>,
    arg: &Expr,
    namespace: &typed_ir::Path,
) -> Option<typed_ir::Type> {
    let evidence = evidence?;
    let principal = evidence.principal_callee.as_ref()?;
    let (params, _ret, ret_effect) = core_fun_spine_parts_exact(principal, 1)?;
    let (param, _param_effect) = params.first()?;
    if effect_payload_type_for_namespace(&ret_effect, namespace).is_none() {
        return None;
    }
    let actual = runtime_core_type(&arg.ty);
    if !specialization_shape_usable(&actual) {
        return None;
    }
    let mut required_vars = BTreeSet::new();
    collect_core_type_vars(principal, &mut required_vars);
    if required_vars.is_empty() {
        return None;
    }
    let mut substitutions = evidence
        .substitutions
        .iter()
        .map(|substitution| (substitution.var.clone(), substitution.ty.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut conflicts = BTreeSet::new();
    project_closed_substitutions_from_type(
        param,
        &actual,
        &required_vars,
        &mut substitutions,
        &mut conflicts,
        false,
        64,
    );
    if !conflicts.is_empty() {
        return None;
    }
    let ret_effect = substitute_type(&ret_effect, &substitutions);
    effect_payload_type_for_namespace(&ret_effect, namespace)
}

fn collect_effect_payload_types_for_namespace_in_stmt(
    stmt: &Stmt,
    namespace: &typed_ir::Path,
    out: &mut Vec<typed_ir::Type>,
) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_effect_payload_types_for_namespace_in_expr(value, namespace, out);
        }
    }
}

fn choose_effect_payload_type(payloads: Vec<typed_ir::Type>) -> Option<typed_ir::Type> {
    let mut precise_non_unit = payloads.iter().filter(|payload| {
        !runtime_type_is_unit_core(payload) && !core_type_is_imprecise_runtime_slot(payload)
    });
    match (precise_non_unit.next(), precise_non_unit.next()) {
        (Some(payload), None) => return Some(payload.clone()),
        (Some(_), Some(_)) => return None,
        (None, _) => {}
    }
    let mut non_unit = payloads
        .iter()
        .filter(|payload| !runtime_type_is_unit_core(payload));
    match (non_unit.next(), non_unit.next()) {
        (Some(payload), None) => Some(payload.clone()),
        (Some(_), Some(_)) => None,
        (None, _) => payloads.into_iter().next(),
    }
}
