use super::*;

pub(in crate::generalize) fn live_covariant_stack_ids_in_root_and_roles(
    root: &CompactRoot,
    role_predicates: &[CompactRoleConstraint],
) -> FxHashSet<SubtractId> {
    let mut ids = FxHashSet::default();
    collect_live_stack_ids_in_type(&root.root, true, None, &mut ids);
    for rec in &root.rec_vars {
        collect_live_stack_ids_in_bounds(&rec.bounds, true, None, &mut ids);
    }
    for role in role_predicates {
        for input in &role.inputs {
            collect_live_stack_ids_in_bounds(&input.bounds, true, None, &mut ids);
        }
        for associated in &role.associated {
            collect_live_stack_ids_in_bounds(&associated.value.bounds, true, None, &mut ids);
        }
    }
    ids
}

pub(in crate::generalize) fn sorted_stack_quantifiers(
    root: &CompactRoot,
    role_predicates: &[CompactRoleConstraint],
    quantifier_set: &FxHashSet<TypeVar>,
) -> Vec<SubtractId> {
    let mut ids = FxHashSet::default();
    collect_live_stack_ids_in_type(&root.root, true, Some(quantifier_set), &mut ids);
    for rec in &root.rec_vars {
        collect_live_stack_ids_in_bounds(&rec.bounds, true, Some(quantifier_set), &mut ids);
    }
    for role in role_predicates {
        for input in &role.inputs {
            collect_live_stack_ids_in_bounds(&input.bounds, true, Some(quantifier_set), &mut ids);
        }
        for associated in &role.associated {
            collect_live_stack_ids_in_bounds(
                &associated.value.bounds,
                true,
                Some(quantifier_set),
                &mut ids,
            );
        }
    }
    let mut ids = ids.into_iter().collect::<Vec<_>>();
    ids.sort_by_key(|id| id.0);
    ids.dedup();
    ids
}

pub(in crate::generalize) fn all_stack_ids_in_root_and_roles(
    root: &CompactRoot,
    role_predicates: &[CompactRoleConstraint],
) -> FxHashSet<SubtractId> {
    let mut ids = FxHashSet::default();
    collect_all_stack_ids_in_type(&root.root, &mut ids);
    for rec in &root.rec_vars {
        collect_all_stack_ids_in_bounds(&rec.bounds, &mut ids);
    }
    for role in role_predicates {
        for input in &role.inputs {
            collect_all_stack_ids_in_bounds(&input.bounds, &mut ids);
        }
        for associated in &role.associated {
            collect_all_stack_ids_in_bounds(&associated.value.bounds, &mut ids);
        }
    }
    ids
}

pub(in crate::generalize) fn collect_live_stack_ids_in_type(
    ty: &CompactType,
    covariant: bool,
    var_filter: Option<&FxHashSet<TypeVar>>,
    out: &mut FxHashSet<SubtractId>,
) {
    if covariant {
        for var in &ty.vars {
            if var_filter.is_some_and(|filter| !filter.contains(&var.var)) {
                continue;
            }
            for entry in var.weight.entries() {
                if stack_entry_keeps_stack_id_live(entry) {
                    out.insert(entry.id);
                }
            }
        }
    }
    for args in ty.cons.values() {
        for arg in args {
            collect_live_stack_ids_in_bounds(arg, covariant, var_filter, out);
        }
    }
    for fun in &ty.funs {
        collect_live_stack_ids_in_type(&fun.arg, !covariant, var_filter, out);
        collect_live_stack_ids_in_type(&fun.arg_eff, !covariant, var_filter, out);
        collect_live_stack_ids_in_type(&fun.ret_eff, covariant, var_filter, out);
        collect_live_stack_ids_in_type(&fun.ret, covariant, var_filter, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_live_stack_ids_in_type(&field.value, covariant, var_filter, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_live_stack_ids_in_type(&field.value, covariant, var_filter, out);
        }
        collect_live_stack_ids_in_type(&spread.tail, covariant, var_filter, out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_live_stack_ids_in_type(payload, covariant, var_filter, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            collect_live_stack_ids_in_type(item, covariant, var_filter, out);
        }
    }
    for row in &ty.rows {
        for args in row.items.values() {
            for arg in args {
                collect_live_stack_ids_in_bounds(arg, covariant, var_filter, out);
            }
        }
        collect_live_stack_ids_in_type(&row.tail, covariant, var_filter, out);
    }
}

pub(in crate::generalize) fn collect_live_stack_ids_in_bounds(
    bounds: &CompactBounds,
    covariant: bool,
    var_filter: Option<&FxHashSet<TypeVar>>,
    out: &mut FxHashSet<SubtractId>,
) {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            collect_live_stack_ids_in_type(lower, covariant, var_filter, out);
            collect_live_stack_ids_in_type(upper, covariant, var_filter, out);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                collect_live_stack_ids_in_bounds(arg, covariant, var_filter, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_live_stack_ids_in_bounds(arg, !covariant, var_filter, out);
            collect_live_stack_ids_in_bounds(arg_eff, !covariant, var_filter, out);
            collect_live_stack_ids_in_bounds(ret_eff, covariant, var_filter, out);
            collect_live_stack_ids_in_bounds(ret, covariant, var_filter, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                collect_live_stack_ids_in_bounds(&field.value, covariant, var_filter, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_live_stack_ids_in_bounds(payload, covariant, var_filter, out);
                }
            }
        }
    }
}

pub(in crate::generalize) fn stack_entry_keeps_stack_id_live(
    entry: &poly::types::StackWeightEntry,
) -> bool {
    !entry.stack.is_empty()
}

pub(in crate::generalize) fn collect_all_stack_ids_in_type(
    ty: &CompactType,
    out: &mut FxHashSet<SubtractId>,
) {
    for var in &ty.vars {
        for id in var.weight.iter() {
            out.insert(id);
        }
    }
    for args in ty.cons.values() {
        for arg in args {
            collect_all_stack_ids_in_bounds(arg, out);
        }
    }
    for fun in &ty.funs {
        collect_all_stack_ids_in_type(&fun.arg, out);
        collect_all_stack_ids_in_type(&fun.arg_eff, out);
        collect_all_stack_ids_in_type(&fun.ret_eff, out);
        collect_all_stack_ids_in_type(&fun.ret, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_all_stack_ids_in_type(&field.value, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_all_stack_ids_in_type(&field.value, out);
        }
        collect_all_stack_ids_in_type(&spread.tail, out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_all_stack_ids_in_type(payload, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            collect_all_stack_ids_in_type(item, out);
        }
    }
    for row in &ty.rows {
        for args in row.items.values() {
            for arg in args {
                collect_all_stack_ids_in_bounds(arg, out);
            }
        }
        collect_all_stack_ids_in_type(&row.tail, out);
    }
}

pub(in crate::generalize) fn collect_all_stack_ids_in_bounds(
    bounds: &CompactBounds,
    out: &mut FxHashSet<SubtractId>,
) {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            collect_all_stack_ids_in_type(lower, out);
            collect_all_stack_ids_in_type(upper, out);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                collect_all_stack_ids_in_bounds(arg, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_all_stack_ids_in_bounds(arg, out);
            collect_all_stack_ids_in_bounds(arg_eff, out);
            collect_all_stack_ids_in_bounds(ret_eff, out);
            collect_all_stack_ids_in_bounds(ret, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                collect_all_stack_ids_in_bounds(&field.value, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_all_stack_ids_in_bounds(payload, out);
                }
            }
        }
    }
}
