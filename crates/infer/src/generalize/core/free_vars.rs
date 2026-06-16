use super::*;

pub(in crate::generalize) fn collect_root_free_vars(root: &CompactRoot, out: &mut Vec<TypeVar>) {
    collect_type_free_vars(&root.root, out);
    for rec in &root.rec_vars {
        collect_recursive_var_free_vars(rec, out);
    }
}

pub(in crate::generalize) fn collect_role_free_vars(
    role: &CompactRoleConstraint,
    out: &mut Vec<TypeVar>,
) {
    for input in &role.inputs {
        collect_role_arg_free_vars(input, out);
    }
    for associated in &role.associated {
        collect_role_arg_free_vars(&associated.value, out);
    }
}

pub(in crate::generalize) fn collect_role_arg_free_vars(
    arg: &CompactRoleArg,
    out: &mut Vec<TypeVar>,
) {
    collect_bounds_free_vars(&arg.bounds, out);
}

pub(in crate::generalize) fn collect_recursive_var_free_vars(
    rec: &CompactRecursiveVar,
    out: &mut Vec<TypeVar>,
) {
    out.push(rec.var);
    collect_bounds_free_vars(&rec.bounds, out);
}

pub(in crate::generalize) fn collect_bounds_free_vars(
    bounds: &CompactBounds,
    out: &mut Vec<TypeVar>,
) {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            collect_type_free_vars(lower, out);
            collect_type_free_vars(upper, out);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                collect_bounds_free_vars(arg, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_bounds_free_vars(arg, out);
            collect_bounds_free_vars(arg_eff, out);
            collect_bounds_free_vars(ret_eff, out);
            collect_bounds_free_vars(ret, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                collect_bounds_free_vars(&field.value, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_bounds_free_vars(payload, out);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                collect_bounds_free_vars(item, out);
            }
        }
    }
}

pub(in crate::generalize) fn collect_type_free_vars(ty: &CompactType, out: &mut Vec<TypeVar>) {
    out.extend(ty.vars.iter().map(|var| var.var));
    for con in compact_con_entries(&ty.cons) {
        collect_con_free_vars(&con, out);
    }
    for fun in &ty.funs {
        collect_fun_free_vars(fun, out);
    }
    for record in &ty.records {
        collect_record_free_vars(record, out);
    }
    for spread in &ty.record_spreads {
        collect_record_spread_free_vars(spread, out);
    }
    for variant in &ty.poly_variants {
        collect_poly_variant_free_vars(variant, out);
    }
    for tuple in &ty.tuples {
        collect_tuple_free_vars(tuple, out);
    }
    for row in &ty.rows {
        collect_row_free_vars(row, out);
    }
}

pub(in crate::generalize) fn collect_con_free_vars(con: &CompactCon, out: &mut Vec<TypeVar>) {
    for arg in &con.args {
        collect_bounds_free_vars(arg, out);
    }
}

pub(in crate::generalize) fn collect_fun_free_vars(fun: &CompactFun, out: &mut Vec<TypeVar>) {
    collect_type_free_vars(&fun.arg, out);
    collect_type_free_vars(&fun.arg_eff, out);
    collect_type_free_vars(&fun.ret_eff, out);
    collect_type_free_vars(&fun.ret, out);
}

pub(in crate::generalize) fn collect_record_free_vars(
    record: &CompactRecord,
    out: &mut Vec<TypeVar>,
) {
    for field in &record.fields {
        collect_type_free_vars(&field.value, out);
    }
}

pub(in crate::generalize) fn collect_record_spread_free_vars(
    spread: &CompactRecordSpread,
    out: &mut Vec<TypeVar>,
) {
    for field in &spread.fields {
        collect_type_free_vars(&field.value, out);
    }
    collect_type_free_vars(&spread.tail, out);
}

pub(in crate::generalize) fn collect_poly_variant_free_vars(
    variant: &CompactPolyVariant,
    out: &mut Vec<TypeVar>,
) {
    for (_, payloads) in &variant.items {
        for payload in payloads {
            collect_type_free_vars(payload, out);
        }
    }
}

pub(in crate::generalize) fn collect_tuple_free_vars(tuple: &CompactTuple, out: &mut Vec<TypeVar>) {
    for item in &tuple.items {
        collect_type_free_vars(item, out);
    }
}

pub(in crate::generalize) fn collect_row_free_vars(row: &CompactRow, out: &mut Vec<TypeVar>) {
    for item in compact_row_item_entries(&row.items) {
        collect_con_free_vars(&item, out);
    }
    collect_type_free_vars(&row.tail, out);
}
