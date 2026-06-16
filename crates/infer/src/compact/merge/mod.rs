use super::*;

mod entries;
pub(crate) use entries::*;

pub(super) trait CompactMergeConstraintSink {
    fn record_merge_constraint(&mut self, lhs: &CompactBounds, rhs: &CompactBounds);
}

pub(super) struct NoopCompactMergeConstraintSink;

impl CompactMergeConstraintSink for NoopCompactMergeConstraintSink {
    fn record_merge_constraint(&mut self, _lhs: &CompactBounds, _rhs: &CompactBounds) {}
}

impl CompactMergeConstraintSink for Vec<CompactMergeConstraint> {
    fn record_merge_constraint(&mut self, lhs: &CompactBounds, rhs: &CompactBounds) {
        if lhs != rhs {
            self.push(CompactMergeConstraint {
                key: compact_merge_constraint_key(lhs, rhs),
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            });
        }
    }
}

pub(super) fn compact_merge_constraint_key(
    lhs: &CompactBounds,
    rhs: &CompactBounds,
) -> CompactMergeConstraintKey {
    CompactMergeConstraintKey {
        lhs: compact_merge_constraint_shape(lhs),
        rhs: compact_merge_constraint_shape(rhs),
    }
}

pub(super) fn compact_merge_constraint_shape(
    bounds: &CompactBounds,
) -> CompactMergeConstraintShape {
    match bounds {
        CompactBounds::Interval { lower, upper } => CompactMergeConstraintShape::Interval {
            center: compact_interval_center_var(lower, upper),
        },
        CompactBounds::Con { path, args } => CompactMergeConstraintShape::Con {
            path: path.clone(),
            args: args.iter().map(compact_merge_constraint_shape).collect(),
        },
        CompactBounds::Tuple { items } => CompactMergeConstraintShape::Tuple(
            items.iter().map(compact_merge_constraint_shape).collect(),
        ),
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactMergeConstraintShape::Fun {
            arg: Box::new(compact_merge_constraint_shape(arg)),
            arg_eff: Box::new(compact_merge_constraint_shape(arg_eff)),
            ret_eff: Box::new(compact_merge_constraint_shape(ret_eff)),
            ret: Box::new(compact_merge_constraint_shape(ret)),
        },
        CompactBounds::Record { fields } => CompactMergeConstraintShape::Record(
            fields
                .iter()
                .map(|field| CompactMergeConstraintFieldShape {
                    name: field.name.clone(),
                    value: compact_merge_constraint_shape(&field.value),
                    optional: field.optional,
                })
                .collect(),
        ),
        CompactBounds::PolyVariant { items } => CompactMergeConstraintShape::PolyVariant(
            items
                .iter()
                .map(|(name, payloads)| {
                    (
                        name.clone(),
                        payloads
                            .iter()
                            .map(compact_merge_constraint_shape)
                            .collect(),
                    )
                })
                .collect(),
        ),
    }
}

pub(super) fn compact_interval_center_var(
    lower: &CompactType,
    upper: &CompactType,
) -> Option<TypeVar> {
    let lower = single_plain_compact_var(lower)?;
    let upper = single_plain_compact_var(upper)?;
    (lower == upper).then_some(lower)
}

pub(super) fn single_plain_compact_var(ty: &CompactType) -> Option<TypeVar> {
    if ty.vars.len() == 1
        && !ty.never
        && ty.builtins.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        Some(ty.vars[0].var)
    } else {
        None
    }
}

pub(crate) fn merge_compact_types(
    positive: bool,
    lhs: CompactType,
    rhs: CompactType,
) -> CompactType {
    let mut sink = NoopCompactMergeConstraintSink;
    merge_compact_types_with_sink(positive, lhs, rhs, &mut sink)
}

pub(crate) fn merge_compact_bounds_recording_merge_constraints(
    positive: bool,
    lhs: CompactBounds,
    rhs: CompactBounds,
) -> (CompactBounds, Vec<CompactMergeConstraint>) {
    let mut constraints = Vec::new();
    constraints.record_merge_constraint(&lhs, &rhs);
    let bounds = merge_compact_bounds_with_sink(positive, lhs, rhs, &mut constraints);
    (bounds, constraints)
}

pub(super) fn merge_compact_types_with_sink<S: CompactMergeConstraintSink>(
    positive: bool,
    lhs: CompactType,
    rhs: CompactType,
    sink: &mut S,
) -> CompactType {
    if is_empty_compact_type(&lhs) {
        return rhs;
    }
    if is_empty_compact_type(&rhs) {
        return lhs;
    }
    if lhs == rhs {
        return lhs;
    }
    if !positive && (lhs.never || rhs.never) {
        return CompactType::never();
    }

    let CompactType {
        vars,
        never,
        builtins,
        cons,
        funs,
        records,
        record_spreads,
        poly_variants,
        tuples,
        rows,
    } = rhs;
    let mut lhs = lhs;
    if positive {
        lhs.never = lhs.never && never;
    } else {
        lhs.never |= never;
    }
    lhs.vars = merge_compact_vars(lhs.vars, vars);
    lhs.builtins = merge_unique_owned(lhs.builtins, builtins);
    lhs.cons = merge_cons_with_sink(positive, lhs.cons, cons, sink);
    lhs.funs = merge_funs_with_sink(positive, lhs.funs, funs, sink);
    lhs.records = merge_records_with_sink(positive, lhs.records, records, sink);
    lhs.record_spreads = merge_unique_owned(lhs.record_spreads, record_spreads);
    lhs.poly_variants = merge_variants_with_sink(positive, lhs.poly_variants, poly_variants, sink);
    lhs.tuples = merge_tuples_with_sink(positive, lhs.tuples, tuples, sink);
    lhs.rows = merge_rows_with_sink(positive, lhs.rows, rows, sink);
    record_effect_family_coexistence_with_sink(&lhs, sink);
    lhs
}

pub(super) fn is_empty_compact_type(ty: &CompactType) -> bool {
    !ty.never
        && ty.vars.is_empty()
        && ty.builtins.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

pub(super) fn role_arg_bounds_from_types(lower: CompactType, upper: CompactType) -> CompactBounds {
    let mut sink = NoopCompactMergeConstraintSink;
    role_arg_bounds_from_types_with_sink(lower, upper, &mut sink)
}

pub(super) fn role_arg_bounds_from_types_with_sink<S: CompactMergeConstraintSink>(
    lower: CompactType,
    upper: CompactType,
    sink: &mut S,
) -> CompactBounds {
    if let (Some(lower_bounds), Some(upper_bounds)) = (
        exact_compact_type_bounds(&lower),
        exact_compact_type_bounds(&upper),
    ) {
        if lower_bounds == upper_bounds {
            return lower_bounds;
        }
        if compact_bounds_can_merge(&lower_bounds, &upper_bounds) {
            sink.record_merge_constraint(&lower_bounds, &upper_bounds);
            return merge_compact_bounds_with_sink(true, lower_bounds, upper_bounds, sink);
        }
    }

    CompactBounds::Interval { lower, upper }
}

pub(super) fn compact_bounds_can_merge(lhs: &CompactBounds, rhs: &CompactBounds) -> bool {
    match (lhs, rhs) {
        (lhs, rhs) if lhs == rhs => true,
        (CompactBounds::Interval { .. }, CompactBounds::Interval { .. }) => true,
        (
            CompactBounds::Con { path, args },
            CompactBounds::Con {
                path: rhs_path,
                args: rhs_args,
            },
        ) => path == rhs_path && args.len() == rhs_args.len(),
        (CompactBounds::Tuple { items }, CompactBounds::Tuple { items: rhs_items }) => {
            items.len() == rhs_items.len()
        }
        (CompactBounds::Fun { .. }, CompactBounds::Fun { .. }) => true,
        (CompactBounds::Record { fields }, CompactBounds::Record { fields: rhs_fields }) => {
            fields.len() == rhs_fields.len()
        }
        (CompactBounds::PolyVariant { items }, CompactBounds::PolyVariant { items: rhs_items }) => {
            items == rhs_items
        }
        _ => false,
    }
}

pub(super) fn exact_compact_type_bounds(ty: &CompactType) -> Option<CompactBounds> {
    if ty.vars.len() == 1
        && !ty.never
        && ty.builtins.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        let var = ty.vars[0].var;
        return Some(CompactBounds::Interval {
            lower: CompactType::from_var(CompactVar::plain(var)),
            upper: CompactType::from_var(CompactVar::plain(var)),
        });
    }
    if ty.builtins.len() == 1
        && ty.vars.is_empty()
        && !ty.never
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        return Some(CompactBounds::Con {
            path: vec![ty.builtins[0].surface_name().into()],
            args: Vec::new(),
        });
    }
    if ty.cons.len() == 1
        && ty.vars.is_empty()
        && !ty.never
        && ty.builtins.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        let con = compact_con_entries(&ty.cons).into_iter().next()?;
        return Some(CompactBounds::Con {
            path: con.path,
            args: con.args,
        });
    }
    if ty.funs.len() == 1
        && ty.vars.is_empty()
        && !ty.never
        && ty.builtins.is_empty()
        && ty.cons.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        let fun = &ty.funs[0];
        return Some(CompactBounds::Fun {
            arg: Box::new(role_arg_bounds_from_types(fun.arg.clone(), fun.arg.clone())),
            arg_eff: Box::new(role_arg_bounds_from_types(
                fun.arg_eff.clone(),
                fun.arg_eff.clone(),
            )),
            ret_eff: Box::new(role_arg_bounds_from_types(
                fun.ret_eff.clone(),
                fun.ret_eff.clone(),
            )),
            ret: Box::new(role_arg_bounds_from_types(fun.ret.clone(), fun.ret.clone())),
        });
    }
    if ty.records.len() == 1
        && ty.vars.is_empty()
        && !ty.never
        && ty.builtins.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        return Some(CompactBounds::Record {
            fields: ty.records[0]
                .fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: role_arg_bounds_from_types(field.value.clone(), field.value.clone()),
                    optional: field.optional,
                })
                .collect(),
        });
    }
    if ty.poly_variants.len() == 1
        && ty.vars.is_empty()
        && !ty.never
        && ty.builtins.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        return Some(CompactBounds::PolyVariant {
            items: ty.poly_variants[0]
                .items
                .iter()
                .map(|(name, payloads)| {
                    (
                        name.clone(),
                        payloads
                            .iter()
                            .map(|payload| {
                                role_arg_bounds_from_types(payload.clone(), payload.clone())
                            })
                            .collect(),
                    )
                })
                .collect(),
        });
    }
    if ty.tuples.len() == 1
        && ty.vars.is_empty()
        && !ty.never
        && ty.builtins.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.rows.is_empty()
    {
        return Some(CompactBounds::Tuple {
            items: ty.tuples[0]
                .items
                .iter()
                .map(|item| role_arg_bounds_from_types(item.clone(), item.clone()))
                .collect(),
        });
    }
    None
}

pub(super) fn merge_exact_interval_without_center(
    lower: CompactType,
    upper: CompactType,
) -> Option<CompactBounds> {
    let lower_bounds = exact_compact_type_bounds(&lower)?;
    let upper_bounds = exact_compact_type_bounds(&upper)?;
    if lower_bounds == upper_bounds {
        if matches!(lower_bounds, CompactBounds::Interval { .. }) {
            return None;
        }
        return Some(lower_bounds);
    }
    compact_bounds_can_merge(&lower_bounds, &upper_bounds).then(|| {
        let mut sink = NoopCompactMergeConstraintSink;
        merge_compact_bounds_with_sink(true, lower_bounds, upper_bounds, &mut sink)
    })
}

pub(super) fn free_vars_in_root(root: &CompactRoot) -> FxHashSet<TypeVar> {
    let mut vars = FxHashSet::default();
    collect_free_vars_in_type(&root.root, &mut vars);
    for rec in &root.rec_vars {
        vars.insert(rec.var);
        collect_free_vars_in_bounds(&rec.bounds, &mut vars);
    }
    vars
}

pub(super) fn free_vars_in_role_constraint(
    constraint: &CompactRoleConstraint,
) -> FxHashSet<TypeVar> {
    let mut vars = FxHashSet::default();
    for input in &constraint.inputs {
        collect_free_vars_in_role_arg(input, &mut vars);
    }
    for associated in &constraint.associated {
        collect_free_vars_in_role_arg(&associated.value, &mut vars);
    }
    vars
}

pub(super) fn collect_free_vars_in_role_arg(arg: &CompactRoleArg, vars: &mut FxHashSet<TypeVar>) {
    collect_free_vars_in_bounds(&arg.bounds, vars);
}

pub(super) fn collect_free_vars_in_type(ty: &CompactType, vars: &mut FxHashSet<TypeVar>) {
    for var in &ty.vars {
        vars.insert(var.var);
    }
    for args in ty.cons.values() {
        for arg in args {
            collect_free_vars_in_bounds(arg, vars);
        }
    }
    for fun in &ty.funs {
        collect_free_vars_in_type(&fun.arg, vars);
        collect_free_vars_in_type(&fun.arg_eff, vars);
        collect_free_vars_in_type(&fun.ret_eff, vars);
        collect_free_vars_in_type(&fun.ret, vars);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_free_vars_in_type(&field.value, vars);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_free_vars_in_type(&field.value, vars);
        }
        collect_free_vars_in_type(&spread.tail, vars);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_free_vars_in_type(payload, vars);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            collect_free_vars_in_type(item, vars);
        }
    }
    for row in &ty.rows {
        for args in row.items.values() {
            for arg in args {
                collect_free_vars_in_bounds(arg, vars);
            }
        }
        collect_free_vars_in_type(&row.tail, vars);
    }
}

pub(super) fn collect_free_vars_in_bounds(bounds: &CompactBounds, vars: &mut FxHashSet<TypeVar>) {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            collect_free_vars_in_type(lower, vars);
            collect_free_vars_in_type(upper, vars);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                collect_free_vars_in_bounds(arg, vars);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_free_vars_in_bounds(arg, vars);
            collect_free_vars_in_bounds(arg_eff, vars);
            collect_free_vars_in_bounds(ret_eff, vars);
            collect_free_vars_in_bounds(ret, vars);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                collect_free_vars_in_bounds(&field.value, vars);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_free_vars_in_bounds(payload, vars);
                }
            }
        }
    }
}
