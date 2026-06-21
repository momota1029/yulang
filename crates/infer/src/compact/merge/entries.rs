use super::*;

pub(crate) fn compact_con_entries(cons: &CompactConMap) -> Vec<CompactCon> {
    let mut entries = cons
        .iter()
        .map(|(path, args)| CompactCon {
            path: path.clone(),
            args: args.clone(),
        })
        .collect::<Vec<_>>();
    entries.sort_by(|lhs, rhs| lhs.path.cmp(&rhs.path));
    entries
}

pub(crate) fn compact_row_item_entries(items: &CompactRowItemMap) -> Vec<CompactCon> {
    let mut entries = items
        .iter()
        .map(|(path, args)| CompactCon {
            path: path.clone(),
            args: args.clone(),
        })
        .collect::<Vec<_>>();
    entries.sort_by(|lhs, rhs| lhs.path.cmp(&rhs.path));
    entries
}

pub(in crate::compact) fn singleton_row_item_map(
    path: Vec<String>,
    args: Vec<CompactBounds>,
) -> CompactRowItemMap {
    let mut items = CompactRowItemMap::default();
    items.insert(path, args);
    items
}

pub(in crate::compact) fn merge_pos_row_item(items: &mut CompactRowItemMap, con: CompactCon) {
    *items = merge_row_items(
        true,
        mem::take(items),
        singleton_row_item_map(con.path, con.args),
    );
}

pub(in crate::compact) fn record_effect_family_coexistence_with_sink<
    S: CompactMergeConstraintSink,
>(
    ty: &CompactType,
    sink: &mut S,
) {
    let mut families = Vec::new();
    collect_effect_families(ty, &mut families);
    for (index, (path, args)) in families.iter().enumerate() {
        for (other_path, other_args) in families.iter().skip(index + 1) {
            if path == other_path && args.len() == other_args.len() {
                record_merge_bound_args_with_sink(sink, args, other_args);
            }
        }
    }
}

pub(in crate::compact) fn collect_effect_families<'a>(
    ty: &'a CompactType,
    out: &mut Vec<(&'a Vec<String>, &'a Vec<CompactBounds>)>,
) {
    for (path, args) in &ty.cons {
        out.push((path, args));
    }
    for row in &ty.rows {
        for (path, args) in &row.items {
            out.push((path, args));
        }
        collect_effect_families(&row.tail, out);
    }
}

pub(in crate::compact) fn record_merge_bound_args_with_sink<S: CompactMergeConstraintSink>(
    sink: &mut S,
    lhs: &[CompactBounds],
    rhs: &[CompactBounds],
) {
    for (lhs, rhs) in lhs.iter().zip(rhs) {
        sink.record_merge_constraint(lhs, rhs);
    }
}

#[derive(Debug, Clone)]
pub(in crate::compact) struct CompactStackFamily {
    pub(in crate::compact) path: Vec<String>,
    pub(in crate::compact) args: Vec<CompactBounds>,
}

pub(in crate::compact) fn compact_weight_effect_families(
    weight: &ConstraintWeight,
) -> Vec<(Vec<String>, Vec<NeuId>)> {
    weight
        .active_stack_items()
        .flat_map(compact_subtractability_families)
        .collect()
}

pub(in crate::compact) fn compact_subtractability_families(
    subtractability: &Subtractability,
) -> Vec<(Vec<String>, Vec<NeuId>)> {
    match subtractability {
        Subtractability::Empty | Subtractability::All => Vec::new(),
        Subtractability::Set(path, args) | Subtractability::AllExcept(path, args) => {
            vec![(path.clone(), args.clone())]
        }
        Subtractability::SetMany(families) | Subtractability::AllExceptMany(families) => {
            families.clone()
        }
    }
}

pub(in crate::compact) fn merge_unique_owned<T: PartialEq>(mut lhs: Vec<T>, rhs: Vec<T>) -> Vec<T> {
    for item in rhs {
        if !lhs.contains(&item) {
            lhs.push(item);
        }
    }
    lhs
}

pub(in crate::compact) fn merge_compact_vars(
    mut lhs: Vec<CompactVar>,
    rhs: Vec<CompactVar>,
) -> Vec<CompactVar> {
    for var in rhs {
        if let Some(existing) = lhs.iter_mut().find(|existing| existing.var == var.var) {
            // 同一変数の合流は並列文脈の合流であり、逐次合成ではない。
            // 同じ weight を compose すると push が二重に積まれるため、冪等に保つ。
            if existing.weight != var.weight {
                existing.weight = existing.weight.parallel_union(&var.weight);
            }
            existing.origin = existing.origin.merged(var.origin);
        } else {
            lhs.push(var);
        }
    }
    lhs
}

pub(crate) fn merge_cons(positive: bool, lhs: CompactConMap, rhs: CompactConMap) -> CompactConMap {
    let mut sink = NoopCompactMergeConstraintSink;
    merge_cons_with_sink(positive, lhs, rhs, &mut sink)
}

pub(in crate::compact) fn merge_cons_with_sink<S: CompactMergeConstraintSink>(
    positive: bool,
    mut lhs: CompactConMap,
    rhs: CompactConMap,
    sink: &mut S,
) -> CompactConMap {
    for (path, args) in rhs {
        if let Some(existing) = lhs.get_mut(&path) {
            *existing =
                merge_compact_bound_args_with_sink(positive, mem::take(existing), args, sink);
        } else {
            lhs.insert(path, args);
        }
    }
    lhs
}

pub(in crate::compact) fn merge_compact_bound_args_with_sink<S: CompactMergeConstraintSink>(
    positive: bool,
    lhs: Vec<CompactBounds>,
    rhs: Vec<CompactBounds>,
    sink: &mut S,
) -> Vec<CompactBounds> {
    if lhs.len() != rhs.len() {
        return lhs;
    }
    lhs.into_iter()
        .zip(rhs)
        .map(|(lhs, rhs)| {
            sink.record_merge_constraint(&lhs, &rhs);
            merge_compact_bounds_with_sink(positive, lhs, rhs, sink)
        })
        .collect()
}

pub(in crate::compact) fn merge_compact_bounds_with_sink<S: CompactMergeConstraintSink>(
    positive: bool,
    lhs: CompactBounds,
    rhs: CompactBounds,
    sink: &mut S,
) -> CompactBounds {
    match (lhs, rhs) {
        (
            CompactBounds::Interval { lower, upper },
            CompactBounds::Interval {
                lower: rhs_lower,
                upper: rhs_upper,
            },
        ) => {
            let lower = merge_compact_types_with_sink(positive, lower, rhs_lower, sink);
            let upper = merge_compact_types_with_sink(!positive, upper, rhs_upper, sink);
            CompactBounds::Interval { lower, upper }
        }
        (
            CompactBounds::Con { path, args },
            CompactBounds::Con {
                path: rhs_path,
                args: rhs_args,
            },
        ) if path == rhs_path && args.len() == rhs_args.len() => CompactBounds::Con {
            path,
            args: merge_compact_bound_args_with_sink(positive, args, rhs_args, sink),
        },
        (CompactBounds::Tuple { items }, CompactBounds::Tuple { items: rhs_items })
            if items.len() == rhs_items.len() =>
        {
            CompactBounds::Tuple {
                items: merge_compact_bound_args_with_sink(positive, items, rhs_items, sink),
            }
        }
        (
            CompactBounds::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
            CompactBounds::Fun {
                arg: rhs_arg,
                arg_eff: rhs_arg_eff,
                ret_eff: rhs_ret_eff,
                ret: rhs_ret,
            },
        ) => {
            sink.record_merge_constraint(&arg, &rhs_arg);
            sink.record_merge_constraint(&arg_eff, &rhs_arg_eff);
            sink.record_merge_constraint(&ret_eff, &rhs_ret_eff);
            sink.record_merge_constraint(&ret, &rhs_ret);
            CompactBounds::Fun {
                arg: Box::new(merge_compact_bounds_with_sink(
                    !positive, *arg, *rhs_arg, sink,
                )),
                arg_eff: Box::new(merge_compact_bounds_with_sink(
                    !positive,
                    *arg_eff,
                    *rhs_arg_eff,
                    sink,
                )),
                ret_eff: Box::new(merge_compact_bounds_with_sink(
                    positive,
                    *ret_eff,
                    *rhs_ret_eff,
                    sink,
                )),
                ret: Box::new(merge_compact_bounds_with_sink(
                    positive, *ret, *rhs_ret, sink,
                )),
            }
        }
        (CompactBounds::Record { fields }, CompactBounds::Record { fields: rhs_fields }) => {
            CompactBounds::Record {
                fields: fields
                    .into_iter()
                    .zip(rhs_fields)
                    .map(|(field, rhs_field)| RecordField {
                        name: field.name,
                        value: {
                            sink.record_merge_constraint(&field.value, &rhs_field.value);
                            merge_compact_bounds_with_sink(
                                positive,
                                field.value,
                                rhs_field.value,
                                sink,
                            )
                        },
                        optional: field.optional && rhs_field.optional,
                    })
                    .collect(),
            }
        }
        (CompactBounds::PolyVariant { items }, CompactBounds::PolyVariant { items: rhs_items })
            if items == rhs_items =>
        {
            CompactBounds::PolyVariant { items }
        }
        (lhs, rhs) if lhs == rhs => lhs,
        (lhs, _) => lhs,
    }
}

pub(in crate::compact) fn merge_funs_with_sink<S: CompactMergeConstraintSink>(
    positive: bool,
    lhs: Vec<CompactFun>,
    rhs: Vec<CompactFun>,
    sink: &mut S,
) -> Vec<CompactFun> {
    let mut iter = lhs.into_iter().chain(rhs);
    let Some(mut acc) = iter.next() else {
        return Vec::new();
    };
    for other in iter {
        acc = CompactFun {
            arg: merge_compact_types_with_sink(!positive, acc.arg, other.arg, sink),
            arg_eff: merge_compact_types_with_sink(!positive, acc.arg_eff, other.arg_eff, sink),
            ret_eff: merge_compact_types_with_sink(positive, acc.ret_eff, other.ret_eff, sink),
            ret: merge_compact_types_with_sink(positive, acc.ret, other.ret, sink),
        };
    }
    vec![acc]
}

pub(in crate::compact) fn merge_records_with_sink<S: CompactMergeConstraintSink>(
    positive: bool,
    lhs: Vec<CompactRecord>,
    rhs: Vec<CompactRecord>,
    sink: &mut S,
) -> Vec<CompactRecord> {
    let mut iter = lhs.into_iter().chain(rhs);
    let Some(mut acc) = iter.next() else {
        return Vec::new();
    };
    for other in iter {
        let mut rhs_fields = other
            .fields
            .into_iter()
            .map(|field| (field.name.clone(), field))
            .collect::<FxHashMap<_, _>>();
        let mut fields = Vec::new();
        for lhs_field in acc.fields {
            match rhs_fields.remove(&lhs_field.name) {
                Some(rhs_field) => fields.push(RecordField {
                    name: lhs_field.name,
                    value: merge_compact_types_with_sink(
                        positive,
                        lhs_field.value,
                        rhs_field.value,
                        sink,
                    ),
                    optional: lhs_field.optional && rhs_field.optional,
                }),
                None if !positive => fields.push(lhs_field),
                None => {}
            }
        }
        if !positive {
            for rhs_field in rhs_fields.into_values() {
                if !fields.iter().any(|field| field.name == rhs_field.name) {
                    fields.push(rhs_field);
                }
            }
        }
        acc = CompactRecord { fields };
    }
    vec![acc]
}

pub(in crate::compact) fn merge_variants_with_sink<S: CompactMergeConstraintSink>(
    positive: bool,
    lhs: Vec<CompactPolyVariant>,
    rhs: Vec<CompactPolyVariant>,
    sink: &mut S,
) -> Vec<CompactPolyVariant> {
    let mut items = Vec::<(String, Vec<CompactType>)>::new();
    for variant in lhs.into_iter().chain(rhs) {
        for (name, payloads) in variant.items {
            if let Some((_, existing_payloads)) =
                items.iter_mut().find(|(existing_name, existing_payloads)| {
                    *existing_name == name && existing_payloads.len() == payloads.len()
                })
            {
                *existing_payloads = mem::take(existing_payloads)
                    .into_iter()
                    .zip(payloads)
                    .map(|(lhs, rhs)| merge_compact_types_with_sink(positive, lhs, rhs, sink))
                    .collect();
            } else {
                items.push((name, payloads));
            }
        }
    }
    if items.is_empty() {
        Vec::new()
    } else {
        vec![CompactPolyVariant { items }]
    }
}

pub(in crate::compact) fn merge_tuples_with_sink<S: CompactMergeConstraintSink>(
    positive: bool,
    lhs: Vec<CompactTuple>,
    rhs: Vec<CompactTuple>,
    sink: &mut S,
) -> Vec<CompactTuple> {
    let mut out = lhs;
    for other in rhs {
        if let Some(existing) = out
            .iter_mut()
            .find(|tuple| tuple.items.len() == other.items.len())
        {
            existing.items = mem::take(&mut existing.items)
                .into_iter()
                .zip(other.items)
                .map(|(lhs, rhs)| merge_compact_types_with_sink(positive, lhs, rhs, sink))
                .collect();
        } else if !out.contains(&other) {
            out.push(other);
        }
    }
    out
}

pub(in crate::compact) fn merge_rows_with_sink<S: CompactMergeConstraintSink>(
    positive: bool,
    lhs: Vec<CompactRow>,
    rhs: Vec<CompactRow>,
    sink: &mut S,
) -> Vec<CompactRow> {
    if !positive {
        return merge_negative_rows_with_sink(lhs, rhs, sink);
    }

    let mut iter = lhs.into_iter().chain(rhs);
    let Some(mut acc) = iter.next() else {
        return Vec::new();
    };
    for other in iter {
        acc.items = merge_row_items_with_sink(positive, acc.items, other.items, sink);
        acc.tail = Box::new(merge_compact_types_with_sink(
            positive,
            *acc.tail,
            *other.tail,
            sink,
        ));
    }
    vec![acc]
}

pub(in crate::compact) fn merge_negative_rows_with_sink<S: CompactMergeConstraintSink>(
    lhs: Vec<CompactRow>,
    rhs: Vec<CompactRow>,
    sink: &mut S,
) -> Vec<CompactRow> {
    if lhs.is_empty() {
        return rhs;
    }
    if rhs.is_empty() {
        return lhs;
    }

    let mut out = Vec::new();
    for left in lhs {
        for right in &rhs {
            let row = CompactRow {
                items: merge_row_items_with_sink(
                    false,
                    left.items.clone(),
                    right.items.clone(),
                    sink,
                ),
                tail: Box::new(merge_compact_types_with_sink(
                    false,
                    (*left.tail).clone(),
                    (*right.tail).clone(),
                    sink,
                )),
            };
            if !out.contains(&row) {
                out.push(row);
            }
        }
    }
    out
}

pub(in crate::compact) fn merge_row_items(
    positive: bool,
    lhs: CompactRowItemMap,
    rhs: CompactRowItemMap,
) -> CompactRowItemMap {
    let mut sink = NoopCompactMergeConstraintSink;
    merge_row_items_with_sink(positive, lhs, rhs, &mut sink)
}

pub(in crate::compact) fn merge_row_items_with_sink<S: CompactMergeConstraintSink>(
    positive: bool,
    mut lhs: CompactRowItemMap,
    rhs: CompactRowItemMap,
    sink: &mut S,
) -> CompactRowItemMap {
    if !positive {
        let mut out = CompactRowItemMap::default();
        for (path, args) in lhs {
            if let Some(rhs_args) = rhs.get(&path)
                && args.len() == rhs_args.len()
            {
                out.insert(
                    path,
                    args.into_iter()
                        .zip(rhs_args.clone())
                        .map(|(lhs, rhs)| {
                            sink.record_merge_constraint(&lhs, &rhs);
                            merge_compact_bounds_with_sink(false, lhs, rhs, sink)
                        })
                        .collect(),
                );
            }
        }
        return out;
    }

    for (path, args) in rhs {
        if let Some(existing) = lhs.get_mut(&path) {
            *existing =
                merge_compact_bound_args_with_sink(positive, mem::take(existing), args, sink);
        } else {
            lhs.insert(path, args);
        }
    }
    lhs
}
