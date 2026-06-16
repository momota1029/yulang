use super::*;

pub(super) fn rewrite_role_constraint(
    constraint: &CompactRoleConstraint,
    subst: &TypeSubst,
) -> CompactRoleConstraint {
    CompactRoleConstraint {
        role: constraint.role.clone(),
        inputs: constraint
            .inputs
            .iter()
            .map(|arg| rewrite_role_arg(arg, subst))
            .collect(),
        associated: constraint
            .associated
            .iter()
            .map(|associated| CompactRoleAssociatedType {
                name: associated.name.clone(),
                value: rewrite_role_arg(&associated.value, subst),
            })
            .collect(),
    }
}

pub(super) fn rewrite_role_arg(arg: &CompactRoleArg, subst: &TypeSubst) -> CompactRoleArg {
    CompactRoleArg {
        polarity: arg.polarity,
        bounds: rewrite_bounds(&arg.bounds, subst),
    }
}

pub(super) fn rewrite_type(ty: &CompactType, subst: &TypeSubst, positive: bool) -> CompactType {
    let mut out = CompactType {
        never: ty.never,
        builtins: ty.builtins.clone(),
        cons: compact_con_entries(&ty.cons)
            .into_iter()
            .map(|con| rewrite_con(&con, subst))
            .fold(CompactConMap::default(), |acc, con| {
                merge_cons(positive, acc, compact_con_map(con))
            }),
        funs: ty
            .funs
            .iter()
            .map(|fun| CompactFun {
                arg: rewrite_type(&fun.arg, subst, !positive),
                arg_eff: rewrite_type(&fun.arg_eff, subst, !positive),
                ret_eff: rewrite_type(&fun.ret_eff, subst, positive),
                ret: rewrite_type(&fun.ret, subst, positive),
            })
            .collect(),
        records: ty
            .records
            .iter()
            .map(|record| CompactRecord {
                fields: record
                    .fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: rewrite_type(&field.value, subst, positive),
                        optional: field.optional,
                    })
                    .collect(),
            })
            .collect(),
        record_spreads: ty
            .record_spreads
            .iter()
            .map(|spread| CompactRecordSpread {
                fields: spread
                    .fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: rewrite_type(&field.value, subst, positive),
                        optional: field.optional,
                    })
                    .collect(),
                tail: Box::new(rewrite_type(&spread.tail, subst, positive)),
                tail_wins: spread.tail_wins,
            })
            .collect(),
        poly_variants: ty
            .poly_variants
            .iter()
            .map(|variant| CompactPolyVariant {
                items: variant
                    .items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| rewrite_type(payload, subst, positive))
                                .collect(),
                        )
                    })
                    .collect(),
            })
            .collect(),
        tuples: ty
            .tuples
            .iter()
            .map(|tuple| CompactTuple {
                items: tuple
                    .items
                    .iter()
                    .map(|item| rewrite_type(item, subst, positive))
                    .collect(),
            })
            .collect(),
        rows: ty
            .rows
            .iter()
            .map(|row| CompactRow {
                items: row
                    .items
                    .iter()
                    .map(|(path, args)| {
                        (
                            path.clone(),
                            args.iter().map(|arg| rewrite_bounds(arg, subst)).collect(),
                        )
                    })
                    .collect(),
                tail: Box::new(rewrite_type(&row.tail, subst, positive)),
            })
            .collect(),
        ..CompactType::default()
    };

    for var in &ty.vars {
        if let Some(replacement) = subst.get(var.var) {
            out = merge_compact_types(positive, out, replacement.clone());
        } else {
            out.vars.push(var.clone());
        }
    }
    canonical_substitution_type(out)
}

pub(super) fn rewrite_con(con: &CompactCon, subst: &TypeSubst) -> CompactCon {
    CompactCon {
        path: con.path.clone(),
        args: con
            .args
            .iter()
            .map(|arg| rewrite_bounds(arg, subst))
            .collect(),
    }
}

pub(super) fn rewrite_bounds(bounds: &CompactBounds, subst: &TypeSubst) -> CompactBounds {
    match bounds {
        CompactBounds::Interval { lower, upper } => CompactBounds::Interval {
            lower: rewrite_type(lower, subst, true),
            upper: rewrite_type(upper, subst, false),
        },
        CompactBounds::Con { path, args } => CompactBounds::Con {
            path: path.clone(),
            args: args.iter().map(|arg| rewrite_bounds(arg, subst)).collect(),
        },
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactBounds::Fun {
            arg: Box::new(rewrite_bounds(arg, subst)),
            arg_eff: Box::new(rewrite_bounds(arg_eff, subst)),
            ret_eff: Box::new(rewrite_bounds(ret_eff, subst)),
            ret: Box::new(rewrite_bounds(ret, subst)),
        },
        CompactBounds::Record { fields } => CompactBounds::Record {
            fields: fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: rewrite_bounds(&field.value, subst),
                    optional: field.optional,
                })
                .collect(),
        },
        CompactBounds::PolyVariant { items } => CompactBounds::PolyVariant {
            items: items
                .iter()
                .map(|(name, payloads)| {
                    (
                        name.clone(),
                        payloads
                            .iter()
                            .map(|payload| rewrite_bounds(payload, subst))
                            .collect(),
                    )
                })
                .collect(),
        },
        CompactBounds::Tuple { items } => CompactBounds::Tuple {
            items: items
                .iter()
                .map(|item| rewrite_bounds(item, subst))
                .collect(),
        },
    }
}

pub(super) fn compact_bounds_from_type(ty: &CompactType) -> Option<CompactBounds> {
    let ty = canonical_substitution_type(ty.clone());
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
            lower: CompactType::from_var(crate::compact::CompactVar::plain(var)),
            upper: CompactType::from_var(crate::compact::CompactVar::plain(var)),
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
            arg: Box::new(compact_bounds_from_type(&fun.arg)?),
            arg_eff: Box::new(compact_bounds_from_type(&fun.arg_eff)?),
            ret_eff: Box::new(compact_bounds_from_type(&fun.ret_eff)?),
            ret: Box::new(compact_bounds_from_type(&fun.ret)?),
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
        return ty.records[0]
            .fields
            .iter()
            .map(|field| {
                compact_bounds_from_type(&field.value).map(|value| RecordField {
                    name: field.name.clone(),
                    value,
                    optional: field.optional,
                })
            })
            .collect::<Option<Vec<_>>>()
            .map(|fields| CompactBounds::Record { fields });
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
        return ty.poly_variants[0]
            .items
            .iter()
            .map(|(name, payloads)| {
                payloads
                    .iter()
                    .map(compact_bounds_from_type)
                    .collect::<Option<Vec<_>>>()
                    .map(|payloads| (name.clone(), payloads))
            })
            .collect::<Option<Vec<_>>>()
            .map(|items| CompactBounds::PolyVariant { items });
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
        return ty.tuples[0]
            .items
            .iter()
            .map(compact_bounds_from_type)
            .collect::<Option<Vec<_>>>()
            .map(|items| CompactBounds::Tuple { items });
    }
    None
}

pub(super) fn canonical_substitution_type(ty: CompactType) -> CompactType {
    let mut out = CompactType {
        vars: ty.vars,
        never: ty.never,
        builtins: ty.builtins,
        cons: CompactConMap::default(),
        funs: ty.funs,
        records: ty.records,
        record_spreads: ty.record_spreads,
        poly_variants: ty.poly_variants,
        tuples: ty.tuples,
        rows: ty.rows,
    };
    for con in compact_con_entries(&ty.cons) {
        if con.args.is_empty()
            && let Some(builtin) = builtin_for_path(&con.path)
        {
            if !out.builtins.contains(&builtin) {
                out.builtins.push(builtin);
            }
        } else {
            out.cons.insert(con.path, con.args);
        }
    }
    out
}

pub(super) fn compact_con_map(con: CompactCon) -> CompactConMap {
    let mut cons = CompactConMap::default();
    cons.insert(con.path, con.args);
    cons
}

pub(super) fn builtin_for_path(path: &[String]) -> Option<BuiltinType> {
    (path.len() == 1)
        .then(|| BuiltinType::from_surface_name(&path[0]))
        .flatten()
}

pub(super) fn compact_type_is_empty(ty: &CompactType) -> bool {
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
