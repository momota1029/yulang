use super::collect::CompactCollector;
use super::finalize::CompactFinalizer;
use super::*;
use crate::time::{Duration, Instant};

const VAR_ONLY_INTERVAL_DIRECT_MERGE_THRESHOLD: usize = 32;

pub(crate) fn compact_type_var(machine: &ConstraintMachine, root: TypeVar) -> CompactRoot {
    CompactCollector::new(machine).compact_root(root)
}

pub(crate) fn compact_type_var_for_scheme(
    machine: &ConstraintMachine,
    root: TypeVar,
) -> CompactRoot {
    CompactCollector::new(machine).compact_root(root)
}

pub(crate) fn compact_pos_surface(types: &TypeArena, id: PosId) -> CompactType {
    match types.pos(id) {
        Pos::Bot => CompactType::never(),
        Pos::Var(var) => CompactType::from_var(CompactVar::plain(*var)),
        Pos::Con(path, args) => CompactType::from_con(CompactCon {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| compact_neu_surface(types, *arg))
                .collect(),
        }),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactType::from_fun(CompactFun {
            arg: compact_neg_surface(types, *arg),
            arg_eff: compact_neg_surface(types, *arg_eff),
            ret_eff: compact_pos_surface(types, *ret_eff),
            ret: compact_pos_surface(types, *ret),
        }),
        Pos::Record(fields) => CompactType::from_record(CompactRecord {
            fields: fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: compact_pos_surface(types, field.value),
                    optional: field.optional,
                })
                .collect(),
        }),
        Pos::RecordTailSpread { fields, tail } => {
            CompactType::from_record_spread(CompactRecordSpread {
                fields: fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: compact_pos_surface(types, field.value),
                        optional: field.optional,
                    })
                    .collect(),
                tail: Box::new(compact_pos_surface(types, *tail)),
                tail_wins: false,
            })
        }
        Pos::RecordHeadSpread { tail, fields } => {
            CompactType::from_record_spread(CompactRecordSpread {
                fields: fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: compact_pos_surface(types, field.value),
                        optional: field.optional,
                    })
                    .collect(),
                tail: Box::new(compact_pos_surface(types, *tail)),
                tail_wins: true,
            })
        }
        Pos::PolyVariant(items) => CompactType::from_poly_variant(CompactPolyVariant {
            items: items
                .iter()
                .map(|(name, payloads)| {
                    (
                        name.clone(),
                        payloads
                            .iter()
                            .map(|payload| compact_pos_surface(types, *payload))
                            .collect(),
                    )
                })
                .collect(),
        }),
        Pos::Tuple(items) => CompactType::from_tuple(CompactTuple {
            items: items
                .iter()
                .map(|item| compact_pos_surface(types, *item))
                .collect(),
        }),
        Pos::Row(items) => {
            let mut row_items = CompactRowItemMap::default();
            for item in items {
                if let Pos::Con(path, args) = types.pos(*item) {
                    row_items
                        .entry(path.clone())
                        .or_default()
                        .push(CompactBounds::Con {
                            path: path.clone(),
                            args: args
                                .iter()
                                .map(|arg| compact_neu_surface(types, *arg))
                                .collect(),
                        });
                }
            }
            CompactType::from_row(CompactRow {
                items: row_items,
                tail: Box::new(CompactType::default()),
            })
        }
        Pos::Stack { inner, .. } | Pos::NonSubtract(inner, _) => compact_pos_surface(types, *inner),
        Pos::Union(left, right) => merge_compact_types(
            true,
            compact_pos_surface(types, *left),
            compact_pos_surface(types, *right),
        ),
    }
}

pub(crate) fn compact_type_var_recording_merge_constraints(
    machine: &ConstraintMachine,
    root: TypeVar,
) -> (CompactRoot, Vec<CompactMergeConstraint>) {
    CompactCollector::new_recording(machine).compact_root_with_merge_constraints(root)
}

pub(crate) fn compact_type_var_recording_merge_constraints_for_scheme(
    machine: &ConstraintMachine,
    root: TypeVar,
) -> (CompactRoot, Vec<CompactMergeConstraint>) {
    CompactCollector::new_recording(machine).compact_root_with_merge_constraints(root)
}

fn compact_neg_surface(types: &TypeArena, id: NegId) -> CompactType {
    match types.neg(id) {
        Neg::Top => CompactType::default(),
        Neg::Bot => CompactType::never(),
        Neg::Var(var) => CompactType::from_var(CompactVar::plain(*var)),
        Neg::Con(path, args) => CompactType::from_con(CompactCon {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| compact_neu_surface(types, *arg))
                .collect(),
        }),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactType::from_fun(CompactFun {
            arg: compact_pos_surface(types, *arg),
            arg_eff: compact_pos_surface(types, *arg_eff),
            ret_eff: compact_neg_surface(types, *ret_eff),
            ret: compact_neg_surface(types, *ret),
        }),
        Neg::Record(fields) => CompactType::from_record(CompactRecord {
            fields: fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: compact_neg_surface(types, field.value),
                    optional: field.optional,
                })
                .collect(),
        }),
        Neg::PolyVariant(items) => CompactType::from_poly_variant(CompactPolyVariant {
            items: items
                .iter()
                .map(|(name, payloads)| {
                    (
                        name.clone(),
                        payloads
                            .iter()
                            .map(|payload| compact_neg_surface(types, *payload))
                            .collect(),
                    )
                })
                .collect(),
        }),
        Neg::Tuple(items) => CompactType::from_tuple(CompactTuple {
            items: items
                .iter()
                .map(|item| compact_neg_surface(types, *item))
                .collect(),
        }),
        Neg::Row(items, tail) => {
            let mut row_items = CompactRowItemMap::default();
            for item in items {
                if let Neg::Con(path, args) = types.neg(*item) {
                    row_items
                        .entry(path.clone())
                        .or_default()
                        .push(CompactBounds::Con {
                            path: path.clone(),
                            args: args
                                .iter()
                                .map(|arg| compact_neu_surface(types, *arg))
                                .collect(),
                        });
                }
            }
            CompactType::from_row(CompactRow {
                items: row_items,
                tail: Box::new(compact_neg_surface(types, *tail)),
            })
        }
        Neg::Stack { inner, .. } => compact_neg_surface(types, *inner),
        Neg::Intersection(left, right) => merge_compact_types(
            false,
            compact_neg_surface(types, *left),
            compact_neg_surface(types, *right),
        ),
    }
}

fn compact_neu_surface(types: &TypeArena, id: NeuId) -> CompactBounds {
    match types.neu(id) {
        Neu::Bounds(lower, upper) => CompactBounds::Interval {
            lower: compact_pos_surface(types, *lower),
            upper: compact_neg_surface(types, *upper),
        },
        Neu::Con(path, args) => CompactBounds::Con {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| compact_neu_surface(types, *arg))
                .collect(),
        },
        Neu::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactBounds::Fun {
            arg: Box::new(compact_neu_surface(types, *arg)),
            arg_eff: Box::new(compact_neu_surface(types, *arg_eff)),
            ret_eff: Box::new(compact_neu_surface(types, *ret_eff)),
            ret: Box::new(compact_neu_surface(types, *ret)),
        },
        Neu::Record(fields) => CompactBounds::Record {
            fields: fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: compact_neu_surface(types, field.value),
                    optional: field.optional,
                })
                .collect(),
        },
        Neu::PolyVariant(items) => CompactBounds::PolyVariant {
            items: items
                .iter()
                .map(|(name, payloads)| {
                    (
                        name.clone(),
                        payloads
                            .iter()
                            .map(|payload| compact_neu_surface(types, *payload))
                            .collect(),
                    )
                })
                .collect(),
        },
        Neu::Tuple(items) => CompactBounds::Tuple {
            items: items
                .iter()
                .map(|item| compact_neu_surface(types, *item))
                .collect(),
        },
    }
}

pub(crate) fn apply_compact_merge_constraints(
    machine: &mut ConstraintMachine,
    constraints: Vec<CompactMergeConstraint>,
    applied: &mut FxHashSet<CompactMergeConstraintKey>,
) -> bool {
    let mut changed = false;
    for constraint in constraints {
        let CompactMergeConstraint { key, lhs, rhs } = constraint;
        if lhs == rhs || !applied.insert(key) {
            continue;
        }
        let phase = Instant::now();
        if let Some(pairs) = var_only_interval_merge_pairs(&lhs, &rhs) {
            if pairs.len() > VAR_ONLY_INTERVAL_DIRECT_MERGE_THRESHOLD {
                changed |= machine.constrain_var_var_pairs_direct(pairs);
                trace_slow_compact_merge_constraint(&lhs, &rhs, phase.elapsed());
                continue;
            }
        }
        let (lhs_neu, rhs_neu) = {
            let mut finalizer = CompactFinalizer::new(&mut *machine);
            (
                finalizer.finalize_bounds(&lhs),
                finalizer.finalize_bounds(&rhs),
            )
        };
        changed |= machine.constrain_invariant_neu(lhs_neu, rhs_neu);
        trace_slow_compact_merge_constraint(&lhs, &rhs, phase.elapsed());
    }
    changed
}

fn trace_slow_compact_merge_constraint(
    lhs: &CompactBounds,
    rhs: &CompactBounds,
    elapsed: Duration,
) {
    if elapsed < Duration::from_millis(50) || !compact_merge_trace_enabled() {
        return;
    }
    eprintln!(
        "[compact] apply merge constraint: elapsed={:.3}ms lhs={} rhs={}",
        elapsed.as_secs_f64() * 1000.0,
        compact_bounds_trace_summary(lhs),
        compact_bounds_trace_summary(rhs)
    );
}

fn compact_merge_trace_enabled() -> bool {
    std::env::var("YULANG_ANALYSIS_TIMING").is_ok_and(|value| !value.is_empty() && value != "0")
}

fn var_only_interval_merge_pairs(
    lhs: &CompactBounds,
    rhs: &CompactBounds,
) -> Option<Vec<(TypeVar, TypeVar)>> {
    let (
        CompactBounds::Interval {
            lower: lhs_lower,
            upper: lhs_upper,
        },
        CompactBounds::Interval {
            lower: rhs_lower,
            upper: rhs_upper,
        },
    ) = (lhs, rhs)
    else {
        return None;
    };
    let lhs_lower = var_only_compact_type_vars(lhs_lower)?;
    let lhs_upper = var_only_compact_type_vars(lhs_upper)?;
    let rhs_lower = var_only_compact_type_vars(rhs_lower)?;
    let rhs_upper = var_only_compact_type_vars(rhs_upper)?;
    let mut pairs = Vec::new();
    push_var_var_pairs(&mut pairs, &lhs_lower, &rhs_upper);
    push_var_var_pairs(&mut pairs, &rhs_lower, &lhs_upper);
    Some(pairs)
}

fn var_only_compact_type_vars(ty: &CompactType) -> Option<Vec<TypeVar>> {
    if ty.never
        || !ty.builtins.is_empty()
        || !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.poly_variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
    {
        return None;
    }
    Some(ty.vars.iter().map(|var| var.var).collect())
}

fn push_var_var_pairs(pairs: &mut Vec<(TypeVar, TypeVar)>, lowers: &[TypeVar], uppers: &[TypeVar]) {
    for lower in lowers {
        for upper in uppers {
            let pair = (*lower, *upper);
            if lower != upper && !pairs.contains(&pair) {
                pairs.push(pair);
            }
        }
    }
}

fn compact_bounds_trace_summary(bounds: &CompactBounds) -> String {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            format!(
                "interval(lower={}, upper={})",
                compact_type_trace_summary(lower),
                compact_type_trace_summary(upper)
            )
        }
        CompactBounds::Con { path, args } => format!("con({path:?}, args={})", args.len()),
        CompactBounds::Tuple { items } => format!("tuple(items={})", items.len()),
        CompactBounds::Fun { .. } => "fun".to_string(),
        CompactBounds::Record { fields } => format!("record(fields={})", fields.len()),
        CompactBounds::PolyVariant { items } => format!("variant(items={})", items.len()),
    }
}

fn compact_type_trace_summary(ty: &CompactType) -> String {
    format!(
        "vars={} never={} builtins={} cons={} funs={} records={} spreads={} variants={} tuples={} rows={}",
        ty.vars.len(),
        ty.never,
        ty.builtins.len(),
        ty.cons.len(),
        ty.funs.len(),
        ty.records.len(),
        ty.record_spreads.len(),
        ty.poly_variants.len(),
        ty.tuples.len(),
        ty.rows.len()
    )
}

pub(crate) fn apply_compact_subtype_constraints(
    machine: &mut ConstraintMachine,
    constraints: Vec<CompactSubtypeConstraint>,
    applied: &mut FxHashSet<CompactSubtypeConstraintKey>,
) -> bool {
    let mut changed = false;
    for constraint in constraints {
        let CompactSubtypeConstraint { key, lower, upper } = constraint;
        if lower == upper || !applied.insert(key) {
            continue;
        }
        let (lower, upper) = {
            let mut finalizer = CompactFinalizer::new(&mut *machine);
            (
                finalizer.finalize_pos_type(&lower),
                finalizer.finalize_neg_type(&upper),
            )
        };
        changed |= machine.constrain_subtype(lower, upper);
    }
    changed
}

#[cfg(test)]
pub(crate) fn compact_reachable_role_constraints(
    machine: &ConstraintMachine,
    seed: &CompactRoot,
    constraints: &[RoleConstraint],
) -> Vec<CompactRoleConstraint> {
    if constraints.is_empty() {
        return Vec::new();
    }
    CompactCollector::new(machine).compact_reachable_role_constraints(seed, constraints)
}

pub(crate) fn compact_reachable_role_constraints_recording_merge_constraints(
    machine: &ConstraintMachine,
    seed: &CompactRoot,
    constraints: &[RoleConstraint],
) -> (Vec<CompactRoleConstraint>, Vec<CompactMergeConstraint>) {
    if constraints.is_empty() {
        return (Vec::new(), Vec::new());
    }
    CompactCollector::new_recording(machine)
        .compact_reachable_role_constraints_with_merge_constraints(seed, constraints)
}

pub(crate) fn compact_role_constraint(
    machine: &ConstraintMachine,
    constraint: &RoleConstraint,
) -> CompactRoleConstraint {
    CompactCollector::new(machine).compact_role_constraint(constraint)
}

pub(crate) fn compact_role_constraint_recording_merge_constraints(
    machine: &ConstraintMachine,
    constraint: &RoleConstraint,
) -> (CompactRoleConstraint, Vec<CompactMergeConstraint>) {
    CompactCollector::new_recording(machine)
        .compact_role_constraint_with_merge_constraints(constraint)
}
