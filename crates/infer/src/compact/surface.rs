use super::collect::CompactCollector;
use super::finalize::CompactFinalizer;
use super::*;

pub(crate) fn compact_type_var(machine: &ConstraintMachine, root: TypeVar) -> CompactRoot {
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
        if constraint.lhs == constraint.rhs || !applied.insert(constraint.key.clone()) {
            continue;
        }
        let (lhs, rhs) = {
            let mut finalizer = CompactFinalizer::new(&mut *machine);
            (
                finalizer.finalize_bounds(&constraint.lhs),
                finalizer.finalize_bounds(&constraint.rhs),
            )
        };
        changed |= machine.constrain_invariant_neu(lhs, rhs);
    }
    changed
}

pub(crate) fn apply_compact_subtype_constraints(
    machine: &mut ConstraintMachine,
    constraints: Vec<CompactSubtypeConstraint>,
    applied: &mut FxHashSet<CompactSubtypeConstraintKey>,
) -> bool {
    let mut changed = false;
    for constraint in constraints {
        if constraint.lower == constraint.upper || !applied.insert(constraint.key.clone()) {
            continue;
        }
        let (lower, upper) = {
            let mut finalizer = CompactFinalizer::new(&mut *machine);
            (
                finalizer.finalize_pos_type(&constraint.lower),
                finalizer.finalize_neg_type(&constraint.upper),
            )
        };
        changed |= machine.constrain_subtype(lower, upper);
    }
    changed
}

pub(crate) fn compact_reachable_role_constraints(
    machine: &ConstraintMachine,
    seed: &CompactRoot,
    constraints: &[RoleConstraint],
) -> Vec<CompactRoleConstraint> {
    CompactCollector::new(machine).compact_reachable_role_constraints(seed, constraints)
}

pub(crate) fn compact_reachable_role_constraints_recording_merge_constraints(
    machine: &ConstraintMachine,
    seed: &CompactRoot,
    constraints: &[RoleConstraint],
) -> (Vec<CompactRoleConstraint>, Vec<CompactMergeConstraint>) {
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
