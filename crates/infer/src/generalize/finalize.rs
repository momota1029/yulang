use super::*;

pub(crate) fn finalize_generalized_compact_root(
    types: &mut TypeArena,
    machine: &ConstraintMachine,
    root: &GeneralizedCompactRoot,
) -> FinalizedGeneralizedCompactRoot {
    let mut compact = root.compact.clone();
    let mut role_predicates = root.role_predicates.clone();
    clone_compact_stack_weights_for_scheme(
        machine.types(),
        types,
        &mut compact,
        &mut role_predicates,
    );
    let finalized = finalize_compact_root(types, &compact);
    let role_predicates = finalize_compact_role_predicates(types, &role_predicates);
    FinalizedGeneralizedCompactRoot {
        scheme: Scheme {
            quantifiers: root.quantifiers.clone(),
            role_predicates,
            recursive_bounds: finalized.rec_vars.clone(),
            stack_quantifiers: root.stack_quantifiers.clone(),
            predicate: finalized.root,
        },
    }
}

/// Freeze one already-canonical compact boundary interval into the scheme arena.
///
/// Stack-weight type arguments still refer to the inference arena at this point, so the
/// structural freeze remaps those arguments before allocating the neutral interval. It does not
/// simplify the bound or add constraints.
pub(crate) fn finalize_compact_boundary_bounds(
    types: &mut TypeArena,
    machine: &ConstraintMachine,
    bounds: &CompactBounds,
) -> NeuId {
    let mut bounds = bounds.clone();
    clone_compact_stack_weights_in_bounds(machine.types(), types, &mut bounds);
    finalize_compact_bounds(types, &bounds)
}

fn finalize_compact_role_predicates(
    types: &mut TypeArena,
    predicates: &[CompactRoleConstraint],
) -> Vec<RolePredicate> {
    predicates
        .iter()
        .map(|predicate| RolePredicate {
            role: predicate.role.clone(),
            inputs: predicate
                .inputs
                .iter()
                .map(|arg| finalize_compact_role_arg(types, arg))
                .collect(),
            associated: predicate
                .associated
                .iter()
                .map(|associated| RoleAssociatedType {
                    name: associated.name.clone(),
                    value: finalize_compact_role_arg_invariant(types, &associated.value),
                })
                .collect(),
        })
        .collect()
}

fn finalize_compact_role_arg(types: &mut TypeArena, arg: &CompactRoleArg) -> RolePredicateArg {
    match arg.polarity {
        CompactRoleArgPolarity::Covariant => {
            RolePredicateArg::Covariant(finalize_compact_bounds_lower(types, &arg.bounds))
        }
        CompactRoleArgPolarity::Contravariant => {
            RolePredicateArg::Contravariant(finalize_compact_bounds_upper(types, &arg.bounds))
        }
        CompactRoleArgPolarity::Invariant => {
            RolePredicateArg::Invariant(finalize_compact_bounds(types, &arg.bounds))
        }
    }
}

fn finalize_compact_role_arg_invariant(types: &mut TypeArena, arg: &CompactRoleArg) -> NeuId {
    finalize_compact_bounds(types, &arg.bounds)
}

pub(crate) fn clone_role_impl_candidate_between_arenas(
    source: &TypeArena,
    target: &mut TypeArena,
    candidate: &RoleImplCandidate,
) -> RoleImplCandidate {
    RoleImplCandidate {
        impl_def: candidate.impl_def,
        role: candidate.role.clone(),
        inputs: candidate
            .inputs
            .iter()
            .map(|arg| clone_role_constraint_arg_between_arenas(source, target, arg))
            .collect(),
        associated: candidate
            .associated
            .iter()
            .map(|associated| RoleAssociatedConstraint {
                name: associated.name.clone(),
                value: clone_role_constraint_arg_between_arenas(source, target, &associated.value),
            })
            .collect(),
        prerequisites: candidate
            .prerequisites
            .iter()
            .map(|constraint| clone_role_constraint_between_arenas(source, target, constraint))
            .collect(),
        methods: candidate.methods.clone(),
    }
}

fn clone_role_constraint_between_arenas(
    source: &TypeArena,
    target: &mut TypeArena,
    constraint: &RoleConstraint,
) -> RoleConstraint {
    RoleConstraint {
        role: constraint.role.clone(),
        inputs: constraint
            .inputs
            .iter()
            .map(|arg| clone_role_constraint_arg_between_arenas(source, target, arg))
            .collect(),
        associated: constraint
            .associated
            .iter()
            .map(|associated| RoleAssociatedConstraint {
                name: associated.name.clone(),
                value: clone_role_constraint_arg_between_arenas(source, target, &associated.value),
            })
            .collect(),
    }
}

fn clone_role_constraint_arg_between_arenas(
    source: &TypeArena,
    target: &mut TypeArena,
    arg: &RoleConstraintArg,
) -> RoleConstraintArg {
    RoleConstraintArg {
        lower: clone_pos_between_arenas(source, target, arg.lower),
        upper: clone_neg_between_arenas(source, target, arg.upper),
    }
}

fn clone_compact_stack_weights_for_scheme(
    source: &TypeArena,
    target: &mut TypeArena,
    root: &mut CompactRoot,
    role_predicates: &mut [CompactRoleConstraint],
) {
    clone_compact_stack_weights_in_type(source, target, &mut root.root);
    for rec in &mut root.rec_vars {
        clone_compact_stack_weights_in_bounds(source, target, &mut rec.bounds);
    }
    for predicate in role_predicates {
        for input in &mut predicate.inputs {
            clone_compact_stack_weights_in_role_arg(source, target, input);
        }
        for associated in &mut predicate.associated {
            clone_compact_stack_weights_in_role_arg(source, target, &mut associated.value);
        }
    }
}

fn clone_compact_stack_weights_in_role_arg(
    source: &TypeArena,
    target: &mut TypeArena,
    arg: &mut CompactRoleArg,
) {
    clone_compact_stack_weights_in_bounds(source, target, &mut arg.bounds);
}

fn clone_compact_stack_weights_in_type(
    source: &TypeArena,
    target: &mut TypeArena,
    ty: &mut CompactType,
) {
    for var in &mut ty.vars {
        if !var.weight.is_empty() {
            var.weight = clone_stack_weight_between_arenas(source, target, var.weight.clone());
        }
    }
    for args in ty.cons.values_mut() {
        for arg in args {
            clone_compact_stack_weights_in_bounds(source, target, arg);
        }
    }
    for fun in &mut ty.funs {
        clone_compact_stack_weights_in_type(source, target, &mut fun.arg);
        clone_compact_stack_weights_in_type(source, target, &mut fun.arg_eff);
        clone_compact_stack_weights_in_type(source, target, &mut fun.ret_eff);
        clone_compact_stack_weights_in_type(source, target, &mut fun.ret);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            clone_compact_stack_weights_in_type(source, target, &mut field.value);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            clone_compact_stack_weights_in_type(source, target, &mut field.value);
        }
        clone_compact_stack_weights_in_type(source, target, &mut spread.tail);
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                clone_compact_stack_weights_in_type(source, target, payload);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            clone_compact_stack_weights_in_type(source, target, item);
        }
    }
    for row in &mut ty.rows {
        for args in row.items.values_mut() {
            for arg in args {
                clone_compact_stack_weights_in_bounds(source, target, arg);
            }
        }
        clone_compact_stack_weights_in_type(source, target, &mut row.tail);
    }
}

fn clone_compact_stack_weights_in_bounds(
    source: &TypeArena,
    target: &mut TypeArena,
    bounds: &mut CompactBounds,
) {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            clone_compact_stack_weights_in_type(source, target, lower);
            clone_compact_stack_weights_in_type(source, target, upper);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                clone_compact_stack_weights_in_bounds(source, target, arg);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            clone_compact_stack_weights_in_bounds(source, target, arg);
            clone_compact_stack_weights_in_bounds(source, target, arg_eff);
            clone_compact_stack_weights_in_bounds(source, target, ret_eff);
            clone_compact_stack_weights_in_bounds(source, target, ret);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                clone_compact_stack_weights_in_bounds(source, target, &mut field.value);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    clone_compact_stack_weights_in_bounds(source, target, payload);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                clone_compact_stack_weights_in_bounds(source, target, item);
            }
        }
    }
}

fn clone_subtractability(
    source: &TypeArena,
    target: &mut TypeArena,
    subtractability: &Subtractability,
) -> Subtractability {
    match subtractability {
        Subtractability::Empty => Subtractability::Empty,
        Subtractability::All => Subtractability::All,
        Subtractability::AllExcept(path, args) => Subtractability::AllExcept(
            path.clone(),
            args.iter()
                .map(|arg| clone_neu_between_arenas(source, target, *arg))
                .collect(),
        ),
        Subtractability::AllExceptMany(families) => Subtractability::AllExceptMany(
            families
                .iter()
                .map(|(path, args)| {
                    (
                        path.clone(),
                        args.iter()
                            .map(|arg| clone_neu_between_arenas(source, target, *arg))
                            .collect(),
                    )
                })
                .collect(),
        ),
        Subtractability::Set(path, args) => Subtractability::Set(
            path.clone(),
            args.iter()
                .map(|arg| clone_neu_between_arenas(source, target, *arg))
                .collect(),
        ),
        Subtractability::SetMany(families) => Subtractability::SetMany(
            families
                .iter()
                .map(|(path, args)| {
                    (
                        path.clone(),
                        args.iter()
                            .map(|arg| clone_neu_between_arenas(source, target, *arg))
                            .collect(),
                    )
                })
                .collect(),
        ),
    }
}

fn clone_stack_weight_between_arenas(
    source: &TypeArena,
    target: &mut TypeArena,
    weight: StackWeight,
) -> StackWeight {
    let mut out = StackWeight::filter(clone_subtractability(source, target, weight.filter_set()));
    for entry in weight.entries() {
        for subtractability in &entry.floor {
            out = out.compose(&StackWeight::floor(
                entry.id,
                clone_subtractability(source, target, subtractability),
            ));
        }
        out = out.compose(&StackWeight::pops(entry.id, entry.pops));
        for subtractability in &entry.stack {
            out = out.compose(&StackWeight::push(
                entry.id,
                clone_subtractability(source, target, subtractability),
            ));
        }
    }
    out
}

fn clone_pos_between_arenas(source: &TypeArena, target: &mut TypeArena, id: PosId) -> PosId {
    let pos = match source.pos(id).clone() {
        Pos::Bot => Pos::Bot,
        Pos::Var(var) => Pos::Var(var),
        Pos::Con(path, args) => Pos::Con(
            path,
            args.into_iter()
                .map(|arg| clone_neu_between_arenas(source, target, arg))
                .collect(),
        ),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => Pos::Fun {
            arg: clone_neg_between_arenas(source, target, arg),
            arg_eff: clone_neg_between_arenas(source, target, arg_eff),
            ret_eff: clone_pos_between_arenas(source, target, ret_eff),
            ret: clone_pos_between_arenas(source, target, ret),
        },
        Pos::Record(fields) => Pos::Record(clone_fields_between_arenas(
            source,
            target,
            fields,
            clone_pos_between_arenas,
        )),
        Pos::RecordTailSpread { fields, tail } => Pos::RecordTailSpread {
            fields: clone_fields_between_arenas(source, target, fields, clone_pos_between_arenas),
            tail: clone_pos_between_arenas(source, target, tail),
        },
        Pos::RecordHeadSpread { tail, fields } => Pos::RecordHeadSpread {
            tail: clone_pos_between_arenas(source, target, tail),
            fields: clone_fields_between_arenas(source, target, fields, clone_pos_between_arenas),
        },
        Pos::PolyVariant(items) => Pos::PolyVariant(
            items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| clone_pos_between_arenas(source, target, payload))
                            .collect(),
                    )
                })
                .collect(),
        ),
        Pos::Tuple(items) => Pos::Tuple(
            items
                .into_iter()
                .map(|item| clone_pos_between_arenas(source, target, item))
                .collect(),
        ),
        Pos::Row(items) => Pos::Row(
            items
                .into_iter()
                .map(|item| clone_pos_between_arenas(source, target, item))
                .collect(),
        ),
        Pos::NonSubtract(pos, weight) => Pos::NonSubtract(
            clone_pos_between_arenas(source, target, pos),
            clone_stack_weight_between_arenas(source, target, weight),
        ),
        Pos::Stack { inner, weight } => Pos::Stack {
            inner: clone_pos_between_arenas(source, target, inner),
            weight: clone_stack_weight_between_arenas(source, target, weight),
        },
        Pos::Union(left, right) => Pos::Union(
            clone_pos_between_arenas(source, target, left),
            clone_pos_between_arenas(source, target, right),
        ),
    };
    target.alloc_pos(pos)
}

fn clone_neg_between_arenas(source: &TypeArena, target: &mut TypeArena, id: NegId) -> NegId {
    let neg = match source.neg(id).clone() {
        Neg::Top => Neg::Top,
        Neg::Bot => Neg::Bot,
        Neg::Var(var) => Neg::Var(var),
        Neg::Con(path, args) => Neg::Con(
            path,
            args.into_iter()
                .map(|arg| clone_neu_between_arenas(source, target, arg))
                .collect(),
        ),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => Neg::Fun {
            arg: clone_pos_between_arenas(source, target, arg),
            arg_eff: clone_pos_between_arenas(source, target, arg_eff),
            ret_eff: clone_neg_between_arenas(source, target, ret_eff),
            ret: clone_neg_between_arenas(source, target, ret),
        },
        Neg::Record(fields) => Neg::Record(clone_fields_between_arenas(
            source,
            target,
            fields,
            clone_neg_between_arenas,
        )),
        Neg::PolyVariant(items) => Neg::PolyVariant(
            items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| clone_neg_between_arenas(source, target, payload))
                            .collect(),
                    )
                })
                .collect(),
        ),
        Neg::Tuple(items) => Neg::Tuple(
            items
                .into_iter()
                .map(|item| clone_neg_between_arenas(source, target, item))
                .collect(),
        ),
        Neg::Row(items, tail) => Neg::Row(
            items
                .into_iter()
                .map(|item| clone_neg_between_arenas(source, target, item))
                .collect(),
            clone_neg_between_arenas(source, target, tail),
        ),
        Neg::Stack { inner, weight } => Neg::Stack {
            inner: clone_neg_between_arenas(source, target, inner),
            weight: clone_stack_weight_between_arenas(source, target, weight),
        },
        Neg::Intersection(left, right) => Neg::Intersection(
            clone_neg_between_arenas(source, target, left),
            clone_neg_between_arenas(source, target, right),
        ),
    };
    target.alloc_neg(neg)
}

fn clone_neu_between_arenas(source: &TypeArena, target: &mut TypeArena, id: NeuId) -> NeuId {
    let neu = match source.neu(id).clone() {
        Neu::Bounds(lower, upper) => Neu::Bounds(
            clone_pos_between_arenas(source, target, lower),
            clone_neg_between_arenas(source, target, upper),
        ),
        Neu::Con(path, args) => Neu::Con(
            path,
            args.into_iter()
                .map(|arg| clone_neu_between_arenas(source, target, arg))
                .collect(),
        ),
        Neu::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => Neu::Fun {
            arg: clone_neu_between_arenas(source, target, arg),
            arg_eff: clone_neu_between_arenas(source, target, arg_eff),
            ret_eff: clone_neu_between_arenas(source, target, ret_eff),
            ret: clone_neu_between_arenas(source, target, ret),
        },
        Neu::Record(fields) => Neu::Record(clone_fields_between_arenas(
            source,
            target,
            fields,
            clone_neu_between_arenas,
        )),
        Neu::PolyVariant(items) => Neu::PolyVariant(
            items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| clone_neu_between_arenas(source, target, payload))
                            .collect(),
                    )
                })
                .collect(),
        ),
        Neu::Tuple(items) => Neu::Tuple(
            items
                .into_iter()
                .map(|item| clone_neu_between_arenas(source, target, item))
                .collect(),
        ),
    };
    target.alloc_neu(neu)
}

fn clone_fields_between_arenas<Id: Copy>(
    source: &TypeArena,
    target: &mut TypeArena,
    fields: Vec<RecordField<Id>>,
    clone_value: fn(&TypeArena, &mut TypeArena, Id) -> Id,
) -> Vec<RecordField<Id>> {
    fields
        .into_iter()
        .map(|field| RecordField {
            name: field.name,
            value: clone_value(source, target, field.value),
            optional: field.optional,
        })
        .collect()
}
