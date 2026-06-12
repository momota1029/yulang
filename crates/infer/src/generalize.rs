//! Compact result の量化計画を作る入口。
//!
//! collect / simplify は `compact` が持ち、ここでは「どの変数を scheme の quantifier にするか」
//! を compact 表現のまま決める。`poly::Scheme` への finalize は最後の出口として分ける。

use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RoleAssociatedType, RolePredicate, Scheme,
    SchemeSubtractFact, StackWeight, SubtractId, Subtractability, TypeArena, TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::compact::{
    CompactBounds, CompactCon, CompactFun, CompactPolyVariant, CompactRecord, CompactRecordSpread,
    CompactRecursiveVar, CompactRoleArg, CompactRoleConstraint, CompactRoot, CompactRow,
    CompactSandwich, CompactSandwichKind, CompactSimplification, CompactTuple, CompactType,
    CompactVar, CompactVarSubstitution, compact_type_var, finalize_compact_bounds,
    finalize_compact_root, finalize_compact_type, finalize_compact_type_to_neg,
    merge_compact_types, simplify_compact_root_with_roles_and_non_generic,
};
#[cfg(test)]
use crate::constraints::ConstraintWeight;
use crate::constraints::{ConstraintMachine, TypeLevel};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GeneralizedCompactRoot {
    pub(crate) compact: CompactRoot,
    pub(crate) role_predicates: Vec<CompactRoleConstraint>,
    pub(crate) quantifiers: Vec<TypeVar>,
    pub(crate) stack_quantifiers: Vec<SubtractId>,
    pub(crate) subtracts: Vec<(TypeVar, SubtractId)>,
    pub(crate) substitutions: Vec<CompactVarSubstitution>,
    pub(crate) sandwiches: Vec<CompactSandwich>,
}

pub(crate) struct FinalizedGeneralizedCompactRoot {
    pub(crate) scheme: Scheme,
}

pub(crate) fn generalize_type_var(
    machine: &ConstraintMachine,
    root: TypeVar,
    boundary: TypeLevel,
    non_generic: &FxHashSet<TypeVar>,
) -> GeneralizedCompactRoot {
    let compact = compact_type_var(machine, root);
    generalize_prepared_compact_root(machine, boundary, compact, non_generic)
}

pub(crate) fn generalize_prepared_compact_root(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    compact: CompactRoot,
    non_generic: &FxHashSet<TypeVar>,
) -> GeneralizedCompactRoot {
    generalize_prepared_compact_root_with_roles(machine, boundary, compact, Vec::new(), non_generic)
}

pub(crate) fn generalize_prepared_compact_root_with_roles(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    mut compact: CompactRoot,
    mut role_predicates: Vec<CompactRoleConstraint>,
    non_generic: &FxHashSet<TypeVar>,
) -> GeneralizedCompactRoot {
    let simplification_boundary = boundary.child();
    let simplification = simplify_compact_root_with_roles_and_non_generic(
        machine,
        simplification_boundary,
        &mut compact,
        &mut role_predicates,
        non_generic,
    );
    generalize_compact_root_with_simplification(
        machine,
        boundary,
        compact,
        role_predicates,
        non_generic,
        simplification,
    )
}

#[cfg(test)]
pub(crate) fn generalize_prepared_compact_root_with_roles_and_simplifications(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    mut compact: CompactRoot,
    mut role_predicates: Vec<CompactRoleConstraint>,
    simplifications: &[CompactSimplification],
    non_generic: &FxHashSet<TypeVar>,
) -> GeneralizedCompactRoot {
    apply_compact_simplifications_to_root_and_roles(
        &mut compact,
        &mut role_predicates,
        simplifications,
    );
    generalize_prepared_compact_root_with_roles(
        machine,
        boundary,
        compact,
        role_predicates,
        non_generic,
    )
}

#[cfg(test)]
pub(crate) fn generalize_compact_root(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: CompactRoot,
    non_generic: &FxHashSet<TypeVar>,
) -> GeneralizedCompactRoot {
    generalize_prepared_compact_root_with_roles(machine, boundary, root, Vec::new(), non_generic)
}

fn generalize_compact_root_with_simplification(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    mut root: CompactRoot,
    mut role_predicates: Vec<CompactRoleConstraint>,
    non_generic: &FxHashSet<TypeVar>,
    simplification: CompactSimplification,
) -> GeneralizedCompactRoot {
    let substitutions = simplification.substitutions;
    let sandwiches = simplification.sandwiches;
    prune_unreachable_recursive_bounds(&mut root, &role_predicates);

    let mut quantifiers =
        quantified_vars_in_root_and_roles(machine, boundary, &root, &role_predicates, non_generic);
    let mut subtracts = prepare_quantified_subtracts(
        machine,
        &quantifiers,
        &substitutions,
        non_generic,
        &mut root,
        &mut role_predicates,
    );
    prune_unreachable_recursive_bounds(&mut root, &role_predicates);
    cleanup_stack_weights_in_root_and_roles(&mut root, &mut role_predicates);
    cleanup_empty_stack_entries_with_plain_negative_occurrence(&mut root, &mut role_predicates);
    quantifiers =
        quantified_vars_in_root_and_roles(machine, boundary, &root, &role_predicates, non_generic);
    let quantifier_set = quantifiers.iter().copied().collect::<FxHashSet<_>>();
    subtracts.retain(|(var, _)| quantifier_set.contains(var));
    let mut stack_quantifiers = sorted_stack_quantifiers(&root, &role_predicates, &quantifier_set);
    // scheme へ残す subtract に入らなかった id の weight は、scheme の compact からは剥がす。
    // 重み付き境界は machine 側に残っており、scheme 表示では「使い切られた寿命境界は消える」。
    let mut scheme_ids = subtracts
        .iter()
        .map(|(_, id)| *id)
        .collect::<FxHashSet<_>>();
    scheme_ids.extend(stack_quantifiers.iter().copied());
    let stray_ids = all_stack_ids_in_root_and_roles(&root, &role_predicates)
        .difference(&scheme_ids)
        .copied()
        .collect::<FxHashSet<_>>();
    if !stray_ids.is_empty() {
        prune_dead_subtract_weights_in_root_and_roles(&mut root, &mut role_predicates, &stray_ids);
        quantifiers = quantified_vars_in_root_and_roles(
            machine,
            boundary,
            &root,
            &role_predicates,
            non_generic,
        );
        let quantifier_set = quantifiers.iter().copied().collect::<FxHashSet<_>>();
        subtracts.retain(|(var, _)| quantifier_set.contains(var));
        stack_quantifiers = sorted_stack_quantifiers(&root, &role_predicates, &quantifier_set);
    }
    GeneralizedCompactRoot {
        compact: root,
        role_predicates,
        quantifiers,
        stack_quantifiers,
        subtracts,
        substitutions,
        sandwiches,
    }
}

pub(crate) fn finalize_generalized_compact_root(
    types: &mut TypeArena,
    machine: &ConstraintMachine,
    root: &GeneralizedCompactRoot,
) -> FinalizedGeneralizedCompactRoot {
    let finalized = finalize_compact_root(types, &root.compact);
    let role_predicates = finalize_compact_role_predicates(types, &root.role_predicates);
    let subtracts = finalize_scheme_subtracts(types, machine, &root.subtracts);
    FinalizedGeneralizedCompactRoot {
        scheme: Scheme {
            quantifiers: root.quantifiers.clone(),
            role_predicates,
            recursive_bounds: finalized.rec_vars.clone(),
            stack_quantifiers: root.stack_quantifiers.clone(),
            predicate: finalized.root,
            subtracts,
        },
    }
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
                    value: finalize_compact_role_arg(types, &associated.value),
                })
                .collect(),
        })
        .collect()
}

fn finalize_compact_role_arg(types: &mut TypeArena, arg: &CompactRoleArg) -> NeuId {
    if let Some(bounds) = exact_compact_role_arg_bounds(arg) {
        return finalize_compact_bounds(types, &bounds);
    }
    let self_var = common_var_in_types(&arg.lower, &arg.upper)
        .or_else(|| unique_var_in_type(&arg.lower))
        .or_else(|| unique_var_in_type(&arg.upper))
        .unwrap_or_else(|| {
            panic!("compact role arg should be exact or retain a shared variable: {arg:?}")
        });
    let lower = finalize_compact_type(types, &arg.lower);
    let upper = finalize_compact_type_to_neg(types, &arg.upper);
    types.alloc_neu(Neu::Bounds(lower, self_var, upper))
}

fn finalize_scheme_subtracts(
    types: &mut TypeArena,
    machine: &ConstraintMachine,
    subtracts: &[(TypeVar, SubtractId)],
) -> Vec<SchemeSubtractFact> {
    subtracts
        .iter()
        .map(|(var, id)| {
            let fact = machine
                .subtracts()
                .facts(*var)
                .iter()
                .find(|fact| fact.id == *id)
                .or_else(|| machine.subtracts().fact_by_id(*id))
                .expect("generalized subtract fact should exist in the source machine");
            SchemeSubtractFact {
                var: *var,
                id: *id,
                subtractability: clone_subtractability(
                    machine.types(),
                    types,
                    &fact.subtractability,
                ),
            }
        })
        .collect()
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
    let mut out = StackWeight::empty();
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
        Pos::NonSubtract(pos, subtract) => {
            Pos::NonSubtract(clone_pos_between_arenas(source, target, pos), subtract)
        }
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
        Neu::Bounds(lower, var, upper) => Neu::Bounds(
            clone_pos_between_arenas(source, target, lower),
            var,
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

fn exact_compact_role_arg_bounds(arg: &CompactRoleArg) -> Option<CompactBounds> {
    let lower = exact_compact_type_bounds(&arg.lower)?;
    let upper = exact_compact_type_bounds(&arg.upper)?;
    (lower == upper).then_some(lower)
}

fn exact_compact_type_bounds(ty: &CompactType) -> Option<CompactBounds> {
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
        let con = ty.cons[0].clone();
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
            arg: Box::new(exact_compact_type_bounds(&fun.arg)?),
            arg_eff: Box::new(exact_compact_type_bounds(&fun.arg_eff)?),
            ret_eff: Box::new(exact_compact_type_bounds(&fun.ret_eff)?),
            ret: Box::new(exact_compact_type_bounds(&fun.ret)?),
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
        return ty.tuples[0]
            .items
            .iter()
            .map(exact_compact_type_bounds)
            .collect::<Option<Vec<_>>>()
            .map(|items| CompactBounds::Tuple { items });
    }
    None
}

fn unique_var_in_type(ty: &CompactType) -> Option<TypeVar> {
    let mut vars = ty.vars.iter().map(|var| var.var).collect::<Vec<_>>();
    vars.sort_by_key(|var| var.0);
    vars.dedup();
    (vars.len() == 1).then(|| vars[0])
}

pub(crate) fn finalize_generalized_compact_root_with_ancestors(
    types: &mut TypeArena,
    machine: &ConstraintMachine,
    root: &GeneralizedCompactRoot,
    ancestors: &[&GeneralizedCompactRoot],
) -> FinalizedGeneralizedCompactRoot {
    let mut root = root.clone();
    apply_ancestor_simplifications(&mut root, ancestors);
    prune_unreachable_recursive_bounds(&mut root.compact, &root.role_predicates);
    prune_dead_quantifiers(&mut root);
    prune_existing_subtracts(&mut root);
    cleanup_stack_weights_in_root_and_roles(&mut root.compact, &mut root.role_predicates);
    cleanup_empty_stack_entries_with_plain_negative_occurrence(
        &mut root.compact,
        &mut root.role_predicates,
    );
    prune_unreachable_recursive_bounds(&mut root.compact, &root.role_predicates);
    prune_dead_quantifiers(&mut root);
    let quantifier_set = root.quantifiers.iter().copied().collect::<FxHashSet<_>>();
    root.stack_quantifiers =
        sorted_stack_quantifiers(&root.compact, &root.role_predicates, &quantifier_set);
    finalize_generalized_compact_root(types, machine, &root)
}

#[cfg(test)]
pub(crate) fn quantified_vars(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &CompactRoot,
    non_generic: &FxHashSet<TypeVar>,
) -> Vec<TypeVar> {
    quantified_vars_in_root_and_roles(machine, boundary, root, &[], non_generic)
}

fn quantified_vars_in_root_and_roles(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &CompactRoot,
    role_predicates: &[CompactRoleConstraint],
    non_generic: &FxHashSet<TypeVar>,
) -> Vec<TypeVar> {
    let mut vars = Vec::new();
    collect_root_free_vars(root, &mut vars);
    for role in role_predicates {
        collect_role_free_vars(role, &mut vars);
    }
    vars.retain(|var| machine.level_of(*var) > boundary && !non_generic.contains(var));
    vars.sort_by_key(|var| var.0);
    vars.dedup();
    vars
}

fn quantified_subtracts(
    machine: &ConstraintMachine,
    quantifiers: &[TypeVar],
    substitutions: &[CompactVarSubstitution],
) -> Vec<(TypeVar, SubtractId)> {
    let quantifier_set = quantifiers.iter().copied().collect::<FxHashSet<_>>();
    let mut subtracts = Vec::new();
    for var in quantifiers {
        subtracts.extend(
            machine
                .subtracts()
                .facts(*var)
                .iter()
                .map(|fact| (*var, fact.id)),
        );
    }
    for substitution in substitutions {
        let Some(target) = substitution.target else {
            continue;
        };
        if !quantifier_set.contains(&target) {
            continue;
        }
        subtracts.extend(
            machine
                .subtracts()
                .facts(substitution.source)
                .iter()
                .map(|fact| (target, fact.id)),
        );
    }
    subtracts.sort_by_key(|(var, subtract)| (var.0, subtract.0));
    subtracts.dedup();
    subtracts
}

fn prepare_quantified_subtracts(
    machine: &ConstraintMachine,
    quantifiers: &[TypeVar],
    substitutions: &[CompactVarSubstitution],
    non_generic: &FxHashSet<TypeVar>,
    root: &mut CompactRoot,
    role_predicates: &mut [CompactRoleConstraint],
) -> Vec<(TypeVar, SubtractId)> {
    let mut candidates = quantified_subtracts(machine, quantifiers, substitutions);
    // scheme へ保持するのは注釈・データ宣言が直接導入した id だけ。
    // instantiate の clone で再登録された fact（推論残差）はこの境界で消える。
    candidates.retain(|(_, id)| machine.subtract_declared(*id));
    if candidates.is_empty() {
        return Vec::new();
    }

    let candidate_ids = candidates
        .iter()
        .map(|(_, subtract)| *subtract)
        .collect::<FxHashSet<_>>();
    // A subtract id stays useful if at least one covariant occurrence is not
    // protected by the corresponding non-subtract weight.
    let live_subtracts = live_subtracts(root, role_predicates, &candidates);
    let live_ids = live_subtracts
        .iter()
        .map(|(_, subtract)| *subtract)
        .collect::<FxHashSet<_>>();
    let live_stack_ids = live_covariant_stack_ids_in_root_and_roles(root, role_predicates);
    let non_generic_subtract_ids = non_generic_subtract_ids(machine, non_generic);
    let dead_ids = candidate_ids
        .difference(&live_ids)
        .copied()
        .filter(|id| !live_stack_ids.contains(id))
        .filter(|id| !non_generic_subtract_ids.contains(id))
        .collect::<FxHashSet<_>>();
    if !dead_ids.is_empty() {
        prune_dead_subtract_weights_in_root_and_roles(root, role_predicates, &dead_ids);
    }

    candidates
        .into_iter()
        .filter(|candidate| live_subtracts.contains(candidate))
        .collect()
}

fn non_generic_subtract_ids(
    machine: &ConstraintMachine,
    non_generic: &FxHashSet<TypeVar>,
) -> FxHashSet<SubtractId> {
    non_generic
        .iter()
        .flat_map(|var| machine.subtracts().facts(*var).iter().map(|fact| fact.id))
        .collect()
}

fn apply_ancestor_simplifications(
    root: &mut GeneralizedCompactRoot,
    ancestors: &[&GeneralizedCompactRoot],
) {
    for ancestor in ancestors {
        apply_var_substitutions(root, &ancestor.substitutions);
        apply_sandwiches_to_root_and_roles(
            &mut root.compact,
            &mut root.role_predicates,
            &ancestor.sandwiches,
        );
    }
}

pub(crate) fn apply_compact_simplifications_to_root_and_roles(
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    simplifications: &[CompactSimplification],
) {
    for simplification in simplifications {
        apply_var_substitutions_to_root_and_roles(root, roles, &simplification.substitutions);
        apply_sandwiches_to_root_and_roles(root, roles, &simplification.sandwiches);
    }
}

fn apply_var_substitutions(
    root: &mut GeneralizedCompactRoot,
    substitutions: &[CompactVarSubstitution],
) {
    if substitutions.is_empty() {
        return;
    }
    let map = var_substitution_map(substitutions);
    rewrite_root_vars(&mut root.compact, &map);
    rewrite_role_predicates_vars(&mut root.role_predicates, &map);
    let quantifier_set = root.quantifiers.iter().copied().collect::<FxHashSet<_>>();
    root.subtracts = root
        .subtracts
        .iter()
        .filter_map(|(var, id)| {
            let target = resolve_rewrite_target(*var, &map)?;
            if quantifier_set.contains(&target) {
                Some((target, *id))
            } else {
                None
            }
        })
        .collect();
    sort_dedup_subtracts(&mut root.subtracts);
}

fn apply_var_substitutions_to_root_and_roles(
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    substitutions: &[CompactVarSubstitution],
) {
    if substitutions.is_empty() {
        return;
    }
    let map = var_substitution_map(substitutions);
    rewrite_root_vars(root, &map);
    rewrite_role_predicates_vars(roles, &map);
}

fn var_substitution_map(
    substitutions: &[CompactVarSubstitution],
) -> FxHashMap<TypeVar, Option<TypeVar>> {
    substitutions
        .iter()
        .map(|substitution| (substitution.source, substitution.target))
        .collect()
}

fn rewrite_root_vars(root: &mut CompactRoot, substitutions: &FxHashMap<TypeVar, Option<TypeVar>>) {
    rewrite_type_vars(&mut root.root, substitutions);
    for rec in &mut root.rec_vars {
        if let Some(target) = resolve_rewrite_target(rec.var, substitutions) {
            rec.var = target;
        }
        rewrite_bounds_vars(&mut rec.bounds, substitutions);
    }
}

fn rewrite_role_predicates_vars(
    roles: &mut [CompactRoleConstraint],
    substitutions: &FxHashMap<TypeVar, Option<TypeVar>>,
) {
    for role in roles {
        rewrite_role_vars(role, substitutions);
    }
}

fn rewrite_role_vars(
    role: &mut CompactRoleConstraint,
    substitutions: &FxHashMap<TypeVar, Option<TypeVar>>,
) {
    for input in &mut role.inputs {
        rewrite_role_arg_vars(input, substitutions);
    }
    for associated in &mut role.associated {
        rewrite_role_arg_vars(&mut associated.value, substitutions);
    }
}

fn rewrite_role_arg_vars(
    arg: &mut CompactRoleArg,
    substitutions: &FxHashMap<TypeVar, Option<TypeVar>>,
) {
    rewrite_type_vars(&mut arg.lower, substitutions);
    rewrite_type_vars(&mut arg.upper, substitutions);
}

fn rewrite_type_vars(ty: &mut CompactType, substitutions: &FxHashMap<TypeVar, Option<TypeVar>>) {
    let mut vars = Vec::new();
    for mut var in std::mem::take(&mut ty.vars) {
        let Some(target) = resolve_rewrite_target(var.var, substitutions) else {
            continue;
        };
        var.var = target;
        push_compact_var_with_unioned_weight(&mut vars, var);
    }
    ty.vars = vars;

    for con in &mut ty.cons {
        for arg in &mut con.args {
            rewrite_bounds_vars(arg, substitutions);
        }
    }
    for fun in &mut ty.funs {
        rewrite_type_vars(&mut fun.arg, substitutions);
        rewrite_type_vars(&mut fun.arg_eff, substitutions);
        rewrite_type_vars(&mut fun.ret_eff, substitutions);
        rewrite_type_vars(&mut fun.ret, substitutions);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            rewrite_type_vars(&mut field.value, substitutions);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            rewrite_type_vars(&mut field.value, substitutions);
        }
        rewrite_type_vars(&mut spread.tail, substitutions);
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                rewrite_type_vars(payload, substitutions);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            rewrite_type_vars(item, substitutions);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            rewrite_type_vars(item, substitutions);
        }
        rewrite_type_vars(&mut row.tail, substitutions);
    }
}

fn push_compact_var_with_unioned_weight(vars: &mut Vec<CompactVar>, var: CompactVar) {
    if let Some(existing) = vars.iter_mut().find(|existing| existing.var == var.var) {
        existing.weight = existing.weight.union(&var.weight);
        existing.origin = existing.origin.merged(var.origin);
    } else {
        vars.push(var);
    }
}

fn rewrite_bounds_vars(
    bounds: &mut CompactBounds,
    substitutions: &FxHashMap<TypeVar, Option<TypeVar>>,
) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            if let Some(target) = resolve_rewrite_target(*self_var, substitutions) {
                *self_var = target;
            }
            rewrite_type_vars(lower, substitutions);
            rewrite_type_vars(upper, substitutions);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                rewrite_bounds_vars(arg, substitutions);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            rewrite_bounds_vars(arg, substitutions);
            rewrite_bounds_vars(arg_eff, substitutions);
            rewrite_bounds_vars(ret_eff, substitutions);
            rewrite_bounds_vars(ret, substitutions);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                rewrite_bounds_vars(&mut field.value, substitutions);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    rewrite_bounds_vars(payload, substitutions);
                }
            }
        }
    }
}

fn resolve_rewrite_target(
    source: TypeVar,
    substitutions: &FxHashMap<TypeVar, Option<TypeVar>>,
) -> Option<TypeVar> {
    let mut current = source;
    let mut seen = FxHashSet::default();
    loop {
        if !seen.insert(current) {
            return Some(current);
        }
        match substitutions.get(&current).copied() {
            None => return Some(current),
            Some(None) => return None,
            Some(Some(next)) => current = next,
        }
    }
}

fn apply_sandwiches_to_root_and_roles(
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    sandwiches: &[CompactSandwich],
) {
    if sandwiches.is_empty() {
        return;
    }
    let sandwiches = sandwiches
        .iter()
        .map(|sandwich| (sandwich.var, sandwich.kind.clone()))
        .collect::<FxHashMap<_, _>>();
    let mut fresh = FreshCompactVars::new(root);
    loop {
        let mut changed = false;
        root.root = apply_sandwiches_to_type(
            std::mem::take(&mut root.root),
            &sandwiches,
            &mut fresh,
            &mut changed,
        );
        for rec in &mut root.rec_vars {
            rec.bounds = apply_sandwiches_to_bounds(
                std::mem::replace(&mut rec.bounds, empty_interval(rec.var)),
                &sandwiches,
                &mut fresh,
                &mut changed,
            );
        }
        for role in &mut *roles {
            apply_sandwiches_to_role(role, &sandwiches, &mut fresh, &mut changed);
        }
        if !changed {
            return;
        }
    }
}

fn apply_sandwiches_to_role(
    role: &mut CompactRoleConstraint,
    sandwiches: &FxHashMap<TypeVar, CompactSandwichKind>,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
) {
    for input in &mut role.inputs {
        apply_sandwiches_to_role_arg(input, sandwiches, fresh, changed);
    }
    for associated in &mut role.associated {
        apply_sandwiches_to_role_arg(&mut associated.value, sandwiches, fresh, changed);
    }
}

fn apply_sandwiches_to_role_arg(
    arg: &mut CompactRoleArg,
    sandwiches: &FxHashMap<TypeVar, CompactSandwichKind>,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
) {
    arg.lower =
        apply_sandwiches_to_type(std::mem::take(&mut arg.lower), sandwiches, fresh, changed);
    arg.upper =
        apply_sandwiches_to_type(std::mem::take(&mut arg.upper), sandwiches, fresh, changed);
}

fn apply_sandwiches_to_type(
    mut ty: CompactType,
    sandwiches: &FxHashMap<TypeVar, CompactSandwichKind>,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
) -> CompactType {
    for con in &mut ty.cons {
        for arg in &mut con.args {
            *arg = apply_sandwiches_to_bounds(
                std::mem::replace(arg, empty_interval(TypeVar(0))),
                sandwiches,
                fresh,
                changed,
            );
        }
    }
    for fun in &mut ty.funs {
        fun.arg =
            apply_sandwiches_to_type(std::mem::take(&mut fun.arg), sandwiches, fresh, changed);
        fun.arg_eff =
            apply_sandwiches_to_type(std::mem::take(&mut fun.arg_eff), sandwiches, fresh, changed);
        fun.ret_eff =
            apply_sandwiches_to_type(std::mem::take(&mut fun.ret_eff), sandwiches, fresh, changed);
        fun.ret =
            apply_sandwiches_to_type(std::mem::take(&mut fun.ret), sandwiches, fresh, changed);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            field.value = apply_sandwiches_to_type(
                std::mem::take(&mut field.value),
                sandwiches,
                fresh,
                changed,
            );
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            field.value = apply_sandwiches_to_type(
                std::mem::take(&mut field.value),
                sandwiches,
                fresh,
                changed,
            );
        }
        spread.tail = Box::new(apply_sandwiches_to_type(
            *std::mem::take(&mut spread.tail),
            sandwiches,
            fresh,
            changed,
        ));
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                *payload =
                    apply_sandwiches_to_type(std::mem::take(payload), sandwiches, fresh, changed);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            *item = apply_sandwiches_to_type(std::mem::take(item), sandwiches, fresh, changed);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            *item = apply_sandwiches_to_type(std::mem::take(item), sandwiches, fresh, changed);
        }
        row.tail = Box::new(apply_sandwiches_to_type(
            *std::mem::take(&mut row.tail),
            sandwiches,
            fresh,
            changed,
        ));
    }
    ty
}

fn apply_sandwiches_to_bounds(
    bounds: CompactBounds,
    sandwiches: &FxHashMap<TypeVar, CompactSandwichKind>,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
) -> CompactBounds {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            if let Some(lifted) = try_apply_sandwich(self_var, &lower, &upper, sandwiches, fresh) {
                *changed = true;
                apply_sandwiches_to_bounds(lifted, sandwiches, fresh, changed)
            } else {
                CompactBounds::Interval {
                    self_var,
                    lower: apply_sandwiches_to_type(lower, sandwiches, fresh, changed),
                    upper: apply_sandwiches_to_type(upper, sandwiches, fresh, changed),
                }
            }
        }
        CompactBounds::Con { path, args } => CompactBounds::Con {
            path,
            args: args
                .into_iter()
                .map(|arg| apply_sandwiches_to_bounds(arg, sandwiches, fresh, changed))
                .collect(),
        },
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactBounds::Fun {
            arg: Box::new(apply_sandwiches_to_bounds(*arg, sandwiches, fresh, changed)),
            arg_eff: Box::new(apply_sandwiches_to_bounds(
                *arg_eff, sandwiches, fresh, changed,
            )),
            ret_eff: Box::new(apply_sandwiches_to_bounds(
                *ret_eff, sandwiches, fresh, changed,
            )),
            ret: Box::new(apply_sandwiches_to_bounds(*ret, sandwiches, fresh, changed)),
        },
        CompactBounds::Record { fields } => CompactBounds::Record {
            fields: fields
                .into_iter()
                .map(|field| poly::types::RecordField {
                    name: field.name,
                    value: apply_sandwiches_to_bounds(field.value, sandwiches, fresh, changed),
                    optional: field.optional,
                })
                .collect(),
        },
        CompactBounds::PolyVariant { items } => CompactBounds::PolyVariant {
            items: items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| {
                                apply_sandwiches_to_bounds(payload, sandwiches, fresh, changed)
                            })
                            .collect(),
                    )
                })
                .collect(),
        },
        CompactBounds::Tuple { items } => CompactBounds::Tuple {
            items: items
                .into_iter()
                .map(|item| apply_sandwiches_to_bounds(item, sandwiches, fresh, changed))
                .collect(),
        },
    }
}

fn try_apply_sandwich(
    self_var: TypeVar,
    lower: &CompactType,
    upper: &CompactType,
    sandwiches: &FxHashMap<TypeVar, CompactSandwichKind>,
    fresh: &mut FreshCompactVars,
) -> Option<CompactBounds> {
    let center = if sandwiches.contains_key(&self_var) {
        self_var
    } else {
        common_var_in_types(lower, upper).filter(|var| sandwiches.contains_key(var))?
    };
    match sandwiches.get(&center)? {
        CompactSandwichKind::Con { path, arity } => {
            let lower_args = single_con(lower, path, *arity)?;
            let upper_args = single_con(upper, path, *arity)?;
            Some(CompactBounds::Con {
                path: path.clone(),
                args: lower_args
                    .iter()
                    .zip(upper_args)
                    .map(|(lower, upper)| merge_arg_bounds(lower, upper, fresh))
                    .collect(),
            })
        }
        CompactSandwichKind::Tuple { arity } => {
            let lower_items = single_tuple(lower, *arity)?;
            let upper_items = single_tuple(upper, *arity)?;
            Some(CompactBounds::Tuple {
                items: lower_items
                    .iter()
                    .zip(upper_items)
                    .map(|(lower, upper)| interval_from_types(lower.clone(), upper.clone(), fresh))
                    .collect(),
            })
        }
        CompactSandwichKind::Fun => {
            let lower_fun = single_fun(lower)?;
            let upper_fun = single_fun(upper)?;
            Some(CompactBounds::Fun {
                arg: Box::new(interval_from_types(
                    upper_fun.arg.clone(),
                    lower_fun.arg.clone(),
                    fresh,
                )),
                arg_eff: Box::new(interval_from_types(
                    upper_fun.arg_eff.clone(),
                    lower_fun.arg_eff.clone(),
                    fresh,
                )),
                ret_eff: Box::new(interval_from_types(
                    lower_fun.ret_eff.clone(),
                    upper_fun.ret_eff.clone(),
                    fresh,
                )),
                ret: Box::new(interval_from_types(
                    lower_fun.ret.clone(),
                    upper_fun.ret.clone(),
                    fresh,
                )),
            })
        }
    }
}

fn prune_unreachable_recursive_bounds(
    root: &mut CompactRoot,
    role_predicates: &[CompactRoleConstraint],
) -> bool {
    if root.rec_vars.is_empty() {
        return false;
    }

    let mut reachable = FxHashSet::default();
    collect_type_free_vars_into_set(&root.root, &mut reachable);
    for role in role_predicates {
        collect_role_free_vars_into_set(role, &mut reachable);
    }

    let mut keep = FxHashSet::default();
    loop {
        let mut changed = false;
        for rec in &root.rec_vars {
            if keep.contains(&rec.var) || !reachable.contains(&rec.var) {
                continue;
            }
            keep.insert(rec.var);
            collect_bounds_free_vars_into_set(&rec.bounds, &mut reachable);
            changed = true;
        }
        if !changed {
            break;
        }
    }

    let before = root.rec_vars.len();
    root.rec_vars.retain(|rec| keep.contains(&rec.var));
    before != root.rec_vars.len()
}

fn collect_role_free_vars_into_set(role: &CompactRoleConstraint, out: &mut FxHashSet<TypeVar>) {
    for input in &role.inputs {
        collect_type_free_vars_into_set(&input.lower, out);
        collect_type_free_vars_into_set(&input.upper, out);
    }
    for associated in &role.associated {
        collect_type_free_vars_into_set(&associated.value.lower, out);
        collect_type_free_vars_into_set(&associated.value.upper, out);
    }
}

fn collect_type_free_vars_into_set(ty: &CompactType, out: &mut FxHashSet<TypeVar>) {
    let mut vars = Vec::new();
    collect_type_free_vars(ty, &mut vars);
    out.extend(vars);
}

fn collect_bounds_free_vars_into_set(bounds: &CompactBounds, out: &mut FxHashSet<TypeVar>) {
    let mut vars = Vec::new();
    collect_bounds_free_vars(bounds, &mut vars);
    out.extend(vars);
}

fn prune_dead_quantifiers(root: &mut GeneralizedCompactRoot) {
    let mut free = Vec::new();
    collect_root_free_vars(&root.compact, &mut free);
    for role in &root.role_predicates {
        collect_role_free_vars(role, &mut free);
    }
    let free = free.into_iter().collect::<FxHashSet<_>>();
    root.quantifiers.retain(|var| free.contains(var));
}

fn prune_existing_subtracts(root: &mut GeneralizedCompactRoot) {
    let quantifiers = root.quantifiers.iter().copied().collect::<FxHashSet<_>>();
    root.subtracts.retain(|(var, _)| quantifiers.contains(var));
    let candidate_ids = root
        .subtracts
        .iter()
        .map(|(_, subtract)| *subtract)
        .collect::<FxHashSet<_>>();
    if candidate_ids.is_empty() {
        return;
    }

    let live_subtracts = live_subtracts(&root.compact, &root.role_predicates, &root.subtracts);
    let live_ids = live_subtracts
        .iter()
        .map(|(_, subtract)| *subtract)
        .collect::<FxHashSet<_>>();
    let live_stack_ids =
        live_covariant_stack_ids_in_root_and_roles(&root.compact, &root.role_predicates);
    let dead_ids = candidate_ids
        .difference(&live_ids)
        .copied()
        .filter(|id| !live_stack_ids.contains(id))
        .collect::<FxHashSet<_>>();
    if !dead_ids.is_empty() {
        prune_dead_subtract_weights_in_root_and_roles(
            &mut root.compact,
            &mut root.role_predicates,
            &dead_ids,
        );
    }
    root.subtracts
        .retain(|subtract| live_subtracts.contains(subtract));
    sort_dedup_subtracts(&mut root.subtracts);
}

fn sort_dedup_subtracts(subtracts: &mut Vec<(TypeVar, SubtractId)>) {
    subtracts.sort_by_key(|(var, subtract)| (var.0, subtract.0));
    subtracts.dedup();
}

fn merge_arg_bounds(
    lower_arg: &CompactBounds,
    upper_arg: &CompactBounds,
    fresh: &mut FreshCompactVars,
) -> CompactBounds {
    match (lower_arg, upper_arg) {
        (
            CompactBounds::Interval {
                lower: lower_lower,
                upper: lower_upper,
                ..
            },
            CompactBounds::Interval {
                lower: upper_lower,
                upper: upper_upper,
                ..
            },
        ) => interval_from_types(
            merge_compact_types(true, lower_lower.clone(), upper_lower.clone()),
            merge_compact_types(false, lower_upper.clone(), upper_upper.clone()),
            fresh,
        ),
        _ if lower_arg == upper_arg => lower_arg.clone(),
        _ => lower_arg.clone(),
    }
}

fn interval_from_types(
    lower: CompactType,
    upper: CompactType,
    fresh: &mut FreshCompactVars,
) -> CompactBounds {
    let self_var = common_var_in_types(&lower, &upper).unwrap_or_else(|| fresh.fresh());
    CompactBounds::Interval {
        self_var,
        lower,
        upper,
    }
}

fn common_var_in_types(lower: &CompactType, upper: &CompactType) -> Option<TypeVar> {
    lower
        .vars
        .iter()
        .map(|var| var.var)
        .filter(|lower_var| {
            upper
                .vars
                .iter()
                .any(|upper_var| upper_var.var == *lower_var)
        })
        .min_by_key(|var| var.0)
}

fn single_con<'a>(
    ty: &'a CompactType,
    path: &[String],
    arity: usize,
) -> Option<&'a [CompactBounds]> {
    if ty.cons.len() == 1
        && ty.cons[0].path == path
        && ty.cons[0].args.len() == arity
        && ty.builtins.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        Some(&ty.cons[0].args)
    } else {
        None
    }
}

fn single_tuple(ty: &CompactType, arity: usize) -> Option<&[CompactType]> {
    if ty.tuples.len() == 1
        && ty.tuples[0].items.len() == arity
        && ty.cons.is_empty()
        && ty.builtins.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.rows.is_empty()
    {
        Some(&ty.tuples[0].items)
    } else {
        None
    }
}

fn single_fun(ty: &CompactType) -> Option<&CompactFun> {
    if ty.funs.len() == 1
        && ty.cons.is_empty()
        && ty.builtins.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        Some(&ty.funs[0])
    } else {
        None
    }
}

fn empty_interval(self_var: TypeVar) -> CompactBounds {
    CompactBounds::Interval {
        self_var,
        lower: CompactType::default(),
        upper: CompactType::default(),
    }
}

struct FreshCompactVars {
    next: u32,
}

impl FreshCompactVars {
    fn new(root: &CompactRoot) -> Self {
        Self {
            next: max_type_var_in_root(root).map_or(0, |var| var.0 + 1),
        }
    }

    fn fresh(&mut self) -> TypeVar {
        let var = TypeVar(self.next);
        self.next += 1;
        var
    }
}

fn max_type_var_in_root(root: &CompactRoot) -> Option<TypeVar> {
    let mut max = None;
    max_type_var_in_type(&root.root, &mut max);
    for rec in &root.rec_vars {
        update_max_type_var(rec.var, &mut max);
        max_type_var_in_bounds(&rec.bounds, &mut max);
    }
    max
}

fn max_type_var_in_bounds(bounds: &CompactBounds, max: &mut Option<TypeVar>) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            update_max_type_var(*self_var, max);
            max_type_var_in_type(lower, max);
            max_type_var_in_type(upper, max);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                max_type_var_in_bounds(arg, max);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            max_type_var_in_bounds(arg, max);
            max_type_var_in_bounds(arg_eff, max);
            max_type_var_in_bounds(ret_eff, max);
            max_type_var_in_bounds(ret, max);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                max_type_var_in_bounds(&field.value, max);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    max_type_var_in_bounds(payload, max);
                }
            }
        }
    }
}

fn max_type_var_in_type(ty: &CompactType, max: &mut Option<TypeVar>) {
    for var in &ty.vars {
        update_max_type_var(var.var, max);
    }
    for con in &ty.cons {
        for arg in &con.args {
            max_type_var_in_bounds(arg, max);
        }
    }
    for fun in &ty.funs {
        max_type_var_in_type(&fun.arg, max);
        max_type_var_in_type(&fun.arg_eff, max);
        max_type_var_in_type(&fun.ret_eff, max);
        max_type_var_in_type(&fun.ret, max);
    }
    for record in &ty.records {
        for field in &record.fields {
            max_type_var_in_type(&field.value, max);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            max_type_var_in_type(&field.value, max);
        }
        max_type_var_in_type(&spread.tail, max);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                max_type_var_in_type(payload, max);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            max_type_var_in_type(item, max);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            max_type_var_in_type(item, max);
        }
        max_type_var_in_type(&row.tail, max);
    }
}

fn update_max_type_var(var: TypeVar, max: &mut Option<TypeVar>) {
    if max.is_none_or(|current| var.0 > current.0) {
        *max = Some(var);
    }
}

fn live_subtracts(
    root: &CompactRoot,
    role_predicates: &[CompactRoleConstraint],
    candidates: &[(TypeVar, SubtractId)],
) -> FxHashSet<(TypeVar, SubtractId)> {
    let mut candidate_map = FxHashMap::<TypeVar, Vec<SubtractId>>::default();
    for (var, id) in candidates {
        candidate_map.entry(*var).or_default().push(*id);
    }
    let mut live = FxHashSet::default();
    collect_live_subtracts_in_type(&root.root, true, &candidate_map, &mut live);
    for rec in &root.rec_vars {
        collect_live_subtracts_in_bounds(&rec.bounds, true, &candidate_map, &mut live);
    }
    for role in role_predicates {
        collect_live_subtracts_in_role(role, &candidate_map, &mut live);
    }
    live
}

fn collect_live_subtracts_in_role(
    role: &CompactRoleConstraint,
    candidate_map: &FxHashMap<TypeVar, Vec<SubtractId>>,
    live: &mut FxHashSet<(TypeVar, SubtractId)>,
) {
    for input in &role.inputs {
        collect_live_subtracts_in_role_arg(input, candidate_map, live);
    }
    for associated in &role.associated {
        collect_live_subtracts_in_role_arg(&associated.value, candidate_map, live);
    }
}

fn collect_live_subtracts_in_role_arg(
    arg: &CompactRoleArg,
    candidate_map: &FxHashMap<TypeVar, Vec<SubtractId>>,
    live: &mut FxHashSet<(TypeVar, SubtractId)>,
) {
    collect_live_subtracts_in_type(&arg.lower, true, candidate_map, live);
    collect_live_subtracts_in_type(&arg.upper, false, candidate_map, live);
}

fn collect_live_subtracts_in_type(
    ty: &CompactType,
    covariant: bool,
    candidate_map: &FxHashMap<TypeVar, Vec<SubtractId>>,
    live: &mut FxHashSet<(TypeVar, SubtractId)>,
) {
    if covariant {
        for var in &ty.vars {
            let Some(ids) = candidate_map.get(&var.var) else {
                continue;
            };
            for id in ids {
                // 保護されていない共変出現が一つでも残っているなら、その id の
                // subtract fact は use-site でまだ意味を持つ（旧 non-subtract と同じ規則）。
                if !var.weight.contains(*id) {
                    live.insert((var.var, *id));
                }
            }
        }
    }

    for con in &ty.cons {
        for arg in &con.args {
            collect_live_subtracts_in_bounds(arg, covariant, candidate_map, live);
        }
    }
    for fun in &ty.funs {
        collect_live_subtracts_in_type(&fun.arg, !covariant, candidate_map, live);
        collect_live_subtracts_in_type(&fun.arg_eff, !covariant, candidate_map, live);
        collect_live_subtracts_in_type(&fun.ret_eff, covariant, candidate_map, live);
        collect_live_subtracts_in_type(&fun.ret, covariant, candidate_map, live);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_live_subtracts_in_type(&field.value, covariant, candidate_map, live);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_live_subtracts_in_type(&field.value, covariant, candidate_map, live);
        }
        collect_live_subtracts_in_type(&spread.tail, covariant, candidate_map, live);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_live_subtracts_in_type(payload, covariant, candidate_map, live);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            collect_live_subtracts_in_type(item, covariant, candidate_map, live);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_live_subtracts_in_type(item, covariant, candidate_map, live);
        }
        collect_live_subtracts_in_type(&row.tail, covariant, candidate_map, live);
    }
}

fn collect_live_subtracts_in_bounds(
    bounds: &CompactBounds,
    covariant: bool,
    candidate_map: &FxHashMap<TypeVar, Vec<SubtractId>>,
    live: &mut FxHashSet<(TypeVar, SubtractId)>,
) {
    if !covariant {
        return;
    }
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            collect_live_subtracts_in_type(lower, true, candidate_map, live);
            collect_live_subtracts_in_type(upper, true, candidate_map, live);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                collect_live_subtracts_in_bounds(arg, covariant, candidate_map, live);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_live_subtracts_in_bounds(arg, !covariant, candidate_map, live);
            collect_live_subtracts_in_bounds(arg_eff, !covariant, candidate_map, live);
            collect_live_subtracts_in_bounds(ret_eff, covariant, candidate_map, live);
            collect_live_subtracts_in_bounds(ret, covariant, candidate_map, live);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                collect_live_subtracts_in_bounds(&field.value, covariant, candidate_map, live);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_live_subtracts_in_bounds(payload, covariant, candidate_map, live);
                }
            }
        }
    }
}

fn prune_dead_subtract_weights_in_root_and_roles(
    root: &mut CompactRoot,
    role_predicates: &mut [CompactRoleConstraint],
    dead_ids: &FxHashSet<SubtractId>,
) -> bool {
    let mut changed = prune_dead_subtract_weights_in_type(&mut root.root, dead_ids);
    for rec in &mut root.rec_vars {
        changed |= prune_dead_subtract_weights_in_bounds(&mut rec.bounds, dead_ids);
    }
    for role in role_predicates {
        changed |= prune_dead_subtract_weights_in_role(role, dead_ids);
    }
    changed
}

fn prune_dead_subtract_weights_in_role(
    role: &mut CompactRoleConstraint,
    dead_ids: &FxHashSet<SubtractId>,
) -> bool {
    let mut changed = false;
    for input in &mut role.inputs {
        changed |= prune_dead_subtract_weights_in_role_arg(input, dead_ids);
    }
    for associated in &mut role.associated {
        changed |= prune_dead_subtract_weights_in_role_arg(&mut associated.value, dead_ids);
    }
    changed
}

fn prune_dead_subtract_weights_in_role_arg(
    arg: &mut CompactRoleArg,
    dead_ids: &FxHashSet<SubtractId>,
) -> bool {
    prune_dead_subtract_weights_in_type(&mut arg.lower, dead_ids)
        | prune_dead_subtract_weights_in_type(&mut arg.upper, dead_ids)
}

fn prune_dead_subtract_weights_in_type(
    ty: &mut CompactType,
    dead_ids: &FxHashSet<SubtractId>,
) -> bool {
    let mut changed = false;
    for var in &mut ty.vars {
        let before = var.weight.clone();
        var.weight = var.weight.without_ids(|id| dead_ids.contains(&id));
        changed |= var.weight != before;
    }
    for con in &mut ty.cons {
        for arg in &mut con.args {
            changed |= prune_dead_subtract_weights_in_bounds(arg, dead_ids);
        }
    }
    for fun in &mut ty.funs {
        changed |= prune_dead_subtract_weights_in_type(&mut fun.arg, dead_ids);
        changed |= prune_dead_subtract_weights_in_type(&mut fun.arg_eff, dead_ids);
        changed |= prune_dead_subtract_weights_in_type(&mut fun.ret_eff, dead_ids);
        changed |= prune_dead_subtract_weights_in_type(&mut fun.ret, dead_ids);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            changed |= prune_dead_subtract_weights_in_type(&mut field.value, dead_ids);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            changed |= prune_dead_subtract_weights_in_type(&mut field.value, dead_ids);
        }
        changed |= prune_dead_subtract_weights_in_type(&mut spread.tail, dead_ids);
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                changed |= prune_dead_subtract_weights_in_type(payload, dead_ids);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            changed |= prune_dead_subtract_weights_in_type(item, dead_ids);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            changed |= prune_dead_subtract_weights_in_type(item, dead_ids);
        }
        changed |= prune_dead_subtract_weights_in_type(&mut row.tail, dead_ids);
    }
    changed
}

fn prune_dead_subtract_weights_in_bounds(
    bounds: &mut CompactBounds,
    dead_ids: &FxHashSet<SubtractId>,
) -> bool {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            prune_dead_subtract_weights_in_type(lower, dead_ids)
                | prune_dead_subtract_weights_in_type(upper, dead_ids)
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            let mut changed = false;
            for arg in args {
                changed |= prune_dead_subtract_weights_in_bounds(arg, dead_ids);
            }
            changed
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            prune_dead_subtract_weights_in_bounds(arg, dead_ids)
                | prune_dead_subtract_weights_in_bounds(arg_eff, dead_ids)
                | prune_dead_subtract_weights_in_bounds(ret_eff, dead_ids)
                | prune_dead_subtract_weights_in_bounds(ret, dead_ids)
        }
        CompactBounds::Record { fields } => {
            let mut changed = false;
            for field in fields {
                changed |= prune_dead_subtract_weights_in_bounds(&mut field.value, dead_ids);
            }
            changed
        }
        CompactBounds::PolyVariant { items } => {
            let mut changed = false;
            for (_, payloads) in items {
                for payload in payloads {
                    changed |= prune_dead_subtract_weights_in_bounds(payload, dead_ids);
                }
            }
            changed
        }
    }
}

fn cleanup_stack_weights_in_root_and_roles(
    root: &mut CompactRoot,
    role_predicates: &mut [CompactRoleConstraint],
) -> bool {
    let live_ids = live_covariant_stack_ids_in_root_and_roles(root, role_predicates);
    let all_ids = all_stack_ids_in_root_and_roles(root, role_predicates);
    let dead_ids = all_ids
        .difference(&live_ids)
        .copied()
        .collect::<FxHashSet<_>>();
    if dead_ids.is_empty() {
        return false;
    }
    prune_dead_subtract_weights_in_root_and_roles(root, role_predicates, &dead_ids)
}

fn cleanup_empty_stack_entries_with_plain_negative_occurrence(
    root: &mut CompactRoot,
    role_predicates: &mut [CompactRoleConstraint],
) -> bool {
    let mut occurrences = EmptyStackOccurrences::default();
    collect_empty_stack_occurrences_in_type(&root.root, true, &mut occurrences);
    for rec in &root.rec_vars {
        collect_empty_stack_occurrences_in_bounds(&rec.bounds, true, &mut occurrences);
    }
    for role in role_predicates.iter() {
        collect_empty_stack_occurrences_in_role(role, &mut occurrences);
    }

    let redundant = occurrences.redundant_positive_entries();
    if redundant.is_empty() {
        return false;
    }

    let mut changed = prune_redundant_empty_stack_entries_in_type(&mut root.root, true, &redundant);
    for rec in &mut root.rec_vars {
        changed |= prune_redundant_empty_stack_entries_in_bounds(&mut rec.bounds, true, &redundant);
    }
    for role in role_predicates {
        changed |= prune_redundant_empty_stack_entries_in_role(role, &redundant);
    }
    changed
}

#[derive(Default)]
struct EmptyStackOccurrences {
    positive_empty_entries: FxHashMap<TypeVar, FxHashSet<SubtractId>>,
    plain_negative_vars: FxHashSet<TypeVar>,
}

impl EmptyStackOccurrences {
    fn record_type(&mut self, var: &CompactVar, covariant: bool) {
        if covariant {
            for entry in var.weight.entries() {
                if empty_stack_entry_only(entry) {
                    self.positive_empty_entries
                        .entry(var.var)
                        .or_default()
                        .insert(entry.id);
                }
            }
        } else if var.weight.is_empty() {
            self.plain_negative_vars.insert(var.var);
        }
    }

    fn record_interval_center(&mut self, var: TypeVar) {
        self.plain_negative_vars.insert(var);
    }

    fn redundant_positive_entries(self) -> FxHashMap<TypeVar, FxHashSet<SubtractId>> {
        self.positive_empty_entries
            .into_iter()
            .filter(|(var, _)| self.plain_negative_vars.contains(var))
            .collect()
    }
}

fn empty_stack_entry_only(entry: &poly::types::StackWeightEntry) -> bool {
    entry.pops == 0
        && entry.floor.is_empty()
        && !entry.stack.is_empty()
        && entry
            .stack
            .iter()
            .all(|item| matches!(item, Subtractability::Empty))
}

fn collect_empty_stack_occurrences_in_role(
    role: &CompactRoleConstraint,
    out: &mut EmptyStackOccurrences,
) {
    for input in &role.inputs {
        collect_empty_stack_occurrences_in_role_arg(input, out);
    }
    for associated in &role.associated {
        collect_empty_stack_occurrences_in_role_arg(&associated.value, out);
    }
}

fn collect_empty_stack_occurrences_in_role_arg(
    arg: &CompactRoleArg,
    out: &mut EmptyStackOccurrences,
) {
    collect_empty_stack_occurrences_in_type(&arg.lower, true, out);
    collect_empty_stack_occurrences_in_type(&arg.upper, false, out);
}

fn collect_empty_stack_occurrences_in_type(
    ty: &CompactType,
    covariant: bool,
    out: &mut EmptyStackOccurrences,
) {
    for var in &ty.vars {
        out.record_type(var, covariant);
    }
    for con in &ty.cons {
        for arg in &con.args {
            collect_empty_stack_occurrences_in_bounds(arg, covariant, out);
        }
    }
    for fun in &ty.funs {
        collect_empty_stack_occurrences_in_type(&fun.arg, !covariant, out);
        collect_empty_stack_occurrences_in_type(&fun.arg_eff, !covariant, out);
        collect_empty_stack_occurrences_in_type(&fun.ret_eff, covariant, out);
        collect_empty_stack_occurrences_in_type(&fun.ret, covariant, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_empty_stack_occurrences_in_type(&field.value, covariant, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_empty_stack_occurrences_in_type(&field.value, covariant, out);
        }
        collect_empty_stack_occurrences_in_type(&spread.tail, covariant, out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_empty_stack_occurrences_in_type(payload, covariant, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            collect_empty_stack_occurrences_in_type(item, covariant, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_empty_stack_occurrences_in_type(item, covariant, out);
        }
        collect_empty_stack_occurrences_in_type(&row.tail, covariant, out);
    }
}

fn collect_empty_stack_occurrences_in_bounds(
    bounds: &CompactBounds,
    covariant: bool,
    out: &mut EmptyStackOccurrences,
) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            out.record_interval_center(*self_var);
            collect_empty_stack_occurrences_in_type(lower, covariant, out);
            collect_empty_stack_occurrences_in_type(upper, !covariant, out);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                collect_empty_stack_occurrences_in_bounds(arg, covariant, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_empty_stack_occurrences_in_bounds(arg, !covariant, out);
            collect_empty_stack_occurrences_in_bounds(arg_eff, !covariant, out);
            collect_empty_stack_occurrences_in_bounds(ret_eff, covariant, out);
            collect_empty_stack_occurrences_in_bounds(ret, covariant, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                collect_empty_stack_occurrences_in_bounds(&field.value, covariant, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_empty_stack_occurrences_in_bounds(payload, covariant, out);
                }
            }
        }
    }
}

fn prune_redundant_empty_stack_entries_in_role(
    role: &mut CompactRoleConstraint,
    redundant: &FxHashMap<TypeVar, FxHashSet<SubtractId>>,
) -> bool {
    let mut changed = false;
    for input in &mut role.inputs {
        changed |= prune_redundant_empty_stack_entries_in_role_arg(input, redundant);
    }
    for associated in &mut role.associated {
        changed |=
            prune_redundant_empty_stack_entries_in_role_arg(&mut associated.value, redundant);
    }
    changed
}

fn prune_redundant_empty_stack_entries_in_role_arg(
    arg: &mut CompactRoleArg,
    redundant: &FxHashMap<TypeVar, FxHashSet<SubtractId>>,
) -> bool {
    prune_redundant_empty_stack_entries_in_type(&mut arg.lower, true, redundant)
        | prune_redundant_empty_stack_entries_in_type(&mut arg.upper, false, redundant)
}

fn prune_redundant_empty_stack_entries_in_type(
    ty: &mut CompactType,
    covariant: bool,
    redundant: &FxHashMap<TypeVar, FxHashSet<SubtractId>>,
) -> bool {
    let mut changed = false;
    if covariant {
        for var in &mut ty.vars {
            let Some(ids) = redundant.get(&var.var) else {
                continue;
            };
            let before = var.weight.clone();
            var.weight = var.weight.without_ids(|id| ids.contains(&id));
            changed |= var.weight != before;
        }
    }
    for con in &mut ty.cons {
        for arg in &mut con.args {
            changed |= prune_redundant_empty_stack_entries_in_bounds(arg, covariant, redundant);
        }
    }
    for fun in &mut ty.funs {
        changed |= prune_redundant_empty_stack_entries_in_type(&mut fun.arg, !covariant, redundant);
        changed |=
            prune_redundant_empty_stack_entries_in_type(&mut fun.arg_eff, !covariant, redundant);
        changed |=
            prune_redundant_empty_stack_entries_in_type(&mut fun.ret_eff, covariant, redundant);
        changed |= prune_redundant_empty_stack_entries_in_type(&mut fun.ret, covariant, redundant);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            changed |=
                prune_redundant_empty_stack_entries_in_type(&mut field.value, covariant, redundant);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            changed |=
                prune_redundant_empty_stack_entries_in_type(&mut field.value, covariant, redundant);
        }
        changed |=
            prune_redundant_empty_stack_entries_in_type(&mut spread.tail, covariant, redundant);
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                changed |=
                    prune_redundant_empty_stack_entries_in_type(payload, covariant, redundant);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            changed |= prune_redundant_empty_stack_entries_in_type(item, covariant, redundant);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            changed |= prune_redundant_empty_stack_entries_in_type(item, covariant, redundant);
        }
        changed |= prune_redundant_empty_stack_entries_in_type(&mut row.tail, covariant, redundant);
    }
    changed
}

fn prune_redundant_empty_stack_entries_in_bounds(
    bounds: &mut CompactBounds,
    covariant: bool,
    redundant: &FxHashMap<TypeVar, FxHashSet<SubtractId>>,
) -> bool {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            prune_redundant_empty_stack_entries_in_type(lower, covariant, redundant)
                | prune_redundant_empty_stack_entries_in_type(upper, !covariant, redundant)
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            let mut changed = false;
            for arg in args {
                changed |= prune_redundant_empty_stack_entries_in_bounds(arg, covariant, redundant);
            }
            changed
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            prune_redundant_empty_stack_entries_in_bounds(arg, !covariant, redundant)
                | prune_redundant_empty_stack_entries_in_bounds(arg_eff, !covariant, redundant)
                | prune_redundant_empty_stack_entries_in_bounds(ret_eff, covariant, redundant)
                | prune_redundant_empty_stack_entries_in_bounds(ret, covariant, redundant)
        }
        CompactBounds::Record { fields } => {
            let mut changed = false;
            for field in fields {
                changed |= prune_redundant_empty_stack_entries_in_bounds(
                    &mut field.value,
                    covariant,
                    redundant,
                );
            }
            changed
        }
        CompactBounds::PolyVariant { items } => {
            let mut changed = false;
            for (_, payloads) in items {
                for payload in payloads {
                    changed |= prune_redundant_empty_stack_entries_in_bounds(
                        payload, covariant, redundant,
                    );
                }
            }
            changed
        }
    }
}

fn live_covariant_stack_ids_in_root_and_roles(
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
            collect_live_stack_ids_in_type(&input.lower, true, None, &mut ids);
            collect_live_stack_ids_in_type(&input.upper, false, None, &mut ids);
        }
        for associated in &role.associated {
            collect_live_stack_ids_in_type(&associated.value.lower, true, None, &mut ids);
            collect_live_stack_ids_in_type(&associated.value.upper, false, None, &mut ids);
        }
    }
    ids
}

fn sorted_stack_quantifiers(
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
            collect_live_stack_ids_in_type(&input.lower, true, Some(quantifier_set), &mut ids);
            collect_live_stack_ids_in_type(&input.upper, false, Some(quantifier_set), &mut ids);
        }
        for associated in &role.associated {
            collect_live_stack_ids_in_type(
                &associated.value.lower,
                true,
                Some(quantifier_set),
                &mut ids,
            );
            collect_live_stack_ids_in_type(
                &associated.value.upper,
                false,
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

fn all_stack_ids_in_root_and_roles(
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
            collect_all_stack_ids_in_type(&input.lower, &mut ids);
            collect_all_stack_ids_in_type(&input.upper, &mut ids);
        }
        for associated in &role.associated {
            collect_all_stack_ids_in_type(&associated.value.lower, &mut ids);
            collect_all_stack_ids_in_type(&associated.value.upper, &mut ids);
        }
    }
    ids
}

fn collect_live_stack_ids_in_type(
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
    for con in &ty.cons {
        for arg in &con.args {
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
        for item in &row.items {
            collect_live_stack_ids_in_type(item, covariant, var_filter, out);
        }
        collect_live_stack_ids_in_type(&row.tail, covariant, var_filter, out);
    }
}

fn collect_live_stack_ids_in_bounds(
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

fn stack_entry_keeps_stack_id_live(entry: &poly::types::StackWeightEntry) -> bool {
    !entry.stack.is_empty()
        || entry
            .floor
            .iter()
            .any(|floor| !matches!(floor, Subtractability::Empty))
}

fn collect_all_stack_ids_in_type(ty: &CompactType, out: &mut FxHashSet<SubtractId>) {
    for var in &ty.vars {
        for id in var.weight.iter() {
            out.insert(id);
        }
    }
    for con in &ty.cons {
        for arg in &con.args {
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
        for item in &row.items {
            collect_all_stack_ids_in_type(item, out);
        }
        collect_all_stack_ids_in_type(&row.tail, out);
    }
}

fn collect_all_stack_ids_in_bounds(bounds: &CompactBounds, out: &mut FxHashSet<SubtractId>) {
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

fn collect_root_free_vars(root: &CompactRoot, out: &mut Vec<TypeVar>) {
    collect_type_free_vars(&root.root, out);
    for rec in &root.rec_vars {
        collect_recursive_var_free_vars(rec, out);
    }
}

fn collect_role_free_vars(role: &CompactRoleConstraint, out: &mut Vec<TypeVar>) {
    for input in &role.inputs {
        collect_role_arg_free_vars(input, out);
    }
    for associated in &role.associated {
        collect_role_arg_free_vars(&associated.value, out);
    }
}

fn collect_role_arg_free_vars(arg: &CompactRoleArg, out: &mut Vec<TypeVar>) {
    collect_type_free_vars(&arg.lower, out);
    collect_type_free_vars(&arg.upper, out);
}

fn collect_recursive_var_free_vars(rec: &CompactRecursiveVar, out: &mut Vec<TypeVar>) {
    out.push(rec.var);
    collect_bounds_free_vars(&rec.bounds, out);
}

fn collect_bounds_free_vars(bounds: &CompactBounds, out: &mut Vec<TypeVar>) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            out.push(*self_var);
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

fn collect_type_free_vars(ty: &CompactType, out: &mut Vec<TypeVar>) {
    out.extend(ty.vars.iter().map(|var| var.var));
    for con in &ty.cons {
        collect_con_free_vars(con, out);
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

fn collect_con_free_vars(con: &CompactCon, out: &mut Vec<TypeVar>) {
    for arg in &con.args {
        collect_bounds_free_vars(arg, out);
    }
}

fn collect_fun_free_vars(fun: &CompactFun, out: &mut Vec<TypeVar>) {
    collect_type_free_vars(&fun.arg, out);
    collect_type_free_vars(&fun.arg_eff, out);
    collect_type_free_vars(&fun.ret_eff, out);
    collect_type_free_vars(&fun.ret, out);
}

fn collect_record_free_vars(record: &CompactRecord, out: &mut Vec<TypeVar>) {
    for field in &record.fields {
        collect_type_free_vars(&field.value, out);
    }
}

fn collect_record_spread_free_vars(spread: &CompactRecordSpread, out: &mut Vec<TypeVar>) {
    for field in &spread.fields {
        collect_type_free_vars(&field.value, out);
    }
    collect_type_free_vars(&spread.tail, out);
}

fn collect_poly_variant_free_vars(variant: &CompactPolyVariant, out: &mut Vec<TypeVar>) {
    for (_, payloads) in &variant.items {
        for payload in payloads {
            collect_type_free_vars(payload, out);
        }
    }
}

fn collect_tuple_free_vars(tuple: &CompactTuple, out: &mut Vec<TypeVar>) {
    for item in &tuple.items {
        collect_type_free_vars(item, out);
    }
}

fn collect_row_free_vars(row: &CompactRow, out: &mut Vec<TypeVar>) {
    for item in &row.items {
        collect_type_free_vars(item, out);
    }
    collect_type_free_vars(&row.tail, out);
}

#[cfg(test)]
mod tests {
    use poly::types::{Pos, SubtractId, Subtractability};

    use super::*;
    use crate::compact::CompactSandwichKind;
    use crate::compact::simplify_compact_root;
    use crate::compact::{CompactFun, CompactVar, merge_compact_types};

    fn bipolar_effect_fun(effect: TypeVar, ret_eff: CompactType) -> CompactType {
        CompactType::from_fun(CompactFun {
            arg: CompactType::default(),
            arg_eff: CompactType::from_var(CompactVar::plain(effect)),
            ret_eff,
            ret: CompactType::default(),
        })
    }

    fn live_subtract_effect_fun(effect: TypeVar, ret_eff: CompactType) -> CompactType {
        CompactType::from_fun(CompactFun {
            arg: CompactType::default(),
            arg_eff: CompactType::from_var(CompactVar::plain(effect)),
            ret_eff,
            ret: CompactType::from_var(CompactVar::plain(effect)),
        })
    }

    fn neg_contains_var(types: &TypeArena, id: NegId, var: TypeVar) -> bool {
        match types.neg(id) {
            poly::types::Neg::Var(found) => *found == var,
            poly::types::Neg::Intersection(left, right) => {
                neg_contains_var(types, *left, var) || neg_contains_var(types, *right, var)
            }
            _ => false,
        }
    }

    #[test]
    fn quantifies_only_vars_above_boundary() {
        let mut machine = ConstraintMachine::new();
        let outer = TypeVar(1);
        let inner = TypeVar(2);
        machine.register_type_var(outer, TypeLevel::root());
        machine.register_type_var(inner, TypeLevel::root().child());
        let root = CompactRoot {
            root: CompactType {
                vars: vec![CompactVar::plain(outer), CompactVar::plain(inner)],
                ..CompactType::default()
            },
            rec_vars: Vec::new(),
        };

        let quantifiers =
            quantified_vars(&machine, TypeLevel::root(), &root, &FxHashSet::default());

        assert_eq!(quantifiers, vec![inner]);
    }

    #[test]
    fn non_generic_vars_are_not_quantified() {
        let mut machine = ConstraintMachine::new();
        let inner = TypeVar(2);
        machine.register_type_var(inner, TypeLevel::root().child());
        let root = CompactRoot {
            root: CompactType::from_var(CompactVar::plain(inner)),
            rec_vars: Vec::new(),
        };
        let non_generic = FxHashSet::from_iter([inner]);

        let quantifiers = quantified_vars(&machine, TypeLevel::root(), &root, &non_generic);

        assert!(quantifiers.is_empty());
    }

    #[test]
    fn interval_center_vars_are_quantified_when_free() {
        let mut machine = ConstraintMachine::new();
        let center = TypeVar(4);
        machine.register_type_var(center, TypeLevel::root().child());
        let root = CompactRoot {
            root: CompactType::from_con(CompactCon {
                path: vec!["list".into()],
                args: vec![CompactBounds::Interval {
                    self_var: center,
                    lower: CompactType::default(),
                    upper: CompactType::default(),
                }],
            }),
            rec_vars: Vec::new(),
        };

        let quantifiers =
            quantified_vars(&machine, TypeLevel::root(), &root, &FxHashSet::default());

        assert_eq!(quantifiers, vec![center]);
    }

    #[test]
    fn generalized_scheme_omits_subtract_fact_without_live_stack_entry() {
        let mut machine = ConstraintMachine::new();
        let effect = TypeVar(2);
        machine.register_type_var(effect, TypeLevel::root().child());
        machine.subtract_fact(effect, SubtractId(3), Subtractability::Empty);
        let root = CompactRoot {
            root: CompactType::from_var(CompactVar::plain(effect)),
            rec_vars: Vec::new(),
        };

        let generalized =
            generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());

        assert!(generalized.quantifiers.is_empty());
        assert!(generalized.subtracts.is_empty());
        assert!(generalized.compact.root.is_empty());
    }

    #[test]
    fn finalized_scheme_keeps_live_stack_subtractability_in_poly_scheme() {
        let mut machine = ConstraintMachine::new();
        let effect = TypeVar(2);
        let subtract = SubtractId(3);
        machine.register_type_var(effect, TypeLevel::root().child());
        machine.declared_subtract_fact(
            effect,
            subtract,
            Subtractability::Set(vec!["io".into()], Vec::new()),
        );
        let root = CompactRoot {
            root: live_subtract_effect_fun(
                effect,
                CompactType::from_var(CompactVar::covariant(
                    effect,
                    StackWeight::push(
                        subtract,
                        Subtractability::Set(vec!["io".into()], Vec::new()),
                    ),
                )),
            ),
            rec_vars: Vec::new(),
        };
        let generalized =
            generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());
        let mut types = TypeArena::new();

        let finalized = finalize_generalized_compact_root(&mut types, &machine, &generalized);

        assert_eq!(finalized.scheme.subtracts.len(), 1);
        let fact = &finalized.scheme.subtracts[0];
        assert_eq!(fact.var, effect);
        assert_eq!(fact.id, subtract);
        assert!(matches!(
            &fact.subtractability,
            Subtractability::Set(path, args)
                if path == &vec!["io".to_string()] && args.is_empty()
        ));
    }

    #[test]
    fn subtract_is_pruned_when_every_covariant_position_is_non_subtract() {
        let mut machine = ConstraintMachine::new();
        let effect = TypeVar(2);
        let subtract = SubtractId(3);
        machine.register_type_var(effect, TypeLevel::root().child());
        machine.subtract_fact(effect, subtract, Subtractability::Empty);
        let root = CompactRoot {
            root: bipolar_effect_fun(
                effect,
                CompactType::from_var(CompactVar::covariant(
                    effect,
                    ConstraintWeight::from_ids([subtract]),
                )),
            ),
            rec_vars: Vec::new(),
        };

        let generalized =
            generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());

        assert_eq!(generalized.quantifiers, vec![effect]);
        assert!(generalized.subtracts.is_empty());
        let ret_eff = &generalized.compact.root.funs[0].ret_eff;
        assert!(!ret_eff.vars[0].weight.contains(subtract));
    }

    #[test]
    fn coalesced_covariant_position_prunes_subtract_after_weight_merge() {
        let mut machine = ConstraintMachine::new();
        let effect = TypeVar(2);
        let value = TypeVar(4);
        let subtract = SubtractId(3);
        machine.register_type_var(effect, TypeLevel::root().child());
        machine.register_type_var(value, TypeLevel::root().child());
        machine.subtract_fact(effect, subtract, Subtractability::Empty);
        let root = CompactRoot {
            root: CompactType {
                vars: vec![
                    CompactVar::covariant(effect, ConstraintWeight::from_ids([subtract])),
                    CompactVar::plain(value),
                ],
                ..CompactType::default()
            },
            rec_vars: Vec::new(),
        };

        let generalized =
            generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());

        assert!(generalized.subtracts.is_empty());
        assert!(
            generalized
                .compact
                .root
                .vars
                .iter()
                .all(|var| !var.weight.contains(subtract))
        );
    }

    #[test]
    fn substitution_maps_live_subtract_variable_to_representative() {
        let mut machine = ConstraintMachine::new();
        let effect = TypeVar(2);
        let replacement = TypeVar(4);
        let subtract = SubtractId(3);
        machine.register_type_var(effect, TypeLevel::root().child());
        machine.register_type_var(replacement, TypeLevel::root().child());
        machine.declared_subtract_fact(
            effect,
            subtract,
            Subtractability::Set(vec!["io".into()], Vec::new()),
        );
        let root = CompactRoot {
            root: live_subtract_effect_fun(
                replacement,
                CompactType::from_var(CompactVar::covariant(
                    replacement,
                    StackWeight::push(
                        subtract,
                        Subtractability::Set(vec!["io".into()], Vec::new()),
                    ),
                )),
            ),
            rec_vars: Vec::new(),
        };

        let generalized = generalize_compact_root_with_simplification(
            &machine,
            TypeLevel::root(),
            root,
            Vec::new(),
            &FxHashSet::default(),
            CompactSimplification {
                substitutions: vec![CompactVarSubstitution {
                    source: effect,
                    target: Some(replacement),
                }],
                sandwiches: Vec::new(),
            },
        );

        assert_eq!(generalized.quantifiers, vec![replacement]);
        assert_eq!(generalized.subtracts, vec![(replacement, subtract)]);
    }

    #[test]
    fn cleanup_removes_pop_only_weights_without_live_stack_entries() {
        let mut machine = ConstraintMachine::new();
        let effect = TypeVar(2);
        let subtract = SubtractId(3);
        let unrelated = SubtractId(9);
        machine.register_type_var(effect, TypeLevel::root().child());
        machine.subtract_fact(effect, subtract, Subtractability::Empty);
        let root = CompactRoot {
            root: bipolar_effect_fun(
                effect,
                CompactType::from_var(CompactVar::covariant(
                    effect,
                    ConstraintWeight::from_ids([subtract, unrelated]),
                )),
            ),
            rec_vars: Vec::new(),
        };

        let generalized =
            generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());

        let weight = &generalized.compact.root.funs[0].ret_eff.vars[0].weight;
        assert!(generalized.subtracts.is_empty());
        assert!(!weight.contains(subtract));
        assert!(!weight.contains(unrelated));
    }

    #[test]
    fn cleanup_removes_empty_floor_weights_without_live_stack_entries() {
        let mut machine = ConstraintMachine::new();
        let effect = TypeVar(2);
        let subtract = SubtractId(3);
        machine.register_type_var(effect, TypeLevel::root().child());
        let root = CompactRoot {
            root: bipolar_effect_fun(
                effect,
                CompactType::from_var(CompactVar::covariant(
                    effect,
                    StackWeight::floor(subtract, Subtractability::Empty)
                        .compose(&StackWeight::pops(subtract, 2)),
                )),
            ),
            rec_vars: Vec::new(),
        };

        let generalized =
            generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());

        let weight = &generalized.compact.root.funs[0].ret_eff.vars[0].weight;
        assert!(generalized.stack_quantifiers.is_empty());
        assert!(!weight.contains(subtract));
    }

    #[test]
    fn empty_stack_entry_with_plain_negative_var_is_internal() {
        let mut machine = ConstraintMachine::new();
        let effect = TypeVar(2);
        let subtract = SubtractId(3);
        machine.register_type_var(effect, TypeLevel::root().child());
        let root = CompactRoot {
            root: bipolar_effect_fun(
                effect,
                CompactType::from_var(CompactVar::covariant(
                    effect,
                    StackWeight::push(subtract, Subtractability::Empty),
                )),
            ),
            rec_vars: Vec::new(),
        };

        let generalized =
            generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());
        let mut types = TypeArena::new();
        let finalized = finalize_generalized_compact_root(&mut types, &machine, &generalized);

        assert!(generalized.stack_quantifiers.is_empty());
        assert!(generalized.subtracts.is_empty());
        assert!(
            !generalized.compact.root.funs[0].ret_eff.vars[0]
                .weight
                .contains(subtract)
        );
        assert!(finalized.scheme.stack_quantifiers.is_empty());
        assert!(finalized.scheme.subtracts.is_empty());
    }

    #[test]
    fn low_level_stack_entry_is_not_stack_quantified() {
        let mut machine = ConstraintMachine::new();
        let effect = TypeVar(2);
        let subtract = SubtractId(3);
        machine.register_type_var(effect, TypeLevel::root());
        let root = CompactRoot {
            root: bipolar_effect_fun(
                effect,
                CompactType::from_var(CompactVar::covariant(
                    effect,
                    StackWeight::push(subtract, Subtractability::Empty),
                )),
            ),
            rec_vars: Vec::new(),
        };

        let generalized =
            generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());

        assert!(generalized.quantifiers.is_empty());
        assert!(generalized.stack_quantifiers.is_empty());
        assert!(
            generalized.compact.root.funs[0].ret_eff.vars[0]
                .weight
                .is_empty()
        );
    }

    #[test]
    fn contravariant_unweighted_position_does_not_keep_subtract() {
        let mut machine = ConstraintMachine::new();
        let effect = TypeVar(2);
        let arg = TypeVar(4);
        let subtract = SubtractId(3);
        machine.register_type_var(effect, TypeLevel::root().child());
        machine.register_type_var(arg, TypeLevel::root().child());
        machine.subtract_fact(effect, subtract, Subtractability::Empty);
        let root = CompactRoot {
            root: CompactType::from_fun(CompactFun {
                arg: CompactType::from_var(CompactVar::plain(arg)),
                arg_eff: CompactType::default(),
                ret_eff: CompactType::from_var(CompactVar::covariant(
                    effect,
                    ConstraintWeight::from_ids([subtract]),
                )),
                ret: CompactType::default(),
            }),
            rec_vars: Vec::new(),
        };

        let generalized =
            generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());

        assert!(generalized.subtracts.is_empty());
        assert!(
            generalized.compact.root.funs[0]
                .ret_eff
                .vars
                .iter()
                .all(|var| !var.weight.contains(subtract))
        );
    }

    #[test]
    fn generalize_compact_root_after_simplification_keeps_low_level_vars() {
        let mut machine = ConstraintMachine::new();
        let outer = TypeVar(1);
        let inner = TypeVar(2);
        machine.register_type_var(outer, TypeLevel::root());
        machine.register_type_var(inner, TypeLevel::root().child());
        let mut root = CompactRoot {
            root: CompactType {
                vars: vec![CompactVar::plain(outer), CompactVar::plain(inner)],
                ..CompactType::default()
            },
            rec_vars: Vec::new(),
        };
        simplify_compact_root(&machine, TypeLevel::root().child(), &mut root);

        let generalized =
            generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());

        assert!(generalized.quantifiers.is_empty());
        assert!(compact_type_contains_var(&generalized.compact.root, outer));
        assert!(!compact_type_contains_var(&generalized.compact.root, inner));
    }

    #[test]
    fn generalize_type_var_runs_collect_simplify_finalize_pipeline() {
        let mut machine = ConstraintMachine::new();
        let root = TypeVar(1);
        machine.register_type_var(root, TypeLevel::root());

        let generalized =
            generalize_type_var(&machine, root, TypeLevel::root(), &FxHashSet::default());

        assert!(generalized.quantifiers.is_empty());
        assert!(compact_type_contains_var(&generalized.compact.root, root));
    }

    #[test]
    fn generalize_preserves_recursive_side_table() {
        let mut machine = ConstraintMachine::new();
        let rec = TypeVar(1);
        machine.register_type_var(rec, TypeLevel::root().child());
        let root = CompactRoot {
            root: CompactType::from_var(CompactVar::plain(rec)),
            rec_vars: vec![CompactRecursiveVar {
                var: rec,
                bounds: CompactBounds::Interval {
                    self_var: rec,
                    lower: merge_compact_types(
                        true,
                        CompactType::from_var(CompactVar::plain(rec)),
                        CompactType::from_con(CompactCon {
                            path: vec!["list".into()],
                            args: Vec::new(),
                        }),
                    ),
                    upper: CompactType::default(),
                },
            }],
        };

        let generalized =
            generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());

        assert_eq!(generalized.quantifiers, vec![rec]);
        assert_eq!(generalized.compact.rec_vars.len(), 1);
    }

    #[test]
    fn finalized_generalized_naked_root_variable_becomes_never() {
        let mut machine = ConstraintMachine::new();
        let var = TypeVar(1);
        machine.register_type_var(var, TypeLevel::root().child());
        let root = CompactRoot {
            root: CompactType::from_var(CompactVar::plain(var)),
            rec_vars: Vec::new(),
        };
        let generalized =
            generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());
        let mut types = TypeArena::new();

        let finalized = finalize_generalized_compact_root(&mut types, &machine, &generalized);

        assert!(finalized.scheme.quantifiers.is_empty());
        assert!(matches!(types.pos(finalized.scheme.predicate), Pos::Bot));
        assert!(generalized.compact.root.is_empty());
    }

    #[test]
    fn finalized_generalized_root_moves_recursive_bounds_into_scheme() {
        let mut machine = ConstraintMachine::new();
        let var = TypeVar(1);
        machine.register_type_var(var, TypeLevel::root().child());
        let root = CompactRoot {
            root: CompactType::from_var(CompactVar::plain(var)),
            rec_vars: vec![CompactRecursiveVar {
                var,
                bounds: CompactBounds::Interval {
                    self_var: var,
                    lower: CompactType::from_builtin(poly::types::BuiltinType::Int),
                    upper: CompactType::default(),
                },
            }],
        };
        let generalized =
            generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());
        let mut types = TypeArena::new();

        let finalized = finalize_generalized_compact_root(&mut types, &machine, &generalized);

        assert_eq!(finalized.scheme.recursive_bounds.len(), 1);
        assert_eq!(finalized.scheme.recursive_bounds[0].var, var);
        assert!(matches!(
            types.neu(finalized.scheme.recursive_bounds[0].bounds),
            poly::types::Neu::Bounds(lower, self_var, _)
                if *self_var == var
                    && matches!(
                        types.pos(*lower),
                        poly::types::Pos::Con(path, args)
                            if path.len() == 1 && path[0] == "int" && args.is_empty()
                    )
        ));
    }

    #[test]
    fn finalizing_keeps_role_predicates_and_quantifies_their_vars() {
        let mut machine = ConstraintMachine::new();
        let role_var = TypeVar(2);
        machine.register_type_var(role_var, TypeLevel::root().child());
        let root = CompactRoot {
            root: CompactType::default(),
            rec_vars: Vec::new(),
        };
        let roles = vec![CompactRoleConstraint {
            role: vec!["Ready".into()],
            inputs: vec![CompactRoleArg {
                lower: CompactType::from_var(CompactVar::plain(role_var)),
                upper: CompactType::from_var(CompactVar::plain(role_var)),
            }],
            associated: Vec::new(),
        }];

        let generalized = generalize_prepared_compact_root_with_roles(
            &machine,
            TypeLevel::root(),
            root,
            roles,
            &FxHashSet::default(),
        );
        let mut types = TypeArena::new();
        let finalized = finalize_generalized_compact_root(&mut types, &machine, &generalized);

        assert_eq!(finalized.scheme.quantifiers, vec![role_var]);
        assert_eq!(finalized.scheme.role_predicates.len(), 1);
        assert_eq!(
            finalized.scheme.role_predicates[0].role,
            vec!["Ready".to_string()]
        );
        assert!(matches!(
            types.neu(finalized.scheme.role_predicates[0].inputs[0]),
            poly::types::Neu::Bounds(lower, var, upper)
                if *var == role_var
                    && matches!(types.pos(*lower), poly::types::Pos::Var(v) if *v == role_var)
                    && matches!(types.neg(*upper), poly::types::Neg::Var(v) if *v == role_var)
        ));
    }

    #[test]
    fn finalizing_role_arg_uses_unique_var_from_structured_bound() {
        let mut machine = ConstraintMachine::new();
        let role_var = TypeVar(2);
        machine.register_type_var(role_var, TypeLevel::root().child());
        let generalized = GeneralizedCompactRoot {
            compact: CompactRoot {
                root: CompactType::default(),
                rec_vars: Vec::new(),
            },
            role_predicates: vec![CompactRoleConstraint {
                role: vec!["Ready".into()],
                inputs: vec![CompactRoleArg {
                    lower: CompactType::from_builtin(poly::types::BuiltinType::Int),
                    upper: merge_compact_types(
                        true,
                        CompactType::from_var(CompactVar::plain(role_var)),
                        CompactType::from_builtin(poly::types::BuiltinType::Int),
                    ),
                }],
                associated: Vec::new(),
            }],
            quantifiers: vec![role_var],
            stack_quantifiers: Vec::new(),
            subtracts: Vec::new(),
            substitutions: Vec::new(),
            sandwiches: Vec::new(),
        };
        let mut types = TypeArena::new();
        let finalized = finalize_generalized_compact_root(&mut types, &machine, &generalized);

        assert_eq!(finalized.scheme.role_predicates.len(), 1);
        let actual = types.neu(finalized.scheme.role_predicates[0].inputs[0]);
        assert!(
            matches!(
                actual,
                poly::types::Neu::Bounds(lower, var, upper)
                    if *var == role_var
                        && matches!(
                            types.pos(*lower),
                            poly::types::Pos::Con(path, args)
                                if path.len() == 1 && path[0] == "int" && args.is_empty()
                        )
                        && neg_contains_var(&types, *upper, role_var)
            ),
            "{actual:?}"
        );
    }

    #[test]
    fn generalized_compact_root_keeps_simplification_substitutions() {
        let mut machine = ConstraintMachine::new();
        let var = TypeVar(1);
        let replacement = TypeVar(2);
        let substitutions = vec![CompactVarSubstitution {
            source: var,
            target: Some(replacement),
        }];
        let sandwiches = vec![CompactSandwich {
            var,
            kind: CompactSandwichKind::Con {
                path: vec!["list".into()],
                arity: 1,
            },
        }];
        machine.register_type_var(replacement, TypeLevel::root().child());
        let root = CompactRoot {
            root: CompactType::default(),
            rec_vars: Vec::new(),
        };

        let generalized = generalize_compact_root_with_simplification(
            &machine,
            TypeLevel::root(),
            root,
            Vec::new(),
            &FxHashSet::default(),
            CompactSimplification {
                substitutions: substitutions.clone(),
                sandwiches: sandwiches.clone(),
            },
        );

        assert_eq!(generalized.substitutions, vec![substitutions[0].clone()]);
        assert_eq!(generalized.sandwiches, sandwiches);
    }

    #[test]
    fn pre_simplifications_run_before_quantifier_selection() {
        let mut machine = ConstraintMachine::new();
        let removed = TypeVar(1);
        machine.register_type_var(removed, TypeLevel::root().child());
        let root = CompactRoot {
            root: CompactType::from_var(CompactVar::plain(removed)),
            rec_vars: Vec::new(),
        };

        let generalized = generalize_prepared_compact_root_with_roles_and_simplifications(
            &machine,
            TypeLevel::root(),
            root,
            Vec::new(),
            &[CompactSimplification {
                substitutions: vec![CompactVarSubstitution {
                    source: removed,
                    target: None,
                }],
                sandwiches: Vec::new(),
            }],
            &FxHashSet::default(),
        );

        assert!(generalized.quantifiers.is_empty());
        assert!(generalized.compact.root.is_empty());
    }

    #[test]
    fn finalizing_with_ancestor_substitution_prunes_child_quantifier() {
        let child_var = TypeVar(1);
        let ancestor = GeneralizedCompactRoot {
            compact: CompactRoot::default(),
            role_predicates: Vec::new(),
            quantifiers: Vec::new(),
            stack_quantifiers: Vec::new(),
            subtracts: Vec::new(),
            substitutions: vec![CompactVarSubstitution {
                source: child_var,
                target: None,
            }],
            sandwiches: Vec::new(),
        };
        let child = GeneralizedCompactRoot {
            compact: CompactRoot {
                root: CompactType::from_var(CompactVar::plain(child_var)),
                rec_vars: Vec::new(),
            },
            role_predicates: Vec::new(),
            quantifiers: vec![child_var],
            stack_quantifiers: Vec::new(),
            subtracts: Vec::new(),
            substitutions: Vec::new(),
            sandwiches: Vec::new(),
        };
        let mut types = TypeArena::new();

        let machine = ConstraintMachine::new();
        let finalized = finalize_generalized_compact_root_with_ancestors(
            &mut types,
            &machine,
            &child,
            &[&ancestor],
        );

        assert!(finalized.scheme.quantifiers.is_empty());
        assert!(matches!(
            types.pos(finalized.scheme.predicate),
            poly::types::Pos::Bot
        ));
    }

    fn compact_type_contains_var(ty: &CompactType, expected: TypeVar) -> bool {
        ty.vars.iter().any(|var| var.var == expected)
            || ty.cons.iter().any(|con| {
                con.args
                    .iter()
                    .any(|arg| compact_bounds_contains_var(arg, expected))
            })
            || ty.funs.iter().any(|fun| {
                compact_type_contains_var(&fun.arg, expected)
                    || compact_type_contains_var(&fun.arg_eff, expected)
                    || compact_type_contains_var(&fun.ret_eff, expected)
                    || compact_type_contains_var(&fun.ret, expected)
            })
            || ty.records.iter().any(|record| {
                record
                    .fields
                    .iter()
                    .any(|field| compact_type_contains_var(&field.value, expected))
            })
            || ty.record_spreads.iter().any(|spread| {
                spread
                    .fields
                    .iter()
                    .any(|field| compact_type_contains_var(&field.value, expected))
                    || compact_type_contains_var(&spread.tail, expected)
            })
            || ty.poly_variants.iter().any(|variant| {
                variant
                    .items
                    .iter()
                    .flat_map(|(_, payloads)| payloads)
                    .any(|payload| compact_type_contains_var(payload, expected))
            })
            || ty.tuples.iter().any(|tuple| {
                tuple
                    .items
                    .iter()
                    .any(|item| compact_type_contains_var(item, expected))
            })
            || ty.rows.iter().any(|row| {
                row.items
                    .iter()
                    .any(|item| compact_type_contains_var(item, expected))
                    || compact_type_contains_var(&row.tail, expected)
            })
    }

    fn compact_bounds_contains_var(bounds: &CompactBounds, expected: TypeVar) -> bool {
        match bounds {
            CompactBounds::Interval {
                self_var,
                lower,
                upper,
            } => {
                *self_var == expected
                    || compact_type_contains_var(lower, expected)
                    || compact_type_contains_var(upper, expected)
            }
            CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => args
                .iter()
                .any(|arg| compact_bounds_contains_var(arg, expected)),
            CompactBounds::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                compact_bounds_contains_var(arg, expected)
                    || compact_bounds_contains_var(arg_eff, expected)
                    || compact_bounds_contains_var(ret_eff, expected)
                    || compact_bounds_contains_var(ret, expected)
            }
            CompactBounds::Record { fields } => fields
                .iter()
                .any(|field| compact_bounds_contains_var(&field.value, expected)),
            CompactBounds::PolyVariant { items } => items
                .iter()
                .flat_map(|(_, payloads)| payloads)
                .any(|payload| compact_bounds_contains_var(payload, expected)),
        }
    }
}
