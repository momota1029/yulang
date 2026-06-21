use crate::constraints::ConstraintWeight;

use poly::types::{Neg, Neu, Pos, SubtractId, Subtractability};

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

    let quantifiers = quantified_vars(&machine, TypeLevel::root(), &root, &FxHashSet::default());

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
fn interval_common_vars_are_quantified_when_free() {
    let mut machine = ConstraintMachine::new();
    let center = TypeVar(4);
    machine.register_type_var(center, TypeLevel::root().child());
    let root = CompactRoot {
        root: CompactType::from_con(CompactCon {
            path: vec!["list".into()],
            args: vec![CompactBounds::Interval {
                lower: CompactType::from_var(CompactVar::plain(center)),
                upper: CompactType::from_var(CompactVar::plain(center)),
            }],
        }),
        rec_vars: Vec::new(),
    };

    let quantifiers = quantified_vars(&machine, TypeLevel::root(), &root, &FxHashSet::default());

    assert_eq!(quantifiers, vec![center]);
}

#[test]
fn generalized_scheme_omits_stack_quantifier_without_live_stack_entry() {
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
    assert!(generalized.stack_quantifiers.is_empty());
    assert!(generalized.compact.root.is_empty());
}

#[test]
fn finalized_scheme_keeps_live_stack_id_as_stack_quantifier() {
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

    assert_eq!(finalized.scheme.stack_quantifiers, vec![subtract]);
}

#[test]
fn finalized_scheme_clones_stack_weight_payloads_into_poly_arena() {
    let mut machine = ConstraintMachine::new();
    let effect = TypeVar(2);
    let payload_var = TypeVar(10);
    let subtract = SubtractId(3);
    let ref_update = vec!["ref_update".into()];
    machine.register_type_var(effect, TypeLevel::root().child());
    machine.register_type_var(payload_var, TypeLevel::root().child());
    let payload_lower = machine.alloc_pos(Pos::Var(payload_var));
    let payload_upper = machine.alloc_neg(Neg::Var(payload_var));
    let payload = machine.alloc_neu(Neu::Bounds(payload_lower, payload_upper));
    machine.declared_subtract_fact(
        effect,
        subtract,
        Subtractability::Set(ref_update.clone(), vec![payload]),
    );
    let root = CompactRoot {
        root: live_subtract_effect_fun(
            effect,
            CompactType::from_var(CompactVar::covariant(
                effect,
                StackWeight::push(subtract, Subtractability::Set(ref_update, vec![payload])),
            )),
        ),
        rec_vars: Vec::new(),
    };
    let generalized =
        generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());
    let mut types = TypeArena::new();

    let finalized = finalize_generalized_compact_root(&mut types, &machine, &generalized);
    let mut target = crate::arena::Arena::new();
    let _ = crate::instantiate::instantiate_scheme(
        &types,
        &mut target,
        TypeLevel::root(),
        &finalized.scheme,
    );
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
    assert!(generalized.stack_quantifiers.is_empty());
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

    assert!(generalized.stack_quantifiers.is_empty());
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
    assert_eq!(generalized.stack_quantifiers, vec![subtract]);
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
    assert!(generalized.stack_quantifiers.is_empty());
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
fn cleanup_removes_bare_floor_weights_without_live_stack_entries() {
    let mut machine = ConstraintMachine::new();
    let effect = TypeVar(2);
    let subtract = SubtractId(3);
    let handled = Subtractability::AllExcept(vec!["handled".into()], Vec::new());
    machine.register_type_var(effect, TypeLevel::root().child());
    let root = CompactRoot {
        root: bipolar_effect_fun(
            effect,
            CompactType::from_var(CompactVar::covariant(
                effect,
                StackWeight::floor(subtract, handled).compose(&StackWeight::pops(subtract, 2)),
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
    assert!(
        !generalized.compact.root.funs[0].ret_eff.vars[0]
            .weight
            .contains(subtract)
    );
    assert!(finalized.scheme.stack_quantifiers.is_empty());
}

#[test]
fn spent_residual_stack_entry_with_plain_negative_var_is_internal() {
    let mut machine = ConstraintMachine::new();
    let effect = TypeVar(2);
    let subtract = SubtractId(3);
    let handled = Subtractability::AllExcept(vec!["handled".into()], Vec::new());
    machine.register_type_var(effect, TypeLevel::root().child());
    let root = CompactRoot {
        root: bipolar_effect_fun(
            effect,
            CompactType::from_var(CompactVar::covariant(
                effect,
                StackWeight::floor(subtract, handled.clone())
                    .compose(&StackWeight::push(subtract, handled)),
            )),
        ),
        rec_vars: Vec::new(),
    };

    let generalized =
        generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());
    let mut types = TypeArena::new();
    let finalized = finalize_generalized_compact_root(&mut types, &machine, &generalized);

    assert!(generalized.stack_quantifiers.is_empty());
    assert!(
        !generalized.compact.root.funs[0].ret_eff.vars[0]
            .weight
            .contains(subtract)
    );
    assert!(finalized.scheme.stack_quantifiers.is_empty());
}

#[test]
fn instantiated_stack_entry_with_plain_negative_var_is_internal() {
    let mut machine = ConstraintMachine::new();
    let effect = TypeVar(2);
    let subtract = SubtractId(3);
    let handled = Subtractability::Set(vec!["handled".into()], Vec::new());
    machine.register_type_var(effect, TypeLevel::root().child());
    let root = CompactRoot {
        root: bipolar_effect_fun(
            effect,
            CompactType::from_var(CompactVar::covariant(
                effect,
                StackWeight::pops(subtract, u32::MAX)
                    .compose(&StackWeight::push(subtract, handled)),
            )),
        ),
        rec_vars: Vec::new(),
    };

    let generalized =
        generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());
    let mut types = TypeArena::new();
    let finalized = finalize_generalized_compact_root(&mut types, &machine, &generalized);

    assert!(generalized.stack_quantifiers.is_empty());
    assert!(
        !generalized.compact.root.funs[0].ret_eff.vars[0]
            .weight
            .contains(subtract)
    );
    assert!(finalized.scheme.stack_quantifiers.is_empty());
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

    assert!(generalized.stack_quantifiers.is_empty());
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

    let generalized = generalize_type_var_with_boundaries(
        &machine,
        root,
        TypeLevel::root(),
        TypeLevel::root().child(),
        &FxHashSet::default(),
    );

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
                lower: merge_compact_types(
                    true,
                    CompactType::from_var(CompactVar::plain(rec)),
                    CompactType::from_con(CompactCon {
                        path: vec!["list".into()],
                        args: Vec::new(),
                    }),
                ),
                upper: CompactType::from_var(CompactVar::plain(rec)),
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
                lower: merge_compact_types(
                    true,
                    CompactType::from_var(CompactVar::plain(var)),
                    CompactType::from_builtin(poly::types::BuiltinType::Int),
                ),
                upper: CompactType::from_var(CompactVar::plain(var)),
            },
        }],
    };
    let generalized =
        generalize_compact_root(&machine, TypeLevel::root(), root, &FxHashSet::default());
    let mut types = TypeArena::new();

    let finalized = finalize_generalized_compact_root(&mut types, &machine, &generalized);

    assert_eq!(finalized.scheme.recursive_bounds.len(), 1);
    assert_eq!(finalized.scheme.recursive_bounds[0].var, var);
    let poly::types::Neu::Bounds(lower, _) = types.neu(finalized.scheme.recursive_bounds[0].bounds)
    else {
        panic!("expected recursive bounds");
    };
    assert!(pos_contains_builtin_path(&types, *lower, "int"));
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
        inputs: vec![CompactRoleArg::invariant(CompactBounds::Interval {
            lower: CompactType::from_var(CompactVar::plain(role_var)),
            upper: CompactType::from_var(CompactVar::plain(role_var)),
        })],
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
    let RolePredicateArg::Invariant(input) = finalized.scheme.role_predicates[0].inputs[0] else {
        panic!("expected invariant role input");
    };
    assert!(matches!(
        types.neu(input),
        poly::types::Neu::Bounds(lower, upper)
            if matches!(types.pos(*lower), poly::types::Pos::Var(v) if *v == role_var)
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
            inputs: vec![CompactRoleArg::invariant(CompactBounds::Interval {
                lower: CompactType::from_builtin(poly::types::BuiltinType::Int),
                upper: merge_compact_types(
                    true,
                    CompactType::from_var(CompactVar::plain(role_var)),
                    CompactType::from_builtin(poly::types::BuiltinType::Int),
                ),
            })],
            associated: Vec::new(),
        }],
        quantifiers: vec![role_var],
        stack_quantifiers: Vec::new(),
        substitutions: Vec::new(),
        sandwiches: Vec::new(),
    };
    let mut types = TypeArena::new();
    let finalized = finalize_generalized_compact_root(&mut types, &machine, &generalized);

    assert_eq!(finalized.scheme.role_predicates.len(), 1);
    let RolePredicateArg::Invariant(input) = finalized.scheme.role_predicates[0].inputs[0] else {
        panic!("expected invariant role input");
    };
    let actual = types.neu(input);
    assert!(
        matches!(
            actual,
            poly::types::Neu::Bounds(lower, upper)
                if matches!(
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

fn pos_contains_builtin_path(types: &TypeArena, id: PosId, expected: &str) -> bool {
    match types.pos(id) {
        poly::types::Pos::Con(path, args) => {
            path.len() == 1 && path[0] == expected && args.is_empty()
        }
        poly::types::Pos::Union(left, right) => {
            pos_contains_builtin_path(types, *left, expected)
                || pos_contains_builtin_path(types, *right, expected)
        }
        _ => false,
    }
}

fn compact_type_contains_var(ty: &CompactType, expected: TypeVar) -> bool {
    ty.vars.iter().any(|var| var.var == expected)
        || ty.cons.values().any(|args| {
            args.iter()
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
            row.items.values().any(|args| {
                args.iter()
                    .any(|arg| compact_bounds_contains_var(arg, expected))
            }) || compact_type_contains_var(&row.tail, expected)
        })
}

fn compact_bounds_contains_var(bounds: &CompactBounds, expected: TypeVar) -> bool {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            compact_type_contains_var(lower, expected) || compact_type_contains_var(upper, expected)
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
