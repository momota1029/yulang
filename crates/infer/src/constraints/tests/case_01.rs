use super::*;

#[test]
fn constraint_weight_keeps_stack_normal_form_per_subtract_id() {
    let a = SubtractId(2);
    let b = SubtractId(1);
    let weight = ConstraintWeight::from_ids([a, b, a]);

    assert_eq!(weight.iter().collect::<Vec<_>>(), vec![b, a]);
    assert!(weight.contains(a));
    assert!(weight.contains(b));
    assert_eq!(weight.entries()[0].pops, 1);
    assert_eq!(weight.entries()[1].pops, 2);
}

#[test]
fn constraint_weights_swap_left_and_right() {
    let left = SubtractId(0);
    let right = SubtractId(1);
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::from_ids([left]),
        right: RightConstraintWeight::from_ids([right]),
    };

    let swapped = weights.swapped();
    assert!(swapped.left.contains(right));
    assert!(swapped.right.contains(left));
}

#[test]
fn constraint_epoch_advances_only_for_new_constraint_state() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let target = TypeVar(1);
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Var(target));

    assert_eq!(machine.epoch().as_u64(), 0);

    machine.subtype(lower, upper);
    let after_first = machine.epoch().as_u64();
    let source_epoch = machine.bounds().of(source).unwrap().epoch().as_u64();
    let target_epoch = machine.bounds().of(target).unwrap().epoch().as_u64();

    assert!(after_first > 0);
    assert!(source_epoch > 0);
    assert!(target_epoch > 0);

    machine.subtype(lower, upper);

    assert_eq!(machine.epoch().as_u64(), after_first);
    assert_eq!(
        machine.bounds().of(source).unwrap().epoch().as_u64(),
        source_epoch
    );
    assert_eq!(
        machine.bounds().of(target).unwrap().epoch().as_u64(),
        target_epoch
    );
}

#[test]
fn constraint_epoch_covers_level_registration_and_lowering() {
    let mut machine = ConstraintMachine::new();
    let var = TypeVar(0);

    machine.register_type_var(var, TypeLevel::root().child());
    let registered = machine.epoch();
    assert!(registered.as_u64() > 0);

    machine.register_type_var(var, TypeLevel::root());
    assert_eq!(
        machine.epoch(),
        registered,
        "re-registration is not a mutation"
    );

    let pos = machine.alloc_pos(Pos::Var(var));
    machine.extrude_pos(pos, TypeLevel::root());
    assert!(machine.epoch() > registered);
    assert_eq!(machine.level_of(var), TypeLevel::root());
}

#[test]
fn constraint_epoch_covers_upper_row_pruning_and_neighbor_removal() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    machine.register_type_var(source, TypeLevel::root());
    machine.register_type_var(tail_var, TypeLevel::root());
    let item = machine.alloc_neg(Neg::Con(vec!["effect".into()], Vec::new()));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let row = machine.alloc_neg(Neg::Row(vec![item], tail));
    machine.add_upper_bound(source, row, ConstraintWeights::empty());
    assert!(machine.var_neighbors(source).any(|var| var == tail_var));
    let epoch = machine.epoch();
    let var_epoch = machine.bounds().of(source).expect("source bounds").epoch();

    machine.prune_upper_rows_subsumed_by_reduced_upper(source, tail);

    assert!(machine.epoch() > epoch);
    let bounds = machine.bounds().of(source).expect("source bounds");
    assert!(bounds.epoch() > var_epoch);
    assert!(bounds.uppers().is_empty());
    assert!(!machine.var_neighbors(source).any(|var| var == tail_var));
}

#[test]
fn saturated_constraint_epoch_cannot_witness_unchanged_state() {
    assert!(!ConstraintEpoch(u64::MAX).can_witness_unchanged_state());
    assert!(ConstraintEpoch(u64::MAX - 1).can_witness_unchanged_state());
}

#[test]
fn constraint_weights_replay_keeps_exact_pop_count_and_stack_sequence() {
    let id = SubtractId(0);
    let io = Subtractability::Set(vec!["io".into()], Vec::new());
    let left = LeftConstraintWeight::pop(id)
        .compose(&LeftConstraintWeight::push(id, io.clone()))
        .compose(&LeftConstraintWeight::push(id, io.clone()));
    let weights = ConstraintWeights {
        left,
        right: RightConstraintWeight::empty(),
    }
    .compose_for_replay(&ConstraintWeights::empty());

    assert_eq!(weights.left.entries().len(), 1);
    assert_eq!(weights.left.entries()[0].leading_pops, 1);
    assert_eq!(weights.left.entries()[0].family, Some(io));
    assert_eq!(weights.left.entries()[0].pushes, 2);
}

#[test]
fn constraint_weights_replay_preserves_pop_only_count() {
    let id = SubtractId(0);
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::pop(id),
        right: RightConstraintWeight::empty(),
    }
    .compose_for_replay(&ConstraintWeights::empty());

    let [entry] = weights.left.entries() else {
        panic!("expected one stack entry");
    };
    assert_eq!(entry.leading_pops, 1);
    assert_eq!(entry.pushes, 0);
    assert!(entry.family.is_none());
}

#[test]
fn constraint_weights_replay_composes_repeated_pop_only_count() {
    let id = SubtractId(0);
    let earlier = ConstraintWeights {
        left: LeftConstraintWeight::pop(id),
        right: RightConstraintWeight::empty(),
    };
    let later = ConstraintWeights {
        left: LeftConstraintWeight::pop(id),
        right: RightConstraintWeight::empty(),
    };

    let weights = earlier.compose_for_replay(&later);

    let [entry] = weights.left.entries() else {
        panic!("expected one stack entry");
    };
    assert_eq!(entry.leading_pops, 2);
    assert_eq!(entry.pushes, 0);
    assert!(entry.family.is_none());
}

#[test]
fn constraint_weights_replay_mixes_left_push_with_right_pop() {
    let id = SubtractId(0);
    let earlier = ConstraintWeights {
        left: LeftConstraintWeight::push(id, Subtractability::Empty),
        right: RightConstraintWeight::empty(),
    };
    let later = ConstraintWeights {
        left: LeftConstraintWeight::empty(),
        right: RightConstraintWeight::pop(id),
    };

    let weights = earlier.compose_for_replay(&later);

    assert!(weights.is_empty());
}

#[test]
fn constraint_weights_replay_keeps_remaining_left_push_after_mix() {
    let id = SubtractId(0);
    let io = Subtractability::Set(vec!["io".into()], Vec::new());
    let earlier = ConstraintWeights {
        left: LeftConstraintWeight::push(id, io.clone())
            .compose(&LeftConstraintWeight::push(id, io.clone())),
        right: RightConstraintWeight::empty(),
    };
    let later = ConstraintWeights {
        left: LeftConstraintWeight::empty(),
        right: RightConstraintWeight::pop(id),
    };

    let weights = earlier.compose_for_replay(&later);

    assert!(weights.right.is_empty());
    let [entry] = weights.left.entries() else {
        panic!("expected one left stack entry");
    };
    assert_eq!(entry.leading_pops, 0);
    assert_eq!(entry.family, Some(io));
    assert_eq!(entry.pushes, 1);
}

#[test]
fn constraint_weights_replay_projects_pure_pop_to_right_after_mix() {
    let id = SubtractId(0);
    let earlier = ConstraintWeights {
        left: LeftConstraintWeight::push(id, Subtractability::Empty),
        right: RightConstraintWeight::empty(),
    };
    let later = ConstraintWeights {
        left: LeftConstraintWeight::empty(),
        right: RightConstraintWeight::pops(id, 2),
    };

    let weights = earlier.compose_for_replay(&later);

    assert!(weights.left.is_empty());
    let [entry] = weights.right.entries() else {
        panic!("expected one right pop entry");
    };
    assert_eq!(entry.id, id);
    assert_eq!(entry.pops, 1);
}

#[test]
fn constraint_weights_replay_ignores_legacy_floor_in_left_weight() {
    let id = SubtractId(0);
    let earlier = ConstraintWeights {
        left: LeftConstraintWeight::from_stack_weight(&StackWeight::floor(
            id,
            Subtractability::Empty,
        )),
        right: RightConstraintWeight::empty(),
    };
    let later = ConstraintWeights {
        left: LeftConstraintWeight::empty(),
        right: RightConstraintWeight::pop(id),
    };

    let weights = earlier.compose_for_replay(&later);

    assert!(weights.left.is_empty());
    let [right_entry] = weights.right.entries() else {
        panic!("expected one right pop entry");
    };
    assert_eq!(right_entry.id, id);
    assert_eq!(right_entry.pops, 1);
}

#[test]
fn constraint_weights_replay_composes_right_pops() {
    let id = SubtractId(0);
    let earlier = ConstraintWeights {
        left: LeftConstraintWeight::empty(),
        right: RightConstraintWeight::pop(id),
    };
    let later = ConstraintWeights {
        left: LeftConstraintWeight::empty(),
        right: RightConstraintWeight::pop(id),
    };

    let weights = earlier.compose_for_replay(&later);

    let [entry] = weights.right.entries() else {
        panic!("expected one right pop entry");
    };
    assert_eq!(entry.id, id);
    assert_eq!(entry.pops, 2);
}

#[test]
fn constraint_weights_replay_keeps_right_pop_saturation() {
    let id = SubtractId(0);
    let earlier = ConstraintWeights {
        left: LeftConstraintWeight::empty(),
        right: RightConstraintWeight::pops(id, u32::MAX),
    };
    let later = ConstraintWeights {
        left: LeftConstraintWeight::empty(),
        right: RightConstraintWeight::pop(id),
    };

    let weights = earlier.compose_for_replay(&later);

    let [entry] = weights.right.entries() else {
        panic!("expected one stack entry");
    };
    assert_eq!(entry.pops, u32::MAX);
}

#[test]
fn stack_weight_floor_survives_later_unmatched_pops() {
    let id = SubtractId(0);
    let io = Subtractability::AllExcept(vec!["io".into()], Vec::new());
    let weight = StackWeight::floor(id, io.clone())
        .compose(&StackWeight::pops(id, u32::MAX))
        .compose(&StackWeight::pop(id));

    let [entry] = weight.entries() else {
        panic!("expected one stack entry");
    };
    assert_eq!(entry.pops, u32::MAX);
    assert_eq!(entry.floor, vec![io]);
    assert!(entry.stack.is_empty());
}

#[test]
fn machine_records_subtract_facts_outside_subtype_bounds() {
    let mut machine = ConstraintMachine::new();
    let effect = TypeVar(0);
    let subtract = SubtractId(1);

    machine.subtract_fact(effect, subtract, Subtractability::All);
    machine.subtract_fact(effect, subtract, Subtractability::All);

    assert_eq!(
        machine.subtracts().facts(effect),
        &[SubtractFact {
            id: subtract,
            subtractability: Subtractability::All
        }]
    );
    assert!(machine.bounds().of(effect).is_none());
    assert_eq!(
        machine.take_events(),
        vec![ConstraintEvent::SubtractFactAdded {
            effect,
            id: subtract
        }]
    );
}

#[test]
fn lower_bound_extrudes_deeper_positive_variables_to_target_level() {
    let mut machine = ConstraintMachine::new();
    let target = TypeVar(0);
    let inner = TypeVar(1);
    let root = TypeLevel::root();
    let child = root.child();
    machine.register_type_var(target, root);
    machine.register_type_var(inner, child);
    let lower = machine.alloc_pos(Pos::Var(inner));
    let upper = machine.alloc_neg(Neg::Var(target));

    machine.subtype(lower, upper);

    assert_eq!(machine.level_of(inner), root);
    let bounds = machine.bounds().of(target).expect("target bounds");
    assert_eq!(
        bounds.lowers(),
        &[WeightedLowerBound {
            pos: lower,
            weights: ConstraintWeights::empty()
        }]
    );
}

#[test]
fn lower_bound_extrudes_secondary_level_variables_to_target_level() {
    let mut machine = ConstraintMachine::new();
    let target = TypeVar(0);
    let inner = TypeVar(1);
    let root = TypeLevel::root();
    machine.register_type_var(target, root);
    machine.register_type_var(inner, TypeLevel::secondary());
    let lower = machine.alloc_pos(Pos::Var(inner));
    let upper = machine.alloc_neg(Neg::Var(target));

    machine.subtype(lower, upper);

    assert_eq!(machine.level_of(inner), root);
}

#[test]
fn upper_bound_extrudes_deeper_negative_variables_to_source_level() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let inner = TypeVar(1);
    let root = TypeLevel::root();
    let child = root.child();
    machine.register_type_var(source, root);
    machine.register_type_var(inner, child);
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Var(inner));

    machine.subtype(lower, upper);

    assert_eq!(machine.level_of(inner), root);
    let bounds = machine.bounds().of(source).expect("source bounds");
    assert_eq!(
        bounds.uppers(),
        &[WeightedUpperBound {
            neg: upper,
            weights: ConstraintWeights::empty()
        }]
    );
}

#[test]
fn extrusion_recurses_through_neutral_constructor_args_and_existing_bounds() {
    let mut machine = ConstraintMachine::new();
    let target = TypeVar(0);
    let inner = TypeVar(1);
    let bound_var = TypeVar(2);
    let root = TypeLevel::root();
    let child = root.child();
    machine.register_type_var(target, root);
    machine.register_type_var(inner, child);
    machine.register_type_var(bound_var, child);
    let inner_as_lower = machine.alloc_pos(Pos::Var(inner));
    let bound_var_as_upper = machine.alloc_neg(Neg::Var(bound_var));
    machine.subtype(inner_as_lower, bound_var_as_upper);

    let arg_lower = machine.alloc_pos(Pos::Var(inner));
    let arg_upper = machine.alloc_neg(Neg::Var(bound_var));
    let arg = machine.alloc_neu(Neu::Bounds(arg_lower, arg_upper));
    let lower = machine.alloc_pos(Pos::Con(vec!["box".into()], vec![arg]));
    let upper = machine.alloc_neg(Neg::Var(target));

    machine.subtype(lower, upper);

    assert_eq!(machine.level_of(inner), root);
    assert_eq!(machine.level_of(bound_var), root);
}

#[test]
fn subtype_to_neg_var_drops_weighted_non_effect_terminal_lower_bound() {
    let mut machine = ConstraintMachine::new();
    let target = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["int".into()], vec![]));
    let upper = machine.alloc_neg(Neg::Var(target));
    let subtract = SubtractId(0);
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::from_ids([subtract]),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights.clone(), upper);

    let bounds = machine.bounds().of(target).expect("target bounds");
    assert_eq!(
        bounds.lowers(),
        &[WeightedLowerBound {
            pos: lower,
            weights: ConstraintWeights::empty()
        }]
    );
    assert!(bounds.uppers().is_empty());
    assert_eq!(
        machine.events(),
        &[ConstraintEvent::LowerBoundAdded {
            var: target,
            bound: lower,
            weights: ConstraintWeights::empty()
        }]
    );
}

#[test]
fn subtype_to_neg_var_keeps_weighted_effect_terminal_lower_bound() {
    let mut machine = ConstraintMachine::new();
    machine.register_effect_family_path(vec!["io".into()]);
    let target = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["io".into()], vec![]));
    let upper = machine.alloc_neg(Neg::Var(target));
    let subtract = SubtractId(0);
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::from_ids([subtract]),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights.clone(), upper);

    let bounds = machine.bounds().of(target).expect("target bounds");
    assert_eq!(
        bounds.lowers(),
        &[WeightedLowerBound {
            pos: lower,
            weights: weights.clone()
        }]
    );
    assert!(bounds.uppers().is_empty());
    assert_eq!(
        machine.events(),
        &[ConstraintEvent::LowerBoundAdded {
            var: target,
            bound: lower,
            weights
        }]
    );
}

#[test]
fn pos_var_to_subtype_drops_weighted_non_effect_terminal_upper_bound() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Con(vec!["int".into()], vec![]));
    let subtract = SubtractId(0);
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::empty(),
        right: RightConstraintWeight::from_ids([subtract]),
    };

    machine.weighted_subtype(lower, weights.clone(), upper);

    let bounds = machine.bounds().of(source).expect("source bounds");
    assert!(bounds.lowers().is_empty());
    assert_eq!(
        bounds.uppers(),
        &[WeightedUpperBound {
            neg: upper,
            weights: ConstraintWeights::empty()
        }]
    );
}

#[test]
fn pos_var_to_subtype_keeps_weighted_effect_terminal_upper_bound() {
    let mut machine = ConstraintMachine::new();
    machine.register_effect_family_path(vec!["io".into()]);
    let source = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let subtract = SubtractId(0);
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::empty(),
        right: RightConstraintWeight::from_ids([subtract]),
    };

    machine.weighted_subtype(lower, weights.clone(), upper);

    let bounds = machine.bounds().of(source).expect("source bounds");
    assert!(bounds.lowers().is_empty());
    assert_eq!(
        bounds.uppers(),
        &[WeightedUpperBound {
            neg: upper,
            weights
        }]
    );
}

#[test]
fn weighted_var_to_itself_constraint_is_noop() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let subtract = SubtractId(0);
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Var(source));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::push(
            subtract,
            Subtractability::Set(vec!["io".into()], Vec::new()),
        ),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights, upper);

    assert!(machine.bounds().of(source).is_none());
}

#[test]
fn var_bound_addition_replays_against_opposite_bounds_with_union_weights() {
    let mut machine = ConstraintMachine::new();
    let var = TypeVar(0);
    let lower_arg_pos = machine.alloc_pos(Pos::Bot);
    let lower_arg_neg = machine.alloc_neg(Neg::Top);
    let lower_arg = machine.alloc_neu(Neu::Bounds(lower_arg_pos, lower_arg_neg));
    let lower = machine.alloc_pos(Pos::Con(vec!["box".into()], vec![lower_arg]));
    let lower_weight = ConstraintWeights {
        left: LeftConstraintWeight::from_ids([SubtractId(0)]),
        right: RightConstraintWeight::empty(),
    };
    let var_neg = machine.alloc_neg(Neg::Var(var));
    machine.weighted_subtype(lower, lower_weight.clone(), var_neg);

    let var_pos = machine.alloc_pos(Pos::Var(var));
    let upper_arg_pos = machine.alloc_pos(Pos::Bot);
    let upper_arg_neg = machine.alloc_neg(Neg::Top);
    let upper_arg = machine.alloc_neu(Neu::Bounds(upper_arg_pos, upper_arg_neg));
    let upper = machine.alloc_neg(Neg::Con(vec!["box".into()], vec![upper_arg]));
    let upper_weight = ConstraintWeights {
        left: LeftConstraintWeight::empty(),
        right: RightConstraintWeight::from_ids([SubtractId(1)]),
    };
    machine.weighted_subtype(var_pos, upper_weight.clone(), upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower,
        upper,
        weights: lower_weight.compose_for_replay(&upper_weight),
    }));
}

#[test]
fn var_var_replay_materializes_transitive_edges() {
    let mut machine = ConstraintMachine::new();
    let a = TypeVar(0);
    let b = TypeVar(1);
    let c = TypeVar(2);

    let a_pos = machine.alloc_pos(Pos::Var(a));
    let b_neg = machine.alloc_neg(Neg::Var(b));
    machine.subtype(a_pos, b_neg);

    let b_pos = machine.alloc_pos(Pos::Var(b));
    let c_neg = machine.alloc_neg(Neg::Var(c));
    machine.subtype(b_pos, c_neg);

    let c_bounds = machine.bounds().of(c).expect("c should have direct lower");
    assert!(
        c_bounds
            .lowers()
            .iter()
            .any(|bound| matches!(machine.types().pos(bound.pos), Pos::Var(var) if *var == b))
    );
    assert!(
        c_bounds
            .lowers()
            .iter()
            .any(|bound| matches!(machine.types().pos(bound.pos), Pos::Var(var) if *var == a))
    );

    let int = machine.alloc_pos(Pos::Con(vec!["int".into()], vec![]));
    let a_neg = machine.alloc_neg(Neg::Var(a));
    machine.subtype(int, a_neg);

    let c_bounds = machine
        .bounds()
        .of(c)
        .expect("concrete lower should propagate to c");
    assert!(
        c_bounds
            .lowers()
            .iter()
            .any(|bound| bound.pos == int && bound.weights == ConstraintWeights::empty())
    );
}

#[test]
fn var_var_replay_keeps_balanced_alias_cycle_finite() {
    let mut machine = ConstraintMachine::new();
    let subtract = SubtractId(0);
    let a = TypeVar(0);
    let b = TypeVar(1);
    let c = TypeVar(2);

    let a_pos = machine.alloc_pos(Pos::Var(a));
    let b_neg = machine.alloc_neg(Neg::Var(b));
    machine.weighted_subtype(
        a_pos,
        ConstraintWeights {
            left: LeftConstraintWeight::push(subtract, Subtractability::Empty),
            right: RightConstraintWeight::empty(),
        },
        b_neg,
    );

    let b_pos = machine.alloc_pos(Pos::Var(b));
    let c_neg = machine.alloc_neg(Neg::Var(c));
    machine.weighted_subtype(
        b_pos,
        ConstraintWeights {
            left: LeftConstraintWeight::pop(subtract),
            right: RightConstraintWeight::empty(),
        },
        c_neg,
    );

    let c_pos = machine.alloc_pos(Pos::Var(c));
    let a_neg = machine.alloc_neg(Neg::Var(a));
    machine.subtype(c_pos, a_neg);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: a_pos,
        upper: c_neg,
        weights: ConstraintWeights::empty(),
    }));
    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: c_pos,
        upper: a_neg,
        weights: ConstraintWeights::empty(),
    }));
}

#[test]
fn var_var_replay_keeps_pop_only_alias_cycle_finite() {
    let mut machine = ConstraintMachine::new();
    let subtract = SubtractId(0);
    let a = TypeVar(0);
    let b = TypeVar(1);

    let a_pos = machine.alloc_pos(Pos::Var(a));
    let b_neg = machine.alloc_neg(Neg::Var(b));
    machine.weighted_subtype(
        a_pos,
        ConstraintWeights {
            left: LeftConstraintWeight::pop(subtract),
            right: RightConstraintWeight::empty(),
        },
        b_neg,
    );

    let b_pos = machine.alloc_pos(Pos::Var(b));
    let a_neg = machine.alloc_neg(Neg::Var(a));
    machine.subtype(b_pos, a_neg);

    for var in [a, b] {
        let Some(bounds) = machine.bounds().of(var) else {
            continue;
        };
        for lower in bounds.lowers() {
            assert_pop_only_weights_do_not_grow(&lower.weights, subtract);
        }
        for upper in bounds.uppers() {
            assert_pop_only_weights_do_not_grow(&upper.weights, subtract);
        }
    }
}

#[test]
fn var_var_replay_keeps_push_only_alias_cycle_finite() {
    let mut machine = ConstraintMachine::new();
    let subtract = SubtractId(0);
    let a = TypeVar(0);
    let b = TypeVar(1);

    let a_pos = machine.alloc_pos(Pos::Var(a));
    let b_neg = machine.alloc_neg(Neg::Var(b));
    machine.weighted_subtype(
        a_pos,
        ConstraintWeights {
            left: LeftConstraintWeight::push(subtract, Subtractability::Empty),
            right: RightConstraintWeight::empty(),
        },
        b_neg,
    );

    let b_pos = machine.alloc_pos(Pos::Var(b));
    let a_neg = machine.alloc_neg(Neg::Var(a));
    machine.subtype(b_pos, a_neg);

    for var in [a, b] {
        let Some(bounds) = machine.bounds().of(var) else {
            continue;
        };
        for lower in bounds.lowers() {
            assert_push_weights_do_not_grow(&lower.weights, subtract);
        }
        for upper in bounds.uppers() {
            assert_push_weights_do_not_grow(&upper.weights, subtract);
        }
    }
}

#[test]
fn var_var_replay_keeps_distinct_pop_only_boundaries() {
    let mut machine = ConstraintMachine::new();
    let first = SubtractId(0);
    let second = SubtractId(1);
    let a = TypeVar(0);
    let b = TypeVar(1);
    let a_pos = machine.alloc_pos(Pos::Var(a));
    let b_neg = machine.alloc_neg(Neg::Var(b));

    machine.weighted_subtype(
        a_pos,
        ConstraintWeights {
            left: LeftConstraintWeight::pop(first),
            right: RightConstraintWeight::empty(),
        },
        b_neg,
    );
    machine.weighted_subtype(
        a_pos,
        ConstraintWeights {
            left: LeftConstraintWeight::pop(second),
            right: RightConstraintWeight::empty(),
        },
        b_neg,
    );

    let bounds = machine.bounds().of(a).expect("a bounds");
    assert!(bounds.uppers().iter().any(|upper| {
        upper.neg == b_neg
            && upper.weights.left.contains(first)
            && !upper.weights.left.contains(second)
    }));
    assert!(bounds.uppers().iter().any(|upper| {
        upper.neg == b_neg
            && upper.weights.left.contains(second)
            && !upper.weights.left.contains(first)
    }));
}

#[test]
fn zero_arg_nominal_subtype_deduplicates_weight_insensitive_edges() {
    let mut machine = ConstraintMachine::new();
    let lower = machine.alloc_pos(Pos::Con(vec!["bool".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec!["bool".into()], Vec::new()));
    let weighted = ConstraintWeights {
        left: LeftConstraintWeight::push(SubtractId(0), Subtractability::Empty),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weighted, upper);
    machine.subtype(lower, upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower,
        upper,
        weights: ConstraintWeights::empty(),
    }));
    assert_eq!(machine.seen.len(), 1);
}

#[test]
fn terminal_non_effect_lower_bound_uses_empty_weight_without_matching_terminal_upper() {
    let mut machine = ConstraintMachine::new();
    let var = TypeVar(0);
    let bool_lower = machine.alloc_pos(Pos::Con(vec!["bool".into()], Vec::new()));
    let var_upper = machine.alloc_neg(Neg::Var(var));
    let weighted = ConstraintWeights {
        left: LeftConstraintWeight::push(SubtractId(0), Subtractability::Empty),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(bool_lower, weighted, var_upper);

    let bounds = machine.bounds().of(var).expect("var bounds");
    assert!(
        bounds
            .lowers()
            .iter()
            .any(|bound| bound.pos == bool_lower && bound.weights.is_empty())
    );
}

#[test]
fn terminal_effect_lower_bound_keeps_weight_without_matching_terminal_upper() {
    let mut machine = ConstraintMachine::new();
    machine.register_effect_family_path(vec!["io".into()]);
    let var = TypeVar(0);
    let io = machine.alloc_pos(Pos::Con(vec!["io".into()], Vec::new()));
    let var_upper = machine.alloc_neg(Neg::Var(var));
    let weighted = ConstraintWeights {
        left: LeftConstraintWeight::push(SubtractId(0), Subtractability::Empty),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(io, weighted.clone(), var_upper);

    let bounds = machine.bounds().of(var).expect("var bounds");
    assert_eq!(
        bounds.lowers(),
        &[WeightedLowerBound {
            pos: io,
            weights: weighted
        }]
    );
}

#[test]
fn function_arguments_propagate_with_swapped_weights() {
    let mut machine = ConstraintMachine::new();
    let lhs_arg = machine.alloc_neg(Neg::Var(TypeVar(0)));
    let lhs_arg_eff = machine.alloc_neg(Neg::Var(TypeVar(1)));
    let lhs_ret_eff = machine.alloc_pos(Pos::Var(TypeVar(2)));
    let lhs_ret = machine.alloc_pos(Pos::Var(TypeVar(3)));
    let lower = machine.alloc_pos(Pos::Fun {
        arg: lhs_arg,
        arg_eff: lhs_arg_eff,
        ret_eff: lhs_ret_eff,
        ret: lhs_ret,
    });

    let rhs_arg = machine.alloc_pos(Pos::Var(TypeVar(4)));
    let rhs_arg_eff = machine.alloc_pos(Pos::Var(TypeVar(5)));
    let rhs_ret_eff = machine.alloc_neg(Neg::Var(TypeVar(6)));
    let rhs_ret = machine.alloc_neg(Neg::Var(TypeVar(7)));
    let upper = machine.alloc_neg(Neg::Fun {
        arg: rhs_arg,
        arg_eff: rhs_arg_eff,
        ret_eff: rhs_ret_eff,
        ret: rhs_ret,
    });
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::from_ids([SubtractId(0)]),
        right: RightConstraintWeight::from_ids([SubtractId(1)]),
    };

    machine.weighted_subtype(lower, weights.clone(), upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: rhs_arg,
        upper: lhs_arg,
        weights: weights.swapped(),
    }));
    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: lhs_ret,
        upper: rhs_ret,
        weights,
    }));
}

#[test]
fn constructor_args_propagate_invariant_neutral_bounds() {
    let mut machine = ConstraintMachine::new();
    let lower_arg_lower = machine.alloc_pos(Pos::Var(TypeVar(0)));
    let lower_arg_upper = machine.alloc_neg(Neg::Var(TypeVar(1)));
    let lower_arg = machine.alloc_neu(Neu::Bounds(lower_arg_lower, lower_arg_upper));
    let upper_arg_lower = machine.alloc_pos(Pos::Var(TypeVar(2)));
    let upper_arg_upper = machine.alloc_neg(Neg::Var(TypeVar(3)));
    let upper_arg = machine.alloc_neu(Neu::Bounds(upper_arg_lower, upper_arg_upper));
    let lower = machine.alloc_pos(Pos::Con(vec!["box".into()], vec![lower_arg]));
    let upper = machine.alloc_neg(Neg::Con(vec!["box".into()], vec![upper_arg]));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::from_ids([SubtractId(0)]),
        right: RightConstraintWeight::from_ids([SubtractId(1)]),
    };

    machine.weighted_subtype(lower, weights.clone(), upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: lower_arg_lower,
        upper: upper_arg_upper,
        weights: weights.clone(),
    }));

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: upper_arg_lower,
        upper: lower_arg_upper,
        weights: weights.swapped(),
    }));
}

#[test]
fn mismatched_constructors_emit_nominal_cast_event() {
    let mut machine = ConstraintMachine::new();
    let lower = machine.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec!["user_id".into()], Vec::new()));

    machine.subtype(lower, upper);

    assert_eq!(
        machine.events(),
        &[ConstraintEvent::NominalCastNeeded {
            lower,
            upper,
            source: vec!["int".into()],
            target: vec!["user_id".into()],
            weights: ConstraintWeights::empty()
        }]
    );
}

#[test]
fn neutral_structures_build_regular_upper_and_lower_bounds() {
    let mut machine = ConstraintMachine::new();
    let lower_item_lower = machine.alloc_pos(Pos::Con(vec!["lower_item_lower".into()], vec![]));
    let lower_item_upper = machine.alloc_neg(Neg::Con(vec!["lower_item_upper".into()], vec![]));
    let lower_item = machine.alloc_neu(Neu::Bounds(lower_item_lower, lower_item_upper));
    let upper_item_lower = machine.alloc_pos(Pos::Con(vec!["upper_item_lower".into()], vec![]));
    let upper_item_upper = machine.alloc_neg(Neg::Con(vec!["upper_item_upper".into()], vec![]));
    let upper_item = machine.alloc_neu(Neu::Bounds(upper_item_lower, upper_item_upper));
    let lower_arg = machine.alloc_neu(Neu::Tuple(vec![lower_item]));
    let upper_arg = machine.alloc_neu(Neu::Tuple(vec![upper_item]));
    let lower = machine.alloc_pos(Pos::Con(vec!["box".into()], vec![lower_arg]));
    let upper = machine.alloc_neg(Neg::Con(vec!["box".into()], vec![upper_arg]));

    machine.subtype(lower, upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: lower_item_lower,
        upper: upper_item_upper,
        weights: ConstraintWeights::empty(),
    }));

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: upper_item_lower,
        upper: lower_item_upper,
        weights: ConstraintWeights::empty(),
    }));
}

#[test]
fn record_fields_propagate_matching_field_constraints() {
    let mut machine = ConstraintMachine::new();
    let lower_x = machine.alloc_pos(Pos::Con(vec!["lower_x".into()], vec![]));
    let upper_x = machine.alloc_neg(Neg::Con(vec!["upper_x".into()], vec![]));
    let lower = machine.alloc_pos(Pos::Record(vec![RecordField {
        name: "x".into(),
        value: lower_x,
        optional: false,
    }]));
    let upper = machine.alloc_neg(Neg::Record(vec![RecordField {
        name: "x".into(),
        value: upper_x,
        optional: false,
    }]));

    machine.subtype(lower, upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: lower_x,
        upper: upper_x,
        weights: ConstraintWeights::empty(),
    }));
}

#[test]
fn record_tail_spread_sends_missing_fields_to_tail() {
    let mut machine = ConstraintMachine::new();
    let tail = machine.alloc_pos(Pos::Var(TypeVar(0)));
    let upper_y = machine.alloc_neg(Neg::Con(vec!["upper_y".into()], vec![]));
    let upper = machine.alloc_neg(Neg::Record(vec![RecordField {
        name: "y".into(),
        value: upper_y,
        optional: false,
    }]));
    let lower = machine.alloc_pos(Pos::RecordTailSpread {
        fields: Vec::new(),
        tail,
    });
    let expected_tail_upper = machine.alloc_neg(Neg::Record(vec![RecordField {
        name: "y".into(),
        value: upper_y,
        optional: false,
    }]));

    machine.subtype(lower, upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: tail,
        upper: expected_tail_upper,
        weights: ConstraintWeights::empty(),
    }));
}

#[test]
fn variant_payloads_propagate_matching_tag_constraints() {
    let mut machine = ConstraintMachine::new();
    let lower_payload = machine.alloc_pos(Pos::Con(vec!["lower_payload".into()], vec![]));
    let upper_payload = machine.alloc_neg(Neg::Con(vec!["upper_payload".into()], vec![]));
    let lower = machine.alloc_pos(Pos::PolyVariant(vec![("some".into(), vec![lower_payload])]));
    let upper = machine.alloc_neg(Neg::PolyVariant(vec![("some".into(), vec![upper_payload])]));

    machine.subtype(lower, upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: lower_payload,
        upper: upper_payload,
        weights: ConstraintWeights::empty(),
    }));
}

#[test]
fn row_items_use_remaining_upper_rows_for_variables_and_tail_for_unmatched_atoms() {
    let mut machine = ConstraintMachine::new();
    machine.register_effect_family_path(vec!["io".into()]);
    machine.register_effect_family_path(vec!["fs".into()]);
    let io_pos = machine.alloc_pos(Pos::Con(vec!["io".into()], vec![]));
    let io_neg = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let fs_pos = machine.alloc_pos(Pos::Con(vec!["fs".into()], vec![]));
    let row_var = machine.alloc_pos(Pos::Var(TypeVar(0)));
    let upper_tail = machine.alloc_neg(Neg::Var(TypeVar(1)));
    let lower = machine.alloc_pos(Pos::Row(vec![io_pos, fs_pos, row_var]));
    let upper = machine.alloc_neg(Neg::Row(vec![io_neg], upper_tail));

    machine.subtype(lower, upper);

    let tail_bounds = machine.bounds().of(TypeVar(1)).expect("upper tail bounds");
    assert!(
        tail_bounds.lowers().iter().any(|lower| {
            lower.weights.is_empty()
                && matches!(
                    machine.types().pos(lower.pos),
                    Pos::Row(items) if items == &[fs_pos]
                )
        }),
        "unmatched concrete row item should flow into the tail as a row: {tail_bounds:?}"
    );
    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: row_var,
        upper: upper_tail,
        weights: ConstraintWeights::empty(),
    }));
    let old_row_var_upper = machine.alloc_neg(Neg::Row(vec![io_neg], upper_tail));
    assert!(!machine.seen.contains(&SubtypeConstraint {
        lower: row_var,
        upper: old_row_var_upper,
        weights: ConstraintWeights::empty(),
    }));
    assert!(!machine.seen.contains(&SubtypeConstraint {
        lower: io_pos,
        upper: upper_tail,
        weights: ConstraintWeights::empty(),
    }));
}

#[test]
fn row_items_keep_non_effect_atoms_direct_for_tail_residuals() {
    let mut machine = ConstraintMachine::new();
    let unit = machine.alloc_pos(Pos::Con(vec!["unit".into()], vec![]));
    let upper_tail = machine.alloc_neg(Neg::Var(TypeVar(0)));
    let lower = machine.alloc_pos(Pos::Row(vec![unit]));
    let upper = machine.alloc_neg(Neg::Row(vec![], upper_tail));

    machine.subtype(lower, upper);

    let tail_bounds = machine.bounds().of(TypeVar(0)).expect("upper tail bounds");
    assert!(
        tail_bounds.lowers().iter().any(|lower| {
            lower.weights.is_empty()
                && matches!(
                    machine.types().pos(lower.pos),
                    Pos::Con(path, _) if path == &vec!["unit".to_string()]
                )
        }),
        "non-effect atoms should stay direct tail candidates: {tail_bounds:?}"
    );
    assert!(
        !tail_bounds.lowers().iter().any(|lower| {
            matches!(
                machine.types().pos(lower.pos),
                Pos::Row(items) if items == &[unit]
            )
        }),
        "non-effect atoms must not be wrapped as effect rows: {tail_bounds:?}"
    );
}

#[test]
fn pos_row_variable_items_use_stack_weighted_row_upper_processing() {
    let mut machine = ConstraintMachine::new();
    let row_var = TypeVar(0);
    let tail_var = TypeVar(1);
    let subtract = SubtractId(0);
    let row_var_pos = machine.alloc_pos(Pos::Var(row_var));
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let nondet = machine.alloc_neg(Neg::Con(vec!["nondet".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let lower = machine.alloc_pos(Pos::Row(vec![row_var_pos]));
    let lower = machine.alloc_pos(Pos::Stack {
        inner: lower,
        weight: StackWeight::push(
            subtract,
            Subtractability::Set(vec!["io".into()], Vec::new()),
        ),
    });
    let upper = machine.alloc_neg(Neg::Row(vec![io, nondet], tail));

    machine.subtype(lower, upper);

    let gamma = single_upper_row_tail(&machine, row_var, &["io"]);
    let residual_weights = ConstraintWeights {
        left: residual_stack_weight(subtract, Subtractability::Empty),
        right: RightConstraintWeight::empty(),
    };
    assert_single_weighted_upper_var(&machine, gamma, tail_var, residual_weights);
}

#[test]
fn pos_row_concrete_effect_items_compare_matching_payloads() {
    let mut machine = ConstraintMachine::new();
    let lower_payload_lower =
        machine.alloc_pos(Pos::Con(vec!["lower_payload_lower".into()], vec![]));
    let lower_payload_upper =
        machine.alloc_neg(Neg::Con(vec!["lower_payload_upper".into()], vec![]));
    let lower_payload = machine.alloc_neu(Neu::Bounds(lower_payload_lower, lower_payload_upper));
    let upper_payload_lower =
        machine.alloc_pos(Pos::Con(vec!["upper_payload_lower".into()], vec![]));
    let upper_payload_upper =
        machine.alloc_neg(Neg::Con(vec!["upper_payload_upper".into()], vec![]));
    let upper_payload = machine.alloc_neu(Neu::Bounds(upper_payload_lower, upper_payload_upper));
    let lower_item = machine.alloc_pos(Pos::Con(
        crate::std_paths::control_var_ref_update_effect(),
        vec![lower_payload],
    ));
    let upper_item = machine.alloc_neg(Neg::Con(
        crate::std_paths::control_var_ref_update_effect(),
        vec![upper_payload],
    ));
    let upper_tail = machine.alloc_neg(Neg::Var(TypeVar(12)));
    let lower = machine.alloc_pos(Pos::Row(vec![lower_item]));
    let upper = machine.alloc_neg(Neg::Row(vec![upper_item], upper_tail));

    machine.subtype(lower, upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: lower_payload_lower,
        upper: upper_payload_upper,
        weights: ConstraintWeights::empty(),
    }));
    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: upper_payload_lower,
        upper: lower_payload_upper,
        weights: ConstraintWeights::empty(),
    }));
    assert!(!machine.seen.contains(&SubtypeConstraint {
        lower: lower_item,
        upper: upper_tail,
        weights: ConstraintWeights::empty(),
    }));
}

#[test]
fn pos_row_concrete_effect_items_match_by_path() {
    let mut machine = ConstraintMachine::new();
    let payload_lower = machine.alloc_pos(Pos::Bot);
    let payload_upper = machine.alloc_neg(Neg::Top);
    let payload = machine.alloc_neu(Neu::Bounds(payload_lower, payload_upper));
    let lower_item = machine.alloc_pos(Pos::Con(vec!["effect".into()], vec![payload]));
    let upper_item = machine.alloc_neg(Neg::Con(vec!["effect".into()], Vec::new()));
    let upper_tail = machine.alloc_neg(Neg::Var(TypeVar(11)));
    let lower = machine.alloc_pos(Pos::Row(vec![lower_item]));
    let upper = machine.alloc_neg(Neg::Row(vec![upper_item], upper_tail));

    machine.subtype(lower, upper);

    assert!(!machine.seen.contains(&SubtypeConstraint {
        lower: lower_item,
        upper: upper_tail,
        weights: ConstraintWeights::empty(),
    }));
}

#[test]
fn var_to_effect_row_upper_without_stack_weight_stores_raw_row() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let nondet = machine.alloc_neg(Neg::Con(vec!["nondet".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![io, nondet], tail));

    machine.subtype(lower, upper);

    let bounds = machine.bounds().of(source).expect("source bounds");
    assert_eq!(
        bounds.uppers(),
        &[WeightedUpperBound {
            neg: upper,
            weights: ConstraintWeights::empty()
        }]
    );
    assert!(machine.bounds().of(tail_var).is_none());
}

fn assert_pop_only_weights_do_not_grow(weights: &ConstraintWeights, subtract: SubtractId) {
    assert_pop_only_weight_does_not_grow(&weights.left, subtract);
    assert_right_pop_only_weight_does_not_grow(&weights.right, subtract);
}

fn assert_pop_only_weight_does_not_grow(weight: &LeftConstraintWeight, subtract: SubtractId) {
    for entry in weight.entries() {
        if entry.id == subtract && entry.pushes == 0 {
            assert!(
                entry.leading_pops <= 1,
                "alias replay should not grow naked pop-only weights: {weight:?}"
            );
        }
    }
}

fn assert_right_pop_only_weight_does_not_grow(
    weight: &RightConstraintWeight,
    subtract: SubtractId,
) {
    for entry in weight.entries() {
        if entry.id == subtract {
            assert!(
                entry.pops <= 1,
                "alias replay should not grow naked right-pop weights: {weight:?}"
            );
        }
    }
}

fn assert_push_weights_do_not_grow(weights: &ConstraintWeights, subtract: SubtractId) {
    for entry in weights.left.entries() {
        if entry.id == subtract && entry.family.is_some() {
            assert!(
                entry.pushes <= 1,
                "alias replay should not grow same-boundary take weights: {:?}",
                weights.left
            );
        }
    }
}
