use super::*;

#[test]
fn var_to_effect_row_upper_without_stack_weight_keeps_self_tail_row() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(source));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![io], tail));

    machine.subtype(lower, upper);

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
fn var_to_effect_row_upper_with_stack_weight_skips_self_tail_residual() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let subtract = SubtractId(0);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(source));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![io], tail));
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
fn var_to_effect_row_upper_filters_items_by_stack_common_part() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let subtract = SubtractId(0);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let nondet = machine.alloc_neg(Neg::Con(vec!["nondet".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![io, nondet], tail));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::push(
            subtract,
            Subtractability::Set(vec!["io".into()], Vec::new()),
        ),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights.clone(), upper);

    let gamma = single_upper_row_tail(&machine, source, &["io"]);
    let residual_weights = ConstraintWeights {
        left: residual_stack_weight(subtract, Subtractability::Empty),
        right: RightConstraintWeight::empty(),
    };
    assert_single_weighted_upper_var(&machine, gamma, tail_var, residual_weights);
}

#[test]
fn weighted_var_replay_does_not_retain_different_effect_family_row_item() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let through = TypeVar(1);
    let tail_var = TypeVar(2);
    let subtract = SubtractId(0);
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let through_neg = machine.alloc_neg(Neg::Var(through));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::push(
            subtract,
            Subtractability::Set(vec!["loop".into()], Vec::new()),
        ),
        right: RightConstraintWeight::empty(),
    };
    let redo = machine.alloc_neg(Neg::Con(vec!["loop".into(), "redo".into()], Vec::new()));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let through_pos = machine.alloc_pos(Pos::Var(through));
    let redo_upper = machine.alloc_neg(Neg::Row(vec![redo], tail));

    machine.weighted_subtype(source_pos, weights.clone(), through_neg);
    machine.subtype(through_pos, redo_upper);

    let bounds = machine.bounds().of(source).expect("source bounds");
    assert!(
        !bounds.uppers().iter().any(|upper| {
            upper.weights.is_empty()
                && matches!(machine.types().neg(upper.neg), Neg::Row(items, _) if items == &[redo])
        }),
        "different family row item should not be retained without stack weight"
    );
    assert!(
        bounds.uppers().iter().any(|upper| {
            upper.weights == weights
                && matches!(machine.types().neg(upper.neg), Neg::Var(found) if *found == tail_var)
        }),
        "unmatched row upper should continue to the tail with the original stack weight"
    );
}

#[test]
fn unweighted_row_upper_uses_concrete_lower_item_before_residual_tail() {
    let mut machine = ConstraintMachine::new();
    let result = TypeVar(0);
    let residual = TypeVar(1);
    let tail_var = TypeVar(2);
    let residual_pos = machine.alloc_pos(Pos::Var(residual));
    let result_neg = machine.alloc_neg(Neg::Var(result));
    let redo_pos = machine.alloc_pos(Pos::Con(vec!["loop".into(), "redo".into()], Vec::new()));
    let result_pos = machine.alloc_pos(Pos::Var(result));
    let redo_neg = machine.alloc_neg(Neg::Con(vec!["loop".into(), "redo".into()], Vec::new()));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let upper = machine.alloc_neg(Neg::Row(vec![redo_neg], tail));

    machine.subtype(residual_pos, result_neg);
    machine.subtype(redo_pos, result_neg);
    machine.subtype(result_pos, upper);

    let bounds = machine.bounds().of(residual).expect("residual bounds");
    assert!(
            !bounds.uppers().iter().any(|upper| {
                upper.weights.is_empty()
                    && matches!(machine.types().neg(upper.neg), Neg::Row(items, _) if items == &[redo_neg])
            }),
            "matched concrete lower item should not be required again from residual"
        );
    assert!(
        bounds.uppers().iter().any(|upper| {
            upper.weights.is_empty()
                && matches!(machine.types().neg(upper.neg), Neg::Var(found) if *found == tail_var)
        }),
        "residual lower should receive only the row tail after concrete item matching"
    );
}

#[test]
fn unweighted_row_upper_consumes_pop_only_weighted_lower_item() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let through = TypeVar(1);
    let tail_var = TypeVar(2);
    let subtract = SubtractId(0);
    let sub_path = vec!["std".into(), "control".into(), "flow".into(), "sub".into()];
    machine.register_effect_family_path(sub_path.clone());
    let sub = machine.alloc_pos(Pos::Con(sub_path.clone(), Vec::new()));
    let sub_upper = machine.alloc_neg(Neg::Con(sub_path, Vec::new()));
    let through_pos = machine.alloc_pos(Pos::Var(through));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let row_upper = machine.alloc_neg(Neg::Row(vec![sub_upper], tail));
    let through_neg = machine.alloc_neg(Neg::Var(through));

    machine.weighted_subtype(
        sub,
        ConstraintWeights {
            left: LeftConstraintWeight::pop(subtract),
            right: RightConstraintWeight::empty(),
        },
        through_neg,
    );
    machine.subtype(through_pos, source_neg);
    machine.subtype(source_pos, row_upper);

    let bounds = machine.bounds().of(source).expect("source bounds");
    assert!(
        !bounds.uppers().iter().any(|upper| {
            upper.weights.is_empty()
                && matches!(machine.types().neg(upper.neg), Neg::Row(items, _) if items == &[sub_upper])
        }),
        "pop-only lower item should satisfy the row item before residual tail"
    );
    assert!(
        bounds.uppers().iter().any(|upper| {
            upper.weights.is_empty()
                && matches!(machine.types().neg(upper.neg), Neg::Var(found) if *found == tail_var)
        }),
        "source should only keep the row tail after matching the item"
    );
    assert!(
        !machine
            .bounds()
            .of(tail_var)
            .into_iter()
            .flat_map(|bounds| bounds.lowers())
            .any(|lower| {
                lower.weights.is_empty()
                    && matches!(
                        machine.types().pos(lower.pos),
                        Pos::Row(items)
                            if items.iter().any(|item| {
                                matches!(
                                    machine.types().pos(*item),
                                    Pos::Con(path, _) if path.iter().map(String::as_str).eq([
                                        "std", "control", "flow", "sub"
                                    ])
                                )
                            })
                    )
            }),
        "matched row item should not flow into the residual tail"
    );
}

#[test]
fn direct_tail_upper_prunes_stale_unweighted_row_upper_from_aliases() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let residual = TypeVar(1);
    let tail_var = TypeVar(2);
    let residual_pos = machine.alloc_pos(Pos::Var(residual));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let sub = machine.alloc_neg(Neg::Con(
        vec!["std".into(), "control".into(), "flow".into(), "sub".into()],
        Vec::new(),
    ));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let row_upper = machine.alloc_neg(Neg::Row(vec![sub], tail));

    machine.subtype(residual_pos, source_neg);
    machine.subtype(source_pos, row_upper);
    machine.subtype(source_pos, tail);

    for var in [source, residual] {
        let bounds = machine.bounds().of(var).expect("bounds");
        assert!(
            !bounds.uppers().iter().any(|upper| {
                upper.weights.is_empty()
                    && matches!(machine.types().neg(upper.neg), Neg::Row(items, _) if items == &[sub])
            }),
            "tail upper should subsume stale row upper for {var:?}"
        );
        assert!(
            bounds.uppers().iter().any(|upper| {
                upper.weights.is_empty()
                    && matches!(machine.types().neg(upper.neg), Neg::Var(found) if *found == tail_var)
            }),
            "tail upper should still reach {var:?}"
        );
    }
}

#[test]
fn tail_alias_keeps_row_upper_across_stack_boundary() {
    fn assert_order(row_first: bool) {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(0);
        let inner = TypeVar(1);
        let tail_var = TypeVar(2);
        let subtract = SubtractId(0);
        let nondet_path = vec!["nondet".into()];
        let inner_pos = machine.alloc_pos(Pos::Var(inner));
        let source_neg = machine.alloc_neg(Neg::Var(source));
        let source_pos = machine.alloc_pos(Pos::Var(source));
        let tail = machine.alloc_neg(Neg::Var(tail_var));
        let nondet = machine.alloc_neg(Neg::Con(nondet_path.clone(), Vec::new()));
        let row = machine.alloc_neg(Neg::Row(vec![nondet], tail));

        machine.weighted_subtype(
            inner_pos,
            ConstraintWeights {
                left: LeftConstraintWeight::push(
                    subtract,
                    Subtractability::Set(nondet_path, Vec::new()),
                ),
                right: RightConstraintWeight::empty(),
            },
            source_neg,
        );
        if row_first {
            machine.subtype(source_pos, row);
            machine.subtype(source_pos, tail);
        } else {
            machine.subtype(source_pos, tail);
            machine.subtype(source_pos, row);
        }

        let bounds = machine.bounds().of(source).expect("source bounds");
        assert!(
            bounds.uppers().iter().any(|upper| {
                upper.weights.is_empty()
                    && matches!(machine.types().neg(upper.neg), Neg::Var(found) if *found == tail_var)
            }),
            "tail alias should remain for row_first={row_first}"
        );
        assert!(
            bounds.uppers().iter().any(|upper| {
                upper.weights.is_empty()
                    && matches!(
                        machine.types().neg(upper.neg),
                        Neg::Row(items, row_tail) if items == &[nondet] && *row_tail == tail
                    )
            }),
            "row upper should survive the tail alias for row_first={row_first}"
        );
    }

    assert_order(true);
    assert_order(false);
}

#[test]
fn unweighted_row_upper_matches_each_lower_independently() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let alias = TypeVar(1);
    let tail_var = TypeVar(2);
    let sub_path = vec!["std".into(), "control".into(), "flow".into(), "sub".into()];
    let sub_pos = machine.alloc_pos(Pos::Con(sub_path.clone(), Vec::new()));
    let sub_row = machine.alloc_pos(Pos::Row(vec![sub_pos]));
    let sub_neg = machine.alloc_neg(Neg::Con(sub_path, Vec::new()));
    let alias_neg = machine.alloc_neg(Neg::Var(alias));
    let alias_pos = machine.alloc_pos(Pos::Var(alias));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let row_upper = machine.alloc_neg(Neg::Row(vec![sub_neg], tail));

    machine.subtype(sub_row, alias_neg);
    machine.subtype(alias_pos, source_neg);
    machine.subtype(sub_row, source_neg);
    machine.subtype(source_pos, row_upper);

    assert!(
        !machine
            .bounds()
            .of(tail_var)
            .into_iter()
            .flat_map(|bounds| bounds.lowers())
            .any(|lower| {
                lower.weights.is_empty()
                    && matches!(
                        machine.types().pos(lower.pos),
                        Pos::Row(items) if items == &[sub_pos]
                    )
            }),
        "a concrete row lower matched after an alias should not flow into the residual tail"
    );
    let bounds = machine.bounds().of(source).expect("source bounds");
    assert!(
        bounds.uppers().iter().any(|upper| {
            upper.weights.is_empty()
                && matches!(machine.types().neg(upper.neg), Neg::Var(found) if *found == tail_var)
        }),
        "source should keep only the residual tail after matching the row item"
    );
}

#[test]
fn var_to_effect_row_upper_reuses_weighted_residual_for_same_source_across_tails() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let first_tail_var = TypeVar(1);
    let second_tail_var = TypeVar(2);
    let subtract = SubtractId(0);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let first_tail = machine.alloc_neg(Neg::Var(first_tail_var));
    let second_tail = machine.alloc_neg(Neg::Var(second_tail_var));
    let lower = machine.alloc_pos(Pos::Var(source));
    let first_upper = machine.alloc_neg(Neg::Row(vec![io], first_tail));
    let second_upper = machine.alloc_neg(Neg::Row(vec![io], second_tail));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::push(
            subtract,
            Subtractability::Set(vec!["io".into()], Vec::new()),
        ),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights.clone(), first_upper);
    machine.weighted_subtype(lower, weights.clone(), second_upper);

    let first_gamma = find_empty_weight_row_tail(&machine, source, &["io"], first_tail_var);
    let second_gamma = find_empty_weight_row_tail(&machine, source, &["io"], second_tail_var);
    assert_eq!(first_gamma, second_gamma);
    let residual_weights = ConstraintWeights {
        left: residual_stack_weight(subtract, Subtractability::Empty),
        right: RightConstraintWeight::empty(),
    };
    assert_weighted_upper_var(
        &machine,
        first_gamma,
        first_tail_var,
        residual_weights.clone(),
    );
    assert_weighted_upper_var(&machine, second_gamma, second_tail_var, residual_weights);
}

#[test]
fn var_to_effect_row_upper_keeps_weighted_residuals_distinct_per_source() {
    let mut machine = ConstraintMachine::new();
    let first_source = TypeVar(0);
    let second_source = TypeVar(1);
    let tail_var = TypeVar(2);
    let subtract = SubtractId(0);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let first_lower = machine.alloc_pos(Pos::Var(first_source));
    let second_lower = machine.alloc_pos(Pos::Var(second_source));
    let first_upper = machine.alloc_neg(Neg::Row(vec![io], tail));
    let second_upper = machine.alloc_neg(Neg::Row(vec![io], tail));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::push(
            subtract,
            Subtractability::Set(vec!["io".into()], Vec::new()),
        ),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(first_lower, weights.clone(), first_upper);
    machine.weighted_subtype(second_lower, weights.clone(), second_upper);

    let first_gamma = single_upper_row_tail(&machine, first_source, &["io"]);
    let second_gamma = single_upper_row_tail(&machine, second_source, &["io"]);
    assert_ne!(first_gamma, second_gamma);
    assert_eq!(machine.row_residuals.len(), 2);
}

#[test]
fn var_to_effect_row_upper_with_empty_stack_intersection_skips_gamma() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let subtract = SubtractId(0);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![io], tail));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::push(subtract, Subtractability::Empty),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights.clone(), upper);

    let bounds = machine.bounds().of(source).expect("source bounds");
    assert_eq!(
        bounds.uppers(),
        &[WeightedUpperBound { neg: tail, weights }]
    );
    assert!(machine.row_residuals.is_empty());
}

#[test]
fn var_to_effect_row_upper_distributes_right_pop_to_tail_after_empty_head() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let subtract = SubtractId(0);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![io], tail));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::push(subtract, Subtractability::Empty),
        right: RightConstraintWeight::pop(subtract),
    };

    machine.weighted_subtype(lower, weights, upper);

    let bounds = machine.bounds().of(source).expect("source bounds");
    assert_eq!(
        bounds.uppers(),
        &[WeightedUpperBound {
            neg: tail,
            weights: ConstraintWeights::empty()
        }]
    );
    assert!(machine.row_residuals.is_empty());
}

#[test]
fn non_subtract_around_pos_stack_cancels_before_effect_row_upper() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let subtract = SubtractId(0);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let upper = machine.alloc_neg(Neg::Row(vec![io], tail));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let stacked = machine.alloc_pos(Pos::Stack {
        inner: source_pos,
        weight: StackWeight::push(subtract, Subtractability::Empty),
    });
    let lower = machine.alloc_pos(Pos::NonSubtract(stacked, StackWeight::pop(subtract)));

    machine.subtype(lower, upper);

    let bounds = machine.bounds().of(source).expect("source bounds");
    assert_eq!(
        bounds.uppers(),
        &[WeightedUpperBound {
            neg: upper,
            weights: ConstraintWeights::empty()
        }]
    );
    assert!(machine.row_residuals.is_empty());
}

#[test]
fn var_to_effect_row_upper_removes_all_except_excluded_effect_family() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let subtract = SubtractId(0);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let nondet = machine.alloc_neg(Neg::Con(vec!["nondet".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![io, nondet], tail));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::push(
            subtract,
            Subtractability::AllExcept(vec!["io".into()], Vec::new()),
        ),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights.clone(), upper);

    let gamma = single_upper_row_tail(&machine, source, &["nondet"]);
    let residual_weights = ConstraintWeights {
        left: residual_stack_weight(
            subtract,
            Subtractability::AllExceptMany(vec![
                (vec!["io".into()], Vec::new()),
                (vec!["nondet".into()], Vec::new()),
            ]),
        ),
        right: RightConstraintWeight::empty(),
    };
    assert_single_weighted_upper_var(&machine, gamma, tail_var, residual_weights);
}

#[test]
fn var_to_effect_row_upper_with_all_stack_retains_all_items() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let subtract = SubtractId(0);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let nondet = machine.alloc_neg(Neg::Con(vec!["nondet".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![io, nondet], tail));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::push(subtract, Subtractability::All),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights.clone(), upper);

    let gamma = single_upper_row_tail(&machine, source, &["io", "nondet"]);
    let residual_weights = ConstraintWeights {
        left: residual_stack_weight(
            subtract,
            Subtractability::AllExceptMany(vec![
                (vec!["io".into()], Vec::new()),
                (vec!["nondet".into()], Vec::new()),
            ]),
        ),
        right: RightConstraintWeight::empty(),
    };
    assert_single_weighted_upper_var(&machine, gamma, tail_var, residual_weights);
}

#[test]
fn var_to_effect_row_upper_removes_retained_item_from_pop_only_stack() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let next_tail_var = TypeVar(2);
    let subtract = SubtractId(0);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let next_tail = machine.alloc_neg(Neg::Var(next_tail_var));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![io], tail));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::pops(subtract, u32::MAX),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights, upper);

    let gamma = single_upper_row_tail(&machine, source, &["io"]);
    let residual_weights = ConstraintWeights {
        left: LeftConstraintWeight::pops(subtract, u32::MAX),
        right: RightConstraintWeight::empty(),
    };
    assert_single_weighted_upper_var(&machine, gamma, tail_var, residual_weights.clone());

    let tail_pos = machine.alloc_pos(Pos::Var(tail_var));
    let tail_upper = machine.alloc_neg(Neg::Row(vec![io], next_tail));
    machine.subtype(tail_pos, tail_upper);

    let gamma2 = find_empty_weight_row_tail(&machine, gamma, &["io"], next_tail_var);
    assert_ne!(gamma, gamma2);
    assert_eq!(machine.row_residuals.len(), 2);
    assert_weighted_upper_var(&machine, gamma2, next_tail_var, residual_weights);
}

#[test]
fn pop_only_residual_keeps_later_distinct_handler_subtractable() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let next_tail_var = TypeVar(2);
    let subtract = SubtractId(0);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let nondet = machine.alloc_neg(Neg::Con(vec!["nondet".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let next_tail = machine.alloc_neg(Neg::Var(next_tail_var));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![io], tail));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::pops(subtract, u32::MAX),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights, upper);

    let gamma = single_upper_row_tail(&machine, source, &["io"]);

    // pure pop だけの L は active family を持たないので、次の row head でも Common(L)=All になる。
    let tail_pos = machine.alloc_pos(Pos::Var(tail_var));
    let tail_upper = machine.alloc_neg(Neg::Row(vec![nondet], next_tail));
    machine.subtype(tail_pos, tail_upper);

    let gamma2 = machine
        .bounds()
        .of(gamma)
        .expect("gamma bounds")
        .uppers()
        .iter()
        .find_map(|upper| {
            if upper.weights != ConstraintWeights::empty() {
                return None;
            }
            let Neg::Row(items, row_tail) = machine.types().neg(upper.neg) else {
                return None;
            };
            let [item] = items.as_slice() else {
                return None;
            };
            let Neg::Con(path, _) = machine.types().neg(*item) else {
                return None;
            };
            if path != &vec!["nondet".to_string()] {
                return None;
            }
            match machine.types().neg(*row_tail) {
                Neg::Var(found) => Some(*found),
                _ => None,
            }
        })
        .expect("gamma row upper [nondet; gamma2]");
    assert_ne!(gamma, gamma2);
    assert_eq!(machine.row_residuals.len(), 2);
    let residual_weights = ConstraintWeights {
        left: LeftConstraintWeight::pops(subtract, u32::MAX),
        right: RightConstraintWeight::empty(),
    };
    assert_weighted_upper_var(&machine, gamma2, next_tail_var, residual_weights);
}

#[test]
fn var_to_effect_row_upper_keeps_residuals_distinct_by_effect_payload() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let subtract = SubtractId(0);
    let ref_update = crate::std_paths::control_var_ref_update_effect();
    let first_payload_lower = machine.alloc_pos(Pos::Var(TypeVar(10)));
    let first_payload_upper = machine.alloc_neg(Neg::Var(TypeVar(10)));
    let first_payload = machine.alloc_neu(Neu::Bounds(first_payload_lower, first_payload_upper));
    let second_payload_lower = machine.alloc_pos(Pos::Var(TypeVar(11)));
    let second_payload_upper = machine.alloc_neg(Neg::Var(TypeVar(11)));
    let second_payload = machine.alloc_neu(Neu::Bounds(second_payload_lower, second_payload_upper));
    let first_item = machine.alloc_neg(Neg::Con(ref_update.clone(), vec![first_payload]));
    let second_item = machine.alloc_neg(Neg::Con(ref_update.clone(), vec![second_payload]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let first_lower = machine.alloc_pos(Pos::Var(source));
    let second_lower = machine.alloc_pos(Pos::Var(source));
    let first_upper = machine.alloc_neg(Neg::Row(vec![first_item], tail));
    let second_upper = machine.alloc_neg(Neg::Row(vec![second_item], tail));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::push(subtract, Subtractability::All),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(first_lower, weights.clone(), first_upper);
    machine.weighted_subtype(second_lower, weights, second_upper);

    assert_eq!(machine.row_residuals.len(), 2);
    for (key, gamma) in &machine.row_residuals {
        let [family] = key.retained_families.as_slice() else {
            panic!(
                "expected one retained family, got {:?}",
                key.retained_families
            );
        };
        assert_eq!(family.path, ref_update);
        let residual_weights = ConstraintWeights {
            left: residual_stack_weight(
                subtract,
                Subtractability::AllExcept(family.path.clone(), family.args.clone()),
            ),
            right: RightConstraintWeight::empty(),
        };
        assert_weighted_upper_var(&machine, *gamma, tail_var, residual_weights);
    }
}

#[test]
fn var_to_effect_row_upper_keeps_effect_payloads_in_residual_stack_weight() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let subtract = SubtractId(0);
    let ref_update = crate::std_paths::control_var_ref_update_effect();
    let payload_lower = machine.alloc_pos(Pos::Var(TypeVar(10)));
    let payload_upper = machine.alloc_neg(Neg::Var(TypeVar(10)));
    let payload = machine.alloc_neu(Neu::Bounds(payload_lower, payload_upper));
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![io], tail));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::push(
            subtract,
            Subtractability::AllExcept(ref_update.clone(), vec![payload]),
        ),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights, upper);

    let gamma = single_upper_row_tail(&machine, source, &["io"]);
    let residual_weights = ConstraintWeights {
        left: residual_stack_weight(
            subtract,
            Subtractability::AllExceptMany(vec![
                (ref_update, vec![payload]),
                (vec!["io".into()], Vec::new()),
            ]),
        ),
        right: RightConstraintWeight::empty(),
    };
    assert_single_weighted_upper_var(&machine, gamma, tail_var, residual_weights);
}

#[test]
fn var_to_effect_row_upper_collects_duplicate_effect_paths_with_payload_constraints() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let subtract = SubtractId(0);
    let ref_update = crate::std_paths::control_var_ref_update_effect();
    let first_payload_lower = machine.alloc_pos(Pos::Var(TypeVar(10)));
    let first_payload_upper = machine.alloc_neg(Neg::Var(TypeVar(10)));
    let first_payload = machine.alloc_neu(Neu::Bounds(first_payload_lower, first_payload_upper));
    let second_payload_lower = machine.alloc_pos(Pos::Var(TypeVar(11)));
    let second_payload_upper = machine.alloc_neg(Neg::Var(TypeVar(11)));
    let second_payload = machine.alloc_neu(Neu::Bounds(second_payload_lower, second_payload_upper));
    let first_item = machine.alloc_neg(Neg::Con(ref_update.clone(), vec![first_payload]));
    let second_item = machine.alloc_neg(Neg::Con(ref_update.clone(), vec![second_payload]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![first_item, second_item], tail));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::push(subtract, Subtractability::All),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights, upper);

    let gamma = single_upper_row_tail(&machine, source, &["std::control::var::ref_update"]);
    let residual_weights = ConstraintWeights {
        left: residual_stack_weight(
            subtract,
            Subtractability::AllExcept(ref_update, vec![first_payload]),
        ),
        right: RightConstraintWeight::empty(),
    };
    assert_single_weighted_upper_var(&machine, gamma, tail_var, residual_weights);
    assert_weighted_upper_var(
        &machine,
        TypeVar(10),
        TypeVar(11),
        ConstraintWeights::empty(),
    );
    assert_weighted_upper_var(
        &machine,
        TypeVar(11),
        TypeVar(10),
        ConstraintWeights::empty(),
    );
}

#[test]
fn effect_row_filter_rejects_disallowed_concrete_family() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let nondet = machine.alloc_neg(Neg::Con(vec!["nondet".into()], Vec::new()));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![nondet], tail));
    let filter = Subtractability::Set(vec!["io".into()], Vec::new());
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::filter(filter.clone()),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights, upper);

    assert!(
        machine.events().iter().any(|event| matches!(
            event,
            ConstraintEvent::EffectFilterViolation {
                effect: Some(path),
                filter: found_filter,
            } if path == &vec!["nondet".to_string()] && found_filter == &filter
        )),
        "events: {:?}",
        machine.events()
    );
}

#[test]
fn effect_row_filter_constrains_matching_payloads() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let ref_update = crate::std_paths::control_var_ref_update_effect();
    let lower_payload_lower = machine.alloc_pos(Pos::Var(TypeVar(10)));
    let lower_payload_upper = machine.alloc_neg(Neg::Var(TypeVar(11)));
    let lower_payload = machine.alloc_neu(Neu::Bounds(lower_payload_lower, lower_payload_upper));
    let upper_payload_lower = machine.alloc_pos(Pos::Var(TypeVar(12)));
    let upper_payload_upper = machine.alloc_neg(Neg::Var(TypeVar(13)));
    let upper_payload = machine.alloc_neu(Neu::Bounds(upper_payload_lower, upper_payload_upper));
    let item = machine.alloc_neg(Neg::Con(ref_update.clone(), vec![lower_payload]));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![item], tail));
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::filter(Subtractability::Set(ref_update, vec![upper_payload])),
        right: RightConstraintWeight::empty(),
    };

    machine.weighted_subtype(lower, weights, upper);

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
    assert!(
        !machine
            .events()
            .iter()
            .any(|event| matches!(event, ConstraintEvent::EffectFilterViolation { .. })),
        "events: {:?}",
        machine.events()
    );
}

#[test]
fn neg_stack_common_stack_constrains_matching_payloads_across_active_ids() {
    let mut machine = ConstraintMachine::new();
    let ref_update = crate::std_paths::control_var_ref_update_effect();
    let first_payload_lower = machine.alloc_pos(Pos::Var(TypeVar(10)));
    let first_payload_upper = machine.alloc_neg(Neg::Var(TypeVar(11)));
    let first_payload = machine.alloc_neu(Neu::Bounds(first_payload_lower, first_payload_upper));
    let second_payload_lower = machine.alloc_pos(Pos::Var(TypeVar(12)));
    let second_payload_upper = machine.alloc_neg(Neg::Var(TypeVar(13)));
    let second_payload = machine.alloc_neu(Neu::Bounds(second_payload_lower, second_payload_upper));
    let value_payload_lower = machine.alloc_pos(Pos::Var(TypeVar(14)));
    let value_payload_upper = machine.alloc_neg(Neg::Var(TypeVar(15)));
    let value_payload = machine.alloc_neu(Neu::Bounds(value_payload_lower, value_payload_upper));
    let lower = machine.alloc_pos(Pos::Con(ref_update.clone(), vec![value_payload]));
    let inner = machine.alloc_neg(Neg::Top);
    let weight = StackWeight::push(
        SubtractId(0),
        Subtractability::Set(ref_update.clone(), vec![first_payload]),
    )
    .compose(&StackWeight::push(
        SubtractId(1),
        Subtractability::Set(ref_update, vec![second_payload]),
    ));
    let upper = machine.alloc_neg(Neg::Stack { inner, weight });

    machine.weighted_subtype(lower, ConstraintWeights::empty(), upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: first_payload_lower,
        upper: second_payload_upper,
        weights: ConstraintWeights::empty(),
    }));
    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: second_payload_lower,
        upper: first_payload_upper,
        weights: ConstraintWeights::empty(),
    }));
}

#[test]
fn neg_stack_empty_filter_rejects_concrete_effect_lower() {
    let mut machine = ConstraintMachine::new();
    let tick_path = vec!["tick".into()];
    machine.register_effect_family_path(tick_path.clone());
    let lower = machine.alloc_pos(Pos::Con(tick_path.clone(), Vec::new()));
    let inner = machine.alloc_neg(Neg::Top);
    let upper = machine.alloc_neg(Neg::Stack {
        inner,
        weight: StackWeight::filter(Subtractability::Empty),
    });

    machine.subtype(lower, upper);

    assert!(
        machine.events().iter().any(|event| matches!(
            event,
            ConstraintEvent::EffectFilterViolation {
                effect: Some(path),
                filter: Subtractability::Empty,
            } if path == &tick_path
        )),
        "events: {:?}",
        machine.events()
    );
}

#[test]
fn neg_stack_empty_active_push_does_not_filter_concrete_effect_lower() {
    let mut machine = ConstraintMachine::new();
    let tick_path = vec!["tick".into()];
    machine.register_effect_family_path(tick_path);
    let lower = machine.alloc_pos(Pos::Con(vec!["tick".into()], Vec::new()));
    let inner = machine.alloc_neg(Neg::Top);
    let upper = machine.alloc_neg(Neg::Stack {
        inner,
        weight: StackWeight::push(SubtractId(0), Subtractability::Empty),
    });

    machine.subtype(lower, upper);

    assert!(
        !machine
            .events()
            .iter()
            .any(|event| matches!(event, ConstraintEvent::EffectFilterViolation { .. })),
        "events: {:?}",
        machine.events()
    );
}

#[test]
fn neg_stack_filter_is_checked_but_not_stored_as_right_weight() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let target = TypeVar(1);
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let target_neg = machine.alloc_neg(Neg::Var(target));
    let filter = Subtractability::Set(vec!["io".into()], Vec::new());
    let upper = machine.alloc_neg(Neg::Stack {
        inner: target_neg,
        weight: StackWeight::filter(filter.clone()),
    });
    machine.subtype(source_pos, upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: source_pos,
        upper: target_neg,
        weights: ConstraintWeights::empty(),
    }));
    assert!(machine.seen.iter().all(|constraint| {
        constraint.upper != target_neg || constraint.weights.right.is_empty()
    }));
}

pub(super) fn single_upper_row_tail(
    machine: &ConstraintMachine,
    var: TypeVar,
    expected_paths: &[&str],
) -> TypeVar {
    let bounds = machine.bounds().of(var).expect("source bounds");
    assert_eq!(bounds.uppers().len(), 1);
    let upper = &bounds.uppers()[0];
    assert_eq!(upper.weights, ConstraintWeights::empty());
    let Neg::Row(items, tail) = machine.types().neg(upper.neg) else {
        panic!(
            "expected row upper bound, got {:?}",
            machine.types().neg(upper.neg)
        );
    };
    assert_neg_item_paths(machine, items, expected_paths);
    match machine.types().neg(*tail) {
        Neg::Var(tail) => *tail,
        other => panic!("expected row tail var, got {other:?}"),
    }
}

pub(super) fn assert_single_weighted_upper_var(
    machine: &ConstraintMachine,
    var: TypeVar,
    expected: TypeVar,
    expected_weights: ConstraintWeights,
) {
    let bounds = machine.bounds().of(var).expect("gamma bounds");
    assert_eq!(bounds.uppers().len(), 1);
    let upper = &bounds.uppers()[0];
    assert_eq!(upper.weights, expected_weights);
    match machine.types().neg(upper.neg) {
        Neg::Var(found) if *found == expected => {}
        other => panic!("expected weighted upper var {expected:?}, got {other:?}"),
    }
}

pub(super) fn residual_stack_weight(
    id: SubtractId,
    subtractability: Subtractability,
) -> LeftConstraintWeight {
    LeftConstraintWeight::push(id, subtractability)
}

fn assert_weighted_upper_var(
    machine: &ConstraintMachine,
    var: TypeVar,
    expected: TypeVar,
    expected_weights: ConstraintWeights,
) {
    let bounds = machine.bounds().of(var).expect("gamma bounds");
    assert!(
        bounds.uppers().iter().any(|upper| {
            upper.weights == expected_weights
                && matches!(machine.types().neg(upper.neg), Neg::Var(found) if *found == expected)
        }),
        "expected weighted upper var {expected:?}"
    );
}

fn find_empty_weight_row_tail(
    machine: &ConstraintMachine,
    source: TypeVar,
    expected_paths: &[&str],
    expected_weighted_upper: TypeVar,
) -> TypeVar {
    let bounds = machine.bounds().of(source).expect("source bounds");
    bounds
        .uppers()
        .iter()
        .find_map(|upper| {
            if upper.weights != ConstraintWeights::empty() {
                return None;
            }
            let Neg::Row(items, tail) = machine.types().neg(upper.neg) else {
                return None;
            };
            if !neg_item_paths_match(machine, items, expected_paths) {
                return None;
            }
            let Neg::Var(gamma) = machine.types().neg(*tail) else {
                return None;
            };
            let gamma_bounds = machine.bounds().of(*gamma)?;
            gamma_bounds
                .uppers()
                .iter()
                .any(|upper| {
                    upper.weights != ConstraintWeights::empty()
                        && matches!(
                            machine.types().neg(upper.neg),
                            Neg::Var(found) if *found == expected_weighted_upper
                        )
                })
                .then_some(*gamma)
        })
        .expect("row residual tail")
}

fn assert_neg_item_paths(machine: &ConstraintMachine, items: &[NegId], expected: &[&str]) {
    assert!(
        neg_item_paths_match(machine, items, expected),
        "row item paths did not match"
    );
}

fn neg_item_paths_match(machine: &ConstraintMachine, items: &[NegId], expected: &[&str]) -> bool {
    let mut found = Vec::new();
    for item in items {
        match machine.types().neg(*item) {
            Neg::Con(path, _) => found.push(path.join("::")),
            _ => return false,
        }
    }
    found
        == expected
            .iter()
            .map(|path| (*path).to_string())
            .collect::<Vec<_>>()
}

#[test]
fn pure_function_argument_effect_passes_to_return_effect() {
    let mut machine = ConstraintMachine::new();
    let lhs_arg = machine.alloc_neg(Neg::Con(vec!["lhs_arg".into()], vec![]));
    let lhs_arg_eff = machine.alloc_neg(Neg::Bot);
    let lhs_ret_eff = machine.alloc_pos(Pos::Con(vec!["lhs_ret_eff".into()], vec![]));
    let lhs_ret = machine.alloc_pos(Pos::Con(vec!["lhs_ret".into()], vec![]));
    let lower = machine.alloc_pos(Pos::Fun {
        arg: lhs_arg,
        arg_eff: lhs_arg_eff,
        ret_eff: lhs_ret_eff,
        ret: lhs_ret,
    });

    let rhs_arg = machine.alloc_pos(Pos::Con(vec!["rhs_arg".into()], vec![]));
    let rhs_arg_eff = machine.alloc_pos(Pos::Con(vec!["rhs_arg_eff".into()], vec![]));
    let rhs_ret_eff = machine.alloc_neg(Neg::Con(vec!["rhs_ret_eff".into()], vec![]));
    let rhs_ret = machine.alloc_neg(Neg::Con(vec!["rhs_ret".into()], vec![]));
    let upper = machine.alloc_neg(Neg::Fun {
        arg: rhs_arg,
        arg_eff: rhs_arg_eff,
        ret_eff: rhs_ret_eff,
        ret: rhs_ret,
    });

    machine.subtype(lower, upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: rhs_arg_eff,
        upper: rhs_ret_eff,
        weights: ConstraintWeights::empty(),
    }));
}

#[test]
fn pure_function_argument_effect_passes_through_with_right_side_weights() {
    let mut machine = ConstraintMachine::new();
    let lhs_arg = machine.alloc_neg(Neg::Var(TypeVar(0)));
    let lhs_arg_eff = machine.alloc_neg(Neg::Bot);
    let lhs_ret_eff = machine.alloc_pos(Pos::Var(TypeVar(1)));
    let lhs_ret = machine.alloc_pos(Pos::Var(TypeVar(2)));
    let lower = machine.alloc_pos(Pos::Fun {
        arg: lhs_arg,
        arg_eff: lhs_arg_eff,
        ret_eff: lhs_ret_eff,
        ret: lhs_ret,
    });

    let rhs_arg = machine.alloc_pos(Pos::Var(TypeVar(3)));
    let rhs_arg_eff = machine.alloc_pos(Pos::Var(TypeVar(4)));
    let rhs_ret_eff = machine.alloc_neg(Neg::Var(TypeVar(5)));
    let rhs_ret = machine.alloc_neg(Neg::Var(TypeVar(6)));
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
    let expected_passthrough_weights = ConstraintWeights {
        left: LeftConstraintWeight::empty(),
        right: RightConstraintWeight::pops(SubtractId(1), 2),
    };
    let unnormalized_passthrough_weights = ConstraintWeights {
        left: LeftConstraintWeight::from_ids([SubtractId(1)]),
        right: RightConstraintWeight::from_ids([SubtractId(1)]),
    };

    machine.weighted_subtype(lower, weights.clone(), upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: rhs_arg_eff,
        upper: rhs_ret_eff,
        weights: expected_passthrough_weights,
    }));
    assert!(!machine.seen.contains(&SubtypeConstraint {
        lower: rhs_arg_eff,
        upper: rhs_ret_eff,
        weights: ConstraintWeights::empty(),
    }));
    assert!(!machine.seen.contains(&SubtypeConstraint {
        lower: rhs_arg_eff,
        upper: rhs_ret_eff,
        weights: unnormalized_passthrough_weights,
    }));
    assert!(!machine.seen.contains(&SubtypeConstraint {
        lower: rhs_arg_eff,
        upper: rhs_ret_eff,
        weights,
    }));
}

#[test]
fn pure_function_argument_effect_passes_outside_return_stack_marker() {
    let mut machine = ConstraintMachine::new();
    let lhs_arg = machine.alloc_neg(Neg::Con(vec!["lhs_arg".into()], vec![]));
    let lhs_arg_eff = machine.alloc_neg(Neg::Bot);
    let lhs_ret_eff = machine.alloc_pos(Pos::Con(vec!["lhs_ret_eff".into()], vec![]));
    let lhs_ret = machine.alloc_pos(Pos::Con(vec!["lhs_ret".into()], vec![]));
    let lower = machine.alloc_pos(Pos::Fun {
        arg: lhs_arg,
        arg_eff: lhs_arg_eff,
        ret_eff: lhs_ret_eff,
        ret: lhs_ret,
    });

    let subtract = SubtractId(0);
    let rhs_arg = machine.alloc_pos(Pos::Con(vec!["rhs_arg".into()], vec![]));
    let rhs_arg_eff = machine.alloc_pos(Pos::Con(vec!["rhs_arg_eff".into()], vec![]));
    let rhs_ret_eff_inner = machine.alloc_neg(Neg::Con(vec!["rhs_ret_eff".into()], vec![]));
    let rhs_ret_eff = machine.alloc_neg(Neg::Stack {
        inner: rhs_ret_eff_inner,
        weight: StackWeight::push(subtract, Subtractability::Empty),
    });
    let rhs_ret = machine.alloc_neg(Neg::Con(vec!["rhs_ret".into()], vec![]));
    let upper = machine.alloc_neg(Neg::Fun {
        arg: rhs_arg,
        arg_eff: rhs_arg_eff,
        ret_eff: rhs_ret_eff,
        ret: rhs_ret,
    });

    machine.subtype(lower, upper);

    assert!(machine.seen.contains(&SubtypeConstraint {
        lower: rhs_arg_eff,
        upper: rhs_ret_eff_inner,
        weights: ConstraintWeights::empty(),
    }));
    assert!(machine.seen.iter().all(|constraint| {
        constraint.upper != rhs_ret_eff_inner || constraint.weights.right.is_empty()
    }));
}

#[test]
fn weighted_var_var_replay_cancels_push_pop_through_var_alias() {
    let mut machine = ConstraintMachine::new();
    let subtract = SubtractId(0);
    let call = TypeVar(0);
    let result = TypeVar(1);
    let outer = TypeVar(2);
    let call_pos = machine.alloc_pos(Pos::Var(call));
    let result_neg = machine.alloc_neg(Neg::Var(result));
    let result_pos = machine.alloc_pos(Pos::Var(result));
    let outer_neg = machine.alloc_neg(Neg::Var(outer));

    machine.weighted_subtype(
        call_pos,
        ConstraintWeights {
            left: LeftConstraintWeight::push(subtract, Subtractability::Empty),
            right: RightConstraintWeight::empty(),
        },
        result_neg,
    );
    machine.weighted_subtype(
        result_pos,
        ConstraintWeights {
            left: LeftConstraintWeight::pop(subtract),
            right: RightConstraintWeight::empty(),
        },
        outer_neg,
    );

    let outer_bounds = machine.bounds().of(outer).expect("outer bounds");
    assert!(outer_bounds.lowers().iter().any(|bound| {
        bound.weights == ConstraintWeights::empty()
            && matches!(machine.types().pos(bound.pos), Pos::Var(var) if *var == call)
    }));
    let call_bounds = machine.bounds().of(call).expect("call bounds");
    assert!(call_bounds.uppers().iter().any(|bound| {
        bound.weights == ConstraintWeights::empty()
            && matches!(machine.types().neg(bound.neg), Neg::Var(var) if *var == outer)
    }));
}
