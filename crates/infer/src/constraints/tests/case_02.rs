use super::*;

#[test]
fn var_to_effect_row_upper_without_stack_weight_keeps_self_tail_row() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], vec![]));
    let tail = machine.alloc_neg(Neg::Var(source));
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Row(vec![io], tail));

    machine.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        lower,
        weights,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        lower,
        weights.clone(),
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        source_pos,
        weights.clone(),
        through_neg,
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.subtype(
        through_pos,
        redo_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.subtype(
        residual_pos,
        result_neg,
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.subtype(
        redo_pos,
        result_neg,
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.subtype(
        result_pos,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.subtype(
        through_pos,
        source_neg,
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.subtype(
        source_pos,
        row_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.subtype(
        residual_pos,
        source_neg,
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.subtype(
        source_pos,
        row_upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.subtype(
        source_pos,
        tail,
        crate::constraints::OriginId::unknown_internal(),
    );

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
            crate::constraints::OriginId::unknown_internal(),
        );
        if row_first {
            machine.subtype(
                source_pos,
                row,
                crate::constraints::OriginId::unknown_internal(),
            );
            machine.subtype(
                source_pos,
                tail,
                crate::constraints::OriginId::unknown_internal(),
            );
        } else {
            machine.subtype(
                source_pos,
                tail,
                crate::constraints::OriginId::unknown_internal(),
            );
            machine.subtype(
                source_pos,
                row,
                crate::constraints::OriginId::unknown_internal(),
            );
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

    machine.subtype(
        sub_row,
        alias_neg,
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.subtype(
        alias_pos,
        source_neg,
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.subtype(
        sub_row,
        source_neg,
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.subtype(
        source_pos,
        row_upper,
        crate::constraints::OriginId::unknown_internal(),
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
    let aggregate = machine
        .row_derivations
        .iter()
        .find(|edge| {
            edge.rule == RowDerivationRule::UnweightedReduction
                && edge
                    .parents
                    .iter()
                    .filter(|parent| matches!(parent, RowDerivationParent::Bound(_)))
                    .count()
                    >= 2
        })
        .expect("unweighted reduction retains every contributing lower record");
    assert!(
        machine.row_derivations.iter().any(|edge| {
            edge.rule == RowDerivationRule::RowItemMatch
                && edge.parents.iter().any(|parent| {
                    matches!(parent, RowDerivationParent::RowDerivation(id)
                        if machine.row_derivations.get(id.0 as usize) == Some(aggregate))
                })
        }),
        "row-item match should point back to the aggregation hyperedge"
    );
}

#[test]
fn unweighted_row_upper_matches_late_lower_against_original_row() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let residual = TypeVar(1);
    let family_path = vec!["effect".into(), "f".into()];
    let initial_family = machine.alloc_pos(Pos::Con(family_path.clone(), Vec::new()));
    let late_family_item = machine.alloc_pos(Pos::Con(family_path.clone(), Vec::new()));
    let late_family = machine.alloc_pos(Pos::Row(vec![late_family_item]));
    let family_upper = machine.alloc_neg(Neg::Con(family_path, Vec::new()));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));
    let origin = crate::constraints::OriginId::unknown_internal();

    machine.subtype(initial_family, source_neg, origin);
    machine.subtype(source_pos, row_upper, origin);
    let before_late = unweighted_row_debug_dump(&machine, source, residual);
    let producer =
        constraint_record_for_key(&machine, source_pos, row_upper, &ConstraintWeights::empty());

    machine.subtype(late_family, source_neg, origin);

    let after_late = unweighted_row_debug_dump(&machine, source, residual);
    assert!(
        !has_lower_family_with_weights(
            &machine,
            residual,
            &["effect", "f"],
            &ConstraintWeights::empty(),
        ),
        "a late family already accepted by the original prefix must not contaminate the residual\n\
         before late lower:\n{before_late}\n\
         after late lower:\n{after_late}"
    );
    let late_record = lower_bound_record(&machine, source, late_family);
    let successor = unweighted_reduction_reaching(
        &machine,
        &[
            RowDerivationParent::Constraint(producer),
            RowDerivationParent::Bound(late_record),
        ],
    );
    assert!(
        constraint_has_row_route_to_original(
            &machine,
            late_family,
            &[&["effect", "f"]],
            residual,
            &ConstraintWeights::empty(),
            successor,
        ),
        "the late matching lower should route to the original row"
    );
    assert!(
        machine.row_derivations.iter().any(|edge| {
            edge.rule == RowDerivationRule::RowItemMatch
                && edge
                    .parents
                    .contains(&RowDerivationParent::RowDerivation(successor))
        }),
        "the late bound should remain traceable through UnweightedReduction/RowItemMatch"
    );
}

#[test]
fn unweighted_row_upper_fixpoint_is_insertion_order_invariant() {
    let all_lowers_before_upper =
        unweighted_row_order_fixpoint(UnweightedRowInsertionOrder::AllLowersBeforeUpper);
    let one_lower_after_upper =
        unweighted_row_order_fixpoint(UnweightedRowInsertionOrder::OneLowerAfterUpper);
    let expected = UnweightedRowOrderFixpoint {
        source_has_only_residual_upper: true,
        residual_lower_families: Vec::new(),
        payload_constraints: [true; 4],
    };

    assert_eq!(
        all_lowers_before_upper, expected,
        "all lowers before the upper should reach the reduced semantic fixpoint"
    );
    assert_eq!(
        one_lower_after_upper, expected,
        "a late lower should reach the same reduced semantic fixpoint"
    );
    assert_eq!(all_lowers_before_upper, one_lower_after_upper);
}

#[test]
#[ignore = "known gap: design §6.6 defers zero-lower UpperFirst until row uppers have structural reduction-eligibility tags"]
fn unweighted_row_upper_zero_initial_lower_upper_first_known_gap() {
    let upper_first = unweighted_row_order_fixpoint(UnweightedRowInsertionOrder::UpperFirst);
    let expected = UnweightedRowOrderFixpoint {
        source_has_only_residual_upper: true,
        residual_lower_families: Vec::new(),
        payload_constraints: [true; 4],
    };

    assert_eq!(
        upper_first, expected,
        "an upper inserted with zero initial lowers should eventually reach the reduced fixpoint; \
         tracked by notes/design/2026-07-29-unweighted-row-reduction-fix.md §6.6"
    );
}

#[test]
fn unweighted_row_upper_routes_unmatched_late_family_to_residual_with_weights() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let residual = TypeVar(1);
    let through = TypeVar(2);
    let subtract = SubtractId(0);
    let initial_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let unmatched_family =
        machine.alloc_pos(Pos::Con(vec!["effect".into(), "g".into()], Vec::new()));
    let family_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let through_neg = machine.alloc_neg(Neg::Var(through));
    let through_pos = machine.alloc_pos(Pos::Var(through));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));
    let unmatched_weights = ConstraintWeights {
        left: LeftConstraintWeight::pop(subtract),
        right: RightConstraintWeight::empty(),
    };
    let origin = crate::constraints::OriginId::unknown_internal();

    machine.subtype(initial_family, source_neg, origin);
    machine.subtype(source_pos, row_upper, origin);
    machine.subtype(unmatched_family, through_neg, origin);
    machine.weighted_subtype(through_pos, unmatched_weights.clone(), source_neg, origin);

    assert!(
        has_lower_alias_with_weights(&machine, residual, through, &unmatched_weights)
            && has_lower_family_with_weights(
                &machine,
                through,
                &["effect", "g"],
                &ConstraintWeights::empty(),
            ),
        "an unmatched late G should reach the residual through its alias with exact lower weights\n{}",
        unweighted_row_debug_dump(&machine, source, residual)
    );
    assert!(
        !has_lower_family_with_weights(
            &machine,
            residual,
            &["effect", "f"],
            &ConstraintWeights::empty(),
        ),
        "the initially matched family should stay out of the residual"
    );
}

#[test]
fn unweighted_row_upper_incrementally_consumes_late_item_from_original_multi_item_row() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let residual = TypeVar(1);
    let initial_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "g".into()], Vec::new()));
    let first_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let second_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "g".into()], Vec::new()));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![first_upper, second_upper], tail));
    let origin = crate::constraints::OriginId::unknown_internal();

    machine.subtype(initial_family, source_neg, origin);
    machine.subtype(source_pos, row_upper, origin);
    let producer =
        constraint_record_for_key(&machine, source_pos, row_upper, &ConstraintWeights::empty());
    let old_reduced_upper =
        upper_bound_record_for_row(&machine, source, &[&["effect", "g"]], residual);

    machine.subtype(late_family, source_neg, origin);

    assert_only_empty_upper_var(&machine, source, residual);
    assert_eq!(
        machine
            .bounds()
            .record(old_reduced_upper)
            .expect("stable old reduced-upper record")
            .state(),
        BoundRecordState::Tombstone,
        "the old [G; rho] materialization must not remain a live replay owner"
    );
    assert!(
        !has_lower_family_with_weights(
            &machine,
            residual,
            &["effect", "g"],
            &ConstraintWeights::empty(),
        ),
        "the incrementally consumed G must not leak to the residual"
    );
    let late_record = lower_bound_record(&machine, source, late_family);
    let successor = unweighted_reduction_reaching(
        &machine,
        &[
            RowDerivationParent::Constraint(producer),
            RowDerivationParent::Bound(late_record),
        ],
    );
    assert!(
        constraint_has_row_route_to_original(
            &machine,
            late_family,
            &[&["effect", "f"], &["effect", "g"]],
            residual,
            &ConstraintWeights::empty(),
            successor,
        ),
        "late G must match the original [F, G; rho], not only [G; rho]"
    );
}

#[test]
fn unweighted_row_upper_incremental_route_registers_reduction_route_claim_parent() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let residual = TypeVar(1);
    let initial_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "g".into()], Vec::new()));
    let first_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let second_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "g".into()], Vec::new()));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![first_upper, second_upper], tail));
    let origin = crate::constraints::OriginId::unknown_internal();

    machine.subtype(initial_family, source_neg, origin);
    machine.subtype(source_pos, row_upper, origin);
    let producer =
        constraint_record_for_key(&machine, source_pos, row_upper, &ConstraintWeights::empty());
    let state = reduction_state_for_source(&machine, source);
    let claim = machine.bounds.reduction_claim_by_state[&state];
    let coverage_root = machine.bounds.upper_replay_claims[claim.0 as usize].coverage_root;
    assert!(
        machine
            .bounds
            .live_coverage_by_root
            .get(&coverage_root)
            .is_some_and(|states| states.contains(&state)),
        "the incremental route starts from a live covered reduction claim"
    );

    machine.subtype(late_family, source_neg, origin);

    let late_record = lower_bound_record(&machine, source, late_family);
    let route_derivation = unweighted_reduction_reaching(
        &machine,
        &[
            RowDerivationParent::Constraint(producer),
            RowDerivationParent::Bound(late_record),
        ],
    );
    let result = constraint_record_for_key(
        &machine,
        late_family,
        row_upper,
        &ConstraintWeights::empty(),
    );
    assert!(
        machine.constraint_records[result.0 as usize]
            .row_derivations
            .contains(&route_derivation),
        "the canonical incremental constraint keeps the exact row-route carrier"
    );
    assert!(
        machine
            .bounds
            .claim_parents_by_constraint
            .get(&result)
            .into_iter()
            .flatten()
            .any(|parent| {
                *parent
                    == ClaimQualifiedParent::ReductionRouteConstraint {
                        parent_claim: claim,
                        derivation: route_derivation,
                    }
            }),
        "the exact incremental row-route carrier must be qualified by its reduction claim"
    );
}

struct MovedRootCollisionFixture {
    machine: ConstraintMachine,
    source_neg: NegId,
    tail: NegId,
    origin: OriginId,
    producer: ConstraintRecordId,
    destination: BoundRecordId,
    root: UpperReplayClaimId,
    displaced: UpperReplayClaimId,
    displaced_record: UpperReplayClaim,
}

fn moved_root_collision_fixture() -> MovedRootCollisionFixture {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let residual = TypeVar(1);
    let initial_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "g".into()], Vec::new()));
    let first_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let second_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "g".into()], Vec::new()));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![first_upper, second_upper], tail));
    let origin = crate::constraints::OriginId::unknown_internal();

    machine.subtype(initial_family, source_neg, origin);
    machine.subtype(source_pos, row_upper, origin);
    let producer =
        constraint_record_for_key(&machine, source_pos, row_upper, &ConstraintWeights::empty());
    let state = reduction_state_for_source(&machine, source);
    let root = machine.bounds.reduction_claim_by_state[&state];

    // The next reduction reuses an exact upper survivor where a qualified parent has already
    // materialized the moving root. The real incremental move below must make the Original root
    // canonical for that reachable `(record, coverage_root)` collision.
    let destination = machine
        .bounds
        .add_upper(
            source,
            tail,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(origin),
        )
        .id;
    let route = machine.intern_row_derivation(
        RowDerivationRule::UnweightedReduction,
        vec![RowDerivationParent::Constraint(producer)],
        Vec::new(),
    );
    machine.constraint_records[producer.0 as usize]
        .row_derivations
        .push(route);
    machine.register_reduction_route_claim_parent(producer, route, root);
    let derived = machine.register_constraint_upper_replay_claims(destination, Some(producer));
    assert_eq!(derived.len(), 1);
    assert_ne!(derived[0], root);
    let displaced = derived[0];
    let displaced_record = machine.bounds.upper_replay_claims[displaced.0 as usize].clone();

    machine.subtype(late_family, source_neg, origin);

    assert_eq!(
        machine.unweighted_row_reduction_records[state.0 as usize]
            .current_reduced_upper
            .record,
        destination,
        "the real incremental row path must move the root into the pre-populated survivor"
    );
    MovedRootCollisionFixture {
        machine,
        source_neg,
        tail,
        origin,
        producer,
        destination,
        root,
        displaced,
        displaced_record,
    }
}

fn assert_upper_record_claim_roots_are_unique(machine: &ConstraintMachine) {
    for (record, claims) in &machine.bounds.claims_by_upper_record {
        let roots = claims
            .iter()
            .map(|claim| machine.bounds.upper_replay_claims[claim.0 as usize].coverage_root)
            .collect::<FxHashSet<_>>();
        assert_eq!(
            roots.len(),
            claims.len(),
            "upper record {record:?} contains two active claims for one coverage root"
        );
    }
}

#[test]
fn unweighted_row_claim_move_displaces_the_same_root_destination_claim() {
    let fixture = moved_root_collision_fixture();
    assert_upper_record_claim_roots_are_unique(&fixture.machine);
    assert_eq!(
        fixture.machine.bounds.claims_by_upper_record[&fixture.destination],
        vec![fixture.root],
        "the Original root replaces, rather than joins, the derived destination claim"
    );
    assert_eq!(
        fixture.machine.bounds.original_claim_by_record_and_producer
            [&(fixture.destination, fixture.producer)],
        fixture.root
    );
    assert!(
        !fixture
            .machine
            .bounds
            .derived_claim_by_record_and_root
            .contains_key(&(fixture.destination, fixture.root))
    );
    assert_eq!(
        fixture.machine.bounds.upper_replay_claims[fixture.displaced.0 as usize],
        fixture.displaced_record,
        "displacement removes only active indexes; historical lineage stays append-only"
    );
}

#[test]
fn non_collision_claim_moves_preserve_unique_roots_across_records() {
    let mut machine = ConstraintMachine::new();
    let upper = machine.alloc_neg(Neg::Var(TypeVar(20)));
    let origin = OriginId::unknown_internal();
    let records = [TypeVar(21), TypeVar(22), TypeVar(23)].map(|owner| {
        machine
            .bounds
            .add_upper(
                owner,
                upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id
    });
    let roots = [0, 1].map(|index| {
        machine
            .original_upper_replay_claim(
                records[index],
                ConstraintRecordId(60_000 + index as u32),
                UpperReplayClaimKind::Direct,
            )
            .claim
    });

    for (claim, destination) in [
        (roots[0], records[2]),
        (roots[1], records[2]),
        (roots[0], records[1]),
        (roots[1], records[1]),
    ] {
        machine.move_upper_replay_claim(claim, destination);
        assert_upper_record_claim_roots_are_unique(&machine);
    }
    assert_eq!(
        machine.bounds.claims_by_upper_record[&records[1]]
            .iter()
            .map(|claim| machine.bounds.upper_replay_claims[claim.0 as usize].coverage_root)
            .collect::<FxHashSet<_>>(),
        roots.into_iter().collect()
    );
}

#[test]
fn replay_after_a_same_root_move_uses_only_the_original_exact_parent() {
    let mut fixture = moved_root_collision_fixture();
    let replay_lower = fixture.machine.alloc_pos(Pos::Var(TypeVar(2)));
    fixture
        .machine
        .subtype(replay_lower, fixture.source_neg, fixture.origin);
    let result = constraint_record_for_key(
        &fixture.machine,
        replay_lower,
        fixture.tail,
        &ConstraintWeights::empty(),
    );
    let replay = fixture.machine.constraint_records[result.0 as usize]
        .replay_derivations
        .iter()
        .copied()
        .find(|replay| replay.upper == fixture.destination)
        .expect("the live reduction route replays against its current upper record");
    let exact_parents = fixture.machine.bounds.claim_parents_by_constraint[&result]
        .iter()
        .filter_map(|parent| match *parent {
            ClaimQualifiedParent::ReplayConstraint {
                parent_claim,
                replay: candidate,
                ..
            } if candidate == replay => Some(parent_claim),
            _ => None,
        })
        .collect::<Vec<_>>();

    assert_eq!(exact_parents, vec![fixture.root]);
    assert!(!exact_parents.contains(&fixture.displaced));
}

#[test]
fn unweighted_row_upper_late_payload_match_generates_invariant_constraints() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let residual = TypeVar(1);
    let initial_payload_pos = machine.alloc_pos(Pos::Var(TypeVar(10)));
    let initial_payload_neg = machine.alloc_neg(Neg::Var(TypeVar(10)));
    let initial_payload = machine.alloc_neu(Neu::Bounds(initial_payload_pos, initial_payload_neg));
    let late_payload_pos = machine.alloc_pos(Pos::Var(TypeVar(11)));
    let late_payload_neg = machine.alloc_neg(Neg::Var(TypeVar(11)));
    let late_payload = machine.alloc_neu(Neu::Bounds(late_payload_pos, late_payload_neg));
    let upper_payload_pos = machine.alloc_pos(Pos::Var(TypeVar(12)));
    let upper_payload_neg = machine.alloc_neg(Neg::Var(TypeVar(12)));
    let upper_payload = machine.alloc_neu(Neu::Bounds(upper_payload_pos, upper_payload_neg));
    let family_path = vec!["effect".into(), "f".into()];
    let initial_family = machine.alloc_pos(Pos::Con(family_path.clone(), vec![initial_payload]));
    let late_family = machine.alloc_pos(Pos::Con(family_path.clone(), vec![late_payload]));
    let family_upper = machine.alloc_neg(Neg::Con(family_path, vec![upper_payload]));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));
    let origin = crate::constraints::OriginId::unknown_internal();

    machine.subtype(initial_family, source_neg, origin);
    machine.subtype(source_pos, row_upper, origin);
    let producer =
        constraint_record_for_key(&machine, source_pos, row_upper, &ConstraintWeights::empty());

    machine.subtype(late_family, source_neg, origin);

    let late_record = lower_bound_record(&machine, source, late_family);
    let successor = unweighted_reduction_reaching(
        &machine,
        &[
            RowDerivationParent::Constraint(producer),
            RowDerivationParent::Bound(late_record),
        ],
    );
    let item_match = row_item_match_from(&machine, successor, family_upper);
    assert_constraint_has_row_derivation(&machine, late_payload_pos, upper_payload_neg, item_match);
    assert_constraint_has_row_derivation(&machine, upper_payload_pos, late_payload_neg, item_match);
    assert!(
        !has_lower_family_with_weights(
            &machine,
            residual,
            &["effect", "f"],
            &ConstraintWeights::empty(),
        ),
        "a payload-bearing family is consumed only together with its invariant constraints"
    );
}

#[test]
fn unweighted_row_upper_matches_alias_routed_and_pop_only_late_lowers() {
    let alias_case_passes = {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(0);
        let alias = TypeVar(1);
        let residual = TypeVar(2);
        let initial_family =
            machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
        let alias_family =
            machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
        let family_upper =
            machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
        let alias_neg = machine.alloc_neg(Neg::Var(alias));
        let alias_pos = machine.alloc_pos(Pos::Var(alias));
        let source_neg = machine.alloc_neg(Neg::Var(source));
        let source_pos = machine.alloc_pos(Pos::Var(source));
        let tail = machine.alloc_neg(Neg::Var(residual));
        let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));
        let origin = crate::constraints::OriginId::unknown_internal();

        machine.subtype(initial_family, source_neg, origin);
        machine.subtype(source_pos, row_upper, origin);
        let producer =
            constraint_record_for_key(&machine, source_pos, row_upper, &ConstraintWeights::empty());
        machine.subtype(alias_family, alias_neg, origin);
        machine.subtype(alias_pos, source_neg, origin);

        let stays_out_of_residual = !has_lower_family_with_weights(
            &machine,
            residual,
            &["effect", "f"],
            &ConstraintWeights::empty(),
        ) && !has_lower_alias_with_weights(
            &machine,
            residual,
            alias,
            &ConstraintWeights::empty(),
        );
        stays_out_of_residual && {
            let alias_record = lower_bound_record(&machine, source, alias_pos);
            let successor = unweighted_reduction_reaching(
                &machine,
                &[
                    RowDerivationParent::Constraint(producer),
                    RowDerivationParent::Bound(alias_record),
                ],
            );
            constraint_has_row_route_to_original(
                &machine,
                alias_pos,
                &[&["effect", "f"]],
                residual,
                &ConstraintWeights::empty(),
                successor,
            )
        }
    };

    let pop_only_case_passes = {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(0);
        let residual = TypeVar(1);
        let through = TypeVar(2);
        let subtract = SubtractId(0);
        let initial_family =
            machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
        let late_family =
            machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
        let family_upper =
            machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
        let through_neg = machine.alloc_neg(Neg::Var(through));
        let through_pos = machine.alloc_pos(Pos::Var(through));
        let source_neg = machine.alloc_neg(Neg::Var(source));
        let source_pos = machine.alloc_pos(Pos::Var(source));
        let tail = machine.alloc_neg(Neg::Var(residual));
        let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));
        let pop_only = ConstraintWeights {
            left: LeftConstraintWeight::pop(subtract),
            right: RightConstraintWeight::empty(),
        };
        let origin = crate::constraints::OriginId::unknown_internal();

        machine.subtype(initial_family, source_neg, origin);
        machine.subtype(source_pos, row_upper, origin);
        let producer =
            constraint_record_for_key(&machine, source_pos, row_upper, &ConstraintWeights::empty());
        machine.subtype(late_family, through_neg, origin);
        machine.weighted_subtype(through_pos, pop_only.clone(), source_neg, origin);

        let stays_out_of_residual =
            !has_lower_alias_with_weights(&machine, residual, through, &pop_only)
                && !has_lower_family_with_weights(
                    &machine,
                    residual,
                    &["effect", "f"],
                    &ConstraintWeights::empty(),
                );
        stays_out_of_residual && {
            let late_record = lower_bound_record(&machine, source, through_pos);
            let successor = unweighted_reduction_reaching(
                &machine,
                &[
                    RowDerivationParent::Constraint(producer),
                    RowDerivationParent::Bound(late_record),
                ],
            );
            constraint_has_row_route_to_original(
                &machine,
                through_pos,
                &[&["effect", "f"]],
                residual,
                &pop_only,
                successor,
            )
        }
    };

    assert!(
        alias_case_passes && pop_only_case_passes,
        "both initial-matching eligibility paths must use the original prefix: \
         alias={alias_case_passes}, pop_only={pop_only_case_passes}"
    );
}

#[test]
fn unweighted_row_upper_replacement_keeps_live_state_and_append_only_provenance() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let residual = TypeVar(1);
    let initial_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let transition_family =
        machine.alloc_pos(Pos::Con(vec!["effect".into(), "g".into()], Vec::new()));
    let late_family_item =
        machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family = machine.alloc_pos(Pos::Row(vec![late_family_item]));
    let first_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let second_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "g".into()], Vec::new()));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![first_upper, second_upper], tail));
    let origin = crate::constraints::OriginId::unknown_internal();

    machine.subtype(initial_family, source_neg, origin);
    let initial_lower_record = lower_bound_record(&machine, source, initial_family);
    machine.subtype(source_pos, row_upper, origin);
    let producer =
        constraint_record_for_key(&machine, source_pos, row_upper, &ConstraintWeights::empty());
    let old_reduced_upper =
        upper_bound_record_for_row(&machine, source, &[&["effect", "g"]], residual);

    machine.subtype(transition_family, source_neg, origin);
    let transition_lower_record = lower_bound_record(&machine, source, transition_family);
    machine.subtype(late_family, source_neg, origin);
    let late_lower_record = lower_bound_record(&machine, source, late_family);

    assert_eq!(
        machine
            .bounds()
            .record(old_reduced_upper)
            .expect("stable replaced reduced-upper record")
            .state(),
        BoundRecordState::Tombstone,
        "replacement must leave the old [G; rho] endpoint as history, not a live owner"
    );
    let live_tail_record = assert_only_empty_upper_var(&machine, source, residual);
    assert_eq!(
        machine
            .bounds()
            .record(live_tail_record)
            .expect("live reduced tail record")
            .state(),
        BoundRecordState::Ordinary,
    );
    assert!(
        !has_lower_family_with_weights(
            &machine,
            residual,
            &["effect", "f"],
            &ConstraintWeights::empty(),
        ) && !has_lower_family_with_weights(
            &machine,
            residual,
            &["effect", "g"],
            &ConstraintWeights::empty(),
        ),
        "matching lowers after replacement must not replay through the tombstoned endpoint"
    );
    let latest = unweighted_reduction_reaching(
        &machine,
        &[
            RowDerivationParent::Constraint(producer),
            RowDerivationParent::Bound(initial_lower_record),
            RowDerivationParent::Bound(transition_lower_record),
            RowDerivationParent::Bound(late_lower_record),
        ],
    );
    assert!(
        constraint_has_row_route_to_original(
            &machine,
            late_family,
            &[&["effect", "f"], &["effect", "g"]],
            residual,
            &ConstraintWeights::empty(),
            latest,
        ),
        "post-replacement matching should retain the original row and latest provenance head"
    );
    assert!(
        machine.row_derivations.iter().any(|edge| {
            edge.rule == RowDerivationRule::RowItemMatch
                && edge
                    .parents
                    .contains(&RowDerivationParent::RowDerivation(latest))
        }),
        "producer, initial lower, transition lower, and late lower should reach RowItemMatch"
    );
}

#[test]
fn unweighted_row_upper_same_producer_merge_remains_covered() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let residual = TypeVar(1);
    let initial_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family_item =
        machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family = machine.alloc_pos(Pos::Row(vec![late_family_item]));
    let family_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));
    let origin = crate::constraints::OriginId::unknown_internal();

    machine.subtype(initial_family, source_neg, origin);
    machine.subtype(source_pos, row_upper, origin);
    let producer =
        constraint_record_for_key(&machine, source_pos, row_upper, &ConstraintWeights::empty());
    let reduced_record = assert_only_empty_upper_var(&machine, source, residual);
    assert_eq!(
        upper_dispositions_for(&machine, source, tail),
        vec![BoundDisposition::Inserted(reduced_record)],
        "initial matching must insert the canonical reduced upper"
    );

    let merge = merge_same_key_upper_proof(
        &mut machine,
        source,
        tail,
        BoundDerivation::Constraint(producer),
    );
    assert_eq!(merge.id, reduced_record);
    assert!(!merge.semantic_changed && merge.provenance_changed);
    let claims = observed_upper_replay_claims(&machine, source, reduced_record);
    assert_eq!(claims.len(), 1, "same-producer proofs must coalesce");
    let reduction_claim = claims[0];
    assert_eq!(reduction_claim.producer, producer);
    assert_eq!(reduction_claim.record, reduced_record);
    assert_eq!(
        reduction_claim.kind,
        ObservedReplayClaimKind::Reduced(reduction_state_for_source(&machine, source))
    );
    assert!(
        reduction_claim.covered,
        "the state token must continue to cover claim {:?}",
        reduction_claim.id
    );
    assert_eq!(
        machine
            .bounds()
            .record(reduced_record)
            .expect("canonical reduced upper")
            .derivations()
            .len(),
        2,
        "the canonical record must retain both proofs without creating another claim"
    );

    let replay_inputs_before = machine.timing().lower_replay_inputs;
    machine.subtype(late_family, source_neg, origin);
    let replay = late_matching_replay_counts(
        &machine,
        source,
        residual,
        late_family,
        row_upper,
        producer,
        replay_inputs_before,
    );

    assert_eq!(
        replay,
        LateMatchingReplayCounts {
            generic: 0,
            incremental_matched: 1,
        },
        "a covered claim must use only the incremental original-row route"
    );
    assert!(
        !has_lower_family_with_weights(
            &machine,
            residual,
            &["effect", "f"],
            &ConstraintWeights::empty(),
        ),
        "a same-producer proof must not make the matched family reach the residual"
    );
}

#[test]
fn unweighted_row_upper_independent_direct_tail_claim_replays() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let residual = TypeVar(1);
    let initial_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family_item =
        machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family = machine.alloc_pos(Pos::Row(vec![late_family_item]));
    let family_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));
    let origin = crate::constraints::OriginId::unknown_internal();

    machine.subtype(initial_family, source_neg, origin);
    machine.subtype(source_pos, tail, origin);
    let direct_producer =
        constraint_record_for_key(&machine, source_pos, tail, &ConstraintWeights::empty());
    machine.subtype(source_pos, row_upper, origin);
    let reduction_producer =
        constraint_record_for_key(&machine, source_pos, row_upper, &ConstraintWeights::empty());
    assert_ne!(
        reduction_producer, direct_producer,
        "the reduced row and direct tail relation need distinct producer roots"
    );
    let reduced_record = assert_only_empty_upper_var(&machine, source, residual);

    let same_producer_merge = merge_same_key_upper_proof(
        &mut machine,
        source,
        tail,
        BoundDerivation::Constraint(reduction_producer),
    );
    assert_eq!(same_producer_merge.id, reduced_record);
    assert!(!same_producer_merge.semantic_changed && same_producer_merge.provenance_changed);
    let claims = observed_upper_replay_claims(&machine, source, reduced_record);
    assert_eq!(
        claims.len(),
        2,
        "one reduced claim and one genuinely direct claim must coexist"
    );
    let reduction_claim = claims
        .iter()
        .find(|claim| claim.producer == reduction_producer)
        .copied()
        .expect("reduction claim");
    let direct_claim = claims
        .iter()
        .find(|claim| claim.producer == direct_producer)
        .copied()
        .expect("direct claim");
    assert_ne!(reduction_claim.id, direct_claim.id);
    assert_eq!(reduction_claim.record, reduced_record);
    assert_eq!(direct_claim.record, reduced_record);
    assert_eq!(
        reduction_claim.kind,
        ObservedReplayClaimKind::Reduced(reduction_state_for_source(&machine, source))
    );
    assert_eq!(direct_claim.kind, ObservedReplayClaimKind::Direct);
    assert!(
        reduction_claim.covered && !direct_claim.covered,
        "coverage must remain claim-local: reduction={reduction_claim:?}, direct={direct_claim:?}"
    );

    let replay_inputs_before = machine.timing().lower_replay_inputs;
    machine.subtype(late_family, source_neg, origin);
    let replay = late_matching_replay_counts(
        &machine,
        source,
        residual,
        late_family,
        row_upper,
        reduction_producer,
        replay_inputs_before,
    );

    assert_eq!(
        replay,
        LateMatchingReplayCounts {
            generic: 1,
            incremental_matched: 1,
        },
        "only the independent direct claim should add generic replay"
    );
    assert!(
        has_lower_family_with_weights(
            &machine,
            residual,
            &["effect", "f"],
            &ConstraintWeights::empty(),
        ),
        "the independent source <: rho constraint must carry late F to rho"
    );
}

#[test]
fn unweighted_row_upper_pins_insert_then_same_key_merge_lifecycle() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let residual = TypeVar(1);
    let initial_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family_item =
        machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family = machine.alloc_pos(Pos::Row(vec![late_family_item]));
    let family_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));
    let origin = crate::constraints::OriginId::unknown_internal();

    machine.subtype(initial_family, source_neg, origin);
    assert_eq!(
        machine
            .bounds()
            .of(source)
            .expect("source has the initial lower")
            .uppers()
            .len(),
        0,
        "the minimized nested lifecycle starts with no ordinary source upper"
    );

    machine.subtype(source_pos, row_upper, origin);
    let producer =
        constraint_record_for_key(&machine, source_pos, row_upper, &ConstraintWeights::empty());
    let reduced_record = assert_only_empty_upper_var(&machine, source, residual);
    assert_eq!(
        upper_dispositions_for(&machine, source, tail),
        vec![BoundDisposition::Inserted(reduced_record)],
        "reduction must materialize R through BoundDisposition::Inserted"
    );
    let before_merge = observed_upper_replay_claims(&machine, source, reduced_record);
    assert_eq!(before_merge.len(), 1);
    let covered_claim = before_merge[0];
    assert_eq!(covered_claim.producer, producer);
    assert!(covered_claim.covered);

    let merge = merge_same_key_upper_proof(
        &mut machine,
        source,
        tail,
        BoundDerivation::Constraint(producer),
    );
    assert_eq!(
        (merge.id, merge.semantic_changed, merge.provenance_changed),
        (reduced_record, false, true),
        "same-key proof merge must preserve R and change provenance only"
    );
    assert_eq!(
        assert_only_empty_upper_var(&machine, source, residual),
        reduced_record,
        "the same-key merge must not change canonical record identity"
    );
    assert_eq!(
        upper_dispositions_for(&machine, source, tail),
        vec![BoundDisposition::Inserted(reduced_record)],
        "the merge must not create a second EquivalentTo/SubsumedBy disposition"
    );
    let after_merge = observed_upper_replay_claims(&machine, source, reduced_record);
    assert_eq!(
        after_merge,
        vec![covered_claim],
        "the same producer must keep the same covered claim ID on R"
    );

    let replay_inputs_before = machine.timing().lower_replay_inputs;
    machine.subtype(late_family, source_neg, origin);
    let replay = late_matching_replay_counts(
        &machine,
        source,
        residual,
        late_family,
        row_upper,
        producer,
        replay_inputs_before,
    );

    assert_eq!(
        replay,
        LateMatchingReplayCounts {
            generic: 0,
            incremental_matched: 1,
        },
        "the confirmed Inserted-to-merge lifecycle must retain claim coverage"
    );
    assert!(
        !has_lower_family_with_weights(
            &machine,
            residual,
            &["effect", "f"],
            &ConstraintWeights::empty(),
        ),
        "late matching F must not be generic-replayed to the residual"
    );
}

#[test]
fn unweighted_row_upper_cross_source_replay_inherits_covered_lineage() {
    let mut machine = ConstraintMachine::new();
    let alpha = TypeVar(0);
    let beta = TypeVar(1);
    let residual = TypeVar(2);
    let origin = crate::constraints::OriginId::unknown_internal();
    let initial_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family_item =
        machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family = machine.alloc_pos(Pos::Row(vec![late_family_item]));
    let family_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let alpha_neg = machine.alloc_neg(Neg::Var(alpha));
    let alpha_pos = machine.alloc_pos(Pos::Var(alpha));
    let beta_pos = machine.alloc_pos(Pos::Var(beta));
    let beta_neg = machine.alloc_neg(Neg::Var(beta));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));

    machine.subtype(initial_family, alpha_neg, origin);
    machine.subtype(alpha_pos, row_upper, origin);
    let root_producer =
        constraint_record_for_key(&machine, alpha_pos, row_upper, &ConstraintWeights::empty());
    let alpha_tail_record = assert_only_empty_upper_var(&machine, alpha, residual);

    let top_arg = machine.alloc_neg(Neg::Top);
    let bottom_arg = machine.alloc_pos(Pos::Bot);
    let top_effect = machine.alloc_neg(Neg::Top);
    let bottom_effect = machine.alloc_pos(Pos::Bot);
    let bottom_return = machine.alloc_pos(Pos::Bot);
    let top_return = machine.alloc_neg(Neg::Top);
    let lower_function = machine.alloc_pos(Pos::Fun {
        arg: top_arg,
        arg_eff: top_effect,
        ret_eff: beta_pos,
        ret: bottom_return,
    });
    let upper_function = machine.alloc_neg(Neg::Fun {
        arg: bottom_arg,
        arg_eff: bottom_effect,
        ret_eff: alpha_neg,
        ret: top_return,
    });
    let ignored_union_branch = machine.alloc_pos(Pos::Bot);
    let nested_union = machine.alloc_pos(Pos::Union(lower_function, ignored_union_branch));

    machine.subtype(nested_union, upper_function, origin);

    let union_parent = constraint_record_for_key(
        &machine,
        nested_union,
        upper_function,
        &ConstraintWeights::empty(),
    );
    let function_parent = constraint_record_for_key(
        &machine,
        lower_function,
        upper_function,
        &ConstraintWeights::empty(),
    );
    let beta_alpha =
        constraint_record_for_key(&machine, beta_pos, alpha_neg, &ConstraintWeights::empty());
    assert_structural_derivation(
        &machine,
        function_parent,
        union_parent,
        StructuralDerivationRule::UnionBranch {
            branch: StructuralIndex::from_usize(0),
        },
    );
    assert_structural_derivation(
        &machine,
        beta_alpha,
        function_parent,
        StructuralDerivationRule::FunctionReturnEffect,
    );

    let beta_alpha_lower = lower_bound_record(&machine, alpha, beta_pos);
    let beta_tail_result =
        constraint_record_for_key(&machine, beta_pos, tail, &ConstraintWeights::empty());
    let replay = exact_replay_derivation(
        &machine,
        beta_tail_result,
        alpha,
        beta_alpha_lower,
        alpha_tail_record,
    );
    let beta_tail_record = upper_bound_record_for_var(&machine, beta, residual);
    assert!(
        machine
            .bounds()
            .record(beta_tail_record)
            .expect("cross-source target upper")
            .derivations()
            .contains(&BoundDerivation::Constraint(beta_tail_result)),
        "the replay result constraint must produce beta's canonical tail upper"
    );
    assert!(
        machine
            .unweighted_row_reductions_by_source
            .get(&beta)
            .is_none(),
        "beta must inherit coverage without owning a reduction state"
    );

    let claims = observed_replay_lineage(&machine);
    let alpha_claim = claims.claim_for(alpha, alpha_tail_record, root_producer);
    let beta_claim = claims.claim_for(beta, beta_tail_record, beta_tail_result);
    assert!(
        alpha_claim.id < beta_claim.id,
        "the originating claim must be older than the replay-derived child"
    );

    machine.subtype(late_family, beta_neg, origin);
    let late_beta_record = lower_bound_record(&machine, beta, late_family);
    let cross_source_generic =
        exact_replay_count(&machine, beta, late_beta_record, beta_tail_record);
    let residual_contaminated = has_lower_family_with_weights(
        &machine,
        residual,
        &["effect", "f"],
        &ConstraintWeights::empty(),
    );

    assert_eq!(
        (
            beta_claim.coverage_root,
            beta_claim.lineage,
            claims.is_covered(beta_claim.id),
            cross_source_generic,
            residual_contaminated,
        ),
        (
            alpha_claim.id,
            ObservedReplayClaimLineage::Derived {
                parent: alpha_claim.id,
                result: beta_tail_result,
                replay,
                depth: 1,
            },
            true,
            0,
            false,
        ),
        "the exact replay edge must carry alpha's covered claim to beta without generic residual replay"
    );
}

#[test]
fn unweighted_row_upper_other_source_same_endpoint_direct_claim_stays_uncovered() {
    let mut machine = ConstraintMachine::new();
    let alpha = TypeVar(0);
    let gamma = TypeVar(1);
    let residual = TypeVar(2);
    let origin = crate::constraints::OriginId::unknown_internal();
    let initial_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family_item =
        machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family = machine.alloc_pos(Pos::Row(vec![late_family_item]));
    let family_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let alpha_neg = machine.alloc_neg(Neg::Var(alpha));
    let alpha_pos = machine.alloc_pos(Pos::Var(alpha));
    let gamma_neg = machine.alloc_neg(Neg::Var(gamma));
    let gamma_pos = machine.alloc_pos(Pos::Var(gamma));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));

    machine.subtype(initial_family, alpha_neg, origin);
    machine.subtype(alpha_pos, row_upper, origin);
    let root_producer =
        constraint_record_for_key(&machine, alpha_pos, row_upper, &ConstraintWeights::empty());
    let alpha_tail_record = assert_only_empty_upper_var(&machine, alpha, residual);

    machine.subtype(gamma_pos, tail, origin);
    let direct_producer =
        constraint_record_for_key(&machine, gamma_pos, tail, &ConstraintWeights::empty());
    assert_ne!(
        direct_producer, root_producer,
        "the direct gamma relation must have its own producer"
    );
    let gamma_tail_record = upper_bound_record_for_var(&machine, gamma, residual);
    assert!(
        !constraint_or_bound_has_replay_parent_upper(
            &machine,
            direct_producer,
            gamma_tail_record,
            alpha_tail_record,
        ),
        "sharing rho must not invent an exact replay edge from alpha's claim"
    );

    let claims = observed_replay_lineage(&machine);
    let alpha_claim = claims.claim_for(alpha, alpha_tail_record, root_producer);
    let gamma_claim = claims.claim_for(gamma, gamma_tail_record, direct_producer);
    assert_eq!(
        (
            gamma_claim.coverage_root,
            gamma_claim.lineage,
            claims.is_covered(gamma_claim.id),
        ),
        (gamma_claim.id, ObservedReplayClaimLineage::Original, false,),
        "an unrelated same-endpoint producer must remain its own uncovered root"
    );
    assert_ne!(
        gamma_claim.coverage_root, alpha_claim.id,
        "endpoint equality alone must not inherit alpha's root"
    );

    machine.subtype(late_family, gamma_neg, origin);
    let late_gamma_record = lower_bound_record(&machine, gamma, late_family);
    assert_eq!(
        exact_replay_count(&machine, gamma, late_gamma_record, gamma_tail_record,),
        1,
        "the independent direct claim must generic-replay its matching lower"
    );
    assert!(
        has_lower_family_with_weights(
            &machine,
            residual,
            &["effect", "f"],
            &ConstraintWeights::empty(),
        ),
        "the independent gamma <: rho relation must carry late F to rho"
    );
}

#[test]
fn unweighted_row_upper_multihop_lineage_root_compresses_without_cycle_growth() {
    let mut machine = ConstraintMachine::new();
    let alpha = TypeVar(0);
    let beta = TypeVar(1);
    let gamma = TypeVar(2);
    let residual = TypeVar(3);
    let origin = crate::constraints::OriginId::unknown_internal();
    let initial_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let family_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let alpha_neg = machine.alloc_neg(Neg::Var(alpha));
    let alpha_pos = machine.alloc_pos(Pos::Var(alpha));
    let beta_pos = machine.alloc_pos(Pos::Var(beta));
    let gamma_pos = machine.alloc_pos(Pos::Var(gamma));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));

    machine.subtype(initial_family, alpha_neg, origin);
    machine.subtype(alpha_pos, row_upper, origin);
    let root_producer =
        constraint_record_for_key(&machine, alpha_pos, row_upper, &ConstraintWeights::empty());
    let alpha_tail_record = assert_only_empty_upper_var(&machine, alpha, residual);

    machine.add_lower_bound(
        alpha,
        beta_pos,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );
    machine.drain();
    let beta_alpha_lower = lower_bound_record(&machine, alpha, beta_pos);
    let beta_tail_result =
        constraint_record_for_key(&machine, beta_pos, tail, &ConstraintWeights::empty());
    let first_replay = exact_replay_derivation(
        &machine,
        beta_tail_result,
        alpha,
        beta_alpha_lower,
        alpha_tail_record,
    );
    let beta_tail_record = upper_bound_record_for_var(&machine, beta, residual);

    machine.add_lower_bound(
        beta,
        gamma_pos,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );
    machine.drain();
    let gamma_beta_lower = lower_bound_record(&machine, beta, gamma_pos);
    let gamma_tail_result =
        constraint_record_for_key(&machine, gamma_pos, tail, &ConstraintWeights::empty());
    let second_replay = exact_replay_derivation(
        &machine,
        gamma_tail_result,
        beta,
        gamma_beta_lower,
        beta_tail_record,
    );
    let gamma_tail_record = upper_bound_record_for_var(&machine, gamma, residual);

    machine.add_lower_bound(
        gamma,
        alpha_pos,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );
    machine.drain();
    let alpha_gamma_lower = lower_bound_record(&machine, gamma, alpha_pos);
    let alpha_tail_result =
        constraint_record_for_key(&machine, alpha_pos, tail, &ConstraintWeights::empty());
    let reverse_replay = exact_replay_derivation(
        &machine,
        alpha_tail_result,
        gamma,
        alpha_gamma_lower,
        gamma_tail_record,
    );
    assert_eq!(
        upper_bound_record_for_var(&machine, alpha, residual),
        alpha_tail_record,
        "the reverse replay must return to the existing canonical root target"
    );
    assert!(
        machine.queue.is_empty(),
        "the semantic alpha-beta-gamma cycle must drain without re-enqueue growth"
    );

    let alternate_origin = machine
        .alloc_source_boundary(ConstraintOriginKind::Annotation)
        .origin();
    machine.add_lower_bound(
        gamma,
        alpha_pos,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(alternate_origin),
    );
    machine.drain();
    assert!(
        machine.queue.is_empty(),
        "a proof-only merge on the reverse edge must also leave the queue drained"
    );

    let claims = observed_replay_lineage(&machine);
    let alpha_claim = claims.claim_for(alpha, alpha_tail_record, root_producer);
    let beta_claim = claims.claim_for(beta, beta_tail_record, beta_tail_result);
    let gamma_claim = claims.claim_for(gamma, gamma_tail_record, gamma_tail_result);
    assert!(
        alpha_claim.id < beta_claim.id && beta_claim.id < gamma_claim.id,
        "each replay hop must allocate a child after its parent"
    );

    assert_eq!(
        (
            beta_claim.coverage_root,
            beta_claim.lineage,
            claims.is_covered(beta_claim.id),
            gamma_claim.coverage_root,
            gamma_claim.lineage,
            claims.is_covered(gamma_claim.id),
            claims.metrics_for_root(alpha_claim.id),
        ),
        (
            alpha_claim.id,
            ObservedReplayClaimLineage::Derived {
                parent: alpha_claim.id,
                result: beta_tail_result,
                replay: first_replay,
                depth: 1,
            },
            true,
            alpha_claim.id,
            ObservedReplayClaimLineage::Derived {
                parent: beta_claim.id,
                result: gamma_tail_result,
                replay: second_replay,
                depth: 2,
            },
            true,
            ObservedReplayLineageMetrics {
                claim_count: 3,
                maximum_depth: 2,
                cycle_coalesces: 1,
            },
        ),
        "two hops must root-compress directly to alpha; reverse replay {reverse_replay:?} must coalesce once"
    );
}

#[test]
fn unweighted_row_upper_initial_unmatched_route_inherits_reduction_root() {
    let mut machine = ConstraintMachine::new();
    let alpha = TypeVar(0);
    let beta = TypeVar(1);
    let residual = TypeVar(2);
    let origin = crate::constraints::OriginId::unknown_internal();
    let initial_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family_item =
        machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let late_family = machine.alloc_pos(Pos::Row(vec![late_family_item]));
    let family_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let alpha_neg = machine.alloc_neg(Neg::Var(alpha));
    let alpha_pos = machine.alloc_pos(Pos::Var(alpha));
    let beta_pos = machine.alloc_pos(Pos::Var(beta));
    let beta_neg = machine.alloc_neg(Neg::Var(beta));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));

    machine.subtype(initial_family, alpha_neg, origin);
    machine.subtype(beta_pos, alpha_neg, origin);
    machine.subtype(alpha_pos, row_upper, origin);

    let root_producer =
        constraint_record_for_key(&machine, alpha_pos, row_upper, &ConstraintWeights::empty());
    let alpha_tail_record = assert_only_empty_upper_var(&machine, alpha, residual);
    let beta_tail_result =
        constraint_record_for_key(&machine, beta_pos, tail, &ConstraintWeights::empty());
    let beta_tail_record = upper_bound_record_for_var(&machine, beta, residual);
    let route_derivation = machine.constraint_records[beta_tail_result.0 as usize]
        .row_derivations
        .iter()
        .copied()
        .find(|derivation| {
            machine.row_derivations[derivation.0 as usize].rule
                == RowDerivationRule::UnweightedReduction
        })
        .expect("the initial unmatched route retains the aggregate row derivation");
    assert!(
        machine.constraint_records[beta_tail_result.0 as usize]
            .replay_derivations
            .is_empty(),
        "the first-party reduction route does not require binary replay lineage"
    );
    assert!(
        machine
            .unweighted_row_reductions_by_source
            .get(&beta)
            .is_none(),
        "beta receives a routed claim without owning a reduction state"
    );

    let claims = observed_replay_lineage(&machine);
    let alpha_claim = claims.claim_for(alpha, alpha_tail_record, root_producer);
    let beta_claim = claims.claim_for(beta, beta_tail_record, beta_tail_result);
    assert_eq!(
        (
            beta_claim.coverage_root,
            beta_claim.lineage,
            claims.is_covered(beta_claim.id),
        ),
        (
            alpha_claim.id,
            ObservedReplayClaimLineage::ReductionRoute {
                parent: alpha_claim.id,
                result: beta_tail_result,
                derivation: route_derivation,
                depth: 1,
            },
            true,
        ),
        "the unmatched route must self-tag its child at admission"
    );

    machine.subtype(late_family, beta_neg, origin);
    let late_beta_record = lower_bound_record(&machine, beta, late_family);
    assert_eq!(
        exact_replay_count(&machine, beta, late_beta_record, beta_tail_record),
        0,
        "the covered routed claim must not generic-replay beta's matching family"
    );
    assert!(
        !has_reachable_scheme_projectable_lower_family_with_weights(
            &machine,
            residual,
            &["effect", "f"],
            &ConstraintWeights::empty(),
        ),
        "beta's matching family must stay out of the residual, including through routed aliases"
    );
}

#[test]
fn covered_unmatched_route_lower_is_raw_but_not_scheme_projectable() {
    let fixture = scheme_projection_unmatched_route_fixture(false);
    let raw = fixture
        .machine
        .bounds()
        .of(fixture.residual)
        .expect("residual raw bounds")
        .generalized_projection_lowers()
        .map(|(record, bound)| (record, bound.clone()))
        .collect::<Vec<_>>();

    assert_eq!(
        raw.iter()
            .filter(|(record, _)| *record == fixture.lower_record)
            .count(),
        1,
        "the covered beta <: residual relation remains one canonical raw lower"
    );
    assert_eq!(
        fixture
            .machine
            .bounds()
            .record(fixture.lower_record)
            .expect("stable raw lower record")
            .state(),
        BoundRecordState::Ordinary,
        "scheme suppression must not tombstone the audit record"
    );
    assert!(
        matches!(
            fixture
                .machine
                .types()
                .pos(raw.iter()
                    .find(|(record, _)| *record == fixture.lower_record)
                    .expect("raw lower endpoint")
                    .1
                    .pos),
            Pos::Var(found) if *found == fixture.beta
        ),
        "the raw endpoint remains beta"
    );
    assert!(
        fixture
            .machine
            .scheme_projectable_lowers(fixture.residual)
            .all(|lower| lower.record != fixture.lower_record),
        "the live covered claim must suppress only the scheme view"
    );
    assert_eq!(
        fixture
            .machine
            .bounds
            .scheme_projection_claims_by_lower_record
            .get(&fixture.lower_record),
        Some(&vec![fixture.covered_claim]),
        "the mirror lower must retain the exact reduction-route claim"
    );
    assert_eq!(
        fixture
            .machine
            .bounds
            .scheme_projection_lower_records_by_root
            .get(&fixture.coverage_root),
        Some(&vec![fixture.lower_record]),
        "the compressed root reverse index must identify the affected raw record"
    );
}

#[test]
fn scheme_projectable_lower_keeps_only_independent_claim_on_mixed_record() {
    let fixture = scheme_projection_unmatched_route_fixture(true);
    let direct_claim = fixture
        .direct_claim
        .expect("mixed fixture has an independent direct claim");
    let raw_records = fixture
        .machine
        .bounds()
        .of(fixture.residual)
        .expect("residual raw bounds")
        .generalized_projection_lowers()
        .filter(|(record, _)| *record == fixture.lower_record)
        .count();
    let projected = fixture
        .machine
        .scheme_projectable_lowers(fixture.residual)
        .filter(|lower| lower.record == fixture.lower_record)
        .collect::<Vec<_>>();

    assert_eq!(raw_records, 1, "the semantic lower key stays canonical");
    assert_eq!(
        projected.len(),
        1,
        "mixed claims must project their endpoint once, not once per claim"
    );
    assert_eq!(
        projected[0].reason,
        SchemeProjectableLowerReason::Qualified {
            uncovered_claims: vec![direct_claim],
            independent_supports: Vec::new(),
        },
        "only the independent direct claim may justify scheme projection"
    );
    let [direct_root, covered_root] = [direct_claim, fixture.covered_claim]
        .map(|claim| fixture.machine.bounds.upper_replay_claims[claim.0 as usize].coverage_root);
    assert!(
        direct_root < covered_root,
        "the pinned claim order follows the ascending coverage-root canonical key"
    );
    assert_eq!(
        fixture
            .machine
            .bounds
            .scheme_projection_claims_by_lower_record
            .get(&fixture.lower_record),
        Some(&vec![direct_claim, fixture.covered_claim]),
        "the canonical mirror lower must retain both claim identities"
    );
}

#[test]
fn scheme_projection_empty_to_nonempty_live_coverage_publishes_inclusion_mutation() {
    let mut fixture = scheme_projection_unmatched_route_fixture(false);
    assert!(
        fixture
            .machine
            .remove_scheme_projection_live_coverage_state(
                fixture.coverage_root,
                fixture.coverage_state,
            ),
        "the setup makes the covered claim projectable again"
    );
    assert!(
        fixture
            .machine
            .scheme_projectable_lowers(fixture.residual)
            .any(|lower| lower.record == fixture.lower_record),
        "the empty root starts included in the scheme view"
    );
    let constraint_epoch_before = fixture.machine.epoch();
    let owner_epoch_before = fixture
        .machine
        .bounds()
        .of(fixture.residual)
        .expect("residual owner epoch before reinsertion")
        .epoch();
    let provenance_epoch_before = fixture.machine.provenance_epoch();
    let journal = fixture.machine.activate_method_role_mutations();

    assert!(
        fixture
            .machine
            .insert_scheme_projection_live_coverage_state(
                fixture.coverage_root,
                fixture.coverage_state,
            ),
        "reinserting the first live state changes the root from empty to non-empty"
    );

    let owner_epoch_after = fixture
        .machine
        .bounds()
        .of(fixture.residual)
        .expect("residual owner epoch after reinsertion")
        .epoch();
    assert!(
        fixture
            .machine
            .scheme_projectable_lowers(fixture.residual)
            .all(|lower| lower.record != fixture.lower_record),
        "the first live state makes the covered-only relation non-projectable"
    );
    assert!(
        fixture.machine.epoch() > constraint_epoch_before
            && owner_epoch_after > owner_epoch_before
            && fixture.machine.provenance_epoch() > provenance_epoch_before,
        "empty-to-non-empty coverage must advance constraint, owner, and provenance epochs"
    );
    assert_eq!(
        owner_epoch_after,
        fixture.machine.epoch(),
        "the affected owner's epoch follows the global inclusion mutation"
    );
    assert!(
        has_constraint_bounds_mutation(
            &fixture.machine.take_method_role_mutations(),
            fixture.residual,
        ),
        "empty-to-non-empty coverage publishes the affected owner dependency"
    );
    journal.finish();
}

#[test]
fn covered_claim_link_publishes_projectable_to_non_projectable_mutation() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let owner = TypeVar(1);
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Var(owner));
    let origin = OriginId::unknown_internal();
    assert!(machine.enqueue_root_subtype(
        lower,
        ConstraintWeights::empty(),
        upper,
        origin,
    ));
    let producer = machine
        .constraint_record_id(lower, ConstraintWeights::empty(), upper)
        .expect("the claim-link producer is admitted before its bounds are materialized");
    let upper_record = machine
        .bounds
        .add_upper(
            source,
            upper,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(producer),
        )
        .id;
    let provenance = machine.intern_row_derivation(
        RowDerivationRule::UnweightedReduction,
        vec![RowDerivationParent::Constraint(producer)],
        Vec::new(),
    );
    let (state, root_claim) = machine.register_unweighted_row_reduction_for_test(
        UnweightedRowReductionRecord {
            source,
            producer_constraint: Some(producer),
            original_items: Vec::new(),
            original_tail: upper,
            original_upper: upper,
            consumed_items: Vec::new(),
            remaining_items: Vec::new(),
            current_reduced_upper: UnweightedRowReductionMaterialization {
                endpoint: upper,
                record: upper_record,
            },
            processed_lower_records: FxHashSet::default(),
            provenance_head: provenance,
        },
    );
    let claim = root_claim.expect("the admitted reduction owns a live coverage root");
    assert_eq!(
        machine.bounds.upper_replay_claims[claim.0 as usize].kind,
        UpperReplayClaimKind::Reduced(state),
        "production reduction admission creates the covered claim before its mirror lower"
    );
    let lower_record = machine
        .bounds
        .add_lower(
            owner,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(producer),
        )
        .id;
    let before_link = machine
        .scheme_projectable_lowers(owner)
        .find(|candidate| candidate.record == lower_record)
        .map(|candidate| candidate.reason);
    assert!(
        machine.proof_terminal_failure().is_none(),
        "the well-formed reduction fixture must not fail CPK projection evaluation before linking"
    );
    assert_eq!(
        before_link,
        Some(SchemeProjectableLowerReason::Unclaimed),
        "before linking, the active mirror lower remains projectable"
    );
    let constraint_epoch_before = machine.epoch();
    let owner_epoch_before = machine
        .bounds()
        .of(owner)
        .expect("mirror lower owner")
        .epoch();
    let provenance_epoch_before = machine.provenance_epoch();
    let journal = machine.activate_method_role_mutations();

    assert_eq!(
        machine.register_constraint_upper_replay_claims(upper_record, Some(producer)),
        vec![claim],
        "constraint-claim registration reuses the covered canonical claim"
    );

    let owner_epoch_after = machine
        .bounds()
        .of(owner)
        .expect("mirror lower owner after claim link")
        .epoch();
    let remains_projectable = machine
        .scheme_projectable_lowers(owner)
        .any(|candidate| candidate.record == lower_record);
    assert!(
        machine.proof_terminal_failure().is_none(),
        "claim-link exclusion must be a successful CPK decision, not an empty failed query"
    );
    assert!(
        !remains_projectable,
        "linking the live covered claim changes the record to non-projectable"
    );
    assert!(
        machine.epoch() > constraint_epoch_before
            && owner_epoch_after > owner_epoch_before
            && machine.provenance_epoch() > provenance_epoch_before,
        "claim-link inclusion changes advance constraint, owner, and provenance epochs"
    );
    assert_eq!(
        owner_epoch_after,
        machine.epoch(),
        "the linked lower owner's epoch follows the global inclusion mutation"
    );
    assert!(
        has_constraint_bounds_mutation(&machine.take_method_role_mutations(), owner),
        "claim-link inclusion changes publish the linked lower owner dependency"
    );
    journal.finish();
}

#[test]
fn scheme_projectability_returns_after_last_live_coverage_state_leaves() {
    let mut fixture = scheme_projection_unmatched_route_fixture(false);
    let raw_before = fixture
        .machine
        .bounds()
        .of(fixture.residual)
        .expect("residual raw bounds")
        .generalized_projection_lowers()
        .map(|(record, bound)| (record, bound.clone()))
        .collect::<Vec<_>>();
    assert!(
        fixture
            .machine
            .scheme_projectable_lowers(fixture.residual)
            .all(|lower| lower.record != fixture.lower_record),
        "the live state initially covers the only linked claim"
    );
    let constraint_epoch_before = fixture.machine.epoch();
    let owner_epoch_before = fixture
        .machine
        .bounds()
        .of(fixture.residual)
        .expect("residual owner epoch")
        .epoch();
    let provenance_epoch_before = fixture.machine.provenance_epoch();
    let journal = fixture.machine.activate_method_role_mutations();

    assert!(
        fixture
            .machine
            .remove_scheme_projection_live_coverage_state(
                fixture.coverage_root,
                fixture.coverage_state,
            ),
        "the fixture removes the root's last live state through the lifecycle primitive"
    );

    let raw_after = fixture
        .machine
        .bounds()
        .of(fixture.residual)
        .expect("residual raw bounds after liveness transition")
        .generalized_projection_lowers()
        .map(|(record, bound)| (record, bound.clone()))
        .collect::<Vec<_>>();
    let projected = fixture
        .machine
        .scheme_projectable_lowers(fixture.residual)
        .find(|lower| lower.record == fixture.lower_record)
        .expect("the uncovered raw relation becomes projectable again");
    let owner_epoch_after = fixture
        .machine
        .bounds()
        .of(fixture.residual)
        .expect("residual owner epoch after transition")
        .epoch();

    assert_eq!(
        raw_after, raw_before,
        "liveness changes projection metadata, never the raw lower relation"
    );
    assert_eq!(
        projected.reason,
        SchemeProjectableLowerReason::Qualified {
            uncovered_claims: vec![fixture.covered_claim],
            independent_supports: Vec::new(),
        },
        "the formerly covered claim is re-evaluated at projection time"
    );
    assert!(
        fixture.machine.epoch() > constraint_epoch_before
            && owner_epoch_after > owner_epoch_before
            && fixture.machine.provenance_epoch() > provenance_epoch_before,
        "constraint, owner, and provenance epochs must all advance"
    );
    assert_eq!(
        owner_epoch_after,
        fixture.machine.epoch(),
        "the affected owner's projection epoch follows the global mutation epoch"
    );
    assert!(
        has_constraint_bounds_mutation(
            &fixture.machine.take_method_role_mutations(),
            fixture.residual,
        ),
        "non-empty-to-empty coverage still publishes the affected owner dependency"
    );
    journal.finish();
}

#[test]
fn second_live_coverage_state_bumps_only_provenance_epoch() {
    let mut fixture = scheme_projection_unmatched_route_fixture(false);
    let second_state = UnweightedRowReductionRecordId(
        fixture
            .coverage_state
            .0
            .checked_add(1)
            .expect("test state ID remains representable"),
    );
    let constraint_epoch_before = fixture.machine.epoch();
    let owner_epoch_before = fixture
        .machine
        .bounds()
        .of(fixture.residual)
        .expect("residual owner before second live state")
        .epoch();
    let provenance_epoch_before = fixture.machine.provenance_epoch();
    let journal = fixture.machine.activate_method_role_mutations();

    assert!(
        fixture
            .machine
            .insert_scheme_projection_live_coverage_state(fixture.coverage_root, second_state),
        "a distinct second live state changes liveness metadata"
    );

    assert_eq!(
        fixture.machine.epoch(),
        constraint_epoch_before,
        "non-empty-to-non-empty coverage must not invalidate compact inclusion"
    );
    assert_eq!(
        fixture
            .machine
            .bounds()
            .of(fixture.residual)
            .expect("residual owner after second live state")
            .epoch(),
        owner_epoch_before,
        "the owner epoch stays unchanged when inclusion stays non-projectable"
    );
    assert!(
        fixture.machine.provenance_epoch() > provenance_epoch_before,
        "the added live member still advances provenance metadata"
    );
    assert!(
        fixture.machine.take_method_role_mutations().is_empty(),
        "provenance-only liveness changes do not publish bounds dependencies"
    );
    journal.finish();
}

#[test]
fn ordinary_scheme_projectable_lowers_are_byte_for_byte_raw_passthrough() {
    let mut machine = ConstraintMachine::new();
    let owner = TypeVar(0);
    let ordinary = machine.alloc_pos(Pos::Con(
        vec!["effect".into(), "ordinary".into()],
        Vec::new(),
    ));
    let evidence = machine.alloc_pos(Pos::Con(
        vec!["effect".into(), "evidence".into()],
        Vec::new(),
    ));
    let origin = crate::constraints::OriginId::unknown_internal();

    machine.bounds.add_lower(
        owner,
        ordinary,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );
    machine.bounds.add_evidence_lower(
        owner,
        evidence,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );

    let raw = machine
        .bounds()
        .of(owner)
        .expect("ordinary owner raw bounds")
        .generalized_projection_lowers()
        .map(|(record, bound)| (record, bound.clone()))
        .collect::<Vec<_>>();
    let projected = machine
        .scheme_projectable_lowers(owner)
        .map(|lower| (lower.record, lower.bound.clone(), lower.reason))
        .collect::<Vec<_>>();

    assert!(
        !machine
            .bounds
            .scheme_projection_claimed_lower_owners
            .contains(&owner),
        "ordinary lower records stay on the no-claim fast path"
    );
    assert_eq!(
        projected.len(),
        raw.len(),
        "the view must preserve every raw record"
    );
    for ((projected_record, projected_bound, reason), (raw_record, raw_bound)) in
        projected.iter().zip(&raw)
    {
        assert_eq!(
            (projected_record, projected_bound),
            (raw_record, raw_bound),
            "record identity, evidence/ordinary ordering, endpoint, and weights must pass through"
        );
        assert_eq!(reason, &SchemeProjectableLowerReason::Unclaimed);
    }
}

#[test]
fn unweighted_row_upper_weighted_residual_route_stays_uncovered() {
    let mut machine = ConstraintMachine::new();
    let gamma = TypeVar(0);
    let residual = TypeVar(1);
    let origin = crate::constraints::OriginId::unknown_internal();
    let gamma_pos = machine.alloc_pos(Pos::Var(gamma));
    let gamma_neg = machine.alloc_neg(Neg::Var(gamma));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let derivation = machine.intern_row_derivation(
        RowDerivationRule::WeightedResidual,
        vec![RowDerivationParent::Origin(origin)],
        Vec::new(),
    );

    machine.enqueue_row_derived_subtype(gamma_pos, ConstraintWeights::empty(), tail, derivation);
    machine.drain();

    let result = constraint_record_for_key(&machine, gamma_pos, tail, &ConstraintWeights::empty());
    assert!(
        machine.constraint_records[result.0 as usize]
            .row_derivations
            .contains(&derivation),
        "the shared row-derived admission retains its exact row proof"
    );
    let record = upper_bound_record_for_var(&machine, gamma, residual);
    let claims = observed_replay_lineage(&machine);
    let claim = claims.claim_for(gamma, record, result);
    assert_eq!(
        (
            claim.coverage_root,
            claim.lineage,
            claims.is_covered(claim.id),
        ),
        (claim.id, ObservedReplayClaimLineage::Original, false),
        "an unrelated WeightedResidual route must remain an uncovered root"
    );

    let late_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    machine.subtype(late_family, gamma_neg, origin);
    let late_record = lower_bound_record(&machine, gamma, late_family);
    assert_eq!(
        exact_replay_count(&machine, gamma, late_record, record),
        1,
        "the unrelated row-derived claim must generic-replay"
    );
    assert!(
        has_lower_family_with_weights(
            &machine,
            residual,
            &["effect", "f"],
            &ConstraintWeights::empty(),
        ),
        "the uncovered gamma <: rho relation must carry F to rho"
    );
}

#[test]
fn dcp_a_8_1_replay_inherits_claim_from_exact_lower_parent() {
    let mut fixture = scheme_projection_unmatched_route_fixture(false);
    let pivot = fixture.residual;
    let lower_record = fixture.lower_record;
    let lower = lower_endpoint(&fixture.machine, lower_record);
    let pivot_pos = fixture.machine.alloc_pos(Pos::Var(pivot));
    let target = TypeVar(3);
    let upper = fixture.machine.alloc_neg(Neg::Var(target));
    let origin = OriginId::unknown_internal();

    fixture.machine.subtype(pivot_pos, upper, origin);

    let upper_record = upper_bound_record(&fixture.machine, pivot, upper);
    let result =
        constraint_record_for_key(&fixture.machine, lower, upper, &ConstraintWeights::empty());
    let replay =
        exact_replay_derivation(&fixture.machine, result, pivot, lower_record, upper_record);
    let parents = observed_replay_claim_parents(&fixture.machine, result, replay);

    assert_eq!(
        replay.lower, lower_record,
        "the replay keeps the exact lower carrier"
    );
    assert_eq!(
        exact_replay_count(&fixture.machine, pivot, lower_record, upper_record),
        1,
        "claim accounting must not multiply the semantic replay"
    );
    assert!(
        parents.iter().any(|parent| {
            parent.side == ObservedReplayParentSide::Lower
                && parent.claim == fixture.covered_claim
                && parent.coverage_root == fixture.coverage_root
        }),
        "the result must inherit the covered root through replay.lower = {lower_record:?}; observed {parents:?}"
    );
}

#[test]
fn dcp_a_8_2_replay_keeps_existing_upper_side_claim_inheritance() {
    let mut fixture = scheme_projection_unmatched_route_fixture(false);
    let pivot = fixture.beta;
    let lower_var = TypeVar(3);
    let lower = fixture.machine.alloc_pos(Pos::Var(lower_var));
    let upper = fixture.machine.alloc_neg(Neg::Var(fixture.residual));
    let origin = OriginId::unknown_internal();
    let upper_record = upper_bound_record(&fixture.machine, pivot, upper);

    fixture.machine.add_lower_bound(
        pivot,
        lower,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );
    fixture.machine.drain();

    let lower_record = lower_bound_record(&fixture.machine, pivot, lower);
    let result =
        constraint_record_for_key(&fixture.machine, lower, upper, &ConstraintWeights::empty());
    let replay =
        exact_replay_derivation(&fixture.machine, result, pivot, lower_record, upper_record);
    let parents = observed_replay_claim_parents(&fixture.machine, result, replay);

    assert!(
        parents.iter().any(|parent| {
            parent.side == ObservedReplayParentSide::Upper
                && parent.claim == fixture.covered_claim
                && parent.coverage_root == fixture.coverage_root
        }),
        "the existing H1 upper-side path must retain the covered root; observed {parents:?}"
    );
    assert_eq!(
        exact_replay_count(&fixture.machine, pivot, lower_record, upper_record),
        1,
        "upper-side metadata must not duplicate the semantic replay"
    );
}

#[test]
fn dcp_a_8_3_both_replay_sides_remain_independent_on_one_result() {
    let mut fixture = scheme_projection_unmatched_route_fixture(true);
    let independent_claim = fixture
        .direct_claim
        .expect("the mixed lower has its independent uncovered claim");
    let pivot = fixture.residual;
    let lower_record = fixture.lower_record;
    let lower = lower_endpoint(&fixture.machine, lower_record);
    let pivot_pos = fixture.machine.alloc_pos(Pos::Var(pivot));
    let target = TypeVar(3);
    let upper = fixture.machine.alloc_neg(Neg::Var(target));
    let origin = OriginId::unknown_internal();

    fixture.machine.subtype(pivot_pos, upper, origin);

    let upper_record = upper_bound_record(&fixture.machine, pivot, upper);
    let upper_claim = claim_for_upper_record(&fixture.machine, upper_record);
    let result =
        constraint_record_for_key(&fixture.machine, lower, upper, &ConstraintWeights::empty());
    let replay =
        exact_replay_derivation(&fixture.machine, result, pivot, lower_record, upper_record);
    let parents = observed_replay_claim_parents(&fixture.machine, result, replay);
    let expected = [
        (
            ObservedReplayParentSide::Lower,
            fixture.covered_claim,
            fixture.coverage_root,
        ),
        (
            ObservedReplayParentSide::Lower,
            independent_claim,
            claim_root(&fixture.machine, independent_claim),
        ),
        (
            ObservedReplayParentSide::Upper,
            upper_claim,
            claim_root(&fixture.machine, upper_claim),
        ),
    ];

    for (side, claim, coverage_root) in expected {
        let missing = (side, claim, coverage_root);
        assert!(
            parents.iter().any(|parent| {
                parent.side == side
                    && parent.claim == claim
                    && parent.coverage_root == coverage_root
            }),
            "each replay-side proof remains an independent lineage; missing {missing:?} from {parents:?}"
        );
    }
    assert_eq!(
        fixture
            .machine
            .constraint_records
            .iter()
            .filter(|record| record.key.lower == lower && record.key.upper == upper)
            .count(),
        1,
        "three claim parents still qualify one canonical semantic constraint"
    );
    let result_lower = lower_bound_record(&fixture.machine, target, lower);
    assert_eq!(
        fixture
            .machine
            .scheme_projectable_lowers(target)
            .filter(|candidate| candidate.record == result_lower)
            .count(),
        1,
        "uncovered support projects the result endpoint once"
    );
}

#[test]
fn dcp_a_8_4_row_aggregate_child_inherits_exact_structural_claim() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let target = TypeVar(1);
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(target));
    let matched_path = vec!["effect".into(), "matched".into()];
    let marker_path = vec!["effect".into(), "marker".into()];
    machine.register_effect_family_path(matched_path.clone());
    machine.register_effect_family_path(marker_path.clone());
    let matched_upper = machine.alloc_neg(Neg::Con(matched_path.clone(), Vec::new()));
    let upper = machine.alloc_neg(Neg::Row(vec![matched_upper], tail));
    let matched_lower = machine.alloc_pos(Pos::Con(matched_path, Vec::new()));
    let marker_lower = machine.alloc_pos(Pos::Con(marker_path, Vec::new()));
    let lower = machine.alloc_pos(Pos::Row(vec![matched_lower, marker_lower]));
    let origin = OriginId::unknown_internal();

    machine.subtype(source_pos, upper, origin);
    let upper_record = upper_bound_record(&machine, source, upper);
    let parent_claim = claim_for_upper_record(&machine, upper_record);
    machine.add_lower_bound(
        source,
        lower,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );
    machine.drain();

    let lower_record = lower_bound_record(&machine, source, lower);
    let parent = constraint_record_for_key(&machine, lower, upper, &ConstraintWeights::empty());
    let replay = exact_replay_derivation(&machine, parent, source, lower_record, upper_record);
    assert!(
        observed_replay_claim_parents(&machine, parent, replay)
            .iter()
            .any(|candidate| candidate.claim == parent_claim),
        "the row-against-row replay parent starts claim-qualified"
    );
    let rule = StructuralDerivationRule::RowItem {
        index: StructuralIndex::from_usize(1),
        route: RowItemRoute::MarkerAggregateToUpperTail,
    };
    let child = structural_child_for(&machine, parent, rule);
    let derivation = StructuralDerivation { parent, rule };
    assert_eq!(
        exact_structural_carriers(&machine, child)
            .iter()
            .filter(|carrier| **carrier == derivation)
            .count(),
        1,
        "the aggregate child keeps its exact structural carrier"
    );
    let child_claims = observed_structural_claim_parents(&machine, child, derivation);
    assert!(
        child_claims.iter().any(|claim| {
            claim.claim == parent_claim && claim.coverage_root == claim_root(&machine, parent_claim)
        }),
        "the exact structural child must inherit its parent's claim root; observed {child_claims:?}"
    );
    // Stable one-sided lower linkage is DCP-D's admission contract, covered by §8.6 and §8.8.
}

#[test]
fn dcp_a_8_5_non_row_structural_children_use_the_generic_claim_carrier() {
    let ordinary = ordinary_one_sided_row_snapshot();
    assert_eq!(
        (
            ordinary.raw_count,
            ordinary.projected_count,
            ordinary.independent_supports
        ),
        (1, 1, 1),
        "the unclaimed control remains a one-record raw passthrough"
    );

    for shape in [
        NonRowStructuralShape::FunctionReturnEffect,
        NonRowStructuralShape::TupleElement,
    ] {
        let fixture = non_row_structural_claim_fixture(shape);
        assert_eq!(
            exact_structural_carriers(&fixture.machine, fixture.child),
            vec![fixture.derivation],
            "{shape:?} keeps the exact generic structural carrier"
        );
        let child_claims =
            observed_structural_claim_parents(&fixture.machine, fixture.child, fixture.derivation);
        assert!(
            child_claims.iter().any(|claim| {
                claim.claim == fixture.parent_claim
                    && claim.coverage_root == claim_root(&fixture.machine, fixture.parent_claim)
            }),
            "{shape:?} must inherit without a row/effect whitelist; observed {child_claims:?}"
        );
    }
}

#[test]
fn dcp_c_trivial_structural_child_creates_no_claim_parent() {
    let mut fixture = non_row_structural_claim_fixture(NonRowStructuralShape::FunctionReturnEffect);
    let canonical_before = fixture.machine.canonical_constraint_count();
    let claim_parents_before = fixture
        .machine
        .bounds
        .claim_parents_by_constraint
        .values()
        .map(Vec::len)
        .sum::<usize>();
    let bottom = fixture.machine.alloc_pos(Pos::Bot);
    let top = fixture.machine.alloc_neg(Neg::Top);

    assert!(
        !fixture.machine.enqueue_derived_subtype(
            bottom,
            ConstraintWeights::empty(),
            top,
            fixture.child,
            StructuralDerivationRule::FunctionReturn,
        ),
        "a trivial structural consequence has no canonical child"
    );
    assert_eq!(
        fixture.machine.canonical_constraint_count(),
        canonical_before,
        "trivial structural admission creates no canonical constraint"
    );
    assert_eq!(
        fixture
            .machine
            .bounds
            .claim_parents_by_constraint
            .values()
            .map(Vec::len)
            .sum::<usize>(),
        claim_parents_before,
        "trivial structural admission creates no claim entry"
    );
}

#[test]
fn dcp_a_8_6_one_sided_concrete_lower_links_claim_without_var_var_mirror() {
    let mut fixture = one_sided_claim_fixture(false);
    assert!(matches!(
        fixture.machine.types().pos(fixture.lower),
        Pos::Row(_)
    ));
    assert!(matches!(
        fixture.machine.types().neg(fixture.upper),
        Neg::Var(found) if *found == fixture.target
    ));
    assert_eq!(
        fixture
            .machine
            .bounds
            .scheme_projection_lower_record_by_constraint
            .get(&fixture.producer),
        Some(&fixture.lower_record),
        "the producer resolves to its stable one-sided lower record"
    );
    let projection =
        observed_lower_projection(&fixture.machine, fixture.target, fixture.lower_record);
    assert_eq!(
        projection.claimed_roots,
        vec![fixture.coverage_root],
        "stable lower admission must link the producer's exact claim root"
    );
    assert_eq!(
        projection.projected_count, 0,
        "the live covered proof suppresses the one-sided relation"
    );

    assert!(
        fixture
            .machine
            .remove_scheme_projection_live_coverage_state(
                fixture.coverage_root,
                fixture.coverage_state,
            ),
        "the fixture removes the last live state"
    );
    let uncovered =
        observed_lower_projection(&fixture.machine, fixture.target, fixture.lower_record);
    assert_eq!(
        uncovered.projected_count, 1,
        "the same stable raw record becomes projectable after liveness removal"
    );
}

#[test]
fn dcp_a_8_7_independent_same_key_lower_stays_projectable_in_both_orders() {
    let direct_first = one_sided_claim_fixture(true);
    let claimed_first = one_sided_claim_fixture_with_claimed_first_then_direct();
    let direct_snapshot = mixed_one_sided_snapshot(&direct_first);
    let claimed_snapshot = mixed_one_sided_snapshot(&claimed_first);

    assert_eq!(
        direct_snapshot, claimed_snapshot,
        "direct-first and claimed-first preserve the same canonical proof model"
    );
    assert_eq!(
        direct_snapshot,
        MixedOneSidedSnapshot {
            raw_count: 1,
            projected_count: 1,
            independent_supports: 1,
            exact_replay_carriers: 1,
            incomplete_replay: false,
        },
        "the independent direct carrier keeps the endpoint projectable once while the claim path remains separately observable"
    );
}

#[test]
fn dcp_a_8_8_duplicate_evidence_and_promotion_keep_root_and_exact_carrier() {
    let mut fixture = row_structural_claim_fixture();
    let alternate_origin = fixture
        .machine
        .alloc_source_boundary(ConstraintOriginKind::Annotation)
        .origin();
    let child_key = fixture.machine.constraint_records[fixture.child.0 as usize]
        .key
        .clone();
    assert!(
        !fixture.machine.enqueue_derived_subtype(
            child_key.lower,
            child_key.weights.clone(),
            child_key.upper,
            fixture.derivation.parent,
            fixture.derivation.rule,
        ),
        "the second structural admission is a canonical duplicate"
    );
    let replay = fixture.replay;
    let evidence = fixture.machine.bounds.add_evidence_lower(
        fixture.target,
        fixture.lower,
        ConstraintWeights::empty(),
        BoundDerivation::ReplayEvidence(replay),
    );
    assert_eq!(
        evidence.id, fixture.lower_record,
        "evidence-only metadata merges into the canonical lower key"
    );

    let promotion_target = TypeVar(9);
    let promotion_item = fixture.machine.alloc_pos(Pos::Con(
        vec!["effect".into(), "promotion".into()],
        Vec::new(),
    ));
    let promotion_lower = fixture.machine.alloc_pos(Pos::Row(vec![promotion_item]));
    let evidence_only = fixture.machine.bounds.add_evidence_lower(
        promotion_target,
        promotion_lower,
        ConstraintWeights::empty(),
        BoundDerivation::ReplayEvidence(replay),
    );
    let promoted = fixture.machine.bounds.add_lower(
        promotion_target,
        promotion_lower,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(alternate_origin),
    );
    assert_eq!(
        promoted.id, evidence_only.id,
        "ordinary promotion preserves the evidence-only stable lower identity"
    );
    assert!(
        promoted.promoted,
        "the fixture exercises evidence promotion"
    );
    assert_eq!(
        exact_structural_carriers(&fixture.machine, fixture.child)
            .iter()
            .filter(|carrier| **carrier == fixture.derivation)
            .count(),
        1,
        "new and duplicate paths retain one exact structural carrier"
    );
    let structural_claims =
        observed_structural_claim_parents(&fixture.machine, fixture.child, fixture.derivation);
    assert_eq!(
        structural_claims.len(),
        1,
        "new and duplicate paths merge one structural claim parent"
    );
    assert_eq!(
        structural_claims[0].coverage_root, fixture.coverage_root,
        "the duplicate structural path keeps the parent's compressed root"
    );
    let projection =
        observed_lower_projection(&fixture.machine, fixture.target, fixture.lower_record);
    assert_eq!(
        projection.claimed_roots,
        vec![fixture.coverage_root],
        "new, duplicate, evidence, and promotion paths converge on the same root"
    );
    assert!(
        !fixture.machine.bounds.records[fixture.lower_record.0 as usize]
            .derivations()
            .contains(&BoundDerivation::IncompleteReplay),
        "the exact carrier must not fail open through IncompleteReplay"
    );
}

#[test]
fn cdm_a_9_1_bulk_oracle_matches_current_ledgers_on_pinned_and_composite_fixtures() {
    let mut direct_first = one_sided_claim_fixture(true);
    assert_cdm_bulk_oracle_fixed_point(
        &mut direct_first.machine,
        direct_first.producer,
        direct_first.lower_record,
        direct_first.target,
        "direct-first dcp_a_8_7 fixture",
    );

    let mut mixed = scheme_projection_unmatched_route_fixture(true);
    let mixed_producers = mixed.machine.bounds.records[mixed.lower_record.0 as usize]
        .derivations()
        .iter()
        .filter_map(|derivation| match derivation {
            BoundDerivation::Constraint(producer) => Some(*producer),
            BoundDerivation::Origin(_)
            | BoundDerivation::ReplayEvidence(_)
            | BoundDerivation::Row(_)
            | BoundDerivation::SchemeInstantiation(_)
            | BoundDerivation::IncompleteReplay => None,
        })
        .collect::<Vec<_>>();
    assert!(
        !mixed_producers.is_empty(),
        "the scheme_projectable_lower pinned fixture exposes its claim-bearing producers"
    );
    for producer in mixed_producers {
        assert_cdm_bulk_oracle_fixed_point(
            &mut mixed.machine,
            producer,
            mixed.lower_record,
            mixed.residual,
            "scheme_projectable_lower mixed-record fixture",
        );
    }

    let mut composite =
        mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::CoveredPremiseFirst, false);
    assert_cdm_bulk_oracle_fixed_point(
        &mut composite.machine,
        composite.result_constraint,
        composite.result_record,
        composite.result_owner,
        "multi-root replay composite fixture",
    );
}

#[test]
fn cdm_a_9_2_direct_and_claimed_insertion_orders_match_after_bulk_oracle() {
    let mut direct_first = one_sided_claim_fixture(true);
    let mut claimed_first = one_sided_claim_fixture_with_claimed_first_then_direct();
    assert_cdm_bulk_oracle_fixed_point(
        &mut direct_first.machine,
        direct_first.producer,
        direct_first.lower_record,
        direct_first.target,
        "direct-first fixture",
    );
    assert_cdm_bulk_oracle_fixed_point(
        &mut claimed_first.machine,
        claimed_first.producer,
        claimed_first.lower_record,
        claimed_first.target,
        "claimed-first fixture",
    );

    assert_eq!(
        mixed_one_sided_snapshot(&direct_first),
        mixed_one_sided_snapshot(&claimed_first),
        "direct-first and claimed-first reach the same ledger, decision, and snapshot"
    );
}

// CDM §9.2's qualified-carrier-index comparison is intentionally deferred to CDM-B, where D3
// introduces that index. The ledger, decision, snapshot, and exact carrier-order controls are
// executable now; pretending to observe a not-yet-existing index would add no contract.

// CDM §9.3 is intentionally deferred to CDM-D. Its observable contract requires D2's delta
// events and a production delta-vs-bulk branch; in CDM-A every listed admission path necessarily
// uses the same bulk implementation, so path fixtures could not detect a missing delta emission
// or a silent bulk fallback and would only duplicate the existing DCP/MPC admission controls.

#[derive(Debug, Clone, PartialEq, Eq)]
struct ObservedCdmBulkOracleSnapshot {
    claim_parents: Vec<ClaimQualifiedParent>,
    projection_claims: Vec<UpperReplayClaimId>,
    projection_proofs: Vec<SchemeProjectionProof>,
    included: bool,
}

fn observed_cdm_bulk_oracle_snapshot(
    machine: &ConstraintMachine,
    producer: ConstraintRecordId,
    lower_record: BoundRecordId,
    owner: TypeVar,
) -> ObservedCdmBulkOracleSnapshot {
    ObservedCdmBulkOracleSnapshot {
        claim_parents: machine
            .bounds
            .claim_parents_by_constraint
            .get(&producer)
            .cloned()
            .unwrap_or_default(),
        projection_claims: machine
            .bounds
            .scheme_projection_claims_by_lower_record
            .get(&lower_record)
            .cloned()
            .unwrap_or_default(),
        projection_proofs: machine
            .bounds
            .projection_proofs_by_lower_record
            .get(&lower_record)
            .cloned()
            .unwrap_or_default(),
        included: machine
            .scheme_projectable_lowers(owner)
            .any(|candidate| candidate.record == lower_record),
    }
}

fn assert_cdm_bulk_oracle_fixed_point(
    machine: &mut ConstraintMachine,
    producer: ConstraintRecordId,
    lower_record: BoundRecordId,
    owner: TypeVar,
    fixture: &str,
) {
    let maintained = observed_cdm_bulk_oracle_snapshot(machine, producer, lower_record, owner);
    machine.recompute_claim_parent_bulk_oracle(producer);
    let bulk = observed_cdm_bulk_oracle_snapshot(machine, producer, lower_record, owner);
    assert_eq!(
        maintained, bulk,
        "{fixture}: claim parents, claim ledger, proof ledger, and inclusion match the bulk oracle"
    );
}

#[test]
fn mpc_a_9_1_conjunctive_only_mixed_replay_is_suppressed() {
    let mut fixture = mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::CoveredPremiseFirst, false);
    let snapshot = observed_mpc_replay_snapshot(&fixture);

    assert_eq!(
        snapshot.clauses,
        vec![ObservedMpcClause::ReplayConjunction {
            lower_premise: ObservedMpcPremise::CoveredOnly,
            upper_premise: ObservedMpcPremise::Standalone,
        }],
        "all result links belong to one exact binary-replay conjunction"
    );
    assert_eq!(
        (snapshot.result_claim_roots, snapshot.standalone_links),
        (2, 0),
        "the result has both replay-side roots but no standalone admission"
    );
    assert!(
        fixture
            .machine
            .remove_scheme_projection_live_coverage_state(
                fixture.coverage_root,
                fixture.coverage_state,
            ),
        "the fixture removes the covered premise's last live state"
    );
    let result_after_liveness = projection_count(
        &fixture.machine,
        fixture.result_owner,
        fixture.result_record,
    );

    assert_eq!(
        (
            snapshot.result_projected,
            snapshot.direct_premise_projected,
            snapshot.raw_result_records,
            result_after_liveness,
        ),
        (0, 1, 1, 1),
        "only the conjunctive result is suppressed while its covered premise is live"
    );
}

#[test]
fn mpc_a_9_2_roots_precede_reduction_registration_before_mixed_replay() {
    let fixture = mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::DirectPremiseFirst, false);
    let direct_root = claim_root(&fixture.machine, fixture.direct_claim);
    let direct_producer =
        fixture.machine.bounds.upper_replay_claims[direct_root.0 as usize].producer_constraint;
    let covered_producer = fixture.machine.bounds.upper_replay_claims
        [fixture.coverage_root.0 as usize]
        .producer_constraint;
    let snapshot = observed_mpc_replay_snapshot(&fixture);

    assert!(
        direct_root < fixture.coverage_root && direct_producer.0 < covered_producer.0,
        "ordinary root admission must precede URR claim registration"
    );
    assert_eq!(
        snapshot.clauses,
        vec![ObservedMpcClause::ReplayConjunction {
            lower_premise: ObservedMpcPremise::CoveredOnly,
            upper_premise: ObservedMpcPremise::Standalone,
        }],
        "the later mixed replay still owns one conjunction, not two standalone roots"
    );
    assert_eq!(
        (
            snapshot.result_projected,
            snapshot.direct_premise_projected,
            snapshot.raw_result_records,
        ),
        (0, 1, 1),
        "pre-URR root topology must not make the replay result independently projectable"
    );
}

#[test]
fn mpc_a_9_3_nested_replay_chain_suppresses_both_results() {
    let mut fixture = mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::CoveredPremiseFirst, false);
    let second_owner = TypeVar(4);
    let pivot_pos = fixture.machine.alloc_pos(Pos::Var(fixture.result_owner));
    let second_upper = fixture.machine.alloc_neg(Neg::Var(second_owner));
    fixture
        .machine
        .subtype(pivot_pos, second_upper, OriginId::unknown_internal());

    let first_lower = lower_endpoint(&fixture.machine, fixture.result_record);
    let second_result = constraint_record_for_key(
        &fixture.machine,
        first_lower,
        second_upper,
        &ConstraintWeights::empty(),
    );
    let second_upper_record =
        upper_bound_record(&fixture.machine, fixture.result_owner, second_upper);
    let second_replay = exact_replay_derivation(
        &fixture.machine,
        second_result,
        fixture.result_owner,
        fixture.result_record,
        second_upper_record,
    );
    let second_record = lower_bound_record(&fixture.machine, second_owner, first_lower);
    let second_parents =
        observed_replay_claim_parents(&fixture.machine, second_result, second_replay);
    assert!(
        second_parents
            .iter()
            .any(|parent| parent.side == ObservedReplayParentSide::Lower),
        "the second replay consumes the first replay result as its exact lower premise"
    );
    assert!(
        fixture.machine.constraint_records[second_result.0 as usize]
            .root_origins
            .is_empty(),
        "the nested result has no standalone root admission"
    );

    assert_eq!(
        (
            projection_count(
                &fixture.machine,
                fixture.result_owner,
                fixture.result_record,
            ),
            projection_count(&fixture.machine, second_owner, second_record),
        ),
        (0, 0),
        "a covered-only conjunction remains suppressed through a second replay"
    );
}

#[test]
fn mpc_a_9_4_premise_alternative_keeps_result_projectable() {
    let fixture = mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::CoveredPremiseFirst, true);
    let snapshot = observed_mpc_replay_snapshot(&fixture);

    assert_eq!(
        snapshot.clauses,
        vec![ObservedMpcClause::ReplayConjunction {
            lower_premise: ObservedMpcPremise::StandaloneAlternative,
            upper_premise: ObservedMpcPremise::Standalone,
        }],
        "the independent direct root is an alternative for the covered upper premise"
    );
    assert_eq!(
        (
            snapshot.result_projected,
            snapshot.direct_premise_projected,
            snapshot.raw_result_records,
            snapshot.standalone_links,
        ),
        (1, 1, 1, 0),
        "the result remains projectable through its premise alternative, not a result-local standalone link"
    );
}

#[test]
fn urr_v3_co_owned_survivor_direct_root_does_not_reopen_replay_premise() {
    let mut fixture = mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::CoveredPremiseFirst, true);
    assert_eq!(
        projection_count(
            &fixture.machine,
            fixture.result_owner,
            fixture.result_record,
        ),
        1,
        "the existing MPC control starts with an unrelated Direct upper alternative"
    );

    let direct_root = claim_root(&fixture.machine, fixture.direct_claim);
    let direct_producer =
        fixture.machine.bounds.upper_replay_claims[direct_root.0 as usize].producer_constraint;
    let direct_key = fixture.machine.constraint_records[direct_producer.0 as usize]
        .key
        .clone();
    let reduction_route = fixture.machine.intern_row_derivation(
        RowDerivationRule::UnweightedReduction,
        vec![RowDerivationParent::Constraint(direct_producer)],
        Vec::new(),
    );
    assert!(
        !fixture.machine.enqueue_row_derived_subtype(
            direct_key.lower,
            direct_key.weights,
            direct_key.upper,
            reduction_route,
        ),
        "the reduction route converges on the already-canonical Direct producer"
    );
    fixture.machine.register_reduction_route_claim_parent(
        direct_producer,
        reduction_route,
        fixture.coverage_root,
    );

    let upper_roots = fixture.machine.bounds.claims_by_upper_record[&fixture.direct_upper_record]
        .iter()
        .map(|claim| claim_root(&fixture.machine, *claim))
        .collect::<FxHashSet<_>>();
    assert!(
        upper_roots.contains(&direct_root) && upper_roots.contains(&fixture.coverage_root),
        "the replay upper is one physical survivor with an uncovered Direct root and the live Reduced root"
    );
    assert!(
        fixture.machine.bounds.claim_parents_by_constraint[&direct_producer]
            .iter()
            .any(|parent| matches!(
                parent,
                ClaimQualifiedParent::ReductionRouteConstraint {
                    parent_claim,
                    derivation,
                } if claim_root(&fixture.machine, *parent_claim) == fixture.coverage_root
                    && *derivation == reduction_route
            )),
        "the Direct producer is causally downstream of the same exact reduction root"
    );
    assert!(
        fixture
            .machine
            .bounds
            .live_coverage_by_root
            .get(&fixture.coverage_root)
            .is_some_and(|states| !states.is_empty())
            && fixture
                .machine
                .bounds
                .live_coverage_by_root
                .get(&direct_root)
                .is_none_or(Vec::is_empty),
        "only the reduction side of the co-owned survivor is live-covered"
    );

    assert_eq!(
        projection_count(
            &fixture.machine,
            fixture.result_owner,
            fixture.result_record,
        ),
        0,
        "a Direct root qualified by the same reduction must not reopen that survivor as an independent replay premise"
    );
}

#[test]
fn mpc_a_9_5_cpk_unattributed_claim_link_is_attempt_terminal() {
    let (machine, _owner, lower_record, _claim) = unattributed_claim_link_fixture();
    let mut round = proof::ProjectionEvaluationRound::new();
    let expected = proof::ProofFailure::MissingProofFact {
        fact: proof::ProofFactRef::ProjectionFormula(lower_record),
    };

    // CPK projection-decision addendum §5 and §6.3 supersede the local metadata fail-open:
    // support without formula is attempt-terminal, and the same round cannot resume locally.
    assert_eq!(
        machine.proof_store.project_lower(&machine, lower_record, &mut round),
        Err(expected.clone()),
    );
    assert_eq!(
        machine.proof_store.project_lower(&machine, lower_record, &mut round),
        Err(expected),
        "the first proof failure remains terminal for the evaluation round",
    );
}

fn unattributed_claim_link_fixture(
) -> (ConstraintMachine, TypeVar, BoundRecordId, UpperReplayClaimId) {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let owner = TypeVar(1);
    let producer = ConstraintRecordId(0);
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Var(owner));
    let upper_record = machine
        .bounds
        .add_upper(
            source,
            upper,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(producer),
        )
        .id;
    let claim = machine
        .original_upper_replay_claim(upper_record, producer, UpperReplayClaimKind::Direct)
        .claim;
    let lower_record = machine
        .bounds
        .add_lower(
            owner,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(producer),
        )
        .id;

    // This deliberately bypasses every admission occurrence. MPC-B must retain an equivalent
    // test-only path so the claim has no clause tag and D4's flat fail-open remains observable.
    let mutation = machine
        .bounds
        .update_scheme_projection_proofs(lower_record, &[claim], &[]);
    machine.apply_scheme_projection_mutation(mutation);

    (machine, owner, lower_record, claim)
}

#[test]
fn mpc_a_9_6_replay_clause_snapshot_is_insertion_order_invariant() {
    let covered_first =
        mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::CoveredPremiseFirst, false);
    let direct_first = mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::DirectPremiseFirst, false);
    assert_eq!(
        observed_mpc_replay_snapshot(&covered_first),
        observed_mpc_replay_snapshot(&direct_first),
        "9.1 has the same clause set, decision, and snapshot in both replay admission orders"
    );

    let alternative_covered_first =
        mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::CoveredPremiseFirst, true);
    let alternative_direct_first =
        mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::DirectPremiseFirst, true);
    assert_eq!(
        observed_mpc_replay_snapshot(&alternative_covered_first),
        observed_mpc_replay_snapshot(&alternative_direct_first),
        "9.4 has the same clause set, decision, and snapshot in both replay admission orders"
    );
}

// MPC §9.7 is intentionally deferred to MPC-D. Its observable contract requires D5's
// `dependent_records_by_premise` reverse index, which is not introduced until MPC-C; a test in
// MPC-A could only repeat the existing root-local empty/non-empty invalidation tests above.

#[test]
fn mpc_a_9_8_duplicate_evidence_and_promotion_preserve_clause_snapshot() {
    let mut fixture = row_structural_claim_fixture();
    let before = observed_mpc_preserved_clause_snapshot(&fixture);
    assert_eq!(
        before,
        ObservedMpcPreservedClauseSnapshot {
            exact_carriers: 1,
            structural_claim_parents: 1,
            linked_roots: 1,
            projected_count: 0,
            incomplete_replay: false,
        },
        "the pre-change claim census pins one covered unary clause"
    );
    let child_key = fixture.machine.constraint_records[fixture.child.0 as usize]
        .key
        .clone();

    assert!(
        !fixture.machine.enqueue_derived_subtype(
            child_key.lower,
            child_key.weights,
            child_key.upper,
            fixture.derivation.parent,
            fixture.derivation.rule,
        ),
        "the exact structural clause exercises canonical duplicate admission"
    );
    let prefiltered_before = fixture.machine.timing.lower_replay_prefiltered
        + fixture.machine.timing.upper_replay_prefiltered;
    let duplicate_source = TypeVar(20);
    let duplicate_pivot = TypeVar(21);
    let duplicate_target = TypeVar(22);
    let duplicate_source_pos = fixture.machine.alloc_pos(Pos::Var(duplicate_source));
    let duplicate_pivot_pos = fixture.machine.alloc_pos(Pos::Var(duplicate_pivot));
    let duplicate_pivot_neg = fixture.machine.alloc_neg(Neg::Var(duplicate_pivot));
    let duplicate_target_neg = fixture.machine.alloc_neg(Neg::Var(duplicate_target));
    fixture.machine.subtype(
        duplicate_source_pos,
        duplicate_target_neg,
        OriginId::unknown_internal(),
    );
    fixture.machine.subtype(
        duplicate_source_pos,
        duplicate_pivot_neg,
        OriginId::unknown_internal(),
    );
    fixture.machine.subtype(
        duplicate_pivot_pos,
        duplicate_target_neg,
        OriginId::unknown_internal(),
    );
    assert!(
        fixture.machine.timing.lower_replay_prefiltered
            + fixture.machine.timing.upper_replay_prefiltered
            > prefiltered_before,
        "the alternate pivot reaches an existing result through production prefiltered duplicate admission"
    );
    let evidence = fixture.machine.bounds.add_evidence_lower(
        fixture.target,
        fixture.lower,
        ConstraintWeights::empty(),
        BoundDerivation::ReplayEvidence(fixture.replay),
    );
    assert_eq!(
        evidence.id, fixture.lower_record,
        "evidence-only admission preserves the clause-bearing lower identity"
    );
    let promotion_target = TypeVar(9);
    let promotion_lower = fixture.machine.alloc_pos(Pos::Row(vec![fixture.lower]));
    let evidence_only = fixture.machine.bounds.add_evidence_lower(
        promotion_target,
        promotion_lower,
        ConstraintWeights::empty(),
        BoundDerivation::ReplayEvidence(fixture.replay),
    );
    let promoted = fixture.machine.bounds.add_lower(
        promotion_target,
        promotion_lower,
        ConstraintWeights::empty(),
        BoundDerivation::Constraint(fixture.child),
    );
    assert_eq!(
        promoted.id, evidence_only.id,
        "ordinary promotion preserves the evidence-only stable identity"
    );
    assert!(
        promoted.promoted,
        "the fixture exercises promotion admission"
    );

    assert_eq!(
        observed_mpc_preserved_clause_snapshot(&fixture),
        before,
        "new, canonical duplicate, prefiltered duplicate, evidence-only, and promotion paths preserve one exact clause and its decision"
    );
}

#[test]
fn dpn_a_9_1_structural_clause_uses_constraint_premise_node() {
    let fixture = row_structural_claim_fixture();
    let clauses = record_proof_clauses(&fixture.machine, fixture.lower_record);
    assert_eq!(
        clauses,
        vec![RecordProofClause::DerivedUnary {
            carrier: DerivedUnaryCarrier::Structural(fixture.derivation),
            premise: ProofPremise::Constraint(fixture.derivation.parent),
        }],
        "the structural occurrence copies its exact parent constraint without a record lookup"
    );
    assert_eq!(
        fixture
            .machine
            .bounds
            .record_proof_clause_links_by_lower_record[&fixture.lower_record]
            .len(),
        1,
        "the one structural claim link is attributed to the one unary clause"
    );
    assert!(dependent_edge_exists(
        &fixture.machine,
        ProofPremise::Constraint(fixture.derivation.parent),
        fixture.lower_record,
    ));
    assert!(dependent_edge_exists(
        &fixture.machine,
        ProofPremise::Record(fixture.replay.lower),
        fixture.lower_record,
    ));
    assert!(dependent_edge_exists(
        &fixture.machine,
        ProofPremise::Record(fixture.replay.upper),
        fixture.lower_record,
    ));
    assert_record_proof_attribution_complete(&fixture.machine, fixture.lower_record);
}

#[test]
fn dpn_a_9_2_reduction_route_clause_uses_root_coverage_premise() {
    let fixture = scheme_projection_unmatched_route_fixture(false);
    let claim = &fixture.machine.bounds.upper_replay_claims[fixture.covered_claim.0 as usize];
    let UpperReplayClaimLineage::ReductionRouteConstraint { derivation, .. } = claim.lineage else {
        panic!("the unmatched route fixture must carry a reduction-route claim");
    };
    let root_claim = &fixture.machine.bounds.upper_replay_claims[fixture.coverage_root.0 as usize];
    assert!(
        !fixture
            .machine
            .bounds
            .scheme_projection_lower_record_by_constraint
            .contains_key(&root_claim.producer_constraint),
        "the URR root producer remains upper-only and has no linked lower record"
    );
    assert!(
        record_proof_clauses(&fixture.machine, fixture.lower_record).contains(
            &RecordProofClause::DerivedUnary {
                carrier: DerivedUnaryCarrier::ReductionRoute(derivation),
                premise: ProofPremise::RootCoverage(fixture.coverage_root),
            }
        ),
        "the reduction-route occurrence stores its event-local canonical coverage root"
    );
    assert!(dependent_edge_exists(
        &fixture.machine,
        ProofPremise::RootCoverage(fixture.coverage_root),
        fixture.lower_record,
    ));
    assert_record_proof_attribution_complete(&fixture.machine, fixture.lower_record);
}

#[test]
fn dpn_a_9_6_replay_registration_is_insertion_order_invariant() {
    let covered_first =
        mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::CoveredPremiseFirst, false);
    let direct_first = mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::DirectPremiseFirst, false);
    let expected = ObservedDpnReplayRegistration {
        replay_clauses: 1,
        attributed_links: 2,
        premise_edges: 2,
        unattributed_supports: 0,
    };
    assert_eq!(observed_dpn_replay_registration(&covered_first), expected);
    assert_eq!(
        observed_dpn_replay_registration(&covered_first),
        observed_dpn_replay_registration(&direct_first),
        "exact replay clauses, link tags, reverse edges, and attribution are order-invariant"
    );
}

#[test]
fn dpn_a_confirmed_path_attribution_is_complete() {
    let covered_first =
        mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::CoveredPremiseFirst, false);
    assert_all_record_proof_attribution_complete(&covered_first.machine);

    let direct_first = mpc_mixed_replay_fixture(MpcReplayAdmissionOrder::DirectPremiseFirst, true);
    assert_all_record_proof_attribution_complete(&direct_first.machine);

    let structural = row_structural_claim_fixture();
    assert_all_record_proof_attribution_complete(&structural.machine);

    let reduction = scheme_projection_unmatched_route_fixture(false);
    assert_all_record_proof_attribution_complete(&reduction.machine);
}

#[test]
fn dpn_b_9_1_structural_constraint_premise_evaluates_replay_conjunction() {
    let mut fixture = row_structural_claim_fixture();
    assert_eq!(
        projection_count(&fixture.machine, fixture.target, fixture.lower_record,),
        0,
        "the child is suppressed while its parent constraint has only a covered replay route"
    );
    let coverage_state = fixture.machine.bounds.live_coverage_by_root[&fixture.coverage_root][0];

    assert!(
        fixture
            .machine
            .remove_scheme_projection_live_coverage_state(fixture.coverage_root, coverage_state)
    );
    assert_eq!(
        projection_count(&fixture.machine, fixture.target, fixture.lower_record,),
        1,
        "the same Constraint premise reopens after its covered replay input becomes projectable"
    );
}

#[test]
fn dpn_b_9_2_root_coverage_premise_tracks_liveness_without_a_lower_map() {
    let mut fixture = scheme_projection_unmatched_route_fixture(false);
    let root_producer = fixture.machine.bounds.upper_replay_claims
        [fixture.coverage_root.0 as usize]
        .producer_constraint;
    assert!(
        !fixture
            .machine
            .bounds
            .scheme_projection_lower_record_by_constraint
            .contains_key(&root_producer),
        "the reduction root has no lower-record delegation"
    );
    assert_eq!(
        projection_count(&fixture.machine, fixture.residual, fixture.lower_record,),
        0
    );

    assert!(
        fixture
            .machine
            .remove_scheme_projection_live_coverage_state(
                fixture.coverage_root,
                fixture.coverage_state,
            )
    );
    assert_eq!(
        projection_count(&fixture.machine, fixture.residual, fixture.lower_record,),
        1,
        "RootCoverage is evaluated directly and reverses when its last live state leaves"
    );
}

#[test]
fn dpn_b_9_4_nested_constraint_chain_reaches_the_root_base_case() {
    let mut fixture = row_structural_claim_fixture();
    let nested_target = TypeVar(70);
    let nested_lower = fixture
        .machine
        .alloc_pos(Pos::Con(vec!["dpn-b-nested-constraint".into()], Vec::new()));
    let nested_upper = fixture.machine.alloc_neg(Neg::Var(nested_target));
    let nested_rule = StructuralDerivationRule::FunctionReturn;
    assert!(fixture.machine.enqueue_derived_subtype(
        nested_lower,
        ConstraintWeights::empty(),
        nested_upper,
        fixture.child,
        nested_rule,
    ));
    fixture.machine.drain();
    let nested_constraint = fixture
        .machine
        .constraint_record_id(nested_lower, ConstraintWeights::empty(), nested_upper)
        .expect("the nested structural child is canonical");
    let nested_record = fixture
        .machine
        .bounds
        .scheme_projection_lower_record_by_constraint[&nested_constraint];
    assert!(
        record_proof_clauses(&fixture.machine, nested_record).contains(
            &RecordProofClause::DerivedUnary {
                carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                    parent: fixture.child,
                    rule: nested_rule,
                }),
                premise: ProofPremise::Constraint(fixture.child),
            }
        )
    );
    assert_eq!(
        projection_count(&fixture.machine, nested_target, nested_record),
        0,
        "two Constraint nodes preserve the covered root result"
    );
    let coverage_state = fixture.machine.bounds.live_coverage_by_root[&fixture.coverage_root][0];

    assert!(
        fixture
            .machine
            .remove_scheme_projection_live_coverage_state(fixture.coverage_root, coverage_state)
    );
    assert_eq!(
        projection_count(&fixture.machine, nested_target, nested_record),
        1,
        "the nested walk reaches the uncovered root without a one-level shortcut"
    );
}

#[test]
fn dpn_b_9_5_late_constraint_route_retriggers_dependent_record() {
    let mut fixture = row_structural_claim_fixture();
    let parent = fixture.derivation.parent;
    assert_eq!(
        projection_count(&fixture.machine, fixture.target, fixture.lower_record,),
        0
    );
    let direct_upper = fixture
        .machine
        .alloc_neg(Neg::Con(vec!["dpn-b-independent-root".into()], Vec::new()));
    let producer_lower = fixture
        .machine
        .alloc_pos(Pos::Con(vec!["dpn-b-route-producer-lower".into()], Vec::new()));
    let producer_upper = fixture
        .machine
        .alloc_neg(Neg::Con(vec!["dpn-b-route-producer-upper".into()], Vec::new()));
    fixture.machine.subtype(
        producer_lower,
        producer_upper,
        OriginId::unknown_internal(),
    );
    let direct_producer = constraint_record_for_key(
        &fixture.machine,
        producer_lower,
        producer_upper,
        &ConstraintWeights::empty(),
    );
    fixture.machine.add_upper_bound(
        TypeVar(71),
        direct_upper,
        ConstraintWeights::empty(),
        BoundDerivation::Constraint(direct_producer),
    );
    let direct_claim = fixture.machine.bounds.root_claim_by_producer_constraint[&direct_producer];
    let route = fixture.machine.intern_row_derivation(
        RowDerivationRule::UnweightedReduction,
        vec![RowDerivationParent::Constraint(direct_producer)],
        Vec::new(),
    );
    let parent_key = fixture.machine.constraint_records[parent.0 as usize]
        .key
        .clone();
    assert!(!fixture.machine.enqueue_row_derived_subtype(
        parent_key.lower,
        parent_key.weights,
        parent_key.upper,
        route,
    ));
    let epoch_before = fixture
        .machine
        .bounds()
        .of(fixture.target)
        .expect("dependent owner")
        .epoch();
    let journal = fixture.machine.activate_method_role_mutations();

    fixture
        .machine
        .register_reduction_route_claim_parent(parent, route, direct_claim);

    assert_eq!(
        projection_count(&fixture.machine, fixture.target, fixture.lower_record,),
        1,
        "the newly admitted independent route becomes another OR source"
    );
    assert!(dependent_edge_exists(
        &fixture.machine,
        ProofPremise::RootCoverage(direct_claim),
        fixture.lower_record,
    ));
    assert!(
        fixture
            .machine
            .bounds()
            .of(fixture.target)
            .expect("dependent owner after late route")
            .epoch()
            > epoch_before,
        "hook 4 publishes the dependent owner's inclusion change"
    );
    assert!(has_constraint_bounds_mutation(
        &fixture.machine.take_method_role_mutations(),
        fixture.target,
    ));
    journal.finish();
}

#[derive(Debug, Clone, Copy)]
enum MpcReplayAdmissionOrder {
    DirectPremiseFirst,
    CoveredPremiseFirst,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ObservedMpcPremise {
    CoveredOnly,
    Standalone,
    StandaloneAlternative,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ObservedMpcClause {
    ReplayConjunction {
        lower_premise: ObservedMpcPremise,
        upper_premise: ObservedMpcPremise,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ObservedMpcReplaySnapshot {
    clauses: Vec<ObservedMpcClause>,
    result_claim_roots: usize,
    standalone_links: usize,
    raw_result_records: usize,
    result_projected: usize,
    direct_premise_projected: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ObservedMpcPreservedClauseSnapshot {
    exact_carriers: usize,
    structural_claim_parents: usize,
    linked_roots: usize,
    projected_count: usize,
    incomplete_replay: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ObservedDpnReplayRegistration {
    replay_clauses: usize,
    attributed_links: usize,
    premise_edges: usize,
    unattributed_supports: usize,
}

struct MpcMixedReplayFixture {
    machine: ConstraintMachine,
    pivot: TypeVar,
    result_owner: TypeVar,
    covered_lower_record: BoundRecordId,
    direct_upper_record: BoundRecordId,
    direct_projection_record: BoundRecordId,
    result_record: BoundRecordId,
    result_constraint: ConstraintRecordId,
    replay: BinaryReplayDerivation,
    direct_claim: UpperReplayClaimId,
    covered_claim: UpperReplayClaimId,
    coverage_root: UpperReplayClaimId,
    coverage_state: UnweightedRowReductionRecordId,
}

fn mpc_mixed_replay_fixture(
    order: MpcReplayAdmissionOrder,
    with_premise_alternative: bool,
) -> MpcMixedReplayFixture {
    let mut machine = ConstraintMachine::new();
    let reduction_source = TypeVar(0);
    let covered_source = TypeVar(1);
    let pivot = TypeVar(2);
    let result_owner = TypeVar(3);
    let origin = OriginId::unknown_internal();
    let initial_family =
        machine.alloc_pos(Pos::Con(vec!["effect".into(), "mpc".into()], Vec::new()));
    let family_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "mpc".into()], Vec::new()));
    let reduction_source_neg = machine.alloc_neg(Neg::Var(reduction_source));
    let reduction_source_pos = machine.alloc_pos(Pos::Var(reduction_source));
    let covered_source_pos = machine.alloc_pos(Pos::Var(covered_source));
    let pivot_pos = machine.alloc_pos(Pos::Var(pivot));
    let result_owner_neg = machine.alloc_neg(Neg::Var(result_owner));
    let tail = machine.alloc_neg(Neg::Var(pivot));
    let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));

    machine.subtype(initial_family, reduction_source_neg, origin);
    if matches!(order, MpcReplayAdmissionOrder::DirectPremiseFirst) {
        machine.subtype(pivot_pos, result_owner_neg, origin);
    }
    machine.subtype(covered_source_pos, reduction_source_neg, origin);
    machine.subtype(reduction_source_pos, row_upper, origin);
    if with_premise_alternative {
        machine.add_lower_bound(
            pivot,
            covered_source_pos,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(origin),
        );
    }
    if matches!(order, MpcReplayAdmissionOrder::CoveredPremiseFirst) {
        machine.subtype(pivot_pos, result_owner_neg, origin);
    }

    let covered_lower_record = lower_bound_record(&machine, pivot, covered_source_pos);
    let direct_upper_record = upper_bound_record(&machine, pivot, result_owner_neg);
    let direct_projection_record = lower_bound_record(&machine, result_owner, pivot_pos);
    let result_constraint = constraint_record_for_key(
        &machine,
        covered_source_pos,
        result_owner_neg,
        &ConstraintWeights::empty(),
    );
    let replay = exact_replay_derivation(
        &machine,
        result_constraint,
        pivot,
        covered_lower_record,
        direct_upper_record,
    );
    let result_record = lower_bound_record(&machine, result_owner, covered_source_pos);
    let parents = observed_replay_claim_parents(&machine, result_constraint, replay);
    let direct_claim = parents
        .iter()
        .find(|parent| {
            parent.side == ObservedReplayParentSide::Upper
                && machine
                    .bounds
                    .live_coverage_by_root
                    .get(&parent.coverage_root)
                    .is_none_or(Vec::is_empty)
        })
        .map(|parent| parent.claim)
        .expect("the upper premise contributes its independent Direct claim");
    let covered_claim = parents
        .iter()
        .find(|parent| {
            parent.side == ObservedReplayParentSide::Lower
                && machine
                    .bounds
                    .live_coverage_by_root
                    .get(&parent.coverage_root)
                    .is_some_and(|states| !states.is_empty())
        })
        .map(|parent| parent.claim)
        .expect("the lower premise contributes its live covered claim");
    let coverage_root = claim_root(&machine, covered_claim);
    let coverage_states = &machine.bounds.live_coverage_by_root[&coverage_root];
    assert_eq!(
        coverage_states.len(),
        1,
        "the fixture has one live state for its covered premise"
    );
    let coverage_state = coverage_states[0];

    MpcMixedReplayFixture {
        machine,
        pivot,
        result_owner,
        covered_lower_record,
        direct_upper_record,
        direct_projection_record,
        result_record,
        result_constraint,
        replay,
        direct_claim,
        covered_claim,
        coverage_root,
        coverage_state,
    }
}

fn observed_mpc_replay_snapshot(fixture: &MpcMixedReplayFixture) -> ObservedMpcReplaySnapshot {
    let parents =
        observed_replay_claim_parents(&fixture.machine, fixture.result_constraint, fixture.replay);
    let lower_parents = parents
        .iter()
        .filter(|parent| parent.side == ObservedReplayParentSide::Lower)
        .collect::<Vec<_>>();
    let upper_parents = parents
        .iter()
        .filter(|parent| parent.side == ObservedReplayParentSide::Upper)
        .collect::<Vec<_>>();
    assert!(
        lower_parents
            .iter()
            .any(|parent| parent.claim == fixture.covered_claim),
        "the exact lower side carries the covered root"
    );
    assert!(
        upper_parents
            .iter()
            .any(|parent| parent.claim == fixture.direct_claim),
        "the exact upper side carries the ordinary Direct root"
    );
    assert_eq!(
        exact_replay_count(
            &fixture.machine,
            fixture.pivot,
            fixture.covered_lower_record,
            fixture.direct_upper_record,
        ),
        1,
        "the result has one exact binary-replay carrier"
    );
    let lower_has_uncovered_alternative = observed_lower_projection(
        &fixture.machine,
        fixture.pivot,
        fixture.covered_lower_record,
    )
    .independent_supports
        > 0;
    let reason = fixture
        .machine
        .scheme_projectable_lowers(fixture.result_owner)
        .find(|candidate| candidate.record == fixture.result_record)
        .map(|candidate| candidate.reason);
    let standalone_links = fixture.machine.constraint_records[fixture.result_constraint.0 as usize]
        .root_origins
        .len()
        + match &reason {
            Some(SchemeProjectableLowerReason::Qualified {
                independent_supports,
                ..
            }) => independent_supports.len(),
            Some(SchemeProjectableLowerReason::Unclaimed) | None => 0,
        };
    let mut result_roots = fixture
        .machine
        .bounds
        .scheme_projection_claims_by_lower_record
        .get(&fixture.result_record)
        .into_iter()
        .flatten()
        .map(|claim| claim_root(&fixture.machine, *claim))
        .collect::<Vec<_>>();
    result_roots.sort_by_key(|root| root.0);
    result_roots.dedup();

    ObservedMpcReplaySnapshot {
        clauses: vec![ObservedMpcClause::ReplayConjunction {
            lower_premise: if lower_has_uncovered_alternative {
                ObservedMpcPremise::StandaloneAlternative
            } else {
                ObservedMpcPremise::CoveredOnly
            },
            upper_premise: ObservedMpcPremise::Standalone,
        }],
        result_claim_roots: result_roots.len(),
        standalone_links,
        raw_result_records: fixture
            .machine
            .bounds()
            .of(fixture.result_owner)
            .expect("result owner raw bounds")
            .generalized_projection_lowers()
            .filter(|(record, _)| *record == fixture.result_record)
            .count(),
        result_projected: usize::from(reason.is_some()),
        direct_premise_projected: projection_count(
            &fixture.machine,
            fixture.result_owner,
            fixture.direct_projection_record,
        ),
    }
}

fn projection_count(machine: &ConstraintMachine, owner: TypeVar, record: BoundRecordId) -> usize {
    machine
        .scheme_projectable_lowers(owner)
        .filter(|candidate| candidate.record == record)
        .count()
}

fn observed_mpc_preserved_clause_snapshot(
    fixture: &RowStructuralClaimFixture,
) -> ObservedMpcPreservedClauseSnapshot {
    let projection =
        observed_lower_projection(&fixture.machine, fixture.target, fixture.lower_record);
    ObservedMpcPreservedClauseSnapshot {
        exact_carriers: exact_structural_carriers(&fixture.machine, fixture.child)
            .iter()
            .filter(|carrier| **carrier == fixture.derivation)
            .count(),
        structural_claim_parents: observed_structural_claim_parents(
            &fixture.machine,
            fixture.child,
            fixture.derivation,
        )
        .len(),
        linked_roots: projection.claimed_roots.len(),
        projected_count: projection.projected_count,
        incomplete_replay: fixture.machine.bounds.records[fixture.lower_record.0 as usize]
            .derivations()
            .contains(&BoundDerivation::IncompleteReplay),
    }
}

fn record_proof_clauses(
    machine: &ConstraintMachine,
    lower_record: BoundRecordId,
) -> Vec<RecordProofClause> {
    machine
        .bounds
        .record_proof_clause_ids_by_lower_record
        .get(&lower_record)
        .into_iter()
        .flatten()
        .map(|clause_id| {
            let clause = machine.bounds.record_proof_clauses[clause_id.0 as usize];
            assert_eq!(clause.id, *clause_id);
            assert_eq!(clause.lower_record, lower_record);
            clause.clause
        })
        .collect()
}

fn dependent_edge_exists(
    machine: &ConstraintMachine,
    premise: ProofPremise,
    dependent: BoundRecordId,
) -> bool {
    machine
        .bounds
        .dependent_records_by_premise
        .get(&premise)
        .is_some_and(|dependents| dependents.contains(&dependent))
}

fn normalized_projection_support(
    machine: &ConstraintMachine,
    support: SchemeProjectionProofSupport,
) -> Option<SchemeProjectionProofSupport> {
    match support {
        SchemeProjectionProofSupport::Claimed(claim) => machine
            .bounds
            .canonical_coverage_root(claim)
            .map(SchemeProjectionProofSupport::Claimed),
        SchemeProjectionProofSupport::Independent(carrier) => {
            Some(SchemeProjectionProofSupport::Independent(carrier))
        }
    }
}

fn unattributed_record_proof_supports(
    machine: &ConstraintMachine,
    lower_record: BoundRecordId,
) -> Vec<SchemeProjectionProofSupport> {
    let attributed = machine
        .bounds
        .record_proof_clause_links_by_lower_record
        .get(&lower_record)
        .into_iter()
        .flatten()
        .map(|link| link.support)
        .collect::<FxHashSet<_>>();
    machine
        .bounds
        .projection_proofs_by_lower_record
        .get(&lower_record)
        .into_iter()
        .flatten()
        .filter_map(|proof| normalized_projection_support(machine, proof.support))
        .filter(|support| !attributed.contains(support))
        .collect()
}

fn assert_record_proof_attribution_complete(
    machine: &ConstraintMachine,
    lower_record: BoundRecordId,
) {
    assert_eq!(
        unattributed_record_proof_supports(machine, lower_record),
        Vec::new(),
        "every confirmed projection support has an occurrence-owned clause link"
    );
}

fn assert_all_record_proof_attribution_complete(machine: &ConstraintMachine) {
    for lower_record in machine
        .bounds
        .projection_proofs_by_lower_record
        .keys()
        .copied()
    {
        assert_record_proof_attribution_complete(machine, lower_record);
    }
}

fn observed_dpn_replay_registration(
    fixture: &MpcMixedReplayFixture,
) -> ObservedDpnReplayRegistration {
    let clauses = record_proof_clauses(&fixture.machine, fixture.result_record);
    assert_eq!(
        clauses,
        vec![RecordProofClause::ReplayConjunction {
            carrier: fixture.replay,
            lower_premise: fixture.replay.lower,
            upper_premise: fixture.replay.upper,
        }]
    );
    let premise_edges = [fixture.replay.lower, fixture.replay.upper]
        .into_iter()
        .filter(|premise| {
            dependent_edge_exists(
                &fixture.machine,
                ProofPremise::Record(*premise),
                fixture.result_record,
            )
        })
        .count();
    ObservedDpnReplayRegistration {
        replay_clauses: clauses.len(),
        attributed_links: fixture
            .machine
            .bounds
            .record_proof_clause_links_by_lower_record
            .get(&fixture.result_record)
            .map_or(0, Vec::len),
        premise_edges,
        unattributed_supports: unattributed_record_proof_supports(
            &fixture.machine,
            fixture.result_record,
        )
        .len(),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ObservedReplayParentSide {
    Lower,
    Upper,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ObservedReplayClaimParent {
    claim: UpperReplayClaimId,
    coverage_root: UpperReplayClaimId,
    side: ObservedReplayParentSide,
    replay: BinaryReplayDerivation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ObservedStructuralClaimParent {
    claim: UpperReplayClaimId,
    coverage_root: UpperReplayClaimId,
    derivation: StructuralDerivation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ObservedLowerProjection {
    claimed_roots: Vec<UpperReplayClaimId>,
    independent_supports: usize,
    projected_count: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct OrdinaryOneSidedSnapshot {
    raw_count: usize,
    projected_count: usize,
    independent_supports: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MixedOneSidedSnapshot {
    raw_count: usize,
    projected_count: usize,
    independent_supports: usize,
    exact_replay_carriers: usize,
    incomplete_replay: bool,
}

#[derive(Debug, Clone, Copy)]
enum NonRowStructuralShape {
    FunctionReturnEffect,
    TupleElement,
}

struct NonRowStructuralClaimFixture {
    machine: ConstraintMachine,
    child: ConstraintRecordId,
    derivation: StructuralDerivation,
    parent_claim: UpperReplayClaimId,
}

struct OneSidedClaimFixture {
    machine: ConstraintMachine,
    target: TypeVar,
    lower: PosId,
    upper: NegId,
    producer: ConstraintRecordId,
    replay: BinaryReplayDerivation,
    lower_record: BoundRecordId,
    coverage_root: UpperReplayClaimId,
    coverage_state: UnweightedRowReductionRecordId,
}

struct RowStructuralClaimFixture {
    machine: ConstraintMachine,
    target: TypeVar,
    child: ConstraintRecordId,
    derivation: StructuralDerivation,
    lower: PosId,
    lower_record: BoundRecordId,
    coverage_root: UpperReplayClaimId,
    replay: BinaryReplayDerivation,
}

fn claim_root(machine: &ConstraintMachine, claim: UpperReplayClaimId) -> UpperReplayClaimId {
    machine.bounds.upper_replay_claims[claim.0 as usize].coverage_root
}

fn claim_for_upper_record(
    machine: &ConstraintMachine,
    record: BoundRecordId,
) -> UpperReplayClaimId {
    machine.bounds.claims_by_upper_record[&record]
        .iter()
        .copied()
        .find(|claim| machine.bounds.upper_replay_claims[claim.0 as usize].current_record == record)
        .expect("upper record has an exact replay claim")
}

fn observed_replay_claim_parents(
    machine: &ConstraintMachine,
    result: ConstraintRecordId,
    replay: BinaryReplayDerivation,
) -> Vec<ObservedReplayClaimParent> {
    machine
        .bounds
        .claim_parents_by_constraint
        .get(&result)
        .into_iter()
        .flatten()
        .filter_map(|parent| match *parent {
            ClaimQualifiedParent::ReplayConstraint {
                parent_claim,
                parent_side,
                replay: candidate,
            } if candidate == replay => Some(ObservedReplayClaimParent {
                claim: parent_claim,
                coverage_root: claim_root(machine, parent_claim),
                side: match parent_side {
                    ReplayClaimParentSide::Lower => ObservedReplayParentSide::Lower,
                    ReplayClaimParentSide::Upper => ObservedReplayParentSide::Upper,
                },
                replay,
            }),
            ClaimQualifiedParent::ReplayConstraint { .. }
            | ClaimQualifiedParent::StructuralConstraint { .. }
            | ClaimQualifiedParent::ReductionRouteConstraint { .. } => None,
        })
        .collect()
}

fn exact_structural_carriers(
    machine: &ConstraintMachine,
    child: ConstraintRecordId,
) -> Vec<StructuralDerivation> {
    machine.constraint_records[child.0 as usize]
        .structural_derivations
        .clone()
}

fn observed_structural_claim_parents(
    machine: &ConstraintMachine,
    child: ConstraintRecordId,
    derivation: StructuralDerivation,
) -> Vec<ObservedStructuralClaimParent> {
    machine
        .bounds
        .claim_parents_by_constraint
        .get(&child)
        .into_iter()
        .flatten()
        .filter_map(|parent| match *parent {
            ClaimQualifiedParent::StructuralConstraint {
                parent_claim,
                derivation: candidate,
            } if candidate == derivation => Some(ObservedStructuralClaimParent {
                claim: parent_claim,
                coverage_root: claim_root(machine, parent_claim),
                derivation,
            }),
            ClaimQualifiedParent::ReplayConstraint { .. }
            | ClaimQualifiedParent::StructuralConstraint { .. }
            | ClaimQualifiedParent::ReductionRouteConstraint { .. } => None,
        })
        .collect()
}

fn observed_lower_projection(
    machine: &ConstraintMachine,
    owner: TypeVar,
    record: BoundRecordId,
) -> ObservedLowerProjection {
    let mut claimed_roots = machine
        .bounds
        .scheme_projection_claims_by_lower_record
        .get(&record)
        .into_iter()
        .flatten()
        .map(|claim| claim_root(machine, *claim))
        .collect::<Vec<_>>();
    claimed_roots.sort_by_key(|root| root.0);
    claimed_roots.dedup();

    let independent_supports = machine.bounds.records[record.0 as usize]
        .derivations()
        .iter()
        .filter(|derivation| match derivation {
            BoundDerivation::Constraint(producer) => !machine.constraint_records
                [producer.0 as usize]
                .root_origins
                .is_empty(),
            BoundDerivation::Origin(_) | BoundDerivation::SchemeInstantiation(_) => true,
            BoundDerivation::ReplayEvidence(_)
            | BoundDerivation::Row(_)
            | BoundDerivation::IncompleteReplay => false,
        })
        .count();
    let projected_count = machine
        .scheme_projectable_lowers(owner)
        .filter(|candidate| candidate.record == record)
        .count();
    ObservedLowerProjection {
        claimed_roots,
        independent_supports,
        projected_count,
    }
}

fn lower_endpoint(machine: &ConstraintMachine, record: BoundRecordId) -> PosId {
    match machine.bounds.records[record.0 as usize].endpoint() {
        BoundEndpoint::Lower(lower) => lower,
        BoundEndpoint::Upper(_) => panic!("expected a lower record"),
    }
}

fn upper_bound_record(machine: &ConstraintMachine, owner: TypeVar, upper: NegId) -> BoundRecordId {
    let bounds = machine.bounds().of(owner).expect("upper-bound owner");
    bounds
        .upper_record_ids()
        .iter()
        .copied()
        .zip(bounds.uppers())
        .find_map(|(record, bound)| {
            (bound.neg == upper && bound.weights.is_empty()).then_some(record)
        })
        .expect("stable upper-bound record")
}

fn structural_child_for(
    machine: &ConstraintMachine,
    parent: ConstraintRecordId,
    rule: StructuralDerivationRule,
) -> ConstraintRecordId {
    machine
        .constraint_records
        .iter()
        .enumerate()
        .find_map(|(index, record)| {
            record
                .structural_derivations
                .contains(&StructuralDerivation { parent, rule })
                .then_some(ConstraintRecordId(index as u32))
        })
        .expect("canonical structural child with exact carrier")
}

fn ordinary_one_sided_row_snapshot() -> OrdinaryOneSidedSnapshot {
    let mut machine = ConstraintMachine::new();
    let target = TypeVar(0);
    let item = machine.alloc_pos(Pos::Con(vec!["effect".into(), "direct".into()], Vec::new()));
    let lower = machine.alloc_pos(Pos::Row(vec![item]));
    let upper = machine.alloc_neg(Neg::Var(target));
    machine.subtype(lower, upper, OriginId::unknown_internal());
    let record = lower_bound_record(&machine, target, lower);
    let projection = observed_lower_projection(&machine, target, record);
    OrdinaryOneSidedSnapshot {
        raw_count: machine
            .bounds()
            .of(target)
            .expect("ordinary target")
            .generalized_projection_lowers()
            .filter(|(candidate, _)| *candidate == record)
            .count(),
        projected_count: projection.projected_count,
        independent_supports: projection.independent_supports,
    }
}

fn non_row_structural_claim_fixture(shape: NonRowStructuralShape) -> NonRowStructuralClaimFixture {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let target = TypeVar(1);
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let target_neg = machine.alloc_neg(Neg::Var(target));
    let item = machine.alloc_pos(Pos::Con(
        vec!["effect".into(), "non-row".into()],
        Vec::new(),
    ));
    let concrete = machine.alloc_pos(Pos::Row(vec![item]));
    let top = machine.alloc_neg(Neg::Top);
    let bottom = machine.alloc_pos(Pos::Bot);
    let origin = OriginId::unknown_internal();
    let (lower, upper, rule) = match shape {
        NonRowStructuralShape::FunctionReturnEffect => (
            machine.alloc_pos(Pos::Fun {
                arg: top,
                arg_eff: top,
                ret_eff: concrete,
                ret: bottom,
            }),
            machine.alloc_neg(Neg::Fun {
                arg: bottom,
                arg_eff: bottom,
                ret_eff: target_neg,
                ret: top,
            }),
            StructuralDerivationRule::FunctionReturnEffect,
        ),
        NonRowStructuralShape::TupleElement => (
            machine.alloc_pos(Pos::Tuple(vec![concrete])),
            machine.alloc_neg(Neg::Tuple(vec![target_neg])),
            StructuralDerivationRule::TupleElement {
                index: StructuralIndex::from_usize(0),
            },
        ),
    };

    machine.subtype(source_pos, upper, origin);
    let source_upper = upper_bound_record(&machine, source, upper);
    let parent_claim = claim_for_upper_record(&machine, source_upper);
    machine.add_lower_bound(
        source,
        lower,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );
    machine.drain();
    let parent = constraint_record_for_key(&machine, lower, upper, &ConstraintWeights::empty());
    let child = structural_child_for(&machine, parent, rule);
    NonRowStructuralClaimFixture {
        machine,
        child,
        derivation: StructuralDerivation { parent, rule },
        parent_claim,
    }
}

fn row_structural_claim_fixture() -> RowStructuralClaimFixture {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let target = TypeVar(1);
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(target));
    let matched_path = vec!["effect".into(), "duplicate-matched".into()];
    let marker_path = vec!["effect".into(), "duplicate-marker".into()];
    machine.register_effect_family_path(matched_path.clone());
    machine.register_effect_family_path(marker_path.clone());
    let matched_upper = machine.alloc_neg(Neg::Con(matched_path.clone(), Vec::new()));
    let upper = machine.alloc_neg(Neg::Row(vec![matched_upper], tail));
    let matched_lower = machine.alloc_pos(Pos::Con(matched_path, Vec::new()));
    let marker_lower = machine.alloc_pos(Pos::Con(marker_path, Vec::new()));
    let row = machine.alloc_pos(Pos::Row(vec![matched_lower, marker_lower]));
    let origin = OriginId::unknown_internal();

    machine.subtype(source_pos, upper, origin);
    let source_upper_record = upper_bound_record(&machine, source, upper);
    let parent_claim = claim_for_upper_record(&machine, source_upper_record);
    machine.add_lower_bound(
        source,
        row,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );
    machine.drain();

    let source_lower_record = lower_bound_record(&machine, source, row);
    let parent = constraint_record_for_key(&machine, row, upper, &ConstraintWeights::empty());
    let replay = exact_replay_derivation(
        &machine,
        parent,
        source,
        source_lower_record,
        source_upper_record,
    );
    let rule = StructuralDerivationRule::RowItem {
        index: StructuralIndex::from_usize(1),
        route: RowItemRoute::MarkerAggregateToUpperTail,
    };
    let child = structural_child_for(&machine, parent, rule);
    let derivation = StructuralDerivation { parent, rule };
    let lower = machine.constraint_records[child.0 as usize].key.lower;
    let lower_record = lower_bound_record(&machine, target, lower);
    let coverage_root = claim_root(&machine, parent_claim);
    register_fixture_live_coverage(
        &mut machine,
        source,
        source_upper_record,
        upper,
        parent,
        coverage_root,
    );
    RowStructuralClaimFixture {
        machine,
        target,
        child,
        derivation,
        lower,
        lower_record,
        coverage_root,
        replay,
    }
}

fn one_sided_claim_fixture(direct_first: bool) -> OneSidedClaimFixture {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let target = TypeVar(1);
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Var(target));
    let item = machine.alloc_pos(Pos::Con(
        vec!["effect".into(), "one-sided".into()],
        Vec::new(),
    ));
    let lower = machine.alloc_pos(Pos::Row(vec![item]));
    let origin = OriginId::unknown_internal();

    if direct_first {
        machine.subtype(lower, upper, origin);
    }
    machine.subtype(source_pos, upper, origin);
    let source_upper_record = upper_bound_record(&machine, source, upper);
    let root_claim = claim_for_upper_record(&machine, source_upper_record);
    machine.add_lower_bound(
        source,
        lower,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );
    machine.drain();

    let source_lower_record = lower_bound_record(&machine, source, lower);
    let producer = constraint_record_for_key(&machine, lower, upper, &ConstraintWeights::empty());
    let replay = exact_replay_derivation(
        &machine,
        producer,
        source,
        source_lower_record,
        source_upper_record,
    );
    assert!(
        observed_replay_claim_parents(&machine, producer, replay)
            .iter()
            .any(|parent| parent.claim == root_claim),
        "the one-sided producer itself is claim-qualified by exact replay"
    );
    let lower_record = lower_bound_record(&machine, target, lower);
    let coverage_root = claim_root(&machine, root_claim);
    let coverage_state = register_fixture_live_coverage(
        &mut machine,
        source,
        source_upper_record,
        upper,
        producer,
        coverage_root,
    );
    OneSidedClaimFixture {
        machine,
        target,
        lower,
        upper,
        producer,
        replay,
        lower_record,
        coverage_root,
        coverage_state,
    }
}

fn register_fixture_live_coverage(
    machine: &mut ConstraintMachine,
    source: TypeVar,
    upper_record: BoundRecordId,
    upper: NegId,
    producer: ConstraintRecordId,
    coverage_root: UpperReplayClaimId,
) -> UnweightedRowReductionRecordId {
    let provenance = machine.intern_row_derivation(
        RowDerivationRule::UnweightedReduction,
        vec![RowDerivationParent::Constraint(producer)],
        Vec::new(),
    );
    let (state, root_claim) = machine.register_unweighted_row_reduction_for_test(
        UnweightedRowReductionRecord {
            source,
            producer_constraint: None,
            original_items: Vec::new(),
            original_tail: upper,
            original_upper: upper,
            consumed_items: Vec::new(),
            remaining_items: Vec::new(),
            current_reduced_upper: UnweightedRowReductionMaterialization {
                endpoint: upper,
                record: upper_record,
            },
            processed_lower_records: FxHashSet::default(),
            provenance_head: provenance,
        },
    );
    assert_eq!(root_claim, None, "fixture coverage reuses the existing claim root");
    assert!(
        machine.insert_scheme_projection_live_coverage_state(coverage_root, state),
        "the fixture observes a live claim root"
    );
    state
}

fn one_sided_claim_fixture_with_claimed_first_then_direct() -> OneSidedClaimFixture {
    let mut fixture = one_sided_claim_fixture(false);
    let direct_origin = fixture
        .machine
        .alloc_source_boundary(ConstraintOriginKind::Annotation)
        .origin();
    fixture
        .machine
        .subtype(fixture.lower, fixture.upper, direct_origin);
    fixture
}

fn mixed_one_sided_snapshot(fixture: &OneSidedClaimFixture) -> MixedOneSidedSnapshot {
    let projection =
        observed_lower_projection(&fixture.machine, fixture.target, fixture.lower_record);
    let ledger_supports = fixture
        .machine
        .scheme_projectable_lowers(fixture.target)
        .find_map(|entry| (entry.record == fixture.lower_record).then_some(entry.reason))
        .and_then(|reason| match reason {
            SchemeProjectableLowerReason::Qualified {
                uncovered_claims,
                independent_supports,
            } if uncovered_claims.is_empty() => Some(independent_supports),
            SchemeProjectableLowerReason::Unclaimed
            | SchemeProjectableLowerReason::Qualified { .. } => None,
        })
        .expect("the mixed one-sided record is projectable only through its qualified ledger");
    assert!(
        ledger_supports.iter().all(|support| matches!(
            support,
            ProjectionProofCarrier::ConstraintOrigin { constraint, .. }
                if *constraint == fixture.producer
        )),
        "the ledger selects only the exact independent root carrier"
    );
    MixedOneSidedSnapshot {
        raw_count: fixture
            .machine
            .bounds()
            .of(fixture.target)
            .expect("mixed target")
            .generalized_projection_lowers()
            .filter(|(record, _)| *record == fixture.lower_record)
            .count(),
        projected_count: projection.projected_count,
        independent_supports: ledger_supports.len(),
        exact_replay_carriers: fixture.machine.constraint_records[fixture.producer.0 as usize]
            .replay_derivations
            .iter()
            .filter(|replay| **replay == fixture.replay)
            .count(),
        incomplete_replay: fixture.machine.bounds.records[fixture.lower_record.0 as usize]
            .derivations()
            .contains(&BoundDerivation::IncompleteReplay),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ObservedReplayClaimId(u32);

impl PartialOrd for ObservedReplayClaimId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ObservedReplayClaimId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ObservedReplayClaimKind {
    Reduced(UnweightedRowReductionRecordId),
    Direct,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ObservedReplayClaim {
    id: ObservedReplayClaimId,
    producer: ConstraintRecordId,
    record: BoundRecordId,
    kind: ObservedReplayClaimKind,
    covered: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LateMatchingReplayCounts {
    generic: usize,
    incremental_matched: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ObservedReplayClaimLineage {
    Original,
    Derived {
        parent: ObservedReplayClaimId,
        result: ConstraintRecordId,
        replay: BinaryReplayDerivation,
        depth: u32,
    },
    DerivedEvidence {
        parent: ObservedReplayClaimId,
        replay: BinaryReplayDerivation,
        depth: u32,
    },
    Structural {
        parent: ObservedReplayClaimId,
        result: ConstraintRecordId,
        derivation: StructuralDerivation,
        depth: u32,
    },
    ReductionRoute {
        parent: ObservedReplayClaimId,
        result: ConstraintRecordId,
        derivation: RowDerivationId,
        depth: u32,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ObservedLineageClaim {
    id: ObservedReplayClaimId,
    source: TypeVar,
    producer: ConstraintRecordId,
    record: BoundRecordId,
    coverage_root: ObservedReplayClaimId,
    lineage: ObservedReplayClaimLineage,
}

#[derive(Debug, Default)]
struct ObservedReplayLineage {
    claims: Vec<ObservedLineageClaim>,
    covered_roots: FxHashSet<ObservedReplayClaimId>,
    cycle_coalesces: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ObservedReplayLineageMetrics {
    claim_count: usize,
    maximum_depth: u32,
    cycle_coalesces: usize,
}

struct SchemeProjectionUnmatchedRouteFixture {
    machine: ConstraintMachine,
    beta: TypeVar,
    residual: TypeVar,
    lower_record: BoundRecordId,
    covered_claim: UpperReplayClaimId,
    direct_claim: Option<UpperReplayClaimId>,
    coverage_root: UpperReplayClaimId,
    coverage_state: UnweightedRowReductionRecordId,
}

fn scheme_projection_unmatched_route_fixture(
    with_independent_direct_claim: bool,
) -> SchemeProjectionUnmatchedRouteFixture {
    let mut machine = ConstraintMachine::new();
    let alpha = TypeVar(0);
    let beta = TypeVar(1);
    let residual = TypeVar(2);
    let origin = crate::constraints::OriginId::unknown_internal();
    let initial_family = machine.alloc_pos(Pos::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let family_upper = machine.alloc_neg(Neg::Con(vec!["effect".into(), "f".into()], Vec::new()));
    let alpha_neg = machine.alloc_neg(Neg::Var(alpha));
    let alpha_pos = machine.alloc_pos(Pos::Var(alpha));
    let beta_pos = machine.alloc_pos(Pos::Var(beta));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));

    machine.subtype(initial_family, alpha_neg, origin);
    machine.subtype(beta_pos, alpha_neg, origin);
    if with_independent_direct_claim {
        machine.subtype(beta_pos, tail, origin);
    }
    machine.subtype(alpha_pos, row_upper, origin);

    let lower_record = lower_bound_record(&machine, residual, beta_pos);
    let upper_record = upper_bound_record_for_var(&machine, beta, residual);
    let linked_claims = machine
        .bounds
        .scheme_projection_claims_by_lower_record
        .get(&lower_record)
        .cloned()
        .expect("the Var-Var admission links its mirror lower record");
    let covered_claim = linked_claims
        .iter()
        .copied()
        .find(|claim| {
            let root = machine.bounds.upper_replay_claims[claim.0 as usize].coverage_root;
            machine
                .bounds
                .live_coverage_by_root
                .get(&root)
                .is_some_and(|states| !states.is_empty())
        })
        .expect("the unmatched reduction route carries a covered claim");
    let direct_claim = linked_claims.iter().copied().find(|claim| {
        let claim = &machine.bounds.upper_replay_claims[claim.0 as usize];
        claim.current_record == upper_record
            && machine
                .bounds
                .live_coverage_by_root
                .get(&claim.coverage_root)
                .is_none_or(Vec::is_empty)
    });
    let coverage_root = machine.bounds.upper_replay_claims[covered_claim.0 as usize].coverage_root;
    let coverage_state = machine.bounds.live_coverage_by_root[&coverage_root][0];

    assert_eq!(
        linked_claims.len(),
        1 + usize::from(with_independent_direct_claim),
        "the fixture has exactly its covered route and optional direct claim"
    );
    assert_eq!(
        machine.bounds.records[lower_record.0 as usize].endpoint(),
        BoundEndpoint::Lower(beta_pos),
        "the linked record is the raw residual <- beta mirror"
    );

    SchemeProjectionUnmatchedRouteFixture {
        machine,
        beta,
        residual,
        lower_record,
        covered_claim,
        direct_claim,
        coverage_root,
        coverage_state,
    }
}

impl ConstraintMachine {
    pub(crate) fn compact_scheme_projection_unmatched_route_fixture(
        with_independent_direct_claim: bool,
    ) -> (Self, TypeVar, TypeVar, UpperReplayClaimId) {
        let fixture = scheme_projection_unmatched_route_fixture(with_independent_direct_claim);
        (
            fixture.machine,
            fixture.beta,
            fixture.residual,
            fixture.coverage_root,
        )
    }

    pub(crate) fn remove_last_scheme_projection_coverage_for_compact_test(
        &mut self,
        root: UpperReplayClaimId,
    ) -> bool {
        let states = self
            .bounds
            .live_coverage_by_root
            .get(&root)
            .expect("compact fixture has a live coverage root");
        assert_eq!(
            states.len(),
            1,
            "compact fixture transition must remove the root's last live state"
        );
        let state = states[0];
        self.remove_scheme_projection_live_coverage_state(root, state)
    }

    pub(crate) fn reinsert_scheme_projection_coverage_for_compact_test(
        &mut self,
        root: UpperReplayClaimId,
    ) -> bool {
        let states = self
            .bounds
            .live_coverage_by_root
            .get(&root)
            .expect("compact fixture retains its empty coverage root");
        assert!(
            states.is_empty(),
            "compact fixture reinsertion starts after its last live state leaves"
        );
        let state = match self.bounds.upper_replay_claims[root.0 as usize].kind {
            UpperReplayClaimKind::Reduced(state) => state,
            UpperReplayClaimKind::Direct => {
                panic!("compact fixture coverage root is a reduction claim")
            }
        };
        self.insert_scheme_projection_live_coverage_state(root, state)
    }

    pub(crate) fn ordinary_no_claim_positive_alias_fixture() -> (Self, TypeVar, TypeVar, TypeVar) {
        let mut machine = Self::new();
        let owner = TypeVar(0);
        let direct = TypeVar(1);
        let transitive = TypeVar(2);
        let origin = OriginId::unknown_internal();
        let direct_pos = machine.alloc_pos(Pos::Var(direct));
        let transitive_pos = machine.alloc_pos(Pos::Var(transitive));

        machine.bounds.add_lower(
            owner,
            direct_pos,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(origin),
        );
        machine.bounds.add_lower(
            direct,
            transitive_pos,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(origin),
        );

        assert!(
            machine
                .bounds
                .scheme_projection_claims_by_lower_record
                .is_empty(),
            "the ordinary alias fixture must not create scheme-projection claims"
        );
        (machine, owner, direct, transitive)
    }
}

fn has_constraint_bounds_mutation(mutations: &[MethodRoleMutation], owner: TypeVar) -> bool {
    mutations.iter().any(|mutation| {
        matches!(
            mutation,
            MethodRoleMutation::Changed {
                key: DependencyKey::ConstraintBounds(found),
                ..
            } if *found == owner
        )
    })
}

impl ObservedReplayLineage {
    fn claim_for(
        &self,
        source: TypeVar,
        record: BoundRecordId,
        producer: ConstraintRecordId,
    ) -> ObservedLineageClaim {
        self.claims
            .iter()
            .copied()
            .find(|claim| {
                claim.source == source && claim.record == record && claim.producer == producer
            })
            .expect("upper replay claim identified by source, record, and producer")
    }

    fn is_covered(&self, claim: ObservedReplayClaimId) -> bool {
        let claim = self
            .claims
            .get(claim.0 as usize)
            .expect("observed claim ID");
        self.covered_roots.contains(&claim.coverage_root)
    }

    fn metrics_for_root(
        &self,
        coverage_root: ObservedReplayClaimId,
    ) -> ObservedReplayLineageMetrics {
        let mut claim_count = 0;
        let mut maximum_depth = 0;
        for claim in &self.claims {
            if claim.coverage_root != coverage_root {
                continue;
            }
            claim_count += 1;
            maximum_depth = maximum_depth.max(match claim.lineage {
                ObservedReplayClaimLineage::Original => 0,
                ObservedReplayClaimLineage::Derived { depth, .. }
                | ObservedReplayClaimLineage::DerivedEvidence { depth, .. }
                | ObservedReplayClaimLineage::Structural { depth, .. }
                | ObservedReplayClaimLineage::ReductionRoute { depth, .. } => depth,
            });
        }
        ObservedReplayLineageMetrics {
            claim_count,
            maximum_depth,
            cycle_coalesces: self.cycle_coalesces,
        }
    }
}

fn observed_replay_lineage(machine: &ConstraintMachine) -> ObservedReplayLineage {
    let claim_id = |id: UpperReplayClaimId| ObservedReplayClaimId(id.0);
    let claims = machine
        .bounds
        .upper_replay_claims
        .iter()
        .map(|claim| ObservedLineageClaim {
            id: claim_id(claim.id),
            source: claim.source,
            producer: claim.producer_constraint,
            record: claim.current_record,
            coverage_root: claim_id(claim.coverage_root),
            lineage: match claim.lineage {
                UpperReplayClaimLineage::Original => ObservedReplayClaimLineage::Original,
                UpperReplayClaimLineage::ReplayConstraint {
                    parent_claim,
                    parent_side: _,
                    result,
                    replay,
                    depth,
                } => ObservedReplayClaimLineage::Derived {
                    parent: claim_id(parent_claim),
                    result,
                    replay,
                    depth,
                },
                UpperReplayClaimLineage::ReplayEvidence {
                    parent_claim,
                    parent_side: _,
                    replay,
                    depth,
                } => ObservedReplayClaimLineage::DerivedEvidence {
                    parent: claim_id(parent_claim),
                    replay,
                    depth,
                },
                UpperReplayClaimLineage::StructuralConstraint {
                    parent_claim,
                    result,
                    derivation,
                    depth,
                } => ObservedReplayClaimLineage::Structural {
                    parent: claim_id(parent_claim),
                    result,
                    derivation,
                    depth,
                },
                UpperReplayClaimLineage::ReductionRouteConstraint {
                    parent_claim,
                    result,
                    derivation,
                    depth,
                } => ObservedReplayClaimLineage::ReductionRoute {
                    parent: claim_id(parent_claim),
                    result,
                    derivation,
                    depth,
                },
            },
        })
        .collect();
    let covered_roots = machine
        .bounds
        .live_coverage_by_root
        .iter()
        .filter_map(|(root, states)| (!states.is_empty()).then_some(claim_id(*root)))
        .collect();

    ObservedReplayLineage {
        claims,
        covered_roots,
        cycle_coalesces: machine.bounds.replay_claim_cycle_coalesces,
    }
}

fn assert_structural_derivation(
    machine: &ConstraintMachine,
    child: ConstraintRecordId,
    parent: ConstraintRecordId,
    rule: StructuralDerivationRule,
) {
    assert!(
        machine.constraint_records[child.0 as usize]
            .structural_derivations
            .contains(&StructuralDerivation { parent, rule }),
        "canonical child {child:?} must retain structural parent {parent:?} via {rule:?}"
    );
}

fn exact_replay_derivation(
    machine: &ConstraintMachine,
    result: ConstraintRecordId,
    pivot: TypeVar,
    lower: BoundRecordId,
    upper: BoundRecordId,
) -> BinaryReplayDerivation {
    machine.constraint_records[result.0 as usize]
        .replay_derivations
        .iter()
        .copied()
        .find(|replay| replay.pivot == pivot && replay.lower == lower && replay.upper == upper)
        .expect("result constraint retains the exact binary replay edge")
}

fn exact_replay_count(
    machine: &ConstraintMachine,
    pivot: TypeVar,
    lower: BoundRecordId,
    upper: BoundRecordId,
) -> usize {
    machine
        .constraint_records
        .iter()
        .flat_map(|record| &record.replay_derivations)
        .filter(|replay| replay.pivot == pivot && replay.lower == lower && replay.upper == upper)
        .count()
}

fn constraint_or_bound_has_replay_parent_upper(
    machine: &ConstraintMachine,
    producer: ConstraintRecordId,
    record: BoundRecordId,
    parent_upper: BoundRecordId,
) -> bool {
    machine.constraint_records[producer.0 as usize]
        .replay_derivations
        .iter()
        .any(|replay| replay.upper == parent_upper)
        || machine
            .bounds()
            .record(record)
            .expect("upper claim record")
            .derivations()
            .iter()
            .any(|derivation| {
                matches!(
                    derivation,
                    BoundDerivation::ReplayEvidence(replay) if replay.upper == parent_upper
                )
            })
}

fn upper_bound_record_for_var(
    machine: &ConstraintMachine,
    owner: TypeVar,
    expected: TypeVar,
) -> BoundRecordId {
    let bounds = machine.bounds().of(owner).expect("upper-bound owner");
    bounds
        .upper_record_ids()
        .iter()
        .copied()
        .zip(bounds.uppers())
        .find_map(|(record, bound)| {
            (bound.weights.is_empty()
                && matches!(
                    machine.types().neg(bound.neg),
                    Neg::Var(found) if *found == expected
                ))
            .then_some(record)
        })
        .expect("canonical variable upper bound")
}

fn observed_upper_replay_claims(
    machine: &ConstraintMachine,
    source: TypeVar,
    record: BoundRecordId,
) -> Vec<ObservedReplayClaim> {
    let mut claims = Vec::new();
    for state_id in machine
        .unweighted_row_reductions_by_source
        .get(&source)
        .into_iter()
        .flatten()
        .copied()
    {
        let state = &machine.unweighted_row_reduction_records[state_id.0 as usize];
        if state.current_reduced_upper.record != record {
            continue;
        }
        let producer = row_derivation_producer(machine, state.provenance_head);
        claims.push(ObservedReplayClaim {
            id: ObservedReplayClaimId(claims.len() as u32),
            producer,
            record,
            kind: ObservedReplayClaimKind::Reduced(state_id),
            covered: true,
        });
    }

    for derivation in machine
        .bounds()
        .record(record)
        .expect("claim-bearing upper record")
        .derivations()
    {
        let BoundDerivation::Constraint(producer) = derivation else {
            continue;
        };
        if claims.iter().any(|claim| claim.producer == *producer) {
            continue;
        }
        claims.push(ObservedReplayClaim {
            id: ObservedReplayClaimId(claims.len() as u32),
            producer: *producer,
            record,
            kind: ObservedReplayClaimKind::Direct,
            covered: false,
        });
    }
    claims
}

fn row_derivation_producer(
    machine: &ConstraintMachine,
    derivation: RowDerivationId,
) -> ConstraintRecordId {
    fn visit(
        machine: &ConstraintMachine,
        derivation: RowDerivationId,
        seen: &mut FxHashSet<RowDerivationId>,
    ) -> Option<ConstraintRecordId> {
        if !seen.insert(derivation) {
            return None;
        }
        machine.row_derivations[derivation.0 as usize]
            .parents
            .iter()
            .find_map(|parent| match parent {
                RowDerivationParent::Constraint(producer) => Some(*producer),
                RowDerivationParent::RowDerivation(parent) => visit(machine, *parent, seen),
                RowDerivationParent::Bound(_)
                | RowDerivationParent::SubtractFact(_)
                | RowDerivationParent::LowerFilter(_)
                | RowDerivationParent::Origin(_) => None,
            })
    }

    visit(machine, derivation, &mut FxHashSet::default())
        .expect("unweighted reduction producer constraint")
}

fn reduction_state_for_source(
    machine: &ConstraintMachine,
    source: TypeVar,
) -> UnweightedRowReductionRecordId {
    let states = machine
        .unweighted_row_reductions_by_source
        .get(&source)
        .expect("source-local reduction state");
    assert_eq!(states.len(), 1, "test fixture has one logical row relation");
    states[0]
}

fn merge_same_key_upper_proof(
    machine: &mut ConstraintMachine,
    source: TypeVar,
    upper: NegId,
    derivation: BoundDerivation,
) -> BoundInsertResult {
    let insertion = machine
        .bounds
        .add_upper(source, upper, ConstraintWeights::empty(), derivation);
    machine.record_bound_provenance(insertion, BoundDirection::Upper, false);
    insertion
}

fn upper_dispositions_for(
    machine: &ConstraintMachine,
    source: TypeVar,
    upper: NegId,
) -> Vec<BoundDisposition> {
    machine
        .bound_dispositions
        .iter()
        .filter_map(|record| {
            (record.direction == BoundDirection::Upper
                && record.owner == source
                && record.endpoint == BoundEndpoint::Upper(upper)
                && record.weights.is_empty())
            .then_some(record.disposition)
        })
        .collect()
}

fn late_matching_replay_counts(
    machine: &ConstraintMachine,
    source: TypeVar,
    residual: TypeVar,
    late_lower: PosId,
    original_upper: NegId,
    producer: ConstraintRecordId,
    replay_inputs_before: usize,
) -> LateMatchingReplayCounts {
    let late_record = lower_bound_record(machine, source, late_lower);
    let successor = unweighted_reduction_reaching(
        machine,
        &[
            RowDerivationParent::Constraint(producer),
            RowDerivationParent::Bound(late_record),
        ],
    );
    let incremental_matched = usize::from(machine.constraint_records.iter().any(|record| {
        record.key.lower == late_lower
            && record.key.upper == original_upper
            && record.key.weights.is_empty()
            && record.row_derivations.contains(&successor)
    }));
    assert_eq!(
        incremental_matched, 1,
        "the late matching lower must keep its original-row route"
    );
    let replay_inputs = machine
        .timing()
        .lower_replay_inputs
        .checked_sub(replay_inputs_before)
        .expect("lower replay input count is monotonic");
    let generic = replay_inputs
        .checked_sub(incremental_matched)
        .expect("incremental matched route is included in replay accounting");
    if generic == 0 {
        assert!(
            !has_lower_family_with_weights(
                machine,
                residual,
                &["effect", "f"],
                &ConstraintWeights::empty(),
            ),
            "zero generic replay must keep F out of the residual"
        );
    }
    LateMatchingReplayCounts {
        generic,
        incremental_matched,
    }
}

#[derive(Clone, Copy)]
enum UnweightedRowInsertionOrder {
    AllLowersBeforeUpper,
    OneLowerAfterUpper,
    UpperFirst,
}

#[derive(Debug, PartialEq, Eq)]
struct UnweightedRowOrderFixpoint {
    source_has_only_residual_upper: bool,
    residual_lower_families: Vec<(Vec<String>, String)>,
    payload_constraints: [bool; 4],
}

fn unweighted_row_order_fixpoint(order: UnweightedRowInsertionOrder) -> UnweightedRowOrderFixpoint {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let residual = TypeVar(1);
    let first_payload_var = TypeVar(10);
    let second_payload_var = TypeVar(11);
    let upper_payload_var = TypeVar(12);
    let first_payload_pos = machine.alloc_pos(Pos::Var(first_payload_var));
    let first_payload_neg = machine.alloc_neg(Neg::Var(first_payload_var));
    let first_payload = machine.alloc_neu(Neu::Bounds(first_payload_pos, first_payload_neg));
    let second_payload_pos = machine.alloc_pos(Pos::Var(second_payload_var));
    let second_payload_neg = machine.alloc_neg(Neg::Var(second_payload_var));
    let second_payload = machine.alloc_neu(Neu::Bounds(second_payload_pos, second_payload_neg));
    let upper_payload_pos = machine.alloc_pos(Pos::Var(upper_payload_var));
    let upper_payload_neg = machine.alloc_neg(Neg::Var(upper_payload_var));
    let upper_payload = machine.alloc_neu(Neu::Bounds(upper_payload_pos, upper_payload_neg));
    let family_path = vec!["effect".into(), "f".into()];
    let first_family = machine.alloc_pos(Pos::Con(family_path.clone(), vec![first_payload]));
    let second_family = machine.alloc_pos(Pos::Con(family_path.clone(), vec![second_payload]));
    let family_upper = machine.alloc_neg(Neg::Con(family_path, vec![upper_payload]));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(residual));
    let row_upper = machine.alloc_neg(Neg::Row(vec![family_upper], tail));
    let origin = crate::constraints::OriginId::unknown_internal();

    match order {
        UnweightedRowInsertionOrder::AllLowersBeforeUpper => {
            machine.subtype(first_family, source_neg, origin);
            machine.subtype(second_family, source_neg, origin);
            machine.subtype(source_pos, row_upper, origin);
        }
        UnweightedRowInsertionOrder::OneLowerAfterUpper => {
            machine.subtype(first_family, source_neg, origin);
            machine.subtype(source_pos, row_upper, origin);
            machine.subtype(second_family, source_neg, origin);
        }
        UnweightedRowInsertionOrder::UpperFirst => {
            machine.subtype(source_pos, row_upper, origin);
            machine.subtype(first_family, source_neg, origin);
            machine.subtype(second_family, source_neg, origin);
        }
    }

    let source_has_only_residual_upper = machine.bounds().of(source).is_some_and(|bounds| {
        bounds.uppers().len() == 1
            && bounds.uppers()[0].weights.is_empty()
            && matches!(
                machine.types().neg(bounds.uppers()[0].neg),
                Neg::Var(found) if *found == residual
            )
    });
    UnweightedRowOrderFixpoint {
        source_has_only_residual_upper,
        residual_lower_families: semantic_lower_families(&machine, residual),
        payload_constraints: [
            machine.has_canonical_constraint(&SubtypeConstraintKey {
                lower: first_payload_pos,
                upper: upper_payload_neg,
                weights: ConstraintWeights::empty(),
            }),
            machine.has_canonical_constraint(&SubtypeConstraintKey {
                lower: upper_payload_pos,
                upper: first_payload_neg,
                weights: ConstraintWeights::empty(),
            }),
            machine.has_canonical_constraint(&SubtypeConstraintKey {
                lower: second_payload_pos,
                upper: upper_payload_neg,
                weights: ConstraintWeights::empty(),
            }),
            machine.has_canonical_constraint(&SubtypeConstraintKey {
                lower: upper_payload_pos,
                upper: second_payload_neg,
                weights: ConstraintWeights::empty(),
            }),
        ],
    }
}

fn has_lower_family_with_weights(
    machine: &ConstraintMachine,
    var: TypeVar,
    expected_path: &[&str],
    expected_weights: &ConstraintWeights,
) -> bool {
    machine
        .bounds()
        .of(var)
        .into_iter()
        .flat_map(|bounds| bounds.lowers())
        .any(|lower| {
            &lower.weights == expected_weights
                && pos_contains_family(machine, lower.pos, expected_path)
        })
}

fn has_reachable_scheme_projectable_lower_family_with_weights(
    machine: &ConstraintMachine,
    var: TypeVar,
    expected_path: &[&str],
    expected_weights: &ConstraintWeights,
) -> bool {
    fn visit_var(
        machine: &ConstraintMachine,
        var: TypeVar,
        expected_path: &[&str],
        expected_weights: &ConstraintWeights,
        seen: &mut FxHashSet<TypeVar>,
    ) -> bool {
        if !seen.insert(var) {
            return false;
        }
        machine.scheme_projectable_lowers(var).any(|lower| {
            &lower.bound.weights == expected_weights
                && (pos_contains_family(machine, lower.bound.pos, expected_path)
                    || matches!(
                        machine.types().pos(lower.bound.pos),
                        Pos::Var(next)
                            if visit_var(
                                machine,
                                *next,
                                expected_path,
                                expected_weights,
                                seen,
                            )
                    ))
        })
    }

    visit_var(
        machine,
        var,
        expected_path,
        expected_weights,
        &mut FxHashSet::default(),
    )
}

fn pos_contains_family(machine: &ConstraintMachine, pos: PosId, expected_path: &[&str]) -> bool {
    match machine.types().pos(pos) {
        Pos::Con(path, _) => path
            .iter()
            .map(String::as_str)
            .eq(expected_path.iter().copied()),
        Pos::Row(items) => items
            .iter()
            .any(|item| pos_contains_family(machine, *item, expected_path)),
        _ => false,
    }
}

fn has_lower_alias_with_weights(
    machine: &ConstraintMachine,
    var: TypeVar,
    expected_alias: TypeVar,
    expected_weights: &ConstraintWeights,
) -> bool {
    machine
        .bounds()
        .of(var)
        .into_iter()
        .flat_map(|bounds| bounds.lowers())
        .any(|lower| {
            &lower.weights == expected_weights
                && matches!(
                    machine.types().pos(lower.pos),
                    Pos::Var(found) if *found == expected_alias
                )
        })
}

fn semantic_lower_families(
    machine: &ConstraintMachine,
    var: TypeVar,
) -> Vec<(Vec<String>, String)> {
    fn collect(
        machine: &ConstraintMachine,
        pos: PosId,
        weights: &ConstraintWeights,
        families: &mut Vec<(Vec<String>, String)>,
    ) {
        match machine.types().pos(pos) {
            Pos::Con(path, _) => families.push((path.clone(), format!("{weights:?}"))),
            Pos::Row(items) => {
                for item in items {
                    collect(machine, *item, weights, families);
                }
            }
            _ => {}
        }
    }

    let mut families = Vec::new();
    if let Some(bounds) = machine.bounds().of(var) {
        for lower in bounds.lowers() {
            collect(machine, lower.pos, &lower.weights, &mut families);
        }
    }
    families.sort();
    families
}

fn constraint_record_for_key(
    machine: &ConstraintMachine,
    lower: PosId,
    upper: NegId,
    weights: &ConstraintWeights,
) -> ConstraintRecordId {
    let index = machine
        .constraint_records
        .iter()
        .position(|record| {
            record.key.lower == lower && record.key.upper == upper && &record.key.weights == weights
        })
        .expect("canonical constraint record");
    ConstraintRecordId(index as u32)
}

fn assert_only_empty_upper_var(
    machine: &ConstraintMachine,
    owner: TypeVar,
    expected: TypeVar,
) -> BoundRecordId {
    let bounds = machine.bounds().of(owner).expect("upper-bound owner");
    assert_eq!(
        bounds.uppers().len(),
        1,
        "{owner:?} should have exactly one current reduced upper"
    );
    assert!(
        bounds.uppers()[0].weights.is_empty()
            && matches!(
                machine.types().neg(bounds.uppers()[0].neg),
                Neg::Var(found) if *found == expected
            ),
        "{owner:?} should retain only the reduced tail {expected:?}"
    );
    bounds.upper_record_ids()[0]
}

fn lower_bound_record(machine: &ConstraintMachine, owner: TypeVar, lower: PosId) -> BoundRecordId {
    let bounds = machine.bounds().of(owner).expect("lower-bound owner");
    bounds
        .lower_record_ids()
        .iter()
        .copied()
        .zip(bounds.lowers())
        .find_map(|(record, bound)| (bound.pos == lower).then_some(record))
        .expect("stable lower-bound record")
}

fn upper_bound_record_for_row(
    machine: &ConstraintMachine,
    owner: TypeVar,
    expected_items: &[&[&str]],
    expected_tail: TypeVar,
) -> BoundRecordId {
    let bounds = machine.bounds().of(owner).expect("upper-bound owner");
    bounds
        .upper_record_ids()
        .iter()
        .copied()
        .zip(bounds.uppers())
        .find_map(|(record, bound)| {
            if !bound.weights.is_empty() {
                return None;
            }
            let Neg::Row(items, tail) = machine.types().neg(bound.neg) else {
                return None;
            };
            (matches!(machine.types().neg(*tail), Neg::Var(found) if *found == expected_tail)
                && items.len() == expected_items.len()
                && items.iter().zip(expected_items).all(|(item, expected)| {
                    matches!(
                        machine.types().neg(*item),
                        Neg::Con(path, _)
                            if path.iter().map(String::as_str).eq(expected.iter().copied())
                    )
                }))
            .then_some(record)
        })
        .expect("live reduced row upper")
}

fn unweighted_reduction_reaching(
    machine: &ConstraintMachine,
    required_parents: &[RowDerivationParent],
) -> RowDerivationId {
    machine
        .row_derivations
        .iter()
        .enumerate()
        .find_map(|(index, edge)| {
            let id = RowDerivationId(index as u32);
            (edge.rule == RowDerivationRule::UnweightedReduction
                && required_parents
                    .iter()
                    .all(|parent| row_derivation_reaches(machine, id, *parent)))
            .then_some(id)
        })
        .expect("unweighted reduction provenance reaches every required parent")
}

fn row_derivation_reaches(
    machine: &ConstraintMachine,
    start: RowDerivationId,
    expected: RowDerivationParent,
) -> bool {
    fn visit(
        machine: &ConstraintMachine,
        current: RowDerivationId,
        expected: RowDerivationParent,
        seen: &mut FxHashSet<RowDerivationId>,
    ) -> bool {
        if !seen.insert(current) {
            return false;
        }
        machine.row_derivations[current.0 as usize]
            .parents
            .iter()
            .copied()
            .any(|parent| {
                parent == expected
                    || matches!(
                        parent,
                        RowDerivationParent::RowDerivation(parent)
                            if visit(machine, parent, expected, seen)
                    )
            })
    }

    visit(machine, start, expected, &mut FxHashSet::default())
}

fn row_item_match_from(
    machine: &ConstraintMachine,
    parent: RowDerivationId,
    upper_item: NegId,
) -> RowDerivationId {
    machine
        .row_derivations
        .iter()
        .enumerate()
        .find_map(|(index, edge)| {
            (edge.rule == RowDerivationRule::RowItemMatch
                && edge
                    .parents
                    .contains(&RowDerivationParent::RowDerivation(parent))
                && edge.retained_items == [upper_item])
            .then_some(RowDerivationId(index as u32))
        })
        .expect("RowItemMatch child of the reduction provenance head")
}

fn assert_constraint_has_row_derivation(
    machine: &ConstraintMachine,
    lower: PosId,
    upper: NegId,
    derivation: RowDerivationId,
) {
    let record = machine
        .constraint_records
        .iter()
        .find(|record| {
            record.key.lower == lower && record.key.upper == upper && record.key.weights.is_empty()
        })
        .expect("payload invariant constraint");
    assert!(
        record.row_derivations.contains(&derivation),
        "payload invariant constraint should be derived by the late RowItemMatch"
    );
}

fn constraint_has_row_route_to_original(
    machine: &ConstraintMachine,
    lower: PosId,
    expected_items: &[&[&str]],
    expected_tail: TypeVar,
    expected_weights: &ConstraintWeights,
    provenance: RowDerivationId,
) -> bool {
    machine.constraint_records.iter().any(|record| {
        if record.key.lower != lower
            || &record.key.weights != expected_weights
            || !record.row_derivations.contains(&provenance)
        {
            return false;
        }
        let Neg::Row(items, tail) = machine.types().neg(record.key.upper) else {
            return false;
        };
        matches!(machine.types().neg(*tail), Neg::Var(found) if *found == expected_tail)
            && items.len() == expected_items.len()
            && items.iter().zip(expected_items).all(|(item, expected)| {
                matches!(
                    machine.types().neg(*item),
                    Neg::Con(path, _)
                        if path.iter().map(String::as_str).eq(expected.iter().copied())
                )
            })
    })
}

fn unweighted_row_debug_dump(
    machine: &ConstraintMachine,
    source: TypeVar,
    residual: TypeVar,
) -> String {
    fn bounds(machine: &ConstraintMachine, var: TypeVar) -> String {
        let Some(bounds) = machine.bounds().of(var) else {
            return "<none>".to_string();
        };
        let lowers = bounds
            .lowers()
            .iter()
            .map(|lower| format!("{:?} @ {:?}", machine.types().pos(lower.pos), lower.weights))
            .collect::<Vec<_>>();
        let uppers = bounds
            .uppers()
            .iter()
            .map(|upper| format!("{:?} @ {:?}", machine.types().neg(upper.neg), upper.weights))
            .collect::<Vec<_>>();
        format!("lowers={lowers:#?}, uppers={uppers:#?}")
    }

    format!(
        "source {source:?}: {}\nresidual {residual:?}: {}\nrow derivations: {:#?}",
        bounds(machine, source),
        bounds(machine, residual),
        machine.row_derivations,
    )
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

    machine.weighted_subtype(
        lower,
        weights.clone(),
        first_upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.weighted_subtype(
        lower,
        weights.clone(),
        second_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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
    assert_eq!(machine.row_residual_records.len(), 1);
    let residual = &machine.row_residual_records[0];
    assert_eq!(residual.gamma, first_gamma);
    assert_eq!(residual.derivations.len(), 2);
    let producers = residual
        .derivations
        .iter()
        .filter_map(|id| {
            machine.row_derivations[id.0 as usize]
                .parents
                .iter()
                .find_map(|parent| match parent {
                    RowDerivationParent::Constraint(parent) => Some(*parent),
                    _ => None,
                })
        })
        .collect::<FxHashSet<_>>();
    assert_eq!(producers.len(), 2, "gamma reuse keeps per-input edges");
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

    machine.weighted_subtype(
        first_lower,
        weights.clone(),
        first_upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.weighted_subtype(
        second_lower,
        weights.clone(),
        second_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        lower,
        weights.clone(),
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        lower,
        weights,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        lower,
        weights.clone(),
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        lower,
        weights.clone(),
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        lower,
        weights,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    let gamma = single_upper_row_tail(&machine, source, &["io"]);
    let residual_weights = ConstraintWeights {
        left: LeftConstraintWeight::pops(subtract, u32::MAX),
        right: RightConstraintWeight::empty(),
    };
    assert_single_weighted_upper_var(&machine, gamma, tail_var, residual_weights.clone());

    let tail_pos = machine.alloc_pos(Pos::Var(tail_var));
    let tail_upper = machine.alloc_neg(Neg::Row(vec![io], next_tail));
    machine.subtype(
        tail_pos,
        tail_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        lower,
        weights,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    let gamma = single_upper_row_tail(&machine, source, &["io"]);

    // pure pop だけの L は active family を持たないので、次の row head でも Common(L)=All になる。
    let tail_pos = machine.alloc_pos(Pos::Var(tail_var));
    let tail_upper = machine.alloc_neg(Neg::Row(vec![nondet], next_tail));
    machine.subtype(
        tail_pos,
        tail_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        first_lower,
        weights.clone(),
        first_upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.weighted_subtype(
        second_lower,
        weights,
        second_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        lower,
        weights,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        lower,
        weights,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        lower,
        weights,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.weighted_subtype(
        lower,
        weights,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    assert!(machine.has_canonical_constraint(&SubtypeConstraintKey {
        lower: lower_payload_lower,
        upper: upper_payload_upper,
        weights: ConstraintWeights::empty(),
    }));
    assert!(machine.has_canonical_constraint(&SubtypeConstraintKey {
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

    machine.weighted_subtype(
        lower,
        ConstraintWeights::empty(),
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    assert!(machine.has_canonical_constraint(&SubtypeConstraintKey {
        lower: first_payload_lower,
        upper: second_payload_upper,
        weights: ConstraintWeights::empty(),
    }));
    assert!(machine.has_canonical_constraint(&SubtypeConstraintKey {
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

    machine.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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

    machine.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

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
    machine.subtype(
        source_pos,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    assert!(machine.has_canonical_constraint(&SubtypeConstraintKey {
        lower: source_pos,
        upper: target_neg,
        weights: ConstraintWeights::empty(),
    }));
    assert!(machine.canonical_constraints.keys().all(|constraint| {
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

    machine.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    assert!(machine.has_canonical_constraint(&SubtypeConstraintKey {
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

    machine.weighted_subtype(
        lower,
        weights.clone(),
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    assert!(machine.has_canonical_constraint(&SubtypeConstraintKey {
        lower: rhs_arg_eff,
        upper: rhs_ret_eff,
        weights: expected_passthrough_weights,
    }));
    assert!(!machine.has_canonical_constraint(&SubtypeConstraintKey {
        lower: rhs_arg_eff,
        upper: rhs_ret_eff,
        weights: ConstraintWeights::empty(),
    }));
    assert!(!machine.has_canonical_constraint(&SubtypeConstraintKey {
        lower: rhs_arg_eff,
        upper: rhs_ret_eff,
        weights: unnormalized_passthrough_weights,
    }));
    assert!(!machine.has_canonical_constraint(&SubtypeConstraintKey {
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

    machine.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    assert!(machine.has_canonical_constraint(&SubtypeConstraintKey {
        lower: rhs_arg_eff,
        upper: rhs_ret_eff_inner,
        weights: ConstraintWeights::empty(),
    }));
    assert!(machine.canonical_constraints.keys().all(|constraint| {
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
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.weighted_subtype(
        result_pos,
        ConstraintWeights {
            left: LeftConstraintWeight::pop(subtract),
            right: RightConstraintWeight::empty(),
        },
        outer_neg,
        crate::constraints::OriginId::unknown_internal(),
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
