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
                ObservedReplayClaimLineage::Derived { depth, .. } => depth,
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
    let mut observed = ObservedReplayLineage::default();

    for (state_index, state) in machine.unweighted_row_reduction_records.iter().enumerate() {
        let id = ObservedReplayClaimId(observed.claims.len() as u32);
        observed.claims.push(ObservedLineageClaim {
            id,
            source: state.source,
            producer: row_derivation_producer(machine, state.provenance_head),
            record: state.current_reduced_upper.record,
            coverage_root: id,
            lineage: ObservedReplayClaimLineage::Original,
        });
        assert_eq!(
            reduction_state_for_source(machine, state.source),
            UnweightedRowReductionRecordId(state_index as u32),
            "the preflight fixture keeps one canonical reduction state per source"
        );
        observed.covered_roots.insert(id);
    }

    for (record_index, record) in machine.bounds.records.iter().enumerate() {
        if record.direction() != BoundDirection::Upper
            || record.state() == BoundRecordState::Tombstone
        {
            continue;
        }
        let record_id = BoundRecordId(record_index as u32);
        for derivation in record.derivations() {
            let BoundDerivation::Constraint(producer) = derivation else {
                continue;
            };
            if observed
                .claims
                .iter()
                .any(|claim| claim.record == record_id && claim.producer == *producer)
            {
                continue;
            }
            let id = ObservedReplayClaimId(observed.claims.len() as u32);
            observed.claims.push(ObservedLineageClaim {
                id,
                source: record.owner(),
                producer: *producer,
                record: record_id,
                coverage_root: id,
                lineage: ObservedReplayClaimLineage::Original,
            });
        }
    }

    observed
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
