use super::*;

use crate::arena::Arena;
use crate::roles::RoleConstraintArg;
use poly::types::{Neg, NegId, Neu, Pos, PosId};

#[test]
fn role_input_rejects_variable_only_aliases_and_top() {
    let mut infer = Arena::new();
    let positive_var = infer.fresh_type_var();
    let negative_var = infer.fresh_type_var();
    let positive_alias = infer.alloc_pos(Pos::Var(positive_var));
    let negative_alias = infer.alloc_neg(Neg::Var(negative_var));
    let bottom = infer.alloc_pos(Pos::Bot);
    let top = infer.alloc_neg(Neg::Top);

    let inputs = [
        compact_role_input(&infer, positive_alias, top),
        compact_role_input(&infer, bottom, negative_alias),
        compact_role_input(&infer, bottom, top),
    ];

    assert!(
        inputs
            .iter()
            .all(|input| !role_input_has_concrete_component(input))
    );
}

#[test]
fn role_input_accepts_each_concrete_component_shape() {
    let mut infer = Arena::new();
    let bottom = infer.alloc_pos(Pos::Bot);
    let top = infer.alloc_neg(Neg::Top);
    let never = infer.alloc_neg(Neg::Bot);
    let builtin = infer.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let positive_con = infer.alloc_pos(Pos::Con(vec!["PositiveNominal".into()], Vec::new()));
    let negative_con = infer.alloc_neg(Neg::Con(vec!["NegativeNominal".into()], Vec::new()));
    let function = infer.alloc_pos(Pos::Fun {
        arg: top,
        arg_eff: top,
        ret_eff: bottom,
        ret: bottom,
    });
    let record = infer.alloc_pos(Pos::Record(Vec::new()));
    let record_spread = infer.alloc_pos(Pos::RecordTailSpread {
        fields: Vec::new(),
        tail: bottom,
    });
    let poly_variant = infer.alloc_pos(Pos::PolyVariant(Vec::new()));
    let tuple = infer.alloc_pos(Pos::Tuple(Vec::new()));
    let row_item = infer.alloc_pos(Pos::Con(vec!["effect".into()], Vec::new()));
    let row = infer.alloc_pos(Pos::Row(vec![row_item]));

    let inputs = [
        ("Never/bottom", compact_role_input(&infer, bottom, never)),
        ("builtin", compact_role_input(&infer, builtin, top)),
        ("Pos::Con", compact_role_input(&infer, positive_con, top)),
        ("Neg::Con", compact_role_input(&infer, bottom, negative_con)),
        ("function", compact_role_input(&infer, function, top)),
        ("record", compact_role_input(&infer, record, top)),
        (
            "record spread",
            compact_role_input(&infer, record_spread, top),
        ),
        (
            "polymorphic variant",
            compact_role_input(&infer, poly_variant, top),
        ),
        ("tuple", compact_role_input(&infer, tuple, top)),
        ("row", compact_role_input(&infer, row, top)),
    ];

    for (shape, input) in inputs {
        assert!(
            role_input_has_concrete_component(&input),
            "{shape} should be a concrete role input component"
        );
    }
}

#[test]
fn role_constraint_could_resolve_requires_concrete_information_for_every_input() {
    let mut infer = Arena::new();
    let first_var = infer.fresh_type_var();
    let second_var = infer.fresh_type_var();
    let first_alias = infer.alloc_pos(Pos::Var(first_var));
    let second_alias = infer.alloc_neg(Neg::Var(second_var));
    let bottom = infer.alloc_pos(Pos::Bot);
    let top = infer.alloc_neg(Neg::Top);
    let builtin = infer.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let nominal = infer.alloc_neg(Neg::Con(vec!["Concrete".into()], Vec::new()));

    let all_variable = role_constraint(vec![
        compact_role_input(&infer, first_alias, top),
        compact_role_input(&infer, bottom, second_alias),
    ]);
    let concrete = role_constraint(vec![
        compact_role_input(&infer, builtin, top),
        compact_role_input(&infer, bottom, nominal),
    ]);

    assert!(!role_constraint_could_resolve(&all_variable));
    assert!(role_constraint_could_resolve(&concrete));
}

#[test]
fn coalesce_singleton_role_constraint_preserves_predicate_and_sorts_associated_types() {
    let constraint = CompactRoleConstraint {
        role: vec!["TestRole".into()],
        inputs: vec![nominal_role_arg("input", Vec::new())],
        associated: vec![
            CompactRoleAssociatedType {
                name: "Zed".into(),
                value: nominal_role_arg("zed", Vec::new()),
            },
            CompactRoleAssociatedType {
                name: "Alpha".into(),
                value: nominal_role_arg("alpha", Vec::new()),
            },
        ],
    };

    let coalesced = coalesce_role_constraints(vec![constraint]);

    assert_eq!(coalesced.len(), 1);
    assert_eq!(coalesced[0].role, vec!["TestRole"]);
    assert_eq!(
        coalesced[0].inputs,
        vec![nominal_role_arg("input", Vec::new())]
    );
    assert_eq!(
        coalesced[0]
            .associated
            .iter()
            .map(|associated| associated.name.as_str())
            .collect::<Vec<_>>(),
        vec!["Alpha", "Zed"]
    );
    assert_eq!(
        coalesced[0].associated[0].value,
        nominal_role_arg("alpha", Vec::new())
    );
    assert_eq!(
        coalesced[0].associated[1].value,
        nominal_role_arg("zed", Vec::new())
    );
}

#[test]
fn coalesce_multi_member_component_still_merges_and_sorts_associated_types() {
    let shared = TypeVar(1);
    let first = CompactRoleConstraint {
        role: vec!["TestRole".into()],
        inputs: vec![identity_role_arg(shared)],
        associated: vec![CompactRoleAssociatedType {
            name: "Zed".into(),
            value: nominal_role_arg("zed", Vec::new()),
        }],
    };
    let second = CompactRoleConstraint {
        role: vec!["TestRole".into()],
        inputs: vec![identity_role_arg(shared)],
        associated: vec![CompactRoleAssociatedType {
            name: "Alpha".into(),
            value: nominal_role_arg("alpha", Vec::new()),
        }],
    };

    let coalesced = coalesce_role_constraints(vec![first, second]);

    assert_eq!(coalesced.len(), 1);
    assert_eq!(coalesced[0].inputs, vec![identity_role_arg(shared)]);
    assert_eq!(
        coalesced[0]
            .associated
            .iter()
            .map(|associated| associated.name.as_str())
            .collect::<Vec<_>>(),
        vec!["Alpha", "Zed"]
    );
}

#[test]
fn candidate_precheck_rejects_definite_non_first_head_mismatch_before_deep_match() {
    let mut infer = Arena::new();
    let node_var = infer.fresh_type_var();
    let candidate = vec![
        nominal_role_arg(
            "doc_leaf",
            vec![nominal_bounds(
                "cons_cell",
                vec![
                    identity_bounds(node_var),
                    nominal_bounds("nil_cell", Vec::new()),
                ],
            )],
        ),
        nominal_role_arg("html_format", Vec::new()),
    ];
    let demand = vec![
        nominal_bounds(
            "doc_leaf",
            vec![nominal_bounds(
                "cons_cell",
                vec![
                    nominal_bounds("text_leaf", Vec::new()),
                    nominal_bounds("nil_cell", Vec::new()),
                ],
            )],
        ),
        nominal_bounds("markdown_format", Vec::new()),
    ];

    assert!(role_candidate_has_definite_input_head_mismatch(
        &candidate, &demand
    ));
    let mut subst = TypeSubst::default();
    assert!(!match_role_candidate_inputs(
        &candidate, &demand, &mut subst
    ));
    assert_eq!(subst.get(node_var), None);
}

#[test]
fn candidate_precheck_defers_ambiguous_input_to_full_match() {
    let mut infer = Arena::new();
    let format_var = infer.fresh_type_var();
    let candidate = vec![
        nominal_role_arg("text_leaf", Vec::new()),
        identity_role_arg(format_var),
    ];
    let demand = vec![
        nominal_bounds("text_leaf", Vec::new()),
        nominal_bounds("markdown_format", Vec::new()),
    ];

    assert!(!role_candidate_has_definite_input_head_mismatch(
        &candidate, &demand
    ));
    let mut subst = TypeSubst::default();
    assert!(match_role_candidate_inputs(&candidate, &demand, &mut subst));
    assert_eq!(
        subst.get(format_var),
        compact_type_from_bounds(&demand[1]).as_ref()
    );
}

#[test]
fn candidate_precheck_preserves_positive_nominal_match() {
    let nested_node = nominal_bounds(
        "doc_leaf",
        vec![nominal_bounds(
            "cons_cell",
            vec![
                nominal_bounds("text_leaf", Vec::new()),
                nominal_bounds("nil_cell", Vec::new()),
            ],
        )],
    );
    let markdown = nominal_bounds("markdown_format", Vec::new());
    let candidate = vec![
        CompactRoleArg::invariant(nested_node.clone()),
        CompactRoleArg::invariant(markdown.clone()),
    ];
    let demand = vec![nested_node, markdown];

    assert!(!role_candidate_has_definite_input_head_mismatch(
        &candidate, &demand
    ));
    assert!(match_role_candidate_inputs(
        &candidate,
        &demand,
        &mut TypeSubst::default()
    ));
}

#[test]
fn constructor_match_rejects_when_later_child_fails() {
    let mut infer = Arena::new();
    let head = infer.fresh_type_var();
    let candidate = vec![nominal_role_arg(
        "doc_leaf",
        vec![
            identity_bounds(head),
            nominal_bounds("nil_cell", Vec::new()),
        ],
    )];
    let demand = vec![nominal_bounds(
        "doc_leaf",
        vec![
            nominal_bounds("text_leaf", Vec::new()),
            nominal_bounds("cons_cell", Vec::new()),
        ],
    )];

    assert!(!match_role_candidate_inputs(
        &candidate,
        &demand,
        &mut TypeSubst::default(),
    ));
}

#[test]
fn failed_constructor_child_does_not_poison_next_structural_alternative() {
    let mut infer = Arena::new();
    let head = infer.fresh_type_var();
    let pattern = CompactTuple {
        items: vec![nominal_type(
            "doc_leaf",
            vec![
                identity_bounds(head),
                nominal_bounds("nil_cell", Vec::new()),
            ],
        )],
    };
    let mut demand = CompactType::default();
    demand.tuples = vec![
        CompactTuple {
            items: vec![nominal_type(
                "doc_leaf",
                vec![
                    nominal_bounds("poison_leaf", Vec::new()),
                    nominal_bounds("cons_cell", Vec::new()),
                ],
            )],
        },
        CompactTuple {
            items: vec![nominal_type(
                "doc_leaf",
                vec![
                    nominal_bounds("winning_leaf", Vec::new()),
                    nominal_bounds("nil_cell", Vec::new()),
                ],
            )],
        },
    ];
    let winning_head = nominal_type("winning_leaf", Vec::new());
    let mut subst = TypeSubst::default();

    assert!(match_tuple_pattern(&pattern, &demand, &mut subst));
    assert_eq!(subst.get(head), Some(&winning_head));
}

#[test]
fn failed_constructor_candidate_does_not_poison_next_role_candidate() {
    let mut machine = ConstraintMachine::new();
    let failed_head = TypeVar(0);
    machine.register_type_var(failed_head, TypeLevel::root());

    let failed_head_arg = raw_identity_role_arg(&mut machine, failed_head);
    let failed_tail_arg = raw_nominal_role_arg(&mut machine, "cons_cell");
    let failed_input = raw_nominal_role_arg_with_args(
        &mut machine,
        "doc_leaf",
        vec![failed_head_arg, failed_tail_arg],
    );
    let failed = raw_role_candidate(vec![failed_input]);

    let winning_head_arg = raw_nominal_role_arg(&mut machine, "text_leaf");
    let winning_tail_arg = raw_nominal_role_arg(&mut machine, "nil_cell");
    let winning_input = raw_nominal_role_arg_with_args(
        &mut machine,
        "doc_leaf",
        vec![winning_head_arg, winning_tail_arg],
    );
    let winning = raw_role_candidate(vec![winning_input]);

    let mut impls = RoleImplTable::new();
    impls.insert(failed);
    impls.insert(winning);
    let demand = nominal_bounds(
        "doc_leaf",
        vec![
            nominal_bounds("text_leaf", Vec::new()),
            nominal_bounds("nil_cell", Vec::new()),
        ],
    );
    let constraint = role_constraint(vec![CompactRoleArg::invariant(demand)]);

    let output = resolve_role_constraints_with_stats(
        &machine,
        &CompactRoot::default(),
        &[constraint],
        &impls,
        &FxHashSet::default(),
    );

    assert_eq!(output.stats.candidate_scans, 2);
    assert_eq!(output.stats.candidate_matches, 1);
    assert_eq!(output.resolutions.len(), 1);
}

#[test]
fn pure_recursive_result_is_independent_of_live_applied_membership() {
    let mut machine = ConstraintMachine::new();
    let prerequisite_input = raw_nominal_role_arg(&mut machine, "fragment");
    let mut prerequisite_candidate = raw_role_candidate(vec![prerequisite_input]);
    prerequisite_candidate.role = vec!["Prerequisite".into()];
    let mut candidate = raw_role_candidate(vec![raw_nominal_role_arg(&mut machine, "document")]);
    candidate.prerequisites.push(RoleConstraint {
        role: vec!["Prerequisite".into()],
        inputs: vec![prerequisite_input],
        associated: Vec::new(),
    });
    let mut impls = RoleImplTable::new();
    impls.insert(prerequisite_candidate);
    impls.insert(candidate);
    let demand = role_constraint(vec![nominal_role_arg("document", Vec::new())]);

    let (first, first_pure) = capture_pure_role_demand_observations(|| {
        resolve_role_constraints_with_stats_and_dispositions(
            &machine,
            &CompactRoot::default(),
            std::slice::from_ref(&demand),
            &impls,
            &FxHashSet::default(),
        )
    });
    let key = first.output.resolutions[0].key.clone();
    let prerequisite_key = first.output.resolutions[0].solved_prerequisites[0]
        .key
        .clone();
    let applied = FxHashSet::from_iter([key.clone(), prerequisite_key]);
    let (second, second_pure) = capture_pure_role_demand_observations(|| {
        resolve_role_constraints_with_stats_and_dispositions(
            &machine,
            &CompactRoot::default(),
            std::slice::from_ref(&demand),
            &impls,
            &applied,
        )
    });

    assert_eq!(first_pure.len(), 1);
    assert_eq!(second_pure.len(), 1);
    assert_eq!(first_pure[0].demand, second_pure[0].demand);
    assert_eq!(first_pure[0].outcome, second_pure[0].outcome);
    assert_eq!(
        first_pure[0].candidate_buckets,
        second_pure[0].candidate_buckets
    );
    assert!(matches!(
        first.dispositions.as_slice(),
        [RoleDemandDisposition::NewlyResolved { key: observed }] if observed == &key
    ));
    assert!(matches!(
        second.dispositions.as_slice(),
        [RoleDemandDisposition::AlreadyApplied { key: observed }] if observed == &key
    ));
    assert_eq!(first.output.resolutions.len(), 1);
    assert!(second.output.resolutions.is_empty());

    let cached_new = apply_pure_role_demand_outcome(&first_pure[0].outcome, &FxHashSet::default());
    let full_new =
        shadow_applications_from_full_solve(&first.dispositions, &first.output.resolutions)
            .expect("full newly-resolved dispositions must align with production deltas")
            .remove(0);
    assert_eq!(cached_new, full_new);
    assert_eq!(cached_new.state_delta.applied_resolution_keys, vec![key]);
    assert_eq!(cached_new.state_delta.applied_demands.len(), 2);
    assert!(cached_new.state_delta.residual_prerequisites.is_empty());
    assert_eq!(cached_new.state_delta.equal_role_args.len(), 2);
    let duplicate_applications = shadow_applications_from_full_solve(
        &[first.dispositions[0].clone(), first.dispositions[0].clone()],
        &[
            first.output.resolutions[0].clone(),
            first.output.resolutions[0].clone(),
        ],
    )
    .expect("full batch order, not key uniqueness, aligns repeated dispositions");
    assert_eq!(duplicate_applications, vec![cached_new.clone(), cached_new]);

    let cached_applied = apply_pure_role_demand_outcome(&first_pure[0].outcome, &applied);
    let full_applied =
        shadow_applications_from_full_solve(&second.dispositions, &second.output.resolutions)
            .expect("full already-applied disposition has an empty production delta")
            .remove(0);
    assert_eq!(cached_applied, full_applied);
    assert_eq!(cached_applied.state_delta, ShadowRoleStateDelta::default());
}

#[test]
fn pure_recursive_result_preserves_nested_solved_and_residual_prerequisites() {
    let mut machine = ConstraintMachine::new();
    let direct = named_raw_role_candidate(&mut machine, "Direct", "fragment");
    let inner = named_raw_role_candidate(&mut machine, "Inner", "atom");
    let mut nested = named_raw_role_candidate(&mut machine, "Nested", "layer");
    nested
        .prerequisites
        .push(named_raw_role_constraint(&mut machine, "Inner", "atom"));
    nested.prerequisites.push(named_raw_role_constraint(
        &mut machine,
        "MissingNested",
        "nested-residual",
    ));
    let mut top = named_raw_role_candidate(&mut machine, "Top", "document");
    top.prerequisites.push(named_raw_role_constraint(
        &mut machine,
        "Direct",
        "fragment",
    ));
    top.prerequisites
        .push(named_raw_role_constraint(&mut machine, "Nested", "layer"));
    top.prerequisites.push(named_raw_role_constraint(
        &mut machine,
        "MissingTop",
        "top-residual",
    ));
    let mut impls = RoleImplTable::new();
    impls.insert(direct);
    impls.insert(inner);
    impls.insert(nested);
    impls.insert(top);
    let demand = named_compact_role_constraint("Top", "document");

    let (full, pure) = capture_pure_role_demand_observations(|| {
        resolve_role_constraints_with_stats_and_dispositions(
            &machine,
            &CompactRoot::default(),
            std::slice::from_ref(&demand),
            &impls,
            &FxHashSet::default(),
        )
    });

    assert_eq!(full.output.stats.prerequisite_demands, 5);
    assert_eq!(full.output.stats.prerequisite_candidate_scans, 3);
    assert_eq!(full.output.stats.prerequisite_candidate_matches, 3);
    assert_eq!(full.output.resolutions.len(), 1);
    let resolution = &full.output.resolutions[0];
    assert_eq!(
        resolution
            .solved_prerequisites
            .iter()
            .map(|resolution| resolution.demand.role[0].as_str())
            .collect::<Vec<_>>(),
        vec!["Direct", "Nested"],
    );
    assert_eq!(resolution.residual_prerequisites[0].role, ["MissingTop"]);
    let nested = &resolution.solved_prerequisites[1];
    assert_eq!(nested.solved_prerequisites[0].demand.role, ["Inner"]);
    assert_eq!(nested.residual_prerequisites[0].role, ["MissingNested"]);
    assert_eq!(
        pure[0].candidate_buckets,
        vec![
            vec!["Top".to_string()],
            vec!["Direct".to_string()],
            vec!["Nested".to_string()],
            vec!["Inner".to_string()],
            vec!["MissingNested".to_string()],
            vec!["MissingTop".to_string()],
        ]
    );

    let cached = apply_pure_role_demand_outcome(&pure[0].outcome, &FxHashSet::default());
    let fresh = shadow_applications_from_full_solve(&full.dispositions, &full.output.resolutions)
        .expect("full nested result aligns with its live disposition")
        .remove(0);
    assert_eq!(cached, fresh);
    assert_eq!(cached.state_delta.applied_demands.len(), 4);
    assert_eq!(
        cached
            .state_delta
            .residual_prerequisites
            .iter()
            .map(|prerequisite| prerequisite.role[0].as_str())
            .collect::<Vec<_>>(),
        vec!["MissingNested", "MissingTop"]
    );
}

#[test]
fn pure_recursive_result_preserves_shared_prerequisite_for_each_top_level_demand() {
    let mut machine = ConstraintMachine::new();
    let shared = named_raw_role_candidate(&mut machine, "Shared", "fragment");
    let mut first = named_raw_role_candidate(&mut machine, "First", "first-document");
    first.prerequisites.push(named_raw_role_constraint(
        &mut machine,
        "Shared",
        "fragment",
    ));
    let mut second = named_raw_role_candidate(&mut machine, "Second", "second-document");
    second.prerequisites.push(named_raw_role_constraint(
        &mut machine,
        "Shared",
        "fragment",
    ));
    let mut impls = RoleImplTable::new();
    impls.insert(shared);
    impls.insert(first);
    impls.insert(second);
    let demands = [
        named_compact_role_constraint("First", "first-document"),
        named_compact_role_constraint("Second", "second-document"),
    ];

    let (full, pure) = capture_pure_role_demand_observations(|| {
        resolve_role_constraints_with_stats_and_dispositions(
            &machine,
            &CompactRoot::default(),
            &demands,
            &impls,
            &FxHashSet::default(),
        )
    });

    assert_eq!(full.output.stats.prerequisite_demands, 2);
    assert_eq!(full.output.stats.prerequisite_candidate_scans, 2);
    assert_eq!(full.output.stats.prerequisite_candidate_matches, 2);
    assert_eq!(full.output.resolutions.len(), 2);
    assert_eq!(pure.len(), 2);
    assert_eq!(
        full.output.resolutions[0].solved_prerequisites[0].key,
        full.output.resolutions[1].solved_prerequisites[0].key,
    );
    let fresh = shadow_applications_from_full_solve(&full.dispositions, &full.output.resolutions)
        .expect("both full top-level results align with their dispositions");
    for (pure, fresh) in pure.iter().zip(fresh) {
        assert_eq!(
            apply_pure_role_demand_outcome(&pure.outcome, &FxHashSet::default()),
            fresh,
        );
    }
}

#[test]
fn pure_recursive_result_preserves_ambiguous_candidate_count() {
    let mut machine = ConstraintMachine::new();
    let first = named_raw_role_candidate(&mut machine, "Ambiguous", "document");
    let second = named_raw_role_candidate(&mut machine, "Ambiguous", "document");
    let mut impls = RoleImplTable::new();
    impls.insert(first);
    impls.insert(second);
    let demand = named_compact_role_constraint("Ambiguous", "document");

    let (full, pure) = capture_pure_role_demand_observations(|| {
        resolve_role_constraints_with_stats_and_dispositions(
            &machine,
            &CompactRoot::default(),
            std::slice::from_ref(&demand),
            &impls,
            &FxHashSet::default(),
        )
    });

    assert_eq!(full.output.stats.candidate_matches, 2);
    assert_eq!(full.output.stats.ambiguous_demands, 1);
    assert!(full.output.resolutions.is_empty());
    assert!(matches!(
        pure[0].outcome,
        PureRoleDemandOutcome::Unresolved {
            candidate_matches: 2
        }
    ));
    let cached = apply_pure_role_demand_outcome(&pure[0].outcome, &FxHashSet::default());
    let fresh = shadow_applications_from_full_solve(&full.dispositions, &full.output.resolutions)
        .expect("ambiguous full result has no publication delta")
        .remove(0);
    assert_eq!(cached, fresh);
    assert_eq!(cached.state_delta, ShadowRoleStateDelta::default());
}

#[test]
fn pure_recursive_result_preserves_existing_cycle_termination_as_a_residual() {
    let mut machine = ConstraintMachine::new();
    let mut cyclic = named_raw_role_candidate(&mut machine, "Cycle", "document");
    cyclic
        .prerequisites
        .push(named_raw_role_constraint(&mut machine, "Cycle", "document"));
    let mut impls = RoleImplTable::new();
    impls.insert(cyclic);
    let demand = named_compact_role_constraint("Cycle", "document");

    let (full, pure) = capture_pure_role_demand_observations(|| {
        resolve_role_constraints_with_stats_and_dispositions(
            &machine,
            &CompactRoot::default(),
            std::slice::from_ref(&demand),
            &impls,
            &FxHashSet::default(),
        )
    });

    assert_eq!(full.output.stats.prerequisite_demands, 1);
    assert_eq!(full.output.stats.prerequisite_candidate_scans, 1);
    assert_eq!(full.output.stats.prerequisite_candidate_matches, 0);
    let resolution = &full.output.resolutions[0];
    assert!(resolution.solved_prerequisites.is_empty());
    assert_eq!(resolution.residual_prerequisites, vec![demand.clone()]);
    let cached = apply_pure_role_demand_outcome(&pure[0].outcome, &FxHashSet::default());
    let fresh = shadow_applications_from_full_solve(&full.dispositions, &full.output.resolutions)
        .expect("cycle-terminated full result aligns with its disposition")
        .remove(0);
    assert_eq!(cached, fresh);
}

#[test]
fn pure_observation_discards_an_incomplete_demand_after_unwind() {
    let demand = named_compact_role_constraint("Partial", "document");
    let unwind = std::panic::catch_unwind(|| {
        capture_pure_role_demand_observations(|| {
            snapshot_characterization::begin_demand(&demand);
            panic!("interrupt the pure solve before publication");
        });
    });
    assert!(unwind.is_err());

    let mut machine = ConstraintMachine::new();
    let candidate = named_raw_role_candidate(&mut machine, "Partial", "document");
    let mut impls = RoleImplTable::new();
    impls.insert(candidate);
    let (_, completed) = capture_pure_role_demand_observations(|| {
        resolve_role_constraints_with_stats_and_dispositions(
            &machine,
            &CompactRoot::default(),
            std::slice::from_ref(&demand),
            &impls,
            &FxHashSet::default(),
        )
    });
    assert_eq!(completed.len(), 1);
    assert!(matches!(
        completed[0].outcome,
        PureRoleDemandOutcome::Resolved(_)
    ));
}

#[test]
fn snapshot_supplemental_epoch_covers_row_match_candidate_bound_mutation() {
    let mut machine = ConstraintMachine::new();
    let candidate_var = TypeVar(0);
    machine.register_type_var(candidate_var, TypeLevel::root());
    let mut candidate = raw_role_candidate(vec![raw_nominal_role_arg(&mut machine, "document")]);
    let associated_lower = machine.alloc_pos(Pos::Var(candidate_var));
    let associated_upper = machine.alloc_neg(Neg::Var(candidate_var));
    candidate
        .associated
        .push(crate::roles::RoleAssociatedConstraint {
            name: "Item".into(),
            value: RoleConstraintArg {
                lower: associated_lower,
                upper: associated_upper,
            },
        });
    let mut impls = RoleImplTable::new();
    impls.insert(candidate);
    let demand = role_constraint(vec![nominal_role_arg("document", Vec::new())]);

    let lower_item = machine.alloc_pos(Pos::Con(vec!["effect_a".into()], Vec::new()));
    let lower_row = machine.alloc_pos(Pos::Row(vec![lower_item]));
    machine.constrain_subtype(
        lower_row,
        associated_upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    let before = resolve_role_constraints_with_stats(
        &machine,
        &CompactRoot::default(),
        std::slice::from_ref(&demand),
        &impls,
        &FxHashSet::default(),
    );
    let unchanged = resolve_role_constraints_with_stats(
        &machine,
        &CompactRoot::default(),
        std::slice::from_ref(&demand),
        &impls,
        &FxHashSet::default(),
    );
    assert_eq!(unchanged, before);
    let epoch = machine.epoch();
    let supplemental_epoch = machine.role_solve_supplemental_epoch();
    let upper_a = machine.alloc_neg(Neg::Con(vec!["effect_a".into()], Vec::new()));
    let upper_b = machine.alloc_neg(Neg::Con(vec!["effect_b".into()], Vec::new()));
    let upper_tail = machine.alloc_neg(Neg::Top);
    let upper_row = machine.alloc_neg(Neg::Row(vec![upper_a, upper_b], upper_tail));
    machine.constrain_subtype(
        associated_lower,
        upper_row,
        crate::constraints::OriginId::unknown_internal(),
    );
    assert_eq!(machine.epoch(), epoch);
    assert_ne!(machine.role_solve_supplemental_epoch(), supplemental_epoch);
    let after = resolve_role_constraints_with_stats(
        &machine,
        &CompactRoot::default(),
        std::slice::from_ref(&demand),
        &impls,
        &FxHashSet::default(),
    );

    assert_ne!(before, after);
}

#[test]
fn snapshot_supplemental_epoch_covers_candidate_level_registration() {
    let mut machine = ConstraintMachine::new();
    let lower_var = TypeVar(0);
    let upper_var = TypeVar(1);
    let mut candidate = raw_role_candidate(vec![raw_nominal_role_arg(&mut machine, "document")]);
    candidate
        .associated
        .push(crate::roles::RoleAssociatedConstraint {
            name: "Item".into(),
            value: RoleConstraintArg {
                lower: machine.alloc_pos(Pos::Var(lower_var)),
                upper: machine.alloc_neg(Neg::Var(upper_var)),
            },
        });
    let mut impls = RoleImplTable::new();
    impls.insert(candidate);
    let demand = role_constraint(vec![nominal_role_arg("document", Vec::new())]);

    let before = resolve_role_constraints_with_stats(
        &machine,
        &CompactRoot::default(),
        std::slice::from_ref(&demand),
        &impls,
        &FxHashSet::default(),
    );
    let epoch = machine.epoch();
    let supplemental_epoch = machine.role_solve_supplemental_epoch();
    machine.register_type_var(lower_var, TypeLevel::root().child());
    assert_eq!(machine.epoch(), epoch);
    assert_ne!(machine.role_solve_supplemental_epoch(), supplemental_epoch);
    let after = resolve_role_constraints_with_stats(
        &machine,
        &CompactRoot::default(),
        std::slice::from_ref(&demand),
        &impls,
        &FxHashSet::default(),
    );

    assert_ne!(before, after);
}

#[test]
fn raw_candidate_precheck_rejects_definite_head_mismatch_before_compaction() {
    let mut machine = ConstraintMachine::new();
    let candidate = raw_role_candidate(vec![raw_nominal_role_arg(&mut machine, "html_format")]);
    let demand = vec![nominal_bounds("markdown_format", Vec::new())];

    assert!(raw_role_candidate_has_definite_input_head_mismatch(
        &machine,
        &candidate.inputs,
        &demand,
    ));
    let (matched, stats, cached_candidates) =
        resolve_raw_candidate_for_test(&machine, &candidate, &demand);

    assert!(!matched);
    assert_eq!(stats.candidate_cache_misses, 0);
    assert_eq!(stats.candidate_cache_hits, 0);
    assert_eq!(cached_candidates, 0);
}

#[test]
fn raw_candidate_precheck_compares_canonical_builtin_heads() {
    let mut machine = ConstraintMachine::new();
    let candidate = raw_role_candidate(vec![raw_nominal_role_arg(&mut machine, "int")]);

    assert!(!raw_role_candidate_has_definite_input_head_mismatch(
        &machine,
        &candidate.inputs,
        &[nominal_bounds("int", Vec::new())],
    ));
    assert!(raw_role_candidate_has_definite_input_head_mismatch(
        &machine,
        &candidate.inputs,
        &[nominal_bounds("float", Vec::new())],
    ));
}

#[test]
fn raw_candidate_precheck_defers_variable_input_to_compaction_and_matching() {
    let mut machine = ConstraintMachine::new();
    let var = TypeVar(0);
    machine.register_type_var(var, TypeLevel::root());
    let candidate = raw_role_candidate(vec![RoleConstraintArg {
        lower: machine.alloc_pos(Pos::Var(var)),
        upper: machine.alloc_neg(Neg::Var(var)),
    }]);
    let demand = vec![nominal_bounds("markdown_format", Vec::new())];

    assert!(!raw_role_candidate_has_definite_input_head_mismatch(
        &machine,
        &candidate.inputs,
        &demand,
    ));
    let (matched, stats, cached_candidates) =
        resolve_raw_candidate_for_test(&machine, &candidate, &demand);

    assert!(matched);
    assert_eq!(stats.candidate_cache_misses, 1);
    assert_eq!(cached_candidates, 1);
}

#[test]
fn raw_candidate_precheck_preserves_positive_nominal_match() {
    let mut machine = ConstraintMachine::new();
    let candidate = raw_role_candidate(vec![raw_nominal_role_arg(&mut machine, "markdown_format")]);
    let demand = vec![nominal_bounds("markdown_format", Vec::new())];

    assert!(!raw_role_candidate_has_definite_input_head_mismatch(
        &machine,
        &candidate.inputs,
        &demand,
    ));
    let (matched, stats, cached_candidates) =
        resolve_raw_candidate_for_test(&machine, &candidate, &demand);

    assert!(matched);
    assert_eq!(stats.candidate_cache_misses, 1);
    assert_eq!(cached_candidates, 1);
}

#[test]
fn raw_and_compacted_candidate_head_prechecks_compose() {
    let mut machine = ConstraintMachine::new();
    let var = TypeVar(0);
    machine.register_type_var(var, TypeLevel::root());
    let html_lower = machine.alloc_pos(Pos::Con(vec!["html_format".into()], Vec::new()));
    let html_upper = machine.alloc_neg(Neg::Con(vec!["html_format".into()], Vec::new()));
    let raw_lower = machine.alloc_pos(Pos::Var(var));
    let raw_upper = machine.alloc_neg(Neg::Var(var));
    machine.constrain_subtype(
        html_lower,
        raw_upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    machine.constrain_subtype(
        raw_lower,
        html_upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    let candidate = raw_role_candidate(vec![RoleConstraintArg {
        lower: raw_lower,
        upper: raw_upper,
    }]);
    let demand = vec![nominal_bounds("markdown_format", Vec::new())];

    assert!(!raw_role_candidate_has_definite_input_head_mismatch(
        &machine,
        &candidate.inputs,
        &demand,
    ));
    let mut cache = CompactRoleImplCandidateCache::default();
    let mut compact_stats = RoleResolveStats::default();
    let compact = cache.compact::<false>(&machine, &candidate, &mut compact_stats);
    assert!(role_candidate_has_definite_input_head_mismatch(
        &compact.inputs,
        &demand,
    ));

    let (matched, stats, cached_candidates) =
        resolve_raw_candidate_for_test(&machine, &candidate, &demand);
    assert!(!matched);
    assert_eq!(stats.candidate_cache_misses, 1);
    assert_eq!(cached_candidates, 1);
}

fn compact_role_input(infer: &Arena, lower: PosId, upper: NegId) -> CompactRoleArg {
    compact_role_constraint(
        infer.constraints(),
        &RoleConstraint {
            role: vec!["TestRole".into()],
            inputs: vec![RoleConstraintArg { lower, upper }],
            associated: Vec::new(),
        },
    )
    .inputs
    .into_iter()
    .next()
    .expect("test role should contain one input")
}

fn role_constraint(inputs: Vec<CompactRoleArg>) -> CompactRoleConstraint {
    CompactRoleConstraint {
        role: vec!["TestRole".into()],
        inputs,
        associated: Vec::new(),
    }
}

fn raw_role_candidate(inputs: Vec<RoleConstraintArg>) -> RoleImplCandidate {
    RoleImplCandidate {
        impl_def: None,
        role: vec!["TestRole".into()],
        inputs,
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    }
}

fn named_raw_role_candidate(
    machine: &mut ConstraintMachine,
    role: &str,
    input: &str,
) -> RoleImplCandidate {
    let mut candidate = raw_role_candidate(vec![raw_nominal_role_arg(machine, input)]);
    candidate.role = vec![role.into()];
    candidate
}

fn named_raw_role_constraint(
    machine: &mut ConstraintMachine,
    role: &str,
    input: &str,
) -> RoleConstraint {
    RoleConstraint {
        role: vec![role.into()],
        inputs: vec![raw_nominal_role_arg(machine, input)],
        associated: Vec::new(),
    }
}

fn named_compact_role_constraint(role: &str, input: &str) -> CompactRoleConstraint {
    CompactRoleConstraint {
        role: vec![role.into()],
        inputs: vec![nominal_role_arg(input, Vec::new())],
        associated: Vec::new(),
    }
}

fn raw_nominal_role_arg(machine: &mut ConstraintMachine, name: &str) -> RoleConstraintArg {
    let path = vec![name.into()];
    RoleConstraintArg {
        lower: machine.alloc_pos(Pos::Con(path.clone(), Vec::new())),
        upper: machine.alloc_neg(Neg::Con(path, Vec::new())),
    }
}

fn raw_identity_role_arg(machine: &mut ConstraintMachine, var: TypeVar) -> RoleConstraintArg {
    let lower = machine.alloc_pos(Pos::Var(var));
    let upper = machine.alloc_neg(Neg::Var(var));
    RoleConstraintArg { lower, upper }
}

fn raw_nominal_role_arg_with_args(
    machine: &mut ConstraintMachine,
    name: &str,
    args: Vec<RoleConstraintArg>,
) -> RoleConstraintArg {
    let args = args
        .into_iter()
        .map(|arg| machine.alloc_neu(Neu::Bounds(arg.lower, arg.upper)))
        .collect::<Vec<_>>();
    let path = vec![name.into()];
    RoleConstraintArg {
        lower: machine.alloc_pos(Pos::Con(path.clone(), args.clone())),
        upper: machine.alloc_neg(Neg::Con(path, args)),
    }
}

fn resolve_raw_candidate_for_test(
    machine: &ConstraintMachine,
    candidate: &RoleImplCandidate,
    demand: &[CompactBounds],
) -> (bool, RoleResolveStats, usize) {
    let constraint = role_constraint(
        demand
            .iter()
            .cloned()
            .map(CompactRoleArg::invariant)
            .collect(),
    );
    let mut cache = CompactRoleImplCandidateCache::default();
    let mut stats = RoleResolveStats::default();
    let matched = resolve_role_candidate::<false>(
        machine,
        &constraint,
        Some(demand),
        candidate,
        &MainPolarity::default(),
        &FxHashMap::default(),
        &RoleImplTable::new(),
        &mut cache,
        &mut FxHashSet::default(),
        &mut stats,
    )
    .is_some();
    (matched, stats, cache.entries.len())
}

fn identity_role_arg(var: TypeVar) -> CompactRoleArg {
    CompactRoleArg::invariant(identity_bounds(var))
}

fn identity_bounds(var: TypeVar) -> CompactBounds {
    let ty = CompactType::from_var(crate::compact::CompactVar::plain(var));
    CompactBounds::Interval {
        lower: ty.clone(),
        upper: ty,
    }
}

fn nominal_role_arg(name: &str, args: Vec<CompactBounds>) -> CompactRoleArg {
    CompactRoleArg::invariant(nominal_bounds(name, args))
}

fn nominal_bounds(name: &str, args: Vec<CompactBounds>) -> CompactBounds {
    CompactBounds::Con {
        path: vec![name.into()],
        args,
    }
}

fn nominal_type(name: &str, args: Vec<CompactBounds>) -> CompactType {
    CompactType::from_con(CompactCon {
        path: vec![name.into()],
        args,
    })
}
