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
}

#[test]
fn snapshot_constraint_epoch_covers_row_match_candidate_bound_mutation() {
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
    machine.constrain_subtype(lower_row, associated_upper);
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
    let upper_a = machine.alloc_neg(Neg::Con(vec!["effect_a".into()], Vec::new()));
    let upper_b = machine.alloc_neg(Neg::Con(vec!["effect_b".into()], Vec::new()));
    let upper_tail = machine.alloc_neg(Neg::Top);
    let upper_row = machine.alloc_neg(Neg::Row(vec![upper_a, upper_b], upper_tail));
    machine.constrain_subtype(associated_lower, upper_row);
    assert_ne!(machine.epoch(), epoch);
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
fn snapshot_constraint_epoch_covers_candidate_level_registration() {
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
    machine.register_type_var(lower_var, TypeLevel::root().child());
    assert_ne!(machine.epoch(), epoch);
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
    machine.constrain_subtype(html_lower, raw_upper);
    machine.constrain_subtype(raw_lower, html_upper);
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
