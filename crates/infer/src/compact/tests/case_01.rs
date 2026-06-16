use super::*;

#[test]
fn covariant_vars_keep_weight() {
    let weight = ConstraintWeight::from_ids([SubtractId(1), SubtractId(1), SubtractId(0)]);
    let var = CompactVar::covariant(TypeVar(7), weight);

    assert_eq!(var.var, TypeVar(7));
    assert!(var.weight.contains(SubtractId(0)));
    assert!(var.weight.contains(SubtractId(1)));
}

#[test]
fn contravariant_vars_drop_weight() {
    let var = CompactVar::contravariant(TypeVar(3));

    assert_eq!(var.var, TypeVar(3));
    assert!(var.weight.is_empty());
}

#[test]
fn compact_duplicate_constructor_args_generate_constraints() {
    let mut machine = ConstraintMachine::new();
    let root = TypeVar(0);
    let left = invariant_var(&mut machine, TypeVar(1));
    let right = invariant_var(&mut machine, TypeVar(2));
    let root_upper = machine.alloc_neg(Neg::Var(root));
    let left_box = machine.alloc_pos(Pos::Con(vec!["box".into()], vec![left]));
    let right_box = machine.alloc_pos(Pos::Con(vec!["box".into()], vec![right]));
    machine.subtype(left_box, root_upper);
    machine.subtype(right_box, root_upper);

    let (compact, constraints) = compact_type_var_recording_merge_constraints(&machine, root);

    assert_eq!(compact.root.cons.len(), 1);
    assert!(!constraints.is_empty());
    assert!(apply_merge_constraints_until_quiescent(&mut machine, root));
}

#[test]
fn compact_stack_family_and_row_item_coexistence_generate_constraints() {
    let mut machine = ConstraintMachine::new();
    let root = TypeVar(0);
    let tail = TypeVar(1);
    let stack_arg = invariant_var(&mut machine, TypeVar(2));
    let row_arg = invariant_var(&mut machine, TypeVar(3));
    let effect_path = vec!["parse".into()];
    let stack_weight = ConstraintWeight::push(
        SubtractId(9),
        Subtractability::Set(effect_path.clone(), vec![stack_arg]),
    );
    let tail_var = machine.alloc_pos(Pos::Var(tail));
    let stacked_tail = machine.alloc_pos(Pos::Stack {
        inner: tail_var,
        weight: stack_weight,
    });
    let row_item = machine.alloc_pos(Pos::Con(effect_path, vec![row_arg]));
    let row = machine.alloc_pos(Pos::Row(vec![row_item]));
    let root_upper = machine.alloc_neg(Neg::Var(root));
    machine.subtype(stacked_tail, root_upper);
    machine.subtype(row, root_upper);

    let (compact, constraints) = compact_type_var_recording_merge_constraints(&machine, root);

    assert_eq!(compact.root.rows.len(), 1);
    assert!(!constraints.is_empty());
    assert!(apply_merge_constraints_until_quiescent(&mut machine, root));
}

#[test]
fn role_arg_coalesce_records_merge_constraints() {
    let lhs_center = TypeVar(1);
    let rhs_center = TypeVar(2);
    let shared = TypeVar(3);
    let role_arg = |subject: TypeVar, other| {
        CompactRoleArg::invariant(CompactBounds::Interval {
            lower: CompactType {
                vars: vec![CompactVar::plain(subject), CompactVar::plain(other)],
                ..CompactType::default()
            },
            upper: CompactType {
                vars: vec![CompactVar::plain(subject), CompactVar::plain(other)],
                ..CompactType::default()
            },
        })
    };
    let (roles, constraints) =
        crate::role_solve::coalesce_role_constraints_recording_merge_constraints(vec![
            CompactRoleConstraint {
                role: vec!["Same".into()],
                inputs: vec![role_arg(lhs_center, shared)],
                associated: Vec::new(),
            },
            CompactRoleConstraint {
                role: vec!["Same".into()],
                inputs: vec![role_arg(rhs_center, shared)],
                associated: Vec::new(),
            },
        ]);

    assert_eq!(roles.len(), 1);
    assert!(constraints.iter().any(|constraint| {
        matches!(
            (&constraint.lhs, &constraint.rhs),
            (
                CompactBounds::Interval { .. },
                CompactBounds::Interval { .. }
            )
        )
    }));
    let CompactBounds::Interval { lower, upper, .. } = &roles[0].inputs[0].bounds else {
        panic!("merged role arg should remain interval");
    };
    assert!(lower.vars.iter().any(|var| var.var == lhs_center));
    assert!(lower.vars.iter().any(|var| var.var == rhs_center));
    assert!(upper.vars.iter().any(|var| var.var == lhs_center));
    assert!(upper.vars.iter().any(|var| var.var == rhs_center));
}

#[test]
fn compact_popped_stack_family_still_merges_with_coexisting_row_item() {
    let mut machine = ConstraintMachine::new();
    let root = TypeVar(0);
    let tail = TypeVar(1);
    let stack_arg = invariant_var(&mut machine, TypeVar(2));
    let row_arg = invariant_var(&mut machine, TypeVar(3));
    let subtract = SubtractId(11);
    let effect_path = vec!["parse".into()];
    let stack_weight = ConstraintWeight::push(
        subtract,
        Subtractability::Set(effect_path.clone(), vec![stack_arg]),
    );
    let tail_var = machine.alloc_pos(Pos::Var(tail));
    let stacked_tail = machine.alloc_pos(Pos::Stack {
        inner: tail_var,
        weight: stack_weight,
    });
    let popped_tail = machine.alloc_pos(Pos::NonSubtract(stacked_tail, subtract));
    let row_item = machine.alloc_pos(Pos::Con(effect_path, vec![row_arg]));
    let row = machine.alloc_pos(Pos::Row(vec![row_item]));
    let root_upper = machine.alloc_neg(Neg::Var(root));
    machine.subtype(popped_tail, root_upper);
    machine.subtype(row, root_upper);

    let (compact, constraints) = compact_type_var_recording_merge_constraints(&machine, root);

    assert!(compact.root.vars.iter().all(|var| var.weight.is_empty()));
    assert_eq!(compact.root.rows.len(), 1);
    assert!(!constraints.is_empty());
    assert!(apply_merge_constraints_until_quiescent(&mut machine, root));
}

#[test]
fn compact_neg_row_tail_cycle_keeps_residual_tail_var() {
    let mut machine = ConstraintMachine::new();
    let tail = TypeVar(1);
    let item = machine.alloc_neg(Neg::Con(vec!["io".into()], Vec::new()));
    let tail_upper = machine.alloc_neg(Neg::Var(tail));
    let row = machine.alloc_neg(Neg::Row(vec![item], tail_upper));
    let tail_lower = machine.alloc_pos(Pos::Var(tail));
    machine.subtype(tail_lower, row);

    let mut collector = CompactCollector::new(&machine);
    let compact = collector.compact_neg_row_tail_var(tail, ConstraintWeight::empty());

    assert!(compact_type_contains_var(&compact, tail));
    assert!(compact_row_contains_path(&compact, "io"));
}

#[test]
fn compact_neg_row_tail_does_not_alias_weighted_var_var_bound() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let through = TypeVar(1);
    let tail = TypeVar(2);
    let subtract = SubtractId(0);
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let through_neg = machine.alloc_neg(Neg::Var(through));
    let weights = ConstraintWeights {
        left: StackWeight::push(subtract, Subtractability::Empty),
        right: StackWeight::empty(),
    };

    machine.weighted_subtype(source_pos, weights, through_neg);

    let item = machine.alloc_neg(Neg::Con(vec!["redo".into()], Vec::new()));
    let row_tail = machine.alloc_neg(Neg::Var(tail));
    let row = machine.alloc_neg(Neg::Row(vec![item], row_tail));
    let through_pos = machine.alloc_pos(Pos::Var(through));
    machine.subtype(through_pos, row);

    let mut collector = CompactCollector::new(&machine);
    let compact = collector.compact_neg_row_tail_var(source, ConstraintWeight::empty());

    assert!(compact_type_contains_var(&compact, source));
    assert!(!compact_type_contains_var(&compact, through));
    assert!(!compact_row_contains_path(&compact, "redo"));
}

#[test]
fn interval_stores_only_lower_and_upper_bounds() {
    let bounds = CompactBounds::Interval {
        lower: CompactType::from_var(CompactVar::plain(TypeVar(2))),
        upper: CompactType::default(),
    };

    let CompactBounds::Interval { lower, upper } = bounds else {
        panic!("expected interval");
    };
    assert_eq!(lower.vars, vec![CompactVar::plain(TypeVar(2))]);
    assert!(upper.is_empty());
}

#[test]
fn collect_pushes_weight_into_covariant_type_argument_vars() {
    let mut machine = ConstraintMachine::new();
    let root = TypeVar(0);
    let payload = TypeVar(1);
    let payload_pos = machine.alloc_pos(Pos::Var(payload));
    let payload_neg = machine.alloc_neg(Neg::Var(payload));
    let payload_neu = machine.alloc_neu(Neu::Bounds(payload_pos, payload_neg));
    let list = machine.alloc_pos(Pos::Con(vec!["list".into()], vec![payload_neu]));
    let root_upper = machine.alloc_neg(Neg::Var(root));
    machine.weighted_subtype(
        list,
        ConstraintWeights::empty().with_left(SubtractId(4)),
        root_upper,
    );

    let compact = compact_type_var(&machine, root);
    let list = compact
        .root
        .cons
        .iter()
        .find(|(path, _)| compact_path_is(path.as_slice(), "list"))
        .expect("list lower bound should be collected");
    let CompactBounds::Interval { lower, upper, .. } = &list.1[0] else {
        panic!("list payload should be an interval");
    };

    let payload_lower = lower
        .vars
        .iter()
        .find(|var| var.var == payload)
        .expect("payload var");
    assert!(payload_lower.weight.contains(SubtractId(4)));
    assert_eq!(payload_lower.origin, CompactVarOrigin::Primary);
    assert!(
        upper
            .vars
            .iter()
            .all(|var| var.var != payload || var.weight.is_empty())
    );
}

#[test]
fn collect_pushes_weight_into_expanded_covariant_var_bounds() {
    let mut machine = ConstraintMachine::new();
    let root = TypeVar(0);
    let payload = TypeVar(1);
    let subtract = SubtractId(4);
    let payload_pos = machine.alloc_pos(Pos::Var(payload));
    let lower = machine.alloc_pos(Pos::NonSubtract(payload_pos, subtract));
    let root_upper = machine.alloc_neg(Neg::Var(root));

    machine.subtype(lower, root_upper);

    let compact = compact_type_var(&machine, root);

    let payload_var = compact
        .root
        .vars
        .iter()
        .find(|var| var.var == payload)
        .expect("payload var");
    assert!(payload_var.weight.contains(subtract));
    assert_eq!(payload_var.origin, CompactVarOrigin::Secondary);
}

#[test]
fn collect_composes_lower_bound_weight_before_outer_weight() {
    let mut machine = ConstraintMachine::new();
    let root = TypeVar(0);
    let outer = TypeVar(1);
    let inner = TypeVar(2);
    let subtract = SubtractId(4);

    let inner_pos = machine.alloc_pos(Pos::Var(inner));
    let pushed_inner = machine.alloc_pos(Pos::Stack {
        inner: inner_pos,
        weight: ConstraintWeight::push(subtract, Subtractability::Empty),
    });
    let outer_upper = machine.alloc_neg(Neg::Var(outer));
    machine.subtype(pushed_inner, outer_upper);

    let outer_pos = machine.alloc_pos(Pos::Var(outer));
    let popped_outer = machine.alloc_pos(Pos::Stack {
        inner: outer_pos,
        weight: ConstraintWeight::pop(subtract),
    });
    let root_upper = machine.alloc_neg(Neg::Var(root));
    machine.subtype(popped_outer, root_upper);

    let compact = compact_type_var(&machine, root);

    assert!(
        compact
            .root
            .vars
            .iter()
            .any(|var| var.var == inner && var.weight.is_empty()),
        "{:?}",
        compact.root
    );
    assert!(
        compact.root.vars.iter().all(|var| {
            var.weight.entries().iter().all(|entry| {
                !entry
                    .stack
                    .iter()
                    .any(|item| matches!(item, Subtractability::Empty))
            })
        }),
        "{:?}",
        compact.root
    );
}

#[test]
fn collect_stops_bare_variable_bounds_but_expands_structured_tails() {
    let mut machine = ConstraintMachine::new();
    let epsilon = TypeVar(1);
    let zeta = TypeVar(2);
    let gamma = TypeVar(3);
    let eta = TypeVar(4);

    let io = machine.alloc_neg(Neg::Con(vec!["io".into()], Vec::new()));
    let eta_tail = machine.alloc_neg(Neg::Var(eta));
    let epsilon_row = machine.alloc_neg(Neg::Row(vec![io], eta_tail));
    let epsilon_pos = machine.alloc_pos(Pos::Var(epsilon));
    machine.subtype(epsilon_pos, epsilon_row);

    let flip = machine.alloc_neg(Neg::Con(vec!["flip".into()], Vec::new()));
    let gamma_tail = machine.alloc_neg(Neg::Var(gamma));
    let zeta_row = machine.alloc_neg(Neg::Row(vec![flip], gamma_tail));
    let zeta_pos = machine.alloc_pos(Pos::Var(zeta));
    machine.subtype(zeta_pos, zeta_row);

    let epsilon_neg = machine.alloc_neg(Neg::Var(epsilon));
    let undet = machine.alloc_neg(Neg::Con(vec!["undet".into()], Vec::new()));
    let zeta_tail = machine.alloc_neg(Neg::Var(zeta));
    let structured_row = machine.alloc_neg(Neg::Row(vec![undet], zeta_tail));

    let mut collector = CompactCollector::new(&machine);
    let bare = collector.compact_neg_bound_id(epsilon_neg, ConstraintWeight::empty());
    let structured = collector.compact_neg_id(structured_row, ConstraintWeight::empty());

    assert!(bare.vars.iter().any(|var| var.var == epsilon));
    assert!(!compact_row_contains_path(&bare, "io"));
    assert!(compact_row_contains_path(&structured, "undet"));
    assert!(compact_row_contains_path(&structured, "flip"));
}

#[test]
fn positive_row_variables_are_collected_as_flat_vars() {
    let mut machine = ConstraintMachine::new();
    let root = TypeVar(0);
    let alpha = TypeVar(1);
    let gamma = TypeVar(2);
    let alpha_item = machine.alloc_pos(Pos::Var(alpha));
    let gamma_item = machine.alloc_pos(Pos::Var(gamma));
    let io_item = machine.alloc_pos(Pos::Con(vec!["io".into()], Vec::new()));
    let row = machine.alloc_pos(Pos::Row(vec![alpha_item, gamma_item, io_item]));
    let root_upper = machine.alloc_neg(Neg::Var(root));
    machine.subtype(row, root_upper);

    let compact = compact_type_var(&machine, root);

    assert!(compact.root.vars.iter().any(|var| var.var == alpha));
    assert!(compact.root.vars.iter().any(|var| var.var == gamma));
    assert!(compact_row_contains_path(&compact.root, "io"));
}

#[test]
fn reachable_role_collect_pulls_roles_from_main_type_frontier() {
    let mut machine = ConstraintMachine::new();
    let root_var = TypeVar(0);
    let output_var = TypeVar(1);
    let next_var = TypeVar(2);
    let unrelated_var = TypeVar(3);
    let seed = CompactRoot {
        root: CompactType::from_var(CompactVar::plain(root_var)),
        rec_vars: Vec::new(),
    };
    let constraints = vec![
        RoleConstraint {
            role: vec!["First".into()],
            inputs: vec![role_arg(&mut machine, root_var)],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_arg(&mut machine, output_var),
            }],
        },
        RoleConstraint {
            role: vec!["Second".into()],
            inputs: vec![role_arg(&mut machine, output_var)],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_arg(&mut machine, next_var),
            }],
        },
        RoleConstraint {
            role: vec!["Unrelated".into()],
            inputs: vec![role_arg(&mut machine, unrelated_var)],
            associated: Vec::new(),
        },
    ];

    let roles = compact_reachable_role_constraints(&machine, &seed, &constraints);

    assert_eq!(roles.len(), 2);
    assert_eq!(roles[0].role, vec!["First".to_string()]);
    assert_eq!(roles[1].role, vec!["Second".to_string()]);
    let CompactBounds::Interval { lower, .. } = &roles[0].associated[0].value.bounds else {
        panic!("associated output should remain interval");
    };
    assert!(lower.vars.iter().any(|var| var.var == output_var));
}

#[test]
fn polar_elimination_removes_one_sided_vars() {
    let machine = ConstraintMachine::new();
    let mut root = CompactRoot {
        root: CompactType::from_fun(CompactFun {
            arg: CompactType::from_var(CompactVar::plain(TypeVar(1))),
            arg_eff: CompactType::default(),
            ret_eff: CompactType::default(),
            ret: CompactType::from_var(CompactVar::plain(TypeVar(2))),
        }),
        rec_vars: Vec::new(),
    };

    let substitutions = eliminate_polar_variables(&machine, TypeLevel::root(), &mut root);

    let fun = &root.root.funs[0];
    assert!(fun.arg.vars.is_empty());
    assert!(fun.ret.vars.is_empty());
    assert_eq!(
        substitutions,
        vec![
            CompactVarSubstitution {
                source: TypeVar(1),
                target: None
            },
            CompactVarSubstitution {
                source: TypeVar(2),
                target: None
            }
        ]
    );
}

#[test]
fn polar_elimination_keeps_low_level_one_sided_vars() {
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

    let substitutions = eliminate_polar_variables(&machine, TypeLevel::root().child(), &mut root);

    assert_eq!(root.root.vars, vec![CompactVar::plain(outer)]);
    assert_eq!(
        substitutions,
        vec![CompactVarSubstitution {
            source: inner,
            target: None
        }]
    );
}

#[test]
fn polar_elimination_keeps_recursive_interval_var() {
    let machine = ConstraintMachine::new();
    let center = TypeVar(1);
    let one_sided = TypeVar(2);
    let mut root = CompactRoot {
        root: CompactType::default(),
        rec_vars: vec![CompactRecursiveVar {
            var: center,
            bounds: CompactBounds::Interval {
                lower: CompactType::from_var(CompactVar::plain(one_sided)),
                upper: CompactType::default(),
            },
        }],
    };

    let substitutions = eliminate_polar_variables(&machine, TypeLevel::root(), &mut root);

    assert_eq!(root.rec_vars[0].var, center);
    assert!(matches!(
        &root.rec_vars[0].bounds,
        CompactBounds::Interval { lower, .. } if lower.vars.is_empty()
    ));
    assert_eq!(
        substitutions,
        vec![CompactVarSubstitution {
            source: one_sided,
            target: None
        }]
    );
}

#[test]
fn co_occurrence_unifies_indistinguishable_vars() {
    let machine = ConstraintMachine::new();
    let mut root = CompactRoot {
        root: CompactType {
            vars: vec![
                CompactVar::plain(TypeVar(10)),
                CompactVar::plain(TypeVar(11)),
            ],
            ..CompactType::default()
        },
        rec_vars: Vec::new(),
    };

    let substitutions = coalesce_by_co_occurrence(&machine, TypeLevel::root(), &mut root);

    assert_eq!(root.root.vars.len(), 1);
    assert_eq!(root.root.vars[0].var, TypeVar(10));
    assert_eq!(
        substitutions,
        vec![CompactVarSubstitution {
            source: TypeVar(11),
            target: Some(TypeVar(10))
        }]
    );
}

#[test]
fn co_occurrence_keeps_one_sided_interval_bounds_distinct() {
    let machine = ConstraintMachine::new();
    let center = TypeVar(1);
    let lower_var = TypeVar(2);
    let upper_var = TypeVar(3);
    let mut root = CompactRoot {
        root: CompactType::default(),
        rec_vars: vec![CompactRecursiveVar {
            var: center,
            bounds: CompactBounds::Interval {
                lower: CompactType::from_var(CompactVar::plain(lower_var)),
                upper: CompactType::from_var(CompactVar::plain(upper_var)),
            },
        }],
    };

    let substitutions = coalesce_by_co_occurrence(&machine, TypeLevel::root(), &mut root);

    assert!(substitutions.is_empty());
    assert!(matches!(
        &root.rec_vars[0].bounds,
        CompactBounds::Interval { lower, upper } if lower.vars == vec![CompactVar::plain(lower_var)]
            && upper.vars == vec![CompactVar::plain(upper_var)]
    ));
}

#[test]
fn co_occurrence_interval_without_common_var_keeps_bounds_open() {
    let machine = ConstraintMachine::new();
    let center = TypeVar(56);
    let lower_var = TypeVar(34);
    let mut root = CompactRoot {
        root: CompactType::from_fun(CompactFun {
            arg: CompactType::default(),
            arg_eff: CompactType::default(),
            ret_eff: CompactType::from_var(CompactVar::plain(center)),
            ret: CompactType::default(),
        }),
        rec_vars: vec![CompactRecursiveVar {
            var: center,
            bounds: CompactBounds::Interval {
                lower: CompactType {
                    vars: vec![CompactVar::plain(lower_var)],
                    funs: vec![CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::from_var(CompactVar::plain(center)),
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
        }],
    };

    let substitutions = coalesce_by_co_occurrence(&machine, TypeLevel::root(), &mut root);

    assert!(substitutions.is_empty());
    assert_eq!(root.rec_vars[0].var, center);
    assert!(matches!(
        &root.rec_vars[0].bounds,
        CompactBounds::Interval { lower, .. } if lower.vars == vec![CompactVar::plain(lower_var)]
            && lower.funs[0].ret_eff.vars == vec![CompactVar::plain(center)]
    ));
}

#[test]
fn co_occurrence_ignores_secondary_marker_for_representative() {
    let machine = ConstraintMachine::new();
    let mut root = CompactRoot {
        root: CompactType {
            vars: vec![
                CompactVar::plain(TypeVar(10)).secondary(),
                CompactVar::plain(TypeVar(11)),
            ],
            ..CompactType::default()
        },
        rec_vars: Vec::new(),
    };

    let substitutions = coalesce_by_co_occurrence(&machine, TypeLevel::root(), &mut root);

    assert_eq!(root.root.vars.len(), 1);
    assert_eq!(root.root.vars[0].var, TypeVar(10));
    assert_eq!(root.root.vars[0].origin, CompactVarOrigin::Secondary);
    assert_eq!(
        substitutions,
        vec![CompactVarSubstitution {
            source: TypeVar(11),
            target: Some(TypeVar(10))
        }]
    );
}

#[test]
fn co_occurrence_ignores_weight_and_unions_ids_after_substitution() {
    let machine = ConstraintMachine::new();
    let first = SubtractId(1);
    let second = SubtractId(2);
    let mut root = CompactRoot {
        root: CompactType {
            vars: vec![
                CompactVar::covariant(TypeVar(10), ConstraintWeight::from_ids([first])),
                CompactVar::covariant(TypeVar(11), ConstraintWeight::from_ids([second])),
            ],
            ..CompactType::default()
        },
        rec_vars: Vec::new(),
    };

    let substitutions = coalesce_by_co_occurrence(&machine, TypeLevel::root(), &mut root);

    assert_eq!(root.root.vars.len(), 1);
    assert_eq!(root.root.vars[0].var, TypeVar(10));
    assert!(root.root.vars[0].weight.contains(first));
    assert!(root.root.vars[0].weight.contains(second));
    assert_eq!(
        substitutions,
        vec![CompactVarSubstitution {
            source: TypeVar(11),
            target: Some(TypeVar(10))
        }]
    );
}

#[test]
fn co_occurrence_removes_variable_sandwiched_by_exact_type() {
    let machine = ConstraintMachine::new();
    let var = TypeVar(10);
    let mut root = CompactRoot {
        root: CompactType::from_fun(CompactFun {
            arg: merge_compact_types(
                true,
                CompactType::from_var(CompactVar::plain(var)),
                CompactType::from_builtin(BuiltinType::Int),
            ),
            arg_eff: CompactType::default(),
            ret_eff: CompactType::default(),
            ret: merge_compact_types(
                true,
                CompactType::from_var(CompactVar::plain(var)),
                CompactType::from_builtin(BuiltinType::Int),
            ),
        }),
        rec_vars: Vec::new(),
    };

    let substitutions = coalesce_by_co_occurrence(&machine, TypeLevel::root(), &mut root);

    let fun = &root.root.funs[0];
    assert!(fun.arg.vars.is_empty());
    assert!(fun.ret.vars.is_empty());
    assert_eq!(fun.arg.builtins, vec![BuiltinType::Int]);
    assert_eq!(fun.ret.builtins, vec![BuiltinType::Int]);
    assert_eq!(
        substitutions,
        vec![CompactVarSubstitution {
            source: var,
            target: None
        }]
    );
}

#[test]
fn floor_redundant_elimination_removes_exact_sandwiched_floor_var() {
    let machine = ConstraintMachine::new();
    let var = TypeVar(10);
    let mut root = CompactRoot {
        root: CompactType::from_fun(CompactFun {
            arg: merge_compact_types(
                true,
                CompactType::from_var(CompactVar::plain(var)),
                CompactType::from_builtin(BuiltinType::Int),
            ),
            arg_eff: CompactType::default(),
            ret_eff: CompactType::default(),
            ret: merge_compact_types(
                true,
                CompactType::from_var(CompactVar::plain(var)),
                CompactType::from_builtin(BuiltinType::Int),
            ),
        }),
        rec_vars: Vec::new(),
    };

    let substitutions =
        eliminate_floor_redundant_variables(&machine, TypeLevel::root(), &mut root, &mut []);

    let fun = &root.root.funs[0];
    assert!(fun.arg.vars.is_empty());
    assert!(fun.ret.vars.is_empty());
    assert_eq!(fun.arg.builtins, vec![BuiltinType::Int]);
    assert_eq!(fun.ret.builtins, vec![BuiltinType::Int]);
    assert_eq!(
        substitutions,
        vec![CompactVarSubstitution {
            source: var,
            target: None
        }]
    );
}

#[test]
fn floor_redundant_elimination_keeps_bare_floor_var() {
    let machine = ConstraintMachine::new();
    let var = TypeVar(10);
    let mut root = CompactRoot {
        root: CompactType::from_var(CompactVar::plain(var)),
        rec_vars: Vec::new(),
    };

    let substitutions =
        eliminate_floor_redundant_variables(&machine, TypeLevel::root(), &mut root, &mut []);

    assert_eq!(root.root.vars, vec![CompactVar::plain(var)]);
    assert!(substitutions.is_empty());
}

#[test]
fn co_occurrence_unifies_variable_sandwiched_by_variable() {
    let machine = ConstraintMachine::new();
    let center = TypeVar(10);
    let extra = TypeVar(11);
    let payload = CompactBounds::Interval {
        lower: CompactType {
            vars: vec![CompactVar::plain(center), CompactVar::plain(extra)],
            ..CompactType::default()
        },
        upper: CompactType::from_var(CompactVar::plain(center)),
    };
    let list = CompactType::from_con(CompactCon {
        path: vec!["list".into()],
        args: vec![payload],
    });
    let mut root = CompactRoot {
        root: CompactType::from_fun(CompactFun {
            arg: list.clone(),
            arg_eff: CompactType::default(),
            ret_eff: CompactType::default(),
            ret: list,
        }),
        rec_vars: Vec::new(),
    };

    let substitutions = coalesce_by_co_occurrence(&machine, TypeLevel::root(), &mut root);

    let CompactBounds::Interval { lower, upper, .. } = &root.root.funs[0]
        .arg
        .cons
        .get(&vec!["list".into()])
        .expect("list")[0]
    else {
        panic!("expected interval");
    };
    assert_eq!(lower.vars, vec![CompactVar::plain(center)]);
    assert_eq!(upper.vars, vec![CompactVar::plain(center)]);
    assert_eq!(
        substitutions,
        vec![CompactVarSubstitution {
            source: extra,
            target: Some(center)
        }]
    );
}

#[test]
fn co_occurrence_uses_role_interval_to_coalesce_returned_receiver_and_argument() {
    let machine = ConstraintMachine::new();
    let receiver = TypeVar(10);
    let argument = TypeVar(11);
    let payload = CompactBounds::Interval {
        lower: CompactType::from_var(CompactVar::plain(receiver)),
        upper: CompactType {
            vars: vec![CompactVar::plain(receiver), CompactVar::plain(argument)],
            ..CompactType::default()
        },
    };
    let mut root = CompactRoot {
        root: CompactType::from_fun(CompactFun {
            arg: CompactType::from_con(CompactCon {
                path: vec!["view".into()],
                args: vec![payload],
            }),
            arg_eff: CompactType::default(),
            ret_eff: CompactType::default(),
            ret: CompactType::from_fun(CompactFun {
                arg: CompactType::from_var(CompactVar::plain(argument)),
                arg_eff: CompactType::default(),
                ret_eff: CompactType::default(),
                ret: CompactType::from_var(CompactVar::plain(receiver)),
            }),
        }),
        rec_vars: Vec::new(),
    };
    let mut roles = vec![CompactRoleConstraint {
        role: vec!["Ord".into()],
        inputs: vec![CompactRoleArg::invariant(CompactBounds::Interval {
            lower: CompactType {
                vars: vec![CompactVar::plain(receiver), CompactVar::plain(argument)],
                ..CompactType::default()
            },
            upper: CompactType {
                vars: vec![CompactVar::plain(receiver), CompactVar::plain(argument)],
                ..CompactType::default()
            },
        })],
        associated: Vec::new(),
    }];

    let substitutions = simplify_compact_root_with_roles_and_non_generic(
        &machine,
        TypeLevel::root(),
        &mut root,
        &mut roles,
        &FxHashSet::default(),
    );

    let outer = &root.root.funs[0];
    let inner = &outer.ret.funs[0];
    assert_eq!(inner.arg.vars, vec![CompactVar::plain(receiver)]);
    assert_eq!(inner.ret.vars, vec![CompactVar::plain(receiver)]);
    let CompactBounds::Interval { lower, upper, .. } =
        &outer.arg.cons.get(&vec!["view".into()]).expect("view")[0]
    else {
        panic!("expected view payload interval");
    };
    assert_eq!(lower.vars, vec![CompactVar::plain(receiver)]);
    assert_eq!(upper.vars, vec![CompactVar::plain(receiver)]);
    let CompactBounds::Interval {
        lower: role_lower,
        upper: role_upper,
        ..
    } = &roles[0].inputs[0].bounds
    else {
        panic!("role arg should remain interval");
    };
    assert_eq!(role_lower.vars, vec![CompactVar::plain(receiver)]);
    assert_eq!(role_upper.vars, vec![CompactVar::plain(receiver)]);
    assert_eq!(
        substitutions.substitutions,
        vec![CompactVarSubstitution {
            source: argument,
            target: Some(receiver)
        }]
    );
}
