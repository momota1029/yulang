use super::*;

#[test]
fn finalize_restores_stack_weights_on_covariant_vars() {
    let subtract = SubtractId(3);
    let mut types = TypeArena::new();
    let compact = CompactType::from_var(CompactVar::covariant(
        TypeVar(10),
        ConstraintWeight::from_ids([subtract]),
    ));

    let pos = finalize_compact_type(&mut types, &compact);

    match types.pos(pos) {
        Pos::Stack { inner, weight } if weight == &ConstraintWeight::from_ids([subtract]) => {
            assert!(matches!(types.pos(*inner), Pos::Var(TypeVar(10))));
        }
        other => panic!("expected stack-weighted var, got {other:?}"),
    }
}

#[test]
fn finalize_restores_stack_weights_on_row_vars() {
    let subtract = SubtractId(4);
    let mut types = TypeArena::new();
    let compact = CompactType {
        vars: vec![CompactVar::covariant(
            TypeVar(11),
            ConstraintWeight::from_ids([subtract]),
        )],
        rows: vec![CompactRow {
            items: CompactRowItemMap::default(),
            tail: Box::new(CompactType::default()),
        }],
        ..CompactType::default()
    };

    let pos = finalize_compact_type(&mut types, &compact);

    let Pos::Row(items) = types.pos(pos) else {
        panic!("expected row");
    };
    assert_eq!(items.len(), 1);
    match types.pos(items[0]) {
        Pos::Stack { inner, weight } if weight == &ConstraintWeight::from_ids([subtract]) => {
            assert!(matches!(types.pos(*inner), Pos::Var(TypeVar(11))));
        }
        other => panic!("expected stack-weighted row var, got {other:?}"),
    }
}

#[test]
fn finalize_drops_filter_only_stack_weights_on_negative_vars() {
    let filter = Subtractability::Set(vec!["io".into()], Vec::new());
    let weight = StackWeight::filter(filter);
    let mut types = TypeArena::new();
    let compact = CompactType::from_var(CompactVar::contravariant_with_weight(TypeVar(12), weight));

    let neg = finalize_compact_type_to_neg(&mut types, &compact);

    assert!(matches!(types.neg(neg), Neg::Var(TypeVar(12))));
}

#[test]
fn finalize_strips_filter_from_non_empty_stack_weights() {
    let subtract = SubtractId(5);
    let filter = Subtractability::Set(vec!["io".into()], Vec::new());
    let weight = StackWeight::filter(filter).compose(&StackWeight::pop(subtract));
    let expected = StackWeight::pop(subtract);
    let mut types = TypeArena::new();
    let compact = CompactType::from_var(CompactVar::contravariant_with_weight(TypeVar(13), weight));

    let neg = finalize_compact_type_to_neg(&mut types, &compact);

    match types.neg(neg) {
        Neg::Stack { inner, weight } if weight == &expected => {
            assert!(matches!(types.neg(*inner), Neg::Var(TypeVar(13))));
        }
        other => panic!("expected stack-weighted negative var without filter, got {other:?}"),
    }
}

#[test]
fn co_occurrence_keeps_ref_update_like_effect_vars_distinct() {
    let machine = ConstraintMachine::new();
    let residual = TypeVar(1);
    let captured = TypeVar(2);
    let value = TypeVar(3);
    let mut root = CompactRoot {
        root: CompactType::from_fun(CompactFun {
            arg: CompactType::from_con(CompactCon {
                path: vec!["ref".into()],
                args: vec![
                    CompactBounds::Interval {
                        lower: CompactType::from_var(CompactVar::plain(residual)),
                        upper: CompactType {
                            vars: vec![CompactVar::plain(residual), CompactVar::plain(captured)],
                            ..CompactType::default()
                        },
                    },
                    CompactBounds::Interval {
                        lower: CompactType::from_var(CompactVar::plain(value)),
                        upper: CompactType::from_var(CompactVar::plain(value)),
                    },
                ],
            }),
            arg_eff: CompactType::default(),
            ret_eff: CompactType::default(),
            ret: CompactType::from_fun(CompactFun {
                arg: CompactType::from_fun(CompactFun {
                    arg: CompactType::from_var(CompactVar::plain(value)),
                    arg_eff: CompactType::default(),
                    ret_eff: CompactType::from_var(CompactVar::plain(captured)),
                    ret: CompactType::from_var(CompactVar::plain(value)),
                }),
                arg_eff: CompactType::default(),
                ret_eff: CompactType {
                    vars: vec![CompactVar::plain(residual), CompactVar::plain(captured)],
                    ..CompactType::default()
                },
                ret: CompactType::default(),
            }),
        }),
        rec_vars: Vec::new(),
    };

    coalesce_by_co_occurrence(&machine, TypeLevel::root(), &mut root);

    let outer = &root.root.funs[0];
    let receiver = CompactCon {
        path: vec!["ref".into()],
        args: outer
            .arg
            .cons
            .get(&vec!["ref".into()])
            .expect("ref")
            .clone(),
    };
    assert_eq!(
        receiver.args[0],
        CompactBounds::Interval {
            lower: CompactType::from_var(CompactVar::plain(residual)),
            upper: CompactType {
                vars: vec![CompactVar::plain(residual), CompactVar::plain(captured)],
                ..CompactType::default()
            }
        }
    );
    let callback = &outer.ret.funs[0].arg.funs[0];
    assert_eq!(callback.ret_eff.vars, vec![CompactVar::plain(captured)]);
    assert_eq!(
        outer.ret.funs[0].ret_eff.vars,
        vec![CompactVar::plain(residual), CompactVar::plain(captured)]
    );
}

#[test]
fn co_occurrence_does_not_merge_low_level_vars_together() {
    let mut machine = ConstraintMachine::new();
    let first_outer = TypeVar(1);
    let second_outer = TypeVar(2);
    machine.register_type_var(first_outer, TypeLevel::root());
    machine.register_type_var(second_outer, TypeLevel::root());
    let mut root = CompactRoot {
        root: CompactType {
            vars: vec![
                CompactVar::plain(first_outer),
                CompactVar::plain(second_outer),
            ],
            ..CompactType::default()
        },
        rec_vars: Vec::new(),
    };

    let substitutions = coalesce_by_co_occurrence(&machine, TypeLevel::root().child(), &mut root);

    assert_eq!(
        root.root.vars,
        vec![
            CompactVar::plain(first_outer),
            CompactVar::plain(second_outer)
        ]
    );
    assert!(substitutions.is_empty());
}

#[test]
fn co_occurrence_rewrites_high_level_var_to_low_level_representative() {
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

    let substitutions = coalesce_by_co_occurrence(&machine, TypeLevel::root().child(), &mut root);

    assert_eq!(root.root.vars, vec![CompactVar::plain(outer)]);
    assert_eq!(
        substitutions,
        vec![CompactVarSubstitution {
            source: inner,
            target: Some(outer)
        }]
    );
}

#[test]
fn sandwich_lifts_list_and_reuses_common_interval_var() {
    let machine = ConstraintMachine::new();
    let center = TypeVar(1);
    let payload = TypeVar(2);
    let mut root = CompactRoot {
        root: CompactType::from_con(CompactCon {
            path: vec!["box".into()],
            args: vec![CompactBounds::Interval {
                lower: list_with_payload_bound(
                    center,
                    CompactBounds::Interval {
                        lower: CompactType::from_var(CompactVar::plain(payload)),
                        upper: CompactType::default(),
                    },
                ),
                upper: list_with_payload_bound(
                    center,
                    CompactBounds::Interval {
                        lower: CompactType::default(),
                        upper: CompactType::from_var(CompactVar::plain(payload)),
                    },
                ),
            }],
        }),
        rec_vars: Vec::new(),
    };

    let sandwiches = sandwich_compact_root(&machine, TypeLevel::root(), &mut root);

    let CompactBounds::Con { path, args } =
        &root.root.cons.get(&vec!["box".into()]).expect("box")[0]
    else {
        panic!("box payload should be lifted to list");
    };
    assert!(compact_path_is(path, "list"));
    let CompactBounds::Interval { lower, upper } = &args[0] else {
        panic!("list payload should remain interval");
    };
    assert!(lower.vars.iter().any(|var| var.var == payload));
    assert!(upper.vars.iter().any(|var| var.var == payload));
    assert_eq!(
        sandwiches,
        vec![CompactSandwich {
            var: center,
            kind: CompactSandwichKind::Con {
                path: vec!["list".into()],
                arity: 1
            }
        }]
    );
}

#[test]
fn sandwich_role_bare_occurrence_blocks_lift() {
    let machine = ConstraintMachine::new();
    let center = TypeVar(1);
    let payload = TypeVar(2);
    let mut root = CompactRoot {
        root: CompactType::from_con(CompactCon {
            path: vec!["box".into()],
            args: vec![CompactBounds::Interval {
                lower: list_with_payload_bound(
                    center,
                    CompactBounds::Interval {
                        lower: CompactType::from_var(CompactVar::plain(payload)),
                        upper: CompactType::default(),
                    },
                ),
                upper: list_with_payload_bound(
                    center,
                    CompactBounds::Interval {
                        lower: CompactType::default(),
                        upper: CompactType::from_var(CompactVar::plain(payload)),
                    },
                ),
            }],
        }),
        rec_vars: Vec::new(),
    };
    let mut roles = vec![CompactRoleConstraint {
        role: vec!["Pinned".into()],
        inputs: vec![CompactRoleArg::invariant(CompactBounds::Interval {
            lower: CompactType::from_var(CompactVar::plain(center)),
            upper: CompactType::from_var(CompactVar::plain(center)),
        })],
        associated: Vec::new(),
    }];

    let sandwiches =
        sandwich_compact_root_with_roles(&machine, TypeLevel::root(), &mut root, &mut roles);

    assert!(sandwiches.is_empty());
    assert!(matches!(
        &root.root.cons.get(&vec!["box".into()]).expect("box")[0],
        CompactBounds::Interval { lower, upper }
            if lower.vars.iter().any(|var| var.var == center)
                && upper.vars.iter().any(|var| var.var == center)
    ));
}

#[test]
fn sandwich_rewrites_nested_role_predicate_bounds() {
    let machine = ConstraintMachine::new();
    let center = TypeVar(1);
    let payload = TypeVar(2);
    let role_self = TypeVar(3);
    let mut root = CompactRoot::default();
    let mut roles = vec![CompactRoleConstraint {
        role: vec!["Ready".into()],
        inputs: vec![CompactRoleArg::invariant(CompactBounds::Interval {
            lower: merge_compact_types(
                true,
                CompactType::from_var(CompactVar::plain(role_self)),
                CompactType::from_con(CompactCon {
                    path: vec!["box".into()],
                    args: vec![CompactBounds::Interval {
                        lower: list_with_payload_bound(
                            center,
                            CompactBounds::Interval {
                                lower: CompactType::from_var(CompactVar::plain(payload)),
                                upper: CompactType::default(),
                            },
                        ),
                        upper: list_with_payload_bound(
                            center,
                            CompactBounds::Interval {
                                lower: CompactType::default(),
                                upper: CompactType::from_var(CompactVar::plain(payload)),
                            },
                        ),
                    }],
                }),
            ),
            upper: CompactType::from_var(CompactVar::plain(role_self)),
        })],
        associated: Vec::new(),
    }];

    let sandwiches =
        sandwich_compact_root_with_roles(&machine, TypeLevel::root(), &mut root, &mut roles);

    let CompactBounds::Interval {
        lower: role_lower, ..
    } = &roles[0].inputs[0].bounds
    else {
        panic!("role arg should remain interval");
    };
    let CompactBounds::Con { path, args } =
        &role_lower.cons.get(&vec!["box".into()]).expect("box")[0]
    else {
        panic!("role predicate payload should be lifted to list");
    };
    assert!(compact_path_is(path, "list"));
    let CompactBounds::Interval { lower, upper } = &args[0] else {
        panic!("list payload should remain interval");
    };
    assert!(lower.vars.iter().any(|var| var.var == payload));
    assert!(upper.vars.iter().any(|var| var.var == payload));
    assert_eq!(
        sandwiches,
        vec![CompactSandwich {
            var: center,
            kind: CompactSandwichKind::Con {
                path: vec!["list".into()],
                arity: 1
            }
        }]
    );
}

#[test]
fn sandwich_lifts_list_without_freshening_interval_center() {
    let machine = ConstraintMachine::new();
    let center = TypeVar(1);
    let lower_payload = TypeVar(2);
    let upper_payload = TypeVar(3);
    let mut root = CompactRoot {
        root: CompactType::from_con(CompactCon {
            path: vec!["box".into()],
            args: vec![CompactBounds::Interval {
                lower: list_with_payload_bound(
                    center,
                    CompactBounds::Interval {
                        lower: CompactType::from_var(CompactVar::plain(lower_payload)),
                        upper: CompactType::default(),
                    },
                ),
                upper: list_with_payload_bound(
                    center,
                    CompactBounds::Interval {
                        lower: CompactType::default(),
                        upper: CompactType::from_var(CompactVar::plain(upper_payload)),
                    },
                ),
            }],
        }),
        rec_vars: Vec::new(),
    };

    let sandwiches = sandwich_compact_root(&machine, TypeLevel::root(), &mut root);

    let CompactBounds::Con { args, .. } = &root.root.cons.get(&vec!["box".into()]).expect("box")[0]
    else {
        panic!("box payload should be lifted to list");
    };
    let CompactBounds::Interval { lower, upper } = &args[0] else {
        panic!("list payload should remain interval");
    };
    assert!(lower.vars.iter().any(|var| var.var == lower_payload));
    assert!(upper.vars.iter().any(|var| var.var == upper_payload));
    assert_eq!(
        sandwiches,
        vec![CompactSandwich {
            var: center,
            kind: CompactSandwichKind::Con {
                path: vec!["list".into()],
                arity: 1
            }
        }]
    );
}

#[test]
fn sandwich_does_not_lift_low_level_vars() {
    let mut machine = ConstraintMachine::new();
    let center = TypeVar(1);
    let payload = TypeVar(2);
    machine.register_type_var(center, TypeLevel::root());
    machine.register_type_var(payload, TypeLevel::root().child());
    let mut root = CompactRoot {
        root: CompactType::from_con(CompactCon {
            path: vec!["box".into()],
            args: vec![CompactBounds::Interval {
                lower: list_with_payload_bound(
                    center,
                    CompactBounds::Interval {
                        lower: CompactType::from_var(CompactVar::plain(payload)),
                        upper: CompactType::default(),
                    },
                ),
                upper: list_with_payload_bound(
                    center,
                    CompactBounds::Interval {
                        lower: CompactType::default(),
                        upper: CompactType::from_var(CompactVar::plain(payload)),
                    },
                ),
            }],
        }),
        rec_vars: Vec::new(),
    };

    let sandwiches = sandwich_compact_root(&machine, TypeLevel::root().child(), &mut root);

    assert!(sandwiches.is_empty());
    assert!(matches!(
        &root.root.cons.get(&vec!["box".into()]).expect("box")[0],
        CompactBounds::Interval { .. }
    ));
}

#[test]
fn sandwich_lifts_without_stored_outer_interval_center() {
    let mut machine = ConstraintMachine::new();
    let inner = TypeVar(2);
    let payload = TypeVar(3);
    machine.register_type_var(inner, TypeLevel::root().child());
    machine.register_type_var(payload, TypeLevel::root().child());
    let mut root = CompactRoot {
        root: CompactType::from_con(CompactCon {
            path: vec!["box".into()],
            args: vec![CompactBounds::Interval {
                lower: list_with_payload_bound(
                    inner,
                    CompactBounds::Interval {
                        lower: CompactType::from_var(CompactVar::plain(payload)),
                        upper: CompactType::default(),
                    },
                ),
                upper: list_with_payload_bound(
                    inner,
                    CompactBounds::Interval {
                        lower: CompactType::default(),
                        upper: CompactType::from_var(CompactVar::plain(payload)),
                    },
                ),
            }],
        }),
        rec_vars: Vec::new(),
    };

    let sandwiches = sandwich_compact_root(&machine, TypeLevel::root().child(), &mut root);

    assert_eq!(
        sandwiches,
        vec![CompactSandwich {
            var: inner,
            kind: CompactSandwichKind::Con {
                path: vec!["list".into()],
                arity: 1
            }
        }]
    );
    assert!(matches!(
        &root.root.cons.get(&vec!["box".into()]).expect("box")[0],
        CompactBounds::Con { path, .. } if compact_path_is(path, "list")
    ));
}

#[test]
fn finalize_returns_pos_union_for_multiple_positive_parts() {
    let mut types = TypeArena::new();
    let ty = merge_compact_types(
        true,
        CompactType::from_var(CompactVar::plain(TypeVar(1))),
        CompactType::from_builtin(BuiltinType::Int),
    );

    let finalized = finalize_compact_type(&mut types, &ty);

    assert!(pos_contains_var(&types, finalized, TypeVar(1)));
    assert!(pos_contains_path(&types, finalized, "int"));
}

#[test]
fn finalize_preserves_function_polarity() {
    let mut types = TypeArena::new();
    let ty = CompactType::from_fun(CompactFun {
        arg: CompactType::from_var(CompactVar::plain(TypeVar(1))),
        arg_eff: CompactType::never(),
        ret_eff: CompactType::from_var(CompactVar::plain(TypeVar(2))),
        ret: CompactType::from_var(CompactVar::plain(TypeVar(3))),
    });

    let finalized = finalize_compact_type(&mut types, &ty);

    let Pos::Fun {
        arg,
        arg_eff,
        ret_eff,
        ret,
    } = types.pos(finalized)
    else {
        panic!("expected finalized function");
    };
    assert!(matches!(types.neg(*arg), Neg::Var(var) if *var == TypeVar(1)));
    assert!(matches!(types.neg(*arg_eff), Neg::Bot));
    assert!(matches!(types.pos(*ret_eff), Pos::Var(var) if *var == TypeVar(2)));
    assert!(matches!(types.pos(*ret), Pos::Var(var) if *var == TypeVar(3)));
}

#[test]
fn finalize_interval_bounds_to_neutral_bounds() {
    let mut types = TypeArena::new();
    let bounds = CompactBounds::Interval {
        lower: CompactType::from_builtin(BuiltinType::Unit),
        upper: CompactType::from_var(CompactVar::plain(TypeVar(8))),
    };

    let finalized = finalize_compact_bounds(&mut types, &bounds);

    let Neu::Bounds(lower, upper) = types.neu(finalized) else {
        panic!("expected neutral bounds");
    };
    assert!(pos_contains_path(&types, *lower, "unit"));
    assert!(matches!(types.neg(*upper), Neg::Var(var) if *var == TypeVar(8)));
}

#[test]
fn finalize_lifted_compact_bounds_to_neutral_constructor() {
    let mut types = TypeArena::new();
    let bounds = CompactBounds::Con {
        path: vec!["list".into()],
        args: vec![CompactBounds::Interval {
            lower: CompactType::from_var(CompactVar::plain(TypeVar(1))),
            upper: CompactType::from_var(CompactVar::plain(TypeVar(1))),
        }],
    };

    let finalized = finalize_compact_bounds(&mut types, &bounds);

    let Neu::Con(path, args) = types.neu(finalized) else {
        panic!("expected neutral constructor");
    };
    assert!(compact_path_is(path, "list"));
    let Neu::Bounds(lower, upper) = types.neu(args[0]) else {
        panic!("expected list payload bounds");
    };
    assert!(matches!(types.pos(*lower), Pos::Var(var) if *var == TypeVar(1)));
    assert!(matches!(types.neg(*upper), Neg::Var(var) if *var == TypeVar(1)));
}

#[test]
fn finalize_positive_row_flattens_tail_vars_into_row_items() {
    let mut types = TypeArena::new();
    let ty = CompactType {
        vars: vec![CompactVar::plain(TypeVar(1))],
        rows: vec![CompactRow {
            items: row_items_from_con(CompactCon {
                path: vec!["io".into()],
                args: Vec::new(),
            }),
            tail: Box::new(CompactType::default()),
        }],
        ..CompactType::default()
    };

    let finalized = finalize_compact_type(&mut types, &ty);

    let Pos::Row(items) = types.pos(finalized) else {
        panic!("expected positive row");
    };
    assert!(
        items
            .iter()
            .any(|item| { matches!(types.pos(*item), Pos::Var(var) if *var == TypeVar(1)) })
    );
    assert!(
        items
            .iter()
            .any(|item| pos_contains_path(&types, *item, "io"))
    );
}

#[test]
fn finalize_positive_row_merges_tail_effect_item_by_path() {
    let mut types = TypeArena::new();
    let ty = CompactType::from_row(CompactRow {
        items: row_items_from_con(effect_con_with_empty_payload(TypeVar(1))),
        tail: Box::new(CompactType::from_con(effect_con_with_empty_payload(
            TypeVar(2),
        ))),
    });

    let finalized = finalize_compact_type(&mut types, &ty);

    let Pos::Row(items) = types.pos(finalized) else {
        panic!("expected positive row");
    };
    let effect_items = items
        .iter()
        .filter_map(|item| match types.pos(*item) {
            Pos::Con(path, args) if compact_path_is(path, "effect") => Some(args),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(effect_items.len(), 1);
    let Neu::Bounds(lower, upper) = types.neu(effect_items[0][0]) else {
        panic!("expected merged effect payload interval");
    };
    assert!(pos_contains_var(&types, *lower, TypeVar(1)));
    assert!(pos_contains_var(&types, *lower, TypeVar(2)));
    assert!(neg_contains_var(&types, *upper, TypeVar(1)));
    assert!(neg_contains_var(&types, *upper, TypeVar(2)));
}

#[test]
fn finalize_root_preserves_recursive_side_table() {
    let mut types = TypeArena::new();
    let root = CompactRoot {
        root: CompactType::from_var(CompactVar::plain(TypeVar(1))),
        rec_vars: vec![CompactRecursiveVar {
            var: TypeVar(1),
            bounds: CompactBounds::Interval {
                lower: CompactType::from_con(CompactCon {
                    path: vec!["list".into()],
                    args: Vec::new(),
                }),
                upper: CompactType::default(),
            },
        }],
    };

    let finalized = finalize_compact_root(&mut types, &root);

    assert!(matches!(types.pos(finalized.root), Pos::Var(var) if *var == TypeVar(1)));
    assert_eq!(finalized.rec_vars.len(), 1);
    assert_eq!(finalized.rec_vars[0].var, TypeVar(1));
    let Neu::Bounds(lower, _) = types.neu(finalized.rec_vars[0].bounds) else {
        panic!("expected recursive bounds");
    };
    assert!(pos_contains_path(&types, *lower, "list"));
}

#[test]
fn merge_cons_by_path_combines_interval_lower_and_upper_bounds() {
    let merged = merge_compact_types(
        true,
        list_with_empty_payload(TypeVar(1)),
        list_with_empty_payload(TypeVar(2)),
    );

    assert_eq!(merged.cons.len(), 1);
    let CompactBounds::Interval { lower, upper } =
        &merged.cons.get(&vec!["list".into()]).expect("list cons")[0]
    else {
        panic!("expected merged payload interval");
    };
    assert!(compact_type_contains_var(lower, TypeVar(1)));
    assert!(compact_type_contains_var(lower, TypeVar(2)));
    assert!(compact_type_contains_var(upper, TypeVar(1)));
    assert!(compact_type_contains_var(upper, TypeVar(2)));
}

#[test]
fn interval_dominance_generates_bounds_consistency_and_witness_constraint() {
    let anchor = TypeVar(1);
    let witness_left = TypeVar(2);
    let witness_both = TypeVar(3);
    let upper_left = TypeVar(4);
    let upper_right = TypeVar(5);
    let root = CompactRoot {
        root: CompactType::from_var(CompactVar::plain(anchor)),
        rec_vars: Vec::new(),
    };
    let roles = vec![CompactRoleConstraint {
        role: vec!["Ord".into()],
        inputs: vec![CompactRoleArg::invariant(CompactBounds::Interval {
            lower: CompactType {
                vars: vec![
                    CompactVar::plain(anchor),
                    CompactVar::plain(witness_left),
                    CompactVar::plain(witness_both),
                ],
                ..CompactType::default()
            },
            upper: CompactType {
                vars: vec![
                    CompactVar::plain(witness_both),
                    CompactVar::plain(upper_left),
                    CompactVar::plain(upper_right),
                ],
                ..CompactType::default()
            },
        })],
        associated: Vec::new(),
    }];

    let constraints = collect_interval_dominance_constraints(&root, &roles);

    assert_eq!(constraints.len(), 2);
    assert!(constraints.iter().any(|constraint| {
        compact_type_contains_var(&constraint.lower, witness_left)
            && compact_type_contains_var(&constraint.upper, witness_both)
    }));
    assert!(constraints.iter().any(|constraint| {
        compact_type_contains_var(&constraint.lower, anchor)
            && !compact_type_contains_var(&constraint.lower, witness_left)
            && !compact_type_contains_var(&constraint.upper, witness_both)
            && compact_type_contains_var(&constraint.upper, upper_left)
            && compact_type_contains_var(&constraint.upper, upper_right)
    }));
}

#[test]
fn interval_dominance_generates_subtype_for_single_lower_variable() {
    let lower = TypeVar(1);
    let upper = TypeVar(2);
    let root = CompactRoot::default();
    let roles = vec![CompactRoleConstraint {
        role: vec!["Ord".into()],
        inputs: vec![CompactRoleArg::invariant(CompactBounds::Interval {
            lower: CompactType::from_var(CompactVar::plain(lower)),
            upper: merge_compact_types(
                false,
                CompactType::from_var(CompactVar::plain(lower)),
                CompactType::from_var(CompactVar::plain(upper)),
            ),
        })],
        associated: Vec::new(),
    }];

    let constraints = collect_interval_dominance_constraints(&root, &roles);

    assert_eq!(constraints.len(), 1);
    assert!(compact_type_contains_var(&constraints[0].lower, lower));
    assert!(compact_type_contains_var(&constraints[0].upper, upper));
}

#[test]
fn interval_dominance_does_not_emit_associated_constraints() {
    let lower = TypeVar(1);
    let upper = TypeVar(2);
    let root = CompactRoot::default();
    let roles = vec![CompactRoleConstraint {
        role: vec!["Iterator".into()],
        inputs: Vec::new(),
        associated: vec![CompactRoleAssociatedType {
            name: "Item".into(),
            value: CompactRoleArg::invariant(CompactBounds::Interval {
                lower: CompactType::from_var(CompactVar::plain(lower)),
                upper: CompactType::from_var(CompactVar::plain(upper)),
            }),
        }],
    }];

    let constraints = collect_interval_dominance_constraints(&root, &roles);

    assert!(constraints.is_empty());
}

#[test]
fn merge_rows_coalesces_con_items_by_path() {
    let merged = merge_compact_types(
        true,
        CompactType::from_row(CompactRow {
            items: row_items_from_con(effect_con_with_empty_payload(TypeVar(1))),
            tail: Box::new(CompactType::default()),
        }),
        CompactType::from_row(CompactRow {
            items: row_items_from_con(effect_con_with_empty_payload(TypeVar(2))),
            tail: Box::new(CompactType::default()),
        }),
    );

    assert_eq!(merged.rows.len(), 1);
    assert_eq!(merged.rows[0].items.len(), 1);
    let args = merged.rows[0]
        .items
        .get(&vec!["effect".into()])
        .expect("effect item");
    let CompactBounds::Interval { lower, upper, .. } = &args[0] else {
        panic!("expected merged effect payload interval");
    };
    assert!(compact_type_contains_var(lower, TypeVar(2)));
    assert!(compact_type_contains_var(upper, TypeVar(2)));
}

#[test]
fn row_and_con_same_path_records_payload_merge_constraints() {
    let mut constraints = Vec::new();

    let merged = merge_compact_types_with_sink(
        true,
        CompactType::from_row(CompactRow {
            items: row_items_from_con(effect_con_with_empty_payload(TypeVar(1))),
            tail: Box::new(CompactType::default()),
        }),
        CompactType::from_con(effect_con_with_empty_payload(TypeVar(2))),
        &mut constraints,
    );

    assert_eq!(merged.rows.len(), 1);
    assert_eq!(merged.cons.len(), 1);
    assert_eq!(constraints.len(), 1);
}

pub(super) fn compact_row_contains_path(compact: &CompactType, path: &str) -> bool {
    compact.rows.iter().any(|row| {
        row.items
            .keys()
            .any(|item_path| compact_path_is(item_path.as_slice(), path))
            || compact_type_contains_path(&row.tail, path)
    }) || compact_type_contains_path_without_rows(compact, path)
}

pub(super) fn compact_type_contains_path(compact: &CompactType, path: &str) -> bool {
    compact_type_contains_path_without_rows(compact, path)
        || compact.rows.iter().any(|row| {
            row.items
                .keys()
                .any(|item_path| compact_path_is(item_path.as_slice(), path))
                || compact_type_contains_path(&row.tail, path)
        })
}

pub(super) fn compact_type_contains_path_without_rows(compact: &CompactType, path: &str) -> bool {
    compact
        .cons
        .keys()
        .any(|con_path| compact_path_is(con_path.as_slice(), path))
        || compact
            .builtins
            .iter()
            .any(|builtin| builtin.surface_name() == path)
}

pub(super) fn compact_type_contains_var(compact: &CompactType, expected: TypeVar) -> bool {
    compact.vars.iter().any(|var| var.var == expected)
}

fn list_with_empty_payload(center: TypeVar) -> CompactType {
    CompactType::from_con(CompactCon {
        path: vec!["list".into()],
        args: vec![empty_interval(center)],
    })
}

fn effect_con_with_empty_payload(center: TypeVar) -> CompactCon {
    CompactCon {
        path: vec!["effect".into()],
        args: vec![empty_interval(center)],
    }
}

fn row_items_from_con(con: CompactCon) -> CompactRowItemMap {
    singleton_row_item_map(con.path, con.args)
}

fn empty_interval(center: TypeVar) -> CompactBounds {
    CompactBounds::Interval {
        lower: CompactType::from_var(CompactVar::plain(center)),
        upper: CompactType::from_var(CompactVar::plain(center)),
    }
}

pub(super) fn compact_path_is(actual: &[String], expected: &str) -> bool {
    actual.len() == 1 && actual[0] == expected
}

fn pos_contains_var(types: &TypeArena, id: PosId, expected: TypeVar) -> bool {
    match types.pos(id) {
        Pos::Var(var) => *var == expected,
        Pos::Row(items) => items
            .iter()
            .any(|item| pos_contains_var(types, *item, expected)),
        Pos::Union(left, right) => {
            pos_contains_var(types, *left, expected) || pos_contains_var(types, *right, expected)
        }
        _ => false,
    }
}

fn neg_contains_var(types: &TypeArena, id: NegId, expected: TypeVar) -> bool {
    match types.neg(id) {
        Neg::Var(var) => *var == expected,
        Neg::Row(items, tail) => {
            items
                .iter()
                .any(|item| neg_contains_var(types, *item, expected))
                || neg_contains_var(types, *tail, expected)
        }
        Neg::Intersection(left, right) => {
            neg_contains_var(types, *left, expected) || neg_contains_var(types, *right, expected)
        }
        _ => false,
    }
}

fn pos_contains_path(types: &TypeArena, id: PosId, expected: &str) -> bool {
    match types.pos(id) {
        Pos::Con(path, _) => compact_path_is(path, expected),
        Pos::Row(items) => items
            .iter()
            .any(|item| pos_contains_path(types, *item, expected)),
        Pos::Union(left, right) => {
            pos_contains_path(types, *left, expected) || pos_contains_path(types, *right, expected)
        }
        _ => false,
    }
}

fn list_with_payload_bound(center: TypeVar, payload: CompactBounds) -> CompactType {
    merge_compact_types(
        true,
        CompactType::from_var(CompactVar::plain(center)),
        CompactType::from_con(CompactCon {
            path: vec!["list".into()],
            args: vec![payload],
        }),
    )
}

pub(super) fn role_arg(machine: &mut ConstraintMachine, var: TypeVar) -> RoleConstraintArg {
    RoleConstraintArg {
        lower: machine.alloc_pos(Pos::Var(var)),
        upper: machine.alloc_neg(Neg::Var(var)),
    }
}
