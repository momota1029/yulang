use super::*;

#[test]
fn lower_bound_events_route_receiver_and_ref_payload_select_watchers() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let receiver_select = SelectId(0);
    let payload_select = SelectId(1);
    let watched = TypeVar(2);
    session.selections.watch_receiver(watched, receiver_select);
    session
        .selections
        .watch_ref_payload(watched, payload_select);

    let lower = session
        .infer
        .alloc_pos(Pos::Con(crate::std_paths::control_var_ref_type(), vec![]));
    let upper = session.infer.alloc_neg(Neg::Var(watched));
    session.infer.weighted_subtype(
        lower,
        ConstraintWeights {
            left: LeftConstraintWeight::from_ids([SubtractId(0)]),
            right: RightConstraintWeight::empty(),
        },
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    session.route_constraint_events();

    assert_eq!(
        session.work().iter().cloned().collect::<Vec<_>>(),
        vec![
            AnalysisWork::ProbeSelect(receiver_select),
            AnalysisWork::ProbeSelect(payload_select)
        ]
    );
}

#[test]
fn upper_bound_events_route_receiver_select_watchers_once() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let select = session.poly.add_select("display");
    let watched = TypeVar(2);
    session.selections.insert(
        select,
        SelectionUse {
            parent: DefId(1),
            method_value: TypeVar(3),
            selected_value: TypeVar(4),
            receiver_value: watched,
            receiver_effect: TypeVar(5),
            local_method_scope: None,
            recursive_self_value: None,
        },
    );
    session.selections.watch_receiver(watched, select);

    let lower = session.infer.alloc_pos(Pos::Var(watched));
    let upper = session
        .infer
        .alloc_neg(Neg::Con(vec!["int".into()], Vec::new()));
    session.infer.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    session.route_constraint_events();

    assert_eq!(
        session.work().iter().cloned().collect::<Vec<_>>(),
        vec![AnalysisWork::ProbeSelect(select)]
    );

    session.drain_work();
    let lower = session.infer.alloc_pos(Pos::Var(watched));
    let upper = session
        .infer
        .alloc_neg(Neg::Con(vec!["float".into()], Vec::new()));
    session.infer.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    session.route_constraint_events();

    assert!(session.work().is_empty());
}

fn register_test_selection_use(
    session: &mut AnalysisSession,
    select: SelectId,
    parent: DefId,
    method_value: TypeVar,
    receiver: TypeVar,
    receiver_effect: TypeVar,
    result: TypeVar,
    result_effect: TypeVar,
) {
    let use_site = prepare_test_selection_use(
        session,
        parent,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session.register_selection_use(select, use_site);
}

fn prepare_test_selection_use(
    session: &mut AnalysisSession,
    parent: DefId,
    method_value: TypeVar,
    receiver: TypeVar,
    receiver_effect: TypeVar,
    result: TypeVar,
    result_effect: TypeVar,
) -> SelectionUse {
    let method = session.infer.alloc_pos(Pos::Var(method_value));
    let arg = session.infer.alloc_pos(Pos::Var(receiver));
    let arg_eff = session.infer.alloc_pos(Pos::Bot);
    let ret_eff = session.infer.alloc_neg(Neg::Var(result_effect));
    let ret = session.infer.alloc_neg(Neg::Var(result));
    let upper = session.infer.alloc_neg(Neg::Fun {
        arg,
        arg_eff,
        ret_eff,
        ret,
    });
    session.infer.subtype(
        method,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    let receiver_effect_pos = session.infer.alloc_pos(Pos::Var(receiver_effect));
    let result_effect_neg = session.infer.alloc_neg(Neg::Var(result_effect));
    session.infer.subtype(
        receiver_effect_pos,
        result_effect_neg,
        crate::constraints::OriginId::unknown_internal(),
    );
    SelectionUse {
        parent,
        method_value,
        selected_value: result,
        receiver_value: receiver,
        receiver_effect,
        local_method_scope: None,
        recursive_self_value: None,
    }
}

#[test]
fn nominal_con_mismatch_applies_registered_cast_scheme() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let source = vec!["int".to_string()];
    let target = vec!["user_id".to_string()];
    let result = TypeVar(0);
    let cast_arg = session
        .poly
        .typ
        .alloc_neg(Neg::Con(source.clone(), Vec::new()));
    let cast_arg_eff = session.poly.typ.alloc_neg(Neg::Bot);
    let cast_ret_eff = session.poly.typ.alloc_pos(Pos::Bot);
    let cast_ret = session.poly.typ.alloc_pos(Pos::Var(result));
    let cast_predicate = session.poly.typ.alloc_pos(Pos::Fun {
        arg: cast_arg,
        arg_eff: cast_arg_eff,
        ret_eff: cast_ret_eff,
        ret: cast_ret,
    });
    session.casts.insert(
        source.clone(),
        target.clone(),
        Scheme {
            quantifiers: vec![result],
            role_predicates: Vec::new(),
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate: cast_predicate,
        },
    );

    let lower = session
        .infer
        .alloc_pos(Pos::Con(source.clone(), Vec::new()));
    let upper = session
        .infer
        .alloc_neg(Neg::Con(target.clone(), Vec::new()));
    session.infer.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    session.route_constraint_events();

    let events = session.infer.constraints().events();
    assert!(events.iter().any(|event| {
            matches!(
                event,
                ConstraintEvent::UpperBoundAdded { bound, .. }
                    if matches!(session.infer.constraints().types().neg(*bound), Neg::Con(path, _) if path == &target)
            )
        }));
}

#[test]
fn ref_resolution_routes_parent_and_use_value_to_scc_machine() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let reference = session.poly.add_ref();
    let parent = DefId(1);
    let target = DefId(2);
    session.refs.insert(
        reference,
        RefUse {
            parent,
            value: TypeVar(3),
            source_span: None,
        },
    );

    session.enqueue(AnalysisWork::ApplyRefResolution {
        ref_id: reference,
        target,
    });
    session.drain_work();

    assert_eq!(session.poly.ref_target(reference), Some(target));
    assert_eq!(
        session.take_scc_events(),
        vec![SccEvent::ComponentEdgeAdded {
            from: vec![parent],
            to: vec![target]
        }]
    );
}

#[test]
fn method_selection_resolution_routes_hidden_method_use_to_scc_machine() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let receiver = session.poly.add_expr(Expr::Lit(Lit::Unit));
    let select = session.poly.add_select("display");
    session.poly.add_expr(Expr::Select(receiver, select));
    let parent = DefId(1);
    let method = DefId(2);
    let method_value = TypeVar(4);
    register_test_selection_use(
        &mut session,
        select,
        parent,
        method_value,
        TypeVar(3),
        TypeVar(5),
        TypeVar(6),
        TypeVar(7),
    );

    session.enqueue(AnalysisWork::ApplySelectionResolution {
        select_id: select,
        target: SelectionTarget::Method { def: method },
    });
    session.drain_work();

    assert_eq!(
        session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method })
    );
    assert_eq!(
        session.take_scc_events(),
        vec![SccEvent::ComponentEdgeAdded {
            from: vec![parent],
            to: vec![method]
        }]
    );
}

#[test]
fn method_selection_resolves_when_receiver_lower_bound_has_method() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let select = session.poly.add_select("display");
    let parent = DefId(1);
    let method = DefId(2);
    let receiver = TypeVar(3);
    let method_value = TypeVar(4);
    let receiver_effect = TypeVar(5);
    let result = TypeVar(6);
    let result_effect = TypeVar(7);
    register_test_selection_use(
        &mut session,
        select,
        parent,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session
        .methods
        .insert_value(vec!["int".to_string()], "display", method);

    let lower = session
        .infer
        .alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let upper = session.infer.alloc_neg(Neg::Var(receiver));
    session.infer.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    session.drain_work();

    assert_eq!(
        session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method })
    );
    assert!(session.take_scc_events().iter().any(|event| {
        matches!(
            event,
            SccEvent::ComponentEdgeAdded {
                from,
                to,
            } if from == &vec![parent] && to == &vec![method]
        )
    }));
}

#[test]
fn method_registration_probes_existing_receiver_lower_bounds() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let select = session.poly.add_select("display");
    let parent = DefId(1);
    let method = DefId(2);
    let receiver = TypeVar(3);
    let method_value = TypeVar(4);
    let receiver_effect = TypeVar(5);
    let result = TypeVar(6);
    let result_effect = TypeVar(7);
    register_test_selection_use(
        &mut session,
        select,
        parent,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    let lower = session
        .infer
        .alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let upper = session.infer.alloc_neg(Neg::Var(receiver));
    session.infer.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    session.drain_work();

    assert_eq!(session.poly.select(select).resolution, None);

    session.register_value_type_method(vec!["int".to_string()], "display", method);
    session.drain_work();

    assert_eq!(
        session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method })
    );
}

#[test]
fn method_selection_uses_single_receiver_upper_when_lower_is_empty() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let select = session.poly.add_select("display");
    let parent = DefId(1);
    let method = DefId(2);
    let receiver = TypeVar(3);
    let method_value = TypeVar(4);
    let receiver_effect = TypeVar(5);
    let result = TypeVar(6);
    let result_effect = TypeVar(7);
    register_test_selection_use(
        &mut session,
        select,
        parent,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session.register_value_type_method(vec!["int".to_string()], "display", method);
    let lower = session.infer.alloc_pos(Pos::Var(receiver));
    let upper = session
        .infer
        .alloc_neg(Neg::Con(vec!["int".into()], Vec::new()));
    session.infer.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    session.drain_work();

    assert_eq!(
        session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method })
    );
}

#[test]
fn method_selection_probes_ref_payload_lower_bounds() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let select = session.poly.add_select("display");
    let parent = DefId(1);
    let method = DefId(2);
    let receiver = TypeVar(3);
    let method_value = TypeVar(4);
    let payload = TypeVar(5);
    let effect = TypeVar(6);
    let receiver_effect = TypeVar(7);
    let result = TypeVar(8);
    let result_effect = TypeVar(9);
    register_test_selection_use(
        &mut session,
        select,
        parent,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session
        .methods
        .insert_ref(vec!["int".to_string()], "display", method);

    let int = session
        .infer
        .alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let payload_upper = session.infer.alloc_neg(Neg::Var(payload));
    session.infer.subtype(
        int,
        payload_upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    let effect_arg = infer_bounds_neu(&mut session.infer, effect);
    let payload_arg = infer_bounds_neu(&mut session.infer, payload);
    let ref_lower = session.infer.alloc_pos(Pos::Con(
        crate::std_paths::control_var_ref_type(),
        vec![effect_arg, payload_arg],
    ));
    let receiver_upper = session.infer.alloc_neg(Neg::Var(receiver));
    session.infer.subtype(
        ref_lower,
        receiver_upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    session.drain_work();

    assert_eq!(
        session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method })
    );
}

#[test]
fn effect_method_selection_resolves_from_receiver_effect_row_lower_bound() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let select = session.poly.add_select("flip");
    let parent = DefId(1);
    let method = DefId(2);
    let receiver = TypeVar(3);
    let receiver_effect = TypeVar(4);
    let result = TypeVar(5);
    let result_effect = TypeVar(6);
    let method_value = TypeVar(7);
    register_test_selection_use(
        &mut session,
        select,
        parent,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session.register_effect_method(vec!["nondet".to_string()], "flip", method);
    let nondet = session
        .infer
        .alloc_pos(Pos::Con(vec!["nondet".into()], Vec::new()));
    let row = session.infer.alloc_pos(Pos::Row(vec![nondet]));
    let upper = session.infer.alloc_neg(Neg::Var(receiver_effect));
    session
        .infer
        .subtype(row, upper, crate::constraints::OriginId::unknown_internal());
    session.drain_work();

    assert_eq!(
        session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method })
    );
}

#[test]
fn effect_method_selection_resolves_from_receiver_effect_subtract_fact() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let select = session.poly.add_select("flip");
    let parent = DefId(1);
    let method = DefId(2);
    let receiver = TypeVar(3);
    let receiver_effect = TypeVar(4);
    let result = TypeVar(5);
    let result_effect = TypeVar(6);
    let method_value = TypeVar(7);
    register_test_selection_use(
        &mut session,
        select,
        parent,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session.register_effect_method(vec!["nondet".to_string()], "flip", method);
    session.infer.subtract_fact(
        receiver_effect,
        SubtractId(0),
        Subtractability::Set(vec!["nondet".into()], Vec::new()),
    );
    session.drain_work();

    assert_eq!(
        session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method })
    );
}

#[test]
fn effect_method_selection_resolves_from_receiver_effect_weighted_lower_bound() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let select = session.poly.add_select("flip");
    let parent = DefId(1);
    let method = DefId(2);
    let receiver = TypeVar(3);
    let receiver_effect = TypeVar(4);
    let tail_effect = TypeVar(5);
    let result = TypeVar(6);
    let result_effect = TypeVar(7);
    let method_value = TypeVar(8);
    register_test_selection_use(
        &mut session,
        select,
        parent,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session.register_effect_method(vec!["nondet".to_string()], "flip", method);
    let tail = session.infer.alloc_pos(Pos::Var(tail_effect));
    let upper = session.infer.alloc_neg(Neg::Var(receiver_effect));
    session.infer.weighted_subtype(
        tail,
        ConstraintWeights {
            left: LeftConstraintWeight::push(
                SubtractId(0),
                Subtractability::Set(vec!["nondet".into()], Vec::new()),
            ),
            right: RightConstraintWeight::empty(),
        },
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    session.drain_work();

    assert_eq!(
        session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method })
    );
}

#[test]
fn effect_method_selection_ignores_non_effect_receiver_value_weighted_lower_bound() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let select = session.poly.add_select("flip");
    let parent = DefId(1);
    let method = DefId(2);
    let receiver = TypeVar(3);
    let receiver_effect = TypeVar(4);
    let result = TypeVar(5);
    let result_effect = TypeVar(6);
    let method_value = TypeVar(7);
    register_test_selection_use(
        &mut session,
        select,
        parent,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session.register_effect_method(vec!["nondet".to_string()], "flip", method);
    let value = session
        .infer
        .alloc_pos(Pos::Con(vec!["bool".into()], Vec::new()));
    let upper = session.infer.alloc_neg(Neg::Var(receiver));
    session.infer.weighted_subtype(
        value,
        ConstraintWeights {
            left: LeftConstraintWeight::push(
                SubtractId(0),
                Subtractability::Set(vec!["nondet".into()], Vec::new()),
            ),
            right: RightConstraintWeight::empty(),
        },
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    session.drain_work();

    assert_eq!(session.poly.select(select).resolution, None);
}

#[test]
fn effect_method_selection_reprobes_when_transitive_effect_fact_is_added() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let select = session.poly.add_select("flip");
    let parent = DefId(1);
    let method = DefId(2);
    let receiver = TypeVar(3);
    let receiver_effect = TypeVar(4);
    let tail_effect = TypeVar(5);
    let result = TypeVar(6);
    let result_effect = TypeVar(7);
    let method_value = TypeVar(8);
    register_test_selection_use(
        &mut session,
        select,
        parent,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session.register_effect_method(vec!["nondet".to_string()], "flip", method);
    let tail = session.infer.alloc_pos(Pos::Var(tail_effect));
    let upper = session.infer.alloc_neg(Neg::Var(receiver_effect));
    session.infer.subtype(
        tail,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    session.drain_work();

    assert_eq!(session.poly.select(select).resolution, None);

    session.infer.subtract_fact(
        tail_effect,
        SubtractId(0),
        Subtractability::Set(vec!["nondet".into()], Vec::new()),
    );
    session.drain_work();

    assert_eq!(
        session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method })
    );
}

#[test]
fn unresolved_method_selection_forces_tainted_role_resolution() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let owner = DefId(1);
    let method = DefId(2);
    let root = TypeVar(0);
    let receiver = TypeVar(3);
    let method_value = TypeVar(4);
    let receiver_effect = TypeVar(5);
    let result = TypeVar(6);
    let result_effect = TypeVar(7);
    let select = session.poly.add_select("display");
    let role = vec!["HasDisplay".to_string()];
    let unit = vec!["unit".to_string()];
    let int = vec!["int".to_string()];

    session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
        def: owner,
        root,
    }));
    session.roles.insert(
        owner,
        RoleConstraint {
            role: role.clone(),
            inputs: vec![role_exact_arg(&mut session.infer, unit.clone())],
            associated: vec![RoleAssociatedConstraint {
                name: "out".to_string(),
                value: role_var_arg(&mut session.infer, receiver),
            }],
        },
    );
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role,
        inputs: vec![role_exact_arg(&mut session.infer, unit)],
        associated: vec![RoleAssociatedConstraint {
            name: "out".to_string(),
            value: role_exact_arg(&mut session.infer, int.clone()),
        }],
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });
    register_test_selection_use(
        &mut session,
        select,
        owner,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session.register_value_type_method(int, "display", method);
    session.enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: owner }));

    session.drain_work();

    assert_eq!(
        session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method })
    );
    assert!(session.take_scc_events().iter().any(|event| {
        matches!(
            event,
            SccEvent::ComponentEdgeAdded { from, to }
                if from == &vec![owner] && to == &vec![method]
        )
    }));
}

struct MethodRolePassGuardFixture {
    session: AnalysisSession,
    select: SelectId,
    selection_use: SelectionUse,
    candidate: RoleImplCandidate,
    method: DefId,
}

fn method_role_pass_guard_fixture() -> MethodRolePassGuardFixture {
    let mut session = AnalysisSession::new(PolyArena::new());
    let owner = DefId(1);
    let method = DefId(2);
    let root = TypeVar(0);
    let receiver = TypeVar(3);
    let method_value = TypeVar(4);
    let receiver_effect = TypeVar(5);
    let result = TypeVar(6);
    let result_effect = TypeVar(7);
    let select = session.poly.add_select("display");
    let role = vec!["HasDisplay".to_string()];
    let unit = vec!["unit".to_string()];
    let int = vec!["int".to_string()];

    session.roles.insert(
        owner,
        RoleConstraint {
            role: role.clone(),
            inputs: vec![role_exact_arg(&mut session.infer, unit.clone())],
            associated: vec![RoleAssociatedConstraint {
                name: "out".to_string(),
                value: role_var_arg(&mut session.infer, receiver),
            }],
        },
    );
    let candidate = RoleImplCandidate {
        impl_def: None,
        role,
        inputs: vec![role_exact_arg(&mut session.infer, unit)],
        associated: vec![RoleAssociatedConstraint {
            name: "out".to_string(),
            value: role_exact_arg(&mut session.infer, int.clone()),
        }],
        prerequisites: Vec::new(),
        methods: Vec::new(),
    };
    let selection_use = prepare_test_selection_use(
        &mut session,
        owner,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session.register_value_type_method(int, "display", method);
    session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
        def: owner,
        root,
    }));

    MethodRolePassGuardFixture {
        session,
        select,
        selection_use,
        candidate,
        method,
    }
}

#[test]
fn unchanged_method_role_inputs_skip_a_redundant_pass() {
    let mut fixture = method_role_pass_guard_fixture();
    fixture
        .session
        .register_selection_use(fixture.select, fixture.selection_use);
    fixture.session.drain_work();

    let executed_passes = fixture.session.timing().role_passes;
    let expected_resolution = fixture.session.poly.select(fixture.select).resolution;
    let expected_constraint_epoch = fixture.session.infer.constraints().epoch();
    assert_eq!(expected_resolution, None);

    fixture.session.drain_work();

    assert_eq!(fixture.session.timing().role_passes, executed_passes);
    assert!(!fixture.session.force_method_role_pass_for_test());
    assert_eq!(
        fixture.session.poly.select(fixture.select).resolution,
        expected_resolution
    );
    assert_eq!(
        fixture.session.infer.constraints().epoch(),
        expected_constraint_epoch
    );
}

#[test]
fn new_unresolved_selection_invalidates_method_role_pass_guard() {
    let mut fixture = method_role_pass_guard_fixture();
    fixture
        .session
        .register_role_impl_candidate(fixture.candidate);
    fixture.session.drain_work();
    let executed_passes = fixture.session.timing().role_passes;
    let constraint_epoch = fixture.session.infer.constraints().epoch();
    let role_epoch = fixture.session.roles.epoch();

    fixture
        .session
        .register_selection_use(fixture.select, fixture.selection_use);
    assert_eq!(
        fixture.session.infer.constraints().epoch(),
        constraint_epoch
    );
    assert_eq!(fixture.session.roles.epoch(), role_epoch);
    fixture.session.drain_work();

    assert!(fixture.session.timing().role_passes > executed_passes);
    assert_eq!(
        fixture.session.poly.select(fixture.select).resolution,
        Some(SelectResolution::Method {
            def: fixture.method
        })
    );
}

#[test]
fn new_role_impl_candidate_invalidates_method_role_pass_guard() {
    let mut fixture = method_role_pass_guard_fixture();
    fixture
        .session
        .register_selection_use(fixture.select, fixture.selection_use);
    fixture.session.drain_work();
    let executed_passes = fixture.session.timing().role_passes;
    let constraint_epoch = fixture.session.infer.constraints().epoch();
    let role_epoch = fixture.session.roles.epoch();

    fixture
        .session
        .register_role_impl_candidate(fixture.candidate);
    assert_eq!(
        fixture.session.infer.constraints().epoch(),
        constraint_epoch
    );
    assert_eq!(fixture.session.roles.epoch(), role_epoch);
    fixture.session.drain_work();

    assert!(fixture.session.timing().role_passes > executed_passes);
    assert_eq!(
        fixture.session.poly.select(fixture.select).resolution,
        Some(SelectResolution::Method {
            def: fixture.method
        })
    );
}

#[test]
fn unresolved_method_selection_does_not_use_tainted_role_endpoint() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let owner = DefId(1);
    let method = DefId(2);
    let root = TypeVar(0);
    let receiver = TypeVar(3);
    let method_value = TypeVar(4);
    let receiver_effect = TypeVar(5);
    let result = TypeVar(6);
    let result_effect = TypeVar(7);
    let output = TypeVar(8);
    let select = session.poly.add_select("display");
    let role = vec!["Box".to_string()];
    let int = vec!["int".to_string()];
    let unit = vec!["unit".to_string()];

    session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
        def: owner,
        root,
    }));
    session.roles.insert(
        owner,
        RoleConstraint {
            role: role.clone(),
            inputs: vec![role_left_concrete_var_arg(
                &mut session.infer,
                int.clone(),
                receiver,
            )],
            associated: vec![RoleAssociatedConstraint {
                name: "out".to_string(),
                value: role_var_arg(&mut session.infer, output),
            }],
        },
    );
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role,
        inputs: vec![role_exact_arg(&mut session.infer, int.clone())],
        associated: vec![RoleAssociatedConstraint {
            name: "out".to_string(),
            value: role_exact_arg(&mut session.infer, unit.clone()),
        }],
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });
    register_test_selection_use(
        &mut session,
        select,
        owner,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session.register_value_type_method(int, "display", method);
    session.enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: owner }));

    session.drain_work();

    assert_eq!(session.poly.select(select).resolution, None);
    assert_var_lacks_exact_bound(&session, output, &unit);
}

#[test]
fn unresolved_selection_falls_back_to_record_field_constraint_in_final_phase() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let select = session.poly.add_select("size");
    let parent = DefId(1);
    let receiver = TypeVar(2);
    let result = TypeVar(3);
    let receiver_effect = TypeVar(4);
    let result_effect = TypeVar(5);
    let method_value = TypeVar(6);
    register_test_selection_use(
        &mut session,
        select,
        parent,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
        def: parent,
        root: method_value,
    }));
    session.enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: parent }));

    session.resolve_unresolved_selections_as_record_fields();

    assert_eq!(
        session.poly.select(select).resolution,
        Some(SelectResolution::RecordField)
    );
    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(receiver)
        .expect("record fallback should constrain receiver");
    assert!(bounds.uppers().iter().any(|bound| {
        matches!(
            session.infer.constraints().types().neg(bound.neg),
            Neg::Record(fields)
                if fields.len() == 1
                    && fields[0].name == "size"
                    && matches!(
                        session.infer.constraints().types().neg(fields[0].value),
                        Neg::Var(var) if *var == result
            )
        )
    }));
    let result_effect_bounds = session
        .infer
        .constraints()
        .bounds()
        .of(result_effect)
        .expect("record fallback should flow receiver effect to result");
    assert!(result_effect_bounds.lowers().iter().any(|bound| {
        matches!(
            session.infer.constraints().types().pos(bound.pos),
            Pos::Var(var) if *var == receiver_effect
        )
    }));
}

#[test]
fn final_selection_fallback_drops_stale_resolved_selection_entry() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let select = session.poly.add_select("size");
    let parent = DefId(1);
    let method = DefId(2);
    register_test_selection_use(
        &mut session,
        select,
        parent,
        TypeVar(3),
        TypeVar(4),
        TypeVar(5),
        TypeVar(6),
        TypeVar(7),
    );
    session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
        def: parent,
        root: TypeVar(3),
    }));
    session.enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: parent }));
    session
        .poly
        .resolve_select(select, SelectResolution::Method { def: method });

    session.resolve_unresolved_selections_as_record_fields();

    assert_eq!(
        session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method })
    );
    assert!(session.selections.get(select).is_none());
}

#[test]
fn typeclass_selection_fallback_resolves_member_without_receiver_demand() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let select = session.poly.add_select("le");
    let parent = DefId(1);
    let method = DefId(2);
    let receiver = TypeVar(3);
    let method_value = TypeVar(4);
    let receiver_effect = TypeVar(5);
    let result = TypeVar(6);
    let result_effect = TypeVar(7);
    let role = vec!["Ord".to_string()];
    register_test_selection_use(
        &mut session,
        select,
        parent,
        method_value,
        receiver,
        receiver_effect,
        result,
        result_effect,
    );
    session.role_methods.insert(role.clone(), "le", method);
    session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
        def: parent,
        root: method_value,
    }));
    session.enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: parent }));

    session.resolve_unresolved_selections_as_record_fields();

    assert_eq!(
        session.poly.select(select).resolution,
        Some(SelectResolution::TypeclassMethod { member: method })
    );
    // demand は method scheme の instantiation 側だけが作る。selection 解決時に
    // receiver の値型を subject にした demand を別に張ると、coalesce 併合で
    // receiver が区間中心(=実引数)を乗っ取り、supertype 解決の instance を失う。
    assert!(session.roles.for_owner(parent).is_empty());
}

#[test]
fn open_scc_use_adds_target_to_use_constraint() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let a = DefId(1);
    let b = DefId(2);
    let a_root = TypeVar(10);
    let b_root = TypeVar(20);
    let a_to_b_use = TypeVar(12);
    let b_to_a_use = TypeVar(21);
    let a_to_b_ref = session.poly.add_ref();
    let b_to_a_ref = session.poly.add_ref();
    session.refs.insert(
        a_to_b_ref,
        RefUse {
            parent: a,
            value: a_to_b_use,
            source_span: None,
        },
    );
    session.refs.insert(
        b_to_a_ref,
        RefUse {
            parent: b,
            value: b_to_a_use,
            source_span: None,
        },
    );

    session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
        def: a,
        root: a_root,
    }));
    session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
        def: b,
        root: b_root,
    }));
    session.enqueue(AnalysisWork::ApplyRefResolution {
        ref_id: a_to_b_ref,
        target: b,
    });
    session.enqueue(AnalysisWork::ApplyRefResolution {
        ref_id: b_to_a_ref,
        target: a,
    });
    session.drain_work();

    let b_root_pos = session.infer.alloc_pos(Pos::Var(b_root));
    let a_to_b_neg = session.infer.alloc_neg(Neg::Var(a_to_b_use));
    let bounds = session.infer.constraints().bounds();
    let use_bounds = bounds.of(a_to_b_use).expect("use bounds");
    assert!(
        use_bounds
            .lowers()
            .iter()
            .any(|bound| bound.pos == b_root_pos && bound.weights == ConstraintWeights::empty())
    );
    let target_bounds = bounds.of(b_root).expect("target root bounds");
    assert!(
        target_bounds
            .uppers()
            .iter()
            .any(|bound| bound.neg == a_to_b_neg && bound.weights == ConstraintWeights::empty())
    );

    assert!(session.take_scc_events().iter().any(|event| {
        matches!(
            event,
            SccEvent::OpenUse {
                target,
                target_root,
                use_value,
            } if *target == b && *target_root == b_root && *use_value == a_to_b_use
        )
    }));
}

#[test]
fn quantify_component_writes_scheme_to_poly_def() {
    let mut poly = PolyArena::new();
    let def = poly.defs.fresh();
    poly.defs.set(
        def,
        Def::Let {
            vis: Vis::My,
            scheme: None,
            body: None,
            children: Vec::new(),
        },
    );
    let mut session = AnalysisSession::new(poly);
    let root = session.infer.fresh_type_var();

    session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef { def, root }));
    session.enqueue(AnalysisWork::Scc(SccInput::DefFinished { def }));
    session.drain_work();

    let Some(Def::Let {
        scheme: Some(scheme),
        ..
    }) = session.poly.defs.get(def)
    else {
        panic!("ready SCC should write a scheme to Def::Let");
    };
    assert_eq!(scheme.quantifiers, Vec::new());
    assert!(session.schemes.contains_key(&def));
    assert!(session.take_scc_events().iter().any(|event| {
        matches!(
            event,
            SccEvent::QuantifyComponent {
                component,
                roots,
            } if component == &vec![def] && roots == &vec![root]
        )
    }));
}
