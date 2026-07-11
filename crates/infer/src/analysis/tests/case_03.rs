use super::*;

#[test]
fn generalize_fallback_floor_normalization_drops_applied_parent_role() {
    let document_role = vec!["Document".to_string()];
    let children_role = vec!["Children".to_string()];
    let node_path = vec!["node".to_string()];
    let owner = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let root = session.infer.fresh_type_var();
    let first = session.infer.fresh_type_var();
    let second = session.infer.fresh_type_var();
    let candidate_item = session.infer.fresh_type_var();

    session.roles.insert(
        owner,
        RoleConstraint {
            role: document_role.clone(),
            inputs: vec![
                role_unary_con_var_and_extra_arg(
                    &mut session.infer,
                    node_path.clone(),
                    first,
                    second,
                ),
                role_unary_con_var_arg(&mut session.infer, node_path.clone(), second),
            ],
            associated: Vec::new(),
        },
    );
    session.roles.insert(
        owner,
        RoleConstraint {
            role: children_role.clone(),
            inputs: vec![role_var_arg(&mut session.infer, first)],
            associated: Vec::new(),
        },
    );
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role: document_role.clone(),
        inputs: vec![
            role_unary_con_var_arg(&mut session.infer, node_path.clone(), candidate_item),
            role_unary_con_var_arg(&mut session.infer, node_path, candidate_item),
        ],
        associated: Vec::new(),
        prerequisites: vec![RoleConstraint {
            role: children_role.clone(),
            inputs: vec![role_var_arg(&mut session.infer, candidate_item)],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    });
    constrain_root_to_vars(&mut session, root, &[first]);

    let applied = floor_normalized_role_resolution(&session, owner, root, &document_role);
    assert!(
        applied
            .residual_prerequisites
            .iter()
            .any(|role| role.role == children_role)
    );
    let applied_flags = fallback_applied_flags(&session, owner, root, &applied);
    assert_eq!(
        applied_flags,
        vec![
            (document_role.clone(), true),
            (children_role.clone(), false),
        ]
    );
    session.applied_method_role_resolutions.insert(applied.key);

    let generalized = session.generalize_root_with_prepasses(owner, root);
    let residual_roles = generalized
        .role_predicates
        .iter()
        .map(|predicate| predicate.role.clone())
        .collect::<Vec<_>>();

    assert_eq!(residual_roles, vec![children_role]);
}

#[test]
fn generalize_fallback_floor_normalization_keeps_unresolved_role() {
    let document_role = vec!["Document".to_string()];
    let node_path = vec!["node".to_string()];
    let owner = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let root = session.infer.fresh_type_var();
    let applied_first = session.infer.fresh_type_var();
    let applied_second = session.infer.fresh_type_var();
    let unresolved_first = session.infer.fresh_type_var();
    let unresolved_second = session.infer.fresh_type_var();
    let unmatched = session.infer.fresh_type_var();
    let candidate_item = session.infer.fresh_type_var();

    session.roles.insert(
        owner,
        RoleConstraint {
            role: document_role.clone(),
            inputs: vec![
                role_unary_con_var_and_extra_arg(
                    &mut session.infer,
                    node_path.clone(),
                    applied_first,
                    applied_second,
                ),
                role_unary_con_var_arg(&mut session.infer, node_path.clone(), applied_second),
            ],
            associated: Vec::new(),
        },
    );
    session.roles.insert(
        owner,
        RoleConstraint {
            role: document_role.clone(),
            inputs: vec![
                role_unary_con_var_and_extra_arg(
                    &mut session.infer,
                    node_path.clone(),
                    unresolved_first,
                    unresolved_second,
                ),
                role_unary_con_var_arg(&mut session.infer, node_path.clone(), unmatched),
            ],
            associated: Vec::new(),
        },
    );
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role: document_role.clone(),
        inputs: vec![
            role_unary_con_var_arg(&mut session.infer, node_path.clone(), candidate_item),
            role_unary_con_var_arg(&mut session.infer, node_path, candidate_item),
        ],
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });
    constrain_root_to_vars(&mut session, root, &[applied_first, unresolved_first]);

    let applied = floor_normalized_role_resolution(&session, owner, root, &document_role);
    let applied_flags = fallback_applied_flags(&session, owner, root, &applied);
    assert_eq!(
        applied_flags
            .iter()
            .filter(|(role, _)| role == &document_role)
            .map(|(_, applied)| *applied)
            .collect::<Vec<_>>(),
        vec![true, false]
    );
    session.applied_method_role_resolutions.insert(applied.key);

    let generalized = session.generalize_root_with_prepasses(owner, root);
    let residual_documents = generalized
        .role_predicates
        .iter()
        .filter(|predicate| predicate.role == document_role)
        .collect::<Vec<_>>();

    assert_eq!(residual_documents.len(), 1, "{residual_documents:?}");
}

#[test]
fn role_prepass_selects_parent_even_when_prerequisite_is_missing() {
    let wrap_role = vec!["Wrap".to_string()];
    let ready_role = vec!["Ready".to_string()];
    let box_path = vec!["box".to_string()];
    let int_path = vec!["int".to_string()];
    let owner = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let root = session.infer.fresh_type_var();
    let output = session.infer.fresh_type_var();
    let item = session.infer.fresh_type_var();

    session.roles.insert(
        owner,
        RoleConstraint {
            role: wrap_role.clone(),
            inputs: vec![role_unary_con_exact_arg(
                &mut session.infer,
                box_path.clone(),
                int_path.clone(),
            )],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_var_arg(&mut session.infer, output),
            }],
        },
    );
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role: wrap_role,
        inputs: vec![role_unary_con_var_arg(&mut session.infer, box_path, item)],
        associated: vec![RoleAssociatedConstraint {
            name: "out".into(),
            value: role_var_arg(&mut session.infer, item),
        }],
        prerequisites: vec![RoleConstraint {
            role: ready_role.clone(),
            inputs: vec![role_var_arg(&mut session.infer, item)],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    });

    let root_lower = session.infer.alloc_pos(Pos::Var(output));
    let root_upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(root_lower, root_upper);

    let generalized = session.generalize_root_with_prepasses(owner, root);

    assert_var_has_exact_bound(&session, output, &int_path);
    assert!(
        generalized
            .role_predicates
            .iter()
            .any(|predicate| predicate.role == ready_role)
    );
    assert_concrete_role_residual_exists(&session, owner, &ready_role, &int_path);
}

#[test]
fn role_prepass_selects_parent_and_keeps_free_prerequisite_residual() {
    let wrap_role = vec!["Wrap".to_string()];
    let ready_role = vec!["Ready".to_string()];
    let box_path = vec!["box".to_string()];
    let owner = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let root = session.infer.fresh_type_var();
    let payload = session.infer.fresh_type_var();
    let output = session.infer.fresh_type_var();
    let item = session.infer.fresh_type_var();

    session.roles.insert(
        owner,
        RoleConstraint {
            role: wrap_role.clone(),
            inputs: vec![role_unary_con_var_arg(
                &mut session.infer,
                box_path.clone(),
                payload,
            )],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_var_arg(&mut session.infer, output),
            }],
        },
    );
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role: wrap_role,
        inputs: vec![role_unary_con_var_arg(&mut session.infer, box_path, item)],
        associated: vec![RoleAssociatedConstraint {
            name: "out".into(),
            value: role_var_arg(&mut session.infer, item),
        }],
        prerequisites: vec![RoleConstraint {
            role: ready_role.clone(),
            inputs: vec![role_var_arg(&mut session.infer, item)],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    });

    let root_lower = session.infer.alloc_pos(Pos::Var(output));
    let root_upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(root_lower, root_upper);

    let generalized = session.generalize_root_with_prepasses(owner, root);

    let residuals = session
        .roles
        .for_owner(owner)
        .iter()
        .filter(|constraint| constraint.role == ready_role)
        .collect::<Vec<_>>();
    assert_eq!(residuals.len(), 1);
    assert!(matches!(
        session
            .infer
            .constraints()
            .types()
            .pos(residuals[0].inputs[0].lower),
        Pos::Var(var) if *var == payload
    ));
    assert!(matches!(
        session
            .infer
            .constraints()
            .types()
            .neg(residuals[0].inputs[0].upper),
        Neg::Var(var) if *var == payload
    ));
    assert!(
        generalized
            .role_predicates
            .iter()
            .any(|predicate| predicate.role == ready_role)
    );
}

#[test]
fn role_impl_member_simplification_runs_before_generalization() {
    let member = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let previous = session.infer.enter_child_level();
    let root = session.infer.fresh_type_var();
    let removed = session.infer.fresh_type_var();
    session.infer.restore_level(previous);
    let lower = session.infer.alloc_pos(Pos::Var(removed));
    let upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(lower, upper);
    session.register_role_impl_member_simplification(
        member,
        CompactSimplification {
            substitutions: vec![crate::compact::CompactVarSubstitution {
                source: removed,
                target: None,
            }],
            sandwiches: Vec::new(),
        },
    );

    let generalized = session.generalize_root_with_prepasses(member, root);

    assert!(generalized.quantifiers.is_empty());
    assert!(generalized.compact.root.is_empty());
}

#[test]
fn computed_fetch_def_does_not_quantify_binding_level_root() {
    let def = DefId(0);
    let mut value_session = AnalysisSession::new(PolyArena::new());
    let previous = value_session.infer.enter_child_level();
    let value_root = value_session.infer.fresh_type_var();
    let value_inner = value_session.infer.fresh_type_var();
    add_identity_function_lower_bound(&mut value_session, value_root, value_inner);
    value_session.infer.restore_level(previous);

    let value_generalized = value_session.generalize_root_with_prepasses(def, value_root);

    assert_eq!(value_generalized.quantifiers, vec![value_inner]);

    let mut computed_session = AnalysisSession::new(PolyArena::new());
    let previous = computed_session.infer.enter_child_level();
    let computed_root = computed_session.infer.fresh_type_var();
    let computed_inner = computed_session.infer.fresh_type_var();
    add_identity_function_lower_bound(&mut computed_session, computed_root, computed_inner);
    computed_session.infer.restore_level(previous);
    computed_session.record_binding_fetch(def, BindingFetch::FetchComputation);

    let computed_generalized = computed_session.generalize_root_with_prepasses(def, computed_root);

    assert!(computed_generalized.quantifiers.is_empty());
    computed_session
        .schemes
        .insert(def, computed_generalized.clone());
    let boundary = computed_session
        .capture_cache_boundary_interface([def])
        .expect("computed binding boundary capture");
    assert!(!boundary.bounds.is_empty());
    assert!(
        boundary
            .bounds
            .iter()
            .all(|bound| !computed_generalized.quantifiers.contains(&bound.var)),
        "value-restricted variables must be classified as unit boundary binders, not Q"
    );
    assert!(
        boundary
            .bounds
            .iter()
            .any(|bound| bound.var == computed_inner),
        "the value-restricted function payload must cross as B"
    );
}

#[test]
fn cache_boundary_capture_preserves_open_lower_and_upper_shape() {
    let def = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let boundary_var = session.infer.fresh_type_var();
    let payload = session.infer.fresh_type_var();
    add_identity_function_lower_bound(&mut session, boundary_var, payload);
    session.schemes.insert(
        def,
        GeneralizedCompactRoot {
            compact: CompactRoot {
                root: CompactType::from_var(crate::compact::CompactVar::plain(boundary_var)),
                rec_vars: Vec::new(),
            },
            role_predicates: Vec::new(),
            quantifiers: Vec::new(),
            stack_quantifiers: Vec::new(),
            substitutions: Vec::new(),
            sandwiches: Vec::new(),
        },
    );

    let boundary = session
        .capture_cache_boundary_interface([def])
        .expect("open boundary capture");
    let root_bound = boundary
        .bounds
        .iter()
        .find(|bound| bound.var == boundary_var)
        .expect("root boundary bound");
    let CompactBounds::Interval { lower, upper } = &root_bound.bounds else {
        panic!("boundary root must stay a centerless interval");
    };
    assert!(lower.vars.iter().any(|var| var.var == boundary_var));
    assert!(!lower.funs.is_empty());
    assert!(upper.vars.iter().any(|var| var.var == boundary_var));
}

#[test]
fn cache_boundary_capture_rejects_unapplied_scheme_dominance_key() {
    let def = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let lower_var = session.infer.fresh_type_var();
    let upper_var = session.infer.fresh_type_var();
    let lower = CompactType::from_var(crate::compact::CompactVar::plain(lower_var));
    let upper = CompactType::from_var(crate::compact::CompactVar::plain(upper_var));
    session.schemes.insert(
        def,
        GeneralizedCompactRoot {
            compact: CompactRoot {
                root: CompactType::from_con(crate::compact::CompactCon {
                    path: vec!["invariant".into()],
                    args: vec![CompactBounds::Interval { lower, upper }],
                }),
                rec_vars: Vec::new(),
            },
            role_predicates: Vec::new(),
            quantifiers: vec![lower_var, upper_var],
            stack_quantifiers: Vec::new(),
            substitutions: Vec::new(),
            sandwiches: Vec::new(),
        },
    );

    let error = session
        .capture_cache_boundary_interface([def])
        .expect_err("freeze must reject a dominance key absent from normal generalization");

    assert_eq!(
        error,
        crate::analysis::cache_interface::BoundaryCaptureError::FreezeProducedConstraint {
            def: Some(def),
            boundary: None,
            merge_constraints: 0,
            subtype_constraints: 1,
        }
    );
}

fn add_identity_function_lower_bound(session: &mut AnalysisSession, root: TypeVar, inner: TypeVar) {
    let arg = session.infer.alloc_neg(Neg::Var(inner));
    let arg_eff = session.infer.alloc_neg(Neg::Bot);
    let ret_eff = session.infer.alloc_pos(Pos::Bot);
    let ret = session.infer.alloc_pos(Pos::Var(inner));
    let lower = session.infer.alloc_pos(Pos::Fun {
        arg,
        arg_eff,
        ret_eff,
        ret,
    });
    let upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(lower, upper);
}

pub(super) fn monomorphic_cast_scheme(
    types: &mut poly::types::TypeArena,
    source: Vec<String>,
    target: Vec<String>,
) -> Scheme {
    let arg = types.alloc_neg(Neg::Con(source, Vec::new()));
    let arg_eff = types.alloc_neg(Neg::Bot);
    let ret_eff = types.alloc_pos(Pos::Bot);
    let ret = types.alloc_pos(Pos::Con(target, Vec::new()));
    let predicate = types.alloc_pos(Pos::Fun {
        arg,
        arg_eff,
        ret_eff,
        ret,
    });
    Scheme {
        quantifiers: Vec::new(),
        role_predicates: Vec::new(),
        recursive_bounds: Vec::new(),
        stack_quantifiers: Vec::new(),
        predicate,
    }
}

pub(super) fn generic_unary_cast_scheme(
    types: &mut poly::types::TypeArena,
    source: Vec<String>,
    target: Vec<String>,
) -> Scheme {
    let quantified = TypeVar(42);
    let arg_item = poly_bounds_neu(types, quantified);
    let ret_item = poly_bounds_neu(types, quantified);
    let arg = types.alloc_neg(Neg::Con(source, vec![arg_item]));
    let arg_eff = types.alloc_neg(Neg::Bot);
    let ret_eff = types.alloc_pos(Pos::Bot);
    let ret = types.alloc_pos(Pos::Con(target, vec![ret_item]));
    let predicate = types.alloc_pos(Pos::Fun {
        arg,
        arg_eff,
        ret_eff,
        ret,
    });
    Scheme {
        quantifiers: vec![quantified],
        role_predicates: Vec::new(),
        recursive_bounds: Vec::new(),
        stack_quantifiers: Vec::new(),
        predicate,
    }
}

fn poly_bounds_neu(types: &mut poly::types::TypeArena, var: TypeVar) -> NeuId {
    let lower = types.alloc_pos(Pos::Var(var));
    let upper = types.alloc_neg(Neg::Var(var));
    types.alloc_neu(Neu::Bounds(lower, upper))
}

fn constrain_root_to_vars(session: &mut AnalysisSession, root: TypeVar, vars: &[TypeVar]) {
    let items = vars
        .iter()
        .map(|var| session.infer.alloc_pos(Pos::Var(*var)))
        .collect();
    let lower = session.infer.alloc_pos(Pos::Tuple(items));
    let upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(lower, upper);
}

fn floor_normalized_role_resolution(
    session: &AnalysisSession,
    owner: DefId,
    root: TypeVar,
    role: &[String],
) -> RoleResolution {
    let mut compact = compact_type_var(session.infer.constraints(), root);
    let mut roles = coalesce_role_constraints(compact_reachable_role_constraints(
        session.infer.constraints(),
        &compact,
        session.roles.for_owner(owner),
    ));
    simplify_compact_root_with_roles_and_non_generic(
        session.infer.constraints(),
        TypeLevel::root().child(),
        &mut compact,
        &mut roles,
        &FxHashSet::default(),
    );
    assert!(
        resolve_role_constraints(
            session.infer.constraints(),
            &compact,
            &roles,
            &session.role_impls,
            &FxHashSet::default(),
        )
        .into_iter()
        .all(|resolution| resolution.demand.role != role),
        "role should require floor normalization"
    );
    let floor_substitutions = coalesce_floor_interval_equalities(
        session.infer.constraints(),
        TypeLevel::root(),
        &mut compact,
        &mut roles,
    );
    assert!(!floor_substitutions.is_empty());
    eliminate_floor_redundant_variables(
        session.infer.constraints(),
        TypeLevel::root(),
        &mut compact,
        &mut roles,
    );
    resolve_role_constraints(
        session.infer.constraints(),
        &compact,
        &roles,
        &session.role_impls,
        &FxHashSet::default(),
    )
    .into_iter()
    .find(|resolution| resolution.demand.role == role)
    .expect("role should resolve after floor normalization")
}

fn fallback_applied_flags(
    session: &AnalysisSession,
    owner: DefId,
    root: TypeVar,
    applied: &RoleResolution,
) -> Vec<(Vec<String>, bool)> {
    let compact = compact_type_var(session.infer.constraints(), root);
    let roles = coalesce_role_constraints(compact_reachable_role_constraints(
        session.infer.constraints(),
        &compact,
        session.roles.for_owner(owner),
    ));
    let applied_candidates = FxHashSet::from_iter([applied.candidate.clone()]);
    let applied_demands = FxHashSet::from_iter([applied.demand.clone()]);
    let flags = session.simplified_role_predicates_already_applied(
        &compact,
        &roles,
        &applied_candidates,
        &applied_demands,
        TypeLevel::root().child(),
    );
    roles
        .into_iter()
        .zip(flags)
        .map(|(role, applied)| (role.role, applied))
        .collect()
}

pub(super) fn infer_bounds_neu(infer: &mut crate::arena::Arena, var: TypeVar) -> NeuId {
    let lower = infer.alloc_pos(Pos::Var(var));
    let upper = infer.alloc_neg(Neg::Var(var));
    infer.alloc_neu(Neu::Bounds(lower, upper))
}

pub(super) fn role_var_arg(infer: &mut crate::arena::Arena, var: TypeVar) -> RoleConstraintArg {
    RoleConstraintArg {
        lower: infer.alloc_pos(Pos::Var(var)),
        upper: infer.alloc_neg(Neg::Var(var)),
    }
}

pub(super) fn role_exact_arg(
    infer: &mut crate::arena::Arena,
    path: Vec<String>,
) -> RoleConstraintArg {
    RoleConstraintArg {
        lower: infer.alloc_pos(Pos::Con(path.clone(), Vec::new())),
        upper: infer.alloc_neg(Neg::Con(path, Vec::new())),
    }
}

pub(super) fn role_unary_con_var_arg(
    infer: &mut crate::arena::Arena,
    path: Vec<String>,
    item: TypeVar,
) -> RoleConstraintArg {
    let lower = infer.alloc_pos(Pos::Var(item));
    let upper = infer.alloc_neg(Neg::Var(item));
    let item = infer.alloc_neu(Neu::Bounds(lower, upper));
    RoleConstraintArg {
        lower: infer.alloc_pos(Pos::Con(path.clone(), vec![item])),
        upper: infer.alloc_neg(Neg::Con(path, vec![item])),
    }
}

pub(super) fn role_unary_con_var_and_extra_arg(
    infer: &mut crate::arena::Arena,
    path: Vec<String>,
    item: TypeVar,
    extra: TypeVar,
) -> RoleConstraintArg {
    let item_lower = infer.alloc_pos(Pos::Var(item));
    let extra_lower = infer.alloc_pos(Pos::Var(extra));
    let lower = infer.alloc_pos(Pos::Union(item_lower, extra_lower));
    let item_upper = infer.alloc_neg(Neg::Var(item));
    let extra_upper = infer.alloc_neg(Neg::Var(extra));
    let upper = infer.alloc_neg(Neg::Intersection(item_upper, extra_upper));
    let item = infer.alloc_neu(Neu::Bounds(lower, upper));
    RoleConstraintArg {
        lower: infer.alloc_pos(Pos::Con(path.clone(), vec![item])),
        upper: infer.alloc_neg(Neg::Con(path, vec![item])),
    }
}

pub(super) fn role_unary_con_open_arg(
    infer: &mut crate::arena::Arena,
    path: Vec<String>,
    _item: TypeVar,
    lower_item: TypeVar,
    upper_item: TypeVar,
) -> RoleConstraintArg {
    let lower = infer.alloc_pos(Pos::Var(lower_item));
    let upper = infer.alloc_neg(Neg::Var(upper_item));
    let item = infer.alloc_neu(Neu::Bounds(lower, upper));
    RoleConstraintArg {
        lower: infer.alloc_pos(Pos::Con(path.clone(), vec![item])),
        upper: infer.alloc_neg(Neg::Con(path, vec![item])),
    }
}

pub(super) fn role_unary_con_open_or_var_arg(
    infer: &mut crate::arena::Arena,
    path: Vec<String>,
    _item: TypeVar,
    lower_item: TypeVar,
    upper_item: TypeVar,
    extra: TypeVar,
) -> RoleConstraintArg {
    let lower_item = infer.alloc_pos(Pos::Var(lower_item));
    let upper_item = infer.alloc_neg(Neg::Var(upper_item));
    let item = infer.alloc_neu(Neu::Bounds(lower_item, upper_item));
    let con = infer.alloc_pos(Pos::Con(path, vec![item]));
    let extra_pos = infer.alloc_pos(Pos::Var(extra));
    RoleConstraintArg {
        lower: infer.alloc_pos(Pos::Union(con, extra_pos)),
        upper: infer.alloc_neg(Neg::Var(extra)),
    }
}

pub(super) fn role_unary_con_exact_arg(
    infer: &mut crate::arena::Arena,
    path: Vec<String>,
    item_path: Vec<String>,
) -> RoleConstraintArg {
    let item_lower = infer.alloc_pos(Pos::Con(item_path.clone(), Vec::new()));
    let item_upper = infer.alloc_neg(Neg::Con(item_path, Vec::new()));
    let item = infer.alloc_neu(Neu::Bounds(item_lower, item_upper));
    RoleConstraintArg {
        lower: infer.alloc_pos(Pos::Con(path.clone(), vec![item])),
        upper: infer.alloc_neg(Neg::Con(path, vec![item])),
    }
}

pub(super) fn role_left_concrete_var_arg(
    infer: &mut crate::arena::Arena,
    path: Vec<String>,
    var: TypeVar,
) -> RoleConstraintArg {
    let con = infer.alloc_pos(Pos::Con(path, Vec::new()));
    let var_pos = infer.alloc_pos(Pos::Var(var));
    RoleConstraintArg {
        lower: infer.alloc_pos(Pos::Union(con, var_pos)),
        upper: infer.alloc_neg(Neg::Var(var)),
    }
}

pub(super) fn assert_var_has_exact_bound(session: &AnalysisSession, var: TypeVar, path: &[String]) {
    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(var)
        .expect("role output should receive impl bounds");
    assert!(bounds.lowers().iter().any(|bound| {
        matches!(
            session.infer.constraints().types().pos(bound.pos),
            Pos::Con(bound_path, _) if bound_path == path
        )
    }));
    assert!(bounds.uppers().iter().any(|bound| {
        matches!(
            session.infer.constraints().types().neg(bound.neg),
            Neg::Con(bound_path, _) if bound_path == path
        )
    }));
}

pub(super) fn assert_var_lacks_exact_bound(
    session: &AnalysisSession,
    var: TypeVar,
    path: &[String],
) {
    let Some(bounds) = session.infer.constraints().bounds().of(var) else {
        return;
    };
    assert!(!bounds.lowers().iter().any(|bound| {
        matches!(
            session.infer.constraints().types().pos(bound.pos),
            Pos::Con(bound_path, _) if bound_path == path
        )
    }));
    assert!(!bounds.uppers().iter().any(|bound| {
        matches!(
            session.infer.constraints().types().neg(bound.neg),
            Neg::Con(bound_path, _) if bound_path == path
        )
    }));
}

pub(super) fn assert_concrete_role_residual_exists(
    session: &AnalysisSession,
    owner: DefId,
    role: &[String],
    path: &[String],
) {
    assert!(
        session.roles.for_owner(owner).iter().any(|constraint| {
            constraint.role == role
                && constraint.inputs.iter().any(|input| {
                    matches!(
                        session.infer.constraints().types().pos(input.lower),
                        Pos::Con(bound_path, _) if bound_path == path
                    ) && matches!(
                        session.infer.constraints().types().neg(input.upper),
                        Neg::Con(bound_path, _) if bound_path == path
                    )
                })
        }),
        "expected concrete residual role demand"
    );
}

pub(super) fn assert_concrete_role_residual_missing(
    session: &AnalysisSession,
    owner: DefId,
    role: &[String],
    path: &[String],
) {
    assert!(
        !session.roles.for_owner(owner).iter().any(|constraint| {
            constraint.role == role
                && constraint.inputs.iter().any(|input| {
                    matches!(
                        session.infer.constraints().types().pos(input.lower),
                        Pos::Con(bound_path, _) if bound_path == path
                    ) && matches!(
                        session.infer.constraints().types().neg(input.upper),
                        Neg::Con(bound_path, _) if bound_path == path
                    )
                })
        }),
        "expected concrete residual role demand to be solved"
    );
}
