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
    let canonical = computed_session
        .freeze_cache_interface([def])
        .expect("computed binding joint cache freeze");
    assert!(
        canonical.binders.boundary.contains(&computed_inner),
        "joint freeze must retain the value-restricted payload in B"
    );

    let mut target = PolyArena::new();
    let target_def = target.defs.fresh();
    assert_eq!(target_def, def);
    let placeholder = target.typ.alloc_pos(Pos::Tuple(Vec::new()));
    target.defs.set(
        target_def,
        Def::Let {
            vis: poly::expr::Vis::Pub,
            scheme: Some(Scheme {
                quantifiers: Vec::new(),
                role_predicates: Vec::new(),
                recursive_bounds: Vec::new(),
                stack_quantifiers: Vec::new(),
                predicate: placeholder,
            }),
            body: None,
            children: Vec::new(),
        },
    );
    let frozen_boundary = canonical
        .freeze_into_poly(computed_session.infer.constraints(), &mut target)
        .expect("one-shot compact draft freeze");

    assert!(
        matches!(
            target.defs.get(def),
            Some(Def::Let {
                scheme: Some(scheme),
                ..
            }) if scheme.quantifiers.is_empty()
        ),
        "the canonical scheme must be written into the same poly arena as its boundary"
    );
    assert!(
        frozen_boundary
            .bounds
            .iter()
            .any(|bound| bound.var == computed_inner)
    );
    assert!(
        frozen_boundary
            .bounds
            .iter()
            .all(|bound| { matches!(target.typ.neu(bound.bounds), Neu::Bounds(_, _)) })
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

    let canonical = session
        .freeze_cache_interface([def])
        .expect("open boundary joint freeze");
    assert_eq!(canonical.schemes.len(), 1);
    assert!(canonical.binders.boundary.contains(&boundary_var));
    assert!(
        canonical
            .boundary
            .bounds
            .iter()
            .any(|bound| bound.var == boundary_var)
    );
}

#[test]
fn cache_candidate_capture_classifies_head_binders_and_shared_boundary() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let head = session.infer.fresh_type_var();
    let boundary_var = session.infer.fresh_type_var();
    session.role_impls.insert(RoleImplCandidate {
        impl_def: Some(DefId(40)),
        role: vec!["CapturedCandidate".into()],
        inputs: vec![
            role_var_arg(&mut session.infer, head),
            role_var_arg(&mut session.infer, boundary_var),
        ],
        associated: Vec::new(),
        prerequisites: vec![RoleConstraint {
            role: vec!["CapturedPrerequisite".into()],
            inputs: vec![
                role_var_arg(&mut session.infer, head),
                role_var_arg(&mut session.infer, boundary_var),
            ],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    });
    let boundary = crate::analysis::cache_interface::CapturedBoundaryInterface {
        bounds: vec![crate::analysis::cache_interface::CapturedBoundaryBound {
            var: boundary_var,
            bounds: CompactBounds::Interval {
                lower: CompactType::from_var(crate::compact::CompactVar::plain(boundary_var)),
                upper: CompactType::from_var(crate::compact::CompactVar::plain(boundary_var)),
            },
        }],
    };

    let captured = session.capture_cache_candidate_interface(&boundary);

    assert_eq!(captured.candidates.len(), 1);
    assert_eq!(captured.candidates[0].head_binders, vec![head]);
    assert_eq!(captured.candidates[0].boundary, vec![boundary_var]);
    assert!(captured.candidates[0].prerequisite_only.is_empty());
    assert_eq!(
        captured.candidates[0].candidate.role,
        vec!["CapturedCandidate".to_string()]
    );
    assert_eq!(captured.candidates[0].candidate.prerequisites.len(), 1);
}

#[test]
fn cache_candidate_capture_leaves_prerequisite_only_variable_unclassified() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let head = session.infer.fresh_type_var();
    let prerequisite_only = session.infer.fresh_type_var();
    session.role_impls.insert(RoleImplCandidate {
        impl_def: Some(DefId(41)),
        role: vec!["OpenCandidate".into()],
        inputs: vec![role_var_arg(&mut session.infer, head)],
        associated: Vec::new(),
        prerequisites: vec![RoleConstraint {
            role: vec!["OpenPrerequisite".into()],
            inputs: vec![role_var_arg(&mut session.infer, prerequisite_only)],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    });

    let captured = session.capture_cache_candidate_interface(
        &crate::analysis::cache_interface::CapturedBoundaryInterface::default(),
    );

    assert_eq!(captured.candidates.len(), 1);
    assert_eq!(captured.candidates[0].head_binders, vec![head]);
    assert!(captured.candidates[0].boundary.is_empty());
    assert_eq!(
        captured.candidates[0].prerequisite_only,
        vec![prerequisite_only]
    );
}

/// Slice 1 positive witness for partial option 1.
///
/// The real zero-prerequisite `ref 'e (list 'a): Index int` candidate still reaches the late pass
/// with its weighted effect-binder alias. Candidate-scoped settlement now proves the post-floor
/// dominance key through the real machine, so Stage 4 accepts the otherwise unchanged head.
#[test]
fn cache_candidate_partial_option_1_slice_1_settles_ref_list_index_effect_head() {
    fn path_is(path: &[String], expected: &[&str]) -> bool {
        path.iter().map(String::as_str).eq(expected.iter().copied())
    }

    fn interval_contains_con(bounds: &CompactBounds, expected: &[&str]) -> bool {
        let CompactBounds::Interval { lower, upper } = bounds else {
            return false;
        };
        [lower, upper].into_iter().all(|ty| {
            ty.cons
                .keys()
                .any(|path| path_is(path.as_slice(), expected))
        })
    }

    fn sole_shared_primary_interval_var(bounds: &CompactBounds) -> Option<TypeVar> {
        let CompactBounds::Interval { lower, upper } = bounds else {
            return None;
        };
        let lower = lower
            .vars
            .iter()
            .filter(|var| var.origin == crate::compact::CompactVarOrigin::Primary)
            .map(|var| var.var)
            .collect::<Vec<_>>();
        let upper = upper
            .vars
            .iter()
            .filter(|var| var.origin == crate::compact::CompactVarOrigin::Primary)
            .map(|var| var.var)
            .collect::<Vec<_>>();
        (lower.len() == 1 && lower == upper).then(|| lower[0])
    }

    let output = lower_repository_std_for_cache_candidate_characterization();
    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let boundary = crate::analysis::cache_interface::CapturedBoundaryInterface::default();
    let captured = output.session.capture_cache_candidate_interface(&boundary);
    let list_module = output
        .modules
        .module_by_path(&sources::Path {
            segments: ["std", "data", "list"]
                .into_iter()
                .map(|segment| sources::Name(segment.to_string()))
                .collect(),
        })
        .expect("repository std list module");
    let impl_def = output
        .modules
        .role_impls(list_module)
        .iter()
        .find(|implementation| {
            implementation.methods.iter().any(|method| {
                method.name.0 == "index"
                    && method
                        .receiver
                        .as_ref()
                        .is_some_and(|receiver| receiver.0 == "r")
            })
        })
        .expect("ref-list Index source impl")
        .def;
    let index_role = vec![
        "std".to_string(),
        "data".to_string(),
        "index".to_string(),
        "Index".to_string(),
    ];
    let matching = captured
        .candidates
        .into_iter()
        .find(|captured| captured.candidate.impl_def == Some(impl_def))
        .expect("captured ref-list Index candidate");
    assert_eq!(matching.candidate.role, index_role);
    assert!(matching.candidate.prerequisites.is_empty());
    let compact = compact_role_constraint(
        output.session.infer.constraints(),
        &matching.candidate.as_constraint(),
    );

    let CompactBounds::Con {
        path: input_path,
        args: input_ref_args,
    } = &compact.inputs[0].bounds
    else {
        panic!("ref-list Index input must be a ref")
    };
    assert!(path_is(input_path, &["std", "control", "var", "ref"]));
    let [input_effect, input_item] = input_ref_args.as_slice() else {
        panic!("ref input must have effect and item arguments")
    };
    assert!(interval_contains_con(
        input_item,
        &["std", "data", "list", "list"]
    ));
    let [associated] = compact.associated.as_slice() else {
        panic!("Index must expose exactly one associated type")
    };
    assert_eq!(associated.name, "value");
    let CompactBounds::Con {
        path: associated_path,
        args: associated_ref_args,
    } = &associated.value.bounds
    else {
        panic!("ref-list Index value must be a ref")
    };
    assert!(path_is(associated_path, &["std", "control", "var", "ref"]));
    let [associated_effect, _associated_item] = associated_ref_args.as_slice() else {
        panic!("associated ref must have effect and item arguments")
    };
    let effect_binder = sole_shared_primary_interval_var(input_effect)
        .expect("input ref must retain the declared effect binder");
    let associated_effect_binder = sole_shared_primary_interval_var(associated_effect)
        .expect("associated ref must retain the declared effect binder");
    assert_eq!(associated_effect_binder, effect_binder);
    assert_eq!(matching.head_binders.len(), 2);
    assert!(matching.head_binders.contains(&effect_binder));

    let CompactBounds::Interval { lower, upper } = input_effect else {
        unreachable!("the effect argument was identified as an interval")
    };
    let weighted_alias = lower
        .vars
        .iter()
        .find(|var| {
            var.origin == crate::compact::CompactVarOrigin::Secondary
                && matches!(
                    var.weight.entries(),
                    [entry]
                        if entry.pops == u32::MAX
                            && entry.floor.is_empty()
                            && entry.stack.is_empty()
                )
        })
        .expect("effect interval must retain the pop-infinity weighted alias");
    assert_ne!(weighted_alias.var, effect_binder);
    assert!(upper.vars.iter().any(|var| {
        var.var == weighted_alias.var
            && var.origin == crate::compact::CompactVarOrigin::Secondary
            && var.weight.is_empty()
    }));

    let (settled_merges, settled_subtypes) = output
        .session
        .candidate_settlement_fact_counts(impl_def)
        .expect("source zero-prerequisite candidate must retain a settlement fact");
    assert!(
        settled_subtypes > 0,
        "the Index witness must exercise the candidate-local dominance lane"
    );
    let normalized = output
        .session
        .normalize_cache_candidate_interface(
            crate::analysis::cache_interface::CapturedCandidateInterface {
                candidates: vec![matching],
            },
            &boundary,
        )
        .expect("Slice 1 settlement must satisfy the strict Stage 4 audit");

    assert_eq!(normalized.candidates.len(), 1);
    assert_eq!(normalized.candidates[0].candidate.impl_def, Some(impl_def));
    assert_eq!(normalized.candidates[0].candidate.prerequisites.len(), 0);
    assert_eq!(settled_merges, 0);
}

/// Late candidate settlement must not rewrite any scheme already finalized by SCC generalization.
#[test]
fn candidate_settlement_preserves_every_repository_std_binding_scheme() {
    let output = lower_repository_std_for_cache_candidate_characterization();
    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert!(
        !output.session.has_pending_work(),
        "late settlement must not leave analysis work behind"
    );
    let witness = output
        .session
        .candidate_settlement_safety_witness()
        .expect("BodyLowerer::finish must record the settlement safety witness in tests");

    assert!(witness.eligible_candidates > 0);
    assert!(witness.recorded_candidates > 0);
    assert!(
        witness.unstable_candidates.is_empty(),
        "repository std must not contain a cross-candidate settlement conflict: {:?}",
        witness.unstable_candidates
    );
    assert_eq!(witness.binding_count_before, witness.binding_count_after);
    assert_eq!(witness.typed_lets_before, witness.typed_lets_after);
    assert_eq!(
        witness.missing_schemes_before,
        witness.missing_schemes_after
    );
    assert!(
        witness.all_binding_schemes_unchanged,
        "every finalized Scheme field must remain structurally identical across settlement"
    );
}

#[test]
fn candidate_settlement_excludes_imported_and_prerequisite_candidates() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let source_def = DefId(50);
    let imported_def = DefId(51);
    let prerequisite_def = DefId(52);
    let source_var = session.infer.fresh_type_var();
    let imported_var = session.infer.fresh_type_var();
    let synthetic_var = session.infer.fresh_type_var();
    let prerequisite_head = session.infer.fresh_type_var();
    let prerequisite_var = session.infer.fresh_type_var();
    session.role_impls.insert(RoleImplCandidate {
        impl_def: Some(source_def),
        role: vec!["SourceZeroPrerequisite".into()],
        inputs: vec![role_var_arg(&mut session.infer, source_var)],
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role: vec!["SyntheticZeroPrerequisite".into()],
        inputs: vec![role_var_arg(&mut session.infer, synthetic_var)],
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });
    session.role_impls.insert(RoleImplCandidate {
        impl_def: Some(imported_def),
        role: vec!["ImportedZeroPrerequisite".into()],
        inputs: vec![role_var_arg(&mut session.infer, imported_var)],
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });
    session.role_impls.insert(RoleImplCandidate {
        impl_def: Some(prerequisite_def),
        role: vec!["SourceWithPrerequisite".into()],
        inputs: vec![role_var_arg(&mut session.infer, prerequisite_head)],
        associated: Vec::new(),
        prerequisites: vec![RoleConstraint {
            role: vec!["Required".into()],
            inputs: vec![role_var_arg(&mut session.infer, prerequisite_var)],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    });

    session.settle_source_role_impl_candidates([source_def, prerequisite_def]);

    assert!(
        session
            .candidate_settlement_fact_counts(source_def)
            .is_some()
    );
    assert!(
        session
            .candidate_settlement_fact_counts(imported_def)
            .is_none()
    );
    assert!(
        session
            .candidate_settlement_fact_counts(prerequisite_def)
            .is_none()
    );
    let witness = session
        .candidate_settlement_safety_witness()
        .expect("settlement scope witness");
    assert_eq!(witness.eligible_candidates, 1);
    assert_eq!(witness.recorded_candidates, 1);
}

#[test]
fn cache_candidate_without_source_settlement_keeps_strict_freeze_rejection() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let impl_def = DefId(53);
    let lower_var = session.infer.fresh_type_var();
    let upper_var = session.infer.fresh_type_var();
    let lower = session.infer.alloc_pos(Pos::Var(lower_var));
    let upper = session.infer.alloc_neg(Neg::Var(upper_var));
    session.role_impls.insert(RoleImplCandidate {
        impl_def: Some(impl_def),
        role: vec!["ImportedUnsettledCandidate".into()],
        inputs: vec![RoleConstraintArg { lower, upper }],
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });
    let boundary = crate::analysis::cache_interface::CapturedBoundaryInterface::default();
    let captured = session.capture_cache_candidate_interface(&boundary);

    let error = session
        .normalize_cache_candidate_interface(captured, &boundary)
        .expect_err("a zero-prerequisite candidate without source settlement stays fail-closed");

    assert_eq!(
        error,
        crate::analysis::cache_interface::BoundaryCaptureError::FreezeProducedConstraint {
            def: Some(impl_def),
            boundary: None,
            merge_constraints: 1,
            subtype_constraints: 0,
        }
    );
}

#[test]
fn cache_candidate_joint_normalization_rewrites_closed_head_and_boundary_inventory() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let head = session.infer.fresh_type_var();
    let head_alias = session.infer.fresh_type_var();
    let boundary_var = session.infer.fresh_type_var();
    let head_lower = session.infer.alloc_pos(Pos::Var(head));
    let alias_upper = session.infer.alloc_neg(Neg::Var(head_alias));
    session.infer.subtype(head_lower, alias_upper);
    let alias_lower = session.infer.alloc_pos(Pos::Var(head_alias));
    let head_upper = session.infer.alloc_neg(Neg::Var(head));
    session.infer.subtype(alias_lower, head_upper);
    session.role_impls.insert(RoleImplCandidate {
        impl_def: Some(DefId(42)),
        role: vec!["NormalizedCandidate".into()],
        inputs: vec![
            role_var_arg(&mut session.infer, head),
            role_var_arg(&mut session.infer, boundary_var),
        ],
        associated: Vec::new(),
        prerequisites: vec![RoleConstraint {
            role: vec!["NormalizedPrerequisite".into()],
            inputs: vec![
                role_var_arg(&mut session.infer, head_alias),
                role_var_arg(&mut session.infer, boundary_var),
            ],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    });
    let boundary = crate::analysis::cache_interface::CapturedBoundaryInterface {
        bounds: vec![crate::analysis::cache_interface::CapturedBoundaryBound {
            var: boundary_var,
            bounds: CompactBounds::Interval {
                lower: CompactType::from_var(crate::compact::CompactVar::plain(boundary_var)),
                upper: CompactType::from_var(crate::compact::CompactVar::plain(boundary_var)),
            },
        }],
    };
    let captured = session.capture_cache_candidate_interface(&boundary);
    assert_eq!(captured.candidates[0].prerequisite_only, vec![head_alias]);

    let normalized = session
        .normalize_cache_candidate_interface(captured, &boundary)
        .expect("head and known B close the normalized candidate");

    assert_eq!(normalized.candidates.len(), 1);
    let candidate = &normalized.candidates[0];
    assert_eq!(candidate.candidate.impl_def, Some(DefId(42)));
    assert_eq!(candidate.head.role, vec!["NormalizedCandidate".to_string()]);
    assert_eq!(candidate.prerequisites.len(), 1);
    assert_eq!(candidate.head_binders, vec![head]);
    assert_eq!(candidate.boundary, vec![boundary_var]);
    assert!(
        compact_boundary_bound_vars(&candidate.head.inputs[0].bounds).contains(&head),
        "normalized head must retain its local binder"
    );
    let normalized_prerequisite_head =
        compact_boundary_bound_vars(&candidate.prerequisites[0].inputs[0].bounds);
    assert!(normalized_prerequisite_head.contains(&head));
    assert!(!normalized_prerequisite_head.contains(&head_alias));
    assert!(
        compact_boundary_bound_vars(&candidate.prerequisites[0].inputs[1].bounds)
            .contains(&boundary_var),
        "normalized prerequisite must retain the shared B occurrence"
    );
}

#[test]
fn cache_candidate_joint_normalization_rejects_surviving_prerequisite_only_variable() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let head = session.infer.fresh_type_var();
    let prerequisite_only = session.infer.fresh_type_var();
    session.role_impls.insert(RoleImplCandidate {
        impl_def: Some(DefId(43)),
        role: vec!["RejectedCandidate".into()],
        inputs: vec![role_var_arg(&mut session.infer, head)],
        associated: Vec::new(),
        prerequisites: vec![RoleConstraint {
            role: vec!["RejectedPrerequisite".into()],
            inputs: vec![role_var_arg(&mut session.infer, prerequisite_only)],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    });
    let boundary = crate::analysis::cache_interface::CapturedBoundaryInterface::default();
    let captured = session.capture_cache_candidate_interface(&boundary);

    let error = session
        .normalize_cache_candidate_interface(captured, &boundary)
        .expect_err("a surviving prerequisite-only variable is not canonical");

    assert_eq!(
        error,
        crate::analysis::cache_interface::BoundaryCaptureError::UnboundCandidateVariable {
            impl_def: Some(DefId(43)),
            role: vec!["RejectedCandidate".into()],
            var: prerequisite_only,
        }
    );
}

#[test]
fn cache_candidate_freeze_orders_and_deduplicates_without_breaking_shared_vars() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let shared = session.infer.fresh_type_var();
    let head_z = role_var_arg(&mut session.infer, shared);
    let head_a = role_var_arg(&mut session.infer, shared);
    let alpha_input = role_var_arg(&mut session.infer, shared);
    let alpha_z = role_var_arg(&mut session.infer, shared);
    let alpha_a = role_var_arg(&mut session.infer, shared);
    let alpha_duplicate_input = role_var_arg(&mut session.infer, shared);
    let alpha_duplicate_z = role_var_arg(&mut session.infer, shared);
    let alpha_duplicate_a = role_var_arg(&mut session.infer, shared);
    let zeta_input = role_var_arg(&mut session.infer, shared);
    session.role_impls.insert(RoleImplCandidate {
        impl_def: Some(DefId(44)),
        role: vec!["OrderedCandidate".into()],
        inputs: vec![role_var_arg(&mut session.infer, shared)],
        associated: vec![
            RoleAssociatedConstraint {
                name: "z".into(),
                value: head_z,
            },
            RoleAssociatedConstraint {
                name: "a".into(),
                value: head_a,
            },
        ],
        prerequisites: vec![
            RoleConstraint {
                role: vec!["Zeta".into()],
                inputs: vec![zeta_input],
                associated: Vec::new(),
            },
            RoleConstraint {
                role: vec!["Alpha".into()],
                inputs: vec![alpha_input],
                associated: vec![
                    RoleAssociatedConstraint {
                        name: "z".into(),
                        value: alpha_z,
                    },
                    RoleAssociatedConstraint {
                        name: "a".into(),
                        value: alpha_a,
                    },
                ],
            },
            RoleConstraint {
                role: vec!["Alpha".into()],
                inputs: vec![alpha_duplicate_input],
                associated: vec![
                    RoleAssociatedConstraint {
                        name: "z".into(),
                        value: alpha_duplicate_z,
                    },
                    RoleAssociatedConstraint {
                        name: "a".into(),
                        value: alpha_duplicate_a,
                    },
                ],
            },
        ],
        methods: vec![poly::roles::RoleImplMethod {
            requirement: DefId(45),
            implementation: DefId(46),
        }],
    });
    let boundary = crate::analysis::cache_interface::CapturedBoundaryInterface::default();
    let captured = session.capture_cache_candidate_interface(&boundary);
    let normalized = session
        .normalize_cache_candidate_interface(captured, &boundary)
        .expect("candidate should normalize");
    let mut reversed = normalized.clone();
    reversed.candidates[0].prerequisites.reverse();
    let mut first_poly = PolyArena::new();
    let mut second_poly = PolyArena::new();

    let first = session
        .freeze_cache_candidate_interface(normalized, &mut first_poly)
        .expect("first canonical freeze");
    let second = session
        .freeze_cache_candidate_interface(reversed, &mut second_poly)
        .expect("reordered canonical freeze");

    assert_eq!(
        first, second,
        "input prerequisite order must not affect freeze"
    );
    let [frozen] = first.candidates.as_slice() else {
        panic!("expected one frozen candidate");
    };
    assert_eq!(
        frozen
            .candidate
            .associated
            .iter()
            .map(|associated| associated.name.as_str())
            .collect::<Vec<_>>(),
        vec!["a", "z"]
    );
    assert_eq!(frozen.candidate.prerequisites.len(), 2);
    assert!(frozen.candidate.prerequisites.iter().all(|prerequisite| {
        prerequisite
            .associated
            .windows(2)
            .all(|pair| pair[0].name <= pair[1].name)
    }));
    assert_eq!(
        frozen.candidate.methods,
        vec![poly::roles::RoleImplMethod {
            requirement: DefId(45),
            implementation: DefId(46),
        }]
    );
    assert_eq!(frozen.head_binders, vec![shared]);
    assert!(frozen.boundary.is_empty());
    let head_vars = frozen.candidate.as_constraint().raw_vars(&first_poly.typ);
    assert_eq!(head_vars, FxHashSet::from_iter([shared]));
    assert!(frozen.candidate.prerequisites.iter().all(|prerequisite| {
        prerequisite.raw_vars(&first_poly.typ) == FxHashSet::from_iter([shared])
    }));
    assert!(matches!(
        first_poly.typ.pos(frozen.candidate.inputs[0].lower),
        Pos::Var(var) if *var == shared
    ));
    assert!(matches!(
        first_poly.typ.neg(frozen.candidate.inputs[0].upper),
        Neg::Var(var) if *var == shared
    ));
}

#[test]
fn cache_candidate_normalization_rejects_the_unit_batch_when_one_candidate_is_unbound() {
    let mut session = AnalysisSession::new(PolyArena::new());
    let closed = session.infer.fresh_type_var();
    session.role_impls.insert(RoleImplCandidate {
        impl_def: Some(DefId(47)),
        role: vec!["ClosedBatchCandidate".into()],
        inputs: vec![role_var_arg(&mut session.infer, closed)],
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });
    let open_head = session.infer.fresh_type_var();
    let open_prerequisite = session.infer.fresh_type_var();
    session.role_impls.insert(RoleImplCandidate {
        impl_def: Some(DefId(48)),
        role: vec!["OpenBatchCandidate".into()],
        inputs: vec![role_var_arg(&mut session.infer, open_head)],
        associated: Vec::new(),
        prerequisites: vec![RoleConstraint {
            role: vec!["OpenBatchPrerequisite".into()],
            inputs: vec![role_var_arg(&mut session.infer, open_prerequisite)],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    });
    let boundary = crate::analysis::cache_interface::CapturedBoundaryInterface::default();
    let captured = session.capture_cache_candidate_interface(&boundary);

    let error = session
        .normalize_cache_candidate_interface(captured, &boundary)
        .expect_err("one non-canonical candidate rejects the unit artifact batch");

    assert_eq!(
        error,
        crate::analysis::cache_interface::BoundaryCaptureError::UnboundCandidateVariable {
            impl_def: Some(DefId(48)),
            role: vec!["OpenBatchCandidate".into()],
            var: open_prerequisite,
        }
    );
}

#[test]
fn canonical_cache_handoff_installs_scheme_and_candidate_with_the_same_unit_boundary() {
    let (session, canonical, frozen, mut target, def, head, boundary_var) =
        canonical_cache_handoff_fixture();

    let boundary = canonical
        .with_frozen_candidates(frozen)
        .freeze_into_poly(session.infer.constraints(), &mut target)
        .expect("closed scheme/candidate handoff");

    assert_eq!(
        boundary
            .bounds
            .iter()
            .map(|bound| bound.var)
            .collect::<Vec<_>>(),
        vec![boundary_var]
    );
    let Some(Def::Let {
        scheme: Some(scheme),
        ..
    }) = target.defs.get(def)
    else {
        panic!("canonical scheme must be installed")
    };
    assert!(matches!(target.typ.pos(scheme.predicate), Pos::Var(var) if *var == boundary_var));

    let [candidate] = target
        .role_impls
        .candidates(&["HandoffCandidate".to_string()])
    else {
        panic!("canonical candidate must be installed")
    };
    assert_eq!(
        candidate.as_constraint().raw_vars(&target.typ),
        FxHashSet::from_iter([head, boundary_var])
    );
    assert_eq!(
        candidate.prerequisites[0].raw_vars(&target.typ),
        FxHashSet::from_iter([head, boundary_var])
    );
}

#[test]
fn canonical_cache_handoff_rejects_candidate_boundary_inventory_not_shared_with_unit_table() {
    let (session, canonical, mut frozen, mut target, def, _, boundary_var) =
        canonical_cache_handoff_fixture();
    frozen.candidates[0].boundary.clear();
    let before_nodes = target.typ.node_len();

    let error = canonical
        .with_frozen_candidates(frozen)
        .freeze_into_poly(session.infer.constraints(), &mut target)
        .expect_err("candidate B inventory must match the unit boundary table");

    assert_eq!(
        error,
        crate::analysis::cache_interface::BoundaryCaptureError::CandidateBinderInventoryMismatch {
            impl_def: Some(DefId(49)),
            role: vec!["HandoffCandidate".into()],
            var: boundary_var,
        }
    );
    assert_eq!(target.typ.node_len(), before_nodes);
    assert!(
        target
            .role_impls
            .candidates(&["HandoffCandidate".to_string()])
            .is_empty(),
        "validator failure must not partially install candidates"
    );
    let Some(Def::Let {
        scheme: Some(scheme),
        ..
    }) = target.defs.get(def)
    else {
        panic!("placeholder scheme must remain installed")
    };
    assert!(matches!(target.typ.pos(scheme.predicate), Pos::Tuple(items) if items.is_empty()));
}

#[test]
fn imported_boundary_is_seeded_once_at_root_with_shared_graph_references() {
    let first = TypeVar(10_000);
    let second = TypeVar(10_001);
    let mut poly = PolyArena::new();

    let int_lower = poly
        .typ
        .alloc_pos(Pos::Con(vec!["int".to_string()], Vec::new()));
    let second_upper = poly.typ.alloc_neg(Neg::Var(second));
    let first_bounds = poly.typ.alloc_neu(Neu::Bounds(int_lower, second_upper));

    let str_lower = poly
        .typ
        .alloc_pos(Pos::Con(vec!["str".to_string()], Vec::new()));
    let str_upper = poly
        .typ
        .alloc_neg(Neg::Con(vec!["str".to_string()], Vec::new()));
    let second_bounds = poly.typ.alloc_neu(Neu::Bounds(str_lower, str_upper));
    let boundary = crate::CompiledBoundaryInterface {
        bounds: vec![
            crate::CompiledBoundaryBound {
                var: first,
                bounds: first_bounds,
            },
            crate::CompiledBoundaryBound {
                var: second,
                bounds: second_bounds,
            },
        ],
    };

    let session = AnalysisSession::new_with_imported_boundary(poly, &boundary);
    let imported_first = session
        .imported_boundary_var(first)
        .expect("first boundary binder should be mapped");
    let imported_second = session
        .imported_boundary_var(second)
        .expect("second boundary binder should be mapped");

    assert_ne!(imported_first, imported_second);
    assert_eq!(
        session.infer.constraints().level_of(imported_first),
        TypeLevel::root()
    );
    assert_eq!(
        session.infer.constraints().level_of(imported_second),
        TypeLevel::root()
    );
    let first_infer_bounds = session
        .infer
        .constraints()
        .bounds()
        .of(imported_first)
        .expect("first imported binder should receive its interval");
    assert!(first_infer_bounds.lowers().iter().any(|bound| {
        matches!(
            session.infer.constraints().types().pos(bound.pos),
            Pos::Con(path, args) if path == &["int".to_string()] && args.is_empty()
        )
    }));
    assert!(first_infer_bounds.uppers().iter().any(|bound| {
        matches!(
            session.infer.constraints().types().neg(bound.neg),
            Neg::Var(var) if *var == imported_second
        )
    }));
    assert!(session.infer.constraints().events().is_empty());
}

#[test]
fn imported_boundary_does_not_create_a_mapping_for_an_unlisted_variable() {
    let listed = TypeVar(20_000);
    let unlisted = TypeVar(20_001);
    let mut poly = PolyArena::new();
    let lower = poly.typ.alloc_pos(Pos::Var(listed));
    let upper = poly.typ.alloc_neg(Neg::Var(listed));
    let bounds = poly.typ.alloc_neu(Neu::Bounds(lower, upper));
    let boundary = crate::CompiledBoundaryInterface {
        bounds: vec![crate::CompiledBoundaryBound {
            var: listed,
            bounds,
        }],
    };

    let session = AnalysisSession::new_with_imported_boundary(poly, &boundary);

    assert!(session.imported_boundary_var(listed).is_some());
    assert_eq!(session.imported_boundary_var(unlisted), None);
}

#[test]
fn joint_cache_freeze_keeps_bare_floor_boundary() {
    let def = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let boundary_var = session.infer.fresh_type_var();
    let concrete_lower = session
        .infer
        .alloc_pos(Pos::Con(vec!["token".into()], Vec::new()));
    let boundary_upper = session.infer.alloc_neg(Neg::Var(boundary_var));
    session.infer.subtype(concrete_lower, boundary_upper);
    let boundary_lower = session.infer.alloc_pos(Pos::Var(boundary_var));
    let concrete_upper = session
        .infer
        .alloc_neg(Neg::Con(vec!["token".into()], Vec::new()));
    session.infer.subtype(boundary_lower, concrete_upper);
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

    let canonical = session
        .freeze_cache_interface([def])
        .expect("bare floor boundary joint freeze");

    assert_eq!(canonical.binders.boundary, vec![boundary_var]);
    assert_eq!(canonical.boundary.bounds.len(), 1);
    assert!(
        canonical.schemes[0]
            .generalized
            .compact
            .root
            .vars
            .iter()
            .any(|var| var.var == boundary_var)
    );
}

#[test]
fn cache_interface_closure_prunes_unreachable_boundary_entry() {
    let def = DefId(0);
    let boundary_var = TypeVar(70);
    let draft = crate::analysis::cache_interface::CanonicalSchemeDraft {
        def,
        generalized: GeneralizedCompactRoot {
            compact: CompactRoot {
                root: CompactType::from_con(crate::compact::CompactCon {
                    path: vec!["token".into()],
                    args: Vec::new(),
                }),
                rec_vars: Vec::new(),
            },
            role_predicates: Vec::new(),
            quantifiers: Vec::new(),
            stack_quantifiers: Vec::new(),
            substitutions: Vec::new(),
            sandwiches: Vec::new(),
        },
    };
    let boundary = crate::analysis::cache_interface::CapturedBoundaryBound {
        var: boundary_var,
        bounds: CompactBounds::Interval {
            lower: CompactType::from_var(crate::compact::CompactVar::plain(boundary_var)),
            upper: CompactType::from_var(crate::compact::CompactVar::plain(boundary_var)),
        },
    };

    let canonical = crate::analysis::cache_interface::validate_and_prune_cache_interface(
        vec![draft],
        vec![boundary],
    )
    .expect("unreachable boundary pruning");

    assert!(canonical.boundary.bounds.is_empty());
    assert!(canonical.binders.boundary.is_empty());
}

#[test]
fn cache_interface_poly_freeze_rejects_missing_scheme_target_before_writing() {
    let def = DefId(0);
    let draft = crate::analysis::cache_interface::CanonicalSchemeDraft {
        def,
        generalized: GeneralizedCompactRoot {
            compact: CompactRoot {
                root: CompactType::from_con(crate::compact::CompactCon {
                    path: vec!["token".into()],
                    args: Vec::new(),
                }),
                rec_vars: Vec::new(),
            },
            role_predicates: Vec::new(),
            quantifiers: Vec::new(),
            stack_quantifiers: Vec::new(),
            substitutions: Vec::new(),
            sandwiches: Vec::new(),
        },
    };
    let canonical = crate::analysis::cache_interface::validate_and_prune_cache_interface(
        vec![draft],
        Vec::new(),
    )
    .expect("closed canonical draft");
    let session = AnalysisSession::new(PolyArena::new());
    let mut target = PolyArena::new();
    let before = target.typ.node_len();

    let error = canonical
        .freeze_into_poly(session.infer.constraints(), &mut target)
        .expect_err("a draft must not be frozen without its corresponding poly scheme");

    assert_eq!(
        error,
        crate::analysis::cache_interface::BoundaryCaptureError::MissingPolySchemeTarget { def }
    );
    assert_eq!(target.typ.node_len(), before);
}

#[test]
fn cache_interface_closure_rejects_unbound_scheme_variable() {
    let def = DefId(0);
    let unbound = TypeVar(71);
    let draft = crate::analysis::cache_interface::CanonicalSchemeDraft {
        def,
        generalized: GeneralizedCompactRoot {
            compact: CompactRoot {
                root: CompactType::from_var(crate::compact::CompactVar::plain(unbound)),
                rec_vars: Vec::new(),
            },
            role_predicates: Vec::new(),
            quantifiers: Vec::new(),
            stack_quantifiers: Vec::new(),
            substitutions: Vec::new(),
            sandwiches: Vec::new(),
        },
    };

    let error = crate::analysis::cache_interface::validate_and_prune_cache_interface(
        vec![draft],
        Vec::new(),
    )
    .expect_err("unbound variable must fail final Q/R/B closure");

    assert_eq!(
        error,
        crate::analysis::cache_interface::BoundaryCaptureError::UnboundSchemeVariable {
            def,
            var: unbound,
        }
    );
}

#[test]
fn cache_interface_closure_classifies_q_r_b_disjointly() {
    let def = DefId(0);
    let quantified = TypeVar(80);
    let recursive = TypeVar(81);
    let boundary_var = TypeVar(82);
    let draft = crate::analysis::cache_interface::CanonicalSchemeDraft {
        def,
        generalized: GeneralizedCompactRoot {
            compact: CompactRoot {
                root: CompactType {
                    vars: vec![
                        crate::compact::CompactVar::plain(quantified),
                        crate::compact::CompactVar::plain(recursive),
                        crate::compact::CompactVar::plain(boundary_var),
                    ],
                    ..CompactType::default()
                },
                rec_vars: vec![crate::compact::CompactRecursiveVar {
                    var: recursive,
                    bounds: CompactBounds::Interval {
                        lower: CompactType::from_var(crate::compact::CompactVar::plain(recursive)),
                        upper: CompactType::from_var(crate::compact::CompactVar::plain(recursive)),
                    },
                }],
            },
            role_predicates: Vec::new(),
            // Current Scheme representation includes R in quantifiers. The canonical
            // classification must still assign it to R only.
            quantifiers: vec![quantified, recursive],
            stack_quantifiers: Vec::new(),
            substitutions: Vec::new(),
            sandwiches: Vec::new(),
        },
    };
    let boundary = crate::analysis::cache_interface::CapturedBoundaryBound {
        var: boundary_var,
        bounds: CompactBounds::Interval {
            lower: CompactType::from_var(crate::compact::CompactVar::plain(boundary_var)),
            upper: CompactType::from_var(crate::compact::CompactVar::plain(boundary_var)),
        },
    };

    let canonical = crate::analysis::cache_interface::validate_and_prune_cache_interface(
        vec![draft],
        vec![boundary],
    )
    .expect("disjoint Q/R/B classification");

    assert_eq!(canonical.binders.boundary, vec![boundary_var]);
    assert_eq!(canonical.binders.schemes[0].quantified, vec![quantified]);
    assert_eq!(canonical.binders.schemes[0].recursive, vec![recursive]);
}

#[test]
fn cache_interface_closure_rejects_boundary_dependency_on_q() {
    let def = DefId(0);
    let quantified = TypeVar(90);
    let boundary_var = TypeVar(91);
    let draft = crate::analysis::cache_interface::CanonicalSchemeDraft {
        def,
        generalized: GeneralizedCompactRoot {
            compact: CompactRoot {
                root: CompactType::from_var(crate::compact::CompactVar::plain(boundary_var)),
                rec_vars: Vec::new(),
            },
            role_predicates: Vec::new(),
            quantifiers: vec![quantified],
            stack_quantifiers: Vec::new(),
            substitutions: Vec::new(),
            sandwiches: Vec::new(),
        },
    };
    let boundary = crate::analysis::cache_interface::CapturedBoundaryBound {
        var: boundary_var,
        bounds: CompactBounds::Interval {
            lower: CompactType::from_var(crate::compact::CompactVar::plain(quantified)),
            upper: CompactType::from_var(crate::compact::CompactVar::plain(boundary_var)),
        },
    };

    let error = crate::analysis::cache_interface::validate_and_prune_cache_interface(
        vec![draft],
        vec![boundary],
    )
    .expect_err("B bounds must not depend on a scheme-local Q binder");

    assert_eq!(
        error,
        crate::analysis::cache_interface::BoundaryCaptureError::BoundaryDependsOnLocalBinder {
            boundary: boundary_var,
            local: quantified,
        }
    );
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

fn lower_repository_std_for_cache_candidate_characterization() -> crate::lowering::BodyLowering {
    fn collect_yu_files(directory: &std::path::Path, files: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(directory).expect("read repository std directory") {
            let path = entry.expect("read repository std entry").path();
            if path.is_dir() {
                collect_yu_files(&path, files);
            } else if path.extension().and_then(|extension| extension.to_str()) == Some("yu") {
                files.push(path);
            }
        }
    }

    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("canonical repository root");
    let lib = repository.join("lib");
    let mut paths = vec![lib.join("std.yu")];
    collect_yu_files(&lib.join("std"), &mut paths);
    paths.sort();

    let mut files = vec![sources::SourceFile {
        module_path: sources::Path::default(),
        source: "use std::prelude::*\nmod std;\n".to_string(),
    }];
    files.extend(paths.into_iter().map(|path| {
        let relative = path.strip_prefix(&lib).expect("std source below lib");
        let mut module = relative.to_path_buf();
        module.set_extension("");
        let segments = module
            .components()
            .map(|component| {
                let std::path::Component::Normal(segment) = component else {
                    panic!("normal std module path component")
                };
                sources::Name(segment.to_str().expect("utf-8 std module path").to_string())
            })
            .collect();
        sources::SourceFile {
            module_path: sources::Path { segments },
            source: std::fs::read_to_string(&path).expect("read repository std source"),
        }
    }));
    let loaded = sources::load(files);
    crate::lowering::lower_loaded_files(&loaded).expect("lower repository std")
}

fn canonical_cache_handoff_fixture() -> (
    AnalysisSession,
    crate::analysis::cache_interface::CanonicalCacheInterfaceDraft,
    crate::analysis::cache_interface::FrozenCandidateInterface,
    PolyArena,
    DefId,
    TypeVar,
    TypeVar,
) {
    let def = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let boundary_var = session.infer.fresh_type_var();
    let head = session.infer.fresh_type_var();
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
    session.role_impls.insert(RoleImplCandidate {
        impl_def: Some(DefId(49)),
        role: vec!["HandoffCandidate".into()],
        inputs: vec![
            role_var_arg(&mut session.infer, head),
            role_var_arg(&mut session.infer, boundary_var),
        ],
        associated: Vec::new(),
        prerequisites: vec![RoleConstraint {
            role: vec!["HandoffPrerequisite".into()],
            inputs: vec![
                role_var_arg(&mut session.infer, head),
                role_var_arg(&mut session.infer, boundary_var),
            ],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    });

    let captured_boundary = session
        .capture_cache_boundary_interface([def])
        .expect("handoff boundary capture");
    let captured_candidates = session.capture_cache_candidate_interface(&captured_boundary);
    let normalized = session
        .normalize_cache_candidate_interface(captured_candidates, &captured_boundary)
        .expect("handoff candidate normalization");
    let canonical = session
        .freeze_cache_interface([def])
        .expect("handoff scheme/boundary draft");

    let mut target = PolyArena::new();
    let target_def = target.defs.fresh();
    assert_eq!(target_def, def);
    let placeholder = target.typ.alloc_pos(Pos::Tuple(Vec::new()));
    target.defs.set(
        target_def,
        Def::Let {
            vis: poly::expr::Vis::Pub,
            scheme: Some(Scheme {
                quantifiers: Vec::new(),
                role_predicates: Vec::new(),
                recursive_bounds: Vec::new(),
                stack_quantifiers: Vec::new(),
                predicate: placeholder,
            }),
            body: None,
            children: Vec::new(),
        },
    );
    let frozen = session
        .freeze_cache_candidate_interface(normalized, &mut target)
        .expect("handoff candidate freeze");

    (session, canonical, frozen, target, def, head, boundary_var)
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
