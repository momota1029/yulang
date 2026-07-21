use super::*;

#[test]
fn role_impl_member_residual_roles_become_impl_prerequisites() {
    let mut poly = PolyArena::new();
    let impl_def = poly.defs.fresh();
    poly.defs.set(
        impl_def,
        Def::Mod {
            vis: Vis::My,
            children: Vec::new(),
        },
    );
    let member = poly.defs.fresh();
    poly.defs.set(
        member,
        Def::Let {
            vis: Vis::Our,
            scheme: None,
            body: None,
            children: Vec::new(),
        },
    );
    let mut session = AnalysisSession::new(poly);
    let box_role = vec!["Box".to_string()];
    let eq_role = vec!["Eq".to_string()];
    let list_path = vec!["list".to_string()];
    let item = session.infer.fresh_type_var_at(TypeLevel::root());
    let member_root = session.infer.fresh_type_var_at(TypeLevel::root().child());

    session.role_impls.insert(RoleImplCandidate {
        impl_def: Some(impl_def),
        role: box_role.clone(),
        inputs: vec![role_unary_con_var_arg(&mut session.infer, list_path, item)],
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });
    session.register_role_impl_member(member, impl_def);
    session.roles.insert(
        member,
        RoleConstraint {
            role: eq_role.clone(),
            inputs: vec![role_var_arg(&mut session.infer, item)],
            associated: Vec::new(),
        },
    );
    let root_lower = session.infer.alloc_pos(Pos::Var(item));
    let root_upper = session.infer.alloc_neg(Neg::Var(member_root));
    session.infer.subtype(
        root_lower,
        root_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    session.enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
        def: member,
        root: member_root,
    }));
    session.enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: member }));
    session.drain_work();

    let candidates = session.role_impls.candidates(&box_role);
    assert_eq!(candidates.len(), 1);
    assert_eq!(candidates[0].prerequisites.len(), 1);
    assert_eq!(candidates[0].prerequisites[0].role, eq_role);
    assert!(matches!(
        session
            .infer
            .constraints()
            .types()
            .pos(candidates[0].prerequisites[0].inputs[0].lower),
        Pos::Var(var) if *var == item
    ));
}

#[test]
fn instantiate_use_freshens_quantifiers_at_secondary_level() {
    let mut poly = PolyArena::new();
    let def = poly.defs.fresh();
    let quantified = TypeVar(42);
    let predicate = poly.typ.alloc_pos(Pos::Var(quantified));
    poly.defs.set(
        def,
        Def::Let {
            vis: Vis::My,
            scheme: Some(Scheme {
                quantifiers: vec![quantified],
                role_predicates: Vec::new(),
                recursive_bounds: Vec::new(),
                stack_quantifiers: Vec::new(),
                predicate,
            }),
            body: None,
            children: Vec::new(),
        },
    );
    let mut session = AnalysisSession::new(poly);
    let use_value = TypeVar(10);
    session
        .infer
        .constraints_mut()
        .register_type_var(use_value, TypeLevel::root());

    session.instantiate_use(DefId(99), def, use_value);

    let use_bounds = session
        .infer
        .constraints()
        .bounds()
        .of(use_value)
        .expect("use value should receive instantiated lower bound");
    let fresh = use_bounds
        .lowers()
        .iter()
        .find_map(
            |bound| match session.infer.constraints().types().pos(bound.pos) {
                Pos::Var(var) if *var != quantified => Some(*var),
                _ => None,
            },
        )
        .expect("scheme quantifier should be freshened");
    assert_eq!(
        session.infer.constraints().level_of(fresh),
        TypeLevel::root()
    );
}

#[test]
fn instantiate_use_freshens_non_subtract_stack_quantifier_id() {
    let mut poly = PolyArena::new();
    let def = poly.defs.fresh();
    let quantified = TypeVar(42);
    let source_subtract = SubtractId(99);
    let inner = poly.typ.alloc_pos(Pos::Var(quantified));
    let predicate = poly
        .typ
        .alloc_pos(Pos::NonSubtract(inner, StackWeight::pop(source_subtract)));
    poly.defs.set(
        def,
        Def::Let {
            vis: Vis::My,
            scheme: Some(Scheme {
                quantifiers: vec![quantified],
                role_predicates: Vec::new(),
                recursive_bounds: Vec::new(),
                stack_quantifiers: vec![source_subtract],
                predicate,
            }),
            body: None,
            children: Vec::new(),
        },
    );
    let mut session = AnalysisSession::new(poly);
    let use_value = TypeVar(10);
    session
        .infer
        .constraints_mut()
        .register_type_var(use_value, TypeLevel::root());

    session.instantiate_use(DefId(99), def, use_value);

    let use_bounds = session
        .infer
        .constraints()
        .bounds()
        .of(use_value)
        .expect("use value should receive instantiated lower bound");
    let (fresh_var, fresh_subtract) = use_bounds
        .lowers()
        .iter()
        .find_map(
            |bound| match session.infer.constraints().types().pos(bound.pos) {
                Pos::Var(var) if !bound.weights.left.is_empty() => {
                    Some((*var, bound.weights.left.iter().next().unwrap()))
                }
                _ => None,
            },
        )
        .expect("non-subtract should add a fresh left weight to the instantiated bound");
    assert_ne!(fresh_var, quantified);
    assert_ne!(fresh_subtract, source_subtract);
}

#[test]
fn routes_effect_filter_violation_to_analysis_diagnostic() {
    let poly = PolyArena::new();
    let mut session = AnalysisSession::new(poly);
    let source = TypeVar(0);
    let tail = session.infer.alloc_neg(Neg::Var(TypeVar(1)));
    let item = session
        .infer
        .alloc_neg(Neg::Con(vec!["nondet".into()], Vec::new()));
    let lower = session.infer.alloc_pos(Pos::Var(source));
    let upper = session.infer.alloc_neg(Neg::Row(vec![item], tail));
    let filter = Subtractability::Set(vec!["io".into()], Vec::new());
    session.infer.constraints_mut().weighted_subtype(
        lower,
        ConstraintWeights {
            left: LeftConstraintWeight::filter(filter.clone()),
            right: RightConstraintWeight::empty(),
        },
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    session.route_constraint_events();

    assert_eq!(
        session.take_diagnostics(),
        vec![AnalysisDiagnostic::EffectFilterViolation {
            effect: Some(vec!["nondet".into()]),
            filter,
        }]
    );
}

#[test]
fn instantiate_use_restores_recursive_bounds_for_fresh_quantifier() {
    let mut poly = PolyArena::new();
    let def = poly.defs.fresh();
    let quantified = TypeVar(42);
    let predicate = poly.typ.alloc_pos(Pos::Var(quantified));
    let int = poly.typ.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let top = poly.typ.alloc_neg(Neg::Top);
    let bounds = poly.typ.alloc_neu(Neu::Bounds(int, top));
    poly.defs.set(
        def,
        Def::Let {
            vis: Vis::My,
            scheme: Some(Scheme {
                quantifiers: vec![quantified],
                role_predicates: Vec::new(),
                recursive_bounds: vec![SchemeRecursiveBound {
                    var: quantified,
                    bounds,
                }],
                stack_quantifiers: Vec::new(),
                predicate,
            }),
            body: None,
            children: Vec::new(),
        },
    );
    let mut session = AnalysisSession::new(poly);
    let use_value = TypeVar(10);
    session
        .infer
        .constraints_mut()
        .register_type_var(use_value, TypeLevel::root());

    session.instantiate_use(DefId(99), def, use_value);

    let use_bounds = session
        .infer
        .constraints()
        .bounds()
        .of(use_value)
        .expect("use value should receive instantiated lower bound");
    let fresh = use_bounds
        .lowers()
        .iter()
        .find_map(
            |bound| match session.infer.constraints().types().pos(bound.pos) {
                Pos::Var(var) if *var != quantified => Some(*var),
                _ => None,
            },
        )
        .expect("scheme quantifier should be freshened");
    let fresh_bounds = session
        .infer
        .constraints()
        .bounds()
        .of(fresh)
        .expect("recursive bounds should be restored onto the fresh var");
    assert!(fresh_bounds.lowers().iter().any(|bound| matches!(
        session.infer.constraints().types().pos(bound.pos),
        Pos::Con(path, args) if path.len() == 1 && path[0] == "int" && args.is_empty()
    )));
}

#[test]
fn instantiate_imported_scheme_freshens_q_r_per_use_and_shares_b() {
    let quantified = TypeVar(40_000);
    let recursive = TypeVar(40_001);
    let boundary_var = TypeVar(40_002);
    let mut poly = PolyArena::new();
    let quantified_pos = poly.typ.alloc_pos(Pos::Var(quantified));
    let recursive_pos = poly.typ.alloc_pos(Pos::Var(recursive));
    let boundary_pos = poly.typ.alloc_pos(Pos::Var(boundary_var));
    let predicate = poly.typ.alloc_pos(Pos::Tuple(vec![
        quantified_pos,
        recursive_pos,
        boundary_pos,
    ]));
    let recursive_lower = poly.typ.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let recursive_upper = poly.typ.alloc_neg(Neg::Top);
    let recursive_bounds = poly
        .typ
        .alloc_neu(Neu::Bounds(recursive_lower, recursive_upper));
    let boundary_lower = poly.typ.alloc_pos(Pos::Var(boundary_var));
    let boundary_upper = poly.typ.alloc_neg(Neg::Var(boundary_var));
    let boundary_bounds = poly
        .typ
        .alloc_neu(Neu::Bounds(boundary_lower, boundary_upper));
    let def = poly.defs.fresh();
    poly.defs.set(
        def,
        Def::Let {
            vis: Vis::Pub,
            scheme: Some(Scheme {
                quantifiers: vec![quantified],
                role_predicates: Vec::new(),
                recursive_bounds: vec![SchemeRecursiveBound {
                    var: recursive,
                    bounds: recursive_bounds,
                }],
                stack_quantifiers: Vec::new(),
                predicate,
            }),
            body: None,
            children: Vec::new(),
        },
    );
    let boundary = crate::CompiledBoundaryInterface {
        bounds: vec![crate::CompiledBoundaryBound {
            var: boundary_var,
            bounds: boundary_bounds,
        }],
    };
    let mut session = AnalysisSession::new_with_imported_boundary(poly, &boundary);
    let first_use = session.infer.fresh_type_var_at(TypeLevel::root());
    let second_use = session.infer.fresh_type_var_at(TypeLevel::root());

    session.instantiate_use(DefId(90), def, first_use);
    session.instantiate_use(DefId(91), def, second_use);

    let [first_q, first_r, first_b] = instantiated_tuple_vars(&session, first_use);
    let [second_q, second_r, second_b] = instantiated_tuple_vars(&session, second_use);
    assert_ne!(first_q, second_q, "Q must be fresh for each use");
    assert_ne!(first_r, second_r, "R must be fresh for each use");
    assert_eq!(first_b, second_b, "B must be shared by every use");
    assert_eq!(
        Some(first_b),
        session.imported_boundary_var(boundary_var),
        "scheme B must reuse the session-level imported mapping"
    );
    assert!(
        session
            .take_imported_scheme_instantiation_failures()
            .is_empty()
    );
}

#[test]
fn instantiate_imported_scheme_rejects_unmapped_free_type_var() {
    let boundary_var = TypeVar(50_000);
    let unknown = TypeVar(50_001);
    let mut poly = PolyArena::new();
    let boundary_pos = poly.typ.alloc_pos(Pos::Var(boundary_var));
    let unknown_pos = poly.typ.alloc_pos(Pos::Var(unknown));
    let predicate = poly
        .typ
        .alloc_pos(Pos::Tuple(vec![boundary_pos, unknown_pos]));
    let boundary_lower = poly.typ.alloc_pos(Pos::Var(boundary_var));
    let boundary_upper = poly.typ.alloc_neg(Neg::Var(boundary_var));
    let boundary_bounds = poly
        .typ
        .alloc_neu(Neu::Bounds(boundary_lower, boundary_upper));
    let def = poly.defs.fresh();
    poly.defs.set(
        def,
        Def::Let {
            vis: Vis::Pub,
            scheme: Some(Scheme {
                quantifiers: Vec::new(),
                role_predicates: Vec::new(),
                recursive_bounds: Vec::new(),
                stack_quantifiers: Vec::new(),
                predicate,
            }),
            body: None,
            children: Vec::new(),
        },
    );
    let boundary = crate::CompiledBoundaryInterface {
        bounds: vec![crate::CompiledBoundaryBound {
            var: boundary_var,
            bounds: boundary_bounds,
        }],
    };
    let mut session = AnalysisSession::new_with_imported_boundary(poly, &boundary);
    let use_value = session.infer.fresh_type_var_at(TypeLevel::root());
    let parent = DefId(99);

    session.instantiate_use(parent, def, use_value);

    assert_eq!(
        session.take_imported_scheme_instantiation_failures(),
        vec![ImportedSchemeInstantiationFailure {
            parent,
            target: def,
            error: SchemeInstantiationError::UnmappedFreeTypeVar { var: unknown },
        }]
    );
    assert!(
        session.infer.constraints().bounds().of(use_value).is_none(),
        "a rejected canonical scheme must not add a partial use constraint"
    );
}

#[test]
fn freshen_imported_role_candidate_shares_b_with_scheme_instantiation() {
    let boundary_var = TypeVar(60_000);
    let head_var = TypeVar(60_001);
    let mut poly = PolyArena::new();
    let predicate = poly.typ.alloc_pos(Pos::Var(boundary_var));
    let boundary_lower = poly.typ.alloc_pos(Pos::Var(boundary_var));
    let boundary_upper = poly.typ.alloc_neg(Neg::Var(boundary_var));
    let boundary_bounds = poly
        .typ
        .alloc_neu(Neu::Bounds(boundary_lower, boundary_upper));
    let def = poly.defs.fresh();
    poly.defs.set(
        def,
        Def::Let {
            vis: Vis::Pub,
            scheme: Some(Scheme {
                quantifiers: Vec::new(),
                role_predicates: Vec::new(),
                recursive_bounds: Vec::new(),
                stack_quantifiers: Vec::new(),
                predicate,
            }),
            body: None,
            children: Vec::new(),
        },
    );
    let head = poly_role_var_arg(&mut poly, head_var);
    let prerequisite_boundary = poly_role_var_arg(&mut poly, boundary_var);
    poly.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role: vec!["ImportedRole".into()],
        inputs: vec![head],
        associated: Vec::new(),
        prerequisites: vec![RoleConstraint {
            role: vec!["NeedsBoundary".into()],
            inputs: vec![prerequisite_boundary],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    });
    let boundary = crate::CompiledBoundaryInterface {
        bounds: vec![crate::CompiledBoundaryBound {
            var: boundary_var,
            bounds: boundary_bounds,
        }],
    };
    let mut session = AnalysisSession::new_with_imported_boundary(poly, &boundary);
    let use_value = session.infer.fresh_type_var_at(TypeLevel::root());

    session.instantiate_use(DefId(95), def, use_value);

    let imported_b = session
        .imported_boundary_var(boundary_var)
        .expect("boundary should have one session-level mapping");
    let use_bounds = session
        .infer
        .constraints()
        .bounds()
        .of(use_value)
        .expect("scheme use should receive the imported B lower bound");
    assert!(use_bounds.lowers().iter().any(|bound| matches!(
        session.infer.constraints().types().pos(bound.pos),
        Pos::Var(var) if *var == imported_b
    )));
    let candidate = &session.role_impls.candidates(&["ImportedRole".into()])[0];
    let candidate_head = candidate
        .as_constraint()
        .raw_vars(session.infer.constraints().types());
    assert_eq!(candidate_head.len(), 1);
    assert!(!candidate_head.contains(&head_var));
    assert!(!candidate_head.contains(&imported_b));
    assert_eq!(
        candidate.prerequisites[0].raw_vars(session.infer.constraints().types()),
        FxHashSet::from_iter([imported_b]),
        "scheme and impl prerequisite must point at the same imported B"
    );
}

#[test]
fn oracle_a1_stage_3_exit_preserves_q_r_and_b_lifetimes_across_imported_uses() {
    let quantified = TypeVar(62_000);
    let recursive = TypeVar(62_001);
    let boundary_var = TypeVar(62_002);
    let candidate_head_var = TypeVar(62_003);
    let mut poly = PolyArena::new();
    let quantified_pos = poly.typ.alloc_pos(Pos::Var(quantified));
    let recursive_pos = poly.typ.alloc_pos(Pos::Var(recursive));
    let boundary_pos = poly.typ.alloc_pos(Pos::Var(boundary_var));
    let predicate = poly.typ.alloc_pos(Pos::Tuple(vec![
        quantified_pos,
        recursive_pos,
        boundary_pos,
    ]));
    let recursive_lower = poly.typ.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let recursive_upper = poly.typ.alloc_neg(Neg::Top);
    let recursive_bounds = poly
        .typ
        .alloc_neu(Neu::Bounds(recursive_lower, recursive_upper));
    let boundary_lower = poly.typ.alloc_pos(Pos::Var(boundary_var));
    let boundary_upper = poly.typ.alloc_neg(Neg::Var(boundary_var));
    let boundary_bounds = poly
        .typ
        .alloc_neu(Neu::Bounds(boundary_lower, boundary_upper));
    let def = poly.defs.fresh();
    poly.defs.set(
        def,
        Def::Let {
            vis: Vis::Pub,
            scheme: Some(Scheme {
                quantifiers: vec![quantified],
                role_predicates: Vec::new(),
                recursive_bounds: vec![SchemeRecursiveBound {
                    var: recursive,
                    bounds: recursive_bounds,
                }],
                stack_quantifiers: Vec::new(),
                predicate,
            }),
            body: None,
            children: Vec::new(),
        },
    );
    let candidate_head = poly_role_var_arg(&mut poly, candidate_head_var);
    let candidate_boundary = poly_role_var_arg(&mut poly, boundary_var);
    poly.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role: vec!["OracleA1Role".into()],
        inputs: vec![candidate_head],
        associated: Vec::new(),
        prerequisites: vec![RoleConstraint {
            role: vec!["OracleA1Boundary".into()],
            inputs: vec![candidate_boundary],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    });
    let boundary = crate::CompiledBoundaryInterface {
        bounds: vec![crate::CompiledBoundaryBound {
            var: boundary_var,
            bounds: boundary_bounds,
        }],
    };
    let mut session = AnalysisSession::new_with_imported_boundary(poly, &boundary);
    let first_use = session.infer.fresh_type_var_at(TypeLevel::root());
    let second_use = session.infer.fresh_type_var_at(TypeLevel::root());

    session.instantiate_use(DefId(96), def, first_use);
    session.instantiate_use(DefId(97), def, second_use);

    let [first_q, first_r, first_b] = instantiated_tuple_vars(&session, first_use);
    let [second_q, second_r, second_b] = instantiated_tuple_vars(&session, second_use);
    assert_ne!(first_q, quantified);
    assert_ne!(second_q, quantified);
    assert_ne!(first_q, second_q, "Q must be fresh for each imported use");
    assert_ne!(first_r, recursive);
    assert_ne!(second_r, recursive);
    assert_ne!(first_r, second_r, "R must be fresh for each imported use");
    assert_eq!(first_b, second_b, "B must be shared between imported uses");
    let imported_b = session
        .imported_boundary_var(boundary_var)
        .expect("B should have one session-level imported mapping");
    assert_eq!(first_b, imported_b);

    let candidate = &session.role_impls.candidates(&["OracleA1Role".into()])[0];
    let fresh_candidate_head = candidate
        .as_constraint()
        .raw_vars(session.infer.constraints().types());
    assert_eq!(fresh_candidate_head.len(), 1);
    assert!(!fresh_candidate_head.contains(&candidate_head_var));
    assert!(!fresh_candidate_head.contains(&imported_b));
    assert_eq!(
        candidate.prerequisites[0].raw_vars(session.infer.constraints().types()),
        FxHashSet::from_iter([imported_b]),
        "scheme instantiation and role candidate freshening must share B"
    );
    let witness = session
        .imported_instantiation_witness(def, &["OracleA1Role".into()])
        .expect("the integration witness must observe the same imported session machinery");
    assert!(!witness.first_recursive.is_empty());
    assert!(
        witness
            .first_recursive
            .iter()
            .all(|var| !witness.second_recursive.contains(var)),
        "the witness view must preserve non-empty R per-use freshness"
    );
    assert_eq!(witness.first_boundary, witness.second_boundary);
    assert_eq!(witness.imported_candidate_boundary, witness.first_boundary);
    assert!(
        session
            .take_imported_scheme_instantiation_failures()
            .is_empty()
    );
}

#[test]
fn freshen_imported_role_candidate_keeps_unmapped_prerequisite_var_fresh() {
    let boundary_var = TypeVar(61_000);
    let head_var = TypeVar(61_001);
    let prerequisite_var = TypeVar(61_002);
    let mut poly = PolyArena::new();
    let boundary_lower = poly.typ.alloc_pos(Pos::Var(boundary_var));
    let boundary_upper = poly.typ.alloc_neg(Neg::Var(boundary_var));
    let boundary_bounds = poly
        .typ
        .alloc_neu(Neu::Bounds(boundary_lower, boundary_upper));
    let head = poly_role_var_arg(&mut poly, head_var);
    let prerequisite = poly_role_var_arg(&mut poly, prerequisite_var);
    poly.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role: vec!["LegacyImportedRole".into()],
        inputs: vec![head],
        associated: Vec::new(),
        prerequisites: vec![RoleConstraint {
            role: vec!["LegacyPrerequisite".into()],
            inputs: vec![prerequisite],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    });
    let boundary = crate::CompiledBoundaryInterface {
        bounds: vec![crate::CompiledBoundaryBound {
            var: boundary_var,
            bounds: boundary_bounds,
        }],
    };

    let session = AnalysisSession::new_with_imported_boundary(poly, &boundary);

    let candidate = &session
        .role_impls
        .candidates(&["LegacyImportedRole".into()])[0];
    let prerequisite_vars =
        candidate.prerequisites[0].raw_vars(session.infer.constraints().types());
    assert_eq!(prerequisite_vars.len(), 1);
    assert!(!prerequisite_vars.contains(&prerequisite_var));
    assert!(
        !prerequisite_vars.contains(
            &session
                .imported_boundary_var(boundary_var)
                .expect("boundary mapping")
        )
    );
}

fn poly_role_var_arg(poly: &mut PolyArena, var: TypeVar) -> RoleConstraintArg {
    let lower = poly.typ.alloc_pos(Pos::Var(var));
    let upper = poly.typ.alloc_neg(Neg::Var(var));
    RoleConstraintArg { lower, upper }
}

fn instantiated_tuple_vars(session: &AnalysisSession, use_value: TypeVar) -> [TypeVar; 3] {
    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(use_value)
        .expect("use value should receive an instantiated tuple lower bound");
    let items = bounds
        .lowers()
        .iter()
        .find_map(
            |bound| match session.infer.constraints().types().pos(bound.pos) {
                Pos::Tuple(items) => Some(items),
                _ => None,
            },
        )
        .expect("instantiated scheme predicate should remain a tuple");
    let vars = items
        .iter()
        .map(
            |item| match session.infer.constraints().types().pos(*item) {
                Pos::Var(var) => *var,
                other => panic!("tuple witness should contain only variables, got {other:?}"),
            },
        )
        .collect::<Vec<_>>();
    vars.try_into()
        .expect("tuple witness should contain Q, R, and B")
}

#[test]
fn compact_cast_prepass_normalizes_bidirectional_constructor_pair_once() {
    let source = vec!["source".to_string()];
    let target = vec!["target".to_string()];
    let mut session = AnalysisSession::new(PolyArena::new());
    let source_to_target =
        monomorphic_cast_scheme(&mut session.poly.typ, source.clone(), target.clone());
    let target_to_source =
        monomorphic_cast_scheme(&mut session.poly.typ, target.clone(), source.clone());
    session
        .casts
        .insert(source.clone(), target.clone(), source_to_target);
    session
        .casts
        .insert(target.clone(), source.clone(), target_to_source);

    let root = session.infer.fresh_type_var();
    let source_lower = session
        .infer
        .alloc_pos(Pos::Con(source.clone(), Vec::new()));
    let target_lower = session
        .infer
        .alloc_pos(Pos::Con(target.clone(), Vec::new()));
    let root_upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(
        source_lower,
        root_upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    session.infer.subtype(
        target_lower,
        root_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    let generalized = session.generalize_root_with_prepasses(DefId(0), root);

    assert_eq!(generalized.compact.root.cons.len(), 1);
    assert!(generalized.compact.root.cons.contains_key(&target));
}

#[test]
fn compact_cast_prepass_adds_cast_scheme_payload_constraints() {
    let source = vec!["source".to_string()];
    let target = vec!["target".to_string()];
    let mut session = AnalysisSession::new(PolyArena::new());
    let cast = generic_unary_cast_scheme(&mut session.poly.typ, source.clone(), target.clone());
    session.casts.insert(source.clone(), target.clone(), cast);

    let root = session.infer.fresh_type_var();
    let source_payload = session.infer.fresh_type_var();
    let target_payload = session.infer.fresh_type_var();
    let source_neu = infer_bounds_neu(&mut session.infer, source_payload);
    let target_neu = infer_bounds_neu(&mut session.infer, target_payload);
    let source_lower = session
        .infer
        .alloc_pos(Pos::Con(source.clone(), vec![source_neu]));
    let target_lower = session
        .infer
        .alloc_pos(Pos::Con(target.clone(), vec![target_neu]));
    let root_upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(
        source_lower,
        root_upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    session.infer.subtype(
        target_lower,
        root_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    let generalized = session.generalize_root_with_prepasses(DefId(0), root);

    assert_eq!(generalized.compact.root.cons.len(), 1);
    assert!(generalized.compact.root.cons.contains_key(&target));
    assert!(
        session
            .infer
            .constraints()
            .bounds()
            .of(source_payload)
            .is_some()
    );
    assert!(
        session
            .infer
            .constraints()
            .bounds()
            .of(target_payload)
            .is_some()
    );
}

#[test]
fn role_prepass_resolves_concrete_impl_and_constrains_associated_type() {
    let role = vec!["Add".to_string()];
    let int_path = vec!["int".to_string()];
    let owner = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let root = session.infer.fresh_type_var();
    let output = session.infer.fresh_type_var();
    let int_arg = role_exact_arg(&mut session.infer, int_path.clone());
    session.roles.insert(
        owner,
        RoleConstraint {
            role: role.clone(),
            inputs: vec![
                role_exact_arg(&mut session.infer, int_path.clone()),
                role_exact_arg(&mut session.infer, int_path.clone()),
            ],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_var_arg(&mut session.infer, output),
            }],
        },
    );
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role,
        inputs: vec![int_arg.clone(), int_arg],
        associated: vec![RoleAssociatedConstraint {
            name: "out".into(),
            value: role_exact_arg(&mut session.infer, int_path.clone()),
        }],
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });

    let root_lower = session.infer.alloc_pos(Pos::Var(output));
    let root_upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(
        root_lower,
        root_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    session.generalize_root_with_prepasses(owner, root);

    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(output)
        .expect("role associated output should receive impl bounds");
    assert!(bounds.lowers().iter().any(|bound| {
        matches!(
            session.infer.constraints().types().pos(bound.pos),
            Pos::Con(path, _) if path == &int_path
        )
    }));
    assert!(bounds.uppers().iter().any(|bound| {
        matches!(
            session.infer.constraints().types().neg(bound.neg),
            Neg::Con(path, _) if path == &int_path
        )
    }));
}

#[test]
fn role_prepass_coalesces_shared_input_roles_before_resolution() {
    let role = vec!["Add".to_string()];
    let int_path = vec!["int".to_string()];
    let owner = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let root = session.infer.fresh_type_var();
    let shared = session.infer.fresh_type_var();
    let first_output = session.infer.fresh_type_var();
    let second_output = session.infer.fresh_type_var();
    let int_arg = role_exact_arg(&mut session.infer, int_path.clone());
    session.roles.insert(
        owner,
        RoleConstraint {
            role: role.clone(),
            inputs: vec![
                role_var_arg(&mut session.infer, shared),
                role_exact_arg(&mut session.infer, int_path.clone()),
            ],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_var_arg(&mut session.infer, first_output),
            }],
        },
    );
    session.roles.insert(
        owner,
        RoleConstraint {
            role: role.clone(),
            inputs: vec![
                role_var_arg(&mut session.infer, shared),
                role_exact_arg(&mut session.infer, int_path.clone()),
            ],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_var_arg(&mut session.infer, second_output),
            }],
        },
    );
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role,
        inputs: vec![int_arg.clone(), int_arg],
        associated: vec![RoleAssociatedConstraint {
            name: "out".into(),
            value: role_exact_arg(&mut session.infer, int_path.clone()),
        }],
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });

    let shared_lower = session
        .infer
        .alloc_pos(Pos::Con(int_path.clone(), Vec::new()));
    let shared_upper = session.infer.alloc_neg(Neg::Var(shared));
    session.infer.subtype(
        shared_lower,
        shared_upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    let root_lower = session.infer.alloc_pos(Pos::Var(first_output));
    let root_upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(
        root_lower,
        root_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    session.generalize_root_with_prepasses(owner, root);

    assert_var_has_exact_bound(&session, first_output, &int_path);
    assert_var_has_exact_bound(&session, second_output, &int_path);
}

#[test]
fn role_prepass_resolves_unary_con_candidate_with_open_payload_bounds() {
    let role = vec!["Add".to_string()];
    let list_path = vec!["list".to_string()];
    let owner = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let root = session.infer.fresh_type_var();
    let payload = session.infer.fresh_type_var();
    let lower_payload = session.infer.fresh_type_var();
    let upper_payload = session.infer.fresh_type_var();
    let item = session.infer.fresh_type_var();
    session.roles.insert(
        owner,
        RoleConstraint {
            role: role.clone(),
            inputs: vec![role_unary_con_open_arg(
                &mut session.infer,
                list_path.clone(),
                payload,
                lower_payload,
                upper_payload,
            )],
            associated: Vec::new(),
        },
    );
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role: role.clone(),
        inputs: vec![role_unary_con_var_arg(&mut session.infer, list_path, item)],
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });

    let root_lower = session.infer.alloc_pos(Pos::Var(payload));
    let root_upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(
        root_lower,
        root_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    let generalized = session.generalize_root_with_prepasses(owner, root);

    assert!(
        generalized
            .role_predicates
            .iter()
            .all(|predicate| predicate.role != role)
    );
}

#[test]
fn role_prepass_resolves_unary_con_candidate_with_open_payload_and_top_var() {
    let role = vec!["Add".to_string()];
    let list_path = vec!["list".to_string()];
    let owner = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let root = session.infer.fresh_type_var();
    let payload = session.infer.fresh_type_var();
    let lower_payload = session.infer.fresh_type_var();
    let upper_payload = session.infer.fresh_type_var();
    let extra = session.infer.fresh_type_var();
    let item = session.infer.fresh_type_var();
    session.roles.insert(
        owner,
        RoleConstraint {
            role: role.clone(),
            inputs: vec![role_unary_con_open_or_var_arg(
                &mut session.infer,
                list_path.clone(),
                payload,
                lower_payload,
                upper_payload,
                extra,
            )],
            associated: Vec::new(),
        },
    );
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role: role.clone(),
        inputs: vec![role_unary_con_var_arg(&mut session.infer, list_path, item)],
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });

    let root_lower = session.infer.alloc_pos(Pos::Var(extra));
    let root_upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(
        root_lower,
        root_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    let generalized = session.generalize_root_with_prepasses(owner, root);

    assert!(
        generalized
            .role_predicates
            .iter()
            .all(|predicate| predicate.role != role)
    );
}

#[test]
fn role_prepass_resolves_unary_con_candidate_with_positive_extra_outputs() {
    let role = vec!["Add".to_string()];
    let list_path = vec!["list".to_string()];
    let owner = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let root = session.infer.fresh_type_var();
    let first_extra = session.infer.fresh_type_var();
    let second_extra = session.infer.fresh_type_var();
    let lower_payload = session.infer.fresh_type_var();
    let upper_payload = session.infer.fresh_type_var();
    let candidate_item = session.infer.fresh_type_var();
    let candidate_extra = session.infer.fresh_type_var();

    let payload_lower = session.infer.alloc_pos(Pos::Var(lower_payload));
    let payload_upper = session.infer.alloc_neg(Neg::Var(upper_payload));
    let payload = session
        .infer
        .alloc_neu(Neu::Bounds(payload_lower, payload_upper));
    let list_lower = session
        .infer
        .alloc_pos(Pos::Con(list_path.clone(), vec![payload]));
    let first_extra_lower = session.infer.alloc_pos(Pos::Var(first_extra));
    let second_extra_lower = session.infer.alloc_pos(Pos::Var(second_extra));
    let rest_lower = session
        .infer
        .alloc_pos(Pos::Union(second_extra_lower, list_lower));
    let lower = session
        .infer
        .alloc_pos(Pos::Union(first_extra_lower, rest_lower));
    let first_extra_upper = session.infer.alloc_neg(Neg::Var(first_extra));
    let second_extra_upper = session.infer.alloc_neg(Neg::Var(second_extra));
    let upper = session
        .infer
        .alloc_neg(Neg::Intersection(first_extra_upper, second_extra_upper));
    session.roles.insert(
        owner,
        RoleConstraint {
            role: role.clone(),
            inputs: vec![RoleConstraintArg { lower, upper }],
            associated: Vec::new(),
        },
    );
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role: role.clone(),
        inputs: vec![role_unary_con_var_and_extra_arg(
            &mut session.infer,
            list_path.clone(),
            candidate_item,
            candidate_extra,
        )],
        associated: Vec::new(),
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });

    let first_output_var = session.infer.alloc_pos(Pos::Var(first_extra));
    let first_output_list = session
        .infer
        .alloc_pos(Pos::Con(list_path.clone(), vec![payload]));
    let first_output = session
        .infer
        .alloc_pos(Pos::Union(first_output_var, first_output_list));
    let second_output_var = session.infer.alloc_pos(Pos::Var(second_extra));
    let second_output_list = session.infer.alloc_pos(Pos::Con(list_path, vec![payload]));
    let second_output = session
        .infer
        .alloc_pos(Pos::Union(second_output_var, second_output_list));
    let root_lower = session
        .infer
        .alloc_pos(Pos::Tuple(vec![first_output, second_output]));
    let root_upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(
        root_lower,
        root_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    let generalized = session.generalize_root_with_prepasses(owner, root);

    assert!(
        generalized
            .role_predicates
            .iter()
            .all(|predicate| predicate.role != role),
        "{:?}",
        generalized.role_predicates
    );
}

#[test]
fn role_prepass_resolves_receiver_first_concrete_with_negative_extra_inputs() {
    let role = vec!["Index".to_string()];
    let ref_lines_path = vec!["ref_lines".to_string()];
    let int_path = vec!["int".to_string()];
    let owner = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let previous_level = session.infer.enter_child_level();
    let root = session.infer.fresh_type_var();
    let receiver_extra = session.infer.fresh_type_var();
    let key_extra = session.infer.fresh_type_var();
    let receiver_payload = session.infer.fresh_type_var();
    let lower_payload = session.infer.fresh_type_var();
    let upper_payload = session.infer.fresh_type_var();
    let candidate_payload = session.infer.fresh_type_var();
    let associated_value = session.infer.fresh_type_var();

    let receiver_arg = role_unary_con_open_or_var_arg(
        &mut session.infer,
        ref_lines_path.clone(),
        receiver_payload,
        lower_payload,
        upper_payload,
        receiver_extra,
    );
    let int_lower = session
        .infer
        .alloc_pos(Pos::Con(int_path.clone(), Vec::new()));
    let key_extra_lower = session.infer.alloc_pos(Pos::Var(key_extra));
    let key_lower = session
        .infer
        .alloc_pos(Pos::Union(key_extra_lower, int_lower));
    let key_upper = session.infer.alloc_neg(Neg::Var(key_extra));
    session.roles.insert(
        owner,
        RoleConstraint {
            role: role.clone(),
            inputs: vec![
                receiver_arg,
                RoleConstraintArg {
                    lower: key_lower,
                    upper: key_upper,
                },
            ],
            associated: vec![RoleAssociatedConstraint {
                name: "value".into(),
                value: role_var_arg(&mut session.infer, associated_value),
            }],
        },
    );
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role: role.clone(),
        inputs: vec![
            role_unary_con_var_arg(
                &mut session.infer,
                ref_lines_path.clone(),
                candidate_payload,
            ),
            role_exact_arg(&mut session.infer, int_path.clone()),
        ],
        associated: vec![RoleAssociatedConstraint {
            name: "value".into(),
            value: role_var_arg(&mut session.infer, candidate_payload),
        }],
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });

    let receiver_payload_lower = session.infer.alloc_pos(Pos::Var(lower_payload));
    let receiver_payload_upper = session.infer.alloc_neg(Neg::Var(upper_payload));
    let receiver_payload = session
        .infer
        .alloc_neu(Neu::Bounds(receiver_payload_lower, receiver_payload_upper));
    let receiver_con = session
        .infer
        .alloc_neg(Neg::Con(ref_lines_path, vec![receiver_payload]));
    let receiver_extra_upper = session.infer.alloc_neg(Neg::Var(receiver_extra));
    let receiver_arg = session
        .infer
        .alloc_neg(Neg::Intersection(receiver_extra_upper, receiver_con));
    let key_con = session.infer.alloc_neg(Neg::Con(int_path, Vec::new()));
    let key_extra_upper = session.infer.alloc_neg(Neg::Var(key_extra));
    let key_arg = session
        .infer
        .alloc_neg(Neg::Intersection(key_extra_upper, key_con));
    let ret = session.infer.alloc_pos(Pos::Var(associated_value));
    let inner_arg_eff = session.infer.alloc_neg(Neg::Bot);
    let inner_ret_eff = session.infer.alloc_pos(Pos::Bot);
    let inner = session.infer.alloc_pos(Pos::Fun {
        arg: key_arg,
        arg_eff: inner_arg_eff,
        ret_eff: inner_ret_eff,
        ret,
    });
    let outer_arg_eff = session.infer.alloc_neg(Neg::Bot);
    let outer_ret_eff = session.infer.alloc_pos(Pos::Bot);
    let outer = session.infer.alloc_pos(Pos::Fun {
        arg: receiver_arg,
        arg_eff: outer_arg_eff,
        ret_eff: outer_ret_eff,
        ret: inner,
    });
    let root_upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(
        outer,
        root_upper,
        crate::constraints::OriginId::unknown_internal(),
    );
    session.infer.restore_level(previous_level);

    let compact = compact_type_var(session.infer.constraints(), root);
    let (role_compact, roles) = session
        .simplified_reachable_role_constraints(owner, &compact, TypeLevel::root().child())
        .expect("role constraints should be reachable");
    let resolutions = resolve_role_constraints(
        session.infer.constraints(),
        &role_compact,
        &roles,
        &session.role_impls,
        &FxHashSet::default(),
    );
    assert_eq!(
        resolutions.len(),
        1,
        "roles={roles:?} candidates={:?}",
        session.role_impls.candidates(&role)
    );

    let generalized = session.generalize_root_with_prepasses(owner, root);

    assert!(
        generalized
            .role_predicates
            .iter()
            .all(|predicate| predicate.role != role),
        "{:?}",
        generalized.role_predicates
    );
}

#[test]
fn role_prepass_does_not_resolve_left_concrete_when_main_var_is_negative() {
    let role = vec!["Add".to_string()];
    let int_path = vec!["int".to_string()];
    let owner = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let root = session.infer.fresh_type_var();
    let arg = session.infer.fresh_type_var();
    let output = session.infer.fresh_type_var();
    let int_arg = role_exact_arg(&mut session.infer, int_path.clone());
    session.roles.insert(
        owner,
        RoleConstraint {
            role: role.clone(),
            inputs: vec![
                role_exact_arg(&mut session.infer, int_path.clone()),
                role_left_concrete_var_arg(&mut session.infer, int_path.clone(), arg),
            ],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_var_arg(&mut session.infer, output),
            }],
        },
    );
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role,
        inputs: vec![int_arg.clone(), int_arg],
        associated: vec![RoleAssociatedConstraint {
            name: "out".into(),
            value: role_exact_arg(&mut session.infer, int_path.clone()),
        }],
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });

    let fun_arg = session.infer.alloc_neg(Neg::Var(arg));
    let fun_arg_eff = session.infer.alloc_neg(Neg::Bot);
    let fun_ret_eff = session.infer.alloc_pos(Pos::Bot);
    let fun_ret = session.infer.alloc_pos(Pos::Var(output));
    let fun = session.infer.alloc_pos(Pos::Fun {
        arg: fun_arg,
        arg_eff: fun_arg_eff,
        ret_eff: fun_ret_eff,
        ret: fun_ret,
    });
    let root_upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(
        fun,
        root_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    session.generalize_root_with_prepasses(owner, root);

    assert_var_lacks_exact_bound(&session, output, &int_path);
}

#[test]
fn role_prepass_selects_parent_and_enqueues_concrete_prerequisite() {
    let wrap_role = vec!["Wrap".to_string()];
    let ready_role = vec!["Ready".to_string()];
    let box_path = vec!["box".to_string()];
    let int_path = vec!["int".to_string()];
    let unit_path = vec!["unit".to_string()];
    let owner = DefId(0);
    let mut session = AnalysisSession::new(PolyArena::new());
    let root = session.infer.fresh_type_var();
    let output = session.infer.fresh_type_var();
    let item = session.infer.fresh_type_var();
    let ready_output = session.infer.fresh_type_var();

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
        inputs: vec![role_unary_con_var_arg(
            &mut session.infer,
            box_path.clone(),
            item,
        )],
        associated: vec![RoleAssociatedConstraint {
            name: "out".into(),
            value: role_var_arg(&mut session.infer, ready_output),
        }],
        prerequisites: vec![RoleConstraint {
            role: ready_role.clone(),
            inputs: vec![role_var_arg(&mut session.infer, item)],
            associated: vec![RoleAssociatedConstraint {
                name: "out".into(),
                value: role_var_arg(&mut session.infer, ready_output),
            }],
        }],
        methods: Vec::new(),
    });
    session.role_impls.insert(RoleImplCandidate {
        impl_def: None,
        role: ready_role.clone(),
        inputs: vec![role_exact_arg(&mut session.infer, int_path.clone())],
        associated: vec![RoleAssociatedConstraint {
            name: "out".into(),
            value: role_exact_arg(&mut session.infer, unit_path.clone()),
        }],
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });

    let root_lower = session.infer.alloc_pos(Pos::Var(output));
    let root_upper = session.infer.alloc_neg(Neg::Var(root));
    session.infer.subtype(
        root_lower,
        root_upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    let generalized = session.generalize_root_with_prepasses(owner, root);

    assert_var_has_exact_bound(&session, output, &unit_path);
    assert!(generalized.role_predicates.is_empty());
    assert_concrete_role_residual_missing(&session, owner, &ready_role, &int_path);
}
