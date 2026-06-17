use mono::Type;

use super::{
    ConstraintGraph, TypeResolver, TypeSlotKind, bool_type, join_type_candidates, list_type,
    meet_type_candidates, solve_expr, unary_type,
};

#[test]
fn root_generic_call_gets_types_for_apply_callee_and_arg() {
    let lowering = lower_source("my id x = x\nid(1)\n");
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let plan = solve_expr(arena, root, None).expect("root expression should solve");

    let poly::expr::Expr::App(callee, arg) = arena.expr(root) else {
        panic!("root should be an apply");
    };
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "int"
    );
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(*callee).unwrap()),
        "int -> int"
    );
    assert_eq!(plan.actual_type_of(*arg), Some(&int_type()));
}

#[test]
fn higher_order_direct_ref_argument_uses_outer_apply_type() {
    let lowering = lower_source("my id x = x\nmy apply f x = f(x)\napply(id)(1)\n");
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let plan = solve_expr(arena, root, None).expect("root expression should solve");

    let poly::expr::Expr::App(inner, arg) = arena.expr(root) else {
        panic!("root should be an apply");
    };
    let poly::expr::Expr::App(apply, id) = arena.expr(*inner) else {
        panic!("callee should be an apply");
    };
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "int"
    );
    assert_eq!(plan.actual_type_of(*arg), Some(&int_type()));
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(*inner).unwrap()),
        "int -> int"
    );
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(*apply).unwrap()),
        "(int -> int) -> int -> int"
    );
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(*id).unwrap()),
        "int -> int"
    );
}

#[test]
fn root_case_without_expected_type_errors_when_arm_results_do_not_join() {
    let lowering = lower_source("case true: true -> 1, false -> 2.0\n");
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let error = solve_expr(arena, root, None).expect_err("root case should be ambiguous");

    assert_conflicting_type_candidates(error, "int", "float");
}

#[test]
fn root_case_uses_direct_cast_as_join_candidate() {
    let lowering = lower_source("cast(x: int): float = 0.0\ncase true: true -> 1, false -> 2.0\n");
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let plan = solve_expr(arena, root, None).expect("root case should solve");

    let poly::expr::Expr::Case(_, arms) = arena.expr(root) else {
        panic!("root should be a case");
    };
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "float"
    );
    assert_eq!(plan.actual_type_of(arms[0].body), Some(&int_type()));
    assert_eq!(plan.actual_type_of(arms[1].body), Some(&float_type()));
    assert_eq!(
        mono::dump::dump_type(plan.boundary(arms[0].body).unwrap().expected),
        "float"
    );
    assert_eq!(
        mono::dump::dump_type(plan.boundary(arms[1].body).unwrap().expected),
        "float"
    );
}

#[test]
fn root_case_uses_variant_patterns_as_scrutinee_expectation() {
    let lowering = lower_source("case :disabled: :label text -> text, :disabled -> \"\"\n");
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let plan = solve_expr(arena, root, None).expect("variant case should solve");

    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "std::text::str::str"
    );
}

#[test]
fn root_role_associated_type_is_resolved_from_poly_impl_candidate() {
    let mut arena = poly::expr::Arena::new();
    let range = con_arg(&mut arena.typ, vec!["range".to_string()]);
    let int = con_arg(&mut arena.typ, vec!["int".to_string()]);
    arena.role_impls.insert(poly::roles::RoleImplCandidate {
        impl_def: None,
        role: vec!["Fold".to_string()],
        inputs: vec![range],
        associated: vec![poly::roles::RoleAssociatedConstraint {
            name: "item".to_string(),
            value: int,
        }],
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });

    let container = arena.fresh_type_var();
    let item = arena.fresh_type_var();
    let container_arg = var_arg(&mut arena.typ, container);
    let item_arg = var_arg(&mut arena.typ, item);
    let predicate_arg = arena.typ.alloc_neg(poly::types::Neg::Var(container));
    let predicate_arg_eff = arena.typ.alloc_neg(poly::types::Neg::Bot);
    let predicate_ret_eff = arena.typ.alloc_pos(poly::types::Pos::Bot);
    let predicate_ret = arena.typ.alloc_pos(poly::types::Pos::Var(item));
    let predicate = arena.typ.alloc_pos(poly::types::Pos::Fun {
        arg: predicate_arg,
        arg_eff: predicate_arg_eff,
        ret_eff: predicate_ret_eff,
        ret: predicate_ret,
    });
    let each_scheme = poly::types::Scheme {
        quantifiers: vec![container, item],
        role_predicates: vec![poly::types::RolePredicate {
            role: vec!["Fold".to_string()],
            inputs: vec![poly::types::RolePredicateArg::Invariant(
                arena.typ.alloc_neu(poly::types::Neu::Bounds(
                    container_arg.lower,
                    container_arg.upper,
                )),
            )],
            associated: vec![poly::types::RoleAssociatedType {
                name: "item".to_string(),
                value: arena
                    .typ
                    .alloc_neu(poly::types::Neu::Bounds(item_arg.lower, item_arg.upper)),
            }],
        }],
        recursive_bounds: Vec::new(),
        stack_quantifiers: Vec::new(),
        predicate,
    };
    let each_def = let_def(&mut arena, Some(each_scheme));
    let range_scheme = monomorphic_scheme(range);
    let range_def = let_def(&mut arena, Some(range_scheme));
    let each_expr = resolved_var_expr(&mut arena, each_def);
    let range_expr = resolved_var_expr(&mut arena, range_def);
    let root = arena.add_expr(poly::expr::Expr::App(each_expr, range_expr));

    let plan = solve_expr(&arena, root, None).expect("role associated type should solve");

    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "int"
    );
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(each_expr).unwrap()),
        "range -> int"
    );
}

#[test]
fn tuple_expression_constrains_open_expected_slot() {
    let lowering = lower_source("my id x = x\nid((1, 2))\n");
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let plan = solve_expr(arena, root, None).expect("tuple argument should solve");

    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "(int, int)"
    );
}

#[test]
fn pure_function_argument_effect_passes_to_apply_result() {
    let lowering = lower_source(
        "act out:\n  our read: unit -> int\n\
             my id x = x\n\
             id(out::read(()))\n",
    );
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let plan = solve_expr(arena, root, None).expect("pure function call should solve");

    let poly::expr::Expr::App(_, arg) = arena.expr(root) else {
        panic!("root should be an apply");
    };
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "thunk[[out], int]"
    );
    assert_eq!(
        mono::dump::dump_type(plan.boundary(*arg).unwrap().actual),
        "thunk[[out], int]"
    );
    assert_eq!(
        mono::dump::dump_type(plan.boundary(*arg).unwrap().expected),
        "int"
    );
}

#[test]
fn effect_row_subtyping_matches_items_by_path_before_tail_residual() {
    let arena = poly::expr::Arena::new();
    let mut graph = ConstraintGraph::new(&arena);
    let tail = graph.fresh_slot(TypeSlotKind::Effect);

    graph
        .constrain_subtype(
            Type::EffectRow(vec![effect_item("nondet")]),
            Type::EffectRow(vec![effect_item("junction"), tail.clone()]),
        )
        .expect("effect row subtype should solve");
    graph
        .solve_constraints()
        .expect("worklist should saturate effect row residual");

    let mut resolver = TypeResolver::new(&graph);
    assert_eq!(
        mono::dump::dump_type(&resolver.resolve(&tail).unwrap()),
        "[nondet]"
    );
}

#[test]
fn constraint_worklist_saturates_structural_constraints_before_resolution() {
    let arena = poly::expr::Arena::new();
    let mut graph = ConstraintGraph::new(&arena);
    let slot = graph.fresh_slot(TypeSlotKind::Value);

    graph
        .constrain_subtype(
            Type::Tuple(vec![int_type()]),
            Type::Tuple(vec![slot.clone()]),
        )
        .expect("tuple constraint should enqueue");
    graph
        .solve_constraints()
        .expect("worklist should saturate tuple children");

    let mut resolver = TypeResolver::new(&graph);
    assert_eq!(
        mono::dump::dump_type(&resolver.resolve(&slot).unwrap()),
        "int"
    );
}

#[test]
fn candidate_merge_refines_open_tuple_items_from_concrete_tuple() {
    let arena = poly::expr::Arena::new();
    let mut graph = ConstraintGraph::new(&arena);
    let left = Type::Tuple(vec![
        graph.fresh_slot(TypeSlotKind::Value),
        graph.fresh_slot(TypeSlotKind::Value),
    ]);
    let callback = unary_type(bool_type(), int_type());
    let right = Type::Tuple(vec![callback.clone(), list_type(callback)]);

    assert_eq!(
        mono::dump::dump_type(
            &join_type_candidates(&graph, 0, left.clone(), right.clone()).unwrap()
        ),
        "(bool -> int, std::data::list::list(bool -> int))"
    );
    assert_eq!(
        mono::dump::dump_type(&meet_type_candidates(&graph, 0, left, right).unwrap()),
        "(bool -> int, std::data::list::list(bool -> int))"
    );
}

#[test]
fn slot_solution_refines_open_tuple_lower_from_concrete_tuple_upper() {
    let arena = poly::expr::Arena::new();
    let mut graph = ConstraintGraph::new(&arena);
    let slot = graph.fresh_slot(TypeSlotKind::Value);
    let lower = Type::Tuple(vec![
        graph.fresh_slot(TypeSlotKind::Value),
        graph.fresh_slot(TypeSlotKind::Value),
    ]);
    let callback = unary_type(bool_type(), int_type());
    let upper = Type::Tuple(vec![callback.clone(), list_type(callback)]);

    graph.constrain_subtype(lower, slot.clone()).unwrap();
    graph.constrain_subtype(slot.clone(), upper).unwrap();
    graph.solve_constraints().unwrap();

    let mut resolver = TypeResolver::new(&graph);
    assert_eq!(
        mono::dump::dump_type(&resolver.resolve(&slot).unwrap()),
        "(bool -> int, std::data::list::list(bool -> int))"
    );
}

#[test]
fn recursive_slot_resolution_does_not_default_to_unit() {
    let arena = poly::expr::Arena::new();
    let mut graph = ConstraintGraph::new(&arena);
    let slot = graph.fresh_slot(TypeSlotKind::Value);

    graph
        .constrain_subtype(slot.clone(), Type::Tuple(vec![slot.clone()]))
        .expect("recursive constraint should enqueue");
    graph
        .solve_constraints()
        .expect("worklist should store recursive upper bound");

    let mut resolver = TypeResolver::new(&graph);
    assert!(matches!(
        resolver.resolve(&slot),
        Err(crate::SpecializeError::UndeterminedTypeSlot { .. })
    ));
}

#[test]
fn concrete_branch_resolution_prunes_unresolved_union_residue() {
    let arena = poly::expr::Arena::new();
    let mut graph = ConstraintGraph::new(&arena);
    let residue = graph.fresh_slot(TypeSlotKind::Value);
    let mut resolver = TypeResolver::new(&graph);

    let ty = resolver
        .resolve(&Type::Union(Box::new(residue), Box::new(int_type())))
        .expect("concrete union branch should resolve");

    assert_eq!(mono::dump::dump_type(&ty), "int");
}

#[test]
fn concrete_branch_resolution_prunes_unresolved_intersection_residue() {
    let arena = poly::expr::Arena::new();
    let mut graph = ConstraintGraph::new(&arena);
    let residue = graph.fresh_slot(TypeSlotKind::Value);
    let mut resolver = TypeResolver::new(&graph);

    let ty = resolver
        .resolve(&Type::Intersection(Box::new(residue), Box::new(int_type())))
        .expect("concrete intersection branch should resolve");

    assert_eq!(mono::dump::dump_type(&ty), "int");
}

#[test]
fn concrete_branch_resolution_absorbs_intersection_with_union_member() {
    let arena = poly::expr::Arena::new();
    let graph = ConstraintGraph::new(&arena);
    let local = Type::Con {
        path: vec!["local".into()],
        args: vec![int_type()],
    };
    let std_var = Type::Con {
        path: vec!["std".into(), "control".into(), "var".into(), "var".into()],
        args: vec![int_type()],
    };
    let union = Type::Union(Box::new(local.clone()), Box::new(std_var));
    let mut resolver = TypeResolver::new(&graph);

    let ty = resolver
        .resolve(&Type::EffectRow(vec![Type::Intersection(
            Box::new(union),
            Box::new(local.clone()),
        )]))
        .expect("intersection with a union member should resolve");

    assert_eq!(ty, Type::EffectRow(vec![local]));
}

#[test]
fn concrete_candidate_selection_ignores_recursive_non_concrete_bound() {
    let arena = poly::expr::Arena::new();
    let mut graph = ConstraintGraph::new(&arena);
    let slot = graph.fresh_slot(TypeSlotKind::Value);
    let weight = mono::StackWeight {
        entries: vec![mono::StackWeightEntry {
            id: 0,
            pops: 1,
            floor: Vec::new(),
            stack: Vec::new(),
        }],
    };

    graph
        .constrain_subtype(int_type(), slot.clone())
        .expect("lower concrete bound should enqueue");
    graph
        .constrain_subtype(
            slot.clone(),
            Type::Union(
                Box::new(Type::Stack {
                    inner: Box::new(slot.clone()),
                    weight,
                }),
                Box::new(int_type()),
            ),
        )
        .expect("recursive upper bound should enqueue");
    graph
        .solve_constraints()
        .expect("worklist should store candidate bounds");

    let mut resolver = TypeResolver::new(&graph);
    assert_eq!(
        mono::dump::dump_type(&resolver.resolve(&slot).unwrap()),
        "int"
    );
}

#[test]
fn effect_row_candidate_comparison_ignores_item_order() {
    let arena = poly::expr::Arena::new();
    let mut graph = ConstraintGraph::new(&arena);
    let slot = graph.fresh_slot(TypeSlotKind::Effect);
    let sub_int = Type::Con {
        path: vec!["sub".to_string()],
        args: vec![int_type()],
    };

    graph
        .constrain_subtype(
            Type::EffectRow(vec![effect_item("nondet"), sub_int.clone()]),
            slot.clone(),
        )
        .expect("lower effect row should constrain");
    graph
        .constrain_subtype(
            slot.clone(),
            Type::EffectRow(vec![sub_int, effect_item("nondet")]),
        )
        .expect("upper effect row should constrain");
    graph
        .solve_constraints()
        .expect("worklist should saturate effect row bounds");

    let mut resolver = TypeResolver::new(&graph);
    assert_eq!(
        mono::dump::dump_type(&resolver.resolve(&slot).unwrap()),
        "[nondet, sub(int)]"
    );
}

#[test]
fn case_scrutinee_effect_passes_to_case_result() {
    let lowering = lower_source(
        "act out:\n  our read: unit -> int\n\
             case out::read(()):\n\
             \x20 1 -> 2\n\
             \x20 _ -> 3\n",
    );
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let plan = solve_expr(arena, root, None).expect("effectful case should solve");

    let poly::expr::Expr::Case(scrutinee, _) = arena.expr(root) else {
        panic!("root should be a case");
    };
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "thunk[[out], int]"
    );
    assert_eq!(
        mono::dump::dump_type(plan.boundary(*scrutinee).unwrap().actual),
        "thunk[[out], int]"
    );
    assert_eq!(
        mono::dump::dump_type(plan.boundary(*scrutinee).unwrap().expected),
        "int"
    );
}

#[test]
fn root_case_errors_instead_of_using_transitive_casts_as_join_candidate() {
    let lowering = lower_source(
        "cast(x: int): bool = true\n\
             cast(x: bool): float = 0.0\n\
             case true: true -> 1, false -> 2.0\n",
    );
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let error = solve_expr(arena, root, None).expect_err("root case should be ambiguous");

    assert_conflicting_type_candidates(error, "int", "float");
}

#[test]
fn catch_effect_arm_uses_operation_type_for_payload_and_continuation() {
    let lowering = lower_source(
        "act out:\n  our say: int -> unit\n\
             catch out::say(1):\n\
             \x20 out::say msg, k -> k(())\n\
             \x20 value -> value\n",
    );
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let plan = solve_expr(arena, root, None).expect("handled effect should solve");

    let poly::expr::Expr::Catch(body, arms) = arena.expr(root) else {
        panic!("root should be a catch");
    };
    assert_eq!(
        arms[0].operation.as_ref().map(|operation| &operation.path),
        Some(&vec!["out".to_string(), "say".to_string()])
    );
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "unit"
    );
    assert_eq!(
        mono::dump::dump_type(plan.boundary(*body).unwrap().actual),
        "thunk[[out], unit]"
    );
    assert_eq!(
        mono::dump::dump_type(plan.boundary(*body).unwrap().expected),
        "unit"
    );

    let poly::expr::Expr::App(continuation, resume_value) = arena.expr(arms[0].body) else {
        panic!("effect arm body should resume the continuation");
    };
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(*continuation).unwrap()),
        "unit -> unit"
    );
    assert_eq!(plan.actual_type_of(*resume_value), Some(&unit_type()));
    assert_eq!(
        mono::dump::dump_type(plan.boundary(arms[0].body).unwrap().actual),
        "unit"
    );
    assert_eq!(
        mono::dump::dump_type(plan.boundary(arms[0].body).unwrap().expected),
        "unit"
    );
}

#[test]
fn catch_effect_arm_matches_generic_operation_effect_to_scrutinee_effect() {
    let lowering = lower_source(
        "act var 't:\n  our get: unit -> 't\n\
             catch var::get():\n\
             \x20 var::get(), k -> k(1)\n\
             \x20 value -> value\n",
    );
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let plan = solve_expr(arena, root, None).expect("generic handled effect should solve");

    let poly::expr::Expr::Catch(body, arms) = arena.expr(root) else {
        panic!("root should be a catch");
    };
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "int"
    );
    assert_eq!(
        mono::dump::dump_type(plan.boundary(*body).unwrap().actual),
        "thunk[[var(int)], int]"
    );
    let poly::expr::Expr::App(continuation, resume_value) = arena.expr(arms[0].body) else {
        panic!("effect arm body should resume the continuation");
    };
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(*continuation).unwrap()),
        "int -> int"
    );
    assert_eq!(plan.actual_type_of(*resume_value), Some(&int_type()));
}

#[test]
fn case_constructor_pattern_binds_payload_from_scrutinee_type() {
    let lowering = lower_source(
        "enum opt 'a:\n  none\n  some 'a\n\
             my id x = x\n\
             case opt::some 1:\n\
             \x20 opt::some x -> id(x)\n\
             \x20 _ -> 0\n",
    );
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let plan = solve_expr(arena, root, None).expect("constructor case should solve");

    let poly::expr::Expr::Case(_, arms) = arena.expr(root) else {
        panic!("root should be a case");
    };
    let poly::expr::Expr::App(_, payload_ref) = arena.expr(arms[0].body) else {
        panic!("first arm body should call id");
    };
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "int"
    );
    assert_eq!(plan.actual_type_of(*payload_ref), Some(&int_type()));
}

#[test]
fn case_record_pattern_binds_field_from_scrutinee_type() {
    let lowering = lower_source(
        "my id x = x\n\
             case { width: 1 }:\n\
             \x20 { width } -> id(width)\n\
             \x20 _ -> 0\n",
    );
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let plan = solve_expr(arena, root, None).expect("record case should solve");

    let poly::expr::Expr::Case(_, arms) = arena.expr(root) else {
        panic!("root should be a case");
    };
    let poly::expr::Expr::App(_, field_ref) = arena.expr(arms[0].body) else {
        panic!("first arm body should call id");
    };
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "int"
    );
    assert_eq!(plan.actual_type_of(*field_ref), Some(&int_type()));
}

#[test]
fn record_pattern_default_uses_provided_field_type_for_later_default() {
    let lowering = lower_source(
        "my box { width = 1, height = width } = height\n\
             box { width: 1.2 }\n",
    );
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let plan = solve_expr(arena, root, None).expect("record default call should solve");

    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "float"
    );
}

#[test]
fn record_select_reads_base_field_type() {
    let lowering = lower_source("my id x = x\nid(({ width: 1 }).width)\n");
    let arena = &lowering.session.poly;
    let root = arena.root_exprs[0];

    let plan = solve_expr(arena, root, None).expect("record select should solve");

    let poly::expr::Expr::App(_, select) = arena.expr(root) else {
        panic!("root should call id");
    };
    assert_eq!(
        mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
        "int"
    );
    assert_eq!(plan.actual_type_of(*select), Some(&int_type()));
}

fn assert_conflicting_type_candidates(error: crate::SpecializeError, left: &str, right: &str) {
    let crate::SpecializeError::ConflictingTypeCandidates {
        existing, incoming, ..
    } = error
    else {
        panic!("expected conflicting type candidates, got {error:?}");
    };
    assert_eq!(mono::dump::dump_type(&existing), left);
    assert_eq!(mono::dump::dump_type(&incoming), right);
}

fn int_type() -> Type {
    Type::Con {
        path: vec!["int".to_string()],
        args: Vec::new(),
    }
}

fn float_type() -> Type {
    Type::Con {
        path: vec!["float".to_string()],
        args: Vec::new(),
    }
}

fn unit_type() -> Type {
    Type::unit()
}

fn effect_item(name: &str) -> Type {
    Type::Con {
        path: vec![name.to_string()],
        args: Vec::new(),
    }
}

fn con_arg(
    types: &mut poly::types::TypeArena,
    path: Vec<String>,
) -> poly::roles::RoleConstraintArg {
    poly::roles::RoleConstraintArg {
        lower: types.alloc_pos(poly::types::Pos::Con(path.clone(), Vec::new())),
        upper: types.alloc_neg(poly::types::Neg::Con(path, Vec::new())),
    }
}

fn var_arg(
    types: &mut poly::types::TypeArena,
    var: poly::types::TypeVar,
) -> poly::roles::RoleConstraintArg {
    poly::roles::RoleConstraintArg {
        lower: types.alloc_pos(poly::types::Pos::Var(var)),
        upper: types.alloc_neg(poly::types::Neg::Var(var)),
    }
}

fn monomorphic_scheme(arg: poly::roles::RoleConstraintArg) -> poly::types::Scheme {
    poly::types::Scheme {
        quantifiers: Vec::new(),
        role_predicates: Vec::new(),
        recursive_bounds: Vec::new(),
        stack_quantifiers: Vec::new(),
        predicate: arg.lower,
    }
}

fn let_def(
    arena: &mut poly::expr::Arena,
    scheme: Option<poly::types::Scheme>,
) -> poly::expr::DefId {
    let def = arena.defs.fresh();
    arena.defs.set(
        def,
        poly::expr::Def::Let {
            vis: poly::expr::Vis::My,
            scheme,
            body: None,
            children: Vec::new(),
        },
    );
    def
}

fn resolved_var_expr(arena: &mut poly::expr::Arena, def: poly::expr::DefId) -> poly::expr::ExprId {
    let reference = arena.add_ref();
    arena.resolve_ref(reference, def);
    arena.add_expr(poly::expr::Expr::Var(reference))
}

fn lower_source(source: &str) -> infer::lowering::BodyLowering {
    let files = sources::load(vec![sources::SourceFile {
        module_path: sources::Path::default(),
        source: source.to_string(),
    }]);
    let output = infer::dump::dump_loaded_files(&files).expect("source should lower");
    assert!(
        output.lowering.errors.is_empty(),
        "body lowering errors: {:?}",
        output.lowering.errors
    );
    output.lowering
}
