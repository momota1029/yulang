use super::*;

#[test]
fn neg_signature_builder_preserves_effect_row_tail_for_data_representation() {
    let signature = build_neg_signature_field_type(
        "act ref_update 'a;\nstruct Box 'e 'a { update_effect: () -> [ref_update 'a; 'e] () }\n",
        "Box",
        "update_effect",
    );

    let SignatureType::Function {
        param,
        ret_eff: Some(row),
        ret,
        ..
    } = signature
    else {
        panic!("expected function signature with return effect row");
    };

    assert!(matches!(*param, SignatureType::Builtin(BuiltinType::Unit)));
    assert!(matches!(*ret, SignatureType::Builtin(BuiltinType::Unit)));
    assert_eq!(row.tail, Some(SignatureVar { name: "e".into() }));
    let [SignatureEffectAtom::Type(effect)] = row.items.as_slice() else {
        panic!("expected one concrete effect atom");
    };
    let SignatureType::Apply { callee, args } = effect else {
        panic!("expected parameterized effect atom");
    };
    assert!(matches!(callee.as_ref(), SignatureType::Named(_)));
    assert_eq!(
        args,
        &vec![SignatureType::Var(SignatureVar { name: "a".into() })]
    );
}

#[test]
fn struct_constructor_field_signature_records_data_tail_stack() {
    let root = parse(
        "act ref_update 'a;\nstruct Box 'e 'a { update_effect: () -> [ref_update 'a; 'e] () }\n",
    );
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let constructor = lower.modules.value_decls(module, &Name("Box".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let update_effect = constructor_record_field_var(&output, constructor, "update_effect");
    let (items, tail) = function_upper_bound_ret_effect_row(&output.session, update_effect);
    assert!(items.iter().any(|item| {
        matches!(
            output.session.infer.constraints().types().neg(*item),
            Neg::Con(path, args) if path == &vec!["ref_update".to_string()] && args.len() == 1
        )
    }));
    let types = output.session.infer.constraints().types();
    let Neg::Stack { inner, weight } = types.neg(tail) else {
        panic!(
            "expected stacked return effect row tail, got {:?}",
            types.neg(tail)
        );
    };
    assert!(matches!(types.neg(*inner), Neg::Var(_)));
    assert!(weight_has_all_except_path(weight, &["ref_update"]));
}

pub(super) fn assert_method_body_is_receiver_identity(output: &BodyLowering, method: DefId) {
    let body = binding_body_id(output, method);
    let (pat, body) = match output.session.poly.expr(body) {
        Expr::Lambda(pat, body) => (*pat, *body),
        _ => panic!("expected method receiver lambda"),
    };
    let receiver = match output.session.poly.pat(pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected receiver var pattern"),
    };
    let reference = expr_ref(&output.session, body);

    assert_eq!(output.session.poly.ref_target(reference), Some(receiver));
}

pub(super) fn assert_act_method_receiver_has_self_subtract(
    output: &BodyLowering,
    method: DefId,
    effect_name: &str,
) {
    let root = output
        .typing
        .def(method)
        .expect("method def should have a root type");
    let (_, arg_eff, ret_eff, ret) = function_lower_bound(&output.session, root);
    let effect = match output.session.infer.constraints().types().neg(arg_eff) {
        Neg::Var(effect) => *effect,
        other => panic!("expected receiver arg effect var, got {other:?}"),
    };
    // act receiver の保護は fresh な内側変数の push 付き下界として入る。self edge にはしない。
    let bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(effect)
        .expect("receiver effect should receive stacked inner lower bound");
    let subtract = bounds
        .lowers()
        .iter()
        .find_map(|bound| {
            if !matches!(
                output.session.infer.constraints().types().pos(bound.pos),
                Pos::Var(var) if *var != effect
            ) {
                return None;
            }
            weight_set_path_id(&bound.weights.left, &[effect_name])
        })
        .expect("receiver effect should record stacked act family");
    assert_pos_or_var_lower_stack_pop_var(&output.session, ret_eff, subtract);
    assert_pos_or_var_lower_stack_pop_var(&output.session, ret, subtract);
}

pub(super) fn function_lower_bound(
    session: &AnalysisSession,
    var: TypeVar,
) -> (NegId, NegId, PosId, PosId) {
    let mut stack = vec![var];
    let mut visited = Vec::new();
    while let Some(var) = stack.pop() {
        if visited.contains(&var) {
            continue;
        }
        visited.push(var);
        let Some(bounds) = session.infer.constraints().bounds().of(var) else {
            continue;
        };
        for lower in bounds.lowers() {
            match session.infer.constraints().types().pos(lower.pos) {
                Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                } => return (*arg, *arg_eff, *ret_eff, *ret),
                Pos::Var(next) => stack.push(*next),
                _ => {}
            }
        }
    }
    panic!("expected function lower bound");
}

fn constructor_record_field_var(
    output: &BodyLowering,
    constructor: DefId,
    field_name: &str,
) -> TypeVar {
    let root = output
        .typing
        .def(constructor)
        .expect("constructor def should have a root type");
    let (arg, _, _, _) = function_lower_bound(&output.session, root);
    let Neg::Var(record) = output.session.infer.constraints().types().neg(arg) else {
        panic!("expected constructor record argument var");
    };
    let Some(bounds) = output.session.infer.constraints().bounds().of(*record) else {
        panic!("expected record argument bounds");
    };
    for upper in bounds.uppers() {
        let Neg::Record(fields) = output.session.infer.constraints().types().neg(upper.neg) else {
            continue;
        };
        let Some(field) = fields.iter().find(|field| field.name == field_name) else {
            continue;
        };
        let Neg::Var(value) = output.session.infer.constraints().types().neg(field.value) else {
            panic!("expected constructor field value var");
        };
        return *value;
    }
    panic!("expected constructor record field {field_name}");
}

fn function_upper_bound_ret_effect_row(
    session: &AnalysisSession,
    var: TypeVar,
) -> (Vec<NegId>, NegId) {
    let Some(bounds) = session.infer.constraints().bounds().of(var) else {
        panic!("expected function upper bound");
    };
    for upper in bounds.uppers() {
        let Neg::Fun { ret_eff, .. } = session.infer.constraints().types().neg(upper.neg) else {
            continue;
        };
        let Neg::Row(items, tail) = session.infer.constraints().types().neg(*ret_eff) else {
            panic!("expected function return effect row");
        };
        return (items.clone(), *tail);
    }
    panic!("expected function upper bound");
}

pub(super) fn type_field_method(
    modules: &ModuleTable,
    owner: TypeDeclId,
    name: &str,
    receiver_kind: TypeMethodReceiver,
) -> TypeFieldMethodDecl {
    modules
        .type_field_methods(owner)
        .iter()
        .find(|method| method.name.0 == name && method.receiver_kind == receiver_kind)
        .cloned()
        .expect("type field method should be registered")
}

pub(super) fn assert_pos_stack_pop_var(
    session: &AnalysisSession,
    pos: PosId,
    subtract: SubtractId,
) -> TypeVar {
    match session.infer.constraints().types().pos(pos) {
        Pos::Stack { inner, weight } => {
            let [entry] = weight.entries() else {
                panic!("expected one stack entry, got {:?}", weight.entries());
            };
            assert_eq!(entry.id, subtract);
            assert_eq!(entry.pops, 1);
            assert!(entry.stack.is_empty());
            match session.infer.constraints().types().pos(*inner) {
                Pos::Var(var) => *var,
                other => panic!("expected stack pop inner var, got {other:?}"),
            }
        }
        Pos::NonSubtract(inner, actual) => {
            assert!(actual.contains(subtract), "non-subtract weight: {actual:?}");
            match session.infer.constraints().types().pos(*inner) {
                Pos::Var(var) => *var,
                other => panic!("expected non-subtract inner var, got {other:?}"),
            }
        }
        other => panic!("expected stack pop #{:?}, got {other:?}", subtract),
    }
}

pub(super) fn assert_pos_or_var_lower_stack_pop_var(
    session: &AnalysisSession,
    pos: PosId,
    subtract: SubtractId,
) -> TypeVar {
    if matches!(
        session.infer.constraints().types().pos(pos),
        Pos::Stack { .. }
    ) {
        return assert_pos_stack_pop_var(session, pos, subtract);
    }
    if matches!(
        session.infer.constraints().types().pos(pos),
        Pos::NonSubtract(_, _)
    ) {
        return assert_pos_stack_pop_var(session, pos, subtract);
    }
    let Pos::Var(var) = session.infer.constraints().types().pos(pos) else {
        panic!("expected stack pop or var with stack pop lower bound");
    };
    let mut stack = vec![*var];
    let mut visited = Vec::new();
    while let Some(var) = stack.pop() {
        if visited.contains(&var) {
            continue;
        }
        visited.push(var);
        let Some(bounds) = session.infer.constraints().bounds().of(var) else {
            continue;
        };
        for lower in bounds.lowers() {
            match session.infer.constraints().types().pos(lower.pos) {
                Pos::Stack { .. } => {
                    return assert_pos_stack_pop_var(session, lower.pos, subtract);
                }
                Pos::NonSubtract(_, _) => {
                    return assert_pos_stack_pop_var(session, lower.pos, subtract);
                }
                Pos::Var(next) if stack_weight_has_single_pop(&lower.weights.left, subtract) => {
                    return *next;
                }
                Pos::Var(next) => stack.push(*next),
                _ => {}
            }
        }
    }
    panic!("expected var lower stack pop #{:?}", subtract);
}

fn stack_weight_has_single_pop(weight: &StackWeight, subtract: SubtractId) -> bool {
    let [entry] = weight.entries() else {
        return false;
    };
    entry.id == subtract && entry.pops == 1 && entry.stack.is_empty()
}

pub(super) fn weight_set_path_id(weight: &StackWeight, expected: &[&str]) -> Option<SubtractId> {
    weight.entries().iter().find_map(|entry| {
        if entry.stack.iter().any(|subtractability| {
            matches!(
                subtractability,
                Subtractability::Set(path, args)
                    if path_matches(path, expected) && args.is_empty()
            )
        }) {
            Some(entry.id)
        } else {
            None
        }
    })
}

fn weight_filter_matches_path(weight: &StackWeight, expected: &[&str]) -> bool {
    matches!(
        weight.filter_set(),
        Subtractability::Set(path, args) if path_matches(path, expected) && args.is_empty()
    )
}

fn neg_is_var_or_filter_stack_var(types: &poly::types::TypeArena, neg: poly::types::NegId) -> bool {
    match types.neg(neg) {
        Neg::Var(_) => true,
        Neg::Stack { inner, weight } if weight.entries().is_empty() => {
            matches!(types.neg(*inner), Neg::Var(_))
        }
        _ => false,
    }
}

fn weight_has_all_except_path(weight: &StackWeight, expected: &[&str]) -> bool {
    weight.entries().iter().any(|entry| {
        entry.stack.iter().any(|subtractability| {
            matches!(
                subtractability,
                Subtractability::AllExcept(path, args)
                    if path_matches(path, expected) && args.is_empty()
            )
        })
    })
}

pub(super) fn weight_has_empty_stack(weight: &StackWeight, subtract: SubtractId) -> bool {
    weight.entries().iter().any(|entry| {
        entry.id == subtract
            && entry.pops == 0
            && entry
                .stack
                .iter()
                .any(|subtractability| matches!(subtractability, Subtractability::Empty))
    })
}

fn path_matches(path: &[String], expected: &[&str]) -> bool {
    path.iter().map(String::as_str).eq(expected.iter().copied())
}

pub(super) fn role_arg_vars(types: &TypeArena, arg: &RoleConstraintArg) -> FxHashSet<TypeVar> {
    let mut vars = FxHashSet::default();
    collect_pos_id_vars(types, arg.lower, &mut vars);
    collect_neg_id_vars(types, arg.upper, &mut vars);
    vars
}

#[test]
fn struct_constructor_lowers_to_scheme() {
    let root = parse("struct Box 'a { value: 'a }\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let constructor = lower.modules.value_decls(module, &Name("Box".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let scheme = def_scheme(&output, constructor);
    assert_eq!(scheme.quantifiers.len(), 1);
    let Pos::Fun { ret, .. } = output.session.poly.typ.pos(scheme.predicate) else {
        panic!("expected unary constructor function");
    };
    let Pos::Con(path, args) = output.session.poly.typ.pos(*ret) else {
        panic!("expected constructor return type");
    };
    assert_eq!(path, &vec!["Box".to_string()]);
    assert_eq!(args.len(), 1);
}

#[test]
fn type_with_self_struct_lowers_outer_constructor_scheme() {
    let root = parse("type t 'a with:\n  struct self:\n    field: 'a\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let constructor = lower.modules.value_decls(module, &Name("t".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let scheme = def_scheme(&output, constructor);
    assert_eq!(scheme.quantifiers.len(), 1);
    let Pos::Fun { ret, .. } = output.session.poly.typ.pos(scheme.predicate) else {
        panic!("expected self struct constructor function");
    };
    let Pos::Con(path, args) = output.session.poly.typ.pos(*ret) else {
        panic!("expected outer type constructor return");
    };
    assert_eq!(path, &vec!["t".to_string()]);
    assert_eq!(args.len(), 1);
}

#[test]
fn enum_variant_constructor_lowers_to_scheme() {
    let root = parse("enum opt 'a = none | some 'a\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let opt = lower.modules.type_decls(module, &Name("opt".into()))[0].id;
    let companion = lower.modules.type_companion(opt).expect("opt companion");
    let none = lower.modules.value_decls(companion, &Name("none".into()))[0].def;
    let some = lower.modules.value_decls(companion, &Name("some".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let none_scheme = def_scheme(&output, none);
    let Pos::Con(path, args) = output.session.poly.typ.pos(none_scheme.predicate) else {
        panic!("expected nullary enum constructor value");
    };
    assert_eq!(path, &vec!["opt".to_string()]);
    assert_eq!(args.len(), 1);

    let some_scheme = def_scheme(&output, some);
    let Pos::Fun { ret, .. } = output.session.poly.typ.pos(some_scheme.predicate) else {
        panic!("expected unary enum constructor function");
    };
    let Pos::Con(path, args) = output.session.poly.typ.pos(*ret) else {
        panic!("expected enum constructor return type");
    };
    assert_eq!(path, &vec!["opt".to_string()]);
    assert_eq!(args.len(), 1);
}

#[test]
fn enum_constructor_expression_resolves_reference() {
    let root = parse("enum opt 'a = some 'a\nmy x = opt::some 1\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let opt = lower.modules.type_decls(module, &Name("opt".into()))[0].id;
    let companion = lower.modules.type_companion(opt).expect("opt companion");
    let constructor = lower.modules.value_decls(companion, &Name("some".into()))[0].def;
    let (x, _) = binding_def_and_order(&lower.modules, module, "x");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, x);
    let Expr::App(callee, _) = output.session.poly.expr(body) else {
        panic!("expected constructor application");
    };
    let reference = expr_ref(&output.session, *callee);
    assert_eq!(output.session.poly.ref_target(reference), Some(constructor));
}

#[test]
fn declared_constructor_expression_spaced_tuple_group_matches_payload_fields() {
    let root = parse(concat!(
        "pub enum bound = unbounded | included int\n",
        "pub enum range = within (bound, bound)\n",
        "my mk(start: bound, end: bound): range = range::within (start, end)\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (mk, _) = binding_def_and_order(&lower.modules, module, "mk");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, mk));
    assert_eq!(rendered, "bound -> bound -> range");
}

#[test]
fn lowers_int_literal_with_primitive_lower_bound() {
    let root = parse("my a = 1\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "a");
    let expr = binding_expr(&root, "a");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    assert!(matches!(
        session.poly.expr(computation.expr),
        Expr::Lit(Lit::Int(1))
    ));
    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(computation.value)
        .expect("literal value should receive a lower bound");
    assert!(bounds.lowers().iter().any(|bound| {
        matches!(
            session.infer.constraints().types().pos(bound.pos),
            Pos::Con(path, args) if path == &vec!["int".to_string()] && args.is_empty()
        )
    }));
}

#[test]
fn binding_annotation_constrains_def_above_body() {
    let root = parse("my a: float = 1\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (def, _) = binding_def_and_order(&lower.modules, module, "a");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let root = output.typing.def(def).expect("def should have a root type");
    assert!(matches!(
        output.session.poly.expr(binding_body_id(&output, def)),
        Expr::Lit(Lit::Int(_))
    ));
    let body = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(root)
        .expect("root should receive bounds")
        .lowers()
        .iter()
        .find_map(
            |bound| match output.session.infer.constraints().types().pos(bound.pos) {
                Pos::Var(body) => Some(*body),
                _ => None,
            },
        )
        .expect("body should flow into def root");

    let types = output.session.infer.constraints().types();
    let root_bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(root)
        .expect("root should receive bounds");
    assert!(root_bounds.uppers().iter().any(|bound| {
        matches!(
            types.neg(bound.neg),
            Neg::Con(path, args) if path == &vec!["float".to_string()] && args.is_empty()
        )
    }));

    let body_bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(body)
        .expect("body should receive bounds");
    assert!(
        body_bounds
            .uppers()
            .iter()
            .any(|bound| { matches!(types.neg(bound.neg), Neg::Var(var) if *var == root) })
    );
}

#[test]
fn binding_header_arg_lowers_to_lambda_and_local_ref() {
    let root = parse("my id x = x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (def, _) = binding_def_and_order(&lower.modules, module, "id");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, def);
    let (pat, lambda_body) = match output.session.poly.expr(body) {
        Expr::Lambda(pat, body) => (*pat, *body),
        _ => panic!("expected header arg lambda"),
    };
    let arg = match output.session.poly.pat(pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected arg var pattern"),
    };
    let reference = expr_ref(&output.session, lambda_body);
    assert_eq!(output.session.poly.ref_target(reference), Some(arg));
}

#[test]
fn binding_header_arg_annotation_constrains_arg_not_def() {
    let root = parse("my f(x: int) = x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (def, _) = binding_def_and_order(&lower.modules, module, "f");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, def);
    let lambda_body = match output.session.poly.expr(body) {
        Expr::Lambda(_, body) => *body,
        _ => panic!("expected header arg lambda"),
    };
    let reference = expr_ref(&output.session, lambda_body);
    let arg_value = output
        .session
        .refs
        .value(reference)
        .expect("arg ref should have a value slot");
    let types = output.session.infer.constraints().types();
    let arg_bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(arg_value)
        .expect("arg annotation should constrain arg value");
    assert!(arg_bounds.lowers().iter().any(|bound| {
        matches!(
            types.pos(bound.pos),
            Pos::Con(path, args) if path == &vec!["int".to_string()] && args.is_empty()
        )
    }));

    let root = output.typing.def(def).expect("def should have a root type");
    let root_bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(root)
        .expect("def root should receive bounds");
    assert!(!root_bounds.uppers().iter().any(|bound| {
        matches!(
            types.neg(bound.neg),
            Neg::Con(path, args) if path == &vec!["int".to_string()] && args.is_empty()
        )
    }));
}

#[test]
fn binding_header_result_annotation_constrains_body_not_def() {
    let root = parse("my f(x: int): float = 1\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (def, _) = binding_def_and_order(&lower.modules, module, "f");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let root = output.typing.def(def).expect("def should have a root type");
    let (_, _, _, ret) = function_lower_bound(&output.session, root);
    let ret_value = match output.session.infer.constraints().types().pos(ret) {
        Pos::Var(var) => *var,
        _ => panic!("expected function return value var"),
    };
    let types = output.session.infer.constraints().types();
    let ret_bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(ret_value)
        .expect("result annotation should constrain body value");
    assert!(ret_bounds.uppers().iter().any(|bound| {
        matches!(
            types.neg(bound.neg),
            Neg::Con(path, args) if path == &vec!["float".to_string()] && args.is_empty()
        )
    }));

    let root_bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(root)
        .expect("def root should receive bounds");
    assert!(!root_bounds.uppers().iter().any(|bound| {
        matches!(
            types.neg(bound.neg),
            Neg::Con(path, args) if path == &vec!["float".to_string()] && args.is_empty()
        )
    }));
}

#[test]
fn role_impl_head_and_colon_description_register_same_candidate_shape() {
    let root = parse("role Eq 'a;\nimpl Eq int;\nimpl int: Eq;\n");
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let candidates = output.session.role_impls.candidates(&["Eq".to_string()]);
    assert_eq!(candidates.len(), 2);
    for candidate in candidates {
        assert_eq!(candidate.inputs.len(), 1);
        assert_role_arg_is_exact_con(&output.session, &candidate.inputs[0], "int");
    }
}

#[test]
fn role_impl_prefix_and_colon_description_register_same_multi_input_shape() {
    for impl_head in ["impl Index lines int:", "impl lines: Index int:"] {
        let root = parse(&format!(
            concat!(
                "struct lines;\n",
                "role Index 'container 'key:\n",
                "  type value\n",
                "  our x.index: 'key -> value\n",
                "{impl_head}\n",
                "  type value = lines\n",
                "  our x.index i = x\n",
            ),
            impl_head = impl_head,
        ));
        let lower = lower_module_map(&root);

        let output = lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let candidates = output.session.role_impls.candidates(&["Index".to_string()]);
        assert_eq!(candidates.len(), 1, "{impl_head}");
        let candidate = &candidates[0];
        assert_eq!(candidate.inputs.len(), 2);
        assert_role_arg_is_exact_con(&output.session, &candidate.inputs[0], "lines");
        assert_role_arg_is_exact_con(&output.session, &candidate.inputs[1], "int");
    }
}

#[test]
fn role_impl_method_receiver_is_constrained_to_impl_target() {
    let root = parse(
        "struct User;\nrole Box 'a:\n  our x.get: 'a\nimpl User: Box {\n  our x.get = x\n}\n",
    );
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let method = lower.modules.role_impls(module)[0].methods[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, method);
    let lambda_body = match output.session.poly.expr(body) {
        Expr::Lambda(_, body) => *body,
        _ => panic!("expected impl method receiver lambda"),
    };
    let reference = expr_ref(&output.session, lambda_body);
    let receiver_value = output
        .session
        .refs
        .value(reference)
        .expect("receiver ref should have a value slot");
    assert_var_has_exact_con_bound(&output.session, receiver_value, "User");
}

#[test]
fn role_impl_method_requirement_rejects_concrete_return_mismatch() {
    let root = parse(
        "struct User;\nrole Box 'a:\n  our x.get: int\nimpl User: Box {\n  our x.get = x\n}\n",
    );
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.iter().any(|error| {
        matches!(
            error,
            BodyLoweringError::Expr {
                error: LoweringError::SignatureTypeMismatch {
                    expected: SignatureShape::Function,
                },
                ..
            }
        )
    }));
}

#[test]
fn role_impl_method_requirement_clamps_associated_type_from_return() {
    let root = parse(
        "struct User;\nrole Box 'a:\n  type item\n  our x.get: item\nimpl User: Box {\n  our x.get = x\n}\n",
    );
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let candidates = output.session.role_impls.candidates(&["Box".to_string()]);
    assert_eq!(candidates.len(), 1);
    assert_eq!(candidates[0].associated.len(), 1);
    assert_eq!(candidates[0].associated[0].name, "item");
    let poly_candidates = output
        .session
        .poly
        .role_impls
        .candidates(&["Box".to_string()]);
    assert_eq!(poly_candidates.len(), 1);
    assert_eq!(poly_candidates[0].associated.len(), 1);
    assert_eq!(poly_candidates[0].associated[0].name, "item");
    output
        .session
        .poly
        .typ
        .pos(poly_candidates[0].associated[0].value.lower);
    let associated = candidates[0].associated[0].value;
    let associated_var = match output
        .session
        .infer
        .constraints()
        .types()
        .pos(associated.lower)
    {
        Pos::Var(var) => *var,
        other => panic!("expected associated lower var, got {other:?}"),
    };
    assert_var_has_lower_con_bound(&output.session, associated_var, "User");
}

#[test]
fn role_impl_method_requirement_ret_effect_records_stack_weighted_upper() {
    let root = parse(
        "act nondet:\nstruct User;\nrole Box 'a:\n  our x.run: [nondet; 'e] unit\nimpl User: Box {\n  our x.run = ()\n}\n",
    );
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let method = lower.modules.role_impls(module)[0].methods[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let root = output.typing.def(method).expect("impl method root");
    let (_, _, ret_eff, _) = function_lower_bound(&output.session, root);
    let body_effect = match output.session.infer.constraints().types().pos(ret_eff) {
        Pos::Var(var) => *var,
        other => panic!("expected body effect var, got {other:?}"),
    };
    let bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(body_effect)
        .expect("body effect should be constrained by requirement");
    let types = output.session.infer.constraints().types();
    assert!(
        bounds.uppers().iter().any(|bound| {
            neg_is_var_or_filter_stack_var(types, bound.neg)
                && weight_filter_matches_path(&bound.weights.right, &["nondet"])
        }),
        "body effect bounds: {:?}",
        bounds
    );
}

#[test]
fn role_method_signature_arg_effect_adds_row_lower_to_fresh_arg_effect() {
    let root = parse("act nondet:\nrole Box 'a:\n  our x.run: unit [nondet; 'e] -> unit\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let role = lower.modules.type_decls(module, &Name("Box".into()))[0].clone();
    let method = lower.modules.role_methods(role.id)[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let root = output.typing.def(method).expect("role method root");
    let (_, _, _, ret) = function_lower_bound(&output.session, root);
    let arg_eff = match output.session.infer.constraints().types().pos(ret) {
        Pos::Fun { arg_eff, .. } => *arg_eff,
        other => panic!("expected inner function lower bound, got {other:?}"),
    };
    let types = output.session.infer.constraints().types();
    let Neg::Var(effect) = types.neg(arg_eff) else {
        panic!("expected arg effect var, got {:?}", types.neg(arg_eff));
    };
    let bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(*effect)
        .expect("arg effect should receive row lower bound");
    assert!(
        bounds.lowers().iter().any(|bound| {
            matches!(
                types.pos(bound.pos),
                Pos::Row(items)
                    if items
                        .iter()
                        .any(|item| matches!(types.pos(*item), Pos::Con(path, _) if path.as_slice() == ["nondet"]))
            )
        }),
        "arg effect bounds: {:?}",
        bounds
    );
}
