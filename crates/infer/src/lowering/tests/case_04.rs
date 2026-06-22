use super::*;

#[test]
fn type_method_header_arg_lowers_after_receiver() {
    let root = parse("type User with:\n  our x.pick y = y\nmy site = 1\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let user = lower.modules.type_decls(module, &Name("User".into()))[0].clone();
    let method = lower.modules.type_methods(user.id)[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, method);
    let arg_lambda = match output.session.poly.expr(body) {
        Expr::Lambda(_, arg_lambda) => *arg_lambda,
        _ => panic!("expected method receiver lambda"),
    };
    let (arg_pat, arg_body) = match output.session.poly.expr(arg_lambda) {
        Expr::Lambda(arg_pat, arg_body) => (*arg_pat, *arg_body),
        _ => panic!("expected method header arg lambda"),
    };
    let arg = match output.session.poly.pat(arg_pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected arg var pattern"),
    };
    let reference = expr_ref(&output.session, arg_body);
    assert_eq!(output.session.poly.ref_target(reference), Some(arg));
}

#[test]
fn std_ref_update_method_body_lowers() {
    let root = parse(concat!(
        "mod std:\n",
        "  mod control:\n",
        "    mod var:\n",
        "      act ref_update 'a:\n",
        "        pub update: 'a -> 'a\n",
        "      type ref 'e 'a with:\n",
        "        struct self:\n",
        "          get: () -> ['e] 'a\n",
        "          update_effect: () -> [ref_update 'a; 'e] ()\n",
        "        pub r.update f =\n",
        "          my loop(x: [_] _) = catch x:\n",
        "            ref_update::update v, k -> loop:k:f v\n",
        "          loop:r.update_effect()\n",
        "my site = 1\n",
    ));
    let lower = lower_module_map(&root);
    let root_module = lower.modules.root_id();
    let std = lower.modules.module_decls(root_module, &Name("std".into()))[0].module;
    let control = lower.modules.module_decls(std, &Name("control".into()))[0].module;
    let var = lower.modules.module_decls(control, &Name("var".into()))[0].module;
    let ref_type = lower.modules.type_decls(var, &Name("ref".into()))[0].clone();
    let field_method = type_field_method(
        &lower.modules,
        ref_type.id,
        "update_effect",
        TypeMethodReceiver::Value,
    )
    .def;
    let method = lower.modules.type_methods(ref_type.id)[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, method);
    let scheme = def_scheme(&output, method);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, scheme);
    assert_eq!(
        rendered,
        "std::control::var::ref('a & 'c, 'b) -> ('b -> ['c] 'b) -> ['c, 'a] ()"
    );
    let update_effect =
        find_select_by_name(&output.session, body, "update_effect").expect("update_effect");
    assert_eq!(
        output.session.poly.select(update_effect).resolution,
        Some(SelectResolution::Method { def: field_method })
    );
}

#[test]
fn std_ref_update_full_signature_hides_private_stack_evidence() {
    let root = parse(concat!(
        "mod std:\n",
        "  mod control:\n",
        "    mod var:\n",
        "      act ref_update 'a:\n",
        "        pub update: 'a -> 'a\n",
        "      type ref 'e 'a with:\n",
        "        struct self:\n",
        "          get: () -> ['e] 'a\n",
        "          update_effect: () -> [ref_update 'a; 'e] ()\n",
        "        pub r.update(f: 'a -> 'a): ['e] () =\n",
        "          my loop(x: [_] _) = catch x:\n",
        "            ref_update::update v, k -> loop:k:f v\n",
        "          loop:r.update_effect()\n",
        "my site = 1\n",
    ));
    let lower = lower_module_map(&root);
    let root_module = lower.modules.root_id();
    let std = lower.modules.module_decls(root_module, &Name("std".into()))[0].module;
    let control = lower.modules.module_decls(std, &Name("control".into()))[0].module;
    let var = lower.modules.module_decls(control, &Name("var".into()))[0].module;
    let ref_type = lower.modules.type_decls(var, &Name("ref".into()))[0].clone();
    let method = lower.modules.type_methods(ref_type.id)[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, method));
    assert_eq!(
        rendered,
        "std::control::var::ref('a & 'c, 'b) -> ('b -> ['c] 'b) -> ['c, 'a] ()"
    );
    assert!(
        !rendered.contains('#') && !rendered.contains("AllExcept"),
        "private stack evidence escaped into ref.update: {rendered}"
    );
}

#[test]
fn annotated_recursive_handler_does_not_subtract_outer_effect() {
    let root = parse(concat!(
        "act tick:\n",
        "  pub out: () -> ()\n",
        "act flip:\n",
        "  pub coin: () -> bool\n",
        "pub pick(action: [flip] _) = catch action:\n",
        "  flip::coin(), k -> pick(k true)\n",
        "  v -> v\n",
        "pub loop(x: [tick] _) = catch x:\n",
        "  tick::out(), k -> pick(loop(k ()))\n",
        "  v -> v\n",
        "my site = 1\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let loop_def = lower.modules.value_decls(module, &Name("loop".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, loop_def));
    assert!(
        !rendered.contains("flip"),
        "loop annotation allowed flip to be subtracted: {rendered}"
    );
}

#[test]
fn annotated_recursive_handler_pick_only_terminates() {
    let root = parse(concat!(
        "act flip:\n",
        "  pub coin: () -> bool\n",
        "pub pick(action: [flip] _) = catch action:\n",
        "  flip::coin(), k -> pick(k true)\n",
        "  v -> v\n",
        "my site = 1\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let pick_def = lower.modules.value_decls(module, &Name("pick".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, pick_def));
    assert!(
        rendered.contains("flip"),
        "pick annotation should mention flip: {rendered}"
    );
}

#[test]
fn catch_bare_operation_uses_declared_act_family() {
    let root = parse(concat!(
        "act sub 'a:\n",
        "  pub return: 'a -> never\n",
        "  pub sub(x: [_] 'a): 'a = catch x:\n",
        "    return a, _ -> a\n",
        "    a -> a\n",
        "my site = 1\n",
    ));
    let lower = lower_module_map(&root);
    let root_module = lower.modules.root_id();
    let sub_act = lower.modules.type_decls(root_module, &Name("sub".into()))[0].clone();
    let companion = lower
        .modules
        .type_companion(sub_act.id)
        .expect("act companion");
    let method = lower.modules.value_decls(companion, &Name("sub".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, method));
    assert!(
        rendered.contains("[sub(") || rendered.contains("[sub;") || rendered.contains("[sub "),
        "{rendered}"
    );
    assert!(
        !rendered.contains("[return(") && !rendered.contains("[return "),
        "{rendered}"
    );
}

#[test]
fn act_operation_signature_keeps_declared_act_type_vars() {
    let root = parse(concat!(
        "act parse 'item 'err 'pos 'snap:\n",
        "  pub item: () -> 'item\n",
        "  pub fail: 'err -> never\n",
        "  pub pos: () -> 'pos\n",
        "  pub snapshot: () -> 'snap\n",
        "my site = 1\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let parse_act = lower.modules.type_decls(module, &Name("parse".into()))[0].clone();
    let companion = lower
        .modules
        .type_companion(parse_act.id)
        .expect("act companion");
    let item = lower.modules.value_decls(companion, &Name("item".into()))[0].def;
    let pos = lower.modules.value_decls(companion, &Name("pos".into()))[0].def;
    let snapshot = lower
        .modules
        .value_decls(companion, &Name("snapshot".into()))[0]
        .def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let item_rendered =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, item));
    let pos_rendered =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, pos));
    let snapshot_rendered =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, snapshot));
    assert_eq!(item_rendered, "() -> [parse 'a 'b 'c 'd] 'a");
    assert_eq!(pos_rendered, "() -> [parse 'a 'b 'c 'd] 'c");
    assert_eq!(snapshot_rendered, "() -> [parse 'a 'b 'c 'd] 'd");
}

#[test]
fn top_level_tuple_binding_registers_each_name() {
    let root = parse("my (x, y) = (1, 2)\nmy site = y\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let x = lower.modules.value_decls(module, &Name("x".into()))[0].def;
    let y = lower.modules.value_decls(module, &Name("y".into()))[0].def;
    let site = lower.modules.value_decls(module, &Name("site".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let site_body = binding_body_id(&output, site);
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, site_body)),
        Some(y)
    );
    assert!(output.session.poly.defs.get(x).is_some());
}

#[test]
fn parenthesized_keyword_binding_registers_as_value_name() {
    let root = parse("my (mod) = 1\nmy site = mod\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let keyword = lower.modules.value_decls(module, &Name("mod".into()))[0].def;
    let site = lower.modules.value_decls(module, &Name("site".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let site_body = binding_body_id(&output, site);
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, site_body)),
        Some(keyword)
    );
}

#[test]
fn type_with_ref_method_keeps_ampersand_receiver_name_and_resolves_ref_selection() {
    let root = parse(concat!(
        "mod std:\n",
        "  mod control:\n",
        "    mod var:\n",
        "      type ref 'e 'a\n",
        "type User with:\n",
        "  our &x.id = &x\n",
        "my r: std::control::var::ref 'e User = 1\n",
        "my got = r.id\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let user = lower.modules.type_decls(module, &Name("User".into()))[0].clone();
    let method = lower.modules.type_methods(user.id)[0].def;
    let (got, _) = binding_def_and_order(&lower.modules, module, "got");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert_method_body_is_receiver_identity(&output, method);
    let got_body = binding_body_id(&output, got);
    let select = match output.session.poly.expr(got_body) {
        Expr::Select(_, select) => *select,
        _ => panic!("expected select expr"),
    };
    assert_eq!(
        output.session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method })
    );
}

#[test]
fn local_type_named_ref_does_not_resolve_ref_selection() {
    let root = parse(
        "type ref 'e 'a\n\
         type User with:\n  our &x.id = &x\n\
         my r: ref 'e User = 1\nmy got = r.id\n",
    );
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (got, _) = binding_def_and_order(&lower.modules, module, "got");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let got_body = binding_body_id(&output, got);
    let select = match output.session.poly.expr(got_body) {
        Expr::Select(_, select) => *select,
        _ => panic!("expected select expr"),
    };
    assert_eq!(
        output.session.poly.select(select).resolution,
        Some(SelectResolution::RecordField)
    );
}

#[test]
fn private_type_method_is_available_only_inside_companion_scope() {
    let root = parse(
        "type User with:\n  my x.secret = x\n  my u: User = 1\n  my inside = u.secret\nmy outside_u: User = 1\nmy outside = outside_u.secret\n",
    );
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let user = lower.modules.type_decls(module, &Name("User".into()))[0].clone();
    let companion = lower.modules.type_companion(user.id).unwrap();
    let method = lower.modules.type_methods(user.id)[0].def;
    let inside = lower.modules.value_decls(companion, &Name("inside".into()))[0].def;
    let (outside, _) = binding_def_and_order(&lower.modules, module, "outside");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert!(
        output
            .session
            .methods
            .value_candidates(&["User".into()], "secret")
            .is_empty()
    );
    let inside_select = match output.session.poly.expr(binding_body_id(&output, inside)) {
        Expr::Select(_, select) => *select,
        _ => panic!("expected inside select"),
    };
    assert_eq!(
        output.session.poly.select(inside_select).resolution,
        Some(SelectResolution::Method { def: method })
    );
    let outside_select = match output.session.poly.expr(binding_body_id(&output, outside)) {
        Expr::Select(_, select) => *select,
        _ => panic!("expected outside select"),
    };
    assert_eq!(
        output.session.poly.select(outside_select).resolution,
        Some(SelectResolution::RecordField)
    );
}

#[test]
fn act_method_lowers_in_companion_and_registers_effect_method() {
    let root = parse("act nondet:\n  our x.flip = x\nmy got = 1\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let nondet = lower.modules.type_decls(module, &Name("nondet".into()))[0].clone();
    let method = lower.modules.act_methods(nondet.id)[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert_method_body_is_receiver_identity(&output, method);
    assert_act_method_receiver_has_self_subtract(&output, method, "nondet");
    assert_eq!(
        output.session.effect_methods.candidates("flip")[0].def,
        method
    );
}

#[test]
fn act_method_selection_waits_for_referenced_function_instantiation_before_field_fallback() {
    let root = parse(
        "act nondet:\n  pub branch: () -> bool\n  pub x.flip = catch x:\n    branch(), k -> k(true).flip\n    v -> v\n\nrole Box 'a:\n  our x.get: int\n\nimpl int: Box {\n  our x.get = 1\n}\n\nmy each x = { x.get; nondet::branch() }\nmy got = (each 0).flip\n",
    );
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let nondet = lower.modules.type_decls(module, &Name("nondet".into()))[0].clone();
    let method = lower.modules.act_methods(nondet.id)[0].def;
    let (got, _) = binding_def_and_order(&lower.modules, module, "got");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let got_select = match output.session.poly.expr(binding_body_id(&output, got)) {
        Expr::Select(_, select) => *select,
        _ => panic!("expected select expr"),
    };
    assert_eq!(
        output.session.poly.select(got_select).resolution,
        Some(SelectResolution::Method { def: method })
    );
}

#[test]
fn act_copy_lowers_source_method_body_as_destination_method() {
    let root =
        parse("act outer:\n  my act last:\n    our x.flip = x\n  my act next = last\nmy got = 1\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let outer = lower.modules.type_decls(module, &Name("outer".into()))[0].clone();
    let companion = lower
        .modules
        .type_companion(outer.id)
        .expect("outer companion");
    let next = lower.modules.type_decls(companion, &Name("next".into()))[0].clone();
    let method = lower.modules.act_methods(next.id)[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert_method_body_is_receiver_identity(&output, method);
}

#[test]
fn act_copy_lowers_qualified_source_method_body() {
    let root = parse(
        "mod source:\n  act box 'a:\n    our x.flip: 'a = x\nact local 't = source::box 't\nmy got = 1\n",
    );
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let local = lower.modules.type_decls(module, &Name("local".into()))[0].clone();
    let method = lower.modules.act_methods(local.id)[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert_method_body_is_receiver_identity(&output, method);
}

#[test]
fn role_method_signature_lowers_to_typeclass_method_selection() {
    let root = parse("role Display 'a:\n  our x.display: unit\nmy show = \\x -> x.display\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let display = lower.modules.type_decls(module, &Name("Display".into()))[0].clone();
    let method = lower.modules.role_methods(display.id)[0].def;
    let (show, _) = binding_def_and_order(&lower.modules, module, "show");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert_eq!(
        output.session.role_methods.candidates("display")[0].def,
        method
    );
    let method_scheme = match output.session.poly.defs.get(method) {
        Some(Def::Let {
            scheme: Some(scheme),
            ..
        }) => scheme,
        _ => panic!("role method should have a generalized scheme"),
    };
    assert_eq!(method_scheme.role_predicates.len(), 1);
    assert_eq!(
        method_scheme.role_predicates[0].role,
        vec!["Display".to_string()]
    );

    let show_body = binding_body_id(&output, show);
    let lambda_body = match output.session.poly.expr(show_body) {
        Expr::Lambda(_, body) => *body,
        _ => panic!("expected show lambda"),
    };
    let select = match output.session.poly.expr(lambda_body) {
        Expr::Select(_, select) => *select,
        _ => panic!("expected select expr"),
    };
    assert_eq!(
        output.session.poly.select(select).resolution,
        Some(SelectResolution::TypeclassMethod { member: method })
    );
}

#[test]
fn tuple_impl_member_coalesces_requirement_scaffolding_vars() {
    let root = parse(concat!(
        "role Size 'a:\n",
        "  our x.size: int\n",
        "impl Size int:\n",
        "  our x.size = x\n",
        "impl Size ('a, 'b):\n",
        "  where 'a: Size\n",
        "  where 'b: Size\n",
        "  our value.size = case value:\n",
        "    (a, b) -> case a.size:\n",
        "      _ -> b.size\n",
    ));
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = output
        .session
        .poly
        .defs
        .iter()
        .filter_map(|(_, def_data)| match def_data {
            Def::Let {
                scheme: Some(scheme),
                ..
            } => Some(poly::dump::format_scheme(&output.session.poly.typ, scheme)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        rendered.iter().any(
            |scheme| scheme == "('a, 'b) -> int where 'b: Size, 'a: Size"
                || scheme == "('a, 'b) -> int where 'a: Size, 'b: Size"
        ),
        "{rendered:?}"
    );
}

#[test]
fn typeclass_method_receiver_participates_in_selected_method_scheme() {
    let root = parse("role Ord 'a:\n  our x.le: 'a -> bool\nmy le = \\x -> \\y -> x.le y\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (le, _) = binding_def_and_order(&lower.modules, module, "le");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, le));
    assert_eq!(rendered, "'a -> 'a -> bool where 'a: Ord");
}

#[test]
fn role_input_variance_records_method_signature_polarities() {
    let root = parse("role Cast 'from 'to:\n  our x.cast: 'to\n");
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let role = vec!["Cast".to_string()];
    assert_eq!(
        output.session.role_input_variances.for_role(&role),
        Some(
            [
                RoleInputVariance::Contravariant,
                RoleInputVariance::Covariant,
            ]
            .as_slice()
        )
    );
}

#[test]
fn role_input_variance_keeps_data_constructor_arguments_invariant() {
    let root = parse(concat!(
        "pub enum wrap 'a = item 'a\n",
        "role UsesWrap 'a:\n",
        "  our x.use: wrap 'a -> bool\n",
    ));
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let role = vec!["UsesWrap".to_string()];
    assert_eq!(
        output.session.role_input_variances.for_role(&role),
        Some([RoleInputVariance::Invariant].as_slice())
    );
}

#[test]
fn unannotated_role_default_method_does_not_force_input_invariant() {
    let root = parse("role Display 'a:\n  our x.display: unit\n  our x.id = x\n");
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let role = vec!["Display".to_string()];
    assert_eq!(
        output.session.role_input_variances.for_role(&role),
        Some([RoleInputVariance::Contravariant].as_slice())
    );
}

#[test]
fn covariant_where_role_input_drops_supertype_scaffold_from_residual() {
    let root = parse(concat!(
        "pub enum mylist 'a = nil | cons('a, mylist 'a)\n",
        "role Ord 'a:\n",
        "  our x.le: 'a -> bool\n",
        "my split_le xs x = case xs:\n",
        "  mylist::nil -> mylist::nil\n",
        "  mylist::cons(y, rest) -> case y.le x:\n",
        "    true -> mylist::cons(y, split_le rest x)\n",
        "    false -> split_le rest x\n",
        "my sort_head xs = case xs:\n",
        "  mylist::nil -> mylist::nil\n",
        "  mylist::cons(x, rest) -> mylist::cons(x, split_le rest x)\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (sort_head, _) = binding_def_and_order(&lower.modules, module, "sort_head");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let scheme = def_scheme(&output, sort_head);
    assert!(matches!(
        scheme.role_predicates[0].inputs[0],
        poly::types::RolePredicateArg::Covariant(_)
    ));
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, scheme);
    assert_eq!(rendered, "mylist('a & 'b) -> mylist('b | 'a) where 'a: Ord");
}

#[test]
fn unannotated_role_default_method_keeps_covariant_where_residual_clean() {
    let root = parse(concat!(
        "pub enum mylist 'a = nil | cons('a, mylist 'a)\n",
        "role Display 'a:\n",
        "  our x.display: unit\n",
        "  our x.id = x\n",
        "my display_items(xs: mylist 'a): unit =\n",
        "  where 'a: Display\n",
        "  case xs:\n",
        "    mylist::nil -> ()\n",
        "    mylist::cons(y, rest) ->\n",
        "      y.display\n",
        "      display_items rest\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (display_items, _) = binding_def_and_order(&lower.modules, module, "display_items");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let scheme = def_scheme(&output, display_items);
    assert!(matches!(
        scheme.role_predicates[0].inputs[0],
        poly::types::RolePredicateArg::Covariant(_)
    ));
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, scheme);
    assert_eq!(rendered, "mylist 'a -> () where 'a: Display");
}

#[test]
fn role_impl_prerequisite_reuses_impl_input_type_parameter() {
    let root = parse(concat!(
        "pub enum mylist 'a = nil | cons('a, mylist 'a)\n",
        "role Display 'a:\n",
        "  our x.display: unit\n",
        "impl (mylist 'a): Display:\n",
        "  our xs.display = case xs:\n",
        "    mylist::nil -> ()\n",
        "    mylist::cons(y, _) -> y.display\n",
    ));
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let types = output.session.infer.constraints().types();
    let role = vec!["Display".to_string()];
    let candidates = output.session.role_impls.candidates(&role);
    let candidate = candidates
        .iter()
        .find(|candidate| {
            candidate.inputs.iter().any(|input| {
                matches!(
                    types.pos(input.lower),
                    Pos::Con(path, _) if path == &vec!["mylist".to_string()]
                )
            })
        })
        .expect("mylist Display impl candidate");
    assert_eq!(candidate.prerequisites.len(), 1);
    assert_eq!(candidate.prerequisites[0].role, role);

    let input_vars = role_arg_vars(types, &candidate.inputs[0]);
    let prerequisite_vars = candidate.prerequisites[0].raw_vars(types);
    assert_eq!(prerequisite_vars, input_vars);
}

#[test]
fn multi_input_role_method_selection_resolves_concrete_demand() {
    let root = parse(concat!(
        "role Index 'container 'key:\n",
        "  type value\n",
        "  pub container.index: 'key -> value\n",
        "impl Index int int:\n",
        "  type value = int\n",
        "  our c.index i = c\n",
        "my pick(c: int, i: int) = c.index i\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (pick, _) = binding_def_and_order(&lower.modules, module, "pick");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, pick));
    // selection 解決は receiver demand を別に fabricate せず、method instantiation
    // 由来の demand だけを使う。複数引数 role でも concrete なら discharge される。
    assert_eq!(rendered, "int -> int -> int");
}

#[test]
fn explicit_associated_type_keeps_impl_input_type_parameter() {
    let root = parse(concat!(
        "type box 'a with:\n",
        "  struct self:\n",
        "    item: 'a\n",
        "role Index 'container 'key:\n",
        "  type value\n",
        "  pub container.index: 'key -> value\n",
        "impl Index (box 'a) int:\n",
        "  type value = 'a\n",
        "  our c.index i = c.item\n",
        "my pick(c: box int, i: int) = c.index i\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (pick, _) = binding_def_and_order(&lower.modules, module, "pick");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, pick));
    assert_eq!(rendered, "box int -> int -> int");
}

#[test]
fn role_method_signature_is_lowered_as_positive_shape() {
    let root = parse("role Display 'a:\n  our x.display: unit\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let display = lower.modules.type_decls(module, &Name("Display".into()))[0].clone();
    let method = lower.modules.role_methods(display.id)[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let root = output.typing.def(method).expect("role method root");
    let bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(root)
        .expect("role method signature should constrain root");
    let types = output.session.infer.constraints().types();
    assert!(bounds.lowers().iter().any(|bound| {
        matches!(
            types.pos(bound.pos),
            Pos::Fun { ret, .. }
                if matches!(
                    types.pos(*ret),
                    Pos::Con(path, args)
                        if path == &vec!["unit".to_string()] && args.is_empty()
                )
        )
    }));
    assert!(
        !bounds
            .uppers()
            .iter()
            .any(|bound| matches!(types.neg(bound.neg), Neg::Fun { .. }))
    );
}

#[test]
fn private_role_method_is_not_registered_for_selection_fallback() {
    let root = parse("role Hidden 'a:\n  my x.secret: unit\nmy show = \\x -> x.secret\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let hidden = lower.modules.type_decls(module, &Name("Hidden".into()))[0].clone();
    assert_eq!(lower.modules.role_methods(hidden.id)[0].vis, Vis::My);
    let (show, _) = binding_def_and_order(&lower.modules, module, "show");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert!(output.session.role_methods.candidates("secret").is_empty());
    let show_body = binding_body_id(&output, show);
    let lambda_body = match output.session.poly.expr(show_body) {
        Expr::Lambda(_, body) => *body,
        _ => panic!("expected show lambda"),
    };
    let select = match output.session.poly.expr(lambda_body) {
        Expr::Select(_, select) => *select,
        _ => panic!("expected select expr"),
    };
    assert_eq!(
        output.session.poly.select(select).resolution,
        Some(SelectResolution::RecordField)
    );
}

#[test]
fn private_role_method_is_available_inside_role_companion_scope() {
    let root = parse(
        "role Hidden 'a:\n  my x.secret = x\n  my inside = \\x -> x.secret\nmy outside = \\x -> x.secret\n",
    );
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let hidden = lower.modules.type_decls(module, &Name("Hidden".into()))[0].clone();
    let companion = lower.modules.type_companion(hidden.id).unwrap();
    let method = lower.modules.role_methods(hidden.id)[0].def;
    let inside = lower.modules.value_decls(companion, &Name("inside".into()))[0].def;
    let (outside, _) = binding_def_and_order(&lower.modules, module, "outside");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert!(output.session.role_methods.candidates("secret").is_empty());
    let inside_body = binding_body_id(&output, inside);
    let inside_select = match output.session.poly.expr(inside_body) {
        Expr::Lambda(_, body) => match output.session.poly.expr(*body) {
            Expr::Select(_, select) => *select,
            _ => panic!("expected inside select"),
        },
        _ => panic!("expected inside lambda"),
    };
    assert_eq!(
        output.session.poly.select(inside_select).resolution,
        Some(SelectResolution::TypeclassMethod { member: method })
    );
    let outside_body = binding_body_id(&output, outside);
    let outside_select = match output.session.poly.expr(outside_body) {
        Expr::Lambda(_, body) => match output.session.poly.expr(*body) {
            Expr::Select(_, select) => *select,
            _ => panic!("expected outside select"),
        },
        _ => panic!("expected outside lambda"),
    };
    assert_eq!(
        output.session.poly.select(outside_select).resolution,
        Some(SelectResolution::RecordField)
    );
}

#[test]
fn local_arg_application_flows_empty_stack_to_callee_and_result() {
    let root = parse("my h = \\f -> f 1\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "h");
    let binding = binding_node(&root, "h").expect("h binding");
    let arg_patterns = binding_arg_patterns(&binding);
    let body = binding_body_expr(&binding).expect("h binding body");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_binding_body_with_args(&arg_patterns, &body, None)
        .unwrap();

    let types = session.infer.constraints().types();
    let (ret_eff, ret) = lambda_output(&session, computation.value);

    let (arg, _, _, _) = function_lower_bound(&session, computation.value);
    let subtract = {
        let callee = match types.neg(arg) {
            Neg::Var(var) => *var,
            other => panic!("expected callee argument var, got {other:?}"),
        };
        session
            .infer
            .constraints()
            .bounds()
            .of(callee)
            .expect("callee argument should receive function upper bound")
            .uppers()
            .iter()
            .find_map(|bound| {
                let Neg::Fun { ret_eff, .. } = types.neg(bound.neg) else {
                    return None;
                };
                let Neg::Stack { weight, .. } = types.neg(*ret_eff) else {
                    return None;
                };
                let [entry] = weight.entries() else {
                    return None;
                };
                (entry.pops == 0 && entry.stack == vec![Subtractability::Empty]).then_some(entry.id)
            })
            .expect("callee return effect upper should carry empty push")
    };
    let callee = match types.neg(arg) {
        Neg::Var(var) => *var,
        other => panic!("expected callee argument var, got {other:?}"),
    };
    let callee_bounds = session
        .infer
        .constraints()
        .bounds()
        .of(callee)
        .expect("callee argument should receive function upper bound");
    let call_effect = callee_bounds
        .uppers()
        .iter()
        .find_map(|bound| {
            let Neg::Fun { ret_eff, .. } = types.neg(bound.neg) else {
                return None;
            };
            let Neg::Stack { inner, weight } = types.neg(*ret_eff) else {
                return None;
            };
            if !weight_has_empty_stack(weight, subtract) {
                return None;
            }
            match types.neg(*inner) {
                Neg::Var(effect) => Some(*effect),
                _ => None,
            }
        })
        .expect("callee return effect upper should carry empty stack");
    let result_effect = function_result_effect(&session, computation.value);
    assert_eq!(
        assert_pos_stack_pop_var(&session, ret_eff, subtract),
        result_effect
    );
    assert_pos_stack_pop_var(&session, ret, subtract);
    let result_effect_bounds = session
        .infer
        .constraints()
        .bounds()
        .of(result_effect)
        .expect("result effect should receive stacked call effect lower bound");
    assert!(
        result_effect_bounds.lowers().iter().any(|bound| {
            matches!(types.pos(bound.pos), Pos::Var(var) if *var == call_effect)
                && weight_has_empty_stack(&bound.weights.left.to_stack_weight(), subtract)
        }),
        "application result effect should carry stacked call effect"
    );
}
