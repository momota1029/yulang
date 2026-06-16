use super::*;

#[test]
fn unannotated_callback_return_effect_surfaces_without_empty_stack() {
    let root = parse("my h(x, f) = f x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (h, _) = binding_def_and_order(&lower.modules, module, "h");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, h));
    assert!(
        rendered == "'a -> ('a -> ['b] 'c) -> ['b] 'c"
            || rendered == "'a -> ('a -> ['c] 'b) -> ['c] 'b",
        "{rendered}"
    );
}

#[test]
fn unannotated_callback_return_effect_raw_compact_keeps_shared_residual() {
    let root = parse("my h(x, f) = f x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (h, _) = binding_def_and_order(&lower.modules, module, "h");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let scheme = def_scheme(&output, h);
    let Pos::Fun { ret, .. } = output.session.poly.typ.pos(scheme.predicate) else {
        panic!("expected outer function");
    };
    let Pos::Fun {
        arg: callback,
        ret_eff,
        ..
    } = output.session.poly.typ.pos(*ret)
    else {
        panic!("expected inner function");
    };
    let Neg::Fun {
        ret_eff: callback_ret_eff,
        ..
    } = output.session.poly.typ.neg(*callback)
    else {
        panic!("expected callback argument");
    };

    assert!(
        matches!(output.session.poly.typ.pos(*ret_eff), Pos::Var(_)),
        "outer result effect should keep a residual var, got {:?}",
        output.session.poly.typ.pos(*ret_eff)
    );
    assert!(
        matches!(output.session.poly.typ.neg(*callback_ret_eff), Neg::Var(_)),
        "callback result effect should keep a residual var, got {:?}",
        output.session.poly.typ.neg(*callback_ret_eff)
    );
}

#[test]
fn defined_arg_call_inside_anonymous_lambda_keeps_sub_residual() {
    let root = parse(concat!(
        "mod std:\n",
        "  pub mod control:\n",
        "    pub mod flow:\n",
        "      pub act sub 'a:\n",
        "        pub return: 'a -> never\n",
        "        pub sub(x: [_] 'a): 'a = catch x:\n",
        "          return a, _ -> a\n",
        "          a -> a\n",
        "our g h = sub:\n",
        "  (\\i -> h i) 0\n",
        "  return 1\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (g, _) = binding_def_and_order(&lower.modules, module, "g");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, g));
    assert_eq!(rendered, "(int -> ['a] any) -> ['a] int");
}

#[test]
fn result_effect_annotation_reuses_callback_tail() {
    let root = parse("type loop\nmy h(xs, f: _ -> [loop; 'e] _): ['e] _ = f xs\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (h, _) = binding_def_and_order(&lower.modules, module, "h");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, h));
    assert_eq!(rendered, "'a -> ('a -> ['b] 'c) -> ['b] 'c");
}

#[test]
fn subtractable_helper_preserves_callback_residual_tail() {
    let root = parse(
        "type handled\nmy sub(x: [handled; 'e] _): ['e] () = x\nmy h(xs, f: _ -> [handled; 'e] _): ['e] () = sub(f xs)\n",
    );
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (h, _) = binding_def_and_order(&lower.modules, module, "h");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, h));
    assert_eq!(rendered, "'a -> ('a -> ['b] ()) -> ['b] ()");
}

#[test]
fn act_body_result_effect_annotation_reuses_callback_tail() {
    let root = parse("act loop:\n  pub h(xs, f: _ -> [loop; 'e] _): ['e] _ = f xs\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let h = lower
        .modules
        .value_path_at(
            module,
            &[Name("loop".into()), Name("h".into())],
            ModuleOrder::from_index(u32::MAX),
        )
        .expect("loop.h value");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, h));
    assert_eq!(rendered, "'a -> ('a -> ['b] 'c) -> ['b] 'c");
}

#[test]
fn role_method_selection_preserves_callback_residual_tail() {
    let root = parse(concat!(
        "type handled\n",
        "struct Box;\n",
        "role Fold 'container:\n",
        "  type item\n",
        "  pub container.fold: 'acc -> ('acc -> ['e] item -> ['e] 'acc) -> ['e] 'acc\n",
        "impl Box: Fold:\n",
        "  type item = int\n",
        "  our b.fold z f = f z 0\n",
        "my sub(x: [handled; 'e] _): ['e] () = x\n",
        "my h(xs: Box, f: int -> [handled; 'e] _): ['e] () = sub(xs.fold () (\\() x -> f x))\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (h, _) = binding_def_and_order(&lower.modules, module, "h");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, h));
    assert_eq!(rendered, "Box -> (int -> ['a] ()) -> ['a] ()");
}

#[test]
fn recursive_header_skeleton_keeps_late_callback_subtracts() {
    let root = parse("my h(f) =\n  f 1\n  h f\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (h, _) = binding_def_and_order(&lower.modules, module, "h");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let root = output.typing.def(h).expect("h def should have a root type");
    let types = output.session.infer.constraints().types();
    let (arg, _, ret_eff, ret) = function_lower_bound(&output.session, root);
    let callback = match types.neg(arg) {
        Neg::Var(var) => *var,
        other => panic!("expected callback argument var, got {other:?}"),
    };
    let subtract = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(callback)
        .expect("callback argument should receive function upper bound")
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
        .expect("callback return effect upper should carry empty push");

    assert_pos_or_var_lower_stack_pop_var(&output.session, ret_eff, subtract);
    assert_pos_or_var_lower_stack_pop_var(&output.session, ret, subtract);
}

#[test]
fn application_result_effect_includes_argument_effect() {
    let root = parse(concat!(
        "mod std:\n",
        "  mod control:\n",
        "    mod junction:\n",
        "      pub act junction:\n",
        "        pub junction: () -> bool\n",
        "act ping:\n",
        "  pub go: () -> bool\n",
        "my f x = if ping::go(): x else: x\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, f));
    assert!(
        rendered.contains("[ping") && rendered.contains("std::control::junction::junction"),
        "{rendered}"
    );
}

#[test]
fn local_recursive_binding_scheme_keeps_argument_effect_passthrough() {
    let root = parse(concat!(
        "mod std:\n",
        "  pub mod control:\n",
        "    pub mod junction:\n",
        "      pub mod junction:\n",
        "        pub junction x = x\n",
        "act signal:\n",
        "  pub ping: () -> never\n",
        "my judge(x: [signal; 'e] _): ['e] bool = catch x:\n",
        "  ping(), _ -> true\n",
        "  _ -> false\n",
        "my h f =\n",
        "  my loop b = if b:\n",
        "    loop (judge (f ()))\n",
        "    ()\n",
        "  loop true\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (h, _) = binding_def_and_order(&lower.modules, module, "h");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let h_body = binding_body_id(&output, h);
    let loop_def = first_local_let_def(&output.session.poly, h_body);
    let loop_rendered =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, loop_def));
    let h_rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, h));

    assert_eq!(h_rendered, "(() -> ['a] any) -> ['a] ()");
    assert_ne!(loop_rendered, "any -> ()", "h inferred as {h_rendered}");
}

fn first_local_let_def(poly: &poly::expr::Arena, expr: ExprId) -> DefId {
    let body = match poly.expr(expr) {
        Expr::Lambda(_, body) => *body,
        _ => expr,
    };
    let Expr::Block(stmts, _) = poly.expr(body) else {
        panic!("expected block body");
    };
    let Some(Stmt::Let(_, pat, _)) = stmts.first() else {
        panic!("expected local let");
    };
    let Pat::Var(def) = poly.pat(*pat) else {
        panic!("expected local let var pattern");
    };
    *def
}

#[test]
fn annotated_local_arg_keeps_return_effect_unannotated_for_call_subtract() {
    let root = parse("my h(x: [_] _) = x\n");
    let binding = binding_node(&root, "h").expect("h binding");

    assert_eq!(
        local_binding_call_return_effect(&binding),
        LocalCallReturnEffect::Unannotated
    );
}

#[test]
fn wildcard_shallow_handler_preserves_residual_without_resuming() {
    let root = parse(concat!(
        "act signal:\n",
        "  our ping: () -> never\n",
        "my judge(x: [_] _) = catch x:\n",
        "  ping(), _ -> true\n",
        "  _ -> false\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (judge, _) = binding_def_and_order(&lower.modules, module, "judge");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, judge));
    assert_eq!(rendered, "any [ping; 'a] -> ['a] bool");
}

#[test]
fn module_callee_application_does_not_record_empty_subtract_for_defined_lambda() {
    let root = parse("my f = 1\nmy h = \\x -> f x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "h");
    let expr = binding_expr(&root, "h");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_binding_body_expr(&expr)
        .unwrap();

    let types = session.infer.constraints().types();
    let (ret_eff, ret) = lambda_output(&session, computation.value);

    assert!(matches!(types.pos(ret_eff), Pos::Var(_)));
    assert!(matches!(types.pos(ret), Pos::Var(_)));
}

#[test]
fn anonymous_lambda_application_does_not_climb_to_outer_defined_predicate() {
    let root = parse("my outer = \\x -> \\f -> f 1\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "outer");
    let expr = binding_expr(&root, "outer");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_binding_body_expr(&expr)
        .unwrap();

    let types = session.infer.constraints().types();
    let (ret_eff, ret) = lambda_output(&session, computation.value);

    assert!(matches!(types.pos(ret_eff), Pos::Var(_)));
    assert!(matches!(types.pos(ret), Pos::Var(_)));
}

#[test]
fn lambda_lowering_binds_local_param_and_constrains_function_value() {
    let root = parse("my id = \\x -> x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "id");
    let expr = binding_expr(&root, "id");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_binding_body_expr(&expr)
        .unwrap();
    let (pat, body) = match session.poly.expr(computation.expr) {
        Expr::Lambda(pat, body) => (*pat, *body),
        _ => panic!("expected lambda expr"),
    };
    let param = match session.poly.pat(pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected lambda param binding"),
    };
    let body_ref = expr_ref(&session, body);
    let param_value = session.refs.value(body_ref).expect("local ref value slot");

    assert_eq!(session.poly.ref_target(body_ref), Some(param));

    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(computation.value)
        .expect("lambda value should receive a function lower bound");
    let types = session.infer.constraints().types();
    let (arg, arg_eff, ret) = bounds
        .lowers()
        .iter()
        .find_map(|bound| match types.pos(bound.pos) {
            Pos::Fun {
                arg, arg_eff, ret, ..
            } => Some((*arg, *arg_eff, *ret)),
            _ => None,
        })
        .expect("lambda lower bound should be a function");

    assert!(matches!(types.neg(arg), Neg::Var(var) if *var == param_value));
    assert_neg_bottom(types, arg_eff);
    assert!(matches!(types.pos(ret), Pos::Var(var) if *var == param_value));
}

#[test]
fn lambda_multiple_params_lower_to_nested_lambdas() {
    let root = parse("my f = \\() x -> x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();
    let (first_pat, inner) = match session.poly.expr(computation.expr) {
        Expr::Lambda(pat, body) => (*pat, *body),
        _ => panic!("expected outer lambda"),
    };
    assert!(matches!(session.poly.pat(first_pat), Pat::Lit(Lit::Unit)));

    let (second_pat, body) = match session.poly.expr(inner) {
        Expr::Lambda(pat, body) => (*pat, *body),
        _ => panic!("expected inner lambda"),
    };
    let param = match session.poly.pat(second_pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected second parameter binding"),
    };
    let body_ref = expr_ref(&session, body);

    assert_eq!(session.poly.ref_target(body_ref), Some(param));
}

#[test]
fn binding_empty_call_header_lowers_to_unit_lambda_param() {
    let root = parse("my f() = 1\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let f = lower.modules.value_decls(module, &Name("f".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let body = binding_body_id(&output, f);
    let (param, _) = match output.session.poly.expr(body) {
        Expr::Lambda(param, body) => (*param, *body),
        _ => panic!("expected unit lambda body"),
    };
    assert!(matches!(
        output.session.poly.pat(param),
        Pat::Lit(Lit::Unit)
    ));
}

#[test]
fn lambda_param_effect_annotation_adds_stacked_inner_lower() {
    let root = parse("type handled\nmy f = \\x: [handled] 'a -> x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_binding_body_expr(&expr)
        .unwrap();

    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(computation.value)
        .expect("lambda value should receive a function lower bound");
    let types = session.infer.constraints().types();
    let (arg_eff, ret_eff, ret) = bounds
        .lowers()
        .iter()
        .find_map(|bound| match types.pos(bound.pos) {
            Pos::Fun {
                arg_eff,
                ret_eff,
                ret,
                ..
            } => Some((*arg_eff, *ret_eff, *ret)),
            _ => None,
        })
        .expect("lambda lower bound should be a function");
    let param_effect = match types.neg(arg_eff) {
        Neg::Var(var) => *var,
        other => panic!("expected arg effect var, got {other:?}"),
    };

    // 注釈残差は fresh な内側変数として param effect の下界に入る。self edge にはしない。
    let param_bounds = session
        .infer
        .constraints()
        .bounds()
        .of(param_effect)
        .expect("param effect should receive stacked inner lower bound");
    let subtract = param_bounds
        .lowers()
        .iter()
        .find_map(|bound| {
            if !matches!(types.pos(bound.pos), Pos::Var(var) if *var != param_effect) {
                return None;
            }
            weight_set_path_id(&bound.weights.left, &["handled"])
        })
        .expect("param effect should carry handled stack on a fresh inner var");
    assert_pos_stack_pop_var(&session, ret_eff, subtract);
    assert_pos_stack_pop_var(&session, ret, subtract);
}

#[test]
fn lambda_param_value_annotation_keeps_outer_arg_effect_bottom() {
    let root = parse("my f = \\x: int -> x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_binding_body_expr(&expr)
        .unwrap();

    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(computation.value)
        .expect("lambda value should receive a function lower bound");
    let types = session.infer.constraints().types();
    let (arg_eff, ret_eff, ret) = bounds
        .lowers()
        .iter()
        .find_map(|bound| match types.pos(bound.pos) {
            Pos::Fun {
                arg_eff,
                ret_eff,
                ret,
                ..
            } => Some((*arg_eff, *ret_eff, *ret)),
            _ => None,
        })
        .expect("lambda lower bound should be a function");

    assert_neg_bottom(types, arg_eff);
    assert!(matches!(types.pos(ret_eff), Pos::Var(_)));
    assert!(matches!(types.pos(ret), Pos::Var(_)));
}

#[test]
fn recursive_lambda_lowers_to_local_self_binding() {
    let root = parse("my f = \\'self x -> 'self\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    let (stmts, tail) = match session.poly.expr(computation.expr) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected recursive lambda block"),
    };
    let [Stmt::Let(_, self_pat, body)] = stmts.as_slice() else {
        panic!("expected recursive self let");
    };
    let self_def = match session.poly.pat(*self_pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected recursive self local"),
    };
    let lambda_body = match session.poly.expr(*body) {
        Expr::Lambda(_, body) => *body,
        _ => panic!("expected recursive lambda body"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, lambda_body)),
        Some(self_def)
    );
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, tail)),
        Some(self_def)
    );
}

#[test]
fn labeled_case_expr_lowers_to_recursive_self_application() {
    let root = parse("my f = case 'go 4: 0 -> 0, n -> 'go 0\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_binding_body_expr(&expr)
        .unwrap();

    let (self_def, lambda, tail) = recursive_self_block_parts(&session, computation.expr);
    let (tail_callee, tail_arg) = match session.poly.expr(tail) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected case label tail application"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, tail_callee)),
        Some(self_def)
    );
    assert!(matches!(
        session.poly.expr(tail_arg),
        Expr::Lit(Lit::Int(4))
    ));

    let case_expr = lambda_body(&session, lambda);
    let arms = match session.poly.expr(case_expr) {
        Expr::Case(_, arms) => arms,
        _ => panic!("expected recursive case body"),
    };
    let recur_callee = match session.poly.expr(arms[1].body) {
        Expr::App(callee, _) => *callee,
        _ => panic!("expected recursive case arm application"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, recur_callee)),
        Some(self_def)
    );
}

#[test]
fn labeled_case_lambda_lowers_to_recursive_self_function() {
    let root = parse("my f = \\case 'go: 0 -> 0, n -> 'go 0\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_binding_body_expr(&expr)
        .unwrap();

    let (self_def, lambda, tail) = recursive_self_block_parts(&session, computation.expr);
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, tail)),
        Some(self_def)
    );
    let case_expr = lambda_body(&session, lambda);
    let arms = match session.poly.expr(case_expr) {
        Expr::Case(_, arms) => arms,
        _ => panic!("expected recursive case lambda body"),
    };
    let recur_callee = match session.poly.expr(arms[1].body) {
        Expr::App(callee, _) => *callee,
        _ => panic!("expected recursive case lambda arm application"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, recur_callee)),
        Some(self_def)
    );
}

#[test]
fn labeled_catch_expr_lowers_to_recursive_self_application() {
    let root = parse("my f = catch 'go 1: value -> 'go value\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_binding_body_expr(&expr)
        .unwrap();

    let (self_def, lambda, tail) = recursive_self_block_parts(&session, computation.expr);
    let (tail_callee, tail_arg) = match session.poly.expr(tail) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected catch label tail application"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, tail_callee)),
        Some(self_def)
    );
    assert!(matches!(
        session.poly.expr(tail_arg),
        Expr::Lit(Lit::Int(1))
    ));

    let catch_expr = lambda_body(&session, lambda);
    let arms = match session.poly.expr(catch_expr) {
        Expr::Catch(_, arms) => arms,
        _ => panic!("expected recursive catch body"),
    };
    let recur_callee = match session.poly.expr(arms[0].body) {
        Expr::App(callee, _) => *callee,
        _ => panic!("expected recursive catch arm application"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, recur_callee)),
        Some(self_def)
    );
}

#[test]
fn labeled_catch_lambda_lowers_to_recursive_self_function() {
    let root = parse("my f = \\catch 'go: value -> 'go value\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_binding_body_expr(&expr)
        .unwrap();

    let (self_def, lambda, tail) = recursive_self_block_parts(&session, computation.expr);
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, tail)),
        Some(self_def)
    );
    let catch_expr = lambda_body(&session, lambda);
    let arms = match session.poly.expr(catch_expr) {
        Expr::Catch(_, arms) => arms,
        _ => panic!("expected recursive catch lambda body"),
    };
    let recur_callee = match session.poly.expr(arms[0].body) {
        Expr::App(callee, _) => *callee,
        _ => panic!("expected recursive catch lambda arm application"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, recur_callee)),
        Some(self_def)
    );
}

#[test]
fn case_lowering_binds_arm_pattern_local() {
    let root = parse("my f = case 1: n -> n\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    let (_scrutinee, arms) = match session.poly.expr(computation.expr) {
        Expr::Case(scrutinee, arms) => (*scrutinee, arms),
        _ => panic!("expected case expr"),
    };
    let [arm] = arms.as_slice() else {
        panic!("expected one case arm");
    };
    let param = match session.poly.pat(arm.pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected arm pattern local"),
    };
    let body_ref = expr_ref(&session, arm.body);

    assert_eq!(session.poly.ref_target(body_ref), Some(param));
    assert!(computation.is_expansive());
}

#[test]
fn case_lambda_lowers_to_lambda_with_case_body() {
    let root = parse("my f = \\case: n -> n\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    let (scrutinee_pat, body) = match session.poly.expr(computation.expr) {
        Expr::Lambda(pat, body) => (*pat, *body),
        _ => panic!("expected case lambda"),
    };
    let scrutinee_def = match session.poly.pat(scrutinee_pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected case lambda scrutinee local"),
    };
    let (scrutinee, arms) = match session.poly.expr(body) {
        Expr::Case(scrutinee, arms) => (*scrutinee, arms),
        _ => panic!("expected case lambda body"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, scrutinee)),
        Some(scrutinee_def)
    );
    let [arm] = arms.as_slice() else {
        panic!("expected one case arm");
    };
    let param = match session.poly.pat(arm.pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected arm pattern local"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, arm.body)),
        Some(param)
    );
}

#[test]
fn case_constructor_pattern_resolves_path_reference() {
    let root = parse("mod m:\n  my some = 0\nmy x = 1\nmy f = case x: m::some y -> y\n");
    let lower = lower_module_map(&root);
    let root_module = lower.modules.root_id();
    let m = lower.modules.module_decls(root_module, &Name("m".into()))[0].module;
    let constructor = lower.modules.value_decls(m, &Name("some".into()))[0].def;
    let (f, _) = binding_def_and_order(&lower.modules, root_module, "f");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let case = binding_body_id(&output, f);
    let (_scrutinee, arms) = match output.session.poly.expr(case) {
        Expr::Case(scrutinee, arms) => (*scrutinee, arms),
        _ => panic!("expected case expr"),
    };
    let [arm] = arms.as_slice() else {
        panic!("expected one case arm");
    };
    let (reference, payloads) = match output.session.poly.pat(arm.pat) {
        Pat::Con(reference, payloads) => (*reference, payloads),
        _ => panic!("expected constructor pattern"),
    };
    let [payload] = payloads.as_slice() else {
        panic!("expected one constructor payload");
    };
    let payload = match output.session.poly.pat(*payload) {
        Pat::Var(def) => *def,
        _ => panic!("expected constructor payload local"),
    };
    let body_ref = expr_ref(&output.session, arm.body);

    assert_eq!(output.session.poly.ref_target(reference), Some(constructor));
    assert_eq!(output.session.poly.ref_target(body_ref), Some(payload));
}

#[test]
fn constructor_pattern_payload_flows_from_scrutinee_without_annotation() {
    let root = parse(concat!(
        "pub enum opt 'a = none | some 'a\n",
        "my id_from_some o = case o:\n",
        "  opt::some x -> x\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (id_from_some, _) = binding_def_and_order(&lower.modules, module, "id_from_some");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let rendered =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, id_from_some));
    assert_eq!(rendered, "opt 'a -> 'a");
}

#[test]
fn constructor_pattern_spaced_tuple_group_matches_tuple_payload_fields() {
    let root = parse(concat!(
        "pub enum bound = unbounded | included int\n",
        "pub enum range = within (bound, bound)\n",
        "my start r = case r:\n",
        "  range::within (start, _) -> start\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (start, _) = binding_def_and_order(&lower.modules, module, "start");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, start));
    assert_eq!(rendered, "range -> bound");
}

#[test]
fn constructor_pattern_payload_participates_in_guard_role_method() {
    let root = parse_with_junction_std(concat!(
        "role Ord 'a:\n",
        "  our x.le: 'a -> bool\n",
        "pub enum view 'a = empty | leaf 'a\n",
        "my keep v x = case v:\n",
        "  view::leaf y if y.le x -> y\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (keep, _) = binding_def_and_order(&lower.modules, module, "keep");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let scheme = def_scheme(&output, keep);
    assert!(matches!(
        scheme.role_predicates[0].inputs[0],
        poly::types::RolePredicateArg::Covariant(_)
    ));
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, scheme);
    assert_eq!(rendered, "view('b & 'a) -> 'a -> 'b where Ord('a | 'b)");
}

#[test]
fn catch_lowering_binds_value_arm_pattern_local() {
    let root = parse("my f = catch 1: value -> value\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    let (_body, arms) = match session.poly.expr(computation.expr) {
        Expr::Catch(body, arms) => (*body, arms),
        _ => panic!("expected catch expr"),
    };
    let [arm] = arms.as_slice() else {
        panic!("expected one catch arm");
    };
    assert!(arm.continuation.is_none());
    let value = match session.poly.pat(arm.pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected value arm pattern local"),
    };
    let body_ref = expr_ref(&session, arm.body);

    assert_eq!(session.poly.ref_target(body_ref), Some(value));
    assert!(computation.is_expansive());
}

#[test]
fn catch_lambda_lowers_to_lambda_with_catch_body() {
    let root = parse("my f = \\catch: value -> value\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    let (scrutinee_pat, body) = match session.poly.expr(computation.expr) {
        Expr::Lambda(pat, body) => (*pat, *body),
        _ => panic!("expected catch lambda"),
    };
    let scrutinee_def = match session.poly.pat(scrutinee_pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected catch lambda scrutinee local"),
    };
    let (scrutinee, arms) = match session.poly.expr(body) {
        Expr::Catch(scrutinee, arms) => (*scrutinee, arms),
        _ => panic!("expected catch lambda body"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, scrutinee)),
        Some(scrutinee_def)
    );
    let [arm] = arms.as_slice() else {
        panic!("expected one catch arm");
    };
    assert!(arm.continuation.is_none());
    let param = match session.poly.pat(arm.pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected value arm pattern local"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, arm.body)),
        Some(param)
    );
}
