use super::*;

#[test]
fn string_interpolation_invalid_format_text_reports_unsupported() {
    let root = parse("my n = 1\nmy text = \"%q{n}\"\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "text");
    let expr = binding_expr(&root, "text");
    let mut session = AnalysisSession::new(lower.arena);

    let error = match ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
    {
        Ok(_) => panic!("expected invalid string format interpolation to be unsupported"),
        Err(error) => error,
    };

    assert!(matches!(
        error,
        LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::StringInterpFormatText
        }
    ));
}

#[test]
fn case_guard_lowers_as_guard_expr_with_pattern_scope() {
    let root = parse_with_junction_std("my f = case true:\n  n if n -> 1\n  _ -> 0\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let junction = std_junction_def(&lower.modules);
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();
    session.drain_work();

    let arms = match session.poly.expr(computation.expr) {
        Expr::Case(_, arms) => arms,
        _ => panic!("expected case expr"),
    };
    let first = &arms[0];
    let local = match session.poly.pat(first.pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected guarded pattern local"),
    };
    let guard = first.guard.expect("expected case guard");
    let guard_arg = assert_junction_app(&session, guard, junction);
    let guard_ref = expr_ref(&session, guard_arg);

    assert_eq!(session.poly.ref_target(guard_ref), Some(local));
}

#[test]
fn catch_guard_lowers_as_guard_expr() {
    let root = parse_with_junction_std(
        "my run = 1\nmy f = catch run:\n  eff x, k if true -> k x\n  value -> value\n",
    );
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let junction = std_junction_def(&lower.modules);
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let catch = binding_body_id(&output, f);
    let arms = match output.session.poly.expr(catch) {
        Expr::Catch(_, arms) => arms,
        _ => panic!("expected catch expr"),
    };
    let first = &arms[0];
    let guard = first.guard.expect("expected catch guard");
    let guard_arg = assert_junction_app(&output.session, guard, junction);

    assert!(first.continuation.is_some());
    assert!(matches!(
        output.session.poly.expr(guard_arg),
        Expr::Lit(Lit::Bool(true))
    ));
}

#[test]
fn string_or_pattern_lowers_to_or_literal_pattern() {
    let root = parse("my f = case \"a\":\n  \"a\" | \"b\" -> 1\n  _ -> 0\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    let arms = match session.poly.expr(computation.expr) {
        Expr::Case(_, arms) => arms,
        _ => panic!("expected case expr"),
    };
    let (lhs, rhs) = match session.poly.pat(arms[0].pat) {
        Pat::Or(lhs, rhs) => (*lhs, *rhs),
        _ => panic!("expected or pattern"),
    };

    assert!(matches!(
        session.poly.pat(lhs),
        Pat::Lit(Lit::Str(text)) if text == "a"
    ));
    assert!(matches!(
        session.poly.pat(rhs),
        Pat::Lit(Lit::Str(text)) if text == "b"
    ));
}

#[test]
fn case_bool_literal_patterns_lower_to_literals() {
    let root = parse("my f = case true:\n  true -> 1\n  false -> 0\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    let arms = match session.poly.expr(computation.expr) {
        Expr::Case(_, arms) => arms,
        _ => panic!("expected case expr"),
    };
    assert!(matches!(
        session.poly.pat(arms[0].pat),
        Pat::Lit(Lit::Bool(true))
    ));
    assert!(matches!(
        session.poly.pat(arms[1].pat),
        Pat::Lit(Lit::Bool(false))
    ));
}

#[test]
fn case_integer_pattern_over_i64_lowers_to_bigint() {
    let root = parse(concat!(
        "my f = case 9223372036854775808:\n",
        "  9223372036854775808 -> 1\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    let arms = match session.poly.expr(computation.expr) {
        Expr::Case(_, arms) => arms,
        _ => panic!("expected case expr"),
    };
    assert!(matches!(
        session.poly.pat(arms[0].pat),
        Pat::Lit(Lit::BigInt(value)) if value.to_string() == "9223372036854775808"
    ));
}

#[test]
fn record_pattern_with_default_binds_field_local() {
    let root = parse("my f({width = 1}) = width\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let lambda = binding_body_id(&output, f);
    let (pat, body) = match output.session.poly.expr(lambda) {
        Expr::Lambda(pat, body) => (*pat, *body),
        _ => panic!("expected function binding to lower to lambda"),
    };
    let field_pat = match output.session.poly.pat(pat) {
        Pat::Record { fields, .. } => {
            assert!(fields[0].default.is_some());
            fields[0].pat
        }
        _ => panic!("expected record pattern"),
    };
    let field = match output.session.poly.pat(field_pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected field local"),
    };
    let body_ref = expr_ref(&output.session, body);

    assert_eq!(output.session.poly.ref_target(body_ref), Some(field));
}

#[test]
fn record_pattern_default_does_not_constrain_optional_input_field() {
    let root = parse(concat!(
        "mod std:\n",
        "  pub mod num:\n",
        "    pub role Mul 'a:\n",
        "      pub a.mul: 'a -> 'a\n",
        "use std::num::*\n",
        "pub infix (*) 6.0.0 6.0.1 = \\x -> \\y -> x.mul y\n",
        "our box {width = 1, height = width} =\n",
        "  width * height\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (box_def, _) = binding_def_and_order(&lower.modules, module, "box");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, box_def));
    assert!(rendered.contains("width?:"), "{rendered}");
    assert!(rendered.contains("height?:"), "{rendered}");
    for name in ["width", "height"] {
        let field = rendered
            .split_once(&format!("{name}?: "))
            .and_then(|(_, tail)| tail.split([',', '}']).next())
            .unwrap_or_else(|| panic!("missing {name} field in {rendered}"));
        assert!(!field.contains("& int"), "{rendered}");
        assert!(!field.contains("int &"), "{rendered}");
    }
}

#[test]
fn poly_variant_expr_and_pattern_lower_to_poly_variant_ir() {
    let root =
        parse("my f option = case option:\n  :ok msg -> :rendered msg\n  :pending -> :empty\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let lambda = binding_body_id(&output, f);
    let case = match output.session.poly.expr(lambda) {
        Expr::Lambda(_, body) => *body,
        _ => panic!("expected function binding to lower to lambda"),
    };
    let arms = match output.session.poly.expr(case) {
        Expr::Case(_, arms) => arms,
        _ => panic!("expected case expr"),
    };
    assert!(matches!(
        output.session.poly.pat(arms[0].pat),
        Pat::PolyVariant(name, payloads) if name == "ok" && payloads.len() == 1
    ));
    assert!(matches!(
        output.session.poly.expr(arms[0].body),
        Expr::PolyVariant(name, payloads) if name == "rendered" && payloads.len() == 1
    ));
}

#[test]
fn poly_variant_case_preserves_payloads_in_scrutinee_type() {
    let root = parse(concat!(
        "my render option = case option:\n",
        "  :ok msg -> :rendered_ok msg\n",
        "  :err code -> :rendered_err code\n",
        "  :pending -> :rendered_pending\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (render, _) = binding_def_and_order(&lower.modules, module, "render");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, render));
    assert!(
        !rendered.contains("ok never") && !rendered.contains("err never"),
        "case scrutinee payloads collapsed to never: {rendered}"
    );
}

#[test]
fn defined_lambda_parameter_local_defs_are_marked_as_inputs() {
    let root = parse("my render option = case option:\n  :pending -> :rendered_pending\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (render, _) = binding_def_and_order(&lower.modules, module, "render");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let lambda = binding_body_id(&output, render);
    let param = match output.session.poly.expr(lambda) {
        Expr::Lambda(pat, _) => match output.session.poly.pat(*pat) {
            Pat::Var(def) => *def,
            _ => panic!("expected parameter var pattern"),
        },
        _ => panic!("expected function binding to lower to lambda"),
    };
    let local = output
        .session
        .local_defs
        .get(param)
        .expect("parameter local def should be tracked");

    assert_eq!(local.role, LocalDefRole::Input);
}

#[test]
fn defined_lambda_pattern_member_local_defs_remain_values() {
    let root = parse("my f({x = 1}) = x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let lambda = binding_body_id(&output, f);
    let x = match output.session.poly.expr(lambda) {
        Expr::Lambda(pat, _) => match output.session.poly.pat(*pat) {
            Pat::Record { fields, .. } => fields
                .iter()
                .find(|field| field.name == "x")
                .and_then(|field| match output.session.poly.pat(field.pat) {
                    Pat::Var(def) => Some(*def),
                    _ => None,
                })
                .expect("expected shorthand record field to bind x"),
            _ => panic!("expected parameter record pattern"),
        },
        _ => panic!("expected function binding to lower to lambda"),
    };
    let local = output
        .session
        .local_defs
        .get(x)
        .expect("pattern member local def should be tracked");

    assert_eq!(local.role, LocalDefRole::Value);
}

#[test]
fn record_literal_lowers_to_record_expr() {
    let root = parse("my r = {x: 1, y: true}\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "r");
    let expr = binding_expr(&root, "r");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    match session.poly.expr(computation.expr) {
        Expr::Record { fields, spread } => {
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].0, "x");
            assert_eq!(fields[1].0, "y");
            assert!(matches!(spread, RecordSpread::None));
        }
        _ => panic!("expected record literal"),
    }
}

#[test]
fn record_literal_spread_lowers_to_head_and_tail_spread() {
    let root = parse("my base = {x: 1}\nmy head = {..base, y: 2}\nmy tail = {z: 3, ..base}\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (base, _) = binding_def_and_order(&lower.modules, module, "base");
    let (head_owner, head_site) = binding_def_and_order(&lower.modules, module, "head");
    let (tail_owner, tail_site) = binding_def_and_order(&lower.modules, module, "tail");
    let head_expr = binding_expr(&root, "head");
    let tail_expr = binding_expr(&root, "tail");
    let mut session = AnalysisSession::new(lower.arena);

    let head = ExprLowerer::new(&mut session, &lower.modules, module, head_site, head_owner)
        .lower_expr(&head_expr)
        .unwrap();
    let tail = ExprLowerer::new(&mut session, &lower.modules, module, tail_site, tail_owner)
        .lower_expr(&tail_expr)
        .unwrap();
    session.drain_work();

    match session.poly.expr(head.expr) {
        Expr::Record { fields, spread } => {
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, "y");
            let spread_expr = match spread {
                RecordSpread::Head(expr) => *expr,
                _ => panic!("expected head spread"),
            };
            assert_eq!(
                session.poly.ref_target(expr_ref(&session, spread_expr)),
                Some(base)
            );
        }
        _ => panic!("expected head spread record literal"),
    }

    match session.poly.expr(tail.expr) {
        Expr::Record { fields, spread } => {
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, "z");
            let spread_expr = match spread {
                RecordSpread::Tail(expr) => *expr,
                _ => panic!("expected tail spread"),
            };
            assert_eq!(
                session.poly.ref_target(expr_ref(&session, spread_expr)),
                Some(base)
            );
        }
        _ => panic!("expected tail spread record literal"),
    }
}

#[test]
fn projection_tuple_tail_lowers_to_tuple_of_receiver_selections() {
    let root = parse("my id x = x\nmy a = {x: 1, y: id}\nmy arg = 2\nmy got = a.(x, y(arg))\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (a, _) = binding_def_and_order(&lower.modules, module, "a");
    let (arg, _) = binding_def_and_order(&lower.modules, module, "arg");
    let (got, _) = binding_def_and_order(&lower.modules, module, "got");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, got);
    let items = match output.session.poly.expr(body) {
        Expr::Tuple(items) => items,
        _ => panic!("expected projection tuple to lower to tuple"),
    };
    let [x_item, y_item] = items.as_slice() else {
        panic!("expected two projection tuple items");
    };

    let x_select = match output.session.poly.expr(*x_item) {
        Expr::Select(receiver, select) => {
            assert_eq!(
                output
                    .session
                    .poly
                    .ref_target(expr_ref(&output.session, *receiver)),
                Some(a)
            );
            *select
        }
        _ => panic!("expected first projection item to be a selection"),
    };
    assert_eq!(output.session.poly.select(x_select).name, "x");

    let (callee, app_arg) = match output.session.poly.expr(*y_item) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected second projection item to be a call"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, app_arg)),
        Some(arg)
    );
    let y_select = match output.session.poly.expr(callee) {
        Expr::Select(receiver, select) => {
            assert_eq!(
                output
                    .session
                    .poly
                    .ref_target(expr_ref(&output.session, *receiver)),
                Some(a)
            );
            *select
        }
        _ => panic!("expected projection call callee to be a selection"),
    };
    assert_eq!(output.session.poly.select(y_select).name, "y");
}

#[test]
fn projection_record_tail_lowers_to_record_of_receiver_selections() {
    let root =
        parse("my id x = x\nmy a = {y: id, z: id}\nmy arg = 2\nmy got = a.{ x: y, y: z(arg) }\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (a, _) = binding_def_and_order(&lower.modules, module, "a");
    let (arg, _) = binding_def_and_order(&lower.modules, module, "arg");
    let (got, _) = binding_def_and_order(&lower.modules, module, "got");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, got);
    let fields = match output.session.poly.expr(body) {
        Expr::Record { fields, spread } => {
            assert!(matches!(spread, RecordSpread::None));
            fields
        }
        _ => panic!("expected projection record to lower to record"),
    };
    let [(x_name, x_expr), (y_name, y_expr)] = fields.as_slice() else {
        panic!("expected two projection record fields");
    };
    assert_eq!(x_name, "x");
    assert_eq!(y_name, "y");

    let x_select = match output.session.poly.expr(*x_expr) {
        Expr::Select(receiver, select) => {
            assert_eq!(
                output
                    .session
                    .poly
                    .ref_target(expr_ref(&output.session, *receiver)),
                Some(a)
            );
            *select
        }
        _ => panic!("expected first record projection value to be a selection"),
    };
    assert_eq!(output.session.poly.select(x_select).name, "y");

    let (callee, app_arg) = match output.session.poly.expr(*y_expr) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected second record projection value to be a call"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, app_arg)),
        Some(arg)
    );
    let z_select = match output.session.poly.expr(callee) {
        Expr::Select(receiver, select) => {
            assert_eq!(
                output
                    .session
                    .poly
                    .ref_target(expr_ref(&output.session, *receiver)),
                Some(a)
            );
            *select
        }
        _ => panic!("expected record projection call callee to be a selection"),
    };
    assert_eq!(output.session.poly.select(z_select).name, "z");
}

#[test]
fn projection_tail_binds_expansive_receiver_once() {
    let root = parse("my make n = {x: n, y: n}\nmy got = make(1).(x, y)\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (got, _) = binding_def_and_order(&lower.modules, module, "got");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, got);
    let (temp_def, tail) = match output.session.poly.expr(body) {
        Expr::Block(stmts, Some(tail)) => {
            let [Stmt::Let(Vis::My, pat, receiver_expr)] = stmts.as_slice() else {
                panic!("expected one projection receiver binding");
            };
            assert!(matches!(
                output.session.poly.expr(*receiver_expr),
                Expr::App(_, _)
            ));
            let Pat::Var(def) = output.session.poly.pat(*pat) else {
                panic!("expected projection receiver var pattern");
            };
            (*def, *tail)
        }
        _ => panic!("expected expansive projection receiver to lower through a block"),
    };
    let items = match output.session.poly.expr(tail) {
        Expr::Tuple(items) => items,
        _ => panic!("expected projection tail block to end in tuple"),
    };
    assert_eq!(items.len(), 2);
    for item in items {
        let Expr::Select(receiver, _) = output.session.poly.expr(*item) else {
            panic!("expected projection item to be a selection");
        };
        assert_eq!(
            output
                .session
                .poly
                .ref_target(expr_ref(&output.session, *receiver)),
            Some(temp_def)
        );
    }
}

#[test]
fn brace_block_with_qualified_apply_colon_lowers_as_block_expr() {
    let root = parse(concat!(
        "mod std:\n",
        "  pub mod control:\n",
        "    pub mod flow:\n",
        "      pub mod sub:\n",
        "        pub return x = x\n",
        "my value = {std::control::flow::sub::return: 1}\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "value");
    let expr = binding_expr(&root, "value");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    assert!(matches!(
        session.poly.expr(computation.expr),
        Expr::App(_, _)
    ));
}

#[test]
fn struct_constructor_accepts_record_literal_argument() {
    let root = parse("struct Point {x: int, y: int}\nmy p = Point {x: 1, y: 2}\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "p");
    let expr = binding_expr(&root, "p");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    let (_, arg) = match session.poly.expr(computation.expr) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected constructor application"),
    };
    assert!(matches!(
        session.poly.expr(arg),
        Expr::Record {
            spread: RecordSpread::None,
            ..
        }
    ));
}

#[test]
fn if_condition_is_wrapped_with_junction_before_bool_case() {
    let root = parse_with_junction_std("my f = if true: 1 else: 2\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let junction = std_junction_def(&lower.modules);
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();
    session.drain_work();

    let arms = match session.poly.expr(computation.expr) {
        Expr::Case(scrutinee, arms) => {
            let condition = assert_junction_app(&session, *scrutinee, junction);
            assert!(matches!(
                session.poly.expr(condition),
                Expr::Lit(Lit::Bool(true))
            ));
            arms
        }
        _ => panic!("expected if expr to lower to case"),
    };
    assert_eq!(arms.len(), 2);
    assert!(matches!(
        session.poly.pat(arms[0].pat),
        Pat::Lit(Lit::Bool(true))
    ));
    assert!(matches!(
        session.poly.pat(arms[1].pat),
        Pat::Lit(Lit::Bool(false))
    ));
}

#[test]
fn elsif_lowers_to_nested_false_case() {
    let root = parse_with_junction_std("my f = if true: 1 elsif false: 2 else: 3\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let junction = std_junction_def(&lower.modules);
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();
    session.drain_work();

    let outer_arms = match session.poly.expr(computation.expr) {
        Expr::Case(scrutinee, arms) => {
            let condition = assert_junction_app(&session, *scrutinee, junction);
            assert!(matches!(
                session.poly.expr(condition),
                Expr::Lit(Lit::Bool(true))
            ));
            arms
        }
        _ => panic!("expected outer case"),
    };
    let nested = outer_arms[1].body;
    match session.poly.expr(nested) {
        Expr::Case(scrutinee, arms) => {
            let condition = assert_junction_app(&session, *scrutinee, junction);
            assert!(matches!(
                session.poly.expr(condition),
                Expr::Lit(Lit::Bool(false))
            ));
            assert_eq!(arms.len(), 2);
        }
        _ => panic!("expected elsif to lower into false branch case"),
    }
}

#[test]
fn if_without_else_discards_then_value_and_returns_unit() {
    let root = parse_with_junction_std("my f = if true: 1\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let junction = std_junction_def(&lower.modules);
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();
    session.drain_work();

    let arms = match session.poly.expr(computation.expr) {
        Expr::Case(scrutinee, arms) => {
            let condition = assert_junction_app(&session, *scrutinee, junction);
            assert!(matches!(
                session.poly.expr(condition),
                Expr::Lit(Lit::Bool(true))
            ));
            arms
        }
        _ => panic!("expected if expr to lower to case"),
    };
    assert!(matches!(session.poly.expr(arms[0].body), Expr::Block(_, _)));
    assert!(matches!(
        session.poly.expr(arms[1].body),
        Expr::Lit(Lit::Unit)
    ));
}

#[test]
fn method_lambda_lowers_to_receiver_lambda_with_selection_body() {
    let root = parse("my display = \\.display\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "display");
    let expr = binding_expr(&root, "display");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    let (pat, body) = match session.poly.expr(computation.expr) {
        Expr::Lambda(pat, body) => (*pat, *body),
        _ => panic!("expected method lambda to lower to lambda"),
    };
    let receiver = match session.poly.pat(pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected implicit receiver pattern"),
    };
    let (receiver_expr, select) = match session.poly.expr(body) {
        Expr::Select(receiver_expr, select) => (*receiver_expr, *select),
        _ => panic!("expected method lambda body to be a selection"),
    };
    let receiver_ref = expr_ref(&session, receiver_expr);

    assert_eq!(session.poly.ref_target(receiver_ref), Some(receiver));
    assert_eq!(session.poly.select(select).name, "display");
}

#[test]
fn dollar_sigil_read_lowers_to_ref_get_call() {
    let root = parse("my &x = 1\nmy got = $x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (target, _) = binding_def_and_order(&lower.modules, module, "&x");
    let (owner, site) = binding_def_and_order(&lower.modules, module, "got");
    let expr = binding_expr(&root, "got");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();
    session.drain_work();

    let (callee, unit) = match session.poly.expr(computation.expr) {
        Expr::App(callee, unit) => (*callee, *unit),
        _ => panic!("expected var read to apply get to unit"),
    };
    let (receiver_expr, select) = match session.poly.expr(callee) {
        Expr::Select(receiver_expr, select) => (*receiver_expr, *select),
        _ => panic!("expected var read callee to be get selection"),
    };
    let receiver_ref = expr_ref(&session, receiver_expr);

    assert_eq!(session.poly.ref_target(receiver_ref), Some(target));
    assert_eq!(session.poly.select(select).name, "get");
    assert!(matches!(session.poly.expr(unit), Expr::Lit(Lit::Unit)));
}

#[test]
fn top_level_dollar_binding_reports_scope_error() {
    let root = parse("my $x = 1\nmy got = $x\n");
    let lower = lower_module_map(&root);
    let output = lower_binding_bodies(&root, lower);

    assert!(
        output.errors.iter().any(|error| matches!(
            error,
            BodyLoweringError::Expr {
                error: LoweringError::UnsupportedTopLevelVarBinding { name, .. },
                ..
            } if name == &Name("$x".into())
        )),
        "expected top-level dollar binding diagnostic, got {:?}",
        output.errors
    );
    assert!(
        !output.errors.iter().any(|error| matches!(
            error,
            BodyLoweringError::Expr {
                error: LoweringError::UnresolvedName { name, .. },
                ..
            } if name == &Name("&x".into())
        )),
        "top-level dollar binding should not cascade to unresolved &x: {:?}",
        output.errors
    );
}

#[test]
fn assign_tail_lowers_to_ref_set() {
    let root = parse("my &x = 1\nmy set = &x = 2\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (target, _) = binding_def_and_order(&lower.modules, module, "&x");
    let (set, _) = binding_def_and_order(&lower.modules, module, "set");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, set);
    let (reference_expr, value_expr) = match output.session.poly.expr(body) {
        Expr::RefSet(reference_expr, value_expr) => (*reference_expr, *value_expr),
        _ => panic!("expected assignment to lower to ref set"),
    };
    let reference = expr_ref(&output.session, reference_expr);

    assert_eq!(output.session.poly.ref_target(reference), Some(target));
    assert!(matches!(
        output.session.poly.expr(value_expr),
        Expr::Lit(Lit::Int(2))
    ));
}

#[test]
fn block_lowers_local_binding_and_tail_reference() {
    let root = parse("my f =\n  my x = 1\n  x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, f);
    let (stmts, tail) = match output.session.poly.expr(body) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected block body"),
    };
    let [Stmt::Let(_, pat, value)] = stmts.as_slice() else {
        panic!("expected one local let");
    };
    let local = match output.session.poly.pat(*pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected local binding pattern"),
    };
    assert!(matches!(
        output.session.poly.expr(*value),
        Expr::Lit(Lit::Int(1))
    ));
    let tail_ref = expr_ref(&output.session, tail);

    assert_eq!(output.session.poly.ref_target(tail_ref), Some(local));
}

#[test]
fn apply_colon_indent_block_lowers_block_as_argument() {
    let root = parse("my id x = x\nmy got = id:\n  my x = 1\n  x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (id, _) = binding_def_and_order(&lower.modules, module, "id");
    let (got, _) = binding_def_and_order(&lower.modules, module, "got");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, got);
    let (callee, arg) = match output.session.poly.expr(body) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected apply-colon body to lower as app"),
    };
    let callee_ref = expr_ref(&output.session, callee);
    assert_eq!(output.session.poly.ref_target(callee_ref), Some(id));
    let (stmts, tail) = match output.session.poly.expr(arg) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected apply-colon argument to be a block"),
    };
    let [Stmt::Let(_, pat, value)] = stmts.as_slice() else {
        panic!("expected one local let in argument block");
    };
    let local = match output.session.poly.pat(*pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected local pattern"),
    };
    assert!(matches!(
        output.session.poly.expr(*value),
        Expr::Lit(Lit::Int(1))
    ));
    let tail_ref = expr_ref(&output.session, tail);
    assert_eq!(output.session.poly.ref_target(tail_ref), Some(local));
}

#[test]
fn dollar_binding_lowers_to_var_ref_and_run_wrapper() {
    let root = parse(concat!(
        "mod std:\n",
        "  mod data:\n",
        "    mod list:\n",
        "      type list 'a\n",
        "  mod control:\n",
        "    mod var:\n",
        "      type ref 'e 'a with:\n",
        "        our r.get = r\n",
        "      act var 't:\n",
        "        pub get: () -> 't\n",
        "        pub set: 't -> ()\n",
        "        my var_ref() = 0\n",
        "        my run(v: 't, x: [_] 'r): 'r = catch x:\n",
        "          get(), k -> run v: k v\n",
        "          set v, k -> run v: k()\n",
        "use std::data::list::*\n",
        "my f =\n",
        "  my $x = [1]\n",
        "  $x\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let std = lower.modules.module_decls(module, &Name("std".into()))[0].module;
    let control = lower.modules.module_decls(std, &Name("control".into()))[0].module;
    let var_module = lower.modules.module_decls(control, &Name("var".into()))[0].module;
    let std_var_companion = lower.modules.module_decls(var_module, &Name("var".into()))[0].module;
    let std_var_ref = lower
        .modules
        .value_decls(std_var_companion, &Name("var_ref".into()))[0]
        .def;
    let std_run = lower
        .modules
        .value_decls(std_var_companion, &Name("run".into()))[0]
        .def;
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");
    let local_var_act = lower.modules.synthetic_var_act_uses(f)[0].clone();
    assert_eq!(local_var_act.source, Name("&x".into()));
    let local_var_companion = lower.modules.type_companion(local_var_act.act).unwrap();
    let var_ref = lower
        .modules
        .value_decls(local_var_companion, &Name("var_ref".into()))[0]
        .def;
    let run = lower
        .modules
        .value_decls(local_var_companion, &Name("run".into()))[0]
        .def;
    assert_ne!(var_ref, std_var_ref);
    assert_ne!(run, std_run);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let run_rendered =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, run));
    let local_effect = local_effect_item_fragment(&run_rendered, "&x#")
        .unwrap_or_else(|| panic!("missing local var effect row item: {run_rendered}"));
    assert!(
        local_effect.contains(' '),
        "local var handler row item lost its payload: {run_rendered}"
    );
    let body = binding_body_id(&output, f);
    let (first_stmts, after_init) = match output.session.poly.expr(body) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected outer block"),
    };
    let [Stmt::Let(_, init_pat, init_expr)] = first_stmts.as_slice() else {
        panic!("expected init let");
    };
    let init_def = match output.session.poly.pat(*init_pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected init binding pattern"),
    };
    let _ = output.session.poly.expr(*init_expr);
    let _ = def_scheme(&output, init_def);

    let (second_stmts, wrapped) = match output.session.poly.expr(after_init) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected reference block"),
    };
    let [Stmt::Let(_, reference_pat, reference_expr)] = second_stmts.as_slice() else {
        panic!("expected reference let");
    };
    assert!(matches!(
        output.session.poly.pat(*reference_pat),
        Pat::Var(_)
    ));
    let reference_def = match output.session.poly.pat(*reference_pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected reference binding pattern"),
    };
    let reference_rendered =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, reference_def));
    assert!(
        reference_rendered.contains("std::data::list::list") && reference_rendered.contains("int"),
        "reference scheme did not keep the initializer type: {reference_rendered}"
    );
    assert!(def_scheme(&output, reference_def).quantifiers.is_empty());
    let (var_ref_callee, _) = match output.session.poly.expr(*reference_expr) {
        Expr::App(callee, _unit) => (*callee, *_unit),
        _ => panic!("expected var_ref call"),
    };
    let var_ref_ref = expr_ref(&output.session, var_ref_callee);
    assert_eq!(output.session.poly.ref_target(var_ref_ref), Some(var_ref));

    let (run_with_init, _) = match output.session.poly.expr(wrapped) {
        Expr::App(callee, _body) => (*callee, *_body),
        _ => panic!("expected run application"),
    };
    let (run_expr, init_arg) = match output.session.poly.expr(run_with_init) {
        Expr::App(callee, init) => (*callee, *init),
        _ => panic!("expected run init application"),
    };
    let run_ref = expr_ref(&output.session, run_expr);
    assert_eq!(output.session.poly.ref_target(run_ref), Some(run));
    let init_ref = expr_ref(&output.session, init_arg);
    assert_eq!(output.session.poly.ref_target(init_ref), Some(init_def));
}

#[test]
fn synthetic_var_act_copy_methods_do_not_get_source_spans() {
    let root = parse(concat!(
        "mod std:\n",
        "  mod control:\n",
        "    mod var:\n",
        "      type ref 'e 'a with:\n",
        "        our r.get = r\n",
        "      act var 't:\n",
        "        my var_ref() = 0\n",
        "        my run v x = x\n",
        "my f =\n",
        "  my $x = 1\n",
        "  $x\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");
    let local_var_act = lower.modules.synthetic_var_act_uses(f)[0].clone();
    let var_ref = act_member_def(&lower.modules, local_var_act.act, "var_ref");
    let run = act_member_def(&lower.modules, local_var_act.act, "run");

    assert_eq!(lower.modules.def_source_span(var_ref), None);
    assert_eq!(lower.modules.def_source_span(run), None);
}

#[test]
fn dollar_binding_inside_tuple_pattern_lowers_to_var_ref_and_run_wrapper() {
    let root = parse(concat!(
        "mod std:\n",
        "  mod control:\n",
        "    mod var:\n",
        "      type ref 'e 'a with:\n",
        "        our r.get = r\n",
        "      act var 't:\n",
        "        my var_ref() = 0\n",
        "        my run v x = x\n",
        "my f =\n",
        "  my (x, $y) = (1, 2)\n",
        "  $y\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");
    let local_var_act = lower.modules.synthetic_var_act_uses(f)[0].clone();
    assert_eq!(local_var_act.source, Name("&y".into()));
    let var_ref = act_member_def(&lower.modules, local_var_act.act, "var_ref");
    let run = act_member_def(&lower.modules, local_var_act.act, "run");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, f);
    let (destructure_stmts, after_destructure) = match output.session.poly.expr(body) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected destructure block"),
    };
    let [Stmt::Let(_, pat, _)] = destructure_stmts.as_slice() else {
        panic!("expected destructuring let");
    };
    let init_def = match output.session.poly.pat(*pat) {
        Pat::Tuple(items) => match output.session.poly.pat(items[1]) {
            Pat::Var(def) => *def,
            _ => panic!("expected mutable tuple item to bind init local"),
        },
        _ => panic!("expected tuple pattern"),
    };

    let (reference_stmts, wrapped) = match output.session.poly.expr(after_destructure) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected reference block"),
    };
    let [Stmt::Let(_, _, reference_expr)] = reference_stmts.as_slice() else {
        panic!("expected reference let");
    };
    let var_ref_callee = match output.session.poly.expr(*reference_expr) {
        Expr::App(callee, _) => *callee,
        _ => panic!("expected var_ref call"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, var_ref_callee)),
        Some(var_ref)
    );

    let run_with_init = match output.session.poly.expr(wrapped) {
        Expr::App(callee, _) => *callee,
        _ => panic!("expected run application"),
    };
    let (run_expr, init_arg) = match output.session.poly.expr(run_with_init) {
        Expr::App(callee, init) => (*callee, *init),
        _ => panic!("expected run init application"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, run_expr)),
        Some(run)
    );
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, init_arg)),
        Some(init_def)
    );
}

#[test]
fn dollar_binding_inside_lambda_pattern_lowers_to_var_ref_and_run_wrapper() {
    let root = parse(concat!(
        "mod std:\n",
        "  mod control:\n",
        "    mod var:\n",
        "      type ref 'e 'a with:\n",
        "        our r.get = r\n",
        "      act var 't:\n",
        "        my var_ref() = 0\n",
        "        my run v x = x\n",
        "my f($x) = $x\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");
    let local_var_act = lower.modules.synthetic_var_act_uses(f)[0].clone();
    assert_eq!(local_var_act.source, Name("&x".into()));
    let var_ref = act_member_def(&lower.modules, local_var_act.act, "var_ref");
    let run = act_member_def(&lower.modules, local_var_act.act, "run");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, f);
    let (init_def, lambda_body) = match output.session.poly.expr(body) {
        Expr::Lambda(pat, body) => {
            let init_def = match output.session.poly.pat(*pat) {
                Pat::Var(def) => *def,
                _ => panic!("expected mutable lambda parameter to bind init local"),
            };
            (init_def, *body)
        }
        _ => panic!("expected lambda body"),
    };
    assert_var_pattern_body_wrapper(&output, lambda_body, init_def, var_ref, run);
}

#[test]
fn dollar_binding_inside_case_pattern_lowers_to_var_ref_and_run_wrapper() {
    let root = parse(concat!(
        "mod std:\n",
        "  mod control:\n",
        "    mod var:\n",
        "      type ref 'e 'a with:\n",
        "        our r.get = r\n",
        "      act var 't:\n",
        "        my var_ref() = 0\n",
        "        my run v x = x\n",
        "my f x = case x:\n",
        "  $y -> $y\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");
    let local_var_act = lower.modules.synthetic_var_act_uses(f)[0].clone();
    assert_eq!(local_var_act.source, Name("&y".into()));
    let var_ref = act_member_def(&lower.modules, local_var_act.act, "var_ref");
    let run = act_member_def(&lower.modules, local_var_act.act, "run");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, f);
    let case_body = match output.session.poly.expr(body) {
        Expr::Lambda(_, body) => *body,
        _ => panic!("expected function lambda"),
    };
    let arms = match output.session.poly.expr(case_body) {
        Expr::Case(_, arms) => arms,
        _ => panic!("expected case body"),
    };
    let [arm] = arms.as_slice() else {
        panic!("expected one case arm");
    };
    let init_def = match output.session.poly.pat(arm.pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected mutable case pattern to bind init local"),
    };
    assert_var_pattern_body_wrapper(&output, arm.body, init_def, var_ref, run);
}

#[test]
fn dollar_binding_inside_catch_value_pattern_lowers_to_var_ref_and_run_wrapper() {
    let root = parse(concat!(
        "mod std:\n",
        "  mod control:\n",
        "    mod var:\n",
        "      type ref 'e 'a with:\n",
        "        our r.get = r\n",
        "      act var 't:\n",
        "        my var_ref() = 0\n",
        "        my run v x = x\n",
        "my f x = catch x:\n",
        "  $y -> $y\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");
    let local_var_act = lower.modules.synthetic_var_act_uses(f)[0].clone();
    assert_eq!(local_var_act.source, Name("&y".into()));
    let var_ref = act_member_def(&lower.modules, local_var_act.act, "var_ref");
    let run = act_member_def(&lower.modules, local_var_act.act, "run");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, f);
    let catch_body = match output.session.poly.expr(body) {
        Expr::Lambda(_, body) => *body,
        _ => panic!("expected function lambda"),
    };
    let arms = match output.session.poly.expr(catch_body) {
        Expr::Catch(_, arms) => arms,
        _ => panic!("expected catch body"),
    };
    let [arm] = arms.as_slice() else {
        panic!("expected one catch arm");
    };
    let init_def = match output.session.poly.pat(arm.pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected mutable catch pattern to bind init local"),
    };
    assert_var_pattern_body_wrapper(&output, arm.body, init_def, var_ref, run);
}

#[test]
fn dollar_binding_synthetic_act_is_scoped_by_owner_def() {
    let root = parse(concat!(
        "mod std:\n",
        "  mod control:\n",
        "    mod var:\n",
        "      type ref 'e 'a with:\n",
        "        our r.get = r\n",
        "      act var 't:\n",
        "        my var_ref() = 0\n",
        "        my run v x = x\n",
        "my f =\n",
        "  my $x = 1\n",
        "  $x\n",
        "my g =\n",
        "  my $x = 2\n",
        "  $x\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");
    let (g, _) = binding_def_and_order(&lower.modules, module, "g");
    let f_act = lower.modules.synthetic_var_act_uses(f)[0].clone();
    let g_act = lower.modules.synthetic_var_act_uses(g)[0].clone();
    assert_eq!(f_act.source, Name("&x".into()));
    assert_eq!(g_act.source, Name("&x".into()));
    assert_ne!(f_act.act, g_act.act);
    let f_var_ref = act_member_def(&lower.modules, f_act.act, "var_ref");
    let f_run = act_member_def(&lower.modules, f_act.act, "run");
    let g_var_ref = act_member_def(&lower.modules, g_act.act, "var_ref");
    let g_run = act_member_def(&lower.modules, g_act.act, "run");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert_eq!(
        dollar_binding_method_targets(&output, f),
        (f_var_ref, f_run)
    );
    assert_eq!(
        dollar_binding_method_targets(&output, g),
        (g_var_ref, g_run)
    );
}

fn act_member_def(modules: &ModuleTable, act: TypeDeclId, member: &str) -> DefId {
    let companion = modules.type_companion(act).expect("synthetic companion");
    modules.value_decls(companion, &Name(member.into()))[0].def
}

fn dollar_binding_method_targets(output: &BodyLowering, owner: DefId) -> (DefId, DefId) {
    let body = binding_body_id(output, owner);
    let (_, after_init) = match output.session.poly.expr(body) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected outer block"),
    };
    let (second_stmts, wrapped) = match output.session.poly.expr(after_init) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected reference block"),
    };
    let [Stmt::Let(_, _, reference_expr)] = second_stmts.as_slice() else {
        panic!("expected reference let");
    };
    let var_ref_callee = match output.session.poly.expr(*reference_expr) {
        Expr::App(callee, _) => *callee,
        _ => panic!("expected var_ref call"),
    };
    let var_ref = output
        .session
        .poly
        .ref_target(expr_ref(&output.session, var_ref_callee))
        .expect("var_ref target");
    let run_with_init = match output.session.poly.expr(wrapped) {
        Expr::App(callee, _) => *callee,
        _ => panic!("expected run application"),
    };
    let run_expr = match output.session.poly.expr(run_with_init) {
        Expr::App(callee, _) => *callee,
        _ => panic!("expected run init application"),
    };
    let run = output
        .session
        .poly
        .ref_target(expr_ref(&output.session, run_expr))
        .expect("run target");
    (var_ref, run)
}

fn assert_var_pattern_body_wrapper(
    output: &BodyLowering,
    body: poly::expr::ExprId,
    init_def: DefId,
    var_ref: DefId,
    run: DefId,
) {
    let (reference_stmts, wrapped) = match output.session.poly.expr(body) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected reference block"),
    };
    let [Stmt::Let(_, _, reference_expr)] = reference_stmts.as_slice() else {
        panic!("expected reference let");
    };
    let var_ref_callee = match output.session.poly.expr(*reference_expr) {
        Expr::App(callee, _) => *callee,
        _ => panic!("expected var_ref call"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, var_ref_callee)),
        Some(var_ref)
    );

    let run_with_init = match output.session.poly.expr(wrapped) {
        Expr::App(callee, _) => *callee,
        _ => panic!("expected run application"),
    };
    let (run_expr, init_arg) = match output.session.poly.expr(run_with_init) {
        Expr::App(callee, init) => (*callee, *init),
        _ => panic!("expected run init application"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, run_expr)),
        Some(run)
    );
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, init_arg)),
        Some(init_def)
    );
}

#[test]
fn field_tail_lowers_to_deferred_selection_and_final_record_fallback() {
    let root = parse("my get = \\x -> x.foo\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, _) = binding_def_and_order(&lower.modules, module, "get");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, owner);
    let lambda_body = match output.session.poly.expr(body) {
        Expr::Lambda(_, body) => *body,
        _ => panic!("expected lambda body"),
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
fn field_tail_absorbs_qualified_method_path() {
    let root = parse("my get = \\x -> x.foo::bar::baz\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, _) = binding_def_and_order(&lower.modules, module, "get");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let body = binding_body_id(&output, owner);
    let lambda_body = match output.session.poly.expr(body) {
        Expr::Lambda(_, body) => *body,
        _ => panic!("expected lambda body"),
    };
    let select = match output.session.poly.expr(lambda_body) {
        Expr::Select(_, select) => *select,
        _ => panic!("expected select expr"),
    };
    assert_eq!(output.session.poly.select(select).name, "foo::bar::baz");
}

#[test]
fn struct_field_lowers_to_value_method_selection() {
    let root = parse("struct User { age: int }\nmy u: User = 1\nmy got = u.age\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let user = lower.modules.type_decls(module, &Name("User".into()))[0].clone();
    let method = type_field_method(&lower.modules, user.id, "age", TypeMethodReceiver::Value);
    let (got, _) = binding_def_and_order(&lower.modules, module, "got");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let method_scheme = def_scheme(&output, method.def);
    let Pos::Fun { ret, .. } = output.session.poly.typ.pos(method_scheme.predicate) else {
        panic!("expected field method function scheme");
    };
    assert!(matches!(
        output.session.poly.typ.pos(*ret),
        Pos::Con(path, args) if path == &vec!["int".to_string()] && args.is_empty()
    ));
    let got_body = binding_body_id(&output, got);
    let select = match output.session.poly.expr(got_body) {
        Expr::Select(_, select) => *select,
        _ => panic!("expected struct field select"),
    };
    assert_eq!(
        output.session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method.def })
    );
}

#[test]
fn struct_field_ref_assignment_lowers_to_ref_method_selection() {
    let root = parse(concat!(
        "mod std:\n",
        "  mod control:\n",
        "    mod var:\n",
        "      type ref 'e 'a\n",
        "struct User { age: int }\n",
        "my &u: std::control::var::ref 'e User = 1\n",
        "my set = &u.age = 2\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let user = lower.modules.type_decls(module, &Name("User".into()))[0].clone();
    let method = type_field_method(&lower.modules, user.id, "age", TypeMethodReceiver::Ref);
    let (set, _) = binding_def_and_order(&lower.modules, module, "set");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let method_scheme = def_scheme(&output, method.def);
    let Pos::Fun { ret, .. } = output.session.poly.typ.pos(method_scheme.predicate) else {
        panic!("expected ref field method function scheme");
    };
    assert!(matches!(
        output.session.poly.typ.pos(*ret),
        Pos::Con(path, args)
            if path == &crate::std_paths::control_var_ref_type() && args.len() == 2
    ));
    let set_body = binding_body_id(&output, set);
    let (reference_expr, value_expr) = match output.session.poly.expr(set_body) {
        Expr::RefSet(reference_expr, value_expr) => (*reference_expr, *value_expr),
        _ => panic!("expected field assignment to lower to ref set"),
    };
    let select = match output.session.poly.expr(reference_expr) {
        Expr::Select(_, select) => *select,
        _ => panic!("expected assignment target to be a field select"),
    };

    assert_eq!(
        output.session.poly.select(select).resolution,
        Some(SelectResolution::Method { def: method.def })
    );
    assert!(matches!(
        output.session.poly.expr(value_expr),
        Expr::Lit(Lit::Int(2))
    ));
}

#[test]
fn type_with_value_method_lowers_in_companion_and_resolves_selection() {
    let root = parse("type User with:\n  our x.id = x\nmy u: User = 1\nmy got = u.id\n");
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
fn user_error_throw_method_preserves_declared_error_effect() {
    let root = parse(concat!(
        "mod std:\n",
        "  pub mod control:\n",
        "    pub mod throw:\n",
        "      pub role Throw 'e:\n",
        "        type throws\n",
        "        pub e.throw: [throws] never\n",
        "error my_err:\n",
        "  boom int\n",
        "my f(p: int): [my_err] int = (my_err::boom p).throw\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, f));
    assert!(
        rendered.contains("int -> [my_err] int"),
        "error throw should keep the declared effect, got {rendered}"
    );
}

#[test]
fn user_error_throw_method_infers_error_effect_without_annotation() {
    let root = parse(concat!(
        "mod std:\n",
        "  pub mod control:\n",
        "    pub mod throw:\n",
        "      pub role Throw 'e:\n",
        "        type throws\n",
        "        pub e.throw: [throws] never\n",
        "error my_err:\n",
        "  boom int\n",
        "my f(p: int) = (my_err::boom p).throw\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, f));
    assert!(
        rendered.contains("int -> [my_err]"),
        "error throw should infer the thrown effect, got {rendered}"
    );
}
