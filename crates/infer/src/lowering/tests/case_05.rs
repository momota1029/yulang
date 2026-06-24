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
    assert_eq!(rendered, "'a -> ('a -> ['b] 'c) -> ['b] 'c");
}

#[test]
fn earlier_unannotated_callback_return_effect_surfaces_in_later_param_body() {
    let root = parse("my k(g, y) = g y\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (k, _) = binding_def_and_order(&lower.modules, module, "k");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, k));
    assert_eq!(rendered, "('a -> ['b] 'c) -> 'a -> ['b] 'c");
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
fn callback_effect_annotation_records_explicit_contract_metadata() {
    let root = parse("type loop\nmy h(f: _ -> [loop; 'e] _) = f 0\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (h, _) = binding_def_and_order(&lower.modules, module, "h");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let param = first_lambda_param_def(&output, h);
    let contract = output
        .session
        .poly
        .arg_effect_contracts
        .get(&param)
        .expect("callback annotation should record an explicit effect contract");
    assert_eq!(
        contract.markers,
        vec![poly::expr::ArgEffectContractMarker {
            path: vec!["loop".to_string()],
            depth: 1,
            resume: poly::expr::ContractResumePolicy::PreserveMatchingPath,
        }]
    );
}

#[test]
fn computation_effect_annotation_does_not_record_callback_contract_metadata() {
    let root = parse("type handled\nmy h(x: [handled; 'e] _) = x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (h, _) = binding_def_and_order(&lower.modules, module, "h");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let param = first_lambda_param_def(&output, h);
    assert!(
        !output
            .session
            .poly
            .arg_effect_contracts
            .contains_key(&param),
        "root computation annotations are handled by stack constraints, not callback contract metadata"
    );
}

#[test]
fn recursive_loop_for_in_callback_annotation_terminates() {
    let root = parse(concat!(
        "mod std:\n",
        "  mod control:\n",
        "    mod junction:\n",
        "      pub mod junction:\n",
        "        pub junction x = x\n",
        "  mod data:\n",
        "    mod fold:\n",
        "      pub role Fold 'container:\n",
        "        type item\n",
        "        pub container.fold: 'acc -> ('acc -> ['e] item -> ['e] 'acc) -> ['e] 'acc\n",
        "act loop:\n",
        "  pub last: () -> never\n",
        "  pub next: () -> never\n",
        "  pub redo: () -> never\n",
        "  my act last:\n",
        "    our break: () -> never\n",
        "    our judge(x: [_] _) = catch x { break(), _ -> true, _ -> false }\n",
        "    our sub(x: [_] _) = catch x { break(), _ -> (), _ -> () }\n",
        "  my act next = last\n",
        "  my act redo = last\n",
        "  pub for_in(xs: 'container, f: _ -> [loop; 'e] _): ['e] () =\n",
        "    where 'container: std::data::fold::Fold 'item\n",
        "    last::sub:xs.fold (): \\() x -> next::sub:loop true with:\n",
        "      our loop b = if b: loop:redo::judge:catch f x:\n",
        "        last(), _ -> last::break()\n",
        "        next(), _ -> next::break()\n",
        "        redo(), _ -> redo::break()\n",
        "        loop::last(), _ -> last::break()\n",
        "        loop::next(), _ -> next::break()\n",
        "        loop::redo(), _ -> redo::break()\n",
    ));
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
}

#[test]
fn parser_choice_callback_annotation_terminates() {
    let root = parse(concat!(
        "act parse 'item 'err 'pos 'snap:\n",
        "  pub fail: 'err -> never\n",
        "  pub cut: () -> ()\n",
        "  pub snapshot: () -> 'snap\n",
        "  pub restore: 'snap -> ()\n",
        "role ParseError 'err:\n",
        "  pub e.merge: 'err -> 'err\n",
        "pub choice(p: () -> [parse 'item 'err 'pos 'snap] 'a, q: () -> [parse 'item 'err 'pos 'snap] 'a, ()): [parse 'item 'err 'pos 'snap] 'a =\n",
        "  my snap = parse::snapshot()\n",
        "  catch p():\n",
        "    parse::cut(), k ->\n",
        "      parse::cut()\n",
        "      catch k(): parse::fail e, _ -> parse::fail e\n",
        "    parse::fail e1, _ ->\n",
        "      parse::restore snap\n",
        "      catch q(): parse::fail e2, _ -> parse::fail: e1.merge e2\n",
    ));
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
}

#[test]
fn result_annotation_rejects_function_value_body() {
    let root = parse("my bad(): int = \\() -> 1\n");
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(
        output.errors.iter().any(|error| {
            matches!(
                error,
                BodyLoweringError::Expr {
                    name,
                    error:
                        LoweringError::SignatureTypeMismatch {
                            expected: SignatureShape::Constructor,
                        },
                    ..
                } if name == &Name("bad".into())
            )
        }),
        "{:?}",
        output.errors
    );
}

#[test]
fn result_annotation_rejects_deferred_partial_application_body() {
    let root = parse(concat!(
        "my choose(p, q, ()): int = p()\n",
        "my bad(): int = choose(\\() -> 1, \\() -> 2)\n",
    ));
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(
        output.errors.iter().any(|error| {
            matches!(
                error,
                BodyLoweringError::Expr {
                    name,
                    error:
                        LoweringError::SignatureTypeMismatch {
                            expected: SignatureShape::Constructor,
                        },
                    ..
                } if name == &Name("bad".into())
            )
        }),
        "{:?}",
        output.errors
    );
}

#[test]
fn nested_callback_wildcard_return_contract_stays_surface() {
    let root = parse("pub full_compose(f: _ -> [_] _, g, x) = g f(x)\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (full_compose, _) = binding_def_and_order(&lower.modules, module, "full_compose");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, full_compose));
    assert_eq!(
        rendered,
        "('a -> ['b] 'c) -> ('c ['b] -> ['d] 'e) -> 'a -> ['d] 'e"
    );
    assert!(
        !rendered.contains("4294967295"),
        "annotation pop must not be rendered as the instantiate sentinel: {rendered}"
    );
}

#[test]
fn unannotated_compose_protects_callback_return_from_outer_callee() {
    let root = parse(concat!(
        "pub compose1(f, g: _ -> [_] _, x) = f g(x)\n",
        "pub compose2(f, g, x) = f g(x)\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (compose1, _) = binding_def_and_order(&lower.modules, module, "compose1");
    let (compose2, _) = binding_def_and_order(&lower.modules, module, "compose2");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let compose1 =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, compose1));
    let compose2 =
        poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, compose2));
    assert_eq!(
        compose1,
        "('a ['b] -> ['c] 'd) -> ('e -> ['b] 'a) -> 'e -> ['c] 'd"
    );
    assert_eq!(
        compose2,
        "('a ['b#0[Empty]] -> ['c] 'd) -> ('e -> ['b#0[Empty]] 'a) -> 'e -> ['c#0] 'd#0"
    );
}

#[test]
fn callback_empty_return_annotation_records_filter_upper() {
    let root = parse("my run(g: () -> [] int): [] int = g ()\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (run, _) = binding_def_and_order(&lower.modules, module, "run");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let root = output.typing.def(run).expect("run root type");
    let (arg, _, _, _) = function_lower_bound(&output.session, root);
    let types = output.session.infer.constraints().types();
    let Neg::Var(callback) = types.neg(arg) else {
        panic!("expected callback argument var, got {:?}", types.neg(arg));
    };
    let bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(*callback)
        .expect("callback should receive function upper");
    let ret_eff = bounds
        .uppers()
        .iter()
        .find_map(|bound| match types.neg(bound.neg) {
            Neg::Fun { ret_eff, .. } => Some(*ret_eff),
            _ => None,
        })
        .expect("callback upper should include function shape");
    let Neg::Stack { inner, weight } = types.neg(ret_eff) else {
        panic!(
            "expected filtered callback return effect upper, got {:?}",
            types.neg(ret_eff)
        );
    };
    assert!(matches!(types.neg(*inner), Neg::Var(_)));
    assert_eq!(weight.filter_set(), &Subtractability::Empty);
    assert!(
        weight.entries().is_empty(),
        "callback return effect upper should carry only filter, got {weight:?}"
    );
}

#[test]
fn effectful_parameter_forwarding_keeps_unhandled_effect() {
    let root = parse("type handled\nmy h(x: [handled; 'e] 'a) = x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (h, _) = binding_def_and_order(&lower.modules, module, "h");

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, h));
    assert!(
        rendered.contains("[handled; '"),
        "forwarding should keep handled in the result effect: {rendered}"
    );
    assert!(
        !rendered.contains("& [handled;"),
        "forwarding without catch must not become a shallow handler type: {rendered}"
    );
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
fn recursive_act_method_selection_passes_receiver_effect_as_argument_effect() {
    let root = parse(concat!(
        "act nondet:\n",
        "  pub branch: () -> bool\n",
        "  pub x.run = catch x:\n",
        "    branch(), k -> k(true).run\n",
        "    v -> v\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let nondet = lower
        .modules
        .type_path_at(
            module,
            &[Name("nondet".into())],
            ModuleOrder::from_index(u32::MAX),
        )
        .expect("nondet type");
    let run = lower.modules.act_methods(nondet.id)[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, run));
    assert!(
        rendered.contains(" [nondet; '"),
        "recursive act method should expose handled effect with an independent residual: {rendered}"
    );
    assert!(
        !rendered.contains("& [nondet;"),
        "recursive act method must not leak the receiver effect as a shallow handler: {rendered}"
    );
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
    let (arg, _, _, _) = function_lower_bound(&output.session, root);
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

    let has_public_predicate =
        reachable_function_lower_returns(&output.session, root).any(|(ret_eff, ret)| {
            find_pos_or_var_lower_stack_pop_var(&output.session, ret_eff, subtract).is_some()
                && find_pos_or_var_lower_stack_pop_var(&output.session, ret, subtract).is_some()
        });
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, h));
    assert!(
        has_public_predicate,
        "expected public function lower bound to carry late callback pop: {rendered}"
    );
}

fn reachable_function_lower_returns(
    session: &AnalysisSession,
    root: TypeVar,
) -> impl Iterator<Item = (PosId, PosId)> + '_ {
    let mut stack = vec![root];
    let mut visited = Vec::new();
    let mut out = Vec::new();
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
                Pos::Fun { ret_eff, ret, .. } => out.push((*ret_eff, *ret)),
                Pos::Var(next) if lower.weights.is_empty() => stack.push(*next),
                _ => {}
            }
        }
    }
    out.into_iter()
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

#[test]
fn local_sub_lambda_scheme_keeps_escaping_labeled_return_effect() {
    let root = parse(concat!(
        "mod std:\n",
        "  pub mod control:\n",
        "    pub mod flow:\n",
        "      pub act sub 'a:\n",
        "        pub return: 'a -> never\n",
        "        pub sub(x: [_] 'a): 'a = catch x:\n",
        "          return a, _ -> a\n",
        "          a -> a\n",
        "      pub act label_sub 'a:\n",
        "        pub return: 'a -> never\n",
        "        pub struct label { marker: unit }\n",
        "        our control_label = label { marker: () }\n",
        "        pub sub(x: [_] 'a): 'a = catch x:\n",
        "          return a, _ -> a\n",
        "          sub::return a, _ -> a\n",
        "          a -> a\n",
        "sub 'outer:\n",
        "  my f = \\sub 'inner x -> 'outer.return x\n",
        "  f 7\n",
        "  'outer.return 1\n",
    ));
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let outer_body = output
        .session
        .poly
        .root_exprs
        .first()
        .copied()
        .expect("root expr");
    let f_def = first_let_def_in_expr(&output.session.poly, outer_body);
    let rendered = poly::dump::format_scheme(&output.session.poly.typ, def_scheme(&output, f_def));

    assert!(
        rendered.contains("#sub_label:outer"),
        "escaping labeled return effect should remain in f scheme, got {rendered}"
    );
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

fn first_let_def_in_expr(poly: &poly::expr::Arena, expr: ExprId) -> DefId {
    maybe_first_let_def_in_expr(poly, expr).expect("expected local let")
}

fn maybe_first_let_def_in_expr(poly: &poly::expr::Arena, expr: ExprId) -> Option<DefId> {
    match poly.expr(expr) {
        Expr::Block(stmts, tail) => first_let_def_in_stmts(poly, stmts)
            .or_else(|| tail.and_then(|tail| maybe_first_let_def_in_expr(poly, tail))),
        Expr::App(callee, arg) | Expr::RefSet(callee, arg) => {
            maybe_first_let_def_in_expr(poly, *callee)
                .or_else(|| maybe_first_let_def_in_expr(poly, *arg))
        }
        Expr::Lambda(_, body) => maybe_first_let_def_in_expr(poly, *body),
        Expr::Tuple(items) => first_let_def_in_exprs(poly, items),
        Expr::Record { fields, spread } => fields
            .iter()
            .map(|(_, expr)| *expr)
            .find_map(|expr| maybe_first_let_def_in_expr(poly, expr))
            .or_else(|| match spread {
                RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                    maybe_first_let_def_in_expr(poly, *expr)
                }
                RecordSpread::None => None,
            }),
        Expr::PolyVariant(_, payloads) => first_let_def_in_exprs(poly, payloads),
        Expr::Select(receiver, _) => maybe_first_let_def_in_expr(poly, *receiver),
        Expr::Case(scrutinee, arms) => {
            maybe_first_let_def_in_expr(poly, *scrutinee).or_else(|| {
                arms.iter().find_map(|arm| {
                    arm.guard
                        .and_then(|guard| maybe_first_let_def_in_expr(poly, guard))
                        .or_else(|| maybe_first_let_def_in_expr(poly, arm.body))
                })
            })
        }
        Expr::Catch(scrutinee, arms) => {
            maybe_first_let_def_in_expr(poly, *scrutinee).or_else(|| {
                arms.iter().find_map(|arm| {
                    arm.guard
                        .and_then(|guard| maybe_first_let_def_in_expr(poly, guard))
                        .or_else(|| maybe_first_let_def_in_expr(poly, arm.body))
                })
            })
        }
        Expr::Lit(_) | Expr::PrimitiveOp(_) | Expr::Var(_) => None,
    }
}

fn first_let_def_in_stmts(poly: &poly::expr::Arena, stmts: &[Stmt]) -> Option<DefId> {
    stmts.iter().find_map(|stmt| match stmt {
        Stmt::Let(_, pat, _) => match poly.pat(*pat) {
            Pat::Var(def) => Some(*def),
            _ => None,
        },
        Stmt::Expr(expr) => maybe_first_let_def_in_expr(poly, *expr),
        Stmt::Module(_, stmts) => first_let_def_in_stmts(poly, stmts),
    })
}

fn first_let_def_in_exprs(poly: &poly::expr::Arena, exprs: &[ExprId]) -> Option<DefId> {
    exprs
        .iter()
        .find_map(|expr| maybe_first_let_def_in_expr(poly, *expr))
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
fn lambda_param_effect_annotation_exposes_row_arg_effect_without_subtracting_body() {
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
    let Neg::Intersection(full, row) = types.neg(arg_eff) else {
        panic!(
            "expected full effect and row intersection, got {:?}",
            types.neg(arg_eff)
        );
    };
    assert!(
        matches!(types.neg(*full), Neg::Var(_)),
        "expected full effect var, got {:?}",
        types.neg(*full)
    );
    let Neg::Row(items, _) = types.neg(*row) else {
        panic!("expected row arg effect, got {:?}", types.neg(*row));
    };
    assert!(
        items.iter().any(
            |item| matches!(types.neg(*item), Neg::Con(path, _) if path.as_slice() == ["handled"])
        ),
        "expected handled row item, got {:?}",
        items
    );
    assert!(
        !matches!(
            types.pos(ret_eff),
            Pos::Stack { .. } | Pos::NonSubtract(_, _)
        ),
        "ordinary forwarding should not subtract the parameter effect, got {:?}",
        types.pos(ret_eff)
    );
    assert!(
        !matches!(types.pos(ret), Pos::Stack { .. } | Pos::NonSubtract(_, _)),
        "ordinary forwarding should not wrap the result value in a subtract marker, got {:?}",
        types.pos(ret)
    );
}

#[test]
fn lambda_param_effect_annotation_with_tail_exposes_full_effect_and_row() {
    let root = parse("type handled\nmy f = \\x: [handled; 'e] 'a -> x\n");
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
    let arg_eff = bounds
        .lowers()
        .iter()
        .find_map(|bound| match types.pos(bound.pos) {
            Pos::Fun { arg_eff, .. } => Some(*arg_eff),
            _ => None,
        })
        .expect("lambda lower bound should be a function");
    let Neg::Intersection(full, row) = types.neg(arg_eff) else {
        panic!(
            "expected full effect and row intersection, got {:?}",
            types.neg(arg_eff)
        );
    };
    assert!(
        matches!(types.neg(*full), Neg::Var(_)),
        "expected full effect var, got {:?}",
        types.neg(*full)
    );
    let Neg::Row(items, tail) = types.neg(*row) else {
        panic!("expected annotated row, got {:?}", types.neg(*row));
    };
    assert!(
        items.iter().any(
            |item| matches!(types.neg(*item), Neg::Con(path, _) if path.as_slice() == ["handled"])
        ),
        "expected handled row item, got {:?}",
        items
    );
    let Neg::Var(_tail) = types.neg(*tail) else {
        panic!("expected row tail var, got {:?}", types.neg(*tail));
    };
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
fn bare_nullary_constructor_pattern_resolves_scope_reference() {
    let root = parse(concat!(
        "pub enum opt 'a = none | some 'a\n",
        "use opt::*\n",
        "my f = case none:\n",
        "  none -> 0\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let opt = lower.modules.type_decls(module, &Name("opt".into()))[0].id;
    let companion = lower.modules.type_companion(opt).expect("opt companion");
    let constructor = lower.modules.value_decls(companion, &Name("none".into()))[0].def;
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");

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

    assert!(payloads.is_empty());
    assert_eq!(output.session.poly.ref_target(reference), Some(constructor));
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
fn constructor_payload_name_can_match_unary_constructor_name() {
    let root = parse(concat!(
        "pub enum result 'ok 'err:\n",
        "  ok 'ok\n",
        "  err 'err\n",
        "my r = result::err 1\n",
        "my recover = case r:\n",
        "  result::ok value -> value\n",
        "  result::err err -> err\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (recover, _) = binding_def_and_order(&lower.modules, module, "recover");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let case = binding_body_id(&output, recover);
    let (_scrutinee, arms) = match output.session.poly.expr(case) {
        Expr::Case(scrutinee, arms) => (*scrutinee, arms),
        _ => panic!("expected case expr"),
    };
    let [_ok_arm, err_arm] = arms.as_slice() else {
        panic!("expected two case arms");
    };
    let [err_payload] = (match output.session.poly.pat(err_arm.pat) {
        Pat::Con(_, payloads) => payloads.as_slice(),
        _ => panic!("expected constructor pattern"),
    }) else {
        panic!("expected one constructor payload");
    };
    let err_local = match output.session.poly.pat(*err_payload) {
        Pat::Var(def) => *def,
        _ => panic!("expected constructor payload local"),
    };
    let body_ref = expr_ref(&output.session, err_arm.body);

    assert_eq!(output.session.poly.ref_target(body_ref), Some(err_local));
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
    assert_eq!(rendered, "view('a & 'b) -> 'b -> 'a where Ord('b | 'a)");
}

#[test]
fn do_binding_lowers_suffix_to_continuation_lambda() {
    let root = parse(concat!(
        "my f k = k 1\n",
        "my g =\n",
        "  my x = f(do)\n",
        "  x\n",
    ));
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let f = lower.modules.value_decls(module, &Name("f".into()))[0].def;
    let (g, _) = binding_def_and_order(&lower.modules, module, "g");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let body = binding_body_id(&output, g);
    let (callee, continuation) = match output.session.poly.expr(body) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected do binding to lower to application"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, callee)),
        Some(f)
    );

    let (param_pat, continuation_body) = match output.session.poly.expr(continuation) {
        Expr::Lambda(pat, body) => (*pat, *body),
        _ => panic!("expected do replacement to be a lambda"),
    };
    let param = match output.session.poly.pat(param_pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected do binding name to become lambda parameter"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, continuation_body)),
        Some(param)
    );
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

fn first_lambda_param_def(output: &BodyLowering, def: DefId) -> DefId {
    let body = binding_body_id(output, def);
    let Expr::Lambda(param, _) = output.session.poly.expr(body) else {
        panic!("expected lowered binding body to start with a lambda");
    };
    let Pat::Var(def) = output.session.poly.pat(*param) else {
        panic!("expected lambda parameter var pattern");
    };
    *def
}
