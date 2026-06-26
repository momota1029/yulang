use super::*;

#[test]
fn lower_loaded_files_with_prefix_preserves_cached_child_module_defs() {
    let prefix_loaded = sources::load(vec![
        source_file(&[], "mod a;\n"),
        source_file(&["a"], "mod b;\n"),
        source_file(&["a", "b"], "pub y = 7\n"),
    ]);
    let prefix = lower_loaded_files_prefix(&prefix_loaded).unwrap();
    let suffix_loaded = sources::load(vec![
        source_file(&[], "mod a;\n"),
        source_file(&["a"], "pub x = b::y\n"),
    ]);

    let output = lower_loaded_files_with_prefix(&prefix, &suffix_loaded).unwrap();

    assert_eq!(output.errors, Vec::new());
    let a_module = output.modules.module_by_path(&module_path(&["a"])).unwrap();
    let b_module = output
        .modules
        .module_by_path(&module_path(&["a", "b"]))
        .unwrap();
    let a_def = output.modules.module_def(a_module).unwrap();
    let b_def = output.modules.module_def(b_module).unwrap();
    match output.session.poly.defs.get(a_def) {
        Some(Def::Mod { children, .. }) => {
            assert!(
                children.contains(&b_def),
                "cached child module def should remain in parent children"
            );
        }
        _ => panic!("expected module def"),
    }
    let x = output
        .modules
        .value_path_at(
            output.modules.root_id(),
            &[Name("a".into()), Name("x".into())],
            ModuleOrder::from_index(u32::MAX),
        )
        .expect("suffix value should resolve through cached child module");
    binding_body_id(&output, x);
}

#[test]
fn catch_effect_arm_binds_payload_and_continuation_locals() {
    let root = parse("my run = 1\nmy f = catch run:\n  eff x, k -> k x\n  value -> value\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (f, _) = binding_def_and_order(&lower.modules, module, "f");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let catch = binding_body_id(&output, f);
    let (_body, arms) = match output.session.poly.expr(catch) {
        Expr::Catch(body, arms) => (*body, arms),
        _ => panic!("expected catch expr"),
    };
    let [effect_arm, value_arm] = arms.as_slice() else {
        panic!("expected effect arm followed by value arm");
    };
    let continuation = effect_arm
        .continuation
        .expect("expected effect arm continuation");
    assert!(value_arm.continuation.is_none());

    let payload = match output.session.poly.pat(effect_arm.pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected effect payload local"),
    };
    let continuation = match output.session.poly.pat(continuation) {
        Pat::Var(def) => *def,
        _ => panic!("expected continuation local"),
    };
    let (callee, arg) = match output.session.poly.expr(effect_arm.body) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected continuation application"),
    };
    let k_ref = expr_ref(&output.session, callee);
    let x_ref = expr_ref(&output.session, arg);
    let k_value = output
        .session
        .refs
        .value(k_ref)
        .expect("continuation ref value");

    assert_eq!(output.session.poly.ref_target(k_ref), Some(continuation));
    assert_eq!(output.session.poly.ref_target(x_ref), Some(payload));
    let bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(k_value)
        .expect("continuation should receive function bounds");
    let types = output.session.infer.constraints().types();
    assert!(
        bounds
            .lowers()
            .iter()
            .any(|bound| matches!(types.pos(bound.pos), Pos::Fun { .. }))
    );
    assert!(
        bounds
            .uppers()
            .iter()
            .any(|bound| matches!(types.neg(bound.neg), Neg::Fun { .. }))
    );
}

fn source_file(module: &[&str], source: &str) -> sources::SourceFile {
    sources::SourceFile {
        module_path: module_path(module),
        source: source.to_string(),
    }
}

fn module_path(module: &[&str]) -> sources::Path {
    sources::Path {
        segments: module
            .iter()
            .map(|segment| sources::Name((*segment).to_string()))
            .collect(),
    }
}

#[test]
fn catch_complete_effect_handler_flows_rest_effect_to_result() {
    let root = parse(
        "act out:\n  our say: int -> unit\nmy run = 1\nmy f = catch run:\n  out::say msg, k -> 0\n  value -> value\n",
    );
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    assert!(!effect_has_lower_source_with_row_upper(
        &session,
        computation.effect,
        &["out"],
    ));
}

#[test]
fn catch_incomplete_effect_handler_flows_scrutinee_effect_to_result() {
    let root = parse(
        "act choose:\n  our branch: unit -> int\n  our reject: unit -> never\nmy run = 1\nmy f = catch run:\n  choose::branch(), k -> 0\n  value -> value\n",
    );
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "f");
    let expr = binding_expr(&root, "f");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    assert!(effect_has_lower_source_with_row_upper(
        &session,
        computation.effect,
        &["choose"],
    ));
}

#[test]
fn body_lowering_keeps_lambda_local_refs_out_of_scc_edges() {
    let root = parse("my id = \\x -> x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (def, _) = binding_def_and_order(&lower.modules, module, "id");

    let mut output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let events = output.session.take_scc_events();
    assert!(events
        .iter()
        .any(|event| matches!(event, SccEvent::QuantifyComponent { component, .. } if component == &vec![def])));
    assert!(!events.iter().any(|event| {
        matches!(
            event,
            SccEvent::ComponentEdgeAdded { .. } | SccEvent::MergeComponents { .. }
        )
    }));
}

pub(super) fn expr_ref(session: &AnalysisSession, expr: poly::expr::ExprId) -> RefId {
    match session.poly.expr(expr) {
        Expr::Var(reference) => *reference,
        _ => panic!("expected var expr"),
    }
}

pub(super) fn recursive_self_block_parts(
    session: &AnalysisSession,
    expr: poly::expr::ExprId,
) -> (DefId, poly::expr::ExprId, poly::expr::ExprId) {
    let (stmts, tail) = match session.poly.expr(expr) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected recursive self block"),
    };
    let [Stmt::Let(_, self_pat, body)] = stmts.as_slice() else {
        panic!("expected recursive self let");
    };
    let self_def = match session.poly.pat(*self_pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected recursive self local"),
    };
    (self_def, *body, tail)
}

pub(super) fn lambda_body(
    session: &AnalysisSession,
    expr: poly::expr::ExprId,
) -> poly::expr::ExprId {
    match session.poly.expr(expr) {
        Expr::Lambda(_, body) => *body,
        _ => panic!("expected lambda expr"),
    }
}

pub(super) fn find_select_by_name(
    session: &AnalysisSession,
    expr: poly::expr::ExprId,
    name: &str,
) -> Option<SelectId> {
    let mut children = Vec::new();
    match session.poly.expr(expr) {
        Expr::Select(receiver, select) => {
            if session.poly.select(*select).name == name {
                return Some(*select);
            }
            children.push(*receiver);
        }
        Expr::App(callee, arg) | Expr::RefSet(callee, arg) => {
            children.push(*callee);
            children.push(*arg);
        }
        Expr::Lambda(_, body) => children.push(*body),
        Expr::Tuple(items) | Expr::PolyVariant(_, items) => {
            children.extend(items.iter().copied());
        }
        Expr::Record { fields, spread } => {
            children.extend(fields.iter().map(|(_, expr)| *expr));
            match spread {
                RecordSpread::Head(expr) | RecordSpread::Tail(expr) => children.push(*expr),
                RecordSpread::None => {}
            }
        }
        Expr::Case(scrutinee, arms) => {
            children.push(*scrutinee);
            children.extend(arms.iter().filter_map(|arm| arm.guard));
            children.extend(arms.iter().map(|arm| arm.body));
        }
        Expr::Catch(scrutinee, arms) => {
            children.push(*scrutinee);
            children.extend(arms.iter().filter_map(|arm| arm.guard));
            children.extend(arms.iter().map(|arm| arm.body));
        }
        Expr::Block(statements, tail) => {
            for statement in statements {
                match statement {
                    Stmt::Let(_, _, body) | Stmt::Expr(body) => children.push(*body),
                    Stmt::Module(_, body) => {
                        for statement in body {
                            match statement {
                                Stmt::Let(_, _, body) | Stmt::Expr(body) => {
                                    children.push(*body);
                                }
                                Stmt::Module(_, _) => {}
                            }
                        }
                    }
                }
            }
            if let Some(tail) = tail {
                children.push(*tail);
            }
        }
        Expr::Lit(_) | Expr::PrimitiveOp(_) | Expr::Var(_) => {}
    }
    children
        .into_iter()
        .find_map(|child| find_select_by_name(session, child, name))
}

pub(super) fn lambda_output(session: &AnalysisSession, value: TypeVar) -> (PosId, PosId) {
    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(value)
        .expect("lambda value should receive a function lower bound");
    let types = session.infer.constraints().types();
    bounds
        .lowers()
        .iter()
        .find_map(|bound| match types.pos(bound.pos) {
            Pos::Fun { ret_eff, ret, .. } => Some((*ret_eff, *ret)),
            _ => None,
        })
        .expect("lambda lower bound should be a function")
}

pub(super) fn function_result_effect(session: &AnalysisSession, value: TypeVar) -> TypeVar {
    let (ret_eff, _) = lambda_output(session, value);
    match session.infer.constraints().types().pos(ret_eff) {
        Pos::Stack { inner, .. } => match session.infer.constraints().types().pos(*inner) {
            Pos::Var(effect) => *effect,
            other => panic!("expected stacked result effect var, got {other:?}"),
        },
        Pos::NonSubtract(inner, _) => match session.infer.constraints().types().pos(*inner) {
            Pos::Var(effect) => *effect,
            other => panic!("expected non-subtract result effect var, got {other:?}"),
        },
        Pos::Var(effect) => *effect,
        other => panic!("expected result effect var, got {other:?}"),
    }
}

pub(super) fn assert_neg_bottom(types: &poly::types::TypeArena, row: NegId) {
    match types.neg(row) {
        Neg::Bot => {}
        other => panic!("expected negative bottom, got {other:?}"),
    }
}

pub(super) fn assert_role_arg_is_exact_con(
    session: &AnalysisSession,
    arg: &crate::roles::RoleConstraintArg,
    name: &str,
) {
    let types = session.infer.constraints().types();
    assert!(matches!(
        types.pos(arg.lower),
        Pos::Con(path, args) if path == &vec![name.to_string()] && args.is_empty()
    ));
    assert!(matches!(
        types.neg(arg.upper),
        Neg::Con(path, args) if path == &vec![name.to_string()] && args.is_empty()
    ));
}

pub(super) fn assert_var_has_exact_con_bound(session: &AnalysisSession, var: TypeVar, name: &str) {
    let types = session.infer.constraints().types();
    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(var)
        .expect("variable should receive bounds");
    assert!(bounds.lowers().iter().any(|bound| {
        matches!(
            types.pos(bound.pos),
            Pos::Con(path, args) if path == &vec![name.to_string()] && args.is_empty()
        )
    }));
    assert!(bounds.uppers().iter().any(|bound| {
        matches!(
            types.neg(bound.neg),
            Neg::Con(path, args) if path == &vec![name.to_string()] && args.is_empty()
        )
    }));
}

pub(super) fn assert_var_has_lower_con_bound(session: &AnalysisSession, var: TypeVar, name: &str) {
    let types = session.infer.constraints().types();
    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(var)
        .expect("variable should receive bounds");
    assert!(bounds.lowers().iter().any(|bound| {
        matches!(
            types.pos(bound.pos),
            Pos::Con(path, args) if path == &vec![name.to_string()] && args.is_empty()
        )
    }));
}

pub(super) fn assert_var_has_lower_con_path(
    session: &AnalysisSession,
    var: TypeVar,
    path: &[&str],
) {
    let expected = path
        .iter()
        .map(|segment| (*segment).to_string())
        .collect::<Vec<_>>();
    let types = session.infer.constraints().types();
    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(var)
        .expect("variable should receive bounds");
    assert!(bounds.lowers().iter().any(|bound| {
        matches!(
            types.pos(bound.pos),
            Pos::Con(path, args) if path == &expected && args.is_empty()
        )
    }));
}

pub(super) fn effect_has_lower_source_with_row_upper(
    session: &AnalysisSession,
    effect: TypeVar,
    path: &[&str],
) -> bool {
    let Some(bounds) = session.infer.constraints().bounds().of(effect) else {
        return false;
    };
    let types = session.infer.constraints().types();
    bounds.lowers().iter().any(|bound| {
        let Pos::Var(source) = types.pos(bound.pos) else {
            return false;
        };
        var_has_row_upper(session, *source, path)
    })
}

fn var_has_row_upper(session: &AnalysisSession, var: TypeVar, path: &[&str]) -> bool {
    let Some(bounds) = session.infer.constraints().bounds().of(var) else {
        return false;
    };
    let types = session.infer.constraints().types();
    bounds
        .uppers()
        .iter()
        .any(|bound| neg_row_contains_path(types, bound.neg, path))
}

fn neg_row_contains_path(types: &poly::types::TypeArena, neg: NegId, path: &[&str]) -> bool {
    let Neg::Row(items, _) = types.neg(neg) else {
        return false;
    };
    items.iter().any(|item| match types.neg(*item) {
        Neg::Con(found, args) => {
            args.is_empty()
                && found
                    .iter()
                    .map(|segment| segment.as_str())
                    .eq(path.iter().copied())
        }
        _ => false,
    })
}

#[test]
fn body_lowering_writes_let_body_and_def_type() {
    let root = parse("my a = 1\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (def, _) = binding_def_and_order(&lower.modules, module, "a");

    let mut output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let body = binding_body_id(&output, def);
    assert!(matches!(
        output.session.poly.expr(body),
        Expr::Lit(Lit::Int(1))
    ));
    assert!(output.typing.def(def).is_some());
    assert!(output
        .session
        .take_scc_events()
        .iter()
        .any(|event| matches!(event, SccEvent::QuantifyComponent { component, .. } if component == &vec![def])));
}

#[test]
fn body_lowering_resolves_references_after_queue_drain() {
    let root = parse("my a = 1\nmy b = a\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (target, _) = binding_def_and_order(&lower.modules, module, "a");
    let (owner, _) = binding_def_and_order(&lower.modules, module, "b");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let body = binding_body_id(&output, owner);
    let reference = expr_ref(&output.session, body);
    assert_eq!(output.session.poly.ref_target(reference), Some(target));
}

#[test]
fn body_lowering_resolves_import_alias_references_after_queue_drain() {
    let root = parse("mod m:\n  our a = 1\nuse m::a as imported\nmy b = imported\n");
    let lower = lower_module_map(&root);
    let root_module = lower.modules.root_id();
    let m = lower.modules.module_decls(root_module, &Name("m".into()))[0].module;
    let target = lower.modules.value_decls(m, &Name("a".into()))[0].def;
    let (owner, _) = binding_def_and_order(&lower.modules, root_module, "b");

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let body = binding_body_id(&output, owner);
    let reference = expr_ref(&output.session, body);
    assert_eq!(output.session.poly.ref_target(reference), Some(target));
}

#[test]
fn body_lowering_opens_self_recursion_from_registered_root() {
    let root = parse("my f = \\x -> f\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (def, _) = binding_def_and_order(&lower.modules, module, "f");

    let mut output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let def_root = output.typing.def(def).expect("def root");
    let body = binding_body_id(&output, def);
    let lambda_body = match output.session.poly.expr(body) {
        Expr::Lambda(_, body) => *body,
        _ => panic!("expected lambda body"),
    };
    let reference = expr_ref(&output.session, lambda_body);
    let use_value = output
        .session
        .refs
        .value(reference)
        .expect("self ref use value");
    let events = output.session.take_scc_events();
    assert!(events.iter().any(|event| {
        matches!(
            event,
            SccEvent::OpenUse {
                target,
                target_root,
                use_value: event_use,
            } if *target == def && *target_root == def_root && *event_use == use_value
        )
    }));

    let root_pos = output.session.infer.alloc_pos(Pos::Var(def_root));
    let use_bounds = output
        .session
        .infer
        .constraints()
        .bounds()
        .of(use_value)
        .expect("self ref use bounds");
    assert!(
        use_bounds
            .lowers()
            .iter()
            .any(|bound| bound.pos == root_pos)
    );
}

#[test]
fn body_lowering_keeps_forward_cycle_in_one_scc() {
    let root = parse("my a = b\nmy b = a\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (a, _) = binding_def_and_order(&lower.modules, module, "a");
    let (b, _) = binding_def_and_order(&lower.modules, module, "b");

    let mut output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors, Vec::new());
    let events = output.session.take_scc_events();
    assert!(events.iter().any(|event| {
        matches!(event, SccEvent::MergeComponents { merged, .. } if merged == &vec![a, b] || merged == &vec![b, a])
    }));
    assert!(events.iter().any(|event| {
        matches!(event, SccEvent::QuantifyComponent { component, .. } if component == &vec![a, b] || component == &vec![b, a])
    }));
}

#[test]
fn body_lowering_closes_binding_after_annotation_error() {
    let root = parse("my bad: Missing = 1\nmy y = bad\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (bad, _) = binding_def_and_order(&lower.modules, module, "bad");
    let (y, _) = binding_def_and_order(&lower.modules, module, "y");

    let mut output = lower_binding_bodies(&root, lower);

    assert!(output.errors.iter().any(|error| {
        matches!(
            error,
            BodyLoweringError::Expr {
                def,
                name,
                error: LoweringError::AnnotationBuild { .. },
            } if *def == bad && name == &Name("bad".into())
        )
    }));
    let events = output.session.take_scc_events();
    assert!(events.iter().any(|event| {
        matches!(event, SccEvent::QuantifyComponent { component, .. } if component == &vec![bad])
    }));
    assert!(events.iter().any(|event| {
        matches!(event, SccEvent::InstantiateUse { parent, target, .. } if *parent == y && *target == bad)
    }));
    assert!(events.iter().any(|event| {
        matches!(event, SccEvent::QuantifyComponent { component, .. } if component == &vec![y])
    }));
}

#[test]
fn body_lowering_closes_binding_after_missing_body_error() {
    let root = parse("my bad: int\nmy y = bad\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (bad, _) = binding_def_and_order(&lower.modules, module, "bad");
    let (y, _) = binding_def_and_order(&lower.modules, module, "y");

    let mut output = lower_binding_bodies(&root, lower);

    assert!(output.errors.iter().any(|error| {
        matches!(
            error,
            BodyLoweringError::MissingBody { def, name }
                if *def == bad && name == &Name("bad".into())
        )
    }));
    let events = output.session.take_scc_events();
    assert!(events.iter().any(|event| {
        matches!(event, SccEvent::QuantifyComponent { component, .. } if component == &vec![bad])
    }));
    assert!(events.iter().any(|event| {
        matches!(event, SccEvent::InstantiateUse { parent, target, .. } if *parent == y && *target == bad)
    }));
    assert!(events.iter().any(|event| {
        matches!(event, SccEvent::QuantifyComponent { component, .. } if component == &vec![y])
    }));
}
