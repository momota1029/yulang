use super::*;

#[test]
fn role_impl_method_requirement_checks_receiver_function_shape() {
    let root = parse(
        "struct User;\nrole Box 'a:\n  our x.get: unit\nimpl User: Box {\n  our get: unit = ()\n}\n",
    );
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.iter().any(|error| {
        matches!(
            error,
            BodyLoweringError::Expr {
                error: LoweringError::SignatureShapeMismatch {
                    expected: SignatureShape::Function,
                },
                ..
            }
        )
    }));
}

#[test]
fn role_impl_method_requirement_is_available_before_role_body_lowering() {
    let root = parse(
        "struct User;\nimpl User: Box {\n  our x.get = x\n}\nrole Box 'a:\n  type item\n  our x.get: item\n",
    );
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let candidates = output.session.role_impls.candidates(&["Box".to_string()]);
    assert_eq!(candidates.len(), 1);
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
fn unresolved_role_impl_head_reports_lowering_error() {
    let root = parse("role Box 'a:\n  our x.get: 'a\nimpl Missing: Box {\n  our x.get = x\n}\n");
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.iter().any(|error| {
        matches!(
            error,
            BodyLoweringError::Expr {
                error:
                    LoweringError::AnnotationBuild {
                        error: AnnBuildError::UnresolvedTypeName { path },
                        ..
                    },
                ..
            } if path == &vec![Name("Missing".into())]
        )
    }));
}

#[test]
fn role_impl_member_residual_role_is_collected_as_impl_prerequisite() {
    let root = parse(
        "role Eq 'a:\n  our x.eq: unit\nrole Box 'a:\n  our x.get: unit\nimpl 'a: Box {\n  our x.get = x.eq\n}\n",
    );
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let candidates = output.session.role_impls.candidates(&["Box".to_string()]);
    assert_eq!(candidates.len(), 1);
    assert_eq!(candidates[0].prerequisites.len(), 1);
    assert_eq!(candidates[0].prerequisites[0].role, vec!["Eq".to_string()]);
    assert_eq!(candidates[0].prerequisites[0].inputs.len(), 1);
}

#[test]
fn reference_lowering_queues_resolution_and_scc_edge() {
    let root = parse("my a = 1\nmy b = a\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (target, _) = binding_def_and_order(&lower.modules, module, "a");
    let (owner, site) = binding_def_and_order(&lower.modules, module, "b");
    let expr = binding_expr(&root, "b");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();
    let reference = match session.poly.expr(computation.expr) {
        Expr::Var(reference) => *reference,
        _ => panic!("expected var expr"),
    };

    assert_eq!(session.poly.ref_target(reference), None);
    session.drain_work();

    assert_eq!(session.poly.ref_target(reference), Some(target));
    assert_eq!(
        session.take_scc_events(),
        vec![SccEvent::ComponentEdgeAdded {
            from: vec![owner],
            to: vec![target]
        }]
    );
}

#[test]
fn qualified_path_lowers_to_resolved_value_reference() {
    let root = parse("mod m:\n  pub x = 1\nmy y = m::x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let m = lower
        .modules
        .module_at(module, &Name("m".into()), ModuleOrder(0))
        .unwrap();
    let target = lower.modules.value_decls(m, &Name("x".into()))[0].def;
    let (owner, site) = binding_def_and_order(&lower.modules, module, "y");
    let expr = binding_expr(&root, "y");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();
    let reference = match session.poly.expr(computation.expr) {
        Expr::Var(reference) => *reference,
        _ => panic!("expected path expr to lower to var reference"),
    };

    assert_eq!(session.poly.ref_target(reference), None);
    session.drain_work();
    assert_eq!(session.poly.ref_target(reference), Some(target));
}

#[test]
fn builtin_op_path_lowers_to_primitive_body() {
    let root = parse("pub add: int -> int -> int = builtin_op::int_add\nmy site = add\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let add = lower.modules.value_decls(module, &Name("add".into()))[0].def;
    let site = lower.modules.value_decls(module, &Name("site".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert!(matches!(
        output.session.poly.expr(binding_body_id(&output, add)),
        Expr::PrimitiveOp(PrimitiveOp::IntAdd)
    ));
    let site_body = binding_body_id(&output, site);
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, site_body)),
        Some(add)
    );
}

#[test]
fn yada_yada_syntax_lowers_to_primitive_never() {
    let root = parse("pub main = ...\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "main");
    let expr = binding_expr(&root, "main");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    assert!(matches!(
        session.poly.expr(computation.expr),
        Expr::PrimitiveOp(PrimitiveOp::YadaYada)
    ));
    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(computation.value)
        .expect("yada yada should constrain value");
    let types = session.infer.constraints().types();
    assert!(
        bounds
            .uppers()
            .iter()
            .any(|bound| matches!(types.neg(bound.neg), Neg::Bot))
    );
}

#[test]
fn pipeline_lowers_lhs_as_first_rhs_argument() {
    let root = parse("my f = builtin_op::int_add\nmy x = 1\nmy y = 2\npub z = x | f y\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let f = lower.modules.value_decls(module, &Name("f".into()))[0].def;
    let x = lower.modules.value_decls(module, &Name("x".into()))[0].def;
    let y = lower.modules.value_decls(module, &Name("y".into()))[0].def;
    let z = lower.modules.value_decls(module, &Name("z".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let (outer_callee, outer_arg) = match output.session.poly.expr(binding_body_id(&output, z)) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected outer app"),
    };
    let (inner_callee, inner_arg) = match output.session.poly.expr(outer_callee) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected inner app"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, inner_callee)),
        Some(f)
    );
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, inner_arg)),
        Some(x)
    );
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, outer_arg)),
        Some(y)
    );
}

#[test]
fn rule_lit_lowers_plain_text_to_text_parse_token() {
    let root = parse_with_text_parse_std("pub main = ~\"hello\"\n");
    let lower = lower_module_map(&root);
    let token = text_parse_def(&lower.modules, "token");
    let module = lower.modules.root_id();
    let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let (callee, arg) = match output.session.poly.expr(binding_body_id(&output, main)) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected token application"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, callee)),
        Some(token)
    );
    assert!(matches!(output.session.poly.expr(arg), Expr::Lit(Lit::Str(text)) if text == "hello"));
}

#[test]
fn mark_expr_plain_text_lowers_to_yumark_cons_text_leaf_nil() {
    let output = lower_yumark_main("pub main = '[hello world]\n");

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let heads = assert_yumark_chain(&output, yumark_main_body(&output), 1);
    assert_text_leaf_application(&output, heads[0], "hello world");
}

#[test]
fn mark_expr_empty_inline_lowers_to_yumark_nil() {
    let output = lower_yumark_main("pub main = '[]\n");

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    assert_nil_application(&output, yumark_main_body(&output));
}

#[test]
fn mark_expr_inline_emphasis_and_strong_lower_to_container_leaves() {
    let output = lower_yumark_main("pub main = '[plain *em* **strong**]\n");

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let heads = assert_yumark_chain(&output, yumark_main_body(&output), 4);
    assert_text_leaf_application(&output, heads[0], "plain ");

    let emphasis = assert_yumark_ctor(&output, heads[1], "emphasis_leaf");
    let emphasis_children = assert_yumark_chain(&output, field(&emphasis, "children"), 1);
    assert_text_leaf_application(&output, emphasis_children[0], "em");

    assert_text_leaf_application(&output, heads[2], " ");

    let strong = assert_yumark_ctor(&output, heads[3], "strong_leaf");
    let strong_children = assert_yumark_chain(&output, field(&strong, "children"), 1);
    assert_text_leaf_application(&output, strong_children[0], "strong");
}

#[test]
fn mark_expr_block_paragraph_lowers_to_paragraph_leaf() {
    let output = lower_yumark_main("pub main = '{hello *em*\n}\n");

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let heads = assert_yumark_chain(&output, yumark_main_body(&output), 1);
    let paragraph = assert_yumark_ctor(&output, heads[0], "paragraph_leaf");
    let children = assert_yumark_chain(&output, field(&paragraph, "children"), 2);
    assert_text_leaf_application(&output, children[0], "hello ");
    assert_yumark_ctor(&output, children[1], "emphasis_leaf");
}

#[test]
fn mark_expr_block_heading_blank_line_and_section_close_lower_to_static_leaves() {
    let output = lower_yumark_main("pub main = '{# Title\n\n#.\n}\n");

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let heads = assert_yumark_chain(&output, yumark_main_body(&output), 3);
    let heading = assert_yumark_ctor(&output, heads[0], "heading_leaf");
    assert_str_lit(&output, field(&heading, "marker"), "# ");
    assert_int_lit(&output, field(&heading, "level"), 1);
    let heading_children = assert_yumark_chain(&output, field(&heading, "children"), 1);
    assert_text_leaf_application(&output, heading_children[0], "Title");

    let blank = assert_yumark_ctor(&output, heads[1], "blank_line_leaf");
    assert_str_lit(&output, field(&blank, "marker"), "\n");

    let close = assert_yumark_ctor(&output, heads[2], "section_close_leaf");
    assert_str_lit(&output, field(&close, "marker"), "#.");
    assert_nil_application(&output, field(&close, "children"));
}

#[test]
fn mark_expr_block_list_lowers_to_list_block_items_and_item_body() {
    let output = lower_yumark_main("pub main = '{1. one\n2. **two**\n}\n");

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let heads = assert_yumark_chain(&output, yumark_main_body(&output), 2);
    let list = assert_yumark_ctor(&output, heads[0], "list_block_leaf");
    assert_bool_lit(&output, field(&list, "ordered"), true);

    let items = assert_yumark_chain(&output, field(&list, "items"), 1);
    let first = assert_yumark_ctor(&output, items[0], "list_item_leaf");
    assert_str_lit(&output, field(&first, "marker"), "1. ");
    let first_body = assert_yumark_chain(&output, field(&first, "children"), 1);
    let first_body = assert_yumark_ctor(&output, first_body[0], "list_item_body_leaf");
    let first_body_children = assert_yumark_chain(&output, field(&first_body, "children"), 1);
    assert_text_leaf_application(&output, first_body_children[0], "one");

    let list = assert_yumark_ctor(&output, heads[1], "list_block_leaf");
    assert_bool_lit(&output, field(&list, "ordered"), true);
    let items = assert_yumark_chain(&output, field(&list, "items"), 1);
    let second = assert_yumark_ctor(&output, items[0], "list_item_leaf");
    assert_str_lit(&output, field(&second, "marker"), "2. ");
    let second_body = assert_yumark_chain(&output, field(&second, "children"), 1);
    let second_body = assert_yumark_ctor(&output, second_body[0], "list_item_body_leaf");
    let second_body_children = assert_yumark_chain(&output, field(&second_body, "children"), 1);
    assert_yumark_ctor(&output, second_body_children[0], "strong_leaf");
}

#[test]
fn mark_expr_block_code_fence_lowers_to_info_and_raw_body() {
    let output = lower_yumark_main("pub main = '{```rust\nlet x = 1;\n```\n}\n");

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let heads = assert_yumark_chain(&output, yumark_main_body(&output), 1);
    let fence = assert_yumark_ctor(&output, heads[0], "code_fence_leaf");
    assert_str_lit(&output, field(&fence, "info"), "rust");
    assert_str_lit(&output, field(&fence, "body"), "let x = 1;");
}

#[test]
fn mark_expr_block_code_fence_after_list_uses_raw_body_after_info_line() {
    let output = lower_yumark_main("pub main = '{- one\n- before\n```text\ncode\n```\n}\n");

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let heads = assert_yumark_chain(&output, yumark_main_body(&output), 3);
    let fence = assert_yumark_ctor(&output, heads[2], "code_fence_leaf");
    assert_str_lit(&output, field(&fence, "info"), "text");
    assert_str_lit(&output, field(&fence, "body"), "code");
}

#[test]
fn mark_expr_block_yulang_code_fence_lowers_from_raw_source_not_embedded_statement() {
    let output = lower_yumark_main("pub main = '{```yulang\nmy x = 1\n```\n}\n");

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let heads = assert_yumark_chain(&output, yumark_main_body(&output), 1);
    let fence = assert_yumark_ctor(&output, heads[0], "code_fence_leaf");
    assert_str_lit(&output, field(&fence, "info"), "yulang");
    assert_str_lit(&output, field(&fence, "body"), "my x = 1");
}

#[test]
fn mark_expr_block_quote_lowers_to_quote_block_leaf() {
    let output = lower_yumark_main("pub main = '{> quoted\n}\n");

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let heads = assert_yumark_chain(&output, yumark_main_body(&output), 1);
    let quote = assert_yumark_ctor(&output, heads[0], "quote_block_leaf");
    let quote_children = assert_yumark_chain(&output, field(&quote, "children"), 1);
    assert_yumark_ctor(&output, quote_children[0], "paragraph_leaf");
}

#[test]
fn mark_expr_block_rich_document_lowers_static_vocab_without_bespoke_shape() {
    let output = lower_yumark_main(
        "pub main = '{# Title\nParagraph with *em* and **strong**.\n\n- one\n- two\n```text\ncode\n```\n> quote\n}\n",
    );

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let heads = assert_yumark_chain(&output, yumark_main_body(&output), 7);
    assert_yumark_ctor(&output, heads[0], "heading_leaf");
    assert_yumark_ctor(&output, heads[1], "paragraph_leaf");
    assert_yumark_ctor(&output, heads[2], "blank_line_leaf");
    assert_yumark_ctor(&output, heads[3], "list_block_leaf");
    assert_yumark_ctor(&output, heads[4], "list_block_leaf");
    assert_yumark_ctor(&output, heads[5], "code_fence_leaf");
    assert_yumark_ctor(&output, heads[6], "quote_block_leaf");
}

#[test]
fn mark_expr_command_still_rejects_as_unsupported() {
    let (root, lower) = lower_with_text_yumark_std("pub main = '{\\cmd;\n}\n");
    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.iter().any(|error| {
        matches!(
            error,
            BodyLoweringError::Expr {
                error: LoweringError::UnsupportedSyntax {
                    kind: SyntaxKind::YmCommand,
                },
                ..
            }
        )
    }));
}

#[test]
fn mark_expr_inline_expr_still_rejects_as_unsupported() {
    let (root, lower) = lower_with_text_yumark_std("pub main = '{[hello]\n}\n");
    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.iter().any(|error| {
        matches!(
            error,
            BodyLoweringError::Expr {
                error: LoweringError::UnsupportedSyntax {
                    kind: SyntaxKind::YmInlineExpr,
                },
                ..
            }
        )
    }));
}

fn lower_yumark_main(src: &str) -> BodyLowering {
    let (root, lower) = lower_with_text_yumark_std(src);
    lower_binding_bodies(&root, lower)
}

fn yumark_main_body(output: &BodyLowering) -> ExprId {
    let module = output.modules.root_id();
    let main = output.modules.value_decls(module, &Name("main".into()))[0].def;
    binding_body_id(output, main)
}

fn assert_yumark_chain(output: &BodyLowering, expr: ExprId, expected_len: usize) -> Vec<ExprId> {
    let cons = text_yumark_def(&output.modules, "cons");
    let mut expr = expr;
    let mut heads = Vec::new();
    for _ in 0..expected_len {
        let (cons_partial, tail) = match output.session.poly.expr(expr) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected cons application"),
        };
        let head = match output.session.poly.expr(cons_partial) {
            Expr::App(callee, arg) => {
                assert_eq!(root_ref_target(&output.session, *callee), Some(cons));
                *arg
            }
            _ => panic!("expected partial cons application"),
        };
        heads.push(head);
        expr = tail;
    }
    assert_nil_application(output, expr);
    heads
}

fn assert_yumark_ctor(output: &BodyLowering, expr: ExprId, name: &str) -> Vec<(String, ExprId)> {
    let constructor = text_yumark_def(&output.modules, name);
    let (callee, arg) = match output.session.poly.expr(expr) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected {name} application"),
    };
    let target = root_ref_target(&output.session, callee);
    assert_eq!(
        target,
        Some(constructor),
        "expected {name} constructor target {:?} ({:?}), got {:?} ({:?})",
        constructor,
        output.labels.def_label(constructor),
        target,
        target.and_then(|def| output.labels.def_label(def))
    );
    match output.session.poly.expr(arg) {
        Expr::Record {
            fields,
            spread: RecordSpread::None,
        } => fields.clone(),
        _ => panic!("expected {name} record payload"),
    }
}

fn field(fields: &[(String, ExprId)], name: &str) -> ExprId {
    fields
        .iter()
        .find(|(field, _)| field == name)
        .map(|(_, value)| *value)
        .unwrap_or_else(|| panic!("expected field {name}"))
}

fn assert_text_leaf_application(output: &BodyLowering, expr: ExprId, expected: &str) {
    let fields = assert_yumark_ctor(output, expr, "text_leaf");
    assert_str_lit(output, field(&fields, "value"), expected);
}

fn assert_nil_application(output: &BodyLowering, expr: ExprId) {
    let nil = text_yumark_def(&output.modules, "nil");
    let (callee, arg) = match output.session.poly.expr(expr) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected nil application"),
    };
    assert_eq!(root_ref_target(&output.session, callee), Some(nil));
    assert!(matches!(
        output.session.poly.expr(arg),
        Expr::Lit(Lit::Unit)
    ));
}

fn assert_str_lit(output: &BodyLowering, expr: ExprId, expected: &str) {
    assert!(
        matches!(output.session.poly.expr(expr), Expr::Lit(Lit::Str(text)) if text == expected),
        "expected string literal {expected:?}"
    );
}

fn assert_int_lit(output: &BodyLowering, expr: ExprId, expected: i64) {
    assert!(
        matches!(output.session.poly.expr(expr), Expr::Lit(Lit::Int(value)) if *value == expected),
        "expected int literal {expected}"
    );
}

fn assert_bool_lit(output: &BodyLowering, expr: ExprId, expected: bool) {
    assert!(
        matches!(output.session.poly.expr(expr), Expr::Lit(Lit::Bool(value)) if *value == expected),
        "expected bool literal {expected}"
    );
}

fn root_ref_target(session: &AnalysisSession, expr: ExprId) -> Option<DefId> {
    match session.poly.expr(expr) {
        Expr::Var(reference) => session.poly.ref_target(*reference),
        Expr::App(callee, _) => root_ref_target(session, *callee),
        _ => None,
    }
}

#[test]
fn rule_expr_wraps_sequence_in_unit_lambda() {
    let root = parse_with_text_parse_std("pub main = rule { \"a\" }\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let (pat, body) = match output.session.poly.expr(binding_body_id(&output, main)) {
        Expr::Lambda(pat, body) => (*pat, *body),
        _ => panic!("expected rule expr lambda"),
    };
    assert!(matches!(output.session.poly.pat(pat), Pat::Lit(Lit::Unit)));
    let (stmts, tail) = match output.session.poly.expr(body) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected rule sequence block"),
    };
    assert_eq!(stmts.len(), 1);
    assert!(matches!(stmts[0], Stmt::Expr(_)));
    assert!(matches!(
        output.session.poly.expr(tail),
        Expr::Lit(Lit::Unit)
    ));
}

#[test]
fn rule_expr_capture_builds_record_value() {
    let root = parse_with_text_parse_std("pub main = rule { id = std::text::parse::word }\n");
    let lower = lower_module_map(&root);
    let word = text_parse_def(&lower.modules, "word");
    let module = lower.modules.root_id();
    let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let (_, body) = match output.session.poly.expr(binding_body_id(&output, main)) {
        Expr::Lambda(pat, body) => {
            assert!(matches!(output.session.poly.pat(*pat), Pat::Lit(Lit::Unit)));
            (*pat, *body)
        }
        _ => panic!("expected rule expr lambda"),
    };
    let (stmts, tail) = match output.session.poly.expr(body) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected rule capture block"),
    };
    assert_eq!(stmts.len(), 1);
    let captured_expr = match &stmts[0] {
        Stmt::Let(_, _, expr) => *expr,
        _ => panic!("expected capture let"),
    };
    let (callee, unit) = match output.session.poly.expr(captured_expr) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected capture parser application"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, callee)),
        Some(word)
    );
    assert!(matches!(
        output.session.poly.expr(unit),
        Expr::Lit(Lit::Unit)
    ));
    match output.session.poly.expr(tail) {
        Expr::Record {
            fields,
            spread: RecordSpread::None,
        } => {
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, "id");
        }
        _ => panic!("expected capture record"),
    }
}

#[test]
fn rule_expr_value_quantifier_runs_some_parser_as_tail_value() {
    let root = parse_with_text_parse_std("pub main = rule { std::text::parse::word+ }\n");
    let lower = lower_module_map(&root);
    let some = text_parse_def(&lower.modules, "some");
    let word = text_parse_def(&lower.modules, "word");
    let module = lower.modules.root_id();
    let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let (_, body) = match output.session.poly.expr(binding_body_id(&output, main)) {
        Expr::Lambda(pat, body) => {
            assert!(matches!(output.session.poly.pat(*pat), Pat::Lit(Lit::Unit)));
            (*pat, *body)
        }
        _ => panic!("expected rule expr lambda"),
    };
    let (stmts, tail) = match output.session.poly.expr(body) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected rule quantifier block"),
    };
    assert!(stmts.is_empty());
    let (parser, unit) = match output.session.poly.expr(tail) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected quantified parser to be run as tail value"),
    };
    assert!(matches!(
        output.session.poly.expr(unit),
        Expr::Lit(Lit::Unit)
    ));
    let (combinator, parser_arg) = match output.session.poly.expr(parser) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected some parser application"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, combinator)),
        Some(some)
    );
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, parser_arg)),
        Some(word)
    );
}

#[test]
fn rule_lit_lazy_capture_builds_record_parser() {
    let root = parse_with_text_parse_std("pub main = ~\"users/:id\"\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let (_, body) = match output.session.poly.expr(binding_body_id(&output, main)) {
        Expr::Lambda(pat, body) => {
            assert!(matches!(output.session.poly.pat(*pat), Pat::Lit(Lit::Unit)));
            (*pat, *body)
        }
        _ => panic!("expected rule literal lambda"),
    };
    let (stmts, tail) = match output.session.poly.expr(body) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected rule literal block"),
    };
    assert_eq!(stmts.len(), 2);
    assert!(matches!(stmts[0], Stmt::Expr(_)));
    assert!(matches!(stmts[1], Stmt::Let(..)));
    match output.session.poly.expr(tail) {
        Expr::Record {
            fields,
            spread: RecordSpread::None,
        } => {
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, "id");
        }
        _ => panic!("expected capture record"),
    }
}

#[test]
fn rule_lit_interp_runs_parser_without_capture() {
    let root =
        parse_with_text_parse_std("my id = std::text::parse::word\npub main = ~\"users/{id}\"\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let id = lower.modules.value_decls(module, &Name("id".into()))[0].def;
    let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let (_, body) = match output.session.poly.expr(binding_body_id(&output, main)) {
        Expr::Lambda(pat, body) => {
            assert!(matches!(output.session.poly.pat(*pat), Pat::Lit(Lit::Unit)));
            (*pat, *body)
        }
        _ => panic!("expected rule literal lambda"),
    };
    let (stmts, tail) = match output.session.poly.expr(body) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected rule literal block"),
    };
    assert_eq!(stmts.len(), 2);
    let parser_run = match &stmts[1] {
        Stmt::Expr(expr) => *expr,
        _ => panic!("expected parser interpolation statement"),
    };
    let (callee, _unit) = match output.session.poly.expr(parser_run) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected parser interpolation application"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, callee)),
        Some(id)
    );
    assert!(matches!(
        output.session.poly.expr(tail),
        Expr::Lit(Lit::Unit)
    ));
}

#[test]
fn rule_lit_interp_capture_builds_record_parser() {
    let root = parse_with_text_parse_std(
        "my ident = std::text::parse::word\npub main = ~\"users/{id = ident}/posts\"\n",
    );
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let ident = lower.modules.value_decls(module, &Name("ident".into()))[0].def;
    let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let (_, body) = match output.session.poly.expr(binding_body_id(&output, main)) {
        Expr::Lambda(pat, body) => {
            assert!(matches!(output.session.poly.pat(*pat), Pat::Lit(Lit::Unit)));
            (*pat, *body)
        }
        _ => panic!("expected rule literal lambda"),
    };
    let (stmts, tail) = match output.session.poly.expr(body) {
        Expr::Block(stmts, Some(tail)) => (stmts, *tail),
        _ => panic!("expected rule literal block"),
    };
    assert_eq!(stmts.len(), 3);
    let captured_expr = match &stmts[1] {
        Stmt::Let(_, _, expr) => *expr,
        _ => panic!("expected interpolation capture statement"),
    };
    let (callee, _unit) = match output.session.poly.expr(captured_expr) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected capture parser application"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, callee)),
        Some(ident)
    );
    match output.session.poly.expr(tail) {
        Expr::Record {
            fields,
            spread: RecordSpread::None,
        } => {
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, "id");
        }
        _ => panic!("expected interpolation capture record"),
    }
}

#[test]
fn rule_expr_alternation_uses_text_parse_choice() {
    let root = parse_with_text_parse_std("pub main = rule { \"a\" | \"b\" }\n");
    let lower = lower_module_map(&root);
    let choice = text_parse_def(&lower.modules, "choice");
    let module = lower.modules.root_id();
    let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let (_, body) = match output.session.poly.expr(binding_body_id(&output, main)) {
        Expr::Lambda(pat, body) => {
            assert!(matches!(output.session.poly.pat(*pat), Pat::Lit(Lit::Unit)));
            (*pat, *body)
        }
        _ => panic!("expected rule expr lambda"),
    };
    let (parser, unit) = match output.session.poly.expr(body) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected choice parser invocation"),
    };
    assert!(matches!(
        output.session.poly.expr(unit),
        Expr::Lit(Lit::Unit)
    ));
    let (partial, _right) = match output.session.poly.expr(parser) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected choice second application"),
    };
    let (choice_ref, _left) = match output.session.poly.expr(partial) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected choice first application"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, choice_ref)),
        Some(choice)
    );
}

#[test]
fn rule_quantifier_lowers_tail_base_exprs() {
    let root = parse_with_text_parse_std(concat!(
        "my parsers = {word: std::text::parse::word}\n",
        "my id x = x\n",
        "pub field_base = rule { parsers.word* }\n",
        "pub call_base = rule { id(std::text::parse::word)+ }\n",
    ));
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
}

#[test]
fn rule_lazy_quantifiers_are_rejected_by_peg_rule_lowering() {
    let root = parse_with_text_parse_std(concat!(
        "pub many_site = rule { std::text::parse::word*? }\n",
        "pub some_site = rule { std::text::parse::word+? }\n",
    ));
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert_eq!(output.errors.len(), 2, "{:?}", output.errors);
    assert!(output.errors.iter().any(|error| matches!(
        error,
        BodyLoweringError::Expr {
            name,
            error:
                LoweringError::UnsupportedRuleLazyQuantifier {
                    kind: SyntaxKind::RuleQuantStarLazy,
                    ..
                },
            ..
        } if name.0 == "many_site"
    )));
    assert!(output.errors.iter().any(|error| matches!(
        error,
        BodyLoweringError::Expr {
            name,
            error:
                LoweringError::UnsupportedRuleLazyQuantifier {
                    kind: SyntaxKind::RuleQuantPlusLazy,
                    ..
                },
            ..
        } if name.0 == "some_site"
    )));
}

#[test]
fn cast_decl_registers_cast_scheme_before_annotation_generalization() {
    let root = parse(concat!(
        "struct user_id { raw: int }\n",
        "cast(x: int): user_id = user_id { raw: x }\n",
        "pub main: user_id = 0\n",
    ));
    let lower = lower_module_map(&root);

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let candidates = output
        .session
        .casts
        .candidates(&["int".to_string()], &["user_id".to_string()]);
    assert_eq!(candidates.len(), 1);
}

#[test]
fn for_stmt_lowers_to_std_loop_for_in() {
    let root = parse_with_flow_loop_std("my xs = 1\npub main = { for x in xs: x }\n");
    let lower = lower_module_map(&root);
    let for_in = control_flow_loop_for_in_def(&lower.modules);
    let module = lower.modules.root_id();
    let xs = lower.modules.value_decls(module, &Name("xs".into()))[0].def;
    let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let (applied_iter, body_lambda) = match output.session.poly.expr(binding_body_id(&output, main))
    {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected for_in body application"),
    };
    let (for_in_ref, iter_arg) = match output.session.poly.expr(applied_iter) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected for_in iterator application"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, for_in_ref)),
        Some(for_in)
    );
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, iter_arg)),
        Some(xs)
    );
    assert!(matches!(
        output.session.poly.expr(body_lambda),
        Expr::Lambda(..)
    ));
}

#[test]
fn labeled_for_stmt_lowers_to_std_label_loop_for_in() {
    let root = parse_with_flow_loop_and_label_std(
        "my xs = 1\npub main = { for 'outer x in xs: 'outer }\n",
    );
    let lower = lower_module_map(&root);
    let for_in = control_flow_label_loop_for_in_def(&lower.modules);
    let module = lower.modules.root_id();
    let xs = lower.modules.value_decls(module, &Name("xs".into()))[0].def;
    let main = lower.modules.value_decls(module, &Name("main".into()))[0].def;

    let output = lower_binding_bodies(&root, lower);

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let (applied_iter, label_lambda) =
        match output.session.poly.expr(binding_body_id(&output, main)) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected label_loop for_in body application"),
        };
    let (for_in_ref, iter_arg) = match output.session.poly.expr(applied_iter) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected label_loop for_in iterator application"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, for_in_ref)),
        Some(for_in)
    );
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, iter_arg)),
        Some(xs)
    );
    let (label_pat, item_lambda) = match output.session.poly.expr(label_lambda) {
        Expr::Lambda(pat, body) => (*pat, *body),
        _ => panic!("expected label lambda"),
    };
    let label = match output.session.poly.pat(label_pat) {
        Pat::Var(def) => *def,
        _ => panic!("expected label param"),
    };
    let item_body = match output.session.poly.expr(item_lambda) {
        Expr::Lambda(_, body) => *body,
        _ => panic!("expected item lambda"),
    };
    assert_eq!(
        output
            .session
            .poly
            .ref_target(expr_ref(&output.session, item_body)),
        Some(label)
    );
}

#[test]
fn application_lowers_to_app_and_constrains_callee_as_function() {
    let root = parse("my f = 1\nmy x = 2\nmy y = f x\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "y");
    let expr = binding_expr(&root, "y");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();
    let (callee, arg) = match session.poly.expr(computation.expr) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected app expr"),
    };
    let callee_ref = expr_ref(&session, callee);
    let arg_ref = expr_ref(&session, arg);
    let callee_value = session
        .refs
        .value(callee_ref)
        .expect("callee ref value slot");
    assert!(session.refs.value(arg_ref).is_some());

    let bounds = session
        .infer
        .constraints()
        .bounds()
        .of(callee_value)
        .expect("callee should have function upper bound");
    assert!(bounds.uppers().iter().any(|bound| {
        matches!(
            session.infer.constraints().types().neg(bound.neg),
            Neg::Fun { .. }
        )
    }));
}

#[test]
fn index_tail_lowers_to_index_selection_application() {
    let root = parse("my xs = 1\nmy i = 0\nmy got = xs[i]\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "got");
    let expr = binding_expr(&root, "got");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    let (callee, arg) = match session.poly.expr(computation.expr) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected index desugar to application"),
    };
    let select = match session.poly.expr(callee) {
        Expr::Select(_, select) => *select,
        _ => panic!("expected index callee to be a selection"),
    };
    assert_eq!(session.poly.select(select).name, "index");
    assert!(matches!(session.poly.expr(arg), Expr::Var(_)));
}

#[test]
fn bool_names_lower_to_bool_literals() {
    let root = parse("my flag = true\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "flag");
    let expr = binding_expr(&root, "flag");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    assert!(matches!(
        session.poly.expr(computation.expr),
        Expr::Lit(Lit::Bool(true))
    ));
}

#[test]
fn integer_literal_over_i64_lowers_to_bigint() {
    let root = parse("my huge = 9223372036854775808\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "huge");
    let expr = binding_expr(&root, "huge");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    assert!(matches!(
        session.poly.expr(computation.expr),
        Expr::Lit(Lit::BigInt(value)) if value.to_string() == "9223372036854775808"
    ));
}

#[test]
fn plain_string_literal_lowers_to_str_literal() {
    let root = parse("my text = \"a\\n\"\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "text");
    let expr = binding_expr(&root, "text");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    assert!(matches!(
        session.poly.expr(computation.expr),
        Expr::Lit(Lit::Str(text)) if text == "a\n"
    ));
    assert_var_has_lower_con_path(&session, computation.value, &["std", "text", "str", "str"]);
}

#[test]
fn string_interpolation_lowers_to_show_and_concat() {
    let root = parse_with_text_str_std("my x = 1\nmy text = \"hello %{x}\"\n");
    let lower = lower_module_map(&root);
    let concat = text_str_concat_def(&lower.modules);
    let module = lower.modules.root_id();
    let x = lower.modules.value_decls(module, &Name("x".into()))[0].def;
    let (owner, site) = binding_def_and_order(&lower.modules, module, "text");
    let expr = binding_expr(&root, "text");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();
    session.drain_work();

    let (concat_partial, interpolation) = match session.poly.expr(computation.expr) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected concat application"),
    };
    let (concat_ref, text) = match session.poly.expr(concat_partial) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected concat partial application"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, concat_ref)),
        Some(concat)
    );
    assert!(matches!(
        session.poly.expr(text),
        Expr::Lit(Lit::Str(text)) if text == "hello "
    ));
    let (receiver, show) = match session.poly.expr(interpolation) {
        Expr::Select(receiver, select) => (*receiver, *select),
        _ => panic!("expected interpolation show selection"),
    };
    assert_eq!(session.poly.select(show).name, "show");
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, receiver)),
        Some(x)
    );
}

#[test]
fn string_interpolation_lowers_statement_block_body() {
    let root = parse("my text = \"%{my x = 41; x}\"\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let (owner, site) = binding_def_and_order(&lower.modules, module, "text");
    let expr = binding_expr(&root, "text");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();

    let (receiver, show) = match session.poly.expr(computation.expr) {
        Expr::Select(receiver, select) => (*receiver, *select),
        _ => panic!("expected interpolation show selection"),
    };
    assert_eq!(session.poly.select(show).name, "show");
    assert!(matches!(session.poly.expr(receiver), Expr::Block(..)));
}

#[test]
fn string_interpolation_kind_only_format_lowers_to_method_selection() {
    let root =
        parse("my n = 1\nmy debug = \"%?{n}\"\nmy lower = \"%x{n}\"\nmy upper = \"%X{n}\"\n");
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let n = lower.modules.value_decls(module, &Name("n".into()))[0].def;
    let mut session = AnalysisSession::new(lower.arena);

    for (binding, method) in [
        ("debug", "debug"),
        ("lower", "lower_hex"),
        ("upper", "upper_hex"),
    ] {
        let (owner, site) = binding_def_and_order(&lower.modules, module, binding);
        let expr = binding_expr(&root, binding);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        session.drain_work();

        let (receiver, select) = match session.poly.expr(computation.expr) {
            Expr::Select(receiver, select) => (*receiver, *select),
            _ => panic!("expected interpolation format kind selection"),
        };
        assert_eq!(session.poly.select(select).name, method);
        assert_eq!(
            session.poly.ref_target(expr_ref(&session, receiver)),
            Some(n)
        );
    }
}

#[test]
fn string_interpolation_layout_format_lowers_to_std_format_protocol() {
    let root = parse_with_text_str_and_format_std("my n = 1\nmy text = \"%+#08x{n}\"\n");
    let lower = lower_module_map(&root);
    let format_lower_hex = core_fmt_def(&lower.modules, "format_lower_hex");
    let format_spec_ctor = core_fmt_def(&lower.modules, "format_spec");
    let sign_plus = core_fmt_format_sign_def(&lower.modules, "plus");
    let module = lower.modules.root_id();
    let n = lower.modules.value_decls(module, &Name("n".into()))[0].def;
    let (owner, site) = binding_def_and_order(&lower.modules, module, "text");
    let expr = binding_expr(&root, "text");
    let mut session = AnalysisSession::new(lower.arena);

    let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
        .lower_expr(&expr)
        .unwrap();
    session.drain_work();

    let (format_partial, receiver) = match session.poly.expr(computation.expr) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected format protocol application"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, receiver)),
        Some(n)
    );

    let (format_ref, format_spec) = match session.poly.expr(format_partial) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected format protocol partial application"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, format_ref)),
        Some(format_lower_hex)
    );

    let (constructor, record) = match session.poly.expr(format_spec) {
        Expr::App(callee, arg) => (*callee, *arg),
        _ => panic!("expected format_spec constructor application"),
    };
    assert_eq!(
        session.poly.ref_target(expr_ref(&session, constructor)),
        Some(format_spec_ctor)
    );
    let fields = match session.poly.expr(record) {
        Expr::Record {
            fields,
            spread: RecordSpread::None,
        } => fields,
        _ => panic!("expected format_spec record payload"),
    };
    assert_eq!(
        fields
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>(),
        vec![
            "kind",
            "align",
            "sign",
            "fill",
            "width",
            "precision",
            "alternate",
            "zero_pad"
        ]
    );
    assert!(matches!(
        session
            .poly
            .expr(format_spec_record_field(fields, "alternate")),
        Expr::Lit(Lit::Bool(true))
    ));
    assert!(matches!(
        session
            .poly
            .expr(format_spec_record_field(fields, "zero_pad")),
        Expr::Lit(Lit::Bool(true))
    ));
    assert!(matches!(
        format_spec_some_lit_int(&session, format_spec_record_field(fields, "width")),
        8
    ));
    assert_eq!(
        session.poly.ref_target(expr_ref(
            &session,
            format_spec_some_payload(&session, format_spec_record_field(fields, "sign"))
        )),
        Some(sign_plus)
    );
}

fn format_spec_record_field(fields: &[(String, ExprId)], name: &str) -> ExprId {
    fields
        .iter()
        .find_map(|(field, expr)| (field == name).then_some(*expr))
        .unwrap_or_else(|| panic!("expected format_spec field {name}"))
}

fn format_spec_some_lit_int(session: &AnalysisSession, expr: ExprId) -> i64 {
    let value = format_spec_some_payload(session, expr);
    match session.poly.expr(value) {
        Expr::Lit(Lit::Int(number)) => *number,
        _ => panic!("expected opt::just int payload"),
    }
}

fn format_spec_some_payload(session: &AnalysisSession, expr: ExprId) -> ExprId {
    match session.poly.expr(expr) {
        Expr::App(_, value) => *value,
        _ => panic!("expected opt::just application"),
    }
}
