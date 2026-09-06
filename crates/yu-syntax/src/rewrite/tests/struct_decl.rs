use super::*;

fn declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::StructDeclaration)
        .expect("StructDeclaration")
}

fn count(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    node.descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn token_count(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    node.descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == kind)
        .count()
}

fn assert_pending_word_with_leading(exit: Option<TailExit>, word: &str, leading: &str) {
    let mut item = match exit {
        Some(Err(Either::Left(item))) => item,
        Some(Err(Either::Right(end))) => end.item,
        _ => panic!("{word:?} must remain pending"),
    };
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    assert_eq!(item.payload_view().spelling(), Some(word));
    assert_eq!(emit_pending_leading_text(&mut item), leading);
}

#[test]
fn struct_c11_builds_exact_direct_topology_and_forms() {
    for (source, fields) in [
        ("struct Empty;", 0),
        ("my struct Point{x: F, y: Y}", 2),
        ("our struct Pair(F, G)", 2),
        ("pub struct Row:\n  x: F\n  y: Y", 2),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            node.parent().map(|node| node.kind()),
            Some(SyntaxKind::Statement)
        );
        assert_eq!(count(&node, SyntaxKind::StructField), fields, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::TypeExpression),
            fields,
            "{source:?}"
        );
        assert_eq!(count(&node, SyntaxKind::BindingHeader), 0, "{source:?}");
    }
}

#[test]
fn struct_c11_dispatch_is_exact_and_irrevocable() {
    for source in [
        "struct S;",
        "my struct S;",
        "our struct S;",
        "pub struct S;",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        declaration(&green);
    }
    for source in ["structure", "structural", "my structure = value"] {
        let (green, _) = run_statement(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::StructDeclaration),
            "{source:?}"
        );
    }
    let (green, _) = run_statement("my struct = value");
    let root = SyntaxNode::new_root(green);
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::StructDeclaration)
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );
}

#[test]
fn struct_c11_keeps_dynamic_word_operator_names_raw() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new("Dynamic", OperatorFixities::new().with_nullfix()),
        OperatorDeclaration::new("field", OperatorFixities::new().with_nullfix()),
    ])
    .expect("dynamic Struct-name operator table");
    let source = "struct Dynamic{field: T}";
    let (green, exit) = run_statement_with(source, &operators);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::NullfixOperatorUse), 0);
    assert_eq!(count(&node, SyntaxKind::Error), 0);
    assert_eq!(count(&node, SyntaxKind::StructField), 1);
}

#[test]
fn struct_c11_named_boundary_splits_only_complete_next_fields() {
    for (source, fields, types, missing) in [
        ("struct S{x:F y:Y}", 2, 2, 1),
        ("struct S{x:F Y}", 1, 2, 0),
        ("struct S{x:Pair(F Y)}", 1, 3, 0),
        ("struct S(F Y)", 1, 2, 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::StructField), fields, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::TypeExpression),
            types,
            "{source:?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            missing,
            "{source:?}\n{node:#?}"
        );
    }
}

#[test]
fn struct_c11_gap_rules_keep_shallow_items_pending() {
    let (green, _) = run_statement("my\nstruct S;");
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::StructDeclaration)
    );

    let (green, exit) = run_statement("struct\nName;");
    assert_eq!(green.to_string(), "struct");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    for (source, fields, missing) in [
        ("struct S{x\n:y}", 2, 2),
        ("struct S{x\n  :y}", 2, 3),
        ("struct S{x:\nY}", 2, 2),
        ("struct S{x:\n  Y}", 1, 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::StructField), fields, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            missing,
            "{source:?}\n{node:#?}"
        );
    }
}

#[test]
fn struct_c11_header_and_body_recovery_stays_owner_local() {
    for (source, missing, errors) in [
        ("struct;", 1, 0),
        ("struct @ S;", 0, 1),
        ("struct S @ ;", 0, 1),
        ("struct S:", 1, 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::Missing), missing, "{source:?}");
        assert_eq!(count(&node, SyntaxKind::Error), errors, "{source:?}");
    }
}

#[test]
fn struct_c11_malformed_recovery_owns_trailing_eof_trivia() {
    for (source, error_parent, error_text) in [
        ("struct @ ", SyntaxKind::StructDeclaration, "@ "),
        ("struct S @ ", SyntaxKind::StructDeclaration, "@ "),
        ("struct S{x @ ", SyntaxKind::StructField, " @ "),
        ("struct S{@ ", SyntaxKind::StructField, "@ "),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let root = SyntaxNode::new_root(green);
        let trailing = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .last()
            .expect("trailing EOF trivia token");
        assert_eq!(trailing.kind(), SyntaxKind::Whitespace, "{source:?}");
        assert_eq!(trailing.text(), " ", "{source:?}");
        let error = trailing.parent().expect("trailing EOF trivia owner");
        assert_eq!(error.kind(), SyntaxKind::Error, "{source:?}");
        assert_eq!(error.to_string(), error_text, "{source:?}");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(error_parent),
            "{source:?}",
        );
    }
}

#[test]
fn struct_c11_gstruct_and_body_handoff_are_lossless() {
    for source in ["struct\n  Deep;", "struct Adjacent{}"] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        declaration(&green);
    }
    let (green, _) = run_statement("struct S Foo");
    let node = declaration(&green);
    assert_eq!(green.to_string(), "struct S ");
    assert_eq!(count(&node, SyntaxKind::StructField), 0);
    assert_eq!(count(&node, SyntaxKind::Missing), 1);

    let (green, exit) = run_statement("struct S 1");
    let node = declaration(&green);
    assert_eq!(green.to_string(), "struct S ");
    assert_eq!(count(&node, SyntaxKind::Missing), 1);
    assert_eq!(count(&node, SyntaxKind::Error), 0);
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    let (green, exit) = run_statement("struct S\nnext");
    assert_eq!(green.to_string(), "struct S");
    let Err(Either::Left(mut item)) = exit.expect("statement exit") else {
        panic!("pending item")
    };
    assert_eq!(emit_pending_leading_text(&mut item), "\n");

    let (green, exit) = run_statement("struct S:\nnext");
    assert_eq!(count(&declaration(&green), SyntaxKind::StructField), 1);
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
}

#[test]
fn struct_c11_body_colon_does_not_capture_polymorphic_variant_type() {
    let (green, exit) = run_statement("struct S :{A}");
    let node = declaration(&green);
    assert_eq!(green.to_string(), "struct S ");
    assert_eq!(count(&node, SyntaxKind::Missing), 1);
    assert_eq!(count(&node, SyntaxKind::Error), 0);
    let Some(Err(Either::Left(item))) = exit else {
        panic!("polymorphic variant type must remain pending")
    };
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::PolymorphicVariantColon)
    );
    assert_eq!(item.payload_view().spelling(), Some(":"));

    let source = "struct S:\n  x: T";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::StructField), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
}

#[test]
fn struct_c11_tuple_uses_the_complete_type_vocabulary() {
    let source = "struct S(for 'a: T, '[E], :{A}, [R])";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::StructField), 4);
    for kind in [
        SyntaxKind::ForallType,
        SyntaxKind::EffectRowType,
        SyntaxKind::PolymorphicVariantType,
        SyntaxKind::BracketRow,
    ] {
        assert_eq!(count(&node, kind), 1, "{kind:?}");
    }

    let source = "struct S(A; for 'a: T)";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::StructField), 2);
    assert_eq!(count(&node, SyntaxKind::ForallType), 1);

    let source = "struct S(,A,,)";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    let fields = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::StructField)
        .collect::<Vec<_>>();
    assert_eq!(fields.len(), 3);
    assert!(fields.iter().all(|field| {
        field
            .children()
            .all(|child| child.kind() == SyntaxKind::TypeExpression)
            && field
                .children()
                .any(|child| child.kind() == SyntaxKind::TypeExpression)
    }));
}

#[test]
fn struct_c11_trivia_stays_with_the_struct_sequence_and_named_gap() {
    let source = "struct S(\n  A, /*post*/\n  B\n)";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    let tuple_fields = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::StructField)
        .collect::<Vec<_>>();
    assert_eq!(tuple_fields.len(), 2);
    assert!(tuple_fields.iter().all(|field| {
        field
            .children()
            .map(|child| child.kind())
            .collect::<Vec<_>>()
            == [SyntaxKind::TypeExpression]
            && field
                .children_with_tokens()
                .all(|element| element.as_token().is_none())
    }));
    assert!(
        node.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| matches!(
                token.kind(),
                SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::BlockComment
            ))
            .all(|token| token.parent().as_ref() == Some(&node))
    );

    let source = "struct S{\n  x :  F,\n  y:Y\n}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    let first = node
        .children()
        .find(|child| child.kind() == SyntaxKind::StructField)
        .expect("named field");
    let ty = first
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeExpression)
        .expect("field type");
    assert_eq!(ty.text().to_string(), "F");
    assert_eq!(first.text().to_string(), "x :  F");
}

#[test]
fn struct_c11_recovers_owned_fields_and_typed_closes() {
    for source in [
        "struct S{x F, y: Y}",
        "struct S{: F}",
        "struct S{x: , y:Y}",
        "struct S{x:F; y:Y}",
        "struct S{x:F; :Y}",
        "struct S(F; G)",
        "struct S{x:F] y:Y}",
        "struct S(F} G)",
        "struct S{x:F",
        "struct S(F",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        declaration(&green);
    }
}

#[test]
fn struct_c11_reaches_nested_canonical_consumers_but_not_inline_expr_slots() {
    for source in [
        "{struct S;}",
        "f:\n  struct S;",
        "if c:\n  struct S;",
        "case x:\n  p ->\n    struct S;",
        "catch x:\n  p ->\n    struct S;",
        "value with: struct S;",
        "value with:\n  struct S;",
        "mod M {struct S;}",
        "mod M:\n  struct S;",
        "mod M: struct S;",
        "my body =\n  struct S;",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        declaration(&green);
    }
    for source in [
        "f: struct S;",
        "if c: struct S;",
        "case x: p -> struct S;",
        "catch x: p -> struct S;",
        "my x = struct S;",
        "f struct S;",
    ] {
        let (green, _) = run(source);
        assert!(source.starts_with(&green.to_string()), "{source:?}");
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::StructDeclaration),
            "{source:?}"
        );
    }
}

#[test]
fn struct_companion_header_orders_derives_before_the_companion() {
    for (source, missing, errors) in [
        ("struct S with {}", 0, 0),
        ("struct S derives Eq with {}", 0, 0),
        ("struct S derives with {}", 1, 0),
        ("struct S derives @ with {}", 0, 1),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            1,
            "{source:?}"
        );
        assert_eq!(token_count(&node, SyntaxKind::WithKw), 1, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            missing,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Error),
            errors,
            "{source:?}\n{node:#?}"
        );
        let owned = node
            .children()
            .filter(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::DerivesClause | SyntaxKind::DeclarationCompanion
                )
            })
            .map(|child| child.kind())
            .collect::<Vec<_>>();
        assert_eq!(
            owned.last(),
            Some(&SyntaxKind::DeclarationCompanion),
            "{source:?}: {owned:?}",
        );
    }
}

#[test]
fn struct_companion_trailing_follows_the_actual_matching_close() {
    for source in [
        "struct S{} derives Eq with {}",
        "struct S(A) derives Eq with {}",
        "struct S{x F} with {}",
        "struct S{x:F; y:Y} with {}",
        "struct S{x:F] y:Y} with {}",
        "struct S(@) with {}",
        "struct S(A; B) with {}",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            1,
            "{source:?}"
        );
    }

    for source in [
        "struct S{x:T with {}",
        "struct S{x:T] with ()",
        "struct S(A] with {}",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn struct_header_derives_hands_body_starters_back_by_role_phase() {
    for (source, fields) in [
        ("struct S derives {}", 0),
        ("struct S derives :\n  x:T", 1),
        ("struct S derives ;", 0),
        ("struct S derives Eq{}", 0),
        ("struct S derives Eq(A)", 1),
        ("struct S derives Eq:\n  x:T", 1),
        ("struct S derives Eq;", 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DerivesClause), 1, "{source:?}");
        assert_eq!(count(&node, SyntaxKind::StructField), fields, "{source:?}");
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 0);
    }

    for source in [
        "struct S derives (Eq) with {}",
        "struct S derives (Eq(A)) with {}",
        "struct S derives (Eq {x:T}) with {}",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DerivesClause), 1, "{source:?}");
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
        assert_eq!(count(&node, SyntaxKind::StructField), 0, "{source:?}");
    }

    let source = "struct S derives , with {}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::DerivesClause), 1);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 2);
}

#[test]
fn struct_companion_rejects_nontrailing_body_forms_and_incomplete_name() {
    for (source, leading) in [
        ("struct S; with {}", " "),
        ("struct S:\n  x:T\nwith {}", "\n"),
        ("struct ; with {}", " "),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
        assert_pending_word_with_leading(exit, "with", leading);
    }

    let source = "struct S{x:T\nwith {}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert_eq!(
        count(&declaration(&green), SyntaxKind::DeclarationCompanion),
        0
    );
}

#[test]
fn struct_companion_suspends_with_inside_nested_derives_types() {
    let source = "struct S derives (A with B) with {}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
    assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
    assert!(
        node.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Identifier && token.text() == "with")
    );
}

#[test]
fn struct_companion_gap_and_contextual_word_judges_are_exact() {
    for source in ["struct S\n  with {}", "struct S\r\n  with {}"] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            1
        );
    }
    for (source, leading) in [
        ("struct S\nwith {}", "\n"),
        ("struct S{}\r\nwith {}", "\r\n"),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0
        );
        assert_pending_word_with_leading(exit, "with", leading);
    }

    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "with",
        OperatorFixities::new().with_nullfix(),
    )])
    .expect("dynamic with operator table");
    let (green, exit) = run_statement_with("struct S{} with {}", &operators);
    assert_eq!(
        count(&declaration(&green), SyntaxKind::DeclarationCompanion),
        0
    );
    assert!(matches!(
        exit,
        Some(Err(Either::Left(_))) | Some(Err(Either::Right(_)))
    ));

    let (green, exit) = run_statement_with_stops(
        "struct S with {}",
        &OperatorTable::empty(),
        super::super::operator::STOP_WITH,
    );
    assert_eq!(
        count(&declaration(&green), SyntaxKind::DeclarationCompanion),
        0
    );
    assert_pending_word_with_leading(exit, "with", " ");

    for source in ["struct S withx {}", "struct S within {}"] {
        let (green, _) = run_statement(source);
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn struct_companion_rejected_incomplete_lists_keep_the_exact_fence_handoff() {
    use super::super::item::{BorrowedTarget, Boundary};
    use super::super::yumark::{FenceOpener, FencePrefixPolicy};

    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let origin = 8200;
    for accepted in [
        "> > struct S{x:T with {}",
        "> > struct S{x:T] with {}",
        "> > struct S(A with B",
        "> > struct S(A] with B",
    ] {
        let source = format!("{accepted}\r\n> > ```\r\nouter");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("the incomplete Struct body must return its exact fence boundary")
        };

        assert_eq!(green.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\r\nouter", "{accepted:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            0,
            "{accepted:?}\n{node:#?}",
        );
        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, "\r\n", "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + 2,
            "{accepted:?}",
        );
        assert!(matches!(
            pending.into_kind(),
            Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
        ));
    }
}

#[test]
fn struct_actual_close_returns_the_exact_normalized_successor() {
    let origin = 8300;
    for declaration_text in ["struct S{x:T}", "struct S(T)"] {
        let source = format!("{declaration_text}  next tail");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::InLine, None);
        let NormalizedExit::Complete(Err(Either::Left(mut successor)), LineEntry::InLine) = exit
        else {
            panic!("the closed Struct must return its exact successor")
        };

        assert_eq!(green.to_string(), declaration_text, "{declaration_text:?}");
        assert_eq!(remainder, " tail", "{declaration_text:?}");
        assert_eq!(
            successor.payload_view().token_kind(),
            Some(TokenKind::Identifier),
            "{declaration_text:?}",
        );
        assert_eq!(
            successor.payload_view().spelling(),
            Some("next"),
            "{declaration_text:?}",
        );
        assert_eq!(
            origin + source.len() - remainder.len() - "next".len(),
            origin + declaration_text.len() + 2,
            "{declaration_text:?}",
        );
        assert_eq!(
            emit_pending_leading_text(&mut successor),
            "  ",
            "{declaration_text:?}",
        );
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0,
            "{declaration_text:?}",
        );
    }
}

#[test]
fn struct_accepted_companion_returns_the_exact_outer_remainder() {
    let origin = 8400;
    for declaration_text in ["struct S{} with {}", "struct S(T) with {}"] {
        let source = format!("{declaration_text} outer tail");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::InLine, None);
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Ok(()), LineEntry::InLine)
        ));

        assert_eq!(green.to_string(), declaration_text, "{declaration_text:?}");
        assert_eq!(remainder, " outer tail", "{declaration_text:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
        assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
    }
}

#[test]
fn struct_companion_streams_crlf_to_the_same_fence_boundary() {
    use super::super::yumark::{FenceOpener, FencePrefixPolicy};

    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let origin = 8100;
    let accepted = "> > struct S{} derives Eq with: our x = y";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
    else {
        panic!("the Struct companion must return the exact fence boundary")
    };
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
    assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
}
