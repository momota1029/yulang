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
