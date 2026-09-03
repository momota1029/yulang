use super::*;

fn top_type_expression(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeExpression)
        .expect("top-level type expression")
}

#[test]
fn type_expression_keeps_fixed_tails_in_source_order() {
    let source = "List(Int)::Result Arg -> Out -> Final";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let top = top_type_expression(&green);
    assert_eq!(
        top.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::TypeCallTail,
            SyntaxKind::TypePathTail,
            SyntaxKind::TypeApplyArgument,
            SyntaxKind::TypeArrowTail,
        ]
    );
    let arrows = top
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::TypeArrowTail)
        .count();
    assert_eq!(arrows, 2);
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Identifier, "List".to_owned()),
            (SyntaxKind::LParen, "(".to_owned()),
            (SyntaxKind::Identifier, "Int".to_owned()),
            (SyntaxKind::RParen, ")".to_owned()),
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Identifier, "Result".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "Arg".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Arrow, "->".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "Out".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Arrow, "->".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "Final".to_owned()),
        ]
    );
}

#[test]
fn type_expression_accepts_sigil_and_numeric_atoms_but_not_numeric_path_segments() {
    let source = "$value::'result _hidden 42";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::SigilIdentifier, "$value".to_owned()),
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::SigilIdentifier, "'result".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::SigilIdentifier, "_hidden".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Integer, "42".to_owned()),
        ]
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeApplyArgument)
            .count(),
        2
    );
}

#[test]
fn type_apply_scope_keeps_adjacent_and_spaced_paths_distinct() {
    let adjacent = run_type("F A::B").0;
    let spaced = run_type("F A ::B").0;
    assert_eq!(adjacent.to_string(), "F A::B");
    assert_eq!(spaced.to_string(), "F A ::B");

    let adjacent_top = top_type_expression(&adjacent);
    let adjacent_apply = adjacent_top
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeApplyArgument)
        .expect("adjacent apply");
    assert!(
        adjacent_apply
            .descendants()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );
    assert!(
        !adjacent_top
            .children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );

    let spaced_top = top_type_expression(&spaced);
    assert!(
        spaced_top
            .children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );
}

#[test]
fn type_call_and_group_keep_explicit_and_implicit_boundaries() {
    let source = "T(A, B; C) (D\nE)";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let top = top_type_expression(&green);
    let call = top
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("type call");
    assert_eq!(
        call.children()
            .filter(|node| node.kind() == SyntaxKind::TypeExpression)
            .count(),
        3
    );
    assert_eq!(
        call.children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::LParen, "(".to_owned()),
            (SyntaxKind::Comma, ",".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Semicolon, ";".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::RParen, ")".to_owned()),
        ]
    );
    let apply = top
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeApplyArgument)
        .expect("group apply");
    let group = apply
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
        .expect("parenthesized type group");
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeExpression)
            .count(),
        2
    );
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn type_path_tail_recovers_its_mandatory_segment() {
    for (source, recovery) in [
        ("A::", SyntaxKind::Missing),
        ("A::123", SyntaxKind::Error),
        ("A::@Name", SyntaxKind::Error),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let path = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypePathTail)
            .expect("type path tail");
        assert_eq!(
            path.children()
                .filter(|node| node.kind() == recovery)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("A::::Name");
    assert_eq!(green.to_string(), "A::::Name");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypePathTail)
            .count(),
        2
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run_type("A:: ");
    assert_eq!(green.to_string(), "A:: ");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let path = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypePathTail)
        .expect("type path tail");
    assert_eq!(
        path.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
        ]
    );
}

#[test]
fn type_arrow_tail_recovers_its_mandatory_rhs() {
    for (source, recovery) in [("A->", SyntaxKind::Missing), ("A->@B", SyntaxKind::Error)] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let arrow = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
            .expect("type arrow tail");
        assert_eq!(
            arrow
                .children()
                .filter(|node| node.kind() == recovery)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("A->\n");
    assert_eq!(green.to_string(), "A->\n");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let arrow = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
        .expect("type arrow tail");
    assert_eq!(
        arrow
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Arrow, "->".to_owned()),
            (SyntaxKind::Newline, "\n".to_owned()),
        ]
    );
}

#[test]
fn type_delimited_owner_recovers_missing_items_and_close_at_eof() {
    for (source, owner, missing) in [
        ("T(", SyntaxKind::TypeCallTail, 1),
        ("(A", SyntaxKind::ParenthesizedTypeGroup, 1),
        ("T(A,", SyntaxKind::TypeCallTail, 2),
        ("T(,A)", SyntaxKind::TypeCallTail, 1),
        ("T(A,,B)", SyntaxKind::TypeCallTail, 1),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("type delimited owner");
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T(A ");
    assert_eq!(green.to_string(), "T(A ");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("type call tail");
    assert_eq!(
        call.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::LParen, "(".to_owned()),
            (SyntaxKind::Identifier, "A".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
        ]
    );
}

#[test]
fn named_record_type_keeps_field_and_separator_ownership() {
    let source = "{a: A, b: List(Int)}";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let record = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        2
    );
    assert_eq!(
        record
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::LBrace, "{".to_owned()),
            (SyntaxKind::Comma, ",".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::RBrace, "}".to_owned()),
        ]
    );
}

#[test]
fn named_record_type_accepts_layout_and_type_tails() {
    let layout = "{\n  a: A\n  b: B\n}";
    let (green, exit) = run_type(layout);
    assert_eq!(green.to_string(), layout);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let record = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        2
    );

    let applied = run_type("F {a: A} -> Out").0;
    assert_eq!(applied.to_string(), "F {a: A} -> Out");
    let top = top_type_expression(&applied);
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeArrowTail)
    );

    let (adjacent, exit) = run_type("F{a:A}");
    assert_eq!(adjacent.to_string(), "F");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::LBrace)
    ));
    assert!(
        !SyntaxNode::new_root(adjacent)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::NamedRecordType)
    );
}

#[test]
fn forall_type_is_contextual_terminal_primary() {
    let source = "for 'a: A -> A";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let top = top_type_expression(&green);
    assert_eq!(
        top.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::ForallType]
    );
    let forall = top
        .children()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    assert_eq!(
        forall
            .children()
            .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
            .count(),
        1
    );
    assert!(
        forall
            .descendants()
            .any(|node| node.kind() == SyntaxKind::TypeArrowTail)
    );

    let layout = "for\n  'a\n  'b:\n    Pair('a, 'b)";
    let (green, exit) = run_type(layout);
    assert_eq!(green.to_string(), layout);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
            .count(),
        2
    );

    for source in ["(for 'a: T)", "F(for 'a: T)", "A -> for 'a: T"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(
            SyntaxNode::new_root(green)
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::ForallType)
                .count(),
            1,
            "{source:?}"
        );
    }

    let grouped = run_type("(for 'a: T)::Result").0;
    let top = top_type_expression(&grouped);
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );
}

#[test]
fn forall_type_does_not_reclassify_type_apply_for() {
    for source in ["forx 'a", "forall 'a", "for_ 'a"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::ForallType),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("F for 'a: T");
    assert_eq!(green.to_string(), "F for 'a");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::Colon)
    ));
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ForallType)
    );
}

#[test]
fn effect_row_type_keeps_its_compound_opener_and_items() {
    for (source, item_kind) in [
        ("'[]", None),
        ("'[e]", Some(SyntaxKind::Identifier)),
        ("'['e]", Some(SyntaxKind::SigilIdentifier)),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let row = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::EffectRowType)
            .expect("effect row type");
        assert_eq!(
            row.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::Apostrophe | SyntaxKind::LBracket | SyntaxKind::RBracket
                    )
                })
                .map(|token| (token.kind(), token.text().to_owned()))
                .collect::<Vec<_>>(),
            [
                (SyntaxKind::Apostrophe, "'".to_owned()),
                (SyntaxKind::LBracket, "[".to_owned()),
                (SyntaxKind::RBracket, "]".to_owned()),
            ],
            "{source:?}"
        );
        assert_eq!(
            row.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::Identifier | SyntaxKind::SigilIdentifier
                    )
                })
                .map(|token| token.kind())
                .collect::<Vec<_>>(),
            item_kind.into_iter().collect::<Vec<_>>(),
            "{source:?}"
        );
    }
}

#[test]
fn effect_row_type_composes_with_layout_and_tails() {
    let layout = "'[\n  A, B;\n  C\n  D\n]";
    let (green, exit) = run_type(layout);
    assert_eq!(green.to_string(), layout);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let row = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::EffectRowType)
        .expect("effect row type");
    assert_eq!(
        row.children()
            .filter(|node| node.kind() == SyntaxKind::TypeExpression)
            .count(),
        4
    );

    let (green, exit) = run_type("Foo '['e] -> Out");
    assert_eq!(green.to_string(), "Foo '['e] -> Out");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let top = top_type_expression(&green);
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeArrowTail)
    );

    let path = run_type("'[e]::Result").0;
    assert!(
        top_type_expression(&path)
            .children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );

    for source in ["'", "' [e]", "'/*c*/[e]"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), "", "{source:?}");
        assert!(exit.is_none(), "{source:?}");
    }
}

#[test]
fn polymorphic_variant_type_keeps_two_level_boundaries() {
    for (source, tags, payloads) in [
        (":{}", 0, 0),
        (":{A Int, B}", 2, 1),
        (":{A Int Bool}", 1, 2),
        (":{A Int\nB}", 2, 1),
        (":{A,}", 1, 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let variant = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(
            variant
                .children()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
                .count(),
            tags,
            "{source:?}"
        );
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
                .count(),
            payloads,
            "{source:?}"
        );
    }

    let nested = ":{\n  A Pair(\n    Int,\n    Bool\n  )\n  B\n}";
    let (green, exit) = run_type(nested);
    assert_eq!(green.to_string(), nested);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(
        variant
            .children()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .count(),
        2
    );

    let (green, exit) = run_type(":{A [e] T X}");
    assert_eq!(green.to_string(), ":{A [e] T X}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
            .count(),
        2
    );
}

#[test]
fn polymorphic_variant_type_composes_with_type_tails() {
    let (green, exit) = run_type("F :{A} -> Out");
    assert_eq!(green.to_string(), "F :{A} -> Out");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let top = top_type_expression(&green);
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeArrowTail)
    );

    let path = run_type(":{A}::Result").0;
    assert!(
        top_type_expression(&path)
            .children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );

    let (green, exit) = run_type("F:{A}");
    assert_eq!(green.to_string(), "F");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    for source in [": {A}", ":/*comment*/{A}", ":\n{A}", ":"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), "", "{source:?}");
        assert!(exit.is_none(), "{source:?}");
    }
}

#[test]
fn bracket_rows_attach_at_leading_and_arrow_positions() {
    for (source, items) in [("[] T", 0), ("[e] T", 1), ("[e, f; g\nh] T", 4)] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let top = top_type_expression(&green);
        let row = top
            .children()
            .find(|node| node.kind() == SyntaxKind::BracketRow)
            .expect("leading bracket row");
        assert_eq!(
            row.children()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .count(),
            items,
            "{source:?}"
        );
    }

    let source = "T [e, f] -> U -> V";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let top = top_type_expression(&green);
    let tail = top
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
        .expect("bracket row arrow tail");
    assert!(
        tail.children()
            .any(|node| node.kind() == SyntaxKind::BracketRow)
    );
    assert_eq!(
        top.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeArrowTail)
            .count(),
        2
    );

    for source in ["T -> [e] U", "F([e] T)", "[[e] T] U", "[e] F [io] -> U"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
    }
}

#[test]
fn bracket_row_arrow_is_mandatory_at_normal_boundaries() {
    for source in ["T [e]", "T [e] U", "F(T [e])"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T [e]\nU");
    assert_eq!(green.to_string(), "T [e]");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn leading_bracket_row_head_is_mandatory_at_normal_boundaries() {
    for source in ["[e]", "F([e])"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("[e]\nT");
    assert_eq!(green.to_string(), "[e]");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn leading_bracket_row_retries_a_balanced_second_row_as_one_error() {
    for source in ["[e][f]T", "[e][/*]*/f]T"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let top = top_type_expression(&green);
        assert_eq!(
            top.descendants()
                .filter(|node| node.kind() == SyntaxKind::BracketRow)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            top.children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("[e][f");
    assert_eq!(green.to_string(), "[e]");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );
}

#[test]
fn leading_bracket_row_retries_malformed_heads_without_a_missing_cascade() {
    for source in ["[e] @ T", "[e] @"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let top = top_type_expression(&green);
        assert_eq!(
            top.children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !top.children()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
        assert!(
            top.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Whitespace)
                .all(|token| token
                    .parent()
                    .is_some_and(|parent| parent.kind() == SyntaxKind::TypeExpression)),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("[e] @\nT");
    assert_eq!(green.to_string(), "[e] @");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert!(
        !top_type_expression(&green)
            .children()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn bracket_rows_recover_malformed_items_and_local_closes() {
    for (source, missing) in [
        ("T [)] -> U", 1),
        ("T [e)] -> U", 0),
        ("T [@ A] -> U", 0),
        ("T [@] -> U", 0),
        ("T [@", 2),
        ("T [e)", 2),
        ("T [@, A] -> U", 0),
        ("T [e @ A] -> U", 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T [@ A] -> U");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let error = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("bracket item error");
    assert_eq!(error.text().to_string(), "@ ");

    let (green, exit) = run_type("[e");
    assert_eq!(green.to_string(), "[e");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );

    let (green, exit) = run_type("T [e\n  @]");
    assert_eq!(green.to_string(), "T [e");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    let root = SyntaxNode::new_root(green);
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn bracket_row_recovery_keeps_item_and_close_slots_distinct() {
    for (source, error_text, missing) in [
        ("T [:] -> U", ":", 0),
        ("T [@\nA] -> U", "@", 0),
        ("T [@\n  A] -> U", "@\n  ", 0),
        ("T [A\n  )] -> U", ")", 0),
        ("T [@/* comment */A] -> U", "@/* comment */", 0),
        ("T [@/*\n*/A] -> U", "@/*\n*/", 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let errors = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{source:?}");
        assert_eq!(errors[0].text().to_string(), error_text, "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T [A\n  ] -> U");
    assert_eq!(green.to_string(), "T [A\n  ] -> U");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
    );

    let (green, exit) = run_type("T [");
    assert_eq!(green.to_string(), "T [");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        3
    );

    for (source, errors, missing) in [
        ("T [e,)] -> U", 1, 1),
        ("T [@,)] -> U", 2, 1),
        ("T [e))] -> U", 2, 0),
        ("T [e))", 2, 2),
        ("T [)", 1, 3),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            errors,
            "{source:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    for (source, parsed) in [("T [e) U]", "T [e)"), ("T [e)\nU]", "T [e)")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), parsed, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Left(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T [e)\n");
    assert_eq!(green.to_string(), "T [e)\n");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let newline = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::Newline)
        .expect("caller newline");
    assert_ne!(
        newline.parent().expect("newline parent").kind(),
        SyntaxKind::BracketRow
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );
}
