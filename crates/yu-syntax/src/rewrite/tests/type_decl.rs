use super::*;

fn type_declaration_node(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeDeclaration)
        .expect("TypeDeclaration")
}

fn count(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    node.descendants()
        .filter(|descendant| descendant.kind() == kind)
        .count()
}

#[test]
fn type_c12_builds_the_exact_equality_topology() {
    let source = "type Pair 'left 'right = ('left, 'right)";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = type_declaration_node(&green);
    assert_eq!(
        format!("{declaration:#?}"),
        concat!(
            "TypeDeclaration@0..40\n",
            "  TypeKw@0..4 \"type\"\n",
            "  Whitespace@4..5 \" \"\n",
            "  Identifier@5..9 \"Pair\"\n",
            "  DeclarationTypeParameterList@9..22\n",
            "    Whitespace@9..10 \" \"\n",
            "    SigilIdentifier@10..15 \"'left\"\n",
            "    Whitespace@15..16 \" \"\n",
            "    SigilIdentifier@16..22 \"'right\"\n",
            "  Whitespace@22..23 \" \"\n",
            "  Equals@23..24 \"=\"\n",
            "  Whitespace@24..25 \" \"\n",
            "  TypeExpression@25..40\n",
            "    ParenthesizedTypeGroup@25..40\n",
            "      LParen@25..26 \"(\"\n",
            "      TypeExpression@26..31\n",
            "        SigilIdentifier@26..31 \"'left\"\n",
            "      Comma@31..32 \",\"\n",
            "      Whitespace@32..33 \" \"\n",
            "      TypeExpression@33..39\n",
            "        SigilIdentifier@33..39 \"'right\"\n",
            "      RParen@39..40 \")\"\n",
        )
    );
    assert_eq!(
        declaration.parent().map(|parent| parent.kind()),
        Some(SyntaxKind::Statement)
    );
    assert_eq!(
        count(&declaration, SyntaxKind::DeclarationTypeParameterList),
        1
    );
    assert_eq!(
        declaration
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::SigilIdentifier)
            .count(),
        4
    );
    assert_eq!(count(&declaration, SyntaxKind::TypeExpression), 3);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 0);

    for source in [
        "type A = B",
        "my type A = B",
        "our type A = B",
        "pub type A = B",
        "type\n  A = B",
        "my\n  type\n  A = B",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        type_declaration_node(&green);
    }
}

#[test]
fn type_c12_dispatch_is_exact_and_irrevocable() {
    for source in ["typewriter", "type_name", "my typewriter = value"] {
        let (green, _) = run_statement(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TypeDeclaration),
            "{source:?}"
        );
    }

    let (green, _) = run_statement("my type = Value");
    let root = SyntaxNode::new_root(green);
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::TypeDeclaration)
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );

    let (green, _) = run_statement("my typewriter = value");
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );
}

#[test]
fn type_c12_parameters_are_same_line_raw_identifiers_only() {
    let source = "type T $a &a 'a _a = R";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let declaration = type_declaration_node(&green);
    let parameters = declaration
        .children()
        .find(|node| node.kind() == SyntaxKind::DeclarationTypeParameterList)
        .expect("nonempty parameter list");
    assert_eq!(
        parameters
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::SigilIdentifier)
            .map(|token| token.text().to_string())
            .collect::<Vec<_>>(),
        ["$a", "&a", "'a"]
    );
    assert_eq!(
        parameters
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Identifier)
            .map(|token| token.text().to_string())
            .collect::<Vec<_>>(),
        ["_a"]
    );

    let (green, exit) = run_statement("type T\n  'a");
    assert_eq!(green.to_string(), "type T\n  'a");
    assert_eq!(
        count(
            &type_declaration_node(&green),
            SyntaxKind::DeclarationTypeParameterList
        ),
        0
    );
    assert_eq!(
        count(&type_declaration_node(&green), SyntaxKind::Missing),
        1
    );
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let (green, exit) = run_statement("type T\n'a = R");
    assert_eq!(green.to_string(), "type T");
    let Some(Err(Either::Left(item))) = exit else {
        panic!("shallow header continuation must remain pending")
    };
    assert_eq!(
        item.leading
            .0
            .iter()
            .map(|part| &*part.text)
            .collect::<String>(),
        "\n"
    );

    for tail in [
        "use", "mod", "struct", "type", "enum", "error", "role", "impl", "cast", "act", "my",
        "our", "pub", "lazy", "prefix", "infix", "suffix", "nullfix", "with", "derives",
    ] {
        let source = format!("type T {tail}");
        let (green, _) = run_statement(&source);
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DeclarationTypeParameterList),
            0,
            "{tail}"
        );
    }
}

#[test]
fn type_c12_name_uses_raw_header_identifier_vocabulary() {
    for (source, expected_name) in [("type for = A", "for"), ("type _name = A", "_name")] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        let declaration = type_declaration_node(&green);
        let names = declaration
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Identifier)
            .map(|token| token.text().to_string())
            .collect::<Vec<_>>();
        assert_eq!(names, [expected_name], "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
    }

    let (green, _) = run_statement("type @ for = A");
    let declaration = type_declaration_node(&green);
    assert_eq!(green.to_string(), "type @ for = A");
    assert_eq!(count(&declaration, SyntaxKind::Error), 1);
    assert!(declaration.children_with_tokens().any(|element| {
        element
            .into_token()
            .is_some_and(|token| token.kind() == SyntaxKind::Identifier && token.text() == "for")
    }));
}

#[test]
fn type_c12_exact_equals_and_header_recovery_do_not_cascade() {
    for (source, missing, errors) in [
        ("type", 1, 0),
        ("type = Int", 1, 0),
        ("type @ Name = Int", 0, 1),
        ("type Name @ = Int", 0, 1),
        ("type Id 'a 'a", 1, 0),
        ("type Id 'a ('a)", 1, 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
    }

    for source in ["type T == U", "type T => U"] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        let declaration = type_declaration_node(&green);
        assert_eq!(count(&declaration, SyntaxKind::Equals), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
    }

    let (green, exit) = run_statement("type T\n= A");
    assert_eq!(green.to_string(), "type T");
    assert_eq!(
        count(&type_declaration_node(&green), SyntaxKind::Missing),
        1
    );
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    for (source, missing, errors) in [("type T = @ A", 0, 1), ("type T = @;", 0, 1)] {
        let (green, _) = run_statement(source);
        assert!(source.starts_with(&green.to_string()), "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
    }
}

#[test]
fn type_c12_rhs_uses_the_full_ordinary_type_surface() {
    let source = "type T = (for 'a: A, '[E], :{Tag}, [R], {x: X})";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let declaration = type_declaration_node(&green);
    for kind in [
        SyntaxKind::ForallType,
        SyntaxKind::EffectRowType,
        SyntaxKind::PolymorphicVariantType,
        SyntaxKind::BracketRow,
        SyntaxKind::NamedRecordType,
    ] {
        assert_eq!(count(&declaration, kind), 1, "{kind:?}");
    }

    let source = "type T = A::with";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert_eq!(
        count(&type_declaration_node(&green), SyntaxKind::TypePathTail),
        1
    );

    let source = "type T = {with: A}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert_eq!(
        count(&type_declaration_node(&green), SyntaxKind::NamedRecordType),
        1
    );

    let source = "type T = for 'a, 'b: A";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert_eq!(
        type_declaration_node(&green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::SigilIdentifier)
            .count(),
        2
    );
}

#[test]
fn type_c12_rhs_boundaries_remain_exact_pending_items() {
    let (green, exit) = run_statement("type Result 'a = ;");
    assert_eq!(green.to_string(), "type Result 'a = ");
    let declaration = type_declaration_node(&green);
    assert_eq!(
        format!("{declaration:#?}"),
        concat!(
            "TypeDeclaration@0..17\n",
            "  TypeKw@0..4 \"type\"\n",
            "  Whitespace@4..5 \" \"\n",
            "  Identifier@5..11 \"Result\"\n",
            "  DeclarationTypeParameterList@11..14\n",
            "    Whitespace@11..12 \" \"\n",
            "    SigilIdentifier@12..14 \"'a\"\n",
            "  Whitespace@14..15 \" \"\n",
            "  Equals@15..16 \"=\"\n",
            "  Whitespace@16..17 \" \"\n",
            "  TypeExpression@17..17\n",
            "    Missing@17..17\n",
        )
    );
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert!(!declaration.text().to_string().contains(';'));
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    let (green, exit) = run_statement("type T = for 'a;");
    assert_eq!(green.to_string(), "type T = for 'a");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(ref item))) if token_kind(item) == Some(TokenKind::Semicolon)
    ));

    let (green, exit) = run_statement("type T = A with");
    assert_eq!(green.to_string(), "type T = A");
    let Some(Err(Either::Left(item))) = exit else {
        panic!("With must remain pending")
    };
    assert!(matches!(
        item.payload,
        Payload::Token(ref token)
            if token.kind == TokenKind::Identifier && token.text.as_ref() == "with"
    ));
    assert_eq!(
        item.leading
            .0
            .iter()
            .map(|part| &*part.text)
            .collect::<String>(),
        " "
    );

    for source in [
        "type T = A -> B with",
        "type T = [A] -> B with",
        "type T = for 'a: A with",
        "type T = (A) with",
        "type T = {x: A} with",
        "type T = '[E] with",
        "type T = :{Tag} with",
        "type T = A -> @ with",
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(
            green.to_string(),
            source.strip_suffix(" with").expect("With suffix")
        );
        assert!(
            matches!(
                exit,
                Some(Err(Either::Left(ref item)))
                    if matches!(
                        item.payload,
                        Payload::Token(ref token)
                            if token.kind == TokenKind::Identifier && token.text.as_ref() == "with"
                    )
            ),
            "{source:?}"
        );
    }

    let (green, _) = run_statement("type T = A without");
    assert_eq!(green.to_string(), "type T = A without");

    let (green, exit) = run_statement("type T =\nA");
    assert_eq!(green.to_string(), "type T =");
    assert_eq!(
        count(&type_declaration_node(&green), SyntaxKind::Missing),
        1
    );
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    let source = "type T =\n  A";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
}

#[test]
fn type_c12_nested_type_owners_preserve_outer_boundaries() {
    for (source, committed) in [
        ("type T = (A with", "type T = (A"),
        ("type T = A(B with", "type T = A(B"),
        ("type T = [A with", "type T = [A"),
        ("type T = {x: A with", "type T = {x: A"),
        ("type T = '[E with", "type T = '[E"),
        ("type T = :{Tag A with", "type T = :{Tag A"),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), committed, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 1, "{source:?}");
        assert!(
            matches!(
                exit,
                Some(Err(Either::Left(ref item)))
                    if matches!(
                        item.payload,
                        Payload::Token(ref token)
                            if token.kind == TokenKind::Identifier && token.text.as_ref() == "with"
                    ) && item.leading.0.iter().map(|part| &*part.text).collect::<String>() == " "
            ),
            "{source:?}"
        );
    }

    for source in [
        "type T = (@ with",
        "type T = A(@ with",
        "type T = {x: @ with",
        "type T = '[ @ with",
        "type T = :{Tag @ with",
    ] {
        let (green, exit) = run_statement(source);
        let declaration = type_declaration_node(&green);
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 1, "{source:?}");
        assert!(
            matches!(
                exit,
                Some(Err(Either::Left(ref item)))
                    if matches!(
                        item.payload,
                        Payload::Token(ref token)
                            if token.kind == TokenKind::Identifier && token.text.as_ref() == "with"
                    )
            ),
            "{source:?}: {:?}",
            green.to_string()
        );
    }

    let operators = OperatorTable::empty();
    for (source, stops, kind) in [
        (
            "type T = (A;",
            stops_for(TokenKind::RParen),
            TokenKind::Semicolon,
        ),
        (
            "type T = (A]",
            stops_for(TokenKind::RBracket),
            TokenKind::RBracket,
        ),
    ] {
        let (green, exit) = run_statement_with_stops(source, &operators, stops);
        let declaration = type_declaration_node(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 1, "{source:?}");
        assert!(
            matches!(
                exit,
                Some(Err(Either::Left(ref item))) if token_kind(item) == Some(kind)
            ),
            "{source:?}: {:?}",
            green.to_string()
        );
    }

    let (green, exit) = run_statement_with_stops("type T = (A else", &operators, STOP_ELSE);
    assert_eq!(green.to_string(), "type T = (A");
    assert_eq!(
        count(&type_declaration_node(&green), SyntaxKind::Missing),
        1
    );
    assert!(matches!(
        exit,
        Some(Err(Either::Left(ref item)))
            if matches!(
                item.payload,
                Payload::Token(ref token)
                    if token.kind == TokenKind::Identifier && token.text.as_ref() == "else"
            ) && item.leading.0.iter().map(|part| &*part.text).collect::<String>() == " "
    ));
}

#[test]
fn type_c12_malformed_path_retry_preserves_caller_stops() {
    let operators = OperatorTable::empty();
    for (source, stops, committed, expected_kind, expected_word) in [
        ("type T = A::@ with", 0, "type T = A::@", None, Some("with")),
        (
            "type T = A::@ ;",
            0,
            "type T = A::@",
            Some(TokenKind::Semicolon),
            None,
        ),
        (
            "type T = A::@ else",
            STOP_ELSE,
            "type T = A::@",
            None,
            Some("else"),
        ),
    ] {
        let (green, exit) = run_statement_with_stops(source, &operators, stops);
        assert_eq!(green.to_string(), committed, "{source:?}");
        let declaration = type_declaration_node(&green);
        let errors = declaration
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{source:?}");
        assert_eq!(errors[0].text().to_string(), "@");
        assert_eq!(
            errors[0].parent().map(|node| node.kind()),
            Some(SyntaxKind::TypePathTail)
        );
        let Some(Err(Either::Left(item))) = exit else {
            panic!("caller boundary must remain pending: {source:?}")
        };
        assert_eq!(
            item.leading
                .0
                .iter()
                .map(|part| &*part.text)
                .collect::<String>(),
            " "
        );
        if let Some(kind) = expected_kind {
            assert_eq!(token_kind(&item), Some(kind), "{source:?}");
        }
        if let Some(word) = expected_word {
            assert!(matches!(
                item.payload,
                Payload::Token(ref token)
                    if token.kind == TokenKind::Identifier && token.text.as_ref() == word
            ));
        }
    }

    let (green, _) = run_statement("type T = A::with");
    assert_eq!(green.to_string(), "type T = A::with");
    assert_eq!(count(&type_declaration_node(&green), SyntaxKind::Error), 0);
}

#[test]
fn type_c12_recovery_roles_stay_at_the_owning_slot() {
    for (source, error_parent, error_text, missing_parent, pending) in [
        (
            "type @ Name = A",
            Some(SyntaxKind::TypeDeclaration),
            Some("@ "),
            None,
            None,
        ),
        (
            "type Name @ = A",
            Some(SyntaxKind::TypeDeclaration),
            Some("@ "),
            None,
            None,
        ),
        (
            "type Name = @ A",
            Some(SyntaxKind::TypeDeclaration),
            Some("@"),
            None,
            None,
        ),
        (
            "type Name = @ ;",
            Some(SyntaxKind::TypeDeclaration),
            Some("@"),
            None,
            Some(TokenKind::Semicolon),
        ),
        (
            "type Name = ;",
            None,
            None,
            Some(SyntaxKind::TypeExpression),
            Some(TokenKind::Semicolon),
        ),
    ] {
        let (green, exit) = run_statement(source);
        let declaration = type_declaration_node(&green);
        let errors = declaration
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        let missing = declaration
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .collect::<Vec<_>>();
        assert_eq!(
            errors.len(),
            usize::from(error_parent.is_some()),
            "{source:?}"
        );
        assert_eq!(
            missing.len(),
            usize::from(missing_parent.is_some()),
            "{source:?}"
        );
        if let Some(parent) = error_parent {
            assert_eq!(errors[0].parent().map(|node| node.kind()), Some(parent));
            assert_eq!(
                errors[0].text().to_string(),
                error_text.expect("Error text")
            );
        }
        if let Some(parent) = missing_parent {
            assert_eq!(missing[0].parent().map(|node| node.kind()), Some(parent));
            assert!(missing[0].text().is_empty(), "{source:?}");
        }
        if let Some(kind) = pending {
            assert!(
                matches!(exit, Some(Err(Either::Left(ref item))) if token_kind(item) == Some(kind)),
                "{source:?}"
            );
            assert!(!declaration.text().to_string().contains(';'), "{source:?}");
        }
    }
}

#[test]
fn type_c12_completes_the_header_and_rhs_recovery_rows() {
    let operators = OperatorTable::empty();
    for (source, error_text, committed, pending) in [
        ("type @ = A", "@ ", "type @ = A", None),
        ("type T @ A", "@ ", "type T @ A", None),
        ("type T @ ;", "@", "type T @", Some(TokenKind::Semicolon)),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), committed, "{source:?}");
        let declaration = type_declaration_node(&green);
        let errors = declaration
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{source:?}");
        assert_eq!(errors[0].text().to_string(), error_text, "{source:?}");
        assert_eq!(
            errors[0].parent().map(|node| node.kind()),
            Some(SyntaxKind::TypeDeclaration),
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        if pending.is_none() {
            assert!(
                declaration
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                    .any(|rhs| rhs.text().to_string() == "A"),
                "{source:?}"
            );
        }
        if let Some(kind) = pending {
            assert!(matches!(
                exit,
                Some(Err(Either::Left(ref item)))
                    if token_kind(item) == Some(kind)
                        && item.leading.0.iter().map(|part| &*part.text).collect::<String>() == " "
            ));
        }
    }

    let (green, exit) = run_statement("type T =");
    let declaration = type_declaration_node(&green);
    assert_eq!(green.to_string(), "type T =");
    assert_eq!(count(&declaration, SyntaxKind::Error), 0);
    let missing = declaration
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Missing)
        .collect::<Vec<_>>();
    assert_eq!(missing.len(), 1);
    assert!(missing[0].text().is_empty());
    assert_eq!(
        missing[0].parent().map(|node| node.kind()),
        Some(SyntaxKind::TypeExpression)
    );
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    for (source, stops, word) in [
        ("type T = with", 0, "with"),
        ("type T = else", STOP_ELSE, "else"),
    ] {
        let (green, exit) = run_statement_with_stops(source, &operators, stops);
        assert_eq!(green.to_string(), "type T =", "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        let missing = declaration
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .collect::<Vec<_>>();
        assert_eq!(missing.len(), 1, "{source:?}");
        assert!(missing[0].text().is_empty(), "{source:?}");
        assert_eq!(
            missing[0].parent().map(|node| node.kind()),
            Some(SyntaxKind::TypeExpression),
            "{source:?}"
        );
        let Some(Err(Either::Left(item))) = exit else {
            panic!("ambient boundary must remain pending: {source:?}")
        };
        assert!(matches!(
            item.payload,
            Payload::Token(ref token)
                if token.kind == TokenKind::Identifier && token.text.as_ref() == word
        ));
        assert_eq!(
            item.leading
                .0
                .iter()
                .map(|part| &*part.text)
                .collect::<String>(),
            " "
        );
    }
}

#[test]
fn type_c12_inherits_active_stops_and_outer_separator_ownership() {
    let operators = OperatorTable::empty();
    let (green, exit) = run_statement_with_stops("type T = A else", &operators, STOP_ELSE);
    assert_eq!(green.to_string(), "type T = A");
    let Some(Err(Either::Left(item))) = exit else {
        panic!("active Else must remain pending")
    };
    assert_eq!(
        item.leading
            .0
            .iter()
            .map(|part| &*part.text)
            .collect::<String>(),
        " "
    );

    let (green, exit) =
        run_statement_with_stops("type T = A]", &operators, stops_for(TokenKind::RBracket));
    assert_eq!(green.to_string(), "type T = A");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(ref item))) if token_kind(item) == Some(TokenKind::RBracket)
    ));

    let source = "{type T = A; my x = value}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let declaration = type_declaration_node(&green);
    assert!(
        !declaration
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Semicolon)
    );
    let root = SyntaxNode::new_root(green);
    let separator = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::Semicolon)
        .expect("outer statement separator");
    assert!(
        !separator
            .parent_ancestors()
            .any(|ancestor| ancestor == declaration)
    );
}

#[test]
fn type_c12_reaches_full_statement_consumers_only() {
    for source in [
        "{type T = A}",
        "f:\n  type T = A",
        "if c:\n  type T = A",
        "case x:\n  p ->\n    type T = A",
        "catch x:\n  p ->\n    type T = A",
        "value with: type T = A",
        "value with:\n  type T = A",
        "my body =\n  type T = A",
        "mod M {type T = A}",
        "mod M:\n  type T = A",
    ] {
        let (green, _) = run_statement(source);
        assert!(source.starts_with(&green.to_string()), "{source:?}");
        type_declaration_node(&green);
    }

    for source in [
        "f: type T = A",
        "if c: type T = A",
        "case x: p -> type T = A",
        "catch x: p -> type T = A",
        "my x = type T = A",
        "f type T = A",
    ] {
        let (green, _) = run(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TypeDeclaration),
            "{source:?}"
        );
    }
}
