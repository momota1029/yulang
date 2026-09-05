use super::*;
use reborrow_generic::Reborrow as _;

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

fn token_count(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    node.descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == kind)
        .count()
}

fn identifier_count(node: &SyntaxNode, spelling: &str) -> usize {
    node.descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Identifier && token.text() == spelling)
        .count()
}

fn assert_pending_word(exit: Option<TailExit>, word: &str) {
    let Some(Err(Either::Left(item))) = exit else {
        panic!("{word:?} must remain pending")
    };
    assert!(
        matches!(
            item.payload,
            Payload::Token(ref token)
                if token.kind == TokenKind::Identifier && token.text.as_ref() == word
        ),
        "expected pending {word:?}, got {item:?}"
    );
}

fn assert_pending_word_with_leading(exit: Option<TailExit>, word: &str, leading: &str) {
    let Some(Err(Either::Left(item))) = exit else {
        panic!("{word:?} must remain pending")
    };
    assert!(
        matches!(
            item.payload,
            Payload::Token(ref token)
                if token.kind == TokenKind::Identifier && token.text.as_ref() == word
        ),
        "expected pending {word:?}, got {item:?}"
    );
    assert_eq!(
        item.leading
            .0
            .iter()
            .map(|part| &*part.text)
            .collect::<String>(),
        leading,
        "pending {word:?} must retain its complete leading trivia"
    );
}

fn run_type_declaration_with_handoff(
    source: &str,
    line_handoff: super::super::statement::StatementLineHandoff,
) -> (GreenNode, Option<TailExit>) {
    let operators = OperatorTable::empty();
    let mut source_input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let mut i = In::new(&mut source_input, &mut recover, &mut builder);
    let leading = super::super::lexer::scan_trivia(i.rb());
    let intro = super::super::lexer::statement_item_after_trivia(i.rb(), leading, 0, 0);
    let exit = super::super::type_decl::type_declaration(i, intro, 0, 0, line_handoff);
    if let Err(Either::Right(end)) = &exit {
        emit_end(&mut builder, end);
    }
    builder.finish_node();
    (builder.finish(), Some(exit))
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

#[test]
fn type_c14_commits_complete_nominal_headers_at_the_owned_terminal() {
    for source in [
        "type Point",
        "type Point  ",
        "type Point\n  ",
        "type Id 'a 'a",
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        assert_eq!(
            count(&declaration, SyntaxKind::TypeExpression),
            0,
            "{source:?}"
        );
    }

    for (source, kind) in [
        ("type Point;", TokenKind::Semicolon),
        ("type Point)", TokenKind::RParen),
        ("type Point]", TokenKind::RBracket),
        ("type Point}", TokenKind::RBrace),
    ] {
        let stops = match kind {
            TokenKind::Semicolon => 0,
            _ => stops_for(kind),
        };
        let (green, exit) = run_statement_with_stops(source, &OperatorTable::empty(), stops);
        assert_eq!(green.to_string(), "type Point", "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(
            count(&declaration, SyntaxKind::TypeExpression),
            0,
            "{source:?}"
        );
        assert!(matches!(
            exit,
            Some(Err(Either::Left(ref item))) if token_kind(item) == Some(kind)
        ));
    }

    let (green, exit) =
        run_statement_with_stops("type Point else", &OperatorTable::empty(), STOP_ELSE);
    assert_eq!(green.to_string(), "type Point");
    let declaration = type_declaration_node(&green);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 0);
    assert!(matches!(
        exit,
        Some(Err(Either::Left(ref item)))
            if matches!(&item.payload, Payload::Token(token) if token.text.as_ref() == "else")
    ));
}

#[test]
fn type_c14_threads_only_statement_line_provenance() {
    let (green, exit) = run_statement("type Point\nnext");
    assert_eq!(green.to_string(), "type Point");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(ref item)))
            if matches!(&item.payload, Payload::Token(token) if token.text.as_ref() == "next")
                && item.leading.0.iter().map(|part| &*part.text).collect::<String>() == "\n"
    ));
    assert_eq!(
        count(&type_declaration_node(&green), SyntaxKind::Missing),
        0
    );

    let (green, exit) = run_statement("type Point\n= Value");
    assert_eq!(green.to_string(), "type Point");
    assert_eq!(
        count(&type_declaration_node(&green), SyntaxKind::Missing),
        0
    );
    assert!(matches!(
        exit,
        Some(Err(Either::Left(ref item))) if token_kind(item) == Some(TokenKind::Equals)
    ));

    for source in [
        "{type Point\nnext}",
        "catch action { A -> value with: type Point\n B -> fallback }",
        "catch action { A -> value with: mod M: type Point\n B -> fallback }",
        "f(value with: type Point, next)",
        "if c: value with: type Point else: fallback",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(
            SyntaxNode::new_root(green.clone())
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TypeDeclaration),
            "missing TypeDeclaration for {source:?}"
        );
        let declaration = type_declaration_node(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }

    let (green, _) = run_statement("{ x } with: type Point\n  next");
    let declaration = type_declaration_node(&green);
    assert_eq!(
        count(&declaration, SyntaxKind::Missing),
        1,
        "the completed braced block must not leak its line owner"
    );
}

#[test]
fn type_c14_preserves_handoff_through_record_pattern_defaults() {
    for source in [
        "{my {x = y with: type Point\n next} = rhs}",
        "catch action { A -> value with: for {x = y with: type Point\n next} in xs: B",
        "{my {x = y with: type Point, z} = rhs}",
        "{my {x = y with: type Point} = rhs}",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(
            SyntaxNode::new_root(green.clone())
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TypeDeclaration),
            "missing TypeDeclaration for {source:?}"
        );
        let declaration = type_declaration_node(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        assert_eq!(
            count(&declaration, SyntaxKind::TypeExpression),
            0,
            "{source:?}"
        );
    }

    let (green, _) = run_statement("catch action { A -> type Point\n B -> fallback }");
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::TypeDeclaration),
        "a zero-inline Catch arm must not enter canonical TypeDeclaration parsing"
    );
}

#[test]
fn type_c15_builds_direct_header_and_trailing_derives_clauses() {
    for (source, clauses, via) in [
        ("type Nominal derives Eq", 1, 0),
        ("type Generic 'a derives Eq", 1, 0),
        ("type Value derives Eq = Body derives Debug", 2, 0),
        (
            "type Value derives Eq, Debug via display = Body derives Show",
            2,
            1,
        ),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            clauses,
            "{source:?}"
        );
        assert_eq!(
            token_count(&declaration, SyntaxKind::DerivesKw),
            clauses,
            "{source:?}"
        );
        assert_eq!(
            token_count(&declaration, SyntaxKind::ViaKw),
            via,
            "{source:?}"
        );
        assert_eq!(
            declaration
                .children()
                .filter(|child| child.kind() == SyntaxKind::DerivesClause)
                .count(),
            clauses,
            "C15 clauses must be direct TypeDeclaration children: {source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }

    let (green, _) = run_statement("type Value derives Eq = Body derives Debug");
    let declaration = type_declaration_node(&green);
    assert_eq!(
        declaration
            .children()
            .filter(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::DerivesClause | SyntaxKind::TypeExpression
                )
            })
            .map(|child| child.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::DerivesClause,
            SyntaxKind::TypeExpression,
            SyntaxKind::DerivesClause,
        ]
    );
}

#[test]
fn type_c15_fresh_type_expression_edges_fence_contextual_words() {
    for source in [
        "type T = (Inner derives Inside) derives Outer",
        "type T = Call(Inner derives Inside) derives Outer",
        "type T = Head (Inner derives Inside) derives Outer",
        "type T = (Left -> Inner derives Inside) derives Outer",
        "type T = (for 'a: Inner derives Inside) derives Outer",
        "type T = ({field: Inner derives Inside}) derives Outer",
        "type T = ([Inner derives Inside] Result) derives Outer",
        "type T = ('[Inner derives Inside]) derives Outer",
        "type T = (:{Tag Inner derives Inside}) derives Outer",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            1,
            "{source:?}"
        );
        assert_eq!(
            token_count(&declaration, SyntaxKind::DerivesKw),
            1,
            "{source:?}"
        );
        assert_eq!(
            identifier_count(&declaration, "derives"),
            1,
            "the nested spelling remains an ordinary Identifier: {source:?}"
        );
    }
}

#[test]
fn type_c15_preserves_header_boundaries_and_nested_suspension() {
    for (source, committed, word, missing, errors) in [
        ("type T derives Eq with", "type T derives Eq", "with", 0, 0),
        (
            "type T derives Eq impl P",
            "type T derives Eq",
            "impl",
            0,
            0,
        ),
        ("type T derives with", "type T derives", "with", 1, 0),
        ("type T derives impl P", "type T derives", "impl", 1, 0),
        ("type T derives @ with", "type T derives @", "with", 0, 1),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), committed, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            1,
            "{source:?}"
        );
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
        assert_pending_word(exit, word);
    }

    for (source, equals) in [
        ("type Id derives Eq::@ = Int", 1),
        ("type Id derives (Eq::@ = Int) = Body", 2),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            1,
            "{source:?}"
        );
        assert_eq!(
            token_count(&declaration, SyntaxKind::Equals),
            equals,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
    }
}

#[test]
fn type_c15_recovers_clause_slots_without_consuming_successors() {
    for (source, clauses, via, missing, errors) in [
        ("type Id = derives Eq", 1, 0, 1, 0),
        ("type T derives Eq,", 1, 0, 1, 0),
        ("type T derives Eq, via key", 1, 1, 1, 0),
        ("type T derives Eq via @ key", 1, 1, 0, 1),
        ("type T derives Eq, derives Debug", 2, 0, 1, 0),
        ("type T derives Eq via derives Debug", 2, 1, 1, 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            clauses,
            "{source:?}"
        );
        assert_eq!(
            token_count(&declaration, SyntaxKind::ViaKw),
            via,
            "{source:?}"
        );
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
    }

    for source in [
        "type T = Int derives Eq with",
        "type T = Int derives (Eq with Inner) with",
        "type T derives Eq via with",
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(
            green.to_string(),
            source.strip_suffix(" with").expect("with suffix"),
            "{source:?}"
        );
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            1,
            "{source:?}"
        );
        assert_pending_word(exit, "with");
    }
}

#[test]
fn type_c15_threads_clause_gaps_only_through_ordinary_deeper_layout() {
    for source in [
        "type T\n  derives Eq",
        "type T derives\n  Eq",
        "type T derives Eq,\n  Debug",
        "type T derives Eq\n  via key",
        "type T derives Eq via\n  key",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            1,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }

    let (green, exit) = run_statement("type T derives\nEq");
    assert_eq!(green.to_string(), "type T derives");
    let declaration = type_declaration_node(&green);
    assert_eq!(count(&declaration, SyntaxKind::DerivesClause), 1);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert_pending_word(exit, "Eq");

    for source in [
        "{type T derives\n next}",
        "catch action { A -> value with: type T derives\n B -> fallback }",
        "{type T = Value derives\n next}",
        "catch action { A -> value with: type T = Value derives\n B -> fallback }",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            1,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Missing), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }
}

#[test]
fn type_c15_contextual_words_remain_exact() {
    for (source, clauses) in [
        ("type T derivesx = viax", 0),
        ("type T = derivesx viax withx implx", 0),
        ("type T derives Eq viax", 1),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            clauses,
            "{source:?}"
        );
        assert_eq!(
            token_count(&declaration, SyntaxKind::DerivesKw),
            clauses,
            "{source:?}"
        );
        assert_eq!(
            token_count(&declaration, SyntaxKind::ViaKw),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn type_c15_keeps_with_outer_only_for_derives_roles() {
    for source in [
        "type T = Body derives (Eq with Inner) with",
        "type T = Body derives Call(Eq with Inner) with",
        "type T = Body derives Head (Eq with Inner) with",
        "type T = Body derives (Left -> Eq with Inner) with",
        "type T = Body derives (for 'a: Eq with Inner) with",
        "type T = Body derives ({field: Eq with Inner}) with",
        "type T = Body derives ([Eq with Inner] Result) with",
        "type T = Body derives ('[Eq with Inner]) with",
        "type T = Body derives (:{Tag Eq with Inner}) with",
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(
            green.to_string(),
            source.strip_suffix(" with").expect("outer with suffix"),
            "{source:?}"
        );
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            1,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        assert_eq!(identifier_count(&declaration, "with"), 1, "{source:?}");
        assert_pending_word(exit, "with");
    }
}

#[test]
fn type_c15_keeps_existing_name_and_terminal_ownership() {
    let (green, _) = run_statement("type derives Eq");
    assert_eq!(green.to_string(), "type derives Eq");
    assert_eq!(
        count(&type_declaration_node(&green), SyntaxKind::DerivesClause),
        0
    );

    let (green, _) = run_statement("type = derives Eq");
    assert_eq!(green.to_string(), "type = derives Eq");
    let declaration = type_declaration_node(&green);
    assert_eq!(count(&declaration, SyntaxKind::DerivesClause), 1);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 2);

    let (green, exit) = run_statement("type T derives Eq;");
    assert_eq!(green.to_string(), "type T derives Eq");
    assert_eq!(
        count(&type_declaration_node(&green), SyntaxKind::Missing),
        0
    );
    assert!(matches!(
        exit,
        Some(Err(Either::Left(ref item))) if token_kind(item) == Some(TokenKind::Semicolon)
    ));

    let (green, _) = run_statement("{type T derives Eq}");
    assert_eq!(green.to_string(), "{type T derives Eq}");
    assert_eq!(
        count(&type_declaration_node(&green), SyntaxKind::DerivesClause),
        1
    );

    let (green, exit) = run_statement_with_stops(
        "type T derives Eq]",
        &OperatorTable::empty(),
        stops_for(TokenKind::RBracket),
    );
    assert_eq!(green.to_string(), "type T derives Eq");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(ref item))) if token_kind(item) == Some(TokenKind::RBracket)
    ));
}

#[test]
fn type_c15_preserves_boundaries_in_path_and_forall_binder_recovery() {
    let (green, _) = run_statement("type T derives Eq::= Body");
    assert_eq!(green.to_string(), "type T derives Eq::= Body");
    let declaration = type_declaration_node(&green);
    assert_eq!(count(&declaration, SyntaxKind::DerivesClause), 1);
    assert_eq!(token_count(&declaration, SyntaxKind::Equals), 1);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert_eq!(count(&declaration, SyntaxKind::Error), 0);

    for (source, missing, errors) in [
        ("type T derives for derives Eq", 1, 0),
        ("type T derives for @ derives Eq", 0, 1),
        ("type T derives for 'a derives Eq", 1, 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            2,
            "{source:?}"
        );
        assert_eq!(
            token_count(&declaration, SyntaxKind::DerivesKw),
            2,
            "{source:?}"
        );
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
    }

    let source = "type T derives for 'a: Inner derives Inside = Body";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let declaration = type_declaration_node(&green);
    assert_eq!(count(&declaration, SyntaxKind::DerivesClause), 1);
    assert_eq!(token_count(&declaration, SyntaxKind::DerivesKw), 1);
    assert_eq!(identifier_count(&declaration, "derives"), 1);
}

#[test]
fn type_c15_clause_gaps_preserve_outer_owned_items_for_every_handoff() {
    use super::super::statement::StatementLineHandoff;

    let positions = [
        ("type T derives", "Role", 1),
        ("type T derives Eq,", "Role", 1),
        ("type T derives Eq", "via", 0),
        ("type T derives Eq via", "target", 1),
    ];
    for (handoff, gap) in [
        (StatementLineHandoff::OrdinaryLayout, "\n"),
        (StatementLineHandoff::BracedStatementSequence, "\n  "),
        (
            StatementLineHandoff::CatchArmSequenceThroughInlineCanonicalStatement,
            "\n  ",
        ),
    ] {
        for (prefix, pending, missing) in positions {
            let source = format!("{prefix}{gap}{pending}");
            let (green, exit) = run_type_declaration_with_handoff(&source, handoff);
            assert_eq!(green.to_string(), prefix, "{handoff:?}, {source:?}");
            let declaration = type_declaration_node(&green);
            assert_eq!(
                count(&declaration, SyntaxKind::DerivesClause),
                1,
                "{handoff:?}, {source:?}"
            );
            assert_eq!(
                count(&declaration, SyntaxKind::Missing),
                missing,
                "{handoff:?}, {source:?}"
            );
            assert_eq!(
                count(&declaration, SyntaxKind::Error),
                0,
                "{handoff:?}, {source:?}"
            );
            assert_pending_word_with_leading(exit, pending, gap);
        }
    }
}

#[test]
fn type_c15_zero_catch_distinguishes_header_and_trailing_clause_recovery() {
    use super::super::statement::StatementLineHandoff;

    let header_positions = [
        ("type T derives", "Role", 2),
        ("type T derives Eq,", "Role", 2),
        ("type T derives Eq", "via", 1),
        ("type T derives Eq via", "target", 2),
    ];
    for (prefix, successor, missing) in header_positions {
        let source = format!("{prefix}\n  {successor}");
        let (green, exit) =
            run_type_declaration_with_handoff(&source, StatementLineHandoff::CatchBracedArm);
        assert_eq!(green.to_string(), source, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            1,
            "{source:?}"
        );
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
    }

    let trailing_positions = [
        ("type T = Body derives", "Role", 1),
        ("type T = Body derives Eq,", "Role", 1),
        ("type T = Body derives Eq", "via", 0),
        ("type T = Body derives Eq via", "target", 1),
    ];
    for (prefix, pending, missing) in trailing_positions {
        let source = format!("{prefix}\n  {pending}");
        let (green, exit) =
            run_type_declaration_with_handoff(&source, StatementLineHandoff::CatchBracedArm);
        assert_eq!(green.to_string(), prefix, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            1,
            "{source:?}"
        );
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        assert_pending_word_with_leading(exit, pending, "\n  ");
    }
}

#[test]
fn type_c15_retains_outer_boundary_trivia_through_rhs_path_and_forall() {
    let (green, _) = run_statement("{type T =\n  derives Eq}");
    assert_eq!(green.to_string(), "{type T =\n  derives Eq}");
    let declaration = type_declaration_node(&green);
    assert_eq!(count(&declaration, SyntaxKind::DerivesClause), 0);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);

    for source in [
        "{type T derives Eq::\n  derives Show}",
        "{type T derives for\n  derives Eq}",
        "{type T derives for 'a\n  derives Eq}",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            1,
            "the newline successor belongs to the braced statement owner: {source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Missing), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }
}

#[test]
fn type_c15_header_handoff_and_rhs_retry_keep_single_owners() {
    use super::super::statement::StatementLineHandoff;

    for (source, committed, missing, errors) in [
        ("type T derives Eq with:", "type T derives Eq", 0, 0),
        ("type T derives with:", "type T derives", 1, 0),
        ("type T derives @ with:", "type T derives @", 0, 1),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), committed, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            1,
            "{source:?}"
        );
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
        assert_pending_word_with_leading(exit, "with", " ");
    }

    let source = "type T derives Eq\n  with";
    let (green, exit) =
        run_type_declaration_with_handoff(source, StatementLineHandoff::CatchBracedArm);
    assert_eq!(green.to_string(), "type T derives Eq\n  ");
    let declaration = type_declaration_node(&green);
    assert_eq!(count(&declaration, SyntaxKind::DerivesClause), 1);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert_eq!(count(&declaration, SyntaxKind::Error), 0);
    assert_pending_word_with_leading(exit, "with", "");

    let source = "type T derives Eq\n  impl";
    let (green, exit) =
        run_type_declaration_with_handoff(source, StatementLineHandoff::CatchBracedArm);
    assert_eq!(green.to_string(), "type T derives Eq\n  ");
    let declaration = type_declaration_node(&green);
    assert_eq!(count(&declaration, SyntaxKind::DerivesClause), 1);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert_eq!(count(&declaration, SyntaxKind::Error), 0);
    assert_pending_word_with_leading(exit, "impl", "");

    for (source, missing, errors) in [
        ("type T = @ derives Eq", 0, 1),
        ("type T = @ Body derives Eq", 0, 1),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let declaration = type_declaration_node(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::DerivesClause),
            1,
            "{source:?}"
        );
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
    }
}

#[test]
fn type_c15_contextual_via_and_adjacent_roles_stay_type_syntax() {
    let (green, _) = run_statement("type T = via");
    assert_eq!(green.to_string(), "type T = via");
    let declaration = type_declaration_node(&green);
    assert_eq!(token_count(&declaration, SyntaxKind::ViaKw), 0);
    assert_eq!(identifier_count(&declaration, "via"), 1);

    let (green, _) = run_statement("type T derives Eq Show");
    assert_eq!(green.to_string(), "type T derives Eq Show");
    let declaration = type_declaration_node(&green);
    assert_eq!(count(&declaration, SyntaxKind::DerivesClause), 1);
    assert_eq!(count(&declaration, SyntaxKind::TypeExpression), 2);
    assert_eq!(count(&declaration, SyntaxKind::TypeApplyArgument), 1);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 0);
    assert_eq!(count(&declaration, SyntaxKind::Error), 0);
}

#[test]
fn type_c15_keeps_active_else_companion_outside_a_completed_clause() {
    let source = "if c: value with: type T derives Eq else: fallback";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);

    let declaration = type_declaration_node(&green);
    assert_eq!(count(&declaration, SyntaxKind::DerivesClause), 1);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 0);
    assert_eq!(count(&declaration, SyntaxKind::Error), 0);

    let root = SyntaxNode::new_root(green);
    assert_eq!(count(&root, SyntaxKind::IfExpression), 1);
    assert_eq!(count(&root, SyntaxKind::ElseArm), 1);
}
