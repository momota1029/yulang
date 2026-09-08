use super::*;

fn for_node(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForStatement)
        .expect("ForStatement")
}

fn count(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    node.descendants()
        .filter(|descendant| descendant.kind() == kind)
        .count()
}

fn token_texts(node: &SyntaxNode, kind: SyntaxKind) -> Vec<String> {
    node.descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == kind)
        .map(|token| token.text().to_owned())
        .collect()
}

#[test]
fn for_c13_builds_the_exact_colon_indented_topology() {
    let source = "for x in xs:\n  x";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let statement = for_node(&green);
    assert_eq!(
        format!("{statement:#?}"),
        concat!(
            "ForStatement@0..16\n",
            "  ForKw@0..3 \"for\"\n",
            "  Whitespace@3..4 \" \"\n",
            "  Pattern@4..5\n",
            "    IdentifierPattern@4..5\n",
            "      Identifier@4..5 \"x\"\n",
            "  Whitespace@5..6 \" \"\n",
            "  InKw@6..8 \"in\"\n",
            "  Whitespace@8..9 \" \"\n",
            "  ForIterable@9..11\n",
            "    OperatorChain@9..11\n",
            "      IdentifierExpression@9..11\n",
            "        Identifier@9..11 \"xs\"\n",
            "  Colon@11..12 \":\"\n",
            "  IndentedStatementBlock@12..16\n",
            "    Newline@12..13 \"\\n\"\n",
            "    Whitespace@13..15 \"  \"\n",
            "    Statement@15..16\n",
            "      OperatorChain@15..16\n",
            "        IdentifierExpression@15..16\n",
            "          Identifier@15..16 \"x\"\n",
        )
    );
    assert_eq!(
        statement.parent().map(|node| node.kind()),
        Some(SyntaxKind::Statement)
    );
    assert_eq!(count(&statement, SyntaxKind::Missing), 0);
    assert_eq!(count(&statement, SyntaxKind::Error), 0);
}

#[test]
fn for_c13_accepts_all_three_body_forms_without_extra_wrappers() {
    for source in ["for x in xs: x", "for x in xs:\n  x", "for x in xs { x }"] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let statement = for_node(&green);
        assert_eq!(count(&statement, SyntaxKind::ForIterable), 1, "{source:?}");
        assert_eq!(count(&statement, SyntaxKind::Missing), 0, "{source:?}");
    }

    let (green, _) = run_statement("for x in xs: x");
    let statement = for_node(&green);
    assert_eq!(
        statement
            .children()
            .filter(|child| child.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );
    assert_eq!(count(&statement, SyntaxKind::Statement), 0);

    let (green, _) = run_statement("for x in xs { x }");
    let statement = for_node(&green);
    assert_eq!(
        count(&statement, SyntaxKind::BracedStatementBlockExpression),
        1
    );
    assert_eq!(count(&statement, SyntaxKind::Statement), 1);
}

#[test]
fn for_c13_label_probe_accepts_only_a_real_label() {
    let (green, _) = run_statement("for 'outer x in xs: x");
    let statement = for_node(&green);
    assert_eq!(green.to_string(), "for 'outer x in xs: x");
    assert_eq!(
        token_texts(&statement, SyntaxKind::SigilIdentifier),
        ["'outer"]
    );
    assert_eq!(count(&statement, SyntaxKind::ForLabel), 1);

    for source in ["for 'x in xs: x", "for 'outer in xs: x"] {
        let (green, _) = run_statement(source);
        let statement = for_node(&green);
        assert_eq!(green.to_string(), source);
        assert_eq!(count(&statement, SyntaxKind::ForLabel), 0, "{source:?}");
        assert_eq!(
            count(&statement, SyntaxKind::IdentifierPattern),
            1,
            "{source:?}"
        );
        assert_eq!(count(&statement, SyntaxKind::Missing), 0, "{source:?}");
    }

    for source in ["for 'x", "for '[E]", "for '{ x }"] {
        let (green, _) = run_statement(source);
        let statement = for_node(&green);
        assert_eq!(count(&statement, SyntaxKind::ForLabel), 0, "{source:?}");
    }
}

#[test]
fn for_c13_statement_dispatch_is_exact_and_visibility_stays_binding() {
    for source in ["forall", "fork", "format"] {
        let (green, _) = run_statement(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::ForStatement),
            "{source:?}"
        );
    }

    let (green, _) = run_statement("my for = 1");
    let root = SyntaxNode::new_root(green);
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ForStatement)
    );

    let (green, _) = run("for x in xs: x");
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ForStatement)
    );
}

#[test]
fn for_c13_pattern_and_annotation_stop_at_exact_in() {
    for source in [
        "for x: T in xs: x",
        "for (x, y) in pairs: x",
        "for x | y in xs: x",
        "for x as y in xs: x",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let statement = for_node(&green);
        assert_eq!(
            token_texts(&statement, SyntaxKind::InKw),
            ["in"],
            "{source:?}\n{statement:#?}"
        );
        assert_eq!(count(&statement, SyntaxKind::Missing), 0, "{source:?}");
    }

    let (green, _) = run_statement("for x: Inner in index: x");
    let statement = for_node(&green);
    assert_eq!(
        token_texts(&statement, SyntaxKind::InKw),
        ["in"],
        "{statement:#?}"
    );
    assert_eq!(
        token_texts(&statement, SyntaxKind::Identifier),
        ["x", "Inner", "index", "x"]
    );
}

#[test]
fn for_c13_missing_and_malformed_patterns_do_not_confuse_in() {
    let (green, _) = run_statement("for in xs: x");
    let statement = for_node(&green);
    assert_eq!(green.to_string(), "for in xs: x");
    assert_eq!(count(&statement, SyntaxKind::Missing), 1);
    assert_eq!(
        token_texts(&statement, SyntaxKind::InKw),
        ["in"],
        "{statement:#?}"
    );

    let (green, exit) = run_statement("for @ in xs: x");
    let statement = for_node(&green);
    assert_eq!(green.to_string(), "for @");
    assert_eq!(count(&statement, SyntaxKind::Error), 1);
    assert_eq!(
        token_texts(&statement, SyntaxKind::InKw),
        Vec::<String>::new()
    );
    assert!(matches!(
        exit,
        Some(Err(Either::Left(ref item))) if item_word_for_test(item) == Some("in")
    ));

    for source in [
        "for x | in xs: x",
        "for x as in xs: x",
        "for x: in xs: x",
        "for (x |) in xs: x",
    ] {
        let (green, exit) = run_statement(source);
        let statement = for_node(&green);
        assert_eq!(
            token_texts(&statement, SyntaxKind::InKw),
            Vec::<String>::new()
        );
        assert!(
            matches!(exit, Some(Err(Either::Left(ref item))) if item_word_for_test(item) == Some("in")),
            "{source:?}\n{statement:#?}"
        );
    }

    let (green, _) = run_statement("for @ x in xs: x");
    let statement = for_node(&green);
    assert_eq!(green.to_string(), "for @ x in xs: x");
    assert_eq!(count(&statement, SyntaxKind::Error), 1);
    assert_eq!(count(&statement, SyntaxKind::Missing), 0);
    assert_eq!(token_texts(&statement, SyntaxKind::InKw), ["in"]);

    for source in ["for: x", "for { x }"] {
        let (green, _) = run_statement(source);
        let statement = for_node(&green);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(count(&statement, SyntaxKind::Missing), 1, "{source:?}");
    }
}

#[test]
fn for_c13_in_and_iterable_recovery_obey_truncation() {
    let (green, _) = run_statement("for x xs: x");
    let statement = for_node(&green);
    assert_eq!(green.to_string(), "for x xs: x");
    assert_eq!(count(&statement, SyntaxKind::Missing), 1);
    assert_eq!(
        token_texts(&statement, SyntaxKind::InKw),
        Vec::<String>::new()
    );
    assert_eq!(count(&statement, SyntaxKind::ForIterable), 1);

    for (source, missing) in [("for x:", 1), ("for x { x }", 1)] {
        let (green, _) = run_statement(source);
        let statement = for_node(&green);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(
            count(&statement, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&statement, SyntaxKind::ForIterable), 0, "{source:?}");
    }

    for source in ["for x in: x", "for x in { x }"] {
        let (green, _) = run_statement(source);
        let statement = for_node(&green);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(count(&statement, SyntaxKind::Missing), 1, "{source:?}");
        assert_eq!(count(&statement, SyntaxKind::ForIterable), 1, "{source:?}");
    }

    let (green, _) = run_statement("for x in @ xs: x");
    let statement = for_node(&green);
    assert_eq!(green.to_string(), "for x in @ xs: x");
    assert_eq!(count(&statement, SyntaxKind::Error), 1);
    assert_eq!(count(&statement, SyntaxKind::Missing), 0);
}

#[test]
fn for_c13_body_boundaries_remain_outer_owned() {
    for source in ["for x in xs;", "for x in xs,", "for x in xs"] {
        let (green, exit) = run_statement(source);
        let statement = for_node(&green);
        let expected = source.trim_end_matches([';', ',']);
        assert_eq!(green.to_string(), expected, "{source:?}");
        assert_eq!(count(&statement, SyntaxKind::Missing), 1, "{source:?}");
        if source.ends_with([';', ',']) {
            assert!(matches!(exit, Some(Err(Either::Left(_)))), "{source:?}");
        }
    }

    for source in ["for x in xs:;", "for x in xs:,", "for x in xs:\nnext"] {
        let (green, exit) = run_statement(source);
        let statement = for_node(&green);
        assert_eq!(count(&statement, SyntaxKind::Missing), 1, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Left(_)))), "{source:?}");
    }

    let (green, exit) = run_statement("for x in xs: body; sibling");
    assert_eq!(green.to_string(), "for x in xs: body");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(ref item))) if token_kind(item) == Some(TokenKind::Semicolon)
    ));

    for source in ["for x in xs @ : body", "for x in xs @ { body }"] {
        let (green, _) = run_statement(source);
        let statement = for_node(&green);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(count(&statement, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&statement, SyntaxKind::Missing), 0, "{source:?}");
    }
}

#[test]
fn for_c13_active_closes_and_label_boundaries_stay_pending() {
    let operators = OperatorTable::empty();
    for (source, close) in [
        ("for x in xs)", TokenKind::RParen),
        ("for x in xs]", TokenKind::RBracket),
        ("for x in xs}", TokenKind::RBrace),
    ] {
        let (green, exit) = run_statement_with_stops(source, &operators, stops_for(close));
        let statement = for_node(&green);
        assert_eq!(green.to_string(), "for x in xs", "{source:?}");
        assert_eq!(count(&statement, SyntaxKind::Missing), 1, "{source:?}");
        assert!(
            matches!(exit, Some(Err(Either::Left(ref item))) if token_kind(item) == Some(close)),
            "{source:?}"
        );
    }

    let (green, exit) =
        run_statement_with_stops("for 'x)", &operators, stops_for(TokenKind::RParen));
    let statement = for_node(&green);
    assert_eq!(green.to_string(), "for 'x");
    assert_eq!(count(&statement, SyntaxKind::ForLabel), 0);
    assert_eq!(count(&statement, SyntaxKind::IdentifierPattern), 1);
    assert!(matches!(
        exit,
        Some(Err(Either::Left(ref item))) if token_kind(item) == Some(TokenKind::RParen)
    ));
}

#[test]
fn for_c13_nested_blocks_use_canonical_statements_but_inline_does_not() {
    for source in [
        "for x in xs { for y in ys: y }",
        "for x in xs:\n  for y in ys: y",
        "for ({x}) in xs: x",
        "mod M { for x in xs: x }",
        "my value =\n  for x in xs: x",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(count(&SyntaxNode::new_root(green), SyntaxKind::ForStatement) >= 1);
    }

    let (green, exit) = run_statement("for x in xs: for y in ys: y");
    let root = SyntaxNode::new_root(green);
    assert_eq!(count(&root, SyntaxKind::ForStatement), 1);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
}

#[test]
fn for_c13_inline_body_leaves_a_same_indent_sibling_to_the_enclosing_sequence() {
    let source = "my body =\n  for x in xs: if x: y\n  z";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("enclosing IndentedStatementBlock");
    let siblings: Vec<_> = block
        .children()
        .filter(|node| node.kind() == SyntaxKind::Statement)
        .collect();
    assert_eq!(siblings.len(), 2, "{block:#?}");
    assert_eq!(count(&root, SyntaxKind::ForStatement), 1);
    assert!(
        siblings[0]
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ForStatement)
    );
    assert_eq!(token_texts(&siblings[1], SyntaxKind::Identifier), ["z"]);

    let statement = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForStatement)
        .expect("ForStatement");
    let inline = statement
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("inline body OperatorChain");
    assert!(!token_texts(&inline, SyntaxKind::Identifier).contains(&"z".to_owned()));
}

#[test]
fn for_c13_use_group_and_header_layout_preserve_the_pending_item() {
    let (green, exit) = run_statement("use {a\nfor x in xs: x}");
    assert_eq!(green.to_string(), "use {a");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(ref item))) if item_word_for_test(item) == Some("for")
    ));

    for source in ["for\nx in xs: x", "for x\nin xs: x", "for x in\nxs: x"] {
        let (green, exit) = run_statement(source);
        assert!(green.to_string().len() < source.len(), "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Left(_)))), "{source:?}");
    }

    for source in [
        "for\n  x in xs: x",
        "for x\n  in xs: x",
        "for x in\n  xs: x",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
    }
}

fn item_word_for_test(item: &super::super::item::Item) -> Option<&str> {
    (item.payload_view().token_kind() == Some(TokenKind::Identifier))
        .then(|| item.payload_view().spelling())
        .flatten()
}
