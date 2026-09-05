use super::*;

fn binding(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BindingStatement)
        .expect("BindingStatement")
}

#[test]
fn binding_c8_builds_canonical_header_and_optional_body_topology() {
    for (source, visibility) in [
        ("my x", SyntaxKind::MyKw),
        ("our x", SyntaxKind::OurKw),
        ("pub x", SyntaxKind::PubKw),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = binding(&green);
        assert_eq!(
            declaration
                .children()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [SyntaxKind::BindingHeader],
            "{source:?}"
        );
        let header = declaration.first_child().expect("BindingHeader");
        assert_eq!(
            header.first_token().map(|token| token.kind()),
            Some(visibility)
        );
        assert!(
            header
                .children()
                .any(|node| node.kind() == SyntaxKind::Pattern)
        );
        assert!(
            !declaration
                .children()
                .any(|node| node.kind() == SyntaxKind::BindingBody)
        );
    }

    let (green, exit) = run_statement("my A | B as name = value");
    assert_eq!(green.to_string(), "my A | B as name = value");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = binding(&green);
    assert_eq!(
        declaration
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::BindingHeader, SyntaxKind::BindingBody]
    );
    let header = declaration.first_child().expect("BindingHeader");
    assert_eq!(
        header
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Equals)
            .count(),
        1
    );
    let body = declaration.last_child().expect("BindingBody");
    assert_eq!(
        body.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::OperatorChain]
    );

    let source = "my /*after visibility*/ x /*before equals*/ = /*after equals*/ value";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let declaration = binding(&green);
    let header = declaration.first_child().expect("BindingHeader");
    let body = declaration.last_child().expect("BindingBody");
    assert_eq!(
        header
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::BlockComment)
            .count(),
        2
    );
    assert_eq!(
        body.children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::BlockComment)
            .count(),
        1
    );
    assert!(
        !header
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Pattern)
            .expect("Pattern")
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::BlockComment)
    );
}

#[test]
fn binding_c8_reuses_full_current_pattern_surface_and_exact_equals_stop() {
    for source in [
        "my (a, b) = value",
        "my [a, ..rest] = value",
        "my {a: b, c = 1} = value",
        "my :tag = value",
        "my x: T = value",
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = binding(&green);
        assert_eq!(
            declaration
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Equals)
                .count(),
            source.matches('=').count(),
            "{source:?}"
        );
        assert!(
            declaration
                .children()
                .any(|node| node.kind() == SyntaxKind::BindingBody)
        );
    }

    for source in ["my x == value", "my x => value"] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), "my x", "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Left(_)))), "{source:?}");
        assert!(
            !binding(&green)
                .children()
                .any(|node| node.kind() == SyntaxKind::BindingBody)
        );
    }

    let (green, exit) = run_statement("my x\n= y");
    assert_eq!(green.to_string(), "my x");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::Equals)
                && item.leading_view().has_ordinary_newline()
    ));
    let declaration = binding(&green);
    assert!(
        !declaration
            .children()
            .any(|node| node.kind() == SyntaxKind::BindingBody)
    );
    assert!(
        !declaration
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Equals)
    );

    let source = "my x\n  = y";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = binding(&green);
    assert!(
        declaration
            .children()
            .any(|node| node.kind() == SyntaxKind::BindingBody)
    );
    assert!(
        declaration
            .first_child()
            .expect("BindingHeader")
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Equals)
    );
}

#[test]
fn binding_c8_distinguishes_inline_strict_deeper_and_wrong_indent_bodies() {
    let (green, _) = run_statement("my x =  value");
    let body = binding(&green).last_child().expect("inline BindingBody");
    assert_eq!(body.text().to_string(), "  value");
    assert_eq!(
        body.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::OperatorChain]
    );

    let source = "my x =\n  my y = 1\n  y";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let body = binding(&green).last_child().expect("indented BindingBody");
    let block = body
        .children()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("IndentedStatementBlock");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        2
    );
    assert_eq!(
        block
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::BindingStatement)
            .count(),
        1
    );

    let (green, exit) = run_statement("my x =\ny");
    assert_eq!(green.to_string(), "my x =");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    let body = binding(&green).last_child().expect("missing BindingBody");
    assert_eq!(
        body.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::Missing]
    );
}

#[test]
fn binding_c8_totalizes_target_and_accepted_body_slots_once() {
    for (source, missing, error) in [
        ("my", 1, 0),
        ("my = value", 1, 0),
        ("my @ x = value", 0, 1),
        ("my x =", 1, 0),
        ("my x = @ value", 0, 1),
        ("my x = @", 0, 1),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = binding(&green);
        assert_eq!(
            declaration
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
        assert_eq!(
            declaration
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            error,
            "{source:?}"
        );
    }

    let (green, _) = run_statement("my x");
    assert!(
        !binding(&green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    for (source, missing, error) in [("my x;", 0, 0), ("my x =;", 1, 0), ("my x = @;", 0, 1)] {
        let (green, exit) = run_statement(source);
        assert_eq!(
            green.to_string(),
            source.trim_end_matches(';'),
            "{source:?}"
        );
        assert!(matches!(
            exit,
            Some(Err(Either::Left(item)))
                if item.payload_view().token_kind() == Some(TokenKind::Semicolon)
        ));
        let declaration = binding(&green);
        assert_eq!(
            declaration
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
        assert_eq!(
            declaration
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            error,
            "{source:?}"
        );
    }

    let (green, exit) = run_statement("my\nx");
    assert_eq!(green.to_string(), "my");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.leading_view().has_ordinary_newline()
    ));
    assert_eq!(
        binding(&green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn binding_c8_keeps_statement_head_reservation_source_only_and_exact() {
    let (green, _) = run_statement("my use = value");
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );

    for source in [
        "my use path",
        "my mod = value",
        "my struct = value",
        "my type = value",
        "my role = value",
        "my impl = value",
        "my cast = value",
        "my enum Name = value",
        "my error Name = value",
        "my act Name = value",
        "our enum = value",
        "pub act = value",
        "my lazy value",
        "my prefix value",
    ] {
        let (green, _) = run_statement(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::BindingStatement),
            "{source:?}"
        );
    }

    for source in [
        "my enum = value",
        "my error = value",
        "my act = value",
        "my lazy = value",
        "my prefix = value",
        "my infix = value",
        "my suffix = value",
        "my nullfix = value",
    ] {
        let (green, _) = run_statement(source);
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::BindingStatement),
            "{source:?}"
        );
    }

    for source in ["myx = value", "ours = value", "public = value"] {
        let (green, _) = run_statement(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::BindingStatement),
            "{source:?}"
        );
    }

    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "my",
        OperatorFixities::new().with_prefix(BindingPower::scalar(40)),
    )])
    .expect("visibility/operator collision table");
    let (green, _) = run_statement_with("my x = value", &operators);
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );
    let (green, _) = run_with("my x", &operators);
    let root = SyntaxNode::new_root(green);
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );
}

#[test]
fn binding_c8_is_canonical_in_braced_indented_and_with_statement_slots_only() {
    for source in [
        "{my x = 1; x}",
        "f:\n  my x = 1\n  x",
        "if c:\n  my x = 1\n  x",
        "case x:\n  p ->\n    my y = 1\n    y",
        "value with: my x = 1",
        "value with:\n  my x = 1\n  x",
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::BindingStatement),
            "{source:?}"
        );
    }

    for source in [
        "f: my x = 1",
        "if c: my x = 1",
        "case x: p -> my y = 1",
        "catch x: p -> my y = 1",
    ] {
        let (green, _) = run(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::BindingStatement),
            "{source:?}"
        );
    }
}

#[test]
fn binding_c8_leaves_statement_boundaries_and_opening_trivia_with_their_owners() {
    let source = "{my x = 1;  my y = 2}";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let bindings = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::BindingStatement)
        .collect::<Vec<_>>();
    assert_eq!(bindings.len(), 2);
    assert!(bindings.iter().all(|binding| {
        !binding
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Semicolon)
    }));
    let separator = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
        .expect("BlockStatementSeparator");
    assert_eq!(separator.text().to_string(), ";  ");

    let (green, exit) = run("f:\n  my x = 1\ny");
    assert_eq!(green.to_string(), "f:\n  my x = 1");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    let source = "f:\n  my x =\n  y";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("IndentedStatementBlock");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        2
    );
    let binding = block
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BindingStatement)
        .expect("BindingStatement");
    assert_eq!(
        binding
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let source = "f:\n  my\n  y";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        2
    );
}
