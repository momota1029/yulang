use super::*;

#[test]
fn fixed_field_and_path_tails_keep_their_own_tokens() {
    let source = "a .field:: name b";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    assert_eq!(
        outer.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::FieldTail,
            SyntaxKind::PathTail,
            SyntaxKind::MlArgument,
        ]
    );
    let field = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::FieldTail)
        .expect("field tail");
    assert_eq!(
        field
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Dot, ".".to_owned()),
            (SyntaxKind::Identifier, "field".to_owned()),
        ]
    );
    let path = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::PathTail)
        .expect("path tail");
    assert_eq!(
        path.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "name".to_owned()),
        ]
    );
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn path_tails_classify_sigil_segments() {
    let source = "a::$value?:: &reference::'label::_hidden::_";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let paths = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::PathTail)
        .map(|path| {
            path.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::ColonColon
                            | SyntaxKind::Identifier
                            | SyntaxKind::SigilIdentifier
                    )
                })
                .map(|token| (token.kind(), token.text().to_owned()))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        paths,
        [
            vec![
                (SyntaxKind::ColonColon, "::".to_owned()),
                (SyntaxKind::SigilIdentifier, "$value?".to_owned()),
            ],
            vec![
                (SyntaxKind::ColonColon, "::".to_owned()),
                (SyntaxKind::SigilIdentifier, "&reference".to_owned()),
            ],
            vec![
                (SyntaxKind::ColonColon, "::".to_owned()),
                (SyntaxKind::SigilIdentifier, "'label".to_owned()),
            ],
            vec![
                (SyntaxKind::ColonColon, "::".to_owned()),
                (SyntaxKind::SigilIdentifier, "_hidden".to_owned()),
            ],
            vec![
                (SyntaxKind::ColonColon, "::".to_owned()),
                (SyntaxKind::Identifier, "_".to_owned()),
            ],
        ]
    );
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn fixed_tails_keep_missing_and_invalid_identifier_slots_local() {
    for (source, tail_kind, recovery_kind) in [
        ("x.", SyntaxKind::FieldTail, SyntaxKind::Missing),
        ("x.@", SyntaxKind::FieldTail, SyntaxKind::Error),
        ("x::", SyntaxKind::PathTail, SyntaxKind::Missing),
        ("x::123", SyntaxKind::PathTail, SyntaxKind::Error),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let tail = root
            .descendants()
            .find(|node| node.kind() == tail_kind)
            .expect("fixed tail");
        assert_eq!(
            tail.children()
                .filter(|node| node.kind() == recovery_kind)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run("x::::name");
    assert_eq!(green.to_string(), "x::::name");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::PathTail)
            .count(),
        2
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn double_dot_is_not_a_field_tail() {
    for source in ["a..", "a..."] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), "a", "{source:?}");
        assert!(
            matches!(
                exit,
                Some(Err(Either::Left(item)))
                    if matches!(item.payload, Payload::Token(ref token)
                        if token.kind == TokenKind::Unknown && &*token.text == ".")
            ),
            "{source:?}"
        );
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::FieldTail),
            "{source:?}"
        );
    }
}

#[test]
fn lone_colon_tail_is_terminal_and_preserves_outer_comma_ownership() {
    let (green, exit) = run("f: x");
    assert_eq!(green.to_string(), "f: x");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        operator_chain_children(&green),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::ColonApplicationTail,
        ]
    );

    let operators = dynamic_operator_table();
    let (green, exit) = run_with("a + b: x", &operators);
    assert_eq!(green.to_string(), "a + b: x");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    assert_eq!(
        chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::IdentifierExpression,
            SyntaxKind::ColonApplicationTail,
        ]
    );
    let colon = chain
        .children()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .expect("colon tail");
    assert_eq!(
        colon.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::OperatorChain]
    );

    let (green, exit) = run("f: x, y");
    assert_eq!(green.to_string(), "f: x, y");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let colon = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .expect("colon tail");
    assert_eq!(
        colon
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        2
    );
    assert_eq!(
        colon
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Comma)
            .count(),
        1
    );

    let (green, exit) = run("(f: x, y)");
    assert_eq!(green.to_string(), "(f: x, y)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let colon = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .expect("colon tail");
    assert_eq!(
        colon
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Comma)
            .count(),
        1
    );

    let (green, exit) = run("f::T");
    assert_eq!(green.to_string(), "f::T");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::PathTail)
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ColonApplicationTail)
    );

    let (green, exit) = run("f\n: x");
    assert_eq!(green.to_string(), "f");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::Colon)
    ));
}

#[test]
fn with_colon_is_reserved_for_its_dedicated_tail_owner() {
    let (green, exit) = run("f with: x");
    assert_eq!(green.to_string(), "f");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token)
                if token.kind == TokenKind::Identifier && &*token.text == "with")
    ));
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ColonApplicationTail)
    );
}

#[test]
fn colon_c1_handoffs_before_an_unimplemented_mandatory_slot() {
    for source in ["f:", "f:\nx", "f:\n  ", "f: @"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), "f", "{source:?}");
        assert!(matches!(
            exit,
            Some(Err(Either::Left(item)))
                if matches!(item.payload, Payload::Token(ref token)
                    if token.kind == TokenKind::Colon)
        ));
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        );
    }

    for source in ["f: x,", "f: x,\n y", "f: x, @"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), "f: x", "{source:?}");
        assert!(matches!(
            exit,
            Some(Err(Either::Left(item)))
                if matches!(item.payload, Payload::Token(ref token)
                    if token.kind == TokenKind::Comma)
        ));
        let root = SyntaxNode::new_root(green);
        let colon = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .expect("completed first argument retains the colon tail");
        assert!(
            !colon
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Comma)
        );
    }
}

#[test]
fn colon_c2_indented_expression_statement_block_preserves_dedent() {
    let (green, exit) = run("f:\n  x");
    assert_eq!(green.to_string(), "f:\n  x");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("indented colon block");
    assert_eq!(
        block.first_token().expect("opening newline").kind(),
        SyntaxKind::Newline
    );
    assert_eq!(
        block.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::Statement]
    );

    let (green, exit) = run("f:\n  x\n  y");
    assert_eq!(green.to_string(), "f:\n  x\n  y");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("indented colon block");
    assert_eq!(
        block.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::Statement,
            SyntaxKind::BlockStatementSeparator,
            SyntaxKind::Statement,
        ]
    );

    let (green, exit) = run("f:\n  x\nz");
    assert_eq!(green.to_string(), "f:\n  x");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token)
                if token.kind == TokenKind::Identifier && &*token.text == "z")
    ));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        1
    );

    let (green, exit) = run("f:\n    x\n      y");
    assert_eq!(green.to_string(), "f:\n    x\n      y");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("indented colon block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        1
    );
    assert!(
        block
            .descendants()
            .any(|node| node.kind() == SyntaxKind::MlArgument)
    );
}

#[test]
fn colon_c2_handoffs_unimplemented_block_statement_slots() {
    for source in ["f:\nx", "f:\n  ", "f:\n  @"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), "f", "{source:?}");
        assert!(matches!(
            exit,
            Some(Err(Either::Left(item)))
                if matches!(item.payload, Payload::Token(ref token)
                    if token.kind == TokenKind::Colon)
        ));
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        );
    }

    let (green, exit) = run("f:\n  x\n  @");
    assert_eq!(green.to_string(), "f:\n  x");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token)
                if token.kind == TokenKind::Unknown)
    ));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("completed first block statement");
    assert!(
        !block
            .children()
            .any(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
    );
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}
