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
                    if item.payload_view().token_kind() == Some(TokenKind::Unknown)
                        && item.payload_view().spelling() == Some(".")
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
            if item.payload_view().token_kind() == Some(TokenKind::Colon)
    ));
}

#[test]
fn with_c5_is_a_terminal_direct_body_tail() {
    let (green, exit) = run("f with: x");
    assert_eq!(green.to_string(), "f with: x");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        operator_chain_children(&green),
        [SyntaxKind::IdentifierExpression, SyntaxKind::WithBodyTail,]
    );

    for source in ["f /*c*/ with : x", "f\n  with:\n    x"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::WithBodyTail)
        );
    }

    for source in ["f withx", "f with?"] {
        let (green, _) = run(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::WithBodyTail),
            "{source:?}"
        );
    }

    let with_operator = OperatorTable::from_declarations([OperatorDeclaration::new(
        "with",
        OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::scalar(40)),
    )])
    .expect("contextual with test table");
    let (green, exit) = run_with("f with: x", &with_operator);
    assert_eq!(green.to_string(), "f with: x");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::WithKw)
    );
    for source in ["f with?: x", "f with!: x"] {
        let (green, _) = run_with(source, &with_operator);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::WithBodyTail),
            "{source:?}"
        );
    }

    for source in ["f with: x: y", "f with: x with: y"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.children()
                .find(|node| node.kind() == SyntaxKind::OperatorChain)
                .expect("outer chain")
                .children()
                .filter(|node| node.kind() == SyntaxKind::WithBodyTail)
                .count(),
            1,
            "{source:?}"
        );
    }

    for source in ["f with", "f with x", "f with: ", "f with:\n  "] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let tail = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::WithBodyTail)
            .expect("with tail");
        assert_eq!(
            tail.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run("f with:\nx");
    assert_eq!(green.to_string(), "f with:");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::Identifier)
                && item.payload_view().spelling() == Some("x")
    ));
    let tail = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::WithBodyTail)
        .expect("with tail");
    assert_eq!(
        tail.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run("f with\nx");
    assert_eq!(green.to_string(), "f with");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::Identifier)
                && item.payload_view().spelling() == Some("x")
    ));
    let tail = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::WithBodyTail)
        .expect("with tail");
    assert_eq!(
        tail.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        !tail
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Newline)
    );

    let (green, exit) = run("f with ;");
    assert_eq!(green.to_string(), "f with ");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::Semicolon)
    ));
    let tail = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::WithBodyTail)
        .expect("with tail");
    assert!(
        !tail
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Semicolon)
    );

    for source in ["f with: ;", "f with: @;", "f with: @ x"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let tail = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::WithBodyTail)
            .expect("with tail");
        if source == "f with: ;" {
            assert_eq!(
                tail.children()
                    .filter(|node| node.kind() == SyntaxKind::Missing)
                    .count(),
                1
            );
        } else {
            assert_eq!(
                tail.children()
                    .filter(|node| node.kind() == SyntaxKind::Error)
                    .count(),
                1,
                "{source:?}"
            );
        }
        if source != "f with: @ x" {
            assert!(
                tail.descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| token.kind() == SyntaxKind::Semicolon)
            );
        }
    }

    let (green, exit) = run("f with {}");
    assert_eq!(green.to_string(), "f with ");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::LBrace)
    ));
    let tail = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::WithBodyTail)
        .expect("with tail");
    assert_eq!(
        tail.descendants()
            .filter(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .count(),
        0
    );

    let (green, exit) = run("(f with: x, y)");
    assert_eq!(green.to_string(), "(f with: x, y)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let tail = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::WithBodyTail)
        .expect("with tail");
    assert!(
        !tail
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Comma)
    );
}

#[test]
fn colon_c4_commits_and_recovers_mandatory_inline_slots() {
    for (source, expected) in [
        ("f:", "f:"),
        ("f:   ", "f:   "),
        ("f:\nx", "f:"),
        ("f:\n  ", "f:\n  "),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), expected, "{source:?}");
        let root = SyntaxNode::new_root(green);
        let colon = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .expect("accepted colon tail");
        assert_eq!(
            colon
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !colon
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{source:?}"
        );
        if source == "f:\nx" {
            assert!(matches!(
                exit,
                Some(Err(Either::Left(item)))
                    if item.payload_view().token_kind() == Some(TokenKind::Identifier)
                        && item.payload_view().spelling() == Some("x")
            ));
            assert!(
                !colon
                    .descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| token.kind() == SyntaxKind::Newline)
            );
        } else {
            assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        }
    }

    for source in ["f: , x", "f: x,"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let colon = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .expect("colon tail");
        assert_eq!(
            colon
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            colon
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Comma)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run("(f:, y)");
    assert_eq!(green.to_string(), "(f:, y)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let colon = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .expect("colon tail");
    assert_eq!(
        colon
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        !colon
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Comma)
    );

    let (green, exit) = run("f: @ x");
    assert_eq!(green.to_string(), "f: @ x");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let colon = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .expect("colon tail");
    assert_eq!(
        colon
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );
    assert_eq!(
        colon
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        0
    );
    assert_eq!(
        colon
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );

    let (green, exit) = run("f: @  ");
    assert_eq!(green.to_string(), "f: @  ");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let colon = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .expect("colon tail");
    assert_eq!(
        colon.last_token().expect("tail trailing trivia").text(),
        "  "
    );

    let (green, exit) = run("f: {x}");
    assert_eq!(green.to_string(), "f: {x}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
    );

    let operators = dynamic_operator_table();
    for (source, kind) in [
        ("f: ~x", SyntaxKind::PrefixOperatorUse),
        ("f: ?", SyntaxKind::NullfixOperatorUse),
    ] {
        let (green, exit) = run_with(source, &operators);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let colon = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .expect("colon tail");
        assert!(
            colon.descendants().any(|node| node.kind() == kind),
            "{source:?}"
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
            if item.payload_view().token_kind() == Some(TokenKind::Identifier)
                && item.payload_view().spelling() == Some("z")
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
fn colon_c4_recovers_deep_indented_statement_slots() {
    let (green, exit) = run("f:\n  ");
    assert_eq!(green.to_string(), "f:\n  ");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("deep block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    for source in ["f:\n  @", "f:\n  @ x"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
            .expect("deep block");
        assert_eq!(
            block
                .children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            block
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            0,
            "{source:?}"
        );
    }

    let (green, exit) = run("f:\n  x\n  @\n  y");
    assert_eq!(green.to_string(), "f:\n  x\n  @\n  y");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("deep block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
            .count(),
        2
    );
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        2
    );
}

#[test]
fn braced_statement_block_owns_normal_sequence_and_colon_comma() {
    for source in ["{}", "{ }", "{\n}"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .expect("braced statement block");
        assert!(
            !block
                .children()
                .any(|node| node.kind() == SyntaxKind::Statement)
        );
    }

    let (green, exit) = run("{x: 1}");
    assert_eq!(green.to_string(), "{x: 1}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced statement block");
    assert_eq!(
        block.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::Statement]
    );
    assert_eq!(
        block
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .count(),
        1
    );

    for (source, separator) in [
        ("{x,y}", SyntaxKind::Comma),
        ("{x;y}", SyntaxKind::Semicolon),
        ("{x\ny}", SyntaxKind::Newline),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .expect("braced statement block");
        assert_eq!(
            block.children().map(|node| node.kind()).collect::<Vec<_>>(),
            [
                SyntaxKind::Statement,
                SyntaxKind::BlockStatementSeparator,
                SyntaxKind::Statement,
            ],
            "{source:?}"
        );
        let separator_node = block
            .children()
            .find(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
            .expect("block separator");
        assert!(
            separator_node
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == separator),
            "{source:?}"
        );
    }

    for source in ["{x,}", "{x;}", "{x\n}"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .expect("braced statement block");
        assert_eq!(
            block.children().map(|node| node.kind()).collect::<Vec<_>>(),
            [SyntaxKind::Statement, SyntaxKind::BlockStatementSeparator],
            "{source:?}"
        );
        assert!(
            !block
                .descendants()
                .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error)),
            "{source:?}"
        );
    }

    let (green, exit) = run("{x: 1, y: 2}");
    assert_eq!(green.to_string(), "{x: 1, y: 2}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced statement block");
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
            .filter(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .count(),
        2
    );
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
            .count(),
        1
    );
}

#[test]
fn braced_statement_block_recovers_close_and_keeps_nested_boundaries() {
    for source in ["{", "{x", "{x,"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .expect("braced statement block");
        assert_eq!(
            block
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run("{@}");
    assert_eq!(green.to_string(), "{@}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );

    let (green, exit) = run("{x]}");
    assert_eq!(green.to_string(), "{x]}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced statement block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );
    assert_eq!(
        block
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::RBrace)
            .count(),
        1
    );
    assert!(
        !block
            .children()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    let (green, exit) = run("{x\n  y}");
    assert_eq!(green.to_string(), "{x\n  y}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced statement block");
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

    let (green, exit) = run("{x,@\ny}");
    assert_eq!(green.to_string(), "{x,@\ny}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced statement block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
            .count(),
        2
    );
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        2
    );

    let (green, exit) = run("{x\n  @}");
    assert_eq!(green.to_string(), "{x\n  @}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced statement block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
            .count(),
        0
    );
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );

    let (green, exit) = run("{{x}}.field");
    assert_eq!(green.to_string(), "{{x}}.field");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        operator_chain_children(&green),
        [
            SyntaxKind::BracedStatementBlockExpression,
            SyntaxKind::FieldTail,
        ]
    );
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .count(),
        2
    );
}
